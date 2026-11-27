import unittest
from pathlib import Path

from .language import LanguageError, parse, run_source


TRUTH = """
public class Functions{public TypeDef Unary:Int->Int;}

class Truth : Prop {}
constructor func Truth.intro() Truth {}
"""

ANY = TRUTH + """
class AnyInput : Sort(2) {
    const A : Type;
    TypeDef B : A -> Prop;
    const b : B;
    TypeDef H : ((x : A) -> b(x));
    const h : H;
}
class Any : Prop {
    const A : SortU;
    TypeDef B : A -> Prop;
    const b : B;
    TypeDef H : ((x : A) -> b(x));
    const h : H;
}
constructor func Any.intro(input:AnyInput) Any {
    this.A = input.A;
    this.b = input.b;
    this.h = input.h;
}
static func Functions.predicate(x:Nat) Prop { return Truth; }
static func Functions.evidence(x:Nat) Truth { return Truth.intro(); }
"""

BOX = """
public class Functions{public TypeDef Unary:Int->Int;}

class BoxInput : Sort(2) { const A:Type; value:A; }
class Box : Sort(2) { const A:Type; value:A; }
constructor func Box.make(input:BoxInput) Box { this.A=input.A; this.value=input.value; }
"""


class DependentClassTests(unittest.TestCase):
    def test_pi_is_not_a_native_keyword(self):
        self.assertEqual(self.output("Int Pi=3;print(Pi);"), ["3"])
        program = parse("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f(x:Int, callback:Functions.Unary) Int{return callback(x);}")
        self.assertFalse(any(info.kind == "pi_term" for info in program.descriptions.values()))
        self.reject("check Pi(x:Nat)=>Nat;", stage="syntax")

    def output(self, source):
        return run_source(source)["output"]

    def reject(self, source, text=None, stage="type", packages=None):
        with self.assertRaises(LanguageError) as caught:
            run_source(source, packages)
        self.assertEqual(caught.exception.stage, stage)
        if text is not None:
            self.assertIn(text, caught.exception.message)

    def test_colon_fields_parameters_and_const_metadata(self):
        program = parse("""
            class Box : Sort(2) { const A:Sort(1); value:A; }
            constructor func Box.make(A:Sort(1), value:A) Box {
                this.A=A;this.value=value;
            }
        """)
        class_spec = program.items()[0]
        children = program.description(class_spec).children
        self.assertEqual(program.description(children[1]).kind, "class_sort_level")
        bindings = [program.binding(node) for node in children[2:]]
        self.assertEqual([(name, const) for _, name, const, _ in bindings], [("A", True), ("value", False)])
        self.assertEqual(program.description(program.items()[1]).kind, "constructor")

    def test_named_unnamed_and_colon_parameters(self):
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.inc(x:Int) Int { return x+1; }
            static func Functions.apply(x:Int, f:Functions.Unary) Int { return f(x); }
            static func Functions.ignore(Int, f:Functions.Unary){ print(f(2)); }
            print(Functions.apply(3,Functions.inc));Functions.ignore(100,Functions.inc);
            static func Functions.identity(Int x) Int { return x; } print(Functions.identity(9));
        """), ["4", "3", "9"])
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f(x:Int,x:Bool){}", "Duplicate")
        self.reject("class X{const Type:Sort(1);}", "Reserved field")
        self.reject("class X{Int Copy;}", "Reserved field")
        self.reject("print((fun(Type:Type)=>Type)(Nat));", stage="tokenizer")

    def test_first_class_function_variables_fields_and_named_implementations(self):
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.inc(x:Int) Int{return x+1;}
            const Int->Int f=Functions.inc;
            class Holder{const callback:Functions.Unary;}
            const Holder h=Holder{callback:f};
            print(h.callback(5));
            static func Functions.apply(x:Int,f:Functions.Unary) Int{return f(x);}
            static func Functions.double(Int x) Int{return x*2;}
            print(Functions.apply(3,Functions.double));
            print(Functions.inc(4));
        """), ["6", "6", "5"])
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.use(f:Bool->Bool) Int{return f(3);}", "simple names")
        self.reject("Int->Int f;", "initializer")

    def test_arrow_is_right_associative_and_can_return_function_values(self):
        self.assertEqual(self.output("""
            class Operations{TypeDef Add:((x:Int)->(y:Int)->Int);}
            static func Add Operations.add{return x+y;}
            const Int->Int->Int f=Operations.add;
            print(f(3)(4));print(f(5,6));
        """), ["7", "11"])
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.add(x:Int,y:Int) Int{return x+y;}
            const Int->Int->Int f=Functions.add;
            const Int->Int g=f(3);print(g(4));print(f(5,6));
        """), ["7", "11"])
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f() Int{return 1;}Int x=Functions.f;", "Expected Int")

    def test_function_interfaces_package_dependencies_in_classes(self):
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            class Box:Sort(2){const A:Type;value:A;}
            static func Functions.identity(Box input) Box{return input;}
            const Box numbers=Box{A:Nat,value:5};
            const Box flags=Box{A:Bool,value:true};
            const Box output=Functions.identity(numbers);print(output.value);
            const Box boolOutput=Functions.identity(flags);print(boolOutput.value);
        """), ["5", "true"])
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.identity(A:SortU,x:A) A{return x;}", "non-dependent")
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.identity(A:Type,Int x) A{return x;}", "non-dependent")
        self.reject("SortU all=SortU;", "not a first-class")

    def test_type_producing_functions_reduce_without_runtime_effects(self):
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.IdType(A:Type) Type{return A;}
            const Type Alias=Functions.IdType(Nat);
            Alias x=5;print(x);
            class Input{TypeDef N:Functions.IdType(Int);}
            static func Functions.consume(n:Input.N) Int{return n;}
            print(Functions.consume(7));
        """), ["5", "7"])
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.bad() Type{print(1);return Nat;}", "pure single-return")
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nType t=Nat;static func Functions.bad() Type{return t;}", "must be const")
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.bad() Type{return 3;}", "Expected")
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.arrow(Type A) Type{return A->A;}
            const Type F=Functions.arrow(Nat);print(F);
            class Identity{TypeDef H:((x:Nat)->Nat);}
            static func H Identity.id{return x;}
            const F identity=Identity.id;print(identity(3));
        """), ["(Nat -> Nat)", "3"])
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.arrow(Type A,Type B) Type{return A->B;}
            const Type->Type->Type full=Functions.arrow;
            const Type->Type resultType=full(Nat);
            const Type F=resultType(Nat);
            class Identity{TypeDef H:((x:Nat)->Nat);}
            static func H Identity.id{return x;}
            const F identity=Identity.id;print(identity(3));
        """), ["3"])

    def test_type_dependency_rejects_mutable_value_and_accepts_const(self):
        type_function = "\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.fixed(n:Nat) Type{return Nat;}"
        self.reject(type_function + "Nat n=3;Functions.fixed(n) x=1;", "must be const")
        self.assertEqual(self.output(type_function + "const Nat n=3;Functions.fixed(n) x=5;print(x);"), ["5"])
        self.assertEqual(self.output("const Type A=Nat;class X{value:A;}X x=X{value:3};print(x.value);"), ["3"])
        self.assertEqual(self.output("const Type A=Nat;class X{value:A;}X x;X y=nil;print(x.value);print(y.value);"), ["0", "0"])
        self.reject("const A A=Nat;class X{value:A;}", "Cyclic dependency")
        self.reject("const SortU A=Sort(99);class X:Type{value:A;}", "above class")
        from .runtime import World

        program = parse("const Nat n=3-5;")
        world = World(program, {})
        world.check()
        declaration = world.entry.declarations["n"]
        symbol = world.symbol(world.entry, declaration.node, "n")
        self.assertEqual(world.normalize_static(world.entry, declaration.node, world.static_values[symbol]).value, 0)

    def test_const_binding_and_field_writes_rejected_through_aliases(self):
        for source in (
            "const Nat n=3;n=4;",
            "class C{const Nat length;}C c=C{length:3};C alias=c;alias.length=4;",
            "class C{const Nat length;}C c=nil;c.length=4;",
            "class C{const Nat length;}C c=C{length:3};C d=c.Copy();d.length=4;",
        ):
            with self.subTest(source=source):
                self.reject(source, "const")
        self.assertEqual(self.output("class C{const Nat length;Int spare;}C c=C{length:3};c.spare=9;print(c.spare);"), ["9"])

    def test_const_paths_in_nested_dependent_fields(self):
        prefix = """
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.fixed(n:Nat) Type{return Nat;}
            class Config{const Nat length;}
        """
        self.assertEqual(self.output(prefix + """
            class Buffer{const config:Config;data:Functions.fixed(config.length);}
            const Config c=Config{length:3};
            const Buffer b=Buffer{config:c,data:5};
            print(b.data);
        """), ["5"])
        self.reject(prefix + "class Buffer{config:Config;data:Functions.fixed(config.length);}", "must be const")
        self.reject("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.fixed(n:Nat) Type{return Nat;}
            class Config{Nat length;}
            class Buffer{const config:Config;data:Functions.fixed(config.length);}
        """, "const through every alias")

    def test_mutable_reference_is_not_a_stable_type_path(self):
        prefix = "\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.fixed(n:Nat) Type{return Nat;}class Config{const Nat length;}"
        self.reject(prefix + "Config c=Config{length:3};Functions.fixed(c.length) value=2;", "must be const")
        self.assertEqual(self.output(prefix + "const Config c=Config{length:3};Functions.fixed(c.length) value=2;print(value);"), ["2"])

    def test_const_can_freeze_a_snapshot_without_reading_it_during_type_checking(self):
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            Int changing=3;const Int frozen=changing;changing=4;print(frozen);
            class Config{const Nat length;Int spare;}
            Config original=Config{length:3};const Config snapshot=original;
            original=Config{length:4};print(snapshot.length);
            static func Functions.fixed(n:Nat) Type{return Nat;}
            Functions.fixed(snapshot.length) value=5;print(value);
        """), ["3", "3", "5"])
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.f(x:Int) Int{const Int original=x;x=x+1;return original;}
            class Pair{const Int first;Int second;}
            constructor func Pair.make(n:Int) Pair {this.first=n;n=n+1;this.second=n;}
            Pair p=Pair.make(3);print(Functions.f(3));print(p.first);print(p.second);
        """), ["3", "3", "4"])

    def test_constructor_static_capture_does_not_require_mutable_payload_to_be_static(self):
        self.assertEqual(self.output("""
        """ + BOX + """
            Nat payload=5;const BoxInput input=BoxInput{A:Nat,value:payload};
            const Box b=Box.make(input);
            Nat extracted=b.value;print(extracted);
        """), ["5"])

    def test_dependent_function_signatures_are_rejected_even_when_reducible(self):
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.id(A:SortU,x:A) A{A=Bool;return x;}", "non-dependent")
        self.reject("""
public class Functions{public TypeDef Unary:Int->Int;}

            static func Functions.fixed(n:Nat) Type{return Nat;}
            static func Functions.f(n:Nat,x:Functions.fixed(n)) Nat{n=4;return x;}
        """, "simple names")
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nclass Box:Sort(2){const A:Type;value:A;}static func Functions.get(Box b) b.A{return b.value;}", "non-dependent")
        self.reject("class Box:Sort(2){const A:Type;value:A;}func Box.get() this.A{return this.value;}", "non-dependent")
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nconst Sort(2) H=(A:Type)->A;static func Functions.use(H h){}", "non-dependent")
        self.assertEqual(self.output("\npublic class Functions{public TypeDef Unary:Int->Int;}\nstatic func Functions.f(x:Int) Int{x=x+1;return x;}print(Functions.f(2));"), ["3"])

    def test_dependent_field_specialization_and_mutable_value_field(self):
        self.assertEqual(self.output("""
            class Box:Sort(2){const A:Sort(1);value:A;}
            const Box b=Box{A:Nat,value:5};b.value=6;print(b.value);
            const Box truth=Box{A:Bool,value:true};print(truth.value);
        """), ["6", "true"])
        self.reject("class Box:Sort(2){const A:Sort(1);value:A;}const Box b=Box{A:Nat,value:true};", "Expected Nat")
        self.reject("class Box:Sort(2){const A:Sort(1);value:A;}const Box b=Box{A:Nat,value:3};b.value=true;", "Expected Nat")
        self.reject("class Box:Sort(2){A:Sort(1);value:A;}", "must be const")

    def test_field_order_and_initializer_order_are_explicit(self):
        self.reject("class Box{value:A;const A:SortU;}", "Unknown")
        self.reject("class Box:Sort(2){const A:Type;value:A;}const Box b=Box{value:3,A:Nat};", "declaration order")
        self.assertEqual(self.output("class Box:Sort(2){const A:Type;value:A;}const Box b=Box{A:Nat};print(b.value);"), ["0"])
        self.assertEqual(self.output("class Pair{Int a;Int b;}Pair p=Pair{b:2,a:1};print(p.a);print(p.b);"), ["1", "2"])

    def test_constructor_builds_all_fields_and_returns_this_implicitly(self):
        result = run_source("""
            class Pair{const Int first;Int second;}
            constructor func Pair.make(first:Int,second:Int) Pair {this.first=first;this.second=second;}
            Pair p=Pair.make(1,2);print(p.first);print(p.second);
        """)
        self.assertEqual(result["output"], ["1", "2"])
        self.assertEqual(result["classes"][0]["constructors"], ["make"])
        self.assertIn("first", result["objects"][0]["constFields"])

    def test_multiple_constructors_and_explicit_return_this(self):
        self.assertEqual(self.output("""
            class X{Int n;}
            constructor func X.first() X {this.n=1;return this;}
            constructor func X.second() X {this.n=2;}
            print(X.first().n);print(X.second().n);
        """), ["1", "2"])

    def test_unnamed_constructor_returns_its_owning_type(self):
        result = run_source("""
            class Box{const Int value;}
            constructor func Box(Int value) Box {this.value=value;}
            Box b=Box(5);print(b.value);
        """)
        self.assertEqual(result["output"], ["5"])
        function = next(fn for fn in result["functions"] if fn["name"] == "Box")
        self.assertTrue(function["constructor"])
        self.assertTrue(function["unnamed"])
        self.assertFalse(function["generator"])
        self.assertEqual(function["returns"], "Box")
        self.assertEqual(result["classes"][0]["constructors"], ["(unnamed)"])
        self.assertTrue(any(node.get("unnamed") for node in result["nodes"]))

    def test_named_and_unnamed_constructors_can_coexist(self):
        self.assertEqual(self.output("""
            class X{Int n;}
            constructor func X(n) X{this.n=n;return this;}
            constructor func X.special() X {this.n=9;}
            print(X(3).n);print(X.special().n);
        """), ["3", "9"])

    def test_unnamed_constructor_can_be_empty_or_schema_dependent(self):
        self.assertEqual(self.output("""
            class Empty{}
            constructor func Empty() Empty {}
            Empty a=Empty();Empty b=Empty();print(a==b);
            class Box:Sort(2){const A:Type;value:A;}
            constructor func Box(A,value) Box {this.A=A;this.value=value;}
            const Box box=Box(Nat,4);print(box.value);
        """), ["false", "4"])

    def test_unnamed_constructor_is_unique_and_not_inferred_from_named_ones(self):
        self.reject("class X{}constructor func X() X {}constructor func X() X {}", "Duplicate unnamed constructor")
        self.reject("class X{Int n;}constructor func X(n) X {this.n=n;}constructor func X() X {this.n=0;}", "Duplicate unnamed constructor")
        self.reject("class X{}constructor func X.make() X {}X x=X();", "No unnamed constructor")
        self.assertEqual(self.output("class X{}class Y{}constructor func X() X {}constructor func Y() Y {}X x=X();Y y=Y();"), [])

    def test_unnamed_constructor_checks_arguments_and_complete_initialization(self):
        self.reject("class X{Int n;}constructor func X(n) X {this.n=n;}X x=X();", "'X' expects 1 arguments")
        self.reject("class X{Int n;}constructor func X(n) X {this.n=n;}X x=X(true);", "Expected Int")
        self.reject("class X{Int n;}constructor func X() X {}", "uninitialized")
        self.reject("class X{Int a;Int b;}constructor func X(a,b) X {this.b=b;this.a=a;}", "before")
        self.reject("class X{Int n;}constructor func X(n) X {return this;}", "unfinished")

    def test_unnamed_constructor_does_not_restore_automatic_creation(self):
        prefix = "class X{const Int n;}constructor func X() X {this.n=3;}"
        for suffix in ("X x;", "X x=nil;", "X x=X(nil);", "X x=X{};", "X x=X();X y=x.Copy();"):
            with self.subTest(suffix=suffix):
                self.reject(prefix + suffix)
        self.assertEqual(self.output(prefix + "func X.Copy() X{return X();}X x=X();print(x.Copy().n);"), ["3"])

    def test_unnamed_constructor_keeps_visibility_and_package_ownership(self):
        package = "package a;public class X{public Int n;}public constructor func X(n) X {this.n=n;}"
        self.assertEqual(run_source("package b;import a;a.X x=a.X(4);print(x.n);", {"a": package})["output"], ["4"])
        self.reject("package b;import a;a.X x=a.X(4);", "Private", packages={"a": package.replace("public constructor func", "constructor func")})
        self.reject("package b;import a;constructor func a.X(n) a.X {this.n=n;}", "class's package", packages={"a": "package a;public class X{public Int n;}"})

    def test_unnamed_constructor_evaluates_arguments_once_in_order(self):
        self.assertEqual(self.output("""
public class Functions{public TypeDef Unary:Int->Int;}

            Int count=0;
            static func Functions.next() Int{count=count+1;return count;}
            class Pair{Int first;Int second;}
            constructor func Pair(first,second) Pair {this.first=first;this.second=second;}
            Pair p=Pair(Functions.next(),Functions.next());
            print(p.first);print(p.second);print(count);
        """), ["1", "2", "2"])

    def test_unnamed_constructor_accepts_nil_as_an_argument_not_an_owner_bypass(self):
        self.assertEqual(self.output("""
            class Inner{Int n;}
            class Outer{Inner child;}
            constructor func Outer(child) Outer {this.child=child;}
            Outer x=Outer(nil);print(x.child==Inner(nil));
        """), ["true"])

    def test_constructor_must_be_in_declaring_package(self):
        self.reject("package b;import a;constructor func a.X.make() a.X {}", "class's package",
                    packages={"a": "package a;public class X{}"})

    def test_constructor_only_creation_no_literal_default_nil_or_implicit_copy(self):
        prefix = "class X{Int n;}constructor func X.make() X {this.n=1;}"
        for suffix in ("X x;", "X x=nil;", "X x=X(nil);", "X x=X{n:1};",
                       "X x=X{};", "X x=X.make();X copy=x.Copy();"):
            with self.subTest(suffix=suffix):
                self.reject(prefix + suffix, "constructor" if "Copy" not in suffix else "checked Copy")
        self.assertEqual(self.output("""
            class X{const Int n;}
            constructor func X.make(Int n) X {this.n=n;}
            func X.Copy() X{return X.make(this.n);}
            X x=X.make(3);X copy=x.Copy();print(copy.n);print(x==copy);
        """), ["3", "false"])

    def test_implicit_field_defaults_do_not_bypass_controlled_type(self):
        prefix = "class X{Int n;}constructor func X.make() X {this.n=1;}class Outer{X child;}"
        self.reject(prefix + "Outer x;", "constructor")
        self.reject(prefix + "Outer x=Outer{};", "constructor")
        self.assertEqual(self.output(prefix + "Outer x=Outer{child:X.make()};print(x.child.n);"), ["1"])

    def test_constructor_definite_initialization_and_order(self):
        for source, message in (
            ("class X{Int a;Int b;}constructor func X.make() X {this.a=1;}", "uninitialized"),
            ("class X{Int a;Int b;}constructor func X.make() X {this.b=2;this.a=1;}", "before"),
            ("class X{Int a;}constructor func X.make() X {this.a=true;}", "Expected Int"),
            ("class X{const Int a;}constructor func X.make() X {this.a=1;this.a=2;}", "already initialized"),
            ("class X{Int a;}constructor func X.make() X {print(this.a);this.a=1;}", "before initialization"),
        ):
            with self.subTest(source=source):
                self.reject(source, message)

    def test_unfinished_constructor_cannot_escape(self):
        for source in (
            "class X{Int a;}constructor func X.make() X {return this;}",
            "class X{Int a;}constructor func X.make() X {X alias=this;this.a=1;}",
            "\npublic class Functions{public TypeDef Unary:Int->Int;}\nclass X{Int a;}static func Functions.consume(x:X) Int{return 1;}constructor func X.make() X {Functions.consume(this);this.a=1;}",
            "class X{Int a;}constructor func X.make() X {return X{a:1};}",
            "class X{Int a;}constructor func X.make() X {this.a=1;return X(nil);}",
        ):
            with self.subTest(source=source):
                self.reject(source)

    def test_constructor_branching_only_after_complete_initialization(self):
        self.reject("class X{Int n;}constructor func X.make(b:Bool) X {if(b){this.n=1;}else{this.n=2;}}", "before branching")
        self.assertEqual(self.output("""
            class X{Int n;}
            constructor func X.make(b:Bool) X {this.n=1;if(b){return this;}return this;}
            print(X.make(true).n);
        """), ["1"])

    def test_dependent_constructor_result_can_be_used_at_its_specialized_type(self):
        self.assertEqual(self.output(BOX + """
            const BoxInput input=BoxInput{A:Nat,value:3};
            const Box b=Box.make(input);
            print(b.value);b.value=4;print(b.value);
        """), ["3", "4"])
        self.reject(BOX + """
            const BoxInput input=BoxInput{A:Nat,value:true};
            const Box b=Box.make(input);
        """, "Expected Nat")

    def test_class_sort_bounds_and_native_sortu_marker(self):
        self.reject("class X:Nat{}", "sort must be")
        self.reject("class Box:Type{const A:Type;}", "above class")
        self.reject("class Box:Sort(2){const A:Type;}const Box b=Box{A:Type};", "Expected Sort(1)")
        self.assertEqual(self.output("class Box:Sort(2){const A:SortU;}const Box b=Box{A:Nat};print(b.A);"), ["Nat"])
        self.reject("class Box:Type{const A:SortU;}const Box b=Box{A:Nat};", "above class")
        self.reject("class Box:Sort(2){const A:SortU;}constructor func Box.make(A:SortU) Box {this.A=A;}", "bounded universe")
        self.reject("class Box:Sort(2){const A:Type;}Box b=nil;", "automatic default")
        self.reject("class Holder{Int->Int f;}Holder h=nil;", "automatic default")

    def test_prop_has_no_field_default_or_nil_creation_even_without_constructor(self):
        for source in ("class P:Prop{}P p;", "class P:Prop{}P p=nil;", "class P:Prop{}P p=P{};",
                       "class P:Prop{}P p=P(nil);"):
            self.reject(source)
        self.assertEqual(run_source("class P:Prop{}")["output"], [])

    def test_any_proof_constructor_checks_evidence(self):
        result = run_source(ANY + "const AnyInput input=AnyInput{A:Nat,b:Functions.predicate,h:Functions.evidence};Any h=Any.intro(input);print(h);")
        self.assertEqual(result["output"], ["<proof Any>"])
        any_object = next(obj for obj in result["objects"] if obj["type"] == "Any")
        self.assertTrue(any_object["prop"])
        self.assertEqual(any_object["fields"], {})
        self.reject(ANY + "static func Functions.wrong(x:Nat) Bool{return true;}const AnyInput input=AnyInput{A:Nat,b:Functions.predicate,h:Functions.wrong};", "Expected")

    def test_sortu_accepts_proposition_domains_from_a_bounded_input_class(self):
        self.assertEqual(self.output(TRUTH + """
            class Evidence:Type{
                const A:Prop;
                TypeDef B:A->Prop;const b:B;
                TypeDef H:((x:A)->b(x));const h:H;
            }
            class Any:Prop{
                const A:SortU;
                TypeDef B:A->Prop;const b:B;
                TypeDef H:((x:A)->b(x));const h:H;
            }
            constructor func Any.intro(Evidence input) Any {
                this.A=input.A;this.b=input.b;this.h=input.h;
            }
            static func Functions.predicate(Truth x) Prop{return Truth;}
            static func Functions.evidence(Truth x) Truth{return x;}
            const Evidence input=Evidence{A:Truth,b:Functions.predicate,h:Functions.evidence};
            Any proof=Any.intro(input);print(proof);
        """), ["<proof Any>"])

    def test_nontermination_is_not_accepted_as_universal_proof(self):
        self.reject("""
public class Functions{public TypeDef Unary:Int->Int;}

            class Impossible:Prop {}
            static func Functions.loop(x:Nat) Impossible{return Functions.loop(x);}
        """, "Recursive code")
        self.reject("""
public class Functions{public TypeDef Unary:Int->Int;}

            class Impossible:Prop {}
            static func Functions.bottom(A:SortU) A{return Functions.bottom(A);}
            static func Functions.evidence(x:Nat) Impossible{return Functions.bottom(Impossible);}
        """, "non-dependent")
        self.reject(TRUTH + "static func Functions.evidence(x:Nat) Truth{while(true){}return Truth.intro();}", "cannot loop")
        self.reject(TRUTH + "static func Functions.evidence(x:Nat) Truth{print(x);return Truth.intro();}", "print effects")
        self.reject(TRUTH + """
            const Nat->Truth evidence=Functions.loop;
            static func Functions.loop(Nat x) Truth{return Functions.loop(x);}
        """, "Recursive code")
        self.reject(TRUTH + """
            class P:Prop{h:Truth;}
            constructor func P.intro() P {this.h=Functions.spin();}
            static func Functions.spin() Truth{return Functions.spin();}
        """, "Recursive code")
        self.assertEqual(self.output(TRUTH + """
            class Config{const Nat length;}
            static func Functions.evidence(Nat n) Truth{return Truth.intro();}
            class Proofs{TypeDef H:((c:Config)->Truth);}
            static func H Proofs.prove{return Functions.evidence(c.length);}
            const Config->Truth proof=Proofs.prove;
            Config c=Config{length:3};print(proof(c));
        """), ["<proof Truth>"])

    def test_prop_field_extraction_is_not_an_unrestricted_data_operation(self):
        self.reject(ANY + "const AnyInput input=AnyInput{A:Nat,b:Functions.predicate,h:Functions.evidence};Any h=Any.intro(input);print(h.A);", "opaque")
        self.reject(TRUTH + "Truth h=Truth.intro();Truth c=h.Copy();", "checked Copy")

    def test_prop_and_dependent_fields_are_initialized_not_filled_by_defaults(self):
        self.reject(TRUTH + "class P:Prop{h:Truth;}constructor func P.intro() P {}", "uninitialized")
        self.reject(TRUTH + "class P:Prop{h:Truth;}constructor func P.intro() P {this.h=nil;}", "constructor")
        self.assertEqual(self.output(TRUTH + """
            class P:Prop{h:Truth;}
            constructor func P.intro(h:Truth) P {this.h=h;}
            P p=P.intro(Truth.intro());print(p);
        """), ["<proof P>"])

    def test_public_constructor_signature_and_field_visibility(self):
        source = """
            package p;
            public class X{const Int n;}
            public constructor func X.make(n:Int) X {this.n=n;}
            public func X.get() Int{return this.n;}
        """
        result = run_source("package q;import p;p.X x=p.X.make(3);print(x.get());", {"p": source})
        self.assertEqual(result["output"], ["3"])
        self.reject("package q;import p;p.X x=p.X.make(3);print(x.n);", "Private field", packages={"p": source})
        self.reject("class Secret{}public class X{Secret s;}public constructor func X.make(s:Secret) X {this.s=s;}",
                    "Public signature")

    def test_public_function_type_parameters_are_checked_recursively(self):
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nclass Hidden{}class Contract{public TypeDef H:Hidden->Int;}public static func Functions.call(f:Contract.H) Int{return 1;}", "Public signature")
        self.assertEqual(run_source("\npublic class Functions{public TypeDef Unary:Int->Int;}\npublic class X{}public class Contract{public TypeDef H:X->Int;}public static func Functions.call(f:Contract.H) Int{return 1;}")["output"], [])
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\npublic class Box:Sort(2){const A:Type;}public static func Functions.get(b:Box) b.A{return b.A;}",
                    "non-dependent")
        self.reject("\npublic class Functions{public TypeDef Unary:Int->Int;}\nclass Hidden{}const Type Alias=Hidden;public static func Functions.use(Alias value) Int{return 1;}",
                    "Public")

    def test_live_example_and_constraint_annotations(self):
        result = run_source(Path(__file__).with_name("dependent_example.nod").read_text())
        self.assertEqual(result["output"], ["6", "true", "4", "<proof Any>", "9", "5"])
        self.assertTrue(any(node.get("constructor") for node in result["nodes"]))
        self.assertTrue(any(node.get("const") for node in result["nodes"]))
        self.assertTrue(any(node.get("sort") == 0 for node in result["nodes"]))
        self.assertTrue(any(fn["constructor"] for fn in result["functions"] if not fn.get("implicit")))


class AliasContractTests(unittest.TestCase):
    def reject(self, source, message=None):
        with self.assertRaises(LanguageError) as caught:
            run_source(source)
        if message:
            self.assertIn(message, str(caught.exception))

    def test_aliases_are_ordered_transparent_and_not_storage(self):
        result = run_source("""
            class Cell{
                TypeDef N:Nat; TypeDef Same:N; const value:Same;
            }
            constructor func Cell(Same n) Cell {this.value=n;}
            Cell c=Cell(3);Nat n=c.value;print(n);
        """)
        self.assertEqual(result["output"], ["3"])
        self.assertEqual([field["name"] for field in result["classes"][0]["fields"]], ["value"])
        self.assertEqual([alias["type"] for alias in result["classes"][0]["aliases"]], ["Nat", "Nat"])
        self.assertEqual(result["objects"][0]["fields"], {"value": 3})
        aliases = [node for node in result["nodes"] if node.get("alias")]
        self.assertEqual(len(aliases), 2)
        self.assertTrue(all("const" not in node for node in aliases))
        self.reject("class Cell{value:N;TypeDef N:Nat;}", "Unknown")
        self.reject("class Cell{TypeDef N:Later;TypeDef Later:Nat;}", "Unknown")

    def test_aliases_do_not_get_defaults_or_literal_initializers(self):
        result = run_source("class Cell{TypeDef N:Nat;N n;}Cell c;print(c.n);")
        self.assertEqual(result["output"], ["0"])
        self.assertEqual(result["objects"][0]["fields"], {"n": 0})
        for source in (
            "class Cell{TypeDef N:Nat;N n;}Cell c=Cell{N:Nat,n:3};",
            "class Cell{TypeDef N:Nat;}Cell c;print(c.N);",
            "class Cell{TypeDef N:Nat;}print(Cell.N);",
            "class Cell{const TypeDef N:Nat;}",
            "class Cell{TypeDef N:Nat=Nat;}",
            "class Cell{TypeDef N:Nat;}constructor func Cell() Cell {this.N=Nat;}",
        ):
            self.reject(source)

    def test_alias_formation_universe_and_reserved_names(self):
        for source in (
            "class Cell{TypeDef N:3;}",
            "class Cell{TypeDef N:Missing;}",
            "class Cell{TypeDef Type:Nat;}",
            "class Cell{TypeDef N:Nat;TypeDef N:Bool;}",
            "class Cell{Nat n;TypeDef n:Nat;}",
            "class Cell{TypeDef N:Nat;Nat N;}",
            "class Cell{TypeDef U:Type;}",
            "class Cell{TypeDef U:SortU;}",
        ):
            self.reject(source)
        self.assertEqual(run_source("class Cell:Sort(2){TypeDef U:Type;}")["classes"][0]["aliases"][0]["type"], "Sort(1)")

    def test_alias_dependencies_require_stable_fields(self):
        self.reject("class Cell:Sort(2){A:Type;TypeDef N:A;}", "must be const")
        self.reject("class Cell:Sort(2){TypeDef N:A;const A:Type;}", "Unknown")
        result = run_source("""
            class Cell:Sort(2){const A:Type;TypeDef N:A;const value:N;}
            constructor func Cell(A a,N n) Cell {this.A=a;this.value=n;}
            const Cell c=Cell(Nat,4);print(c.value);
        """)
        self.assertEqual(result["output"], ["4"])

    def test_simple_parameter_annotations_only(self):
        for type_source in ("Int->Int", "((x:Int)->Int)", "F(Int)", "(Int->Int):Type"):
            self.reject(f"class Owner{{}}static func Int Owner.f({type_source} value){{return 1;}}")
        result = run_source("""
            class Owner{TypeDef Unary:Int->Int;}
            static func Owner.inc(Int n) Int{return n+1;}
            static func Owner.apply(Unary f,Int x) Int{return f(x);}
            print(Owner.apply(Owner.inc,3));
        """)
        self.assertEqual(result["output"], ["4"])

    def test_constructor_lowercase_schema_binding_and_alias_specialization(self):
        from .test_generated_propositions import QUANTIFIERS

        result = run_source(QUANTIFIERS + """
            const Prop P=Any(Nat,Functions.always);print(P.b(Nat(0)));
        """)
        fn = next(fn for fn in result["functions"] if fn["name"] == "Any")
        self.assertEqual(fn["parameters"], [("a", "Sort(1)"), ("b", "(a -> Sort(0))")])
        self.assertEqual(result["output"], ["Truth"])
        self.assertEqual(result["generatedPropositions"][0]["aliases"][0]["type"], "(Nat -> Sort(0))")
        alias_result = run_source(QUANTIFIERS + """
            const Prop P=Any(Nat,Functions.always);
            const P.B predicate=Functions.always;
            print(predicate(Nat(0)));
        """)
        self.assertEqual(alias_result["output"], ["Truth"])
        for suffix in (
            "const Prop P=Any(Nat,Functions.boolProof);",
            "const Prop P=Any(Nat);",
            "const Prop P=Any(Nat,Functions.always);print(P.B(Nat(0)));",
            "constructor func Any.bad(B b,A a) Prop{this.A=a;this.b=b;}",
            "constructor func Any.bad(A a,B b) Prop{this.A=a;this.B=b;}",
            "static func Functions.bad(Any.B predicate) Prop{return Truth;}",
        ):
            self.reject(QUANTIFIERS + suffix)

    def test_named_dependent_contract_body_is_checked(self):
        prefix = """
            class Truth:Prop{}constructor func Truth() Truth {}
            class Packed{const p:Prop;const h:p;}
            constructor func Packed(p,h) Packed {this.p=p;this.h=h;}
            class Proofs{TypeDef H:((x:Packed)->x.p);}
        """
        result = run_source(prefix + """
            static func H Proofs.prove{return x.h;}
            const Packed p=Packed(Truth,Truth());print(Proofs.prove(p));
        """)
        self.assertEqual(result["output"], ["<proof Truth>"])
        self.reject(prefix + "static func H Proofs.wrong{return Truth();}", "Expected")
        self.reject(prefix + "static func H Proofs.wrong{return nil;}")
        self.reject(prefix + "static func H Proofs.wrong{while(true){}return x.h;}", "cannot loop")
        self.reject(prefix + "static func H Proofs.wrong{print(1);return x.h;}", "print effects")
        self.reject(prefix + "static func H Proofs.wrong{return Proofs.wrong(x);}", "Recursive")

    def test_contract_parameters_are_not_a_return_type_shortcut(self):
        self.reject("class Owner{TypeDef N:Nat;}static func N Owner.bad{return 1;}", "complete arrow")
        self.reject("class Owner{TypeDef H:Int->Int;}static func H Owner.bad{return 1;}", "named arrow binders")
        self.reject("class Owner{TypeDef H:((x:Int)->Int);}func H Owner.bad{return x;}", "static")
        self.reject("class Owner{}static func Int Owner.bad{return 1;}", "class TypeDef")
        self.reject("class Owner{TypeDef H:((x:Int)->Int);}static func H Owner.bad{}", "must return")

    def test_qualified_contract_and_explicit_capture_specialization(self):
        result = run_source("""
            class Contracts:Sort(2){TypeDef I:((T:Type)->(x:T)->T);}
            class Identity:Sort(2){const A:Type;TypeDef Apply:A->A;const apply:Apply;}
            static func Contracts.I Identity.id{return x;}
            constructor func Identity(A a) Identity {this.A=a;this.apply=Identity.id(a);}
            const Identity n=Identity(Nat);const Identity b=Identity(Bool);
            print(n.apply(4));print(b.apply(true));
        """)
        self.assertEqual(result["output"], ["4", "true"])
        self.reject("class O:Sort(2){TypeDef I:((T:Type)->(x:T)->T);}static func O.id(Int n) O.I{return n;}", "non-dependent")

    def test_named_implementations_reduce_alpha_beta_and_delta(self):
        from .test_generated_propositions import QUANTIFIERS

        result = run_source(QUANTIFIERS + """
            class Contracts:Sort(2){
                TypeDef F:((T:Type)->(x:T)->Prop);
                TypeDef G:((U:Type)->(y:U)->Prop);
            }
            static func F Contracts.first{return Truth;}
            static func G Contracts.second{return Truth;}
            const Prop P=Any(Nat,Contracts.first(Nat));
            const Prop Q=Any(Nat,Contracts.second(Nat));
            const Prop R=Any(Nat,Functions.always);
            print(P==Q);print(P==R);
        """)
        self.assertEqual(result["output"], ["true", "true"])
        self.assertEqual(len(result["generatedPropositions"]), 3)

    def test_alias_visibility_and_public_signatures(self):
        package = """
            package a;public class Owner{public TypeDef N:Nat;TypeDef Private:Nat;}
            public static func Owner.id(Owner.N n) Nat{return n;}
        """
        self.assertEqual(run_source("package b;import a;a.Owner.N n=3;print(a.Owner.id(n));", {"a": package})["output"], ["3"])
        with self.assertRaises(LanguageError):
            run_source("package b;import a;a.Owner.Private n=3;", {"a": package})
        contract_package = "package a;public class Contracts:Sort(2){public TypeDef I:((T:Type)->(x:T)->T);}"
        result = run_source("""
            package b;import a;class Helpers{}
            static func a.Contracts.I Helpers.identity{return x;}
            print(Helpers.identity(Nat,3));print(Helpers.identity(Bool,true));
        """, {"a": contract_package})
        self.assertEqual(result["output"], ["3", "true"])
        self.reject("class Hidden{}public class Owner{public TypeDef N:Hidden;}", "Public")
        self.reject("public class Owner{TypeDef H:((x:Int)->Int);}public static func H Owner.f{return x;}", "private TypeDef")
        self.reject("public class Owner{TypeDef H:((x:Int)->Int);}public class Helpers{}public static func Owner.H Helpers.f{return x;}", "private TypeDef")
        self.reject("class Owner{public TypeDef H:((x:Int)->Int);}public static func H Owner.f{return x;}", "private type")
        checked = run_source("package b;import a;check a.Owner.N:Type;", {"a": package})
        self.assertEqual(checked["output"], ["a.Owner.N : Sort(1)"])

    def test_no_source_anonymous_functions_in_any_position(self):
        for source in (
            "check fun(x:Type)=>x;",
            "class O{const f:Int->Int;}constructor func O() O {this.f=fun(x:Int)=>x;}",
            "class O{TypeDef H:((x:Int)->Int);const h:H;}constructor func O(H h) O {this.h=h;}O o=O(fun(x:Int)=>x);",
            "class O{TypeDef H:((x:Int)->Int);}static func H O.f{return fun(y:Int)=>y;}",
            "const Int->Int f=fun(x:Int)=>x;",
        ):
            self.reject(source)

    def test_formal_class_checks_have_real_annotations_without_execution(self):
        from unittest.mock import patch
        from .runtime import World

        source = """
            class Box:Sort(2){const A:Type;value:A;}
            class Contracts{TypeDef N:Nat;}
            check Box:Sort(2);check Contracts.N:Type;
            print(123);Int n=1;while(true){n=n+1;}
        """
        with patch.object(World, "execute", side_effect=AssertionError("runtime effects")), \
             patch.object(World, "evaluate", side_effect=AssertionError("runtime effects")), \
             patch.object(World, "invoke", side_effect=AssertionError("runtime effects")):
            result = run_source(source)
        self.assertEqual(result["steps"], 0)
        self.assertEqual(result["variables"], {})
        graph = {node["id"]: node for node in result["theory"]["nodes"]}
        for report in result["theory"]["reports"]:
            annotation = graph[report["annotation"]]
            self.assertEqual(annotation["kind"], "Annotation")
            self.assertEqual(annotation["children"], [report["node"], report["typeNode"]])
            self.assertEqual(graph[report["typeNode"]]["kind"], "Sort")
        self.assertEqual(result["output"], ["Box : Sort(2)", "Contracts.N : Sort(1)"])
        self.reject("class Box:Sort(2){const A:Type;}check Box:Type;", "Expected")
        self.reject("class Box{}check (Nat->Nat);", "named")
        self.reject("check Sort(1);", "named")

    def test_formal_generated_specification_never_materializes_runtime_fields(self):
        from unittest.mock import patch
        from .runtime import World
        from .test_generated_propositions import QUANTIFIERS

        with patch.object(World, "execute", side_effect=AssertionError("effect")):
            result = run_source(QUANTIFIERS + """
                const Type T=Nat;const Prop P=Any(T,Functions.always);
                class Evidence:P{TypeDef H:((x:P.A)->P.b(x));const h:H;}
                constructor func Evidence(H h) Evidence {this.h=h;}
                static func H Evidence.prove{return Truth();}
                check Evidence.H:Prop;
                check P.B:Type;
            """)
        self.assertEqual(result["steps"], 0)
        self.assertEqual(result["output"], ["Evidence.H : Sort(0)", "P.B : Sort(1)"])

    def test_named_contract_value_bindings_preserve_their_checked_type(self):
        self.assertEqual(run_source("""
            class Owner{TypeDef H:((x:Int)->Int);}
            static func H Owner.identity{return x;}
            const Owner.H operation=Owner.identity;
            print(operation(7));
        """)["output"], ["7"])
        self.reject("""
            class Owner{TypeDef H:((x:Int)->Int);}
            static func Owner.wrong(Int x) Bool{return true;}
            const Owner.H operation=Owner.wrong;
        """, "Expected")


if __name__ == "__main__":
    unittest.main()
