import json
import unittest
from pathlib import Path

from .language import LanguageError, parse, run_source
from .runtime import World


class ObjectLanguageTests(unittest.TestCase):
    def reject(self, source, message=None, stage="type", packages=None):
        with self.assertRaises(LanguageError) as caught:
            run_source(source, packages)
        self.assertEqual(caught.exception.stage, stage)
        if message:
            self.assertIn(message, caught.exception.message)

    def test_basic_types_literals_and_explicit_conversions(self):
        result = run_source("""
            Nat n=10;Int i=-5;Bool b=true;Float f=1.5;
            print(n);print(i);print(b);print(f);
            print(Int(n));print(Nat(3));print(Float(n));print(Int(1.9));
            Nat other=5;print(n-other);print(other-n);
        """)
        self.assertEqual(result["output"], ["10", "-5", "true", "1.5", "10", "3", "10.0", "1", "5", "0"])
        for source in ("Nat n=-1;", "Bool b=5;", "Int x=true;", "Float f=true;",
                       "Nat n=5;Int x=n;", "Int x=5;Float f=x;", "Bool b=Bool(1);"):
            self.reject(source)
        self.reject("print(Nat(-1));", "negative", "runtime")
        self.reject("\npublic class Functions{}\nstatic func Functions.f(Int Nat) Int{return Nat;}", "reserved parameter")
        self.reject("\npublic class Functions{}\nstatic func Functions.f() Int{Int Nat=1;return Nat;}", "reserved name")

    def test_arbitrary_precision_not_fixed_width(self):
        number = "9" * 600
        result = run_source(f"Nat n={number};print(n+1);Int i=-{number};print(i-1);")
        self.assertEqual(result["output"], [str(int(number)+1), str(-int(number)-1)])
        self.assertEqual(result["variables"]["n"], number)
        self.assertEqual(result["variables"]["i"], "-" + number)
        self.assertTrue(all(node["type"] in (None, "Nat", "Int") for node in result["nodes"]))

    def test_float_arithmetic_and_nonfinite_errors(self):
        self.assertEqual(run_source("Float x=1.5;print(x+2);print(x/2);print(2.5%2.0);")["output"],
                         ["3.5", "0.75", "0.5"])
        self.reject("Float x=1e999;", "Nonfinite", "runtime")
        self.reject("print(1.0/0.0);", "zero", "runtime")
        self.assertEqual(run_source("print(-1.5);")["output"], ["-1.5"])
        self.reject("Float x=" + "9" * 600 + ";", "overflow", "runtime")
        self.reject("Nat n=3;print(-n);", "Negating Nat")

    def test_class_type_identity_is_nominal(self):
        self.reject("class X{Int a;}class Y{Int a;}X x=X{a:1};Y y=x;", "Expected Y")
        world = World(parse("class X{Int a;}class Y{Int a;}"), {})
        world.check()
        self.assertNotEqual(world.modules[""].declarations["X"].type, world.modules[""].declarations["Y"].type)

    def test_alias_assignment_and_rebinding(self):
        result = run_source("""
            class X{Int a;}
            X x=X{a:1};X y=x;y.a=9;print(x.a);
            y=X{a:2};print(x.a);print(y.a);
        """)
        self.assertEqual(result["output"], ["9", "9", "2"])
        self.assertNotEqual(result["variables"]["x"]["object"], result["variables"]["y"]["object"])

    def test_shallow_copy_does_not_copy_nested_class(self):
        result = run_source("""
            class Inner{Int n;}
            class Outer{Int a;Inner l;}
            Inner inner=Inner{n:1};
            Outer w=Outer{a:2,l:inner};
            Outer copy=w.Copy();
            copy.a=8;copy.l.n=9;
            print(w.a);print(w.l.n);print(copy.a);
        """)
        self.assertEqual(result["output"], ["2", "9", "8"])
        objects = {item["id"]: item for item in result["objects"]}
        w, copy = result["variables"]["w"]["object"], result["variables"]["copy"]["object"]
        self.assertNotEqual(w, copy)
        self.assertEqual(objects[w]["fields"]["l"], objects[copy]["fields"]["l"])

    def test_copy_is_only_an_instance_method(self):
        self.reject("print(Copy(3));")
        self.reject("class X{}X x=X{};x.Copy(1);", "no arguments")

    def test_user_copy_hook_can_choose_deep_copy(self):
        result = run_source("""
            class Inner{Int n;}
            class Outer{Inner l;}
            func Inner.Copy() Inner{return Inner{n:this.n};}
            func Outer.Copy() Outer{return Outer{l:this.l.Copy()};}
            Outer w=Outer{l:Inner{n:1}};
            Outer cloned=w.Copy();cloned.l.n=9;print(w.l.n);
        """)
        self.assertEqual(result["output"], ["1"])

    def test_custom_copy_hook_may_deliberately_return_alias(self):
        self.assertEqual(run_source("""
            class X{Int n;}
            func X.Copy() X{return this;}
            X x=X{n:1};X y=x.Copy();y.n=2;print(x.n);
        """)["output"], ["2"])
        for source in (
            "class X{}func X.Copy() Int{return 1;}",
            "class X{}func X.Copy(Int n) X{return X{};}",
        ):
            self.reject(source, "Copy method")

    def test_copy_receiver_is_evaluated_once(self):
        self.assertEqual(run_source("""
public class Functions{}

            Int calls=0;
            class X{Int n;}
            static func Functions.make() X{calls=calls+1;return X{n:1};}
            func X.Copy() X{return X{n:this.n};}
            X copied=Functions.make().Copy();print(calls);
        """)["output"], ["1"])

    def test_copy_override_visibility(self):
        source = """
            package a;
public class Functions{}

            public class X{Int n;}
            public static func Functions.make() X{return X{n:1};}
            func X.Copy() X{return this;}
        """
        self.reject("package z;import a;X x=Functions.make();X c=x.Copy();", "Private", packages={"a": source})
        public = source.replace("func X.Copy", "public func X.Copy")
        self.assertEqual(run_source("package z;import a;X x=Functions.make();X c=x.Copy();print(x==c);", {"a": public})["output"], ["true"])

    def test_method_receiver_evaluated_before_argument_side_effect(self):
        self.assertEqual(run_source("""
public class Functions{}

            class X{Int n;}
            X x=X{n:1};X old=x;
            static func Functions.switch() Int{x=X{n:9};return 3;}
            func X.set(Int n) X{this.n=n;return this;}
            x.set(Functions.switch());print(old.n);print(x.n);
        """)["output"], ["3", "9"])

    def test_package_headers_without_semicolons(self):
        self.assertEqual(run_source(
            "package z\nimport a\nprint(Functions.f());",
            {"a": "package a\npublic class Functions{}\n\npublic static func Functions.f() Int{return 1;}"},
        )["output"], ["1"])

    def test_class_initializer_must_be_unique_and_typed(self):
        for source in (
            "class X{Int a;}X x=X{a:true};",
            "class X{Int a;}X x=X{a:1,a:2};",
            "class X{Int a;}X x=X{b:1};",
            "class X{Int a;Int a;}",
        ):
            self.reject(source)

    def test_default_declarations_for_all_types(self):
        result = run_source("""
            Bool b; Float f; Int i; Nat n;
            class X{Int a;} X x;
            print(b);print(f);print(i);print(n);print(x);
        """)
        self.assertEqual(result["output"], ["false", "0.0", "0", "0", "X{a: 0}"])
        self.assertEqual({name: result["variables"][name] for name in ("b", "f", "i", "n")},
                         {"b": False, "f": 0.0, "i": 0, "n": 0})
        self.assertFalse(result["variables"]["x"]["nil"])
        self.assertEqual(result["objects"][0]["fields"], {"a": 0})

    def test_local_defaults_assignment_and_shadowing(self):
        self.assertEqual(run_source("""
public class Functions{}

            Bool b=true;
            static func Functions.f() Int{Int n;Bool ready; n=n+3;if(ready){return 9;}return n;}
            if(true){Bool b;print(b);}print(b);print(Functions.f());
        """)["output"], ["false", "true", "3"])

    def test_partial_class_literals_default_all_omitted_fields(self):
        result = run_source("""
            class X{Int i;Nat n;Bool b;Float f;X child;}
            X x=X{i:5}; X empty=X{};
            print(x.i);print(x.n);print(x.b);print(x.f);print(x.child);
            print(empty.i);print(empty==nil);
        """)
        self.assertEqual(result["output"], ["5", "0", "false", "0.0", "X(nil)", "0", "false"])
        objects = {obj["id"]: obj for obj in result["objects"]}
        fields = objects[result["variables"]["x"]["object"]]["fields"]
        self.assertEqual({name: fields[name] for name in ("i", "n", "b", "f")},
                         {"i": 5, "n": 0, "b": False, "f": 0.0})
        self.assertTrue(fields["child"]["nil"])

    def test_recursive_class_defaults_do_not_allocate_children(self):
        result = run_source("class X{X next;}X x=X{};print(x.next==nil);")
        self.assertEqual(result["output"], ["true"])
        self.assertEqual(len(result["objects"]), 2)
        sentinel = next(obj for obj in result["objects"] if obj["nil"])
        self.assertEqual(sentinel["fields"]["next"]["object"], sentinel["id"])

    def test_nil_assignment_comparisons_parameters_and_returns(self):
        self.assertEqual(run_source("""
public class Functions{}

            class X{Int n;}
            static func Functions.empty() X{return nil;}
            static func Functions.missing(X x) Bool{return x==nil;}
            X x=nil;print(x==nil);print(nil==x);print(x==X(nil));
            x=X{};print(nil!=x);print(Functions.missing(nil));print(Functions.empty());
            x=nil;print(x);
        """)["output"], ["true", "true", "true", "true", "true", "X(nil)", "X(nil)"])

    def test_nil_cannot_be_used_as_a_scalar_or_condition(self):
        for source in ("Bool x=nil;", "Nat x=nil;", "Int x=nil;", "Float x=nil;",
                       "if(nil){}", "print(nil+1);", "print(true==nil);",
                       "print(nil==3);", "print(Int(nil));"):
            with self.subTest(source=source):
                self.reject(source)
        for source in ("print(nil);", "print(nil==nil);", "nil;", "class X{};print(nil.Copy());"):
            self.reject(source, "expected class type")

    def test_nil_does_not_erase_nominal_class_types(self):
        self.reject("class X{}class Y{}X x;Y y=x;", "Expected Y")
        self.reject("class X{}class Y{}X x;Y y;print(x==y);", "Expected X")

    def test_typed_nil_is_a_shared_mutable_inhabitant(self):
        result = run_source("""
            class X{Int n;}
            X a=nil;X b=nil;X c=X(nil);X fresh;
            print(a==b);print(b==c);print(fresh==nil);
            a.n=7;print(b.n);print(c.n);print(fresh.n);
            func X.get() Int{return this.n;}
            print(b.get());print(X(nil).get());
        """)
        self.assertEqual(result["output"], ["true", "true", "false", "7", "7", "0", "7", "7"])
        self.assertEqual(result["variables"]["a"], result["variables"]["b"])
        self.assertTrue(result["variables"]["a"]["nil"])
        self.assertFalse(result["variables"]["fresh"]["nil"])

    def test_default_declarations_allocate_distinct_usable_objects(self):
        self.assertEqual(run_source("class X{Int n;}X a;X b;a.n=3;print(b.n);print(a==b);print(a==nil);")["output"],
                         ["0", "false", "false"])

    def test_nil_copy_makes_a_new_outer_object(self):
        result = run_source("class X{Int n;}X a=nil;a.n=7;X b=a.Copy();b.n=9;print(a.n);print(b.n);print(b==nil);")
        self.assertEqual(result["output"], ["7", "9", "false"])

    def test_nested_typed_nil_sharing_and_mutual_recursion(self):
        result = run_source("""
            class A{B b;}class B{A a;Int n;}
            A x;A y;x.b.n=5;print(y.b.n);
            A nilA=nil;B nilB=nil;print(nilA.b==nilB);print(nilB.a==nilA);
        """)
        self.assertEqual(result["output"], ["5", "true", "true"])

    def test_nil_singletons_are_per_nominal_type_and_execution(self):
        self.reject("class X{}class Y{}X a=nil;Y b=nil;print(a==b);", "Expected X")
        run_source("class X{Int n;}X a=nil;a.n=7;")
        self.assertEqual(run_source("class X{Int n;}X a=nil;print(a.n);")["output"], ["0"])

    def test_default_copy_preserves_nil_nested_fields(self):
        result = run_source("class X{X child;Int n;}X x=X{n:1};X y=x.Copy();y.n=3;print(x.n);print(y.child);")
        self.assertEqual(result["output"], ["1", "X(nil)"])

    def test_partial_literals_do_not_expose_private_fields(self):
        sources = {"a": "package a;public class X{Int hidden;public Bool ready;}"}
        result = run_source("package z;import a;X x=X{ready:true};X y=X{};print(x.ready);", sources)
        self.assertEqual(result["output"], ["true"])
        self.reject("package z;import a;X x=X{hidden:0};", "Private field", packages=sources)
        self.reject("package z;import a;X x=X{};print(x.hidden);", "Private field", packages=sources)

    def test_nil_is_a_keyword_not_an_identifier(self):
        self.reject("Int nil;", stage="syntax")
        self.assertEqual(run_source("Bool nil_value;print(nil_value);")["output"], ["false"])

    def test_package_defaults_and_nil_fields_follow_visibility_rules(self):
        result = run_source("package b;import a;print(flag);print(absent);print(Functions.make().n);", {
            "a": "package a;\npublic class Functions{}\npublic Bool flag;public class X{public Int n;}public X absent;public static func Functions.make() X{return X{};}",
        })
        self.assertEqual(result["output"], ["false", "a.X{n: 0}", "0"])

    def test_typed_nil_still_obeys_private_field_rules(self):
        sources = {"a": "package a;public class X{Int hidden;public Int visible;}"}
        self.assertEqual(run_source("package z;import a;X x=nil;X y=nil;x.visible=4;print(y.visible);", sources)["output"], ["4"])
        self.reject("package z;import a;X x=nil;print(x.hidden);", "Private field", packages=sources)

    def test_nil_source_location_and_default_declaration_classure(self):
        program = parse("class X{};\nX x;\nx=nil;")
        declaration = next(node for node, info in program.descriptions.items() if info.kind == "declaration")
        self.assertEqual(len(program.description(declaration).children), 2)
        literal = next(node for node, info in program.descriptions.items() if info.kind == "nil_literal")
        self.assertEqual((program.description(literal).line, program.description(literal).column), (3, 3))

    def test_method_declared_outside_class_and_this_alias(self):
        result = run_source("""
            class X{Int a;}
            func X.set(Int a) X{this.a=a;return this;}
            func X.get() Int{return this.a;}
            X x=X{a:1};X y=x.set(5);print(x.get());print(y==x);
        """)
        self.assertEqual(result["output"], ["5", "true"])
        self.assertEqual(result["variables"]["x"], result["variables"]["y"])
        self.reject("class X{func f() Int{return 1;}}", stage="syntax")
        self.reject("class X{}func X.f() X{this=X{};return this;}", "this cannot")
        self.reject("\npublic class Functions{}\nstatic func Functions.f() Int{return this;}", "Unknown variable")

    def test_method_calls_on_returned_objects(self):
        self.assertEqual(run_source("""
public class Functions{}

            class X{Int a;}
            static func Functions.make() X{return X{a:4};}
            func X.get() Int{return this.a;}
            print(Functions.make().get());
        """)["output"], ["4"])

    def test_nested_fields_assignment_and_methods(self):
        self.assertEqual(run_source("""
            class Inner{Int a;}class Outer{Inner l;}
            func Inner.get() Int{return this.a;}
            Outer w=Outer{l:Inner{a:3}};
            w.l.a=4;print(w.l.get());print(w.l.a);
        """)["output"], ["4", "4"])

    def test_repeated_classes_are_separate_objects_not_interned(self):
        result = run_source("class X{Int a;}X x=X{a:1};X y=X{a:1};print(x==y);")
        self.assertEqual(result["output"], ["false"])
        self.assertNotEqual(result["variables"]["x"], result["variables"]["y"])
        program = parse("Bool a=true;Bool b=true;")
        types = [node for node, info in program.descriptions.items() if info.kind == "type"]
        self.assertEqual(len(types), 2)
        self.assertIsNot(types[0], types[1])

    def test_recursive_functions_and_control_flow(self):
        self.assertEqual(run_source("""
public class Functions{}

            static func Functions.fact(Nat n) Nat{if(n<=1){return 1;}else{return n*Functions.fact(n-1);}}
            print(Functions.fact(5));
            Nat i=0;while(i<3){i=i+1;}print(i);
        """)["output"], ["120", "3"])

    def test_public_class_does_not_expose_private_fields(self):
        package = "package a;\npublic class Functions{}\npublic class X{Int hidden;public Int visible;}public static func Functions.make() X{return X{hidden:1,visible:2};}"
        self.assertEqual(run_source("package b;import a;a.X x=a.Functions.make();print(x.visible);", {"a": package})["output"], ["2"])
        self.reject("package b;import a;a.X x=a.Functions.make();print(x.hidden);", "Private field", packages={"a": package})
        self.reject("package b;import a;a.X x=a.X{hidden:1,visible:2};", "Private field", packages={"a": package})

    def test_parent_private_visibility_and_no_reexport(self):
        sources = {
            "a": "package a;\npublic class Functions{}\nstatic func Functions.secret() Int{return 7;}public static func Functions.pub() Int{return 8;}",
            "a.child": "package a.child;\npublic class Functions{}\npublic static func Functions.child() Int{return a.Functions.secret();}",
        }
        self.assertEqual(run_source("package z;import a.child;print(Functions.child());", sources)["output"], ["7"])
        self.reject("package z;import a.child;print(Functions.secret());", packages=sources)
        self.reject("package z;import a.child;print(a.Functions.pub());", packages=sources)
        self.reject("package z;import a;print(a.child.Functions.child());", packages=sources)
        self.assertEqual(run_source("package a.child;print(Functions.secret());", {"a": sources["a"]})["output"], ["7"])

    def test_parent_private_types_and_fields_are_visible_to_descendants(self):
        sources = {"a": "package a;class X{Int n;}X x=X{n:4};"}
        self.assertEqual(run_source("package a.child;print(x.n);X y=x;print(y.n);", sources)["output"], ["4", "4"])
        self.reject("package z;import a;X y=x;", packages=sources)

    def test_siblings_and_parents_do_not_see_child_without_import(self):
        source = "package a.one;\npublic class Functions{}\npublic static func Functions.f() Int{return 1;}"
        self.reject("package a.two;print(Functions.f());", packages={"a.one": source})
        self.assertEqual(run_source("package a.two;import a.one;print(Functions.f());", {"a.one": source})["output"], ["1"])
        self.reject("package a;print(a.one.Functions.f());", packages={"a.one": source})

    def test_exact_imports_and_qualified_types(self):
        sources = {
            "a": "package a;public class A{public Int n;}",
            "a.child": "package a.child;public class B{public Int n;}",
        }
        self.reject("package z;import a.child;a.A x=a.A{n:1};", packages=sources)
        self.reject("package z;import a;a.child.B x=a.child.B{n:1};", packages=sources)
        self.assertEqual(run_source(
            "package z;import a;import a.child;a.A x=a.A{n:1};a.child.B y=a.child.B{n:2};print(x.n);print(y.n);", sources,
        )["output"], ["1", "2"])

    def test_public_function_parameter_return_and_receiver_types_must_be_public(self):
        for source in (
            "\npublic class Functions{}\nclass X{}public static func Functions.f() X{return X{};}",
            "\npublic class Functions{}\nclass X{}public static func Functions.f(X x) Int{return 1;}",
            "class X{}public func X.f() Int{return 1;}",
        ):
            self.reject(source, "Public signature")
        result = run_source("public class X{Int n;}class Helper{}public func X.get() Int{Helper h=Helper{};return this.n;}")
        self.assertEqual(result["output"], [])

    def test_private_methods_remain_private_even_on_public_objects(self):
        package = "package a;\npublic class Functions{}\npublic class X{Int n;}public static func Functions.make() X{return X{n:1};}func X.get() Int{return this.n;}"
        self.reject("package z;import a;X x=Functions.make();print(x.get());", "Private", packages={"a": package})
        self.assertEqual(run_source("package a.child;X x=Functions.make();print(x.get());", {"a": package})["output"], ["1"])

    def test_methods_cannot_be_added_to_foreign_classes(self):
        self.reject("package b;import a;func a.X.f() Int{return 1;}", "class's package",
                    packages={"a": "package a;public class X{}"})

    def test_public_functions_can_use_private_helpers_internally(self):
        sources = {"a": "package a;\npublic class Functions{}\nstatic func Functions.helper() Int{return 3;}public static func Functions.f() Int{return Functions.helper();}"}
        self.assertEqual(run_source("package z;import a;print(Functions.f());", sources)["output"], ["3"])

    def test_imports_are_not_transitively_visible(self):
        sources = {
            "a": "package a;\npublic class Functions{}\npublic static func Functions.f() Int{return 1;}",
            "b": "package b;import a;\npublic class Functions{}\npublic static func Functions.g() Int{return a.Functions.f();}",
        }
        self.assertEqual(run_source("package c;import b;print(Functions.g());", sources)["output"], ["1"])
        self.reject("package c;import b;print(Functions.f());", packages=sources)

    def test_conflicts_cycles_missing_imports_and_source_identity(self):
        self.reject("package a;import missing;", stage="package")
        self.reject("package a;import a;", stage="package")
        self.reject("package a;import b;", stage="package", packages={"b": "package b;import a;"})
        self.reject("package a;", stage="package", packages={"a": "package a;"})
        self.reject("package a;", stage="package", packages={"b": "package wrong;"})
        sources = {
            "a": "package a;\npublic class Functions{}\npublic static func Functions.f() Int{return 1;}",
            "b": "package b;\npublic class Functions{}\npublic static func Functions.f() Int{return 2;}",
        }
        self.reject("package z;import a;import b;print(Functions.f());", packages=sources)
        self.assertEqual(run_source("package z;import a;import b;print(a.Functions.f());print(b.Functions.f());", sources)["output"], ["1", "2"])

    def test_all_packages_checked_before_any_execution(self):
        self.reject("package z;import a;print(1);", packages={
            "a": "package a;\npublic class Functions{}\npublic static func Functions.f() Int{return true;}",
        })

    def test_package_example(self):
        example = json.loads(Path(__file__).with_name("package_example.json").read_text())
        result = run_source(example["source"], example["packages"])
        self.assertEqual(result["output"], ["10", "10", "20", "42", "1000000000000000000000000000001", "-5", "1.5", "true"])
        self.assertEqual(set(result["packageGraphs"]), {"geometry", "geometry.tools", "demo"})

    def test_full_default_example(self):
        self.assertEqual(run_source(Path(__file__).with_name("example.nod").read_text())["output"],
                         ["0", "-5", "true", "1.5", "10", "10", "20", "120"])


if __name__ == "__main__":
    unittest.main()
