/- Independent Lean counterparts of the graph fixtures in lean_examples.py.
   Layer 1 U(n) corresponds to Lean Type n, not Lean Sort n or Prop.
   No Mathlib or external packages are used. -/

namespace Layer1Examples

def identity (A : Type) (x : A) : A := x

def constant (A B : Type) (x : A) (_y : B) : A := x

def compose (A B C : Type) (f : B → C) (g : A → B) (x : A) : C :=
  f (g x)

def flip (A B C : Type) (f : A → B → C) (y : B) (x : A) : C :=
  f x y

def dependentApply (A : Type) (B : A → Type)
    (f : (x : A) → B x) (x : A) : B x :=
  f x

def dependentCompose (A : Type) (B : A → Type)
    (C : (x : A) → B x → Type)
    (f : (x : A) → (y : B x) → C x y)
    (g : (x : A) → B x) (x : A) : C x (g x) :=
  f x (g x)

def Endo (A : Type) : Type := A → A

def endoIdentity (A : Type) : Endo A := fun x => x

def letIdentity (A : Type) (x : A) : A :=
  let y := x
  y

abbrev CBool := (A : Type) → A → A → A

def churchTrue : CBool := fun _A yes _no => yes
def churchFalse : CBool := fun _A _yes no => no

def choose (A : Type) (b : CBool) (yes no : A) : A :=
  b A yes no

def churchNot (b : CBool) : CBool := fun A yes no => b A no yes

example (A : Type) (x y : A) : choose A churchTrue x y = x := rfl
example (A : Type) (x y : A) : choose A churchFalse x y = y := rfl
example : churchNot churchTrue = churchFalse := rfl
example : churchNot churchFalse = churchTrue := rfl

abbrev CNat := (A : Type) → (A → A) → A → A

def church0 : CNat := fun _A _step zero => zero
def church1 : CNat := fun _A step zero => step zero
def church2 : CNat := fun _A step zero => step (step zero)
def church3 : CNat := fun _A step zero => step (step (step zero))

def churchAdd (m n : CNat) : CNat := fun A step zero =>
  m A step (n A step zero)

def churchMul (m n : CNat) : CNat := fun A step zero =>
  m A (n A step) zero

example (A : Type) (s : A → A) (z : A) :
    churchAdd church2 church3 A s z = s (s (s (s (s z)))) := rfl
example (A : Type) (s : A → A) (z : A) :
    churchMul church2 church3 A s z = s (s (s (s (s (s z))))) := rfl
example : churchAdd church0 church2 = church2 := rfl
example : churchMul church0 church2 = church0 := rfl

abbrev CPair (A B : Type) := (R : Type) → (A → B → R) → R

def churchPair (A B : Type) (x : A) (y : B) : CPair A B :=
  fun _R combine => combine x y

def churchFst (A B : Type) (p : CPair A B) : A :=
  p A (fun x _y => x)

def churchSnd (A B : Type) (p : CPair A B) : B :=
  p B (fun _x y => y)

example (A B : Type) (x : A) (y : B) :
    churchFst A B (churchPair A B x y) = x := rfl
example (A B : Type) (x : A) (y : B) :
    churchSnd A B (churchPair A B x y) = y := rfl

-- Layer 1 checks this same function eta typing example.
def etaWitness (A B : Type) (D : (A → B) → Type)
    (f : A → B) (value : D f) : D (fun x => f x) :=
  value

def etaArgument (A B : Type) (D : (A → B) → Type)
    (f : A → B) (value : D f) (consume : D (fun x => f x) → A) : A :=
  consume value

example : True := by
  fail_if_success
    have bad : (A : Type) → (D : (A → A) → Type) →
        (f g : A → A) → D f → D (fun x => f (g x)) :=
      fun _A _D _f _g value => value
  trivial

-- Negative checks: each inner declaration must fail to elaborate.
example : True := by
  fail_if_success
    have bad : Type := Type
  trivial

example : True := by
  fail_if_success
    have bad : Type 2 := Type
  trivial

example : True := by
  fail_if_success
    have bad : (A : Type) → A := fun A => A
  trivial

example : True := by
  fail_if_success
    have bad : Type := (Type : Type 1) Type
  trivial

example : True := by
  fail_if_success
    have bad := churchTrue Type
  trivial

end Layer1Examples
