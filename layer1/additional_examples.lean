/- Additional counterparts for the supported fragment only. No new eliminators
   or indexed inductives are required by the Python test fixtures. -/
namespace Layer1Additional

def twice (A : Type) (f : A → A) (x : A) : A := f (f x)
example (A : Type) (x : A) : twice A (fun y => y) x = x := rfl

def returnsFunction (A B : Type) (_f : A → B) (_x : A) (g : B → A) :
    B → A := fun y => g y

def Endo (A : Type) : Type := A → A
example (A : Type) : Endo ((fun (T : Type) => T) A) = (A → A) := rfl

inductive Ground : Type where
  | value : Ground

inductive Triple : Type where
  | mk : Ground → Ground → Ground → Triple

def triple : Triple := .mk .value .value .value

inductive EvidenceBox (A : Type) (B : A → Type) (a : A) (h : B a) : Type where
  | mk : EvidenceBox A B a h

def evidenceBox : EvidenceBox Ground (fun _ => Ground) Ground.value Ground.value :=
  .mk

inductive Package (A : Type) (B : A → Type) : Type where
  | mk : (x : A) → B x → Package A B

def package : Package Ground (fun _ => Ground) := .mk .value .value

inductive LargeBox (A : Type 1) : Type 1 where
  | mk : A → LargeBox A

def largeBox : LargeBox Type := .mk Ground

example : True := by
  fail_if_success
    have bad : (A : Type) → (B : A → Type) → (x y : A) → B x →
        Package A B :=
      fun _A _B _x y h => Package.mk y h
  trivial

-- A bad use must not succeed merely because the result has the right name.
example : True := by
  fail_if_success
    have bad : (A B : Type) → A → B := fun _A _B x => x
  trivial

end Layer1Additional
