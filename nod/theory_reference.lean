namespace NodReference

structure Box where
  A : Type
  value : A

def makeBox (A : Type) (value : A) : Box :=
  { A := A, value := value }

example : Sort 2 := Box
example : (makeBox Nat 3).A = Nat := rfl
example : (makeBox Nat 3).value = (3 : Nat) := rfl

inductive Truth : Prop where
  | intro

structure PackedProof where
  p : Prop
  h : p

namespace StructContracts

abbrev Identity := (T : Type) → T → T
abbrev RenamedIdentity := (A : Type) → A → A

def identity (T : Type) (x : T) : T := x

example : Sort 2 := Identity
example : Identity := identity
example : Identity = RenamedIdentity := rfl
example (T : Type) (x : T) : identity T x = x := rfl

abbrev Predicate (A : Type) := A → Prop

structure Specification where
  A : Type
  b : Predicate A

abbrev B (spec : Specification) := Predicate spec.A
abbrev H (spec : Specification) := (x : spec.A) → spec.b x

inductive Universal (spec : Specification) : Prop where
  | intro (h : H spec)

inductive Existential (spec : Specification) : Prop where
  | intro (witness : spec.A) (h : spec.b witness)

def always (_ : Nat) : Prop := Truth
theorem truthAt (_ : Nat) : Truth := Truth.intro
def naturalSpecification : Specification := { A := Nat, b := always }

example : Sort 2 := Specification
example : B naturalSpecification := always
example : H naturalSpecification := truthAt
example : Universal naturalSpecification := .intro truthAt
example : Existential naturalSpecification := .intro (3 : Nat) Truth.intro

def packedPredicate (x : PackedProof) : Prop := x.p
theorem packedEvidence (x : PackedProof) : x.p := x.h
def packedSpecification : Specification := { A := PackedProof, b := packedPredicate }

example : H packedSpecification := packedEvidence
example : Universal packedSpecification := .intro packedEvidence
example : Existential packedSpecification :=
  .intro { p := Truth, h := Truth.intro } Truth.intro

def never (_ : Nat) : Prop := False
def falseSpecification : Specification := { A := Nat, b := never }

example : Prop := Universal falseSpecification
example : Prop := Existential falseSpecification

theorem falseUniversalHasNoEvidence (h : Universal falseSpecification) : False := by
  cases h with
  | intro evidence => exact evidence (0 : Nat)

theorem falseExistentialHasNoEvidence (h : Existential falseSpecification) : False := by
  cases h with
  | intro _ evidence => exact evidence

theorem universalIff (spec : Specification) :
    Universal spec ↔ (∀ x : spec.A, spec.b x) := by
  constructor
  · intro h
    cases h with
    | intro evidence => exact evidence
  · intro evidence
    exact .intro evidence

theorem existentialIff (spec : Specification) :
    Existential spec ↔ (∃ x : spec.A, spec.b x) := by
  constructor
  · intro h
    cases h with
    | intro witness evidence => exact ⟨witness, evidence⟩
  · intro h
    rcases h with ⟨witness, evidence⟩
    exact .intro witness evidence

end StructContracts

end NodReference
