/- Independent counterparts of logic_examples.py, followed by native Lean
   checks showing what is not captured by simply renaming Layer 1 U(0). -/

namespace Layer1Logic

abbrev CExists (A : Type) (P : A → Type) :=
  (R : Type) → ((x : A) → P x → R) → R

abbrev COr (P Q : Type) :=
  (R : Type) → (P → R) → (Q → R) → R

abbrev CEq (A : Type) (x y : A) :=
  (P : A → Type) → P x → P y

abbrev CFalse := (R : Type) → R

def forallReorder (A B : Type) (P : A → B → Type)
    (h : (x : A) → (y : B) → P x y) (y : B) (x : A) : P x y :=
  h x y

def existsIntro (A : Type) (P : A → Type) (x : A) (proof : P x) :
    CExists A P :=
  fun _R handler => handler x proof

def existsElim (A : Type) (P : A → Type) (value : CExists A P)
    (R : Type) (handler : (x : A) → P x → R) : R :=
  value R handler

def existsWitness (A : Type) (P : A → Type) (value : CExists A P) : A :=
  value A (fun x _proof => x)

def existsMap (A : Type) (P Q : A → Type)
    (transform : (x : A) → P x → Q x) (value : CExists A P) :
    CExists A Q :=
  fun R handler => value R (fun x proof => handler x (transform x proof))

def orLeft (P Q : Type) (proof : P) : COr P Q :=
  fun _R onLeft _onRight => onLeft proof

def orRight (P Q : Type) (proof : Q) : COr P Q :=
  fun _R _onLeft onRight => onRight proof

def orElim (P Q R : Type) (value : COr P Q)
    (onLeft : P → R) (onRight : Q → R) : R :=
  value R onLeft onRight

def equalityRefl (A : Type) (x : A) : CEq A x x := fun _P proof => proof

def equalitySubst (A : Type) (x y : A) (equality : CEq A x y)
    (P : A → Type) (proof : P x) : P y :=
  equality P proof

def equalitySymm (A : Type) (x y : A) (equality : CEq A x y) : CEq A y x :=
  fun P proofY => equality (fun z => P z → P x) (fun proofX => proofX) proofY

def equalityTrans (A : Type) (x y z : A)
    (xy : CEq A x y) (yz : CEq A y z) : CEq A x z :=
  fun P proof => yz P (xy P proof)

def falseElim (empty : CFalse) (R : Type) : R := empty R

def doubleNegIntro (P : Type) (proof : P) (negate : P → CFalse) : CFalse :=
  negate proof

example (A : Type) (P : A → Type) (x : A) (proof : P x)
    (R : Type) (handler : (x : A) → P x → R) :
    existsElim A P (existsIntro A P x proof) R handler = handler x proof := rfl

example (A : Type) (P : A → Type) (x : A) (proof : P x) :
    existsWitness A P (existsIntro A P x proof) = x := rfl

example (A : Type) (P Q : A → Type) (f : (x : A) → P x → Q x)
    (x : A) (proof : P x) :
    existsMap A P Q f (existsIntro A P x proof) =
      existsIntro A Q x (f x proof) := rfl

example (P Q R : Type) (proof : P) (f : P → R) (g : Q → R) :
    orElim P Q R (orLeft P Q proof) f g = f proof := rfl

example (P Q R : Type) (proof : Q) (f : P → R) (g : Q → R) :
    orElim P Q R (orRight P Q proof) f g = g proof := rfl

example (A : Type) (x : A) (P : A → Type) (proof : P x) :
    equalitySubst A x x (equalityRefl A x) P proof = proof := rfl

example (A : Type) (P : A → Type) : Type 1 := CExists A P
example (P Q : Type) : Type 1 := COr P Q
example (A : Type) (x y : A) : Type 1 := CEq A x y

example : True := by
  fail_if_success
    have bad : (P : Type) → (p q : P) → (D : P → Type) → D p → D q :=
      fun _P _p _q _D value => value
  trivial

example : True := by
  fail_if_success
    have bad : (A : Type) → (P : A → Type) → CExists A P → Type :=
      fun A P value => value Type (fun _x _proof => A)
  trivial

example : True := by
  fail_if_success
    have bad : (S : Type 1) → (A : S) → A → A :=
      fun _S _A x => x
  trivial

-- Native Lean features below are not implemented by the graph fixtures.
example : Prop = Sort 0 := rfl
example : Type = Sort 1 := rfl
example : Type 1 := Type
example : Type := Prop

theorem nativeForall (A : Type) (P : A → Prop) (h : ∀ x, P x) (x : A) : P x :=
  h x

theorem nativeExistsIntro (A : Type) (P : A → Prop) (x : A) (proof : P x) :
    ∃ x, P x :=
  ⟨x, proof⟩

theorem nativeExistsElim (A : Type) (P : A → Prop) (R : Prop)
    (value : ∃ x, P x) (handler : ∀ x, P x → R) : R :=
  Exists.elim value handler

theorem nativeOrElim (P Q R : Prop) (value : P ∨ Q)
    (onLeft : P → R) (onRight : Q → R) : R :=
  Or.elim value onLeft onRight

theorem nativeAndIntro (P Q : Prop) (p : P) (q : Q) : P ∧ Q := ⟨p, q⟩

example : ([0, 1] : List Nat).any (fun n => n == 1) = true := rfl

example : ∃ n : Nat, n ∈ [0, 1] ∧ n = 1 :=
  ⟨1, by simp, rfl⟩

-- Impredicativity: even quantification over Type 1 can produce a Prop.
example : Prop := ∀ (A : Type 1), A → True
example : Type 2 := (A : Type 1) → A → A

-- Proof irrelevance changes definitional equality, not just printed names.
def nativeProofIrrelevance (P : Prop) (p q : P)
    (D : P → Type) (value : D p) : D q :=
  value

example : True := by
  fail_if_success
    have bad : (A : Type) → (P : A → Prop) → (∃ x, P x) → A :=
      fun _A _P value => match value with
        | ⟨x, _proof⟩ => x
  trivial

def nativeSigmaIntro (A : Type) (B : A → Type) (x : A) (value : B x) :
    Sigma B :=
  ⟨x, value⟩

def nativeSigmaSnd (A : Type) (B : A → Type) (value : Sigma B) :
    B value.1 :=
  value.2

end Layer1Logic