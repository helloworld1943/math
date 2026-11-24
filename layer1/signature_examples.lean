namespace Layer1SignatureChecks

inductive Ground : Type where
  | value : Ground

inductive HandlerBox (A : Type) (B : A → Type) : Type where
  | mk : ((x : A) → B x) → HandlerBox A B

def handler : HandlerBox Ground (fun _ => Ground) :=
  .mk (fun _ => Ground.value)

inductive BinaryTree : Type where
  | leaf : BinaryTree
  | branch : BinaryTree → BinaryTree → BinaryTree

def tree : BinaryTree := .branch (.branch .leaf .leaf) .leaf

inductive TypeHolder : Type 1 where
  | mk : Type → TypeHolder

def heldType : TypeHolder := .mk Ground

inductive NamedHandler (A : Type) (f : A → A) : Type where
  | mk : NamedHandler A f

def namedIdentity : NamedHandler Ground (fun x => x) := .mk

example : True := by
  fail_if_success
    have bad : HandlerBox Ground (fun _ => Ground) := HandlerBox.mk Ground.value
  trivial

example : True := by
  fail_if_success
    have bad : Type := Ground.value
  trivial

end Layer1SignatureChecks
