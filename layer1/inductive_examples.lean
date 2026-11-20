/- The first declaration fragment: no eliminators are implemented in Python.
   Python currently still indexes U(n) like Type n, not Sort n. -/

namespace Layer1Inductives

inductive MyBool : Type where
  | false : MyBool
  | true : MyBool

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

def two : MyNat := .succ (.succ .zero)

inductive Box (A : Type) : Type where
  | mk : A → Box A

def boxedTrue : Box MyBool := .mk .true

inductive MyList (A : Type) : Type where
  | nil : MyList A
  | cons : A → MyList A → MyList A

def oneTrue : MyList MyBool := .cons .true .nil

inductive Stored (A : Type) (x : A) : Type where
  | mk : Stored A x

def storedTrue : Stored MyBool MyBool.true := .mk

inductive FunctionHolder (A : Type) (h : A → A) : Type where
  | mk : FunctionHolder A h

inductive Empty : Type where

#check MyBool.true
#check MyNat.succ
#check Box.mk
#check MyList.cons
#check Stored.mk
#check FunctionHolder.mk

end Layer1Inductives
