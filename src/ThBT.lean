import src.LambdaTheory.Basic
import src.BetaEquiv
import src.Bohm_Tree
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

open Cslib
open LambdaCalculus.LocallyNameless.Untyped

open Term

namespace LambdaTheory

universe u

variable {Var : Type u}

-- Lemma 3.9
lemma BT_eq_of_BetaEquiv (M N : Term Var) (hβ : M ≡β N) : BT Var M = BT Var N := by
  sorry

def ThBT (M N : Term Var) : Prop :=
  BT Var M = BT Var N

-- We prove that ThBT defines a λ-theory
instance instThBT : LambdaTheory (Var:=Var) ThBT where
  beta M N := by
    intro h
    apply BT_eq_of_BetaEquiv
    apply Relation.EqvGen.rel
    apply Xi.base
    assumption
  refl M := by
    apply BT_eq_of_BetaEquiv
    apply Relation.EqvGen.refl
  sym M N := by
    intro h
    apply h.symm
  trans M N O := by
    unfold ThBT
    intro h₁ h₂
    rw [h₁, h₂]
  -- Requires a bit of work
  xi M N xs h := by
    unfold ThBT
    sorry
  app M N P Q := by
    sorry
