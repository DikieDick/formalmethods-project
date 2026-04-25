import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Mathlib.Tactic
import src.BetaEquiv

open Cslib
open LambdaCalculus.LocallyNameless.Untyped

universe u

variable {Var : Type u}

inductive isHeadRedexApp : Term Var → Prop where
  | base N P₁ : isHeadRedexApp ((Term.abs N).app P₁)
  | step T Pₙ : isHeadRedexApp T -> isHeadRedexApp (T.app Pₙ)

inductive isHeadRedex : Term Var → Prop where
  | base T : isHeadRedexApp T -> isHeadRedex T
  | step T : isHeadRedex T -> isHeadRedex (Term.abs T)

inductive isHeadNormalApp : Term Var → Prop where
  | base_free y : isHeadNormalApp (Term.fvar y)
  | base_bound n : isHeadNormalApp (Term.bvar n)
  | step T Pₙ : isHeadNormalApp T -> isHeadNormalApp (T.app Pₙ)

inductive isHeadNormal : Term Var → Prop where
  | base T : isHeadNormalApp T -> isHeadNormal T
  | step T : isHeadNormal T -> isHeadNormal (Term.abs T)

-- Lemma 3.2
lemma normal_or_redex (T : Term Var) : isHeadRedex T ∨ isHeadNormal T := by
  induction' T with T T T ih T₁ T₂ ih1 ih2
  · right
    apply isHeadNormal.base
    apply isHeadNormalApp.base_bound
  · right
    apply isHeadNormal.base
    apply isHeadNormalApp.base_free
  · cases ih
    · left ; apply isHeadRedex.step ; assumption
    · right; apply isHeadNormal.step ; assumption
  · induction T₁
    · right ; apply isHeadNormal.base ; apply isHeadNormalApp.step ; apply isHeadNormalApp.base_bound
    · right ; apply isHeadNormal.base ; apply isHeadNormalApp.step ; apply isHeadNormalApp.base_free
    · left ; apply isHeadRedex.base ; apply isHeadRedexApp.base
    · rcases ih1 with ih1 | ih1
      · cases ih1 ; left ; apply isHeadRedex.base ; apply isHeadRedexApp.step ; assumption
      · cases ih1 ; right ; apply isHeadNormal.base ; apply isHeadNormalApp.step ; assumption

def nfoldAbs : ℕ → Term Var → Term Var
| 0, T => T
| n + 1, T => nfoldAbs n T.abs

def nfoldApp : List (Term Var) → Term Var → Term Var
| [], T => T
| a :: as, T => nfoldApp as (T.app a)

inductive List.BetaEquiv : List (Term Var) → List (Term Var) → Prop where
  | base : [].BetaEquiv []
  | step as bs T₁ T₂ : T₁.BetaEquiv T₂ → as.BetaEquiv bs → (T₁ :: as).BetaEquiv (T₂ :: bs)

-- Reduction does not affect the number of leading abstractions, the head variable, or the number of arguments of the head-variable
lemma reduction_preservation (n m : ℕ) (y z : Var) (Ps Qs : List (Term Var)) :
    (nfoldAbs n (nfoldApp Ps (Term.fvar y))).Beta (nfoldAbs m (nfoldApp Qs (Term.fvar z))) ->
    n = m ∧ y = z ∧ Ps.BetaEquiv Qs := by
  sorry

-- Lemma 3.5
lemma hnfs_similar (n m : ℕ) (y z : Var) (Ps Qs : List (Term Var)) (M : Term Var) :
    M.BetaEquiv (nfoldAbs n (nfoldApp Ps (Term.fvar y))) ->
    M.BetaEquiv (nfoldAbs m (nfoldApp Qs (Term.fvar z))) ->
    n = m ∧ y = z ∧ Ps.BetaEquiv Qs := by
  sorry

-- coinductive BöhmTree : Type where
--   | no_hnf : BöhmTree
--   | hnf : List BöhmTree → BöhmTree
--
-- -- Definition 3.7
-- def BT : Term Var → BöhmTree
