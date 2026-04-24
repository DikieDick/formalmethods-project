import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Mathlib.Tactic

open Cslib
open LambdaCalculus.LocallyNameless.Untyped

universe u

variable {Var : Type u}

inductive isHeadRedexApp : Term Var → Prop where
  | base N P₁ : isHeadRedexApp (Term.app (Term.abs N) P₁)
  | step T Pₙ : isHeadRedexApp T -> isHeadRedexApp (Term.app T Pₙ)

inductive isHeadRedex : Term Var → Prop where
  | base T : isHeadRedexApp T -> isHeadRedex T
  | step T : isHeadRedex T -> isHeadRedex (Term.abs T)

inductive isHeadNormalApp : Term Var → Prop where
  | base_free y : isHeadNormalApp (Term.fvar y)
  | base_bound n : isHeadNormalApp (Term.bvar n)
  | step T Pₙ : isHeadNormalApp T -> isHeadNormalApp (Term.app T Pₙ)

inductive isHeadNormal : Term Var → Prop where
  | base T : isHeadNormalApp T -> isHeadNormal T
  | step T : isHeadNormal T -> isHeadNormal (Term.abs T)

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
