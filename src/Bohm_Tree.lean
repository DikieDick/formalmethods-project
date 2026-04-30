import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Mathlib.Tactic
import Coinductive
import src.BetaEquiv

open Cslib
open LambdaCalculus.LocallyNameless.Untyped
open Coinductive

universe u

variable {Var : Type u}

inductive isHeadRedexApp : Term Var → Prop where
  | base N P₁ : isHeadRedexApp ((Term.abs N).app P₁)
  | step T Pₙ : isHeadRedexApp T → isHeadRedexApp (T.app Pₙ)

inductive isHeadRedex : Term Var → Prop where
  | base T : isHeadRedexApp T → isHeadRedex T
  | step T : isHeadRedex T → isHeadRedex (Term.abs T)

inductive isHeadNormalApp : Term Var → Prop where
  | base_free y : isHeadNormalApp (Term.fvar y)
  | base_bound n : isHeadNormalApp (Term.bvar n)
  | step T Pₙ : isHeadNormalApp T → isHeadNormalApp (T.app Pₙ)

inductive isHeadNormal : Term Var → Prop where
  | base T : isHeadNormalApp T → isHeadNormal T
  | step T : isHeadNormal T → isHeadNormal (Term.abs T)

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

def bfvar (Var : Type u) := { v : Term Var // (exists n, v = Term.bvar n) ∨ (exists v', v = Term.fvar v') }

-- Reduction does not affect the number of leading abstractions, the head variable, or the number of arguments of the head-variable
lemma reduction_preservation_fvar (n m : ℕ) (y z : bfvar Var) (Ps Qs : List (Term Var)) :
    (nfoldAbs n (nfoldApp Ps y.val)).Beta (nfoldAbs m (nfoldApp Qs z.val)) →
    n = m ∧ y = z ∧ Ps.BetaEquiv Qs := by
  sorry

-- Lemma 3.5
lemma hnfs_similar_fvar (n m : ℕ) (y z : bfvar Var) (Ps Qs : List (Term Var)) (M : Term Var) :
    M.BetaEquiv (nfoldAbs n (nfoldApp Ps y.val)) →
    M.BetaEquiv (nfoldAbs m (nfoldApp Qs z.val)) →
    n = m ∧ y = z ∧ Ps.BetaEquiv Qs := by
  sorry

inductive BöhmTreeF (Var : Type u) (T : Type u) : Type u where
  | no_hnf
  | hnf (n : ℕ) (num_abstractions : ℕ) (v : bfvar Var) (branches : ULift (Fin n) → T)

instance : Inhabited (BöhmTreeF Var PUnit) where default := .no_hnf

inductive BöhmTreeF.in : Type u where
  | no_hnf
  | hnf (n : ℕ) (num_abstractions : ℕ) (v : bfvar Var)

instance : PF (BöhmTreeF Var) where
  P := ⟨BöhmTreeF.in, fun
    | .no_hnf => PEmpty
    | .hnf n na v => ULift (Fin n)⟩
  unpack
    | .no_hnf => .obj (.no_hnf) nofun
    | .hnf n na v f => .obj (.hnf n na v) f
  pack
    | .obj (.no_hnf) _ => .no_hnf
    | .obj (.hnf n na v) f => .hnf n na v f
  unpack_pack := by rintro _ ⟨⟩ <;> simp
  pack_unpack := by rintro _ (⟨⟨⟩, _⟩ | ⟨⟨⟩⟩) <;> simp ; funext x ; cases x

abbrev BöhmTree (Var : Type u) := CoInd (BöhmTreeF Var)
abbrev BöhmTreeN (Var : Type u) (n : Nat) : Type u := CoIndN (BöhmTreeF Var) n

def BöhmTree.fold (t : (BöhmTreeF Var) (BöhmTree Var)) : (BöhmTree Var) := CoInd.fold _ t
def BöhmTree.unfold (t : (BöhmTree Var)) : (BöhmTreeF Var) (BöhmTree Var) := CoInd.unfold _ t
def BöhmTree.no_hnf : (BöhmTree Var) := BöhmTree.fold .no_hnf
def BöhmTree.hnf (n : ℕ) (na : ℕ) (t : bfvar Var) (f : ULift (Fin n) → (BöhmTree Var)) : (BöhmTree Var) := BöhmTree.fold (.hnf n na t f)

def hasAsHnf : Term Var → (n : ℕ) → List (Term Var) → bfvar Var → Prop := λ T n Ps y ↦
  let T' := nfoldAbs n (nfoldApp Ps y.val) ; isHeadNormal T' ∧ T.BetaEquiv T'

-- Definition 3.7
coinductive BT (Var : Type u) : Term Var → BöhmTree Var → Prop where
  | no_hnf (T : Term Var) :
      ¬(exists n Ps y, hasAsHnf T n Ps y) →
      BT Var T BöhmTree.no_hnf
  | hnf_fvar (T : Term Var) (n : ℕ) (na : ℕ) (t : bfvar Var) (Ps : Vector (Term Var) n) (y : bfvar Var) (Ts : ULift (Fin n) → BöhmTree Var) :
      hasAsHnf T n Ps.toList y →
      forall (m : ULift (Fin n)), BT Var (Ps.get m.down) (Ts m) →
      BT Var T (BöhmTree.hnf n na t Ts)

--                        λ x .                f      (           x                 x )
def omega_f : Term Var := Term.abs ((Term.bvar 1).app ((Term.bvar 0).app (Term.bvar 0)))
--                            λ f .                f      (ωf          ωf     )
def Ycombinator : Term Var := Term.abs ((Term.bvar 0).app (omega_f.app omega_f))

coinductive is_inf_Ytree : BöhmTree Var → Prop where
  | Is_inf_Ytree T : is_inf_Ytree T → is_inf_Ytree (BöhmTree.hnf 1 0 ⟨Term.bvar 0, by simp⟩ (λ _ ↦ T))

lemma Ycombinator_tree T : is_inf_Ytree T → BT Var Ycombinator (BöhmTree.hnf 1 1 ⟨Term.bvar 0, by simp⟩ (λ _ ↦ T)) := by
  sorry
