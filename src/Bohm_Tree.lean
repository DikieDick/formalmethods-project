import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Mathlib.Tactic
import Coinductive
import src.BetaEquiv

open Cslib
open LambdaCalculus.LocallyNameless.Untyped
open Coinductive
open Lean.Order

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
  | hnf (term : Term Var) (num_children : ℕ) (term_num_abs : ℕ) (term_base_var : bfvar Var) (term_apps : Vector (Term Var) num_children) (subtrees : ULift (Fin num_children) → BöhmTree Var) :
      hasAsHnf term term_num_abs term_apps.toList term_base_var →
      (forall (m : ULift (Fin num_children)), BT Var term_apps[m.down] (subtrees m)) →
      BT Var term (BöhmTree.hnf num_children term_num_abs term_base_var subtrees)

--             λ x .                        f      (           x                 x )
def omega_f := Term.abs ((Term.fvar Unit.unit).app ((Term.bvar 0).app (Term.bvar 0)))
--                 λ f .                f      (ωf          ωf     )
def Ycombinator := Term.abs ((Term.bvar 0).app (omega_f.app omega_f))

lemma inf_Ytree_approx (t : bfvar Var) (n n' na : ℕ) (f : ULift (Fin n') → (BöhmTree Var)) : (BöhmTree.hnf n' na t f).approx (n + 1) = BöhmTreeF.hnf n' na t (λ x ↦ (f x).approx n) := by
  simp [BöhmTree.hnf, BöhmTree.fold, CoInd.fold, PF.map, PF.pack]
  rfl

@[partial_fixpoint_monotone]
theorem hnf_mono : monotone fun f ↦ BöhmTree.hnf 1 0 ⟨Term.fvar Unit.unit, by simp⟩ fun _ ↦ f := by
  intro T T' Hle
  simp
  apply CoInd.le_leN
  rintro ⟨n⟩; simp [CoIndN.le]
  simp [CoIndN.le, PF.unpack]
  right
  constructor <;> try rfl
  grind [coherent, CoInd.leN_le, monotone]

def inf_Ytree : BöhmTree Unit :=
  .hnf 1 0 ⟨Term.fvar Unit.unit, by simp⟩ (λ _ ↦ inf_Ytree)
partial_fixpoint

lemma omega_f_beta_f : omega_f.app omega_f ≡β (Term.fvar Unit.unit).app (omega_f.app omega_f) := by
  constructor
  constructor
  constructor
  · apply Term.LC.abs {Unit.unit}
    simp [Finset.mem_singleton]
  · apply Term.LC.abs {Unit.unit}
    simp [Finset.mem_singleton]

lemma Ycombinator_tree : BT Unit (omega_f.app omega_f) (BöhmTree.hnf 1 0 ⟨Term.fvar Unit.unit, by simp⟩ (λ _ ↦ inf_Ytree)) := by
  apply BT.coinduct Unit (fun term tree ↦ tree = inf_Ytree ∧ term = omega_f.app omega_f)
  · rintro term tree ⟨prop_tree, prop_term⟩
    right
    use 1, 0, ⟨Term.fvar Unit.unit, by simp⟩, #v[omega_f.app omega_f], (λ _ ↦ inf_Ytree)
    simp
    constructor
    · simp [hasAsHnf, nfoldAbs, nfoldApp]
      constructor
      · apply isHeadNormal.base
        apply isHeadNormalApp.step
        apply isHeadNormalApp.base_free
      · rw [prop_term]
        exact omega_f_beta_f
    · simp [prop_tree]
      nth_rw 1 [inf_Ytree]
  · simp
    nth_rw 2 [inf_Ytree]
