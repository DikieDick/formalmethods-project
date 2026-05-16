import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Mathlib.Tactic
import Coinductive
import src.ChurchRosser

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

def nfoldOpen : List Var → Term Var → Term Var
| [], T => T
| a :: as, T => nfoldOpen as (T.open' (Term.fvar a))

def nfoldApp : List (Term Var) → Term Var → Term Var
| [], T => T
| a :: as, T => nfoldApp as (T.app a)

inductive List.BetaEquiv : List (Term Var) → List (Term Var) → Prop where
  | base : [].BetaEquiv []
  | step as bs T₁ T₂ : T₁.BetaEquiv T₂ → as.BetaEquiv bs → (T₁ :: as).BetaEquiv (T₂ :: bs)

def bfvar (Var : Type u) := { v : Term Var // (exists n, v = Term.bvar n) ∨ (exists v', v = Term.fvar v') }

-- Reduction does not affect the number of leading abstractions, the head variable, or the number of arguments of the head-variable
lemma reduction_preservation_fvar (n m : ℕ) (y z : bfvar Var) (Ps Qs : List (Term Var)) :
    (nfoldAbs n (nfoldApp Ps y.val)).multiBeta (nfoldAbs m (nfoldApp Qs z.val)) →
    n = m ∧ y = z ∧ Ps.BetaEquiv Qs := by
  intros h
  sorry

lemma reduction_preservation_fvar' (n : ℕ) (y : bfvar Var) (Ps : List (Term Var)) (p : Term Var):
    (nfoldAbs n (nfoldApp Ps y.val)).multiBeta p →
    exists Qs,
    p.BetaEquiv (nfoldAbs n (nfoldApp Qs y.val)) ∧ Ps.BetaEquiv Qs := by
  intros h
  sorry

-- Lemma 3.5
lemma hnfs_similar_fvar [HasFresh Var] [DecidableEq Var] (n m : ℕ) (y z : bfvar Var) (Ps Qs : List (Term Var)) (M : Term Var) :
    M.BetaEquiv (nfoldAbs n (nfoldApp Ps y.val)) →
    M.BetaEquiv (nfoldAbs m (nfoldApp Qs z.val)) →
    n = m ∧ y = z ∧ Ps.BetaEquiv Qs := by
  intros hn hm
  apply Relation.EqvGen.symm _ _ at hn
  have := Relation.EqvGen.trans _ _ _ hn hm
  obtain ⟨p, h₁, h₂⟩ := (Term.common_reduct_of_BetaEquiv _ _ this)
  have ⟨Qs₁, hp₁, hps₁⟩ := reduction_preservation_fvar' _ _ _ _ h₁
  have ⟨Qs₂, hp₂, hps₂⟩ := reduction_preservation_fvar' _ _ _ _ h₂
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

def hasAsHnf (T : Term Var) (n : ℕ) (Ps : List (Term Var)) (y : bfvar Var) :=
  let T' := nfoldAbs n (nfoldApp Ps y.val) ; isHeadNormal T' ∧ T.BetaEquiv T'

-- Definition 3.7
coinductive BT (Var : Type u) : Term Var → List Var → BöhmTree Var → Prop where
  | no_hnf (T : Term Var) (L : List Var) :
      ¬(exists n Ps y, hasAsHnf T n Ps y) →
      BT Var T L BöhmTree.no_hnf
  | hnf_bvar (term : Term Var) (abs_vars : List Var) (term_base_var : ℕ) (term_apps : List (Term Var)) (subtrees : ULift (Fin term_apps.length) → BöhmTree Var) (L : List Var) :
      hasAsHnf term abs_vars.length term_apps ⟨Term.bvar term_base_var, by simp⟩ →
      (forall (m : ULift (Fin term_apps.length)), BT Var (nfoldOpen (abs_vars ++ L) term_apps[m.down]) (abs_vars ++ L) (subtrees m)) →
      BT Var term L (BöhmTree.hnf term_apps.length abs_vars.length ⟨Term.bvar term_base_var, by simp⟩ subtrees)
  | hnf_bound_fvar (term : Term Var) (abs_vars : List Var) (term_base_var : Var) (term_apps : List (Term Var)) (subtrees : ULift (Fin term_apps.length) → BöhmTree Var) (L : List Var) (L_index : Fin L.length) :
      hasAsHnf term abs_vars.length term_apps ⟨Term.fvar term_base_var, by simp⟩ →
      L.get L_index = term_base_var →
      (forall (m : ULift (Fin term_apps.length)), BT Var (nfoldOpen (abs_vars ++ L) term_apps[m.down]) (abs_vars ++ L) (subtrees m)) →
      BT Var term L (BöhmTree.hnf term_apps.length abs_vars.length ⟨Term.bvar L_index, by simp⟩ subtrees)
  | hnf_free_fvar (term : Term Var) (abs_vars : List Var) (term_base_var : Var) (term_apps : List (Term Var)) (subtrees : ULift (Fin term_apps.length) → BöhmTree Var) (L : List Var) :
      hasAsHnf term abs_vars.length term_apps ⟨Term.fvar term_base_var, by simp⟩ →
      (¬∃ L_index, L.get L_index = term_base_var) →
      (forall (m : ULift (Fin term_apps.length)), BT Var (nfoldOpen (abs_vars ++ L) term_apps[m.down]) (abs_vars ++ L) (subtrees m)) →
      BT Var term L (BöhmTree.hnf term_apps.length abs_vars.length ⟨Term.fvar term_base_var, by simp⟩ subtrees)

@[partial_fixpoint_monotone]
theorem hnf_mono (t : bfvar Var) : monotone fun f ↦ BöhmTree.hnf 1 0 t fun _ ↦ f := by
  intro T T' Hle
  simp
  apply CoInd.le_leN
  rintro ⟨n⟩; simp [CoIndN.le]
  simp [CoIndN.le, PF.unpack]
  right
  constructor <;> try rfl
  grind [coherent, CoInd.leN_le, monotone]

def inf_Ytree : BöhmTree Var :=
  .hnf 1 0 ⟨Term.bvar 0, by simp⟩ (λ _ ↦ inf_Ytree)
partial_fixpoint
def Ytree : BöhmTree Var := .hnf 1 1 ⟨Term.bvar 0, by simp⟩ (λ _ ↦ inf_Ytree)

def omega_f := @Term.abs Var ((Term.bvar 1).app ((Term.bvar 0).app (Term.bvar 0)))
def Ycombinator := @Term.abs Var ((Term.bvar 0).app (omega_f.app omega_f))
def omega_f_free (f : Var) := @Term.abs Var ((Term.fvar f).app ((Term.bvar 0).app (Term.bvar 0)))

lemma omega_f_beta_f (f : Var) : (omega_f_free f).app (omega_f_free f) ≡β (Term.fvar f).app ((omega_f_free f).app (omega_f_free f)) := by
  constructor
  constructor
  constructor
  · apply Term.LC.abs {f}
    intro x elem
    apply Term.LC.app <;> simp [Term.openRec] <;> constructor <;> constructor
  · simp [omega_f_free]
    apply Term.LC.abs {f}
    intro x elem
    apply Term.LC.app <;> simp [Term.openRec] <;> constructor <;> constructor

lemma Ycombinator_tree [fresh : HasFresh Var] : BT Var Ycombinator [] Ytree := by
  have f := fresh.fresh ∅
  apply BT.hnf_bvar Var Ycombinator [f] 0 [omega_f.app omega_f]
  · constructor
    · apply isHeadNormal.step
      apply isHeadNormal.base
      apply isHeadNormalApp.step
      apply isHeadNormalApp.base_bound
    · simp [nfoldAbs, nfoldApp]
      nth_rw 1 [Ycombinator]
  · intros m
    simp [nfoldOpen, Term.open', Term.openRec, omega_f]
    rw [←omega_f_free]
    apply BT.coinduct Var (fun term L tree ↦ tree = inf_Ytree ∧ L = [f] ∧ term = (omega_f_free f).app (omega_f_free f))
    · rintro term L tree ⟨prop_tree, prop_L, prop_term⟩
      right ; right ; left
      use [], f, [(omega_f_free f).app (omega_f_free f)], (λ _ ↦ inf_Ytree), ⟨0, by rw [prop_L] ; simp⟩
      simp
      constructor
      · simp [hasAsHnf, nfoldAbs, nfoldApp]
        constructor
        · apply isHeadNormal.base
          apply isHeadNormalApp.step
          apply isHeadNormalApp.base_free
        · rw [prop_term]
          exact omega_f_beta_f f
      · cases prop_L
        simp [prop_tree]
        constructor
        · simp [nfoldOpen, Term.open', Term.openRec, omega_f_free]
        · nth_rw 1 [inf_Ytree]
    · simp

lemma BT_congr_app (M P Q : Term Var) (h : BT Var P = BT Var Q) : BT Var (M.app P) = BT Var (M.app Q) := by

  sorry
