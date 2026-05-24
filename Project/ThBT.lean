import Project.LambdaTheory.Basic
import Project.BetaEquiv
import Project.Bohm_Tree
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

open Cslib
open LambdaCalculus.LocallyNameless.Untyped

open Coinductive

open Term
namespace LT

universe u

variable {Var : Type u} [HasFresh Var] [DecidableEq Var]

lemma helper {Var : Type u} {as bs : List (Term Var)} (h : as.BetaEquiv bs) :
    as.length = bs.length := by
  induction h with
  | base => rfl
  | step as bs T₁ T₂ _ _ ih => simp [ih]

lemma List.BetaEquiv.get_index {Var : Type u} {as bs : List (Term Var)} (h : as.BetaEquiv bs)
    (i : ℕ) (h1 : i < as.length) (h2 : i < bs.length) :
    as.get ⟨i, h1⟩ ≡β bs.get ⟨i, h2⟩ := by
  induction h generalizing i with
  | base =>
    grind only [= List.length_nil]
  | step as bs T₁ T₂ hT habs ih =>
    cases i with
    | zero =>
      exact hT
    | succ i =>
      exact ih i _ _

-- Lemma 3.9
/-
lemma BT_eq_of_BetaEquiv (M N : Term Var) (T1 T2 : BöhmTree Var) (hMN : M.BetaEquiv N) (h1 : BT Var M T1) (h2 : BT Var N T2) : T1 = T2 := by
  ext n
  induction n generalizing M N T1 T2 with
  | zero => rfl
  | succ n ih =>
    cases h1 with
    | no_hnf _ h1 =>
      cases h2 with
      | no_hnf _ h2 =>
        simp
      | hnf =>
        have eqHnf := HnfEq_of_BetaEquiv N M hMN.symm
        grind -- contradiction
    | hnf term num_children term_num_abs term_base_var term_apps subtrees h_1 h_sub1 =>
      cases h2 with
      | no_hnf _ h2 =>
        have eqHnf := HnfEq_of_BetaEquiv M N hMN
        grind
      | hnf term_1 num_children_1 term_num_abs_1 term_base_var_1 term_apps_1 subtrees_1 h_3 h_sub2 =>
        obtain ⟨_, hM_eqv⟩ := h_1
        obtain ⟨_, hN_eqv⟩ := h_3

        have hMN_hnf : M.BetaEquiv _ := Relation.EqvGen.trans _ _ _ hMN hN_eqv
        -- We apply Lemma 3.5
        have ⟨h_num_abs_eq, h_var_eq, h_apps_BetaEquiv⟩ := hnfs_similar_fvar _ _ _ _ _ _ M hM_eqv hMN_hnf
        have h_list_len : term_apps.toList.length = term_apps_1.toList.length := helper h_apps_BetaEquiv
        -- We have equality of the length of the lists that we got from vector.to_list
        have h_len_eq : num_children = num_children_1 := by
          grind

        subst h_num_abs_eq h_var_eq h_len_eq
        simp only [BöhmTree.hnf, BöhmTree.fold, CoInd.fold, PF.map, PF.pack]
        congr
        ext x
        apply ih (term_apps[x.down]) (term_apps_1[x.down]) (subtrees x) (subtrees_1 x)
        · apply List.BetaEquiv.get_index h_apps_BetaEquiv
        · apply h_sub1 x
        · apply h_sub2 x

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

-/
