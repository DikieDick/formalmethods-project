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

lemma BetaEquiv_open {l : Var} {t₁ t₂ : Term Var} (h : t₁ ≡β t₂) : (t₁ ^ fvar l) ≡β t₂ ^ fvar l := by
  induction h
  case rel a b h =>
    apply Relation.EqvGen.rel
    induction h <;> try grind
    case a.abs t₁ t₂ t₃ t₄ s h₁ h₂ =>
      apply Term.FullBeta.step_open_cong_l _ _ _ s _ (by constructor)
      intro s hs
      specialize h₁ s hs
      specialize h₂ s hs
      generalize eq : fvar s = fvar_s
      constructor
      sorry
  case refl _ => apply Relation.EqvGen.refl
  case symm _ _ _ h => apply Relation.EqvGen.symm _ _ h
  case trans _ _ _ _ _ h₁ h₂ => apply Relation.EqvGen.trans _ _ _ h₁ h₂

lemma nfoldopen_preserves_beta (t₁ t₂ : Term Var) (L : List Var) : (t₁ ≡β t₂) → (nfoldOpen L t₁) ≡β (nfoldOpen L t₂) := by
  intro h
  induction L generalizing t₁ t₂
  case nil => exact h
  case cons l L ih => exact ih _ _ (BetaEquiv_open h)

-- Lemma 3.9
lemma BT_eq_of_BetaEquiv (M N : Term Var) (T1 T2 : BöhmTree Var) (L : List Var) (h_dis : L.Nodup) (hMN : M.BetaEquiv N) (h1 : BT M L T1) (h2 : BT N L T2) : T1 = T2 := by
  ext n
  induction n generalizing M N T1 T2 L with
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
    | hnf term_1 abs_vars_1 term_base_var_1 num_apps_1 term_apps_1 subtrees_1 L_1 h_hnf_1 h_distinct_1 h_L_1 =>
      cases h2 with
      | no_hnf _ h2 =>
        have eqHnf := HnfEq_of_BetaEquiv M N hMN
        grind
      | hnf term_2 abs_vars_2 term_base_var_2 num_apps_2 term_apps_2 subtrees_2 L_2 h_hnf_2 h_distinct_2 h_L_2 =>
        obtain ⟨_, h_equiv_1⟩ := h_hnf_1
        obtain ⟨_, h_equiv_2⟩ := h_hnf_2
        have hMN_hnf : M.BetaEquiv _ := Relation.EqvGen.trans _ _ _ hMN h_equiv_2
        -- We apply Lemma 3.5
        have ⟨h_num_abs_eq, h_var_eq, h_apps_BetaEquiv⟩ := hnfs_similar_fvar _ _ _ _ _ _ M h_equiv_1 hMN_hnf
        have h_num_apps : num_apps_1 = num_apps_2 := by
          have := helper h_apps_BetaEquiv
          cases term_apps_1
          cases term_apps_2
          simp_all
        subst h_num_apps
        have h_num_apps_1 : num_apps_1 = term_apps_1.toArray.toList.length := by simp
        have h_num_apps_2 : num_apps_1 = term_apps_2.toArray.toList.length := by simp
        simp [BöhmTree.hnf, BöhmTree.fold, CoInd.fold, PF.map, PF.pack]
        congr 1
        · congr
        · ext x
          unfold PF.P instPFBöhmTreeF at x
          simp at x
          let new_L : List Var := abs_vars_1 ++ L
          have new_L_nodup : new_L.Nodup := by grind [(nodup_fvar _).mp]
          apply ih (nfoldOpen new_L (term_apps_1[x.down])) (nfoldOpen new_L (term_apps_2[x.down])) _ _ new_L
          · exact new_L_nodup
          · apply nfoldopen_preserves_beta
            exact BetaEquivHelper h_apps_BetaEquiv x.down
          · grind only
          · apply BT_L_sub _ _ _ _ _ _ (h_L_2 _)
            grind [(nodup_fvar _).mp]
            exact new_L_nodup


def ThBT (M N : Term Var) : Prop :=
  ∀ T1 T2 L, L.Nodup → BT M L T1 → BT N L T2 → T1 = T2

-- We prove that ThBT defines a λ-theory
instance instThBT : @LambdaTheory Var (@ThBT Var _) where
  beta M N := by
    intro h T1 T2 L hL BT1 BT2
    apply BT_eq_of_BetaEquiv <;> try assumption
    apply Relation.EqvGen.rel
    apply Xi.base
    assumption
  refl M := by
    intro T1 T2 L hL BT1 BT2
    apply BT_eq_of_BetaEquiv <;> try assumption
    apply Relation.EqvGen.refl
  sym M N := by
    intro h T1 T2 L hL BT1 BT2
    exact (h T2 T1 L hL BT2 BT1).symm
  trans M N O := by
    unfold ThBT
    intro h₁ h₂ T1 T2 L hL BT1 BT2
    obtain ⟨TN, BTN⟩ := exists_BT_for_term N L hL
    rw [h₁ T1 TN L hL BT1 BTN, h₂ TN T2 L hL BTN BT2]
  -- Requires a bit of work
  xi M N xs h := by
    unfold ThBT at *
    intros T1 T2 L hL BT1 BT2
    sorry
  app M N P Q := by
    sorry
