import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import src.AndrejBauer.GraphModel
import src.EngelerModel
import src.ChurchRosser
import src.LambdaTheory.Basic
import src.LCresults

open F_G_equal
open Listing
open Cslib
open LambdaCalculus.LocallyNameless.Untyped
open Term

universe u
variable {Var : Type u} [DecidableEq Var] [HasFresh Var]
variable {α : Type} [Listing α]

@[simp]
def subst_rho (ρ : ℕ → Set α) (n : ℕ) (d : Set α) : ℕ → Set α :=
  fun x => if x = n then d else ρ (x)

@[simp]
def subst_sigma (σ : Var → Set α) (x : Var) (d : Set α) : Var → Set α :=
  fun y => if y = x then d else σ y

@[simp]
def DeBruijnShift (ρ : ℕ → Set α ): ℕ → Set α :=
  fun n => ρ (n - 1)

@[simp]
def Interp (ρ : ℕ → Set α) (σ: Var → Set α) : Term Var → Set α
| fvar x  => (σ x)
| bvar n  => (ρ n)
| app a b => (F (Interp ρ σ a) (Interp ρ σ b))
| Term.abs e   =>  G (fun d => (Interp (subst_rho (DeBruijnShift ρ) 0 d) σ e) )

variable {ρ : ℕ → Set α}
variable {σ : Var → Set α}
variable {M N: Term Var}

notation "〚"M"〛_{"ρ","σ"}" => Interp ρ σ M

def K : Term Var := abs (abs $ bvar 1) -- λxy.x
def I : Term Var := abs (bvar 0)

-- We interp our I and K to see if our definition is well-defined according to our paper
-- Example 3.1
lemma interp_id :
〚 I 〛_{ρ,σ} = {x | ∃ b, ∃ (β : α), x = (pair b β) ∧ b ∈ toSet β}
 := by
  unfold I Interp G
  ext x
  constructor
  · intro h
    obtain ⟨b, ⟨β, ⟨h₁, h₂⟩⟩⟩ := h
    use b, β
    constructor
    · assumption
    · dsimp [Interp] at h₂
      assumption
  · intro h
    obtain ⟨b, ⟨β, ⟨h₁, h₂⟩⟩⟩ := h
    use b, β
    constructor
    · assumption
    · dsimp [Interp]
      assumption

lemma interp_K:
〚 K 〛_{ρ,σ} = {x | ∃ β γ c, x = (pair (pair c γ) β) ∧ c ∈ toSet β}
 := by
  unfold K
  unfold Interp
  unfold G
  ext x
  simp
  constructor
  · intro h
    obtain ⟨b, β, h₁, h₂⟩ := h
    obtain ⟨c, γ, heq, h₂⟩ := h₂
    use β, γ, c
    constructor
    · rwa [heq] at h₁
    · grind
  · intro h
    obtain ⟨β, γ, c, h⟩ := h
    use ((pair c γ)), β
    constructor
    · grind
    · unfold G
      simp
      grind

---------------------------------------------------------------------------------

open GraphModel

lemma env_comm {α : Type} (n : ℕ) (ρ : ℕ → Set α) (d es: Set α) :
  subst_rho (DeBruijnShift (subst_rho ρ n d)) 0 es =
  subst_rho (subst_rho (DeBruijnShift ρ) 0 es) (n + 1) d := by
    ext z _
    cases z with
    | zero => simp
    | succ z => simp


lemma interp_open_rec (M : Term Var) (n : ℕ) (x : Var) (hx : x ∉ M.fv) (d : Set α) (ρ : ℕ → Set α) (σ : Var → Set α) :
  Interp (subst_rho ρ n d) σ M = Interp ρ (subst_sigma σ x d) (openRec n (fvar x) M) := by
  induction M generalizing n ρ with
  | fvar y =>
    simp only [Interp, openRec, subst_sigma, right_eq_ite_iff]
    have : y ≠ x := by grind
    simp [this]
  | bvar m =>
    cases m with
    | zero =>
      cases n with
      | zero =>
        simp [openRec]
      | succ n =>
        simp [openRec]
    | succ m =>
      simp [openRec, Interp]
      by_cases h : n = m + 1
      · subst h
        simp
      · simp [h]
        grind only
  | abs O ih =>
    simp only [openRec, Interp]
    congr 1
    ext es e
    rw [env_comm]
    rw [ih]
    simp [fv] at hx
    assumption
  | app O P ih₁ ih₂ =>
    simp only [openRec, Interp]
    congr 1
    · grind
    · grind

-- Interp of locally closed M does not change under different ρ
lemma interp_rho_indep (M : Term Var) (ρ₁ ρ₂ : ℕ → Set α) (σ : Var → Set α) (h : M.LC) :
  〚M〛_{ρ₁, σ} = 〚M〛_{ρ₂, σ} := by
  induction h generalizing ρ₁ ρ₂ σ with
  | fvar x => simp only [Interp]
  | abs L O h ih =>
    simp only [Interp]
    congr 1
    ext ds d
    let exl_vars := O.fv ∪ L
    have ⟨f, f_fresh⟩ := fresh_exists exl_vars
    have h_f_notin_fvO : f ∉ O.fv := by grind only [= Finset.mem_union]
    have h_f_notin_L : f ∉ L := by grind only [= Finset.mem_union]
    specialize ih f h_f_notin_L (DeBruijnShift ρ₁) (DeBruijnShift ρ₂) (subst_sigma σ f ds)
    rw [interp_open_rec O 0 f h_f_notin_fvO ds (DeBruijnShift ρ₁) σ]
    rw [interp_open_rec O 0 f h_f_notin_fvO ds (DeBruijnShift ρ₂) σ]
    simp [open'] at ih
    rw [ih]
  | @app O P hO hP ih₁ ih₂ =>
    simp only [Interp]
    rw [ih₁ _ _, ih₂ _ _]

-- 2.7 Substitution
lemma DeBruijnSubst (M P : Term Var) (h : P.LC) (n : ℕ) (ρ : ℕ → Set α) (σ : Var → Set α) :
  〚M〛_{subst_rho ρ n 〚P〛_{ρ,σ}, σ} = 〚openRec n P M〛_{ρ,σ} := by
  induction M generalizing n ρ with
  | bvar m =>
    simp [openRec, Interp]
    by_cases h : n = m
    · simp only [h, ↓reduceIte]
    · simp [h]
      intro h; have h := h.symm
      contradiction
  | fvar x  => simp [Interp, openRec]
  | app a b ih₁ ih₂ =>
    simp [openRec, Interp]
    rw [ih₁, ih₂]
  | abs e ih =>
    simp [openRec, Interp]
    congr 1
    ext ds d
    rw [env_comm]
    let exl_vars := e.fv ∪ P.fv
    have ⟨f, f_fresh⟩ := fresh_exists exl_vars
    have := interp_rho_indep P ρ (subst_rho (DeBruijnShift ρ) 0 ds) σ h
    rw [this, ih (n + 1) (subst_rho (DeBruijnShift ρ) 0 ds)]

lemma G_cont (f : Set α → Set α → Set α) (h : ∀ S : Set α, continuous (f S)) :
continuous fun S ↦ G (fun T ↦ f S T) := by
  sorry -- SORRY

lemma DeBruijnSubst_continuous (P : Term Var) (i : ℕ)
(ρ : ℕ → Set α) (σ : Var → Set α) :
continuous fun d ↦ 〚P〛_{subst_rho (DeBruijnShift ρ) i d,σ} := by
  induction P generalizing i ρ with
  | bvar n =>
    simp
    by_cases h: n = i <;> simp [h]
    · apply GraphModel.continuous_id
  | fvar x => apply GraphModel.continuous_const
  | app N Q ihN ihQ =>
    simp
    have (A : Set α → Set α) (B : Set α → Set α) (hA : continuous A) (hB : continuous B):
      continuous fun d ↦ apply (A d) (B d) := by
      apply continuous₂_compose
      · exact hA
      · exact hB
      exact apply.continuous₂
    unfold F
    apply this
    · apply ihN
    · apply ihQ
  | abs Q ih =>
    unfold Interp
    apply G_cont
    intro a
    specialize ih 0 (subst_rho (DeBruijnShift ρ) i a)
    exact ih

---------------------------------------------------------------------------------

lemma interp_ξ (xs : Finset Var)
(h: ∀ x ∉ xs, ∀ (ρ : ℕ → Set α) (σ : Var → Set α),
〚M ^ fvar x〛_{ρ,σ} = 〚N ^ fvar x〛_{ρ,σ}) : 〚M.abs〛_{ρ,σ} = 〚N.abs〛_{ρ,σ}
:= by
  dsimp [Interp]
  congr 2
  ext d a
  let exl_vars := M.fv ∪ N.fv ∪ xs
  have ⟨f, f_fresh⟩ := fresh_exists exl_vars

  have hM : f ∉ M.fv := by grind
  have hN : f ∉ N.fv := by grind
  have hxs : f ∉ xs := by grind

  rw [interp_open_rec M 0 f hM d (DeBruijnShift ρ) σ]
  rw [interp_open_rec N 0 f hN d (DeBruijnShift ρ) σ]
  specialize h f hxs (DeBruijnShift ρ) (subst_sigma σ f d)
  simp [open'] at h
  rw [h]

---------------------------------------------------------------------------------

-- Prove Interp is a λ-theory

open LT

def InterpRel (M N : Term Var) : Prop :=
  ∀ (ρ : ℕ → Set α) (σ : Var → Set α), 〚M〛_{ρ,σ} = 〚N〛_{ρ,σ}

-- Prove beta-step entails model interpretation equality
lemma beta_step_imp_interp_eq (ρ : ℕ → Set α) (σ : Var → Set α)
{A B : Term Var} (h: A ⭢βᶠ B) : 〚A〛_{ρ,σ} = 〚B〛_{ρ,σ} := by
  induction h generalizing ρ σ
  · expose_names
    cases M with
    | app a b =>
      obtain ⟨hM,hb⟩:= h
      expose_names
      simp only [Interp]
      rw [F_G_eq_id]
      · change 〚M〛_{subst_rho (DeBruijnShift ρ) 0 〚b〛_{ρ,σ}, σ} = 〚M⟦0 ↝ b⟧〛_{ρ,σ}
        have hb_shift : 〚b〛_{ρ, σ} = 〚b〛_{DeBruijnShift ρ, σ} := interp_rho_indep b _ _ _ hb
        rw [hb_shift]

        have h_reduced_LC : (M⟦0 ↝ b⟧).LC := by exact LC_of_absLC_and_LC_term M b hM hb

        have rhs_shift : 〚M⟦0 ↝ b⟧〛_{ρ, σ} = 〚M⟦0 ↝ b⟧〛_{DeBruijnShift ρ, σ} :=
          interp_rho_indep (M⟦0 ↝ b⟧) _ _ _ h_reduced_LC

        rw [rhs_shift]

        apply DeBruijnSubst M b hb 0 (DeBruijnShift ρ) σ
      · apply DeBruijnSubst_continuous
    | _ => contradiction
  · expose_names
    simp
    rw [a_ih]
  · expose_names
    simp
    rw [a_ih]
  · expose_names
    simp at h
    apply interp_ξ xs
    · intro x hx ρ σ
      apply a_ih x hx ρ σ

-- Prove multi-beta-step entails model interpretation equality
lemma multi_beta_imp_interp_eq (ρ : ℕ → Set α) (σ : Var → Set α) (A B : Term Var):
(A ↠βᶠ B) -> 〚 A 〛_{ρ,σ} = 〚 B 〛_{ρ,σ}
 := by
 intro h
 induction h generalizing ρ σ
 · rfl
 · expose_names
   rw [a_ih]
   apply (beta_step_imp_interp_eq ρ σ h_1)

-- Prove beta-equality entails model interpretation equality
lemma beta_eq_imp_interp_eq (ρ : ℕ → Set α) (σ : Var → Set α) (A B : Term Var):
(A ≡β B) -> 〚 A 〛_{ρ,σ} = 〚 B 〛_{ρ,σ}
  := by
  intro h
  obtain ⟨Q,⟨hmA, hmB⟩⟩:= (common_reduct_of_BetaEquiv A B h)
  rw [multi_beta_imp_interp_eq ρ σ _ _ hmB]
  exact multi_beta_imp_interp_eq ρ σ _ _ hmA

instance : LambdaTheory (fun (M N : Term Var) => @InterpRel Var α _ M N) where
  beta M N h ρ σ := by
    apply beta_eq_imp_interp_eq
    apply Relation.EqvGen.rel
    apply Xi.base h
  xi M N xs h ρ σ := by
    apply interp_ξ xs h
  app M N P Q hMN hPQ ρ σ:= by
    unfold Interp
    rw [hMN, hPQ]
  refl M ρ σ := by rfl
  trans M N Q hMN hNQ ρ σ := (hMN ρ σ).trans (hNQ ρ σ)
  sym M N h ρ σ := (h ρ σ).symm

--------------------------------------------------------------------------------
-- Prove beta-equvialence entails model interpretation equality
