import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import src.AndrejBauer.GraphModel
import src.EngelerModel
import src.ChurchRosser
import src.LambdaTheory.Basic

open F_G_equal
open Listing
open Cslib
open LambdaCalculus.LocallyNameless.Untyped
open Term

universe u
variable {Var : Type u}
variable {α : Type} [Listing α]

@[simp]
def subst_rho (ρ : ℕ → Set α) (n : ℕ) (d : Set α) : ℕ → Set α :=
  fun x => if x = n then d else ρ (x)

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

-- 2.7 Substitution
lemma DeBruijnSubst {α : Type} [Listing α]
 {ρ : ℕ → Set α} {σ: Var → Set α} (M P : Term Var):
〚M〛_{subst_rho (DeBruijnShift ρ) 0 〚P〛_{ρ,σ},σ} = 〚M ^ P〛_{ρ,σ} := by
  induction M with
  | bvar n  =>
  unfold open'
  unfold openRec
  cases n
  · simp_all
  · sorry
    -- possible with simp_all of redefine subst_rho
  | fvar x  =>
  have h: 〚(fvar x) ^ P〛_{ρ,σ} = 〚fvar x〛_{ρ,σ} := by grind
  rwa [h]
  | app a b =>
  expose_names
  simp
  have h: 〚(app a b) ^ P〛_{ρ,σ} = 〚app (a ^ P) (b ^ P)〛_{ρ,σ} := by grind
  rwa [h, a_ih, a_ih_1]
  | abs e   =>
  sorry -- SORRY
  -- expose_names
  -- simp_all
  -- unfold open' at *
  -- unfold openRec at *
  -- unfold openRec at *
  -- cases e
  -- · simp_all
  --   grind
  -- simp
  -- ext x
  -- constructor
  -- · intro h
  --   unfold subst_rho at h
  --   simp at h

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
    -- Note that this could also be proven by showing that this function rewrites to S ( apply ∘ A ) B
    -- showing that S is continuous and then using the fact that composition is continuous
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

variable [HasFresh Var]

lemma interp_ξ [fresh : HasFresh Var] {xs : Finset Var}
(h: ∀ x ∉ xs, 〚M ^ fvar x〛_{ρ,σ} = 〚N ^ fvar x〛_{ρ,σ}) : 〚M.abs〛_{ρ,σ} = 〚N.abs〛_{ρ,σ} := by
  -- have h2:= @redex_abs_cong _ M --- A GENERAL BIG SORRY
  have h1:= fresh.fresh_notMem xs
  specialize h (fresh.fresh xs) h1
  rw [<-DeBruijnSubst, <-DeBruijnSubst] at h
  simp at h
  -- have h:= DeBruijnSubst M
  simp_all
  unfold G
  ext x
  constructor
  · rintro ⟨ b , β, h1, h2 ⟩
    use b, β
    constructor
    · assumption
    · simp_all
      have hmaybe2: (toSet β) = (σ (Cslib.fresh xs)) := by sorry
      rwa [hmaybe2, <-h, <-hmaybe2]
  · rintro ⟨ b , β, h1, h2 ⟩
    use b, β
    constructor
    · assumption
    · simp_all
      have hmaybe2: (toSet β) = (σ (Cslib.fresh xs)) := by sorry
      rwa [hmaybe2, h, <-hmaybe2]


---------------------------------------------------------------------------------

-- Prove Interp is a model theory

open LT

def InterpRel (ρ : ℕ → Set α) (σ : Var → Set α)
 (M N : Term Var) : Prop := Interp ρ σ M = Interp ρ σ N

instance : LambdaTheory (fun M N => @InterpRel _ _ _ ρ σ M N) where
  beta := by
    intro M N h
    unfold InterpRel
    induction h
    expose_names
    simp
    rw [F_G_eq_id]
    apply DeBruijnSubst
    apply DeBruijnSubst_continuous
  xi := by
    intros M N xs
    unfold InterpRel at *
    apply interp_ξ
  app:= by
    intros M N P Q hMN hPQ
    unfold InterpRel at *
    unfold Interp
    rw [hMN, hPQ]
  refl := by
    intros M
    unfold InterpRel
    rfl
  trans := by
    intros M N Q hMN hNQ
    unfold InterpRel at *
    grind
  sym := by
    intros M N h
    unfold InterpRel at *
    symm
    assumption

--------------------------------------------------------------------------------
-- Prove beta-equvialence entails model interpretation equality


-- Prove beta-step entails model interpretation equality
lemma beta_step_imp_interp_eq {ρ : ℕ → Set α} {σ : Var → Set α}
{A B : Term Var} (h: A ⭢βᶠ B) : 〚A〛_{ρ,σ} = 〚B〛_{ρ,σ} := by
  induction h
  · expose_names
    cases M with
    | app a b =>
    obtain ⟨hM,hb⟩:= h
    expose_names
    simp only [Interp]
    rw [F_G_eq_id]
    apply DeBruijnSubst
    apply DeBruijnSubst_continuous
    | _ => contradiction
  · expose_names
    simp
    rw [a_ih]
  · expose_names
    simp
    rw [a_ih]
  · expose_names
    simp at h
    apply interp_ξ a_ih

-- Prove multi-beta-step entails model interpretation equality
lemma multi_beta_imp_interp_eq {ρ : ℕ → Set α} {σ : Var → Set α} (A B : Term Var):
(A ↠βᶠ B) -> 〚 A 〛_{ρ,σ} = 〚 B 〛_{ρ,σ}
 := by
 intro h
 induction h
 · rfl
 · expose_names
   rw [a_ih]
   apply (beta_step_imp_interp_eq h_1)


variable [DecidableEq Var]

-- Prove beta-equality entails model interpretation equality
lemma beta_eq_imp_interp_eq {ρ : ℕ → Set α} {σ : Var → Set α} (A B : Term Var):
(A ≡β B) -> 〚 A 〛_{ρ,σ} = 〚 B 〛_{ρ,σ}
  := by
  intro h
  obtain ⟨Q,⟨hmA, hmB⟩⟩:= (common_reduct_of_BetaEquiv A B h)
  rw [multi_beta_imp_interp_eq _ _ hmB]
  exact multi_beta_imp_interp_eq _ _ hmA
