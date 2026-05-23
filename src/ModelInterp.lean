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

-- [DecidableEq Var]

-- [HasFresh Var]
variable {α : Type} [Listing α]

-- We need to define substition for our bound variables
@[simp]
def subst_ρ (ρ : ℕ → Set α) (n : ℕ) (d : Set α) : ℕ → Set α :=
  fun x => if x = n then d else ρ (x)

-- Make notation for substitution in ρ
variable {n : ℕ}
variable {d : Set α}

notation ρ"["d"./"n"]" => subst_ρ ρ n d

-- We need to define a shifting function in order to use the De Bruijn notation
@[simp]
def DeBruijnShift (ρ : ℕ → Set α ): ℕ → Set α :=
  fun n => ρ (n - 1)

-- We implement the inductive defintion from 2.27 of our model interpretation of untyped lambda terms
@[simp]
def Interp (ρ : ℕ → Set α) (σ: Var → Set α) : Term Var → Set α
| fvar x  => (σ x)
| bvar n  => (ρ n)
| app a b => (F (Interp ρ σ a) (Interp ρ σ b))
| Term.abs e   =>  G (fun d => (Interp ((DeBruijnShift ρ)[d./0]) σ e) )

variable {ρ : ℕ → Set α}
variable {σ : Var → Set α}
variable {M N: Term Var}

notation "〚"M"〛_{"ρ","σ"}" => Interp ρ σ M

def K : Term Var := abs (abs $ bvar 1) -- λxy.x
def I : Term Var := abs (bvar 0) -- λx.x

-- We interp our I and K to see if our definition is well-defined according to our paper
-- Example 3.1
lemma interp_I :
〚 I 〛_{ρ,σ} = {x | ∃ b, ∃ (β : α), x = (pair b β) ∧ b ∈ toSet β}
 := by
  unfold I Interp G
  ext x
  constructor
  · rintro ⟨b, ⟨β, ⟨h₁, h₂⟩⟩⟩
    use b, β
    simp at h₂
    constructor <;> assumption
  · rintro ⟨b, ⟨β, ⟨h₁, h₂⟩⟩⟩
    use b, β
    constructor <;> assumption

lemma interp_K:
〚 K 〛_{ρ,σ} = {x | ∃ β γ c, x = (pair (pair c γ) β) ∧ c ∈ toSet β}
 := by
  unfold K Interp G
  ext x
  simp
  constructor
  · rintro  ⟨b, β, h₁, ⟨c, γ, heq, h₂⟩⟩
    use β, γ, c
    constructor
    · rwa [heq] at h₁
    · grind
  · intro  ⟨β, γ, c, h⟩
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
〚M〛_{ ((DeBruijnShift ρ)[〚P〛_{ρ,σ} ./ 0]) , σ} = 〚M ^ P〛_{ρ,σ} := by
  induction M with
  | bvar n  =>
  unfold open'
  unfold openRec
  cases n
  · simp_all
  · sorry
  | fvar x  =>
  have h: 〚(fvar x) ^ P〛_{ρ,σ} = 〚fvar x〛_{ρ,σ} := by grind
  rwa [h]
  | app a b =>
  expose_names
  simp
  have h: 〚(app a b) ^ P〛_{ρ,σ} = 〚app (a ^ P) (b ^ P)〛_{ρ,σ} := by grind
  rwa [h, a_ih, a_ih_1]
  | abs e   =>
  sorry


lemma G_cont (f : Set α → Set α → Set α) (h : ∀ S : Set α, continuous (f S)) :
continuous fun S ↦ G (fun T ↦ f S T) := by
  sorry

lemma DeBruijnSubst_continuous (P : Term Var) (i : ℕ)
(ρ : ℕ → Set α) (σ : Var → Set α) :
continuous fun d ↦ 〚P〛_{ ((DeBruijnShift ρ)[d ./ i]) , σ} := by
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
    exact ih 0 ((DeBruijnShift ρ)[a ./ i])

---------------------------------------------------------------------------------
-- Define how opening and closing related
variable [DecidableEq Var]

-- We now need to define substition for our free variables
@[simp]
def subst_σ (σ : Var → Set α) (x : Var) (d : Set α) : Var → Set α :=
  fun y => if y = x then d else σ (y)

-- Make notation for substitution in σ
variable {x : Var}
notation σ"["d"/."x"]" => subst_σ σ x d

-- Prove how opening a term under our interpretation relates to substitution in σ
lemma interp_open_rec (M : Term Var) (n : ℕ) (x : Var)
(hx : x ∉ M.fv) (d : Set α) (ρ : ℕ → Set α) (σ : Var → Set α) :
〚M〛_{(ρ)[d ./ n] , σ} = 〚(openRec n (fvar x) M)〛_{ρ, (σ)[d /. x] }:= by
  induction M generalizing n ρ with
  | fvar y =>
    simp only [Interp, openRec, subst_σ, right_eq_ite_iff]
    have : y ≠ x := by grind
    simp [this]
  | bvar m =>
    cases m with
    | zero =>
      cases n <;> simp [openRec]
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
    have env_comm : ( DeBruijnShift (ρ [d ./ n]    ) )[es ./ 0] =
                    ( ( (DeBruijnShift ρ)[es ./ 0] ) )[d ./ n+1] := by
      ext z _
      cases z <;> simp
    rw [env_comm,ih]
    simp [fv] at hx
    assumption
  | app O P ih₁ ih₂ =>
    simp only [openRec, Interp]
    congr 1 <;> grind

lemma helper {M P: Term Var} {β : α } (hx : x ∉ M.fv):
〚M⟦1 ↝ P⟧〛_{subst_ρ (DeBruijnShift ρ) 0 (toSet β),σ} =
〚M⟦1 ↝ fvar x⟧〛_{  (subst_ρ  (DeBruijnShift (DeBruijnShift ρ)) 0 (toSet β)), σ[〚P〛_{ρ,σ}/.x]}
 := by
  induction M generalizing σ ρ with
  | fvar y =>
    simp only [Interp, openRec, subst_σ,right_eq_ite_iff]
    grind
  | bvar m =>
    simp only [Interp, openRec]
    by_cases h: 1 = m
    · rw [h]
      simp [DeBruijnShift]
      sorry
    · have h₁ : (if 1 = m then P else bvar m) = bvar m := by grind
      have h₂ : (if 1 = m then fvar x else bvar m)  = bvar m := by grind
      rw [h₁, h₂]
      simp
      sorry
  | abs O ih =>
    simp only [openRec, Interp]
    congr 1
    ext es e
    sorry

    -- have env_comm : ( DeBruijnShift ((DeBruijnShift ρ) [toSet β./0]    ) )[es ./ 0] =
    --                 ( ( (DeBruijnShift (DeBruijnShift ρ))[toSet β./0] ) )[es ./ 0] := by

    --   ext z _
    --   cases z <;> simp


    -- rw [env_comm]
    -- simp [fv] at hx
    -- specialize (@ih ρ σ hx)
    -- sorry
  | app O P ih₁ ih₂ =>
    simp only [openRec, Interp]
    congr 1 <;> grind


-- 2.7 Substitution
lemma DeBruijnSubst1 {α : Type} [Listing α]
 {ρ : ℕ → Set α} {σ: Var → Set α} (M P : Term Var):
〚M〛_{ ((DeBruijnShift ρ)[〚P〛_{ρ,σ} ./ 0]) , σ} = 〚M ^ P〛_{ρ,σ} := by
  induction M with
  | bvar n  =>
  unfold open'
  unfold openRec
  cases n
  · simp_all
  · sorry
  | fvar x  =>
  have h: 〚(fvar x) ^ P〛_{ρ,σ} = 〚fvar x〛_{ρ,σ} := by grind
  rwa [h]
  | app a b =>
  expose_names
  simp
  have h: 〚(app a b) ^ P〛_{ρ,σ} = 〚app (a ^ P) (b ^ P)〛_{ρ,σ} := by grind
  rwa [h, a_ih, a_ih_1]
  | abs e   =>
  rw [interp_open_rec e.abs 0 ?_ _ _ (DeBruijnShift ρ) σ]
  unfold open' openRec
  simp
  ext x
  constructor
  · rintro  ⟨b, β, h₁, h₂⟩
    use b, β
    constructor
    · assumption
    · simp_all
      rw [helper]
      apply h₂
      sorry
  · intro  ⟨b, β, h₁, h₂⟩
    use b, β
    constructor
    · assumption
    · simp_all
      rw [helper] at h₂
      apply h₂
      sorry
  sorry
  sorry

---------------------------------------------------------------------------------
variable [HasFresh Var]

lemma interp_ξ (xs : Finset Var)
(h: ∀ x ∉ xs, ∀ (ρ : ℕ → Set α) (σ : Var → Set α),
〚M ^ fvar x〛_{ρ,σ} = 〚N ^ fvar x〛_{ρ,σ}) :
〚M.abs〛_{ρ,σ} = 〚N.abs〛_{ρ,σ}
:= by
  dsimp [Interp]
  congr 2
  ext d _
  have ⟨f, f_fresh⟩ := fresh_exists (M.fv ∪ N.fv ∪ xs)

  have hM : f ∉ M.fv := by grind
  have hN : f ∉ N.fv := by grind
  have hxs : f ∉ xs := by grind

  rw [interp_open_rec M 0 f hM d (DeBruijnShift ρ) σ]
  rw [interp_open_rec N 0 f hN d (DeBruijnShift ρ) σ]
  specialize h f hxs
  simp [open'] at h
  rw [h]

---------------------------------------------------------------------------------
-- =β

-- Prove β-step entails model interpretation equality
lemma beta_step_imp_interp_eq (ρ : ℕ → Set α) (σ : Var → Set α)
{A B : Term Var} (h: A ⭢βᶠ B) : 〚A〛_{ρ,σ} = 〚B〛_{ρ,σ} := by
  induction h generalizing ρ σ
  · expose_names
    cases M with
    | app a b =>
    obtain ⟨hM,hb⟩:= h
    simp only [Interp]
    rw [F_G_eq_id]
    apply DeBruijnSubst
    apply DeBruijnSubst_continuous
    | _ => contradiction
  · expose_names
    simp [a_ih]
  · expose_names
    simp [a_ih]
  · expose_names
    apply interp_ξ xs
    · intro x hx ρ σ
      apply a_ih x hx ρ σ

-- Prove multi-β-step entails model interpretation equality
lemma multi_beta_imp_interp_eq (ρ : ℕ → Set α) (σ : Var → Set α) (A B : Term Var):
(A ↠βᶠ B) -> 〚 A 〛_{ρ,σ} = 〚 B 〛_{ρ,σ}
 := by
 intro h
 induction h generalizing ρ σ
 · rfl
 · expose_names
   rw [a_ih]
   apply (beta_step_imp_interp_eq ρ σ h_1)

-- Prove β-equality entails model interpretation equality
lemma beta_eq_imp_interp_eq (ρ : ℕ → Set α) (σ : Var → Set α) (A B : Term Var):
(A ≡β B) -> 〚 A 〛_{ρ,σ} = 〚 B 〛_{ρ,σ}
  := by
  intro h
  obtain ⟨Q,⟨hmA, hmB⟩⟩:= (common_reduct_of_BetaEquiv A B h)
  rw [multi_beta_imp_interp_eq ρ σ _ _ hmB]
  exact multi_beta_imp_interp_eq ρ σ _ _ hmA

--------------------------------------------------------------------------------
-- Prove Interp is a λ-theory

open LT

-- We define a relation for our interpretation as expected
def InterpRel (M N : Term Var) : Prop :=
  ∀ (ρ : ℕ → Set α) (σ : Var → Set α), 〚M〛_{ρ,σ} = 〚N〛_{ρ,σ}

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
