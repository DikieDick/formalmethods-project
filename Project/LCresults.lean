import Project.LambdaTheory.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt

open Cslib
open LambdaCalculus.LocallyNameless.Untyped
open Term

universe u

@[simp, grind .]
lemma absLC_of_LC {Var : Type u} [HasFresh Var] {M : Term Var} (h : M.LC): (abs M).LC := by
    apply LC.abs
    grind
    exact Finset.empty

@[simp, grind =]
lemma openRec_abs_eq_abs_of_LC {Var : Type u} [HasFresh Var] (M N : Term Var) (hM : M.LC) : (M.abs ^ N = M.abs) := by
  induction M with
  | bvar n => cases hM
  | fvar x => cases hM with | fvar =>  unfold open'; simp_rw [openRec_abs, openRec_fvar]
  | app M O ih₁ ih₂ =>
    cases hM with | app hM hO =>
      specialize ih₁ hM
      specialize ih₂ hO
      unfold open' at *
      rw [openRec_abs] at ih₁
      rw [openRec_abs] at ih₂
      rw [openRec_abs, openRec_app]
      simp
      constructor
      · simp only [zero_add, abs.injEq] at ih₁
        exact ih₁
      · simp only [zero_add, abs.injEq] at ih₂
        exact ih₂
  | abs M ih => grind only [= open'.eq_1, =_ open_lc, absLC_of_LC]


lemma lcAt_rename {Var : Type u} (M : Term Var) (k n : ℕ) (x y : Var): LcAt k (M⟦n ↝ fvar x⟧) → LcAt k (M⟦n ↝ fvar y⟧) := by
  induction M generalizing k n with grind

lemma LC_rename {Var : Type u} [HasFresh Var] [DecidableEq Var] (x y : Var) {M : Term Var} (h : (M⟦0 ↝ fvar x⟧).LC) : (M⟦0 ↝ fvar y⟧).LC := by
  have h_lcAt : LcAt 0 (M⟦0 ↝ fvar x⟧) := (lcAt_iff_LC (M⟦0 ↝ fvar x⟧)).mpr h
  have h_lcAt_y := lcAt_rename M 0 0 x y h_lcAt
  rwa [← lcAt_iff_LC]

@[simp, grind =]
lemma test {Var : Type u} [HasFresh Var] (M N : Term Var) (hM : M.LC) : M ^ N = M := by
  grind only [= open'.eq_1, =_ open_lc]

lemma helper {Var : Type u} [HasFresh Var] (M N : Term Var) (hM : M.LC) (hN : N.LC): app (abs M) N →βᶠ M:= by
  induction M with
  | abs O ih =>
    apply Xi.base
    have : (O.abs) = (O.abs) ^ N := by grind
    nth_rw 2 [this]
    apply Beta.beta
    · grind
    · assumption
  | bvar n =>
    apply Xi.base
    have : bvar n = bvar n ^ N := by
      grind
    nth_rw 2 [this]
    constructor
    · grind
    · assumption
  | fvar x =>
    apply Xi.base
    have : fvar x = fvar x ^ N := by grind
    nth_rw 2 [this]
    constructor <;> try assumption
    grind
  | app M O ih₁ ih₂ =>
    apply Xi.base
    have : (M.app O) = (M.app O) ^ N := by grind
    nth_rw 2 [this]
    constructor <;> try assumption
    grind
