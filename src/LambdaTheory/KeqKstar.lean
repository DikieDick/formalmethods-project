import src.LambdaTheory.Basic
import src.LambdaTerms
import src.BetaEquiv
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

open Cslib
open LambdaCalculus.LocallyNameless.Untyped
open Term

open LambdaTerms
open LambdaTheory

universe u
variable {Var : Type u} [HasFresh Var] [DecidableEq Var]

inductive ThKeqKstar : Term Var → Term Var → Prop
| beta (M N) : FullBeta M N → ThKeqKstar M N
| app (M N P Q) : ThKeqKstar M N → ThKeqKstar P Q → ThKeqKstar (Term.app M P) (Term.app N Q)
-- | xi (M N) : LambdaRelated M N → Term.abs
| refl (M) : ThKeqKstar M M
| trans (M N P) : ThKeqKstar M N → ThKeqKstar N P → ThKeqKstar M P
| sym (M N): ThKeqKstar M N → ThKeqKstar N M
| new : ThKeqKstar K Kstar

instance instKeqKstar : @LambdaTheory Var ThKeqKstar :=
    ⟨ThKeqKstar.beta, ThKeqKstar.app, ThKeqKstar.refl, ThKeqKstar.trans, ThKeqKstar.sym⟩


lemma Kstar_LC {Var : Type u} : (@Kstar Var).LC := by
  unfold Kstar
  apply LC.abs
  intro x _
  apply LC.abs
  intro y _
  simp
  apply LC.fvar
  · exact Finset.empty
  exact Finset.empty

lemma reduceKstar {Var : Type u} (M : Term Var) (hM : M.LC) : (@app Var Kstar M) →βᶠ (abs $ bvar 0) := by
  unfold Kstar

  constructor
  constructor
  · apply LC.abs
    intro x _
    apply LC.abs
    intro y _
    simp
    apply LC.fvar
    · exact Finset.empty
    · exact Finset.empty
  · exact hM

lemma reduceKstar2 {Var : Type u} (M N : Term Var) (hM : M.LC) (hN : N.LC) : (@app Var (@app Var Kstar M) N) ↠βᶠ N := by
  -- unfold Kstar
  apply Relation.ReflTransGen.tail (b := app (abs $ bvar 0) N)
  apply Relation.ReflTransGen.single
  apply Xi.appR
  · assumption
  · apply reduceKstar
    · assumption
  · constructor
    constructor
    apply LC.abs
    grind
    exact Finset.empty
    assumption

lemma K_LC {Var : Type u} : (@K Var).LC := by
  unfold K
  apply LC.abs
  intro x _
  apply LC.abs
  intro y _
  apply LC.fvar
  · exact Finset.empty
  exact Finset.empty


lemma KstarMN_eq_N (M N : Term Var) (hM : M.LC) (hN : N.LC) : app (app Kstar M) N ≡β N := by
  apply betaEquiv_of_multiBeta
  · constructor
    swap; assumption
    constructor
    swap; assumption
    exact Kstar_LC
  · assumption
  · apply reduceKstar2
    · assumption
    · assumption

lemma reduceK {Var : Type u} (M N : Term Var) (hM : M.LC) (hN : N.LC) : (app (app K M) N) ↠βᶠ M := by
  unfold K
  apply Relation.ReflTransGen.tail (b := app (abs $ bvar 1) N)
  apply Relation.ReflTransGen.single
  apply Xi.appR
  · assumption
  · sorry
  sorry

-- instance : CoeFun (Term Var) (fun _ => Term Var → Term Var) where
--   coe M N := Term.app M N

@[simp]
lemma K_MN_eq_M (M N : Term Var) (hM : M.LC) (hN : N.LC) : app (app K M) N ≡β M := by
  apply betaEquiv_of_multiBeta
  · apply LC.app
    · apply LC.app
      · exact K_LC
      · assumption
    · assumption
  · assumption
  · apply reduceK
    · assumption
    · assumption

local notation:50 M " =K= " N => ThKeqKstar M N

-- We prove that adding K = Kstar results in an inconsistent λ-theory
lemma K_eq_Kstart_inconsistent {Var : Type u} [DecidableEq Var] [HasFresh Var] : @inconsistent Var ThKeqKstar instKeqKstar := by
  intro M N hM hN

  #check Var

  have h₁: M =K= @app Var (@app Var K M) N := by
    -- apply @ThEq_of_BetaEquiv Var M ((K.app M).app N) ThKeqKstar
    apply ThEq_of_BetaEquiv
    -- have t : (M ≡β (K.app M).app N) → (K.app M).app N =K= M := sorry
    -- have : (M ≡β (K.app M).app N) := sorry
    -- have t : (@BetaEquiv Var M (@app Var (@app Var K M) N)) → (@ThKeqKstar Var (@app Var (@app Var K M) N) M) := sorry
    -- have : @ThKeqKstar Var (@app Var (@app Var K M) N) M := sorry
    symm
    -- apply t
    -- exact this
    -- symm
    apply K_MN_eq_M
    assumption
    assumption

  have h₂: (K.app M).app N =K= (Kstar.app M).app N := by
    -- simp
    apply app_left₂
    apply ThKeqKstar.new
  have h₃: (Kstar.app M).app N =K= N := by
    apply ThEq_of_BetaEquiv
    apply KstarMN_eq_N
    assumption
    assumption
-- M = K M N = Kstar M N = N
  calc M =K= (K.app M).app N := h₁
       _ =K= (Kstar.app M).app N := h₂
       _ =K= N := h₃


  -- calc
  --   M =K= K M N := by simp; apply ThEq_of_BetaEquiv; symm; apply K_MN_eq_M; assumption; assumption
  --   _ =K= Kstar M N := by simp; apply app_left₂; apply ThKeqKstar.new
  --   _ =K= N := by simp; apply ThEq_of_BetaEquiv; apply KstarMN_eq_N; assumption; assumption
