import src.LambdaTheory.Basic
import src.LambdaTerms
import src.BetaEquiv
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Lean


open Cslib
open LambdaCalculus.LocallyNameless.Untyped
open Term

open LambdaTerms
open LambdaTheory

universe u
variable {Var : Type u} [HasFresh Var] [DecidableEq Var]


-- This file contains some examples of inconsistent theories

section KeqKstar

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

lemma ThKeqKstar_of_ThLambdaBeta {M N : Term Var} (h : ThLambdaBeta M N) : ThKeqKstar M N := by
  induction h with
  | beta _ _ h => apply ThKeqKstar.beta; assumption
  | refl P => apply ThKeqKstar.refl
  | sym M N h ih => apply ThKeqKstar.sym; assumption
  | trans M N P _ _ hMN hNP =>
    apply ThKeqKstar.trans M N P
    · assumption
    · assumption
  | app M N P Q hMN hPQ _ _ =>
    apply ThKeqKstar.app M N P Q
    · assumption
    · assumption

lemma ThKeqKstar_of_BetaEquiv {M N : Term Var} (h : M ≡β N) : ThKeqKstar M N :=
  ThKeqKstar_of_ThLambdaBeta (ThLambdaBeta_of_BetaEquiv h)

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

lemma helper₃ {Var : Type u} (M O : Term Var) (hM : M.LC) (hO : O.LC) : (M.app O).LC := by
  grind

@[simp, grind .]
lemma absLC_of_LC {M : Term Var} (h : M.LC): (abs M).LC := by
    apply LC.abs
    grind
    exact Finset.empty

@[simp, grind =]
lemma openRec_abs_eq_abs_of_LC (M N : Term Var) (hM : M.LC) : (M.abs ^ N = M.abs) := by
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

@[simp, grind =]
lemma test (M N : Term Var) (hM : M.LC) : M ^ N = M := by
  grind

-- -- (λx.M)
lemma helper (M N : Term Var) (hM : M.LC) (hN : N.LC): app (abs M) N ↠βᶠ M:= by
  induction M with
  | abs O ih =>
    apply Relation.ReflTransGen.single
    apply Xi.base
    have : (O.abs) = (O.abs) ^ N := by grind
    nth_rw 2 [this]
    apply Beta.beta
    · grind
    · assumption
  | bvar n =>
    apply Relation.ReflTransGen.single
    apply Xi.base
    have : bvar n = bvar n ^ N := by
      grind
    nth_rw 2 [this]
    constructor
    · grind
    · assumption
  | fvar x =>
    apply Relation.ReflTransGen.single
    apply Xi.base
    have : fvar x = fvar x ^ N := by grind
    nth_rw 2 [this]
    constructor <;> try assumption
    grind
  | app M O ih₁ ih₂ =>
    apply Relation.ReflTransGen.single
    apply Xi.base
    have : (M.app O) = (M.app O) ^ N := by grind
    nth_rw 2 [this]
    constructor <;> try assumption
    grind

  -- apply Relation.ReflTransGen.tail (b := M ^ N)
  -- constructor


lemma reduceK {Var : Type u} (M N : Term Var) (hM : M.LC) (hN : N.LC) : (app (app K M) N) ↠βᶠ M := by
  unfold K
  apply Relation.ReflTransGen.tail (b := app (abs M) N)
  · apply Relation.ReflTransGen.single
    apply Xi.appR
    · exact hN
    · constructor
      constructor
      apply LC.abs
      · intro x _
        apply LC.abs
        intro y _
        simp
        apply LC.fvar
        exact Finset.empty
      · exact Finset.empty
      · exact hM
  · sorry




instance : CoeFun (Term Var) (fun _ => Term Var → Term Var) where
  coe M N := Term.app M N

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
lemma K_eq_Kstart_inconsistent {Var : Type u} [instDec : DecidableEq Var] [instFresh : HasFresh Var] : @inconsistent Var ThKeqKstar instKeqKstar := by
  intro M N hM hN

  have h₁: M =K= K M N := by
    simp
    apply ThKeqKstar_of_BetaEquiv
    apply BetaEquiv_symm
    apply K_MN_eq_M
    assumption
    assumption

  have h₂: K M N =K= Kstar M N := by
    simp
    apply app_left₂
    apply ThKeqKstar.new

  have h₃: Kstar M N =K= N := by
    apply ThKeqKstar_of_BetaEquiv
    apply KstarMN_eq_N
    assumption
    assumption

  calc M =K= K M N := h₁
       _ =K= Kstar M N := h₂
       _ =K= N := h₃

end KeqKstar

section KeqI

open Lean Elab Command

syntax (name := deriveLambdaTheoryInstance)
"mk_lambda_theory " ident : command

@[command_elab deriveLambdaTheoryInstance]
def elabDeriveLambdaTheoryInstance : CommandElab
| `(mk_lambda_theory $thName:ident) => do
  -- let thStr := thName.getId.toString

  -- let instName := mkIdent <| Name.mkSimple s!"inst{thStr}"

  let beta  := mkIdent <| thName.getId ++ `beta
  let app   := mkIdent <| thName.getId ++ `app
  let refl  := mkIdent <| thName.getId ++ `refl
  let trans := mkIdent <| thName.getId ++ `trans
  let sym   := mkIdent <| thName.getId ++ `sym

  elabCommand <|
    ← `(instance : @LambdaTheory Var $thName :=
          ⟨$beta, $app, $refl, $trans, $sym⟩)
| _ => throwUnsupportedSyntax

-- @[LambdaTheory]
inductive ThKeqI : Term Var → Term Var → Prop
| beta (M N) : FullBeta M N → ThKeqI M N
| app (M N P Q) : ThKeqI M N → ThKeqI P Q → ThKeqI (Term.app M P) (Term.app N Q)
-- | xi (M N) : LambdaRelated M N → Term.abs
| refl (M) : ThKeqI M M
| trans (M N P) : ThKeqI M N → ThKeqI N P → ThKeqI M P
| sym (M N): ThKeqI M N → ThKeqI N M
| new : ThKeqI K I

mk_lambda_theory ThKeqI

-- instance instKeqI : @LambdaTheory Var ThKeqI :=
--     ⟨ThKeqI.beta, ThKeqI.app, ThKeqI.refl, ThKeqI.trans, ThKeqI.sym⟩

lemma ThKeqI_of_ThLambdaBeta {M N : Term Var} (h : ThLambdaBeta M N) : ThKeqI M N := by
  induction h with
  | beta _ _ h => apply ThKeqI.beta; assumption
  | refl P => apply ThKeqI.refl
  | sym M N h ih => apply ThKeqI.sym; assumption
  | trans M N P _ _ hMN hNP =>
    apply ThKeqI.trans M N P
    · assumption
    · assumption
  | app M N P Q hMN hPQ _ _ =>
    apply ThKeqI.app M N P Q
    · assumption
    · assumption

lemma ThKeqI_of_BetaEquiv {M N : Term Var} (h : M ≡β N) : ThKeqI M N :=
  ThKeqI_of_ThLambdaBeta (ThLambdaBeta_of_BetaEquiv h)

local notation:50 M " =K= " N => ThKeqI M N

-- M = K M N = I M N = K I I M N = I K I M N = K I M N = I N = N
theorem KeqI_inconsistent : inconsistent (Var := Var) ThKeqI := by
  intro M N hM hN

  -- Th ⊨ M = N
  -- TODO
  calc M =K= K M N := by simp; sorry
    _ =K= I M N := by simp; sorry
    _ =K= K I I M N := by simp; sorry
    _ =K= I K I M N := by simp; sorry
    _ =K= K I M N := by simp; sorry
    _ =K= I N := by simp; sorry
    _ =K= N := by simp; sorry

end KeqI
