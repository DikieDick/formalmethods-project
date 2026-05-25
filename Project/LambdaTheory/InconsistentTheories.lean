import Project.LambdaTheory.Basic
import Project.LambdaTerms
import Project.BetaEquiv
import Project.LCresults
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

open Cslib
open LambdaCalculus.LocallyNameless.Untyped
open Term

open LambdaTerms
open LT

universe u
variable {Var : Type u} [HasFresh Var] [DecidableEq Var]


-- This file contains some examples of inconsistent theories

section KeqKstar

inductive ThKeqKstar : Term Var → Term Var → Prop
| beta (M N) : Beta M N → ThKeqKstar M N
| xi (M N : Term Var) (xs : Finset Var) : (∀ x ∉ xs, ThKeqKstar (M ^ fvar x) (N ^ fvar x)) → ThKeqKstar (abs M) (abs N)
| app (M N P Q) : ThKeqKstar M N → ThKeqKstar P Q → ThKeqKstar (Term.app M P) (Term.app N Q)
| refl (M) : ThKeqKstar M M
| trans (M N P) : ThKeqKstar M N → ThKeqKstar N P → ThKeqKstar M P
| sym (M N): ThKeqKstar M N → ThKeqKstar N M
| new : ThKeqKstar K Kstar

instance instKeqKstar : LambdaTheory (@ThKeqKstar Var) :=
  ⟨ThKeqKstar.beta, ThKeqKstar.xi, ThKeqKstar.app, ThKeqKstar.refl, ThKeqKstar.trans, ThKeqKstar.sym⟩

lemma ThKeqKstar_of_BetaEquiv {Var : Type u} {M N : Term Var} (h : M ≡β N) : ThKeqKstar M N :=
    ThEq_of_ThLambdaBeta (ThLambdaBeta_of_BetaEquiv h)

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
  apply BetaEquiv_of_MultiBeta
  · constructor
    swap; assumption
    constructor
    swap; assumption
    exact Kstar_LC
  · assumption
  · apply reduceKstar2
    · assumption
    · assumption


lemma reduceK {Var : Type u} [HasFresh Var] (M N : Term Var) (hM : M.LC) (hN : N.LC) : (app (app K M) N) ↠βᶠ M := by
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
  · apply helper <;> assumption

instance : CoeFun (Term Var) (fun _ => Term Var → Term Var) where
  coe M N := Term.app M N

@[simp]
lemma KMN_eq_M (M N : Term Var) (hM : M.LC) (hN : N.LC) : app (app K M) N ≡β M := by
  apply BetaEquiv_of_MultiBeta
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
    apply KMN_eq_M
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

inductive ThKeqI : Term Var → Term Var → Prop
| beta (M N) : Beta M N → ThKeqI M N
| xi (M N : Term Var) (xs : Finset Var) : (∀ x ∉ xs, ThKeqI (M ^ fvar x) (N ^ fvar x)) → ThKeqI (abs M) (abs N)
| app (M N P Q) : ThKeqI M N → ThKeqI P Q → ThKeqI (Term.app M P) (Term.app N Q)
| refl (M) : ThKeqI M M
| trans (M N P) : ThKeqI M N → ThKeqI N P → ThKeqI M P
| sym (M N): ThKeqI M N → ThKeqI N M
| new : ThKeqI K I

instance instKeqI : LambdaTheory (@ThKeqI Var) :=
  ⟨ThKeqI.beta, ThKeqI.xi, ThKeqI.app, ThKeqI.refl, ThKeqI.trans, ThKeqI.sym⟩

lemma ThKeqI_of_BetaEquiv {Var : Type u} {M N : Term Var} (h : M ≡β N) : ThKeqI M N :=
  ThEq_of_ThLambdaBeta (ThLambdaBeta_of_BetaEquiv h)

local notation:50 M " =K= " N => ThKeqI M N

lemma I_LC {Var : Type u} : (@I Var).LC := by
  unfold I
  apply LC.abs
  · intro x _
    grind
  · exact Finset.empty

lemma reduce_I {Var : Type u} (M : Term Var) (hM : M.LC) : I M ≡β M := by
  simp
  unfold I
  apply Relation.EqvGen.rel
  constructor
  constructor
  · apply LC.abs
    intro x _
    grind
    exact Finset.empty
  · assumption

-- M = K M N = I M N = K I I M N = I K I M N = K I M N = I N = N
theorem KeqI_inconsistent {Var : Type u} [instFresh : HasFresh Var] [instDEq: DecidableEq Var]: inconsistent (Var := Var) ThKeqI := by
  intro M N hM hN

  -- Th ⊨ M = N
  calc M =K= K M N := by
        simp
        apply ThKeqI_of_BetaEquiv
        apply BetaEquiv_symm
        apply KMN_eq_M <;> assumption
    _ =K= I M N := by
        simp
        apply app_left₂
        apply ThKeqI.new
    _ =K= K I I M N := by
        simp
        have := KMN_eq_M (Var:=Var) I I I_LC I_LC
        apply app_congr _ (LambdaTheory.refl N)
        apply app_congr _ (LambdaTheory.refl M)
        apply ThKeqI_of_BetaEquiv
        apply BetaEquiv_symm
        exact KMN_eq_M I I I_LC I_LC
    _ =K= I K I M N := by
        simp
        apply app_congr _ (LambdaTheory.refl N)
        apply app_congr _ (LambdaTheory.refl M)
        apply app_congr _ (LambdaTheory.refl I)
        apply app_congr _ (ThKeqI.sym K I ThKeqI.new)
        apply ThKeqI.new
    _ =K= K I M N := by
        simp
        apply app_congr _ (LambdaTheory.refl N)
        apply app_congr _ (LambdaTheory.refl M)
        apply app_congr _ (LambdaTheory.refl I)
        apply ThEq_of_BetaEquiv (reduce_I K K_LC)
    _ =K= I N := by
      simp
      apply app_congr _ (LambdaTheory.refl N)
      apply ThKeqI_of_BetaEquiv
      exact KMN_eq_M I M I_LC hM
    _ =K= N := by
      simp
      apply ThKeqI_of_BetaEquiv
      apply reduce_I
      · assumption
end KeqI
