import src.LambdaTheory.Basic
import src.BetaEquiv
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta

open Cslib
open LambdaCalculus.LocallyNameless.Untyped
open Term

universe u
variable {Var : Type u}


open LambdaTheory

section LambdaBeta

inductive ThLambdaBeta : Term Var → Term Var → Prop
| beta (M N) : FullBeta M N → ThLambdaBeta M N
| app (M N P Q) : ThLambdaBeta M N → ThLambdaBeta P Q → ThLambdaBeta (app M P) (app N Q)
-- | xi (M N) : LambdaBeta M N →
| refl (M) : ThLambdaBeta M M
| trans (M N P) : ThLambdaBeta M N → ThLambdaBeta N P → ThLambdaBeta M P
| sym (M N): ThLambdaBeta M N → ThLambdaBeta N M

instance : @LambdaTheory Var (ThLambdaBeta) :=
  ⟨ThLambdaBeta.beta, ThLambdaBeta.app, ThLambdaBeta.refl, ThLambdaBeta.trans, ThLambdaBeta.sym⟩

lemma lambdaBeta_iff_betaEquiv (M N : Term Var) : (ThLambdaBeta M N) ↔ (M ≡β N) := by
  constructor
  · intro h
    induction h with
    | beta M N h =>
        apply Relation.EqvGen.rel
        exact h
    | refl M =>
        apply Relation.EqvGen.refl
    | sym M N h ih =>
        apply Relation.EqvGen.symm
        exact ih
    | trans M N P h₁ h₂ ih₁ ih₂ =>
        sorry
    | app M N P Q h₁ h₂ ih₁ ih₂ =>
        sorry

  · intro h
    induction h with
    | rel _ _ h =>
        constructor; assumption
    | refl => apply ThLambdaBeta.refl
    | symm M N h ih => apply ThLambdaBeta.sym; assumption
    | trans M N P h₁ h₂ ih₁ ih₂ =>
        apply ThLambdaBeta.trans M N P
        · assumption
        · assumption

end LambdaBeta

section LambdaBetaEta

inductive ThLambdaBetaEta : Term Var → Term Var → Prop
| beta (M N) : FullBeta M N → ThLambdaBetaEta M N
| app (M N P Q) : ThLambdaBetaEta M N → ThLambdaBetaEta P Q → ThLambdaBetaEta (app M P) (app N Q)
-- | xi (M N) : LambdaRelated M N → Term.abs
| refl (M) : ThLambdaBetaEta M M
| trans (M N P) : ThLambdaBetaEta M N → ThLambdaBetaEta N P → ThLambdaBetaEta M P
| sym (M N): ThLambdaBetaEta M N → ThLambdaBetaEta N M
-- | eta (M) : LambdaBetaEta (abs (app M (bvar 0))) M -- TODO: Should be outer most

#check FullEta

instance : @LambdaTheory Var (ThLambdaBetaEta) :=
  ⟨ThLambdaBetaEta.beta, ThLambdaBetaEta.app, ThLambdaBetaEta.refl, ThLambdaBetaEta.trans, ThLambdaBetaEta.sym⟩

end LambdaBetaEta
