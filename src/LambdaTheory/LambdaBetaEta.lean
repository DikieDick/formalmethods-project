import src.LambdaTheory.Basic
import src.BetaEquiv
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta

open Cslib
open LambdaCalculus.LocallyNameless.Untyped
open Term

universe u
variable {Var : Type u}

open LT

section LambdaBetaEta

inductive ThLambdaBetaEta : Term Var → Term Var → Prop
| beta (M N) : Beta M N → ThLambdaBetaEta M N
| app (M N P Q) : ThLambdaBetaEta M N → ThLambdaBetaEta P Q → ThLambdaBetaEta (app M P) (app N Q)
| xi (M N) (xs : Finset Var) : (∀ x ∉ xs, ThLambdaBetaEta (M ^ fvar x) (N ^ fvar x)) → ThLambdaBetaEta (abs M) (abs N)
| refl (M) : ThLambdaBetaEta M M
| trans (M N P) : ThLambdaBetaEta M N → ThLambdaBetaEta N P → ThLambdaBetaEta M P
| sym (M N): ThLambdaBetaEta M N → ThLambdaBetaEta N M
-- | eta (M) : LambdaBetaEta (abs (app M (bvar 0))) M -- TODO: Should be outer most

#check FullEta

instance : @LambdaTheory Var (ThLambdaBetaEta) :=
  ⟨ThLambdaBetaEta.beta, ThLambdaBetaEta.xi, ThLambdaBetaEta.app, ThLambdaBetaEta.refl, ThLambdaBetaEta.trans, ThLambdaBetaEta.sym⟩

end LambdaBetaEta
