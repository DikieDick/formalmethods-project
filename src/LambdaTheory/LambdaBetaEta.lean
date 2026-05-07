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
