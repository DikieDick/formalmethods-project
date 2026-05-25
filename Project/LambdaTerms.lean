import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

namespace Cslib
namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Term

namespace LambdaTerms

universe u
variable {Var : Type u}

-- Collection of different λ-terms

def K     : Term Var := abs (abs $ bvar 1)                -- λxy.x = K
def Kstar : Term Var := abs (abs $ bvar 0)                -- λxy.y = K*
def I     : Term Var := abs (bvar 0)                      -- λx.x = I
def II    : Term Var := app (abs $ bvar 0) (abs $ bvar 0) -- II

end LambdaTerms
