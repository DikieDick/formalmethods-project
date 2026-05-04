import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

namespace Cslib
namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Term

namespace LambdaTerms

universe u
variable {Var : Type u}

def K     : Term Var := abs (abs $ bvar 1) -- λxy.x
def Kstar : Term Var := abs (abs $ bvar 0) -- λxy.y
def id    : Term Var := abs (bvar 0)       -- λx.x

end LambdaTerms
