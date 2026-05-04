import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import src.BetaEquiv

open Cslib
open LambdaCalculus.LocallyNameless.Untyped

open Term

namespace LambdaTheory

universe u
variable {Var : Type u}

-- Herman Geuvers (https://www.cs.ru.nl/~herman/onderwijs/semantics2025/model_untyped_lambda.pdf)
-- A λ-theory is closed under the following six rules
class LambdaTheory (rel: Term Var → Term Var → Prop) where
  beta (M N : Term Var) : FullBeta M N → rel M N
  app (M N P Q : Term Var) : rel M N → rel P Q → rel (Term.app M P) (Term.app N Q)
-- | xi (M N) : LambdaRelated M N → Term.abs
  refl (M : Term Var) : rel M M
  trans (M N P : Term Var) : rel M N → rel N P → rel M P
  sym (M N : Term Var): rel M N → rel N M


variable {r : Term Var → Term Var → Prop} [LambdaTheory r]

@[simp, grind .]
lemma ThEq_of_BetaEquiv {M N : Term Var} {r : Term Var → Term Var → Prop} [LambdaTheory r] (h : M ≡β N) : r M N := by
  induction h with
  | rel _ _ h => apply LambdaTheory.beta; assumption
  | refl => apply LambdaTheory.refl
  | symm M N h ih => apply LambdaTheory.sym; assumption
  | trans M N P h₁ h₂ ih₁ ih₂ =>
    apply LambdaTheory.trans M N P
    · assumption
    · assumption

-- This way we can use calc blocks when reasoning over equality in a theory
instance : Trans r r r where
  trans {M N P} h1 h2 := LambdaTheory.trans M N P h1 h2

@[refl]
lemma refl' (M : Term Var) : r M M :=
  LambdaTheory.refl M

@[symm]
lemma sym' {M N : Term Var} (h : r M N) : r N M :=
  LambdaTheory.sym M N h

lemma app_left {M N : Term Var} (P : Term Var) (h : r M N) :
  r (Term.app M P) (Term.app N P) :=
  LambdaTheory.app M N P P h (LambdaTheory.refl P)

lemma app_right (M : Term Var) {P Q : Term Var} (h : r P Q) :
  r (Term.app M P) (Term.app M Q) :=
  LambdaTheory.app M M P Q (LambdaTheory.refl M) h

lemma app_left₂ {M N : Term Var} (P Q : Term Var) (h : r M N) :
  r (Term.app (Term.app M P) Q) (Term.app (Term.app N P) Q) :=
  app_left Q (app_left P h)


def inconsistent (r : Term Var → Term Var → Prop) [LambdaTheory r] : Prop := ∀ M N : Term Var, M.LC → N.LC → r M N

end LambdaTheory
