import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Project.BetaEquiv

open Cslib
open LambdaCalculus.LocallyNameless.Untyped

open Term

namespace LT

universe u
variable {Var : Type u}

-- Herman Geuvers (https://www.cs.ru.nl/~herman/onderwijs/semantics2025/model_untyped_lambda.pdf)
-- A λ-theory is closed under the following six rules
class LambdaTheory (rel: Term Var → Term Var → Prop) where
  beta (M N : Term Var): Beta M N → rel M N
  xi (M N : Term Var) (xs : Finset Var) : (∀ x ∉ xs, rel (M ^ fvar x) (N ^ fvar x)) → rel (abs M) (abs N)
  app (M N P Q : Term Var) : rel M N → rel P Q → rel (Term.app M P) (Term.app N Q)
  refl (M : Term Var) : rel M M
  trans (M N P : Term Var) : rel M N → rel N P → rel M P
  sym (M N : Term Var): rel M N → rel N M

-- Minimal λ-theory, contains the same rules as the definition
inductive ThLambdaBeta : Term Var → Term Var → Prop
| beta (M N) : Beta M N → ThLambdaBeta M N
| xi (M N) (xs : Finset Var) : (∀ x ∉ xs, ThLambdaBeta (M ^ fvar x) (N ^ fvar x)) → ThLambdaBeta (abs M) (abs N)
| app (M N P Q) : ThLambdaBeta M N → ThLambdaBeta P Q → ThLambdaBeta (app M P) (app N Q)
| refl (M) : ThLambdaBeta M M
| trans (M N P) : ThLambdaBeta M N → ThLambdaBeta N P → ThLambdaBeta M P
| sym (M N): ThLambdaBeta M N → ThLambdaBeta N M

instance : @LambdaTheory Var (ThLambdaBeta) :=
  ⟨ThLambdaBeta.beta, ThLambdaBeta.xi, ThLambdaBeta.app, ThLambdaBeta.refl, ThLambdaBeta.trans, ThLambdaBeta.sym⟩

-- β-equivalence between M and N implies M and N are related in λβ
lemma ThLambdaBeta_of_BetaEquiv {M N : Term Var} (h : M ≡β N) : ThLambdaBeta M N := by
  induction h with
  | rel O P h =>
    induction h with
    | base h => apply ThLambdaBeta.beta; assumption
    | appL =>
      expose_names
      apply ThLambdaBeta.app
      · apply ThLambdaBeta.refl
      · assumption
    | appR =>
      expose_names
      apply ThLambdaBeta.app
      · assumption
      · apply ThLambdaBeta.refl
    | abs =>
      expose_names
      apply ThLambdaBeta.xi _ _ xs
      intro x hx
      apply a_ih _ hx
  | refl O => exact ThLambdaBeta.refl O
  | symm O P h ih =>
    apply ThLambdaBeta.sym; assumption
  | trans O P Q h1 h2 ih1 ih2 =>
    exact ThLambdaBeta.trans O P Q ih1 ih2

-- Being related under λβ implies being related under any other λ-theory
lemma ThEq_of_ThLambdaBeta {M N : Term Var} {r : Term Var → Term Var → Prop} [LambdaTheory r] (h : ThLambdaBeta M N) : r M N := by
  induction h with
  | beta A B h => apply LambdaTheory.beta; assumption
  | xi A B xs h ih => apply LambdaTheory.xi; assumption
  | refl P => apply LambdaTheory.refl
  | sym M N h ih => apply LambdaTheory.sym; assumption
  | trans M N P _ _ hMN hNP =>
    apply LambdaTheory.trans M N P <;> assumption
  | app M N P Q hMN hPQ _ _ =>
    apply LambdaTheory.app M N P Q <;> assumption

lemma ThEq_of_BetaEquiv {M N : Term Var} {r : Term Var → Term Var → Prop} [LambdaTheory r] (h : M ≡β N) : r M N :=
  ThEq_of_ThLambdaBeta (ThLambdaBeta_of_BetaEquiv h)

-- M = N in λβ if and only if M =β N :
lemma ThLambdaBeta_iff_BetaEquiv (M N : Term Var) : ThLambdaBeta M N ↔ M.BetaEquiv N := by
  constructor <;> intro h
  · induction h with
    | beta O P h =>
      apply Relation.EqvGen.rel
      apply Xi.base
      apply h
    | refl O => apply Relation.EqvGen.refl
    | sym O P _ ih => exact ih.symm
    | trans O P Q hOP hPQ ih₁ ih₂ => exact Relation.EqvGen.trans O P Q ih₁ ih₂
    | app O P Q R hOP hQR ih₁ ih₂ =>
      sorry
    | xi O P xs h ih =>
      sorry
  · exact ThEq_of_BetaEquiv h

variable {r : Term Var → Term Var → Prop} [LambdaTheory r]

-- This way we can use calc blocks when reasoning over equality in a theory
instance : Trans r r r where
  trans {M N P} h1 h2 := LambdaTheory.trans M N P h1 h2

@[refl]
lemma LambdaTheory_refl (M : Term Var) : r M M :=
  LambdaTheory.refl M

@[symm]
lemma LambdaTheory_symm {M N : Term Var} (h : r M N) : r N M :=
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

@[simp, grind .]
lemma app_congr {M N P Q : Term Var} (h1 : r M N) (h2 : r P Q) : r (app M P) (app N Q) :=
  LambdaTheory.app M N P Q h1 h2

-- A λ-theory R is inconsistent when ∀ M N, R M N.
def inconsistent (r : Term Var → Term Var → Prop) [LambdaTheory r] : Prop := ∀ M N : Term Var, M.LC → N.LC → r M N

end LT
