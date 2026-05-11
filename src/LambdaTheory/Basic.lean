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
  refl (M : Term Var) : rel M M
  trans (M N P : Term Var) : rel M N → rel N P → rel M P
  sym (M N : Term Var): rel M N → rel N M

inductive ThLambdaBeta : Term Var → Term Var → Prop
| beta (M N) : FullBeta M N → ThLambdaBeta M N
| app (M N P Q) : ThLambdaBeta M N → ThLambdaBeta P Q → ThLambdaBeta (app M P) (app N Q)
| refl (M) : ThLambdaBeta M M
| trans (M N P) : ThLambdaBeta M N → ThLambdaBeta N P → ThLambdaBeta M P
| sym (M N): ThLambdaBeta M N → ThLambdaBeta N M

instance : @LambdaTheory Var (ThLambdaBeta) :=
  ⟨ThLambdaBeta.beta, ThLambdaBeta.app, ThLambdaBeta.refl, ThLambdaBeta.trans, ThLambdaBeta.sym⟩

lemma ThLambdaBeta_of_BetaEquiv {M N : Term Var} (h : M ≡β N) : ThLambdaBeta M N := by
  induction h with
  | rel _ _ h => apply ThLambdaBeta.beta; assumption
  | refl => apply ThLambdaBeta.refl
  | symm M N h ih => apply ThLambdaBeta.sym; assumption
  | trans M N P h₁ h₂ ih₁ ih₂ =>
    apply ThLambdaBeta.trans M N P
    · assumption
    · assumption

lemma ThEq_of_ThLambdaBeta {M N : Term Var} {r : Term Var → Term Var → Prop} [LambdaTheory r] (h : ThLambdaBeta M N) : r M N := by
  induction h with
  | beta A B h => apply LambdaTheory.beta; assumption
  | refl P => apply LambdaTheory.refl
  | sym M N h ih => apply LambdaTheory.sym; assumption
  | trans M N P _ _ hMN hNP =>
    apply LambdaTheory.trans M N P <;> assumption
  | app M N P Q hMN hPQ _ _ =>
    apply LambdaTheory.app M N P Q <;> assumption

lemma ThEq_of_BetaEquiv {M N : Term Var} {r : Term Var → Term Var → Prop} [LambdaTheory r] (h : M ≡β N) : r M N :=
  ThEq_of_ThLambdaBeta (ThLambdaBeta_of_BetaEquiv h)

lemma BetaEquiv_of_ThLambdaBeta {M N : Term Var} (h : ThLambdaBeta M N) : M ≡β N := by
  induction h with
  | beta M N h => apply Relation.EqvGen.rel; exact h
  | refl M => apply Relation.EqvGen.refl
  | sym M N h ih => apply Relation.EqvGen.symm; exact ih
  | trans M N P h₁ h₂ ih₁ ih₂ =>
    apply Relation.EqvGen.trans M N P
    · assumption
    · assumption
  | app M N P Q h₁ h₂ ih₁ ih₂ =>
    sorry

lemma ThLambdaBeta_iff_BetaEquiv {M N : Term Var} : ThLambdaBeta M N ↔ M ≡β N :=
  ⟨BetaEquiv_of_ThLambdaBeta, ThLambdaBeta_of_BetaEquiv⟩

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


def inconsistent (r : Term Var → Term Var → Prop) [LambdaTheory r] : Prop := ∀ M N : Term Var, M.LC → N.LC → r M N


-- public meta section
-- open Lean Elab Command Meta

-- syntax (name := mkLambdaTheory)
--   "mkLambdaTheory" : attr

-- initialize registerBuiltinAttribute {
--   name := `mkLambdaTheory
--   descr := "Generate a LambdaTheory instance"

--   add := fun declName stx _ => MetaM.run' do
--     match stx with
--     | `(attr| mkLambdaTheory) =>
--         let currNamespace ← getCurrNamespace

--         let beta  := mkIdent <| declName ++ `beta
--         let app   := mkIdent <| declName ++ `app
--         let refl  := mkIdent <| declName ++ `refl
--         let trans := mkIdent <| declName ++ `trans
--         let sym   := mkIdent <| declName ++ `sym
--         let thIdent := mkIdent declName

--         liftCommandElabM do
--           modifyScope ({ · with currNamespace })
--           elabCommand <|
--             ← `(instance {Var}: @LambdaTheory Var $thIdent :=
--                   ⟨$beta, $app, $refl, $trans, $sym⟩)
--     | _ => throwError "mkLambdaTheory error"
-- }

-- end

end LambdaTheory
