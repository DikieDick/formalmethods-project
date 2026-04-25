import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

namespace Cslib
namespace LambdaCalculus.LocallyNameless.Untyped.Term

universe u
variable {Var : Type u}

#check Relation.ReflTransGen
#check Relation.EqvGen

def MultiBeta {Var : Type u} : Term Var → Term Var → Prop :=
  Relation.ReflTransGen $ FullBeta (Var := Var)

notation M " ⭢βᶠ* " N => MultiBeta M N

def BetaEquiv {Var : Type u} : Term Var → Term Var → Prop :=
  Relation.EqvGen $ FullBeta (Var := Var)

notation M " ≡βᶠ " N => BetaEquiv M N

def idTerm := Term.abs $ @Term.bvar ℕ 0
def betaRedex := Term.app (Term.abs $ @Term.bvar ℕ 0) (Term.abs $ @Term.bvar ℕ 0)

lemma test : betaRedex ⭢βᶠ idTerm := by
  constructor
  constructor
  apply LC.abs
  grind
  exact Finset.empty
  apply LC.abs
  grind
  exact Finset.empty

example : betaRedex ⭢βᶠ* idTerm := by
  apply Relation.ReflTransGen.single
  apply test

example : betaRedex ≡βᶠ idTerm := by
  apply Relation.EqvGen.rel
  apply test

example : idTerm ≡βᶠ idTerm := by
  apply Relation.EqvGen.refl

example : idTerm ≡βᶠ betaRedex := by
  apply Relation.EqvGen.symm
  apply Relation.EqvGen.rel
  apply test

def normalForm (M : Term Var) : Prop :=
  ¬∃ N, M ⭢βᶠ N

example : normalForm idTerm := by
  intro h
  obtain ⟨N, h⟩ := h
  cases h with
  | base h => cases h
  | abs xs h =>
    obtain ⟨x, hx⟩ := Finset.exists_notMem xs
    specialize h x hx
    cases h with
    | base h => cases h

example : ¬ normalForm betaRedex := by
  unfold normalForm
  push Not
  use idTerm
  apply test
