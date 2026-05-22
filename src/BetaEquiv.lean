import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

namespace Cslib
namespace LambdaCalculus.LocallyNameless.Untyped

open Term

universe u
variable {Var : Type u} [HasFresh Var] [DecidableEq Var]

notation3 t:39 " →βᶠ " t':39 => t ⭢βᶠ t'

def Term.BetaEquiv : Term Var → Term Var → Prop :=
  Relation.EqvGen FullBeta

instance instEquivBetaEquiv : Equivalence (@BetaEquiv Var) :=
  Relation.EqvGen.is_equivalence FullBeta

instance : Setoid (Term Var) :=
  {r := BetaEquiv
   iseqv := instEquivBetaEquiv}

notation M " ≡β " N => BetaEquiv M N

@[symm]
lemma BetaEquiv_symm {Var : Type u} {M N : Term Var} (h : M ≡β N) : N ≡β M := by
  apply Relation.EqvGen.symm
  exact h

@[refl]
lemma BetaEquiv_refl {Var : Type u} {M : Term Var} : M ≡β M := by
  apply Relation.EqvGen.refl


def idTerm := Term.abs $ @Term.bvar ℕ 0
def betaRedex := Term.app (Term.abs $ @Term.bvar ℕ 0) (Term.abs $ @Term.bvar ℕ 0)

lemma test : betaRedex →βᶠ idTerm := by
  constructor
  constructor
  apply LC.abs
  grind
  exact Finset.empty
  apply LC.abs
  grind
  exact Finset.empty

example : betaRedex ↠βᶠ idTerm := by
  apply Relation.ReflTransGen.single
  apply test

example : betaRedex ≡β idTerm := by
  apply Relation.EqvGen.rel
  apply test

example : idTerm ≡β idTerm := by
  apply Relation.EqvGen.refl

example : idTerm ≡β betaRedex := by
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


lemma betaEquiv_of_multiBeta (M N : Term Var) (hM : M.LC) (hN : N.LC) : (M ↠βᶠ N) → M ≡β N := by
  intro h
  induction h with
  | refl => apply Relation.EqvGen.refl
  | tail h₁ h₂ h₃ =>
    expose_names -- TODO
    have hb : b.LC := by
      have := FullBeta.steps_lc_or_rfl h₁
      cases this with
      | inl h => exact h.right
      | inr h => rwa [<- h]
    have hm := h₃ hb
    apply Relation.EqvGen.trans M b c
    · exact hm
    · constructor; assumption

lemma BetaEquiv_of_BetaEquiv_and_step {Var : Type u} (M N O : Term Var) (hMN : M.BetaEquiv N) (hNO : N →βᶠ O) : M.BetaEquiv O :=
  Relation.EqvGen.trans M N O hMN (Relation.EqvGen.rel N O hNO)
