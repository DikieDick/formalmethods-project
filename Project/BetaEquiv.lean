import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

import Project.LambdaTerms

namespace Cslib
namespace LambdaCalculus.LocallyNameless.Untyped

open Term
open LambdaTerms

universe u
variable {Var : Type u}
-- [HasFresh Var] [DecidableEq Var]

notation3 t:39 " →βᶠ " t':39 => t ⭢βᶠ t'

-- β-equivalence
-- transitive reflexive symmetric closure of →βᶠ (FullBeta)
def Term.BetaEquiv : Term Var → Term Var → Prop :=
  Relation.EqvGen FullBeta

-- Equivalence instance from Term.BetaEquiv
instance instEquivBetaEquiv : Equivalence (@BetaEquiv Var) :=
  Relation.EqvGen.is_equivalence FullBeta

notation M " ≡β " N => BetaEquiv M N

@[symm]
lemma BetaEquiv_symm {Var : Type u} {M N : Term Var} (h : M ≡β N) : N ≡β M := by
  apply Relation.EqvGen.symm
  exact h

@[refl]
lemma BetaEquiv_refl {Var : Type u} {M : Term Var} : M ≡β M := by
  apply Relation.EqvGen.refl

lemma test : (@II Var) →βᶠ I := by
  constructor
  constructor
  apply LC.abs
  grind
  exact Finset.empty
  apply LC.abs
  grind
  exact Finset.empty

example : (@II Var) ↠βᶠ I := by
  apply Relation.ReflTransGen.single
  apply test

example : (@II Var) ≡β I := by
  apply Relation.EqvGen.rel
  apply test

example : (@I Var) ≡β I := by
  apply Relation.EqvGen.refl

example : (@I Var) ≡β II := by
  apply Relation.EqvGen.symm
  apply Relation.EqvGen.rel
  apply test

def normalForm (M : Term Var) : Prop :=
  ¬∃ N, M ⭢βᶠ N

variable [HasFresh Var]

-- The λ-term I is in normal form
example : normalForm (@I Var) := by
  intro h
  obtain ⟨N, h⟩ := h
  cases h with
  | base h => cases h
  | abs xs h =>
    obtain ⟨x, hx⟩ := Finset.exists_notMem xs
    specialize h x hx
    cases h with
    | base h => cases h

-- Our term with a β-redex (II) is *not* in normal form
example : ¬ normalForm (@II Var) := by
  unfold normalForm
  push Not
  use I
  apply test

variable [DecidableEq Var]

-- if M ↠βᶠ N then M ≡β N
lemma BetaEquiv_of_MultiBeta (M N : Term Var) (hM : M.LC) (hN : N.LC) : (M ↠βᶠ N) → M ≡β N := by
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

-- β-equivalence is preserved under →βᶠ
lemma BetaEquiv_of_BetaEquiv_and_step {Var : Type u} (M N O : Term Var) (hMN : M.BetaEquiv N) (hNO : N →βᶠ O) : M.BetaEquiv O :=
  Relation.EqvGen.trans M N O hMN (Relation.EqvGen.rel N O hNO)
