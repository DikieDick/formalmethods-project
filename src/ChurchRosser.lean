import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence


namespace Cslib
namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Term

universe u
variable {Var : Type u} [HasFresh Var] [DecidableEq Var]


def multiBeta (M N : Term Var) : Prop := M ↠βᶠ N

#check Relation.ChurchRosser -- Cslib
-- #check Relation.church_rosser -- Mathlib

theorem ChurchRosserMultiBeta : Relation.ChurchRosser (@multiBeta Var) := by
  unfold multiBeta
  intro x y h_equiv

  have h_equiv_base : Relation.EqvGen FullBeta x y := by
    induction h_equiv
    case refl => apply Relation.EqvGen.refl
    case symm ih => apply Relation.EqvGen.symm; assumption
    case rel h =>
      induction h
      case refl a b => apply Relation.EqvGen.refl
      case tail a b c d e f g h =>
        apply Relation.EqvGen.trans _ d
        · assumption
        · apply Relation.EqvGen.rel
          assumption
    case trans a b c d e f g h i =>
      apply Relation.EqvGen.trans _ d
      · assumption
      · assumption

  have h_cr := Relation.Confluent.toChurchRosser confluence_beta h_equiv_base

  obtain ⟨z, hxz, hyz⟩ := h_cr
  use z
  constructor
  · apply Relation.ReflTransGen.single
    exact hxz
  · apply Relation.ReflTransGen.single
    exact hyz

theorem ChurchRosserMultiBeta' {Var : Type u} :
    ∀ (M N : Term Var), multiBeta M N → ∃ P : Term Var, multiBeta M P ∧ multiBeta N P := by
  intro M N hMN
  refine ⟨N, hMN, ?_⟩
  exact Relation.ReflTransGen.refl

end LambdaCalculus.LocallyNameless.Untyped.Term
end Cslib
