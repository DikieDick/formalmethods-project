import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Project.BetaEquiv

namespace Cslib
namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Term

universe u
variable {Var : Type u} [instFresh: HasFresh Var] [instDecEq: DecidableEq Var]


def multiBeta (M N : Term Var) : Prop := M ↠βᶠ N

-- #check Relation.ChurchRosser -- Cslib
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
      case tail c d e f g h =>
        apply Relation.EqvGen.trans _ d
        · assumption
        · apply Relation.EqvGen.rel
          assumption
    case trans c d e f g h i =>
      apply Relation.EqvGen.trans _ d
      · assumption
      · assumption
  -- Could also prove this by the fact that ReflTransGen of ReflTransGen r is just ReflTransGen r ?
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

theorem ChurchRosser (M P₁ P₂ : Term Var) (h₁ : multiBeta M P₁) (h₂ : multiBeta M P₂) :
  ∃ Q : Term Var, multiBeta P₁ Q ∧ multiBeta P₂ Q := by
  have confl := @confluence_beta Var instFresh instDecEq
  specialize confl h₁ h₂
  exact confl

theorem common_reduct_of_BetaEquiv (M N : Term Var) (h : BetaEquiv M N) :
  ∃ Q : Term Var, multiBeta M Q ∧ multiBeta N Q := by
  induction h with
  | refl M =>
    use M
    exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | rel M N h =>
    use N
    exact ⟨Relation.ReflTransGen.single h, Relation.ReflTransGen.refl⟩
  | symm M N h ih =>
    rcases ih with ⟨Q, hMQ, hNQ⟩
    exact ⟨Q, ⟨hNQ, hMQ⟩⟩
  | trans M N O h1 h2 ih1 ih2 =>
    rcases ih1 with ⟨Q, hMQ, hNQ⟩
    rcases ih2 with ⟨P, hNP, hOP⟩
    obtain ⟨R, hQR, hPR⟩ := ChurchRosser N Q P hNQ hNP
    exact ⟨R, ⟨Relation.ReflTransGen.trans hMQ hQR, Relation.ReflTransGen.trans hOP hPR⟩⟩

end LambdaCalculus.LocallyNameless.Untyped.Term
end Cslib
