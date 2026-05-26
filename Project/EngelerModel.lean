import Project.LambdaTheory.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Project.AndrejBauer.GraphModel

open GraphModel
open Listing

namespace F_G_equal

variable {α : Type} [Listing α]

-- We have defined apply as a applicative structure. We now follow the paper to define
-- F as apply, and then G as the inverse, such that F (G f) Y = f Y
def F (X : Set α) (Y : Set α) : Set α := apply X Y

def G (f : Set α → Set α) : Set α := { x | ∃ b β, x = pair b β ∧ b ∈ f (toSet β) }

-- Helper lemmer for our proof of F (G f) Y = f Y
@[simp]
lemma pair_iff (a b x y : α): pair x y = pair a b ↔ (x=a ∧ y=b) := by
  constructor
  · intro h
    have fst := congrArg fst h
    have snd := congrArg snd h
    rw [Listing.eq_fst_pair, Listing.eq_fst_pair] at fst
    rw [Listing.eq_snd_pair, Listing.eq_snd_pair] at snd
    exact ⟨fst, snd⟩
  · intro ⟨hxa, hyb⟩
    congr

theorem F_G_eq_id (f : Set α → Set α) (Y : Set α) (h : continuous f ) :
F (G f) Y = f Y := by
  unfold F G apply
  ext x
  constructor
  · rintro ⟨y, h₁, _, b, hh, h₂⟩
    simp_all only [pair_iff]
    have := continuous_monotone h
    exact Set.mem_of_subset_of_mem (this (toSet b) Y h₁) h₂
  · intro _
    obtain ⟨h₁, _⟩ := h Y x
    simp_all only [forall_const, Set.mem_setOf_eq, pair_iff, ↓existsAndEq, and_true,
      exists_eq_left']
    exact Set.mem_of_subset_of_mem (fun _ y ↦ y) h₁

end F_G_equal
