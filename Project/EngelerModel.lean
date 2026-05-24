import Project.LambdaTheory.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Project.AndrejBauer.GraphModel

open GraphModel
open Listing

namespace F_G_equal

variable {α : Type} [Listing α]

-- We have defined apply as a applicative structure. We now follow the paper to define
-- F as apply, and then G as the inverse, such that F (G f) Y = f Y
def F (X : Set α) (Y : Set α) : Set α :=
  apply X Y

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

-- Helper lemmer for our proof of F (G f) Y = f Y
lemma fY_set {f : Set α → Set α} {Y : Set α} (h : continuous f):
f Y = { x | ∃ y, toSet y ⊆ Y ∧ x ∈ f (toSet y) } := by
  ext x
  constructor
  · intro hx
    obtain ⟨h₁, h₂⟩  := (h Y x)
    simp_all
  · rintro ⟨y, h₁, h₂⟩
    have := continuous_monotone h (toSet y) Y h₁
    exact Set.mem_of_subset_of_mem this h₂

-- Shorter proof due to fY_set being defined as a the above set
lemma F_G_eq_id (f : Set α → Set α) (Y : Set α) (h : continuous f ) :
F (G f) Y = f Y := by
  rw [fY_set h]
  unfold F G apply
  ext x
  constructor
  · rintro ⟨_, _, _, b, _, _⟩
    simp_all
    use b
  · rintro ⟨b, _, _⟩
    simp_all
    use b

end F_G_equal
