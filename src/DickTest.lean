import Mathlib

variable {L : Type} [CompleteLattice L] (A : Set L)

def sup []

notation "⨆" A => sSup A
notation "⨅" A => sInf A
notation "⇑" A => upperClosure A
notation "⇓" A => lowerClosure A

def fixedPoint (f : L -> L) (a : L) := f a = a

#check OrderHom
#check OrderHom.lfp
-- Knarster-Tarski:
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/FixedPoints.html#fixedPoints.completeLattice

variable (f : L →o L)
#check f
#check f.toFun
#check f.monotone'

-- THIS IS NEW MATERIAL? :) maybe?

-- ⊔ A = ⊔(↓A)
lemma sSup_eq_sSup_lowerClosure : sSup A = sSup (lowerClosure A)  := by
  apply le_antisymm
  · apply sSup_le_sSup
    intro x hx
    simp only [SetLike.mem_coe, mem_lowerClosure]
    use x
  · apply sSup_le
    intro x ⟨a, ha, hxa⟩
    #check hxa.trans
    apply hxa.trans
    apply le_sSup ha

-- ⊓ A = ⊓(↑A).
lemma sInf_eq_sInf_upperClosure : sInf A = sInf (upperClosure A) := by
  apply le_antisymm
  · exact le_sInf (fun x ⟨a, ha, hax⟩ => (sInf_le ha).trans hax)
  · exact sInf_le_sInf (fun x hx => ⟨x, hx, le_rfl⟩)

-- we start from an applicative structure (M; ·), which just means a set endowed
-- with a binary function “·”. This dot will often be omitted.
class ApplicativeStructure (M : Type) where
  op : M → M → M

-- Definition 56. A function f : M → M is representable in M if there is some d ∈ M
-- such that f(x) = dx. We let R(M ) be the set of functions which are representable in M
def representable (M : Type) [ApplicativeStructure M] (f : M → M) : Prop :=
  ∃ d : M, ∀ x : M, f x = ApplicativeStructure.op d x

def representableIn (M : Type) [ApplicativeStructure M] : Set (M → M) :=
  { f | representable M f }

notation "R(" M ")" => representableIn M
