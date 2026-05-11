import Mathlib.Data.SetLike.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

import src.Basic
import src.CombinatoryAlgebra

/-! We derive from a given section-retraction `List α → α` the
    combinatory algebra structure on `Set α`.
-/

/-- An encoding of lists of `α`'s as `α`. -/
class Listing (α : Type) where
  fromList : List α → α
  toList : α → List α
  eq_list : ∀ xs, toList (fromList xs) = xs

/-- A set equipped with `Listing` has as its canonical element the encoding of `[]`. -/
instance Listing.inhabited {α : Type} [Listing α] : Inhabited α where
  default := fromList []

/-- [x] qua subset of elements listed by `x`. -/
@[reducible]
def toSet {α : Type} [Listing α] (x : α) : Set α := (Listing.toList x).Mem

@[simp]
theorem eq_toSet_fromList {α : Type} [Listing α] {ys : List α} :
  toSet (Listing.fromList ys) = ys.Mem := by
  ext ; unfold toSet ; rw [Listing.eq_list]

/-- We encode pairs as lists of length two. -/
def Listing.pair {α : Type} [Listing α] (x y : α) : α := fromList [x, y]

/-- The first projection from a pair. -/
def Listing.fst {α : Type} [Listing α] (x : α) : α := (toList x).head!

/-- The second projection from a pair. -/
def Listing.snd {α : Type} [Listing α] (x : α) : α := (toList x).get! (1: Fin (toList x).length)

/-- Computation rule for the first projection from a pair. -/
theorem Listing.eq_fst_pair {α : Type} [Listing α] (x y : α) : fst (pair x y) = x
  := by simp [fst, snd, pair, eq_list]

/-- Computation rule for the second projection from a pair. -/
theorem Listing.eq_snd_pair {α : Type} [Listing α] (x y : α) : snd (pair x y) = y
  := by
  simp
  simp [snd, pair]

namespace GraphModel

variable {α : Type} [Listing α]
open Listing

/-- A map `Set α → Set α` is continuous when its values are determined
    on finite subsets. This is continuity in the sense of Scott topology, but
    we avoid developing a general theory of domains, so we will specialize all
    definitions to the situation at hand. -/
def continuous (f : Set α → Set α) :=
  ∀ (S : Set α) (x : α), x ∈ f S ↔ ∃ y : α, toSet y ⊆ S ∧ (x ∈ f (toSet y))

/-- Monotonicity of a map `Set α → Set α` with respect to subset inclusion. -/
def monotone (f : Set α → Set α) := ∀ S T, S ⊆ T → f S ⊆ f T

/-- A continuous map is monotone -/
theorem continuous_monotone {f : Set α → Set α} : continuous f → monotone f := by
  intro Cf S T ST x xfS
  obtain ⟨y, yS, xfy⟩ := (Cf S x).mp xfS
  apply (Cf T x).mpr
  use y
  constructor
  · intro z zy ; exact ST (yS zy)
  · assumption

-- /-- Continuity of a binary map-/
def continuous₂ (f : Set α → Set α → Set α) :=
  ∀ S T x, x ∈ f S T ↔ ∃ y z, toSet y ⊆ S ∧ toSet z ⊆ T ∧ x ∈ f (toSet y) (toSet z)

-- /-- Monotonicity of a binary map.-/
def monotone₂ (f : Set α → Set α → Set α) :=
  ∀ (S S' T T'), S ⊆ S' → T ⊆ T' → f S T ⊆ f S' T'

/-- A continuous binary map is monotone. -/
theorem continuous₂_monotone₂ {f : Set α → Set α → Set α} :
  continuous₂ f → monotone₂ f := by
  intro Cf S S' T T' SS' TT' x xfST
  obtain ⟨y, z, yS, zT, xfyz⟩ := (Cf S T x).mp xfST
  apply (Cf S' T' x).mpr
  use y, z
  constructor
  · intro w wy ; exact SS' (yS wy)
  · constructor
    · intro w wz ; exact TT' (zT wz)
    · assumption

/-- If a binary map is continuous in each arguments separately, then it is continuous. -/
theorem continuous₂_separately (f : Set α → Set α → Set α) :
  (∀ S, continuous (f S)) →
  (∀ T, continuous (fun S => f S T)) →
  continuous₂ f := by
  intro Cf₁ Cf₂ S T x
  constructor
  · intro xfST
    obtain ⟨z, zT, xfSz⟩ := (Cf₁ S T x).mp xfST
    obtain ⟨y, zS, xfyz⟩ := (Cf₂ (toSet z) S x).mp xfSz
    use y ; use z
  · rintro ⟨y, z, yS, zT, xfyz⟩
    apply (Cf₁ S T x).mpr
    use z
    constructor
    · assumption
    · apply (Cf₂ (toSet z) S x).mpr
      use y

/-- A continuous binary map is continuous as a map of its first argument -/
theorem continuous₂_fst (h : Set α → Set α → Set α) :
  continuous₂ h → ∀ S, continuous (h S) := by
  intro Ch S T x
  constructor
  · intro xhST
    obtain ⟨y, z, yS, zT, xhyz⟩ :=  (Ch S T x).mp xhST
    use z
    constructor
    · assumption
    · exact continuous₂_monotone₂ Ch (toSet y) S (toSet z) (toSet z) yS (fun ⦃_⦄ a => a) xhyz
  · rintro ⟨z, zT, xhSz⟩
    exact continuous₂_monotone₂ Ch S S (toSet z) T (fun ⦃_⦄ a => a) zT xhSz

/-- A continuous binary map is contunuous as a map of its second argument -/
theorem continuous₂_snd (h : Set α → Set α → Set α) :
  continuous₂ h → ∀ T, continuous (fun S => h S T) := by
  intro Ch T S x
  constructor
  · intro xhST
    obtain ⟨y, z, yS, zT, xhyz⟩ :=  (Ch S T x).mp xhST
    use y
    constructor
    · assumption
    · exact continuous₂_monotone₂ Ch (toSet y) (toSet y) (toSet z) T (fun ⦃_⦄ a => a) zT xhyz
  · rintro ⟨y, yS, xhyT⟩
    exact continuous₂_monotone₂ Ch (toSet y) S T T yS (fun ⦃_⦄ a => a) xhyT

/-- The identity map is continuous. -/
def continuous_id : continuous (@id (Set α)) := by
  intros S x
  simp only [id_eq]
  constructor
  case mp =>
    intro xS
    use (fromList [x])
    constructor
    · intro y
      rw [eq_toSet_fromList]
      simp only [Membership.mem, Set.Mem]
      rintro (H | ⟨A, ⟨⟩⟩) ; assumption
    · rw [eq_toSet_fromList]
      constructor
  case mpr =>
    rintro ⟨y, yS, xy⟩
    exact yS xy

/-- A constant map is continuous. -/
def continuous_const (T : Set α) : continuous (fun (_ : Set α) => T) := by
  intro S x
  simp only [exists_and_right, iff_and_self]
  intro xT
  use (fromList [])
  rw [eq_toSet_fromList]
  rintro x ⟨⟩

/-- If `f` is continuous then any finite subset of `f S` is already a subset of some
    `f S'` where `S' ⊆ S` is finite (in the statement `S'` is `toSet z`).
    The lemma is used in the theorem showing that composition preserves continuity. -/
lemma continuous_finite {f : Set α → Set α} (ys : List α) (S : Set α) :
  continuous f → (∀ y, y ∈ ys → y ∈ f S) → ∃ z, toSet z ⊆ S ∧ ∀ y, y ∈ ys → y ∈ f (toSet z) := by
  intro Cf ysfS
  induction ys
  case nil =>
    use (fromList [])
    constructor
    · rw [eq_toSet_fromList] ; rintro _ ⟨⟩
    · rintro _ ⟨⟩
  case cons y ys ih =>
    have H : ∀ z ∈ ys, z ∈ f S := by
      intro z zys
      apply ysfS
      exact List.mem_cons_of_mem _ zys
    obtain ⟨zs, zsS, ysfzs⟩ := ih H
    have h₁ : y ∈ y :: ys := by grind
    obtain ⟨z, zS, yfz⟩ := (Cf S y).mp (ysfS y  h₁)
    use (fromList (toList z ++ toList zs))
    rw [eq_toSet_fromList]
    constructor
    · intro w wzws
      cases List.mem_append.mp wzws
      case inl => apply zS ; assumption
      case inr H => apply zsS ; assumption
    · intro w wyys
      cases wyys
      case head =>
        apply continuous_monotone Cf (toSet z)
        · intro w wz
          apply List.mem_append.mpr ; left ; exact wz
        · assumption
      case tail =>
        apply continuous_monotone Cf (toSet zs)
        · intro w wzs
          apply List.mem_append.mpr ; right ; exact wzs
        · apply ysfzs ; assumption

-- /-- The composition of continuous maps is continuous. -/
theorem continuous_compose (f g : Set α → Set α) :
  continuous f → continuous g → continuous (f ∘ g) := by
  intro Cf Cg S x
  constructor
  · intro xfgS
    obtain ⟨y, ygS, xfy⟩ := (Cf (g S) x).mp xfgS
    unfold toSet at ygS
    obtain ⟨z, zS, ygz⟩ := continuous_finite (toList y) S Cg ygS
    use z
    constructor
    · assumption
    · apply continuous_monotone Cf (toSet y) (g (toSet z))
      · intro z zy
        apply ygz
        apply zy
      · assumption
  · rintro ⟨y, yS, xfgy⟩
    apply continuous_monotone Cf (g (toSet y)) (g S)
    · exact continuous_monotone Cg _ _ yS
    · assumption

/-- The composition of a binary continuous map and continuous maps is continuous. -/
theorem continuous₂_compose (f g : Set α → Set α) (h : Set α → Set α → Set α) :
  continuous f →
  continuous g →
  continuous₂ h ->
  continuous (fun U => h (f U) (g U)) := by
  intros Cf Cg Ch U x
  constructor
  · intro xhfUgU
    obtain ⟨y, z, yfU, zgU, xhyz⟩ := (Ch (f U) (g U) x).mp xhfUgU
    obtain ⟨u, uU, yfu⟩ := continuous_finite (toList y) U Cf yfU
    obtain ⟨v, vU, zgv⟩ := continuous_finite (toList z) U Cg zgU
    use (fromList (toList u ++ toList v))
    rw [eq_toSet_fromList]
    constructor
    · intro w wuv
      cases (List.mem_append.mp wuv)
      case inl wu => exact uU wu
      case inr wv => exact vU wv
    · apply continuous₂_monotone₂ Ch (f (toSet u)) _ (g (toSet v)) _
      -- unfold toSet
      · apply continuous_monotone Cf
        intro ; apply List.mem_append_left _
      · apply continuous_monotone Cg
        intro ; apply List.mem_append_right _
      · exact continuous₂_monotone₂ Ch _ _ _ _ yfu zgv xhyz
  · rintro ⟨y, yU, xhfygy⟩
    have fyfU : f (toSet y) ⊆ f U := continuous_monotone Cf _ _ yU
    have gygU : g (toSet y) ⊆ g U := continuous_monotone Cg _ _ yU
    exact continuous₂_monotone₂ Ch _ _ _ _ fyfU gygU xhfygy

/-- The graph of a function -/
def graph (f : Set α → Set α) : Set α :=
  fun x => fst x ∈ f (toSet (snd x))

/-- Currying combined with graph is continuous -/
def continuous_graph (f : Set α → Set α → Set α) :
  continuous₂ f → continuous (fun S => graph (f S)) := by
  intro fC S x
  have fC₁ := continuous₂_fst f fC
  have fC₂ := continuous₂_snd f fC
  constructor
  · exact (fC₂ (toSet (snd x)) S (fst x)).mp
  · intro ⟨y, yS, H⟩
    apply (fC₁ S (toSet (snd x)) (fst x)).mpr
    use (snd x)
    constructor
    · trivial
    · exact continuous_monotone (fC₂ (toSet (snd x))) _ _ yS H

/-- Combinatory application on the graph model -/
def apply (S : Set α) : Set α → Set α :=
  fun T x => ∃ y, toSet y ⊆ T ∧ pair x y ∈ S

@[reducible]
instance Listing.hasDot : HasDot (Set α) where dot := apply

lemma Listing.hasDot_Dot (A B: Set α) : A ⬝ B = apply A B := rfl

/-- Application is monotone. -/
theorem apply.monotone₂ : monotone₂ (@apply α _) := by
  rintro S S' T T' SS' TT' x ⟨y, yT, yzS⟩
  use y
  constructor
  · intro w wy ; exact TT' (yT wy)
  · exact SS' yzS

/-- Application is monotone in the first argument. -/
theorem apply.monotone_fst {T : Set α} : monotone (fun S => apply S T) := by
  intro S S' SS'
  apply apply.monotone₂ _ _ _ _ SS' (fun ⦃_⦄ a => a)

/-- Application is monotone in the second argument. -/
theorem apply.monotone_snd {S : Set α} : monotone (apply S) := by
  intro T T' TT'
  apply apply.monotone₂ _ _ _ _ (fun ⦃_⦄ a => a) TT'

/-- Application is continuous in the first argument. -/
theorem apply.continuous_fst (T : Set α) : continuous (apply T) := by
  intros S x
  constructor
  · rintro ⟨y, yS, xyT⟩
    use y
    constructor
    · assumption
    · use y
  · rintro ⟨y, yS, xTy⟩
    apply apply.monotone_snd _ _ yS xTy

/-- Application is continuous in the second argument. -/
theorem apply.continuous_snd (S : Set α) : continuous (fun T => apply T S) := by
  intros T x
  constructor
  · rintro ⟨y, yS, xyT⟩
    use (fromList [pair x y])
    constructor
    · rw [eq_toSet_fromList]
      intro z zxy
      cases zxy
      case head => assumption
      case tail H => cases H
    · use y
      constructor
      · assumption
      · rw [eq_toSet_fromList] ; constructor
  · rintro ⟨y, yT, z, zS, xyz⟩
    unfold apply
    use z
    constructor
    · assumption
    · exact yT xyz

/-- Application is continuous. -/
theorem apply.continuous₂ : continuous₂ (@apply α _) := by
  apply continuous₂_separately
  · apply apply.continuous_fst
  · apply apply.continuous_snd

theorem eq_apply_graph (f : Set α → Set α) : continuous f → apply (graph f) = f := by
  intro Cf
  ext S x
  constructor
  case mp =>
    simp only [apply, graph, Membership.mem, Set.Mem]
    rintro ⟨y, yS, H⟩
    rw [eq_fst_pair, eq_snd_pair] at H
    apply (Cf S x).mpr
    use y
    trivial
  case mpr =>
    intro xfS
    obtain ⟨y, ys, H⟩ := (Cf S x).mp xfS
    use y
    constructor
    · assumption
    · simp only [graph, Membership.mem, Set.Mem]
      rw [eq_fst_pair, eq_snd_pair]
      assumption

def K : Set α := graph (fun A => graph (fun _ => A))

theorem eq_K {A B : Set α} : K ⬝ A ⬝ B = A := by
  unfold K
  simp only [Listing.hasDot_Dot]
  rw [eq_apply_graph, eq_apply_graph]
  · apply continuous_const
  · apply continuous_graph
    apply continuous₂_separately
    · apply continuous_const
    · intro ; apply continuous_id

def S : Set α := graph (fun A => graph (fun B => graph (fun C => (A ⬝ C) ⬝ (B ⬝ C))))

lemma S.continuous₁ {B C : Set α} : continuous (fun A => (A ⬝ C) ⬝ (B ⬝ C)) := by
  apply continuous₂_compose (fun A => A ⬝ C) (fun _ => B ⬝ C)
  · apply apply.continuous_snd
  · apply continuous_const
  · apply apply.continuous₂

lemma S.continuous₂ {A C : Set α} : continuous (fun B => (A ⬝ C) ⬝ (B ⬝ C)) := by
  apply continuous₂_compose (fun _ => A ⬝ C) (fun B => B ⬝ C)
  · apply continuous_const
  · apply apply.continuous_snd
  · apply apply.continuous₂

lemma S.continuous₃ {A B : Set α} : continuous (fun C => (A ⬝ C) ⬝ (B ⬝ C)) := by
  apply continuous₂_compose (apply A) (apply B) apply
  · apply apply.continuous_fst
  · apply apply.continuous_fst
  · apply apply.continuous₂

theorem eq_S {A B C : Set α} : S ⬝ A ⬝ B ⬝ C = (A ⬝ C) ⬝ (B ⬝ C) := by
  simp only [S, Listing.hasDot_Dot]
  rw [eq_apply_graph, eq_apply_graph, eq_apply_graph]
  · apply S.continuous₃
  · apply continuous_graph
    apply continuous₂_separately
    · apply S.continuous₃
    · apply S.continuous₂
  · apply continuous_graph
    apply continuous₂_separately
    · intro ; apply continuous_graph
      apply continuous₂_separately
      · apply S.continuous₃
      · apply S.continuous₂
    · intro ; apply continuous_graph
      apply continuous₂_separately
      · intro ; apply S.continuous₃
      · intro ; apply S.continuous₁

/-- The graph model -/
instance isCA : CA (Set α) where
  K := K
  S := S
  eq_K := eq_K
  eq_S := eq_S

def F (X : Set α) (Y : Set α) : Set α :=
  apply X Y

def G_old (f : Set α → Set α) : Set α :=
fun x => ∃ b β, x = pair b β ∧ b ∈ f (toSet β)

def G (f : Set α → Set α) : Set α := { x | ∃ b β, x = pair b β ∧ b ∈ f (toSet β) }

lemma G_old_eq_G (f : Set α → Set α):  G_old f = G f := by
  unfold G
  unfold G_old
  ext z
  constructor
  · rintro ⟨a, b, rfl, hb⟩
    use a, b
  · rintro ⟨x, y, rfl, hx⟩
    use x, y

lemma pair_iff (a b x y : α): pair x y = pair a b ↔ (x=a ∧ y=b) := by sorry

lemma fY_set (f : Set α → Set α) (Y : Set α)
(h : continuous f):
f Y = { x | ∃ y, toSet y ⊆ Y ∧ x ∈ f (toSet y) } := by
  unfold continuous at h
  ext x
  constructor
  · intro hx
    specialize h Y x
    obtain ⟨h₁, h₂ ⟩ := h
    apply h₁ hx
  · rintro ⟨y, h₁, h₂⟩
    exact (continuous_monotone h (toSet y) Y h₁) h₂

lemma F_G_eq_id (f : Set α → Set α) (Y : Set α) (h : continuous f ) :
F (G f) Y = f Y := by
  rw [fY_set f Y h]
  unfold F G apply
  simp
  ext x
  constructor
  · rintro ⟨y, _, a, b, heq, _⟩
    have h₁ : x= a := by
      rw [pair_iff] at heq
      lia
    have h₂ : y= b := by
      rw [pair_iff] at heq
      lia
    rw [h₁]
    use b
    constructor
    · rw [<-h₂]
      assumption
    · assumption
  · rintro ⟨y, h₁, _⟩
    use y, h₁, x, y

end GraphModel

namespace Cslib
namespace LambdaCalculus.LocallyNameless.Untyped.Term
open Listing

variable {α : Type} [Listing α]
variable (i : α → α)
variable (hi : Function.Injective i)
variable {A : Set α}

def apply (S : Set α) : Set α → Set α :=
  fun T b => ∃ β, toSet β ⊆ T ∧ pair b β ∈ S

def F (X : Set α) (Y : Set α) : Set α :=
  apply X Y

def G (f : Set α → Set α) : Set α := { x | ∃ b β, x = pair b β ∧ b ∈ f (toSet β) }

universe u
variable {Var : Type u} [DecidableEq Var]

@[simp]
def subst_rho (ρ : ℕ → Set α) (n : ℕ) (d : Set α) : ℕ → Set α :=
  fun x => if x = n then d else ρ x

lemma subst_rho_zero (ρ : ℕ → Set α) (n : ℕ) (d : Set α) :
subst_rho ρ 0 d 0 = d
 := by
 simp

def DeBruijnShift (ρ : ℕ → Set α ): ℕ → Set α :=
  fun n => ρ (n + 1)

@[simp]
def Interp (ρ : ℕ → Set α) (σ: Var → Set α) : Term Var → Set α
| fvar x  => (σ x)
| bvar n  => (ρ n)
| app a b => (F (Interp ρ σ a) (Interp ρ σ b))
| abs e   =>  G (fun d => (Interp (subst_rho (DeBruijnShift ρ) 0 d) σ e) )


variable {ρ : ℕ → Set α}
variable {σ : Var → Set α}
variable {M : Term Var}

notation "〚"M"〛_{"ρ","σ"}" => Interp ρ σ M

#check 〚 M 〛_{ρ,σ}

@[reducible]
instance UntypedLambdaCalculus.hasDot : HasDot (Term Var) where dot := app

def K : Term Var := abs (abs $ bvar 1) -- λxy.x
def S : Term Var := abs (abs (abs (app (app (bvar 2) (bvar 0)) (app (bvar 1) (bvar 2)))))-- λxyz.xz (yz) =  λ210.02 (12)
def Kstar : Term Var := abs (abs $ bvar 0) -- λxy.y
def id : Term Var := abs (bvar 0)
def id_id : Term Var := app id id
def ω : Term Var := abs (app (bvar 0) (bvar 0))
def Ω : Term Var := app ω ω

#check 〚 id 〛_{ρ,σ}

-- Example 3.1
lemma interp_id :
〚 id 〛_{ρ,σ} = {x | ∃ b, ∃ (β : α), x = (pair b β) ∧ b ∈ toSet β}
 := by
  unfold id
  unfold Interp
  unfold G
  ext x
  constructor
  · intro h
    obtain ⟨b, ⟨β, ⟨h₁, h₂⟩⟩⟩ := h
    use b, β
    constructor
    · assumption
    · dsimp [Interp] at h₂
      assumption
  · intro h
    obtain ⟨b, ⟨β, ⟨h₁, h₂⟩⟩⟩ := h
    use b, β
    constructor
    · assumption
    · dsimp [Interp]
      assumption


lemma interp_id_id :
〚 app id id 〛_{ρ,σ} = 〚 id 〛_{ρ,σ}
 := by
  simp
  unfold F
  unfold apply
  ext b
  have h₁: ∀ b β, pair b β ∈ 〚id〛_{ρ,σ} ↔ b ∈ toSet β := by
    intro a β
    sorry
  constructor
  · intro h
    obtain ⟨β, h⟩ := h
    rw [h₁ b β] at h
    grind
  · intro h
    simp at *
    obtain ⟨b', β, h₂, h₃⟩ := h
    use β
    simp at *
    rw [h₂]
    specialize (h₁ ((pair b' β)) β)
    rw [h₁]
    rw [<-h₂]
    sorry

lemma interp_k :
〚 K 〛_{ρ,σ} = {x | ∃ β γ c, x = (pair (pair c γ) β) }
 := by
  unfold K
  unfold Interp
  unfold G
  ext x
  simp
  constructor
  · intro h
    obtain ⟨b, β, h₁, h₂⟩ := h
    obtain ⟨c, γ, heq, h₂⟩ := h₂
    use β, γ, c
    rwa [heq] at h₁
  · intro h
    obtain ⟨β, γ, c, h⟩ := h
    use ((pair c γ)), β
    constructor
    · assumption
    · unfold G
      simp
      use c
      constructor
      · use γ
      · simp [DeBruijnShift]
        sorry


lemma interp_Omega :
〚 Ω 〛_{ρ,σ} = ∅
 := by
  -- grind
  -- unfold Ω
  -- unfold Interp
  -- unfold F
  -- unfold apply
  -- grind
  sorry



--  OLD STUFF!!!
-- lemma interp_abs_M (M : Term Var) :
-- 〚 abs M 〛_{ρ,σ} = {x | ∃ (β : α), ∃ b, x = (pair β, b)}
-- x | ∃ (β : α), ∃ b, x = (pair β b)
-- -- ∧ b ∈ 〚 abs M 〛_{ ρ } }
--  := by
--   sorry

-- inductive Interp where
--   | empty : BinTree
--   | node  : BinTree → BinTree → BinTree

-- variable {A : Set α}

-- inductive BinTree where
--   | empty : BinTree
--   | node  : BinTree → BinTree → BinTree

-- namespace BinTree



def D_i (A : Set α) : ℕ → Set α
  | 0       => A
  | n + 1 =>  Set.union (D_i A n) { x | ∃ β b, x = pair β b ∧ toSet β ⊆ (D_i A n) ∧ b ∈ (D_i A n) }

def D_A : Set α := Set.iUnion (D_i A)


-- def rank : ℕ → Set α
--   | 0       => A
--   | n + 1 =>  Set.union (D_A n) { x | ∃ β b, x = pair β b ∧ toSet β ⊆ (D_A n) ∧ b ∈ (D_A n) }

-- inductive D_A (n: ℕ) where
-- | 0 : A
-- | S : Expr
-- | app : Expr → Expr → Expr





end Ours
