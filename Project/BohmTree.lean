import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Mathlib.Tactic
import Coinductive
import Project.ChurchRosser

open Cslib
open LambdaCalculus.LocallyNameless.Untyped
open Coinductive
open Lean.Order

universe u

variable {Var : Type u}

@[grind]
inductive IsHeadRedexApp : Term Var → Prop where
  | base N P₁ : IsHeadRedexApp ((Term.abs N).app P₁)
  | step T Pₙ : IsHeadRedexApp T → IsHeadRedexApp (T.app Pₙ)

@[grind]
inductive IsHeadRedex : Term Var → Prop where
  | base T : IsHeadRedexApp T → IsHeadRedex T
  | step T : IsHeadRedex T → IsHeadRedex (Term.abs T)

@[grind]
inductive IsHeadNormalApp : Term Var → Prop where
  | base_free y : IsHeadNormalApp (Term.fvar y)
  | base_bound n : IsHeadNormalApp (Term.bvar n)
  | step T Pₙ : IsHeadNormalApp T → IsHeadNormalApp (T.app Pₙ)

@[grind]
inductive IsHeadNormal : Term Var → Prop where
  | base T : IsHeadNormalApp T → IsHeadNormal T
  | step T : IsHeadNormal T → IsHeadNormal (Term.abs T)

-- Lemma 3.2
lemma normal_or_redex (T : Term Var) : IsHeadRedex T ∨ IsHeadNormal T := by
  induction' T with T T T ih T₁ T₂ ih1 ih2
  · right
    apply IsHeadNormal.base
    apply IsHeadNormalApp.base_bound
  · right
    apply IsHeadNormal.base
    apply IsHeadNormalApp.base_free
  · cases ih
    · left ; apply IsHeadRedex.step ; assumption
    · right; apply IsHeadNormal.step ; assumption
  · induction T₁
    · right ; apply IsHeadNormal.base ; apply IsHeadNormalApp.step ; apply IsHeadNormalApp.base_bound
    · right ; apply IsHeadNormal.base ; apply IsHeadNormalApp.step ; apply IsHeadNormalApp.base_free
    · left ; apply IsHeadRedex.base ; apply IsHeadRedexApp.base
    · rcases ih1 with ih1 | ih1
      · cases ih1 ; left ; apply IsHeadRedex.base ; apply IsHeadRedexApp.step ; assumption
      · cases ih1 ; right ; apply IsHeadNormal.base ; apply IsHeadNormalApp.step ; assumption

@[grind]
inductive List.BetaEquiv : List (Term Var) → List (Term Var) → Prop where
  | base : [].BetaEquiv []
  | step as bs T₁ T₂ : T₁.BetaEquiv T₂ → as.BetaEquiv bs → (T₁ :: as).BetaEquiv (T₂ :: bs)

lemma List.BetaEquiv_length {L₁ L₂ : List (Term Var)} : L₁.BetaEquiv L₂ → L₁.length = L₂.length := by
  induction L₁ generalizing L₂ <;> induction L₂
  case nil.nil => simp
  case nil.cons => grind
  case cons.nil => grind
  case cons.cons ih _ _ _ =>
    simp_all
    intro h
    apply ih
    grind

lemma BetaEquiv_helper {n} {L₁ L₂ : Vector (Term Var) n} (h : L₁.toList.BetaEquiv L₂.toList) : ∀ (x : Fin n), L₁[x] ≡β L₂[x] := by
  sorry

def bfvar (Var : Type u) := { v : Term Var // (exists n, v = Term.bvar n) ∨ (exists v', v = Term.fvar v') }

@[simp]
def nfoldAbs := Nat.iterate (@Term.abs Var)

@[simp]
def nfoldOpen : List Var → Term Var → Term Var
| [], T => T
| a :: as, T => nfoldOpen as (T.open' (Term.fvar a))

@[simp]
def nfoldApp : List (Term Var) → Term Var → Term Var
| [], T => T
| a :: as, T => nfoldApp as (T.app a)

lemma BetaEquiv_of_BetaEquiv_abs (P Q : Term Var) (lc_P : P.LC) (lc_Q : Q.LC) (h : P.abs ≡β Q.abs) : P ≡β Q := by
  cases h
  case rel h =>
    apply Relation.EqvGen.rel
    cases h
    case a.base h =>
      constructor
      sorry
    case a.abs xs a =>
      sorry
  case symm h => sorry
  case refl => sorry
  case trans R h₁ h₂ => sorry

lemma destruct_BetaEquiv_nfoldAbs (n : ℕ) (P Q : bfvar Var) (h : nfoldAbs n P.val ≡β nfoldAbs n Q.val) : P.val ≡β Q.val := by
  induction n
  case zero => exact h
  case succ n ih =>
    simp [nfoldAbs] at h ih
    apply ih
    sorry

-- Reduction does not affect the number of leading abstractions, the head variable, or the number of arguments of the head-variable
lemma reduction_preservation_fvar (n m : ℕ) (y z : bfvar Var) (Ps Qs : List (Term Var)) :
    (nfoldAbs n (nfoldApp Ps y.val)).multiBeta (nfoldAbs m (nfoldApp Qs z.val)) →
    n = m ∧ y = z ∧ Ps.BetaEquiv Qs := by
  intros h
  sorry

lemma reduction_preservation_fvar' (n : ℕ) (y : bfvar Var) (Ps : List (Term Var)) (p : Term Var):
    (nfoldAbs n (nfoldApp Ps y.val)).multiBeta p →
    exists Qs,
    p = (nfoldAbs n (nfoldApp Qs y.val)) ∧ Ps.BetaEquiv Qs := by
  intros h
  sorry

def hasAsHnf (T : Term Var) (n : ℕ) (Ps : List (Term Var)) (y : bfvar Var) :=
  let T' := nfoldAbs n (nfoldApp Ps y.val) ; IsHeadNormal T' ∧ T.BetaEquiv T'

def hasHnf (T : Term Var) := exists n L y, hasAsHnf T n L y

lemma HnfEq_of_BetaEquiv (M N : Term Var) (hMN : M.BetaEquiv N) n Ps y (h : hasAsHnf M n Ps y) : hasAsHnf N n Ps y := by
  obtain ⟨hl, hr⟩ := h
  refine ⟨hl, ?_⟩
  apply Relation.EqvGen.trans N M _ hMN.symm hr

-- Lemma 3.5
lemma hnfs_similar_fvar [HasFresh Var] [DecidableEq Var] (n m : ℕ) (y z : bfvar Var) (Ps Qs : List (Term Var)) (M : Term Var) :
    M.BetaEquiv (nfoldAbs n (nfoldApp Ps y.val)) →
    M.BetaEquiv (nfoldAbs m (nfoldApp Qs z.val)) →
    n = m ∧ y = z ∧ Ps.BetaEquiv Qs := by
  intros hn hm
  apply Relation.EqvGen.symm _ _ at hn
  have : (nfoldAbs n (nfoldApp Ps y.val)) ≡β (nfoldAbs m (nfoldApp Qs z.val)) := Relation.EqvGen.trans _ _ _ hn hm
  have ⟨Q, h₁, h₂⟩ := Term.common_reduct_of_BetaEquiv _ _ this
  have ⟨Qs, hq₁, hqs₁⟩ := reduction_preservation_fvar' _ _ _ _ h₁
  have ⟨Qs, hq₂, hqs₂⟩ := reduction_preservation_fvar' _ _ _ _ h₂
  cases hq₁
  have ⟨a, b, h⟩ : exists a b : Term Var, nfoldAbs n a = nfoldAbs m b := sorry

  sorry

inductive BöhmTreeF (Var : Type u) (T : Type u) : Type u where
  | no_hnf
  | hnf (num_children : ℕ) (num_abstractions : ℕ) (v : bfvar Var) (branches : ULift (Fin num_children) → T)

instance : Inhabited (BöhmTreeF Var PUnit) where default := .no_hnf

inductive BöhmTreeF.in : Type u where
  | no_hnf
  | hnf (num_children : ℕ) (num_abstractions : ℕ) (v : bfvar Var)

instance : PF (BöhmTreeF Var) where
  P := ⟨BöhmTreeF.in, fun
    | .no_hnf => PEmpty
    | .hnf nc na v => ULift (Fin nc)⟩
  unpack
    | .no_hnf => .obj (.no_hnf) nofun
    | .hnf nc na v f => .obj (.hnf nc na v) f
  pack
    | .obj (.no_hnf) _ => .no_hnf
    | .obj (.hnf nc na v) f => .hnf nc na v f
  unpack_pack := by rintro _ ⟨⟩ <;> simp
  pack_unpack := by rintro _ (⟨⟨⟩, _⟩ | ⟨⟨⟩⟩) <;> simp ; funext x ; cases x

abbrev BöhmTree (Var : Type u) := CoInd (BöhmTreeF Var)
abbrev BöhmTreeN (Var : Type u) (n : Nat) : Type u := CoIndN (BöhmTreeF Var) n

def BöhmTree.fold (t : (BöhmTreeF Var) (BöhmTree Var)) : (BöhmTree Var) := CoInd.fold _ t
def BöhmTree.unfold (t : (BöhmTree Var)) : (BöhmTreeF Var) (BöhmTree Var) := CoInd.unfold _ t
def BöhmTree.no_hnf : (BöhmTree Var) := BöhmTree.fold .no_hnf
def BöhmTree.hnf (num_children : ℕ) (num_abstractions : ℕ) (base_var : bfvar Var) (subtrees : ULift (Fin num_children) → (BöhmTree Var)) : (BöhmTree Var) := BöhmTree.fold (.hnf num_children num_abstractions base_var subtrees)

@[simp]
def BöhmTreeNode {Var : Type u} [DecidableEq Var]: bfvar Var → List Var → bfvar Var
  | ⟨Term.bvar n, _⟩, L => ⟨Term.bvar n, by simp⟩
  | ⟨Term.fvar v, _⟩, L => match List.idxsOf v L with
    | idx :: _ => ⟨Term.bvar idx, by simp⟩
    | [] => ⟨Term.fvar v, by simp⟩

lemma nodup_fvar (L : List Var) : (List.map Term.fvar L).Nodup ↔ L.Nodup := by grind

-- Definition 3.7
coinductive BT {Var : Type u} [DecidableEq Var] : Term Var → List Var → BöhmTree Var → Prop where
  | no_hnf (term : Term Var) (L : List Var) :
      ¬(exists n Ps y, hasAsHnf term n Ps y) →
      BT term L BöhmTree.no_hnf
  | hnf (term : Term Var) (abs_vars : List Var) (term_base_var : bfvar Var) (num_apps : ℕ) (term_apps : Vector (Term Var) num_apps) (subtrees : ULift (Fin num_apps) → BöhmTree Var) (L : List Var) :
      hasAsHnf term abs_vars.length term_apps.toList term_base_var →
      (abs_vars.map Term.fvar ++ term_apps.toList ++ L.map Term.fvar).Nodup →
      (forall (m : ULift (Fin num_apps)), BT (nfoldOpen (abs_vars ++ L) term_apps[m.down]) (abs_vars ++ L) (subtrees m)) →
      BT term L (BöhmTree.hnf num_apps abs_vars.length (BöhmTreeNode term_base_var L) subtrees)

@[partial_fixpoint_monotone]
theorem hnf_mono (t : bfvar Var) : monotone fun f ↦ BöhmTree.hnf 1 0 t fun _ ↦ f := by
  intro T T' Hle
  simp
  apply CoInd.le_leN
  rintro ⟨n⟩; simp [CoIndN.le]
  simp [CoIndN.le, PF.unpack]
  right
  constructor <;> try rfl
  grind [coherent, CoInd.leN_le, monotone]

-- BT of free variable together with correctness proof
def BT_fvar [DecidableEq Var] (n : Var) (L : List Var) : BöhmTree Var := .hnf 0 0 (BöhmTreeNode ⟨Term.fvar n, by simp⟩ L) (fun n ↦ .no_hnf)
lemma BT_fvar_correct [DecidableEq Var] (n : Var) (L : List Var) (hL : L.Nodup) : BT (Term.fvar n) L (BT_fvar n L) := by
  unfold BT_fvar
  apply BT.hnf _ [] ⟨Term.fvar n, by simp⟩ 0 #v[]
  · simp [hasAsHnf]
    constructor
    · apply IsHeadNormal.base
      apply IsHeadNormalApp.base_free
    · apply Relation.EqvGen.refl
  · simp [(nodup_fvar L).mpr hL]
  . simp only [Fin.getElem_fin, IsEmpty.forall_iff]

-- BT of bound variable together with correctness proof
def BT_bvar (n : ℕ) : BöhmTree Var := .hnf 0 0 ⟨Term.bvar n, by simp⟩ (fun n ↦ .no_hnf)
lemma BT_bvar_correct [DecidableEq Var] (n : ℕ) (L : List Var) (hL : L.Nodup) : BT (@Term.bvar Var n) L (BT_bvar n) := by
  unfold BT_bvar
  apply BT.hnf _ [] ⟨Term.bvar n, by simp⟩ 0 #v[]
  · simp [hasAsHnf]
    constructor
    · apply IsHeadNormal.base
      apply IsHeadNormalApp.base_bound
    · apply Relation.EqvGen.refl
  · simp [(nodup_fvar L).mpr hL]
  · simp only [Fin.getElem_fin, IsEmpty.forall_iff]

lemma BT_L_sub {Var} [DecidableEq Var] L₁ L₂ term tree (h_dis₁ : L₁.Nodup) (h_dis₂ : L₂.Nodup) : BT (Var:=Var) (nfoldOpen L₁ term) L₁ tree → BT (Var:=Var) (nfoldOpen L₂ term) L₂ tree := by
  intros h
  induction term
  case bvar n =>
    cases h
    case no_hnf h =>
      sorry
    case hnf =>
      sorry
  case fvar x => sorry
  case abs term ih => sorry
  case app term₁ term₂ ih₁ ih₂ => sorry

lemma exists_BT_for_term [DecidableEq Var] [fresh : HasFresh Var] (M : Term Var) (L : List Var) (hL : L.Nodup) : ∃ T, BT M L T := by
  induction M with
  | bvar n =>
    exact ⟨BT_bvar n, BT_bvar_correct n L hL⟩
  | fvar x => exact ⟨BT_fvar x L, BT_fvar_correct x L hL⟩
  | app P Q ihP ihQ =>
    obtain ⟨Ptree, BT_P⟩ := ihP
    obtain ⟨Qtree, BT_Q⟩ := ihQ
    by_cases (∃ n Ps y, hasAsHnf (P.app Q) n Ps y)
    case neg h =>
      exists BöhmTree.no_hnf
      apply BT.no_hnf _ _ h
    case pos h =>
      obtain ⟨n, Ps, y, hnf⟩ := h
      sorry
  | abs P ih =>
    obtain ⟨tree, ih⟩ := ih
    cases ih
    case no_hnf h =>
      exists BöhmTree.no_hnf
      apply BT.no_hnf
      sorry
    case hnf abs_vars term_base_var num_apps term_apps subtrees hnf hNodup hBT =>
      let new_abs_vars := (fresh.fresh (abs_vars ++ L).toFinset) :: abs_vars
      exists BöhmTree.hnf num_apps new_abs_vars.length (BöhmTreeNode term_base_var L) subtrees
      apply BT.hnf P.abs new_abs_vars term_base_var num_apps term_apps subtrees L
      · sorry
      · sorry
      · intro m
        specialize hBT m
        apply BT_L_sub _ _ _ _ _ _ hBT
        · sorry
        · sorry

def InfYtree : BöhmTree Var :=
  .hnf 1 0 ⟨Term.bvar 0, by simp⟩ (λ _ ↦ InfYtree)
partial_fixpoint
def Ytree : BöhmTree Var := .hnf 1 1 ⟨Term.bvar 0, by simp⟩ (λ _ ↦ InfYtree)

def omega_f := @Term.abs Var ((Term.bvar 1).app ((Term.bvar 0).app (Term.bvar 0)))
def Ycombinator := @Term.abs Var ((Term.bvar 0).app (omega_f.app omega_f))
def omega_f_free (f : Var) := @Term.abs Var ((Term.fvar f).app ((Term.bvar 0).app (Term.bvar 0)))

lemma omega_f_beta_f (f : Var) : (omega_f_free f).app (omega_f_free f) ≡β (Term.fvar f).app ((omega_f_free f).app (omega_f_free f)) := by
  constructor
  constructor
  constructor
  · apply Term.LC.abs {f}
    intro x elem
    apply Term.LC.app <;> simp [Term.openRec] <;> constructor <;> constructor
  · simp [omega_f_free]
    apply Term.LC.abs {f}
    intro x elem
    apply Term.LC.app <;> simp [Term.openRec] <;> constructor <;> constructor

lemma Ycombinator_tree [DecidableEq Var] [fresh : HasFresh Var] : BT (@Ycombinator Var) [] Ytree := by
  have f := fresh.fresh ∅
  apply BT.hnf Ycombinator [f] ⟨Term.bvar 0, by simp⟩ 1 #v[omega_f.app omega_f]
  · constructor
    · apply IsHeadNormal.step
      apply IsHeadNormal.base
      apply IsHeadNormalApp.step
      apply IsHeadNormalApp.base_bound
    · simp [nfoldAbs, nfoldApp]
      nth_rw 1 [Ycombinator]
  · simp [omega_f]
  · intros m
    simp [nfoldOpen, Term.open', Term.openRec, omega_f]
    rw [←omega_f_free]
    apply BT.coinduct (fun term L tree ↦ tree = InfYtree ∧ L = [f] ∧ term = (omega_f_free f).app (omega_f_free f))
    · rintro term L tree ⟨prop_tree, prop_L, prop_term⟩
      right
      use [], ⟨Term.fvar f, by simp⟩, 1, #v[(omega_f_free f).app (omega_f_free f)], (λ _ ↦ InfYtree)
      simp
      constructor
      · simp [hasAsHnf, nfoldAbs, nfoldApp]
        constructor
        · apply IsHeadNormal.base
          apply IsHeadNormalApp.step
          apply IsHeadNormalApp.base_free
        · rw [prop_term]
          exact omega_f_beta_f f
      · cases prop_L
        simp [prop_tree]
        constructor
        · simp [Term.open', Term.openRec, omega_f_free]
        · nth_rw 1 [InfYtree]
    · simp
