import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

import Project.ModelInterp
import Project.AndrejBauer.GraphModel
import Project.BetaEquiv
import Project.Bohm_Tree

open Listing
open Cslib
open LambdaCalculus.LocallyNameless.Untyped
open Term

universe u
variable {Var : Type u} [DecidableEq Var]
variable {α : Type} [Listing α]
variable {ρ : ℕ → Set α}
variable {σ : Var → Set α}

def solvable (T : Term Var) : Prop := True -- Has to be defined

theorem Interp_iff_context_solvable (A B : Term Var):
〚 A 〛_{ρ,σ} = 〚 B 〛_{ρ,σ} ↔ ∀ C : Term Var -> Term Var, (solvable (C A) ↔  solvable (C B))
  := by
  sorry

theorem solvable_iff_hasHnf (A: Term Var):
solvable A ↔ hasHnf A
  := by
  sorry

theorem context_solvable_iff_BT (A B : Term Var):
( ∀ C : Term Var -> Term Var, (solvable (C A) ↔  solvable (C B))) ↔ BT A = BT B
  := by
  sorry

theorem BT_eq_Interp (A B : Term Var):
〚 A 〛_{ρ,σ} = 〚 B 〛_{ρ,σ} ↔ BT A = BT B
  := by
  rw [Interp_iff_context_solvable A B]
  rw [<-context_solvable_iff_BT A B]
