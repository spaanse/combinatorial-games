/-
Copyright (c) 2025 Jelmer Firet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jelmer Firet
-/

import CombinatorialGames.Game.IGame
import CombinatorialGames.Surreal.Cut
import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic.Ring.Basic

universe u

namespace Temperature
open Set IGame Surreal Cut

def leftStop := leftGame
def rightStop := rightGame

noncomputable def heat (x t : IGame) : IGame :=
  !{range fun y : xᴿ ↦ (heat y t) + t | range fun y : xᴸ ↦ (heat y t) - t}
termination_by x
decreasing_by igame_wf

def Wall := Surreal → Cut

def hasMastSlope (s : Surreal) (w : Wall) : Prop := ∃ T, ∀ t ≥ T, w t = s * (t - T) +ᵥ w T
def hasMast (w : Wall) : Prop := hasMastSlope 0 w
def hasPosMast (w : Wall) : Prop := hasMastSlope 1 w
def hasNegMast (w : Wall) : Prop := hasMastSlope (-1) w

-- I chose the terminolagy pile as it is a pole going into the ground, thus the opposite of a mast
def hasPileSlope (s : Surreal) (w : Wall) : Prop := ∃ T, ∀ t ≤ T, w t = s * (t - T) +ᵥ w T
def hasPile (w : Wall) : Prop := hasPileSlope 0 w
def hasPosPile (w : Wall) : Prop := hasPileSlope 1 w
def hasNegPile (w : Wall) : Prop := hasPileSlope (-1) w

def slantPos (w : Wall) : Wall :=
  fun t => t +ᵥ w t
def slantNeg (w : Wall) : Wall :=
  fun t => (-t) +ᵥ w t

theorem slantPos_hasMastSlope {s : Surreal} {w : Wall}
: hasMastSlope s w → hasMastSlope (s+1) (slantPos w) := by
  unfold hasMastSlope slantPos
  refine fun ⟨T, H⟩ ↦ ⟨T, fun t T_le_t ↦ ?_⟩
  rw [H t T_le_t]
  simp_all only [←add_vadd]
  congr 1 ; ring1

theorem slantNeg_hasMastSlope {s : Surreal} {w : Wall}
: hasMastSlope s w → hasMastSlope (s-1) (slantNeg w) := by
  unfold hasMastSlope slantNeg
  refine fun ⟨T, H⟩ ↦ ⟨T, fun t T_le_t ↦ ?_⟩
  rw [H t T_le_t]
  simp_all only [←add_vadd]
  congr 1 ; ring1

theorem slantPos_hasPileSlope {s : Surreal} {w : Wall}
: hasPileSlope s w → hasPileSlope (s+1) (slantPos w) := by
  unfold hasPileSlope slantPos
  refine fun ⟨T, H⟩ ↦ ⟨T, fun t T_le_t ↦ ?_⟩
  rw [H t T_le_t]
  simp_all only [←add_vadd]
  congr 1 ; ring1

theorem slantNeg_hasPileSlope {s : Surreal} {w : Wall}
: hasPileSlope s w → hasPileSlope (s-1) (slantNeg w) := by
  unfold hasPileSlope slantNeg
  refine fun ⟨T, H⟩ ↦ ⟨T, fun t T_le_t ↦ ?_⟩
  rw [H t T_le_t]
  simp_all only [←add_vadd]
  congr 1 ; ring1

theorem slantPos_hasPosMast_of_hasMast (w : Wall) (w_mast : hasMast w) : hasPosMast (slantPos w) :=
  (congrArg (hasMastSlope · (slantPos w)) (zero_add 1)).mp (slantPos_hasMastSlope w_mast)
theorem slantPos_hasMast_of_hasNegMast (w : Wall) (w_mast : hasNegMast w) : hasMast (slantPos w) :=
  (congrArg (hasMastSlope · (slantPos w)) (neg_add_cancel 1)).mp (slantPos_hasMastSlope w_mast)
theorem slantNeg_hasMast_of_hasPosMast (w : Wall) (w_mast : hasPosMast w) : hasMast (slantNeg w) :=
  (congrArg (hasMastSlope · (slantNeg w)) (sub_self 1)).mp (slantNeg_hasMastSlope w_mast)
theorem slantNeg_hasNegMast_of_hasMast (w : Wall) (w_mast : hasMast w) : hasNegMast (slantNeg w) :=
  (congrArg (hasMastSlope · (slantNeg w)) (zero_sub 1)).mp (slantNeg_hasMastSlope w_mast)
theorem slantPos_hasPosPile_of_hasPile (w : Wall) (w_pile : hasPile w) : hasPosPile (slantPos w) :=
  (congrArg (hasPileSlope · (slantPos w)) (zero_add 1)).mp (slantPos_hasPileSlope w_pile)
theorem slantPos_hasPile_of_hasNegPile (w : Wall) (w_pile : hasNegPile w) : hasPile (slantPos w) :=
  (congrArg (hasPileSlope · (slantPos w)) (neg_add_cancel 1)).mp (slantPos_hasPileSlope w_pile)
theorem slantNeg_hasPile_of_hasPosPile (w : Wall) (w_pile : hasPosPile w) : hasPile (slantNeg w) :=
  (congrArg (hasPileSlope · (slantNeg w)) (sub_self 1)).mp (slantNeg_hasPileSlope w_pile)
theorem slantNeg_hasNegPile_of_hasPile (w : Wall) (w_pile : hasPile w) : hasNegPile (slantNeg w) :=
  (congrArg (hasPileSlope · (slantNeg w)) (zero_sub 1)).mp (slantNeg_hasPileSlope w_pile)

instance : SupSet Wall where
  sSup := fun S x ↦ ⨆ w ∈ S, w x
instance : InfSet Wall where
  sInf := fun S x ↦ ⨅ w ∈ S, w x

theorem exists_max_of_forall_exists (S : Set Wall) (S_fin : S.Finite) (P : Wall → Surreal → Surreal → Prop)
: (∀ w ∈ S, ∃ T, ∀ t ≥ T, P w t T) → (∃ T, ∀ t ≥ T, ∀ w ∈ S, P w t T) := by sorry


theorem sup_hasMastSlope (S : Set Wall) (S_fin : S.Finite) (s : Surreal) (S_mast : ∀ w ∈ S, hasMastSlope s w) : hasMastSlope s (⨆ w ∈ S, w) := by
  unfold hasMastSlope at *
  obtain ⟨T, H⟩ := (exists_max_of_forall_exists S S_fin _ S_mast)
  exists T
  intro t T_le_t
  specialize (H t T_le_t)
  unfold iSup instSupSetWall sSup
  simp








end Temperature
