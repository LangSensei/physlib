/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.LightLike
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.TimeLike
/-!
# Proper Time

This file introduces 4d Minkowski spacetime.

-/

@[expose] public section

noncomputable section

namespace SpaceTime

open Manifold
open Matrix
open Real
open ComplexConjugate
open Lorentz
open Vector

/-- The proper time from `q` to `p`. Defaults to zero if `p` and `q`
  have a space-like separation. -/
def properTime {d : ℕ} (q p : SpaceTime d) : ℝ :=
  √⟪p - q, p - q⟫ₘ

lemma properTime_pos_ofTimeLike {d : ℕ} (q p : SpaceTime d)
    (h : causalCharacter (p - q) = .timeLike) :
    0 < properTime q p := by
  rw [properTime]
  refine sqrt_pos_of_pos ?_
  exact (timeLike_iff_norm_sq_pos (p - q)).mp h

lemma properTime_zero_ofLightLike {d : ℕ} (q p : SpaceTime d)
    (h : causalCharacter (p - q) = .lightLike) :
    properTime q p = 0 := by
  rw [properTime]
  rw [lightLike_iff_norm_sq_zero] at h
  simp only [h, sqrt_zero]

lemma properTime_zero_ofSpaceLike {d : ℕ} (q p : SpaceTime d)
    (h : causalCharacter (p - q) = .spaceLike) :
    properTime q p = 0 := by
  rw [properTime]
  rw [spaceLike_iff_norm_sq_neg] at h
  exact sqrt_eq_zero'.mpr (le_of_lt h)

/-- A future-causal separation has nonnegative Minkowski norm squared and time component. -/
private lemma causallyFollows_bounds {d : ℕ} {p q : SpaceTime d}
    (h : causallyFollows p q) :
    0 ≤ ⟪q - p, q - p⟫ₘ ∧ 0 ≤ (q - p) (Sum.inl 0) := by
  rcases h with h | h
  · exact ⟨((timeLike_iff_norm_sq_pos _).mp h.1).le, h.2.le⟩
  · exact ⟨((lightLike_iff_norm_sq_zero _).mp h.1).ge, h.2⟩

/-- The proper time of the straight segment from `p` to `r` is at least the sum for the
straight segments from `p` to `q` and from `q` to `r`, when both legs are future-causal.
No condition that the direct segment is at rest in the chosen coordinates is imposed. -/
lemma properTime_add_le {d : ℕ} {p q r : SpaceTime d}
    (hpq : causallyFollows p q) (hqr : causallyFollows q r) :
    properTime p q + properTime q r ≤ properTime p r := by
  obtain ⟨hp, hp₀⟩ := causallyFollows_bounds hpq
  obtain ⟨hq, hq₀⟩ := causallyFollows_bounds hqr
  have hcs := sqrt_mul_sqrt_le_minkowskiProduct (q - p) (r - q) hp hq hp₀ hq₀
  have hsum : ⟪r - p, r - p⟫ₘ =
      ⟪q - p, q - p⟫ₘ + ⟪r - q, r - q⟫ₘ + 2 * ⟪q - p, r - q⟫ₘ := by
    have hrp : r - p = (q - p) + (r - q) := by abel
    rw [hrp]
    simp only [minkowskiProduct_apply, minkowskiProductMap_add_fst,
      minkowskiProductMap_add_snd]
    rw [minkowskiProductMap_symm (r - q) (q - p)]
    ring
  unfold properTime
  apply Real.le_sqrt_of_sq_le
  rw [hsum]
  nlinarith [Real.sq_sqrt hp, Real.sq_sqrt hq]

end SpaceTime

end
