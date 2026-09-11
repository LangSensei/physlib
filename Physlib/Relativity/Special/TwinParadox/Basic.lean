/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Special.ProperTime
/-!
# Twin Paradox

This module compares elapsed proper times along piecewise straight, future-causal journeys
in Minkowski spacetime. Both journeys start at `startPoint` and end at `endPoint`.
Twin A takes the single straight segment between them. Twin B takes two straight segments
through `twinBMid`.

For massive twins, these segments describe inertial motion, with B's velocity allowed to
change instantaneously at the intermediate event. No condition that A is at rest in the
chosen coordinates is imposed. The formal causal hypotheses also allow null segments and
coincident events as boundary cases.

We prove that A accumulates at least as much proper time as B. The signed difference
`ageGap` is therefore nonnegative; it is not defined using an absolute value. For twins of
equal initial age, this is their final age difference. The model does not require a genuine
detour, so the conclusion is non-strict. The example below chooses coordinates in which A
remains at the spatial origin.

The origin of the twin paradox dates back to Paul Langevin in 1911.

-/

@[expose] public section

noncomputable section

namespace SpecialRelativity

open Matrix
open Real
open Lorentz
open Vector

/-- Two future-causal journeys with common endpoints, represented by one straight segment
for twin A and two straight segments for twin B. -/
structure InstantaneousTwinParadox where
  /-- The starting point of both twins. -/
  startPoint : SpaceTime 3
  /-- The end point of both twins. -/
  endPoint : SpaceTime 3
  /-- The point twin B travels to between the start point and the end point. -/
  twinBMid : SpaceTime 3
  endPoint_causallyFollows_startPoint : causallyFollows startPoint endPoint
  twinBMid_causallyFollows_startPoint : causallyFollows startPoint twinBMid
  endPoint_causallyFollows_twinBMid : causallyFollows twinBMid endPoint

namespace InstantaneousTwinParadox
variable (T: InstantaneousTwinParadox)
open SpaceTime

/-- The proper time along twin A's straight segment from `T.startPoint` to `T.endPoint`. -/
def properTimeTwinA : ℝ := SpaceTime.properTime T.startPoint T.endPoint

/-- The sum of the proper times along twin B's straight segments from `T.startPoint`
to `T.twinBMid` and from `T.twinBMid` to `T.endPoint`. -/
def properTimeTwinB : ℝ := SpaceTime.properTime T.startPoint T.twinBMid +
  SpaceTime.properTime T.twinBMid T.endPoint

/-- The signed difference of elapsed proper times: twin A's minus twin B's.
For equal initial ages, this is the difference of final ages. -/
def ageGap : ℝ := T.properTimeTwinA - T.properTimeTwinB

TODO "Find the conditions for which the age gap for the twin paradox is zero."

/-- In the straight-segment twin model, A accumulates at least as much proper time as B.
No rest-frame or strict-detour assumption is required. Null segments and coincident events
are included. -/
lemma ageGap_nonneg : 0 ≤ T.ageGap := by
  exact sub_nonneg.mpr (SpaceTime.properTime_add_le
    T.twinBMid_causallyFollows_startPoint T.endPoint_causallyFollows_twinBMid)

/-!

## Example 1

-/

set_option backward.isDefEq.respectTransparency false in
/-- An example in a frame where twin A remains at the spatial origin:
- Twin A goes from event `0` to `[15, 0, 0, 0]` without changing spatial position.
- Twin B follows two straight segments via `[7.5, 6, 0, 0]` to `[15, 0, 0, 0]`.
The two legs of B's journey have equal speed and opposite spatial velocities. -/
def example1 : InstantaneousTwinParadox where
  startPoint := 0
  endPoint := (fun
    | Sum.inl 0 => 15
    | Sum.inr i => 0)
  twinBMid := (fun
    | Sum.inl 0 => 7.5
    | Sum.inr 0 => 6
    | Sum.inr i => 0)
  endPoint_causallyFollows_startPoint := by
    simp [causallyFollows]
    left
    simp only [interiorFutureLightCone, sub_zero, Fin.isValue, Set.mem_ofPred_eq, Nat.ofNat_pos,
      and_true]
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [minkowskiProduct_toCoord]
    simp
  twinBMid_causallyFollows_startPoint := by
    simp only [causallyFollows]
    left
    simp only [interiorFutureLightCone, sub_zero, Fin.isValue, Set.mem_ofPred_eq]
    norm_num
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [minkowskiProduct_toCoord]
    simp [Fin.sum_univ_three]
    norm_num
  endPoint_causallyFollows_twinBMid := by
    simp [causallyFollows]
    left
    simp [interiorFutureLightCone]
    norm_num
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [minkowskiProduct_toCoord]
    simp [Fin.sum_univ_three]
    norm_num

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma example1_properTimeTwinA : example1.properTimeTwinA = 15 := by
  simp [properTimeTwinA, example1, properTime, minkowskiProduct_toCoord]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma example1_properTimeTwinB : example1.properTimeTwinB = 9 := by
  simp [properTimeTwinB, properTime, example1, minkowskiProduct_toCoord, Fin.sum_univ_three]
  norm_num [show √81 = 9 from sqrt_eq_cases.mpr (by norm_num),
    show √4 = 2 from sqrt_eq_cases.mpr (by norm_num)]

lemma example1_ageGap : example1.ageGap = 6 := by
  norm_num [ageGap]

end InstantaneousTwinParadox

TODO "Do the twin paradox with a non-instantaneous acceleration. This should be done
  in a different module."

end SpecialRelativity

end
