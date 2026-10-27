/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3: short-time control of a flight
-/

import HamiltonianMetricGraphs.FlightRetrace

/-!
# Short-time control of a flight

The tube coordinates of Lemma VI.1 are available on a *monotone* window: a position interval inside
the extension domain on which the energy is classically allowed and along which the flight moves in
one direction.  Producing such a window around a departure needs two elementary estimates on the
flight, both of which follow from the mean value inequality applied to the edge ODE:

* `FlightState.norm_flightCurve_sub_initial_le` — while the flight lasts, `‖φ_w(x) - x‖ ≤ C w`,
  where `C` bounds the edge vector field along the flight;
* `FlightState.momentum_pos_of_short_time` / `momentum_neg_of_short_time` — hence a flight that
  starts with momentum `p ≠ 0` keeps the sign of `p` for a time `|p| / C`, and its position moves by
  at most `C w`.

These are exactly the hypotheses `hmem`, `hmom` of `timeAt_flow_add` (Lemma VI.1), which says that
along such a stretch the time coordinate advances linearly — i.e. that the flight *is* the
energy--time chart of the tube.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set MeasureTheory PhysicalEdgeSegment

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

namespace FlightState

/-- **The mean value inequality along a flight.**  While a flight lasts, its state moves at a rate
bounded by the edge vector field along it. -/
theorem norm_flightCurve_sub_initial_le (a : V.FlightState) {C D : ℝ}
    (hD : ∀ _ : BddAbove (durationSet V a.edge a.state),
      D ≤ sSup (durationSet V a.edge a.state))
    (hbound : ∀ w ∈ Icc (0 : ℝ) D, ‖V.edgeVectorField a.edge (flightCurve V a w)‖ ≤ C)
    {w : ℝ} (hw : w ∈ Icc (0 : ℝ) D) :
    ‖flightCurve V a w - a.state‖ ≤ C * w := by
  have hderiv : ∀ x ∈ Icc (0 : ℝ) D, HasDerivWithinAt (flightCurve V a)
      (V.edgeVectorField a.edge (flightCurve V a x)) (Icc (0 : ℝ) D) x :=
    fun x hx => flightCurve_hasDerivWithinAt_Icc a hD hx
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) D := ⟨le_rfl, le_trans hw.1 hw.2⟩
  have h := (convex_Icc (0 : ℝ) D).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound h0 hw
  rw [flightCurve_zero] at h
  calc ‖flightCurve V a w - a.state‖ ≤ C * ‖w - (0 : ℝ)‖ := h
    _ = C * w := by rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hw.1]

/-- The edge vector field along a flight is bounded by the momentum bound and the force bound. -/
theorem norm_edgeVectorField_flightCurve_le (a : V.FlightState) {P F D : ℝ}
    (hD : ∀ _ : BddAbove (durationSet V a.edge a.state),
      D ≤ sSup (durationSet V a.edge a.state))
    (hP : ∀ w ∈ Icc (0 : ℝ) D, |(flightCurve V a w).2| ≤ P)
    (hF : ∀ q ∈ Icc (0 : ℝ) (Γ.length a.edge), |V.force a.edge q| ≤ F)
    {w : ℝ} (hw : w ∈ Icc (0 : ℝ) D) :
    ‖V.edgeVectorField a.edge (flightCurve V a w)‖ ≤ max P F := by
  have hphys : (flightCurve V a w).1 ∈ Icc (0 : ℝ) (Γ.length a.edge) :=
    flightCurve_physical V a hw.1 (fun hbdd => le_trans hw.2 (hD hbdd))
  have h1 : ‖(flightCurve V a w).2‖ ≤ max P F :=
    le_trans (by rw [Real.norm_eq_abs]; exact hP w hw) (le_max_left _ _)
  have h2 : ‖V.force a.edge (flightCurve V a w).1‖ ≤ max P F :=
    le_trans (by rw [Real.norm_eq_abs]; exact hF _ hphys) (le_max_right _ _)
  have hval : V.edgeVectorField a.edge (flightCurve V a w)
      = ((flightCurve V a w).2, V.force a.edge (flightCurve V a w).1) := rfl
  rw [hval, Prod.norm_def]
  exact max_le h1 h2

/-- **A flight keeps the sign of a positive initial momentum for a short time.** -/
theorem momentum_pos_of_short_time (a : V.FlightState) {P F D : ℝ}
    (hD : ∀ _ : BddAbove (durationSet V a.edge a.state),
      D ≤ sSup (durationSet V a.edge a.state))
    (hP : ∀ w ∈ Icc (0 : ℝ) D, |(flightCurve V a w).2| ≤ P)
    (hF : ∀ q ∈ Icc (0 : ℝ) (Γ.length a.edge), |V.force a.edge q| ≤ F)
    {w : ℝ} (hw : w ∈ Icc (0 : ℝ) D) (hlt : max P F * w < a.state.2) :
    0 < (flightCurve V a w).2 := by
  have h := norm_flightCurve_sub_initial_le V a hD
    (fun u hu => norm_edgeVectorField_flightCurve_le V a hD hP hF hu) hw
  have h2 : |(flightCurve V a w).2 - a.state.2| ≤ max P F * w := by
    refine le_trans ?_ h
    rw [Prod.norm_def]
    exact le_trans (le_of_eq (Real.norm_eq_abs _).symm) (le_max_right _ _)
  have := (abs_le.mp h2).1
  linarith

/-- **A flight keeps the sign of a negative initial momentum for a short time.** -/
theorem momentum_neg_of_short_time (a : V.FlightState) {P F D : ℝ}
    (hD : ∀ _ : BddAbove (durationSet V a.edge a.state),
      D ≤ sSup (durationSet V a.edge a.state))
    (hP : ∀ w ∈ Icc (0 : ℝ) D, |(flightCurve V a w).2| ≤ P)
    (hF : ∀ q ∈ Icc (0 : ℝ) (Γ.length a.edge), |V.force a.edge q| ≤ F)
    {w : ℝ} (hw : w ∈ Icc (0 : ℝ) D) (hlt : max P F * w < -a.state.2) :
    (flightCurve V a w).2 < 0 := by
  have h := norm_flightCurve_sub_initial_le V a hD
    (fun u hu => norm_edgeVectorField_flightCurve_le V a hD hP hF hu) hw
  have h2 : |(flightCurve V a w).2 - a.state.2| ≤ max P F * w := by
    refine le_trans ?_ h
    rw [Prod.norm_def]
    exact le_trans (le_of_eq (Real.norm_eq_abs _).symm) (le_max_right _ _)
  have := (abs_le.mp h2).2
  linarith

/-- **A flight's position moves at a bounded rate.** -/
theorem abs_flightCurve_position_sub_le (a : V.FlightState) {P F D : ℝ}
    (hD : ∀ _ : BddAbove (durationSet V a.edge a.state),
      D ≤ sSup (durationSet V a.edge a.state))
    (hP : ∀ w ∈ Icc (0 : ℝ) D, |(flightCurve V a w).2| ≤ P)
    (hF : ∀ q ∈ Icc (0 : ℝ) (Γ.length a.edge), |V.force a.edge q| ≤ F)
    {w : ℝ} (hw : w ∈ Icc (0 : ℝ) D) :
    |(flightCurve V a w).1 - a.state.1| ≤ max P F * w := by
  have h := norm_flightCurve_sub_initial_le V a hD
    (fun u hu => norm_edgeVectorField_flightCurve_le V a hD hP hF hu) hw
  refine le_trans ?_ h
  rw [Prod.norm_def]
  exact le_trans (le_of_eq (Real.norm_eq_abs _).symm) (le_max_left _ _)

end FlightState

end MechanicalPotential

end HamiltonianMetricGraphs
