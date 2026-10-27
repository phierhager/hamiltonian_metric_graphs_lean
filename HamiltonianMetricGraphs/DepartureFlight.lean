/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.2: continuity and Borel measurability of the departure flight map
-/

import HamiltonianMetricGraphs.OutgoingFlight

/-!
# The departure flight map: continuity and Borel measurability

`EdgeFlightMap.lean` treats the flight issued from an *interior* state of an edge.  After an impact
the flight is issued from a *vertex*, and the natural parameter is then the inward speed `r` at the
germ rather than a two-dimensional initial condition: the departure states of a fixed germ form the
one-parameter family `departurePoint η r = (coordinate η, -sign η · r)`.

This module carries the regularity results of `EdgeFlightMap.lean` over to that family.

* `regularSpeeds`, `isOpen_regularSpeeds`: the inward speeds at a regular energy form an open set
  of speeds.
* `departureNoImpactSet`, `isOpen_departureNoImpactSet`: surviving past `Δ` is an open condition on
  the speed (`OutgoingFlight.departureNoImpact_persists`), so the departure impact time is lower
  semicontinuous and hence Borel (`measurable_departureImpactTime`).
* `departureFlight`, `departurePreImpact`, `continuousOn_departureFlight`: the departure flight map
  is jointly continuous in the speed and the time strictly before the impact — Grönwall in the
  speed (the two initial points *coincide*, so their distance is exactly `|r' - r|`), the edge ODE
  in the time.
* `departureFlightAt`, `measurable_departureFlightAt`: the total time-`w` departure map is Borel.
* `departureLanding`, `measurable_departureLanding`: the departure landing map is Borel, again as
  the pointwise limit of the flights stopped at the largest dyadic time below the impact time.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter Metric MeasureTheory PhysicalEdgeSegment
open scoped Topology NNReal ENNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### Regular departure speeds -/

/-- The inward speeds at the germ `η` whose departure energy is regular. -/
def regularSpeeds (η : Γ.EdgeEnd) : Set ℝ :=
  {r | 0 < r ∧ V.departureEnergy η r ∉ V.exceptionalEnergies}

theorem isOpen_regularSpeeds (η : Γ.EdgeEnd) : IsOpen (V.regularSpeeds η) := by
  have hexc : IsOpen ((↑V.exceptionalEnergies : Set ℝ)ᶜ) :=
    V.exceptionalEnergies.finite_toSet.isClosed.isOpen_compl
  have h2 : IsOpen (V.departureEnergy η ⁻¹' ((↑V.exceptionalEnergies : Set ℝ)ᶜ)) :=
    hexc.preimage (V.continuous_departureEnergy η)
  have heq : V.regularSpeeds η =
      Ioi (0 : ℝ) ∩ V.departureEnergy η ⁻¹' ((↑V.exceptionalEnergies : Set ℝ)ᶜ) := by
    ext r
    simp [regularSpeeds, mem_Ioi]
  rw [heq]
  exact isOpen_Ioi.inter h2

theorem durationSet_nonempty_of_regularSpeed {η : Γ.EdgeEnd} {r : ℝ}
    (hr : r ∈ V.regularSpeeds η) :
    (durationSet V η.1 (departurePoint η r)).Nonempty :=
  PhysicalEdgeSegment.durationSet_nonempty (V.ofDeparture η hr.1 hr.2).segment

/-! ### The departure no-impact set -/

/-- The speeds at the germ `η` whose departure flight survives past the time `Δ`. -/
def departureNoImpactSet (η : Γ.EdgeEnd) (Δ : ℝ) : Set ℝ :=
  {r ∈ V.regularSpeeds η | ∀ _ : BddAbove (durationSet V η.1 (departurePoint η r)),
    Δ < sSup (durationSet V η.1 (departurePoint η r))}

section Departure

variable [Nonempty Γ.Edge]

theorem isOpen_departureNoImpactSet (η : Γ.EdgeEnd) {Δ : ℝ} (hΔ : 0 < Δ) :
    IsOpen (V.departureNoImpactSet η Δ) := by
  rw [isOpen_iff_mem_nhds]
  rintro r ⟨hrreg, hsurv⟩
  obtain ⟨ρ, hρ, hρspec⟩ := V.departureNoImpact_persists η hΔ hrreg.1 hrreg.2 hsurv
  refine Filter.mem_of_superset
    (Filter.inter_mem ((V.isOpen_regularSpeeds η).mem_nhds hrreg) (Metric.ball_mem_nhds r hρ)) ?_
  rintro r' ⟨hr'reg, hr'ball⟩
  refine ⟨hr'reg, hρspec r' hr'reg.1 ?_⟩
  rw [Metric.mem_ball, Real.dist_eq] at hr'ball
  exact hr'ball

theorem measurableSet_departureNoImpactSet (η : Γ.EdgeEnd) {Δ : ℝ} (hΔ : 0 < Δ) :
    MeasurableSet (V.departureNoImpactSet η Δ) :=
  (V.isOpen_departureNoImpactSet η hΔ).measurableSet

/-- **The departure impact time is lower semicontinuous, hence Borel.** -/
theorem isOpen_lt_departureImpactTime (η : Γ.EdgeEnd) (y : ℝ≥0∞) :
    IsOpen {s : V.regularSpeeds η |
      y < V.impactTime η.1 (departurePoint η (s : ℝ))} := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  obtain ⟨Δ, hΔ0, hyΔ, hΔf⟩ := ENNReal.lt_iff_exists_real_btwn.mp hs
  have hΔpos : 0 < Δ := by
    rcases hΔ0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hyΔ; simp at hyΔ
  have hsmem : (s : ℝ) ∈ V.departureNoImpactSet η Δ :=
    ⟨s.2, (V.ofReal_lt_impactTime_iff (V.durationSet_nonempty_of_regularSpeed s.2) hΔpos).mp hΔf⟩
  refine Filter.mem_of_superset
    (((V.isOpen_departureNoImpactSet η hΔpos).preimage continuous_subtype_val).mem_nhds
      hsmem) ?_
  intro s' hs'
  exact lt_trans hyΔ
    ((V.ofReal_lt_impactTime_iff (V.durationSet_nonempty_of_regularSpeed s'.2) hΔpos).mpr hs'.2)

theorem measurable_departureImpactTime (η : Γ.EdgeEnd) :
    Measurable fun s : V.regularSpeeds η =>
      V.impactTime η.1 (departurePoint η (s : ℝ)) :=
  measurable_of_Ioi fun y => (V.isOpen_lt_departureImpactTime η y).measurableSet

end Departure

/-! ### The departure flight map -/

/-- The **departure flight map**: the state reached at time `w` by the flight leaving the germ `η`
with inward speed `r` (and the departure point itself off the regular speeds, a junk value). -/
noncomputable def departureFlight (η : Γ.EdgeEnd) (r w : ℝ) : ℝ × ℝ := by
  classical
  exact if h : r ∈ V.regularSpeeds η then
    FlightState.flightCurve V (V.ofDeparture η h.1 h.2) w
  else departurePoint η r

theorem departureFlight_of_mem {η : Γ.EdgeEnd} {r : ℝ} (h : r ∈ V.regularSpeeds η) (w : ℝ) :
    V.departureFlight η r w = FlightState.flightCurve V (V.ofDeparture η h.1 h.2) w := by
  classical
  unfold departureFlight
  rw [dif_pos h]

theorem departureFlight_of_notMem {η : Γ.EdgeEnd} {r : ℝ} (h : r ∉ V.regularSpeeds η) (w : ℝ) :
    V.departureFlight η r w = departurePoint η r := by
  classical
  unfold departureFlight
  rw [dif_neg h]

@[simp] theorem departureFlight_zero (η : Γ.EdgeEnd) (r : ℝ) :
    V.departureFlight η r 0 = departurePoint η r := by
  by_cases h : r ∈ V.regularSpeeds η
  · rw [V.departureFlight_of_mem h, FlightState.flightCurve_zero, V.ofDeparture_state]
  · rw [V.departureFlight_of_notMem h]

/-- The region on which the departure flight map is the genuine pre-impact flow. -/
def departurePreImpact (η : Γ.EdgeEnd) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ V.regularSpeeds η ∧ 0 ≤ z.2 ∧
    ENNReal.ofReal z.2 < V.impactTime η.1 (departurePoint η z.1)}

section Continuity

variable [Nonempty Γ.Edge]

/-- **The departure flight map is continuous before the impact.**  In the speed this is the
Grönwall comparison of two flights leaving the *same* germ — their initial points coincide, so
their distance is exactly the difference of the speeds — and in the time it is the edge ODE. -/
theorem continuousOn_departureFlight (η : Γ.EdgeEnd) :
    ContinuousOn (fun z : ℝ × ℝ => V.departureFlight η z.1 z.2) (V.departurePreImpact η) := by
  classical
  rintro ⟨r, w₀⟩ hmem
  have hrreg : r ∈ V.regularSpeeds η := hmem.1
  have hw₀ : (0 : ℝ) ≤ w₀ := hmem.2.1
  have hlt : ENNReal.ofReal w₀ < V.impactTime η.1 (departurePoint η r) := hmem.2.2
  -- a survival time `Δ > w₀`
  obtain ⟨Δ, hΔ0, hwΔ, hΔf⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have hw₀Δ : w₀ < Δ := by
    rcases lt_or_ge w₀ Δ with h | h
    · exact h
    · exact absurd (ENNReal.ofReal_le_ofReal h) (not_le.mpr hwΔ)
  have hΔpos : 0 < Δ := lt_of_le_of_lt hw₀ hw₀Δ
  have hrne := V.durationSet_nonempty_of_regularSpeed hrreg
  have hrsurv : ∀ _ : BddAbove (durationSet V η.1 (departurePoint η r)),
      Δ < sSup (durationSet V η.1 (departurePoint η r)) :=
    (V.ofReal_lt_impactTime_iff hrne hΔpos).mp hΔf
  -- the compact regular energy window around the reference energy
  obtain ⟨d, hd, hdreg⟩ := V.exists_regular_window hrreg.2
  obtain ⟨P, hP, hPbound⟩ := V.exists_compact_energy_speed_bound
    (Icc (V.departureEnergy η r - d) (V.departureEnergy η r + d)) isCompact_Icc
  obtain ⟨L, hL⟩ := V.exists_lipschitzOnWith_edgeVectorField_closedMomentumBox η.1 P
  have haE : (V.ofDeparture η hrreg.1 hrreg.2).energy ∈
      Icc (V.departureEnergy η r - d) (V.departureEnergy η r + d) := by
    rw [V.ofDeparture_energy, mem_Icc]
    constructor <;> linarith
  have hdura : ∀ s ∈ Icc (0 : ℝ) Δ,
      ∀ _ : BddAbove (durationSet V (V.ofDeparture η hrreg.1 hrreg.2).edge
        (V.ofDeparture η hrreg.1 hrreg.2).state),
      s ≤ sSup (durationSet V (V.ofDeparture η hrreg.1 hrreg.2).edge
        (V.ofDeparture η hrreg.1 hrreg.2).state) :=
    fun s hs hbdd => le_trans hs.2 (hrsurv hbdd).le
  have hboxa : ∀ s ∈ Icc (0 : ℝ) Δ,
      FlightState.flightCurve V (V.ofDeparture η hrreg.1 hrreg.2) s ∈
        closedEdgeMomentumBox η.1 P := fun s hs =>
    FlightState.flightCurve_mem_closedEdgeMomentumBox V _ hPbound haE hs.1 (hdura s hs)
  -- nearby speeds: survival, regularity and the energy window
  obtain ⟨ρ₀, hρ₀, hρ₀spec⟩ :=
    V.departureNoImpact_persists η hΔpos hrreg.1 hrreg.2 hrsurv
  obtain ⟨ρ₁, hρ₁, hρ₁spec⟩ :=
    Metric.continuousAt_iff.mp ((V.continuous_departureEnergy η).continuousAt (x := r)) d hd
  set ρ : ℝ := min ρ₀ ρ₁ with hρdef
  have hρpos : 0 < ρ := lt_min hρ₀ hρ₁
  have hKmem : ∀ r' : ℝ, |r' - r| < ρ →
      V.departureEnergy η r' ∈ Icc (V.departureEnergy η r - d) (V.departureEnergy η r + d) := by
    intro r' hlt'
    have h := hρ₁spec (by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le hlt' (min_le_right _ _))
    rw [Real.dist_eq, abs_lt] at h
    rw [mem_Icc]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hreg' : ∀ r' : ℝ, 0 < r' → |r' - r| < ρ → r' ∈ V.regularSpeeds η :=
    fun r' hr' hlt' => ⟨hr', hdreg _ (hKmem r' hlt')⟩
  -- the Grönwall estimate
  have hkey : ∀ r' : ℝ, 0 < r' → |r' - r| < ρ → ∀ s ∈ Icc (0 : ℝ) Δ,
      dist (V.departureFlight η r' s) (V.departureFlight η r s) ≤
        |r' - r| * Real.exp (L * Δ) := by
    intro r' hr' hlt' s hs
    have hr'reg : r' ∈ V.regularSpeeds η := hreg' r' hr' hlt'
    have hbsurv : ∀ _ : BddAbove (durationSet V η.1 (departurePoint η r')),
        Δ < sSup (durationSet V η.1 (departurePoint η r')) :=
      hρ₀spec r' hr' (lt_of_lt_of_le hlt' (min_le_left _ _))
    have hdurb : ∀ s ∈ Icc (0 : ℝ) Δ,
        ∀ _ : BddAbove (durationSet V (V.ofDeparture η hr'reg.1 hr'reg.2).edge
          (V.ofDeparture η hr'reg.1 hr'reg.2).state),
        s ≤ sSup (durationSet V (V.ofDeparture η hr'reg.1 hr'reg.2).edge
          (V.ofDeparture η hr'reg.1 hr'reg.2).state) :=
      fun s hs hbdd => le_trans hs.2 (hbsurv hbdd).le
    have hbE : (V.ofDeparture η hr'reg.1 hr'reg.2).energy ∈
        Icc (V.departureEnergy η r - d) (V.departureEnergy η r + d) := by
      rw [V.ofDeparture_energy]
      exact hKmem r' hlt'
    have hboxb : ∀ s ∈ Icc (0 : ℝ) Δ,
        FlightState.flightCurve V (V.ofDeparture η hr'reg.1 hr'reg.2) s ∈
          closedEdgeMomentumBox η.1 P := fun s hs =>
      FlightState.flightCurve_mem_closedEdgeMomentumBox V _ hPbound hbE hs.1 (hdurb s hs)
    have hgron := FlightState.dist_flightCurve_le V (V.ofDeparture η hrreg.1 hrreg.2)
      (V.ofDeparture η hr'reg.1 hr'reg.2) rfl hL
      (hdura Δ ⟨hΔpos.le, le_rfl⟩) (hdurb Δ ⟨hΔpos.le, le_rfl⟩) hboxa hboxb s hs
    rw [V.departureFlight_of_mem hr'reg, V.departureFlight_of_mem hrreg]
    refine le_trans hgron ?_
    rw [V.ofDeparture_state, V.ofDeparture_state, dist_departurePoint]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by
        have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
        nlinarith [hs.1, hs.2])) (abs_nonneg _)
  -- continuity in the time variable
  have hflight : (fun s : ℝ => V.departureFlight η r s)
      = FlightState.flightCurve V (V.ofDeparture η hrreg.1 hrreg.2) :=
    funext fun s => V.departureFlight_of_mem hrreg s
  have htime : ContinuousWithinAt (fun s : ℝ => V.departureFlight η r s)
      (Icc (0 : ℝ) Δ) w₀ := by
    rw [hflight]
    exact (FlightState.flightCurve_hasDerivWithinAt_Icc _ (hdura Δ ⟨hΔpos.le, le_rfl⟩)
      ⟨hw₀, hw₀Δ.le⟩).continuousWithinAt
  -- combine
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hexp : (0 : ℝ) < Real.exp (L * Δ) := Real.exp_pos _
  obtain ⟨δ₁, hδ₁, hδ₁spec⟩ := Metric.continuousWithinAt_iff.mp htime (ε / 2) (by linarith)
  refine ⟨min (min ρ (ε / (2 * Real.exp (L * Δ)))) (min δ₁ (Δ - w₀)),
    lt_min (lt_min hρpos (by positivity)) (lt_min hδ₁ (by linarith)), ?_⟩
  rintro ⟨r', s⟩ hzmem hdlt
  have hs0 : (0 : ℝ) ≤ s := hzmem.2.1
  have hr'pos : 0 < r' := hzmem.1.1
  have hd1 : |r' - r| ≤ dist ((r', s) : ℝ × ℝ) (r, w₀) := by
    rw [Prod.dist_eq, ← Real.dist_eq]
    exact le_max_left _ _
  have hd2 : dist s w₀ ≤ dist ((r', s) : ℝ × ℝ) (r, w₀) := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hdr : |r' - r| < ρ :=
    lt_of_le_of_lt hd1 (lt_of_lt_of_le hdlt (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hdr2 : |r' - r| < ε / (2 * Real.exp (L * Δ)) :=
    lt_of_le_of_lt hd1 (lt_of_lt_of_le hdlt (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hds : dist s w₀ < min δ₁ (Δ - w₀) :=
    lt_of_le_of_lt hd2 (lt_of_lt_of_le hdlt (min_le_right _ _))
  have hsΔ : s ∈ Icc (0 : ℝ) Δ := by
    refine ⟨hs0, ?_⟩
    have hlt' := lt_of_lt_of_le hds (min_le_right _ _)
    rw [Real.dist_eq] at hlt'
    linarith [(abs_lt.mp hlt').2]
  have h1 : dist (V.departureFlight η r' s) (V.departureFlight η r s) < ε / 2 := by
    refine lt_of_le_of_lt (hkey r' hr'pos hdr s hsΔ) ?_
    calc |r' - r| * Real.exp (L * Δ)
        < (ε / (2 * Real.exp (L * Δ))) * Real.exp (L * Δ) :=
          mul_lt_mul_of_pos_right hdr2 hexp
      _ = ε / 2 := by field_simp
  have h2 : dist (V.departureFlight η r s) (V.departureFlight η r w₀) < ε / 2 :=
    hδ₁spec hsΔ (lt_of_lt_of_le hds (min_le_left _ _))
  calc dist (V.departureFlight η r' s) (V.departureFlight η r w₀)
      ≤ dist (V.departureFlight η r' s) (V.departureFlight η r s) +
        dist (V.departureFlight η r s) (V.departureFlight η r w₀) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

/-! ### The departure flight at a fixed time as a total Borel map -/

/-- The departure flight at the fixed time `w`, extended by the departure point off the no-impact
set so that it is a total map of the speed line. -/
noncomputable def departureFlightAt (η : Γ.EdgeEnd) (w : ℝ) : ℝ → ℝ × ℝ := by
  classical
  exact fun r => if r ∈ V.departureNoImpactSet η w then V.departureFlight η r w
    else departurePoint η r

omit [Nonempty Γ.Edge] in
theorem departureFlightAt_of_mem {η : Γ.EdgeEnd} {w r : ℝ}
    (hr : r ∈ V.departureNoImpactSet η w) :
    V.departureFlightAt η w r = V.departureFlight η r w := by
  classical
  unfold departureFlightAt
  rw [if_pos hr]

omit [Nonempty Γ.Edge] in
theorem departureFlightAt_of_notMem {η : Γ.EdgeEnd} {w r : ℝ}
    (hr : r ∉ V.departureNoImpactSet η w) :
    V.departureFlightAt η w r = departurePoint η r := by
  classical
  unfold departureFlightAt
  rw [if_neg hr]

omit [Nonempty Γ.Edge] in
theorem continuous_departurePoint (η : Γ.EdgeEnd) :
    Continuous (departurePoint (Γ := Γ) η) := by
  unfold departurePoint
  fun_prop

theorem continuousOn_departureFlightAtTime (η : Γ.EdgeEnd) {w : ℝ} (hw : 0 < w) :
    ContinuousOn (fun r => V.departureFlight η r w) (V.departureNoImpactSet η w) := by
  have hcomp : ContinuousOn (fun r : ℝ => ((r, w) : ℝ × ℝ)) (V.departureNoImpactSet η w) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hmaps : MapsTo (fun r : ℝ => ((r, w) : ℝ × ℝ)) (V.departureNoImpactSet η w)
      (V.departurePreImpact η) := fun r hr =>
    ⟨hr.1, hw.le,
      (V.ofReal_lt_impactTime_iff (V.durationSet_nonempty_of_regularSpeed hr.1) hw).mpr hr.2⟩
  exact (V.continuousOn_departureFlight η).comp hcomp hmaps

/-- The total time-`w` departure flight map is Borel. -/
theorem measurable_departureFlightAt (η : Γ.EdgeEnd) {w : ℝ} (hw : 0 ≤ w) :
    Measurable (V.departureFlightAt η w) := by
  classical
  rcases hw.lt_or_eq with hpos | h0
  · refine measurable_of_measurable_union_cover (V.departureNoImpactSet η w)
      (V.departureNoImpactSet η w)ᶜ (V.measurableSet_departureNoImpactSet η hpos)
      (V.measurableSet_departureNoImpactSet η hpos).compl (by rw [union_compl_self]) ?_ ?_
    · change Measurable ((V.departureNoImpactSet η w).restrict (V.departureFlightAt η w))
      have heq : (V.departureNoImpactSet η w).restrict (V.departureFlightAt η w) =
          (V.departureNoImpactSet η w).restrict (fun r => V.departureFlight η r w) :=
        funext fun s => V.departureFlightAt_of_mem s.2
      rw [heq]
      exact (continuousOn_iff_continuous_restrict.mp
        (V.continuousOn_departureFlightAtTime η hpos)).measurable
    · change Measurable ((V.departureNoImpactSet η w)ᶜ.restrict (V.departureFlightAt η w))
      have heq : (V.departureNoImpactSet η w)ᶜ.restrict (V.departureFlightAt η w) =
          (V.departureNoImpactSet η w)ᶜ.restrict (departurePoint η) :=
        funext fun s => V.departureFlightAt_of_notMem s.2
      rw [heq]
      exact ((continuous_departurePoint η).comp continuous_subtype_val).measurable
  · have hid : V.departureFlightAt η w = departurePoint η := by
      funext r
      by_cases hr : r ∈ V.departureNoImpactSet η w
      · rw [V.departureFlightAt_of_mem hr, ← h0, V.departureFlight_zero]
      · rw [V.departureFlightAt_of_notMem hr]
    rw [hid]
    exact (continuous_departurePoint η).measurable

/-! ### The departure landing map -/

/-- The speeds at the germ `η` whose departure flight lands at or before `Δ`. -/
def departureImpactSet (η : Γ.EdgeEnd) (Δ : ℝ) : Set ℝ :=
  V.regularSpeeds η \ V.departureNoImpactSet η Δ

theorem measurableSet_departureImpactSet (η : Γ.EdgeEnd) {Δ : ℝ} (hΔ : 0 < Δ) :
    MeasurableSet (V.departureImpactSet η Δ) :=
  (V.isOpen_regularSpeeds η).measurableSet.diff (V.measurableSet_departureNoImpactSet η hΔ)

omit [Nonempty Γ.Edge] in
theorem bddAbove_of_mem_departureImpactSet {η : Γ.EdgeEnd} {Δ r : ℝ}
    (hr : r ∈ V.departureImpactSet η Δ) :
    BddAbove (durationSet V η.1 (departurePoint η r)) ∧
      sSup (durationSet V η.1 (departurePoint η r)) ≤ Δ := by
  have hnot : ¬ ∀ _ : BddAbove (durationSet V η.1 (departurePoint η r)),
      Δ < sSup (durationSet V η.1 (departurePoint η r)) := fun h => hr.2 ⟨hr.1, h⟩
  by_cases hbdd : BddAbove (durationSet V η.1 (departurePoint η r))
  · refine ⟨hbdd, ?_⟩
    by_contra hcon
    exact hnot fun _ => not_le.mp hcon
  · exact absurd (fun hb : BddAbove (durationSet V η.1 (departurePoint η r)) =>
      absurd hb hbdd) hnot

omit [Nonempty Γ.Edge] in
theorem departureDuration_pos {η : Γ.EdgeEnd} {Δ r : ℝ}
    (hr : r ∈ V.departureImpactSet η Δ) :
    0 < sSup (durationSet V η.1 (departurePoint η r)) :=
  FlightState.impactDuration_pos_of_bddAbove (V := V) (V.ofDeparture η hr.1.1 hr.1.2)
    (V.bddAbove_of_mem_departureImpactSet hr).1

/-- The departure impact duration is Borel on the departure impact stratum. -/
theorem measurable_departureDuration (η : Γ.EdgeEnd) (Δ : ℝ) :
    Measurable fun s : V.departureImpactSet η Δ =>
      sSup (durationSet V η.1 (departurePoint η (s : ℝ))) := by
  have hincl : Measurable fun s : V.departureImpactSet η Δ =>
      (⟨(s : ℝ), s.2.1⟩ : V.regularSpeeds η) :=
    measurable_subtype_coe.subtype_mk
  have hmeas : Measurable fun s : V.departureImpactSet η Δ =>
      V.impactTime η.1 (departurePoint η (s : ℝ)) :=
    (V.measurable_departureImpactTime η).comp hincl
  have hfun : (fun s : V.departureImpactSet η Δ =>
        sSup (durationSet V η.1 (departurePoint η (s : ℝ)))) =
      fun s : V.departureImpactSet η Δ =>
        (V.impactTime η.1 (departurePoint η (s : ℝ))).toReal := by
    funext s
    rw [V.impactTime_eq_ofReal_sSup (V.durationSet_nonempty_of_regularSpeed s.2.1)
      (V.bddAbove_of_mem_departureImpactSet s.2).1,
      ENNReal.toReal_ofReal (V.departureDuration_pos s.2).le]
  rw [hfun]
  exact hmeas.ennreal_toReal

/-- The **departure landing state**: the position and momentum at the first impact of the flight
leaving `η` with inward speed `r`. -/
noncomputable def departureLanding (η : Γ.EdgeEnd) (r : ℝ) : ℝ × ℝ :=
  V.departureFlight η r (sSup (durationSet V η.1 (departurePoint η r)))

/-- The dyadic approximations of the departure landing map. -/
noncomputable def departureLandingApprox (η : Γ.EdgeEnd) (n : ℕ) (r : ℝ) : ℝ × ℝ :=
  V.departureFlightAt η
    (((⌈2 ^ n * sSup (durationSet V η.1 (departurePoint η r))⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n) r

set_option maxHeartbeats 2000000 in -- the dyadic decomposition of the departure landing map unfolds a
-- nested `if`-guarded flight map against a countably valued time
theorem measurable_departureLandingApprox (η : Γ.EdgeEnd) (Δ : ℝ) (n : ℕ) :
    Measurable fun s : V.departureImpactSet η Δ =>
      V.departureLandingApprox η n (s : ℝ) := by
  have hT := V.measurable_departureDuration η Δ
  have hceil : Measurable fun s : V.departureImpactSet η Δ =>
      ⌈2 ^ n * sSup (durationSet V η.1 (departurePoint η (s : ℝ)))⌉₊ :=
    Nat.measurable_ceil.comp (measurable_const.mul hT)
  have hnum : Measurable fun s : V.departureImpactSet η Δ =>
      (⌈2 ^ n * sSup (durationSet V η.1 (departurePoint η (s : ℝ)))⌉₊ - 1 : ℕ) :=
    (measurable_of_countable (fun k : ℕ => k - 1)).comp hceil
  have hfix : ∀ m : ℕ, Measurable fun s : V.departureImpactSet η Δ =>
      V.departureFlightAt η ((m : ℝ) / 2 ^ n) (s : ℝ) := fun m =>
    (V.measurable_departureFlightAt η (by positivity)).comp measurable_subtype_coe
  have hprod : Measurable fun p : ℕ × V.departureImpactSet η Δ =>
      V.departureFlightAt η ((p.1 : ℝ) / 2 ^ n) (p.2 : ℝ) :=
    measurable_from_prod_countable_right hfix
  have hfinal : Measurable fun s : V.departureImpactSet η Δ =>
      V.departureFlightAt η
        (((⌈2 ^ n * sSup (durationSet V η.1 (departurePoint η (s : ℝ)))⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n)
        (s : ℝ) :=
    hprod.comp (hnum.prodMk measurable_id)
  simpa only [departureLandingApprox] using hfinal

omit [Nonempty Γ.Edge] in
theorem tendsto_departureLandingApprox (η : Γ.EdgeEnd) {Δ r : ℝ}
    (hr : r ∈ V.departureImpactSet η Δ) :
    Tendsto (fun n => V.departureLandingApprox η n r) atTop
      (𝓝 (V.departureLanding η r)) := by
  classical
  obtain ⟨hbdd, hTΔ⟩ := V.bddAbove_of_mem_departureImpactSet hr
  have hT0 : 0 < sSup (durationSet V η.1 (departurePoint η r)) := V.departureDuration_pos hr
  have hlow : ∀ n : ℕ,
      ((⌈2 ^ n * sSup (durationSet V η.1 (departurePoint η r))⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n
        < sSup (durationSet V η.1 (departurePoint η r)) := fun n => (dyadic_below hT0 n).1
  have hgap : ∀ n : ℕ, sSup (durationSet V η.1 (departurePoint η r)) -
      ((⌈2 ^ n * sSup (durationSet V η.1 (departurePoint η r))⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n
        ≤ (1 / 2) ^ n := fun n => (dyadic_below hT0 n).2
  have hsurv : ∀ n : ℕ, r ∈ V.departureNoImpactSet η
      (((⌈2 ^ n * sSup (durationSet V η.1 (departurePoint η r))⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n) :=
    fun n => ⟨hr.1, fun _ => hlow n⟩
  have happrox : ∀ n : ℕ, V.departureLandingApprox η n r =
      FlightState.flightCurve V (V.ofDeparture η hr.1.1 hr.1.2)
        (((⌈2 ^ n * sSup (durationSet V η.1 (departurePoint η r))⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n) := by
    intro n
    rw [departureLandingApprox, V.departureFlightAt_of_mem (hsurv n),
      V.departureFlight_of_mem hr.1]
  have hland : V.departureLanding η r =
      FlightState.flightCurve V (V.ofDeparture η hr.1.1 hr.1.2)
        (sSup (durationSet V η.1 (departurePoint η r))) := by
    rw [departureLanding, V.departureFlight_of_mem hr.1]
  have hcont : ContinuousWithinAt
      (FlightState.flightCurve V (V.ofDeparture η hr.1.1 hr.1.2))
      (Iic (sSup (durationSet V η.1 (departurePoint η r))))
      (sSup (durationSet V η.1 (departurePoint η r))) :=
    (FlightState.flightCurve_hasDerivWithinAt_Iic_sSup
      (V.ofDeparture η hr.1.1 hr.1.2) hbdd).continuousWithinAt
  have htend : Tendsto (fun n : ℕ =>
      ((⌈2 ^ n * sSup (durationSet V η.1 (departurePoint η r))⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n) atTop
      (𝓝[Iic (sSup (durationSet V η.1 (departurePoint η r)))]
        (sSup (durationSet V η.1 (departurePoint η r)))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun n => (hlow n).le)
    refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : ((1 : ℝ) / 2) < 1)
    refine ⟨N, fun n hn => ?_⟩
    have hmono : ((1 : ℝ) / 2) ^ n ≤ ((1 : ℝ) / 2) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    rw [Real.dist_eq, abs_of_nonpos (by linarith [hlow n])]
    linarith [hgap n]
  rw [hland]
  simp only [happrox]
  exact hcont.tendsto.comp htend

/-- **The departure landing map is Borel.** -/
theorem measurable_departureLanding (η : Γ.EdgeEnd) (Δ : ℝ) :
    Measurable fun s : V.departureImpactSet η Δ => V.departureLanding η (s : ℝ) :=
  measurable_of_tendsto_metrizable
    (f := fun n (s : V.departureImpactSet η Δ) => V.departureLandingApprox η n (s : ℝ))
    (fun n => V.measurable_departureLandingApprox η Δ n)
    (tendsto_pi_nhds.mpr fun s => V.tendsto_departureLandingApprox η s.2)

end Continuity

end MechanicalPotential

end HamiltonianMetricGraphs
