/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.2: continuity and Borel measurability of the edge flight map
-/

import HamiltonianMetricGraphs.NoImpact

/-!
# The edge flight map: continuity and Borel measurability

`edgeFlight V e x t` is the state reached at time `t` by the flight issued from the interior
regular state `x` of the edge `e`.  This module proves the two regularity statements that the
paper's Lemma VI.2 needs about it.

* **Joint continuity before the impact** (`continuousOn_edgeFlight`).  On the region
  `{(x,t) | 0 ≤ t < T(x)}`, where `T` is the impact time of `NoImpact.lean`, the flight map is
  continuous.  In the initial condition this is the Grönwall comparison
  `FlightState.dist_flightCurve_le` of two flights on the same edge — they are confined to one
  physical momentum box because their energies lie in a common compact window — and in the time
  variable it is the edge ODE.

* **Borel measurability of the landing map** (`measurable_landingState`).  The landing state
  `x ↦ φ_{T(x)}(x)` is *not* continuous: `T` is only lower semicontinuous.  It is nevertheless
  Borel, because it is the pointwise limit of the maps `x ↦ φ_{s_n(x)}(x)` where `s_n(x)` is the
  largest dyadic time of level `n` strictly below `T(x)`: each `s_n` is countably valued and
  measurable, on each of its level sets the flight map is continuous by the previous item, and
  `φ_s(x) → φ_{T(x)}(x)` as `s ↑ T(x)` because the flight has a one-sided derivative at its
  landing time.

Together with `isOpen_noImpactSet` and `measurable_impactTime` these replace the paper's
Lusin--Souslin argument for the tube charts.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter Metric MeasureTheory PhysicalEdgeSegment
open scoped Topology NNReal ENNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

namespace FlightState

/-! ### The flight is confined to the momentum box of its energy window -/

/-- A flight whose energy lies in a compact window `K` stays, for as long as it lasts, inside the
physical momentum box of the uniform speed bound of `K`. -/
theorem flightCurve_mem_closedEdgeMomentumBox (a : V.FlightState) {P : ℝ} {K : Set ℝ}
    (hPbound : ∀ e : Γ.Edge, ∀ q p E : ℝ, q ∈ Icc (0 : ℝ) (Γ.length e) → E ∈ K →
      V.hamiltonian e q p = E → |p| ≤ P)
    (haE : a.energy ∈ K) {t : ℝ} (ht0 : 0 ≤ t)
    (hdur : ∀ _ : BddAbove (durationSet V a.edge a.state),
      t ≤ sSup (durationSet V a.edge a.state)) :
    flightCurve V a t ∈ closedEdgeMomentumBox a.edge P := by
  have hphys := flightCurve_physical V a ht0 hdur
  have hen := flightCurve_hamiltonian_eq V a ht0 hdur
  refine ⟨hphys, ?_⟩
  have habs := hPbound a.edge (flightCurve V a t).1 (flightCurve V a t).2 a.energy hphys haE hen
  rw [mem_Icc]
  constructor <;> [linarith [abs_le.mp habs |>.1]; linarith [abs_le.mp habs |>.2]]

/-! ### Grönwall comparison of two flights on one edge -/

/-- **Grönwall comparison of two flights.**  Two flights on the same edge which both last until
`D` and are both confined to one physical momentum box stay exponentially close on `[0, D]`. -/
theorem dist_flightCurve_le (a b : V.FlightState) (hbe : b.edge = a.edge)
    {P : ℝ} {L : ℝ≥0} {D : ℝ}
    (hL : LipschitzOnWith L (V.edgeVectorField a.edge) (closedEdgeMomentumBox a.edge P))
    (hdura : ∀ _ : BddAbove (durationSet V a.edge a.state),
      D ≤ sSup (durationSet V a.edge a.state))
    (hdurb : ∀ _ : BddAbove (durationSet V b.edge b.state),
      D ≤ sSup (durationSet V b.edge b.state))
    (hboxa : ∀ t ∈ Icc (0 : ℝ) D, flightCurve V a t ∈ closedEdgeMomentumBox a.edge P)
    (hboxb : ∀ t ∈ Icc (0 : ℝ) D, flightCurve V b t ∈ closedEdgeMomentumBox a.edge P) :
    ∀ t ∈ Icc (0 : ℝ) D, dist (flightCurve V b t) (flightCurve V a t) ≤
      dist b.state a.state * Real.exp (L * t) := by
  have hderivb : ∀ t ∈ Icc (0 : ℝ) D,
      HasDerivWithinAt (flightCurve V b)
        (V.edgeVectorField a.edge (flightCurve V b t)) (Icc (0 : ℝ) D) t := by
    intro t ht
    rw [← hbe]
    exact flightCurve_hasDerivWithinAt_Icc b hdurb ht
  have hderiva : ∀ t ∈ Icc (0 : ℝ) D,
      HasDerivWithinAt (flightCurve V a)
        (V.edgeVectorField a.edge (flightCurve V a t)) (Icc (0 : ℝ) D) t :=
    fun t ht => flightCurve_hasDerivWithinAt_Icc a hdura ht
  intro t ht
  have h := dist_le_of_trajectories_ODE_of_mem (v := fun _ => V.edgeVectorField a.edge)
    (s := fun _ => closedEdgeMomentumBox a.edge P) (K := L) (a := 0) (b := D)
    (f := flightCurve V b) (g := flightCurve V a) (δ := dist b.state a.state)
    (fun _ _ => hL)
    (fun s hs => (hderivb s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_mem_Icc hs (hderivb s (Ico_subset_Icc_self hs)))
    (fun s hs => hboxb s (Ico_subset_Icc_self hs))
    (fun s hs => (hderiva s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_mem_Icc hs (hderiva s (Ico_subset_Icc_self hs)))
    (fun s hs => hboxa s (Ico_subset_Icc_self hs))
    (by rw [flightCurve_zero, flightCurve_zero]) t ht
  rwa [sub_zero] at h

end FlightState

/-! ### The edge flight map -/

/-- The **edge flight map**: the state reached at time `t` by the flight issued from `x`, for `x`
an interior regular state of the edge `e` (and `x` itself elsewhere, a junk value). -/
noncomputable def edgeFlight (e : Γ.Edge) (x : ℝ × ℝ) (t : ℝ) : ℝ × ℝ := by
  classical
  exact if h : x ∈ V.interiorRegular e then
    FlightState.flightCurve V (FlightState.ofInterior V h.1 h.2) t
  else x

theorem edgeFlight_of_mem {e : Γ.Edge} {x : ℝ × ℝ} (h : x ∈ V.interiorRegular e) (t : ℝ) :
    V.edgeFlight e x t = FlightState.flightCurve V (FlightState.ofInterior V h.1 h.2) t := by
  classical
  unfold edgeFlight
  rw [dif_pos h]

theorem edgeFlight_of_notMem {e : Γ.Edge} {x : ℝ × ℝ} (h : x ∉ V.interiorRegular e) (t : ℝ) :
    V.edgeFlight e x t = x := by
  classical
  unfold edgeFlight
  rw [dif_neg h]

@[simp] theorem edgeFlight_zero (e : Γ.Edge) (x : ℝ × ℝ) : V.edgeFlight e x 0 = x := by
  by_cases h : x ∈ V.interiorRegular e
  · rw [V.edgeFlight_of_mem h, FlightState.flightCurve_zero]
    rfl
  · rw [V.edgeFlight_of_notMem h]

/-- The region on which the edge flight map is the genuine pre-impact flow: the interior regular
states together with the times strictly before their impact. -/
def preImpactRegion (e : Γ.Edge) : Set ((ℝ × ℝ) × ℝ) :=
  {z | z.1 ∈ V.interiorRegular e ∧ 0 ≤ z.2 ∧ ENNReal.ofReal z.2 < V.impactTime e z.1}

theorem durationSet_nonempty_of_interiorRegular {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x ∈ V.interiorRegular e) : (durationSet V e x).Nonempty :=
  PhysicalEdgeSegment.durationSet_nonempty
    (Classical.choose (V.exists_physicalEdgeSegment_from_interior hx.1))

/-- Inside the pre-impact region at a positive time, the flight survives past that time. -/
theorem survives_of_mem_preImpactRegion {e : Γ.Edge} {x : ℝ × ℝ} {t : ℝ}
    (hx : x ∈ V.interiorRegular e) (ht : 0 < t) (hlt : ENNReal.ofReal t < V.impactTime e x) :
    ∀ _ : BddAbove (durationSet V e x), t < sSup (durationSet V e x) :=
  (V.ofReal_lt_impactTime_iff (V.durationSet_nonempty_of_interiorRegular hx) ht).mp hlt

/-- Inside the pre-impact region the flight lasts at least until that time. -/
theorem lasts_of_mem_preImpactRegion {e : Γ.Edge} {x : ℝ × ℝ} {t : ℝ}
    (hx : x ∈ V.interiorRegular e) (ht : 0 ≤ t) (hlt : ENNReal.ofReal t < V.impactTime e x) :
    ∀ _ : BddAbove (durationSet V e x), t ≤ sSup (durationSet V e x) := by
  intro hbdd
  rcases ht.lt_or_eq with h | h
  · exact (V.survives_of_mem_preImpactRegion hx h hlt hbdd).le
  · rw [← h]
    exact le_of_lt (FlightState.impactDuration_pos_of_bddAbove (V := V)
      (FlightState.ofInterior V hx.1 hx.2) hbdd)

/-! ### Joint continuity of the edge flight map before the impact -/

/-- **The edge flight map is continuous before the impact.**  Continuity in the initial condition
is the Grönwall comparison of two flights on the same edge; continuity in the time variable is the
edge ODE. -/
theorem continuousOn_edgeFlight (e : Γ.Edge) :
    ContinuousOn (fun z : (ℝ × ℝ) × ℝ => V.edgeFlight e z.1 z.2) (V.preImpactRegion e) := by
  classical
  rintro ⟨x, t₀⟩ hmem
  have hx : x ∈ V.interiorRegular e := hmem.1
  have ht₀ : (0 : ℝ) ≤ t₀ := hmem.2.1
  have hlt : ENNReal.ofReal t₀ < V.impactTime e x := hmem.2.2
  -- choose a survival time `Δ > t₀` for the reference flight
  obtain ⟨Δ, hΔ0, htΔ, hΔf⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have ht₀Δ : t₀ < Δ := by
    rcases lt_or_ge t₀ Δ with h | h
    · exact h
    · exact absurd (ENNReal.ofReal_le_ofReal h) (not_le.mpr htΔ)
  have hΔpos : 0 < Δ := lt_of_le_of_lt ht₀ ht₀Δ
  have hxne := V.durationSet_nonempty_of_interiorRegular hx
  have hxsurv : ∀ _ : BddAbove (durationSet V e x), Δ < sSup (durationSet V e x) :=
    (V.ofReal_lt_impactTime_iff hxne hΔpos).mp hΔf
  set a : V.FlightState := FlightState.ofInterior V hx.1 hx.2 with ha
  have hae : a.edge = e := rfl
  have has : a.state = x := rfl
  -- a compact energy window around the reference energy
  set K : Set ℝ := Icc (a.energy - 1) (a.energy + 1) with hK
  obtain ⟨P, hP, hPbound⟩ := V.exists_compact_energy_speed_bound K isCompact_Icc
  obtain ⟨L, hL⟩ := V.exists_lipschitzOnWith_edgeVectorField_closedMomentumBox e P
  have haE : a.energy ∈ K := by rw [hK, mem_Icc]; constructor <;> linarith
  -- the reference flight survives past `Δ`, hence stays in the box
  have hdura : ∀ s ∈ Icc (0 : ℝ) Δ,
      ∀ _ : BddAbove (durationSet V a.edge a.state), s ≤ sSup (durationSet V a.edge a.state) :=
    fun s hs hbdd => le_trans hs.2 (hxsurv hbdd).le
  have hboxa : ∀ s ∈ Icc (0 : ℝ) Δ,
      FlightState.flightCurve V a s ∈ closedEdgeMomentumBox e P := fun s hs =>
    FlightState.flightCurve_mem_closedEdgeMomentumBox V a hPbound haE hs.1 (hdura s hs)
  -- nearby states are interior regular, have energy in `K` and survive past `Δ`
  obtain ⟨ρ₀, hρ₀, hρ₀spec⟩ := FlightState.noImpact_persists V a hx.1 hΔpos hxsurv
  have hEcont : ContinuousAt (fun y : ℝ × ℝ => V.hamiltonian e y.1 y.2) x :=
    V.continuousAt_hamiltonian_prod (V.closedEdge_subset_domain e ⟨hx.1.1.le, hx.1.2.le⟩)
  obtain ⟨ρ₁, hρ₁, hρ₁spec⟩ := Metric.continuousAt_iff.mp hEcont 1 one_pos
  obtain ⟨ρ₂, hρ₂, hρ₂spec⟩ :=
    Metric.isOpen_iff.mp (V.isOpen_interiorRegular e) x hx
  -- the flight-to-flight estimate on the ball of radius `ρ`
  set ρ : ℝ := min (min ρ₀ ρ₁) ρ₂ with hρdef
  have hρpos : 0 < ρ := lt_min (lt_min hρ₀ hρ₁) hρ₂
  have hkey : ∀ y : ℝ × ℝ, dist y x < ρ → ∀ s ∈ Icc (0 : ℝ) Δ,
      dist (V.edgeFlight e y s) (V.edgeFlight e x s) ≤ dist y x * Real.exp (L * Δ) := by
    intro y hy s hs
    have hyIR : y ∈ V.interiorRegular e :=
      hρ₂spec (Metric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_right _ _)))
    set b : V.FlightState := FlightState.ofInterior V hyIR.1 hyIR.2 with hb
    have hbe : b.edge = e := rfl
    have hbs : b.state = y := rfl
    have hyρ₀ : dist y x < ρ₀ :=
      lt_of_lt_of_le hy (le_trans (min_le_left _ _) (min_le_left _ _))
    have hyρ₁ : dist y x < ρ₁ :=
      lt_of_lt_of_le hy (le_trans (min_le_left _ _) (min_le_right _ _))
    have hbsurv : ∀ _ : BddAbove (durationSet V b.edge b.state),
        Δ < sSup (durationSet V b.edge b.state) := hρ₀spec b rfl hyρ₀
    have hdurb : ∀ s ∈ Icc (0 : ℝ) Δ,
        ∀ _ : BddAbove (durationSet V b.edge b.state), s ≤ sSup (durationSet V b.edge b.state) :=
      fun s hs hbdd => le_trans hs.2 (hbsurv hbdd).le
    have hbE : b.energy ∈ K := by
      have h1 := hρ₁spec hyρ₁
      rw [Real.dist_eq] at h1
      change |V.hamiltonian e y.1 y.2 - V.hamiltonian e x.1 x.2| < 1 at h1
      have hb' : b.energy = V.hamiltonian e y.1 y.2 := rfl
      have ha' : V.hamiltonian e x.1 x.2 = a.energy := rfl
      rw [ha'] at h1
      rw [hK, mem_Icc, hb']
      rcases abs_lt.mp h1 with ⟨hl, hr⟩
      constructor <;> linarith
    have hboxb : ∀ s ∈ Icc (0 : ℝ) Δ,
        FlightState.flightCurve V b s ∈ closedEdgeMomentumBox e P := fun s hs =>
      FlightState.flightCurve_mem_closedEdgeMomentumBox V b hPbound hbE hs.1 (hdurb s hs)
    have hgron := FlightState.dist_flightCurve_le V a b rfl hL (hdura Δ ⟨hΔpos.le, le_rfl⟩)
      (hdurb Δ ⟨hΔpos.le, le_rfl⟩) hboxa hboxb s hs
    rw [V.edgeFlight_of_mem hyIR, V.edgeFlight_of_mem hx]
    refine le_trans hgron ?_
    rw [hbs, has]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by
        have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
        nlinarith [hs.1, hs.2])) dist_nonneg
  -- continuity in the time variable
  have hflight : (fun s : ℝ => V.edgeFlight e x s) = FlightState.flightCurve V a := by
    funext s
    rw [V.edgeFlight_of_mem hx, ha]
  have htime : ContinuousWithinAt (fun s : ℝ => V.edgeFlight e x s) (Icc (0 : ℝ) Δ) t₀ := by
    rw [hflight]
    exact (FlightState.flightCurve_hasDerivWithinAt_Icc a (hdura Δ ⟨hΔpos.le, le_rfl⟩)
      ⟨ht₀, ht₀Δ.le⟩).continuousWithinAt
  -- combine
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hexp : (0 : ℝ) < Real.exp (L * Δ) := Real.exp_pos _
  obtain ⟨δ₁, hδ₁, hδ₁spec⟩ := Metric.continuousWithinAt_iff.mp htime (ε / 2) (by linarith)
  refine ⟨min (min ρ (ε / (2 * Real.exp (L * Δ)))) (min δ₁ (Δ - t₀)),
    lt_min (lt_min hρpos (by positivity)) (lt_min hδ₁ (by linarith)), ?_⟩
  rintro ⟨y, s⟩ hzmem hdlt
  have hs0 : (0 : ℝ) ≤ s := hzmem.2.1
  have hd1 : dist y x ≤ dist ((y, s) : (ℝ × ℝ) × ℝ) (x, t₀) := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hd2 : dist s t₀ ≤ dist ((y, s) : (ℝ × ℝ) × ℝ) (x, t₀) := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  have hdy : dist y x < ρ :=
    lt_of_le_of_lt hd1
      (lt_of_lt_of_le hdlt (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hdy2 : dist y x < ε / (2 * Real.exp (L * Δ)) :=
    lt_of_le_of_lt hd1
      (lt_of_lt_of_le hdlt (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hds : dist s t₀ < min δ₁ (Δ - t₀) :=
    lt_of_le_of_lt hd2 (lt_of_lt_of_le hdlt (min_le_right _ _))
  have hsΔ : s ∈ Icc (0 : ℝ) Δ := by
    refine ⟨hs0, ?_⟩
    have hlt' := lt_of_lt_of_le hds (min_le_right _ _)
    rw [Real.dist_eq] at hlt'
    linarith [(abs_lt.mp hlt').2]
  have h1 : dist (V.edgeFlight e y s) (V.edgeFlight e x s) < ε / 2 := by
    refine lt_of_le_of_lt (hkey y hdy s hsΔ) ?_
    calc dist y x * Real.exp (L * Δ) < (ε / (2 * Real.exp (L * Δ))) * Real.exp (L * Δ) :=
          mul_lt_mul_of_pos_right hdy2 hexp
      _ = ε / 2 := by field_simp
  have h2 : dist (V.edgeFlight e x s) (V.edgeFlight e x t₀) < ε / 2 :=
    hδ₁spec hsΔ (lt_of_lt_of_le hds (min_le_left _ _))
  calc dist (V.edgeFlight e y s) (V.edgeFlight e x t₀)
      ≤ dist (V.edgeFlight e y s) (V.edgeFlight e x s) +
        dist (V.edgeFlight e x s) (V.edgeFlight e x t₀) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring


/-! ### The flight at a fixed time as a total Borel map -/

/-- The flight at the fixed time `s`, extended by the identity off the no-impact set so that it is
a total map of the plane. -/
noncomputable def flightAt (e : Γ.Edge) (s : ℝ) : (ℝ × ℝ) → ℝ × ℝ := by
  classical
  exact fun x => if x ∈ V.noImpactSet e s then V.edgeFlight e x s else x

theorem flightAt_of_mem {e : Γ.Edge} {s : ℝ} {x : ℝ × ℝ} (hx : x ∈ V.noImpactSet e s) :
    V.flightAt e s x = V.edgeFlight e x s := by
  classical
  unfold flightAt
  rw [if_pos hx]

theorem flightAt_of_notMem {e : Γ.Edge} {s : ℝ} {x : ℝ × ℝ} (hx : x ∉ V.noImpactSet e s) :
    V.flightAt e s x = x := by
  classical
  unfold flightAt
  rw [if_neg hx]

/-- The time-`s` edge flow is continuous on the no-impact set at time `s`. -/
theorem continuousOn_flightAtTime (e : Γ.Edge) {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun x => V.edgeFlight e x s) (V.noImpactSet e s) := by
  have hcomp : ContinuousOn (fun x : ℝ × ℝ => ((x, s) : (ℝ × ℝ) × ℝ)) (V.noImpactSet e s) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hmaps : MapsTo (fun x : ℝ × ℝ => ((x, s) : (ℝ × ℝ) × ℝ)) (V.noImpactSet e s)
      (V.preImpactRegion e) := fun x hx =>
    ⟨hx.1, hs.le,
      (V.ofReal_lt_impactTime_iff (V.durationSet_nonempty_of_interiorRegular hx.1) hs).mpr hx.2⟩
  exact (V.continuousOn_edgeFlight e).comp hcomp hmaps

/-- The total time-`s` flight map is Borel: it is continuous on the open no-impact set and the
identity off it. -/
theorem measurable_flightAt (e : Γ.Edge) {s : ℝ} (hs : 0 ≤ s) : Measurable (V.flightAt e s) := by
  classical
  rcases hs.lt_or_eq with hpos | h0
  · refine measurable_of_measurable_union_cover (V.noImpactSet e s) (V.noImpactSet e s)ᶜ
      (V.measurableSet_noImpactSet e hpos) (V.measurableSet_noImpactSet e hpos).compl
      (by rw [union_compl_self]) ?_ ?_
    · change Measurable ((V.noImpactSet e s).restrict (V.flightAt e s))
      have heq : (V.noImpactSet e s).restrict (V.flightAt e s) =
          (V.noImpactSet e s).restrict (fun x => V.edgeFlight e x s) :=
        funext fun z => V.flightAt_of_mem z.2
      rw [heq]
      exact (continuousOn_iff_continuous_restrict.mp
        (V.continuousOn_flightAtTime e hpos)).measurable
    · change Measurable ((V.noImpactSet e s)ᶜ.restrict (V.flightAt e s))
      have heq : (V.noImpactSet e s)ᶜ.restrict (V.flightAt e s) = Subtype.val :=
        funext fun z => V.flightAt_of_notMem z.2
      rw [heq]
      exact measurable_subtype_coe
  · have hid : V.flightAt e s = id := by
      funext x
      by_cases hx : x ∈ V.noImpactSet e s
      · rw [V.flightAt_of_mem hx, ← h0, V.edgeFlight_zero]; rfl
      · rw [V.flightAt_of_notMem hx]; rfl
    rw [hid]
    exact measurable_id

/-! ### The impact stratum -/

theorem pos_of_mem_durationSet {e : Γ.Edge} {x : ℝ × ℝ} {T : ℝ}
    (hT : T ∈ durationSet V e x) : 0 < T := by
  obtain ⟨h, hh⟩ := hT
  rw [← hh]
  exact h.duration_pos

/-- For a terminating flight the impact time of `NoImpact.lean` is the supremum of the segment
durations. -/
theorem impactTime_eq_ofReal_sSup {e : Γ.Edge} {x : ℝ × ℝ}
    (hne : (durationSet V e x).Nonempty) (hbdd : BddAbove (durationSet V e x)) :
    V.impactTime e x = ENNReal.ofReal (sSup (durationSet V e x)) := by
  rw [impactTime]
  refine le_antisymm (iSup_le fun T => ENNReal.ofReal_le_ofReal (le_csSup hbdd T.2)) ?_
  refine le_of_forall_lt fun y hy => ?_
  obtain ⟨r, hr0, hyr, hrS⟩ := ENNReal.lt_iff_exists_real_btwn.mp hy
  have hrlt : r < sSup (durationSet V e x) := by
    by_contra hcon
    exact absurd (ENNReal.ofReal_le_ofReal (not_lt.mp hcon)) (not_le.mpr hrS)
  obtain ⟨T, hT, hrT⟩ := (lt_csSup_iff hbdd hne).mp hrlt
  exact lt_of_lt_of_le hyr (le_trans (ENNReal.ofReal_le_ofReal hrT.le)
    (le_iSup (fun T : durationSet V e x => ENNReal.ofReal (T : ℝ)) ⟨T, hT⟩))

/-- The **impact stratum** at time `Δ`: the interior regular states whose flight lands at or
before `Δ`.  It is the complement of the no-impact set inside the interior regular sector, hence
Borel — this is the second stratum of Lemma VI.2. -/
def impactSetAt (e : Γ.Edge) (Δ : ℝ) : Set (ℝ × ℝ) :=
  V.interiorRegular e \ V.noImpactSet e Δ

theorem measurableSet_impactSetAt (e : Γ.Edge) {Δ : ℝ} (hΔ : 0 < Δ) :
    MeasurableSet (V.impactSetAt e Δ) :=
  (V.isOpen_interiorRegular e).measurableSet.diff (V.measurableSet_noImpactSet e hΔ)

theorem bddAbove_of_mem_impactSetAt {e : Γ.Edge} {Δ : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ V.impactSetAt e Δ) :
    BddAbove (durationSet V e x) ∧ sSup (durationSet V e x) ≤ Δ := by
  have hnot : ¬ ∀ _ : BddAbove (durationSet V e x), Δ < sSup (durationSet V e x) :=
    fun h => hx.2 ⟨hx.1, h⟩
  by_cases hbdd : BddAbove (durationSet V e x)
  · refine ⟨hbdd, ?_⟩
    by_contra hcon
    exact hnot fun _ => not_le.mp hcon
  · exact absurd (fun hb : BddAbove (durationSet V e x) => absurd hb hbdd) hnot

theorem impactDuration_pos_of_mem_impactSetAt {e : Γ.Edge} {Δ : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ V.impactSetAt e Δ) : 0 < sSup (durationSet V e x) :=
  FlightState.impactDuration_pos_of_bddAbove (V := V)
    (FlightState.ofInterior V hx.1.1 hx.1.2) (V.bddAbove_of_mem_impactSetAt hx).1

/-- The impact duration is Borel on the impact stratum: it is the real part of the lower
semicontinuous impact time. -/
theorem measurable_impactDuration (e : Γ.Edge) (Δ : ℝ) :
    Measurable fun z : V.impactSetAt e Δ => sSup (durationSet V e (z : ℝ × ℝ)) := by
  have hincl : Measurable fun z : V.impactSetAt e Δ =>
      (⟨(z : ℝ × ℝ), z.2.1⟩ : V.interiorRegular e) :=
    measurable_subtype_coe.subtype_mk
  have hmeas : Measurable fun z : V.impactSetAt e Δ => V.impactTime e (z : ℝ × ℝ) :=
    (V.measurable_impactTime e).comp hincl
  have hfun : (fun z : V.impactSetAt e Δ => sSup (durationSet V e (z : ℝ × ℝ))) =
      fun z : V.impactSetAt e Δ => (V.impactTime e (z : ℝ × ℝ)).toReal := by
    funext z
    rw [V.impactTime_eq_ofReal_sSup (V.durationSet_nonempty_of_interiorRegular z.2.1)
      (V.bddAbove_of_mem_impactSetAt z.2).1,
      ENNReal.toReal_ofReal (V.impactDuration_pos_of_mem_impactSetAt z.2).le]
  rw [hfun]
  exact hmeas.ennreal_toReal

/-! ### The landing map -/

/-- The **landing state** of a terminating flight: position and momentum at the first impact. -/
noncomputable def landingState (e : Γ.Edge) (x : ℝ × ℝ) : ℝ × ℝ :=
  V.edgeFlight e x (sSup (durationSet V e x))

/-- The dyadic time of level `n` just below a positive real, with the two estimates that make the
family an approximation from below. -/
theorem dyadic_below {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ((⌈2 ^ n * T⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n < T ∧
      T - ((⌈2 ^ n * T⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n ≤ (1 / 2) ^ n := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hr : 0 < 2 ^ n * T := by positivity
  have h1 : 1 ≤ ⌈2 ^ n * T⌉₊ := Nat.one_le_ceil_iff.mpr hr
  have hsucc : (⌈2 ^ n * T⌉₊ - 1 : ℕ) + 1 = ⌈2 ^ n * T⌉₊ := by omega
  have hlt : ((⌈2 ^ n * T⌉₊ - 1 : ℕ) : ℝ) < 2 ^ n * T := Nat.lt_ceil.mp (by omega)
  have hle : 2 ^ n * T ≤ ((⌈2 ^ n * T⌉₊ - 1 : ℕ) : ℝ) + 1 := by
    have hceil := Nat.le_ceil (2 ^ n * T)
    rw [← hsucc] at hceil
    push_cast at hceil
    linarith
  have h2n : ((1 : ℝ) / 2) ^ n = 1 / 2 ^ n := by rw [div_pow, one_pow]
  refine ⟨?_, ?_⟩
  · rw [div_lt_iff₀ hpow]; linarith
  · rw [h2n, sub_le_iff_le_add]
    have hstep : (2 ^ n * T) / 2 ^ n ≤ (((⌈2 ^ n * T⌉₊ - 1 : ℕ) : ℝ) + 1) / 2 ^ n := by gcongr
    calc T = (2 ^ n * T) / 2 ^ n := by field_simp
      _ ≤ (((⌈2 ^ n * T⌉₊ - 1 : ℕ) : ℝ) + 1) / 2 ^ n := hstep
      _ = 1 / 2 ^ n + ((⌈2 ^ n * T⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n := by ring

/-- The dyadic time of level `n` strictly below the impact time. -/
noncomputable def preImpactTime (e : Γ.Edge) (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  ((⌈2 ^ n * sSup (durationSet V e x)⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n

/-- The dyadic approximations of the landing map. -/
noncomputable def landingApprox (e : Γ.Edge) (n : ℕ) (x : ℝ × ℝ) : ℝ × ℝ :=
  V.flightAt e (V.preImpactTime e n x) x

set_option maxHeartbeats 2000000 in -- the dyadic decomposition of the landing map unfolds a
-- nested `if`-guarded flight map against a countably valued time
theorem measurable_landingApprox (e : Γ.Edge) (Δ : ℝ) (n : ℕ) :
    Measurable fun z : V.impactSetAt e Δ => V.landingApprox e n (z : ℝ × ℝ) := by
  have hT := V.measurable_impactDuration e Δ
  have hceil : Measurable fun z : V.impactSetAt e Δ =>
      ⌈2 ^ n * sSup (durationSet V e (z : ℝ × ℝ))⌉₊ :=
    Nat.measurable_ceil.comp (measurable_const.mul hT)
  have hnum : Measurable fun z : V.impactSetAt e Δ =>
      (⌈2 ^ n * sSup (durationSet V e (z : ℝ × ℝ))⌉₊ - 1 : ℕ) :=
    (measurable_of_countable (fun k : ℕ => k - 1)).comp hceil
  have hfix : ∀ m : ℕ, Measurable fun z : V.impactSetAt e Δ =>
      V.flightAt e ((m : ℝ) / 2 ^ n) (z : ℝ × ℝ) := fun m =>
    (V.measurable_flightAt e (by positivity)).comp measurable_subtype_coe
  have hprod : Measurable fun p : ℕ × V.impactSetAt e Δ =>
      V.flightAt e ((p.1 : ℝ) / 2 ^ n) (p.2 : ℝ × ℝ) :=
    measurable_from_prod_countable_right hfix
  have hfinal : Measurable fun z : V.impactSetAt e Δ =>
      V.flightAt e (((⌈2 ^ n * sSup (durationSet V e (z : ℝ × ℝ))⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n)
        (z : ℝ × ℝ) :=
    hprod.comp (hnum.prodMk measurable_id)
  simpa only [landingApprox, preImpactTime] using hfinal

theorem tendsto_landingApprox (e : Γ.Edge) {Δ : ℝ} {x : ℝ × ℝ} (hx : x ∈ V.impactSetAt e Δ) :
    Tendsto (fun n => V.landingApprox e n x) atTop (𝓝 (V.landingState e x)) := by
  classical
  obtain ⟨hbdd, hTΔ⟩ := V.bddAbove_of_mem_impactSetAt hx
  have hT0 : 0 < sSup (durationSet V e x) := V.impactDuration_pos_of_mem_impactSetAt hx
  have hlow : ∀ n : ℕ, V.preImpactTime e n x < sSup (durationSet V e x) :=
    fun n => (dyadic_below hT0 n).1
  have hgap : ∀ n : ℕ, sSup (durationSet V e x) - V.preImpactTime e n x ≤ (1 / 2) ^ n :=
    fun n => (dyadic_below hT0 n).2
  have hsurv : ∀ n : ℕ, x ∈ V.noImpactSet e (V.preImpactTime e n x) :=
    fun n => ⟨hx.1, fun _ => hlow n⟩
  have happrox : ∀ n : ℕ, V.landingApprox e n x =
      FlightState.flightCurve V (FlightState.ofInterior V hx.1.1 hx.1.2)
        (V.preImpactTime e n x) := by
    intro n
    rw [landingApprox, V.flightAt_of_mem (hsurv n), V.edgeFlight_of_mem hx.1]
  have hland : V.landingState e x =
      FlightState.flightCurve V (FlightState.ofInterior V hx.1.1 hx.1.2)
        (sSup (durationSet V e x)) := by
    rw [landingState, V.edgeFlight_of_mem hx.1]
  have hcont : ContinuousWithinAt
      (FlightState.flightCurve V (FlightState.ofInterior V hx.1.1 hx.1.2))
      (Iic (sSup (durationSet V e x))) (sSup (durationSet V e x)) :=
    (FlightState.flightCurve_hasDerivWithinAt_Iic_sSup
      (FlightState.ofInterior V hx.1.1 hx.1.2) hbdd).continuousWithinAt
  have htend : Tendsto (fun n => V.preImpactTime e n x) atTop
      (𝓝[Iic (sSup (durationSet V e x))] (sSup (durationSet V e x))) := by
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

/-- **The landing map is Borel on the impact stratum.**  It is the pointwise limit of the dyadic
approximations, each of which is Borel because the flight map is continuous strictly before the
impact and the dyadic pre-impact times are countably valued.  This is the measurability that the
paper obtains from the Lusin--Souslin theorem applied to the tube charts. -/
theorem measurable_landingState (e : Γ.Edge) (Δ : ℝ) :
    Measurable fun z : V.impactSetAt e Δ => V.landingState e (z : ℝ × ℝ) :=
  measurable_of_tendsto_metrizable
    (f := fun n (z : V.impactSetAt e Δ) => V.landingApprox e n (z : ℝ × ℝ))
    (fun n => V.measurable_landingApprox e Δ n)
    (tendsto_pi_nhds.mpr fun z => V.tendsto_landingApprox e z.2)

end MechanicalPotential

end HamiltonianMetricGraphs
