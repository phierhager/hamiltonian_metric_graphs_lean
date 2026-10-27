/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.2 (no-impact part): the no-impact condition is open.
-/

import HamiltonianMetricGraphs.FlightRetrace
import HamiltonianMetricGraphs.EdgeLiouville

/-!
# The no-impact set is open

Lemma VI.2 of the paper obtains the Borel structure of the short-time strata from the
Lusin--Souslin theorem applied to the tube charts.  For the **no-impact** stratum there is a
shorter and stronger argument, carried out here: the condition *"the flight from `x` survives past
time `Δ`"* is **open** in the initial condition, so the no-impact set is open and in particular
Borel.

The proof is the standard continuation argument.  The reference flight stays in the *open*
cylinder on the compact interval `[0, Δ]`, hence at distance at least `ε > 0` from the two
endpoints (`exists_interior_margin`).  If a nearby flight had an impact at some time `T ≤ Δ`, then
at that time it would sit on the boundary (`maximalEndpoint_coordinate_eq_zero_or_length`), while
the Grönwall estimate `dist_le_of_trajectories_ODE_of_mem` keeps it within `ε` of the reference
flight, which is `ε`-far from the boundary — a contradiction.

Combined with `measure_image_edgeFlow` (Lemma V.1) this gives the no-impact half of Lemma VI.3:
the time-`Δ` map preserves `dq dp` on every measurable subset of an open no-impact set
(`measure_image_edgeFlow_of_noImpact`).
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter Metric MeasureTheory PhysicalEdgeSegment
open scoped Topology NNReal ENNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

namespace FlightState

/-! ### The reference flight has an interior margin -/

/-- **The interior margin of a surviving flight.**  A flight that starts strictly inside its edge
and survives past `Δ` stays, on the whole of `[0, Δ]`, at a positive distance from both
endpoints. -/
theorem exists_interior_margin (a : V.FlightState)
    (hint : a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge)) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hsurv : ∀ _ : BddAbove (durationSet V a.edge a.state),
      Δ < sSup (durationSet V a.edge a.state)) :
    ∃ ε > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) Δ,
      ε ≤ (flightCurve V a t).1 ∧ ε ≤ Γ.length a.edge - (flightCurve V a t).1 := by
  classical
  -- the flight is interior on the whole of `[0, Δ]`
  have hinterior : ∀ t ∈ Icc (0 : ℝ) Δ,
      (flightCurve V a t).1 ∈ Ioo (0 : ℝ) (Γ.length a.edge) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, flightCurve_zero]; exact hint
    · exact flightCurve_interior V a h0 (fun hbdd => lt_of_le_of_lt ht.2 (hsurv hbdd))
  -- the margin is a continuous positive function on a compact interval
  set g : ℝ → ℝ := fun t =>
    min (flightCurve V a t).1 (Γ.length a.edge - (flightCurve V a t).1) with hg
  have hcont : ContinuousOn g (Icc (0 : ℝ) Δ) := by
    have hq : ContinuousOn (fun t => (flightCurve V a t).1) (Icc (0 : ℝ) Δ) := by
      intro t ht
      exact ((flightCurve_hasDerivWithinAt_Icc a
        (fun hbdd => le_of_lt (hsurv hbdd)) ht).continuousWithinAt).fst
    have hr : ContinuousOn (fun t => Γ.length a.edge - (flightCurve V a t).1)
        (Icc (0 : ℝ) Δ) := continuousOn_const.sub hq
    have h : ContinuousOn
        (fun t => (flightCurve V a t).1 ⊓ (Γ.length a.edge - (flightCurve V a t).1))
        (Icc (0 : ℝ) Δ) := hq.inf hr
    rw [hg]
    exact h
  have hne : (Icc (0 : ℝ) Δ).Nonempty := nonempty_Icc.mpr hΔ
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  refine ⟨g t₀, ?_, fun t ht => ?_⟩
  · have h := hinterior t₀ ht₀
    rw [hg]
    exact lt_min h.1 (by linarith [h.2])
  · exact ⟨le_trans (hmin ht) (min_le_left _ _), le_trans (hmin ht) (min_le_right _ _)⟩

/-! ### Persistence of the no-impact condition -/

/-- **The no-impact condition is open.**  If the flight from `a` survives past `Δ`, then so does
the flight from every state on the same edge whose initial point is close enough to `a`'s.

This is the no-impact half of Lemma VI.2, with a continuation argument in place of the paper's
Lusin--Souslin one; in particular the no-impact set is *open*, not merely Borel. -/
theorem noImpact_persists (a : V.FlightState)
    (hint : a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge)) {Δ : ℝ} (hΔ : 0 < Δ)
    (hsurv : ∀ _ : BddAbove (durationSet V a.edge a.state),
      Δ < sSup (durationSet V a.edge a.state)) :
    ∃ ρ > (0 : ℝ), ∀ b : V.FlightState, b.edge = a.edge → dist b.state a.state < ρ →
      ∀ _ : BddAbove (durationSet V b.edge b.state),
        Δ < sSup (durationSet V b.edge b.state) := by
  classical
  obtain ⟨ε, hε, hmargin⟩ := exists_interior_margin V a hint hΔ.le hsurv
  -- a uniform momentum bound for all energies near `a.energy`
  set K : Set ℝ := Icc (a.energy - 1) (a.energy + 1) with hK
  obtain ⟨P, hP, hPbound⟩ := V.exists_compact_energy_speed_bound K isCompact_Icc
  obtain ⟨L, hL⟩ := V.exists_lipschitzOnWith_edgeVectorField_closedMomentumBox a.edge P
  -- the energy is continuous, so nearby states have energy in `K`
  have hEcont : ContinuousAt (fun y : ℝ × ℝ => V.hamiltonian a.edge y.1 y.2) a.state := by
    have hV : ContinuousAt (V.extension a.edge) a.state.1 :=
      V.extension_continuousAt_of_mem (V.closedEdge_subset_domain a.edge
        ⟨hint.1.le, hint.2.le⟩)
    have h1 : ContinuousAt (fun y : ℝ × ℝ => V.extension a.edge y.1) a.state :=
      hV.comp continuousAt_fst
    have h2 : ContinuousAt (fun y : ℝ × ℝ => y.2 ^ 2 / 2) a.state := by fun_prop
    exact h2.add h1
  obtain ⟨ρ₁, hρ₁, hρ₁spec⟩ := Metric.continuousAt_iff.mp hEcont 1 one_pos
  refine ⟨min ρ₁ (ε / Real.exp (L * Δ)), lt_min hρ₁ (by positivity), ?_⟩
  intro b hbe hbdist hbdd
  by_contra hcon
  rw [not_lt] at hcon
  set T : ℝ := sSup (durationSet V b.edge b.state) with hT
  have hT0 : 0 < T := impactDuration_pos_of_bddAbove (V := V) b hbdd
  have hTΔ : T ≤ Δ := hcon
  -- the energy of `b` lies in the compact window
  have hbE : b.energy ∈ K := by
    have hd : dist b.state a.state < ρ₁ := lt_of_lt_of_le hbdist (min_le_left _ _)
    have h1 := hρ₁spec hd
    rw [Real.dist_eq] at h1
    change |V.hamiltonian a.edge b.state.1 b.state.2 -
      V.hamiltonian a.edge a.state.1 a.state.2| < 1 at h1
    have hb' : b.energy = V.hamiltonian a.edge b.state.1 b.state.2 := by
      change V.hamiltonian b.edge b.state.1 b.state.2 = _
      rw [hbe]
    have ha' : V.hamiltonian a.edge a.state.1 a.state.2 = a.energy := rfl
    rw [ha'] at h1
    rw [hK, mem_Icc, hb']
    rcases abs_lt.mp h1 with ⟨hl, hr⟩
    constructor <;> linarith
  have haE : a.energy ∈ K := by rw [hK, mem_Icc]; constructor <;> linarith
  -- both flights are confined to the same physical momentum box on `[0, T]`
  have hbox : ∀ (c : V.FlightState), c.edge = a.edge → c.energy ∈ K →
      ∀ t ∈ Icc (0 : ℝ) T,
        (∀ hbdd' : BddAbove (durationSet V c.edge c.state),
          t ≤ sSup (durationSet V c.edge c.state)) →
        flightCurve V c t ∈ closedEdgeMomentumBox a.edge P := by
    intro c hce hcE t ht hdur
    have hphys := flightCurve_physical V c ht.1 hdur
    have hen := flightCurve_hamiltonian_eq V c ht.1 hdur
    refine ⟨by rw [← hce]; exact hphys, ?_⟩
    have habs := hPbound c.edge (flightCurve V c t).1 (flightCurve V c t).2 c.energy
      hphys hcE hen
    rw [mem_Icc]
    constructor <;> [linarith [abs_le.mp habs |>.1]; linarith [abs_le.mp habs |>.2]]
  have hdurb : ∀ t ∈ Icc (0 : ℝ) T,
      ∀ _ : BddAbove (durationSet V b.edge b.state), t ≤ sSup (durationSet V b.edge b.state) :=
    fun t ht _ => by rw [← hT]; exact ht.2
  have hdura : ∀ t ∈ Icc (0 : ℝ) T,
      ∀ hbdd' : BddAbove (durationSet V a.edge a.state),
        t ≤ sSup (durationSet V a.edge a.state) :=
    fun t ht hbdd' => le_trans (le_trans ht.2 hTΔ) (le_of_lt (hsurv hbdd'))
  -- the flight of `b` solves the edge equation of `a.edge` as well
  have hderivb : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (flightCurve V b)
        (V.edgeVectorField a.edge (flightCurve V b t)) (Icc (0 : ℝ) T) t := by
    intro t ht
    rw [← hbe]
    exact flightCurve_hasDerivWithinAt_Icc b (hdurb T ⟨hT0.le, le_rfl⟩) ht
  have hderiva : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (flightCurve V a)
        (V.edgeVectorField a.edge (flightCurve V a t)) (Icc (0 : ℝ) T) t :=
    fun t ht => flightCurve_hasDerivWithinAt_Icc a (hdura T ⟨hT0.le, le_rfl⟩) ht
  -- Grönwall on `[0, T]`
  have hgron := dist_le_of_trajectories_ODE_of_mem (v := fun _ => V.edgeVectorField a.edge)
    (s := fun _ => closedEdgeMomentumBox a.edge P) (K := L) (a := 0) (b := T)
    (f := flightCurve V b) (g := flightCurve V a) (δ := dist b.state a.state)
    (fun _ _ => hL)
    (fun t ht => (hderivb t ht).continuousWithinAt)
    (fun t ht => hasDerivWithinAt_Ici_of_mem_Icc ht (hderivb t (Ico_subset_Icc_self ht)))
    (fun t ht => hbox b hbe hbE t (Ico_subset_Icc_self ht)
      (hdurb t (Ico_subset_Icc_self ht)))
    (fun t ht => (hderiva t ht).continuousWithinAt)
    (fun t ht => hasDerivWithinAt_Ici_of_mem_Icc ht (hderiva t (Ico_subset_Icc_self ht)))
    (fun t ht => hbox a rfl haE t (Ico_subset_Icc_self ht)
      (hdura t (Ico_subset_Icc_self ht)))
    (by rw [flightCurve_zero, flightCurve_zero]) T ⟨hT0.le, le_rfl⟩
  rw [sub_zero] at hgron
  -- the flight of `b` is on the boundary at time `T`, the reference flight is `ε` away from it
  have hbend : (flightCurve V b T).1 = 0 ∨ (flightCurve V b T).1 = Γ.length a.edge := by
    rw [← hbe, hT, flightCurve_sSup b hbdd]
    exact b.segment.maximalEndpoint_coordinate_eq_zero_or_length hbdd
  have hmargT := hmargin T ⟨hT0.le, hTΔ⟩
  have hqdist : ε ≤ |(flightCurve V b T).1 - (flightCurve V a T).1| := by
    rcases hbend with h0 | hl
    · rw [h0, zero_sub, abs_neg, abs_of_nonneg (le_trans hε.le hmargT.1)]
      exact hmargT.1
    · rw [hl, abs_of_nonneg (by linarith [hmargT.2])]
      linarith [hmargT.2]
  have hdistq : |(flightCurve V b T).1 - (flightCurve V a T).1| ≤
      dist (flightCurve V b T) (flightCurve V a T) := by
    rw [dist_eq_norm, Prod.norm_def]
    exact le_max_left _ _
  -- but Grönwall keeps them closer than `ε`
  have hexp : Real.exp (L * T) ≤ Real.exp (L * Δ) :=
    Real.exp_le_exp.mpr (by
      have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
      nlinarith [hT0.le])
  have hsmall : dist b.state a.state * Real.exp (L * T) < ε := by
    have h1 : dist b.state a.state < ε / Real.exp (L * Δ) :=
      lt_of_lt_of_le hbdist (min_le_right _ _)
    have h2 : (0 : ℝ) < Real.exp (L * Δ) := Real.exp_pos _
    calc dist b.state a.state * Real.exp (L * T)
        ≤ dist b.state a.state * Real.exp (L * Δ) :=
          mul_le_mul_of_nonneg_left hexp dist_nonneg
      _ < (ε / Real.exp (L * Δ)) * Real.exp (L * Δ) := by
          exact mul_lt_mul_of_pos_right h1 h2
      _ = ε := by field_simp
  linarith [hqdist.trans (hdistq.trans hgron)]

end FlightState

/-! ### The no-impact set is open, the impact time is lower semicontinuous -/

/-- The interior regular states of one edge: the base of the paper's tube charts. -/
def interiorRegular (e : Γ.Edge) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioo (0 : ℝ) (Γ.length e) ∧ V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies}

/-- The **no-impact set** of the edge `e` at time `Δ`: the interior regular states whose flight
survives past the time `Δ`.  This is the no-impact stratum of Lemma VI.2, before the restriction
to a compact energy window. -/
def noImpactSet (e : Γ.Edge) (Δ : ℝ) : Set (ℝ × ℝ) :=
  {x ∈ V.interiorRegular e | ∀ _ : BddAbove (durationSet V e x), Δ < sSup (durationSet V e x)}

/-- The mechanical energy is continuous at every state whose position lies in the extension
domain. -/
theorem continuousAt_hamiltonian_prod {e : Γ.Edge} {x : ℝ × ℝ} (hx : x.1 ∈ V.domain e) :
    ContinuousAt (fun y : ℝ × ℝ => V.hamiltonian e y.1 y.2) x := by
  have hV : ContinuousAt (V.extension e) x.1 := V.extension_continuousAt_of_mem hx
  have h1 : ContinuousAt (fun y : ℝ × ℝ => V.extension e y.1) x := hV.comp continuousAt_fst
  have h2 : ContinuousAt (fun y : ℝ × ℝ => y.2 ^ 2 / 2) x := by fun_prop
  exact h2.add h1

/-- Being an interior state of `e` with regular energy is an open condition: the interior is open
and the exceptional energies form a finite, hence closed, set. -/
theorem isOpen_interiorRegular (e : Γ.Edge) : IsOpen (V.interiorRegular e) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hx, hreg⟩
  have hdom : x.1 ∈ V.domain e := V.closedEdge_subset_domain e ⟨hx.1.le, hx.2.le⟩
  have hnhd1 : {y : ℝ × ℝ | y.1 ∈ Ioo (0 : ℝ) (Γ.length e)} ∈ 𝓝 x :=
    (isOpen_Ioo.preimage continuous_fst).mem_nhds hx
  have hexc : IsOpen ((↑V.exceptionalEnergies : Set ℝ)ᶜ) :=
    V.exceptionalEnergies.finite_toSet.isClosed.isOpen_compl
  have hxmem : V.hamiltonian e x.1 x.2 ∈ (↑V.exceptionalEnergies : Set ℝ)ᶜ := by
    simpa using hreg
  have hnhd2 : (fun y : ℝ × ℝ => V.hamiltonian e y.1 y.2) ⁻¹'
      ((↑V.exceptionalEnergies : Set ℝ)ᶜ) ∈ 𝓝 x :=
    (V.continuousAt_hamiltonian_prod hdom).preimage_mem_nhds (hexc.mem_nhds hxmem)
  refine Filter.mem_of_superset (Filter.inter_mem hnhd1 hnhd2) ?_
  rintro y ⟨hy1, hy2⟩
  exact ⟨hy1, by simpa using hy2⟩

/-- **Lemma VI.2, no-impact stratum.**  The no-impact set is *open* — in particular Borel, which
is all the paper needs.  This replaces the Lusin--Souslin argument by the continuation estimate
`FlightState.noImpact_persists`. -/
theorem isOpen_noImpactSet (e : Γ.Edge) {Δ : ℝ} (hΔ : 0 < Δ) :
    IsOpen (V.noImpactSet e Δ) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨⟨hx, hreg⟩, hsurv⟩
  obtain ⟨ρ, hρ, hρspec⟩ :=
    FlightState.noImpact_persists V (FlightState.ofInterior V hx hreg) hx hΔ hsurv
  refine Filter.mem_of_superset
    (Filter.inter_mem ((V.isOpen_interiorRegular e).mem_nhds ⟨hx, hreg⟩)
      (Metric.ball_mem_nhds x hρ)) ?_
  rintro y ⟨⟨hy, hyreg⟩, hyd⟩
  exact ⟨⟨hy, hyreg⟩, hρspec (FlightState.ofInterior V hy hyreg) rfl (Metric.mem_ball.mp hyd)⟩

theorem measurableSet_noImpactSet (e : Γ.Edge) {Δ : ℝ} (hΔ : 0 < Δ) :
    MeasurableSet (V.noImpactSet e Δ) :=
  (V.isOpen_noImpactSet e hΔ).measurableSet

/-- The **impact time** of an edge state: the supremum of the durations of the physical segments
issued from it, measured in `ℝ≥0∞` so that a flight which never reaches a vertex gets the value
`⊤`.  On the interior regular sector this is the paper's first-hit time `T(x)`. -/
noncomputable def impactTime (e : Γ.Edge) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ⨆ T : durationSet V e x, ENNReal.ofReal (T : ℝ)

theorem lt_impactTime_iff {e : Γ.Edge} {x : ℝ × ℝ} {y : ℝ≥0∞} :
    y < V.impactTime e x ↔ ∃ T : durationSet V e x, y < ENNReal.ofReal (T : ℝ) :=
  lt_iSup_iff

/-- On states with a physical segment, surviving past a positive time `Δ` in the sense used by the
flight machinery is the same as `Δ < T(x)` for the impact time. -/
theorem ofReal_lt_impactTime_iff {e : Γ.Edge} {x : ℝ × ℝ}
    (hne : (durationSet V e x).Nonempty) {Δ : ℝ} (hΔ : 0 < Δ) :
    ENNReal.ofReal Δ < V.impactTime e x ↔
      ∀ _ : BddAbove (durationSet V e x), Δ < sSup (durationSet V e x) := by
  rw [lt_impactTime_iff]
  constructor
  · rintro ⟨⟨T, hT⟩, hlt⟩ hbdd
    have hTΔ : Δ < T := by
      by_contra hcon
      exact absurd (ENNReal.ofReal_le_ofReal (not_lt.mp hcon)) (not_le.mpr hlt)
    exact lt_of_lt_of_le hTΔ (le_csSup hbdd hT)
  · intro h
    by_cases hbdd : BddAbove (durationSet V e x)
    · obtain ⟨T, hT, hTΔ⟩ := (lt_csSup_iff hbdd hne).mp (h hbdd)
      exact ⟨⟨T, hT⟩, by simpa using ENNReal.ofReal_lt_ofReal_iff_of_nonneg hΔ.le |>.mpr hTΔ⟩
    · obtain ⟨T, hT, hTΔ⟩ : ∃ T ∈ durationSet V e x, Δ < T := by
        rcases not_bddAbove_iff.mp hbdd Δ with ⟨T, hT, hTΔ⟩
        exact ⟨T, hT, hTΔ⟩
      exact ⟨⟨T, hT⟩, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hΔ.le).mpr hTΔ⟩

/-- **The impact time is lower semicontinuous on the interior regular sector.**  Its strict
superlevel sets are the no-impact sets, which are open.  Consequently `T` is Borel — this is the
measurability input that the paper obtains from the Lusin--Souslin theorem. -/
theorem isOpen_lt_impactTime (e : Γ.Edge) (y : ℝ≥0∞) :
    IsOpen {z : V.interiorRegular e | y < V.impactTime e (z : ℝ × ℝ)} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨Δ, hΔ0, hyΔ, hΔf⟩ := ENNReal.lt_iff_exists_real_btwn.mp hz
  have hΔpos : 0 < Δ := by
    rcases hΔ0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hyΔ; simp at hyΔ
  have hzne : (durationSet V e (z : ℝ × ℝ)).Nonempty :=
    PhysicalEdgeSegment.durationSet_nonempty
      (Classical.choose (V.exists_physicalEdgeSegment_from_interior z.2.1))
  have hzmem : (z : ℝ × ℝ) ∈ V.noImpactSet e Δ :=
    ⟨z.2, (V.ofReal_lt_impactTime_iff hzne hΔpos).mp hΔf⟩
  refine Filter.mem_of_superset
    (((V.isOpen_noImpactSet e hΔpos).preimage continuous_subtype_val).mem_nhds hzmem) ?_
  intro w hw
  have hwne : (durationSet V e (w : ℝ × ℝ)).Nonempty :=
    PhysicalEdgeSegment.durationSet_nonempty
      (Classical.choose (V.exists_physicalEdgeSegment_from_interior w.2.1))
  exact lt_trans hyΔ ((V.ofReal_lt_impactTime_iff hwne hΔpos).mpr hw.2)

theorem lowerSemicontinuous_impactTime (e : Γ.Edge) :
    LowerSemicontinuous fun z : V.interiorRegular e => V.impactTime e (z : ℝ × ℝ) := by
  intro z y hy
  exact (V.isOpen_lt_impactTime e y).mem_nhds hy

/-- **The impact time is Borel.**  This is the measurability of the paper's first-hit time on the
interior regular sector of one edge. -/
theorem measurable_impactTime (e : Γ.Edge) :
    Measurable fun z : V.interiorRegular e => V.impactTime e (z : ℝ × ℝ) :=
  measurable_of_Ioi fun y => (V.isOpen_lt_impactTime e y).measurableSet

/-! ### The no-impact half of Lemma VI.3 -/

/-- **From flights to a confined solution family.**  A family of flights based at the points of a
set `s` of one edge, all surviving past `Δ` and staying in a common physical momentum box, is an
`EdgeSolutionFamily` — the hypothesis of the Liouville theorem of Lemma V.1. -/
theorem edgeSolutionFamily_of_flights (e : Γ.Edge) {P Δ : ℝ} {s : Set (ℝ × ℝ)}
    (b : ℝ × ℝ → V.FlightState)
    (hbe : ∀ x ∈ s, (b x).edge = e) (hbs : ∀ x ∈ s, (b x).state = x)
    (hsurv : ∀ x ∈ s, ∀ _ : BddAbove (durationSet V (b x).edge (b x).state),
      Δ ≤ sSup (durationSet V (b x).edge (b x).state))
    (hbox : ∀ x ∈ s, ∀ t ∈ Icc (0 : ℝ) Δ,
      FlightState.flightCurve V (b x) t ∈ closedEdgeMomentumBox e P) :
    EdgeSolutionFamily V e P Δ s (fun x t => FlightState.flightCurve V (b x) t) := by
  refine ⟨fun x hx => ?_, fun x hx t ht => ?_, fun x hx t ht => hbox x hx t ht⟩
  · rw [FlightState.flightCurve_zero, hbs x hx]
  · have h := FlightState.flightCurve_hasDerivWithinAt_Icc (b x) (hsurv x hx) ht
    rw [hbe x hx] at h
    exact h

/-- **The no-impact half of Lemma VI.3.**  On a measurable set of initial conditions whose flights
survive past `Δ` and stay in a common physical momentum box, the time-`Δ` map of the edge flow
preserves `dq dp`.  This is `measure_image_edgeFlow` (Lemma V.1) with the hypotheses supplied by
the flight machinery; by `noImpact_persists` such sets are plentiful — every point of the
no-impact set has a whole ball of them. -/
theorem measure_image_flightCurve {e : Γ.Edge} {P Δ : ℝ} {s : Set (ℝ × ℝ)}
    (b : ℝ × ℝ → V.FlightState)
    (hbe : ∀ x ∈ s, (b x).edge = e) (hbs : ∀ x ∈ s, (b x).state = x)
    (hsurv : ∀ x ∈ s, ∀ _ : BddAbove (durationSet V (b x).edge (b x).state),
      Δ ≤ sSup (durationSet V (b x).edge (b x).state))
    (hbox : ∀ x ∈ s, ∀ t ∈ Icc (0 : ℝ) Δ,
      FlightState.flightCurve V (b x) t ∈ closedEdgeMomentumBox e P)
    (hs : MeasurableSet s) (hΔ : 0 < Δ) {M : ℝ≥0} (hM1 : (1 : ℝ) ≤ M)
    (hMbound : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), ‖V.edgeFieldDeriv e q‖ ≤ M)
    (hΔM : Δ ≤ 1 / (3 * M)) :
    volume ((fun x => FlightState.flightCurve V (b x) Δ) '' s) = volume s :=
  V.measure_image_edgeFlow (V.edgeSolutionFamily_of_flights e b hbe hbs hsurv hbox) hs hΔ hM1
    hMbound hΔM

end MechanicalPotential

end HamiltonianMetricGraphs
