/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.2: the no-impact condition along the outgoing-boundary family
-/

import HamiltonianMetricGraphs.EdgeFlightMap

/-!
# The no-impact condition along the outgoing-boundary family

`NoImpact.lean` proves that surviving past a fixed time is an open condition among *interior*
states of one edge.  The post-impact stratum of Lemma VI.2 needs the same statement for flights
that *depart a vertex*: there the initial point sits on the boundary of the edge, so the interior
margin of the reference flight degenerates at time `0` and the argument has to start slightly
later.

The extra ingredient is the uniform no-Zeno bound of Lemma V.2
(`exists_uniform_impactDuration_lower_bound`): on a compact regular energy window every outgoing
flight lasts at least `τ > 0`.  Hence a competing flight cannot land before `τ`, and on the
interval `[σ, Δ]` with `0 < σ < τ` the reference flight *does* have a positive interior margin
(`exists_interior_margin_of_pos`).  The Grönwall comparison of `EdgeFlightMap.lean` then rules out
a landing at any time in `[σ, Δ]`, exactly as in the interior case.

`noImpact_persists_outgoing` is the resulting openness statement.  `departureNoImpact_persists`
specialises it to the one-parameter family that actually occurs after an impact: for a fixed
departure germ `η`, the set of inward speeds `r` at a regular energy whose flight survives past
`Δ` is open.  Hence the departure impact time is lower semicontinuous, and in particular Borel, in
the speed.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter Metric MeasureTheory PhysicalEdgeSegment
open scoped Topology NNReal ENNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

namespace FlightState

/-! ### The interior margin away from the departure time -/

/-- **The interior margin of a surviving flight, away from time zero.**  A flight that survives
past `Δ` stays at a positive distance from both endpoints of its edge on every interval
`[σ, Δ]` with `σ > 0`.  Unlike `exists_interior_margin` this needs no assumption at time `0`, so
it applies to a flight departing a vertex. -/
theorem exists_interior_margin_of_pos (a : V.FlightState) {σ Δ : ℝ} (hσ : 0 < σ) (hσΔ : σ ≤ Δ)
    (hsurv : ∀ _ : BddAbove (durationSet V a.edge a.state),
      Δ < sSup (durationSet V a.edge a.state)) :
    ∃ ε > (0 : ℝ), ∀ t ∈ Icc σ Δ,
      ε ≤ (flightCurve V a t).1 ∧ ε ≤ Γ.length a.edge - (flightCurve V a t).1 := by
  classical
  have hsub : Icc σ Δ ⊆ Icc (0 : ℝ) Δ := Icc_subset_Icc hσ.le le_rfl
  have hinterior : ∀ t ∈ Icc σ Δ,
      (flightCurve V a t).1 ∈ Ioo (0 : ℝ) (Γ.length a.edge) := fun t ht =>
    flightCurve_interior V a (lt_of_lt_of_le hσ ht.1)
      (fun hbdd => lt_of_le_of_lt ht.2 (hsurv hbdd))
  set g : ℝ → ℝ := fun t =>
    min (flightCurve V a t).1 (Γ.length a.edge - (flightCurve V a t).1) with hg
  have hcont : ContinuousOn g (Icc σ Δ) := by
    have hq : ContinuousOn (fun t => (flightCurve V a t).1) (Icc σ Δ) := by
      intro t ht
      have h := flightCurve_hasDerivWithinAt_Icc a
        (fun hbdd => le_of_lt (hsurv hbdd)) (hsub ht)
      exact ((h.continuousWithinAt).mono hsub).fst
    have hr : ContinuousOn (fun t => Γ.length a.edge - (flightCurve V a t).1)
        (Icc σ Δ) := continuousOn_const.sub hq
    have h : ContinuousOn
        (fun t => (flightCurve V a t).1 ⊓ (Γ.length a.edge - (flightCurve V a t).1))
        (Icc σ Δ) := hq.inf hr
    rw [hg]
    exact h
  have hne : (Icc σ Δ).Nonempty := nonempty_Icc.mpr hσΔ
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  refine ⟨g t₀, ?_, fun t ht => ?_⟩
  · have h := hinterior t₀ ht₀
    rw [hg]
    exact lt_min h.1 (by linarith [h.2])
  · exact ⟨le_trans (hmin ht) (min_le_left _ _), le_trans (hmin ht) (min_le_right _ _)⟩

/-! ### Persistence of the no-impact condition for departing flights -/

/-- **The no-impact condition is open along the outgoing family.**  If the flight from `a`
survives past `Δ`, then so does every outgoing flight on the same edge, with energy in the same
compact regular window, whose initial state is close enough to `a`'s.

This is the post-impact half of Lemma VI.2.  The uniform no-Zeno bound `τ` of Lemma V.2 forbids a
competing landing before `τ`, and after `σ < τ` the reference flight has a positive interior
margin, which the Grönwall comparison forbids the competing flight to cross. -/
theorem noImpact_persists_outgoing [Nonempty Γ.Edge] (a : V.FlightState) {Δ : ℝ} (hΔ : 0 < Δ)
    {K : Set ℝ} (hKcompact : IsCompact K) (hKreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies)
    (haE : a.energy ∈ K)
    (hsurv : ∀ _ : BddAbove (durationSet V a.edge a.state),
      Δ < sSup (durationSet V a.edge a.state)) :
    ∃ ρ > (0 : ℝ), ∀ b : V.FlightState, b.edge = a.edge → b.IsOutgoing → b.energy ∈ K →
      dist b.state a.state < ρ →
      ∀ _ : BddAbove (durationSet V b.edge b.state),
        Δ < sSup (durationSet V b.edge b.state) := by
  classical
  obtain ⟨τ, hτ, hτbound⟩ :=
    exists_uniform_impactDuration_lower_bound (V := V) K hKcompact hKreg
  set σ : ℝ := min (τ / 2) (Δ / 2) with hσdef
  have hσ : 0 < σ := lt_min (by linarith) (by linarith)
  have hσΔ : σ ≤ Δ := le_trans (min_le_right _ _) (by linarith)
  have hστ : σ < τ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨ε, hε, hmargin⟩ := exists_interior_margin_of_pos V a hσ hσΔ hsurv
  obtain ⟨P, hP, hPbound⟩ := V.exists_compact_energy_speed_bound K hKcompact
  obtain ⟨L, hL⟩ := V.exists_lipschitzOnWith_edgeVectorField_closedMomentumBox a.edge P
  refine ⟨ε / Real.exp (L * Δ), by positivity, ?_⟩
  intro b hbe hbout hbE hbdist hbdd
  by_contra hcon
  rw [not_lt] at hcon
  set T : ℝ := sSup (durationSet V b.edge b.state) with hT
  have hτT : τ ≤ T := hτbound b hbout hbE hbdd
  have hσT : σ ≤ T := le_of_lt (lt_of_lt_of_le hστ hτT)
  have hT0 : 0 < T := lt_of_lt_of_le hσ hσT
  -- both flights last until `T` and stay in the physical momentum box of `K`
  have hdurb : ∀ _ : BddAbove (durationSet V b.edge b.state),
      T ≤ sSup (durationSet V b.edge b.state) := fun _ => by rw [← hT]
  have hdura : ∀ _ : BddAbove (durationSet V a.edge a.state),
      T ≤ sSup (durationSet V a.edge a.state) := fun hbdd' =>
    le_trans (le_trans hcon (le_of_lt (hsurv hbdd'))) le_rfl
  have hboxa : ∀ t ∈ Icc (0 : ℝ) T,
      flightCurve V a t ∈ closedEdgeMomentumBox a.edge P := fun t ht =>
    flightCurve_mem_closedEdgeMomentumBox V a hPbound haE ht.1
      (fun hbdd' => le_trans ht.2 (hdura hbdd'))
  have hboxb : ∀ t ∈ Icc (0 : ℝ) T,
      flightCurve V b t ∈ closedEdgeMomentumBox a.edge P := by
    intro t ht
    rw [← hbe]
    exact flightCurve_mem_closedEdgeMomentumBox V b hPbound hbE ht.1
      (fun hbdd' => le_trans ht.2 (hdurb hbdd'))
  have hgron := dist_flightCurve_le V a b hbe hL hdura hdurb hboxa hboxb T ⟨hT0.le, le_rfl⟩
  -- at the landing time the competing flight is on the boundary
  have hbend : (flightCurve V b T).1 = 0 ∨ (flightCurve V b T).1 = Γ.length a.edge := by
    rw [← hbe, hT, flightCurve_sSup b hbdd]
    exact b.segment.maximalEndpoint_coordinate_eq_zero_or_length hbdd
  have hmargT := hmargin T ⟨hσT, hcon⟩
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
  have hexp : Real.exp (L * T) ≤ Real.exp (L * Δ) :=
    Real.exp_le_exp.mpr (by
      have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
      nlinarith [hT0.le])
  have hsmall : dist b.state a.state * Real.exp (L * T) < ε := by
    have h2 : (0 : ℝ) < Real.exp (L * Δ) := Real.exp_pos _
    calc dist b.state a.state * Real.exp (L * T)
        ≤ dist b.state a.state * Real.exp (L * Δ) :=
          mul_le_mul_of_nonneg_left hexp dist_nonneg
      _ < (ε / Real.exp (L * Δ)) * Real.exp (L * Δ) := mul_lt_mul_of_pos_right hbdist h2
      _ = ε := by field_simp
  linarith [hqdist.trans (hdistq.trans hgron)]


end FlightState

/-! ### The departure family of a germ -/

/-- The phase point of a flight departing the germ `η` with inward speed `r`. -/
def departurePoint (η : Γ.EdgeEnd) (r : ℝ) : ℝ × ℝ :=
  (FiniteMetricGraph.EdgeEnd.coordinate Γ η, -(FiniteMetricGraph.EdgeEnd.sign Γ η * r))

/-- The energy of a flight departing the germ `η` with inward speed `r`. -/
noncomputable def departureEnergy (η : Γ.EdgeEnd) (r : ℝ) : ℝ :=
  V.hamiltonian η.1 (departurePoint η r).1 (departurePoint η r).2

theorem abs_edgeEnd_sign (η : Γ.EdgeEnd) : |FiniteMetricGraph.EdgeEnd.sign Γ η| = 1 := by
  rcases η with ⟨e, b⟩
  cases b <;> simp

theorem edgeEnd_sign_mul_self (η : Γ.EdgeEnd) :
    FiniteMetricGraph.EdgeEnd.sign Γ η * FiniteMetricGraph.EdgeEnd.sign Γ η = 1 := by
  have h := Γ.edgeEnd_sign_sq η
  nlinarith [h]

theorem departureEnergy_eq (η : Γ.EdgeEnd) (r : ℝ) :
    V.departureEnergy η r = r ^ 2 / 2 + V.vertexValue η.vertex := by
  rw [departureEnergy, departurePoint, V.endpoint_hamiltonian]
  have hsq := Γ.edgeEnd_sign_sq η
  have h : (-(FiniteMetricGraph.EdgeEnd.sign Γ η * r)) ^ 2 = r ^ 2 := by
    rw [neg_pow, mul_pow, hsq]
    ring
  rw [h]

theorem continuous_departureEnergy (η : Γ.EdgeEnd) : Continuous (V.departureEnergy η) := by
  have heq : V.departureEnergy η = fun r : ℝ => r ^ 2 / 2 + V.vertexValue η.vertex :=
    funext (V.departureEnergy_eq η)
  rw [heq]
  fun_prop

theorem dist_departurePoint (η : Γ.EdgeEnd) (r r' : ℝ) :
    dist (departurePoint η r') (departurePoint η r) = |r' - r| := by
  rw [Prod.dist_eq]
  have h1 : dist (departurePoint η r').1 (departurePoint η r).1 = 0 := by
    rw [departurePoint, departurePoint, dist_self]
  have h2 : dist (departurePoint η r').2 (departurePoint η r).2 = |r' - r| := by
    rw [departurePoint, departurePoint, Real.dist_eq]
    have hexp : -(FiniteMetricGraph.EdgeEnd.sign Γ η * r') -
        -(FiniteMetricGraph.EdgeEnd.sign Γ η * r) =
        FiniteMetricGraph.EdgeEnd.sign Γ η * (r - r') := by ring
    rw [hexp, abs_mul, abs_edgeEnd_sign, one_mul, abs_sub_comm]
  rw [h1, h2]
  exact max_eq_right (abs_nonneg _)

/-- The flight state departing the germ `η` with inward speed `r` at a regular energy. -/
noncomputable def ofDeparture (η : Γ.EdgeEnd) {r : ℝ} (hr : 0 < r)
    (hreg : V.departureEnergy η r ∉ V.exceptionalEnergies) : V.FlightState :=
  FlightState.ofOutgoingBoundary (V := V)
    (Γ.outgoingAtSpeed (v := η.vertex) ⟨η, rfl⟩ ⟨r, hr⟩) (by
      rw [V.boundaryEnergy_eq_edgeHamiltonian]
      simpa [departureEnergy, departurePoint] using hreg)

@[simp] theorem ofDeparture_edge (η : Γ.EdgeEnd) {r : ℝ} (hr : 0 < r)
    (hreg : V.departureEnergy η r ∉ V.exceptionalEnergies) :
    (V.ofDeparture η hr hreg).edge = η.1 := rfl

@[simp] theorem ofDeparture_state (η : Γ.EdgeEnd) {r : ℝ} (hr : 0 < r)
    (hreg : V.departureEnergy η r ∉ V.exceptionalEnergies) :
    (V.ofDeparture η hr hreg).state = departurePoint η r := rfl

@[simp] theorem ofDeparture_energy (η : Γ.EdgeEnd) {r : ℝ} (hr : 0 < r)
    (hreg : V.departureEnergy η r ∉ V.exceptionalEnergies) :
    (V.ofDeparture η hr hreg).energy = V.departureEnergy η r := rfl

theorem isOutgoing_ofDeparture (η : Γ.EdgeEnd) {r : ℝ} (hr : 0 < r)
    (hreg : V.departureEnergy η r ∉ V.exceptionalEnergies) :
    (V.ofDeparture η hr hreg).IsOutgoing := by
  refine ⟨η, rfl, rfl, ?_⟩
  rw [V.ofDeparture_state, departurePoint]
  have h : FiniteMetricGraph.EdgeEnd.sign Γ η * -(FiniteMetricGraph.EdgeEnd.sign Γ η * r)
      = -r := by
    have hs := edgeEnd_sign_mul_self η
    nlinarith [hs]
  rw [h]
  linarith

/-- A regular energy has a whole compact window of regular energies around it: the exceptional
energies form a finite set. -/
theorem exists_regular_window {E₀ : ℝ} (hreg : E₀ ∉ V.exceptionalEnergies) :
    ∃ d > (0 : ℝ), ∀ E ∈ Icc (E₀ - d) (E₀ + d), E ∉ V.exceptionalEnergies := by
  have hopen : IsOpen ((↑V.exceptionalEnergies : Set ℝ)ᶜ) :=
    V.exceptionalEnergies.finite_toSet.isClosed.isOpen_compl
  have hmem : E₀ ∈ (↑V.exceptionalEnergies : Set ℝ)ᶜ := by simpa using hreg
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen E₀ hmem
  refine ⟨ε / 2, by linarith, fun E hE => ?_⟩
  have hball : E ∈ Metric.ball E₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> [linarith [hE.1]; linarith [hE.2]]
  simpa using hsub hball

/-- **The no-impact condition is open in the departure speed.**  For a fixed departure germ at a
regular energy, every nearby inward speed also gives a flight surviving past `Δ`.  Hence the
departure impact time is lower semicontinuous, and in particular Borel, in the speed — the
post-impact counterpart of `isOpen_noImpactSet`. -/
theorem departureNoImpact_persists [Nonempty Γ.Edge] (η : Γ.EdgeEnd) {Δ : ℝ} (hΔ : 0 < Δ)
    {r : ℝ} (hr : 0 < r) (hreg : V.departureEnergy η r ∉ V.exceptionalEnergies)
    (hsurv : ∀ _ : BddAbove (durationSet V η.1 (departurePoint η r)),
      Δ < sSup (durationSet V η.1 (departurePoint η r))) :
    ∃ ρ > (0 : ℝ), ∀ r' : ℝ, 0 < r' → |r' - r| < ρ →
      ∀ _ : BddAbove (durationSet V η.1 (departurePoint η r')),
        Δ < sSup (durationSet V η.1 (departurePoint η r')) := by
  classical
  obtain ⟨d, hd, hdreg⟩ := V.exists_regular_window hreg
  have hasurv : ∀ _ : BddAbove (durationSet V (V.ofDeparture η hr hreg).edge
      (V.ofDeparture η hr hreg).state),
      Δ < sSup (durationSet V (V.ofDeparture η hr hreg).edge
        (V.ofDeparture η hr hreg).state) := hsurv
  have haE : (V.ofDeparture η hr hreg).energy ∈
      Icc (V.departureEnergy η r - d) (V.departureEnergy η r + d) := by
    rw [V.ofDeparture_energy, mem_Icc]
    constructor <;> linarith
  obtain ⟨ρ₀, hρ₀, hρ₀spec⟩ :=
    FlightState.noImpact_persists_outgoing V (V.ofDeparture η hr hreg) hΔ isCompact_Icc
      hdreg haE hasurv
  -- nearby speeds keep the energy in the window
  obtain ⟨ρ₁, hρ₁, hρ₁spec⟩ :=
    Metric.continuousAt_iff.mp ((V.continuous_departureEnergy η).continuousAt (x := r)) d hd
  have hKmem : ∀ r' : ℝ, |r' - r| < ρ₁ →
      V.departureEnergy η r' ∈ Icc (V.departureEnergy η r - d) (V.departureEnergy η r + d) := by
    intro r' hlt
    have h := hρ₁spec (by rw [Real.dist_eq]; exact hlt)
    rw [Real.dist_eq, abs_lt] at h
    rw [mem_Icc]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  refine ⟨min ρ₀ ρ₁, lt_min hρ₀ hρ₁, ?_⟩
  intro r' hr' hdist
  have hr'ρ₁ : |r' - r| < ρ₁ := lt_of_lt_of_le hdist (min_le_right _ _)
  have hreg' : V.departureEnergy η r' ∉ V.exceptionalEnergies := hdreg _ (hKmem r' hr'ρ₁)
  have hdd : dist (V.ofDeparture η hr' hreg').state (V.ofDeparture η hr hreg).state < ρ₀ := by
    rw [V.ofDeparture_state, V.ofDeparture_state, dist_departurePoint]
    exact lt_of_lt_of_le hdist (min_le_left _ _)
  exact hρ₀spec (V.ofDeparture η hr' hreg') rfl (V.isOutgoing_ofDeparture η hr' hreg')
    (by rw [V.ofDeparture_energy]; exact hKmem r' hr'ρ₁) hdd

end MechanicalPotential

end HamiltonianMetricGraphs
