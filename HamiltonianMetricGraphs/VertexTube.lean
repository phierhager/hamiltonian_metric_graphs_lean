/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3: the vertex tube of a regular energy window
-/

import HamiltonianMetricGraphs.TubeForm
import HamiltonianMetricGraphs.FlightShortTime
import HamiltonianMetricGraphs.DepartureFlight

/-!
# The vertex tube of a regular energy window

The exceptional energies of Definition IV.1 are *exactly* the vertex potential values
(`mem_exceptionalEnergies_iff`).  A compact regular energy window `K` therefore keeps a positive
distance from all of them, and since a flight departing a germ with inward speed `r` has energy
`r² / 2 + V(v)`, the departure speeds over `K` are bounded **away from zero** as well as above
(`exists_departure_speed_lower_bound`, `exists_compact_energy_speed_bound`).

This is what makes the tube coordinates of Lemma VI.1 usable at a vertex with *one* speed window:
the flight leaving a germ at a regular energy has speed in a fixed compact subinterval of
`(0, ∞)`, so the elementary estimates of `FlightShortTime.lean` give a *uniform* time `u₀` and
position window on which the flight is monotone — the flow box in which the impact step acts.

`timeAt_flow_neg` is the mirror of `timeAt_flow` for a leftward-moving solution, needed because a
germ at the *right* endpoint of an edge departs with negative momentum.

## The intended use (Lemma VI.3, one-impact piece)

With `r₁ ≤ r ≤ r₂` fixed by `exists_departure_speed_window`, set `C := max P F` (momentum bound and
force bound) and

`u₀ := min τ (min (r₁ / (2C)) (δ / (2C)))`,

where `τ` is the uniform no-Zeno bound of Lemma V.2 and `δ` is a radius on which the potential
varies by less than `d / 2` (with `d` from `exists_uniform_exceptional_distance`).  Then for
`u ∈ [0, u₀]` the departure flight of every germ keeps the sign of its momentum
(`FlightState.momentum_pos_of_short_time` / `momentum_neg_of_short_time`) and stays within `δ / 2`
of the vertex (`FlightState.abs_flightCurve_position_sub_le`), and `V < E` holds on
`Ioo (c - δ) (c + δ)` for every energy of the window; so `timeAt_flow`/`timeAt_flow_neg` give

`timeAt e E c (position at u) = -sign(η) · u`,

i.e. the flight *is* the energy--time chart of `lintegral_tube_chart_speed` (respectively
`lintegral_tube_chart_speed_neg`).  Transporting `(r dr) ⊗ du` through that chart gives the tube
measure at a germ; the *incoming* tube of a germ is the momentum reflection of its outgoing tube
(`measurePreserving_momentumReflection`), because the time reverse of a flight arriving at `η` with
speed `r` is the flight departing `η` with speed `r`.  Since scattering preserves the boundary
energy, it preserves the speed, so the incoming and outgoing tubes of an impact share one speed
window and `map_impactStep_flux_prod` identifies their measures.  Feeding the resulting countable
partition into `measure_preimage_flow_of_partition` closes Lemma VI.3.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set MeasureTheory PhysicalEdgeSegment
open scoped Topology

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- A compact regular energy window keeps a positive distance from the (finitely many) exceptional
energies. -/
theorem exists_uniform_exceptional_distance (K : Set ℝ) (hK : IsCompact K)
    (hKreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ d : ℝ, 0 < d ∧ ∀ E ∈ K, ∀ c ∈ V.exceptionalEnergies, d ≤ |E - c| := by
  classical
  rcases V.exceptionalEnergies.eq_empty_or_nonempty with hF | hF
  · exact ⟨1, one_pos, by simp [hF]⟩
  rcases eq_empty_or_nonempty K with hKe | hKne
  · exact ⟨1, one_pos, by simp [hKe]⟩
  refine ⟨V.exceptionalEnergies.inf' hF (fun c => Metric.infDist c K), ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro c hc
    refine (hK.isClosed.notMem_iff_infDist_pos hKne).mp (fun hcK => hKreg c hcK hc)
  · intro E hE c hc
    have h1 : V.exceptionalEnergies.inf' hF (fun c => Metric.infDist c K) ≤ Metric.infDist c K :=
      Finset.inf'_le _ hc
    have h2 : Metric.infDist c K ≤ dist c E := Metric.infDist_le_dist_of_mem hE
    rw [Real.dist_eq, abs_sub_comm] at h2
    linarith

/-- **On a regular energy window the departure speeds are bounded away from zero.**  The
exceptional energies are exactly the vertex potential values, so `E - V(v) ≥ d > 0` for every
energy `E` of the window; since `E = r² / 2 + V(v)` for a departure of speed `r`, this bounds `r`
below. -/
theorem exists_departure_speed_lower_bound (K : Set ℝ) (hK : IsCompact K)
    (hKreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ r₁ : ℝ, 0 < r₁ ∧
      ∀ (η : Γ.EdgeEnd) (r : ℝ), 0 < r → V.departureEnergy η r ∈ K → r₁ ≤ r := by
  obtain ⟨d, hd, hdist⟩ := V.exists_uniform_exceptional_distance K hK hKreg
  refine ⟨Real.sqrt (2 * d), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro η r hr hE
  have hc : V.vertexValue η.vertex ∈ V.exceptionalEnergies :=
    V.mem_exceptionalEnergies_iff.mpr ⟨η.vertex, rfl⟩
  have h := hdist _ hE _ hc
  rw [V.departureEnergy_eq η r] at h
  have habs : |r ^ 2 / 2 + V.vertexValue η.vertex - V.vertexValue η.vertex| = r ^ 2 / 2 := by
    rw [add_sub_cancel_right, abs_of_nonneg (by positivity)]
  rw [habs] at h
  have h3 : 2 * d ≤ r ^ 2 := by linarith
  calc Real.sqrt (2 * d) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt h3
    _ = r := by rw [Real.sqrt_sq hr.le]

/-- **The departure speeds of a regular energy window lie in a fixed compact subinterval of
`(0, ∞)`.**  Below by `exists_departure_speed_lower_bound`, above by the momentum bound of the
window. -/
theorem exists_departure_speed_window (K : Set ℝ) (hK : IsCompact K)
    (hKreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ ≤ r₂ ∧
      ∀ (η : Γ.EdgeEnd) (r : ℝ), 0 < r → V.departureEnergy η r ∈ K → r ∈ Icc r₁ r₂ := by
  obtain ⟨r₁, hr₁, hlow⟩ := V.exists_departure_speed_lower_bound K hK hKreg
  obtain ⟨P, hP, hPbound⟩ := V.exists_compact_energy_speed_bound K hK
  refine ⟨r₁, max r₁ P, hr₁, le_max_left _ _, ?_⟩
  intro η r hr hE
  refine ⟨hlow η r hr hE, ?_⟩
  -- the departure momentum has absolute value `r` and energy in `K`
  have hcoord : FiniteMetricGraph.EdgeEnd.coordinate Γ η ∈ Icc (0 : ℝ) (Γ.length η.1) :=
    Γ.edgeEnd_coordinate_mem_closedEdge η
  have hham : V.hamiltonian η.1 (departurePoint η r).1 (departurePoint η r).2 =
      V.departureEnergy η r := rfl
  have habs := hPbound η.1 (departurePoint η r).1 (departurePoint η r).2
    (V.departureEnergy η r) (by exact hcoord) hE hham
  have hval : |(departurePoint η r).2| = r := by
    rw [departurePoint]
    have h1 : |(-(FiniteMetricGraph.EdgeEnd.sign Γ η * r))| = r := by
      rw [abs_neg, abs_mul, abs_edgeEnd_sign η, one_mul, abs_of_pos hr]
    exact h1
  rw [hval] at habs
  exact le_trans habs (le_max_right _ _)

/-! ### The flow is a translation in the time coordinate, leftward version -/

/-- On an energy level a negative momentum is minus the speed. -/
theorem momentum_eq_neg_speedAt (e : Γ.Edge) {q p E : ℝ} (hp : p < 0)
    (hE : V.hamiltonian e q p = E) : p = -V.speedAt e E q := by
  rw [← hE, V.speedAt_hamiltonian e q p, abs_of_neg hp, neg_neg]

/-- **The edge flow is a translation in the time coordinate, for a leftward-moving solution.**  The
mirror of `timeAt_flow`: since `p = -p(E, q)` the derivative of `timeAt ∘ γ` is `-1`, so the travel
time from the initial position is minus the elapsed time. -/
theorem timeAt_flow_neg (e : Γ.Edge) {E D : ℝ} (hD : 0 < D) {γ : ℝ → ℝ × ℝ} {α β : ℝ}
    (hderiv : ∀ w ∈ Icc (0 : ℝ) D, HasDerivWithinAt γ (V.edgeVectorField e (γ w)) (Icc 0 D) w)
    (henergy : ∀ w ∈ Icc (0 : ℝ) D, V.hamiltonian e (γ w).1 (γ w).2 = E)
    (hmem : ∀ w ∈ Icc (0 : ℝ) D, (γ w).1 ∈ Ioo α β)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hpos : ∀ x ∈ Ioo α β, V.extension e x < E)
    (hmom : ∀ w ∈ Icc (0 : ℝ) D, (γ w).2 < 0) :
    ∀ w ∈ Icc (0 : ℝ) D, V.timeAt e E (γ 0).1 (γ w).1 = -w := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) D := ⟨le_rfl, hD.le⟩
  set q₀ : ℝ := (γ 0).1 with hq₀def
  have hq₀ : q₀ ∈ Ioo α β := hmem 0 h0
  set f : ℝ → ℝ := fun w => V.timeAt e E q₀ (γ w).1 + w with hf
  have hfderiv : ∀ w ∈ Icc (0 : ℝ) D, HasDerivWithinAt f 0 (Icc (0 : ℝ) D) w := by
    intro w hw
    have hq : HasDerivWithinAt (fun s => (γ s).1) ((γ w).2) (Icc (0 : ℝ) D) w :=
      V.edgeIntegralCurve_hasDerivWithinAt_fst (hderiv w hw)
    have ht : HasDerivAt (fun x => V.timeAt e E q₀ x) (1 / V.speedAt e E ((γ w).1)) ((γ w).1) :=
      V.hasDerivAt_timeAt e (hmem w hw) hq₀ hdom hpos
    have hcomp : HasDerivWithinAt ((fun x => V.timeAt e E q₀ x) ∘ fun s => (γ s).1)
        (1 / V.speedAt e E ((γ w).1) * (γ w).2) (Icc (0 : ℝ) D) w :=
      ht.comp_hasDerivWithinAt w hq
    have hspeed : 0 < V.speedAt e E ((γ w).1) := V.speedAt_pos e (hpos _ (hmem w hw))
    have hone : 1 / V.speedAt e E ((γ w).1) * (γ w).2 = -1 := by
      rw [V.momentum_eq_neg_speedAt e (hmom w hw) (henergy w hw), one_div,
        mul_neg, inv_mul_cancel₀ (ne_of_gt hspeed)]
    rw [hone] at hcomp
    have hid : HasDerivWithinAt (fun w : ℝ => w) 1 (Icc (0 : ℝ) D) w :=
      (hasDerivAt_id w).hasDerivWithinAt
    have h := hcomp.add hid
    rwa [show (-1 : ℝ) + 1 = 0 from by ring] at h
  have hdiff : DifferentiableOn ℝ f (Icc (0 : ℝ) D) :=
    fun w hw => (hfderiv w hw).differentiableWithinAt
  have hconst := constant_of_derivWithin_zero hdiff (fun w hw =>
    (hfderiv w (Ico_subset_Icc_self hw)).derivWithin
      (uniqueDiffOn_Icc hD w (Ico_subset_Icc_self hw)))
  intro w hw
  have hfw := hconst w hw
  have hf0 : f 0 = 0 := by
    rw [hf]
    simp only
    rw [timeAt, intervalIntegral.integral_same, add_zero]
  rw [hf0] at hfw
  have hres : V.timeAt e E q₀ (γ w).1 + w = 0 := hfw
  linarith

/-! ### The monotone flow box at a germ -/

/-- The speeds at which the germ `η` may be left with an energy of the window `K`. -/
def windowSpeeds (K : Set ℝ) (η : Γ.EdgeEnd) : Set ℝ :=
  V.regularSpeeds η ∩ V.departureEnergy η ⁻¹' K

theorem windowSpeeds_subset (K : Set ℝ) (η : Γ.EdgeEnd) :
    V.windowSpeeds K η ⊆ V.regularSpeeds η := fun _ hr => hr.1

theorem measurableSet_windowSpeeds {K : Set ℝ} (hK : MeasurableSet K) (η : Γ.EdgeEnd) :
    MeasurableSet (V.windowSpeeds K η) :=
  (V.isOpen_regularSpeeds η).measurableSet.inter
    ((V.continuous_departureEnergy η).measurable hK)

/-- **A monotone flow box at a germ.**  The geometric data that makes the tube coordinates of
Lemma VI.1 usable at the germ `η` with the *single* speed window `(r₁, r₂)`:

* the collar `Ioo (c - δ) (c + δ)` of the germ coordinate `c` lies in the extension domain, and the
  potential varies on it by less than `r₁² / 4`;
* every speed of `A` lies in `(r₁, r₂)`, is a regular departure speed, and its flight survives past
  the time `u₀`;
* on `[0, u₀]` that flight conserves the energy, stays within `δ / 2` of the germ, keeps the inward
  sign of its momentum, and its position inverts the time coordinate:
  `timeAt e E c (position at u) = -sign(η) · u`.

The last display is what identifies the flight with the energy--time chart of
`lintegral_tube_chart_speed`. -/
structure GermFlowBox (η : Γ.EdgeEnd) (A : Set ℝ) (r₁ r₂ δ u₀ : ℝ) : Prop where
  /-- The speed window is bounded away from zero. -/
  speed_pos : 0 < r₁
  /-- The speed window is an interval. -/
  speed_le : r₁ ≤ r₂
  /-- The collar has positive radius. -/
  radius_pos : 0 < δ
  /-- The flow box has positive duration. -/
  time_pos : 0 < u₀
  /-- The collar lies in the extension domain. -/
  domain : ∀ x ∈ Ioo (FiniteMetricGraph.EdgeEnd.coordinate Γ η - δ)
    (FiniteMetricGraph.EdgeEnd.coordinate Γ η + δ), x ∈ V.domain η.1
  /-- The potential is nearly constant on the collar. -/
  collar : ∀ x ∈ Ioo (FiniteMetricGraph.EdgeEnd.coordinate Γ η - δ)
    (FiniteMetricGraph.EdgeEnd.coordinate Γ η + δ),
    |V.extension η.1 x - V.vertexValue (FiniteMetricGraph.EdgeEnd.vertex Γ η)| < r₁ ^ 2 / 4
  /-- The speeds of `A` lie strictly inside the window. -/
  speeds : A ⊆ Ioo r₁ r₂
  /-- The speeds of `A` are regular departure speeds. -/
  regular : ∀ r ∈ A, r ∈ V.regularSpeeds η
  /-- The departure flight survives past `u₀`. -/
  duration : ∀ r ∈ A, ∀ _ : BddAbove (durationSet V η.1 (departurePoint η r)),
    u₀ ≤ sSup (durationSet V η.1 (departurePoint η r))
  /-- The departure flight conserves the energy on `[0, u₀]`. -/
  energy : ∀ r ∈ A, ∀ u ∈ Icc (0 : ℝ) u₀,
    V.hamiltonian η.1 (V.departureFlight η r u).1 (V.departureFlight η r u).2
      = V.departureEnergy η r
  /-- The departure flight stays within `δ / 2` of the germ on `[0, u₀]`. -/
  position : ∀ r ∈ A, ∀ u ∈ Icc (0 : ℝ) u₀,
    |(V.departureFlight η r u).1 - FiniteMetricGraph.EdgeEnd.coordinate Γ η| ≤ δ / 2
  /-- The departure flight keeps the inward sign of its momentum on `[0, u₀]`. -/
  momentum : ∀ r ∈ A, ∀ u ∈ Icc (0 : ℝ) u₀,
    0 < -(FiniteMetricGraph.EdgeEnd.sign Γ η) * (V.departureFlight η r u).2
  /-- The departure flight inverts the time coordinate on `[0, u₀]`. -/
  time : ∀ r ∈ A, ∀ u ∈ Icc (0 : ℝ) u₀,
    V.timeAt η.1 (V.departureEnergy η r) (FiniteMetricGraph.EdgeEnd.coordinate Γ η)
      (V.departureFlight η r u).1 = -(FiniteMetricGraph.EdgeEnd.sign Γ η) * u

namespace GermFlowBox

variable {V} {η : Γ.EdgeEnd} {A : Set ℝ} {r₁ r₂ δ u₀ : ℝ}

/-- A flow box on a larger speed set restricts to any subset. -/
theorem mono (h : V.GermFlowBox η A r₁ r₂ δ u₀) {B : Set ℝ} (hB : B ⊆ A) :
    V.GermFlowBox η B r₁ r₂ δ u₀ :=
  { speed_pos := h.speed_pos
    speed_le := h.speed_le
    radius_pos := h.radius_pos
    time_pos := h.time_pos
    domain := h.domain
    collar := h.collar
    speeds := le_trans hB h.speeds
    regular := fun r hr => h.regular r (hB hr)
    duration := fun r hr => h.duration r (hB hr)
    energy := fun r hr => h.energy r (hB hr)
    position := fun r hr => h.position r (hB hr)
    momentum := fun r hr => h.momentum r (hB hr)
    time := fun r hr => h.time r (hB hr) }

/-- Every energy above `r₁² / 2 + V(v)` is classically allowed on the collar. -/
theorem allowed (h : V.GermFlowBox η A r₁ r₂ δ u₀) {E : ℝ}
    (hE : r₁ ^ 2 / 2 + V.vertexValue (FiniteMetricGraph.EdgeEnd.vertex Γ η) ≤ E) :
    ∀ x ∈ Ioo (FiniteMetricGraph.EdgeEnd.coordinate Γ η - δ)
      (FiniteMetricGraph.EdgeEnd.coordinate Γ η + δ), V.extension η.1 x < E := by
  intro x hx
  have h1 := (abs_lt.mp (h.collar x hx)).2
  have hr₁ := h.speed_pos
  have h2 : (0 : ℝ) < r₁ ^ 2 / 4 := by positivity
  linarith

/-- The energy window of the speed window is classically allowed on the collar. -/
theorem allowed_window (h : V.GermFlowBox η A r₁ r₂ δ u₀) :
    ∀ E ∈ Ioo (r₁ ^ 2 / 2 + V.vertexValue (FiniteMetricGraph.EdgeEnd.vertex Γ η))
      (r₂ ^ 2 / 2 + V.vertexValue (FiniteMetricGraph.EdgeEnd.vertex Γ η)),
      ∀ x ∈ Ioo (FiniteMetricGraph.EdgeEnd.coordinate Γ η - δ)
        (FiniteMetricGraph.EdgeEnd.coordinate Γ η + δ), V.extension η.1 x < E :=
  fun _ hE => h.allowed hE.1.le

/-- The energy window of the speed window is contained in the energy range of the momentum strip
`(r₁ / 2, 2 r₂)` at every position of the collar. -/
theorem energy_subset (h : V.GermFlowBox η A r₁ r₂ δ u₀)
    {x : ℝ} (hx : x ∈ Ioo (FiniteMetricGraph.EdgeEnd.coordinate Γ η - δ)
      (FiniteMetricGraph.EdgeEnd.coordinate Γ η + δ)) :
    Ioo (r₁ ^ 2 / 2 + V.vertexValue (FiniteMetricGraph.EdgeEnd.vertex Γ η))
        (r₂ ^ 2 / 2 + V.vertexValue (FiniteMetricGraph.EdgeEnd.vertex Γ η)) ⊆
      Ioo (V.energyOfMomentum η.1 x (r₁ / 2)) (V.energyOfMomentum η.1 x (2 * r₂)) := by
  have hcol := abs_lt.mp (h.collar x hx)
  have hr₁ := h.speed_pos
  have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ h.speed_le
  have hsq : r₁ ^ 2 ≤ r₂ ^ 2 := by nlinarith [h.speed_le, hr₁]
  intro E hE
  constructor
  · have hlow : V.energyOfMomentum η.1 x (r₁ / 2) = (r₁ / 2) ^ 2 / 2 + V.extension η.1 x := rfl
    rw [hlow]
    nlinarith [hE.1, hcol.2]
  · have hhigh : V.energyOfMomentum η.1 x (2 * r₂) = (2 * r₂) ^ 2 / 2 + V.extension η.1 x := rfl
    rw [hhigh]
    nlinarith [hE.2, hcol.1]

end GermFlowBox

/-- **The monotone flow box at a vertex.**  On a compact regular energy window `K` there are a
speed window `(r₁, r₂) ⊆ (0, ∞)`, a collar radius `δ > 0` and a time `u₀ > 0` for which every germ
carries a `GermFlowBox` on the speeds that leave it with an energy of `K`.

The three ingredients are the uniform no-Zeno bound of Lemma V.2 (for `u₀ ≤ τ`), the mean value
estimates of `FlightShortTime.lean` (for the momentum sign and the position), and
`exists_departure_speed_window` (which makes `u₀ ≈ r₁ / 2C` positive, uniformly in the germ). -/
theorem exists_germFlowBox [Nonempty Γ.Edge] (K : Set ℝ) (hK : IsCompact K)
    (hKreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ r₁ r₂ δ u₀ : ℝ, (∀ e : Γ.Edge, δ < Γ.length e / 2) ∧
      ∀ η : Γ.EdgeEnd, V.GermFlowBox η (V.windowSpeeds K η) r₁ r₂ δ u₀ := by
  classical
  obtain ⟨ra, rb, hra, hrab, hspeedwin⟩ := V.exists_departure_speed_window K hK hKreg
  set r₁ : ℝ := ra / 2 with hr₁def
  set r₂ : ℝ := rb + 1 with hr₂def
  have hr₁ : 0 < r₁ := by positivity
  have hr₁₂ : r₁ ≤ r₂ := by rw [hr₁def, hr₂def]; linarith
  obtain ⟨ρ₁, hρ₁, hlen, hcollar⟩ :=
    V.exists_uniform_disjoint_endpoint_potential_collar (ε := r₁ ^ 2 / 4) (by positivity)
  obtain ⟨ρ₂, hρ₂, hdomcollar⟩ := V.exists_uniform_closedEdge_cthickening_subset_domain
  obtain ⟨P, hP, hPbound⟩ := V.exists_compact_energy_speed_bound K hK
  obtain ⟨F, hFbound⟩ := V.exists_uniform_absBound_force_closedEdges
  obtain ⟨τ, hτ, hsep⟩ :=
    FlightState.exists_uniform_impactDuration_lower_bound (V := V) K hK hKreg
  set δ : ℝ := min ρ₁ ρ₂ with hδdef
  have hδ : 0 < δ := lt_min hρ₁ hρ₂
  set C : ℝ := max (max P F) 1 with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hCP : P ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCF : F ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  set u₀ : ℝ := min τ (min (r₁ / (2 * C)) (δ / (2 * C))) with hu₀def
  have hu₀ : 0 < u₀ := lt_min hτ (lt_min (by positivity) (by positivity))
  -- the collar lies in the extension domain
  have hdom : ∀ η : Γ.EdgeEnd, ∀ x ∈ Ioo (FiniteMetricGraph.EdgeEnd.coordinate Γ η - δ)
      (FiniteMetricGraph.EdgeEnd.coordinate Γ η + δ), x ∈ V.domain η.1 := by
    intro η x hx
    refine hdomcollar η.1 ?_
    refine Metric.mem_cthickening_of_dist_le x (FiniteMetricGraph.EdgeEnd.coordinate Γ η) _ _
      (Γ.edgeEnd_coordinate_mem_closedEdge η) ?_
    rw [Real.dist_eq, abs_le]
    exact ⟨by linarith [hx.1, min_le_right ρ₁ ρ₂], by linarith [hx.2, min_le_right ρ₁ ρ₂]⟩
  -- the potential is nearly constant on the collar
  have hcol : ∀ η : Γ.EdgeEnd, ∀ x ∈ Ioo (FiniteMetricGraph.EdgeEnd.coordinate Γ η - δ)
      (FiniteMetricGraph.EdgeEnd.coordinate Γ η + δ),
      |V.extension η.1 x - V.vertexValue (FiniteMetricGraph.EdgeEnd.vertex Γ η)| < r₁ ^ 2 / 4 := by
    intro η x hx
    refine hcollar η x ?_
    rw [abs_lt]
    exact ⟨by linarith [hx.1, min_le_left ρ₁ ρ₂], by linarith [hx.2, min_le_left ρ₁ ρ₂]⟩
  refine ⟨r₁, r₂, δ, u₀, fun e => lt_of_le_of_lt (min_le_left ρ₁ ρ₂) (hlen e), fun η => ?_⟩
  have hpos : ∀ E : ℝ, r₁ ^ 2 / 2 + V.vertexValue (FiniteMetricGraph.EdgeEnd.vertex Γ η) ≤ E →
      ∀ x ∈ Ioo (FiniteMetricGraph.EdgeEnd.coordinate Γ η - δ)
        (FiniteMetricGraph.EdgeEnd.coordinate Γ η + δ), V.extension η.1 x < E := by
    intro E hE x hx
    have h := (abs_lt.mp (hcol η x hx)).2
    have hsq : (0 : ℝ) < r₁ ^ 2 / 4 := by positivity
    linarith
  -- everything below is proved for one fixed speed of the window
  have hmain : ∀ r ∈ V.windowSpeeds K η,
      (∀ _ : BddAbove (durationSet V η.1 (departurePoint η r)),
        u₀ ≤ sSup (durationSet V η.1 (departurePoint η r))) ∧
      r ∈ Ioo r₁ r₂ ∧
      ∀ u ∈ Icc (0 : ℝ) u₀,
        V.hamiltonian η.1 (V.departureFlight η r u).1 (V.departureFlight η r u).2
            = V.departureEnergy η r ∧
        |(V.departureFlight η r u).1 - FiniteMetricGraph.EdgeEnd.coordinate Γ η| ≤ δ / 2 ∧
        0 < -(FiniteMetricGraph.EdgeEnd.sign Γ η) * (V.departureFlight η r u).2 ∧
        V.timeAt η.1 (V.departureEnergy η r) (FiniteMetricGraph.EdgeEnd.coordinate Γ η)
          (V.departureFlight η r u).1
            = -(FiniteMetricGraph.EdgeEnd.sign Γ η) * u := by
    intro r hrw
    obtain ⟨hr, hE⟩ := hrw
    set a : V.FlightState := V.ofDeparture η hr.1 hr.2 with hadef
    have hae : a.edge = η.1 := rfl
    have has : a.state = departurePoint η r := rfl
    have haE : a.energy = V.departureEnergy η r := rfl
    have hwin : r ∈ Icc ra rb := hspeedwin η r hr.1 hE
    have hrwin : r ∈ Ioo r₁ r₂ := by
      refine ⟨?_, ?_⟩
      · rw [hr₁def]; linarith [hwin.1]
      · rw [hr₂def]; linarith [hwin.2]
    -- the flight lasts past `u₀`
    have hD : ∀ _ : BddAbove (durationSet V a.edge a.state),
        u₀ ≤ sSup (durationSet V a.edge a.state) := by
      intro hbdd
      exact le_trans (min_le_left _ _)
        (hsep a (V.isOutgoing_ofDeparture η hr.1 hr.2) (by rw [haE]; exact hE) hbdd)
    -- the flight stays in the momentum box, so the vector field is bounded by `C`
    have hmombound : ∀ u ∈ Icc (0 : ℝ) u₀, |(FlightState.flightCurve V a u).2| ≤ C := by
      intro u hu
      have h := FlightState.flightCurve_mem_closedEdgeMomentumBox V a hPbound
        (by rw [haE]; exact hE) hu.1 (fun hbdd => le_trans hu.2 (hD hbdd))
      have h2 := h.2
      rw [mem_Icc] at h2
      rw [abs_le]
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    have hforce : ∀ q ∈ Icc (0 : ℝ) (Γ.length a.edge), |V.force a.edge q| ≤ C :=
      fun q hq => le_trans (hFbound a.edge q hq) hCF
    -- position control
    have hposctl : ∀ u ∈ Icc (0 : ℝ) u₀,
        |(FlightState.flightCurve V a u).1 - a.state.1| ≤ δ / 2 := by
      intro u hu
      have h := FlightState.abs_flightCurve_position_sub_le V a hD hmombound hforce hu
      have hmax : max C C = C := max_self C
      rw [hmax] at h
      have hub : C * u ≤ δ / 2 := by
        have h1 : u ≤ δ / (2 * C) := le_trans hu.2 (le_trans (min_le_right _ _) (min_le_right _ _))
        calc C * u ≤ C * (δ / (2 * C)) := by
              exact mul_le_mul_of_nonneg_left h1 hCpos.le
          _ = δ / 2 := by field_simp
      exact le_trans h hub
    -- the momentum keeps its inward sign
    have hspeedlow : C * u₀ < r := by
      have h1 : u₀ ≤ r₁ / (2 * C) := le_trans (min_le_right _ _) (min_le_left _ _)
      have h2 : C * u₀ ≤ r₁ / 2 := by
        calc C * u₀ ≤ C * (r₁ / (2 * C)) := mul_le_mul_of_nonneg_left h1 hCpos.le
          _ = r₁ / 2 := by field_simp
      have h3 : r₁ < r := hrwin.1
      linarith
    have hsign : ∀ u ∈ Icc (0 : ℝ) u₀,
        0 < -(FiniteMetricGraph.EdgeEnd.sign Γ η) * (FlightState.flightCurve V a u).2 := by
      intro u hu
      have hlt : max C C * u < -(FiniteMetricGraph.EdgeEnd.sign Γ η) * a.state.2 := by
        rw [max_self, has, departurePoint]
        have hself := edgeEnd_sign_mul_self η
        have hval : -(FiniteMetricGraph.EdgeEnd.sign Γ η) *
            -(FiniteMetricGraph.EdgeEnd.sign Γ η * r) = r := by
          have hexp : -(FiniteMetricGraph.EdgeEnd.sign Γ η) *
              -(FiniteMetricGraph.EdgeEnd.sign Γ η * r)
              = (FiniteMetricGraph.EdgeEnd.sign Γ η *
                FiniteMetricGraph.EdgeEnd.sign Γ η) * r := by ring
          rw [hexp, hself, one_mul]
        rw [hval]
        calc C * u ≤ C * u₀ := mul_le_mul_of_nonneg_left hu.2 hCpos.le
          _ < r := hspeedlow
      rcases η with ⟨e, bo⟩
      cases bo
      · rw [Γ.edgeEnd_sign_false] at hlt ⊢
        have hpm : 0 < (FlightState.flightCurve V a u).2 := by
          refine FlightState.momentum_pos_of_short_time V a hD hmombound hforce hu ?_
          linarith [hlt]
        linarith
      · rw [Γ.edgeEnd_sign_true] at hlt ⊢
        have hpm : (FlightState.flightCurve V a u).2 < 0 := by
          refine FlightState.momentum_neg_of_short_time V a hD hmombound hforce hu ?_
          linarith [hlt]
        linarith
    -- the time coordinate
    have hmem : ∀ u ∈ Icc (0 : ℝ) u₀, (FlightState.flightCurve V a u).1 ∈
        Ioo (FiniteMetricGraph.EdgeEnd.coordinate Γ η - δ)
          (FiniteMetricGraph.EdgeEnd.coordinate Γ η + δ) := by
      intro u hu
      have h := hposctl u hu
      have hs1 : a.state.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ η := by
        rw [has, departurePoint]
      rw [hs1] at h
      have h2 := abs_le.mp h
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    have hEge : r₁ ^ 2 / 2 + V.vertexValue (FiniteMetricGraph.EdgeEnd.vertex Γ η) ≤
        V.departureEnergy η r := by
      rw [V.departureEnergy_eq η r]
      have h1 : r₁ ^ 2 ≤ r ^ 2 := by nlinarith [hrwin.1, hr₁]
      linarith
    have hderiv : ∀ w ∈ Icc (0 : ℝ) u₀, HasDerivWithinAt (FlightState.flightCurve V a)
        (V.edgeVectorField η.1 (FlightState.flightCurve V a w)) (Icc 0 u₀) w := by
      intro w hw
      have h := FlightState.flightCurve_hasDerivWithinAt_Icc a hD hw
      rwa [hae] at h
    have henergy : ∀ w ∈ Icc (0 : ℝ) u₀,
        V.hamiltonian η.1 (FlightState.flightCurve V a w).1 (FlightState.flightCurve V a w).2
          = V.departureEnergy η r := by
      intro w hw
      have h := FlightState.flightCurve_hamiltonian_eq V a hw.1
        (fun hbdd => le_trans hw.2 (hD hbdd))
      rwa [hae, haE] at h
    have hq0 : (FlightState.flightCurve V a 0).1 =
        FiniteMetricGraph.EdgeEnd.coordinate Γ η := by
      rw [FlightState.flightCurve_zero, has, departurePoint]
    have htime : ∀ u ∈ Icc (0 : ℝ) u₀,
        V.timeAt η.1 (V.departureEnergy η r) (FiniteMetricGraph.EdgeEnd.coordinate Γ η)
          (FlightState.flightCurve V a u).1
            = -(FiniteMetricGraph.EdgeEnd.sign Γ η) * u := by
      have hdom' := hdom η
      have hpos' := hpos (V.departureEnergy η r) hEge
      by_cases hbo : η.2 = true
      · have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η = 1 := by
          simp [FiniteMetricGraph.EdgeEnd.sign, hbo]
        have hmom : ∀ w ∈ Icc (0 : ℝ) u₀, (FlightState.flightCurve V a w).2 < 0 := by
          intro w hw
          have h := hsign w hw
          rw [hsgn] at h
          linarith
        have h := V.timeAt_flow_neg η.1 hu₀ hderiv henergy hmem hdom' hpos' hmom
        intro u hu
        have h2 := h u hu
        rw [hq0] at h2
        rw [h2, hsgn]
        ring
      · have hbo' : η.2 = false := by
          cases h : η.2 with
          | false => rfl
          | true => exact absurd h hbo
        have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η = -1 := by
          simp [FiniteMetricGraph.EdgeEnd.sign, hbo']
        have hmom : ∀ w ∈ Icc (0 : ℝ) u₀, 0 < (FlightState.flightCurve V a w).2 := by
          intro w hw
          have h := hsign w hw
          rw [hsgn] at h
          linarith
        have h := V.timeAt_flow η.1 hu₀ hderiv henergy hmem hdom' hpos' hmom
        intro u hu
        have h2 := h u hu
        rw [hq0] at h2
        rw [h2, hsgn]
        ring
    refine ⟨?_, hrwin, ?_⟩
    · intro hbdd
      have hbdd' : BddAbove (durationSet V a.edge a.state) := by
        rw [hae, has]; exact hbdd
      have h := hD hbdd'
      rwa [hae, has] at h
    · intro u hu
      rw [V.departureFlight_of_mem hr u]
      refine ⟨henergy u hu, ?_, hsign u hu, htime u hu⟩
      have h := hposctl u hu
      have hs1 : a.state.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ η := by
        rw [has, departurePoint]
      rwa [hs1] at h
  exact
    { speed_pos := hr₁
      speed_le := hr₁₂
      radius_pos := hδ
      time_pos := hu₀
      domain := hdom η
      collar := hcol η
      speeds := fun r hr => (hmain r hr).2.1
      regular := fun r hr => hr.1
      duration := fun r hr => (hmain r hr).1
      energy := fun r hr u hu => ((hmain r hr).2.2 u hu).1
      position := fun r hr u hu => ((hmain r hr).2.2 u hu).2.1
      momentum := fun r hr u hu => ((hmain r hr).2.2 u hu).2.2.1
      time := fun r hr u hu => ((hmain r hr).2.2 u hu).2.2.2 }

/-! ### Bounds for the travel time -/

/-- A speed lower bound on a position interval gives an upper bound for the travel time across
it. -/
theorem timeAt_le_of_speed_ge (e : Γ.Edge) {E α β : ℝ}
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hposE : ∀ x ∈ Ioo α β, V.extension e x < E)
    {q₀ q : ℝ} (hq₀ : q₀ ∈ Ioo α β) (hq : q ∈ Ioo α β) (hle : q₀ ≤ q)
    {m : ℝ} (hm : 0 < m) (hmb : ∀ x ∈ Icc q₀ q, m ≤ V.speedAt e E x) :
    V.timeAt e E q₀ q ≤ (q - q₀) / m := by
  have hint1 : IntervalIntegrable (fun x => 1 / V.speedAt e E x) MeasureTheory.volume q₀ q :=
    V.intervalIntegrable_one_div_speedAt e hdom hposE hq₀ hq
  have hint2 : IntervalIntegrable (fun _ : ℝ => 1 / m) MeasureTheory.volume q₀ q :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hle hint1 hint2
    (fun x hx => one_div_le_one_div_of_le hm (hmb x hx))
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one_div] at hmono
  exact hmono

/-- A speed upper bound on a position interval gives a lower bound for the travel time across
it. -/
theorem le_timeAt_of_speed_le (e : Γ.Edge) {E α β : ℝ}
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hposE : ∀ x ∈ Ioo α β, V.extension e x < E)
    {q₀ q : ℝ} (hq₀ : q₀ ∈ Ioo α β) (hq : q ∈ Ioo α β) (hle : q₀ ≤ q)
    {M : ℝ} (hsub : Icc q₀ q ⊆ Ioo α β)
    (hMb : ∀ x ∈ Icc q₀ q, V.speedAt e E x ≤ M) :
    (q - q₀) / M ≤ V.timeAt e E q₀ q := by
  have hint1 : IntervalIntegrable (fun x => 1 / V.speedAt e E x) MeasureTheory.volume q₀ q :=
    V.intervalIntegrable_one_div_speedAt e hdom hposE hq₀ hq
  have hint2 : IntervalIntegrable (fun _ : ℝ => 1 / M) MeasureTheory.volume q₀ q :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hle hint2 hint1
    (fun x hx => one_div_le_one_div_of_le (V.speedAt_pos e (hposE x (hsub hx))) (hMb x hx))
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one_div] at hmono
  exact hmono

/-- On a physical position the speed at an energy of a compact window is bounded by the momentum
bound of the window. -/
theorem speedAt_le_of_mem (e : Γ.Edge) {K : Set ℝ} {P : ℝ}
    (hPbound : ∀ (e : Γ.Edge) (q p E : ℝ), q ∈ Icc (0 : ℝ) (Γ.length e) → E ∈ K →
      V.hamiltonian e q p = E → |p| ≤ P)
    {E x : ℝ} (hE : E ∈ K) (hx : x ∈ Icc (0 : ℝ) (Γ.length e))
    (hle : V.extension e x ≤ E) : V.speedAt e E x ≤ P := by
  have hham : V.hamiltonian e x (V.speedAt e E x) = E := by
    have h := V.hamiltonian_speedAt e (ε := 1) (by norm_num) hle
    rwa [one_mul] at h
  have habs := hPbound e x (V.speedAt e E x) E hx hE hham
  exact le_trans (le_abs_self _) habs

end MechanicalPotential

end HamiltonianMetricGraphs
