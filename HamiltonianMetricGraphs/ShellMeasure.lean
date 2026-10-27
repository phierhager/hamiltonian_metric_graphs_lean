/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Theorem VIII.5 (c): the invariant time measure of a regular shell, orbit by orbit
-/

import HamiltonianMetricGraphs.ShellTravelTime

/-!
# The invariant time measure of a shell-regular energy surface

Proposition VII.1 defines the invariant measure `ν_E` of an energy surface as the pushforward of
the branch measures `dq / √(2(E - V_e(q)))` on `U_e(E) = {q ∈ (0, ℓ_e) : V_e(q) < E}` under the
maps `q ↦ π(e, q, ε √(2(E - V_e(q))))`, `ε = ±1`.  In the development the branch measure is
`edgeTimeMeasure e E` (`EnergySurface.lean`), the time density `timeDensity e E` on the closed edge,
which vanishes off `{V_e < E}`.

## The formal `ν_E`

We realise `ν_E` on the **edge phase spaces**, before the quotient by the vertex identifications:

`shellMeasure E e = (q ↦ (q, speedAt e E q))_* μ_E^e + (q ↦ (q, -speedAt e E q))_* μ_E^e`,

a measure on the phase plane `ℝ × ℝ` of the edge `e`; the measure of Proposition VII.1 is the
family `e ↦ shellMeasure E e`, and the `ν_E`-mass or integral of anything is the sum over the
finitely many edges.  This is faithful to the paper's definition: the quotient map is the identity
on interior edge points, and the only points of the edge phase spaces identified by the quotient
are boundary covectors, which the paper (and this measure) gives mass zero, as it gives mass zero
to the interior turning points (`volume_germZero`).  Working on the edge phase spaces avoids
transporting `ν_E` through the measurable structure of the quotient, and the orbits of the flow
are described there by their graph trajectories.

## Results

* `sum_lintegral_shellMeasure`, **the flight decomposition of `ν_E`**: for every Borel `F`,
  `∑_e ∫ F(e, ·) dν_E^e = ∑_{η ∈ G_E} ∫_0^{t_E(η)} F(γ_η(u)) du`, `γ_η` the flight departing `η`.
  In other words, `ν_E` is the pushforward of Lebesgue measure under the flights: the time
  coordinate along the flights is Lebesgue measure for `ν_E`.  The proof is the substitution
  `u ↦ q(u)` on each momentum sheet of each flight (`lintegral_germSheet`) together with the fact
  that, for each edge and each sign, the positions swept by the flights partition the allowed
  region `U_e(E)` (`allowedPositions_eq_biUnion`, `pairwiseDisjoint_sheetImage`), which in turn
  comes from the uniqueness of the flight through a point of the shell
  (`eq_of_flow_departureClass_eq`).
* `shellMass`, **(8.5)**: `ν_E(Σ_E) = ∑_{η ∈ G_E} t_E(η) = ∑_c T_c(E)`.
* `sum_setLIntegral_orbit` and `orbitMass`, **`ν_E` on the orbit of a cycle**: on the orbit of
  the cycle `c` of `η` (as a set of edge phase points, `cycleOrbit`), `ν_E` is the image of
  Lebesgue measure on `[0, T_c(E))` under the suspension chart `u ↦` (trajectory of `η` at time
  `u`), and its mass is `T_c(E)`.  The orbits of distinct cycles are disjoint
  (`disjoint_cycleOrbit`).
* `mem_cycleOrbit_iff_mem_shellOrbitPreimage`, `shellOrbitPreimage_ae_eq`: the edge-phase orbit
  `cycleOrbit` is the preimage `shellOrbitPreimage` of the quotient orbit `shellOrbit`, except at
  the incoming boundary states, which are `ν_E`-null (`shellMeasure_boundary`); hence
  `sum_setLIntegral_shellOrbitPreimage` and `shellOrbitMass` state the measure part of (c) for
  the quotient orbit itself.
* `ofReal_cyclePeriod_eq_sum`: (8.4) with the travel-time formula, `T_c(E)` as a sum of edge
  integrals of the time density over the flights of the cycle.
* `lintegral_timeDensity_edge_lt_top_of_shellRegular`: shell-regularity gives the hypothesis of
  Proposition VII.1 (no interior critical point on the level), so each edge carries finite mass.
* `regularShell_periodic`, `regularShell_decomposition`, `regularShell_measure`: Theorem VIII.5
  (b) and (c), packaged.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The measure -/

/-- The lift of a position of the edge `e` to the momentum sheet of sign `ε` of the level `E`. -/
noncomputable def sheetLift (e : Γ.Edge) (E ε : ℝ) (q : ℝ) : ℝ × ℝ := (q, ε * V.speedAt e E q)

/-- The branch of `ν_E` on the momentum sheet of sign `ε` of the edge `e`. -/
noncomputable def sheetMeasure (E : ℝ) (e : Γ.Edge) (ε : ℝ) : Measure (ℝ × ℝ) :=
  (V.edgeTimeMeasure e E).map (V.sheetLift e E ε)

/-- **The invariant time measure `ν_E` of Proposition VII.1 on the edge phase space of `e`**: the
time density `dq / √(2(E - V_e(q)))` pushed to both momentum sheets of the level `E`. -/
noncomputable def shellMeasure (E : ℝ) (e : Γ.Edge) : Measure (ℝ × ℝ) :=
  V.sheetMeasure E e 1 + V.sheetMeasure E e (-1)

theorem continuousOn_speedAt (e : Γ.Edge) (E : ℝ) :
    ContinuousOn (fun q => V.speedAt e E q) (Icc 0 (Γ.length e)) := fun _ hq =>
  (V.continuousAt_speedAt e (V.closedEdge_subset_domain e hq)).continuousWithinAt

theorem aemeasurable_sheetLift (e : Γ.Edge) (E ε : ℝ) :
    AEMeasurable (V.sheetLift e E ε) (V.edgeTimeMeasure e E) := by
  have h : ContinuousOn (V.sheetLift e E ε) (Icc 0 (Γ.length e)) :=
    continuousOn_id.prodMk ((V.continuousOn_speedAt e E).const_smul ε)
  exact (h.aemeasurable measurableSet_Icc).mono_ac (withDensity_absolutelyContinuous _ _)

theorem aemeasurable_timeDensity (e : Γ.Edge) (E : ℝ) :
    AEMeasurable (V.timeDensity e E) (volume.restrict (Icc 0 (Γ.length e))) := by
  have h : AEMeasurable (fun q => V.speedAt e E q) (volume.restrict (Icc 0 (Γ.length e))) :=
    (V.continuousOn_speedAt e E).aemeasurable measurableSet_Icc
  exact ENNReal.measurable_ofReal.comp_aemeasurable (h.const_div 1)

/-- Integration against a sheet of `ν_E` is integration against the time density. -/
theorem lintegral_sheetMeasure (e : Γ.Edge) (E ε : ℝ) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(V.sheetMeasure E e ε) =
      ∫⁻ q in Icc 0 (Γ.length e), V.timeDensity e E q * F (q, ε * V.speedAt e E q) := by
  rw [sheetMeasure, lintegral_map' hF.aemeasurable (V.aemeasurable_sheetLift e E ε)]
  have hg := hF.comp_aemeasurable (V.aemeasurable_sheetLift e E ε)
  unfold edgeTimeMeasure at hg ⊢
  exact lintegral_withDensity_eq_lintegral_mul₀' (V.aemeasurable_timeDensity e E) hg

/-! ### The allowed region -/

/-- The classically allowed positions `U_e(E) = {q ∈ (0, ℓ_e) : V_e(q) < E}` of
Proposition VII.1. -/
def allowedPositions (e : Γ.Edge) (E : ℝ) : Set ℝ :=
  {q | q ∈ Ioo 0 (Γ.length e) ∧ V.extension e q < E}

theorem isOpen_allowedPositions (e : Γ.Edge) (E : ℝ) : IsOpen (V.allowedPositions e E) := by
  have hcont : ContinuousOn (V.extension e) (Ioo 0 (Γ.length e)) := fun q hq =>
    (V.extension_continuousAt_of_mem
      (V.closedEdge_subset_domain e (Ioo_subset_Icc_self hq))).continuousWithinAt
  exact hcont.isOpen_inter_preimage isOpen_Ioo isOpen_Iio

theorem measurableSet_allowedPositions (e : Γ.Edge) (E : ℝ) :
    MeasurableSet (V.allowedPositions e E) :=
  (V.isOpen_allowedPositions e E).measurableSet

/-- The time density lives on the allowed region. -/
theorem setLIntegral_Icc_eq_allowedPositions (e : Γ.Edge) (E : ℝ) (G : ℝ → ℝ≥0∞) :
    ∫⁻ q in Icc 0 (Γ.length e), V.timeDensity e E q * G q =
      ∫⁻ q in V.allowedPositions e E, V.timeDensity e E q * G q := by
  rw [← setLIntegral_congr Ioo_ae_eq_Icc,
    ← lintegral_inter_add_sdiff _ (Ioo 0 (Γ.length e)) (V.measurableSet_allowedPositions e E)]
  have h1 : Ioo 0 (Γ.length e) ∩ V.allowedPositions e E = V.allowedPositions e E :=
    inter_eq_right.mpr fun q hq => hq.1
  have h2 : ∫⁻ q in Ioo 0 (Γ.length e) \ V.allowedPositions e E, V.timeDensity e E q * G q = 0 := by
    rw [setLIntegral_congr_fun (measurableSet_Ioo.diff (V.measurableSet_allowedPositions e E))
      (g := fun _ => 0) (fun q hq => ?_)]
    · simp
    · have hge : E ≤ V.extension e q := by
        by_contra hlt
        exact hq.2 ⟨hq.1, not_le.mp hlt⟩
      simp only
      rw [V.timeDensity_eq_zero_of_le e hge, zero_mul]
  rw [h1, h2, add_zero]

/-! ### The positions swept by the flights -/

section Sweep

variable {E : ℝ} (hE : V.ShellRegular E)

/-- The positions swept on the momentum sheet of sign `ε` by the flight departing `ζ`
(empty if `ζ` is not admissible). -/
noncomputable def sheetImage (ε : ℝ) (ζ : Γ.EdgeEnd) : Set ℝ := by
  classical
  exact if h : ζ ∈ V.allowedGerms E then
    (fun u => (V.germCurve hE h u).1) '' V.germSheet hE h ε else ∅

theorem sheetImage_of_mem (ε : ℝ) {ζ : Γ.EdgeEnd} (h : ζ ∈ V.allowedGerms E) :
    V.sheetImage hE ε ζ = (fun u => (V.germCurve hE h u).1) '' V.germSheet hE h ε := by
  classical
  unfold sheetImage
  rw [dif_pos h]

theorem measurableSet_sheetImage {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (ζ : Γ.EdgeEnd) :
    MeasurableSet (V.sheetImage hE ε ζ) := by
  classical
  by_cases h : ζ ∈ V.allowedGerms E
  · rw [V.sheetImage_of_mem hE ε h]
    exact (V.measurableSet_germSheet hE h ε).image_of_continuousOn_injOn
      ((V.germCurve_continuousOn_fst hE h).mono
        ((V.germSheet_subset hE h ε).trans Ioo_subset_Icc_self))
      (V.injOn_germSheet hE h hε)
  · unfold sheetImage
    rw [dif_neg h]
    exact MeasurableSet.empty

/-- The class of an interior edge point is not an incoming point. -/
theorem not_isIncomingPoint_graphPoint_of_interior (S : BorelEnergyPreservingScattering V)
    {y : Γ.Edge × ℝ × ℝ} (hy : y.2.1 ∈ Ioo 0 (Γ.length y.1)) :
    ¬ IsIncomingPoint (V := V) S (Γ.graphPoint y) := by
  rw [isIncomingPoint_graphPoint_iff V S ⟨Ioo_subset_Icc_self hy, Or.inl hy⟩]
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · rw [h] at hy; exact lt_irrefl _ hy.1
  · rw [h] at hy; exact lt_irrefl _ hy.2

/-- A trajectory point whose class is the class of a non-incoming graph point is that point. -/
theorem trajectory_eq_of_trajClass_val_eq (S : BorelEnergyPreservingScattering V)
    [Nonempty Γ.Edge] {a : V.FlightState} (ha : a.NotIncoming) {s : ℝ}
    {y : Γ.Edge × ℝ × ℝ} (hy : Γ.AdmissiblePoint y)
    (hyin : ¬ IsIncomingPoint (V := V) S (Γ.graphPoint y))
    (h : (V.trajClass S a s).1 = graphClass V S y) :
    FlightState.trajectory V S a s = y := by
  have hrep : rep V S (V.trajClass S a s).1 = Γ.graphPoint y := by
    rw [h, graphClass]
    exact rep_quotientMap_of_not_incoming V S _ hyin
  rw [V.rep_trajClass S ha] at hrep
  have h1 := Γ.graphPoint_edge (FlightState.trajectory_admissible S a s)
  have h2 := Γ.graphPoint_state (FlightState.trajectory_admissible S a s)
  rw [hrep] at h1 h2
  exact Prod.ext (h1.symm.trans (Γ.graphPoint_edge hy)) (h2.symm.trans (Γ.graphPoint_state hy))

/-- The departing trajectory at a time of the first flight, through the departure flight map. -/
theorem departureFlight_germSpeed {ζ : Γ.EdgeEnd} (hζ : ζ ∈ V.allowedGerms E) (u : ℝ) :
    V.departureFlight ζ (V.germSpeed ζ E) u = V.germCurve hE hζ u :=
  V.departureFlight_of_mem (V.germSpeed_mem_regularSpeeds hE hζ) u

/-- **Every allowed position is swept**, on each momentum sheet, by the flight of some admissible
end of its edge. -/
theorem exists_mem_sheetImage {e : Γ.Edge} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {x : ℝ}
    (hx : x ∈ V.allowedPositions e E) :
    ∃ ζ : Γ.EdgeEnd, ζ ∈ V.allowedGerms E ∧ ζ.1 = e ∧ x ∈ V.sheetImage hE ε ζ := by
  haveI : Nonempty Γ.Edge := ⟨e⟩
  set S := reflectionScattering V
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  set y : Γ.Edge × ℝ × ℝ := (e, x, ε * V.speedAt e E x) with hydef
  have hadm : Γ.AdmissiblePoint y := ⟨Ioo_subset_Icc_self hx.1, Or.inl hx.1⟩
  have hyin := V.not_isIncomingPoint_graphPoint_of_interior S (y := y) hx.1
  have hHy : V.hamiltonian e x (ε * V.speedAt e E x) = E := V.hamiltonian_speedAt e hε2 hx.2.le
  have hHq : quotientHamiltonian (V := V) S (graphClass V S y) = E := by
    rw [quotientHamiltonian_graphClass V S hadm]
    exact hHy
  set z : RegularScatteringPhaseSpace (V := V) S := ⟨graphClass V S y, by
    change quotientHamiltonian (V := V) S (graphClass V S y) ∉ V.exceptionalEnergies
    rw [hHq]
    exact hE.not_exceptional⟩ with hzdef
  have hz : z ∈ V.shell S E := hHq
  obtain ⟨ξ, hξ, w, hw, hzw⟩ := V.exists_departureClass_flow_lt S hE hz
  rw [V.flow_departureClass S hE ξ hξ hw.1] at hzw
  have htr := V.trajectory_eq_of_trajClass_val_eq S (V.germFlight_notIncoming hE ξ hξ) hadm hyin
    (congrArg Subtype.val hzw).symm
  rcases eq_or_lt_of_le hw.1 with hw0 | hwpos
  · exfalso
    rw [← hw0, FlightState.trajectory_zero] at htr
    have he : ξ.1 = e := congrArg Prod.fst htr
    have hc : FiniteMetricGraph.EdgeEnd.coordinate Γ ξ = x := congrArg (fun y => y.2.1) htr
    have hxint := hx.1
    rw [← he, ← hc] at hxint
    exact edgeEnd_coordinate_notMem_Ioo ξ hxint
  · have h1 := V.germTrajectory_of_lt S hE hξ hw.1 hw.2
    unfold germTrajectory at h1
    rw [h1] at htr
    have he : ξ.1 = e := congrArg Prod.fst htr
    have hγ : V.germCurve hE hξ w = (x, ε * V.speedAt e E x) := congrArg Prod.snd htr
    refine ⟨ξ, hξ, he, ?_⟩
    rw [V.sheetImage_of_mem hE ε hξ]
    refine ⟨w, ⟨⟨hwpos, hw.2⟩, ?_⟩, by simp only; rw [hγ]⟩
    rw [hγ]
    have hsp : 0 < V.speedAt e E x := V.speedAt_pos e hx.2
    simp only
    nlinarith

/-- **The flights of distinct ends sweep disjoint position sets** on each momentum sheet. -/
theorem disjoint_sheetImage {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {ζ ζ' : Γ.EdgeEnd} (he : ζ.1 = ζ'.1)
    (hne : ζ ≠ ζ') : Disjoint (V.sheetImage hE ε ζ) (V.sheetImage hE ε ζ') := by
  classical
  rw [Set.disjoint_left]
  intro x hx hx'
  by_cases hζ : ζ ∈ V.allowedGerms E
  swap
  · unfold sheetImage at hx; rw [dif_neg hζ] at hx; exact hx
  by_cases hζ' : ζ' ∈ V.allowedGerms E
  swap
  · unfold sheetImage at hx'; rw [dif_neg hζ'] at hx'; exact hx'
  haveI : Nonempty Γ.Edge := ⟨ζ.1⟩
  set S := reflectionScattering V
  rw [V.sheetImage_of_mem hE ε hζ] at hx
  rw [V.sheetImage_of_mem hE ε hζ'] at hx'
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨u', hu', hxx⟩ := hx'
  have h1 := V.germCurve_snd_of_mem_germSheet hE hζ hε hu
  have h2 := V.germCurve_snd_of_mem_germSheet hE hζ' hε hu'
  simp only at hxx
  have hγ : V.germCurve hE hζ' u' = V.germCurve hE hζ u := by
    refine Prod.ext hxx ?_
    rw [h1, h2, hxx, he]
  have ht1 := V.germTrajectory_of_lt S hE hζ hu.1.1.le hu.1.2
  have ht2 := V.germTrajectory_of_lt S hE hζ' hu'.1.1.le hu'.1.2
  unfold germTrajectory at ht1 ht2
  have hflow : flow V S (V.departureClass S hE ζ hζ) u =
      flow V S (V.departureClass S hE ζ' hζ') u' := by
    rw [V.flow_departureClass S hE ζ hζ hu.1.1.le, V.flow_departureClass S hE ζ' hζ' hu'.1.1.le]
    apply Subtype.ext
    rw [trajClass_val, trajClass_val, ht1, ht2, he]
    exact congrArg (fun p => graphClass V S (ζ'.1, p)) hγ.symm
  exact hne (V.eq_of_flow_departureClass_eq S hE hζ hζ' ⟨hu.1.1.le, hu.1.2⟩
    ⟨hu'.1.1.le, hu'.1.2⟩ hflow).1

/-- The ends of an edge admissible at energy `E`. -/
noncomputable def edgeAllowedFinset (e : Γ.Edge) : Finset Γ.EdgeEnd := by
  classical
  exact (V.allowedFinset E).filter fun ζ => ζ.1 = e

theorem mem_edgeAllowedFinset {e : Γ.Edge} {ζ : Γ.EdgeEnd} :
    ζ ∈ V.edgeAllowedFinset (E := E) e ↔ ζ ∈ V.allowedGerms E ∧ ζ.1 = e := by
  classical
  unfold edgeAllowedFinset
  rw [Finset.mem_filter, mem_allowedFinset]

/-- **The flights partition the allowed region**, on each momentum sheet. -/
theorem allowedPositions_eq_biUnion (e : Γ.Edge) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    V.allowedPositions e E = ⋃ ζ ∈ V.edgeAllowedFinset (E := E) e, V.sheetImage hE ε ζ := by
  ext x
  simp only [mem_iUnion, exists_prop]
  constructor
  · intro hx
    obtain ⟨ζ, hζ, he, hxζ⟩ := V.exists_mem_sheetImage hE hε hx
    exact ⟨ζ, (V.mem_edgeAllowedFinset).mpr ⟨hζ, he⟩, hxζ⟩
  · rintro ⟨ζ, hζmem, hxζ⟩
    obtain ⟨hζ, he⟩ := (V.mem_edgeAllowedFinset).mp hζmem
    rw [V.sheetImage_of_mem hE ε hζ] at hxζ
    obtain ⟨u, hu, rfl⟩ := hxζ
    have hp : (V.germCurve hE hζ u).2 ≠ 0 := by
      intro h0; have := hu.2; rw [h0, mul_zero] at this; exact lt_irrefl _ this
    subst he
    exact ⟨V.germCurve_interior hE hζ hu.1,
      V.extension_germCurve_lt hE hζ (Ioo_subset_Icc_self hu.1) hp⟩

theorem pairwiseDisjoint_sheetImage (e : Γ.Edge) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Set.PairwiseDisjoint (↑(V.edgeAllowedFinset (E := E) e)) (V.sheetImage hE ε) := by
  intro ζ hζ ζ' hζ' hne
  have h1 := ((V.mem_edgeAllowedFinset).mp hζ).2
  have h2 := ((V.mem_edgeAllowedFinset).mp hζ').2
  exact V.disjoint_sheetImage hE hε (h1.trans h2.symm) hne

end Sweep

/-! ### The flight decomposition of `ν_E` -/

/-- **`ν_E` is the pushforward of the flight times.**  For every Borel function `F` on the edge
phase spaces, the `ν_E`-integral of `F` is the sum, over the admissible ends `η`, of the time
integrals of `F` along the flight departing `η`:

`∑_e ∫ F(e, ·) dν_E = ∑_{η ∈ G_E} ∫_0^{t_E(η)} F(γ_η(u)) du`.

So the time coordinate of the flights is Lebesgue measure for `ν_E`. -/
theorem sum_lintegral_shellMeasure {E : ℝ} (hE : V.ShellRegular E)
    {F : Γ.Edge → ℝ × ℝ → ℝ≥0∞} (hF : ∀ e, Measurable (F e)) :
    ∑ e, ∫⁻ x, F e x ∂(V.shellMeasure E e) =
      ∑ η ∈ V.allowedFinset E,
        ∫⁻ u in Ioo 0 (V.flightTime E η), F η.1 (V.departureFlight η (V.germSpeed η E) u) := by
  set J : ℝ → Γ.EdgeEnd → ℝ≥0∞ := fun ε ζ => ∫⁻ x in V.sheetImage hE ε ζ,
    V.timeDensity ζ.1 E x * F ζ.1 (x, ε * V.speedAt ζ.1 E x) with hJ
  have hsheet : ∀ (e : Γ.Edge) (ε : ℝ), (ε = 1 ∨ ε = -1) →
      ∫⁻ x, F e x ∂(V.sheetMeasure E e ε) = ∑ ζ ∈ V.edgeAllowedFinset (E := E) e, J ε ζ := by
    intro e ε hε
    rw [V.lintegral_sheetMeasure e E ε (hF e), V.setLIntegral_Icc_eq_allowedPositions e E,
      V.allowedPositions_eq_biUnion hE e hε,
      lintegral_biUnion_finset (V.pairwiseDisjoint_sheetImage hE e hε)
        (fun ζ _ => V.measurableSet_sheetImage hE hε ζ)]
    refine Finset.sum_congr rfl (fun ζ hζ => ?_)
    obtain ⟨-, he⟩ := (V.mem_edgeAllowedFinset).mp hζ
    subst he
    rfl
  have hflight : ∀ η ∈ V.allowedFinset E,
      ∫⁻ u in Ioo 0 (V.flightTime E η), F η.1 (V.departureFlight η (V.germSpeed η E) u) =
        J 1 η + J (-1) η := by
    intro η hηmem
    have hη := (V.mem_allowedFinset).mp hηmem
    simp only [hJ]
    rw [V.sheetImage_of_mem hE 1 hη, V.sheetImage_of_mem hE (-1) hη]
    simp_rw [V.departureFlight_germSpeed hE hη]
    exact V.lintegral_germCurve hE hη (F η.1)
  rw [Finset.sum_congr rfl hflight]
  simp only [shellMeasure, lintegral_add_measure]
  rw [Finset.sum_congr rfl (fun e _ => by
    rw [hsheet e 1 (Or.inl rfl), hsheet e (-1) (Or.inr rfl), ← Finset.sum_add_distrib])]
  unfold edgeAllowedFinset
  exact Finset.sum_fiberwise (V.allowedFinset E) (fun ζ => ζ.1) (fun ζ => J 1 ζ + J (-1) ζ)

/-- **The total mass of `ν_E`, equation (8.5), first equality with the flight times.** -/
theorem sum_shellMeasure_univ {E : ℝ} (hE : V.ShellRegular E) :
    ∑ e, V.shellMeasure E e univ = ENNReal.ofReal (∑ η ∈ V.allowedFinset E, V.flightTime E η) := by
  have h := V.sum_lintegral_shellMeasure hE (F := fun _ _ => 1) (fun _ => measurable_const)
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ, Real.volume_Ioo,
    sub_zero] at h
  rw [h, ENNReal.ofReal_sum_of_nonneg (f := V.flightTime E)
    (fun η _ => V.departureDurationTotal_nonneg _ _)]

/-- **Equation (8.5).**  The mass of the shell for `ν_E` is the sum of the periods of the cycles of
`Π_E`, and the sum of the flight times of the admissible ends:
`ν_E(Σ_E) = ∑_{c} T_c(E) = ∑_{η ∈ G_E} t_E(η)`. -/
theorem shellMass {E : ℝ} (hE : V.ShellRegular E) (S : BorelEnergyPreservingScattering V) :
    ∑ e, V.shellMeasure E e univ =
        ENNReal.ofReal (∑ c ∈ V.germCycles S E, ∑ ζ ∈ c, V.flightTime E ζ) ∧
      ∑ c ∈ V.germCycles S E, ∑ ζ ∈ c, V.flightTime E ζ =
        ∑ η ∈ V.allowedFinset E, V.flightTime E η := by
  refine ⟨?_, V.sum_germCycles S hE⟩
  rw [V.sum_germCycles S hE]
  exact V.sum_shellMeasure_univ hE

/-! ### `ν_E` on the orbit of a cycle -/

/-- A Lebesgue integral over `[0, c_n)` split along the consecutive intervals `[c_k, c_{k+1})`. -/
theorem lintegral_Ico_eq_sum {c : ℕ → ℝ} (hc : Monotone c) (hc0 : c 0 = 0) (f : ℝ → ℝ≥0∞)
    (n : ℕ) :
    ∫⁻ u in Ico 0 (c n), f u = ∑ k ∈ Finset.range n, ∫⁻ u in Ico (c k) (c (k + 1)), f u := by
  induction n with
  | zero => simp [hc0]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih,
        ← Ico_union_Ico_eq_Ico (by rw [← hc0]; exact hc (Nat.zero_le n)) (hc (Nat.le_succ n)),
        lintegral_union measurableSet_Ico Ico_disjoint_Ico_same]

/-- Translation of a Lebesgue integral over an interval. -/
theorem lintegral_Ico_add (f : ℝ → ℝ≥0∞) (c d : ℝ) :
    ∫⁻ u in Ico c (c + d), f u = ∫⁻ w in Ico 0 d, f (c + w) := by
  rw [(measurePreserving_add_left volume c).setLIntegral_comp_emb
    (measurableEmbedding_addLeft c) f (Ico 0 d), image_const_add_Ico, add_zero]

section Orbit

variable (S : BorelEnergyPreservingScattering V) [Nonempty Γ.Edge]
variable {E : ℝ} (hE : V.ShellRegular E)

/-- **The orbit of the cycle of `η` on the edge phase space of `e`**: the points `x` such that
the trajectory departing `η` passes through `(e, x)` during one period `[0, T_c(E))`. -/
def cycleOrbit (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E) (e : Γ.Edge) : Set (ℝ × ℝ) :=
  {x | ∃ u ∈ Ico 0 (V.cyclePeriod S E η), V.germTrajectory S hE η hη u = (e, x)}

omit [Nonempty Γ.Edge] in
/-- The ends of the cycle of `η` are reached at the first `n` impact times, `n` the cycle length. -/
theorem exists_lt_of_mem_germCycle {η ζ : Γ.EdgeEnd} (h : ζ ∈ V.germCycle S E η) :
    ∃ k < Function.minimalPeriod (V.germStep S E) η, (V.germStep S E)^[k] η = ζ := by
  unfold germCycle at h
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
  exact ⟨k, Finset.mem_range.mp hk, rfl⟩

/-- The orbit of a cycle is the union of the first flights of the ends of the cycle. -/
theorem mem_cycleOrbit_iff {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) (e : Γ.Edge)
    (x : ℝ × ℝ) :
    x ∈ V.cycleOrbit S hE η hη e ↔ ∃ ζ ∈ V.germCycle S E η, ∃ hζ : ζ ∈ V.allowedGerms E,
      ζ.1 = e ∧ ∃ w ∈ Ico 0 (V.flightTime E ζ), V.germCurve hE hζ w = x := by
  constructor
  · rintro ⟨u, hu, hux⟩
    obtain ⟨k, -, hk1, hk2⟩ := V.exists_chainTime_le_lt S hE hη hu.1 hu.2
    set ξ := (V.germStep S E)^[k] η with hξdef
    have hξ : ξ ∈ V.allowedGerms E := V.germStep_iterate_mem S hE hη k
    set w := u - chainTime V S (η, V.germSpeed η E) k with hw
    have hw0 : 0 ≤ w := by rw [hw]; linarith
    have hwlt : w < V.flightTime E ξ := by
      rw [V.chainTime_succ_germSpeed S hE hη k] at hk2
      rw [hw]; linarith
    have h1 := V.germTrajectory_chainTime_add S hE hη k hw0
    rw [hw, add_sub_cancel, hux, V.germTrajectory_of_lt S hE hξ hw0 hwlt] at h1
    refine ⟨ξ, (V.mem_germCycle_iff S hE hη).mpr ⟨k, rfl⟩, hξ, (congrArg Prod.fst h1).symm,
      w, ⟨hw0, hwlt⟩, (congrArg Prod.snd h1).symm⟩
  · rintro ⟨ζ, hζc, hζ, he, w, hw, rfl⟩
    obtain ⟨k, hkn, rfl⟩ := V.exists_lt_of_mem_germCycle S hζc
    refine ⟨chainTime V S (η, V.germSpeed η E) k + w, ⟨?_, ?_⟩, ?_⟩
    · linarith [V.chainTime_nonneg S (η, V.germSpeed η E) k, hw.1]
    · have h1 := V.chainTime_succ_germSpeed S hE hη k
      have h2 : chainTime V S (η, V.germSpeed η E) (k + 1) ≤
          chainTime V S (η, V.germSpeed η E) (Function.minimalPeriod (V.germStep S E) η) :=
        (V.chainTime_germSpeed_strictMono S hE hη).monotone hkn
      rw [V.cyclePeriod_eq_chainTime S hE hη]
      linarith [hw.2]
    · rw [V.germTrajectory_chainTime_add S hE hη k hw.1, V.germTrajectory_of_lt S hE hζ hw.1 hw.2,
        he]
      rfl

theorem measurableSet_cycleOrbit {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) (e : Γ.Edge) :
    MeasurableSet (V.cycleOrbit S hE η hη e) := by
  classical
  have heq : V.cycleOrbit S hE η hη e = ⋃ ζ ∈ V.germCycle S E η,
      if hζ : ζ ∈ V.allowedGerms E ∧ ζ.1 = e then
        V.germCurve hE hζ.1 '' Ico 0 (V.flightTime E ζ) else ∅ := by
    ext x
    rw [V.mem_cycleOrbit_iff S hE hη e x]
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨ζ, hζc, hζ, he, w, hw, rfl⟩
      refine ⟨ζ, hζc, ?_⟩
      rw [dif_pos ⟨hζ, he⟩]
      exact ⟨w, hw, rfl⟩
    · rintro ⟨ζ, hζc, hx⟩
      by_cases h : ζ ∈ V.allowedGerms E ∧ ζ.1 = e
      · rw [dif_pos h] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        exact ⟨ζ, hζc, h.1, h.2, w, hw, rfl⟩
      · rw [dif_neg h] at hx
        exact absurd hx (notMem_empty x)
  rw [heq]
  refine Finset.measurableSet_biUnion _ (fun ζ _ => ?_)
  split_ifs with h
  · exact measurableSet_Ico.image_of_continuousOn_injOn
      ((V.germCurve_continuousOn hE h.1).mono Ico_subset_Icc_self) (V.germCurve_injOn hE h.1)
  · exact MeasurableSet.empty

/-- A point of the first flight of `ζ` lies on the orbit of the cycle of `η` exactly when `ζ` is
in that cycle. -/
theorem germCurve_mem_cycleOrbit_iff {η ζ : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E)
    (hζ : ζ ∈ V.allowedGerms E) {u : ℝ} (hu : u ∈ Ico 0 (V.flightTime E ζ)) :
    V.germCurve hE hζ u ∈ V.cycleOrbit S hE η hη ζ.1 ↔ ζ ∈ V.germCycle S E η := by
  rw [V.mem_cycleOrbit_iff S hE hη]
  constructor
  · rintro ⟨ξ, hξc, hξ, he, w, hw, hwx⟩
    have h1 := V.germTrajectory_of_lt S hE hξ hw.1 hw.2
    have h2 := V.germTrajectory_of_lt S hE hζ hu.1 hu.2
    unfold germTrajectory at h1 h2
    have hflow : flow V S (V.departureClass S hE ξ hξ) w =
        flow V S (V.departureClass S hE ζ hζ) u := by
      rw [V.flow_departureClass S hE ξ hξ hw.1, V.flow_departureClass S hE ζ hζ hu.1]
      apply Subtype.ext
      rw [trajClass_val, trajClass_val, h1, h2, he]
      exact congrArg (fun p => graphClass V S (ζ.1, p)) hwx
    obtain ⟨rfl, -⟩ := V.eq_of_flow_departureClass_eq S hE hξ hζ hw hu hflow
    exact hξc
  · intro hc
    exact ⟨ζ, hc, hζ, rfl, u, hu, rfl⟩

/-- **Theorem VIII.5 (c): `ν_E` is Lebesgue measure in the time coordinate of each orbit.**  On the
orbit of the cycle of `η`, integrating a Borel function against `ν_E` is integrating it in time
along one period of the trajectory departing `η`:

`∑_e ∫_{orbit} F(e, ·) dν_E = ∫_0^{T_c(E)} F(trajectory of η at time u) du`. -/
theorem sum_setLIntegral_cycleOrbit {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E)
    {F : Γ.Edge → ℝ × ℝ → ℝ≥0∞} (hF : ∀ e, Measurable (F e)) :
    ∑ e, ∫⁻ x in V.cycleOrbit S hE η hη e, F e x ∂(V.shellMeasure E e) =
      ∫⁻ u in Ico 0 (V.cyclePeriod S E η),
        F (V.germTrajectory S hE η hη u).1 (V.germTrajectory S hE η hη u).2 := by
  classical
  set G : Γ.EdgeEnd → ℝ≥0∞ := fun ζ =>
    ∫⁻ u in Ioo 0 (V.flightTime E ζ), F ζ.1 (V.departureFlight ζ (V.germSpeed ζ E) u) with hG
  -- the left side, through the flight decomposition of `ν_E`
  have hL : ∑ e, ∫⁻ x in V.cycleOrbit S hE η hη e, F e x ∂(V.shellMeasure E e) =
      ∑ ζ ∈ V.germCycle S E η, G ζ := by
    simp_rw [← lintegral_indicator (V.measurableSet_cycleOrbit S hE hη _)]
    rw [V.sum_lintegral_shellMeasure hE
      (fun e => (hF e).indicator (V.measurableSet_cycleOrbit S hE hη e))]
    have hsub : V.germCycle S E η ⊆ V.allowedFinset E := fun ζ hζ =>
      (V.mem_allowedFinset).mpr (V.germCycle_subset S hE hη hζ)
    rw [← Finset.sum_subset hsub (fun ζ hζa hζc => ?_)]
    · refine Finset.sum_congr rfl (fun ζ hζc => ?_)
      have hζ := V.germCycle_subset S hE hη hζc
      refine setLIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
      rw [V.departureFlight_germSpeed hE hζ, indicator_of_mem
        ((V.germCurve_mem_cycleOrbit_iff S hE hη hζ (Ioo_subset_Ico_self hu)).mpr hζc)]
    · have hζ := (V.mem_allowedFinset).mp hζa
      rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => 0) (fun u hu => ?_)]
      · simp
      · simp only
        rw [V.departureFlight_germSpeed hE hζ, indicator_of_notMem]
        exact fun hmem => hζc
          ((V.germCurve_mem_cycleOrbit_iff S hE hη hζ (Ioo_subset_Ico_self hu)).mp hmem)
  -- the right side, through the impact times of one period
  have hR : ∫⁻ u in Ico 0 (V.cyclePeriod S E η),
      F (V.germTrajectory S hE η hη u).1 (V.germTrajectory S hE η hη u).2 =
        ∑ ζ ∈ V.germCycle S E η, G ζ := by
    rw [V.cyclePeriod_eq_chainTime S hE hη,
      lintegral_Ico_eq_sum (V.chainTime_germSpeed_strictMono S hE hη).monotone
        (chainTime_zero _ _ _)]
    have hpiece : ∀ k : ℕ, ∫⁻ u in Ico (chainTime V S (η, V.germSpeed η E) k)
        (chainTime V S (η, V.germSpeed η E) (k + 1)),
          F (V.germTrajectory S hE η hη u).1 (V.germTrajectory S hE η hη u).2 =
        G ((V.germStep S E)^[k] η) := by
      intro k
      have hξ := V.germStep_iterate_mem S hE hη k
      rw [V.chainTime_succ_germSpeed S hE hη k, lintegral_Ico_add,
        ← setLIntegral_congr Ioo_ae_eq_Ico]
      refine setLIntegral_congr_fun measurableSet_Ioo (fun w hw => ?_)
      rw [V.germTrajectory_chainTime_add S hE hη k hw.1.le,
        V.germTrajectory_of_lt S hE hξ hw.1.le hw.2, V.departureFlight_germSpeed hE hξ]
      rfl
    rw [Finset.sum_congr rfl (fun k _ => hpiece k)]
    unfold germCycle
    rw [Finset.sum_image]
    intro i hi j hj hij
    exact Function.iterate_injOn_Iio_minimalPeriod (Finset.mem_range.mp hi)
      (Finset.mem_range.mp hj) hij
  rw [hL, hR]

/-- **Theorem VIII.5 (c): the `ν_E`-mass of an orbit is its period** `T_c(E)`. -/
theorem orbitMass {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) :
    ∑ e, V.shellMeasure E e (V.cycleOrbit S hE η hη e) = ENNReal.ofReal (V.cyclePeriod S E η) := by
  have h := V.sum_setLIntegral_cycleOrbit S hE hη (F := fun _ _ => 1) (fun _ => measurable_const)
  simp only [setLIntegral_one, Real.volume_Ico, sub_zero] at h
  exact h

/-- The orbits of distinct cycles are disjoint on every edge phase space. -/
theorem disjoint_cycleOrbit {η ζ : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E)
    (hζ : ζ ∈ V.allowedGerms E) (h : ζ ∉ V.germCycle S E η) (e : Γ.Edge) :
    Disjoint (V.cycleOrbit S hE η hη e) (V.cycleOrbit S hE ζ hζ e) := by
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, hux⟩ ⟨u', hu', hux'⟩
  unfold germTrajectory at hux hux'
  have hflow : flow V S (V.departureClass S hE ζ hζ) u' =
      flow V S (V.departureClass S hE η hη) u := by
    rw [V.flow_departureClass S hE η hη hu.1, V.flow_departureClass S hE ζ hζ hu'.1]
    apply Subtype.ext
    rw [trajClass_val, trajClass_val, hux, hux']
  exact Set.disjoint_left.mp (V.disjoint_shellOrbit S hE hη hζ h) ⟨u, rfl⟩ ⟨u', hflow⟩

end Orbit

/-! ### The orbit of a cycle as a quotient orbit -/

/-- **The boundary states are `ν_E`-null**: `ν_E` gives no mass to the edge-phase points over the
two ends of an edge. -/
theorem shellMeasure_boundary (E : ℝ) (e : Γ.Edge) :
    V.shellMeasure E e {x | x.1 = 0 ∨ x.1 = Γ.length e} = 0 := by
  have hmeas : MeasurableSet {x : ℝ × ℝ | x.1 = 0 ∨ x.1 = Γ.length e} :=
    ((measurableSet_singleton 0).preimage measurable_fst).union
      ((measurableSet_singleton _).preimage measurable_fst)
  have hvol : volume {q : ℝ | q = 0 ∨ q = Γ.length e} = 0 := by
    rw [Set.setOf_or]
    exact ((Set.countable_singleton 0).union (Set.countable_singleton _)).measure_zero _
  have hsheet : ∀ ε : ℝ, V.sheetMeasure E e ε {x | x.1 = 0 ∨ x.1 = Γ.length e} = 0 := by
    intro ε
    rw [sheetMeasure, Measure.map_apply_of_aemeasurable (V.aemeasurable_sheetLift e E ε) hmeas]
    unfold edgeTimeMeasure
    refine withDensity_absolutelyContinuous _ _ ?_
    exact nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans (le_of_eq hvol))
  rw [shellMeasure, Measure.add_apply, hsheet, hsheet, add_zero]

/-- On a shell-regular level every point of the closed edge is admissible: a boundary state of
energy `E` has nonzero momentum since `E` is not a vertex value. -/
theorem admissiblePoint_of_hamiltonian {E : ℝ} (hE : V.ShellRegular E) {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x.1 ∈ Icc 0 (Γ.length e)) (hxE : V.hamiltonian e x.1 x.2 = E) :
    Γ.AdmissiblePoint (e, x) := by
  refine ⟨hx, ?_⟩
  by_cases hint : x.1 ∈ Ioo 0 (Γ.length e)
  · exact Or.inl hint
  right
  intro hp
  apply hE.not_exceptional
  rw [V.mem_exceptionalEnergies_iff]
  have hend : ∃ b : Bool, x.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ (e, b) := by
    rcases eq_or_lt_of_le hx.1 with h | h
    · exact ⟨false, h.symm⟩
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · exact ⟨true, h'⟩
    · exact absurd ⟨h, h'⟩ hint
  obtain ⟨b, hb⟩ := hend
  refine ⟨FiniteMetricGraph.EdgeEnd.vertex Γ (e, b), ?_⟩
  have hp' : x.2 = 0 := hp
  rw [← V.endpoint_value (e, b), ← hb, ← hxE]
  simp [hamiltonian, hp']

section QuotientOrbit

variable (S : BorelEnergyPreservingScattering V) [Nonempty Γ.Edge]
variable {E : ℝ} (hE : V.ShellRegular E)

/-- **The preimage of the quotient orbit** of the departure state of `η` in the edge phase space
of `e`: the points of the closed edge at energy `E` whose class lies on the orbit `shellOrbit` of
the global flow. -/
def shellOrbitPreimage (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E) (e : Γ.Edge) :
    Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc 0 (Γ.length e) ∧ V.hamiltonian e x.1 x.2 = E ∧
    graphClass V S (e, x) ∈ Subtype.val '' V.shellOrbit S hE η hη}

/-- The edge-phase orbit of a cycle lies in the preimage of the quotient orbit. -/
theorem cycleOrbit_subset_shellOrbitPreimage {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E)
    (e : Γ.Edge) : V.cycleOrbit S hE η hη e ⊆ V.shellOrbitPreimage S hE η hη e := by
  rintro x ⟨u, hu, hux⟩
  have hadm := FlightState.trajectory_admissible S (V.germFlight hE η hη) u
  have hH := FlightState.trajectory_hamiltonian_eq' S (V.germFlight hE η hη) u
  unfold germTrajectory at hux
  rw [hux] at hadm hH
  rw [V.germFlight_energy] at hH
  refine ⟨hadm.1, hH, V.flow S (V.departureClass S hE η hη) u, ⟨u, rfl⟩, ?_⟩
  rw [V.flow_departureClass S hE η hη hu.1, trajClass_val, hux]

/-- **The orbit of a cycle is the preimage of the quotient orbit, off the incoming boundary
states.**  A point `x` of the closed edge at energy `E` which is not an incoming boundary state
(at an end of the edge with momentum pointing into the vertex) lies on the edge-phase orbit of the
cycle of `η` exactly when its class lies on the orbit of the global flow through the departure
state of `η`.  At the incoming boundary states the class is that of the scattered outgoing state,
which the trajectory visits instead; these states are `ν_E`-null (`shellMeasure_boundary`). -/
theorem mem_cycleOrbit_iff_mem_shellOrbitPreimage {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E)
    {e : Γ.Edge} {x : ℝ × ℝ}
    (hin : ¬ ((x.1 = 0 ∧ x.2 < 0) ∨ (x.1 = Γ.length e ∧ 0 < x.2))) :
    x ∈ V.cycleOrbit S hE η hη e ↔ x ∈ V.shellOrbitPreimage S hE η hη e := by
  refine ⟨fun h => V.cycleOrbit_subset_shellOrbitPreimage S hE hη e h, ?_⟩
  rintro ⟨hx, hxE, z, hz, hzx⟩
  have hadm := V.admissiblePoint_of_hamiltonian hE hx hxE
  have hyin : ¬ IsIncomingPoint (V := V) S (Γ.graphPoint (e, x)) := by
    rw [isIncomingPoint_graphPoint_iff V S hadm]
    exact hin
  rw [← V.suspension_image S hE hη] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  simp only at hzx
  rw [V.flow_departureClass S hE η hη hu.1] at hzx
  exact ⟨u, hu, V.trajectory_eq_of_trajClass_val_eq S (V.germFlight_notIncoming hE η hη) hadm
    hyin hzx⟩

/-- The preimage of the quotient orbit differs from the edge-phase orbit only by boundary
states. -/
theorem shellOrbitPreimage_diff_subset {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E)
    (e : Γ.Edge) :
    V.shellOrbitPreimage S hE η hη e \ V.cycleOrbit S hE η hη e ⊆
      {x | x.1 = 0 ∨ x.1 = Γ.length e} := by
  rintro x ⟨hx, hnx⟩
  by_contra hb
  apply hnx
  refine (V.mem_cycleOrbit_iff_mem_shellOrbitPreimage S hE hη ?_).mpr hx
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact hb (Or.inl h)
  · exact hb (Or.inr h)

theorem shellOrbitPreimage_ae_eq {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) (e : Γ.Edge) :
    V.shellOrbitPreimage S hE η hη e =ᵐ[V.shellMeasure E e] V.cycleOrbit S hE η hη e := by
  rw [ae_eq_set]
  refine ⟨measure_mono_null (V.shellOrbitPreimage_diff_subset S hE hη e)
    (V.shellMeasure_boundary E e), ?_⟩
  rw [sdiff_eq_empty.mpr (V.cycleOrbit_subset_shellOrbitPreimage S hE hη e), measure_empty]

/-- **Theorem VIII.5 (c) on the quotient orbit: `ν_E` is Lebesgue measure in the time
coordinate.**  Integrating a Borel function against `ν_E` over the edge-phase points whose class
lies on the orbit of the departure state of `η` is integrating it in time over one period. -/
theorem sum_setLIntegral_shellOrbitPreimage {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E)
    {F : Γ.Edge → ℝ × ℝ → ℝ≥0∞} (hF : ∀ e, Measurable (F e)) :
    ∑ e, ∫⁻ x in V.shellOrbitPreimage S hE η hη e, F e x ∂(V.shellMeasure E e) =
      ∫⁻ u in Ico 0 (V.cyclePeriod S E η),
        F (V.germTrajectory S hE η hη u).1 (V.germTrajectory S hE η hη u).2 := by
  rw [← V.sum_setLIntegral_cycleOrbit S hE hη hF]
  exact Finset.sum_congr rfl fun e _ => setLIntegral_congr (V.shellOrbitPreimage_ae_eq S hE hη e)

/-- **Theorem VIII.5 (c) on the quotient orbit: the `ν_E`-mass of the orbit of a cycle is its
period** `T_c(E)`. -/
theorem shellOrbitMass {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) :
    ∑ e, V.shellMeasure E e (V.shellOrbitPreimage S hE η hη e) =
      ENNReal.ofReal (V.cyclePeriod S E η) := by
  rw [← V.orbitMass S hE hη]
  exact Finset.sum_congr rfl fun e _ => measure_congr (V.shellOrbitPreimage_ae_eq S hE hη e)

end QuotientOrbit

/-! ### The period as an edge integral, and the applicability of Proposition VII.1 -/

/-- **Equation (8.4) with the travel-time formula.**  The period of the cycle of `η` is the sum,
over the ends `ζ` of the cycle, of the time-density masses of the positions swept by the two
momentum sheets of the flight of `ζ`: `T_c(E) = ∑_{ζ ∈ c} ∫_{flight of ζ} |dq| / √(2(E - V))`. -/
theorem ofReal_cyclePeriod_eq_sum (S : BorelEnergyPreservingScattering V) {E : ℝ}
    (hE : V.ShellRegular E) {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) :
    ENNReal.ofReal (V.cyclePeriod S E η) = ∑ ζ ∈ V.germCycle S E η,
      ((∫⁻ x in V.sheetImage hE 1 ζ, V.timeDensity ζ.1 E x) +
        ∫⁻ x in V.sheetImage hE (-1) ζ, V.timeDensity ζ.1 E x) := by
  rw [cyclePeriod, ENNReal.ofReal_sum_of_nonneg (f := V.flightTime E)
    (fun ζ _ => V.departureDurationTotal_nonneg _ _)]
  refine Finset.sum_congr rfl (fun ζ hζc => ?_)
  have hζ := V.germCycle_subset S hE hη hζc
  rw [V.sheetImage_of_mem hE 1 hζ, V.sheetImage_of_mem hE (-1) hζ]
  exact V.ofReal_flightTime_eq hE hζ

/-- **Proposition VII.1 applies at a shell-regular energy.**  Every turning point of the level `E`
on a closed edge is simple: inside the edge by `deriv_extension_ne_zero_of_shellRegular`, and the
endpoints are not on the level since `E` is not a vertex value.  Hence the time measure of every
edge is finite. -/
theorem lintegral_timeDensity_edge_lt_top_of_shellRegular {E : ℝ} (hE : V.ShellRegular E)
    (e : Γ.Edge) : ∫⁻ q in Icc (0 : ℝ) (Γ.length e), V.timeDensity e E q < ⊤ := by
  refine V.lintegral_timeDensity_edge_lt_top e (fun q hq hVq => ?_)
  have hvert : ∀ b : Bool, q = FiniteMetricGraph.EdgeEnd.coordinate Γ (e, b) → False := by
    intro b hb
    apply hE.not_exceptional
    rw [V.mem_exceptionalEnergies_iff]
    refine ⟨FiniteMetricGraph.EdgeEnd.vertex Γ (e, b), ?_⟩
    rw [← V.endpoint_value (e, b), ← hb, hVq]
  rcases eq_or_lt_of_le hq.1 with h0 | h0
  · exact (hvert false h0.symm).elim
  rcases eq_or_lt_of_le hq.2 with hl | hl
  · exact (hvert true hl).elim
  exact V.deriv_extension_ne_zero_of_shellRegular hE ⟨h0, hl⟩ hVq

/-! ### Theorem VIII.5 (b) and (c), packaged -/

section Packaged

variable (S : BorelEnergyPreservingScattering V) [Nonempty Γ.Edge]

/-- **Theorem VIII.5 (b), periodicity.**  For a shell-regular energy `E`:

* the departure state of every admissible end `η` returns to itself after the period
  `T_c(E) = ∑_{ζ ∈ c} t_E(ζ) > 0` of the cycle `c` of `η`, and `T_c(E)` is its least positive
  period, both for the global flow `Φ_t` of Theorem VI.5 and for the trajectory on the edge phase
  spaces;
* every point of the shell `Σ_E` lies on such an orbit and is periodic with least period the
  period of its cycle.

The travel-time formula is `ofReal_cyclePeriod_eq_sum`, `flightTime_eq_integral_of_crossing` and
`flightTime_eq_two_mul_integral_of_turning`. -/
theorem regularShell_periodic {E : ℝ} (hE : V.ShellRegular E) :
    (∀ (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E),
      V.cyclePeriod S E η = ∑ ζ ∈ V.germCycle S E η, V.flightTime E ζ ∧
      0 < V.cyclePeriod S E η ∧
      flow V S (V.departureClass S hE η hη) (V.cyclePeriod S E η) =
        V.departureClass S hE η hη ∧
      (∀ u ∈ Ioo 0 (V.cyclePeriod S E η),
        flow V S (V.departureClass S hE η hη) u ≠ V.departureClass S hE η hη) ∧
      V.germTrajectory S hE η hη (V.cyclePeriod S E η) = V.germTrajectory S hE η hη 0 ∧
      ∀ u ∈ Ioo 0 (V.cyclePeriod S E η),
        V.germTrajectory S hE η hη u ≠ V.germTrajectory S hE η hη 0) ∧
    ∀ z ∈ V.shell S E, ∃ (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E),
      z ∈ V.shellOrbit S hE η hη ∧ 0 < V.cyclePeriod S E η ∧
      flow V S z (V.cyclePeriod S E η) = z ∧
      ∀ t ∈ Ioo 0 (V.cyclePeriod S E η), flow V S z t ≠ z :=
  ⟨fun _ hη => ⟨rfl, V.cyclePeriod_pos S hE hη, V.flow_cyclePeriod_departureClass S hE hη,
      fun _ hu => V.flow_departureClass_ne_self S hE hη hu, V.germTrajectory_cyclePeriod S hE hη,
      fun _ hu => V.germTrajectory_ne_zero S hE hη hu⟩,
    fun _ hz => V.shell_periodic S hE hz⟩

/-- **Theorem VIII.5 (c), the orbit decomposition and the suspension.**  For a shell-regular
energy `E`:

* the shell `Σ_E` is the union of the orbits of the departure states;
* two such orbits coincide exactly when the ends lie in the same cycle of `Π_E`, and are disjoint
  otherwise, so `Σ_E` is the disjoint union of one orbit per cycle;
* on the orbit of `η`, `u ↦ Φ_u(departure state of η)` is a bijection from `[0, T_c(E))` onto the
  orbit in which `Φ_t` is the translation `u ↦ u + t mod T_c(E)`, and the first return to the
  departure states happens after `t_E(η)`, at the departure state of `Π_E(η)`. -/
theorem regularShell_decomposition {E : ℝ} (hE : V.ShellRegular E) :
    (∀ z, z ∈ V.shell S E ↔
      ∃ (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E), z ∈ V.shellOrbit S hE η hη) ∧
    (∀ η ζ : V.allowedGerms E, V.shellOrbit S hE η η.2 = V.shellOrbit S hE ζ ζ.2 ↔
      (V.shellGermPerm S hE).SameCycle η ζ) ∧
    (∀ (η ζ : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E) (hζ : ζ ∈ V.allowedGerms E),
      ζ ∉ V.germCycle S E η → Disjoint (V.shellOrbit S hE η hη) (V.shellOrbit S hE ζ hζ)) ∧
    ∀ (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E),
      InjOn (fun u => flow V S (V.departureClass S hE η hη) u) (Ico 0 (V.cyclePeriod S E η)) ∧
      (fun u => flow V S (V.departureClass S hE η hη) u) '' Ico 0 (V.cyclePeriod S E η) =
        V.shellOrbit S hE η hη ∧
      (∀ u t : ℝ, flow V S (flow V S (V.departureClass S hE η hη) u) t =
        flow V S (V.departureClass S hE η hη)
          (toIcoMod (V.cyclePeriod_pos S hE hη) 0 (u + t))) ∧
      flow V S (V.departureClass S hE η hη) (V.flightTime E η) =
        V.departureClass S hE (V.germStep S E η) (V.germStep_mem S hE hη) ∧
      ∀ u ∈ Ioo 0 (V.flightTime E η), ∀ (ζ : Γ.EdgeEnd) (hζ : ζ ∈ V.allowedGerms E),
        flow V S (V.departureClass S hE η hη) u ≠ V.departureClass S hE ζ hζ :=
  ⟨V.mem_shell_iff_exists_mem_shellOrbit S hE, V.shellOrbit_eq_iff S hE,
    fun _ _ hη hζ h => V.disjoint_shellOrbit S hE hη hζ h,
    fun _ hη => ⟨V.suspension_injOn S hE hη, V.suspension_image S hE hη,
      V.flow_suspension S hE hη, V.flow_departureClass_flightTime S hE hη,
      fun _ hu ζ hζ => V.flow_departureClass_ne_departureClass S hE hη hu.1 hu.2 ζ hζ⟩⟩

/-- **Theorem VIII.5 (c), the measure.**  For a shell-regular energy `E`, on the orbit of the
global flow through the departure state of every admissible end `η` (as the set
`shellOrbitPreimage` of edge-phase points whose class lies on that orbit) the invariant measure
`ν_E` is Lebesgue measure in the time coordinate, with mass `T_c(E)`, and
`ν_E(Σ_E) = ∑_c T_c(E) = ∑_{η ∈ G_E} t_E(η)`. -/
theorem regularShell_measure {E : ℝ} (hE : V.ShellRegular E) :
    (∀ (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E) (F : Γ.Edge → ℝ × ℝ → ℝ≥0∞),
      (∀ e, Measurable (F e)) →
      ∑ e, ∫⁻ x in V.shellOrbitPreimage S hE η hη e, F e x ∂(V.shellMeasure E e) =
        ∫⁻ u in Ico 0 (V.cyclePeriod S E η),
          F (V.germTrajectory S hE η hη u).1 (V.germTrajectory S hE η hη u).2) ∧
    (∀ (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E),
      ∑ e, V.shellMeasure E e (V.shellOrbitPreimage S hE η hη e) =
        ENNReal.ofReal (V.cyclePeriod S E η)) ∧
    ∑ e, V.shellMeasure E e univ =
      ENNReal.ofReal (∑ c ∈ V.germCycles S E, ∑ ζ ∈ c, V.flightTime E ζ) ∧
    ∑ c ∈ V.germCycles S E, ∑ ζ ∈ c, V.flightTime E ζ =
      ∑ η ∈ V.allowedFinset E, V.flightTime E η :=
  ⟨fun _ hη _ hF => V.sum_setLIntegral_shellOrbitPreimage S hE hη hF,
    fun _ hη => V.shellOrbitMass S hE hη, (V.shellMass hE S).1, (V.shellMass hE S).2⟩

end Packaged

end MechanicalPotential

end HamiltonianMetricGraphs
