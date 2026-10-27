/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3: the invariance of the quotient Liouville measure
-/

import HamiltonianMetricGraphs.ExactPiece

/-!
# The invariance of the quotient Liouville measure

The partition that closes Lemma VI.3.  Fix a compact regular energy window `K` and let
`(r₁, r₂, δ, u₀)` be the flow box of `exists_germFlowBox`.  For `0 < s` with `2 s ≤ u₀` the regular
energy sector of `K` is the disjoint union of

* one **no-impact** stratum per edge (the flight survives past `s`),
* one **one-impact** stratum per ordered pair of germs (the impact happens strictly inside `(0, s)`,
  lands at the first germ and scatters into the second),
* one **end-of-step** stratum per ordered pair of germs (the impact happens exactly at `s`),
* one **departure** stratum per germ (the representative sits at a vertex).

Disjointness is automatic because each stratum lies in a fibre of the classifier `stratumIndex`,
and the cover is the dichotomy interior/at-a-vertex together with the trichotomy no
impact/impact before `s`/impact at `s`.  The flow preserves the measure of each stratum: the first
by Lemma V.1 (`measure_image_flow_noImpactPiece`), the second by the germ tube charts
(`measure_image_flow_impactPiece`), and the last two because both they and their images are null
(`measure_image_flow_exactPiece`, `measure_image_flow_departurePiece`).

`preservesOn_of_countable_partition` turns this into `ShortTimeInvariance`, and
`measure_preimage_flow_of_shortTime` upgrades that to **Lemma VI.3**: `m (Φ_t⁻¹ B) = m B` for every
real time and every Borel set (`measure_preimage_flow`).
-/

namespace HamiltonianMetricGraphs

open Set MeasureTheory
open FiniteMetricGraph.EdgeEnd (coordinate vertex)
open scoped ENNReal NNReal

/-! ### The germ of an endpoint position -/

/-- The endpoint germ of a position which is an endpoint of the edge `e`. -/
noncomputable def edgeEndOfPosition (Γ : FiniteMetricGraph) (e : Γ.Edge) (q : ℝ) :
    Γ.EdgeEnd := by
  classical
  exact if q = Γ.length e then (e, true) else (e, false)

theorem edgeEndOfPosition_fst (Γ : FiniteMetricGraph) (e : Γ.Edge) (q : ℝ) :
    (edgeEndOfPosition Γ e q).1 = e := by
  classical
  unfold edgeEndOfPosition
  by_cases h : q = Γ.length e
  · rw [if_pos h]
  · rw [if_neg h]

theorem edgeEndOfPosition_coordinate (Γ : FiniteMetricGraph) (e : Γ.Edge) {q : ℝ}
    (hq : q = 0 ∨ q = Γ.length e) : coordinate Γ (edgeEndOfPosition Γ e q) = q := by
  classical
  unfold edgeEndOfPosition
  by_cases h : q = Γ.length e
  · rw [if_pos h, FiniteMetricGraph.edgeEnd_coordinate_true, h]
  · rw [if_neg h, FiniteMetricGraph.edgeEnd_coordinate_false]
    exact (hq.resolve_right h).symm

theorem edgeEndOfPosition_self (Γ : FiniteMetricGraph) (η : Γ.EdgeEnd) :
    edgeEndOfPosition Γ η.1 (coordinate Γ η) = η := by
  classical
  unfold edgeEndOfPosition
  by_cases hbo : η.2 = true
  · have hcoord : coordinate Γ η = Γ.length η.1 := by
      simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo]
    rw [if_pos hcoord]
    exact Prod.ext rfl hbo.symm
  · have hbo' : η.2 = false := by
      cases h : η.2 with
      | false => rfl
      | true => exact absurd h hbo
    have hcoord : coordinate Γ η = 0 := by
      simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo']
    have hne : coordinate Γ η ≠ Γ.length η.1 := by
      rw [hcoord]
      exact ne_of_lt (Γ.length_pos η.1)
    rw [if_neg hne]
    exact Prod.ext rfl hbo'.symm

/-- The index set of the partition of a regular energy sector into strata. -/
abbrev StratumIndex (Γ : FiniteMetricGraph) : Type :=
  Γ.Edge ⊕ (Γ.EdgeEnd × Γ.EdgeEnd) ⊕ (Γ.EdgeEnd × Γ.EdgeEnd) ⊕ Γ.EdgeEnd

namespace MechanicalPotential

open PhysicalEdgeSegment

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-! ### A countable partition of one energy sector suffices -/

/-- **A countable partition of one energy sector with piecewise invariance suffices.**  The
argument of `measure_preimage_flow_of_partition`, run inside the invariant energy sector `C` and
for an arbitrary countable index. -/
theorem preservesOn_of_countable_partition [Nonempty Γ.Edge] {C : Set ℝ} (t : ℝ)
    {ι : Type*} [Countable ι] {P : ι → Set (RegularScatteringPhaseSpace (V := V) S)}
    (hPmeas : ∀ i, MeasurableSet (P i))
    (hPdisj : Pairwise (Function.onFun Disjoint P))
    (hPcover : V.energySector S C ⊆ ⋃ i, P i)
    (hPpres : ∀ i, ∀ W, W ⊆ P i → MeasurableSet W →
      regularLiouville V S ((fun z => flow V S z t) '' W) = regularLiouville V S W) :
    V.PreservesOn S C t := by
  classical
  intro B hB hBC
  have hinj : Function.Injective
      (fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z t) :=
    (V.flowMeasurableEquiv S t).injective
  have hsurj : Function.Surjective
      (fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z t) :=
    (V.flowMeasurableEquiv S t).surjective
  have hBpre : MeasurableSet ((fun z => flow V S z t) ⁻¹' B) := (V.measurable_flow S t) hB
  have hpresub : (fun z => flow V S z t) ⁻¹' B ⊆ ⋃ i, P i :=
    le_trans (V.preimage_flow_subset_energySector S hBC t) hPcover
  have hsrc : (fun z => flow V S z t) ⁻¹' B = ⋃ i, (P i ∩ (fun z => flow V S z t) ⁻¹' B) := by
    rw [← iUnion_inter]
    exact (inter_eq_self_of_subset_right hpresub).symm
  have hsrcmeas : ∀ i, MeasurableSet (P i ∩ (fun z => flow V S z t) ⁻¹' B) :=
    fun i => (hPmeas i).inter hBpre
  have hsrcdisj : Pairwise (Function.onFun Disjoint
      fun i => P i ∩ (fun z => flow V S z t) ⁻¹' B) :=
    fun m n hmn => Disjoint.mono inter_subset_left inter_subset_left (hPdisj hmn)
  have himgmeas : ∀ i, MeasurableSet ((fun z => flow V S z t) '' (P i) ∩ B) :=
    fun i => (V.measurableSet_image_flow S t (hPmeas i)).inter hB
  have himgdisj : Pairwise (Function.onFun Disjoint
      fun i => (fun z => flow V S z t) '' (P i) ∩ B) :=
    fun m n hmn => Disjoint.mono inter_subset_left inter_subset_left
      (Set.disjoint_image_of_injective hinj (hPdisj hmn))
  have hBimg : B ⊆ (fun z => flow V S z t) '' (⋃ i, P i) := by
    intro y hy
    obtain ⟨z, hz⟩ := hsurj y
    have hzy : flow V S z t = y := hz
    have hzpre : z ∈ (fun z => flow V S z t) ⁻¹' B := by
      change flow V S z t ∈ B
      rw [hzy]
      exact hy
    exact ⟨z, hpresub hzpre, hz⟩
  have himgcover : (⋃ i, ((fun z => flow V S z t) '' (P i) ∩ B)) = B := by
    rw [← iUnion_inter, ← image_iUnion]
    exact inter_eq_self_of_subset_right hBimg
  have hkey : ∀ i, regularLiouville V S (P i ∩ (fun z => flow V S z t) ⁻¹' B) =
      regularLiouville V S ((fun z => flow V S z t) '' (P i) ∩ B) := by
    intro i
    have himg : (fun z => flow V S z t) '' (P i ∩ (fun z => flow V S z t) ⁻¹' B) =
        (fun z => flow V S z t) '' (P i) ∩ B := by
      ext y
      constructor
      · rintro ⟨z, ⟨hzP, hzB⟩, rfl⟩
        exact ⟨⟨z, hzP, rfl⟩, hzB⟩
      · rintro ⟨⟨z, hzP, rfl⟩, hyB⟩
        exact ⟨z, ⟨hzP, hyB⟩, rfl⟩
    rw [← hPpres i _ inter_subset_left (hsrcmeas i), himg]
  rw [hsrc, measure_iUnion hsrcdisj hsrcmeas, tsum_congr hkey,
    ← measure_iUnion himgdisj himgmeas, himgcover]

/-! ### The impact speeds of a pair of germs -/

/-- The speeds that leave both germs of an impact with an energy of the window `K`. -/
def impactSpeeds (K : Set ℝ) (η η' : Γ.EdgeEnd) : Set ℝ :=
  V.windowSpeeds K η ∩ V.windowSpeeds K η'

theorem measurableSet_impactSpeeds {K : Set ℝ} (hK : MeasurableSet K) (η η' : Γ.EdgeEnd) :
    MeasurableSet (V.impactSpeeds K η η') :=
  (V.measurableSet_windowSpeeds hK η).inter (V.measurableSet_windowSpeeds hK η')

theorem impactSpeeds_subset_left (K : Set ℝ) (η η' : Γ.EdgeEnd) :
    V.impactSpeeds K η η' ⊆ V.windowSpeeds K η := inter_subset_left

theorem impactSpeeds_subset_right (K : Set ℝ) (η η' : Γ.EdgeEnd) :
    V.impactSpeeds K η η' ⊆ V.windowSpeeds K η' := inter_subset_right

/-! ### The impact speed leaves both germs of the impact -/

/-- The departure after the first impact of an interior flight carries the energy of the flight. -/
theorem departureEnergy_interiorStep {e : Γ.Edge} {x : ℝ × ℝ} (hx : x ∈ V.interiorRegular e)
    (hbdd : BddAbove (durationSet V e x)) :
    V.departureEnergy (interiorStep V S e x).1 (interiorStep V S e x).2
      = V.hamiltonian e x.1 x.2 := by
  have hbdd' : BddAbove (durationSet V (FlightState.ofInterior V hx.1 hx.2).edge
      (FlightState.ofInterior V hx.1 hx.2).state) := hbdd
  obtain ⟨b, hb, -, hbenergy, -, -⟩ :=
    FlightState.next_eq_some_of_bddAbove (V := V) S (FlightState.ofInterior V hx.1 hx.2) hbdd'
  obtain ⟨he, hs⟩ := V.interiorStep_next S hx hbdd hb
  have heq : V.departureEnergy (interiorStep V S e x).1 (interiorStep V S e x).2
      = b.energy := by
    rw [FlightState.energy_eq, he, hs]
    rfl
  rw [heq, hbenergy]
  rfl

/-- **Scattering does not move the vertex.**  The germ the flight departs after its first impact
sits at the same vertex as the germ it arrives at. -/
theorem vertex_interiorStep {e : Γ.Edge} {x : ℝ × ℝ} (hx : x ∈ V.interiorRegular e)
    (hbdd : BddAbove (durationSet V e x)) :
    vertex Γ (interiorStep V S e x).1
      = vertex Γ (edgeCovector (Γ := Γ) e (V.landingState e x)).germ := by
  classical
  set a : V.FlightState := FlightState.ofInterior V hx.1 hx.2 with hadef
  have hbdd' : BddAbove (durationSet V a.edge a.state) := hbdd
  have hland : V.landingState e x = a.segment.maximalEndpoint hbdd' := by
    rw [landingState, V.edgeFlight_of_mem hx]
    exact FlightState.flightCurve_sSup a hbdd'
  have hcoveq : edgeCovector (Γ := Γ) e (V.landingState e x)
      = a.segment.maximalArrivalCovector hbdd' a.regular := by
    rw [hland]
    exact V.edgeCovector_eq_maximalArrivalCovector a.segment hbdd' a.regular
  have hinraw := (a.segment.maximalArrivalIncoming hbdd' a.regular).2.2
  have hpos : (edgeCovector (Γ := Γ) e (V.landingState e x)).germ.sign *
      (edgeCovector (Γ := Γ) e (V.landingState e x)).momentum > 0 := by
    rw [hcoveq]; exact hinraw
  have hstep1 : (interiorStep V S e x).1
      = (scatterCovector (V := V) S (edgeCovector (Γ := Γ) e (V.landingState e x))).germ := rfl
  rw [hstep1, scatterCovector_incoming (V := V) S hpos]
  exact (S.map (edgeCovector (Γ := Γ) e (V.landingState e x)).germ.vertex
    ⟨edgeCovector (Γ := Γ) e (V.landingState e x), ⟨rfl, hpos⟩⟩).2.1

/-- **The impact speed leaves both germs of the impact with the energy of the state.** -/
theorem interiorStep_mem_impactSpeeds {e : Γ.Edge} {x : ℝ × ℝ} (hx : x ∈ V.interiorRegular e)
    (hbdd : BddAbove (durationSet V e x)) {K : Set ℝ} (hE : V.hamiltonian e x.1 x.2 ∈ K) :
    (interiorStep V S e x).2 ∈ V.impactSpeeds K
      (edgeCovector (Γ := Γ) e (V.landingState e x)).germ (interiorStep V S e x).1 := by
  classical
  have hreg' : (interiorStep V S e x).2 ∈ V.regularSpeeds (interiorStep V S e x).1 :=
    V.interiorStep_mem_regularSpeeds S hx hbdd
  have hEstep := V.departureEnergy_interiorStep S hx hbdd
  have hvert := V.vertex_interiorStep S hx hbdd
  have hEsame : V.departureEnergy (edgeCovector (Γ := Γ) e (V.landingState e x)).germ
      (interiorStep V S e x).2
      = V.departureEnergy (interiorStep V S e x).1 (interiorStep V S e x).2 := by
    rw [V.departureEnergy_eq, V.departureEnergy_eq, hvert]
  refine ⟨⟨⟨hreg'.1, ?_⟩, ?_⟩, hreg', ?_⟩
  · rw [hEsame, hEstep]
    exact hx.2
  · rw [Set.mem_preimage, hEsame, hEstep]
    exact hE
  · rw [Set.mem_preimage, hEstep]
    exact hE

/-! ### The classifier -/

/-- The stratum index of an edge state at the step length `s`. -/
noncomputable def pointIndex (s : ℝ) (y : Γ.Edge × ℝ × ℝ) : StratumIndex Γ := by
  classical
  exact
    if y.2.1 ∈ Ioo (0 : ℝ) (Γ.length y.1) then
      if y.2 ∈ V.noImpactSet y.1 s then Sum.inl y.1
      else if V.interiorDurationTotal y.1 y.2 = s then
        Sum.inr (Sum.inr (Sum.inl
          ((edgeCovector (Γ := Γ) y.1 (V.landingState y.1 y.2)).germ,
            (interiorStep V S y.1 y.2).1)))
      else
        Sum.inr (Sum.inl
          ((edgeCovector (Γ := Γ) y.1 (V.landingState y.1 y.2)).germ,
            (interiorStep V S y.1 y.2).1))
    else Sum.inr (Sum.inr (Sum.inr (edgeEndOfPosition Γ y.1 y.2.1)))

theorem pointIndex_noImpact {s : ℝ} {e : Γ.Edge} {x : ℝ × ℝ} (h : x ∈ V.noImpactSet e s) :
    V.pointIndex S s ((e, x) : Γ.Edge × ℝ × ℝ) = Sum.inl e := by
  classical
  unfold pointIndex
  rw [if_pos (show x.1 ∈ Ioo (0 : ℝ) (Γ.length e) from h.1.1), if_pos h]

theorem pointIndex_impact {s : ℝ} {e : Γ.Edge} {x : ℝ × ℝ}
    (hxreg : x ∈ V.interiorRegular e) (hno : x ∉ V.noImpactSet e s)
    (hne : V.interiorDurationTotal e x ≠ s) :
    V.pointIndex S s ((e, x) : Γ.Edge × ℝ × ℝ) = Sum.inr (Sum.inl
      ((edgeCovector (Γ := Γ) e (V.landingState e x)).germ, (interiorStep V S e x).1)) := by
  classical
  unfold pointIndex
  rw [if_pos (show x.1 ∈ Ioo (0 : ℝ) (Γ.length e) from hxreg.1), if_neg hno, if_neg hne]

theorem pointIndex_exact {s : ℝ} {e : Γ.Edge} {x : ℝ × ℝ}
    (hxreg : x ∈ V.interiorRegular e) (hno : x ∉ V.noImpactSet e s)
    (heq : V.interiorDurationTotal e x = s) :
    V.pointIndex S s ((e, x) : Γ.Edge × ℝ × ℝ) = Sum.inr (Sum.inr (Sum.inl
      ((edgeCovector (Γ := Γ) e (V.landingState e x)).germ, (interiorStep V S e x).1))) := by
  classical
  unfold pointIndex
  rw [if_pos (show x.1 ∈ Ioo (0 : ℝ) (Γ.length e) from hxreg.1), if_neg hno, if_pos heq]

theorem pointIndex_boundary {s : ℝ} {e : Γ.Edge} {x : ℝ × ℝ}
    (h : x.1 ∉ Ioo (0 : ℝ) (Γ.length e)) :
    V.pointIndex S s ((e, x) : Γ.Edge × ℝ × ℝ) =
      Sum.inr (Sum.inr (Sum.inr (edgeEndOfPosition Γ e x.1))) := by
  classical
  unfold pointIndex
  rw [if_neg h]

/-- The stratum index of a regular class. -/
noncomputable def stratumIndex (s : ℝ) (z : RegularScatteringPhaseSpace (V := V) S) :
    StratumIndex Γ :=
  V.pointIndex S s (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
    (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ)

/-! ### The strata -/

/-- The strata of the partition of the regular energy sector of `K`. -/
noncomputable def stratum (K : Set ℝ) (s : ℝ) :
    StratumIndex Γ → Set (RegularScatteringPhaseSpace (V := V) S)
  | Sum.inl e => V.noImpactPiece S e K s
  | Sum.inr (Sum.inl (η, η')) => V.impactPiece S η η' (V.impactSpeeds K η η') s
  | Sum.inr (Sum.inr (Sum.inl (η, η'))) => V.exactPiece S η η' (V.impactSpeeds K η η') s
  | Sum.inr (Sum.inr (Sum.inr η₀)) => V.departurePiece S η₀ (V.windowSpeeds K η₀)

theorem measurableSet_stratum {K : Set ℝ} (hK : MeasurableSet K) {s : ℝ} (hs : 0 < s)
    (i : StratumIndex Γ) : MeasurableSet (V.stratum S K s i) := by
  rcases i with e | ⟨η, η'⟩ | ⟨η, η'⟩ | η₀
  · exact V.measurableSet_noImpactPiece S e hK hs
  · exact V.measurableSet_impactPiece S η η' (V.measurableSet_impactSpeeds hK η η') s
  · exact V.measurableSet_exactPiece S η η' (V.measurableSet_impactSpeeds hK η η') s
  · exact V.measurableSet_departurePiece S η₀ (V.measurableSet_windowSpeeds hK η₀)

/-- Each stratum lies in a fibre of the classifier. -/
theorem stratum_subset_fibre (K : Set ℝ) {s : ℝ} (i : StratumIndex Γ) :
    V.stratum S K s i ⊆ {z | V.stratumIndex S s z = i} := by
  classical
  rcases i with e | ⟨η, η'⟩ | ⟨η, η'⟩ | η₀
  · intro z hz
    obtain ⟨-, hedge, hnoi⟩ := hz
    have hpair : (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
          (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ)
        = ((e, (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) :=
      Prod.ext hedge rfl
    change V.pointIndex S s _ = _
    rw [hpair, V.pointIndex_noImpact S hnoi]
  · intro z hz
    obtain ⟨hedge, hslice⟩ := hz
    have hpair : (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
          (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ)
        = ((η.1, (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) :=
      Prod.ext hedge rfl
    have hθ : V.interiorDurationTotal η.1
        ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)
        = sSup (durationSet V η.1 ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)) :=
      V.interiorDurationTotal_of_mem hslice.1.1
    have hno : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 ∉
        V.noImpactSet η.1 s := by
      intro hcon
      have h := hcon.2 hslice.1.2
      rw [← hθ] at h
      linarith [hslice.2.1.2]
    change V.pointIndex S s _ = _
    rw [hpair, V.pointIndex_impact S hslice.1.1 hno (ne_of_lt hslice.2.1.2),
      hslice.2.2.1, hslice.2.2.2.1]
  · intro z hz
    obtain ⟨⟨hedge, hslice⟩, hexact⟩ := hz
    have hexact' : V.interiorDurationTotal η.1
        ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) = s := hexact
    have hpair : (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
          (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ)
        = ((η.1, (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) :=
      Prod.ext hedge rfl
    have hθ : V.interiorDurationTotal η.1
        ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)
        = sSup (durationSet V η.1 ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)) :=
      V.interiorDurationTotal_of_mem hslice.1.1
    have hno : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 ∉
        V.noImpactSet η.1 s := by
      intro hcon
      have h := hcon.2 hslice.1.2
      rw [← hθ, hexact'] at h
      linarith
    change V.pointIndex S s _ = _
    rw [hpair, V.pointIndex_exact S hslice.1.1 hno hexact',
      hslice.2.2.1, hslice.2.2.2.1]
  · intro z hz
    obtain ⟨hedge, hposc, -, -⟩ := hz
    have hpair : (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
          (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ)
        = ((η₀.1, (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) :=
      Prod.ext hedge rfl
    have hlenpos : 0 < Γ.length η₀.1 := Γ.length_pos η₀.1
    have hnotint : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.1 ∉
        Ioo (0 : ℝ) (Γ.length η₀.1) := by
      rw [hposc]
      by_cases hbo : η₀.2 = true
      · have hcoord : coordinate Γ η₀ = Γ.length η₀.1 := by
          simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo]
        rw [hcoord]
        exact fun hcon => absurd hcon.2 (lt_irrefl _)
      · have hbo' : η₀.2 = false := by
          cases h : η₀.2 with
          | false => rfl
          | true => exact absurd h hbo
        have hcoord : coordinate Γ η₀ = 0 := by
          simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo']
        rw [hcoord]
        exact fun hcon => absurd hcon.1 (lt_irrefl _)
    change V.pointIndex S s _ = _
    rw [hpair, V.pointIndex_boundary S hnotint, hposc, edgeEndOfPosition_self]

theorem pairwise_disjoint_stratum (K : Set ℝ) (s : ℝ) :
    Pairwise (Function.onFun Disjoint (V.stratum S K s)) := by
  intro i j hij
  refine Set.disjoint_left.mpr (fun z hzi hzj => ?_)
  have h1 := V.stratum_subset_fibre S K i hzi
  have h2 := V.stratum_subset_fibre S K j hzj
  exact hij (h1.symm.trans h2)

/-! ### The strata cover the energy sector -/

/-- **The strata cover the regular energy sector.**  A representative is either interior — and then
its flight either survives past `s`, or lands before `s`, or lands exactly at `s` — or it sits at a
vertex. -/
theorem energySector_subset_iUnion_stratum (K : Set ℝ) {s : ℝ} (hs : 0 < s) :
    V.energySector S K ⊆ ⋃ i, V.stratum S K s i := by
  classical
  intro z hz
  have hEz : quotientHamiltonian (V := V) S (z : ScatteringPhaseSpace (V := V) S) ∈ K := hz
  set e : Γ.Edge := (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 with hedef
  set x : ℝ × ℝ := (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 with hxdef
  have hEeq : quotientHamiltonian (V := V) S (z : ScatteringPhaseSpace (V := V) S)
      = V.hamiltonian e x.1 x.2 := by
    rw [← quotientMap_rep V S (z : ScatteringPhaseSpace (V := V) S), quotientHamiltonian_mk]
    rfl
  have hEx : V.hamiltonian e x.1 x.2 ∈ K := by rw [← hEeq]; exact hEz
  have hEreg : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies := by
    have h : quotientHamiltonian (V := V) S (z : ScatteringPhaseSpace (V := V) S) ∉
      V.exceptionalEnergies := z.2
    rw [hEeq] at h
    exact h
  by_cases hint : x.1 ∈ Ioo (0 : ℝ) (Γ.length e)
  · have hxreg : x ∈ V.interiorRegular e := ⟨hint, hEreg⟩
    by_cases hno : x ∈ V.noImpactSet e s
    · exact mem_iUnion.mpr ⟨Sum.inl e, hEz, rfl, hno⟩
    · have hnot : ¬ (∀ _ : BddAbove (durationSet V e x), s < sSup (durationSet V e x)) :=
        fun h => hno ⟨hxreg, h⟩
      have hbdd : BddAbove (durationSet V e x) := by
        by_contra hb
        exact hnot (fun h => absurd h hb)
      have hle : sSup (durationSet V e x) ≤ s := by
        by_contra hl
        exact hnot (fun _ => not_le.mp hl)
      have hθ : V.interiorDurationTotal e x = sSup (durationSet V e x) :=
        V.interiorDurationTotal_of_mem hxreg
      have hθpos : 0 < V.interiorDurationTotal e x := by
        rw [hθ]
        exact FlightState.impactDuration_pos_of_bddAbove (V := V)
          (FlightState.ofInterior V hxreg.1 hxreg.2) hbdd
      have hθle : V.interiorDurationTotal e x ≤ s := by rw [hθ]; exact hle
      have hrA := V.interiorStep_mem_impactSpeeds S hxreg hbdd hEx
      set η : Γ.EdgeEnd := (edgeCovector (Γ := Γ) e (V.landingState e x)).germ with hηdef
      set η' : Γ.EdgeEnd := (interiorStep V S e x).1 with hη'def
      have hη1 : η.1 = e := by rw [hηdef, edgeCovector_germ]
      have hslice : ∀ s' : ℝ, V.interiorDurationTotal e x ∈ Ioo (0 : ℝ) s' →
          x ∈ V.impactSlice S η η' (V.impactSpeeds K η η') s' := by
        intro s' hs'
        refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
        · rw [hη1]; exact hxreg
        · rw [hη1]; exact hbdd
        · rw [hη1]; exact hs'
        · rw [hη1]
        · rw [hη1]
        · rw [hη1]; exact hrA
      by_cases hexact : V.interiorDurationTotal e x = s
      · exact mem_iUnion.mpr ⟨Sum.inr (Sum.inr (Sum.inl (η, η'))),
          ⟨hη1.symm, hslice (2 * s) ⟨hθpos, by rw [hexact]; linarith⟩⟩,
          by rw [hη1]; exact hexact⟩
      · exact mem_iUnion.mpr ⟨Sum.inr (Sum.inl (η, η')),
          hη1.symm, hslice s ⟨hθpos, lt_of_le_of_ne hθle hexact⟩⟩
  · have hIcc : x.1 ∈ Icc (0 : ℝ) (Γ.length e) :=
      (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.2
    have hlenpos : 0 < Γ.length e := Γ.length_pos e
    have hor : x.1 = 0 ∨ x.1 = Γ.length e := by
      rcases lt_or_eq_of_le hIcc.1 with h | h
      · rcases lt_or_eq_of_le hIcc.2 with h2 | h2
        · exact absurd ⟨h, h2⟩ hint
        · exact Or.inr h2
      · exact Or.inl h.symm
    have hne : x.2 ≠ 0 := (rep V S (z : ScatteringPhaseSpace (V := V) S)).2.resolve_left hint
    have hnotin := rep_not_incoming V S (z : ScatteringPhaseSpace (V := V) S)
    rw [isIncomingPoint_iff] at hnotin
    have hη₀1 : (edgeEndOfPosition Γ e x.1).1 = e := edgeEndOfPosition_fst Γ e x.1
    have hη₀c : coordinate Γ (edgeEndOfPosition Γ e x.1) = x.1 :=
      edgeEndOfPosition_coordinate Γ e hor
    have hsign : FiniteMetricGraph.EdgeEnd.sign Γ (edgeEndOfPosition Γ e x.1) * x.2 < 0 := by
      rcases hor with h0 | hl
      · have hη₀eq : edgeEndOfPosition Γ e x.1 = (e, false) := by
          unfold edgeEndOfPosition
          rw [if_neg (by rw [h0]; exact ne_of_lt hlenpos)]
        have hxpos : 0 < x.2 := by
          rcases lt_trichotomy x.2 0 with h | h | h
          · exact absurd (Or.inl ⟨h0, h⟩) hnotin
          · exact absurd h hne
          · exact h
        rw [hη₀eq, Γ.edgeEnd_sign_false]
        linarith
      · have hη₀eq : edgeEndOfPosition Γ e x.1 = (e, true) := by
          unfold edgeEndOfPosition
          rw [if_pos hl]
        have hxneg : x.2 < 0 := by
          rcases lt_trichotomy x.2 0 with h | h | h
          · exact h
          · exact absurd h hne
          · exact absurd (Or.inr ⟨hl, h⟩) hnotin
        rw [hη₀eq, Γ.edgeEnd_sign_true]
        linarith
    have hEη₀ : V.departureEnergy (edgeEndOfPosition Γ e x.1) |x.2|
        = V.hamiltonian e x.1 x.2 := by
      have h1 : V.hamiltonian (edgeEndOfPosition Γ e x.1).1
            (coordinate Γ (edgeEndOfPosition Γ e x.1)) x.2
          = x.2 ^ 2 / 2 + V.vertexValue (vertex Γ (edgeEndOfPosition Γ e x.1)) :=
        V.endpoint_hamiltonian (edgeEndOfPosition Γ e x.1) x.2
      rw [hη₀1, hη₀c] at h1
      rw [V.departureEnergy_eq, sq_abs, h1]
    refine mem_iUnion.mpr ⟨Sum.inr (Sum.inr (Sum.inr (edgeEndOfPosition Γ e x.1))),
      hη₀1.symm, hη₀c.symm, hsign, ⟨⟨abs_pos.mpr hne, ?_⟩, ?_⟩⟩
    · rw [hEη₀]; exact hEreg
    · rw [Set.mem_preimage, hEη₀]; exact hEx

/-! ### The short-time invariance and Lemma VI.3 -/

section Flow

variable [Nonempty Γ.Edge]

/-- **Lemma VI.3, short-time part.**  On every compact regular energy window the flow preserves
the quotient Liouville measure for all sufficiently short times. -/
theorem shortTimeInvariance : V.ShortTimeInvariance S := by
  classical
  intro K hK hKreg
  obtain ⟨r₁, r₂, δ, u₀, hlen, hbox⟩ := V.exists_germFlowBox K hK hKreg
  obtain ⟨ε₀, hε₀, hnoimp⟩ := V.exists_uniform_measure_image_flightCurve K hK
  have hu₀ : 0 < u₀ := (hbox (Classical.arbitrary Γ.EdgeEnd)).time_pos
  refine ⟨min (u₀ / 2) ε₀, lt_min (by linarith) hε₀, ?_⟩
  intro s hs hslt
  have hsu₀ : s < u₀ / 2 := lt_of_lt_of_le hslt (min_le_left _ _)
  have hsε : s ≤ ε₀ := le_of_lt (lt_of_lt_of_le hslt (min_le_right _ _))
  have h2s : 2 * s ≤ u₀ := by linarith
  have hsu : s ≤ u₀ := by linarith
  have hKm : MeasurableSet K := hK.measurableSet
  refine V.preservesOn_of_countable_partition S s
    (V.measurableSet_stratum S hKm hs) (V.pairwise_disjoint_stratum S K s)
    (V.energySector_subset_iUnion_stratum S K hs) ?_
  intro i W hWsub hWm
  rcases i with e | ⟨η, η'⟩ | ⟨η, η'⟩ | η₀
  · exact V.measure_image_flow_noImpactPiece S e K hs (hnoimp e s hs hsε) hWm hWsub
  · exact V.measure_image_flow_impactPiece S (V.measurableSet_impactSpeeds hKm η η')
      ((hbox η).mono (V.impactSpeeds_subset_left K η η'))
      ((hbox η').mono (V.impactSpeeds_subset_right K η η'))
      (hlen η.1) (hlen η'.1) hsu hWm hWsub
  · exact V.measure_image_flow_exactPiece S (V.measurableSet_impactSpeeds hKm η η')
      ((hbox η).mono (V.impactSpeeds_subset_left K η η'))
      ((hbox η').mono (V.impactSpeeds_subset_right K η η')) hs h2s hWm hWsub
  · exact V.measure_image_flow_departurePiece S η₀ (V.measurableSet_windowSpeeds hKm η₀)
      (hbox η₀) (hlen η₀.1) hs h2s hWm hWsub

/-- **Lemma VI.3.**  The quotient Liouville measure of the regular sector is invariant under the
scattered evolution `Φ_t`, for every real time and every Borel set. -/
theorem measure_preimage_flow (t : ℝ)
    {B : Set (RegularScatteringPhaseSpace (V := V) S)} (hB : MeasurableSet B) :
    regularLiouville V S ((fun z => flow V S z t) ⁻¹' B) = regularLiouville V S B :=
  V.measure_preimage_flow_of_shortTime S (V.shortTimeInvariance S) t hB

/-- **Lemma VI.3, measure-preserving form.**  `Φ_t` preserves the quotient Liouville measure of the
regular sector. -/
theorem measurePreserving_flow (t : ℝ) :
    MeasurePreserving (fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z t)
      (regularLiouville V S) (regularLiouville V S) := by
  refine ⟨V.measurable_flow S t, ?_⟩
  refine Measure.ext (fun B hB => ?_)
  rw [Measure.map_apply (V.measurable_flow S t) hB]
  exact V.measure_preimage_flow S t hB

end Flow

end MechanicalPotential

end HamiltonianMetricGraphs
