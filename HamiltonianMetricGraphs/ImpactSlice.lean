/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3: the one-impact stratum in interior edge coordinates
-/

import HamiltonianMetricGraphs.LiouvilleChart
import HamiltonianMetricGraphs.GermTube

/-!
# The one-impact stratum in interior edge coordinates

`LiouvilleChart.lean` writes the quotient Liouville measure as the sum over the edges of the planar
Lebesgue measure of the interior slices.  For the strata of Lemma VI.3 that sum has a *single*
term: every point of such a stratum is the class of an interior state of one fixed edge, and the
quotient map is injective on the edge interiors (`rep_interiorClass`), so all the other slices are
empty (`regularLiouville_eq_volume_interiorSlice`).

The stratum itself is described by the *first impact data*, which `PointTrajectory.lean` and
`ImpactStep.lean` provide as Borel functions of the interior state:

* `interiorDurationTotal` — the time until the first impact;
* `landingState` together with `edgeCovector` — the germ at which the flight lands;
* `interiorStep` — the germ and the speed with which the flight departs again.

`impactSlice η η' A s` collects the interior states of the edge of `η` whose first impact happens
strictly within the time `s`, lands at `η`, and scatters into `η'` with a speed of `A`; it is Borel
(`measurableSet_impactSlice`), and `impactPiece` is the corresponding Borel set of the quotient.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set MeasureTheory PhysicalEdgeSegment

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-! ### A quotient set carried by one edge -/

/-- **A stratum carried by one edge.**  If every point of a Borel set of the regular sector has its
outgoing representative on the edge `e`, then its quotient Liouville measure is the planar measure
of its interior slice over `e`: all the other slices are empty, because an interior point is its own
outgoing representative. -/
theorem regularLiouville_eq_volume_interiorSlice (e : Γ.Edge)
    {W : Set (RegularScatteringPhaseSpace (V := V) S)} (hW : MeasurableSet W)
    (hWsub : ∀ z ∈ W, (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 = e) :
    regularLiouville V S W = volume (V.interiorSlice S (Subtype.val '' W) e) := by
  classical
  rw [V.regularLiouville_eq_tsum_interiorSlice S hW]
  refine tsum_eq_single e (fun e' he' => ?_)
  have hempty : V.interiorSlice S (Subtype.val '' W) e' = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx1, z, hzW, hzv⟩
    have hadm : Γ.AdmissiblePoint ((e', x) : Γ.Edge × ℝ × ℝ) :=
      ⟨Set.Ioo_subset_Icc_self hx1, Or.inl hx1⟩
    have hxreg : x ∈ V.interiorRegular e' := by
      refine ⟨hx1, ?_⟩
      have h := z.2
      change quotientHamiltonian (V := V) S (z : ScatteringPhaseSpace (V := V) S) ∉
        V.exceptionalEnergies at h
      rw [hzv, quotientHamiltonian_graphClass V S hadm] at h
      exact h
    have hrep : rep V S (graphClass V S ((e', x) : Γ.Edge × ℝ × ℝ))
        = Γ.graphPoint ((e', x) : Γ.Edge × ℝ × ℝ) := V.rep_interiorClass S hxreg
    have hedge : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 = e' := by
      rw [hzv, hrep]
      exact Γ.graphPoint_edge hadm
    exact he' (hedge.symm.trans (hWsub z hzW))
  rw [hempty, measure_empty]

/-! ### The one-impact stratum -/

/-- **The one-impact stratum in interior edge coordinates.**  The interior states of the edge of
`η` whose flight lands, does so strictly within the time `s` at the germ `η`, and scatters into the
germ `η'` with a speed belonging to `A`. -/
def impactSlice (η η' : Γ.EdgeEnd) (A : Set ℝ) (s : ℝ) : Set (ℝ × ℝ) :=
  {x | (x ∈ V.interiorRegular η.1 ∧ BddAbove (durationSet V η.1 x)) ∧
    V.interiorDurationTotal η.1 x ∈ Ioo (0 : ℝ) s ∧
    (edgeCovector (Γ := Γ) η.1 (V.landingState η.1 x)).germ = η ∧
    (interiorStep V S η.1 x).1 = η' ∧ (interiorStep V S η.1 x).2 ∈ A}

theorem impactSlice_subset_interiorRegular (η η' : Γ.EdgeEnd) (A : Set ℝ) (s : ℝ) :
    V.impactSlice S η η' A s ⊆ V.interiorRegular η.1 := fun _ hx => hx.1.1

theorem measurableSet_impactSlice (η η' : Γ.EdgeEnd) {A : Set ℝ} (hA : MeasurableSet A)
    (s : ℝ) : MeasurableSet (V.impactSlice S η η' A s) := by
  classical
  have h1 : MeasurableSet
      {x : ℝ × ℝ | x ∈ V.interiorRegular η.1 ∧ BddAbove (durationSet V η.1 x)} :=
    V.measurableSet_interiorLands η.1
  have h2 : MeasurableSet
      {x : ℝ × ℝ | V.interiorDurationTotal η.1 x ∈ Ioo (0 : ℝ) s} :=
    (V.measurable_interiorDurationTotal η.1) measurableSet_Ioo
  have hgerm : Measurable fun x : ℝ × ℝ =>
      (edgeCovector (Γ := Γ) η.1 (V.landingState η.1 x)).germ :=
    (Γ.measurable_boundary_germ).comp
      ((measurable_edgeCovector (Γ := Γ) η.1).comp (V.measurable_landingStateTotal η.1))
  have h3 : MeasurableSet
      {x : ℝ × ℝ | (edgeCovector (Γ := Γ) η.1 (V.landingState η.1 x)).germ = η } :=
    hgerm (measurableSet_singleton η)
  have hstep : Measurable (interiorStep V S η.1) := V.measurable_interiorStepTotal S η.1
  have h4 : MeasurableSet {x : ℝ × ℝ | (interiorStep V S η.1 x).1 = η'} :=
    hstep.fst (measurableSet_singleton η')
  have h5 : MeasurableSet {x : ℝ × ℝ | (interiorStep V S η.1 x).2 ∈ A} := hstep.snd hA
  exact h1.inter (h2.inter (h3.inter (h4.inter h5)))

/-- The one-impact stratum of the quotient: the regular points whose outgoing representative is an
interior state of the edge of `η` lying in `impactSlice`. -/
def impactPiece (η η' : Γ.EdgeEnd) (A : Set ℝ) (s : ℝ) :
    Set (RegularScatteringPhaseSpace (V := V) S) :=
  {z | (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 = η.1 ∧
    (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 ∈ V.impactSlice S η η' A s}

theorem measurableSet_impactPiece (η η' : Γ.EdgeEnd) {A : Set ℝ} (hA : MeasurableSet A)
    (s : ℝ) : MeasurableSet (V.impactPiece S η η' A s) := by
  classical
  have hpair : Measurable fun z : RegularScatteringPhaseSpace (V := V) S =>
      (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
        (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) :=
    (V.measurable_repPair S).comp measurable_subtype_coe
  have h1 : MeasurableSet {z : RegularScatteringPhaseSpace (V := V) S |
      (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 = η.1} :=
    hpair.fst (measurableSet_singleton η.1)
  have h2 : MeasurableSet {z : RegularScatteringPhaseSpace (V := V) S |
      (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 ∈ V.impactSlice S η η' A s} :=
    hpair.snd (V.measurableSet_impactSlice S η η' hA s)
  exact h1.inter h2

/-- The interior slice of a Borel subset of the one-impact stratum sits inside the stratum in
interior edge coordinates. -/
theorem interiorSlice_subset_impactSlice {η η' : Γ.EdgeEnd} {A : Set ℝ} {s : ℝ}
    {W : Set (RegularScatteringPhaseSpace (V := V) S)} (hW : W ⊆ V.impactPiece S η η' A s) :
    V.interiorSlice S (Subtype.val '' W) η.1 ⊆ V.impactSlice S η η' A s := by
  rintro x ⟨hx1, z, hzW, hzv⟩
  have hadm : Γ.AdmissiblePoint ((η.1, x) : Γ.Edge × ℝ × ℝ) :=
    ⟨Set.Ioo_subset_Icc_self hx1, Or.inl hx1⟩
  have hxreg : x ∈ V.interiorRegular η.1 := by
    refine ⟨hx1, ?_⟩
    have h := z.2
    change quotientHamiltonian (V := V) S (z : ScatteringPhaseSpace (V := V) S) ∉
      V.exceptionalEnergies at h
    rw [hzv, quotientHamiltonian_graphClass V S hadm] at h
    exact h
  have hrep : rep V S (graphClass V S ((η.1, x) : Γ.Edge × ℝ × ℝ))
      = Γ.graphPoint ((η.1, x) : Γ.Edge × ℝ × ℝ) := V.rep_interiorClass S hxreg
  have hstate : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 = x := by
    rw [hzv, hrep]
    exact Γ.graphPoint_state hadm
  have h := (hW hzW).2
  rwa [hstate] at h

/-- Every point of the one-impact stratum has its outgoing representative on the edge of `η`. -/
theorem rep_edge_of_mem_impactPiece {η η' : Γ.EdgeEnd} {A : Set ℝ} {s : ℝ}
    {W : Set (RegularScatteringPhaseSpace (V := V) S)} (hW : W ⊆ V.impactPiece S η η' A s) :
    ∀ z ∈ W, (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 = η.1 :=
  fun _ hz => (hW hz).1

/-- **The one-impact stratum in a single planar chart.**  The quotient Liouville measure of a Borel
subset of the stratum is the planar measure of its interior slice over the edge of `η`, and that
slice lies inside `impactSlice`. -/
theorem regularLiouville_impactPiece_eq {η η' : Γ.EdgeEnd} {A : Set ℝ} {s : ℝ}
    {W : Set (RegularScatteringPhaseSpace (V := V) S)} (hWmeas : MeasurableSet W)
    (hW : W ⊆ V.impactPiece S η η' A s) :
    regularLiouville V S W = volume (V.interiorSlice S (Subtype.val '' W) η.1) :=
  V.regularLiouville_eq_volume_interiorSlice S η.1 hWmeas (V.rep_edge_of_mem_impactPiece S hW)

end MechanicalPotential

end HamiltonianMetricGraphs
