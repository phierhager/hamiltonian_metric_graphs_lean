/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma IV.6 / Lemma VI.3: the quotient Liouville measure in interior edge coordinates
-/

import HamiltonianMetricGraphs.FlowMeasurable
import HamiltonianMetricGraphs.LiouvilleMeasure

/-!
# The quotient Liouville measure in interior edge coordinates

The quotient Liouville measure `m` of Definition IV.5 is the pushforward of the edgewise Lebesgue
measure along the scattering quotient map.  The vertex identifications live on the edge endpoints,
which are Liouville-null (`prequotientLiouville_boundary_null`), so `m` is carried by the edge
interiors, where the quotient map is injective.  This module turns that observation into a working
formula:

`m A = ∑ₑ vol { x : 0 < q < ℓₑ, [e, x] ∈ A }`   (`quotientLiouville_eq_tsum_interiorSlice`)

which reduces every statement about `m` to a statement about planar Lebesgue measure on the
interiors of the edges.  Together with

`Φ_t [e, x] = [pointTrajectory (e, x) t]`   (`forwardFlow_interiorClass`)

— the flow read in the same coordinates, using that an interior point is its own outgoing
representative — this reduces the invariance `m (Φ_t⁻¹ A) = m A` of Lemma VI.3 to the *prequotient*
statement that the time-`t` graph trajectory preserves `∑ₑ vol` on the edge interiors
(`measure_preimage_flow_iff_interior`).
-/

namespace HamiltonianMetricGraphs

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-! ### The interior slices of a quotient set -/

/-- The set of interior states of the edge `e` whose class lies in `A`. -/
def interiorSlice (A : Set (ScatteringPhaseSpace (V := V) S)) (e : Γ.Edge) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioo (0 : ℝ) (Γ.length e) ∧ graphClass V S (e, x) ∈ A}

theorem measurableSet_interiorSlice {A : Set (ScatteringPhaseSpace (V := V) S)}
    (hA : MeasurableSet A) (e : Γ.Edge) : MeasurableSet (V.interiorSlice S A e) := by
  have hcls : Measurable fun x : ℝ × ℝ => graphClass V S (e, x) :=
    (V.measurable_graphClass S).comp (measurable_const.prodMk measurable_id)
  exact (measurable_fst measurableSet_Ioo).inter (hcls hA)

/-- The vertical lines over the two endpoints of an edge are planar-null. -/
theorem volume_edgeBoundary (e : Γ.Edge) :
    (volume : Measure (ℝ × ℝ)) {x : ℝ × ℝ | x.1 = 0 ∨ x.1 = Γ.length e} = 0 := by
  have hset : {x : ℝ × ℝ | x.1 = 0 ∨ x.1 = Γ.length e}
      = ({0, Γ.length e} : Set ℝ) ×ˢ (univ : Set ℝ) := by
    ext x
    simp [Set.mem_prod, Set.mem_insert_iff]
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod,
    show (volume : Measure ℝ) {0, Γ.length e} = 0 from
      measure_union_null (measure_singleton 0) (measure_singleton _),
    zero_mul]

/-- **The quotient Liouville measure in interior edge coordinates.**  Since the vertex
identifications live on the Liouville-null edge endpoints and the quotient map is injective on the
edge interiors, the measure of a Borel quotient set is the sum over the edges of the planar
Lebesgue measure of its interior slices. -/
theorem quotientLiouville_eq_tsum_interiorSlice {A : Set (ScatteringPhaseSpace (V := V) S)}
    (hA : MeasurableSet A) :
    quotientLiouville (V := V) S A = ∑' e : Γ.Edge, volume (V.interiorSlice S A e) := by
  classical
  have hemb : MeasurableEmbedding
      (Subtype.val : Γ.NonzeroPrequotientPhase → Γ.PrequotientPhase) :=
    MeasurableEmbedding.subtype_coe measurableSet_nonzeroPrequotientPhase
  have hpre : MeasurableSet (quotientMap (V := V) S ⁻¹' A) :=
    (measurable_quotientMap (V := V) S) hA
  have himg : MeasurableSet (Subtype.val '' (quotientMap (V := V) S ⁻¹' A)) :=
    hemb.measurableSet_image' hpre
  rw [quotientLiouville, Measure.map_apply (measurable_quotientMap (V := V) S) hA,
    FiniteMetricGraph.nonzeroPrequotientLiouville, hemb.comap_apply,
    FiniteMetricGraph.prequotientLiouville, Measure.sum_apply _ himg]
  refine tsum_congr fun e => ?_
  change (Measure.map (fun y : Γ.EdgePhase e => (⟨e, y⟩ : Γ.PrequotientPhase))
    (Γ.edgeLiouville e)) _ = _
  rw [Measure.map_apply (Γ.measurable_prequotientSigmaMk e) himg,
    FiniteMetricGraph.edgeLiouville,
    (MeasurableEmbedding.subtype_coe
      (show MeasurableSet (Γ.EdgePhase e) from measurable_fst measurableSet_Icc)).comap_apply]
  -- the admissible fibre slice and the interior slice differ only inside the null boundary lines
  refine le_antisymm ?_ ?_
  · refine le_trans (measure_mono (t := V.interiorSlice S A e ∪
      {x : ℝ × ℝ | x.1 = 0 ∨ x.1 = Γ.length e}) ?_) ?_
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := hx
      by_cases hb : x.1 = 0 ∨ x.1 = Γ.length e
      · exact Or.inr hb
      · have hIcc : x.1 ∈ Icc (0 : ℝ) (Γ.length e) := by rw [← hyx]; exact y.2
        have hIoo : x.1 ∈ Ioo (0 : ℝ) (Γ.length e) :=
          ⟨lt_of_le_of_ne hIcc.1 (fun h => hb (Or.inl h.symm)),
            lt_of_le_of_ne hIcc.2 (fun h => hb (Or.inr h))⟩
        have hadm : Γ.AdmissiblePoint ((e, x) : Γ.Edge × ℝ × ℝ) := ⟨hIcc, Or.inl hIoo⟩
        have hyeq : (⟨x, hIcc⟩ : Γ.EdgePhase e) = y := Subtype.ext hyx.symm
        obtain ⟨q, hq, hqv⟩ := hy
        have hgp : (Γ.graphPoint ((e, x) : Γ.Edge × ℝ × ℝ)).1 = q.1 := by
          rw [Γ.graphPoint_val hadm, hqv]
          exact congrArg (fun z : Γ.EdgePhase e => (⟨e, z⟩ : Γ.PrequotientPhase)) hyeq
        refine Or.inl ⟨hIoo, ?_⟩
        have hcls : graphClass V S ((e, x) : Γ.Edge × ℝ × ℝ) = quotientMap (V := V) S q :=
          congrArg (quotientMap (V := V) S) (Subtype.ext hgp)
        rw [hcls]
        exact hq
    · refine le_trans (measure_union_le _ _) ?_
      rw [volume_edgeBoundary (Γ := Γ) e, add_zero]
  · refine measure_mono ?_
    intro x hx
    have hadm : Γ.AdmissiblePoint ((e, x) : Γ.Edge × ℝ × ℝ) :=
      ⟨Ioo_subset_Icc_self hx.1, Or.inl hx.1⟩
    refine ⟨⟨x, hadm.1⟩, ⟨Γ.graphPoint ((e, x) : Γ.Edge × ℝ × ℝ), hx.2, ?_⟩, rfl⟩
    exact Γ.graphPoint_val hadm

/-! ### The flow in interior edge coordinates -/

/-- The class of an interior regular edge state, as a point of the regular quotient sector. -/
noncomputable def interiorClass {e : Γ.Edge} {x : ℝ × ℝ} (hx : x ∈ V.interiorRegular e) :
    RegularScatteringPhaseSpace (V := V) S :=
  ⟨graphClass V S (e, x), by
    change quotientHamiltonian (V := V) S (graphClass V S (e, x)) ∉ V.exceptionalEnergies
    rw [quotientHamiltonian_graphClass V S ⟨Ioo_subset_Icc_self hx.1, Or.inl hx.1⟩]
    exact hx.2⟩

@[simp] theorem interiorClass_val {e : Γ.Edge} {x : ℝ × ℝ} (hx : x ∈ V.interiorRegular e) :
    (V.interiorClass S hx).1 = graphClass V S (e, x) := rfl

/-- An interior point is its own outgoing representative. -/
theorem rep_interiorClass {e : Γ.Edge} {x : ℝ × ℝ} (hx : x ∈ V.interiorRegular e) :
    rep V S (V.interiorClass S hx).1 = Γ.graphPoint (e, x) := by
  have hadm : Γ.AdmissiblePoint ((e, x) : Γ.Edge × ℝ × ℝ) :=
    ⟨Ioo_subset_Icc_self hx.1, Or.inl hx.1⟩
  refine rep_quotientMap_of_not_incoming V S _ ?_
  rw [isIncomingPoint_graphPoint_iff V S hadm]
  rintro (⟨h0, -⟩ | ⟨hl, -⟩)
  · exact absurd h0 (ne_of_gt hx.1.1)
  · exact absurd hl (ne_of_lt hx.1.2)

section Flow

variable [Nonempty Γ.Edge]

/-- **The forward flow in interior edge coordinates.**  The class of an interior regular state
flows to the class of its graph trajectory. -/
theorem forwardFlow_interiorClass {e : Γ.Edge} {x : ℝ × ℝ} (hx : x ∈ V.interiorRegular e)
    (t : ℝ) :
    (forwardFlow V S (V.interiorClass S hx) t).1 =
      graphClass V S (V.pointTrajectory S (e, x) t) := by
  have hadm : Γ.AdmissiblePoint ((e, x) : Γ.Edge × ℝ × ℝ) :=
    ⟨Ioo_subset_Icc_self hx.1, Or.inl hx.1⟩
  have hpair : (((Γ.graphPoint ((e, x) : Γ.Edge × ℝ × ℝ)).1.1,
      (Γ.graphPoint ((e, x) : Γ.Edge × ℝ × ℝ)).1.2.1) : Γ.Edge × ℝ × ℝ) = (e, x) :=
    Prod.ext (Γ.graphPoint_edge hadm) (Γ.graphPoint_state hadm)
  rw [V.forwardFlow_eq_graphClass S (V.interiorClass S hx) t, V.rep_interiorClass S hx]
  exact congrArg (fun y : Γ.Edge × ℝ × ℝ => graphClass V S (V.pointTrajectory S y t)) hpair

/-! ### The reduction of Lemma VI.3 to the prequotient -/

/-- The quotient Liouville measure restricted to the regular sector, where the flow lives. -/
noncomputable def regularLiouville : Measure (RegularScatteringPhaseSpace (V := V) S) :=
  (quotientLiouville (V := V) S).comap Subtype.val

omit [Nonempty Γ.Edge] in
theorem regularLiouville_apply (B : Set (RegularScatteringPhaseSpace (V := V) S)) :
    regularLiouville V S B = quotientLiouville (V := V) S (Subtype.val '' B) :=
  (MeasurableEmbedding.subtype_coe (measurableSet_regularScatteringPhaseSpace V S)).comap_apply _ _

omit [Nonempty Γ.Edge] in
/-- The regular sector measure in interior edge coordinates. -/
theorem regularLiouville_eq_tsum_interiorSlice
    {B : Set (RegularScatteringPhaseSpace (V := V) S)} (hB : MeasurableSet B) :
    regularLiouville V S B = ∑' e : Γ.Edge, volume (V.interiorSlice S (Subtype.val '' B) e) := by
  rw [V.regularLiouville_apply S B]
  exact V.quotientLiouville_eq_tsum_interiorSlice S
    ((MeasurableEmbedding.subtype_coe
      (measurableSet_regularScatteringPhaseSpace V S)).measurableSet_image' hB)

/-- The interior slice of the `Φ_t`-preimage of a regular set: the interior regular states whose
time-`t` graph trajectory has its class in `C`. -/
def interiorPreimage (C : Set (ScatteringPhaseSpace (V := V) S)) (t : ℝ) (e : Γ.Edge) :
    Set (ℝ × ℝ) :=
  {x | x ∈ V.interiorRegular e ∧ graphClass V S (V.pointTrajectory S (e, x) t) ∈ C}

/-- The interior slice of a `Φ_t`-preimage is computed by the graph trajectory. -/
theorem interiorSlice_preimage_flow {B : Set (RegularScatteringPhaseSpace (V := V) S)}
    {t : ℝ} (ht : 0 ≤ t) (e : Γ.Edge) :
    V.interiorSlice S (Subtype.val '' ((fun z => flow V S z t) ⁻¹' B)) e =
      V.interiorPreimage S (Subtype.val '' B) t e := by
  ext x
  constructor
  · rintro ⟨hx1, w, hw, hwv⟩
    have hreg : x ∈ V.interiorRegular e := by
      refine ⟨hx1, ?_⟩
      have h := w.2
      change quotientHamiltonian (V := V) S (w : ScatteringPhaseSpace (V := V) S) ∉
        V.exceptionalEnergies at h
      rw [hwv, quotientHamiltonian_graphClass V S
        ⟨Ioo_subset_Icc_self hx1, Or.inl hx1⟩] at h
      exact h
    refine ⟨hreg, ?_⟩
    have hwe : w = V.interiorClass S hreg := Subtype.ext hwv
    refine ⟨flow V S w t, hw, ?_⟩
    rw [hwe, V.flow_of_nonneg S _ ht, V.forwardFlow_interiorClass S hreg]
  · rintro ⟨hreg, z, hz, hzv⟩
    refine ⟨hreg.1, V.interiorClass S hreg, ?_, rfl⟩
    have hval : (flow V S (V.interiorClass S hreg) t).1 =
        graphClass V S (V.pointTrajectory S (e, x) t) := by
      rw [V.flow_of_nonneg S _ ht, V.forwardFlow_interiorClass S hreg]
    have hfz : flow V S (V.interiorClass S hreg) t = z := Subtype.ext (by rw [hval, hzv])
    have hmem : flow V S (V.interiorClass S hreg) t ∈ B := by rw [hfz]; exact hz
    exact hmem

/-- **Reduction of Lemma VI.3 to the prequotient.**  For a nonnegative time the measure of the
`Φ_t`-preimage of a Borel set is the edgewise planar Lebesgue measure of the set of interior
regular states whose time-`t` graph trajectory lands in it.  Combined with
`regularLiouville_eq_tsum_interiorSlice`, the invariance `m (Φ_t⁻¹ B) = m B` of Lemma VI.3 is
therefore *equivalent* to the prequotient statement that the time-`t` graph trajectory preserves
`∑ₑ vol` on the edge interiors. -/
theorem regularLiouville_preimage_flow_eq_tsum
    {B : Set (RegularScatteringPhaseSpace (V := V) S)} (hB : MeasurableSet B)
    {t : ℝ} (ht : 0 ≤ t) :
    regularLiouville V S ((fun z => flow V S z t) ⁻¹' B) =
      ∑' e : Γ.Edge, volume (V.interiorPreimage S (Subtype.val '' B) t e) := by
  rw [V.regularLiouville_eq_tsum_interiorSlice S ((V.measurable_flow S t) hB)]
  exact tsum_congr fun e => congrArg _ (V.interiorSlice_preimage_flow S ht e)

end Flow

end MechanicalPotential

end HamiltonianMetricGraphs
