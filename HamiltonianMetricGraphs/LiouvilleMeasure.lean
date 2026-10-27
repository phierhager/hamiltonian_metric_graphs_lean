/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.QuotientPhaseSpace

/-!
# Liouville measures

The prequotient Liouville measure is the finite sum of Lebesgue `dq dp` on closed edge
cylinders.  The quotient measure is its pushforward under the scattering quotient map.
-/

namespace HamiltonianMetricGraphs

open MeasureTheory

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- Lebesgue `dq dp` on a closed edge cylinder, represented as the comap to its subtype. -/
noncomputable def edgeLiouville (e : Γ.Edge) : Measure (Γ.EdgePhase e) :=
  volume.comap Subtype.val

/-- The two edge endpoints `q ∈ {0, length}` form a Liouville-null set in a single edge cylinder:
the vertical lines `{0} × ℝ` and `{length} × ℝ` have planar Lebesgue measure zero.  This is the
edgewise input to the quotient Liouville boundary-null formula (Lemma IV.5/IV.6): the vertex
identifications live on a Liouville-null set, so the quotient measure is carried by the interior. -/
theorem edgeLiouville_boundary_null (e : Γ.Edge) :
    Γ.edgeLiouville e {x : Γ.EdgePhase e | x.1.1 = 0 ∨ x.1.1 = Γ.length e} = 0 := by
  have hEP : MeasurableSet (Γ.EdgePhase e) := measurable_fst measurableSet_Icc
  rw [edgeLiouville, (MeasurableEmbedding.subtype_coe hEP).comap_apply]
  refine measure_mono_null (t := {y : ℝ × ℝ | y.1 = 0 ∨ y.1 = Γ.length e}) ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact hx
  · have hset : {y : ℝ × ℝ | y.1 = 0 ∨ y.1 = Γ.length e}
        = ({0, Γ.length e} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true,
        Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod,
      Set.Finite.measure_zero ((Set.finite_singleton _).insert _) volume, zero_mul]

/-- The edgewise Liouville measure is σ-finite: its pushforward along the (measurable-embedding)
subtype inclusion is `volume` restricted to the edge cylinder, which is σ-finite. -/
noncomputable instance (e : Γ.Edge) : SigmaFinite (Γ.edgeLiouville e) := by
  have hEP : MeasurableSet (Γ.EdgePhase e) := measurable_fst measurableSet_Icc
  refine SigmaFinite.of_map _ (measurable_subtype_coe.aemeasurable) ?_
  rw [edgeLiouville, (MeasurableEmbedding.subtype_coe hEP).map_comap, Subtype.range_coe]
  infer_instance

noncomputable instance (e : Γ.Edge) : SFinite (Γ.edgeLiouville e) := inferInstance

noncomputable instance (e : Γ.Edge) :
    SFinite (Measure.map (Sigma.mk e) (Γ.edgeLiouville e) : Measure Γ.PrequotientPhase) :=
  inferInstance

/-- Finite disjoint sum of the edgewise Liouville measures. -/
noncomputable def prequotientLiouville : Measure Γ.PrequotientPhase :=
  Measure.sum fun e : Γ.Edge => Measure.map (Sigma.mk e) (Γ.edgeLiouville e)

noncomputable instance : SFinite Γ.prequotientLiouville := by
  unfold prequotientLiouville; infer_instance

/-- **Boundary-null formula (Lemma IV.5/IV.6 input).**  The set of prequotient states sitting at an
edge endpoint (`q ∈ {0, length}`) — exactly where the scattering quotient glues fibres together —
is `prequotientLiouville`-null.  Hence the quotient Liouville measure is carried by the edge
interiors, and the vertex identifications contribute nothing. -/
theorem prequotientLiouville_boundary_null :
    Γ.prequotientLiouville {x : Γ.PrequotientPhase | x.2.1.1 = 0 ∨ x.2.1.1 = Γ.length x.1} = 0 := by
  have hBmeas : MeasurableSet {x : Γ.PrequotientPhase | x.2.1.1 = 0 ∨ x.2.1.1 = Γ.length x.1} := by
    have h1 : MeasurableSet {x : Γ.PrequotientPhase | x.2.1.1 = 0} :=
      MechanicalPotential.measurable_prequotientPosition (measurableSet_singleton 0)
    have h2 : MeasurableSet {x : Γ.PrequotientPhase | x.2.1.1 = Γ.length x.1} :=
      measurableSet_eq_fun MechanicalPotential.measurable_prequotientPosition
        MechanicalPotential.measurable_prequotientLength
    exact h1.union h2
  rw [prequotientLiouville, Measure.sum_apply _ hBmeas]
  refine ENNReal.tsum_eq_zero.mpr (fun e => ?_)
  change (Measure.map (fun y : Γ.EdgePhase e => (⟨e, y⟩ : Γ.PrequotientPhase))
    (Γ.edgeLiouville e)) _ = 0
  rw [Measure.map_apply (Γ.measurable_prequotientSigmaMk e) hBmeas]
  exact Γ.edgeLiouville_boundary_null e

/-- The edge momentum reversal is an involution. -/
theorem edgePhaseMomentumReversal_involutive (e : Γ.Edge) (x : Γ.EdgePhase e) :
    Γ.edgePhaseMomentumReversal e (Γ.edgePhaseMomentumReversal e x) = x := by
  apply Subtype.ext; simp [edgePhaseMomentumReversal]

/-- **Edgewise Liouville invariance of momentum reversal.**  The reflection `(q,p) ↦ (q,-p)`
preserves the edge Liouville measure `dq dp`.  This is the one Liouville invariance whose Jacobian is
trivially `±1`; it is the reflection component of the reversibility (Corollary VI.6) hypothesis. -/
theorem measurePreserving_edgePhaseMomentumReversal (e : Γ.Edge) :
    MeasureTheory.MeasurePreserving (Γ.edgePhaseMomentumReversal e)
      (Γ.edgeLiouville e) (Γ.edgeLiouville e) := by
  have hR : MeasurePreserving (fun x : ℝ × ℝ => (x.1, -x.2))
      (volume : Measure (ℝ × ℝ)) volume := by
    have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
    rw [← Measure.volume_eq_prod] at h
    exact h
  have hEP : MeasurableSet (Γ.EdgePhase e) := measurable_fst measurableSet_Icc
  have hemb : MeasurableEmbedding (Subtype.val : Γ.EdgePhase e → ℝ × ℝ) :=
    MeasurableEmbedding.subtype_coe hEP
  refine ⟨Γ.measurable_edgePhaseMomentumReversal e, ?_⟩
  ext s hs
  rw [Measure.map_apply (Γ.measurable_edgePhaseMomentumReversal e) hs, edgeLiouville,
    hemb.comap_apply, hemb.comap_apply]
  have hinv := Γ.edgePhaseMomentumReversal_involutive e
  have hset : Subtype.val '' (Γ.edgePhaseMomentumReversal e ⁻¹' s)
      = (fun x : ℝ × ℝ => (x.1, -x.2)) ⁻¹' (Subtype.val '' s) := by
    ext y
    constructor
    · rintro ⟨x, hxs, rfl⟩
      exact ⟨Γ.edgePhaseMomentumReversal e x, hxs, rfl⟩
    · rintro ⟨x', hx's, hx'y⟩
      refine ⟨Γ.edgePhaseMomentumReversal e x', ?_, ?_⟩
      · show Γ.edgePhaseMomentumReversal e (Γ.edgePhaseMomentumReversal e x') ∈ s
        rw [hinv]; exact hx's
      · show ((Γ.edgePhaseMomentumReversal e x' : Γ.EdgePhase e) : ℝ × ℝ) = y
        have hval : ((Γ.edgePhaseMomentumReversal e x' : Γ.EdgePhase e) : ℝ × ℝ)
            = ((x'.1).1, -(x'.1).2) := rfl
        rw [hval, show (x'.1 : ℝ × ℝ) = (y.1, -y.2) from hx'y]
        simp
  rw [hset]
  exact hR.measure_preimage (hemb.measurableSet_image.mpr hs).nullMeasurableSet

/-- The edge momentum reversal packaged as a measurable equivalence (a measurable involution). -/
noncomputable def edgePhaseMomentumReversalEquiv (e : Γ.Edge) :
    Γ.EdgePhase e ≃ᵐ Γ.EdgePhase e where
  toFun := Γ.edgePhaseMomentumReversal e
  invFun := Γ.edgePhaseMomentumReversal e
  left_inv := Γ.edgePhaseMomentumReversal_involutive e
  right_inv := Γ.edgePhaseMomentumReversal_involutive e
  measurable_toFun := Γ.measurable_edgePhaseMomentumReversal e
  measurable_invFun := Γ.measurable_edgePhaseMomentumReversal e

/-- Comap along a measurable embedding commutes with countable measure sums. -/
theorem comap_embedding_sum {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) (m : ℕ → Measure β) :
    (Measure.sum m).comap f = Measure.sum (fun n => (m n).comap f) := by
  ext s hs
  rw [hf.comap_apply, Measure.sum_apply _ (hf.measurableSet_image.mpr hs),
    Measure.sum_apply _ hs]
  simp_rw [hf.comap_apply]

/-- Restriction of the prequotient Liouville measure to nonzero-momentum states. -/
noncomputable def nonzeroPrequotientLiouville : Measure Γ.NonzeroPrequotientPhase :=
  Γ.prequotientLiouville.comap Subtype.val

noncomputable instance : SFinite Γ.nonzeroPrequotientLiouville := by
  have hemb : MeasurableEmbedding
      (Subtype.val : Γ.NonzeroPrequotientPhase → Γ.PrequotientPhase) :=
    MeasurableEmbedding.subtype_coe (MechanicalPotential.measurableSet_nonzeroPrequotientPhase)
  unfold nonzeroPrequotientLiouville
  rw [show Γ.prequotientLiouville = Measure.sum (sfiniteSeq Γ.prequotientLiouville) from
      (sum_sfiniteSeq _).symm, comap_embedding_sum hemb]
  infer_instance

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-- The quotient Liouville measure from Definition IV.5. -/
noncomputable def quotientLiouville : Measure (ScatteringPhaseSpace (V := V) S) :=
  Measure.map (quotientMap (V := V) S) Γ.nonzeroPrequotientLiouville

noncomputable instance : SFinite (quotientLiouville (V := V) S) := by
  unfold quotientLiouville; infer_instance

end MechanicalPotential
end HamiltonianMetricGraphs
