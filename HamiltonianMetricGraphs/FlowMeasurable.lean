/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Theorem VI.5: the scattered evolution is a Borel isomorphism
-/

import HamiltonianMetricGraphs.PointTrajectory
import HamiltonianMetricGraphs.FlowGroup

/-!
# The scattered evolution is bimeasurable

`PointTrajectory.lean` provides the totally defined Borel map `pointTrajectory` which computes
`FlightState.trajectory` from the bare graph phase point.  Composing it with the Borel outgoing
chart of Lemma IV.4 turns the quotient flow into a composition of Borel maps:

`Φ_t = (class of) ∘ pointTrajectory (·, t) ∘ (coordinates of the outgoing representative)`.

The remaining measurability input is that a graph phase point has a Borel class in the quotient
(`measurable_graphPoint`, `measurable_graphClass`): on each edge fibre the guarded constructor
`graphPoint` is the inclusion of the admissible set extended by a constant, and the fibre
inclusions into the prequotient coproduct are Borel.

Since `Φ_t⁻¹ = Φ_{-t}`, measurability of every `Φ_t` upgrades at once to bimeasurability, i.e. to
the measurable equivalence `flowMeasurableEquiv`.  This is the measurability half of
Theorem VI.5 (Lemma VI.4 in the paper).
-/

namespace HamiltonianMetricGraphs

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- The admissible points of a fixed edge form a Borel subset of the edge phase plane. -/
theorem measurableSet_admissiblePoint (e : Γ.Edge) :
    MeasurableSet {x : ℝ × ℝ | Γ.AdmissiblePoint (e, x)} := by
  have h1 : MeasurableSet {x : ℝ × ℝ | x.1 ∈ Icc (0 : ℝ) (Γ.length e)} :=
    measurable_fst measurableSet_Icc
  have h2 : MeasurableSet {x : ℝ × ℝ | x.1 ∈ Ioo (0 : ℝ) (Γ.length e)} :=
    measurable_fst measurableSet_Ioo
  have h3 : MeasurableSet {x : ℝ × ℝ | x.2 ≠ 0} :=
    (measurable_snd (measurableSet_singleton (0 : ℝ))).compl
  exact h1.inter (h2.union h3)

/-- The graph point of a fixed edge, as a point of that edge's closed phase cylinder. -/
noncomputable def edgeGraphPoint (e : Γ.Edge) (x : ℝ × ℝ) : Γ.EdgePhase e := by
  classical
  exact if h : Γ.AdmissiblePoint (e, x) then ⟨x, h.1⟩
    else ⟨(Γ.length e / 2, 0),
      ⟨(half_pos (Γ.length_pos e)).le, half_le_self (Γ.length_pos e).le⟩⟩

theorem edgeGraphPoint_val_of_mem {e : Γ.Edge} {x : ℝ × ℝ} (h : Γ.AdmissiblePoint (e, x)) :
    ((Γ.edgeGraphPoint e x : Γ.EdgePhase e) : ℝ × ℝ) = x := by
  classical
  unfold edgeGraphPoint
  rw [dif_pos h]

theorem edgeGraphPoint_val_of_notMem {e : Γ.Edge} {x : ℝ × ℝ}
    (h : ¬ Γ.AdmissiblePoint (e, x)) :
    ((Γ.edgeGraphPoint e x : Γ.EdgePhase e) : ℝ × ℝ) = (Γ.length e / 2, 0) := by
  classical
  unfold edgeGraphPoint
  rw [dif_neg h]

theorem measurable_edgeGraphPoint (e : Γ.Edge) : Measurable (Γ.edgeGraphPoint e) := by
  classical
  rw [measurable_comap_iff]
  change Measurable fun x : ℝ × ℝ => ((Γ.edgeGraphPoint e x : Γ.EdgePhase e) : ℝ × ℝ)
  refine measurable_of_measurable_union_cover {x : ℝ × ℝ | Γ.AdmissiblePoint (e, x)}
    {x : ℝ × ℝ | Γ.AdmissiblePoint (e, x)}ᶜ (Γ.measurableSet_admissiblePoint e)
    (Γ.measurableSet_admissiblePoint e).compl (by rw [union_compl_self]) ?_ ?_
  · change Measurable ({x : ℝ × ℝ | Γ.AdmissiblePoint (e, x)}.restrict
      (fun x : ℝ × ℝ => ((Γ.edgeGraphPoint e x : Γ.EdgePhase e) : ℝ × ℝ)))
    have heq : {x : ℝ × ℝ | Γ.AdmissiblePoint (e, x)}.restrict
        (fun x : ℝ × ℝ => ((Γ.edgeGraphPoint e x : Γ.EdgePhase e) : ℝ × ℝ)) =
        fun s => s.val :=
      funext fun s => Γ.edgeGraphPoint_val_of_mem s.2
    rw [heq]
    exact measurable_subtype_coe
  · change Measurable ({x : ℝ × ℝ | Γ.AdmissiblePoint (e, x)}ᶜ.restrict
      (fun x : ℝ × ℝ => ((Γ.edgeGraphPoint e x : Γ.EdgePhase e) : ℝ × ℝ)))
    have heq : {x : ℝ × ℝ | Γ.AdmissiblePoint (e, x)}ᶜ.restrict
        (fun x : ℝ × ℝ => ((Γ.edgeGraphPoint e x : Γ.EdgePhase e) : ℝ × ℝ)) =
        fun _ => (Γ.length e / 2, 0) :=
      funext fun s => Γ.edgeGraphPoint_val_of_notMem s.2
    rw [heq]
    exact measurable_const

theorem graphPoint_eq_sigma (e : Γ.Edge) (x : ℝ × ℝ) :
    ((Γ.graphPoint (e, x)).1 : Γ.PrequotientPhase) = ⟨e, Γ.edgeGraphPoint e x⟩ := by
  classical
  unfold graphPoint edgeGraphPoint
  by_cases h : Γ.AdmissiblePoint (e, x)
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]

/-- **A graph phase point has a Borel prequotient point.**  On each (finitely many) edge fibre the
guarded constructor is the inclusion of the admissible set, extended by the edge midpoint at rest,
and the fibre inclusion into the coproduct is Borel. -/
theorem measurable_graphPoint : Measurable Γ.graphPoint := by
  rw [measurable_comap_iff]
  change Measurable fun y : Γ.Edge × ℝ × ℝ => ((Γ.graphPoint y).1 : Γ.PrequotientPhase)
  refine measurable_from_prod_countable_right fun e => ?_
  have heq : (fun x : ℝ × ℝ => ((Γ.graphPoint (e, x)).1 : Γ.PrequotientPhase)) =
      fun x : ℝ × ℝ => (⟨e, Γ.edgeGraphPoint e x⟩ : Γ.PrequotientPhase) :=
    funext (Γ.graphPoint_eq_sigma e)
  rw [heq]
  exact (Γ.measurable_prequotientSigmaMk e).comp (Γ.measurable_edgeGraphPoint e)

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-- The edge and phase coordinates of a nonzero prequotient point are Borel. -/
theorem measurable_nonzeroPair :
    Measurable fun x : Γ.NonzeroPrequotientPhase => ((x.1.1, x.1.2.1) : Γ.Edge × ℝ × ℝ) := by
  have h1 : Measurable fun x : Γ.NonzeroPrequotientPhase => x.1.1 :=
    measurable_prequotientEdge.comp measurable_subtype_coe
  have h2 : Measurable fun x : Γ.NonzeroPrequotientPhase => x.1.2.1.1 :=
    measurable_prequotientPosition.comp measurable_subtype_coe
  have h3 : Measurable fun x : Γ.NonzeroPrequotientPhase => x.1.2.1.2 :=
    measurable_prequotientMomentum.comp measurable_subtype_coe
  exact h1.prodMk (h2.prodMk h3)

/-- **The class of a graph phase point is Borel.** -/
theorem measurable_graphClass : Measurable (graphClass V S) :=
  (measurable_quotientMap (V := V) S).comp Γ.measurable_graphPoint

/-- **The outgoing representative of a quotient point is Borel** (Lemma IV.4). -/
theorem measurable_rep : Measurable (rep V S) :=
  measurable_subtype_coe.comp (measurable_outgoingChart (V := V) S)

/-- The coordinates of the outgoing representative are a Borel function of the quotient point. -/
theorem measurable_repPair :
    Measurable fun z : ScatteringPhaseSpace (V := V) S =>
      (((rep V S z).1.1, (rep V S z).1.2.1) : Γ.Edge × ℝ × ℝ) :=
  (measurable_nonzeroPair (Γ := Γ)).comp (V.measurable_rep S)

section Flow

variable [Nonempty Γ.Edge]

/-- The forward flow in the coordinates of the outgoing representative. -/
theorem forwardFlow_eq_graphClass (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ) :
    (forwardFlow V S z t).1 =
      graphClass V S (V.pointTrajectory S
        (((rep V S z.1).1.1, (rep V S z.1).1.2.1) : Γ.Edge × ℝ × ℝ) t) := by
  rw [forwardFlow_val, V.trajectory_eq_pointTrajectory S (repFlight V S z) t]
  rfl

/-- **The forward flow is Borel at every time.** -/
theorem measurable_forwardFlow (t : ℝ) :
    Measurable fun z : RegularScatteringPhaseSpace (V := V) S => forwardFlow V S z t := by
  rw [measurable_comap_iff]
  change Measurable fun z : RegularScatteringPhaseSpace (V := V) S => (forwardFlow V S z t).1
  have heq : (fun z : RegularScatteringPhaseSpace (V := V) S => (forwardFlow V S z t).1) =
      fun z => graphClass V S (V.pointTrajectory S
        (((rep V S z.1).1.1, (rep V S z.1).1.2.1) : Γ.Edge × ℝ × ℝ) t) :=
    funext fun z => V.forwardFlow_eq_graphClass S z t
  rw [heq]
  exact (V.measurable_graphClass S).comp ((V.measurable_pointTrajectory S t).comp
    ((V.measurable_repPair S).comp measurable_subtype_coe))

/-- **Lemma VI.4.**  The scattered evolution `Φ_t` is Borel on the regular quotient sector, for
every real time. -/
theorem measurable_flow (t : ℝ) :
    Measurable fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z t := by
  by_cases ht : 0 ≤ t
  · have heq : (fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z t) =
        fun z => forwardFlow V S z t :=
      funext fun z => flow_of_nonneg V S z ht
    rw [heq]
    exact V.measurable_forwardFlow S t
  · have ht' : t < 0 := not_le.mp ht
    have heq : (fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z t) =
        fun z => reverseRegular (isTimeReversal_symm_timeReversed V S)
          (forwardFlow V (BorelEnergyPreservingScattering.timeReversed V S)
            (reverseRegular (BorelEnergyPreservingScattering.isTimeReversal_timeReversed V S) z)
            (-t)) :=
      funext fun z => flow_of_neg V S z ht'
    rw [heq]
    exact (measurable_reverseRegular (isTimeReversal_symm_timeReversed V S)).comp
      ((V.measurable_forwardFlow (BorelEnergyPreservingScattering.timeReversed V S) (-t)).comp
        (measurable_reverseRegular
          (BorelEnergyPreservingScattering.isTimeReversal_timeReversed V S)))

/-- **Theorem VI.5 (bimeasurability).**  For every time `t` the scattered evolution `Φ_t` is a
Borel isomorphism of the regular quotient phase space: it is a bijection with inverse `Φ_{-t}`,
and both directions are Borel. -/
noncomputable def flowMeasurableEquiv (t : ℝ) :
    RegularScatteringPhaseSpace (V := V) S ≃ᵐ RegularScatteringPhaseSpace (V := V) S where
  toEquiv := flowEquiv V S t
  measurable_toFun := V.measurable_flow S t
  measurable_invFun := V.measurable_flow S (-t)

@[simp] theorem flowMeasurableEquiv_apply (t : ℝ) (z : RegularScatteringPhaseSpace (V := V) S) :
    V.flowMeasurableEquiv S t z = flow V S z t := rfl

@[simp] theorem flowMeasurableEquiv_symm_apply (t : ℝ)
    (z : RegularScatteringPhaseSpace (V := V) S) :
    (V.flowMeasurableEquiv S t).symm z = flow V S z (-t) := rfl

/-- `Φ_t` maps Borel sets to Borel sets. -/
theorem measurableSet_image_flow (t : ℝ)
    {A : Set (RegularScatteringPhaseSpace (V := V) S)} (hA : MeasurableSet A) :
    MeasurableSet ((fun z => flow V S z t) '' A) :=
  (V.flowMeasurableEquiv S t).measurableEmbedding.measurableSet_image' hA

/-- A set is Borel exactly when its `Φ_t`-preimage is. -/
theorem measurableSet_preimage_flow_iff (t : ℝ)
    {A : Set (RegularScatteringPhaseSpace (V := V) S)} :
    MeasurableSet ((fun z => flow V S z t) ⁻¹' A) ↔ MeasurableSet A :=
  (V.flowMeasurableEquiv S t).measurableSet_preimage

end Flow

end MechanicalPotential

end HamiltonianMetricGraphs
