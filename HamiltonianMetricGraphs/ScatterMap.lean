/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.QuotientPhaseSpace
import HamiltonianMetricGraphs.StandardBorelQuotient

/-!
# A measurable global scattering map on boundary covectors

Lemma IV.4 needs the outgoing chart of the scattering quotient to be a `MeasurableEquiv`, which comes
from a **measurable representative map**.  The core ingredient is a single Borel map
`scatterCovector : BoundaryCovector → BoundaryCovector` that scatters a genuinely incoming covector
through `S` at its own vertex and is the identity otherwise.  Measurability is obtained by a finite
germ dispatch (`EdgeEnd` is a `Fintype`): for each fixed germ the vertex is constant and the map is
the fixed `MeasurableEquiv` `S.map v` precomposed with a measurable covector selection.
-/

namespace HamiltonianMetricGraphs

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- A canonical incoming covector at the vertex of a germ (unit speed), used only as a junk value in
the total scattering selection below. -/
noncomputable def junkIncoming (η : Γ.EdgeEnd) : Γ.IncomingBoundary η.vertex :=
  Γ.incomingAtSpeed ⟨η, rfl⟩ ⟨1, Set.mem_Ioi.mpr one_pos⟩

/-- Total selection sending `α` to itself (viewed as an incoming covector at the vertex of `η`) when
it is genuinely incoming there, and to the junk covector otherwise. -/
noncomputable def toIncomingOrJunk (η : Γ.EdgeEnd) (α : Γ.BoundaryCovector) :
    Γ.IncomingBoundary η.vertex :=
  if h : α.germ.vertex = η.vertex ∧ α.germ.sign * α.momentum > 0 then ⟨α, h⟩
  else Γ.junkIncoming η

theorem toIncomingOrJunk_val (η : Γ.EdgeEnd) (α : Γ.BoundaryCovector) :
    (Γ.toIncomingOrJunk η α).1 =
      if α.germ.vertex = η.vertex ∧ α.germ.sign * α.momentum > 0 then α
      else (Γ.junkIncoming η).1 := by
  unfold toIncomingOrJunk
  split <;> rfl

/-- The boundary flag of a germ is recovered from whether its coordinate equals the edge length. -/
theorem edgeEnd_bool_of_coordinate (η : Γ.EdgeEnd) :
    (if FiniteMetricGraph.EdgeEnd.coordinate Γ η = Γ.length η.1 then true else false) = η.2 := by
  rcases η with ⟨e, b⟩
  cases b
  · have h0 : FiniteMetricGraph.EdgeEnd.coordinate Γ (e, false) = 0 := rfl
    rw [h0, if_neg (Γ.length_pos e).ne]
  · have h1 : FiniteMetricGraph.EdgeEnd.coordinate Γ (e, true) = Γ.length e := rfl
    rw [h1, if_pos rfl]

theorem measurable_germ_vertex :
    Measurable (fun α : Γ.BoundaryCovector => α.germ.vertex) :=
  (measurable_from_top (f := fun η : Γ.EdgeEnd => η.vertex)).comp (Γ.measurable_boundary_germ)

theorem measurable_germ_sign :
    Measurable (fun α : Γ.BoundaryCovector => α.germ.sign) :=
  (measurable_from_top (f := fun η : Γ.EdgeEnd => FiniteMetricGraph.EdgeEnd.sign Γ η)).comp
    (Γ.measurable_boundary_germ)

theorem measurableSet_incomingAt (η : Γ.EdgeEnd) :
    MeasurableSet {α : Γ.BoundaryCovector |
      α.germ.vertex = η.vertex ∧ α.germ.sign * α.momentum > 0} := by
  have h1 : MeasurableSet {α : Γ.BoundaryCovector | α.germ.vertex = η.vertex} :=
    (Γ.measurable_germ_vertex) (measurableSet_singleton η.vertex)
  have h2 : MeasurableSet {α : Γ.BoundaryCovector | α.germ.sign * α.momentum > 0} :=
    measurableSet_lt measurable_const
      ((Γ.measurable_germ_sign).mul (Γ.measurable_boundary_momentum))
  exact h1.inter h2

theorem measurable_toIncomingOrJunk (η : Γ.EdgeEnd) :
    Measurable (fun α : Γ.BoundaryCovector => Γ.toIncomingOrJunk η α) := by
  rw [measurable_comap_iff]
  have hval : (fun α : Γ.BoundaryCovector => (Γ.toIncomingOrJunk η α).1)
      = {α : Γ.BoundaryCovector |
          α.germ.vertex = η.vertex ∧ α.germ.sign * α.momentum > 0}.piecewise id
          (fun _ => (Γ.junkIncoming η).1) := by
    funext α
    rw [toIncomingOrJunk_val]
    rfl
  change Measurable (fun α : Γ.BoundaryCovector => (Γ.toIncomingOrJunk η α).1)
  rw [hval]
  exact Measurable.piecewise (Γ.measurableSet_incomingAt η) measurable_id measurable_const

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-- Scatter a covector through `S` at the vertex of a fixed germ (junk-guarded so it is total). -/
noncomputable def scatterAt (η : Γ.EdgeEnd) (α : Γ.BoundaryCovector) : Γ.BoundaryCovector :=
  (S.map η.vertex (Γ.toIncomingOrJunk η α)).1

theorem measurable_scatterAt (η : Γ.EdgeEnd) :
    Measurable (fun α : Γ.BoundaryCovector => scatterAt (V := V) S η α) :=
  measurable_subtype_coe.comp ((S.map η.vertex).measurable.comp (Γ.measurable_toIncomingOrJunk η))

/-- The global scattering map on covectors: scatter a genuinely incoming covector at its own vertex,
and leave everything else fixed. -/
noncomputable def scatterCovector (α : Γ.BoundaryCovector) : Γ.BoundaryCovector :=
  if α.germ.sign * α.momentum > 0 then scatterAt (V := V) S α.germ α else α

theorem measurable_scatterCovector :
    Measurable (fun α : Γ.BoundaryCovector => scatterCovector (V := V) S α) := by
  have hthen : Measurable (fun α : Γ.BoundaryCovector => scatterAt (V := V) S α.germ α) := by
    have hprod : Measurable (fun p : Γ.EdgeEnd × Γ.BoundaryCovector =>
        scatterAt (V := V) S p.1 p.2) :=
      measurable_from_prod_countable_right (fun η => measurable_scatterAt (V := V) S η)
    exact hprod.comp ((Γ.measurable_boundary_germ).prodMk measurable_id)
  refine Measurable.ite ?_ hthen measurable_id
  exact measurableSet_lt measurable_const
    ((Γ.measurable_germ_sign).mul (Γ.measurable_boundary_momentum))

/-- On a genuine incoming covector, the global scattering map is exactly the vertex scattering at
the covector's own vertex. -/
theorem scatterCovector_incoming {α : Γ.BoundaryCovector}
    (hpos : α.germ.sign * α.momentum > 0) :
    scatterCovector (V := V) S α
      = (S.map α.germ.vertex ⟨α, ⟨rfl, hpos⟩⟩).1 := by
  have hti : Γ.toIncomingOrJunk α.germ α = ⟨α, ⟨rfl, hpos⟩⟩ := by
    apply Subtype.ext
    rw [Γ.toIncomingOrJunk_val, if_pos ⟨rfl, hpos⟩]
  unfold scatterCovector scatterAt
  rw [if_pos hpos, hti]

/-- Reconstruction inverts the covector embedding: for a genuine boundary covector, reading off the
germ (edge + boundary flag) and momentum of its prequotient point recovers the covector exactly. -/
theorem pointToCovector_toNonzero (α : Γ.BoundaryCovector) :
    pointToCovector (Γ := Γ) (α.toNonzeroPrequotientPhase Γ) = α := by
  apply FiniteMetricGraph.BoundaryCovector.ext
  · show ((α.germ.1, if FiniteMetricGraph.EdgeEnd.coordinate Γ α.germ = Γ.length α.germ.1
        then true else false) : Γ.EdgeEnd) = α.germ
    rw [Γ.edgeEnd_bool_of_coordinate α.germ]
  · show (if α.momentum = 0 then (1 : ℝ) else α.momentum) = α.momentum
    exact if_neg α.momentum_ne_zero

/-- The outgoing-representative map on prequotient points: an incoming point is scattered forward to
its outgoing image, every other point is left fixed.  It is Borel measurable, and (proved elsewhere)
selects exactly the outgoing representative of each scattering class. -/
noncomputable def repOf (x : Γ.NonzeroPrequotientPhase) : Γ.NonzeroPrequotientPhase := by
  classical
  exact if IsIncomingPoint (V := V) S x then
    (scatterCovector (V := V) S (pointToCovector (Γ := Γ) x)).toNonzeroPrequotientPhase Γ
  else x

theorem measurable_repOf : Measurable (repOf (V := V) S) := by
  classical
  have hpiece : repOf (V := V) S
      = {x : Γ.NonzeroPrequotientPhase | IsIncomingPoint (V := V) S x}.piecewise
          (fun x => (scatterCovector (V := V) S
            (pointToCovector (Γ := Γ) x)).toNonzeroPrequotientPhase Γ)
          id := by
    funext x
    simp only [repOf, Set.piecewise, Set.mem_setOf_eq, id]
  rw [hpiece]
  exact Measurable.piecewise (measurableSet_isIncomingPoint (V := V) S)
    ((Γ.measurable_toNonzeroPrequotientPhase).comp
      ((measurable_scatterCovector (V := V) S).comp (measurable_pointToCovector (Γ := Γ))))
    measurable_id

theorem repOf_of_not_incoming {x : Γ.NonzeroPrequotientPhase}
    (hx : ¬ IsIncomingPoint (V := V) S x) : repOf (V := V) S x = x := by
  unfold repOf; rw [if_neg hx]

/-- On an incoming point, `repOf` is exactly the forward scattering step. -/
theorem scatteringStep_repOf {x : Γ.NonzeroPrequotientPhase}
    (hx : IsIncomingPoint (V := V) S x) :
    scatteringStep (V := V) S x (repOf (V := V) S x) := by
  obtain ⟨v, β, hxeq⟩ := hx
  have hpos : β.1.germ.sign * β.1.momentum > 0 := β.2.2
  have hpt : pointToCovector (Γ := Γ) x = β.1 := by
    rw [hxeq]; exact pointToCovector_toNonzero β.1
  have hrep : repOf (V := V) S x
      = ((S.map β.1.germ.vertex ⟨β.1, ⟨rfl, hpos⟩⟩).1).toNonzeroPrequotientPhase Γ := by
    unfold repOf
    rw [if_pos ⟨v, β, hxeq⟩, hpt, scatterCovector_incoming (V := V) S hpos]
  exact ⟨β.1.germ.vertex, ⟨β.1, ⟨rfl, hpos⟩⟩, hxeq, hrep⟩

/-- `repOf` always lands in the outgoing representative section. -/
theorem not_isIncoming_repOf (x : Γ.NonzeroPrequotientPhase) :
    ¬ IsIncomingPoint (V := V) S (repOf (V := V) S x) := by
  by_cases hx : IsIncomingPoint (V := V) S x
  · exact scatteringStep_target_notIncoming (V := V) S (scatteringStep_repOf (V := V) S hx)
  · rw [repOf_of_not_incoming (V := V) S hx]; exact hx

/-- `repOf` selects a representative of the same scattering class. -/
theorem quotientMap_repOf (x : Γ.NonzeroPrequotientPhase) :
    quotientMap (V := V) S (repOf (V := V) S x) = quotientMap (V := V) S x := by
  by_cases hx : IsIncomingPoint (V := V) S x
  · exact (Quotient.sound
      (Relation.EqvGen.rel _ _ (scatteringStep_repOf (V := V) S hx))).symm
  · rw [repOf_of_not_incoming (V := V) S hx]

/-- The set-theoretic outgoing chart evaluated on a class equals the measurable representative. -/
theorem outgoingChart_quotientMap (x : Γ.NonzeroPrequotientPhase) :
    outgoingChart (V := V) S (quotientMap (V := V) S x)
      = ⟨repOf (V := V) S x, not_isIncoming_repOf (V := V) S x⟩ := by
  rw [outgoingChart, Equiv.symm_apply_eq]
  exact (quotientMap_repOf (V := V) S x).symm

/-- **The outgoing chart is Borel measurable (Lemma IV.4).**  Via the quotient universal property it
suffices that `outgoingChart ∘ quotientMap = repOf` (as a section), which is measurable. -/
theorem measurable_outgoingChart : Measurable (outgoingChart (V := V) S) := by
  intro A hA
  rw [measurableSet_quotient_iff]
  have hcomp : quotientMap (V := V) S ⁻¹' (outgoingChart (V := V) S ⁻¹' A)
      = (fun x => (⟨repOf (V := V) S x, not_isIncoming_repOf (V := V) S x⟩ :
          OutgoingRepresentativeSpace (V := V) S)) ⁻¹' A := by
    ext x
    simp only [Set.mem_preimage, outgoingChart_quotientMap]
  rw [hcomp]
  exact (Measurable.subtype_mk (measurable_repOf (V := V) S)) hA

/-- The outgoing representative chart of Lemma IV.4 as a genuine measurable equivalence. -/
noncomputable def outgoingChartMeasurableEquiv :
    ScatteringPhaseSpace (V := V) S ≃ᵐ OutgoingRepresentativeSpace (V := V) S where
  toEquiv := outgoingChart (V := V) S
  measurable_toFun := measurable_outgoingChart (V := V) S
  measurable_invFun := by
    change Measurable ((outgoingChart (V := V) S).symm)
    rw [outgoingChart]
    simpa using measurable_outgoingRepresentativeMap (V := V) S

/-- Consequently the scattering quotient phase space is standard Borel. -/
noncomputable instance : StandardBorelSpace (ScatteringPhaseSpace (V := V) S) :=
  standardBorelSpace_of_measurableEquiv (outgoingChartMeasurableEquiv (V := V) S)

/-- The regular energy sector of the scattering quotient — the domain of the scattered flow and of
Theorem VI.5 — is a Borel subset of the standard Borel quotient, hence itself standard Borel. -/
noncomputable instance : StandardBorelSpace (RegularScatteringPhaseSpace (V := V) S) :=
  (measurableSet_regularScatteringPhaseSpace (V := V) S).standardBorel

/-- Two prequotient points share a class iff they have the same outgoing representative. -/
theorem repOf_eq_iff (x y : Γ.NonzeroPrequotientPhase) :
    repOf (V := V) S x = repOf (V := V) S y
      ↔ quotientMap (V := V) S x = quotientMap (V := V) S y := by
  constructor
  · intro h
    rw [← quotientMap_repOf (V := V) S x, ← quotientMap_repOf (V := V) S y, h]
  · intro h
    have h2 := congrArg (outgoingChart (V := V) S) h
    rw [outgoingChart_quotientMap, outgoingChart_quotientMap] at h2
    exact congrArg Subtype.val h2

/-- `repOf` is injective on incoming points (a scattering step is determined by its target). -/
theorem repOf_injOn_incoming :
    Set.InjOn (repOf (V := V) S) {x | IsIncomingPoint (V := V) S x} := by
  intro x hx x' hx' heq
  have s1 := scatteringStep_repOf (V := V) S hx
  have s2 := scatteringStep_repOf (V := V) S hx'
  rw [← heq] at s2
  exact scatteringStep_cofunctional (V := V) S s1 s2

/-- **Lemma IV.2 (saturation measurability).**  The saturation of a Borel set under the scattering
setoid is Borel: it is `repOf ⁻¹'` of the Borel image `repOf '' A`, and that image splits into the
(identity) outgoing part and an injective-`repOf` incoming part, each Borel (Lusin--Souslin). -/
theorem measurableSet_saturation {A : Set Γ.NonzeroPrequotientPhase} (hA : MeasurableSet A) :
    MeasurableSet (quotientMap (V := V) S ⁻¹' (quotientMap (V := V) S '' A)) := by
  have hchar : quotientMap (V := V) S ⁻¹' (quotientMap (V := V) S '' A)
      = repOf (V := V) S ⁻¹' (repOf (V := V) S '' A) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨x, hxA, hxy⟩
      exact ⟨x, hxA, (repOf_eq_iff (V := V) S x y).mpr hxy⟩
    · rintro ⟨x, hxA, hxy⟩
      exact ⟨x, hxA, (repOf_eq_iff (V := V) S x y).mp hxy⟩
  rw [hchar]
  refine MeasurableSet.preimage ?_ (measurable_repOf (V := V) S)
  have hsplit : A = (A ∩ {x | IsIncomingPoint (V := V) S x})
      ∪ (A ∩ {x | ¬ IsIncomingPoint (V := V) S x}) := by
    ext x
    by_cases hx : IsIncomingPoint (V := V) S x <;> simp [hx]
  have himg : repOf (V := V) S '' A
      = (repOf (V := V) S '' (A ∩ {x | IsIncomingPoint (V := V) S x}))
        ∪ (repOf (V := V) S '' (A ∩ {x | ¬ IsIncomingPoint (V := V) S x})) := by
    rw [← Set.image_union, ← hsplit]
  rw [himg]
  refine MeasurableSet.union ?_ ?_
  · exact MeasurableSet.image_of_measurable_injOn
      (hA.inter (measurableSet_isIncomingPoint (V := V) S))
      (measurable_repOf (V := V) S)
      ((repOf_injOn_incoming (V := V) S).mono Set.inter_subset_right)
  · have hid : repOf (V := V) S '' (A ∩ {x | ¬ IsIncomingPoint (V := V) S x})
        = A ∩ {x | ¬ IsIncomingPoint (V := V) S x} := by
      ext z
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, ⟨hxA, hxni⟩, hxz⟩
        rw [repOf_of_not_incoming (V := V) S hxni] at hxz
        rw [← hxz]; exact ⟨hxA, hxni⟩
      · rintro ⟨hzA, hzni⟩
        exact ⟨z, ⟨hzA, hzni⟩, repOf_of_not_incoming (V := V) S hzni⟩
    rw [hid]
    exact hA.inter (measurableSet_isIncomingPoint (V := V) S).compl

end MechanicalPotential

end HamiltonianMetricGraphs
