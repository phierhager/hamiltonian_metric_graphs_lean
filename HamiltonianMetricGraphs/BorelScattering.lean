/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Measurable

/-!
# Borel energy-preserving scattering laws

This packages exactly the vertex datum in the paper: a deterministic Borel isomorphism from
incoming to outgoing nonzero covectors which preserves boundary energy.
-/

namespace HamiltonianMetricGraphs

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

theorem measurable_incomingMomentumReversal (v : Γ.Vertex) :
    Measurable (Γ.incomingMomentumReversal v) := by
  rw [measurable_comap_iff, measurable_comap_iff]
  change Measurable (fun α : Γ.IncomingBoundary v => (α.1.germ, -α.1.momentum))
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_boundary_germ Γ).comp measurable_subtype_coe
  · exact ((measurable_boundary_momentum Γ).comp measurable_subtype_coe).neg

theorem measurable_incomingMomentumReversal_symm (v : Γ.Vertex) :
    Measurable (Γ.incomingMomentumReversal v).symm := by
  rw [measurable_comap_iff, measurable_comap_iff]
  change Measurable (fun α : Γ.OutgoingBoundary v => (α.1.germ, -α.1.momentum))
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_boundary_germ Γ).comp measurable_subtype_coe
  · exact ((measurable_boundary_momentum Γ).comp measurable_subtype_coe).neg

/-- Momentum reversal is a Borel isomorphism of the incoming and outgoing boundary sections. -/
noncomputable def incomingMomentumReversalMeasurableEquiv (v : Γ.Vertex) :
    Γ.IncomingBoundary v ≃ᵐ Γ.OutgoingBoundary v where
  toEquiv := Γ.incomingMomentumReversal v
  measurable_toFun := Γ.measurable_incomingMomentumReversal v
  measurable_invFun := Γ.measurable_incomingMomentumReversal_symm v

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- The full vertex-scattering datum of the paper. -/
structure BorelEnergyPreservingScattering where
  map : ∀ v : Γ.Vertex, Γ.IncomingBoundary v ≃ᵐ Γ.OutgoingBoundary v
  preserves_energy : ∀ (v : Γ.Vertex) (α : Γ.IncomingBoundary v),
    V.boundaryEnergy (map v α).1 = V.boundaryEnergy α.1

namespace BorelEnergyPreservingScattering

variable (S : BorelEnergyPreservingScattering V)

/-- Forgetting Borel measurability recovers the algebraic scattering law used in Proposition
III.2. -/
def toEnergyPreservingScattering : EnergyPreservingScattering V where
  map v := (S.map v).toEquiv
  preserves_energy := S.preserves_energy

theorem measurable_map (v : Γ.Vertex) : Measurable (S.map v) :=
  (S.map v).measurable_toFun

/-- Scattering preserves the boundary speed `|momentum|`: energy conservation at a fixed vertex
forces equal squared momenta.  This fixed-speed property is the core of the flux-measure
preservation (Lemma III.7). -/
theorem scattered_speed_eq (v : Γ.Vertex) (α : Γ.IncomingBoundary v) :
    |(S.map v α).1.momentum| = |α.1.momentum| := by
  have hE := S.preserves_energy v α
  unfold MechanicalPotential.boundaryEnergy at hE
  rw [(S.map v α).2.1, α.2.1] at hE
  have hsq : (S.map v α).1.momentum ^ 2 = α.1.momentum ^ 2 := by linarith
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs, hsq]

/-- In speed coordinates, scattering is a fixed-speed germ permutation: it sends the incoming
covector of germ `η` at speed `r` to the outgoing covector of germ `speedEndpoint η` at the same
speed `r`.  This is the exact form of Proposition III.2 needed for flux preservation (III.7). -/
theorem scattered_incomingAtSpeed (v : Γ.Vertex) (η : Γ.IncidentEnds v)
    (r : FiniteMetricGraph.PositiveSpeed) :
    S.map v (Γ.incomingAtSpeed η r) =
      Γ.outgoingAtSpeed (EnergyPreservingScattering.speedEndpoint V
        S.toEnergyPreservingScattering v η r) r :=
  EnergyPreservingScattering.speed_representation V S.toEnergyPreservingScattering v η r

/-- Inverse scattering preserves the boundary energy.  This is the energy conservation used to
build the backward trajectory by inverse scattering, without assuming reversibility. -/
theorem symm_preserves_energy (v : Γ.Vertex) (β : Γ.OutgoingBoundary v) :
    V.boundaryEnergy ((S.map v).symm β).1 = V.boundaryEnergy β.1 := by
  have hE := S.preserves_energy v ((S.map v).symm β)
  rw [(S.map v).apply_symm_apply β] at hE
  exact hE.symm

/-- Inverse scattering preserves the boundary speed `|momentum|`. -/
theorem symm_preserves_speed (v : Γ.Vertex) (β : Γ.OutgoingBoundary v) :
    |((S.map v).symm β).1.momentum| = |β.1.momentum| := by
  have hE := scattered_speed_eq (V := V) S v ((S.map v).symm β)
  rw [(S.map v).apply_symm_apply β] at hE
  exact hE.symm

theorem measurable_map_symm (v : Γ.Vertex) : Measurable (S.map v).symm :=
  (S.map v).measurable_invFun

/-- The **time-reversed scattering law**: momentum-reverse the incoming covector, apply *inverse*
scattering, then momentum-reverse again.  It is a genuine Borel energy-preserving scattering law
built from `S` using only the *invertibility* of `S` (never reversibility), and it is the law whose
forward dynamics realise the backward trajectory of `S`.  Energy preservation chains the two
momentum-reversal invariances with `symm_preserves_energy`. -/
noncomputable def timeReversed : BorelEnergyPreservingScattering V where
  map v :=
    (Γ.incomingMomentumReversalMeasurableEquiv v).trans
      ((S.map v).symm.trans (Γ.incomingMomentumReversalMeasurableEquiv v))
  preserves_energy v α := by
    have h1 : V.boundaryEnergy ((Γ.incomingMomentumReversalMeasurableEquiv v) α).1
        = V.boundaryEnergy α.1 := V.boundaryEnergy_momentumReversal α
    have h2 : V.boundaryEnergy
          ((S.map v).symm ((Γ.incomingMomentumReversalMeasurableEquiv v) α)).1
        = V.boundaryEnergy ((Γ.incomingMomentumReversalMeasurableEquiv v) α).1 :=
      symm_preserves_energy (V := V) S v _
    have h3 : V.boundaryEnergy ((Γ.incomingMomentumReversalMeasurableEquiv v)
            ((S.map v).symm ((Γ.incomingMomentumReversalMeasurableEquiv v) α))).1
        = V.boundaryEnergy ((S.map v).symm
            ((Γ.incomingMomentumReversalMeasurableEquiv v) α)).1 :=
      V.boundaryEnergy_momentumReversal _
    simpa only [MeasurableEquiv.trans_apply] using h3.trans (h2.trans h1)

/-- `timeReversed` is an involution on scattering laws: time-reversing the time-reversed dynamics
recovers the original scattering map pointwise.  This confirms `timeReversed S` is a genuine
dynamical inverse of `S`, and it underlies the group law `Φ(-t) = (Φ t)⁻¹`. -/
theorem timeReversed_timeReversed_apply (v : Γ.Vertex) (α : Γ.IncomingBoundary v) :
    ((timeReversed V (timeReversed V S)).map v) α = (S.map v) α := by
  show (Γ.incomingMomentumReversalMeasurableEquiv v)
      (((timeReversed V S).map v).symm
        ((Γ.incomingMomentumReversalMeasurableEquiv v) α)) = (S.map v) α
  have hinner : ((timeReversed V S).map v).symm
      ((Γ.incomingMomentumReversalMeasurableEquiv v) α)
      = (Γ.incomingMomentumReversalMeasurableEquiv v).symm ((S.map v) α) := by
    apply ((timeReversed V S).map v).injective
    simp only [timeReversed, MeasurableEquiv.apply_symm_apply, MeasurableEquiv.trans_apply,
      MeasurableEquiv.symm_apply_apply]
  rw [hinner, (Γ.incomingMomentumReversalMeasurableEquiv v).apply_symm_apply]

/-- The endpoint-selection function in speed coordinates is Borel measurable. -/
theorem measurable_speedEndpoint (v : Γ.Vertex) :
    Measurable (fun x : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed =>
      EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v x.1 x.2) := by
  rw [measurable_comap_iff]
  change Measurable (fun x : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed =>
    (S.map v (Γ.incomingAtSpeed x.1 x.2)).1.germ)
  exact (FiniteMetricGraph.measurable_boundary_germ Γ).comp
    (measurable_subtype_coe.comp ((S.map v).measurable_toFun.comp
      (Γ.measurable_incomingAtSpeed v)))

/-- The coordinate fibres in Lemma III.3 are Borel for every Borel scattering law. -/
theorem measurable_speedEndpoint_fiber (v : Γ.Vertex) (η ζ : Γ.IncidentEnds v) :
    MeasurableSet {r : FiniteMetricGraph.PositiveSpeed |
      EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v η r = ζ} := by
  have hcoord : Measurable (fun r : FiniteMetricGraph.PositiveSpeed =>
      EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v η r) :=
    (BorelEnergyPreservingScattering.measurable_speedEndpoint V S v).comp
      (Measurable.prodMk measurable_const measurable_id)
  exact hcoord (MeasurableSet.singleton ζ)

end BorelEnergyPreservingScattering
end MechanicalPotential
end HamiltonianMetricGraphs
