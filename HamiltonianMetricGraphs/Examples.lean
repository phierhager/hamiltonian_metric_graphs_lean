/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.QuotientReversal

/-!
# Basic scattering examples

These examples exercise the paper's endpoint-sign convention independently of the global-flow
construction.  The reflection law is available on every finite metric graph and every mechanical
potential.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- Reflection reverses momentum at each vertex, independently of the incident endpoint. -/
noncomputable def reflectionScattering : BorelEnergyPreservingScattering V where
  map v := Γ.incomingMomentumReversalMeasurableEquiv v
  preserves_energy _ α := V.boundaryEnergy_momentumReversal α

/-- Reflection satisfies the paper's reversible-scattering condition. -/
theorem reflectionScattering_reversible :
    (reflectionScattering V).toEnergyPreservingScattering.IsReversible := by
  intro v
  ext α
  change (Γ.incomingMomentumReversal v).symm α =
    (Γ.incomingMomentumReversal v).symm
      (Γ.incomingMomentumReversal v ((Γ.incomingMomentumReversal v).symm α))
  simp

/-- Consequently every fixed-speed endpoint permutation for reflection is an involution. -/
theorem reflectionScattering_speedEndpoint_involutive (v : Γ.Vertex)
    (η : Γ.IncidentEnds v) (r : FiniteMetricGraph.PositiveSpeed) :
    EnergyPreservingScattering.speedEndpoint V
      (reflectionScattering V).toEnergyPreservingScattering v
      (EnergyPreservingScattering.speedEndpoint V
        (reflectionScattering V).toEnergyPreservingScattering v η r) r = η :=
  EnergyPreservingScattering.reversible_speedEndpoint_involutive V
    (reflectionScattering V).toEnergyPreservingScattering
    (reflectionScattering_reversible V) v η r

end MechanicalPotential
end HamiltonianMetricGraphs
