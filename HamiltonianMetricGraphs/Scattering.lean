/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Boundary

/-!
# Deterministic energy-preserving vertex scattering

This module first records the set-theoretic core of Proposition III.2.  The Borel condition
is added in the measurable-structure layer, where the finite/discrete measurable spaces and
their subtype charts are installed explicitly.
-/

namespace HamiltonianMetricGraphs

open Set

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- Every incoming covector has a unique positive-speed incoming chart representation. -/
theorem incoming_eq_incomingAtSpeed {v : Γ.Vertex} (α : Γ.IncomingBoundary v) :
    α = Γ.incomingAtSpeed ⟨α.1.germ, α.2.1⟩ ⟨|α.1.momentum|,
      abs_pos.mpr α.1.momentum_ne_zero⟩ := by
  rcases α with ⟨⟨⟨e, b⟩, p, hp⟩, hv, hi⟩
  apply Subtype.ext
  cases b
  · have hp' : p < 0 := by
      simpa [EdgeEnd.sign] using hi
    simp [incomingAtSpeed, EdgeEnd.sign, abs_of_neg hp']
  · have hp' : 0 < p := by
      simpa [EdgeEnd.sign] using hi
    simp [incomingAtSpeed, EdgeEnd.sign, abs_of_pos hp']

/-- Every outgoing covector has a unique positive-speed outgoing chart representation. -/
theorem outgoing_eq_outgoingAtSpeed {v : Γ.Vertex} (α : Γ.OutgoingBoundary v) :
    α = Γ.outgoingAtSpeed ⟨α.1.germ, α.2.1⟩ ⟨|α.1.momentum|,
      abs_pos.mpr α.1.momentum_ne_zero⟩ := by
  rcases α with ⟨⟨⟨e, b⟩, p, hp⟩, hv, ho⟩
  apply Subtype.ext
  cases b
  · have hp' : 0 < p := by
      simpa [EdgeEnd.sign] using ho
    simp [outgoingAtSpeed, EdgeEnd.sign, abs_of_pos hp']
  · have hp' : p < 0 := by
      simpa [EdgeEnd.sign] using ho
    simp [outgoingAtSpeed, EdgeEnd.sign, abs_of_neg hp']

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

theorem boundaryEnergy_at_vertex {v : Γ.Vertex} (α : Γ.BoundaryCovector)
    (hα : α.germ.vertex = v) :
    V.boundaryEnergy α = α.momentum ^ 2 / 2 + V.vertexValue v := by
  simp [boundaryEnergy, hα]

/-- The supplied deterministic vertex law: a bijection on nonzero covectors which preserves
the mechanical boundary energy.  Borel hypotheses are deliberately kept separate from this
algebraic core and will strengthen this structure later. -/
structure EnergyPreservingScattering where
  map : ∀ v : Γ.Vertex, Γ.IncomingBoundary v ≃ Γ.OutgoingBoundary v
  preserves_energy : ∀ (v : Γ.Vertex) (α : Γ.IncomingBoundary v),
    V.boundaryEnergy (map v α).1 = V.boundaryEnergy α.1

namespace EnergyPreservingScattering

variable (S : EnergyPreservingScattering V)

/-- The endpoint selected by scattering in positive-speed coordinates. -/
def speedEndpoint (v : Γ.Vertex) (η : Γ.IncidentEnds v) (r : FiniteMetricGraph.PositiveSpeed) :
    Γ.IncidentEnds v :=
  ⟨(S.map v (Γ.incomingAtSpeed η r)).1.germ, (S.map v (Γ.incomingAtSpeed η r)).2.1⟩

theorem scattered_speed_sq (v : Γ.Vertex) (η : Γ.IncidentEnds v)
    (r : FiniteMetricGraph.PositiveSpeed) :
    (S.map v (Γ.incomingAtSpeed η r)).1.momentum ^ 2 = r.1 ^ 2 := by
  have h := S.preserves_energy v (Γ.incomingAtSpeed η r)
  rw [V.boundaryEnergy_at_vertex (S.map v (Γ.incomingAtSpeed η r)).1
      (S.map v (Γ.incomingAtSpeed η r)).2.1,
    V.boundaryEnergy_incomingAtSpeed] at h
  nlinarith

theorem scattered_speed (v : Γ.Vertex) (η : Γ.IncidentEnds v)
    (r : FiniteMetricGraph.PositiveSpeed) :
    |(S.map v (Γ.incomingAtSpeed η r)).1.momentum| = r.1 := by
  have hs := EnergyPreservingScattering.scattered_speed_sq V S v η r
  have hr : 0 < r.1 := r.2
  rw [sq_eq_sq_iff_eq_or_eq_neg] at hs
  rcases hs with h | h
  · simpa [h] using (abs_of_pos hr)
  · simpa [h] using (abs_of_neg (neg_lt_zero.mpr hr))

/-- Proposition III.2: energy preservation forces the scattering law to preserve positive
speed, leaving only a speed-dependent choice of incident endpoint. -/
theorem speed_representation (v : Γ.Vertex) (η : Γ.IncidentEnds v)
    (r : FiniteMetricGraph.PositiveSpeed) :
    S.map v (Γ.incomingAtSpeed η r) =
      Γ.outgoingAtSpeed (EnergyPreservingScattering.speedEndpoint V S v η r) r := by
  rw [Γ.outgoing_eq_outgoingAtSpeed (S.map v (Γ.incomingAtSpeed η r))]
  congr 1
  apply Subtype.ext
  exact EnergyPreservingScattering.scattered_speed V S v η r

theorem speedEndpoint_unique (F : ∀ v : Γ.Vertex, Γ.IncidentEnds v →
    FiniteMetricGraph.PositiveSpeed → Γ.IncidentEnds v)
    (hF : ∀ (v : Γ.Vertex) (η : Γ.IncidentEnds v) (r : FiniteMetricGraph.PositiveSpeed),
      S.map v (Γ.incomingAtSpeed η r) = Γ.outgoingAtSpeed (F v η r) r) :
    ∀ (v : Γ.Vertex) (η : Γ.IncidentEnds v) (r : FiniteMetricGraph.PositiveSpeed),
      F v η r = EnergyPreservingScattering.speedEndpoint V S v η r := by
  intro v η r
  have h := hF v η r
  rw [EnergyPreservingScattering.speed_representation V S v η r] at h
  have hgerm := congrArg (fun α : Γ.OutgoingBoundary v => α.1.germ) h
  exact Subtype.ext (by simpa using hgerm.symm)

/-- At a fixed speed, deterministic energy-preserving scattering is a permutation of the
finite set of endpoint germs. -/
theorem speedEndpoint_injective (v : Γ.Vertex) (r : FiniteMetricGraph.PositiveSpeed) :
    Function.Injective (fun η : Γ.IncidentEnds v =>
      EnergyPreservingScattering.speedEndpoint V S v η r) := by
  intro η ζ hηζ
  have hscatter : S.map v (Γ.incomingAtSpeed η r) = S.map v (Γ.incomingAtSpeed ζ r) := by
    rw [EnergyPreservingScattering.speed_representation V S v η r,
      EnergyPreservingScattering.speed_representation V S v ζ r]
    exact congrArg (fun ξ => Γ.outgoingAtSpeed ξ r) hηζ
  have hin := (S.map v).injective hscatter
  have hgerm := congrArg (fun α : Γ.IncomingBoundary v => α.1.germ) hin
  exact Subtype.ext (by simpa using hgerm)

theorem speedEndpoint_bijective (v : Γ.Vertex) (r : FiniteMetricGraph.PositiveSpeed) :
    Function.Bijective (fun η : Γ.IncidentEnds v =>
      EnergyPreservingScattering.speedEndpoint V S v η r) := by
  refine ⟨EnergyPreservingScattering.speedEndpoint_injective V S v r, ?_⟩
  exact Finite.injective_iff_surjective.mp
    (EnergyPreservingScattering.speedEndpoint_injective V S v r)

/-- The fixed-speed permutation from Proposition III.2. -/
noncomputable def speedPermutation (v : Γ.Vertex) (r : FiniteMetricGraph.PositiveSpeed) :
    Equiv.Perm (Γ.IncidentEnds v) :=
  Equiv.ofBijective (fun η => EnergyPreservingScattering.speedEndpoint V S v η r)
    (EnergyPreservingScattering.speedEndpoint_bijective V S v r)

@[simp] theorem speedPermutation_apply (v : Γ.Vertex) (r : FiniteMetricGraph.PositiveSpeed)
    (η : Γ.IncidentEnds v) :
    EnergyPreservingScattering.speedPermutation V S v r η =
      EnergyPreservingScattering.speedEndpoint V S v η r := rfl

end EnergyPreservingScattering
end MechanicalPotential
end HamiltonianMetricGraphs
