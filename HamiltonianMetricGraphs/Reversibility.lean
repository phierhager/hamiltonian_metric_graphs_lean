/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.BorelScattering

/-!
# Reversibility of vertex scattering

This is the algebraic content of Lemma III.5: vertex reversibility is exactly involutivity of
the fixed-speed endpoint permutation.
-/

namespace HamiltonianMetricGraphs

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

@[simp] theorem incomingMomentumReversal_symm_outgoingAtSpeed {v : Γ.Vertex}
    (η : Γ.IncidentEnds v) (r : PositiveSpeed) :
    (Γ.incomingMomentumReversal v).symm (Γ.outgoingAtSpeed η r) = Γ.incomingAtSpeed η r := by
  apply Subtype.ext
  rcases η with ⟨⟨e, b⟩, hη⟩
  cases b <;> simp [incomingMomentumReversal, incomingAtSpeed, outgoingAtSpeed, EdgeEnd.sign]

@[simp] theorem incomingMomentumReversal_incomingAtSpeed {v : Γ.Vertex}
    (η : Γ.IncidentEnds v) (r : PositiveSpeed) :
    Γ.incomingMomentumReversal v (Γ.incomingAtSpeed η r) = Γ.outgoingAtSpeed η r := by
  apply Subtype.ext
  rcases η with ⟨⟨e, b⟩, hη⟩
  cases b <;> simp [incomingMomentumReversal, incomingAtSpeed, outgoingAtSpeed, EdgeEnd.sign]

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

namespace EnergyPreservingScattering

variable (S : EnergyPreservingScattering V)

/-- The paper's momentum-reversal compatibility condition, with both sides regarded as maps
from outgoing to incoming boundary covectors. -/
def IsReversible : Prop := ∀ v : Γ.Vertex,
  (S.map v).symm = (Γ.incomingMomentumReversal v).symm.trans
    ((S.map v).trans (Γ.incomingMomentumReversal v).symm)

theorem reversible_speedEndpoint_involutive (hS : S.IsReversible) (v : Γ.Vertex)
    (η : Γ.IncidentEnds v) (r : FiniteMetricGraph.PositiveSpeed) :
    EnergyPreservingScattering.speedEndpoint V S v
      (EnergyPreservingScattering.speedEndpoint V S v η r) r = η := by
  let F := EnergyPreservingScattering.speedEndpoint V S
  let β := Γ.outgoingAtSpeed (F v η r) r
  have hleft : (S.map v).symm β = Γ.incomingAtSpeed η r := by
    change (S.map v).symm (Γ.outgoingAtSpeed (F v η r) r) = _
    rw [← EnergyPreservingScattering.speed_representation V S v η r]
    exact (S.map v).symm_apply_apply _
  have hright : (S.map v).symm β = Γ.incomingAtSpeed (F v (F v η r) r) r := by
    have h := congrArg (fun e : Γ.OutgoingBoundary v ≃ Γ.IncomingBoundary v => e β) (hS v)
    change (S.map v).symm β = _ at h
    simpa [β, F, Equiv.trans_apply,
      EnergyPreservingScattering.speed_representation] using h
  have hin : Γ.incomingAtSpeed η r = Γ.incomingAtSpeed (F v (F v η r) r) r :=
    hleft.symm.trans hright
  have hgerm := congrArg (fun α : Γ.IncomingBoundary v => α.1.germ) hin
  exact Subtype.ext (by simpa using hgerm.symm)

/-- Lemma III.5: reversibility is equivalent to the endpoint permutation at every positive speed
being an involution. -/
theorem reversible_iff_speedEndpoint_involutive : S.IsReversible ↔
    ∀ (v : Γ.Vertex) (η : Γ.IncidentEnds v) (r : FiniteMetricGraph.PositiveSpeed),
      EnergyPreservingScattering.speedEndpoint V S v
        (EnergyPreservingScattering.speedEndpoint V S v η r) r = η := by
  constructor
  · intro hS v η r
    exact EnergyPreservingScattering.reversible_speedEndpoint_involutive V S hS v η r
  · intro hF v
    ext β
    let η : Γ.IncidentEnds v := ⟨β.1.germ, β.2.1⟩
    let r : FiniteMetricGraph.PositiveSpeed := ⟨|β.1.momentum|,
      abs_pos.mpr β.1.momentum_ne_zero⟩
    have hβ : β = Γ.outgoingAtSpeed η r :=
      FiniteMetricGraph.outgoing_eq_outgoingAtSpeed Γ β
    have hscatter : S.map v (Γ.incomingAtSpeed
        (EnergyPreservingScattering.speedEndpoint V S v η r) r) = β := by
      rw [EnergyPreservingScattering.speed_representation]
      rw [hF]
      exact hβ.symm
    have hleft : (S.map v).symm β =
        Γ.incomingAtSpeed (EnergyPreservingScattering.speedEndpoint V S v η r) r := by
      rw [← hscatter]
      exact (S.map v).symm_apply_apply _
    rw [hleft]
    rw [hβ]
    simp only [Equiv.trans_apply,
      FiniteMetricGraph.incomingMomentumReversal_symm_outgoingAtSpeed]
    rw [EnergyPreservingScattering.speed_representation]
    simp [FiniteMetricGraph.incomingMomentumReversal_symm_outgoingAtSpeed]

end EnergyPreservingScattering
end MechanicalPotential
end HamiltonianMetricGraphs
