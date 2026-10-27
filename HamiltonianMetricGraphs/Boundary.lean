/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Potential

/-!
# Boundary covectors and speed coordinates

The incoming convention is `σ(η) p > 0`: at the left endpoint `σ = -1`, hence an
incoming covector has negative momentum, while at the right endpoint it has positive
momentum.
-/

namespace HamiltonianMetricGraphs

open Set

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- A nonzero covector based at an endpoint germ. -/
structure BoundaryCovector where
  germ : Γ.EdgeEnd
  momentum : ℝ
  momentum_ne_zero : momentum ≠ 0

theorem BoundaryCovector.ext {α β : Γ.BoundaryCovector}
    (hgerm : α.germ = β.germ) (hmomentum : α.momentum = β.momentum) : α = β := by
  rcases α with ⟨g, p, hp⟩
  rcases β with ⟨h, q, hq⟩
  change g = h at hgerm
  change p = q at hmomentum
  subst h
  subst q
  rfl

/-- Momentum reversal as an operation on an untyped nonzero boundary covector. -/
def BoundaryCovector.momentumReversal (α : Γ.BoundaryCovector) : Γ.BoundaryCovector where
  germ := α.germ
  momentum := -α.momentum
  momentum_ne_zero := neg_ne_zero.mpr α.momentum_ne_zero

@[simp] theorem BoundaryCovector.momentumReversal_germ (α : Γ.BoundaryCovector) :
    α.momentumReversal.germ = α.germ := rfl

@[simp] theorem BoundaryCovector.momentumReversal_momentum (α : Γ.BoundaryCovector) :
    α.momentumReversal.momentum = -α.momentum := rfl

@[simp] theorem BoundaryCovector.momentumReversal_involutive (α : Γ.BoundaryCovector) :
    α.momentumReversal.momentumReversal = α := by
  cases α
  simp [BoundaryCovector.momentumReversal]

/-- Incoming nonzero boundary covectors at a vertex. -/
def IncomingBoundary (v : Γ.Vertex) :=
  {α : Γ.BoundaryCovector // α.germ.vertex = v ∧ α.germ.sign * α.momentum > 0}

/-- Outgoing nonzero boundary covectors at a vertex. -/
def OutgoingBoundary (v : Γ.Vertex) :=
  {α : Γ.BoundaryCovector // α.germ.vertex = v ∧ α.germ.sign * α.momentum < 0}

/-- Positive speed values. -/
abbrev PositiveSpeed := Set.Ioi (0 : ℝ)

theorem sign_mul_sign (η : Γ.EdgeEnd) : η.sign * η.sign = 1 := by
  nlinarith [Γ.edgeEnd_sign_sq η]

/-- The incoming covector determined by an endpoint germ and a positive speed. -/
def incomingAtSpeed {v : Γ.Vertex} (η : Γ.IncidentEnds v) (r : PositiveSpeed) :
    Γ.IncomingBoundary v := by
  refine ⟨⟨η.1, η.1.sign * r.1, ?_⟩, η.2, ?_⟩
  · exact mul_ne_zero (Γ.edgeEnd_sign_ne_zero η.1) (ne_of_gt r.2)
  · rcases η with ⟨⟨e, b⟩, hη⟩
    cases b <;> norm_num [EdgeEnd.sign] at * <;> exact r.2

/-- The outgoing covector determined by an endpoint germ and a positive speed. -/
def outgoingAtSpeed {v : Γ.Vertex} (η : Γ.IncidentEnds v) (r : PositiveSpeed) :
    Γ.OutgoingBoundary v := by
  refine ⟨⟨η.1, -(η.1.sign * r.1), ?_⟩, η.2, ?_⟩
  · exact neg_ne_zero.mpr (mul_ne_zero (Γ.edgeEnd_sign_ne_zero η.1) (ne_of_gt r.2))
  · rcases η with ⟨⟨e, b⟩, hη⟩
    cases b <;> norm_num [EdgeEnd.sign] at * <;> exact r.2

@[simp] theorem incomingAtSpeed_end {v : Γ.Vertex} (η : Γ.IncidentEnds v)
    (r : PositiveSpeed) : (Γ.incomingAtSpeed η r).1.germ = η.1 := rfl

@[simp] theorem incomingAtSpeed_momentum {v : Γ.Vertex} (η : Γ.IncidentEnds v)
    (r : PositiveSpeed) : (Γ.incomingAtSpeed η r).1.momentum = η.1.sign * r.1 := rfl

@[simp] theorem outgoingAtSpeed_end {v : Γ.Vertex} (η : Γ.IncidentEnds v)
    (r : PositiveSpeed) : (Γ.outgoingAtSpeed η r).1.germ = η.1 := rfl

@[simp] theorem outgoingAtSpeed_momentum {v : Γ.Vertex} (η : Γ.IncidentEnds v)
    (r : PositiveSpeed) : (Γ.outgoingAtSpeed η r).1.momentum = -(η.1.sign * r.1) := rfl

/-- Momentum reversal maps an incoming boundary covector to the outgoing covector at the
same endpoint germ. -/
def incomingMomentumReversal (v : Γ.Vertex) : Γ.IncomingBoundary v ≃ Γ.OutgoingBoundary v where
  toFun α := by
    refine ⟨⟨α.1.germ, -α.1.momentum, neg_ne_zero.mpr α.1.momentum_ne_zero⟩, α.2.1, ?_⟩
    rw [mul_neg]
    exact neg_lt_zero.mpr α.2.2
  invFun α := by
    refine ⟨⟨α.1.germ, -α.1.momentum, neg_ne_zero.mpr α.1.momentum_ne_zero⟩, α.2.1, ?_⟩
    rw [mul_neg]
    exact neg_pos.mpr α.2.2
  left_inv α := by
    rcases α with ⟨⟨g, p, hp⟩, hv, hi⟩
    apply Subtype.ext
    change ({ germ := g, momentum := - -p, momentum_ne_zero := _ } : Γ.BoundaryCovector) = _
    congr
    simp
  right_inv α := by
    rcases α with ⟨⟨g, p, hp⟩, hv, ho⟩
    apply Subtype.ext
    change ({ germ := g, momentum := - -p, momentum_ne_zero := _ } : Γ.BoundaryCovector) = _
    congr
    simp

@[simp] theorem incomingMomentumReversal_apply_momentum (v : Γ.Vertex)
    (α : Γ.IncomingBoundary v) : (Γ.incomingMomentumReversal v α).1.momentum = -α.1.momentum := rfl

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- The mechanical energy of a boundary covector. -/
noncomputable def boundaryEnergy (α : Γ.BoundaryCovector) : ℝ :=
  α.momentum ^ 2 / 2 + V.vertexValue α.germ.vertex

theorem boundaryEnergy_eq_edgeHamiltonian (α : Γ.BoundaryCovector) :
    V.boundaryEnergy α =
      V.hamiltonian α.germ.1 (FiniteMetricGraph.EdgeEnd.coordinate Γ α.germ) α.momentum := by
  unfold boundaryEnergy
  rw [V.endpoint_hamiltonian]

theorem boundaryEnergy_momentumReversal {v : Γ.Vertex} (α : Γ.IncomingBoundary v) :
    V.boundaryEnergy ((Γ.incomingMomentumReversal v) α).1 = V.boundaryEnergy α.1 := by
  rcases α with ⟨⟨g, p, hp⟩, hv, hi⟩
  simp [boundaryEnergy, FiniteMetricGraph.incomingMomentumReversal]

theorem boundaryEnergy_incomingAtSpeed {v : Γ.Vertex} (η : Γ.IncidentEnds v)
    (r : FiniteMetricGraph.PositiveSpeed) :
    V.boundaryEnergy (Γ.incomingAtSpeed η r).1 = r.1 ^ 2 / 2 + V.vertexValue v := by
  rcases η with ⟨⟨e, b⟩, hη⟩
  cases b <;> simp [boundaryEnergy, FiniteMetricGraph.incomingAtSpeed,
    FiniteMetricGraph.EdgeEnd.sign, hη]

theorem boundaryEnergy_outgoingAtSpeed {v : Γ.Vertex} (η : Γ.IncidentEnds v)
    (r : FiniteMetricGraph.PositiveSpeed) :
    V.boundaryEnergy (Γ.outgoingAtSpeed η r).1 = r.1 ^ 2 / 2 + V.vertexValue v := by
  rcases η with ⟨⟨e, b⟩, hη⟩
  cases b <;> simp [boundaryEnergy, FiniteMetricGraph.outgoingAtSpeed,
    FiniteMetricGraph.EdgeEnd.sign, hη]

end MechanicalPotential
end HamiltonianMetricGraphs
