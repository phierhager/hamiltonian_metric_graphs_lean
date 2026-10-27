/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.Routing
import HamiltonianMetricGraphs.Reversibility

/-!
# Routing laws as deterministic scattering laws

A speed-independent involutive routing law is a special case of the deterministic
energy-preserving vertex scattering laws of the paper (`EnergyPreservingScattering`): the
incoming covector at speed `r` along `η` is sent to the outgoing covector at the same speed
along `F_v η`.  Its fixed-speed endpoint permutation (Proposition III.2) is `F_v` for every
speed, and the law is reversible in the sense of Lemma III.5.
-/

namespace HamiltonianMetricGraphs

open FiniteMetricGraph

namespace RoutingLaw

variable {Γ : FiniteMetricGraph} (F : RoutingLaw Γ)

/-- Incoming covectors at a vertex are sent to outgoing covectors at the same speed along the
routed edge-end. -/
def scatter (v : Γ.Vertex) (α : Γ.IncomingBoundary v) : Γ.OutgoingBoundary v :=
  Γ.outgoingAtSpeed (F.route v ⟨α.1.germ, α.2.1⟩)
    ⟨|α.1.momentum|, abs_pos.mpr α.1.momentum_ne_zero⟩

/-- The inverse: outgoing covectors are sent back to incoming ones along the routed end. -/
def unscatter (v : Γ.Vertex) (β : Γ.OutgoingBoundary v) : Γ.IncomingBoundary v :=
  Γ.incomingAtSpeed (F.route v ⟨β.1.germ, β.2.1⟩)
    ⟨|β.1.momentum|, abs_pos.mpr β.1.momentum_ne_zero⟩

theorem unscatter_scatter (v : Γ.Vertex) (α : Γ.IncomingBoundary v) :
    F.unscatter v (F.scatter v α) = α := by
  unfold unscatter scatter
  set ξ := F.route v ⟨α.1.germ, α.2.1⟩ with hξ
  set r : PositiveSpeed := ⟨|α.1.momentum|, abs_pos.mpr α.1.momentum_ne_zero⟩ with hr
  conv_rhs => rw [Γ.incoming_eq_incomingAtSpeed α]
  congr 1
  · have h1 : (⟨(Γ.outgoingAtSpeed ξ r).1.germ, (Γ.outgoingAtSpeed ξ r).2.1⟩ :
        Γ.IncidentEnds v) = ξ := Subtype.ext rfl
    rw [h1, hξ, F.route_route]
  · apply Subtype.ext
    change |(Γ.outgoingAtSpeed ξ r).1.momentum| = |α.1.momentum|
    rw [outgoingAtSpeed_momentum, abs_neg, abs_mul, edgeEnd_abs_sign, one_mul, hr]
    exact abs_abs _

theorem scatter_unscatter (v : Γ.Vertex) (β : Γ.OutgoingBoundary v) :
    F.scatter v (F.unscatter v β) = β := by
  unfold unscatter scatter
  set ξ := F.route v ⟨β.1.germ, β.2.1⟩ with hξ
  set r : PositiveSpeed := ⟨|β.1.momentum|, abs_pos.mpr β.1.momentum_ne_zero⟩ with hr
  conv_rhs => rw [Γ.outgoing_eq_outgoingAtSpeed β]
  congr 1
  · have h1 : (⟨(Γ.incomingAtSpeed ξ r).1.germ, (Γ.incomingAtSpeed ξ r).2.1⟩ :
        Γ.IncidentEnds v) = ξ := Subtype.ext rfl
    rw [h1, hξ, F.route_route]
  · apply Subtype.ext
    change |(Γ.incomingAtSpeed ξ r).1.momentum| = |β.1.momentum|
    rw [incomingAtSpeed_momentum, abs_mul, edgeEnd_abs_sign, one_mul, hr]
    exact abs_abs _

/-- The routing law as a bijection between incoming and outgoing covectors at a vertex. -/
def scatterEquiv (v : Γ.Vertex) : Γ.IncomingBoundary v ≃ Γ.OutgoingBoundary v where
  toFun := F.scatter v
  invFun := F.unscatter v
  left_inv := F.unscatter_scatter v
  right_inv := F.scatter_unscatter v

/-- **A routing law is an energy-preserving deterministic scattering law** in the sense of the
paper: the kinetic energy is preserved because the speed is. -/
def toScattering (V : MechanicalPotential Γ) :
    MechanicalPotential.EnergyPreservingScattering V where
  map := F.scatterEquiv
  preserves_energy v α := by
    change V.boundaryEnergy (F.scatter v α).1 = V.boundaryEnergy α.1
    unfold scatter
    rw [V.boundaryEnergy_outgoingAtSpeed]
    conv_rhs => rw [Γ.incoming_eq_incomingAtSpeed α]
    rw [V.boundaryEnergy_incomingAtSpeed]

/-- **Proposition III.2 for routing laws.**  The fixed-speed endpoint permutation of the
scattering law induced by `F` is `F_v` itself, for every speed: the law is speed-independent. -/
theorem speedEndpoint_toScattering (V : MechanicalPotential Γ) (v : Γ.Vertex)
    (η : Γ.IncidentEnds v) (r : PositiveSpeed) :
    MechanicalPotential.EnergyPreservingScattering.speedEndpoint V (F.toScattering V) v η r =
      F.route v η := by
  apply Subtype.ext
  change (F.scatter v (Γ.incomingAtSpeed η r)).1.germ = (F.route v η).1
  unfold scatter
  rw [outgoingAtSpeed_end]
  have h1 : (⟨(Γ.incomingAtSpeed η r).1.germ, (Γ.incomingAtSpeed η r).2.1⟩ :
      Γ.IncidentEnds v) = η := Subtype.ext rfl
  rw [h1]

/-- **Lemma III.5 for routing laws.**  The induced scattering law is reversible (compatible
with momentum reversal): this is exactly the involutivity `F_v² = id`. -/
theorem toScattering_isReversible (V : MechanicalPotential Γ) :
    (F.toScattering V).IsReversible := by
  intro v
  ext β
  change F.unscatter v β = (Γ.incomingMomentumReversal v).symm
    (F.scatter v ((Γ.incomingMomentumReversal v).symm β))
  apply Subtype.ext
  apply BoundaryCovector.ext
  · rfl
  · change EdgeEnd.sign Γ (F.route v ⟨β.1.germ, β.2.1⟩).1 * |β.1.momentum| =
      -(-(EdgeEnd.sign Γ (F.route v ⟨β.1.germ, β.2.1⟩).1 * |-β.1.momentum|))
    rw [neg_neg, abs_neg]

end RoutingLaw

end HamiltonianMetricGraphs
