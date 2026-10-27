/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Basic

/-!
# Speed-independent involutive routing laws

The restricted microscopic-realization theorem uses deterministic vertex routing that depends
only on the incoming edge-end, not on the speed: at every vertex `v` a map
`F_v : IncidentEnds v → IncidentEnds v` with `F_v ∘ F_v = id`.  This file records that notion,
the induced map on endpoint germs, and the departure momentum: the arriving speed is kept and
the momentum is oriented into the routed edge.

Mathematical proof step: this is the combinatorial input "speed-independent reversible routing
law `F_v` with `F_v² = id`" of the theorem statement.
-/

namespace HamiltonianMetricGraphs

open FiniteMetricGraph

/-- A speed-independent reversible routing law: at every vertex an involution of the finite set
of incident edge-ends.  Speed independence is built in (there is no speed argument) and
reversibility is the involution axiom `F_v² = id`. -/
structure RoutingLaw (Γ : FiniteMetricGraph) where
  route : ∀ v : Γ.Vertex, Γ.IncidentEnds v → Γ.IncidentEnds v
  route_route : ∀ (v : Γ.Vertex) (η : Γ.IncidentEnds v), route v (route v η) = η

namespace RoutingLaw

variable {Γ : FiniteMetricGraph} (F : RoutingLaw Γ)

theorem route_involutive (v : Γ.Vertex) : Function.Involutive (F.route v) :=
  F.route_route v

theorem route_bijective (v : Γ.Vertex) : Function.Bijective (F.route v) :=
  (F.route_involutive v).bijective

/-- The routing law at a vertex, as a permutation of the incident edge-ends. -/
def routePerm (v : Γ.Vertex) : Equiv.Perm (Γ.IncidentEnds v) :=
  (F.route_involutive v).toPerm

@[simp] theorem routePerm_apply (v : Γ.Vertex) (η : Γ.IncidentEnds v) :
    F.routePerm v η = F.route v η := rfl

/-- The endpoint germ through which a particle arriving at the vertex of `η` along `η`
departs. -/
def routeGerm (η : Γ.EdgeEnd) : Γ.EdgeEnd := (F.route η.vertex ⟨η, rfl⟩).1

/-- The routed germ is incident to the same vertex. -/
theorem routeGerm_vertex (η : Γ.EdgeEnd) : (F.routeGerm η).vertex = η.vertex :=
  (F.route η.vertex ⟨η, rfl⟩).2

/-- Routing an incident end and then forgetting the incidence proof is `routeGerm`. -/
theorem route_fst_eq_routeGerm {v : Γ.Vertex} (ξ : Γ.IncidentEnds v) :
    (F.route v ξ).1 = F.routeGerm ξ.1 := by
  obtain ⟨η, hη⟩ := ξ
  subst hη
  rfl

/-- The germ-level form of `F_v² = id`. -/
theorem routeGerm_routeGerm (η : Γ.EdgeEnd) : F.routeGerm (F.routeGerm η) = η := by
  have h := F.route_fst_eq_routeGerm (F.route η.vertex ⟨η, rfl⟩)
  rw [F.route_route] at h
  exact h.symm

theorem routeGerm_involutive : Function.Involutive F.routeGerm :=
  F.routeGerm_routeGerm

theorem routeGerm_injective : Function.Injective F.routeGerm :=
  F.routeGerm_involutive.injective

/-- The longitudinal momentum with which a particle arriving with momentum `p` departs along
the routed germ: the same speed `|p|`, oriented into the routed edge (the outgoing convention
`σ(ζ) p < 0` of the paper). -/
def departureMomentum (η : Γ.EdgeEnd) (p : ℝ) : ℝ := -(F.routeGerm η).sign * |p|

theorem edgeEnd_abs_sign (η : Γ.EdgeEnd) : |EdgeEnd.sign Γ η| = 1 := by
  rcases η with ⟨e, b⟩
  cases b <;> simp [EdgeEnd.sign]

/-- The departure momentum is outgoing at the routed germ: `σ(ζ) · p_out = -|p| < 0`. -/
theorem sign_mul_departureMomentum (η : Γ.EdgeEnd) (p : ℝ) :
    (F.routeGerm η).sign * F.departureMomentum η p = -|p| := by
  unfold departureMomentum
  have h := Γ.edgeEnd_sign_sq (F.routeGerm η)
  calc (F.routeGerm η).sign * (-(F.routeGerm η).sign * |p|)
      = -((F.routeGerm η).sign ^ 2) * |p| := by ring
    _ = -|p| := by rw [h]; ring

/-- Speed is preserved through the vertex. -/
theorem abs_departureMomentum (η : Γ.EdgeEnd) (p : ℝ) :
    |F.departureMomentum η p| = |p| := by
  unfold departureMomentum
  rw [abs_mul, abs_neg, edgeEnd_abs_sign, one_mul, abs_abs]

theorem departureMomentum_sq (η : Γ.EdgeEnd) (p : ℝ) :
    F.departureMomentum η p ^ 2 = p ^ 2 := by
  rw [← sq_abs (F.departureMomentum η p), abs_departureMomentum, sq_abs]

theorem departureMomentum_ne_zero (η : Γ.EdgeEnd) {p : ℝ} (hp : p ≠ 0) :
    F.departureMomentum η p ≠ 0 := by
  intro h
  have := F.abs_departureMomentum η p
  rw [h, abs_zero] at this
  exact hp (abs_eq_zero.mp this.symm)

/-- The departure momentum depends on the arriving momentum only through its absolute value:
this is the speed-independence of the routing law in momentum form. -/
theorem departureMomentum_abs (η : Γ.EdgeEnd) (p : ℝ) :
    F.departureMomentum η |p| = F.departureMomentum η p := by
  unfold departureMomentum
  rw [abs_abs]

end RoutingLaw

/-- Total reflection: every germ is routed back to itself.  It is the simplest involutive routing
law and is available on every finite metric graph. -/
def RoutingLaw.reflection (Γ : FiniteMetricGraph) : RoutingLaw Γ where
  route _ η := η
  route_route _ _ := rfl

@[simp] theorem RoutingLaw.reflection_routeGerm (Γ : FiniteMetricGraph) (η : Γ.EdgeEnd) :
    (RoutingLaw.reflection Γ).routeGerm η = η := rfl

end HamiltonianMetricGraphs
