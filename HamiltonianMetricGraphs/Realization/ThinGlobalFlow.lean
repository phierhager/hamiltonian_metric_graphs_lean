/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.GraphFlow
import HamiltonianMetricGraphs.Realization.ThinLimit

/-!
# The thin-junction limit as convergence to the paper's global graph flow

`thin_junction_hamiltonian_limit` shows that the projected microscopic Hamiltonian trajectories
converge to a `GraphTrajectory V F` — the finite hybrid chain of the realization programme.
`GraphFlow.lean` identifies those chains with finite windows of the paper's own global metric-graph
flow

  `Φ_t^{Γ,F} = MechanicalPotential.FlightState.trajectory V (F.toBorelScattering V) a`.

Putting the two together gives the statement the physical interpretation asks for:

> if the graph Hamiltonian flow through a limiting graph state `z` exists on `[0, T]`, and the
> microscopic initial states `z_ε` are well prepared and converge to `z`, then the projected
> microscopic Hamiltonian trajectories converge to that graph-flow trajectory,
> `π_ε Φ_t^{H_ε}(z_ε) → Φ_t^{Γ,F}(z)`.

## What is assumed and what is proved

The graph flow always exists — that is `FlightState.trajectory`, which is total in `t ≥ 0` — so no
existence hypothesis is needed and none is assumed.  What *is* assumed, besides the two microscopic
hypotheses of `ThinHypotheses.lean`, is the compatibility of the limiting initial data with the
microscopic preparation:

* `hedge`, `hstate` — the flight state `a` sits at the limiting graph state `z = (q, r)` on the
  edge of the germ towards which the microscopic particle moves;
* `hgerm` — the first graph flight leaves the edge through that same germ.

The last condition is a genuine restriction only because a graph flight in a nonzero potential may
turn around and leave through the *opposite* end; it is exactly the hypothesis `g.germ 0 = x₀.germ`
built into `IsThinGraphLimit`, transported to the flow side.  For the zero potential — the setting
of the explicit models of this development — it holds automatically.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {Γ : FiniteMetricGraph}

/-- **The thin-junction limit is convergence to the paper's global graph flow.**

Let `H_ε = ½|p|² + W_ε` be a thin Hamiltonian network over `Γ` satisfying (E) and (J) for the
routing law `F` on a compact window `K ⊂ (max_Γ V, ∞)`, and let `x₀` be prepared, not arriving
microscopic initial data converging to the graph state `z = (q, r)` on the edge of the germ
`x₀.germ`.  Let `a` be a flight state at `z` whose first flight leaves through `x₀.germ`.

Then, on every finite time interval `[0, T]`, the projected microscopic Hamiltonian trajectories
converge to the paper's deterministic metric-graph flow through `z`:

  `π_ε Φ_t^{H_ε}(z_ε) ⟶ Φ_t^{Γ,F}(z)`,

where `Φ^{Γ,F}` is `FlightState.trajectory V (F.toBorelScattering V) a`, the flow of the paper's
own vertex-scattering datum induced by `F`.

The convergence itself is `ThinTrajectoryConvergesTo`, exactly as in
`thin_junction_hamiltonian_limit`; what is new here is the first conjunct, which says that the
limiting hybrid chain *is* the paper's global flow on the whole window. -/
theorem thin_junction_global_flow_limit [Nonempty Γ.Edge]
    (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (F : RoutingLaw Γ)
    (K : Set ℝ) (hK : IsCompact K) (hwin : V.IsWindowAbove K)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hEdge : N.SatisfiesEdgeReduction V K ε₀)
    (hJunction : N.JunctionScatteringConvergesTo V K F ε₀)
    (x₀ : WellPreparedInitialState N V K ε₀) (a : V.FlightState)
    (hedge : a.edge = x₀.germ.1) (hstate : a.state = (x₀.q, x₀.r))
    (hgerm : a.arrivalGerm = x₀.germ)
    (hE : V.hamiltonian a.edge a.state.1 a.state.2 ∈ K)
    (hinit : a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge))
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ g : GraphTrajectory V F,
      (∀ t ∈ Icc (0 : ℝ) (g.stop g.N),
        g.state t = FlightState.trajectory V (F.toBorelScattering V) a t) ∧
      IsThinGraphLimit x₀ g ∧ ThinTrajectoryConvergesTo N x₀ g T := by
  obtain ⟨g, hg_edge, hg_germ, hg_curve, hg_T, hg_flow⟩ :=
    FlightState.exists_graphTrajectory_of_flow F a hT
  have hlimit : IsThinGraphLimit x₀ g :=
    ⟨by rw [hg_germ, hgerm], by rw [hg_edge, hedge], by rw [hg_curve, hstate]⟩
  refine ⟨g, hg_flow, hlimit, ?_⟩
  refine thin_junction_hamiltonian_limit N V F K hK hwin hε₀ hEdge hJunction x₀ g hlimit ?_ ?_ hg_T
  · change V.hamiltonian (g.edge 0) (g.curve 0 0).1 (g.curve 0 0).2 ∈ K
    rw [hg_edge, hg_curve]
    exact hE
  · rw [hg_curve, hg_edge]
    exact hinit

/-- **The interface limitation, stated explicitly.**  The bridge above needs the flight state `a`
as an input, and a flight state carries a *witnessing physical edge segment*
(`PhysicalEdgeSegment`), i.e. a genuine short-time solution of the edge Hamiltonian system through
its initial point.  For a regular interior state that segment always exists, and
`FlightState.ofInterior` produces it; so a limiting graph state `z = (q, r)` strictly inside an
edge, at a regular energy, determines a flight state and hence a flow. -/
theorem exists_flightState_of_interior (V : MechanicalPotential Γ) {e : Γ.Edge} {z : ℝ × ℝ}
    (hz : z.1 ∈ Ioo (0 : ℝ) (Γ.length e))
    (hreg : V.hamiltonian e z.1 z.2 ∉ V.exceptionalEnergies) :
    ∃ a : V.FlightState, a.edge = e ∧ a.state = z :=
  ⟨FlightState.ofInterior (V := V) hz hreg, rfl, rfl⟩

/-- The corollary in the form the physical interpretation asks for: from a limiting graph state
`z` strictly inside an edge, at a regular energy of the window, the flow exists and the projected
microscopic trajectories converge to it. -/
theorem thin_junction_global_flow_limit_of_interior [Nonempty Γ.Edge]
    (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (F : RoutingLaw Γ)
    (K : Set ℝ) (hK : IsCompact K) (hwin : V.IsWindowAbove K)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hEdge : N.SatisfiesEdgeReduction V K ε₀)
    (hJunction : N.JunctionScatteringConvergesTo V K F ε₀)
    (x₀ : WellPreparedInitialState N V K ε₀)
    (hz : x₀.q ∈ Ioo (0 : ℝ) (Γ.length x₀.germ.1))
    (hEz : V.hamiltonian x₀.germ.1 x₀.q x₀.r ∈ K)
    (hgerm : ∀ hzz : ((x₀.q, x₀.r) : ℝ × ℝ).1 ∈ Ioo (0 : ℝ) (Γ.length x₀.germ.1),
      ∀ hr : V.hamiltonian x₀.germ.1 ((x₀.q, x₀.r) : ℝ × ℝ).1 ((x₀.q, x₀.r) : ℝ × ℝ).2 ∉
        V.exceptionalEnergies,
      (FlightState.ofInterior (V := V) (e := x₀.germ.1) (x := (x₀.q, x₀.r)) hzz hr).arrivalGerm =
        x₀.germ)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ g : GraphTrajectory V F,
      IsThinGraphLimit x₀ g ∧ ThinTrajectoryConvergesTo N x₀ g T ∧
      ∃ a : V.FlightState, a.edge = x₀.germ.1 ∧ a.state = (x₀.q, x₀.r) ∧
        ∀ t ∈ Icc (0 : ℝ) (g.stop g.N),
          g.state t = FlightState.trajectory V (F.toBorelScattering V) a t := by
  have hzz : ((x₀.q, x₀.r) : ℝ × ℝ).1 ∈ Ioo (0 : ℝ) (Γ.length x₀.germ.1) := hz
  have hr : V.hamiltonian x₀.germ.1 ((x₀.q, x₀.r) : ℝ × ℝ).1 ((x₀.q, x₀.r) : ℝ × ℝ).2 ∉
      V.exceptionalEnergies := hwin.not_mem_exceptionalEnergies _ hEz
  set a : V.FlightState := FlightState.ofInterior (V := V) hzz hr with ha
  obtain ⟨g, hflow, hlimit, hconv⟩ :=
    thin_junction_global_flow_limit N V F K hK hwin hε₀ hEdge hJunction x₀ a rfl rfl
      (hgerm hzz hr) hEz hzz hT
  exact ⟨g, hlimit, hconv, a, rfl, rfl, hflow⟩

end HamiltonianMetricGraphs
