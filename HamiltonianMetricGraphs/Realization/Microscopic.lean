/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.EdgeApproximation
import HamiltonianMetricGraphs.Realization.RegularEnergy

/-!
# Thin Hamiltonian network families

The microscopic side of the realization theorem.  For every scale `ε > 0` the well-prepared
trajectory of the smooth Hamiltonian system on the thin network `M_ε` is described, after
projecting to the graph, by a hybrid chain `chain ε` whose parameters vanish as `ε → 0⁺`:

* `offset ε = O(ε)`   — the routers `J_{v,ε} = ε J_v` occupy a longitudinal length `O(ε)` of
  each incident tube;
* `dwell ε = O(ε)`    — the physical junction time `t_out^ε - t_in^ε` is `O(ε)` (the scaled
  dwell time is uniformly bounded, see `ScaledJunction.lean`);
* `odeErr ε → 0`      — thin-tube confinement: the longitudinal dynamics solves Hamilton's
  equations on the edge up to a vanishing error;
* `momErr ε → 0`      — the outgoing longitudinal momentum converges to the routed momentum
  (same speed, oriented along `F_v(η)`).

The exit channel `F_v(η)` itself is built into the chain (`HybridChain.edge_succ`); it is the
conclusion of the channel-stability lemma of `ScaledJunction.lean` for the scaled router.

**These four vanishing parameters and the chain description are the analytic hypotheses of the
theorem.**  Everything else — edge approximation, impact-time convergence, and the global
concatenation — is proved.

This file defines the family, the convergence of well-prepared initial data, and the invariant
`Matches` carried through the finite induction over impacts.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph
open scoped Topology

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ) (F : RoutingLaw Γ)

/-- A family of thin-network trajectories: for every scale `ε` a hybrid chain (the projected
longitudinal dynamics of the well-prepared microscopic trajectory), with parameters tending to
`0` as `ε → 0⁺`. -/
structure ThinNetworkFamily where
  params : ℝ → ChainParams
  chain : ∀ ε : ℝ, HybridChain V F (params ε)
  offset_tendsto : Tendsto (fun ε => (params ε).offset) (𝓝[>] 0) (𝓝 0)
  dwell_tendsto : Tendsto (fun ε => (params ε).dwell) (𝓝[>] 0) (𝓝 0)
  odeErr_tendsto : Tendsto (fun ε => (params ε).odeErr) (𝓝[>] 0) (𝓝 0)
  momErr_tendsto : Tendsto (fun ε => (params ε).momErr) (𝓝[>] 0) (𝓝 0)

namespace ThinNetworkFamily

variable {V F} (fam : ThinNetworkFamily V F) (g : GraphTrajectory V F)

/-- Well-prepared initial data converging to the initial data of the graph trajectory `g`, on
the same edge, with microscopic chains covering the time window `[0, stop N]` of `g`. -/
structure ConvergesInitially : Prop where
  edge_zero : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (fam.chain ε).edge 0 = g.edge 0
  state_zero : Tendsto (fun ε => (fam.chain ε).curve 0 0) (𝓝[>] 0) (𝓝 (g.curve 0 0))
  finalTime : ∀ᶠ ε in 𝓝[>] (0 : ℝ), g.stop g.N ≤ (fam.chain ε).stop (fam.chain ε).N

/-- The induction invariant: the microscopic chains have a flight `j` on the graph edge of
flight `j`, starting at a time and a state converging to those of the graph flight. -/
structure Matches (j : ℕ) : Prop where
  eventually : ∀ᶠ ε in 𝓝[>] (0 : ℝ), j ≤ (fam.chain ε).N ∧ (fam.chain ε).edge j = g.edge j
  start : Tendsto (fun ε => (fam.chain ε).start j) (𝓝[>] 0) (𝓝 (g.start j))
  state : Tendsto (fun ε => (fam.chain ε).curve j ((fam.chain ε).start j)) (𝓝[>] 0)
    (𝓝 (g.curve j (g.start j)))

/-- All four parameters are eventually below any positive threshold. -/
theorem eventually_params_le {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (fam.params ε).offset ≤ θ ∧ (fam.params ε).dwell ≤ θ ∧
      (fam.params ε).odeErr ≤ θ ∧ (fam.params ε).momErr ≤ θ := by
  have h1 := eventually_lt_of_tendsto_nhds_zero fam.offset_tendsto hθ
  have h2 := eventually_lt_of_tendsto_nhds_zero fam.dwell_tendsto hθ
  have h3 := eventually_lt_of_tendsto_nhds_zero fam.odeErr_tendsto hθ
  have h4 := eventually_lt_of_tendsto_nhds_zero fam.momErr_tendsto hθ
  filter_upwards [h1, h2, h3, h4] with ε h1 h2 h3 h4
  exact ⟨h1.le, h2.le, h3.le, h4.le⟩

variable {fam g}

/-- The invariant in quantitative form: for every threshold `θ > 0`, eventually the flight `j`
exists on the right edge, starts within `θ` of the graph start time, and starts within `θ` of
the graph start state. -/
theorem Matches.eventually_close {j : ℕ} (h : fam.Matches g j) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), j ≤ (fam.chain ε).N ∧ (fam.chain ε).edge j = g.edge j ∧
      |(fam.chain ε).start j - g.start j| ≤ θ ∧
      dist ((fam.chain ε).curve j ((fam.chain ε).start j)) (g.curve j (g.start j)) ≤ θ := by
  have h1 := h.eventually
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), dist ((fam.chain ε).start j) (g.start j) < θ :=
    (Metric.tendsto_nhds.mp h.start) θ hθ
  have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      dist ((fam.chain ε).curve j ((fam.chain ε).start j)) (g.curve j (g.start j)) < θ :=
    (Metric.tendsto_nhds.mp h.state) θ hθ
  filter_upwards [h1, h2, h3] with ε h1 h2 h3
  refine ⟨h1.1, h1.2, ?_, h3.le⟩
  rw [Real.dist_eq] at h2
  exact h2.le

/-- The base case of the induction: convergence of the initial data is the invariant for
flight `0`. -/
theorem matches_zero (h : fam.ConvergesInitially g) : fam.Matches g 0 where
  eventually := by
    filter_upwards [h.edge_zero] with ε hε
    exact ⟨Nat.zero_le _, hε⟩
  start := by
    have : (fun ε => (fam.chain ε).start 0) = fun _ => (0 : ℝ) := by
      funext ε; exact (fam.chain ε).start_zero
    rw [this, g.start_zero]
    exact tendsto_const_nhds
  state := by
    have : (fun ε => (fam.chain ε).curve 0 ((fam.chain ε).start 0)) =
        fun ε => (fam.chain ε).curve 0 0 := by
      funext ε; rw [(fam.chain ε).start_zero]
    rw [this, g.start_zero]
    exact h.state_zero

end ThinNetworkFamily

end MechanicalPotential
end HamiltonianMetricGraphs
