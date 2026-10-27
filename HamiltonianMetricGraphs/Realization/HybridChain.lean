/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.Routing
import HamiltonianMetricGraphs.Realization.IntervalEstimates
import HamiltonianMetricGraphs.EdgeDynamics

/-!
# Hybrid chains: graph scattering trajectories and their thin-network approximants

A *hybrid chain* is a finite alternating sequence of edge flights and router passages on a
finite metric graph, described by four nonnegative parameters:

* `offset`  — the tube around an edge ends at longitudinal distance `offset` from each vertex,
              where the router region begins;
* `dwell`   — the maximal time spent inside a router;
* `odeErr`  — the tolerance in Hamilton's equations along a flight;
* `momErr`  — the tolerance in the outgoing longitudinal momentum after a passage.

The **graph scattering trajectory** is the chain with all four parameters equal to `0`
(`ChainParams.zero`): flights are exact solutions of the edge Hamiltonian system, impacts are
instantaneous, and the routing law `F` fixes the outgoing edge-end and momentum.  The projected
longitudinal dynamics of a well-prepared trajectory of the thin Hamiltonian network `M_ε` is a
chain whose parameters are `O(ε)` (respectively `o(1)`); this is how the thin-tube confinement
and the microscopic-router analysis enter the formalization (see `Microscopic.lean`).

Mathematical proof steps covered here: the definitions of graph Hamiltonian trajectories and
vertex-impact times (`stop j` for `j < N`, with departures at `start (j+1)`), the projected
state function, and energy conservation along the graph trajectory.
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph

/-- The four nonnegative parameters of a hybrid chain; all vanish for the graph trajectory and
tend to `0` along a thin-network family. -/
structure ChainParams where
  offset : ℝ
  dwell : ℝ
  odeErr : ℝ
  momErr : ℝ
  offset_nonneg : 0 ≤ offset
  dwell_nonneg : 0 ≤ dwell
  odeErr_nonneg : 0 ≤ odeErr
  momErr_nonneg : 0 ≤ momErr

namespace ChainParams

/-- The parameters of the exact graph dynamics. -/
def zero : ChainParams := ⟨0, 0, 0, 0, le_rfl, le_rfl, le_rfl, le_rfl⟩

@[simp] theorem zero_offset : zero.offset = 0 := rfl
@[simp] theorem zero_dwell : zero.dwell = 0 := rfl
@[simp] theorem zero_odeErr : zero.odeErr = 0 := rfl
@[simp] theorem zero_momErr : zero.momErr = 0 := rfl

end ChainParams

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ) (F : RoutingLaw Γ)

/-- A hybrid chain with parameters `P`: `N` router passages and `N + 1` tube flights.  Flight `j`
(`0 ≤ j ≤ N`) occupies the time interval `[start j, stop j]` on edge `edge j` with longitudinal
state `curve j t = (q, p)`.  For `j < N` the flight ends at time `stop j` by entering the router
through the edge-end `germ j`, and the next flight starts at time `start (j+1)` on the routed
edge.  The last flight ends at `stop N` strictly inside its tube. -/
structure HybridChain (P : ChainParams) where
  /-- number of router passages (vertex impacts) -/
  N : ℕ
  /-- start time of flight `j`; `start 0 = 0` -/
  start : ℕ → ℝ
  /-- end time of flight `j`: the impact time for `j < N`, the final time for `j = N` -/
  stop : ℕ → ℝ
  /-- edge carrying flight `j` -/
  edge : ℕ → Γ.Edge
  /-- longitudinal coordinate and momentum during flight `j` -/
  curve : ℕ → ℝ → ℝ × ℝ
  /-- edge-end through which passage `j` is entered -/
  germ : ℕ → Γ.EdgeEnd
  start_zero : start 0 = 0
  start_lt_stop : ∀ j ≤ N, start j < stop j
  stop_le_start_succ : ∀ j < N, stop j ≤ start (j + 1)
  start_succ_le : ∀ j < N, start (j + 1) ≤ stop j + P.dwell
  /-- Hamilton's equations along a flight, up to the tolerance `P.odeErr`. -/
  flight_ode : ∀ j ≤ N, ∃ w : ℝ → ℝ × ℝ, ∀ t ∈ Icc (start j) (stop j),
    dist (w t) (V.edgeVectorField (edge j) (curve j t)) ≤ P.odeErr ∧
      HasDerivWithinAt (curve j) (w t) (Icc (start j) (stop j)) t
  /-- A flight stays in the tube of its edge. -/
  flight_tube : ∀ j ≤ N, ∀ t ∈ Icc (start j) (stop j),
    (curve j t).1 ∈ Icc P.offset (Γ.length (edge j) - P.offset)
  /-- A flight touches the router boundary only at its endpoints. -/
  flight_inside : ∀ j ≤ N, ∀ t ∈ Ioo (start j) (stop j),
    (curve j t).1 ∈ Ioo P.offset (Γ.length (edge j) - P.offset)
  /-- The final flight ends strictly inside its tube. -/
  final_inside : (curve N (stop N)).1 ∈ Ioo P.offset (Γ.length (edge N) - P.offset)
  germ_edge : ∀ j < N, (germ j).1 = edge j
  /-- Passage `j` is entered at the tube boundary next to `germ j`. -/
  arrive : ∀ j < N, (curve j (stop j)).1 =
    EdgeEnd.coordinate Γ (germ j) - EdgeEnd.sign Γ (germ j) * P.offset
  /-- The next flight is on the edge of the routed edge-end. -/
  edge_succ : ∀ j < N, edge (j + 1) = (F.routeGerm (germ j)).1
  /-- The next flight starts at the tube boundary next to the routed edge-end. -/
  depart_coord : ∀ j < N, (curve (j + 1) (start (j + 1))).1 =
    EdgeEnd.coordinate Γ (F.routeGerm (germ j)) -
      EdgeEnd.sign Γ (F.routeGerm (germ j)) * P.offset
  /-- The outgoing longitudinal momentum is the routed momentum, up to `P.momErr`. -/
  depart_mom : ∀ j < N, |(curve (j + 1) (start (j + 1))).2 -
    F.departureMomentum (germ j) (curve j (stop j)).2| ≤ P.momErr

/-- The deterministic graph-scattering trajectory: the hybrid chain with vanishing parameters.
Flights solve Hamilton's equations exactly, impacts are instantaneous, and the routing law
`F` prescribes the outgoing edge-end and momentum. -/
abbrev GraphTrajectory := HybridChain V F ChainParams.zero

namespace HybridChain

variable {V F} {P : ChainParams} (c : HybridChain V F P)

/-! ### Time bookkeeping -/

theorem start_lt_start_succ {j : ℕ} (hj : j < c.N) : c.start j < c.start (j + 1) :=
  lt_of_lt_of_le (c.start_lt_stop j hj.le) (c.stop_le_start_succ j hj)

theorem start_le_start {i j : ℕ} (hij : i ≤ j) (hj : j ≤ c.N) : c.start i ≤ c.start j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ m him ih =>
      exact (ih (Nat.le_of_succ_le hj)).trans (c.start_lt_start_succ (Nat.lt_of_succ_le hj)).le

theorem start_nonneg {j : ℕ} (hj : j ≤ c.N) : 0 ≤ c.start j := by
  have := c.start_le_start (Nat.zero_le j) hj
  rwa [c.start_zero] at this

theorem stop_nonneg {j : ℕ} (hj : j ≤ c.N) : 0 ≤ c.stop j :=
  (c.start_nonneg hj).trans (c.start_lt_stop j hj).le

theorem stop_le_stop_succ {j : ℕ} (hj : j < c.N) : c.stop j ≤ c.stop (j + 1) :=
  (c.stop_le_start_succ j hj).trans (c.start_lt_stop (j + 1) hj).le

theorem stop_le_stop {i j : ℕ} (hij : i ≤ j) (hj : j ≤ c.N) : c.stop i ≤ c.stop j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ m him ih =>
      exact (ih (Nat.le_of_succ_le hj)).trans (c.stop_le_stop_succ (Nat.lt_of_succ_le hj))

/-- Every flight interval lies in `[0, stop N]`. -/
theorem stop_le_stop_N {j : ℕ} (hj : j ≤ c.N) : c.stop j ≤ c.stop c.N :=
  c.stop_le_stop hj le_rfl

theorem start_le_stop_of_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ c.N) : c.start i ≤ c.stop j :=
  (c.start_le_start hij hj).trans (c.start_lt_stop j hj).le

theorem mem_Icc_zero_stop_N {j : ℕ} (hj : j ≤ c.N) {t : ℝ} (ht : t ∈ Icc (c.start j) (c.stop j)) :
    t ∈ Icc 0 (c.stop c.N) :=
  ⟨(c.start_nonneg hj).trans ht.1, ht.2.trans (c.stop_le_stop_N hj)⟩

/-! ### The projected state function -/

/-- The index of the flight active at time `t`: the largest `j ≤ N` with `start j ≤ t`.  At an
impact time the departing flight is selected (right-continuity), matching the outgoing
convention of the scattered trajectory. -/
noncomputable def flightIndex (t : ℝ) : ℕ :=
  Nat.findGreatest (fun j => c.start j ≤ t) c.N

/-- The projected graph state at time `t`: the active edge with its longitudinal coordinate and
momentum. -/
noncomputable def state (t : ℝ) : Γ.Edge × ℝ × ℝ :=
  (c.edge (c.flightIndex t), c.curve (c.flightIndex t) t)

theorem flightIndex_le (t : ℝ) : c.flightIndex t ≤ c.N :=
  Nat.findGreatest_le c.N

theorem start_flightIndex_le {t : ℝ} (ht : 0 ≤ t) : c.start (c.flightIndex t) ≤ t :=
  Nat.findGreatest_spec (P := fun j => c.start j ≤ t) (Nat.zero_le c.N)
    (by rw [c.start_zero]; exact ht)

theorem lt_start_succ_flightIndex {t : ℝ} (h : c.flightIndex t < c.N) :
    t < c.start (c.flightIndex t + 1) := by
  have := Nat.findGreatest_is_greatest (P := fun j => c.start j ≤ t)
    (Nat.lt_succ_self (c.flightIndex t)) (Nat.succ_le_of_lt h)
  exact lt_of_not_ge this

/-- The flight index is `j` exactly on the half-open interval between the start of flight `j`
and the start of flight `j + 1` (or from the start of the last flight on). -/
theorem flightIndex_eq_of_mem {j : ℕ} (hj : j ≤ c.N) {t : ℝ} (hjt : c.start j ≤ t)
    (htj : j < c.N → t < c.start (j + 1)) : c.flightIndex t = j := by
  apply le_antisymm
  · by_contra h
    replace h : j < c.flightIndex t := not_le.mp h
    have hjN : j < c.N := lt_of_lt_of_le h (c.flightIndex_le t)
    have h1 : c.start (j + 1) ≤ c.start (c.flightIndex t) :=
      c.start_le_start h (c.flightIndex_le t)
    have h2 := c.start_flightIndex_le ((c.start_nonneg hj).trans hjt)
    exact absurd (lt_of_lt_of_le (htj hjN) (h1.trans h2)) (lt_irrefl _)
  · exact Nat.le_findGreatest hj hjt

theorem state_eq_of_flightIndex_eq {j : ℕ} {t : ℝ} (h : c.flightIndex t = j) :
    c.state t = (c.edge j, c.curve j t) := by
  unfold state
  rw [h]

/-! ### Flight derivatives -/

/-- Extraction of the position equation `q' = p` (up to the tolerance) from `flight_ode`. -/
theorem flight_ode_fst {j : ℕ} (hj : j ≤ c.N) : ∃ w : ℝ → ℝ × ℝ,
    ∀ t ∈ Icc (c.start j) (c.stop j),
      |(w t).1 - (c.curve j t).2| ≤ P.odeErr ∧
      |(w t).2 - V.force (c.edge j) (c.curve j t).1| ≤ P.odeErr ∧
      HasDerivWithinAt (fun s => (c.curve j s).1) (w t).1 (Icc (c.start j) (c.stop j)) t ∧
      HasDerivWithinAt (fun s => (c.curve j s).2) (w t).2 (Icc (c.start j) (c.stop j)) t := by
  obtain ⟨w, hw⟩ := c.flight_ode j hj
  refine ⟨w, fun t ht => ?_⟩
  obtain ⟨hdist, hderiv⟩ := hw t ht
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hdist
  exact ⟨hdist.1, hdist.2, hderiv.fst_comp, hderiv.snd_comp⟩

/-- The longitudinal coordinate of a flight is continuous on the flight interval. -/
theorem continuousOn_curve {j : ℕ} (hj : j ≤ c.N) :
    ContinuousOn (c.curve j) (Icc (c.start j) (c.stop j)) := by
  obtain ⟨w, hw⟩ := c.flight_ode j hj
  exact fun t ht => (hw t ht).2.continuousWithinAt

/-! ### The graph trajectory: exact dynamics -/

section Graph

variable (g : GraphTrajectory V F)

/-- Along the graph trajectory the flights are exact solutions of the edge Hamiltonian system. -/
theorem flight_ode_exact {j : ℕ} (hj : j ≤ g.N) :
    ∀ t ∈ Icc (g.start j) (g.stop j),
      HasDerivWithinAt (g.curve j) (V.edgeVectorField (g.edge j) (g.curve j t))
        (Icc (g.start j) (g.stop j)) t := by
  obtain ⟨w, hw⟩ := g.flight_ode j hj
  intro t ht
  obtain ⟨hdist, hderiv⟩ := hw t ht
  have hw' : w t = V.edgeVectorField (g.edge j) (g.curve j t) :=
    dist_le_zero.mp (by simpa using hdist)
  rwa [hw'] at hderiv

/-- Impacts of the graph trajectory are instantaneous: the departure time equals the impact
time. -/
theorem start_succ_eq_stop {j : ℕ} (hj : j < g.N) : g.start (j + 1) = g.stop j :=
  le_antisymm (by simpa using g.start_succ_le j hj) (g.stop_le_start_succ j hj)

/-- The graph trajectory stays on the closed physical edge. -/
theorem physical {j : ℕ} (hj : j ≤ g.N) {t : ℝ} (ht : t ∈ Icc (g.start j) (g.stop j)) :
    (g.curve j t).1 ∈ Icc (0 : ℝ) (Γ.length (g.edge j)) := by
  simpa using g.flight_tube j hj t ht

/-- Between impacts the graph trajectory is in the open edge. -/
theorem interior {j : ℕ} (hj : j ≤ g.N) {t : ℝ} (ht : t ∈ Ioo (g.start j) (g.stop j)) :
    (g.curve j t).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge j)) := by
  simpa using g.flight_inside j hj t ht

/-- An impact of the graph trajectory happens at the vertex coordinate of its entry germ. -/
theorem arrive_eq {j : ℕ} (hj : j < g.N) :
    (g.curve j (g.stop j)).1 = EdgeEnd.coordinate Γ (g.germ j) := by
  simpa using g.arrive j hj

theorem depart_coord_eq {j : ℕ} (hj : j < g.N) :
    (g.curve (j + 1) (g.start (j + 1))).1 = EdgeEnd.coordinate Γ (F.routeGerm (g.germ j)) := by
  simpa using g.depart_coord j hj

/-- The graph trajectory departs with exactly the routed momentum. -/
theorem depart_mom_eq {j : ℕ} (hj : j < g.N) :
    (g.curve (j + 1) (g.start (j + 1))).2 =
      F.departureMomentum (g.germ j) (g.curve j (g.stop j)).2 := by
  have h := g.depart_mom j hj
  simp only [ChainParams.zero_momErr] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

/-- The (conserved) energy of the graph trajectory, read off from its initial state. -/
noncomputable def energy : ℝ :=
  V.hamiltonian (g.edge 0) (g.curve 0 0).1 (g.curve 0 0).2

/-- Energy conservation along one flight (Lemma: the edge Hamiltonian is a first integral). -/
theorem hamiltonian_eq_start {j : ℕ} (hj : j ≤ g.N) {t : ℝ}
    (ht : t ∈ Icc (g.start j) (g.stop j)) :
    V.hamiltonian (g.edge j) (g.curve j t).1 (g.curve j t).2 =
      V.hamiltonian (g.edge j) (g.curve j (g.start j)).1 (g.curve j (g.start j)).2 := by
  have hode := g.flight_ode_exact hj
  exact V.hamiltonian_eq_of_hamiltonEquations_within
    (q := fun s => (g.curve j s).1) (p := fun s => (g.curve j s).2)
    (fun s hs => V.closedEdge_subset_domain _ (g.physical hj hs))
    (fun s hs => (hode s hs).fst_comp)
    (fun s hs => (hode s hs).snd_comp) t ht

/-- Energy conservation across an impact: the routed momentum has the same speed and the
potential is continuous at the vertex. -/
theorem hamiltonian_start_succ {j : ℕ} (hj : j < g.N) :
    V.hamiltonian (g.edge (j + 1)) (g.curve (j + 1) (g.start (j + 1))).1
        (g.curve (j + 1) (g.start (j + 1))).2 =
      V.hamiltonian (g.edge j) (g.curve j (g.stop j)).1 (g.curve j (g.stop j)).2 := by
  rw [g.depart_coord_eq hj, g.depart_mom_eq hj, g.arrive_eq hj, g.edge_succ j hj,
    ← g.germ_edge j hj, V.endpoint_hamiltonian, V.endpoint_hamiltonian,
    F.departureMomentum_sq, F.routeGerm_vertex]

/-- Every flight of the graph trajectory starts at the initial energy. -/
theorem hamiltonian_start_eq_energy {j : ℕ} (hj : j ≤ g.N) :
    V.hamiltonian (g.edge j) (g.curve j (g.start j)).1 (g.curve j (g.start j)).2 = g.energy := by
  induction j with
  | zero =>
      rw [g.start_zero]
      rfl
  | succ m ih =>
      have hm : m < g.N := Nat.lt_of_succ_le hj
      rw [g.hamiltonian_start_succ hm,
        g.hamiltonian_eq_start hm.le ⟨(g.start_lt_stop m hm.le).le, le_rfl⟩]
      exact ih hm.le

/-- Energy conservation along the whole graph trajectory. -/
theorem hamiltonian_eq_energy {j : ℕ} (hj : j ≤ g.N) {t : ℝ}
    (ht : t ∈ Icc (g.start j) (g.stop j)) :
    V.hamiltonian (g.edge j) (g.curve j t).1 (g.curve j t).2 = g.energy := by
  rw [g.hamiltonian_eq_start hj ht]
  exact g.hamiltonian_start_eq_energy hj

end Graph

end HybridChain

end MechanicalPotential
end HamiltonianMetricGraphs
