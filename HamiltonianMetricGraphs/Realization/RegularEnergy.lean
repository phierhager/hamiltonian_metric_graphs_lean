/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.FlightEstimates
import HamiltonianMetricGraphs.NoZeno

/-!
# Regular energy windows: uniform speed bounds and the no-Zeno estimate

Let `K` be a compact energy window with `K ∩ {V(v) : v ∈ V} = ∅`.  This file provides the
uniform constants used by the microscopic-realization theorem for every graph trajectory with
energy in `K`:

* the **regular-energy lemma**: a state at a vertex with energy in `K` has speed at least
  `c₀ > 0`; in a collar around every vertex the longitudinal speed is at least `c₁ > 0`;
* the compact-window **speed bound** `|p| ≤ P` and the **force bound** `|V'| ≤ R`;
* **transversality**: the impact momentum of a graph trajectory is incoming at its germ;
* the **no-Zeno theorem**: consecutive impacts of a graph trajectory with energy in `K` are
  separated by a uniform positive time `τ`.

Mathematical proof steps: "regular-energy lemma giving a uniform positive longitudinal speed
near vertices" and "no-Zeno theorem giving a uniform lower bound between graph impacts on `K`".
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- **Regular-energy lemma, vertex form.**  On a compact regular energy window every state at
a vertex has speed at least `c₀ = √(2δ) > 0`, where `δ` is the gap between `K` and the vertex
energies. -/
theorem exists_vertex_speed_lower_bound [Nonempty Γ.Edge] (K : Set ℝ) (hK : IsCompact K)
    (hreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ E ∈ K, ∀ (v : Γ.Vertex) (p : ℝ),
      p ^ 2 / 2 + V.vertexValue v = E → c₀ ≤ |p| := by
  obtain ⟨δ, hδ, hgap⟩ := V.exists_compact_regular_energy_gap K hK hreg
  refine ⟨Real.sqrt (2 * δ), Real.sqrt_pos.mpr (by linarith), ?_⟩
  intro E hE v p hp
  have h := hgap E hE v
  have hnn : 0 ≤ E - V.vertexValue v := by
    rw [← hp]
    nlinarith [sq_nonneg p]
  rw [abs_of_nonneg hnn] at h
  have hsq : 2 * δ ≤ p ^ 2 := by nlinarith
  calc Real.sqrt (2 * δ) ≤ Real.sqrt (p ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |p| := Real.sqrt_sq_eq_abs p

/-- **Regular-energy lemma, collar form.**  There is a collar radius `r` (smaller than half of
every edge length) and a speed `c₁ > 0` such that every state with energy in `K` whose
coordinate is within `r` of a vertex has longitudinal speed at least `c₁`. -/
theorem exists_collar_speed_lower_bound [Nonempty Γ.Edge] (K : Set ℝ) (hK : IsCompact K)
    (hreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ r c₁ : ℝ, 0 < r ∧ 0 < c₁ ∧ (∀ e : Γ.Edge, r < Γ.length e / 2) ∧
      ∀ E ∈ K, ∀ (η : Γ.EdgeEnd) (q p : ℝ), |q - EdgeEnd.coordinate Γ η| < r →
        V.hamiltonian η.1 q p = E → c₁ ≤ |p| := by
  obtain ⟨δ, r, hδ, hr, hrlen, hcol⟩ := V.exists_compact_regular_endpoint_collar K hK hreg
  refine ⟨r, Real.sqrt (3 * δ / 2), hr, Real.sqrt_pos.mpr (by linarith), hrlen, ?_⟩
  intro E hE η q p hq hEq
  have h := hcol E hE η q hq
  have hnn : 0 ≤ E - V.extension η.1 q := by
    rw [← hEq]
    unfold hamiltonian
    nlinarith [sq_nonneg p]
  rw [abs_of_nonneg hnn] at h
  have hsq : 3 * δ / 2 ≤ p ^ 2 := by
    unfold hamiltonian at hEq
    nlinarith
  calc Real.sqrt (3 * δ / 2) ≤ Real.sqrt (p ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |p| := Real.sqrt_sq_eq_abs p

/-- A nonnegative uniform force bound on all closed physical edges. -/
theorem exists_force_bound :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.force e q| ≤ R := by
  obtain ⟨R, hR⟩ := V.exists_uniform_absBound_force_closedEdges
  exact ⟨|R|, abs_nonneg R, fun e q hq => (hR e q hq).trans (le_abs_self R)⟩

/-- A positive uniform lower bound for the edge lengths (vacuous without edges). -/
theorem _root_.HamiltonianMetricGraphs.FiniteMetricGraph.exists_length_lower_bound
    (Γ : FiniteMetricGraph) : ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ e : Γ.Edge, ℓ ≤ Γ.length e := by
  classical
  by_cases h : Nonempty Γ.Edge
  · letI := h
    obtain ⟨r, hr, hlen⟩ := Γ.exists_uniform_endpointCollarRadius
    exact ⟨r, hr, fun e => by linarith [hlen e, Γ.length_pos e]⟩
  · exact ⟨1, one_pos, fun e => (h ⟨e⟩).elim⟩

namespace HybridChain

variable {V} {F : RoutingLaw Γ} (g : GraphTrajectory V F)

/-- **Transversality.**  A nonzero impact momentum of the graph trajectory is incoming at the
impact germ: the flight approaches the vertex from inside the edge. -/
theorem sign_mul_impact_pos {j : ℕ} (hj : j < g.N) (hp : (g.curve j (g.stop j)).2 ≠ 0) :
    0 < EdgeEnd.sign Γ (g.germ j) * (g.curve j (g.stop j)).2 := by
  have hlt := g.start_lt_stop j hj.le
  have hode := g.flight_ode_exact hj.le
  have hq : HasDerivWithinAt (fun s => (g.curve j s).1) (g.curve j (g.stop j)).2
      (Iic (g.stop j)) (g.stop j) :=
    hasDerivWithinAt_Iic_of_Icc hlt (hode (g.stop j) (right_mem_Icc.mpr hlt.le)).fst_comp
  have harr := g.arrive_eq hj
  have hedge := g.germ_edge j hj
  rcases hg : g.germ j with ⟨e, s⟩
  rw [hg] at harr hedge
  change e = g.edge j at hedge
  cases s
  · have hzero : (g.curve j (g.stop j)).1 = 0 := by simpa using harr
    have hle := leftEndpoint_derivWithin_nonpos_of_pos_before hlt
      (fun t ht => (g.interior hj.le ht).1) hq hzero
    have hneg : (g.curve j (g.stop j)).2 < 0 := lt_of_le_of_ne hle hp
    simp only [edgeEnd_sign_false]
    linarith
  · have hL : (g.curve j (g.stop j)).1 = Γ.length (g.edge j) := by
      rw [← hedge]; simpa using harr
    have hge := rightEndpoint_derivWithin_nonneg_of_lt_before hlt
      (fun t ht => (g.interior hj.le ht).2) hq hL
    have hpos : 0 < (g.curve j (g.stop j)).2 := lt_of_le_of_ne hge (Ne.symm hp)
    simp only [edgeEnd_sign_true, one_mul]
    exact hpos

/-- The impact energy identity: at an impact the graph trajectory has `p²/2 + V(v) = E`. -/
theorem impact_energy {j : ℕ} (hj : j < g.N) :
    (g.curve j (g.stop j)).2 ^ 2 / 2 + V.vertexValue (g.germ j).vertex = g.energy := by
  have h := g.hamiltonian_eq_energy hj.le (right_mem_Icc.mpr (g.start_lt_stop j hj.le).le)
  rw [g.arrive_eq hj, ← g.germ_edge j hj, V.endpoint_hamiltonian] at h
  exact h

end HybridChain

/-- The compact-window speed bound applies along every graph trajectory with energy in `K`. -/
theorem exists_graph_speed_bound (F : RoutingLaw Γ) (K : Set ℝ) (hK : IsCompact K) :
    ∃ P : ℝ, 0 < P ∧ ∀ g : GraphTrajectory V F, g.energy ∈ K →
      ∀ j ≤ g.N, ∀ t ∈ Icc (g.start j) (g.stop j), |(g.curve j t).2| ≤ P := by
  obtain ⟨P, hP, hbound⟩ := V.exists_compact_energy_speed_bound K hK
  refine ⟨P, hP, fun g hE j hj t ht => ?_⟩
  exact hbound (g.edge j) _ _ g.energy (g.physical hj ht) hE (g.hamiltonian_eq_energy hj ht)

/-- Every impact of a graph trajectory with energy in a compact regular window has speed at
least `c₀ > 0`, and the impact is incoming. -/
theorem exists_impact_speed_lower_bound [Nonempty Γ.Edge] (F : RoutingLaw Γ) (K : Set ℝ)
    (hK : IsCompact K) (hreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ g : GraphTrajectory V F, g.energy ∈ K → ∀ j < g.N,
      c₀ ≤ EdgeEnd.sign Γ (g.germ j) * (g.curve j (g.stop j)).2 := by
  obtain ⟨c₀, hc₀, hspeed⟩ := V.exists_vertex_speed_lower_bound K hK hreg
  refine ⟨c₀, hc₀, fun g hE j hj => ?_⟩
  have habs := hspeed g.energy hE (g.germ j).vertex _ (g.impact_energy hj)
  have hne : (g.curve j (g.stop j)).2 ≠ 0 := by
    intro h
    rw [h, abs_zero] at habs
    linarith
  have hpos := g.sign_mul_impact_pos hj hne
  have hσ : |EdgeEnd.sign Γ (g.germ j)| = 1 := RoutingLaw.edgeEnd_abs_sign _
  calc c₀ ≤ |(g.curve j (g.stop j)).2| := habs
    _ = |EdgeEnd.sign Γ (g.germ j) * (g.curve j (g.stop j)).2| := by
        rw [abs_mul, hσ, one_mul]
    _ = EdgeEnd.sign Γ (g.germ j) * (g.curve j (g.stop j)).2 := abs_of_pos hpos

/-- **No-Zeno theorem.**  Consecutive impacts of a graph trajectory with energy in a compact
regular window are separated by a uniform positive time `τ`: after an impact the trajectory
departs with speed at least `c₀`, and `IsFlight.duration_lower_bound_departure` applies. -/
theorem exists_noZeno_separation [Nonempty Γ.Edge] (F : RoutingLaw Γ) (K : Set ℝ)
    (hK : IsCompact K) (hreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ g : GraphTrajectory V F, g.energy ∈ K →
      ∀ j : ℕ, j + 1 < g.N → τ ≤ g.stop (j + 1) - g.stop j := by
  obtain ⟨c₀, hc₀, himpact⟩ := V.exists_impact_speed_lower_bound F K hK hreg
  obtain ⟨P, hP, hspeed⟩ := V.exists_graph_speed_bound F K hK
  obtain ⟨R, hR0, hR⟩ := V.exists_force_bound
  obtain ⟨ℓ, hℓ, hlen⟩ := Γ.exists_length_lower_bound
  refine ⟨min (c₀ / (2 * (R + 2))) (ℓ / (2 * (P + c₀ + 2))), lt_min (by positivity)
    (by positivity), ?_⟩
  intro g hE j hj
  have hj' : j < g.N := by omega
  obtain ⟨w, hw⟩ := g.isFlight hj.le
  set ζ := F.routeGerm (g.germ j) with hζ
  have hζe : ζ.1 = g.edge (j + 1) := (g.edge_succ j hj').symm
  have hlt := g.start_lt_stop (j + 1) hj.le
  have hstart : |(g.curve (j + 1) (g.start (j + 1))).1 - EdgeEnd.coordinate Γ ζ| ≤
      Γ.length (g.edge (j + 1)) / 4 := by
    rw [g.depart_coord_eq hj', sub_self, abs_zero]
    exact div_nonneg (Γ.length_pos _).le (by norm_num)
  have hout : EdgeEnd.sign Γ ζ * (g.curve (j + 1) (g.start (j + 1))).2 ≤ -c₀ := by
    rw [g.depart_mom_eq hj', F.sign_mul_departureMomentum]
    have h1 := himpact g hE j hj'
    have hσ : |EdgeEnd.sign Γ (g.germ j)| = 1 := RoutingLaw.edgeEnd_abs_sign _
    have : |(g.curve j (g.stop j)).2| =
        |EdgeEnd.sign Γ (g.germ j) * (g.curve j (g.stop j)).2| := by
      rw [abs_mul, hσ, one_mul]
    rw [this, abs_of_pos (lt_of_lt_of_le hc₀ h1)]
    linarith
  have hB : |(g.curve (j + 1) (g.start (j + 1))).2| ≤ P :=
    hspeed g hE (j + 1) hj.le _ (left_mem_Icc.mpr hlt.le)
  have hend := g.arrive j.succ hj
  simp only [ChainParams.zero_offset, mul_zero, sub_zero] at hend
  have key := hw.duration_lower_bound_departure hlt (hR _) hR0 zero_le_one le_rfl
    (div_nonneg (Γ.length_pos _).le (by norm_num)) hζe hstart hc₀
    (by rw [ChainParams.zero_odeErr]; positivity) hout hB
    (g.germ_edge (j + 1) hj) (by simpa using hend)
  rw [g.start_succ_eq_stop hj'] at key
  refine le_trans (min_le_min le_rfl ?_) key
  apply div_le_div_of_nonneg_right (hlen _) (by positivity)

end MechanicalPotential
end HamiltonianMetricGraphs
