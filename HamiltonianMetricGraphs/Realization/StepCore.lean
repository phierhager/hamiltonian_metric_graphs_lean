/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.Microscopic

/-!
# One impact: the deterministic step estimate

This file proves the quantitative core of the induction over impacts.  Fix a graph trajectory
`g` with energy in a compact regular window (constants: speed bound `P`, force bound `R`,
Lipschitz constant `K`, impact speed `c₀`) and a flight `j < N` of `g`, ending at time
`t₁ = stop j` by an impact at the germ `η`.  Let `c` be a hybrid chain (a microscopic
trajectory) whose flight `j` runs on the same edge, starts within `θ` of the start time and
start state of the graph flight, has parameters `≤ θ`, and lasts at least `τ`.  Then, for a
margin `δ` and the Grönwall closeness `Δ` (both small in an explicit, quantified sense):

1. the microscopic flight `j` also ends by entering a router (`j < c.N`);
2. it enters through the same germ `η` (channel stability at the graph level);
3. its impact time lies in `[t₁ - δ, t₁ - δ + 8(Pδ + Δ)/c₀]`;
4. its impact momentum is within `(R+1)·8(Pδ+Δ)/c₀ + Δ + Rδ` of the graph impact momentum;
5. on `[start j + δ, t₁ - δ]` the two flights are within `Δ` of each other.

The proof is: Grönwall on the common time interval (edge approximation), the interior margin of
the graph flight (the microscopic flight cannot enter a router while the graph flight is far
from the vertices), and the transverse-crossing lemma near `t₁`.

Mathematical proof steps: "edge approximation", "channel stability", "convergence of impact
times using transverse crossing".
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph
open scoped Topology NNReal

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} {V : MechanicalPotential Γ} {F : RoutingLaw Γ}

namespace HybridChain

variable (g : GraphTrajectory V F)

/-- The flights of the graph trajectory as flights with literally zero tolerance and offset. -/
theorem isFlight_zero {j : ℕ} (hj : j ≤ g.N) :
    ∃ w : ℝ → ℝ × ℝ, V.IsFlight (g.edge j) 0 0 (g.start j) (g.stop j) (g.curve j) w :=
  g.isFlight hj

/-- **Interior margin.**  On a closed subinterval of a flight on which the graph trajectory
stays in the open edge, its coordinate stays a positive distance `μ` away from both vertices. -/
theorem exists_interior_margin {j : ℕ} (hj : j ≤ g.N) {a' b' : ℝ} (hab : a' ≤ b')
    (hsub : Icc a' b' ⊆ Icc (g.start j) (g.stop j))
    (hint : ∀ t ∈ Icc a' b', (g.curve j t).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge j))) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ t ∈ Icc a' b',
      μ ≤ (g.curve j t).1 ∧ (g.curve j t).1 ≤ Γ.length (g.edge j) - μ := by
  have hq : ContinuousOn (fun t => (g.curve j t).1) (Icc a' b') :=
    (continuous_fst.comp_continuousOn (g.continuousOn_curve hj)).mono hsub
  obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hq
  obtain ⟨t₂, ht₂, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hq
  refine ⟨min (g.curve j t₁).1 (Γ.length (g.edge j) - (g.curve j t₂).1),
    lt_min (hint t₁ ht₁).1 (by linarith [(hint t₂ ht₂).2]), ?_⟩
  intro t ht
  have h1 : (g.curve j t₁).1 ≤ (g.curve j t).1 := hmin ht
  have h2 : (g.curve j t).1 ≤ (g.curve j t₂).1 := hmax ht
  refine ⟨(min_le_left _ _).trans h1, ?_⟩
  linarith [min_le_right (g.curve j t₁).1 (Γ.length (g.edge j) - (g.curve j t₂).1)]

/-- **Approach to an impact.**  Shortly before an impact the graph trajectory is close to the
vertex and its momentum is close to the impact momentum. -/
theorem impact_approach {j : ℕ} (hj : j < g.N) {P R : ℝ}
    (hPg : ∀ t ∈ Icc (g.start j) (g.stop j), |(g.curve j t).2| ≤ P)
    (hR : ∀ q ∈ Icc (0 : ℝ) (Γ.length (g.edge j)), |V.force (g.edge j) q| ≤ R)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδT : g.start j ≤ g.stop j - δ) :
    |(g.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j)).2| ≤ R * δ ∧
    |(g.curve j (g.stop j - δ)).1 - EdgeEnd.coordinate Γ (g.germ j)| ≤ P * δ := by
  obtain ⟨w, hw⟩ := g.isFlight_zero hj.le
  have hlt := g.start_lt_stop j hj.le
  have hmem : g.stop j - δ ∈ Icc (g.start j) (g.stop j) := ⟨hδT, by linarith⟩
  have hend : g.stop j ∈ Icc (g.start j) (g.stop j) := right_mem_Icc.mpr hlt.le
  constructor
  · have h := hw.momentum_drift le_rfl hR hmem hend (by linarith)
    rw [abs_sub_comm]
    simpa using h
  · have h := hw.coordinate_travel hPg hmem hend (by linarith)
    rw [g.arrive_eq hj] at h
    rw [abs_sub_comm]
    simpa using h

/-- The coordinate of a microscopic chain at a router entry lies at one of the two tube
boundaries `offset` or `L - offset` (on the graph edge of the flight). -/
theorem coordinate_at_entry {P' : ChainParams} (c : HybridChain V F P') {j : ℕ} (hjc : j < c.N)
    {e : Γ.Edge} (hedge : c.edge j = e) :
    (c.curve j (c.stop j)).1 = P'.offset ∨
      (c.curve j (c.stop j)).1 = Γ.length e - P'.offset := by
  have harr := c.arrive j hjc
  have hge := c.germ_edge j hjc
  rw [hedge] at hge
  rcases hgj : c.germ j with ⟨e', b⟩
  rw [hgj] at harr hge
  change e' = e at hge
  subst hge
  cases b
  · left
    simp only [edgeEnd_coordinate_false, edgeEnd_sign_false] at harr
    linarith
  · right
    simp only [edgeEnd_coordinate_true, edgeEnd_sign_true] at harr
    linarith

end HybridChain

set_option maxHeartbeats 1600000 in
-- The proof combines Grönwall, the interior margin and the crossing lemma in one declaration;
-- the many `linarith` calls in a large context exceed the default budget.
/-- **The deterministic one-impact step.**  See the module docstring for the statement. -/
theorem step_core (g : GraphTrajectory V F)
    {P R c₀ : ℝ} {K : ℝ≥0}
    (hPg : ∀ j ≤ g.N, ∀ t ∈ Icc (g.start j) (g.stop j), |(g.curve j t).2| ≤ P)
    (hR0 : 0 ≤ R) (hR : ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.force e q| ≤ R)
    (hK : ∀ e : Γ.Edge, LipschitzOnWith K (V.edgeVectorField e) (Γ.edgeStrip e))
    (hc₀ : 0 < c₀)
    (himpact : ∀ j < g.N, c₀ ≤ EdgeEnd.sign Γ (g.germ j) * (g.curve j (g.stop j)).2)
    {j : ℕ} (hj : j < g.N)
    {δ θ Δ μ τ : ℝ} (hδ : 0 < δ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθδ : θ ≤ δ)
    (hΔ : (θ * (2 * P + 2 * R + 4) + θ * (g.stop j - g.start j)) *
        Real.exp (K * (g.stop j - g.start j)) ≤ Δ)
    (hμg : ∀ t ∈ Icc (g.start j + δ) (g.stop j - δ),
      μ ≤ (g.curve j t).1 ∧ (g.curve j t).1 ≤ Γ.length (g.edge j) - μ)
    (hδT : 2 * δ ≤ g.stop j - g.start j)
    (hδτ : 2 * δ ≤ τ) (hθτ : 4 * θ ≤ τ)
    (hΔμ : Δ + θ < μ)
    (hδc : R * δ + Δ ≤ c₀ / 2)
    (hθc : θ ≤ c₀ / 8)
    (hdL : P * δ + Δ ≤ Γ.length (g.edge j) / 4)
    (hθL : θ ≤ Γ.length (g.edge j) / 4)
    (hhor : 8 * (P * δ + Δ) / c₀ < c₀ / (4 * (R + 2)))
    (hgap : 8 * (P * δ + Δ) / c₀ ≤ g.stop (j + 1) - g.stop j)
    {P' : ChainParams} (c : HybridChain V F P')
    (hjN : j ≤ c.N) (hedge : c.edge j = g.edge j)
    (hoff : P'.offset ≤ θ) (hode : P'.odeErr ≤ θ)
    (hstart : |c.start j - g.start j| ≤ θ)
    (hstate : dist (c.curve j (c.start j)) (g.curve j (g.start j)) ≤ θ)
    (hdur : τ ≤ c.stop j - c.start j)
    (hfinal : g.stop g.N ≤ c.stop c.N) :
    j < c.N ∧ c.germ j = g.germ j ∧
    g.stop j - δ ≤ c.stop j ∧ c.stop j ≤ g.stop j - δ + 8 * (P * δ + Δ) / c₀ ∧
    |(c.curve j (c.stop j)).2 - (g.curve j (g.stop j)).2| ≤
      (R + 1) * (8 * (P * δ + Δ) / c₀) + Δ + R * δ ∧
    ∀ t ∈ Icc (g.start j + δ) (g.stop j - δ), dist (c.curve j t) (g.curve j t) ≤ Δ := by
  -- Notation and basic facts.
  obtain ⟨wg, hg⟩ := g.isFlight_zero hj.le
  obtain ⟨wc, hc⟩ := c.isFlight hjN
  rw [hedge] at hc
  have hL := Γ.length_pos (g.edge j)
  have hσ : |EdgeEnd.sign Γ (g.germ j)| = 1 := RoutingLaw.edgeEnd_abs_sign _
  have hηe : (g.germ j).1 = g.edge j := g.germ_edge j hj
  have hρ0 : 0 ≤ P'.odeErr := P'.odeErr_nonneg
  have ho0 : 0 ≤ P'.offset := P'.offset_nonneg
  have hs01 : c.start j < c.stop j := c.start_lt_stop j hjN
  have ht01 : g.start j < g.stop j := g.start_lt_stop j hj.le
  have hRe := hR (g.edge j)
  have hPj := hPg j hj.le
  have hstart' := abs_le.mp hstart
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hPj _ (left_mem_Icc.mpr ht01.le))
  have hΔ0 : 0 ≤ Δ := by
    refine le_trans ?_ hΔ
    apply mul_nonneg
    · have : 0 ≤ θ * (2 * P + 2 * R + 4) := mul_nonneg hθ (by linarith)
      have : 0 ≤ θ * (g.stop j - g.start j) := mul_nonneg hθ (by linarith)
      linarith
    · exact (Real.exp_pos _).le
  -- The microscopic flight ends after `start j + δ`.
  have hs₁ : g.start j + δ < c.stop j := by linarith
  -- The common interval `[m, m']`.
  set m := max (c.start j) (g.start j) with hm
  set m' := min (c.stop j) (g.stop j) with hm'
  have hm_ge : g.start j ≤ m := le_max_right _ _
  have hm_s₀ : c.start j ≤ m := le_max_left _ _
  have hm_le : m ≤ g.start j + θ := max_le (by linarith) (by linarith)
  have hm_le' : m ≤ c.start j + θ := max_le (by linarith) (by linarith)
  have hmm' : m ≤ m' := le_min (by linarith) (by linarith)
  have hm'_c : m' ≤ c.stop j := min_le_left _ _
  have hm'_g : m' ≤ g.stop j := min_le_right _ _
  -- Speed of the microscopic flight at its start.
  have hpm : |(c.curve j (c.start j)).2| ≤ P + 1 := by
    have h1 : |(c.curve j (c.start j)).2 - (g.curve j (g.start j)).2| ≤ θ := by
      have := hstate
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at this
      exact (le_max_right _ _).trans this
    have h2 := hPj _ (left_mem_Icc.mpr ht01.le)
    calc |(c.curve j (c.start j)).2|
        = |((c.curve j (c.start j)).2 - (g.curve j (g.start j)).2) +
            (g.curve j (g.start j)).2| := by ring_nf
      _ ≤ |(c.curve j (c.start j)).2 - (g.curve j (g.start j)).2| +
            |(g.curve j (g.start j)).2| := abs_add_le _ _
      _ ≤ θ + P := add_le_add h1 h2
      _ ≤ P + 1 := by linarith
  -- Drift of the microscopic flight from its start to `m`.
  have hcm : dist (c.curve j m) (c.curve j (c.start j)) ≤ (P + R + 3) * θ := by
    have hsub : V.IsFlight (g.edge j) P'.offset P'.odeErr (c.start j) m (c.curve j) wc :=
      hc.mono le_rfl (hmm'.trans hm'_c)
    have hspeed : ∀ u ∈ Icc (c.start j) m, |(c.curve j u).2| ≤ P + R + 2 := by
      intro u hu
      have h := hsub.abs_momentum_le ho0 hRe hpm hm_s₀ hu
      have h2 : (R + P'.odeErr) * (u - c.start j) ≤ (R + 1) * 1 := by
        apply mul_le_mul (by linarith) (by linarith [hu.1, hu.2]) (by linarith [hu.1])
          (by linarith)
      linarith
    have hw : ∀ u ∈ Icc (c.start j) m, ‖wc u‖ ≤ P + R + 3 := fun u hu =>
      (hsub.norm_w_le ho0 hRe hspeed hu).trans (max_le (by linarith) (by linarith))
    have h := hsub.dist_le hw (left_mem_Icc.mpr hm_s₀) (right_mem_Icc.mpr hm_s₀) hm_s₀
    calc dist (c.curve j m) (c.curve j (c.start j)) ≤ (P + R + 3) * (m - c.start j) := h
      _ ≤ (P + R + 3) * θ := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  -- Drift of the graph flight from its start to `m`.
  have hgm : dist (g.curve j m) (g.curve j (g.start j)) ≤ (P + R) * θ := by
    have hsub : V.IsFlight (g.edge j) 0 0 (g.start j) m (g.curve j) wg :=
      hg.mono le_rfl (hmm'.trans hm'_g)
    have hspeed : ∀ u ∈ Icc (g.start j) m, |(g.curve j u).2| ≤ P := fun u hu =>
      hPj u ⟨hu.1, hu.2.trans (hmm'.trans hm'_g)⟩
    have hw : ∀ u ∈ Icc (g.start j) m, ‖wg u‖ ≤ P + R := fun u hu =>
      (hsub.norm_w_le le_rfl hRe hspeed hu).trans (max_le (by linarith) (by linarith))
    have h := hsub.dist_le hw (left_mem_Icc.mpr hm_ge) (right_mem_Icc.mpr hm_ge) hm_ge
    calc dist (g.curve j m) (g.curve j (g.start j)) ≤ (P + R) * (m - g.start j) := h
      _ ≤ (P + R) * θ := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  -- Closeness at the common start.
  have hd₀ : dist (c.curve j m) (g.curve j m) ≤ θ * (2 * P + 2 * R + 4) := by
    calc dist (c.curve j m) (g.curve j m)
        ≤ dist (c.curve j m) (c.curve j (c.start j)) +
            dist (c.curve j (c.start j)) (g.curve j (g.start j)) +
            dist (g.curve j (g.start j)) (g.curve j m) := dist_triangle4 _ _ _ _
      _ ≤ (P + R + 3) * θ + θ + (P + R) * θ := by
          rw [dist_comm (g.curve j (g.start j))]
          exact add_le_add (add_le_add hcm hstate) hgm
      _ = θ * (2 * P + 2 * R + 4) := by ring
  -- Grönwall on the common interval.
  have hclose : ∀ t ∈ Icc m m', dist (c.curve j t) (g.curve j t) ≤ Δ := by
    have h := (hc.mono hm_s₀ hm'_c).dist_le_closeness (hK _) (hg.mono hm_ge hm'_g) ho0 le_rfl
      hρ0 le_rfl hmm' (mul_nonneg hθ (by linarith)) hd₀
    intro t ht
    refine (h t ht).trans (le_trans ?_ hΔ)
    apply mul_le_mul
    · have h1 : (P'.odeErr + 0) * (m' - m) ≤ θ * (g.stop j - g.start j) := by
        apply mul_le_mul (by linarith) (by linarith) (by linarith) hθ
      linarith
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) K.coe_nonneg)
    · exact (Real.exp_pos _).le
    · have : 0 ≤ θ * (2 * P + 2 * R + 4) := mul_nonneg hθ (by linarith)
      have : 0 ≤ θ * (g.stop j - g.start j) := mul_nonneg hθ (by linarith)
      linarith
  -- Step 1: the microscopic flight does not end before `stop j - δ`.
  have hs₁ge : g.stop j - δ ≤ c.stop j := by
    by_contra hcon
    rw [not_le] at hcon
    have hjc : j < c.N := by
      rcases lt_or_eq_of_le hjN with h | h
      · exact h
      · exfalso
        have h1 : g.stop j ≤ g.stop g.N := g.stop_le_stop_N hj.le
        rw [← h] at hfinal
        linarith
    have hs₁mem : c.stop j ∈ Icc m m' := ⟨by linarith, le_min le_rfl (by linarith)⟩
    have hcl := hclose _ hs₁mem
    have hμs := hμg (c.stop j) ⟨by linarith, by linarith⟩
    have hq : |(c.curve j (c.stop j)).1 - (g.curve j (c.stop j)).1| ≤ Δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hcl
      exact (le_max_left _ _).trans hcl
    have hq' := abs_le.mp hq
    rcases c.coordinate_at_entry hjc hedge with hbd | hbd <;>
      linarith [hμs.1, hμs.2, hq'.1, hq'.2]
  -- Step 2: transverse crossing at `t* = stop j - δ`.
  have htmem_c : g.stop j - δ ∈ Icc (c.start j) (c.stop j) := ⟨by linarith, hs₁ge⟩
  have htmem_m : g.stop j - δ ∈ Icc m m' := ⟨by linarith, le_min hs₁ge (by linarith)⟩
  have hcl := hclose _ htmem_m
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff] at hcl
  obtain ⟨hpg, hqg⟩ := g.impact_approach hj hPj hRe hδ.le (by linarith)
  have hσp := himpact j hj
  -- microscopic momentum at `t*` points towards the vertex with speed `≥ c₀/2`
  have hpc : c₀ / 2 ≤ EdgeEnd.sign Γ (g.germ j) * (c.curve j (g.stop j - δ)).2 := by
    have h1 : |(c.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j)).2| ≤ Δ + R * δ := by
      calc |(c.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j)).2|
          = |((c.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j - δ)).2) +
              ((g.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j)).2)| := by ring_nf
        _ ≤ |(c.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j - δ)).2| +
              |(g.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j)).2| := abs_add_le _ _
        _ ≤ Δ + R * δ := add_le_add hcl.2 hpg
    have h2 : |EdgeEnd.sign Γ (g.germ j) *
        ((c.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j)).2)| ≤ Δ + R * δ := by
      rw [abs_mul, hσ, one_mul]; exact h1
    have h3 := (abs_le.mp h2).1
    have : EdgeEnd.sign Γ (g.germ j) * (c.curve j (g.stop j - δ)).2 =
        EdgeEnd.sign Γ (g.germ j) * (g.curve j (g.stop j)).2 +
          EdgeEnd.sign Γ (g.germ j) *
            ((c.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j)).2) := by ring
    linarith
  -- microscopic coordinate at `t*` is within `Pδ + Δ` of the vertex
  have hqc : -(P * δ + Δ) ≤ EdgeEnd.sign Γ (g.germ j) *
      ((c.curve j (g.stop j - δ)).1 - EdgeEnd.coordinate Γ (g.germ j)) := by
    have h1 : |(c.curve j (g.stop j - δ)).1 - EdgeEnd.coordinate Γ (g.germ j)| ≤ P * δ + Δ := by
      calc |(c.curve j (g.stop j - δ)).1 - EdgeEnd.coordinate Γ (g.germ j)|
          = |((c.curve j (g.stop j - δ)).1 - (g.curve j (g.stop j - δ)).1) +
              ((g.curve j (g.stop j - δ)).1 - EdgeEnd.coordinate Γ (g.germ j))| := by ring_nf
        _ ≤ |(c.curve j (g.stop j - δ)).1 - (g.curve j (g.stop j - δ)).1| +
              |(g.curve j (g.stop j - δ)).1 - EdgeEnd.coordinate Γ (g.germ j)| :=
            abs_add_le _ _
        _ ≤ Δ + P * δ := add_le_add hcl.1 hqg
        _ = P * δ + Δ := by ring
    have h2 : |EdgeEnd.sign Γ (g.germ j) *
        ((c.curve j (g.stop j - δ)).1 - EdgeEnd.coordinate Γ (g.germ j))| ≤ P * δ + Δ := by
      rw [abs_mul, hσ, one_mul]; exact h1
    exact (abs_le.mp h2).1
  have hhor' : 4 * (P * δ + Δ) / (c₀ / 2) < c₀ / 2 / (2 * (R + P'.odeErr + 1)) := by
    have e1 : 4 * (P * δ + Δ) / (c₀ / 2) = 8 * (P * δ + Δ) / c₀ := by
      field_simp
      ring
    have e2 : c₀ / (4 * (R + 2)) ≤ c₀ / 2 / (2 * (R + P'.odeErr + 1)) := by
      rw [div_div]
      apply div_le_div_of_nonneg_left hc₀.le (by positivity)
      nlinarith
    rw [e1]
    exact lt_of_lt_of_le hhor e2
  obtain ⟨hcross1, hcross2, hcross3⟩ := hc.crossing hs01.le hRe hR0 hρ0 ho0 (hoff.trans hθL)
    hηe htmem_c (by positivity) (by linarith) hpc hqc hdL hhor'
  have e1 : 4 * (P * δ + Δ) / (c₀ / 2) = 8 * (P * δ + Δ) / c₀ := by
    field_simp
    ring
  rw [e1] at hcross1 hcross2
  -- Step 3: the microscopic flight ends by entering a router.
  have hjc : j < c.N := by
    rcases lt_or_eq_of_le hjN with h | h
    · exact h
    · exfalso
      have h1 : g.stop (j + 1) ≤ g.stop g.N := g.stop_le_stop_N hj
      rw [← h] at hfinal
      linarith
  -- Step 4: same entry germ.
  have hgerm : c.germ j = g.germ j :=
    hcross3 (c.germ j) (by rw [c.germ_edge j hjc, hedge]) (c.arrive j hjc)
  -- Step 5: impact momentum.
  have hmom : |(c.curve j (c.stop j)).2 - (g.curve j (g.stop j)).2| ≤
      (R + 1) * (8 * (P * δ + Δ) / c₀) + Δ + R * δ := by
    have hpos : 0 ≤ 8 * (P * δ + Δ) / c₀ := by positivity
    have h1 : |(c.curve j (c.stop j)).2 - (c.curve j (g.stop j - δ)).2| ≤
        (R + 1) * (8 * (P * δ + Δ) / c₀) :=
      hcross2.trans (mul_le_mul_of_nonneg_right (by linarith) hpos)
    calc |(c.curve j (c.stop j)).2 - (g.curve j (g.stop j)).2|
        = |((c.curve j (c.stop j)).2 - (c.curve j (g.stop j - δ)).2) +
            ((c.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j - δ)).2) +
            ((g.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j)).2)| := by ring_nf
      _ ≤ |(c.curve j (c.stop j)).2 - (c.curve j (g.stop j - δ)).2| +
            |(c.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j - δ)).2| +
            |(g.curve j (g.stop j - δ)).2 - (g.curve j (g.stop j)).2| :=
          abs_add_three _ _ _
      _ ≤ (R + 1) * (8 * (P * δ + Δ) / c₀) + Δ + R * δ :=
          add_le_add (add_le_add h1 hcl.2) hpg
  refine ⟨hjc, hgerm, hs₁ge, by linarith, hmom, ?_⟩
  intro t ht
  exact hclose t ⟨by linarith [ht.1], le_min (by linarith [ht.2]) (by linarith [ht.2])⟩

end MechanicalPotential
end HamiltonianMetricGraphs
