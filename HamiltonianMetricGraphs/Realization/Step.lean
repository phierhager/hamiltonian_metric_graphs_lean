/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.StepCore

/-!
# The induction step in the thin-network limit

This file turns the deterministic estimate `step_core` into statements about the family
`ε ↦ chain ε` as `ε → 0⁺`:

* `GraphConstants`: the uniform constants attached to a graph trajectory with energy in a
  compact regular window (speed bound, force bound, Lipschitz constant, impact speed);
* `eventually_duration_lower_bound`: the microscopic flight `j` lasts at least a fixed positive
  time (no early re-entry into a router), from `IsFlight.duration_lower_bound_*`;
* `step_quant`: for every small margin `δ`, eventually the microscopic impact time, impact
  momentum and flight are `O(δ)`-close to those of the graph trajectory;
* `step`: the invariant `Matches j` propagates to `Matches (j+1)`, together with convergence of
  the impact times, eventual equality of the impact germs, and uniform convergence of the flights
  away from the impact times.

Mathematical proof step: one round of the "finite induction over the finitely many impacts".
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph
open scoped Topology NNReal

namespace RoutingLaw

/-- The departure momentum is `1`-Lipschitz in the arriving momentum. -/
theorem abs_departureMomentum_sub_le {Γ : FiniteMetricGraph} (F : RoutingLaw Γ) (η : Γ.EdgeEnd)
    (p p' : ℝ) : |F.departureMomentum η p - F.departureMomentum η p'| ≤ |p - p'| := by
  unfold departureMomentum
  have : -(F.routeGerm η).sign * |p| - -(F.routeGerm η).sign * |p'| =
      -(F.routeGerm η).sign * (|p| - |p'|) := by ring
  rw [this, abs_mul, abs_neg, edgeEnd_abs_sign, one_mul]
  exact abs_abs_sub_abs_le_abs_sub p p'

end RoutingLaw

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} {V : MechanicalPotential Γ} {F : RoutingLaw Γ}

/-- The uniform constants of a graph trajectory with energy in a compact regular window. -/
structure GraphConstants (g : GraphTrajectory V F) (P R c₀ : ℝ) (K : ℝ≥0) : Prop where
  P_pos : 0 < P
  speed : ∀ j ≤ g.N, ∀ t ∈ Icc (g.start j) (g.stop j), |(g.curve j t).2| ≤ P
  R_nonneg : 0 ≤ R
  force : ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.force e q| ≤ R
  lipschitz : ∀ e : Γ.Edge, LipschitzOnWith K (V.edgeVectorField e) (Γ.edgeStrip e)
  c₀_pos : 0 < c₀
  impact : ∀ j < g.N, c₀ ≤ EdgeEnd.sign Γ (g.germ j) * (g.curve j (g.stop j)).2

/-- Every graph trajectory with energy in a compact regular window has such constants. -/
theorem exists_graphConstants [Nonempty Γ.Edge] (K : Set ℝ) (hK : IsCompact K)
    (hreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) (g : GraphTrajectory V F)
    (hE : g.energy ∈ K) :
    ∃ (P R c₀ : ℝ) (KL : ℝ≥0), GraphConstants g P R c₀ KL := by
  obtain ⟨P, hP, hspeed⟩ := V.exists_graph_speed_bound F K hK
  obtain ⟨R, hR0, hR⟩ := V.exists_force_bound
  obtain ⟨KL, hKL⟩ := V.exists_uniform_lipschitz_edgeVectorField
  obtain ⟨c₀, hc₀, himpact⟩ := V.exists_impact_speed_lower_bound F K hK hreg
  exact ⟨P, R, c₀, KL, ⟨hP, hspeed g hE, hR0, hR, hKL, hc₀, himpact g hE⟩⟩

namespace ThinNetworkFamily

variable (fam : ThinNetworkFamily V F) (g : GraphTrajectory V F)

/-- **No early end of the microscopic flight.**  Under the invariant `Matches j`, the
microscopic flight `j` eventually lasts at least a fixed positive time.  For `j = 0` this uses
that the initial state is inside the edge; for `j ≥ 1` it uses that the flight departs a vertex
with speed at least `c₀` (`IsFlight.duration_lower_bound_departure`). -/
theorem eventually_duration_lower_bound {P R c₀ : ℝ} {K : ℝ≥0}
    (hc : GraphConstants g P R c₀ K) (hfam : fam.ConvergesInitially g)
    (hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0)))
    {j : ℕ} (hj : j ≤ g.N) (hM : fam.Matches g j) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      τ ≤ (fam.chain ε).stop j - (fam.chain ε).start j := by
  have hT : 0 < g.stop j - g.start j := by linarith [g.start_lt_stop j hj]
  have hL := Γ.length_pos (g.edge j)
  have hP0 := hc.P_pos
  have hR0 := hc.R_nonneg
  have hc₀ := hc.c₀_pos
  -- the momentum bound at the graph start state
  have hPstart : |(g.curve j (g.start j)).2| ≤ P :=
    hc.speed j hj _ (left_mem_Icc.mpr (g.start_lt_stop j hj).le)
  rcases j with _ | i
  · -- flight `0`: interior start
    set μ₀ := min (g.curve 0 0).1 (Γ.length (g.edge 0) - (g.curve 0 0).1) with hμ₀def
    have hμ₀ : 0 < μ₀ := lt_min hinit.1 (by linarith [hinit.2])
    have hμ₀q : μ₀ ≤ (g.curve 0 0).1 := min_le_left _ _
    have hμ₀L : μ₀ ≤ Γ.length (g.edge 0) - (g.curve 0 0).1 := min_le_right _ _
    set θ := min 1 (min (μ₀ / 4) ((g.stop 0 - g.start 0) / 2)) with hθdef
    have hθ : 0 < θ := lt_min one_pos (lt_min (by positivity) (by positivity))
    have hθ1 : θ ≤ 1 := min_le_left _ _
    have hθμ : θ ≤ μ₀ / 4 := (min_le_right _ _).trans (min_le_left _ _)
    have hθT : θ ≤ (g.stop 0 - g.start 0) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨min (min 1 (μ₀ / 2 / (P + 1 + R + 2))) ((g.stop 0 - g.start 0) / 2),
      lt_min (lt_min one_pos (by positivity)) (by positivity), ?_⟩
    filter_upwards [hM.eventually_close hθ, fam.eventually_params_le hθ, hfam.finalTime] with
      ε hclose hparams hfin
    obtain ⟨hjN, hedge, -, hstate⟩ := hclose
    obtain ⟨hoff, -, hode, -⟩ := hparams
    set c := fam.chain ε with hcdef
    rw [g.start_zero] at hstate
    rw [c.start_zero] at hstate
    have hq : |(c.curve 0 0).1 - (g.curve 0 0).1| ≤ θ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hstate
      exact (le_max_left _ _).trans hstate
    have hp : |(c.curve 0 0).2 - (g.curve 0 0).2| ≤ θ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hstate
      exact (le_max_right _ _).trans hstate
    rcases lt_or_eq_of_le hjN with hlt | heq
    · obtain ⟨w, hw⟩ := c.isFlight hjN
      rw [hedge] at hw
      have hend := c.coordinate_at_entry hlt hedge
      have hB : |(c.curve 0 (c.start 0)).2| ≤ P + 1 := by
        rw [c.start_zero]
        rw [g.start_zero] at hPstart
        have := abs_le.mp hp
        rw [abs_le] at hPstart ⊢
        constructor <;> linarith [this.1, this.2]
      have hstart' : (c.curve 0 (c.start 0)).1 ∈
          Icc ((fam.params ε).offset + μ₀ / 2)
            (Γ.length (g.edge 0) - (fam.params ε).offset - μ₀ / 2) := by
        rw [c.start_zero]
        have := abs_le.mp hq
        constructor <;> linarith [this.1, this.2]
      have key := hw.duration_lower_bound_interior (c.start_lt_stop 0 hjN) (hc.force _) hR0
        (hode.trans hθ1) (fam.params ε).offset_nonneg hB hstart' hend
      exact (min_le_left _ _).trans key
    · rw [← heq] at hfin
      have h1 := g.stop_le_stop_N hj
      have h2 : c.start 0 = 0 := c.start_zero
      have h3 : g.start 0 = 0 := g.start_zero
      have h4 := min_le_right (min 1 (μ₀ / 2 / (P + 1 + R + 2))) ((g.stop 0 - g.start 0) / 2)
      linarith
  · -- flight `i + 1`: departure from a vertex
    have hi : i < g.N := Nat.lt_of_succ_le hj
    set ζ := F.routeGerm (g.germ i) with hζdef
    have hζe : ζ.1 = g.edge (i + 1) := (g.edge_succ i hi).symm
    have hσ : |EdgeEnd.sign Γ (g.germ i)| = 1 := RoutingLaw.edgeEnd_abs_sign _
    have hout_g : EdgeEnd.sign Γ ζ * (g.curve (i + 1) (g.start (i + 1))).2 ≤ -c₀ := by
      rw [g.depart_mom_eq hi, F.sign_mul_departureMomentum]
      have h1 := hc.impact i hi
      have : |(g.curve i (g.stop i)).2| =
          |EdgeEnd.sign Γ (g.germ i) * (g.curve i (g.stop i)).2| := by
        rw [abs_mul, hσ, one_mul]
      rw [this, abs_of_pos (lt_of_lt_of_le hc₀ h1)]
      linarith
    have hq_g : (g.curve (i + 1) (g.start (i + 1))).1 = EdgeEnd.coordinate Γ ζ :=
      g.depart_coord_eq hi
    set θ := min 1 (min (c₀ / 8) (min (Γ.length (g.edge (i + 1)) / 4)
      ((g.stop (i + 1) - g.start (i + 1)) / 2))) with hθdef
    have hθ : 0 < θ := lt_min one_pos (lt_min (by positivity) (lt_min (by positivity)
      (by positivity)))
    have hθ1 : θ ≤ 1 := min_le_left _ _
    have hθc : θ ≤ c₀ / 8 := (min_le_right _ _).trans (min_le_left _ _)
    have hθL : θ ≤ Γ.length (g.edge (i + 1)) / 4 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hθT : θ ≤ (g.stop (i + 1) - g.start (i + 1)) / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨min (min (c₀ / 2 / (2 * (R + 2)))
      (Γ.length (g.edge (i + 1)) / (2 * (P + 1 + c₀ / 2 + 2))))
      ((g.stop (i + 1) - g.start (i + 1)) / 2),
      lt_min (lt_min (by positivity) (by positivity)) (by positivity), ?_⟩
    filter_upwards [hM.eventually_close hθ, fam.eventually_params_le hθ, hfam.finalTime] with
      ε hclose hparams hfin
    obtain ⟨hjN, hedge, hstart, hstate⟩ := hclose
    obtain ⟨hoff, -, hode, -⟩ := hparams
    set c := fam.chain ε with hcdef
    have hq : |(c.curve (i + 1) (c.start (i + 1))).1 - (g.curve (i + 1) (g.start (i + 1))).1| ≤
        θ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hstate
      exact (le_max_left _ _).trans hstate
    have hp : |(c.curve (i + 1) (c.start (i + 1))).2 - (g.curve (i + 1) (g.start (i + 1))).2| ≤
        θ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hstate
      exact (le_max_right _ _).trans hstate
    rcases lt_or_eq_of_le hjN with hlt | heq
    · obtain ⟨w, hw⟩ := c.isFlight hjN
      rw [hedge] at hw
      have hstart' : |(c.curve (i + 1) (c.start (i + 1))).1 - EdgeEnd.coordinate Γ ζ| ≤
          Γ.length (g.edge (i + 1)) / 4 := by
        rw [← hq_g]
        exact hq.trans hθL
      have hout_c : EdgeEnd.sign Γ ζ * (c.curve (i + 1) (c.start (i + 1))).2 ≤ -(c₀ / 2) := by
        have hσζ : |EdgeEnd.sign Γ ζ| = 1 := RoutingLaw.edgeEnd_abs_sign _
        have h2 : |EdgeEnd.sign Γ ζ * ((c.curve (i + 1) (c.start (i + 1))).2 -
            (g.curve (i + 1) (g.start (i + 1))).2)| ≤ θ := by
          rw [abs_mul, hσζ, one_mul]; exact hp
        have h3 := (abs_le.mp h2).2
        have : EdgeEnd.sign Γ ζ * (c.curve (i + 1) (c.start (i + 1))).2 =
            EdgeEnd.sign Γ ζ * (g.curve (i + 1) (g.start (i + 1))).2 +
              EdgeEnd.sign Γ ζ * ((c.curve (i + 1) (c.start (i + 1))).2 -
                (g.curve (i + 1) (g.start (i + 1))).2) := by ring
        linarith
      have hB : |(c.curve (i + 1) (c.start (i + 1))).2| ≤ P + 1 := by
        have := abs_le.mp hp
        rw [abs_le] at hPstart ⊢
        constructor <;> linarith [this.1, this.2]
      have hζ' : (c.germ (i + 1)).1 = g.edge (i + 1) := by
        rw [c.germ_edge (i + 1) hlt, hedge]
      have key := hw.duration_lower_bound_departure (c.start_lt_stop (i + 1) hjN) (hc.force _)
        hR0 (hode.trans hθ1) (fam.params ε).offset_nonneg (hoff.trans hθL) hζe hstart'
        (by positivity : 0 < c₀ / 2) (by linarith [hode.trans hθc]) hout_c hB hζ'
        (c.arrive (i + 1) hlt)
      exact (min_le_left _ _).trans key
    · rw [← heq] at hfin
      have h1 := g.stop_le_stop_N hj
      have h2 := abs_le.mp hstart
      linarith [min_le_right (min (c₀ / 2 / (2 * (R + 2)))
        (Γ.length (g.edge (i + 1)) / (2 * (P + 1 + c₀ / 2 + 2))))
        ((g.stop (i + 1) - g.start (i + 1)) / 2), h2.2]

/-- **Quantitative step.**  For every sufficiently small margin `δ`, eventually the microscopic
flight `j` ends by entering the router through the graph germ, its impact time and impact
momentum are `O(δ)`-close to the graph ones, and the flights are `δ`-close on
`[start j + δ, stop j - δ]`. -/
theorem step_quant {P R c₀ : ℝ} {K : ℝ≥0}
    (hc : GraphConstants g P R c₀ K) (hfam : fam.ConvergesInitially g)
    {j : ℕ} (hj : j < g.N) (hM : fam.Matches g j)
    {τ : ℝ} (hτ : 0 < τ)
    (hdur : ∀ᶠ ε in 𝓝[>] (0 : ℝ), τ ≤ (fam.chain ε).stop j - (fam.chain ε).start j) :
    ∃ δmax : ℝ, 0 < δmax ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δmax →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        j < (fam.chain ε).N ∧ (fam.chain ε).germ j = g.germ j ∧
        |(fam.chain ε).stop j - g.stop j| ≤ (1 + 8 * (P + 1) / c₀) * δ ∧
        |((fam.chain ε).curve j ((fam.chain ε).stop j)).2 - (g.curve j (g.stop j)).2| ≤
          ((R + 1) * (8 * (P + 1) / c₀) + 1 + R) * δ ∧
        ∀ t ∈ Icc (g.start j + δ) (g.stop j - δ),
          dist ((fam.chain ε).curve j t) (g.curve j t) ≤ δ := by
  have hP0 := hc.P_pos
  have hR0 := hc.R_nonneg
  have hc₀ := hc.c₀_pos
  have hT : 0 < g.stop j - g.start j := by linarith [g.start_lt_stop j hj.le]
  have hL := Γ.length_pos (g.edge j)
  have hgap : 0 < g.stop (j + 1) - g.stop j := by
    have := g.start_lt_stop (j + 1) hj
    rw [g.start_succ_eq_stop hj] at this
    linarith
  set T := g.stop j - g.start j with hTdef
  set L := Γ.length (g.edge j) with hLdef
  set gap := g.stop (j + 1) - g.stop j with hgapdef
  set CG := (2 * P + 2 * R + 4 + T) * Real.exp (K * T) with hCGdef
  have hCG : 4 ≤ CG := by
    have h1 : 1 ≤ Real.exp (K * T) := Real.one_le_exp (by positivity)
    calc (4 : ℝ) = 4 * 1 := by ring
      _ ≤ (2 * P + 2 * R + 4 + T) * Real.exp (K * T) :=
          mul_le_mul (by linarith) h1 zero_le_one (by linarith)
  have hCGpos : 0 < CG := by linarith
  refine ⟨min (min (T / 2) (τ / 2)) (min (min (c₀ / (2 * (R + 1))) (L / (4 * (P + 1))))
    (min (c₀ ^ 2 / (64 * (P + 1) * (R + 2))) (min (c₀ * gap / (8 * (P + 1))) 1))),
    lt_min (lt_min (by positivity) (by positivity)) (lt_min (lt_min (by positivity)
      (by positivity)) (lt_min (by positivity) (lt_min (by positivity) one_pos))), ?_⟩
  intro δ hδ hδmax
  have hδT : δ ≤ T / 2 := hδmax.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδτ : δ ≤ τ / 2 := hδmax.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδc : δ ≤ c₀ / (2 * (R + 1)) :=
    hδmax.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hδL : δ ≤ L / (4 * (P + 1)) :=
    hδmax.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hδhor : δ ≤ c₀ ^ 2 / (64 * (P + 1) * (R + 2)) :=
    hδmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδgap : δ ≤ c₀ * gap / (8 * (P + 1)) :=
    hδmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hδ1 : δ ≤ 1 :=
    hδmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  -- interior margin of the graph flight on `[start j + δ, stop j - δ]`
  obtain ⟨μ, hμ, hμg⟩ := g.exists_interior_margin hj.le (a' := g.start j + δ)
    (b' := g.stop j - δ) (by linarith) (Icc_subset_Icc (by linarith) (by linarith))
    (fun t ht => g.interior hj.le ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  set Δ := min (μ / 2) δ with hΔdef
  have hΔ0 : 0 < Δ := lt_min (by positivity) hδ
  have hΔμ : Δ ≤ μ / 2 := min_le_left _ _
  have hΔδ : Δ ≤ δ := min_le_right _ _
  set θ := Δ / CG with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθΔ : θ ≤ Δ / 4 := by
    rw [hθdef]
    exact div_le_div_of_nonneg_left hΔ0.le (by norm_num) hCG
  have hΔeq : (θ * (2 * P + 2 * R + 4) + θ * T) * Real.exp (K * T) ≤ Δ := by
    have : (θ * (2 * P + 2 * R + 4) + θ * T) * Real.exp (K * T) = θ * CG := by
      rw [hCGdef]; ring
    rw [this, hθdef, div_mul_cancel₀ _ hCGpos.ne']
  -- the smallness conditions of `step_core`
  have hδc' : R * δ + Δ ≤ c₀ / 2 := by
    rw [le_div_iff₀ (by positivity)] at hδc
    linarith
  have hdL : P * δ + Δ ≤ L / 4 := by
    rw [le_div_iff₀ (by positivity)] at hδL
    linarith
  have hhor : 8 * (P * δ + Δ) / c₀ < c₀ / (4 * (R + 2)) := by
    rw [div_lt_div_iff₀ hc₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hδhor
    have h1 : P * δ + Δ ≤ (P + 1) * δ := by linarith
    have h2 : 0 < c₀ ^ 2 := by positivity
    nlinarith
  have hgap' : 8 * (P * δ + Δ) / c₀ ≤ gap := by
    rw [div_le_iff₀ hc₀]
    rw [le_div_iff₀ (by positivity)] at hδgap
    linarith
  have hRδ : 0 ≤ R * δ := mul_nonneg hR0 hδ.le
  have hPδ : 0 ≤ P * δ := mul_nonneg hP0.le hδ.le
  filter_upwards [hM.eventually_close hθ0, fam.eventually_params_le hθ0, hfam.finalTime, hdur]
    with ε hclose hparams hfin hdurε
  obtain ⟨hjN, hedge, hstart, hstate⟩ := hclose
  obtain ⟨hoff, -, hode, -⟩ := hparams
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := step_core g hc.speed hc.R_nonneg hc.force hc.lipschitz
    hc.c₀_pos hc.impact hj hδ hθ0.le (by linarith) (by linarith) hΔeq hμg (by linarith)
    (by linarith) (by linarith) (by linarith) hδc' (by linarith) hdL (by linarith)
    hhor hgap' (fam.chain ε) hjN hedge hoff hode hstart hstate hdurε hfin
  have hpos : 0 ≤ 8 * (P + 1) / c₀ := by positivity
  have hbound : 8 * (P * δ + Δ) / c₀ ≤ 8 * (P + 1) / c₀ * δ := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc₀]
    linarith
  refine ⟨h1, h2, ?_, ?_, fun t ht => (h6 t ht).trans hΔδ⟩
  · rw [abs_le]
    constructor
    · have : 0 ≤ 8 * (P + 1) / c₀ * δ := mul_nonneg hpos hδ.le
      linarith
    · linarith
  · calc |((fam.chain ε).curve j ((fam.chain ε).stop j)).2 - (g.curve j (g.stop j)).2|
        ≤ (R + 1) * (8 * (P * δ + Δ) / c₀) + Δ + R * δ := h5
      _ ≤ (R + 1) * (8 * (P + 1) / c₀ * δ) + δ + R * δ := by
          have := mul_le_mul_of_nonneg_left hbound (by linarith : (0 : ℝ) ≤ R + 1)
          linarith
      _ = ((R + 1) * (8 * (P + 1) / c₀) + 1 + R) * δ := by ring

/-- **The induction step.**  From the invariant for flight `j < N` we obtain the invariant for
flight `j + 1`, convergence of the `j`-th impact time, eventual equality of the impact germ, and
uniform convergence of the flights on `[start j + δ, stop j - δ]` for every `δ > 0`. -/
theorem step {P R c₀ : ℝ} {K : ℝ≥0}
    (hc : GraphConstants g P R c₀ K) (hfam : fam.ConvergesInitially g)
    (hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0)))
    {j : ℕ} (hj : j < g.N) (hM : fam.Matches g j) :
    fam.Matches g (j + 1) ∧
    Tendsto (fun ε => (fam.chain ε).stop j) (𝓝[>] 0) (𝓝 (g.stop j)) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), j < (fam.chain ε).N ∧ (fam.chain ε).germ j = g.germ j) ∧
    ∀ δ > (0 : ℝ), ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Icc (g.start j + δ) (g.stop j - δ),
        dist ((fam.chain ε).curve j t) (g.curve j t) < η := by
  obtain ⟨τ, hτ, hdur⟩ := fam.eventually_duration_lower_bound g hc hfam hinit hj.le hM
  obtain ⟨δmax, hδmax, hq⟩ := fam.step_quant g hc hfam hj hM hτ hdur
  have hP0 := hc.P_pos
  have hR0 := hc.R_nonneg
  have hc₀ := hc.c₀_pos
  set C₁ := 1 + 8 * (P + 1) / c₀ with hC₁
  set C₂ := (R + 1) * (8 * (P + 1) / c₀) + 1 + R with hC₂
  have hC₁ : 1 ≤ C₁ := by
    have : 0 ≤ 8 * (P + 1) / c₀ := by positivity
    linarith
  have hC₂ : 1 ≤ C₂ := by
    have : 0 ≤ (R + 1) * (8 * (P + 1) / c₀) := by positivity
    linarith
  -- eventual facts at the maximal margin
  have hev := hq δmax hδmax le_rfl
  -- convergence of the impact time
  have hstop : Tendsto (fun ε => (fam.chain ε).stop j) (𝓝[>] 0) (𝓝 (g.stop j)) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    have hδ : 0 < min δmax (η / (2 * C₁)) := lt_min hδmax (by positivity)
    filter_upwards [hq _ hδ (min_le_left _ _)] with ε hε
    rw [Real.dist_eq]
    calc |(fam.chain ε).stop j - g.stop j| ≤ C₁ * min δmax (η / (2 * C₁)) := hε.2.2.1
      _ ≤ C₁ * (η / (2 * C₁)) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
      _ = η / 2 := by field_simp; try ring
      _ < η := by linarith
  refine ⟨?_, hstop, ?_, ?_⟩
  · -- the invariant for flight `j + 1`
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [hev] with ε hε
      refine ⟨hε.1, ?_⟩
      rw [(fam.chain ε).edge_succ j hε.1, hε.2.1, g.edge_succ j hj]
    · rw [Metric.tendsto_nhds]
      intro η hη
      have hδ : 0 < min δmax (η / (4 * C₁)) := lt_min hδmax (by positivity)
      filter_upwards [hq _ hδ (min_le_left _ _), fam.eventually_params_le (by positivity :
        (0 : ℝ) < η / 4)] with ε hε hparams
      have h1 : |(fam.chain ε).stop j - g.stop j| ≤ η / 4 := by
        calc |(fam.chain ε).stop j - g.stop j| ≤ C₁ * min δmax (η / (4 * C₁)) := hε.2.2.1
          _ ≤ C₁ * (η / (4 * C₁)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
          _ = η / 4 := by field_simp; try ring
      have h2 := (fam.chain ε).stop_le_start_succ j hε.1
      have h3 := (fam.chain ε).start_succ_le j hε.1
      have h4 := hparams.2.1
      rw [Real.dist_eq, g.start_succ_eq_stop hj, abs_lt]
      have := abs_le.mp h1
      constructor <;> linarith [this.1, this.2]
    · rw [Metric.tendsto_nhds]
      intro η hη
      have hδ : 0 < min δmax (η / (4 * C₂)) := lt_min hδmax (by positivity)
      filter_upwards [hq _ hδ (min_le_left _ _), fam.eventually_params_le (by positivity :
        (0 : ℝ) < η / 4)] with ε hε hparams
      obtain ⟨hjc, hgerm, -, hmom, -⟩ := hε
      set c := fam.chain ε with hcdef
      have hmom' : |(c.curve j (c.stop j)).2 - (g.curve j (g.stop j)).2| ≤ η / 4 := by
        calc |(c.curve j (c.stop j)).2 - (g.curve j (g.stop j)).2|
            ≤ C₂ * min δmax (η / (4 * C₂)) := hmom
          _ ≤ C₂ * (η / (4 * C₂)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
          _ = η / 4 := by field_simp; try ring
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      apply max_lt
      · rw [c.depart_coord j hjc, g.depart_coord_eq hj, hgerm]
        have hσ : |EdgeEnd.sign Γ (F.routeGerm (g.germ j))| = 1 := RoutingLaw.edgeEnd_abs_sign _
        have : EdgeEnd.coordinate Γ (F.routeGerm (g.germ j)) -
            EdgeEnd.sign Γ (F.routeGerm (g.germ j)) * (fam.params ε).offset -
            EdgeEnd.coordinate Γ (F.routeGerm (g.germ j)) =
            -(EdgeEnd.sign Γ (F.routeGerm (g.germ j)) * (fam.params ε).offset) := by ring
        rw [this, abs_neg, abs_mul, hσ, one_mul, abs_of_nonneg (fam.params ε).offset_nonneg]
        linarith [hparams.1]
      · rw [g.depart_mom_eq hj]
        have h1 := c.depart_mom j hjc
        rw [hgerm] at h1
        have h2 := F.abs_departureMomentum_sub_le (g.germ j) (c.curve j (c.stop j)).2
          (g.curve j (g.stop j)).2
        have h3 := hparams.2.2.2
        calc |(c.curve (j + 1) (c.start (j + 1))).2 -
              F.departureMomentum (g.germ j) (g.curve j (g.stop j)).2|
            = |((c.curve (j + 1) (c.start (j + 1))).2 -
                F.departureMomentum (g.germ j) (c.curve j (c.stop j)).2) +
                (F.departureMomentum (g.germ j) (c.curve j (c.stop j)).2 -
                  F.departureMomentum (g.germ j) (g.curve j (g.stop j)).2)| := by ring_nf
          _ ≤ |(c.curve (j + 1) (c.start (j + 1))).2 -
                F.departureMomentum (g.germ j) (c.curve j (c.stop j)).2| +
                |F.departureMomentum (g.germ j) (c.curve j (c.stop j)).2 -
                  F.departureMomentum (g.germ j) (g.curve j (g.stop j)).2| := abs_add_le _ _
          _ ≤ η / 4 + η / 4 := add_le_add (h1.trans h3) (h2.trans hmom')
          _ < η := by linarith
  · filter_upwards [hev] with ε hε
    exact ⟨hε.1, hε.2.1⟩
  · intro δ hδ η hη
    have hδ' : 0 < min δ (min δmax (η / 2)) := lt_min hδ (lt_min hδmax (by positivity))
    filter_upwards [hq _ hδ' ((min_le_right _ _).trans (min_le_left _ _))] with ε hε
    intro t ht
    have hle : min δ (min δmax (η / 2)) ≤ δ := min_le_left _ _
    have hle' : min δ (min δmax (η / 2)) ≤ η / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have := hε.2.2.2.2 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    linarith

end ThinNetworkFamily

end MechanicalPotential
end HamiltonianMetricGraphs
