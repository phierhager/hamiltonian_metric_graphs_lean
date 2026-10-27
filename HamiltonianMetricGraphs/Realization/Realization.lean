/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.Step

/-!
# The restricted microscopic-realization theorem

**Theorem.**  Let `Γ` be a finite metric graph with edge Hamiltonians `H_e = p²/2 + V_e(q)`
(`V` continuous on `Γ`, `C²` on each edge), `K` a compact regular energy window, and `F` a
speed-independent involutive routing law.  Let `g` be the graph-scattering trajectory of an
initial state inside an edge with energy in `K`, on the time window `[0, T]`, `T = g.stop g.N`.
Let `ε ↦ chain ε` be a thin-network family (the projected well-prepared microscopic
trajectories, with router offset, dwell time, Hamiltonian tolerance and momentum tolerance
tending to `0`) whose initial data converge to those of `g`.  Then, as `ε → 0⁺`:

1. the microscopic trajectories pass through the same sequence of routers, entering through
   the same edge-ends and leaving on the same edges (`Matches`, eventual germ equality);
2. the microscopic impact times converge to the graph impact times;
3. on every compact subset of `[0, T]` avoiding the impact times, the longitudinal state
   converges uniformly to the graph trajectory;
4. the projected state converges at every non-impact time.

The proof is a finite induction over the `N` impacts of `g` in `[0, T]` (`matches_all`), each
step being `ThinNetworkFamily.step`, followed by the last-flight estimate `final_step`.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph
open scoped Topology NNReal

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} {V : MechanicalPotential Γ} {F : RoutingLaw Γ}

set_option maxHeartbeats 800000 in
-- Same structure as `step_core` (Grönwall plus the interior margin) in one declaration.
/-- **The last flight.**  The deterministic estimate for the final flight `N` of the graph
trajectory: the microscopic flight `N` does not enter a router before the end `stop N` of the
time window, and the two flights are `Δ`-close on `[start N + δ, stop N]`. -/
theorem final_core (g : GraphTrajectory V F)
    {P R : ℝ} {K : ℝ≥0}
    (hPg : ∀ j ≤ g.N, ∀ t ∈ Icc (g.start j) (g.stop j), |(g.curve j t).2| ≤ P)
    (hR0 : 0 ≤ R) (hR : ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.force e q| ≤ R)
    (hK : ∀ e : Γ.Edge, LipschitzOnWith K (V.edgeVectorField e) (Γ.edgeStrip e))
    {δ θ Δ μ τ : ℝ} (hδ : 0 < δ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθδ : θ ≤ δ)
    (hΔ : (θ * (2 * P + 2 * R + 4) + θ * (g.stop g.N - g.start g.N)) *
        Real.exp (K * (g.stop g.N - g.start g.N)) ≤ Δ)
    (hμg : ∀ t ∈ Icc (g.start g.N + δ) (g.stop g.N),
      μ ≤ (g.curve g.N t).1 ∧ (g.curve g.N t).1 ≤ Γ.length (g.edge g.N) - μ)
    (hδT : δ ≤ g.stop g.N - g.start g.N)
    (hδτ : 2 * δ ≤ τ) (hθτ : 4 * θ ≤ τ)
    (hΔμ : Δ + θ < μ)
    {P' : ChainParams} (c : HybridChain V F P')
    (hjN : g.N ≤ c.N) (hedge : c.edge g.N = g.edge g.N)
    (hoff : P'.offset ≤ θ) (hode : P'.odeErr ≤ θ)
    (hstart : |c.start g.N - g.start g.N| ≤ θ)
    (hstate : dist (c.curve g.N (c.start g.N)) (g.curve g.N (g.start g.N)) ≤ θ)
    (hdur : τ ≤ c.stop g.N - c.start g.N)
    (hfinal : g.stop g.N ≤ c.stop c.N) :
    (g.N < c.N → g.stop g.N < c.stop g.N) ∧
    ∀ t ∈ Icc (g.start g.N + δ) (g.stop g.N), dist (c.curve g.N t) (g.curve g.N t) ≤ Δ := by
  obtain ⟨wg, hg⟩ := g.isFlight_zero le_rfl
  obtain ⟨wc, hc⟩ := c.isFlight hjN
  rw [hedge] at hc
  have hρ0 : 0 ≤ P'.odeErr := P'.odeErr_nonneg
  have ho0 : 0 ≤ P'.offset := P'.offset_nonneg
  have hs01 : c.start g.N < c.stop g.N := c.start_lt_stop g.N hjN
  have ht01 : g.start g.N < g.stop g.N := g.start_lt_stop g.N le_rfl
  have hRe := hR (g.edge g.N)
  have hPj := hPg g.N le_rfl
  have hstart' := abs_le.mp hstart
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hPj _ (left_mem_Icc.mpr ht01.le))
  have hΔ0 : 0 ≤ Δ := by
    refine le_trans ?_ hΔ
    apply mul_nonneg
    · have : 0 ≤ θ * (2 * P + 2 * R + 4) := mul_nonneg hθ (by linarith)
      have : 0 ≤ θ * (g.stop g.N - g.start g.N) := mul_nonneg hθ (by linarith)
      linarith
    · exact (Real.exp_pos _).le
  have hs₁ : g.start g.N + δ < c.stop g.N := by linarith
  -- The common interval `[m, m']`.
  set m := max (c.start g.N) (g.start g.N) with hm
  set m' := min (c.stop g.N) (g.stop g.N) with hm'
  have hm_ge : g.start g.N ≤ m := le_max_right _ _
  have hm_s₀ : c.start g.N ≤ m := le_max_left _ _
  have hm_le : m ≤ g.start g.N + θ := max_le (by linarith) (by linarith)
  have hm_le' : m ≤ c.start g.N + θ := max_le (by linarith) (by linarith)
  have hmm' : m ≤ m' := le_min (by linarith) (by linarith)
  have hm'_c : m' ≤ c.stop g.N := min_le_left _ _
  have hm'_g : m' ≤ g.stop g.N := min_le_right _ _
  have hpm : |(c.curve g.N (c.start g.N)).2| ≤ P + 1 := by
    have h1 : |(c.curve g.N (c.start g.N)).2 - (g.curve g.N (g.start g.N)).2| ≤ θ := by
      have := hstate
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at this
      exact (le_max_right _ _).trans this
    have h2 := hPj _ (left_mem_Icc.mpr ht01.le)
    calc |(c.curve g.N (c.start g.N)).2|
        = |((c.curve g.N (c.start g.N)).2 - (g.curve g.N (g.start g.N)).2) +
            (g.curve g.N (g.start g.N)).2| := by ring_nf
      _ ≤ |(c.curve g.N (c.start g.N)).2 - (g.curve g.N (g.start g.N)).2| +
            |(g.curve g.N (g.start g.N)).2| := abs_add_le _ _
      _ ≤ θ + P := add_le_add h1 h2
      _ ≤ P + 1 := by linarith
  have hcm : dist (c.curve g.N m) (c.curve g.N (c.start g.N)) ≤ (P + R + 3) * θ := by
    have hsub : V.IsFlight (g.edge g.N) P'.offset P'.odeErr (c.start g.N) m (c.curve g.N) wc :=
      hc.mono le_rfl (hmm'.trans hm'_c)
    have hspeed : ∀ u ∈ Icc (c.start g.N) m, |(c.curve g.N u).2| ≤ P + R + 2 := by
      intro u hu
      have h := hsub.abs_momentum_le ho0 hRe hpm hm_s₀ hu
      have h2 : (R + P'.odeErr) * (u - c.start g.N) ≤ (R + 1) * 1 := by
        apply mul_le_mul (by linarith) (by linarith [hu.1, hu.2]) (by linarith [hu.1])
          (by linarith)
      linarith
    have hw : ∀ u ∈ Icc (c.start g.N) m, ‖wc u‖ ≤ P + R + 3 := fun u hu =>
      (hsub.norm_w_le ho0 hRe hspeed hu).trans (max_le (by linarith) (by linarith))
    have h := hsub.dist_le hw (left_mem_Icc.mpr hm_s₀) (right_mem_Icc.mpr hm_s₀) hm_s₀
    calc dist (c.curve g.N m) (c.curve g.N (c.start g.N)) ≤ (P + R + 3) * (m - c.start g.N) :=
          h
      _ ≤ (P + R + 3) * θ := by
          have : m ≤ c.start g.N + θ := max_le (by linarith) (by linarith)
          apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hgm : dist (g.curve g.N m) (g.curve g.N (g.start g.N)) ≤ (P + R) * θ := by
    have hsub : V.IsFlight (g.edge g.N) 0 0 (g.start g.N) m (g.curve g.N) wg :=
      hg.mono le_rfl (hmm'.trans hm'_g)
    have hspeed : ∀ u ∈ Icc (g.start g.N) m, |(g.curve g.N u).2| ≤ P := fun u hu =>
      hPj u ⟨hu.1, hu.2.trans (hmm'.trans hm'_g)⟩
    have hw : ∀ u ∈ Icc (g.start g.N) m, ‖wg u‖ ≤ P + R := fun u hu =>
      (hsub.norm_w_le le_rfl hRe hspeed hu).trans (max_le (by linarith) (by linarith))
    have h := hsub.dist_le hw (left_mem_Icc.mpr hm_ge) (right_mem_Icc.mpr hm_ge) hm_ge
    calc dist (g.curve g.N m) (g.curve g.N (g.start g.N)) ≤ (P + R) * (m - g.start g.N) := h
      _ ≤ (P + R) * θ := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hd₀ : dist (c.curve g.N m) (g.curve g.N m) ≤ θ * (2 * P + 2 * R + 4) := by
    calc dist (c.curve g.N m) (g.curve g.N m)
        ≤ dist (c.curve g.N m) (c.curve g.N (c.start g.N)) +
            dist (c.curve g.N (c.start g.N)) (g.curve g.N (g.start g.N)) +
            dist (g.curve g.N (g.start g.N)) (g.curve g.N m) := dist_triangle4 _ _ _ _
      _ ≤ (P + R + 3) * θ + θ + (P + R) * θ := by
          rw [dist_comm (g.curve g.N (g.start g.N))]
          exact add_le_add (add_le_add hcm hstate) hgm
      _ = θ * (2 * P + 2 * R + 4) := by ring
  have hclose : ∀ t ∈ Icc m m', dist (c.curve g.N t) (g.curve g.N t) ≤ Δ := by
    have h := (hc.mono hm_s₀ hm'_c).dist_le_closeness (hK _) (hg.mono hm_ge hm'_g) ho0 le_rfl
      hρ0 le_rfl hmm' (mul_nonneg hθ (by linarith)) hd₀
    intro t ht
    refine (h t ht).trans (le_trans ?_ hΔ)
    apply mul_le_mul
    · have h1 : (P'.odeErr + 0) * (m' - m) ≤ θ * (g.stop g.N - g.start g.N) := by
        apply mul_le_mul (by linarith) (by linarith) (by linarith) hθ
      linarith
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) K.coe_nonneg)
    · exact (Real.exp_pos _).le
    · have : 0 ≤ θ * (2 * P + 2 * R + 4) := mul_nonneg hθ (by linarith)
      have : 0 ≤ θ * (g.stop g.N - g.start g.N) := mul_nonneg hθ (by linarith)
      linarith
  -- The microscopic flight does not end by `stop N` if it ends at a router at all.
  have hlate : g.N < c.N → g.stop g.N < c.stop g.N := by
    intro hjc
    by_contra hcon
    rw [not_lt] at hcon
    have hs₁mem : c.stop g.N ∈ Icc m m' := ⟨by linarith, le_min le_rfl hcon⟩
    have hcl := hclose _ hs₁mem
    have hμs := hμg (c.stop g.N) ⟨by linarith, hcon⟩
    have hq : |(c.curve g.N (c.stop g.N)).1 - (g.curve g.N (c.stop g.N)).1| ≤ Δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hcl
      exact (le_max_left _ _).trans hcl
    have hq' := abs_le.mp hq
    rcases c.coordinate_at_entry hjc hedge with hbd | hbd <;>
      linarith [hμs.1, hμs.2, hq'.1, hq'.2]
  have hge : g.stop g.N ≤ c.stop g.N := by
    rcases lt_or_eq_of_le hjN with h | h
    · exact (hlate h).le
    · rw [← h] at hfinal
      exact hfinal
  refine ⟨hlate, fun t ht => hclose t ⟨by linarith [ht.1], le_min (ht.2.trans hge) ht.2⟩⟩

namespace ThinNetworkFamily

variable (fam : ThinNetworkFamily V F) (g : GraphTrajectory V F)

/-- **The last flight, eventual form.**  Under the invariant for the final flight `N`: the
microscopic trajectory stays in the tube of the final edge up to the end of the time window,
and converges uniformly to the graph flight on `[start N + δ, stop N]` for every `δ > 0`. -/
theorem final_step {P R c₀ : ℝ} {K : ℝ≥0}
    (hc : GraphConstants g P R c₀ K) (hfam : fam.ConvergesInitially g)
    (hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0)))
    (hM : fam.Matches g g.N) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), g.N < (fam.chain ε).N → g.stop g.N < (fam.chain ε).stop g.N) ∧
    ∀ δ > (0 : ℝ), ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Icc (g.start g.N + δ) (g.stop g.N),
        dist ((fam.chain ε).curve g.N t) (g.curve g.N t) < η := by
  obtain ⟨τ, hτ, hdur⟩ := fam.eventually_duration_lower_bound g hc hfam hinit le_rfl hM
  have hP0 := hc.P_pos
  have hR0 := hc.R_nonneg
  have hT : 0 < g.stop g.N - g.start g.N := by linarith [g.start_lt_stop g.N le_rfl]
  set T := g.stop g.N - g.start g.N with hTdef
  set CG := (2 * P + 2 * R + 4 + T) * Real.exp (K * T) with hCGdef
  have hCG : 4 ≤ CG := by
    have h1 : 1 ≤ Real.exp (K * T) := Real.one_le_exp (by positivity)
    calc (4 : ℝ) = 4 * 1 := by ring
      _ ≤ (2 * P + 2 * R + 4 + T) * Real.exp (K * T) :=
          mul_le_mul (by linarith) h1 zero_le_one (by linarith)
  have hCGpos : 0 < CG := by linarith
  -- the core estimate for a given margin `δ` and closeness `η`
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ≤ T → δ ≤ τ / 2 → ∀ η : ℝ, 0 < η →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        (g.N < (fam.chain ε).N → g.stop g.N < (fam.chain ε).stop g.N) ∧
        ∀ t ∈ Icc (g.start g.N + δ) (g.stop g.N),
          dist ((fam.chain ε).curve g.N t) (g.curve g.N t) ≤ min η δ := by
    intro δ hδ hδ1 hδT hδτ η hη
    obtain ⟨μ, hμ, hμg⟩ := g.exists_interior_margin le_rfl (a' := g.start g.N + δ)
      (b' := g.stop g.N) (by linarith) (Icc_subset_Icc (by linarith) le_rfl) (by
        intro t ht
        rcases lt_or_eq_of_le ht.2 with hlt | heq
        · exact g.interior le_rfl ⟨by linarith [ht.1], hlt⟩
        · rw [heq]; simpa using g.final_inside)
    set Δ := min (μ / 2) (min η δ) with hΔdef
    have hΔ0 : 0 < Δ := lt_min (by positivity) (lt_min hη hδ)
    have hΔμ : Δ ≤ μ / 2 := min_le_left _ _
    have hΔη : Δ ≤ min η δ := min_le_right _ _
    have hΔδ : Δ ≤ δ := hΔη.trans (min_le_right _ _)
    set θ := Δ / CG with hθdef
    have hθ0 : 0 < θ := by positivity
    have hθΔ : θ ≤ Δ / 4 := by
      rw [hθdef]
      exact div_le_div_of_nonneg_left hΔ0.le (by norm_num) hCG
    have hΔeq : (θ * (2 * P + 2 * R + 4) + θ * T) * Real.exp (K * T) ≤ Δ := by
      have : (θ * (2 * P + 2 * R + 4) + θ * T) * Real.exp (K * T) = θ * CG := by
        rw [hCGdef]; ring
      rw [this, hθdef, div_mul_cancel₀ _ hCGpos.ne']
    filter_upwards [hM.eventually_close hθ0, fam.eventually_params_le hθ0, hfam.finalTime,
      hdur] with ε hclose hparams hfin hdurε
    obtain ⟨hjN, hedge, hstart, hstate⟩ := hclose
    obtain ⟨hoff, -, hode, -⟩ := hparams
    obtain ⟨h1, h2⟩ := final_core g hc.speed hc.R_nonneg hc.force hc.lipschitz hδ hθ0.le
      (by linarith) (by linarith) hΔeq hμg hδT (by linarith) (by linarith) (by linarith)
      (fam.chain ε) hjN hedge hoff hode hstart hstate hdurε hfin
    exact ⟨h1, fun t ht => (h2 t ht).trans hΔη⟩
  set δ₀ := min (min 1 T) (τ / 2) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min (lt_min one_pos hT) (by positivity)
  have hδ₀1 : δ₀ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₀T : δ₀ ≤ T := (min_le_left _ _).trans (min_le_right _ _)
  have hδ₀τ : δ₀ ≤ τ / 2 := min_le_right _ _
  refine ⟨?_, ?_⟩
  · filter_upwards [key _ hδ₀ hδ₀1 hδ₀T hδ₀τ 1 one_pos] with ε hε
    exact hε.1
  · intro δ hδ η hη
    have hδ' : 0 < min δ δ₀ := lt_min hδ hδ₀
    filter_upwards [key _ hδ' ((min_le_right _ _).trans hδ₀1) ((min_le_right _ _).trans hδ₀T)
      ((min_le_right _ _).trans hδ₀τ) (η / 2) (by positivity)] with ε hε
    intro t ht
    have hle : min δ δ₀ ≤ δ := min_le_left _ _
    have := hε.2 t ⟨by linarith [ht.1], ht.2⟩
    have := this.trans (min_le_left _ _)
    linarith

/-- **Finite induction over the impacts.**  The invariant holds for every flight of the graph
trajectory in the time window. -/
theorem matches_all {P R c₀ : ℝ} {K : ℝ≥0}
    (hc : GraphConstants g P R c₀ K) (hfam : fam.ConvergesInitially g)
    (hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0))) :
    ∀ j ≤ g.N, fam.Matches g j := by
  intro j
  induction j with
  | zero => intro _; exact matches_zero hfam
  | succ i ih =>
      intro hi
      exact (fam.step g hc hfam hinit (Nat.lt_of_succ_le hi) (ih (Nat.le_of_succ_le hi))).1

end ThinNetworkFamily

/-- **Restricted microscopic-realization theorem.**  Let `K` be a compact regular energy window,
`g` a graph-scattering trajectory (routing law `F`) with energy in `K` starting inside an edge,
and `fam` a thin-network family whose well-prepared initial data converge to those of `g` and
whose chains cover the time window `[0, stop N]` of `g`.  Then as `ε → 0⁺`:

* (`matches`) every flight `j ≤ N` of `g` is matched by the flight `j` of the microscopic
  chains: same edge, converging start times and start states;
* (`impacts`) for every impact `j < N` the microscopic impact time converges to the graph
  impact time, and the microscopic trajectory eventually enters the router through the graph
  edge-end `g.germ j` (hence leaves along `F_v (g.germ j)`);
* (`flights`) on `[start j + δ, stop j - δ]` (`j < N`) the microscopic longitudinal state
  converges uniformly to the graph flight, for every `δ > 0`;
* (`last`) on `[start N + δ, stop N]` the same holds for the last flight, which does not enter
  a router before the end of the window. -/
theorem microscopic_realization [Nonempty Γ.Edge] (K : Set ℝ) (hK : IsCompact K)
    (hreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies)
    (g : GraphTrajectory V F) (hE : g.energy ∈ K)
    (hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0)))
    (fam : ThinNetworkFamily V F) (hfam : fam.ConvergesInitially g) :
    (∀ j ≤ g.N, fam.Matches g j) ∧
    (∀ j < g.N, Tendsto (fun ε => (fam.chain ε).stop j) (𝓝[>] 0) (𝓝 (g.stop j)) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), j < (fam.chain ε).N ∧ (fam.chain ε).germ j = g.germ j) ∧
    (∀ j < g.N, ∀ δ > (0 : ℝ), ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Icc (g.start j + δ) (g.stop j - δ),
        dist ((fam.chain ε).curve j t) (g.curve j t) < η) ∧
    ((∀ᶠ ε in 𝓝[>] (0 : ℝ), g.N < (fam.chain ε).N →
        g.stop g.N < (fam.chain ε).stop g.N) ∧
      ∀ δ > (0 : ℝ), ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∀ t ∈ Icc (g.start g.N + δ) (g.stop g.N),
          dist ((fam.chain ε).curve g.N t) (g.curve g.N t) < η) := by
  obtain ⟨P, R, c₀, KL, hc⟩ := exists_graphConstants K hK hreg g hE
  have hall := fam.matches_all g hc hfam hinit
  refine ⟨hall, fun j hj => ?_, fun j hj => ?_, fam.final_step g hc hfam hinit (hall g.N le_rfl)⟩
  · obtain ⟨-, h1, h2, -⟩ := fam.step g hc hfam hinit hj (hall j hj.le)
    exact ⟨h1, h2⟩
  · exact (fam.step g hc hfam hinit hj (hall j hj.le)).2.2.2

/-- **Convergence of the projected state at non-impact times.**  If `t` lies strictly inside
flight `j` of the graph trajectory (or in `(start N, stop N]` for the last flight), then
eventually the microscopic chain is in its flight `j` at time `t`, on the graph edge, and its
longitudinal state at time `t` converges to the graph state. -/
theorem microscopic_realization_state [Nonempty Γ.Edge] (K : Set ℝ) (hK : IsCompact K)
    (hreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies)
    (g : GraphTrajectory V F) (hE : g.energy ∈ K)
    (hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0)))
    (fam : ThinNetworkFamily V F) (hfam : fam.ConvergesInitially g)
    {j : ℕ} (hj : j ≤ g.N) {t : ℝ} (ht : g.start j < t)
    (ht' : t < g.stop j ∨ (j = g.N ∧ t ≤ g.stop j)) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (fam.chain ε).flightIndex t = j ∧ (fam.chain ε).edge j = g.edge j) ∧
    Tendsto (fun ε => (fam.chain ε).curve j t) (𝓝[>] 0) (𝓝 (g.curve j t)) := by
  obtain ⟨hall, himp, hfl, hlast⟩ := microscopic_realization K hK hreg g hE hinit fam hfam
  have hM := hall j hj
  -- the flight index is eventually `j`
  have hidx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (fam.chain ε).flightIndex t = j := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (fam.chain ε).start j < t :=
      (Metric.tendsto_nhds.mp hM.start) (t - g.start j) (by linarith) |>.mono (by
        intro ε hε
        rw [Real.dist_eq] at hε
        have := (abs_lt.mp hε).2
        linarith)
    have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), j < (fam.chain ε).N → t < (fam.chain ε).start (j + 1) := by
      rcases lt_or_ge j g.N with hjN | hjN
      · -- the next start converges to the next graph start `stop j > t`
        have hM' := hall (j + 1) hjN
        have ht'' : t < g.stop j := by
          rcases ht' with h | h
          · exact h
          · exact absurd h.1 (Nat.ne_of_lt hjN)
        have := (Metric.tendsto_nhds.mp hM'.start) (g.stop j - t) (by linarith)
        filter_upwards [this] with ε hε _
        rw [Real.dist_eq, g.start_succ_eq_stop hjN] at hε
        have := (abs_lt.mp hε).1
        linarith
      · have hjeq : j = g.N := le_antisymm hj hjN
        subst hjeq
        filter_upwards [hlast.1] with ε hε hjc
        have h3 := (fam.chain ε).stop_le_start_succ g.N hjc
        have h4 := hε hjc
        rcases ht' with h | h
        · linarith
        · linarith [h.2]
    filter_upwards [hM.eventually, h1, h2] with ε hε h1 h2
    exact (fam.chain ε).flightIndex_eq_of_mem hε.1 h1.le h2
  refine ⟨?_, ?_⟩
  · filter_upwards [hidx, hM.eventually] with ε h1 h2
    exact ⟨h1, h2.2⟩
  · rw [Metric.tendsto_nhds]
    intro η hη
    rcases lt_or_ge j g.N with hjN | hjN
    · have ht'' : t < g.stop j := by
        rcases ht' with h | h
        · exact h
        · exact absurd h.1 (Nat.ne_of_lt hjN)
      have hδ : 0 < min (t - g.start j) (g.stop j - t) := lt_min (by linarith) (by linarith)
      filter_upwards [hfl j hjN _ hδ η hη] with ε hε
      exact hε t ⟨by linarith [min_le_left (t - g.start j) (g.stop j - t)],
        by linarith [min_le_right (t - g.start j) (g.stop j - t)]⟩
    · have hjeq : j = g.N := le_antisymm hj hjN
      subst hjeq
      have htle : t ≤ g.stop g.N := by
        rcases ht' with h | h
        · exact h.le
        · exact h.2
      filter_upwards [hlast.2 (t - g.start g.N) (by linarith) η hη] with ε hε
      exact hε t ⟨by linarith, htle⟩

end MechanicalPotential
end HamiltonianMetricGraphs
