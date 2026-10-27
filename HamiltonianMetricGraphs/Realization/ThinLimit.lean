/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ThinRun
import HamiltonianMetricGraphs.Realization.Realization
import HamiltonianMetricGraphs.Realization.BranchingRealization

/-!
# The thin-junction Hamiltonian limit theorem

This file proves the **general thin-junction limit theorem** (Theorem IX.6 of the paper,
`thm:thin-limit`): if a thin network satisfies the hypotheses (E) and (J) of `ThinHypotheses.lean`
for a routing law `F` on a compact window `K ⊂ (max_Γ V, ∞)` — asymptotically one-dimensional
edge dynamics, and a junction that routes by `F` within a vanishing residence time — then the
projected flow `pr Φ^ε_t(z_ε)` of prepared, not arriving initial states `z_ε` with converging
projections converges, on every finite time interval, to the metric-graph flow with vertex law
`F`.

The chain of the abstract machinery is *derived*, not assumed: `ThinRun.chain` builds it by finite
induction from (E) and (J), and `microscopic_realization` then propagates the local estimates over
the finitely many impacts in `[0, T]`.  The window condition `K ⊂ (max_Γ V, ∞)` enters through the
speed bound of `ThinFlightBounds.lean`, which makes the run cover the time window; it also implies
`K ∩ Exc = ∅`, the hypothesis of `microscopic_realization`.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {Γ : FiniteMetricGraph}

/-! ### Extracting a threshold from an eventual statement -/

theorem exists_Ioo_of_eventually_nhdsGT {P : ℝ → Prop} (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Ioo (0 : ℝ) δ, P ε := by
  rw [eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset] at h
  obtain ⟨u, hu, hsub⟩ := h
  exact ⟨u, hu, fun ε hε => hsub hε⟩

/-! ### Well-prepared initial data -/

/-- **Prepared initial data of the microscopic family** (the data `z_ε` of Theorem IX.6).  At
every scale `ε ∈ (0, ε₀)` the state `z_ε = (x₀ ε, p₀ ε)` is prepared towards `germ` and not
arriving there, and its projection `pr_e(z_ε)` converges to a graph state `(q, r)`. -/
structure WellPreparedInitialState (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ)
    (K : Set ℝ) (ε₀ : ℝ) where
  /-- the end `η₀` towards which the particle initially moves -/
  germ : Γ.EdgeEnd
  /-- the initial microscopic configuration at scale `ε` -/
  x₀ : ℝ → ℝ × ℝ
  /-- the initial microscopic momentum at scale `ε` -/
  p₀ : ℝ → ℝ × ℝ
  /-- `z_ε` is prepared towards `η₀` -/
  prepared : ∀ ε ∈ Ioo (0 : ℝ) ε₀, N.Prepared V K ε germ (x₀ ε) (p₀ ε)
  /-- `z_ε` is not arriving at `η₀` -/
  not_arriving : ∀ ε ∈ Ioo (0 : ℝ) ε₀, ¬ N.Arriving V K ε germ (x₀ ε) (p₀ ε)
  /-- the limiting graph coordinate -/
  q : ℝ
  /-- the limiting graph momentum -/
  r : ℝ
  /-- `pr_e(z_ε) → (q, r)` -/
  converges : Tendsto (fun ε => N.gState germ.1 (x₀ ε) (p₀ ε)) (𝓝[>] 0) (𝓝 (q, r))

variable {N : ThinHamiltonianNetwork Γ} {V : MechanicalPotential Γ} {K : Set ℝ} {ε₀ : ℝ}
  {F : RoutingLaw Γ}

/-- **`g` is the graph limit trajectory of the microscopic initial data `x₀`.** -/
def IsThinGraphLimit (x₀ : WellPreparedInitialState N V K ε₀)
    (g : GraphTrajectory V F) : Prop :=
  g.germ 0 = x₀.germ ∧ g.edge 0 = x₀.germ.1 ∧ g.curve 0 0 = (x₀.q, x₀.r)

/-! ### The microscopic certificate -/

/-- **A hybrid chain is the graph projection of a genuine microscopic trajectory.**  There is a
solution of Hamilton's equations for `H_ε` on the whole time window whose image under the
projection `π_ε` is the chain, and whose transverse displacement stays inside the tube. -/
def IsThinProjection (N : ThinHamiltonianNetwork Γ) (ε : ℝ) {P : ChainParams}
    (ch : HybridChain V F P) : Prop :=
  ∃ (S : ℝ) (Θ : N.MicroTrajectory ε S), ch.stop ch.N ≤ S ∧
    ∀ j ≤ ch.N, ∀ t ∈ Icc (ch.start j) (ch.stop j),
      ch.curve j t = N.gState (ch.edge j) (Θ.x t) (Θ.p t) ∧
        |N.trans (ch.edge j) (Θ.x t)| ≤ N.tubeWidth ε

theorem IsThinProjection.congr_scale {a b : ℝ} (hab : a = b) {P : ChainParams}
    {ch : HybridChain V F P} (h : IsThinProjection N a ch) : IsThinProjection N b ch := by
  subst hab; exact h

/-- **A hybrid chain is the graph projection of the flow through the given initial data.**  The
image of `Φ^ε_t(z_ε)`, `z_ε = (x₀ ε, p₀ ε)`, under the projection `π_ε` is the chain, and its
transverse displacement stays inside the tube. -/
def IsThinProjectionFrom (N : ThinHamiltonianNetwork Γ) (x₀ : WellPreparedInitialState N V K ε₀)
    (ε : ℝ) {P : ChainParams} (ch : HybridChain V F P) : Prop :=
  ∀ j ≤ ch.N, ∀ t ∈ Icc (ch.start j) (ch.stop j),
    ch.curve j t = N.gState (ch.edge j) (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).1
        (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).2 ∧
      |N.trans (ch.edge j) (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).1| ≤ N.tubeWidth ε

theorem IsThinProjectionFrom.congr_scale {x₀ : WellPreparedInitialState N V K ε₀} {a b : ℝ}
    (hab : a = b) {P : ChainParams} {ch : HybridChain V F P}
    (h : IsThinProjectionFrom N x₀ a ch) : IsThinProjectionFrom N x₀ b ch := by
  subst hab; exact h

theorem IsThinProjectionFrom.isThinProjection {x₀ : WellPreparedInitialState N V K ε₀} {ε : ℝ}
    {P : ChainParams} {ch : HybridChain V F P} (h : IsThinProjectionFrom N x₀ ε ch) :
    IsThinProjection N ε ch :=
  ⟨ch.stop ch.N, N.flowTraj ε (x₀.x₀ ε, x₀.p₀ ε) (ch.stop ch.N), le_rfl, h⟩

/-- The conclusion of the realization theorem: matching of the routed edge sequence, convergence
of the junction entrance times together with agreement of the entry germs, and uniform
convergence of the projected longitudinal state away from the impacts. -/
def ThinRealizes (fam : ThinNetworkFamily V F) (g : GraphTrajectory V F) : Prop :=
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
        dist ((fam.chain ε).curve g.N t) (g.curve g.N t) < η)

/-- **The projected microscopic Hamiltonian trajectories converge to `g` on `[0, T]`.** -/
def ThinTrajectoryConvergesTo (N : ThinHamiltonianNetwork Γ)
    (_x₀ : WellPreparedInitialState N V K ε₀) (g : GraphTrajectory V F) (T : ℝ) : Prop :=
  ∃ fam : ThinNetworkFamily V F,
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsThinProjection N ε (fam.chain ε)) ∧
    fam.ConvergesInitially g ∧ T ≤ g.stop g.N ∧ ThinRealizes fam g

/-! ### The run at a given scale -/

/-- The microscopic run at the scale `ε`: the flow through the prepared initial state, the
hypotheses (E) and (J), and the window constants. -/
noncomputable def thinRunAt (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ)
    (K : Set ℝ) (F : RoutingLaw Γ) {ε₀ : ℝ}
    (hEdge : N.SatisfiesEdgeReduction V K ε₀)
    (hJunction : N.JunctionScatteringConvergesTo V K F ε₀)
    (x₀ : WellPreparedInitialState N V K ε₀) (n : ℕ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) ε₀)
    (hoff : 2 * N.offset ε < minEdgeLen Γ x₀.germ.1) {g Kmax Vmin : ℝ}
    (hgap : ∀ E ∈ K, ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), V.extension e q + g ≤ E)
    (hKmax : ∀ E ∈ K, E ≤ Kmax)
    (hVmin : ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), Vmin ≤ V.extension e q)
    (hγ : ∀ e : Γ.Edge, N.forceErr ε * Γ.length e < g) : ThinRun N V K F ε n where
  germ₀ := x₀.germ
  x₀ := x₀.x₀ ε
  p₀ := x₀.p₀ ε
  eps_pos := hε.1
  offset_lt := hoff
  init := x₀.prepared ε hε
  init_toGo :=
    ThinHamiltonianNetwork.toGo_pos_of_not_arriving (x₀.prepared ε hε) (x₀.not_arriving ε hε)
  edgeRed := hEdge ε hε
  jct := hJunction ε hε
  gap := g
  Kmax := Kmax
  Vmin := Vmin
  gap_le := hgap
  le_Kmax := hKmax
  Vmin_le := hVmin
  forceErr_lt := hγ

/-! ### The theorem -/

/-- **The scale threshold of the theorem.**  For a window above the potential there are constants
`g > 0`, `Kmax`, `Vmin` (`exists_window_constants`) and a threshold `ε₁ ∈ (0, ε₀]` below which the
junction regions are small (`4 δ_ε < ℓ_min`) and the force error is below the gap
(`γ_ε ℓ_e < g`). -/
theorem exists_thin_threshold (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ)
    {K : Set ℝ} (hK : IsCompact K) (hwin : V.IsWindowAbove K) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (e₀ : Γ.Edge) :
    ∃ g Kmax Vmin ε₁ : ℝ, 0 < g ∧ (∀ E ∈ K, E ≤ Kmax) ∧
      (∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e),
        Vmin ≤ V.extension e q ∧ ∀ E ∈ K, V.extension e q + g ≤ E) ∧
      0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₁,
        4 * N.offset ε < minEdgeLen Γ e₀ ∧ ∀ e : Γ.Edge, N.forceErr ε * Γ.length e < g := by
  obtain ⟨g, Kmax, Vmin, hg, hKmax, hV⟩ := V.exists_window_constants hK hwin
  have hL : 0 < minEdgeLen Γ e₀ := minEdgeLen_pos Γ e₀
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), N.offset ε < minEdgeLen Γ e₀ / 4 :=
    eventually_lt_of_tendsto_nhds_zero N.offset_tendsto (by linarith)
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ e : Γ.Edge, N.forceErr ε * Γ.length e < g := by
    refine Filter.eventually_all.mpr fun e => ?_
    have ht : Tendsto (fun ε => N.forceErr ε * Γ.length e) (𝓝[>] 0) (𝓝 0) := by
      simpa using N.forceErr_tendsto.mul_const (Γ.length e)
    exact eventually_lt_of_tendsto_nhds_zero ht hg
  obtain ⟨δ, hδ, hδP⟩ := exists_Ioo_of_eventually_nhdsGT (h1.and h2)
  refine ⟨g, Kmax, Vmin, min ε₀ δ, hg, hKmax, hV, lt_min hε₀ hδ, min_le_left _ _,
    fun ε hε => ?_⟩
  obtain ⟨hε1, hε2⟩ := hδP ε ⟨hε.1, lt_of_lt_of_le hε.2 (min_le_right _ _)⟩
  exact ⟨by linarith, hε2⟩

set_option maxHeartbeats 1000000 in
-- the family is a large concrete structure assembled in one proof
/-- **The family of projected runs.**  Under the hypotheses of Theorem IX.6 there is a family of
hybrid chains, one per scale, whose chain at scale `ε` is eventually the projection of the flow
`Φ^ε_t(z_ε)` (`IsThinProjectionFrom`), with initial data converging to those of `g` and covering
the time window of `g`.  The chain at scale `ε` is `ThinRun.chain` of the run `thinRunAt` at the
scale `clampEps ε₁ ε`, with `n` passages chosen from the speed bound of the window. -/
theorem thin_family_exists
    (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (F : RoutingLaw Γ)
    (K : Set ℝ) (hK : IsCompact K) (hwin : V.IsWindowAbove K)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hEdge : N.SatisfiesEdgeReduction V K ε₀)
    (hJunction : N.JunctionScatteringConvergesTo V K F ε₀)
    (x₀ : WellPreparedInitialState N V K ε₀)
    (g : GraphTrajectory V F) (hg : IsThinGraphLimit x₀ g) :
    ∃ fam : ThinNetworkFamily V F,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsThinProjectionFrom N x₀ ε (fam.chain ε)) ∧
        fam.ConvergesInitially g := by
  classical
  obtain ⟨gp, Kmax, Vmin, ε₁, hgp, hKmax, hV, hε₁, hε₁₀, hsmall⟩ :=
    exists_thin_threshold N V hK hwin hε₀ x₀.germ.1
  set L : ℝ := minEdgeLen Γ x₀.germ.1 with hLdef
  have hL : 0 < L := minEdgeLen_pos Γ x₀.germ.1
  set M : ℝ := 1 + 2 * |Kmax + gp - Vmin| with hMdef
  have hM : 0 < M := by positivity
  set d₀ : ℝ := L / (2 * M) with hd₀def
  have hd₀ : 0 < d₀ := div_pos hL (by linarith)
  have hmem : ∀ e : ℝ, clampEps ε₁ e ∈ Ioo (0 : ℝ) ε₀ := by
    intro e
    obtain ⟨h1, h2⟩ := clampEps_mem hε₁ e
    exact ⟨h1, lt_of_lt_of_le h2 hε₁₀⟩
  have hsm := fun e : ℝ => hsmall (clampEps ε₁ e) (clampEps_mem hε₁ e)
  have hoff4 : ∀ e : ℝ, 4 * N.offset (clampEps ε₁ e) < L := fun e => (hsm e).1
  have hoff : ∀ e : ℝ, 2 * N.offset (clampEps ε₁ e) < L := by
    intro e
    have h1 := hoff4 e
    have h2 := N.offset_nonneg (clampEps ε₁ e)
    linarith
  -- the number of junction passages
  set n : ℕ := ⌈g.stop g.N / d₀⌉₊ + 1 with hndef
  have hn1 : ((n : ℝ) - 1) = (⌈g.stop g.N / d₀⌉₊ : ℝ) := by rw [hndef]; push_cast; ring
  have hnT : g.stop g.N ≤ ((n : ℝ) - 1) * d₀ := by
    rw [hn1]
    have hceil : g.stop g.N / d₀ ≤ (⌈g.stop g.N / d₀⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hd₀] at hceil
    linarith
  -- the run at each scale
  set run : ∀ e : ℝ, ThinRun N V K F (clampEps ε₁ e) n :=
    fun e => thinRunAt N V K F hEdge hJunction x₀ n (hmem e) (hoff e)
      (fun E hE e' q hq => (hV e' q hq).2 E hE) hKmax (fun e' q hq => (hV e' q hq).1)
      (hsm e).2 with hrundef
  have hminDur : ∀ e : ℝ, d₀ ≤ (run e).minDur := by
    intro e
    have h1 := hoff4 e
    have hgeq : (run e).minDur = (L - 2 * N.offset (clampEps ε₁ e)) / M := rfl
    rw [hgeq, hd₀def, div_le_div_iff₀ (by linarith) hM]
    nlinarith
  have heps : ∀ᶠ e in 𝓝[>] (0 : ℝ), clampEps ε₁ e = e :=
    eventually_nhdsGT_zero_of_forall_Ioo hε₁ (fun e he => clampEps_eq he.1 he.2)
  -- the thin-network family
  set fam : ThinNetworkFamily V F :=
    { params := fun e => thinParams N (clampEps ε₁ e)
      chain := fun e => (run e).chain
      offset_tendsto := by
        refine Tendsto.congr' ?_ (N.offset_tendsto.comp tendsto_id)
        filter_upwards [heps] with e he
        rw [thinParams_offset, he]
        rfl
      dwell_tendsto := by
        refine Tendsto.congr' ?_ (N.dwell_tendsto.comp tendsto_id)
        filter_upwards [heps] with e he
        rw [thinParams_dwell, he]
        rfl
      odeErr_tendsto := by
        refine Tendsto.congr' ?_ (N.forceErr_tendsto.comp tendsto_id)
        filter_upwards [heps] with e he
        rw [thinParams_odeErr, he]
        rfl
      momErr_tendsto := by
        refine Tendsto.congr' ?_ (N.momErr_tendsto.comp tendsto_id)
        filter_upwards [heps] with e he
        rw [thinParams_momErr, he]
        rfl } with hfamdef
  obtain ⟨hgerm, hedge, hcurve⟩ := hg
  refine ⟨fam, ?_, ?_⟩
  · -- the microscopic certificate
    filter_upwards [heps] with e he
    refine IsThinProjectionFrom.congr_scale he ?_
    exact (run e).chain_is_projection
  · -- convergence of the initial data
    refine ⟨Filter.Eventually.of_forall (fun e => ?_), ?_, ?_⟩
    · change ((run e).germ 0).1 = g.edge 0
      rw [hedge]
      rfl
    · have hfun : ∀ e : ℝ, (fam.chain e).curve 0 0 =
          N.gState x₀.germ.1 (x₀.x₀ (clampEps ε₁ e)) (x₀.p₀ (clampEps ε₁ e)) :=
        fun e => (run e).chain_curve_zero_zero
      rw [hcurve]
      refine Tendsto.congr (fun e => (hfun e).symm) ?_
      refine Tendsto.congr' ?_ x₀.converges
      filter_upwards [heps] with e he
      rw [he]
    · refine Filter.Eventually.of_forall (fun e => ?_)
      have h1 := (run e).stopT_lower
      have h2 := hminDur e
      have h3 : (0 : ℝ) ≤ (n : ℝ) - 1 := by rw [hn1]; positivity
      change g.stop g.N ≤ (run e).stopT n
      nlinarith

/-- **The thin-junction Hamiltonian limit theorem** (Theorem IX.6).

Let a thin network over `Γ` satisfy (E) and (J) for a routing law `F` on a compact window `K`
above the potential, `K ⊂ (max_Γ V, ∞)` (`V.IsWindowAbove K`).  Let `z_ε` be prepared towards
`η₀`, not arriving at `η₀`, with `pr_e(z_ε) → (q, r)` (`x₀ : WellPreparedInitialState`), and let
`g` be the graph trajectory from `(q, r)` (`IsThinGraphLimit`).  Then, on every finite time
interval `[0, T]`, the projected flow `pr Φ^ε_t(z_ε)` converges to `g`
(`ThinTrajectoryConvergesTo`): the microscopic run passes through the same routers through the same
ends, its impact times converge to those of `g`, and its projected state converges to `g`
uniformly away from the impacts.

Neither the projected `HybridChain` nor its four convergence parameters are assumed: the chain is
built from (E) and (J) by `ThinRun.chain`, and the global convergence is then the finite induction
of `microscopic_realization` over the impacts in `[0, T]`. -/
theorem thin_junction_hamiltonian_limit
    (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (F : RoutingLaw Γ)
    (K : Set ℝ) (hK : IsCompact K) (hwin : V.IsWindowAbove K)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hEdge : N.SatisfiesEdgeReduction V K ε₀)
    (hJunction : N.JunctionScatteringConvergesTo V K F ε₀)
    (x₀ : WellPreparedInitialState N V K ε₀)
    (g : GraphTrajectory V F) (hg : IsThinGraphLimit x₀ g) (hE : g.energy ∈ K)
    (hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0)))
    {T : ℝ} (hT : T ≤ g.stop g.N) :
    ThinTrajectoryConvergesTo N x₀ g T := by
  obtain ⟨fam, hcert, hconv⟩ := thin_family_exists N V F K hK hwin hε₀ hEdge hJunction x₀ g hg
  haveI : Nonempty Γ.Edge := ⟨x₀.germ.1⟩
  exact ⟨fam, hcert.mono fun _ h => h.isThinProjection, hconv, hT,
    microscopic_realization K hK hwin.not_mem_exceptionalEnergies g hE hinit fam hconv⟩

end HamiltonianMetricGraphs
