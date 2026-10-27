/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ThinLimitExactItinerary

/-!
# Theorem IX.6 as printed: the times `α_j^ε`, `β_j^ε` and the Euclidean distance

`thin_junction_global_flow_limit_from_start` (`ThinLimitInitial.lean`) proves part (c) of
Theorem IX.6 of the paper (`thm:thin-limit`), but two differences from the printed statement
remain there:

1. the arrival and departure times of the microscopic trajectory, and the facts (a), (b) about
   them, are only carried inside the chain family (`ThinRealizes`, `ThinNetworkFamily`), and the
   inclusion `I ∩ [τ_j, τ_{j+1}) ⊆ [β_j^ε, α_{j+1}^ε]` of part (c) is only used internally;
2. distances in the plane are the sup-distances of `ℝ × ℝ`, while the paper uses the Euclidean
   norm `|·|`.

This file removes both: `thin_network_limit` states (a), (b), (c) literally, with the times
`α_j^ε`, `β_j^ε` as functions of `ε`, the predicates `Arriving`, `Departing` of
`ThinHypotheses.lean`, the dwell `θ_ε = N.dwell ε`, the graph itinerary `η_j = F.itinerary η₀ j`
(`η_{j+1} = \overline{F(η_j)}`, Lemma IX.2), the impact times `τ_j` of the paper's flow
`Φ_t = FlightState.trajectory V (F.toBorelScattering V) a`, and the Euclidean distance
`planeDist u v = √((u₁ - v₁)² + (u₂ - v₂)²)`.

## The mathematics

* **The graph side** is Lemma IX.2 (`graph_itinerary`, `ThinLimitExactItinerary.lean`): above
  the potential every flight lands, the chain of the flow is infinite, the impact times
  `τ_j = impactReal V S a j` are genuine and strictly increasing (for every `T ≥ 0` there is
  exactly one `n` with `τ_n ≤ T < τ_{n+1}`, `existsUnique_impact_index`), and the first flight
  lands at the end `η₀` towards which `p` points (`flight_above`).
* **The times.**  The family of the proof of Theorem IX.6 (`thin_family_exists`) is built from the
  runs `ThinRun.chain`, whose flight `j` ends at the arrival time of (E) and whose flight `j + 1`
  starts at the departure time of (J).  `thin_run_family_exists` rebuilds that family and exports
  these facts (`IsThinRunFrom`): `α_{j+1}^ε = stop j` (arriving at `η_j`) and
  `β_{j+1}^ε = start (j + 1)` (departing through `F(η_j)`, within `θ_ε`).
* **The window.**  The graph trajectory is taken through `n + 1` impacts
  (`FlowRun S a (n + 1) TM`, `τ_{n+1} < TM < τ_{n+2}`), so that the convergence of the impact
  times (`ThinRealizes`) also gives `α_{n+1}^ε → τ_{n+1}`.
* **Part (c).**  The inclusion is `ThinNetworkFamily.window_close`, the convergence is
  `ThinConvergesOnCompacts`, and `planeDist ≤ 2 dist` (`planeDist_le_two_mul_dist`) converts the
  sup-distance into the Euclidean one.

## Main statements

* `planeDist` — the Euclidean distance of `ℝ²`; `planeDist_eq_dist_toLp` identifies it with the
  distance of `WithLp 2 (ℝ × ℝ)`.
* `thin_network_limit_of_flightState` — Theorem IX.6, (a), (b), (c), for a flight state `a` at
  `z` whose first flight lands at `η₀`.
* `thin_network_limit` — Theorem IX.6 as printed, with `z = (e, q, p)` given as in the paper and
  the flight state built from it; the compatibility of `η₀` is proved, not assumed.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

/-! ### The Euclidean distance of the plane -/

/-- **The Euclidean distance `|u - v| = √((u₁ - v₁)² + (u₂ - v₂)²)` of `ℝ²`**, the norm `|·|` of
the paper, both on the configuration plane and on the phase plane of an edge.  (The distance of
`ℝ × ℝ` in Mathlib is the maximum distance.) -/
noncomputable def planeDist (u v : ℝ × ℝ) : ℝ :=
  Real.sqrt ((u.1 - v.1) ^ 2 + (u.2 - v.2) ^ 2)

/-- `planeDist` is the distance of the Euclidean plane `WithLp 2 (ℝ × ℝ)`. -/
theorem planeDist_eq_dist_toLp (u v : ℝ × ℝ) :
    planeDist u v = dist (WithLp.toLp 2 u) (WithLp.toLp 2 v) := by
  rw [WithLp.prod_dist_eq_of_L2, planeDist]
  simp [Real.dist_eq, sq_abs]

/-- The Euclidean distance is at most twice the maximum distance. -/
theorem planeDist_le_two_mul_dist (u v : ℝ × ℝ) : planeDist u v ≤ 2 * dist u v := by
  have h1 : |u.1 - v.1| ≤ dist u v := by
    rw [Prod.dist_eq, Real.dist_eq]; exact le_max_left _ _
  have h2 : |u.2 - v.2| ≤ dist u v := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact le_max_right _ _
  have h0 : 0 ≤ dist u v := dist_nonneg
  rw [planeDist, Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  have s1 : (u.1 - v.1) ^ 2 ≤ dist u v ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have s2 : (u.2 - v.2) ^ 2 ≤ dist u v ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  nlinarith

/-! ### The arrival and departure times of the run -/

variable {Γ : FiniteMetricGraph} {N : ThinHamiltonianNetwork Γ} {V : MechanicalPotential Γ}
  {K : Set ℝ} {ε₀ : ℝ} {F : RoutingLaw Γ}

/-- **The chain records the arrivals and departures of the flow through `z_ε`.**  For every
passage `j < N` of the chain: the chain enters along the graph itinerary `η_j = F.itinerary η₀ j`,
the flow `Φ^ε_t(z_ε)` is arriving at `η_j` at the time `stop j`, it is departing through `F(η_j)`
at the later time `start (j + 1)`, and `start (j + 1) - stop j ≤ θ_ε`. -/
def IsThinRunFrom (N : ThinHamiltonianNetwork Γ) (x₀ : WellPreparedInitialState N V K ε₀)
    (ε : ℝ) {P : ChainParams} (ch : HybridChain V F P) : Prop :=
  ∀ j < ch.N, ch.germ j = F.itinerary x₀.germ j ∧ ch.stop j < ch.start (j + 1) ∧
    ch.start (j + 1) ≤ ch.stop j + N.dwell ε ∧
    N.Arriving V K ε (F.itinerary x₀.germ j) (N.flow ε (ch.stop j) (x₀.x₀ ε, x₀.p₀ ε)).1
      (N.flow ε (ch.stop j) (x₀.x₀ ε, x₀.p₀ ε)).2 ∧
    N.Departing V K ε (F.routeGerm (F.itinerary x₀.germ j))
      (N.flow ε (ch.start (j + 1)) (x₀.x₀ ε, x₀.p₀ ε)).1
      (N.flow ε (ch.start (j + 1)) (x₀.x₀ ε, x₀.p₀ ε)).2

theorem IsThinRunFrom.congr_scale {x₀ : WellPreparedInitialState N V K ε₀} {a b : ℝ}
    (hab : a = b) {P : ChainParams} {ch : HybridChain V F P}
    (h : IsThinRunFrom N x₀ a ch) : IsThinRunFrom N x₀ b ch := by
  subst hab; exact h

/-- The chain of the run `thinRunAt` at the scale `ε` records the arrivals (E2) and the departures
(J) of the flow through `z_ε`. -/
theorem thinRunAt_isThinRunFrom (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ)
    (K : Set ℝ) (F : RoutingLaw Γ) {ε₀ : ℝ}
    (hEdge : N.SatisfiesEdgeReduction V K ε₀)
    (hJunction : N.JunctionScatteringConvergesTo V K F ε₀)
    (x₀ : WellPreparedInitialState N V K ε₀) (n : ℕ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) ε₀)
    (hoff : 2 * N.offset ε < minEdgeLen Γ x₀.germ.1) {g Kmax Vmin : ℝ}
    (hgap : ∀ E ∈ K, ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), V.extension e q + g ≤ E)
    (hKmax : ∀ E ∈ K, E ≤ Kmax)
    (hVmin : ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), Vmin ≤ V.extension e q)
    (hγ : ∀ e : Γ.Edge, N.forceErr ε * Γ.length e < g) :
    IsThinRunFrom N x₀ ε
      (thinRunAt N V K F hEdge hJunction x₀ n hε hoff hgap hKmax hVmin hγ).chain := by
  set R := thinRunAt N V K F hEdge hJunction x₀ n hε hoff hgap hKmax hVmin hγ with hRdef
  intro j hj
  change j < n at hj
  have hinv := R.inv j
  have hpass := hinv.passage
  have hstop : R.chain.stop j = R.arriveT j := R.stopT_of_lt hj
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [hstop]; exact hpass.lt
  · rw [hstop]; exact hpass.le
  · rw [hstop]; exact hinv.flight.arrive
  · exact hpass.depart

set_option maxHeartbeats 1000000 in
-- the family is a large concrete structure assembled in one proof
/-- **The family of projected runs, with its arrival and departure times.**  The family of
`thin_family_exists` (the same construction, repeated here so that its runs remain visible), with
the additional certificate `IsThinRunFrom`: eventually, the chain at scale `ε` records the
arrivals and departures of the flow `Φ^ε_t(z_ε)`. -/
theorem thin_run_family_exists
    (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (F : RoutingLaw Γ)
    (K : Set ℝ) (hK : IsCompact K) (hwin : V.IsWindowAbove K)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hEdge : N.SatisfiesEdgeReduction V K ε₀)
    (hJunction : N.JunctionScatteringConvergesTo V K F ε₀)
    (x₀ : WellPreparedInitialState N V K ε₀)
    (g : GraphTrajectory V F) (hg : IsThinGraphLimit x₀ g) :
    ∃ fam : ThinNetworkFamily V F,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsThinProjectionFrom N x₀ ε (fam.chain ε)) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsThinRunFrom N x₀ ε (fam.chain ε)) ∧
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
  refine ⟨fam, ?_, ?_, ?_⟩
  · -- the microscopic certificate
    filter_upwards [heps] with e he
    refine IsThinProjectionFrom.congr_scale he ?_
    exact (run e).chain_is_projection
  · -- the arrivals and departures
    filter_upwards [heps] with e he
    refine IsThinRunFrom.congr_scale he ?_
    exact thinRunAt_isThinRunFrom N V K F hEdge hJunction x₀ n (hmem e) (hoff e) _ _ _ _
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

/-! ### Theorem IX.6 -/

/-- **The thin-network limit, Theorem IX.6 of the paper (`thm:thin-limit`), as printed.**

Let a thin network `N` over `Γ` satisfy (E) and (J) on a compact window `K ⊂ (max_Γ V, ∞)` for a
routing law `F`.  Let `a` be the graph state `z = (e, q, p)`, `0 < q < ℓ_e`, `E = H_e(q, p) ∈ K`,
whose first flight lands at `η₀ = x₀.germ`, and let `z_ε = (x₀.x₀ ε, x₀.p₀ ε)` be prepared towards
`η₀`, not arriving at `η₀`, with `pr_e(z_ε) → (q, p)`.  Write `Φ_t(z) = (e(t), q(t), p(t))` for the
paper's flow `FlightState.trajectory V (F.toBorelScattering V) a`, `τ_j = impactReal V S a j` for
its vertex impact times (`τ₀ = 0`; they exist for all `j`, `iterate_isSome_of_isWindowAbove`),
`η_j = F.itinerary η₀ j` for the graph itinerary of Lemma IX.2 (`η_{j+1} = \overline{F(η_j)}`),
and `z_ε(t) = Φ^ε_t(z_ε) = N.flow ε t z_ε = (x_ε(t), ξ_ε(t))`.  Let `n` satisfy
`τ_n ≤ T < τ_{n+1}` (it exists and is unique, `existsUnique_impact_index`).

Then there are times `α_j^ε = α j ε`, `β_j^ε = β j ε`, with `β_0^ε = 0`, such that for all
sufficiently small `ε`, `β_j^ε < α_{j+1}^ε` (`0 ≤ j ≤ n`) and `α_j^ε < β_j^ε` (`1 ≤ j ≤ n`), and

* (a) for `1 ≤ j ≤ n`, `z_ε(α_j^ε)` is arriving at `η_{j-1}`, `z_ε(β_j^ε)` is departing through
  `F(η_{j-1})`, and `β_j^ε - α_j^ε ≤ θ_ε`;
* (b) `α_j^ε, β_j^ε → τ_j` for `1 ≤ j ≤ n`, and `α_{n+1}^ε → τ_{n+1}`;
* (c) for every compact `I ⊆ [0, T] \ {τ₁, …, τₙ}` and each `j = 0, …, n`, eventually
  `I ∩ [τ_j, τ_{j+1}) ⊆ [β_j^ε, α_{j+1}^ε]`, and
  `sup_{t ∈ I} |pr_{e(t)} z_ε(t) - (q(t), p(t))| → 0`,
  `sup_{t ∈ I} |x_ε(t) - b_{e(t)} - q(t) τ_{e(t)}| → 0`,
  with `|·|` the Euclidean norm (`planeDist`).

The hypothesis `T > 0` of the paper is not needed (`τ_n ≤ T` already gives `T ≥ 0`). -/
theorem thin_network_limit_of_flightState [Nonempty Γ.Edge]
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
    {T : ℝ} {n : ℕ}
    (hn : FlightState.impactReal V (F.toBorelScattering V) a n ≤ T ∧
      T < FlightState.impactReal V (F.toBorelScattering V) a (n + 1)) :
    ∃ α β : ℕ → ℝ → ℝ, (∀ ε, β 0 ε = 0) ∧
      -- the order of the times
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ j ≤ n, β j ε < α (j + 1) ε) ∧
        ∀ j ∈ Icc 1 n, α j ε < β j ε) ∧
      -- (a)
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j ∈ Icc 1 n,
        N.Arriving V K ε (F.itinerary x₀.germ (j - 1))
          (N.flow ε (α j ε) (x₀.x₀ ε, x₀.p₀ ε)).1 (N.flow ε (α j ε) (x₀.x₀ ε, x₀.p₀ ε)).2 ∧
        N.Departing V K ε (F.routeGerm (F.itinerary x₀.germ (j - 1)))
          (N.flow ε (β j ε) (x₀.x₀ ε, x₀.p₀ ε)).1 (N.flow ε (β j ε) (x₀.x₀ ε, x₀.p₀ ε)).2 ∧
        β j ε - α j ε ≤ N.dwell ε) ∧
      -- (b)
      (∀ j ∈ Icc 1 n,
        Tendsto (α j) (𝓝[>] 0) (𝓝 (FlightState.impactReal V (F.toBorelScattering V) a j)) ∧
        Tendsto (β j) (𝓝[>] 0) (𝓝 (FlightState.impactReal V (F.toBorelScattering V) a j))) ∧
      Tendsto (α (n + 1)) (𝓝[>] 0)
        (𝓝 (FlightState.impactReal V (F.toBorelScattering V) a (n + 1))) ∧
      -- (c)
      ∀ I : Set ℝ, IsCompact I → I ⊆ Icc (0 : ℝ) T →
        (∀ j ∈ Icc 1 n, FlightState.impactReal V (F.toBorelScattering V) a j ∉ I) →
        (∀ j ≤ n, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          I ∩ Ico (FlightState.impactReal V (F.toBorelScattering V) a j)
              (FlightState.impactReal V (F.toBorelScattering V) a (j + 1)) ⊆
            Icc (β j ε) (α (j + 1) ε)) ∧
        ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ I,
          planeDist
            (N.gState (FlightState.trajectory V (F.toBorelScattering V) a t).1
              (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).1 (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).2)
            (FlightState.trajectory V (F.toBorelScattering V) a t).2 < η ∧
          planeDist (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).1
            (N.base (FlightState.trajectory V (F.toBorelScattering V) a t).1 +
              (FlightState.trajectory V (F.toBorelScattering V) a t).2.1 •
                N.tang (FlightState.trajectory V (F.toBorelScattering V) a t).1) < η := by
  set S := F.toBorelScattering V with hS
  set τ : ℕ → ℝ := FlightState.impactReal V S a with hτ
  have hreg := hwin.not_mem_exceptionalEnergies
  -- the vertex impacts exist (Lemma IX.2)
  have hchain := FlightState.iterate_isSome_of_isWindowAbove S hwin a hE
  have hτlt : ∀ j, τ j < τ (j + 1) := fun j =>
    FlightState.impactReal_lt_succ_of_isSome (V := V) (hchain (j + 1))
  -- the window of the graph flow through `n + 1` impacts
  set TM : ℝ := (τ (n + 1) + τ (n + 2)) / 2 with hTM
  have h12 := hτlt (n + 1)
  have hR : FlightState.FlowRun S a (n + 1) TM := by
    refine ⟨hchain (n + 1), by rw [hTM]; linarith, fun _ => ?_⟩
    have hdur := FlightState.impactReal_succ_flow (S := S) (a := a) (j := n + 1) (hchain (n + 2))
    change TM - τ (n + 1) < _
    have : τ (n + 1 + 1) = τ (n + 1) + FlightState.flowDur S a (n + 1) := hdur
    rw [hTM]
    linarith
  set g : GraphTrajectory V F := hR.chain (F := F) with hgdef
  have hgN : g.N = n + 1 := rfl
  have hgstart : ∀ j, g.start j = τ j := fun _ => rfl
  have hgstop : ∀ j < n + 1, g.stop j = τ (j + 1) := fun j hj =>
    FlightState.flowStop_of_lt (S := S) (a := a) (TM := TM) hj
  have hgstopN : g.stop g.N = TM := hR.chain_stop_N
  have hTTM : T ≤ TM := by rw [hTM]; linarith [hn.2]
  have hgflow : ∀ t ∈ Icc (0 : ℝ) T, g.state t = FlightState.trajectory V S a t :=
    fun t ht => hR.chain_state_eq ⟨ht.1, ht.2.trans hTTM⟩
  have hlimit : IsThinGraphLimit x₀ g :=
    ⟨by rw [hR.chain_germ_zero, hgerm], by rw [hR.chain_edge_zero, hedge],
      by rw [hR.chain_curve_zero, hstate]⟩
  have hEg : g.energy ∈ K := by
    change V.hamiltonian (g.edge 0) (g.curve 0 0).1 (g.curve 0 0).2 ∈ K
    rw [hR.chain_edge_zero, hR.chain_curve_zero]
    exact hE
  have hinitg : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0)) := by
    rw [hR.chain_curve_zero, hR.chain_edge_zero]
    exact hinit
  -- the family of runs
  obtain ⟨fam, hcert, hrun, hconv⟩ :=
    thin_run_family_exists N V F K hK hwin hε₀ hEdge hJunction x₀ g hlimit
  have hReal := microscopic_realization K hK hreg g hEg hinitg fam hconv
  have hStart := fam.initial_window g K hK hreg hEg hinitg hconv
  have hcpt : ThinConvergesOnCompacts N x₀ g T :=
    ThinTrajectoryConvergesFromStart.thinConvergesOnCompacts
      ⟨fam, hcert, hconv, by rw [hgstopN]; exact hTTM, hReal, hStart⟩
  -- the passages `j ≤ n` eventually exist
  have hpass : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j ∈ Iic n, j < (fam.chain ε).N :=
    (eventually_all_finite (Set.finite_Iic n)).mpr fun j hj =>
      ((hReal.2.1 j (by rw [hgN]; exact Nat.lt_succ_of_le hj)).2).mono fun _ h => h.1
  refine ⟨fun j ε => (fam.chain ε).stop (j - 1), fun j ε => (fam.chain ε).start j,
    fun ε => (fam.chain ε).start_zero, ?_, ?_, ?_, ?_, ?_⟩
  · -- the order of the times
    filter_upwards [hpass, hrun] with ε hp hr
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · simp only [Nat.add_sub_cancel]
      exact (fam.chain ε).start_lt_stop j (hp j hj).le
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by have := hj.1; omega⟩
      simp only [Nat.add_sub_cancel]
      exact (hr i (hp i (by simp only [mem_Iic]; have := hj.2; omega))).2.1
  · -- (a)
    filter_upwards [hpass, hrun] with ε hp hr j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by have := hj.1; omega⟩
    simp only [Nat.add_sub_cancel]
    obtain ⟨-, -, hle, harr, hdep⟩ := hr i (hp i (by simp only [mem_Iic]; have := hj.2; omega))
    exact ⟨harr, hdep, by linarith⟩
  · -- (b), the passages `1 ≤ j ≤ n`
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by have := hj.1; omega⟩
    simp only [Nat.add_sub_cancel]
    have hin : i < g.N := by rw [hgN]; have := hj.2; omega
    refine ⟨?_, ?_⟩
    · have h := (hReal.2.1 i hin).1
      rwa [hgstop i (by have := hj.2; omega)] at h
    · exact (hReal.1 (i + 1) (by rw [hgN]; have := hj.2; omega)).start
  · -- (b), the last arrival
    simp only [Nat.add_sub_cancel]
    have h := (hReal.2.1 n (by rw [hgN]; omega)).1
    rwa [hgstop n (by omega)] at h
  · -- (c)
    intro I hI hIT hImp
    -- `I` avoids every impact of `g`, including `τ_{n+1} > T`
    have hImp' : ∀ j < g.N, g.stop j ∉ I := by
      intro j hj hmem
      rw [hgN] at hj
      rw [hgstop j hj] at hmem
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjn | hjn
      · exact hImp (j + 1) ⟨by omega, by omega⟩ hmem
      · subst hjn
        have := (hIT hmem).2
        linarith [hn.2]
    refine ⟨fun j hj => ?_, fun η hη => ?_⟩
    · -- the flight windows contain `I ∩ [τ_j, τ_{j+1})`
      obtain ⟨δ, hδ, hsep⟩ := exists_impact_separation g hI hImp'
      have hjg : j ≤ g.N := by rw [hgN]; omega
      filter_upwards [fam.window_close g hReal hStart hconv hjg hδ one_pos] with ε hw t ht
      simp only [Nat.add_sub_cancel]
      have hjs : g.start j ≤ t := by rw [hgstart]; exact ht.2.1
      have hjt : t < g.stop j := by rw [hgstop j (by omega)]; exact ht.2.2
      have hlo : 0 < j → g.start j + δ ≤ t := by
        intro hj0
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have hiN : i < g.N := by rw [hgN]; omega
        have hst : g.start (i + 1) = g.stop i := by
          rw [hgstart, hgstop i (by omega)]
        have h1 := hsep t ht.1 i hiN
        rw [hst] at hjs ⊢
        rw [abs_of_nonneg (by linarith)] at h1
        linarith
      have hhi : j < g.N → t ≤ g.stop j - δ := by
        intro hjN
        have h1 := hsep t ht.1 j hjN
        rw [abs_of_neg (by linarith)] at h1
        linarith
      exact (hw.2.2 t ⟨hjs, hjt.le⟩ hlo hhi).1
    · -- the uniform convergence, in the Euclidean distance
      filter_upwards [hcpt I hI hIT hImp' (η / 2) (by positivity)] with ε hε t ht
      obtain ⟨h1, h2⟩ := hε t ht
      rw [hgflow t (hIT ht)] at h1 h2
      exact ⟨(planeDist_le_two_mul_dist _ _).trans_lt (by linarith),
        (planeDist_le_two_mul_dist _ _).trans_lt (by linarith)⟩


/-- **The thin-network limit, Theorem IX.6 of the paper (`thm:thin-limit`), as printed, with the
graph state given as in the paper.**

The data are those of the paper: a thin network `N` satisfying (E) and (J) on a compact window
`K ⊂ (max_Γ V, ∞)` for a routing law `F`; initial states `z_ε` (`x₀`) prepared towards an end
`η₀ = x₀.germ` and not arriving there, with `pr_e(z_ε) → (q, p) = (x₀.q, x₀.r)` on the edge
`e = η₀.1`; the graph state `z = (e, q, p)` with `0 < q < ℓ_e` and `H_e(q, p) ∈ K`.  The flight
state at `z` is built here (`FlightState.ofInterior`), so the flow `Φ_t(z)` is
`FlightState.trajectory V (F.toBorelScattering V) a`.  No compatibility of `η₀` with the graph
flow is assumed: the theorem proves that `η₀` is the end of `e` with `σ(η₀) p > 0` (the first
conjunct), which is the end of Lemma IX.2, and that the first graph flight lands there
(`flight_above`).  For `n` with `τ_n ≤ T < τ_{n+1}`, the conclusion is (a), (b), (c) of
`thin_network_limit_of_flightState`, with `η_j = F.itinerary η₀ j` the itinerary of
`graph_itinerary`. -/
theorem thin_network_limit [Nonempty Γ.Edge]
    (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (F : RoutingLaw Γ)
    (K : Set ℝ) (hK : IsCompact K) (hwin : V.IsWindowAbove K)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hEdge : N.SatisfiesEdgeReduction V K ε₀)
    (hJunction : N.JunctionScatteringConvergesTo V K F ε₀)
    (x₀ : WellPreparedInitialState N V K ε₀)
    (hz : x₀.q ∈ Ioo (0 : ℝ) (Γ.length x₀.germ.1))
    (hEz : V.hamiltonian x₀.germ.1 x₀.q x₀.r ∈ K) {T : ℝ} {n : ℕ} :
    let a : V.FlightState := FlightState.ofInterior (V := V) (e := x₀.germ.1)
      (x := (x₀.q, x₀.r)) hz (hwin.not_mem_exceptionalEnergies _ hEz)
    FlightState.impactReal V (F.toBorelScattering V) a n ≤ T →
    T < FlightState.impactReal V (F.toBorelScattering V) a (n + 1) →
      0 < EdgeEnd.sign Γ x₀.germ * x₀.r ∧ ∃ α β : ℕ → ℝ → ℝ, (∀ ε, β 0 ε = 0) ∧
        -- the order of the times
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ j ≤ n, β j ε < α (j + 1) ε) ∧
          ∀ j ∈ Icc 1 n, α j ε < β j ε) ∧
        -- (a)
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j ∈ Icc 1 n,
          N.Arriving V K ε (F.itinerary x₀.germ (j - 1))
            (N.flow ε (α j ε) (x₀.x₀ ε, x₀.p₀ ε)).1 (N.flow ε (α j ε) (x₀.x₀ ε, x₀.p₀ ε)).2 ∧
          N.Departing V K ε (F.routeGerm (F.itinerary x₀.germ (j - 1)))
            (N.flow ε (β j ε) (x₀.x₀ ε, x₀.p₀ ε)).1 (N.flow ε (β j ε) (x₀.x₀ ε, x₀.p₀ ε)).2 ∧
          β j ε - α j ε ≤ N.dwell ε) ∧
        -- (b)
        (∀ j ∈ Icc 1 n,
          Tendsto (α j) (𝓝[>] 0) (𝓝 (FlightState.impactReal V (F.toBorelScattering V) a j)) ∧
          Tendsto (β j) (𝓝[>] 0) (𝓝 (FlightState.impactReal V (F.toBorelScattering V) a j))) ∧
        Tendsto (α (n + 1)) (𝓝[>] 0)
          (𝓝 (FlightState.impactReal V (F.toBorelScattering V) a (n + 1))) ∧
        -- (c)
        ∀ I : Set ℝ, IsCompact I → I ⊆ Icc (0 : ℝ) T →
          (∀ j ∈ Icc 1 n, FlightState.impactReal V (F.toBorelScattering V) a j ∉ I) →
          (∀ j ≤ n, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
            I ∩ Ico (FlightState.impactReal V (F.toBorelScattering V) a j)
                (FlightState.impactReal V (F.toBorelScattering V) a (j + 1)) ⊆
              Icc (β j ε) (α (j + 1) ε)) ∧
          ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ I,
            planeDist
              (N.gState (FlightState.trajectory V (F.toBorelScattering V) a t).1
                (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).1 (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).2)
              (FlightState.trajectory V (F.toBorelScattering V) a t).2 < η ∧
            planeDist (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).1
              (N.base (FlightState.trajectory V (F.toBorelScattering V) a t).1 +
                (FlightState.trajectory V (F.toBorelScattering V) a t).2.1 •
                  N.tang (FlightState.trajectory V (F.toBorelScattering V) a t).1) < η := by
  intro a hn₁ hn₂
  -- `η₀` is the end of `e` with `σ(η₀) p > 0`
  have hσ : 0 < EdgeEnd.sign Γ x₀.germ * x₀.r := by
    have hlim : Tendsto (fun ε => EdgeEnd.sign Γ x₀.germ * N.longP x₀.germ.1 (x₀.p₀ ε))
        (𝓝[>] 0) (𝓝 (EdgeEnd.sign Γ x₀.germ * x₀.r)) :=
      ((continuous_snd.tendsto _).comp x₀.converges).const_mul _
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        0 ≤ EdgeEnd.sign Γ x₀.germ * N.longP x₀.germ.1 (x₀.p₀ ε) :=
      eventually_nhdsGT_zero_of_forall_Ioo hε₀ fun ε hε => (x₀.prepared ε hε).towards.le
    have hle : 0 ≤ EdgeEnd.sign Γ x₀.germ * x₀.r := ge_of_tendsto hlim hev
    have hr : x₀.r ≠ 0 := by
      intro h0
      have h1 := (hwin _ hEz).2 x₀.germ.1 x₀.q (Ioo_subset_Icc_self hz)
      rw [MechanicalPotential.hamiltonian, h0] at h1
      norm_num at h1
    have hσ0 : EdgeEnd.sign Γ x₀.germ ≠ 0 := by
      intro h
      have := RoutingLaw.edgeEnd_abs_sign x₀.germ
      rw [h, abs_zero] at this
      exact zero_ne_one this
    exact lt_of_le_of_ne hle (Ne.symm (mul_ne_zero hσ0 hr))
  -- the first graph flight lands at `η₀`
  have hgerm : a.arrivalGerm = x₀.germ :=
    (FlightState.flight_above hK hwin a hEz (η := x₀.germ) rfl hσ).2.1
  exact ⟨hσ, thin_network_limit_of_flightState N V F K hK hwin hε₀ hEdge hJunction x₀ a rfl rfl
    hgerm hEz hz ⟨hn₁, hn₂⟩⟩

end HamiltonianMetricGraphs
