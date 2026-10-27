/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ThinGlobalFlow

/-!
# The thin-junction limit up to `t = 0`, and part (c) of Theorem IX.6 as printed

Part (c) of Theorem IX.6 of the paper (`thm:thin-limit`) asserts uniform convergence on every
compact `I ⊆ [0, T] \ {τ₁, …, τₙ}`, in particular on `[0, τ₁ - δ]`, a neighbourhood of `t = 0`.
The conclusion `ThinTrajectoryConvergesTo` of `thin_junction_global_flow_limit` gives uniform
convergence only on `[start j + δ, stop j - δ]` for every flight `j`, *including* `j = 0`, and so
says nothing near `t = 0`.  This file removes that difference.

## The mathematics

The left margin `δ` in `ThinRealizes` comes from the induction step (`step_core`, `final_core`):
the microscopic flight `j` starts at a time `start j` that only converges to the graph departure
time, so Grönwall is run on the common interval `[max (start j) (g.start j), …]`.  For the first
flight there is no such mismatch: both flights start at `t = 0` (`HybridChain.start_zero`), the
initial states converge (`ConvergesInitially.state_zero`), and the projected flight solves the
edge equations up to `odeErr ε = γ_ε → 0`.  Grönwall from `t = 0` (`IsFlight.dist_le_closeness`)
thus gives closeness on `[0, min (stop 0) (g.stop 0)]` (`eventually_initial_close`), and the
convergence of the first arrival time (or, without impacts, the last-flight clause) shows that
this interval eventually contains `[0, g.stop 0 - δ]`, resp. `[0, g.stop 0]` (`initial_window`).
This holds for *every* family with converging initial data, in particular for the family built in
the proof of `thin_junction_hamiltonian_limit` (`thin_family_exists`).

## Main statements

* `ThinRealizesFromStart fam g` — uniform convergence of flight `0` on `[0, stop 0 - δ]`, and on
  `[0, stop 0]` if `g.N = 0`.
* `ThinTrajectoryConvergesFromStart N x₀ g T` — the data of `ThinTrajectoryConvergesTo` for one
  family `fam`, plus `ThinRealizesFromStart fam g`, with the certificate `IsThinProjectionFrom`
  (the chain is the projection of the flow `Φ^ε_t(x₀ ε, p₀ ε)`).
* `ThinConvergesOnCompacts N x₀ g T` — part (c) in the form printed in the paper: for every compact
  `I ⊆ [0, T]` avoiding the impact times, with `z_ε(t) = Φ^ε_t(z_ε) = (x_ε(t), ξ_ε(t))`,
  `sup_I |pr_{e(t)} z_ε(t) - (q(t), p(t))| → 0` and `sup_I |x_ε(t) - b_{e(t)} - q(t) τ_{e(t)}| → 0`.
* `thin_junction_hamiltonian_limit_from_start`, `thin_junction_global_flow_limit_from_start`,
  `thin_junction_global_flow_limit_of_interior_from_start` — the three limit theorems, with the
  hypotheses unchanged and the strengthened conclusions.

Auxiliary result: the geometric estimate `|x - b_e - q τ_e| ≤ |q_e(x) - q| + |y_e(x)|`
(`ThinHamiltonianNetwork.dist_centreline_le`).
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology NNReal


variable {Γ : FiniteMetricGraph} {V : MechanicalPotential Γ} {F : RoutingLaw Γ}

/-- **Uniform convergence on the initial window.**  The projected microscopic flight `0`
converges to the graph flight `0` uniformly on `[0, stop 0 - δ]` for every `δ > 0`, i.e. on every
compact subset of `[0, τ₁)`, `τ₁ = stop 0` being the first impact; and, if the window contains no
impact at all (`g.N = 0`), uniformly on the whole window `[0, stop 0]`. -/
def ThinRealizesFromStart (fam : ThinNetworkFamily V F) (g : GraphTrajectory V F) : Prop :=
  (∀ δ > (0 : ℝ), ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    ∀ t ∈ Icc (0 : ℝ) (g.stop 0 - δ), dist ((fam.chain ε).curve 0 t) (g.curve 0 t) < η) ∧
  (g.N = 0 → ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    ∀ t ∈ Icc (0 : ℝ) (g.stop 0), dist ((fam.chain ε).curve 0 t) (g.curve 0 t) < η)

namespace MechanicalPotential

namespace ThinNetworkFamily

variable (fam : ThinNetworkFamily V F) (g : GraphTrajectory V F)

/-- **Grönwall from `t = 0`.** -/
theorem eventually_initial_close {P R c₀ : ℝ} {KL : ℝ≥0} (hc : GraphConstants g P R c₀ KL)
    (hfam : fam.ConvergesInitially g) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) (min ((fam.chain ε).stop 0) (g.stop 0)),
      dist ((fam.chain ε).curve 0 t) (g.curve 0 t) ≤
        (θ + θ * g.stop 0) * Real.exp (KL * g.stop 0) := by
  have hst : ∀ᶠ ε in 𝓝[>] (0 : ℝ), dist ((fam.chain ε).curve 0 0) (g.curve 0 0) < θ :=
    (Metric.tendsto_nhds.mp hfam.state_zero) θ hθ
  filter_upwards [hfam.edge_zero, hst, fam.eventually_params_le hθ] with ε hedge hdist hpar
  obtain ⟨-, -, hode, -⟩ := hpar
  obtain ⟨wc, hcf⟩ := (fam.chain ε).isFlight (Nat.zero_le (fam.chain ε).N)
  obtain ⟨wg, hgf⟩ := g.isFlight_zero (Nat.zero_le g.N)
  rw [hedge, (fam.chain ε).start_zero] at hcf
  rw [g.start_zero] at hgf
  have hc0 : 0 < (fam.chain ε).stop 0 := by
    have := (fam.chain ε).start_lt_stop 0 (Nat.zero_le _)
    rwa [(fam.chain ε).start_zero] at this
  have hg0 : 0 < g.stop 0 := by
    have := g.start_lt_stop 0 (Nat.zero_le _)
    rwa [g.start_zero] at this
  have hm' : (0 : ℝ) ≤ min ((fam.chain ε).stop 0) (g.stop 0) := le_min hc0.le hg0.le
  have h := (hcf.mono le_rfl (min_le_left _ _)).dist_le_closeness (hc.lipschitz _)
    (hgf.mono le_rfl (min_le_right _ _)) (fam.params ε).offset_nonneg le_rfl
    (fam.params ε).odeErr_nonneg le_rfl hm' hθ.le hdist.le
  intro t ht
  refine (h t ht).trans ?_
  have hmg : min ((fam.chain ε).stop 0) (g.stop 0) ≤ g.stop 0 := min_le_right _ _
  apply mul_le_mul
  · have : ((fam.params ε).odeErr + 0) * (min ((fam.chain ε).stop 0) (g.stop 0) - 0) ≤
        θ * g.stop 0 := by
      apply mul_le_mul (by linarith) (by linarith) (by linarith) hθ.le
    linarith
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) KL.coe_nonneg)
  · exact (Real.exp_pos _).le
  · have : 0 ≤ θ * g.stop 0 := mul_nonneg hθ.le hg0.le
    linarith

/-- **Uniform convergence on the first flight, from `t = 0`.**  For every family whose initial
data converge to those of `g`, the projected microscopic flight `0` converges to the graph flight
`0` uniformly on `[0, stop 0 - δ]` for every `δ > 0`; if the window contains no impact
(`g.N = 0`), uniformly on the whole window `[0, stop 0]`. -/
theorem initial_window [Nonempty Γ.Edge] (K : Set ℝ) (hK : IsCompact K)
    (hreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) (hE : g.energy ∈ K)
    (hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0)))
    (hfam : fam.ConvergesInitially g) : ThinRealizesFromStart fam g := by
  obtain ⟨P, R, c₀, KL, hc⟩ := exists_graphConstants K hK hreg g hE
  obtain ⟨-, himp, -, hlast⟩ := microscopic_realization K hK hreg g hE hinit fam hfam
  have hg0 : 0 < g.stop 0 := by
    have := g.start_lt_stop 0 (Nat.zero_le _)
    rwa [g.start_zero] at this
  set C : ℝ := (1 + g.stop 0) * Real.exp (KL * g.stop 0) with hCdef
  have hC : 0 < C := mul_pos (by linarith) (Real.exp_pos _)
  -- the Grönwall estimate on the common interval `[0, min (stop 0) (g.stop 0)]`
  have key : ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) (min ((fam.chain ε).stop 0) (g.stop 0)),
        dist ((fam.chain ε).curve 0 t) (g.curve 0 t) < η := by
    intro η hη
    have hθ : 0 < η / (2 * C) := by positivity
    filter_upwards [fam.eventually_initial_close g hc hfam hθ] with ε hε t ht
    refine lt_of_le_of_lt (hε t ht) ?_
    have : (η / (2 * C) + η / (2 * C) * g.stop 0) * Real.exp (KL * g.stop 0) = η / 2 := by
      rw [hCdef]
      field_simp
    rw [this]
    linarith
  -- without impacts, the microscopic flight `0` covers the whole window
  have cover0 : g.N = 0 → ∀ᶠ ε in 𝓝[>] (0 : ℝ), g.stop 0 ≤ (fam.chain ε).stop 0 := by
    intro hN
    filter_upwards [hlast.1, hfam.finalTime] with ε h1 h2
    rw [hN] at h1 h2
    rcases Nat.eq_zero_or_pos (fam.chain ε).N with hc0 | hcpos
    · rwa [hc0] at h2
    · exact (h1 hcpos).le
  -- the microscopic flight `0` lasts at least until `stop 0 - δ`
  have cover : ∀ δ > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), g.stop 0 - δ ≤ (fam.chain ε).stop 0 := by
    intro δ hδ
    rcases Nat.eq_zero_or_pos g.N with hN | hN
    · filter_upwards [cover0 hN] with ε hε
      linarith
    · filter_upwards [(Metric.tendsto_nhds.mp (himp 0 hN).1) δ hδ] with ε hε
      rw [Real.dist_eq] at hε
      linarith [(abs_lt.mp hε).1]
  refine ⟨fun δ hδ η hη => ?_, fun hN η hη => ?_⟩
  · filter_upwards [key η hη, cover δ hδ] with ε hε hcov t ht
    exact hε t ⟨ht.1, le_min (ht.2.trans hcov) (by linarith [ht.2])⟩
  · filter_upwards [key η hη, cover0 hN] with ε hε hcov t ht
    exact hε t ⟨ht.1, le_min (ht.2.trans hcov) ht.2⟩

/-- **Uniform convergence on one flight window, with the microscopic flight covering it.**  For
the flight `j ≤ N` of `g` and a margin `δ > 0`, eventually the microscopic flight `j` runs on the
graph edge, contains every time `t` of the graph flight `j` that keeps the distance `δ` from the
impacts bounding it, and is `η`-close to the graph flight at all such times.  The left margin is
not needed for `j = 0` (the start `t = 0` is not an impact) and the right margin is not needed for
the last flight `j = N` (its end is the end of the window, not an impact). -/
theorem window_close (hR : ThinRealizes fam g) (hS : ThinRealizesFromStart fam g)
    (hfam : fam.ConvergesInitially g) {j : ℕ} (hj : j ≤ g.N) {δ : ℝ} (hδ : 0 < δ)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), j ≤ (fam.chain ε).N ∧ (fam.chain ε).edge j = g.edge j ∧
      ∀ t ∈ Icc (g.start j) (g.stop j), (0 < j → g.start j + δ ≤ t) →
        (j < g.N → t ≤ g.stop j - δ) →
          t ∈ Icc ((fam.chain ε).start j) ((fam.chain ε).stop j) ∧
            dist ((fam.chain ε).curve j t) (g.curve j t) < η := by
  obtain ⟨hall, himp, hfl, hlast⟩ := hR
  have hM := hall j hj
  -- the microscopic flight `j` starts before the window
  have hstart : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (fam.chain ε).start j ≤ g.start j + δ := by
    filter_upwards [(Metric.tendsto_nhds.mp hM.start) δ hδ] with ε hε
    rw [Real.dist_eq] at hε
    linarith [(abs_lt.mp hε).2]
  -- the microscopic flight `j` ends after the window
  have hstop : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (j < g.N → g.stop j - δ ≤ (fam.chain ε).stop j) ∧
      (j = g.N → g.stop j ≤ (fam.chain ε).stop j) := by
    rcases lt_or_eq_of_le hj with hjN | hjN
    · filter_upwards [(Metric.tendsto_nhds.mp (himp j hjN).1) δ hδ] with ε hε
      rw [Real.dist_eq] at hε
      exact ⟨fun _ => by linarith [(abs_lt.mp hε).1], fun h => absurd h (Nat.ne_of_lt hjN)⟩
    · subst hjN
      filter_upwards [hlast.1, hfam.finalTime, hM.eventually] with ε h1 h2 h3
      refine ⟨fun h => absurd h (lt_irrefl _), fun _ => ?_⟩
      rcases lt_or_eq_of_le h3.1 with hlt | heq
      · exact (h1 hlt).le
      · rwa [← heq] at h2
  -- closeness on the window
  have hclose : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (g.start j) (g.stop j),
      (0 < j → g.start j + δ ≤ t) → (j < g.N → t ≤ g.stop j - δ) →
        dist ((fam.chain ε).curve j t) (g.curve j t) < η := by
    rcases lt_or_eq_of_le hj with hjN | hjN
    · rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        filter_upwards [hS.1 δ hδ η hη] with ε hε t ht _ hhi
        rw [g.start_zero] at ht
        exact hε t ⟨ht.1, hhi hjN⟩
      · filter_upwards [hfl j hjN δ hδ η hη] with ε hε t _ hlo hhi
        exact hε t ⟨hlo hj0, hhi hjN⟩
    · rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        filter_upwards [hS.2 hjN.symm η hη] with ε hε t ht _ _
        rw [g.start_zero] at ht
        exact hε t ht
      · subst hjN
        filter_upwards [hlast.2 δ hδ η hη] with ε hε t ht hlo _
        exact hε t ⟨hlo hj0, ht.2⟩
  filter_upwards [hM.eventually, hstart, hstop, hclose] with ε hM' hst hsp hcl
  refine ⟨hM'.1, hM'.2, fun t ht hlo hhi => ⟨⟨?_, ?_⟩, hcl t ht hlo hhi⟩⟩
  · rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [(fam.chain ε).start_zero]
      rw [g.start_zero] at ht
      exact ht.1
    · linarith [hlo hj0]
  · rcases lt_or_eq_of_le hj with hjN | hjN
    · linarith [hhi hjN, hsp.1 hjN]
    · linarith [ht.2, hsp.2 hjN]

end ThinNetworkFamily

end MechanicalPotential


/-! ### The configuration and the tube coordinates -/

namespace ThinHamiltonianNetwork

variable {N : ThinHamiltonianNetwork Γ}

/-- **The configuration is controlled by the tube coordinates.**  The distance of a point `x` of
the plane from the point `b_e + q τ_e` of the centreline of the tube of `e` is at most the
longitudinal error `|q_e(x) - q|` plus the transverse displacement `|y_e(x)|`. -/
theorem dist_centreline_le (e : Γ.Edge) (x : ℝ × ℝ) (q : ℝ) :
    dist x (N.base e + q • N.tang e) ≤ |N.long e x - q| + |N.trans e x| := by
  have hτ := N.tang_sq e
  have hν := N.nrm_sq e
  have hτν := N.tang_nrm e
  set τ₁ := (N.tang e).1
  set τ₂ := (N.tang e).2
  set ν₁ := (N.nrm e).1
  set ν₂ := (N.nrm e).2
  set d := τ₁ * ν₂ - τ₂ * ν₁ with hd
  -- the columns of the orthogonal matrix with rows `τ`, `ν` are orthonormal as well
  have hν₂ : ν₂ = d * τ₁ := by linear_combination (-ν₂) * hτ + τ₂ * hτν
  have hν₁ : ν₁ = -(d * τ₂) := by linear_combination (-ν₁) * hτ + τ₁ * hτν
  have hd2 : d ^ 2 = 1 := by
    linear_combination ν₁ ^ 2 * hτ + ν₂ ^ 2 * hτ + hν - (τ₁ * ν₁ + τ₂ * ν₂) * hτν
  have hc₁ : τ₁ ^ 2 + ν₁ ^ 2 = 1 := by linear_combination hτ + τ₂ ^ 2 * hd2 + (ν₁ - d * τ₂) * hν₁
  have hc₁₂ : τ₁ * τ₂ + ν₁ * ν₂ = 0 := by
    linear_combination ν₂ * hν₁ + (-(d * τ₂)) * hν₂ - τ₁ * τ₂ * hd2
  have hc₂ : τ₂ ^ 2 + ν₂ ^ 2 = 1 := by linear_combination hτ + τ₁ ^ 2 * hd2 + (ν₂ + d * τ₁) * hν₂
  have habs : ∀ a : ℝ, a ^ 2 ≤ 1 → |a| ≤ 1 := fun a ha => (sq_le_one_iff_abs_le_one a).mp ha
  have hτ₁ : |τ₁| ≤ 1 := habs _ (by nlinarith)
  have hτ₂ : |τ₂| ≤ 1 := habs _ (by nlinarith)
  have hν₁' : |ν₁| ≤ 1 := habs _ (by nlinarith)
  have hν₂' : |ν₂| ≤ 1 := habs _ (by nlinarith)
  set L := N.long e x with hL
  set Y := N.trans e x with hY
  have hLdef : L = (x.1 - (N.base e).1) * τ₁ + (x.2 - (N.base e).2) * τ₂ := rfl
  have hYdef : Y = (x.1 - (N.base e).1) * ν₁ + (x.2 - (N.base e).2) * ν₂ := rfl
  have e₁ : x.1 - (N.base e + q • N.tang e).1 = (L - q) * τ₁ + Y * ν₁ := by
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    rw [hLdef, hYdef]
    linear_combination (-(x.1 - (N.base e).1)) * hc₁ - (x.2 - (N.base e).2) * hc₁₂
  have e₂ : x.2 - (N.base e + q • N.tang e).2 = (L - q) * τ₂ + Y * ν₂ := by
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [hLdef, hYdef]
    linear_combination (-(x.1 - (N.base e).1)) * hc₁₂ - (x.2 - (N.base e).2) * hc₂
  have hb : ∀ a b : ℝ, |a| ≤ 1 → |b| ≤ 1 → |(L - q) * a + Y * b| ≤ |L - q| + |Y| := by
    intro a b ha hb
    calc |(L - q) * a + Y * b| ≤ |(L - q) * a| + |Y * b| := abs_add_le _ _
      _ = |L - q| * |a| + |Y| * |b| := by rw [abs_mul, abs_mul]
      _ ≤ |L - q| * 1 + |Y| * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
      _ = |L - q| + |Y| := by ring
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, e₁, e₂]
  exact max_le (hb _ _ hτ₁ hν₁') (hb _ _ hτ₂ hν₂')

end ThinHamiltonianNetwork



/-! ### The strengthened convergence statements -/

section Limit

variable {N : ThinHamiltonianNetwork Γ} {K : Set ℝ} {ε₀ : ℝ}

/-- **The projected microscopic trajectories converge to `g` on `[0, T]`, including near
`t = 0`.**  This is `ThinTrajectoryConvergesTo` with two additions, both for the *same* family
`fam`: the certifying microscopic trajectories start at the given initial data (`x₀ ε, p₀ ε`), and
the first flight converges uniformly up to `t = 0` (`ThinRealizesFromStart`). -/
def ThinTrajectoryConvergesFromStart (N : ThinHamiltonianNetwork Γ)
    (x₀ : WellPreparedInitialState N V K ε₀) (g : GraphTrajectory V F) (T : ℝ) : Prop :=
  ∃ fam : ThinNetworkFamily V F,
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsThinProjectionFrom N x₀ ε (fam.chain ε)) ∧
    fam.ConvergesInitially g ∧ T ≤ g.stop g.N ∧ ThinRealizes fam g ∧ ThinRealizesFromStart fam g

theorem ThinTrajectoryConvergesFromStart.thinTrajectoryConvergesTo
    {x₀ : WellPreparedInitialState N V K ε₀} {g : GraphTrajectory V F} {T : ℝ}
    (h : ThinTrajectoryConvergesFromStart N x₀ g T) : ThinTrajectoryConvergesTo N x₀ g T := by
  obtain ⟨fam, hcert, hconv, hT, hreal, -⟩ := h
  exact ⟨fam, hcert.mono fun _ h => h.isThinProjection, hconv, hT, hreal⟩

/-- **Part (c) of the thin-network limit theorem, in the form printed in the paper.**  For every
compact `I ⊆ [0, T]` containing none of the impact times `τ_j = stop j` (`j < N`) of `g`, and
every `η > 0`, for all sufficiently small `ε`, the flow `z_ε(t) = Φ^ε_t(z_ε) = (x_ε(t), ξ_ε(t))`
through the microscopic initial state `z_ε = (x₀ ε, p₀ ε)` satisfies, at every `t ∈ I`,

* `|pr_{e(t)} z_ε(t) - (q(t), p(t))| < η` — the projected state onto the edge `e(t)` carrying the
  graph trajectory at time `t` is `η`-close to the graph state `(q(t), p(t))`, and
* `|x_ε(t) - b_{e(t)} - q(t) τ_{e(t)}| < η` — the particle is `η`-close to the point of the
  centreline of the tube of `e(t)` at the graph coordinate `q(t)`.

Here `(e(t), q(t), p(t)) = g.state t`, and distances in `ℝ²` are the sup-distances of `ℝ × ℝ`.
(Every trajectory of `H_ε` through `z_ε` is this flow, `MicroTrajectory.eq_flow`.) -/
def ThinConvergesOnCompacts (N : ThinHamiltonianNetwork Γ)
    (x₀ : WellPreparedInitialState N V K ε₀) (g : GraphTrajectory V F) (T : ℝ) : Prop :=
  ∀ I : Set ℝ, IsCompact I → I ⊆ Icc (0 : ℝ) T → (∀ j < g.N, g.stop j ∉ I) →
    ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ I,
      dist (N.gState (g.state t).1 (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).1
        (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).2) (g.state t).2 < η ∧
      dist (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).1
        (N.base (g.state t).1 + (g.state t).2.1 • N.tang (g.state t).1) < η

/-- A compact set avoiding the finitely many impact times keeps a positive distance from them. -/
theorem exists_impact_separation (g : GraphTrajectory V F) {I : Set ℝ} (hI : IsCompact I)
    (hImp : ∀ j < g.N, g.stop j ∉ I) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ I, ∀ j < g.N, δ ≤ |t - g.stop j| := by
  set A : Set ℝ := g.stop '' Iio g.N with hA
  have hAc : IsClosed A := ((Set.finite_Iio g.N).image _).isClosed
  have hdisj : Disjoint I A := by
    rw [Set.disjoint_left]
    rintro t ht ⟨j, hj, rfl⟩
    exact hImp j hj ht
  obtain ⟨δ, hδ, hsep⟩ := hdisj.exists_thickenings hI hAc
  refine ⟨δ, hδ, fun t ht j hj => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have h1 : g.stop j ∈ Metric.thickening δ I :=
    Metric.mem_thickening_iff.mpr ⟨t, ht, by rwa [Real.dist_eq, abs_sub_comm]⟩
  have h2 : g.stop j ∈ Metric.thickening δ A :=
    Metric.self_subset_thickening hδ A ⟨j, hj, rfl⟩
  exact Set.disjoint_left.mp hsep h1 h2

/-- **The convergence on compacts follows from the strengthened convergence.**  On a compact set
avoiding the impacts the flight index of `g` is locally constant, so the uniform estimates on the
finitely many flight windows (`window_close`), the projection certificate, the transverse bound
`|y_e(x)| ≤ tubeWidth ε → 0` and `dist_centreline_le` give both estimates of part (c). -/
theorem ThinTrajectoryConvergesFromStart.thinConvergesOnCompacts
    {x₀ : WellPreparedInitialState N V K ε₀} {g : GraphTrajectory V F} {T : ℝ}
    (h : ThinTrajectoryConvergesFromStart N x₀ g T) : ThinConvergesOnCompacts N x₀ g T := by
  obtain ⟨fam, hcert, hfam, hT, hR, hS⟩ := h
  intro I hI hIT hImp η hη
  obtain ⟨δ, hδ, hsep⟩ := exists_impact_separation g hI hImp
  have hw : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j ∈ Iic g.N,
      j ≤ (fam.chain ε).N ∧ (fam.chain ε).edge j = g.edge j ∧
      ∀ t ∈ Icc (g.start j) (g.stop j), (0 < j → g.start j + δ ≤ t) →
        (j < g.N → t ≤ g.stop j - δ) →
          t ∈ Icc ((fam.chain ε).start j) ((fam.chain ε).stop j) ∧
            dist ((fam.chain ε).curve j t) (g.curve j t) < η / 2 :=
    (eventually_all_finite (Set.finite_Iic g.N)).mpr fun j hj =>
      fam.window_close g hR hS hfam hj hδ (by positivity)
  have htube : ∀ᶠ ε in 𝓝[>] (0 : ℝ), N.tubeWidth ε < η / 2 :=
    eventually_lt_of_tendsto_nhds_zero N.tubeWidth_tendsto (by positivity)
  filter_upwards [hw, hcert, htube] with ε hw hproj htube t ht
  set j := g.flightIndex t with hjdef
  have hjN : j ≤ g.N := g.flightIndex_le t
  have ht0 : 0 ≤ t := (hIT ht).1
  have hjs : g.start j ≤ t := g.start_flightIndex_le ht0
  have hjt : t ≤ g.stop j := by
    rcases lt_or_eq_of_le hjN with hlt | heq
    · have := g.lt_start_succ_flightIndex hlt
      rw [g.start_succ_eq_stop hlt] at this
      exact this.le
    · rw [heq]
      exact (hIT ht).2.trans hT
  have hlo : 0 < j → g.start j + δ ≤ t := by
    intro hj0
    obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hiN : i < g.N := by omega
    have hst : g.start j = g.stop i := by rw [hi]; exact g.start_succ_eq_stop hiN
    have h1 := hsep t ht i hiN
    rw [hst] at hjs ⊢
    rw [abs_of_nonneg (by linarith)] at h1
    linarith
  have hhi : j < g.N → t ≤ g.stop j - δ := by
    intro hjN'
    have h1 := hsep t ht j hjN'
    have h2 : t < g.stop j := by
      have := g.lt_start_succ_flightIndex hjN'
      rwa [g.start_succ_eq_stop hjN'] at this
    rw [abs_of_neg (by linarith)] at h1
    linarith
  obtain ⟨hjc, hedge, hwin⟩ := hw j hjN
  obtain ⟨htc, hdist⟩ := hwin t ⟨hjs, hjt⟩ hlo hhi
  obtain ⟨hcurve, htrans⟩ := hproj j hjc t htc
  have hstate : g.state t = (g.edge j, g.curve j t) := g.state_eq_of_flightIndex_eq hjdef.symm
  rw [hstate]
  rw [hedge] at hcurve htrans
  rw [← hcurve]
  refine ⟨by linarith, ?_⟩
  refine lt_of_le_of_lt (ThinHamiltonianNetwork.dist_centreline_le _ _ _) ?_
  have hq : |N.long (g.edge j) (N.flow ε t (x₀.x₀ ε, x₀.p₀ ε)).1 - (g.curve j t).1| ≤
      dist ((fam.chain ε).curve j t) (g.curve j t) := by
    rw [hcurve, Prod.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  linarith

/-! ### The theorems -/

/-- **The thin-junction Hamiltonian limit theorem, up to `t = 0`.**  Under the hypotheses of
`thin_junction_hamiltonian_limit`, the projected microscopic Hamiltonian trajectories through the
given initial data converge to `g` in the strengthened sense `ThinTrajectoryConvergesFromStart`:
in addition to the conclusions of `thin_junction_hamiltonian_limit`, the first flight converges
uniformly on `[0, stop 0 - δ]` (on `[0, stop 0]` if there is no impact), and the certifying
microscopic trajectories start at the given initial data.

The family is the one built for `thin_junction_hamiltonian_limit` (`thin_family_exists`); the
initial window is Grönwall's inequality from `t = 0` for that family
(`ThinNetworkFamily.initial_window`). -/
theorem thin_junction_hamiltonian_limit_from_start
    (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (F : RoutingLaw Γ)
    (K : Set ℝ) (hK : IsCompact K) (hwin : V.IsWindowAbove K)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hEdge : N.SatisfiesEdgeReduction V K ε₀)
    (hJunction : N.JunctionScatteringConvergesTo V K F ε₀)
    (x₀ : WellPreparedInitialState N V K ε₀)
    (g : GraphTrajectory V F) (hg : IsThinGraphLimit x₀ g) (hE : g.energy ∈ K)
    (hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0)))
    {T : ℝ} (hT : T ≤ g.stop g.N) :
    ThinTrajectoryConvergesFromStart N x₀ g T := by
  haveI : Nonempty Γ.Edge := ⟨x₀.germ.1⟩
  have hreg := hwin.not_mem_exceptionalEnergies
  obtain ⟨fam, hcert, hconv⟩ := thin_family_exists N V F K hK hwin hε₀ hEdge hJunction x₀ g hg
  exact ⟨fam, hcert, hconv, hT, microscopic_realization K hK hreg g hE hinit fam hconv,
    fam.initial_window g K hK hreg hE hinit hconv⟩

/-- **The thin-junction limit is convergence to the paper's global graph flow, up to `t = 0`.**
The hypotheses are exactly those of `thin_junction_global_flow_limit`; the conclusion strengthens
`ThinTrajectoryConvergesTo` to `ThinTrajectoryConvergesFromStart` (uniform convergence of the
first flight on `[0, τ₁ - δ]`, certificate anchored at the initial data), and adds part (c) of
Theorem IX.6 in the form printed in the paper (`ThinConvergesOnCompacts`): uniform convergence of
the projected state and of the configuration on every compact `I ⊆ [0, T]` avoiding the impact
times. -/
theorem thin_junction_global_flow_limit_from_start [Nonempty Γ.Edge]
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
      IsThinGraphLimit x₀ g ∧ ThinTrajectoryConvergesFromStart N x₀ g T ∧
      ThinConvergesOnCompacts N x₀ g T := by
  obtain ⟨g, hg_edge, hg_germ, hg_curve, hg_T, hg_flow⟩ :=
    FlightState.exists_graphTrajectory_of_flow F a hT
  have hlimit : IsThinGraphLimit x₀ g :=
    ⟨by rw [hg_germ, hgerm], by rw [hg_edge, hedge], by rw [hg_curve, hstate]⟩
  have hconv : ThinTrajectoryConvergesFromStart N x₀ g T := by
    refine thin_junction_hamiltonian_limit_from_start N V F K hK hwin hε₀ hEdge hJunction x₀ g
      hlimit ?_ ?_ hg_T
    · change V.hamiltonian (g.edge 0) (g.curve 0 0).1 (g.curve 0 0).2 ∈ K
      rw [hg_edge, hg_curve]
      exact hE
    · rw [hg_curve, hg_edge]
      exact hinit
  exact ⟨g, hg_flow, hlimit, hconv, hconv.thinConvergesOnCompacts⟩

/-- **The interior form, up to `t = 0`.**  The hypotheses are exactly those of
`thin_junction_global_flow_limit_of_interior`; the conclusion is strengthened as in
`thin_junction_global_flow_limit_from_start`. -/
theorem thin_junction_global_flow_limit_of_interior_from_start [Nonempty Γ.Edge]
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
      IsThinGraphLimit x₀ g ∧ ThinTrajectoryConvergesFromStart N x₀ g T ∧
      ThinConvergesOnCompacts N x₀ g T ∧
      ∃ a : V.FlightState, a.edge = x₀.germ.1 ∧ a.state = (x₀.q, x₀.r) ∧
        ∀ t ∈ Icc (0 : ℝ) (g.stop g.N),
          g.state t = FlightState.trajectory V (F.toBorelScattering V) a t := by
  have hzz : ((x₀.q, x₀.r) : ℝ × ℝ).1 ∈ Ioo (0 : ℝ) (Γ.length x₀.germ.1) := hz
  have hr : V.hamiltonian x₀.germ.1 ((x₀.q, x₀.r) : ℝ × ℝ).1 ((x₀.q, x₀.r) : ℝ × ℝ).2 ∉
      V.exceptionalEnergies := hwin.not_mem_exceptionalEnergies _ hEz
  set a : V.FlightState := FlightState.ofInterior (V := V) hzz hr with ha
  obtain ⟨g, hflow, hlimit, hconv, hcpt⟩ :=
    thin_junction_global_flow_limit_from_start N V F K hK hwin hε₀ hEdge hJunction x₀ a rfl rfl
      (hgerm hzz hr) hEz hzz hT
  exact ⟨g, hlimit, hconv, hcpt, a, rfl, rfl, hflow⟩

end Limit

end HamiltonianMetricGraphs
