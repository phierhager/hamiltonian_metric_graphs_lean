/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.CapDynamics
import HamiltonianMetricGraphs.Realization.BranchingModel

/-!
# The projected chain of a microscopic trajectory

This file carries out the recursion that turns a genuine trajectory of the two-dimensional
microscopic Hamiltonian `H_ε = ½|p|² + microPot ε` into a `HybridChain` on the star graph `Γ⋆`
with the parameters `starParams ε`.

## Geometry

The through channel of the network is the `u`-axis: edge `0` is `u ∈ [-1, 0]` with graph
coordinate `q = -u`, edge `1` is `u ∈ [0, 1]` with graph coordinate `q = u`, and the branching
vertex `v⋆` sits at `u = 0`.  The routers occupy `|u| ≤ 8ε` (around `v⋆`) and `|u| ≥ 1 - 8ε`
(around the two outer vertices), so `offset = 8ε`.

A particle launched on edge `0` towards `v⋆` therefore performs, forever,

  free flight → *pass through* `v⋆` → free flight → *reflect* at a cap → …

The pass through `v⋆` is what makes the model genuinely branching: the particle arriving along
`η₁` leaves along `η₂`, exactly as `F⋆(η₁) = η₂` prescribes, and never along `η₃` — that channel
is closed by the junction barrier (`arm_barrier_margin`).

## The recursion

`beta k` is the time at which the `k`-th *long* free flight begins (at `u = ∓(1-8ε)`), `alpha k`
the time it ends (at `u = ±(1-8ε)`) and `sigma k` the time it crosses the router boundary next to
`v⋆`.  Each long free flight carries **two** chain flights, `2k` (before `v⋆`) and `2k+1` (after),
and is followed by one cap reflection, which produces `beta (k+1)`.

Everything about a long free flight is explicit (`CapSolution.free`); the only non-explicit datum
is the exit time of a cap passage, which is obtained from `CapSolution.reflect` and named by
`exitAfter`.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

/-! ### The itinerary of the through channel -/

/-- The routing law preserves the endpoint selector: it permutes the edges at a vertex. -/
theorem starGermMap_snd (η : starGraph.EdgeEnd) : (starGermMap η).2 = η.2 := by
  rcases hb : η.2 with _ | _
  · simp [starGermMap_of_false hb]
  · simp [starGermMap_of_true hb, hb]

/-- Along an itinerary the endpoint selector alternates: an arrival at `v⋆` is followed by an
arrival at an outer vertex and conversely. -/
theorem itinerary_snd_succ (η₀ : starGraph.EdgeEnd) (j : ℕ) :
    (starRouting.itinerary η₀ (j + 1)).2 = !(starRouting.itinerary η₀ j).2 := by
  rw [RoutingLaw.itinerary_succ, otherEnd_snd, starRouting_routeGerm, starGermMap_snd]

/-- Even impacts of the through orbit are at the branching vertex, odd impacts at an outer
vertex. -/
theorem itinerary_snd_channel₁ (k : ℕ) :
    (starRouting.itinerary channel₁ (2 * k)).2 = false ∧
      (starRouting.itinerary channel₁ (2 * k + 1)).2 = true := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
      refine ⟨?_, ?_⟩
      · rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, itinerary_snd_succ, ih.2]
        rfl
      · rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, itinerary_snd_succ,
          itinerary_snd_succ, ih.2]
        rfl

theorem itinerary_snd_even (k : ℕ) : (starRouting.itinerary channel₁ (2 * k)).2 = false :=
  (itinerary_snd_channel₁ k).1

theorem itinerary_snd_odd (k : ℕ) : (starRouting.itinerary channel₁ (2 * k + 1)).2 = true :=
  (itinerary_snd_channel₁ k).2

/-- **The orbit of the through channel.**  Starting from `η₁` the edge sequence is
`0, 1, 1, 0, 0, 1, 1, …`: the particle passes straight through `v⋆` from edge `0` to edge `1`,
is reflected at the outer vertex, passes back through `v⋆`, and so on.  The sign `(-1)^k` records
which half of the axis carries the `k`-th long free flight. -/
theorem itinerary_through (k : ℕ) :
    ((starRouting.itinerary channel₁ (2 * k)).1 = 0 ∧
        (starRouting.itinerary channel₁ (2 * k + 1)).1 = 1 ∧ (-1 : ℝ) ^ k = 1) ∨
      ((starRouting.itinerary channel₁ (2 * k)).1 = 1 ∧
        (starRouting.itinerary channel₁ (2 * k + 1)).1 = 0 ∧ (-1 : ℝ) ^ k = -1) := by
  induction k with
  | zero => exact Or.inl ⟨rfl, rfl, by norm_num⟩
  | succ m ih =>
      have e1 : (starRouting.itinerary channel₁ (2 * (m + 1))).1 =
          (starRouting.itinerary channel₁ (2 * m + 1)).1 := by
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, RoutingLaw.itinerary_succ, otherEnd_fst,
          starRouting_routeGerm, starGermMap_of_true (itinerary_snd_odd m)]
      have e2 : (starRouting.itinerary channel₁ (2 * (m + 1) + 1)).1 =
          swapEdge (starRouting.itinerary channel₁ (2 * (m + 1))).1 := by
        rw [RoutingLaw.itinerary_succ, otherEnd_fst, starRouting_routeGerm,
          starGermMap_of_false (itinerary_snd_even (m + 1))]
      rcases ih with ⟨_, h1, hs⟩ | ⟨_, h1, hs⟩
      · refine Or.inr ⟨by rw [e1, h1], by rw [e2, e1, h1]; decide, ?_⟩
        rw [pow_succ, hs]; ring
      · refine Or.inl ⟨by rw [e1, h1], by rw [e2, e1, h1]; decide, ?_⟩
        rw [pow_succ, hs]; ring

/-! ### The exit time of a cap passage -/

open Classical in
/-- The time at which a cap passage entered at time `a` ends.  Along the trajectories of the model
the reflection lemma always applies (`ThroughRun.inv`), so this is the genuine exit time; the
default branch is never used. -/
noncomputable def exitAfter (ε c : ℝ) (u pu : ℝ → ℝ) (a : ℝ) : ℝ :=
  if h : ∃ t, t ∈ Ioc a (a + capReflTime ε c) ∧ u t = u a ∧ pu t = -pu a then h.choose
  else a + capReflTime ε c

theorem exitAfter_spec {ε c : ℝ} {u pu : ℝ → ℝ} {a : ℝ}
    (h : ∃ t, t ∈ Ioc a (a + capReflTime ε c) ∧ u t = u a ∧ pu t = -pu a) :
    exitAfter ε c u pu a ∈ Ioc a (a + capReflTime ε c) ∧
      u (exitAfter ε c u pu a) = u a ∧ pu (exitAfter ε c u pu a) = -pu a := by
  classical
  rw [exitAfter, dif_pos h]
  exact h.choose_spec

/-! ### A microscopic run of the through channel -/

/-- **The data of an explicit microscopic run.**  A genuine longitudinal trajectory `(u, p_u)` of
the microscopic Hamiltonian at scale `ε`, launched on edge `0` at graph coordinate `q₀` towards
the branching vertex with speed `c`, on a time window long enough to carry `N` chain flights. -/
structure ThroughRun where
  /-- the thinness scale -/
  ε : ℝ
  /-- the speed, equivalently the energy `c²/2 ∈ K⋆` -/
  c : ℝ
  /-- the initial graph coordinate on edge `0` -/
  q₀ : ℝ
  /-- the number of chain flights -/
  N : ℕ
  /-- the microscopic longitudinal coordinate -/
  u : ℝ → ℝ
  /-- the microscopic longitudinal momentum -/
  pu : ℝ → ℝ
  N_pos : 1 ≤ N
  eps_pos : 0 < ε
  eps_small : ε ≤ 1 / 1000
  c_ge : 1 ≤ c
  c_le : c ≤ 2
  q_lb : 8 * ε < q₀
  q_ub : q₀ < 1 - 8 * ε
  init_pos : u 0 = -q₀
  init_mom : pu 0 = c
  sol : CapSolution ε c (((N : ℝ) + 1) * (2 / c + capReflTime ε c)) u pu

namespace ThroughRun

/-- The time horizon of the run: long enough for `N` chain flights. -/
noncomputable def horizon (R : ThroughRun) : ℝ :=
  ((R.N : ℝ) + 1) * (2 / R.c + capReflTime R.ε R.c)

theorem sol' (R : ThroughRun) : CapSolution R.ε R.c R.horizon R.u R.pu := R.sol

theorem c_pos (R : ThroughRun) : 0 < R.c := by linarith [R.c_ge]

theorem c_ne (R : ThroughRun) : R.c ≠ 0 := ne_of_gt R.c_pos

theorem tau_pos (R : ThroughRun) : 0 < capReflTime R.ε R.c := capReflTime_pos R.eps_pos R.c_ge

theorem tau_le (R : ThroughRun) : capReflTime R.ε R.c ≤ 100 * R.ε :=
  capReflTime_le R.eps_pos R.c_ge R.c_le

theorem step_pos (R : ThroughRun) : 0 < 2 / R.c + capReflTime R.ε R.c := by
  have := R.tau_pos
  have := R.c_pos
  positivity

/-- The initial distance to `v⋆` of the long free flight `k`: `q₀` for the first, and the tube
boundary `1 - 8ε` for every later one. -/
noncomputable def rad (R : ThroughRun) : ℕ → ℝ
  | 0 => R.q₀
  | _ + 1 => 1 - 8 * R.ε

@[simp] theorem rad_zero (R : ThroughRun) : rad R 0 = R.q₀ := rfl
@[simp] theorem rad_succ (R : ThroughRun) (k : ℕ) : rad R (k + 1) = 1 - 8 * R.ε := rfl

theorem off_lt_rad (R : ThroughRun) (k : ℕ) : 8 * R.ε < rad R k := by
  cases k with
  | zero => exact R.q_lb
  | succ m => rw [rad_succ]; linarith [R.eps_pos, R.eps_small]

theorem rad_le (R : ThroughRun) (k : ℕ) : rad R k ≤ 1 - 8 * R.ε := by
  cases k with
  | zero => exact R.q_ub.le
  | succ m => rw [rad_succ]

theorem rad_lt_one (R : ThroughRun) (k : ℕ) : rad R k < 1 := by
  have := R.rad_le k
  linarith [R.eps_pos]

theorem rad_pos (R : ThroughRun) (k : ℕ) : 0 < rad R k :=
  lt_trans (by linarith [R.eps_pos]) (R.off_lt_rad k)

/-- The duration of the long free flight `k`. -/
noncomputable def longDur (R : ThroughRun) (k : ℕ) : ℝ := (rad R k + 1 - 8 * R.ε) / R.c

theorem longDur_pos (R : ThroughRun) (k : ℕ) : 0 < longDur R k := by
  apply div_pos _ R.c_pos
  have := R.off_lt_rad k
  linarith

theorem longDur_le (R : ThroughRun) (k : ℕ) : longDur R k ≤ 2 / R.c := by
  have hc := R.c_pos
  rw [longDur, div_le_div_iff₀ hc hc]
  nlinarith [R.rad_le k, R.eps_pos]

/-- The entry time of the `k`-th long free flight. -/
noncomputable def beta (R : ThroughRun) : ℕ → ℝ
  | 0 => 0
  | k + 1 => exitAfter R.ε R.c R.u R.pu (beta R k + longDur R k)

@[simp] theorem beta_zero (R : ThroughRun) : beta R 0 = 0 := rfl

/-- The entry time of the `k`-th cap passage. -/
noncomputable def alpha (R : ThroughRun) (k : ℕ) : ℝ := beta R k + longDur R k

theorem beta_succ (R : ThroughRun) (k : ℕ) :
    beta R (k + 1) = exitAfter R.ε R.c R.u R.pu (alpha R k) := by
  simp only [beta, alpha]

theorem beta_lt_alpha (R : ThroughRun) (k : ℕ) : beta R k < alpha R k := by
  rw [alpha]; linarith [R.longDur_pos k]

/-- The time at which the `k`-th long free flight crosses the router boundary next to `v⋆`. -/
noncomputable def sigma (R : ThroughRun) (k : ℕ) : ℝ :=
  beta R k + (rad R k - 8 * R.ε) / R.c

theorem beta_lt_sigma (R : ThroughRun) (k : ℕ) : beta R k < sigma R k := by
  have h : 0 < (rad R k - 8 * R.ε) / R.c := div_pos (by linarith [R.off_lt_rad k]) R.c_pos
  rw [sigma]; linarith

theorem sigma_add_lt_alpha (R : ThroughRun) (k : ℕ) :
    sigma R k + 16 * R.ε / R.c < alpha R k := by
  have hc := R.c_ne
  have h : alpha R k - (sigma R k + 16 * R.ε / R.c) = (1 - 16 * R.ε) / R.c := by
    rw [alpha, sigma, longDur]; field_simp; ring
  have h2 : 0 < (1 - 16 * R.ε) / R.c :=
    div_pos (by linarith [R.eps_small, R.eps_pos]) R.c_pos
  linarith

/-! #### The recursion invariant -/

/-- The state of the run at the beginning of the `k`-th long free flight: it starts at the far
tube boundary of its edge, moving towards `v⋆` at the nominal speed. -/
structure Inv (R : ThroughRun) (k : ℕ) : Prop where
  nonneg : 0 ≤ beta R k
  le : beta R k ≤ (k : ℝ) * (2 / R.c + capReflTime R.ε R.c)
  pos : R.u (beta R k) = -(-1 : ℝ) ^ k * rad R k
  mom : R.pu (beta R k) = (-1 : ℝ) ^ k * R.c

section Invariant

variable {R : ThroughRun}

theorem Inv.beta_nonneg {k : ℕ} (h : Inv R k) : 0 ≤ beta R k := h.nonneg

theorem Inv.alpha_nonneg {k : ℕ} (h : Inv R k) : 0 ≤ alpha R k :=
  le_trans h.nonneg (R.beta_lt_alpha k).le

theorem Inv.beta_mem {k : ℕ} (h : Inv R k) (hk : k ≤ R.N) :
    beta R k ∈ Icc (0 : ℝ) R.horizon := by
  refine ⟨h.nonneg, h.le.trans ?_⟩
  rw [horizon]
  refine mul_le_mul_of_nonneg_right ?_ R.step_pos.le
  have : (k : ℝ) ≤ (R.N : ℝ) := Nat.cast_le.mpr hk
  linarith

theorem Inv.alpha_le {k : ℕ} (h : Inv R k) :
    alpha R k + capReflTime R.ε R.c ≤
      ((k : ℝ) + 1) * (2 / R.c + capReflTime R.ε R.c) := by
  have hexp : ((k : ℝ) + 1) * (2 / R.c + capReflTime R.ε R.c) =
      (k : ℝ) * (2 / R.c + capReflTime R.ε R.c) + (2 / R.c + capReflTime R.ε R.c) := by ring
  rw [alpha, hexp]
  linarith [h.le, R.longDur_le k]

theorem Inv.alpha_horizon {k : ℕ} (h : Inv R k) (hk : k ≤ R.N) :
    alpha R k + capReflTime R.ε R.c ≤ R.horizon := by
  refine h.alpha_le.trans ?_
  rw [horizon]
  refine mul_le_mul_of_nonneg_right ?_ R.step_pos.le
  have : (k : ℝ) ≤ (R.N : ℝ) := Nat.cast_le.mpr hk
  linarith

theorem Inv.alpha_mem {k : ℕ} (h : Inv R k) (hk : k ≤ R.N) :
    alpha R k ∈ Icc (0 : ℝ) R.horizon :=
  ⟨h.alpha_nonneg, le_trans (by linarith [R.tau_pos]) (h.alpha_horizon hk)⟩

theorem abs_neg_one_pow (k : ℕ) : |(-1 : ℝ) ^ k| = 1 := by
  rw [abs_pow, abs_neg, abs_one, one_pow]

theorem neg_one_pow_cases (k : ℕ) : (-1 : ℝ) ^ k = 1 ∨ (-1 : ℝ) ^ k = -1 := by
  rcases Nat.even_or_odd k with hk | hk
  · exact Or.inl hk.neg_one_pow
  · exact Or.inr hk.neg_one_pow

/-- **The long free flight.**  On `[beta k, alpha k]` the microscopic motion is exactly free: the
momentum is constant and the position affine.  This is proved from the Hamiltonian, using only
that `capPot ε` vanishes identically on the closed edge. -/
theorem Inv.flight {k : ℕ} (h : Inv R k) (hk : k ≤ R.N) :
    ∀ t ∈ Icc (beta R k) (alpha R k),
      R.u t = -(-1 : ℝ) ^ k * rad R k + (-1 : ℝ) ^ k * R.c * (t - beta R k) ∧
        R.pu t = (-1 : ℝ) ^ k * R.c := by
  have hc := R.c_ne
  have hsgn := abs_neg_one_pow k
  have hab : beta R k ≤ alpha R k := (R.beta_lt_alpha k).le
  have h1 : |R.u (beta R k)| < 1 := by
    rw [h.pos, abs_mul, abs_neg, hsgn, one_mul, abs_of_pos (R.rad_pos k)]
    exact R.rad_lt_one k
  have hend : R.u (beta R k) + R.pu (beta R k) * (alpha R k - beta R k) =
      (-1 : ℝ) ^ k * (1 - 8 * R.ε) := by
    rw [h.pos, h.mom, alpha, longDur]
    field_simp
    ring
  have h2 : |R.u (beta R k) + R.pu (beta R k) * (alpha R k - beta R k)| < 1 := by
    rw [hend, abs_mul, hsgn, one_mul, abs_of_pos (by linarith [R.eps_pos, R.eps_small])]
    linarith [R.eps_pos]
  intro t ht
  obtain ⟨hu, hp⟩ := R.sol'.free_of_endpoints (h.beta_mem hk) (h.alpha_mem hk) hab h1 h2 t ht
  exact ⟨by rw [hu, h.pos, h.mom], by rw [hp, h.mom]⟩

theorem Inv.u_alpha {k : ℕ} (h : Inv R k) (hk : k ≤ R.N) :
    R.u (alpha R k) = (-1 : ℝ) ^ k * (1 - 8 * R.ε) := by
  have hc := R.c_ne
  have := (h.flight hk (alpha R k) (right_mem_Icc.mpr (R.beta_lt_alpha k).le)).1
  rw [this, alpha, longDur]
  field_simp
  ring

theorem Inv.pu_alpha {k : ℕ} (h : Inv R k) (hk : k ≤ R.N) :
    R.pu (alpha R k) = (-1 : ℝ) ^ k * R.c :=
  (h.flight hk (alpha R k) (right_mem_Icc.mpr (R.beta_lt_alpha k).le)).2

/-- **The cap passage.**  At the end of the long free flight the particle enters a router and is
reflected exactly, so the next long free flight starts in the mirrored state.  This is where
`CapSolution.reflect` — hence `Reflection.reflect_of_barrier` — is used. -/
theorem Inv.exit {k : ℕ} (h : Inv R k) (hk : k ≤ R.N) :
    beta R (k + 1) ∈ Ioc (alpha R k) (alpha R k + capReflTime R.ε R.c) ∧
      R.u (beta R (k + 1)) = R.u (alpha R k) ∧
      R.pu (beta R (k + 1)) = -R.pu (alpha R k) := by
  obtain ⟨t₁, ht₁, hu₁, hp₁⟩ :=
    R.sol'.reflect (neg_one_pow_cases k) h.alpha_nonneg (h.alpha_horizon hk)
      (h.u_alpha hk) (h.pu_alpha hk)
  have hex : ∃ t, t ∈ Ioc (alpha R k) (alpha R k + capReflTime R.ε R.c) ∧
      R.u t = R.u (alpha R k) ∧ R.pu t = -R.pu (alpha R k) :=
    ⟨t₁, ht₁, by rw [hu₁, h.u_alpha hk], by rw [hp₁, h.pu_alpha hk]⟩
  obtain ⟨hmem, hpos, hmom⟩ := exitAfter_spec hex
  rw [← R.beta_succ k] at hmem hpos hmom
  exact ⟨hmem, hpos, hmom⟩

/-- The junction residence time of a cap passage is at most `capReflTime = O(ε)`. -/
theorem Inv.alpha_lt_beta_succ {k : ℕ} (h : Inv R k) (hk : k ≤ R.N) :
    alpha R k < beta R (k + 1) := (h.exit hk).1.1

theorem Inv.beta_succ_le {k : ℕ} (h : Inv R k) (hk : k ≤ R.N) :
    beta R (k + 1) ≤ alpha R k + capReflTime R.ε R.c := (h.exit hk).1.2

theorem Inv.succ {k : ℕ} (h : Inv R k) (hk : k ≤ R.N) : Inv R (k + 1) := by
  obtain ⟨hmem, hpos, hmom⟩ := h.exit hk
  refine ⟨le_trans h.alpha_nonneg hmem.1.le, ?_, ?_, ?_⟩
  · refine le_trans hmem.2 (le_trans h.alpha_le (le_of_eq ?_))
    push_cast
    ring
  · rw [hpos, h.u_alpha hk, rad_succ, pow_succ]; ring
  · rw [hmom, h.pu_alpha hk, pow_succ]; ring

/-- **The invariant holds along the whole run**: the recursion never leaves the time window. -/
theorem inv (R : ThroughRun) : ∀ k ≤ R.N + 1, Inv R k := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨le_rfl, by simp, ?_, ?_⟩
      · rw [beta_zero, R.init_pos, rad_zero]; norm_num
      · rw [beta_zero, R.init_mom]; norm_num
  | succ m ih => intro hm; exact (ih (by omega)).succ (by omega)

end Invariant

/-! ### The projected chain -/

/-- The start time of chain flight `j`: flight `2k` starts the long free flight `k` at the far
tube boundary, flight `2k+1` starts on the other side of the junction. -/
noncomputable def startT (R : ThroughRun) (j : ℕ) : ℝ :=
  if j % 2 = 0 then beta R (j / 2) else sigma R (j / 2) + 16 * R.ε / R.c

/-- The end time of chain flight `j`.  The last flight of the window is stopped strictly inside
its tube. -/
noncomputable def stopT (R : ThroughRun) (j : ℕ) : ℝ :=
  if j = R.N then startT R j + 1 / (2 * R.c)
  else if j % 2 = 0 then sigma R (j / 2) else alpha R (j / 2)

/-- The projected graph state during chain flight `j`: the graph coordinate is `|u|` and the
graph momentum is `±c`, oriented towards the vertex the flight is heading for. -/
noncomputable def crv (R : ThroughRun) (j : ℕ) (t : ℝ) : ℝ × ℝ :=
  if j % 2 = 0 then (rad R (j / 2) - R.c * (t - startT R j), -R.c)
  else (8 * R.ε + R.c * (t - startT R j), R.c)

theorem startT_even (R : ThroughRun) (k : ℕ) : startT R (2 * k) = beta R k := by
  have h1 : 2 * k % 2 = 0 := by omega
  have h2 : 2 * k / 2 = k := by omega
  unfold startT
  rw [if_pos h1, h2]

theorem startT_odd (R : ThroughRun) (k : ℕ) :
    startT R (2 * k + 1) = sigma R k + 16 * R.ε / R.c := by
  have h1 : ¬ (2 * k + 1) % 2 = 0 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  unfold startT
  rw [if_neg h1, h2]

theorem stopT_even (R : ThroughRun) {k : ℕ} (h : 2 * k ≠ R.N) :
    stopT R (2 * k) = sigma R k := by
  have h1 : 2 * k % 2 = 0 := by omega
  have h2 : 2 * k / 2 = k := by omega
  unfold stopT
  rw [if_neg h, if_pos h1, h2]

theorem stopT_odd (R : ThroughRun) {k : ℕ} (h : 2 * k + 1 ≠ R.N) :
    stopT R (2 * k + 1) = alpha R k := by
  have h1 : ¬ (2 * k + 1) % 2 = 0 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  unfold stopT
  rw [if_neg h, if_neg h1, h2]

theorem stopT_last (R : ThroughRun) : stopT R R.N = startT R R.N + 1 / (2 * R.c) := by
  unfold stopT
  rw [if_pos rfl]

theorem crv_even_fun (R : ThroughRun) (k : ℕ) :
    crv R (2 * k) = fun t => (rad R k - R.c * (t - beta R k), -R.c) := by
  funext t
  have h1 : 2 * k % 2 = 0 := by omega
  have h2 : 2 * k / 2 = k := by omega
  unfold crv
  rw [if_pos h1, h2, startT_even]

theorem crv_odd_fun (R : ThroughRun) (k : ℕ) :
    crv R (2 * k + 1) =
      fun t => (8 * R.ε + R.c * (t - startT R (2 * k + 1)), R.c) := by
  funext t
  have h1 : ¬ (2 * k + 1) % 2 = 0 := by omega
  unfold crv
  rw [if_neg h1]

theorem crv_even_fst (R : ThroughRun) (k : ℕ) (t : ℝ) :
    (crv R (2 * k) t).1 = rad R k - R.c * (t - beta R k) := by rw [crv_even_fun]

theorem crv_even_snd (R : ThroughRun) (k : ℕ) (t : ℝ) : (crv R (2 * k) t).2 = -R.c := by
  rw [crv_even_fun]

theorem crv_odd_fst (R : ThroughRun) (k : ℕ) (t : ℝ) :
    (crv R (2 * k + 1) t).1 = 8 * R.ε + R.c * (t - startT R (2 * k + 1)) := by
  rw [crv_odd_fun]

theorem crv_odd_snd (R : ThroughRun) (k : ℕ) (t : ℝ) : (crv R (2 * k + 1) t).2 = R.c := by
  rw [crv_odd_fun]

/-! #### The travelled distance along a flight -/

theorem c_dur_even (R : ThroughRun) {k : ℕ} (h : 2 * k ≠ R.N) :
    R.c * (stopT R (2 * k) - startT R (2 * k)) = rad R k - 8 * R.ε := by
  have hc := R.c_ne
  rw [stopT_even R h, startT_even, sigma]
  field_simp
  ring

theorem c_dur_odd (R : ThroughRun) {k : ℕ} (h : 2 * k + 1 ≠ R.N) :
    R.c * (stopT R (2 * k + 1) - startT R (2 * k + 1)) = 1 - 16 * R.ε := by
  have hc := R.c_ne
  rw [stopT_odd R h, startT_odd, alpha, sigma, longDur]
  field_simp
  ring

theorem c_dur_last (R : ThroughRun) :
    R.c * (stopT R R.N - startT R R.N) = 1 / 2 := by
  have hc := R.c_ne
  rw [stopT_last]
  field_simp
  ring

/-- The chain flights have positive duration. -/
theorem startT_lt_stopT (R : ThroughRun) {j : ℕ} (hj : j ≤ R.N) : startT R j < stopT R j := by
  have hc := R.c_pos
  rcases eq_or_lt_of_le hj with heq | hlt
  · rw [heq, stopT_last]
    have : 0 < 1 / (2 * R.c) := by positivity
    linarith
  · obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · subst hk
      rw [startT_even, stopT_even R (by omega)]
      exact R.beta_lt_sigma k
    · subst hk
      rw [startT_odd, stopT_odd R (by omega)]
      exact R.sigma_add_lt_alpha k

/-- **The chain flights stay in the tube.**  This is the exact statement `flight_tube` of
`HybridChain` for the offset `8ε`. -/
theorem crv_fst_mem_Icc (R : ThroughRun) {j : ℕ} (hj : j ≤ R.N) {t : ℝ}
    (ht : t ∈ Icc (startT R j) (stopT R j)) :
    (crv R j t).1 ∈ Icc (8 * R.ε) (1 - 8 * R.ε) := by
  have hc := R.c_pos
  have hε := R.eps_pos
  have hεs := R.eps_small
  have h0 : 0 ≤ R.c * (t - startT R j) := by nlinarith [ht.1]
  have hd : R.c * (t - startT R j) ≤ R.c * (stopT R j - startT R j) := by nlinarith [ht.2]
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    rw [crv_even_fst, ← startT_even R k]
    rcases eq_or_ne (2 * k) R.N with heq | hne
    · have hk1 : 1 ≤ k := by have := R.N_pos; omega
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hlast : R.c * (stopT R (2 * (m + 1)) - startT R (2 * (m + 1))) = 1 / 2 := by
        rw [heq]; exact R.c_dur_last
      rw [hlast] at hd
      rw [rad_succ]
      constructor <;> linarith
    · rw [c_dur_even R hne] at hd
      have := R.rad_le k
      constructor <;> linarith
  · subst hk
    rw [crv_odd_fst]
    rcases eq_or_ne (2 * k + 1) R.N with heq | hne
    · have hlast : R.c * (stopT R (2 * k + 1) - startT R (2 * k + 1)) = 1 / 2 := by
        rw [heq]; exact R.c_dur_last
      rw [hlast] at hd
      constructor <;> linarith
    · rw [c_dur_odd R hne] at hd
      constructor <;> linarith

/-- The strict version: a flight touches the router boundary only at its endpoints. -/
theorem crv_fst_mem_Ioo (R : ThroughRun) {j : ℕ} (hj : j ≤ R.N) {t : ℝ}
    (ht : t ∈ Ioo (startT R j) (stopT R j)) :
    (crv R j t).1 ∈ Ioo (8 * R.ε) (1 - 8 * R.ε) := by
  have hc := R.c_pos
  have hε := R.eps_pos
  have hεs := R.eps_small
  have h0 : 0 < R.c * (t - startT R j) := by nlinarith [ht.1]
  have hd : R.c * (t - startT R j) < R.c * (stopT R j - startT R j) := by nlinarith [ht.2]
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    rw [crv_even_fst, ← startT_even R k]
    rcases eq_or_ne (2 * k) R.N with heq | hne
    · have hk1 : 1 ≤ k := by have := R.N_pos; omega
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hlast : R.c * (stopT R (2 * (m + 1)) - startT R (2 * (m + 1))) = 1 / 2 := by
        rw [heq]; exact R.c_dur_last
      rw [hlast] at hd
      rw [rad_succ]
      constructor <;> linarith
    · rw [c_dur_even R hne] at hd
      have := R.rad_le k
      constructor <;> linarith
  · subst hk
    rw [crv_odd_fst]
    rcases eq_or_ne (2 * k + 1) R.N with heq | hne
    · have hlast : R.c * (stopT R (2 * k + 1) - startT R (2 * k + 1)) = 1 / 2 := by
        rw [heq]; exact R.c_dur_last
      rw [hlast] at hd
      constructor <;> linarith
    · rw [c_dur_odd R hne] at hd
      constructor <;> linarith

/-- The last flight of the window ends strictly inside its tube. -/
theorem crv_final (R : ThroughRun) :
    (crv R R.N (stopT R R.N)).1 ∈ Ioo (8 * R.ε) (1 - 8 * R.ε) := by
  have hc := R.c_pos
  have hε := R.eps_pos
  have hεs := R.eps_small
  have hd := R.c_dur_last
  obtain ⟨k, hk | hk⟩ : ∃ k, R.N = 2 * k ∨ R.N = 2 * k + 1 := ⟨R.N / 2, by omega⟩
  · have hk1 : 1 ≤ k := by have := R.N_pos; omega
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hd' : R.c * (stopT R (2 * (m + 1)) - startT R (2 * (m + 1))) = 1 / 2 := by
      rw [← hk]; exact hd
    rw [hk, crv_even_fst, ← startT_even R (m + 1), rad_succ]
    constructor <;> linarith
  · have hd' : R.c * (stopT R (2 * k + 1) - startT R (2 * k + 1)) = 1 / 2 := by
      rw [← hk]; exact hd
    rw [hk, crv_odd_fst]
    constructor <;> linarith

/-! #### The germ data -/

theorem coord_even (k : ℕ) :
    EdgeEnd.coordinate starGraph (starRouting.itinerary channel₁ (2 * k)) = 0 :=
  coordinate_of_false (itinerary_snd_even k)

theorem sign_even (k : ℕ) :
    EdgeEnd.sign starGraph (starRouting.itinerary channel₁ (2 * k)) = -1 :=
  sign_of_false (itinerary_snd_even k)

theorem coord_odd (k : ℕ) :
    EdgeEnd.coordinate starGraph (starRouting.itinerary channel₁ (2 * k + 1)) = 1 :=
  coordinate_of_true starGraph_length_eq_one (itinerary_snd_odd k)

theorem sign_odd (k : ℕ) :
    EdgeEnd.sign starGraph (starRouting.itinerary channel₁ (2 * k + 1)) = 1 :=
  sign_of_true (itinerary_snd_odd k)

theorem routed_snd (j : ℕ) :
    (starRouting.routeGerm (starRouting.itinerary channel₁ j)).2 =
      (starRouting.itinerary channel₁ j).2 := by
  rw [starRouting_routeGerm, starGermMap_snd]

theorem routed_coord_even (k : ℕ) :
    EdgeEnd.coordinate starGraph
      (starRouting.routeGerm (starRouting.itinerary channel₁ (2 * k))) = 0 :=
  coordinate_of_false (by rw [routed_snd]; exact itinerary_snd_even k)

theorem routed_sign_even (k : ℕ) :
    EdgeEnd.sign starGraph
      (starRouting.routeGerm (starRouting.itinerary channel₁ (2 * k))) = -1 :=
  sign_of_false (by rw [routed_snd]; exact itinerary_snd_even k)

theorem routed_coord_odd (k : ℕ) :
    EdgeEnd.coordinate starGraph
      (starRouting.routeGerm (starRouting.itinerary channel₁ (2 * k + 1))) = 1 :=
  coordinate_of_true starGraph_length_eq_one (by rw [routed_snd]; exact itinerary_snd_odd k)

theorem routed_sign_odd (k : ℕ) :
    EdgeEnd.sign starGraph
      (starRouting.routeGerm (starRouting.itinerary channel₁ (2 * k + 1))) = 1 :=
  sign_of_true (by rw [routed_snd]; exact itinerary_snd_odd k)

/-! #### The chain -/

theorem hasDerivAt_crv_even (R : ThroughRun) (k : ℕ) (s : ℝ) :
    HasDerivAt (crv R (2 * k)) (-R.c, 0) s := by
  rw [crv_even_fun]
  have h1 : HasDerivAt (fun t : ℝ => rad R k - R.c * (t - beta R k)) (-R.c) s := by
    simpa using (((hasDerivAt_id s).sub_const (beta R k)).const_mul R.c).const_sub (rad R k)
  exact h1.prodMk (hasDerivAt_const s (-R.c))

theorem hasDerivAt_crv_odd (R : ThroughRun) (k : ℕ) (s : ℝ) :
    HasDerivAt (crv R (2 * k + 1)) (R.c, 0) s := by
  rw [crv_odd_fun]
  have h1 : HasDerivAt
      (fun t : ℝ => 8 * R.ε + R.c * (t - startT R (2 * k + 1))) R.c s := by
    simpa using
      (((hasDerivAt_id s).sub_const (startT R (2 * k + 1))).const_mul R.c).const_add (8 * R.ε)
  exact h1.prodMk (hasDerivAt_const s R.c)

/-- **The projected chain of the microscopic run.**  Every field of `HybridChain` is discharged
from the explicit description of the run; in particular the ODE tolerance and the momentum
tolerance are `0`, because the longitudinal motion in a tube is exactly free and the reflection at
a cap reverses the momentum exactly. -/
noncomputable def chain (R : ThroughRun) :
    HybridChain (zeroPotential starGraph) starRouting (starParams R.ε) where
  N := R.N
  start := startT R
  stop := stopT R
  edge j := (starRouting.itinerary channel₁ j).1
  curve := crv R
  germ := starRouting.itinerary channel₁
  start_zero := by
    have := startT_even R 0
    simpa using this
  start_lt_stop := fun j hj => R.startT_lt_stopT hj
  stop_le_start_succ := by
    intro j hj
    have hc := R.c_pos
    have hε := R.eps_pos
    obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · subst hk
      rw [stopT_even R (by omega), startT_odd]
      have : 0 ≤ 16 * R.ε / R.c := by positivity
      linarith
    · subst hk
      rw [stopT_odd R (by omega), show 2 * k + 1 + 1 = 2 * (k + 1) by ring, startT_even]
      exact ((R.inv k (by omega)).alpha_lt_beta_succ (by omega)).le
  start_succ_le := by
    intro j hj
    rw [starParams_dwell_of_pos R.eps_pos]
    have hc := R.c_pos
    have hc1 := R.c_ge
    have hε := R.eps_pos
    obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · subst hk
      rw [stopT_even R (by omega), startT_odd]
      have h16 : 16 * R.ε / R.c ≤ 100 * R.ε := by
        rw [div_le_iff₀ hc]
        nlinarith
      linarith
    · subst hk
      rw [stopT_odd R (by omega), show 2 * k + 1 + 1 = 2 * (k + 1) by ring, startT_even]
      have h1 := (R.inv k (by omega)).beta_succ_le (by omega)
      have h2 := R.tau_le
      linarith
  flight_ode := by
    intro j _
    refine ⟨fun s => ((crv R j s).2, 0), fun t _ => ⟨?_, ?_⟩⟩
    · rw [zeroPotential_edgeVectorField]
      simp
    · show HasDerivWithinAt (crv R j) ((crv R j t).2, 0) _ t
      obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
      · subst hk
        rw [crv_even_snd]
        exact (R.hasDerivAt_crv_even k t).hasDerivWithinAt
      · subst hk
        rw [crv_odd_snd]
        exact (R.hasDerivAt_crv_odd k t).hasDerivWithinAt
  flight_tube := by
    intro j hj t ht
    rw [starGraph_length_eq_one, starParams_offset_of_pos R.eps_pos]
    exact R.crv_fst_mem_Icc hj ht
  flight_inside := by
    intro j hj t ht
    rw [starGraph_length_eq_one, starParams_offset_of_pos R.eps_pos]
    exact R.crv_fst_mem_Ioo hj ht
  final_inside := by
    rw [starGraph_length_eq_one, starParams_offset_of_pos R.eps_pos]
    exact R.crv_final
  germ_edge := fun _ _ => rfl
  edge_succ := by
    intro j _
    rw [RoutingLaw.itinerary_succ, otherEnd_fst]
  arrive := by
    intro j hj
    rw [starParams_offset_of_pos R.eps_pos]
    have hc := R.c_ne
    obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · subst hk
      rw [crv_even_fst, ← startT_even R k, coord_even, sign_even]
      have := R.c_dur_even (k := k) (by omega)
      linarith
    · subst hk
      rw [crv_odd_fst, coord_odd, sign_odd]
      have := R.c_dur_odd (k := k) (by omega)
      linarith
  depart_coord := by
    intro j hj
    rw [starParams_offset_of_pos R.eps_pos]
    obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · subst hk
      rw [routed_coord_even, routed_sign_even, crv_odd_fst]
      ring
    · subst hk
      rw [routed_coord_odd, routed_sign_odd,
        show 2 * k + 1 + 1 = 2 * (k + 1) by ring, crv_even_fst, ← startT_even R (k + 1),
        rad_succ]
      ring
  depart_mom := by
    intro j hj
    have hc := R.c_pos
    obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · subst hk
      rw [crv_odd_snd, crv_even_snd, RoutingLaw.departureMomentum, routed_sign_even,
        abs_neg, abs_of_pos hc]
      simp
    · subst hk
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, crv_even_snd, crv_odd_snd,
        RoutingLaw.departureMomentum, routed_sign_odd, abs_of_pos hc]
      simp

/-! #### The chain is the projection of the microscopic trajectory -/

/-- The embedding of the through channel of `Γ⋆` into the `u`-axis: edge `1` is the positive
half-axis, edge `0` the negative one.  (Edge `2`, the third arm, is embedded in the `w`-axis and
plays no role in the through channel.) -/
noncomputable def embedSign (e : starGraph.Edge) : ℝ := if e = 1 then 1 else -1

theorem embedSign_zero : embedSign 0 = -1 := by rw [embedSign, if_neg (by decide)]

theorem embedSign_one : embedSign 1 = 1 := by rw [embedSign, if_pos rfl]

theorem embedSign_even (k : ℕ) :
    embedSign (starRouting.itinerary channel₁ (2 * k)).1 = -(-1 : ℝ) ^ k := by
  rcases itinerary_through k with ⟨h0, _, hs⟩ | ⟨h0, _, hs⟩
  · rw [h0, hs, embedSign_zero]
  · rw [h0, hs, embedSign_one]; ring

theorem embedSign_odd (k : ℕ) :
    embedSign (starRouting.itinerary channel₁ (2 * k + 1)).1 = (-1 : ℝ) ^ k := by
  rcases itinerary_through k with ⟨_, h1, hs⟩ | ⟨_, h1, hs⟩
  · rw [h1, hs]; exact embedSign_one
  · rw [h1, hs]; exact embedSign_zero

theorem c_alpha_sub_even (R : ThroughRun) (k : ℕ) :
    R.c * (alpha R k - startT R (2 * k)) = rad R k + 1 - 8 * R.ε := by
  have hc := R.c_ne
  rw [startT_even, alpha, longDur]
  field_simp
  ring

theorem c_alpha_sub_odd (R : ThroughRun) (k : ℕ) :
    R.c * (alpha R k - startT R (2 * k + 1)) = 1 - 16 * R.ε := by
  have hc := R.c_ne
  rw [startT_odd, alpha, sigma, longDur]
  field_simp
  ring

/-- Every chain flight lies inside the long free flight that carries it. -/
theorem interval_subset (R : ThroughRun) {j k : ℕ} (hj : j ≤ R.N)
    (hk : j = 2 * k ∨ j = 2 * k + 1) :
    Icc (startT R j) (stopT R j) ⊆ Icc (beta R k) (alpha R k) := by
  have hc := R.c_pos
  have hε := R.eps_pos
  have hεs := R.eps_small
  have key : ∀ x : ℝ, R.c * (stopT R j - startT R j) ≤ R.c * (alpha R k - startT R j) →
      stopT R j ≤ alpha R k := by
    intro _ h
    nlinarith
  rcases hk with rfl | rfl
  · refine Icc_subset_Icc (le_of_eq (startT_even R k).symm) (key 0 ?_)
    rw [c_alpha_sub_even]
    rcases eq_or_ne (2 * k) R.N with heq | hne
    · have hlast : R.c * (stopT R (2 * k) - startT R (2 * k)) = 1 / 2 := by
        rw [heq]; exact R.c_dur_last
      rw [hlast]
      linarith [R.off_lt_rad k]
    · rw [c_dur_even R hne]
      linarith
  · refine Icc_subset_Icc ?_ (key 0 ?_)
    · rw [startT_odd]
      have h1 := (R.beta_lt_sigma k).le
      have h2 : (0 : ℝ) ≤ 16 * R.ε / R.c := by positivity
      linarith
    · rw [c_alpha_sub_odd]
      rcases eq_or_ne (2 * k + 1) R.N with heq | hne
      · have hlast : R.c * (stopT R (2 * k + 1) - startT R (2 * k + 1)) = 1 / 2 := by
          rw [heq]; exact R.c_dur_last
        rw [hlast]
        linarith
      · rw [c_dur_odd R hne]

/-- **The chain is the graph projection of the microscopic trajectory.**  Along every chain flight
the microscopic longitudinal coordinate and momentum are the graph ones, transported by the
embedding of the edge into the `u`-axis.  Nothing here is assumed: it is read off from the exact
free motion of `CapSolution.free`. -/
theorem projection (R : ThroughRun) {j : ℕ} (hj : j ≤ R.N) {t : ℝ}
    (ht : t ∈ Icc (startT R j) (stopT R j)) :
    R.u t = embedSign (starRouting.itinerary channel₁ j).1 * (crv R j t).1 ∧
      R.pu t = embedSign (starRouting.itinerary channel₁ j).1 * (crv R j t).2 := by
  have hc := R.c_ne
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    have hkN : k ≤ R.N := by omega
    have hI := R.interval_subset hj (Or.inl rfl) ht
    obtain ⟨hu, hp⟩ := (R.inv k (by omega)).flight hkN t hI
    rw [embedSign_even, crv_even_fst, crv_even_snd]
    exact ⟨by rw [hu]; ring, by rw [hp]; ring⟩
  · subst hk
    have hkN : k ≤ R.N := by omega
    have hI := R.interval_subset hj (Or.inr rfl) ht
    obtain ⟨hu, hp⟩ := (R.inv k (by omega)).flight hkN t hI
    have hstart : R.c * (t - startT R (2 * k + 1)) =
        R.c * (t - beta R k) - (rad R k + 8 * R.ε) := by
      rw [startT_odd, sigma]
      field_simp
      ring
    rw [embedSign_odd, crv_odd_fst, crv_odd_snd]
    refine ⟨?_, by rw [hp]⟩
    rw [hu, hstart]
    ring

/-! #### A lower bound on the chain times -/

/-- Every chain flight after the first traverses at least half an edge, so the chain times grow
linearly.  This is what makes the microscopic time window cover the graph one. -/
theorem startT_lower (R : ThroughRun) : ∀ j ≤ R.N,
    ((j : ℝ) - 1) * (1 / (2 * R.c)) ≤ startT R j := by
  have hc := R.c_pos
  have hε := R.eps_pos
  have hεs := R.eps_small
  have hunit : (0 : ℝ) < 1 / (2 * R.c) := by positivity
  have h0 : startT R 0 = 0 := by simpa using startT_even R 0
  have hmono : ∀ m, m < R.N → stopT R m ≤ startT R (m + 1) := fun m hm =>
    (chain R).stop_le_start_succ m (show m < R.N by omega)
  have hdur : ∀ m, 1 ≤ m → m ≤ R.N → 1 / (2 * R.c) ≤ stopT R m - startT R m := by
    intro m hm1 hmN
    have key : (1 : ℝ) / 2 ≤ R.c * (stopT R m - startT R m) →
        1 / (2 * R.c) ≤ stopT R m - startT R m := by
      intro h
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * R.c)]
      nlinarith
    refine key ?_
    obtain ⟨k, hk | hk⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
    · subst hk
      obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      rcases eq_or_ne (2 * (i + 1)) R.N with heq | hne
      · rw [show stopT R (2 * (i + 1)) = stopT R R.N by rw [heq],
          show startT R (2 * (i + 1)) = startT R R.N by rw [heq], R.c_dur_last]
      · have hd := R.c_dur_even (k := i + 1) hne
        rw [rad_succ] at hd
        rw [hd]
        linarith
    · subst hk
      rcases eq_or_ne (2 * k + 1) R.N with heq | hne
      · rw [show stopT R (2 * k + 1) = stopT R R.N by rw [heq],
          show startT R (2 * k + 1) = startT R R.N by rw [heq], R.c_dur_last]
      · rw [R.c_dur_odd hne]
        linarith
  intro j
  induction j with
  | zero =>
      intro _
      rw [h0]
      push_cast
      linarith
  | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hstop := hmono m (by omega)
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · have hlt := R.startT_lt_stopT (show 0 ≤ R.N by omega)
        push_cast
        rw [h0] at hlt
        linarith
      · have hd := hdur m hmpos (by omega)
        push_cast
        push_cast at hprev
        linarith

/-- The chain stays inside the time window on which the microscopic trajectory is defined. -/
theorem stopT_le_horizon (R : ThroughRun) : stopT R R.N ≤ R.horizon := by
  have hc := R.c_pos
  have hτ := R.tau_pos
  have hstep := R.step_pos
  have hhalf : 1 / (2 * R.c) ≤ 2 / R.c + capReflTime R.ε R.c := by
    have h : 1 / (2 * R.c) ≤ 2 / R.c := by
      rw [div_le_div_iff₀ (by positivity) hc]
      linarith
    linarith
  rw [stopT_last, horizon]
  obtain ⟨k, hk | hk⟩ : ∃ k, R.N = 2 * k ∨ R.N = 2 * k + 1 := ⟨R.N / 2, by omega⟩
  · have hI := R.inv k (by omega)
    have h1 : startT R R.N = beta R k := by rw [hk]; exact startT_even R k
    have h2 := hI.le
    have hcast : (k : ℝ) + 1 ≤ (R.N : ℝ) + 1 := by
      have : (k : ℝ) ≤ (R.N : ℝ) := by exact_mod_cast (by omega : k ≤ R.N)
      linarith
    have h4 : ((k : ℝ) + 1) * (2 / R.c + capReflTime R.ε R.c) ≤
        ((R.N : ℝ) + 1) * (2 / R.c + capReflTime R.ε R.c) :=
      mul_le_mul_of_nonneg_right hcast hstep.le
    have hexp : ((k : ℝ) + 1) * (2 / R.c + capReflTime R.ε R.c) =
        (k : ℝ) * (2 / R.c + capReflTime R.ε R.c) + (2 / R.c + capReflTime R.ε R.c) := by ring
    rw [h1]
    linarith
  · have hI := R.inv k (by omega)
    have h1 : startT R R.N = sigma R k + 16 * R.ε / R.c := by rw [hk]; exact startT_odd R k
    have h2 : sigma R k + 16 * R.ε / R.c ≤ alpha R k := (R.sigma_add_lt_alpha k).le
    have h3 := hI.alpha_le
    have hcast : (k : ℝ) + 2 ≤ (R.N : ℝ) + 1 := by
      have : (k : ℝ) + 1 ≤ (R.N : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ R.N)
      linarith
    have h4 : ((k : ℝ) + 2) * (2 / R.c + capReflTime R.ε R.c) ≤
        ((R.N : ℝ) + 1) * (2 / R.c + capReflTime R.ε R.c) :=
      mul_le_mul_of_nonneg_right hcast hstep.le
    have hexp : ((k : ℝ) + 2) * (2 / R.c + capReflTime R.ε R.c) =
        ((k : ℝ) + 1) * (2 / R.c + capReflTime R.ε R.c) + (2 / R.c + capReflTime R.ε R.c) := by
      ring
    rw [h1]
    linarith

/-- The microscopic time window reaches at least `N / (2c)`. -/
theorem stopT_lower (R : ThroughRun) : (R.N : ℝ) / (2 * R.c) ≤ stopT R R.N := by
  have hc := R.c_pos
  have h := R.startT_lower R.N le_rfl
  rw [stopT_last]
  have : ((R.N : ℝ) - 1) * (1 / (2 * R.c)) + 1 / (2 * R.c) = (R.N : ℝ) / (2 * R.c) := by
    field_simp
    ring
  linarith

/-- The chain starts at the initial state of the run: graph coordinate `q₀` on edge `0`, momentum
`-c` (towards the branching vertex). -/
theorem crv_zero_zero (R : ThroughRun) : crv R 0 0 = (R.q₀, -R.c) := by
  have h : (0 : ℕ) = 2 * 0 := by norm_num
  rw [h, crv_even_fun]
  simp

@[simp] theorem chain_N (R : ThroughRun) : (chain R).N = R.N := rfl
@[simp] theorem chain_start (R : ThroughRun) : (chain R).start = startT R := rfl
@[simp] theorem chain_stop (R : ThroughRun) : (chain R).stop = stopT R := rfl
@[simp] theorem chain_curve (R : ThroughRun) : (chain R).curve = crv R := rfl
@[simp] theorem chain_edge (R : ThroughRun) (j : ℕ) :
    (chain R).edge j = (starRouting.itinerary channel₁ j).1 := rfl

end ThroughRun

end HamiltonianMetricGraphs
