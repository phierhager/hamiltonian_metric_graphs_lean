/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.GatePotential
import HamiltonianMetricGraphs.Realization.StarReflection

/-!
# The longitudinal dynamics of the gated through channel

This file analyses completely the one-dimensional motion

  `u' = p_u`,  `p_u' = -gatePot ε '(u)`,

which — by the exact separability of `gatePot2` in the through-channel region — is *exactly* the
longitudinal part of the gated microscopic Hamiltonian dynamics.

The potential `gatePot ε = capPot ε + gateBump ε` has three active regions: the two reflecting
caps at the outer vertices `u = ±1`, and the **energy gate** at the junction `u = 0`.  Between
them it is flat, so the edge flights are exactly free.

## Main results

All times are the sharp ones of Lemma IX.8 (`Reflection.reflect_of_barrier_sharp`) and of the
proof of Theorem IX.10, valid at every scale `0 < ε ≤ 1/100`:

* `free_right`, `free_left` — the motion between the gate and a cap is exactly free
  (`odeErr = 0`);
* `reflect_cap_right`, `reflect_cap_left` — the outer caps reverse the momentum exactly, within
  `23ε` (Lemma IX.8 with `d = 8ε`);
* `reflect_gate_left`, `reflect_gate_right` — **below the gate**, i.e. for longitudinal energy
  `< gateHeight = g₀`, the junction reflects the particle exactly, within `26ε` (Lemma IX.8 with
  `Ψ = (g₀/4)B`, `k = g₀e⁻³`, `d = 6ε`: `t_* < 12ε + 2ε(0.36 + 6.57)`).  This is the low-energy
  routing `η ↦ η`;
* `cross_gate_right`, `cross_gate_left` — **above the gate**, i.e. for longitudinal energy
  `≥ 3/2 > 1.365 > max G_ε`, the speed stays above `1/2`, so the particle crosses the junction
  within `32ε` and emerges with exactly the same speed.  This is the high-energy routing
  `η₁ ↦ η₂`.

Both regimes are consequences of energy conservation for the *same* potential: the gate is at
least `g₀` on its core and at most `g₀e^{2/3} < 1.365` everywhere, and the two energy windows sit
on opposite sides of it.
-/

namespace HamiltonianMetricGraphs

open Set Real

variable {ε c Tmax : ℝ} {u pu : ℝ → ℝ}

/-! ### The time of a gate reflection -/

/-- **The sharp time of one gate reflection**: Lemma IX.8 for the barrier
`Ψ = (g₀/4) B`, whose foot is at `ε/4`, whose height `g₀` is reached at `ε`, whose slope is at
least `g₀/(e³ε)` in between, entered from the distance `d = 6ε` (from the junction boundary
`u = -8ε` to the gate foot `u = -2ε`). -/
noncomputable def gateTime (ε c : ℝ) : ℝ :=
  Reflection.sharpTime (ε / 4) ε (gateHeight / (exp 3 * ε)) (c ^ 2 / 2) (6 * ε)

theorem gateTime_pos (hε : 0 < ε) {c : ℝ} (hc : 1 ≤ c) : 0 < gateTime ε c := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hh := gateHeight_pos
  unfold gateTime Reflection.sharpTime
  have h1 : 0 ≤ 2 * (6 * ε) / Real.sqrt (2 * (c ^ 2 / 2)) := by positivity
  have h2 : 0 < 2 * (ε / 4) / Real.sqrt (c ^ 2 / 2) :=
    div_pos (by linarith) (Real.sqrt_pos.mpr (by positivity))
  have h3 : 0 ≤ 2 * (2 * Real.sqrt (ε - ε / 4) / Real.sqrt (2 * (gateHeight / (exp 3 * ε)))) := by
    positivity
  linarith

/-- **The gate reflection takes less than `26ε`** (proof of Theorem IX.10:
`t_* < 12ε + 2ε(0.36 + 6.57) < 26ε`).  The flat part `[-8ε, -2ε]` is crossed twice in time
`12ε/c ≤ 12ε`, the foot twice in time at most `0.71ε`, and the two climbs take at most
`2ε√(3e³/(2g₀)) < 13.28ε`. -/
theorem gateTime_lt (hε : 0 < ε) {c : ℝ} (hc : 1 ≤ c) : gateTime ε c < 26 * ε := by
  have hc0 : (0 : ℝ) < c := by linarith
  have he := exp_pos 3
  have he3 : exp 3 < 201 / 10 := exp_three_lt
  have hh : gateHeight = 7 / 10 := rfl
  unfold gateTime Reflection.sharpTime
  rw [sqrt_two_mul_half_sq hc0.le]
  have h1 : 2 * (6 * ε) / c ≤ 12 * ε := by
    rw [div_le_iff₀ hc0]; nlinarith
  -- the foot: `2δ/√E ≤ 0.71 ε`, since `√E ≥ √(1/2) > 50/71`
  have hsE : (50 : ℝ) / 71 ≤ Real.sqrt (c ^ 2 / 2) := by
    rw [show (50 : ℝ) / 71 = Real.sqrt ((50 / 71) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 : 2 * (ε / 4) / Real.sqrt (c ^ 2 / 2) ≤ 71 / 100 * ε := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  -- the two climbs: `2 · 2√(3ε/4)/√(2g₀/(e³ε)) < 13.28 ε`
  have h3 : 2 * Real.sqrt (ε - ε / 4) / Real.sqrt (2 * (gateHeight / (exp 3 * ε)))
      < 664 / 100 * ε := by
    refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
    rw [climb_sq hε gateHeight_pos, hh, div_lt_iff₀ (by norm_num)]
    nlinarith [mul_pos hε hε]
  linarith

/-! ### Longitudinal solutions of the gated through channel -/

/-- **A longitudinal solution of the gated through channel** on the time window `[0, Tmax]`, at
scale `ε` and energy `c²/2`. -/
structure GateSolution (ε c Tmax : ℝ) (u pu : ℝ → ℝ) : Prop where
  eps_pos : 0 < ε
  eps_small : ε ≤ 1 / 100
  c_ge : 1 ≤ c
  c_le : c ≤ 2
  time_nonneg : 0 ≤ Tmax
  ode_pos : ∀ t ∈ Icc (0 : ℝ) Tmax, HasDerivWithinAt u (pu t) (Icc (0 : ℝ) Tmax) t
  ode_mom : ∀ t ∈ Icc (0 : ℝ) Tmax,
    HasDerivWithinAt pu (-deriv (gatePot ε) (u t)) (Icc (0 : ℝ) Tmax) t
  energy : ∀ t ∈ Icc (0 : ℝ) Tmax, pu t ^ 2 / 2 + gatePot ε (u t) = c ^ 2 / 2

namespace GateSolution

theorem c_pos (S : GateSolution ε c Tmax u pu) : 0 < c := by linarith [S.c_ge]

theorem abs_mom_le (S : GateSolution ε c Tmax u pu) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Tmax) :
    |pu t| ≤ c := by
  have h := S.energy t ht
  have hp := gatePot_nonneg ε (u t)
  have hsq : pu t ^ 2 ≤ c ^ 2 := by linarith
  calc |pu t| = Real.sqrt (pu t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hsq
    _ = c := Real.sqrt_sq S.c_pos.le

theorem travel_le (S : GateSolution ε c Tmax u pu) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) Tmax) (ht : t ∈ Icc (0 : ℝ) Tmax) (hst : s ≤ t) :
    |u t - u s| ≤ c * (t - s) :=
  abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le S.ode_pos
    (fun _ hv => S.abs_mom_le hv) hs ht hst

theorem continuousOn_pos (S : GateSolution ε c Tmax u pu) :
    ContinuousOn u (Icc (0 : ℝ) Tmax) := fun t ht => (S.ode_pos t ht).continuousWithinAt

theorem continuousOn_mom (S : GateSolution ε c Tmax u pu) :
    ContinuousOn pu (Icc (0 : ℝ) Tmax) := fun t ht => (S.ode_mom t ht).continuousWithinAt

/-! #### Exactly free motion between the gate and the caps -/

/-- **The motion between the gate and the right cap is exactly free.** -/
theorem free_right (S : GateSolution ε c Tmax u pu) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (hbnd : ∀ t ∈ Icc a b, u a + pu a * (t - a) ∈ Ioo (2 * ε) 1) :
    ∀ t ∈ Icc a b, u t = u a + pu a * (t - a) ∧ pu t = pu a := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha.1 hb.2
  exact free_motion (Φ := gatePot ε) (A := 2 * ε) (B := 1)
    (fun y hy => deriv_gatePot_of_mem_right S.eps_pos hy.1 hy.2) hab
    (fun t ht => (S.ode_pos t (hsub ht)).mono hsub)
    (fun t ht => (S.ode_mom t (hsub ht)).mono hsub) hbnd

/-- **The motion between the gate and the left cap is exactly free.** -/
theorem free_left (S : GateSolution ε c Tmax u pu) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (hbnd : ∀ t ∈ Icc a b, u a + pu a * (t - a) ∈ Ioo (-1 : ℝ) (-(2 * ε))) :
    ∀ t ∈ Icc a b, u t = u a + pu a * (t - a) ∧ pu t = pu a := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha.1 hb.2
  exact free_motion (Φ := gatePot ε) (A := -1) (B := -(2 * ε))
    (fun y hy => deriv_gatePot_of_mem_left S.eps_pos hy.1 hy.2) hab
    (fun t ht => (S.ode_pos t (hsub ht)).mono hsub)
    (fun t ht => (S.ode_mom t (hsub ht)).mono hsub) hbnd

/-- The convenient endpoint form on the right half. -/
theorem free_right_of_endpoints (S : GateSolution ε c Tmax u pu) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (h1 : u a ∈ Ioo (2 * ε) 1) (h2 : u a + pu a * (b - a) ∈ Ioo (2 * ε) 1) :
    ∀ t ∈ Icc a b, u t = u a + pu a * (t - a) ∧ pu t = pu a := by
  refine S.free_right ha hb hab ?_
  intro t ht
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  rcases le_or_gt 0 (pu a) with hs | hs
  · exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  · exact ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩

/-- The convenient endpoint form on the left half. -/
theorem free_left_of_endpoints (S : GateSolution ε c Tmax u pu) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (h1 : u a ∈ Ioo (-1 : ℝ) (-(2 * ε))) (h2 : u a + pu a * (b - a) ∈ Ioo (-1 : ℝ) (-(2 * ε))) :
    ∀ t ∈ Icc a b, u t = u a + pu a * (t - a) ∧ pu t = pu a := by
  refine S.free_left ha hb hab ?_
  intro t ht
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  rcases le_or_gt 0 (pu a) with hs | hs
  · exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  · exact ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩

/-! #### Reflection at the outer caps -/

/-- Near a cap the gate is inactive, so the gated potential is the ungated one. -/
theorem deriv_gatePot_cap_right (hε : 0 < ε) {v : ℝ} (h₁ : 2 * ε ≤ v) (h₂ : -1 ≤ v) :
    deriv (gatePot ε) v = deriv (wallPot ε) (v - 1) := by
  rw [deriv_gatePot, deriv_gateBump_of_two_le hε h₁, deriv_capPot_right hε h₂, add_zero]

theorem deriv_gatePot_cap_left (hε : 0 < ε) {v : ℝ} (h₁ : v ≤ -(2 * ε)) (h₂ : v ≤ 1) :
    deriv (gatePot ε) v = -deriv (wallPot ε) (-v - 1) := by
  rw [deriv_gatePot, deriv_gateBump_of_le_neg hε h₁, deriv_capPot_left hε h₂, add_zero]

/-- **Exact reflection at the right cap.** -/
theorem reflect_cap_right (S : GateSolution ε c Tmax u pu) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + 23 * ε ≤ Tmax)
    (hua : u a = 1 - 8 * ε) (hpa : pu a = c) :
    ∃ t₁ ∈ Ioo a (a + 23 * ε), u t₁ = 1 - 8 * ε ∧ pu t₁ = -c := by
  have hε := S.eps_pos
  have hεs := S.eps_small
  have hc0 := S.c_pos
  have hτpos : 0 < barrierTime ε c (8 * ε) := barrierTime_pos hε S.c_ge (by linarith)
  have hτle : barrierTime ε c (8 * ε) < 23 * ε := capTime_lt hε S.c_ge
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + barrierTime ε c (8 * ε) ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, by linarith⟩
  have hsub : Icc a (a + barrierTime ε c (8 * ε)) ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha hbmem.2
  have hnear : ∀ t ∈ Icc a (a + barrierTime ε c (8 * ε)), 2 * ε ≤ u t := by
    intro t ht
    have h1 := abs_le.mp (S.travel_le hamem (hsub ht) ht.1)
    have h2 : c * (t - a) ≤ 2 * (23 * ε) := by
      have : t - a ≤ 23 * ε := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    linarith [h1.1]
  have hsetup : Reflection.SharpSetup (wallPot ε) (ε / 4) ε 4 (4 / (exp 3 * ε)) (c ^ 2 / 2)
      (8 * ε) a (a + barrierTime ε c (8 * ε)) (fun t => u t - 1) pu :=
    { contDiff := contDiff_wallPot ε
      nonneg := wallPot_nonneg ε
      flat := fun _ hy => wallPot_of_nonpos hε hy
      mono := fun y => deriv_wallPot_nonneg hε y
      high := fun _ hy => wallPot_ge_of_le hε hy
      slope := fun _ hy => deriv_wallPot_ge hε hy.1 hy.2
      low := fun y hy => by
        have h := wallPot_le_quarter hε hy
        nlinarith [S.c_ge]
      δ_pos := by linarith
      δ_lt := by linarith
      k_pos := by positivity
      E_pos := by nlinarith [S.c_ge]
      E_lt := by nlinarith [S.c_le]
      d_nonneg := by linarith
      hx := fun t ht =>
        ((hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht).sub_const 1
      hp := fun t ht => by
        have h := (hasDerivWithinAt_sub_interval S.ode_mom hamem hbmem) t ht
        rwa [deriv_gatePot_cap_right hε (hnear t ht) (by linarith [hnear t ht])] at h
      init_x := by rw [hua]; ring
      init_p := by
        rw [hpa, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier_sharp hsetup
  have ht₁2 : t₁ ≤ a + barrierTime ε c (8 * ε) := ht₁.2
  refine ⟨t₁, ⟨ht₁.1, by linarith⟩, by linarith [hx₁], ?_⟩
  rw [hp₁, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]

/-- **Exact reflection at the left cap.** -/
theorem reflect_cap_left (S : GateSolution ε c Tmax u pu) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + 23 * ε ≤ Tmax)
    (hua : u a = -(1 - 8 * ε)) (hpa : pu a = -c) :
    ∃ t₁ ∈ Ioo a (a + 23 * ε), u t₁ = -(1 - 8 * ε) ∧ pu t₁ = c := by
  have hε := S.eps_pos
  have hεs := S.eps_small
  have hc0 := S.c_pos
  have hτpos : 0 < barrierTime ε c (8 * ε) := barrierTime_pos hε S.c_ge (by linarith)
  have hτle : barrierTime ε c (8 * ε) < 23 * ε := capTime_lt hε S.c_ge
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + barrierTime ε c (8 * ε) ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, by linarith⟩
  have hsub : Icc a (a + barrierTime ε c (8 * ε)) ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha hbmem.2
  have hnear : ∀ t ∈ Icc a (a + barrierTime ε c (8 * ε)), u t ≤ -(2 * ε) := by
    intro t ht
    have h1 := abs_le.mp (S.travel_le hamem (hsub ht) ht.1)
    have h2 : c * (t - a) ≤ 2 * (23 * ε) := by
      have : t - a ≤ 23 * ε := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    linarith [h1.2]
  have hsetup : Reflection.SharpSetup (wallPot ε) (ε / 4) ε 4 (4 / (exp 3 * ε)) (c ^ 2 / 2)
      (8 * ε) a (a + barrierTime ε c (8 * ε)) (fun t => -u t - 1) (fun t => -pu t) :=
    { contDiff := contDiff_wallPot ε
      nonneg := wallPot_nonneg ε
      flat := fun _ hy => wallPot_of_nonpos hε hy
      mono := fun y => deriv_wallPot_nonneg hε y
      high := fun _ hy => wallPot_ge_of_le hε hy
      slope := fun _ hy => deriv_wallPot_ge hε hy.1 hy.2
      low := fun y hy => by
        have h := wallPot_le_quarter hε hy
        nlinarith [S.c_ge]
      δ_pos := by linarith
      δ_lt := by linarith
      k_pos := by positivity
      E_pos := by nlinarith [S.c_ge]
      E_lt := by nlinarith [S.c_le]
      d_nonneg := by linarith
      hx := fun t ht =>
        (((hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht).neg).sub_const 1
      hp := fun t ht => by
        have h := ((hasDerivWithinAt_sub_interval S.ode_mom hamem hbmem) t ht).neg
        rw [neg_neg, deriv_gatePot_cap_left hε (hnear t ht) (by linarith [hnear t ht])] at h
        exact h
      init_x := by rw [hua]; ring
      init_p := by
        rw [hpa, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]; ring
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier_sharp hsetup
  have ht₁2 : t₁ ≤ a + barrierTime ε c (8 * ε) := ht₁.2
  have hx₁' : -u t₁ - 1 = -(8 * ε) := hx₁
  have hp₁' : -pu t₁ = -Real.sqrt (2 * (c ^ 2 / 2)) := hp₁
  rw [show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le] at hp₁'
  exact ⟨t₁, ⟨ht₁.1, by linarith⟩, by linarith, by linarith⟩

/-! #### Reflection at the gate: the low-energy regime -/

/-- The barrier of the left flank of the gate. -/
noncomputable def gateWall (ε y : ℝ) : ℝ := gateHeight / 4 * wallPot ε y

theorem contDiff_gateWall (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (gateWall ε) :=
  contDiff_const.mul (contDiff_wallPot ε)

theorem deriv_gateWall (ε y : ℝ) :
    deriv (gateWall ε) y = gateHeight / 4 * deriv (wallPot ε) y := by
  have hw : DifferentiableAt ℝ (wallPot ε) y :=
    (contDiff_wallPot ε (n := 1)).differentiable (by norm_num) y
  have h : HasDerivAt (gateWall ε) (gateHeight / 4 * deriv (wallPot ε) y) y :=
    hw.hasDerivAt.const_mul (gateHeight / 4)
  exact h.deriv

theorem gateWall_nonneg (ε : ℝ) : ∀ y : ℝ, 0 ≤ gateWall ε y := by
  intro y
  have := wallPot_nonneg ε y
  have := gateHeight_pos
  rw [gateWall]
  positivity

/-- **The gate confines a low-energy particle to one side.**  Its longitudinal energy is below
the gate height, and the gate is at least that high across the whole core `|u| ≤ ε`. -/
theorem abs_gt_of_low (S : GateSolution ε c Tmax u pu) (hlow : c ^ 2 / 2 < gateHeight)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Tmax) : ε < |u t| := by
  by_contra hcon
  rw [not_lt] at hcon
  have h1 := S.energy t ht
  have h2 := gateBump_ge S.eps_pos hcon
  have h3 : gateBump ε (u t) ≤ gatePot ε (u t) := by
    have := capPot_nonneg ε (u t)
    rw [gatePot]; linarith
  have h4 : (0 : ℝ) ≤ pu t ^ 2 / 2 := by positivity
  linarith

/-- **Exact reflection at the gate, entered from the left.**  This is the low-energy routing
`η ↦ η`: the particle arrives at the junction boundary `u = -8ε` of the first through edge and
returns to it with exactly reversed momentum, having never crossed the junction. -/
theorem reflect_gate_left (S : GateSolution ε c Tmax u pu) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + 26 * ε ≤ Tmax) (hlow : c ^ 2 / 2 < gateHeight)
    (hua : u a = -(8 * ε)) (hpa : pu a = c) :
    ∃ t₁ ∈ Ioo a (a + 26 * ε), u t₁ = -(8 * ε) ∧ pu t₁ = -c := by
  have hε := S.eps_pos
  have hεs := S.eps_small
  have hc0 := S.c_pos
  have hh : gateHeight = 7 / 10 := rfl
  have hτpos : 0 < gateTime ε c := gateTime_pos hε S.c_ge
  have hτle : gateTime ε c < 26 * ε := gateTime_lt hε S.c_ge
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + gateTime ε c ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, by linarith⟩
  have hsub : Icc a (a + gateTime ε c) ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha hbmem.2
  -- the particle never leaves the left half of the junction, and never reaches the caps
  have htravel : ∀ t ∈ Icc a (a + gateTime ε c), |u t - u a| ≤ 52 * ε := by
    intro t ht
    have h1 := S.travel_le hamem (hsub ht) ht.1
    have h2 : c * (t - a) ≤ 2 * (26 * ε) := by
      have : t - a ≤ 26 * ε := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    linarith
  have hfar : ∀ t ∈ Icc a (a + gateTime ε c), -1 ≤ u t ∧ u t ≤ 1 := by
    intro t ht
    have h := abs_le.mp (htravel t ht)
    rw [hua] at h
    constructor <;> linarith
  have hnear : ∀ t ∈ Icc a (a + gateTime ε c), u t < -ε := by
    intro t ht
    by_contra hcon
    rw [not_lt] at hcon
    have hcontu : ContinuousOn u (Icc a t) :=
      (S.continuousOn_pos).mono ((Icc_subset_Icc le_rfl ht.2).trans hsub)
    have hstart : u a < -ε := by rw [hua]; linarith
    obtain ⟨s, hs, hval⟩ := intermediate_value_Icc ht.1 hcontu
      (show -ε ∈ Icc (u a) (u t) from ⟨hstart.le, hcon⟩)
    have hsmem : s ∈ Icc (0 : ℝ) Tmax := hsub ⟨hs.1, hs.2.trans ht.2⟩
    have := S.abs_gt_of_low hlow hsmem
    have hval' : u s = -ε := hval
    rw [hval', abs_neg, abs_of_pos hε] at this
    exact lt_irrefl _ this
  have hsetup : Reflection.SharpSetup (gateWall ε) (ε / 4) ε gateHeight
      (gateHeight / (exp 3 * ε)) (c ^ 2 / 2) (6 * ε)
      a (a + gateTime ε c) (fun t => u t + 2 * ε) pu :=
    { contDiff := contDiff_gateWall ε
      nonneg := gateWall_nonneg ε
      flat := fun _ hy => by rw [gateWall, wallPot_of_nonpos hε hy, mul_zero]
      mono := fun y => by
        rw [deriv_gateWall]
        have := deriv_wallPot_nonneg hε y
        have := gateHeight_pos
        positivity
      high := fun _ hy => by
        have := wallPot_ge_of_le hε hy
        rw [gateWall, hh]
        linarith
      slope := fun y hy => by
        have := deriv_wallPot_ge hε hy.1 hy.2
        rw [deriv_gateWall, hh]
        have hpos : (0 : ℝ) < exp 3 * ε := by positivity
        rw [div_le_iff₀ hpos] at this ⊢
        nlinarith
      low := fun y hy => by
        have h := wallPot_le_quarter hε hy
        have := wallPot_nonneg ε y
        rw [gateWall, hh]
        nlinarith [S.c_ge]
      δ_pos := by linarith
      δ_lt := by linarith
      k_pos := by rw [hh]; positivity
      E_pos := by nlinarith [S.c_ge]
      E_lt := hlow
      d_nonneg := by linarith
      hx := fun t ht =>
        ((hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht).add_const (2 * ε)
      hp := fun t ht => by
        have h := (hasDerivWithinAt_sub_interval S.ode_mom hamem hbmem) t ht
        rw [deriv_gatePot_of_lt hε (hnear t ht) (hfar t ht).1] at h
        rw [deriv_gateWall]
        exact h
      init_x := by rw [hua]; ring
      init_p := by
        rw [hpa, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier_sharp hsetup
  have ht₁2 : t₁ ≤ a + gateTime ε c := ht₁.2
  have hx₁' : u t₁ + 2 * ε = -(6 * ε) := hx₁
  refine ⟨t₁, ⟨ht₁.1, by linarith⟩, by linarith, ?_⟩
  rw [hp₁, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]

/-- **Exact reflection at the gate, entered from the right**, by the mirror symmetry of the
gate. -/
theorem reflect_gate_right (S : GateSolution ε c Tmax u pu) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + 26 * ε ≤ Tmax) (hlow : c ^ 2 / 2 < gateHeight)
    (hua : u a = 8 * ε) (hpa : pu a = -c) :
    ∃ t₁ ∈ Ioo a (a + 26 * ε), u t₁ = 8 * ε ∧ pu t₁ = c := by
  have hε := S.eps_pos
  have hεs := S.eps_small
  have hc0 := S.c_pos
  have hh : gateHeight = 7 / 10 := rfl
  have hτpos : 0 < gateTime ε c := gateTime_pos hε S.c_ge
  have hτle : gateTime ε c < 26 * ε := gateTime_lt hε S.c_ge
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + gateTime ε c ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, by linarith⟩
  have hsub : Icc a (a + gateTime ε c) ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha hbmem.2
  have htravel : ∀ t ∈ Icc a (a + gateTime ε c), |u t - u a| ≤ 52 * ε := by
    intro t ht
    have h1 := S.travel_le hamem (hsub ht) ht.1
    have h2 : c * (t - a) ≤ 2 * (26 * ε) := by
      have : t - a ≤ 26 * ε := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    linarith
  have hfar : ∀ t ∈ Icc a (a + gateTime ε c), -1 ≤ u t ∧ u t ≤ 1 := by
    intro t ht
    have h := abs_le.mp (htravel t ht)
    rw [hua] at h
    constructor <;> linarith
  have hnear : ∀ t ∈ Icc a (a + gateTime ε c), ε < u t := by
    intro t ht
    by_contra hcon
    rw [not_lt] at hcon
    have hcontu : ContinuousOn u (Icc a t) :=
      (S.continuousOn_pos).mono ((Icc_subset_Icc le_rfl ht.2).trans hsub)
    have hstart : ε < u a := by rw [hua]; linarith
    obtain ⟨s, hs, hval⟩ := intermediate_value_Icc' ht.1 hcontu
      (show ε ∈ Icc (u t) (u a) from ⟨hcon, hstart.le⟩)
    have hsmem : s ∈ Icc (0 : ℝ) Tmax := hsub ⟨hs.1, hs.2.trans ht.2⟩
    have := S.abs_gt_of_low hlow hsmem
    have hval' : u s = ε := hval
    rw [hval', abs_of_pos hε] at this
    exact lt_irrefl _ this
  have hsetup : Reflection.SharpSetup (gateWall ε) (ε / 4) ε gateHeight
      (gateHeight / (exp 3 * ε)) (c ^ 2 / 2) (6 * ε)
      a (a + gateTime ε c) (fun t => 2 * ε - u t) (fun t => -pu t) :=
    { contDiff := contDiff_gateWall ε
      nonneg := gateWall_nonneg ε
      flat := fun _ hy => by rw [gateWall, wallPot_of_nonpos hε hy, mul_zero]
      mono := fun y => by
        rw [deriv_gateWall]
        have := deriv_wallPot_nonneg hε y
        have := gateHeight_pos
        positivity
      high := fun _ hy => by
        have := wallPot_ge_of_le hε hy
        rw [gateWall, hh]
        linarith
      slope := fun y hy => by
        have := deriv_wallPot_ge hε hy.1 hy.2
        rw [deriv_gateWall, hh]
        have hpos : (0 : ℝ) < exp 3 * ε := by positivity
        rw [div_le_iff₀ hpos] at this ⊢
        nlinarith
      low := fun y hy => by
        have h := wallPot_le_quarter hε hy
        have := wallPot_nonneg ε y
        rw [gateWall, hh]
        nlinarith [S.c_ge]
      δ_pos := by linarith
      δ_lt := by linarith
      k_pos := by rw [hh]; positivity
      E_pos := by nlinarith [S.c_ge]
      E_lt := hlow
      d_nonneg := by linarith
      hx := fun t ht => by
        have h := (hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht
        simpa using h.const_sub (2 * ε)
      hp := fun t ht => by
        have h := ((hasDerivWithinAt_sub_interval S.ode_mom hamem hbmem) t ht).neg
        rw [neg_neg, deriv_gatePot_of_gt hε (hnear t ht) (hfar t ht).2] at h
        rw [deriv_gateWall]
        exact h
      init_x := by rw [hua]; ring
      init_p := by
        rw [hpa, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]; ring
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier_sharp hsetup
  have ht₁2 : t₁ ≤ a + gateTime ε c := ht₁.2
  have hx₁' : 2 * ε - u t₁ = -(6 * ε) := hx₁
  have hp₁' : -pu t₁ = -Real.sqrt (2 * (c ^ 2 / 2)) := hp₁
  rw [show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le] at hp₁'
  exact ⟨t₁, ⟨ht₁.1, by linarith⟩, by linarith, by linarith⟩

/-! #### Crossing the gate: the high-energy regime -/

/-- **The gate is crossed freely above its height.**  For a longitudinal energy at least `3/2`,
which exceeds the bound `g₀e^{2/3} < 1.365` of the gate, `E - G_ε > 1/8`, so the particle keeps a
speed above `1/2` throughout the junction, crosses `[-8ε, 8ε]` in a time `b < 32ε`, and emerges
on the other side with *exactly* its incoming speed (proof of Theorem IX.10). -/
theorem cross_gate_right (S : GateSolution ε c Tmax u pu) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + 32 * ε ≤ Tmax) (hhigh : 3 / 2 ≤ c ^ 2 / 2)
    (hua : u a = -(8 * ε)) (hpa : pu a = c) :
    ∃ t₁ ∈ Ioo a (a + 32 * ε), u t₁ = 8 * ε ∧ pu t₁ = c := by
  have hε := S.eps_pos
  have hεs := S.eps_small
  have hc0 := S.c_pos
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + 32 * ε ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, hb⟩
  have hsub : Icc a (a + 32 * ε) ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha hb
  -- the particle stays well inside the closed edge
  have hbound : ∀ t ∈ Icc a (a + 32 * ε), |u t| ≤ 1 := by
    intro t ht
    have h1 := abs_le.mp (S.travel_le hamem (hsub ht) ht.1)
    have h2 : c * (t - a) ≤ 2 * (32 * ε) := by
      have : t - a ≤ 32 * ε := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    rw [hua] at h1
    rw [abs_le]
    constructor <;> linarith
  -- the speed never drops below `0.51 > 1/2`
  have hpsq : ∀ t ∈ Icc a (a + 32 * ε), (2601 : ℝ) / 10000 ≤ pu t ^ 2 := by
    intro t ht
    have hen := S.energy t (hsub ht)
    have hcap : capPot ε (u t) = 0 := capPot_of_abs_le_one hε (hbound t ht)
    have hg := gateBump_lt hε (u t)
    rw [gatePot, hcap, zero_add] at hen
    linarith
  have hppos : ∀ t ∈ Icc a (a + 32 * ε), (51 : ℝ) / 100 ≤ pu t := by
    intro t ht
    by_contra hcon
    rw [not_le] at hcon
    have hsq := hpsq t ht
    have hneg : pu t < 0 := by nlinarith
    have hcontp : ContinuousOn pu (Icc a t) :=
      (S.continuousOn_mom).mono ((Icc_subset_Icc le_rfl ht.2).trans hsub)
    have hstart : (0 : ℝ) < pu a := by rw [hpa]; exact hc0
    obtain ⟨s, hs, hval⟩ := intermediate_value_Icc' ht.1 hcontp
      (show (0 : ℝ) ∈ Icc (pu t) (pu a) from ⟨hneg.le, hstart.le⟩)
    have hval' : pu s = 0 := hval
    have := hpsq s ⟨hs.1, hs.2.trans ht.2⟩
    rw [hval'] at this
    norm_num at this
  -- hence it travels more than `16ε` within `32ε`
  have hfar : 8 * ε < u (a + 32 * ε) := by
    have h := mul_sub_le_image_sub_of_le_hasDerivWithinAt' (f := u) (f' := pu) (C := 51 / 100)
      (fun t ht => (hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht)
      hppos (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith)) (by linarith)
    rw [hua] at h
    linarith
  -- and therefore reaches the far junction boundary
  have hcontu : ContinuousOn u (Icc a (a + 32 * ε)) := (S.continuousOn_pos).mono hsub
  obtain ⟨t₁, ht₁, hval⟩ := intermediate_value_Icc (by linarith : a ≤ a + 32 * ε) hcontu
    (show 8 * ε ∈ Icc (u a) (u (a + 32 * ε)) from ⟨by rw [hua]; linarith, hfar.le⟩)
  have hval' : u t₁ = 8 * ε := hval
  have hlt : a < t₁ := by
    rcases eq_or_lt_of_le ht₁.1 with heq | hlt
    · exfalso
      rw [← heq, hua] at hval'
      linarith
    · exact hlt
  have hlt₂ : t₁ < a + 32 * ε := by
    rcases eq_or_lt_of_le ht₁.2 with heq | hlt
    · exfalso
      rw [heq] at hval'
      linarith
    · exact hlt
  refine ⟨t₁, ⟨hlt, hlt₂⟩, hval', ?_⟩
  have hen := S.energy t₁ (hsub ht₁)
  have hz : gatePot ε (u t₁) = 0 := by
    rw [hval']
    exact gatePot_of_mem hε (by rw [abs_of_nonneg (by linarith)]; linarith)
      (by rw [abs_of_nonneg (by linarith)]; linarith)
  rw [hz, add_zero] at hen
  have hp := hppos t₁ ht₁
  nlinarith

/-- **The gate is crossed freely above its height, from the right.** -/
theorem cross_gate_left (S : GateSolution ε c Tmax u pu) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + 32 * ε ≤ Tmax) (hhigh : 3 / 2 ≤ c ^ 2 / 2)
    (hua : u a = 8 * ε) (hpa : pu a = -c) :
    ∃ t₁ ∈ Ioo a (a + 32 * ε), u t₁ = -(8 * ε) ∧ pu t₁ = -c := by
  have hε := S.eps_pos
  have hεs := S.eps_small
  have hc0 := S.c_pos
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + 32 * ε ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, hb⟩
  have hsub : Icc a (a + 32 * ε) ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha hb
  have hbound : ∀ t ∈ Icc a (a + 32 * ε), |u t| ≤ 1 := by
    intro t ht
    have h1 := abs_le.mp (S.travel_le hamem (hsub ht) ht.1)
    have h2 : c * (t - a) ≤ 2 * (32 * ε) := by
      have : t - a ≤ 32 * ε := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    rw [hua] at h1
    rw [abs_le]
    constructor <;> linarith
  have hpsq : ∀ t ∈ Icc a (a + 32 * ε), (2601 : ℝ) / 10000 ≤ pu t ^ 2 := by
    intro t ht
    have hen := S.energy t (hsub ht)
    have hcap : capPot ε (u t) = 0 := capPot_of_abs_le_one hε (hbound t ht)
    have hg := gateBump_lt hε (u t)
    rw [gatePot, hcap, zero_add] at hen
    linarith
  have hpneg : ∀ t ∈ Icc a (a + 32 * ε), pu t ≤ -(51 / 100) := by
    intro t ht
    by_contra hcon
    rw [not_le] at hcon
    have hsq := hpsq t ht
    have hpos : (0 : ℝ) < pu t := by nlinarith
    have hcontp : ContinuousOn pu (Icc a t) :=
      (S.continuousOn_mom).mono ((Icc_subset_Icc le_rfl ht.2).trans hsub)
    have hstart : pu a < 0 := by rw [hpa]; linarith
    obtain ⟨s, hs, hval⟩ := intermediate_value_Icc ht.1 hcontp
      (show (0 : ℝ) ∈ Icc (pu a) (pu t) from ⟨hstart.le, hpos.le⟩)
    have hval' : pu s = 0 := hval
    have := hpsq s ⟨hs.1, hs.2.trans ht.2⟩
    rw [hval'] at this
    norm_num at this
  have hfar : u (a + 32 * ε) < -(8 * ε) := by
    have h := image_sub_le_mul_sub_of_hasDerivWithinAt_le' (f := u) (f' := pu) (C := -(51 / 100))
      (fun t ht => (hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht)
      hpneg (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith)) (by linarith)
    rw [hua] at h
    linarith
  have hcontu : ContinuousOn u (Icc a (a + 32 * ε)) := (S.continuousOn_pos).mono hsub
  obtain ⟨t₁, ht₁, hval⟩ := intermediate_value_Icc' (by linarith : a ≤ a + 32 * ε) hcontu
    (show -(8 * ε) ∈ Icc (u (a + 32 * ε)) (u a) from ⟨hfar.le, by rw [hua]; linarith⟩)
  have hval' : u t₁ = -(8 * ε) := hval
  have hlt : a < t₁ := by
    rcases eq_or_lt_of_le ht₁.1 with heq | hlt
    · exfalso
      rw [← heq, hua] at hval'
      linarith
    · exact hlt
  have hlt₂ : t₁ < a + 32 * ε := by
    rcases eq_or_lt_of_le ht₁.2 with heq | hlt
    · exfalso
      rw [heq] at hval'
      linarith
    · exact hlt
  refine ⟨t₁, ⟨hlt, hlt₂⟩, hval', ?_⟩
  have hen := S.energy t₁ (hsub ht₁)
  have hz : gatePot ε (u t₁) = 0 := by
    rw [hval']
    exact gatePot_of_mem hε (by rw [abs_of_nonpos (by linarith)]; linarith)
      (by rw [abs_of_nonpos (by linarith)]; linarith)
  rw [hz, add_zero] at hen
  have hp := hpneg t₁ ht₁
  nlinarith

end GateSolution

end HamiltonianMetricGraphs
