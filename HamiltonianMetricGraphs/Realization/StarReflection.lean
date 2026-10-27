/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ArmDynamics

/-!
# The sharp reflection time at a barrier (Lemma IX.8)

`Reflection.lean` proves that a monotone barrier reverses the momentum exactly, within the crude
time `reflectionTime δ k E d = 2(d + δ)/√E + 3√(2E)/k`.  That bound is enough for `dwell = O(ε)`,
but its constants are far from those of the paper.  This file proves the **sharp** bound of
Lemma IX.8 of the paper,

  `t_* ≤ 2d/c + 2δ/√E + 2 · 2√(L - δ)/√(2k)`,   `c = √(2E)`,

which for the scaled barrier `B(y/ε)` (`δ = ε/4`, `L = ε`, `k = 4/(e³ε)`) is the paper's
`t_* ≤ 2d/c + 2ε(1/(4√E) + √(3/(2k)))`, and the numerical consequence `eq:cap-time`,

  `t_* < 2d/c + 7ε`   for `E ∈ [1/2, 2]`.

The paper obtains the turning time from the integral `∫ dy/√(2(E - P(y)))` and the time-reversal
symmetry of the equation.  Here the same estimate is obtained without either: below the turning
point `y_*` (where `Φ(y_*) = E`) the slope bound gives `E - Φ(y) ≥ k(y_* - y)`, hence
`|ẏ| ≥ √(2k) · √(y_* - y)`, so `√(y_* - y(t))` decreases at rate at least `√(2k)/2` while the
particle climbs, and increases at that rate while it descends.  Each of the two passages through
`[δ, y_*]` therefore takes at most `2√(y_* - δ)/√(2k) ≤ 2√(L - δ)/√(2k)`, exactly the paper's
`ε√(3/(2k))` for the scaled barrier.  On `[-d, 0]` the potential vanishes and the speed is exactly
`c`; on `[0, δ]` it is at least `√E`.

## Main results

* `Reflection.reflect_of_barrier_sharp` — Lemma IX.8 with the sharp time `sharpTime`;
* `barrierTime_lt` — the paper's `eq:cap-time`: for the scaled barrier `B` and `c ∈ [1, 2]`,
  `t_* < 2d/c + 7ε`.
-/

namespace HamiltonianMetricGraphs

open Set Real

namespace Reflection

/-- **The sharp reflection time of Lemma IX.8**: `2d/c` for crossing the flat region `[-d, 0]`
twice at the speed `c = √(2E)`, `2δ/√E` for crossing the foot `[0, δ]` twice at speed at least
`√E`, and twice the climbing time `2√(L - δ)/√(2k)` through the region of slope at least `k`. -/
noncomputable def sharpTime (δ L k E d : ℝ) : ℝ :=
  2 * d / Real.sqrt (2 * E) + 2 * δ / Real.sqrt E
    + 2 * (2 * Real.sqrt (L - δ) / Real.sqrt (2 * k))

/-- `sharpTime` split into the durations of the six passages. -/
theorem sharpTime_eq (δ L k E d : ℝ) : sharpTime δ L k E d =
    d / Real.sqrt (2 * E) + δ / Real.sqrt E + 2 * Real.sqrt (L - δ) / Real.sqrt (2 * k)
      + 2 * Real.sqrt (L - δ) / Real.sqrt (2 * k) + δ / Real.sqrt E
      + d / Real.sqrt (2 * E) := by
  unfold sharpTime
  ring

/-- The hypotheses of Lemma IX.8: a monotone barrier, flat on `(-∞, 0]`, below `E/2` on
`(-∞, δ]`, of slope at least `k` on `[δ, L]` and above `E` beyond `L`, together with a trajectory
entering it from `-d ≤ 0` with momentum `√(2E)`, followed for the time `sharpTime`. -/
structure SharpSetup (Φ : ℝ → ℝ) (δ L B k E d a b : ℝ) (x p : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 Φ
  nonneg : ∀ y, 0 ≤ Φ y
  flat : ∀ y ≤ (0 : ℝ), Φ y = 0
  mono : ∀ y, 0 ≤ deriv Φ y
  high : ∀ y, L ≤ y → B ≤ Φ y
  slope : ∀ y ∈ Icc δ L, k ≤ deriv Φ y
  low : ∀ y ≤ δ, Φ y ≤ E / 2
  δ_pos : 0 < δ
  δ_lt : δ < L
  k_pos : 0 < k
  E_pos : 0 < E
  E_lt : E < B
  d_nonneg : 0 ≤ d
  hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (p t) (Icc a b) t
  hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (-deriv Φ (x t)) (Icc a b) t
  init_x : x a = -d
  init_p : p a = Real.sqrt (2 * E)
  long : a + sharpTime δ L k E d ≤ b

/-! ### Two estimates for the distance to the turning point -/

/-- **Climbing.**  While the particle moves forward below the turning point `ys` with
`p² ≥ 2k(ys - x)`, the quantity `√(ys - x)` decreases at rate at least `√(2k)/2`. -/
theorem sqrt_gap_climb {x p : ℝ → ℝ} {s t ys k : ℝ} (hst : s < t)
    (hcont : ContinuousOn x (Icc s t)) (hx : ∀ u ∈ Ioo s t, HasDerivAt x (p u) u)
    (hlt : ∀ u ∈ Ioo s t, x u < ys) (hpos : ∀ u ∈ Ioo s t, 0 ≤ p u)
    (hsq : ∀ u ∈ Ioo s t, 2 * k * (ys - x u) ≤ p u ^ 2) (hk : 0 ≤ k) :
    Real.sqrt (ys - x t) - Real.sqrt (ys - x s) ≤ -(Real.sqrt (2 * k) / 2) * (t - s) := by
  have hgc : ContinuousOn (fun u => Real.sqrt (ys - x u)) (Icc s t) :=
    (continuousOn_const.sub hcont).sqrt
  have hder : ∀ u ∈ Ioo s t, HasDerivAt (fun u => Real.sqrt (ys - x u))
      ((0 - p u) / (2 * Real.sqrt (ys - x u))) u := fun u hu =>
    ((hasDerivAt_const u ys).sub (hx u hu)).sqrt (ne_of_gt (sub_pos.mpr (hlt u hu)))
  obtain ⟨w, hw, hval⟩ := exists_hasDerivAt_eq_slope (fun u => Real.sqrt (ys - x u))
    (fun u => (0 - p u) / (2 * Real.sqrt (ys - x u))) hst hgc hder
  have hr : 0 < Real.sqrt (ys - x w) := Real.sqrt_pos.mpr (sub_pos.mpr (hlt w hw))
  have hk2 : 0 ≤ Real.sqrt (2 * k) := Real.sqrt_nonneg _
  -- the speed is at least `√(2k) · √(ys - x)`
  have hspeed : Real.sqrt (2 * k) * Real.sqrt (ys - x w) ≤ p w := by
    have h1 : (Real.sqrt (2 * k) * Real.sqrt (ys - x w)) ^ 2 ≤ p w ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (sub_pos.mpr (hlt w hw)).le]
      exact hsq w hw
    nlinarith [mul_nonneg hk2 hr.le, hpos w hw,
      sq_nonneg (Real.sqrt (2 * k) * Real.sqrt (ys - x w) - p w)]
  have hslope : (0 - p w) / (2 * Real.sqrt (ys - x w)) ≤ -(Real.sqrt (2 * k) / 2) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [hval, div_le_iff₀ (sub_pos.mpr hst)] at hslope
  linarith

/-- **Descending.**  While the particle moves backward below the turning point `ys` with
`p² ≥ 2k(ys - x)`, the quantity `√(ys - x)` increases at rate at least `√(2k)/2`. -/
theorem sqrt_gap_descend {x p : ℝ → ℝ} {s t ys k : ℝ} (hst : s < t)
    (hcont : ContinuousOn x (Icc s t)) (hx : ∀ u ∈ Ioo s t, HasDerivAt x (p u) u)
    (hlt : ∀ u ∈ Ioo s t, x u < ys) (hneg : ∀ u ∈ Ioo s t, p u ≤ 0)
    (hsq : ∀ u ∈ Ioo s t, 2 * k * (ys - x u) ≤ p u ^ 2) (hk : 0 ≤ k) :
    Real.sqrt (2 * k) / 2 * (t - s) ≤ Real.sqrt (ys - x t) - Real.sqrt (ys - x s) := by
  have hgc : ContinuousOn (fun u => Real.sqrt (ys - x u)) (Icc s t) :=
    (continuousOn_const.sub hcont).sqrt
  have hder : ∀ u ∈ Ioo s t, HasDerivAt (fun u => Real.sqrt (ys - x u))
      ((0 - p u) / (2 * Real.sqrt (ys - x u))) u := fun u hu =>
    ((hasDerivAt_const u ys).sub (hx u hu)).sqrt (ne_of_gt (sub_pos.mpr (hlt u hu)))
  obtain ⟨w, hw, hval⟩ := exists_hasDerivAt_eq_slope (fun u => Real.sqrt (ys - x u))
    (fun u => (0 - p u) / (2 * Real.sqrt (ys - x u))) hst hgc hder
  have hr : 0 < Real.sqrt (ys - x w) := Real.sqrt_pos.mpr (sub_pos.mpr (hlt w hw))
  have hk2 : 0 ≤ Real.sqrt (2 * k) := Real.sqrt_nonneg _
  have hspeed : Real.sqrt (2 * k) * Real.sqrt (ys - x w) ≤ -p w := by
    have h1 : (Real.sqrt (2 * k) * Real.sqrt (ys - x w)) ^ 2 ≤ (-p w) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (sub_pos.mpr (hlt w hw)).le, neg_sq]
      exact hsq w hw
    have h2 : 0 ≤ -p w := by linarith [hneg w hw]
    nlinarith [mul_nonneg hk2 hr.le,
      sq_nonneg (Real.sqrt (2 * k) * Real.sqrt (ys - x w) - -p w)]
  have hslope : Real.sqrt (2 * k) / 2 ≤ (0 - p w) / (2 * Real.sqrt (ys - x w)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [hval, le_div_iff₀ (sub_pos.mpr hst)] at hslope
  linarith

namespace SharpSetup

variable {Φ : ℝ → ℝ} {δ L B k E d a b : ℝ} {x p : ℝ → ℝ}
variable (S : SharpSetup Φ δ L B k E d a b x p)
include S

/-! ### Elementary consequences of the hypotheses -/

theorem sqrtE_pos : 0 < Real.sqrt E := Real.sqrt_pos.mpr S.E_pos

theorem sqrt2E_pos : 0 < Real.sqrt (2 * E) := Real.sqrt_pos.mpr (by linarith [S.E_pos])

theorem sq_sqrt2E : Real.sqrt (2 * E) ^ 2 = 2 * E := Real.sq_sqrt (by linarith [S.E_pos])

theorem climb_pos : 0 < 2 * Real.sqrt (L - δ) / Real.sqrt (2 * k) := by
  have h1 : 0 < Real.sqrt (L - δ) := Real.sqrt_pos.mpr (by linarith [S.δ_lt])
  have h2 : 0 < Real.sqrt (2 * k) := Real.sqrt_pos.mpr (by linarith [S.k_pos])
  positivity

theorem le_b : a ≤ b := by
  have h1 : 0 ≤ d / Real.sqrt (2 * E) := div_nonneg S.d_nonneg S.sqrt2E_pos.le
  have h2 : 0 ≤ δ / Real.sqrt E := div_nonneg S.δ_pos.le S.sqrtE_pos.le
  have h3 := S.climb_pos
  have := S.long
  rw [sharpTime_eq] at this
  linarith

theorem energy_eq : energy1D Φ (x a) (p a) = E := by
  simp only [energy1D]
  rw [S.init_x, S.init_p, S.flat (-d) (by linarith [S.d_nonneg]), S.sq_sqrt2E]
  ring

theorem sq_mom {t : ℝ} (ht : t ∈ Icc a b) : p t ^ 2 = 2 * (E - Φ (x t)) := by
  have h := sq_momentum_eq S.contDiff S.hx S.hp t ht
  rwa [S.energy_eq] at h

theorem pot_le {t : ℝ} (ht : t ∈ Icc a b) : Φ (x t) ≤ E := by
  have h := S.sq_mom ht
  nlinarith [sq_nonneg (p t)]

/-- The particle never reaches the far side `L` of the barrier. -/
theorem lt_L {t : ℝ} (ht : t ∈ Icc a b) : x t < L := by
  by_contra hcon
  rw [not_lt] at hcon
  have h1 := S.high _ hcon
  have h2 := S.pot_le ht
  linarith [S.E_lt]

/-- Near the foot of the barrier the speed is at least `√E`. -/
theorem sqrtE_le_abs_p {t : ℝ} (ht : t ∈ Icc a b) (hxt : x t ≤ δ) :
    Real.sqrt E ≤ |p t| := by
  have h := S.sq_mom ht
  have hlow := S.low _ hxt
  have hsq : E ≤ p t ^ 2 := by linarith
  calc Real.sqrt E ≤ Real.sqrt (p t ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |p t| := Real.sqrt_sq_eq_abs _

/-- On the flat side the speed is exactly `√(2E)`. -/
theorem abs_p_of_nonpos {t : ℝ} (ht : t ∈ Icc a b) (hxt : x t ≤ 0) :
    |p t| = Real.sqrt (2 * E) := by
  have h := S.sq_mom ht
  rw [S.flat _ hxt, sub_zero] at h
  rw [← Real.sqrt_sq_eq_abs, h]

theorem p_antitone {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    p t ≤ p s := by
  have h := image_sub_le_mul_sub_of_hasDerivWithinAt_le' S.hp
    (C := 0) (fun u _ => by linarith [S.mono (x u)]) hs ht hst
  linarith

theorem continuousOn_x : ContinuousOn x (Icc a b) := fun t ht => (S.hx t ht).continuousWithinAt

theorem continuousOn_p : ContinuousOn p (Icc a b) := fun t ht => (S.hp t ht).continuousWithinAt

theorem hasDerivAt_x {t : ℝ} (ht : t ∈ Ioo a b) : HasDerivAt x (p t) t :=
  hasDerivAt_of_hasDerivWithinAt_Icc ht (S.hx t (Ioo_subset_Icc_self ht))

/-- Lower bound for the displacement from a lower bound on the momentum, on a subinterval. -/
theorem x_lower {s t C : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hC : ∀ u ∈ Icc s t, C ≤ p u) : C * (t - s) ≤ x t - x s :=
  mul_sub_le_image_sub_of_le_hasDerivWithinAt hst (hasDerivWithinAt_sub_interval S.hx hs ht) hC

/-- Upper bound for the displacement from an upper bound on the momentum, on a subinterval. -/
theorem x_upper {s t C : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hC : ∀ u ∈ Icc s t, p u ≤ C) : x t - x s ≤ C * (t - s) :=
  image_sub_le_mul_sub_of_hasDerivWithinAt_le hst (hasDerivWithinAt_sub_interval S.hx hs ht) hC

/-- **Deceleration**: while the particle is in `[δ, L]` its momentum decreases at rate `≥ k`. -/
theorem p_decel {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hin : ∀ u ∈ Icc s t, δ ≤ x u) : p t - p s ≤ -k * (t - s) := by
  refine image_sub_le_mul_sub_of_hasDerivWithinAt_le hst
    (hasDerivWithinAt_sub_interval S.hp hs ht) (fun u hu => ?_)
  have hu' : u ∈ Icc a b := ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
  have := S.slope (x u) ⟨hin u hu, (S.lt_L hu').le⟩
  linarith

/-- The potential is monotone. -/
theorem monotone_Φ : Monotone Φ :=
  monotone_of_deriv_nonneg (S.contDiff.differentiable (by norm_num)) S.mono

/-- **The slope bound, integrated**: on `[δ, L]` the barrier rises at rate at least `k`. -/
theorem slope_integrated {y₁ y₂ : ℝ} (h₁ : δ ≤ y₁) (h₁₂ : y₁ ≤ y₂) (h₂ : y₂ ≤ L) :
    k * (y₂ - y₁) ≤ Φ y₂ - Φ y₁ := by
  have hd : ∀ y ∈ Icc y₁ y₂, HasDerivWithinAt Φ (deriv Φ y) (Icc y₁ y₂) y := fun y _ =>
    ((S.contDiff.differentiable (by norm_num)) y).hasDerivAt.hasDerivWithinAt
  exact mul_sub_le_image_sub_of_le_hasDerivWithinAt h₁₂ hd
    (fun y hy => S.slope y ⟨h₁.trans hy.1, hy.2.trans h₂⟩)

end SharpSetup

/-! ### The reflection theorem with the sharp time -/

set_option maxHeartbeats 1000000 in
-- four phases, each a mean-value argument
/-- **Reflection at a barrier, with the sharp time of Lemma IX.8.**  A particle entering the
barrier region from the flat side, at `-d ≤ 0` with momentum `√(2E)`, returns to `-d` with exactly
reversed momentum `-√(2E)` within the time

  `sharpTime δ L k E d = 2d/√(2E) + 2δ/√E + 2 · 2√(L - δ)/√(2k)`,

never reaches the far side `L` of the barrier, and stays strictly beyond `-d` in between. -/
theorem reflect_of_barrier_sharp {Φ : ℝ → ℝ} {δ L B k E d a b : ℝ} {x p : ℝ → ℝ}
    (S : SharpSetup Φ δ L B k E d a b x p) :
    ∃ t₁ ∈ Ioc a (a + sharpTime δ L k E d),
      x t₁ = -d ∧ p t₁ = -Real.sqrt (2 * E) ∧ (∀ t ∈ Icc a t₁, x t < L) ∧
        ∀ t ∈ Ioo a t₁, -d < x t := by
  have hlong := S.long
  rw [sharpTime_eq] at hlong ⊢
  have hc0' := S.sqrt2E_pos
  have hs0' := S.sqrtE_pos
  have hτ0' := S.climb_pos
  have hk2 : 0 < Real.sqrt (2 * k) := Real.sqrt_pos.mpr (by linarith [S.k_pos])
  have hrate' : Real.sqrt (2 * k) / 2 * (2 * Real.sqrt (L - δ) / Real.sqrt (2 * k))
      = Real.sqrt (L - δ) := by
    have := hk2.ne'
    field_simp
  obtain ⟨c, hc⟩ : ∃ c, Real.sqrt (2 * E) = c := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, Real.sqrt E = s := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, 2 * Real.sqrt (L - δ) / Real.sqrt (2 * k) = τ := ⟨_, rfl⟩
  rw [hτ, hc, hs] at hlong ⊢
  rw [hc] at hc0'
  rw [hs] at hs0'
  rw [hτ] at hτ0' hrate'
  have hc0 : 0 < c := hc0'
  have hs0 : 0 < s := hs0'
  have hτ0 : 0 < τ := hτ0'
  have hrate : Real.sqrt (2 * k) / 2 * τ = Real.sqrt (L - δ) := hrate'
  have hδ := S.δ_pos
  have hd := S.d_nonneg
  have hk := S.k_pos
  have hdc : 0 ≤ d / c := div_nonneg hd hc0.le
  have hδs : 0 < δ / s := div_pos hδ hs0
  -- the turning point
  obtain ⟨ys, hys, hΦys⟩ : ∃ ys ∈ Ioo δ L, Φ ys = E := by
    have hcont : ContinuousOn Φ (Icc δ L) := S.contDiff.continuous.continuousOn
    have hmem : E ∈ Ioo (Φ δ) (Φ L) :=
      ⟨by linarith [S.low δ le_rfl, S.E_pos], by linarith [S.high L le_rfl, S.E_lt]⟩
    exact intermediate_value_Ioo S.δ_lt.le hcont hmem
  -- the particle never passes the turning point
  have hle_ys : ∀ t ∈ Icc a b, x t ≤ ys := by
    intro t ht
    by_contra hcon
    rw [not_le] at hcon
    have h1 := S.slope_integrated hys.1.le hcon.le (S.lt_L ht).le
    have h2 := S.pot_le ht
    have h3 := mul_pos hk (sub_pos.mpr hcon)
    linarith
  -- and it is strictly below it whenever it moves
  have hlt_ys : ∀ t ∈ Icc a b, p t ≠ 0 → x t < ys := by
    intro t ht hp0
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : E ≤ Φ (x t) := hΦys ▸ S.monotone_Φ hcon
    have h2 := S.sq_mom ht
    have h3 : 0 < p t ^ 2 := by positivity
    linarith
  -- above the foot, the kinetic energy controls the distance to the turning point
  have hsq_gap : ∀ t ∈ Icc a b, δ ≤ x t → 2 * k * (ys - x t) ≤ p t ^ 2 := by
    intro t ht hδx
    have h1 := S.slope_integrated hδx (hle_ys t ht) hys.2.le
    have h2 := S.sq_mom ht
    rw [hΦys] at h1
    nlinarith
  -- **Phase 1**: the particle reaches the foot `δ` within `d/c + δ/s`
  obtain ⟨tδ, htδ, hxtδ⟩ : ∃ tδ ∈ Ioc a (a + d / c + δ / s), δ ≤ x tδ := by
    by_contra hcon
    push Not at hcon
    have hT₁b : a + d / c + δ / s ≤ b := by linarith
    have hlt : ∀ t ∈ Icc a (a + d / c + δ / s), x t < δ := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with heq | hgt
      · rw [← heq, S.init_x]; linarith
      · exact hcon t ⟨hgt, ht.2⟩
    have hsub : Icc a (a + d / c + δ / s) ⊆ Icc a b := Icc_subset_Icc le_rfl hT₁b
    have hpos : ∀ t ∈ Icc a (a + d / c + δ / s), 0 < p t := by
      refine pos_on_of_ne_zero (S.continuousOn_p.mono hsub) (fun t ht h0 => ?_) ?_
      · have := S.sqrtE_le_abs_p (hsub ht) (hlt t ht).le
        rw [h0, abs_zero, hs] at this
        linarith
      · rw [S.init_p, hc]; exact hc0
    have hge : ∀ t ∈ Icc a (a + d / c + δ / s), s ≤ p t := by
      intro t ht
      have := S.sqrtE_le_abs_p (hsub ht) (hlt t ht).le
      rwa [abs_of_pos (hpos t ht), hs] at this
    have ht₀a : a ≤ a + d / c := by linarith
    have ht₀T : a + d / c ≤ a + d / c + δ / s := by linarith
    have hamem : a ∈ Icc a b := ⟨le_rfl, S.le_b⟩
    -- the flat part is crossed at the exact speed `c`
    have hxt₀ : 0 ≤ x (a + d / c) := by
      by_contra hneg
      rw [not_le] at hneg
      have hflat : ∀ t ∈ Icc a (a + d / c), x t ≤ 0 := by
        intro t ht
        have h := S.x_lower (hsub ⟨ht.1, ht.2.trans ht₀T⟩) (hsub ⟨ht₀a, ht₀T⟩) ht.2 (C := 0)
          (fun u hu => (hpos u ⟨ht.1.trans hu.1, hu.2.trans ht₀T⟩).le)
        linarith
      have hpc : ∀ t ∈ Icc a (a + d / c), c ≤ p t := by
        intro t ht
        have hmem : t ∈ Icc a (a + d / c + δ / s) := ⟨ht.1, ht.2.trans ht₀T⟩
        have h1 := S.abs_p_of_nonpos (hsub hmem) (hflat t ht)
        rw [abs_of_pos (hpos t hmem), hc] at h1
        rw [h1]
      have hmv := S.x_lower hamem (hsub ⟨ht₀a, ht₀T⟩) ht₀a hpc
      rw [S.init_x] at hmv
      have : c * (a + d / c - a) = d := by field_simp; ring
      linarith
    have hmv := S.x_lower (hsub ⟨ht₀a, ht₀T⟩) (hsub ⟨by linarith, le_rfl⟩) ht₀T (C := s)
      (fun u hu => hge u ⟨ht₀a.trans hu.1, hu.2⟩)
    have : s * (a + d / c + δ / s - (a + d / c)) = δ := by field_simp; ring
    have := hlt (a + d / c + δ / s) ⟨by linarith, le_rfl⟩
    linarith
  have htδb : tδ ∈ Icc a b := ⟨htδ.1.le, by linarith [htδ.2]⟩
  -- **Phase 2**: within the climbing time `τ` the momentum has become nonpositive
  have ht₂b : tδ + τ ∈ Icc a b := ⟨by linarith [htδ.1], by linarith [htδ.2]⟩
  have hp₂ : p (tδ + τ) ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    have hsub : Icc tδ (tδ + τ) ⊆ Icc a b := Icc_subset_Icc htδb.1 ht₂b.2
    have hpos : ∀ u ∈ Icc tδ (tδ + τ), 0 < p u := fun u hu =>
      lt_of_lt_of_le hcon (S.p_antitone (hsub hu) ht₂b hu.2)
    have hxge : ∀ u ∈ Icc tδ (tδ + τ), δ ≤ x u := by
      intro u hu
      have h := S.x_lower htδb (hsub hu) hu.1 (C := 0)
        (fun v hv => (hpos v ⟨hv.1, hv.2.trans hu.2⟩).le)
      linarith
    have hclimb := sqrt_gap_climb (x := x) (p := p) (ys := ys) (k := k)
      (by linarith : tδ < tδ + τ) (S.continuousOn_x.mono hsub)
      (fun u hu => S.hasDerivAt_x ⟨lt_of_le_of_lt htδb.1 hu.1, lt_of_lt_of_le hu.2 ht₂b.2⟩)
      (fun u hu => hlt_ys u (hsub (Ioo_subset_Icc_self hu)) (hpos u (Ioo_subset_Icc_self hu)).ne')
      (fun u hu => (hpos u (Ioo_subset_Icc_self hu)).le)
      (fun u hu => hsq_gap u (hsub (Ioo_subset_Icc_self hu)) (hxge u (Ioo_subset_Icc_self hu)))
      hk.le
    have h1 : Real.sqrt (ys - x tδ) ≤ Real.sqrt (L - δ) :=
      Real.sqrt_le_sqrt (by linarith [hys.2])
    have h2 : -(Real.sqrt (2 * k) / 2) * (tδ + τ - tδ) = -Real.sqrt (L - δ) := by
      rw [show tδ + τ - tδ = τ by ring, neg_mul, hrate]
    have h3 : Real.sqrt (ys - x (tδ + τ)) ≤ 0 := by linarith
    have h4 := Real.sqrt_eq_zero'.mp (le_antisymm h3 (Real.sqrt_nonneg _))
    have h5 := hlt_ys (tδ + τ) ht₂b hcon.ne'
    linarith
  -- **Phase 3**: within a further time `τ` the particle is back at the foot
  obtain ⟨t₃, ht₃, hxt₃⟩ : ∃ t₃ ∈ Icc (tδ + τ) (tδ + τ + τ), x t₃ ≤ δ := by
    by_contra hcon
    push Not at hcon
    have ht₃b : tδ + τ + τ ∈ Icc a b := ⟨by linarith [htδ.1], by linarith [htδ.2]⟩
    have hsub : Icc (tδ + τ) (tδ + τ + τ) ⊆ Icc a b := Icc_subset_Icc ht₂b.1 ht₃b.2
    have hneg : ∀ u ∈ Ioo (tδ + τ) (tδ + τ + τ), p u < 0 := by
      intro u hu
      have h := S.p_decel ht₂b (hsub (Ioo_subset_Icc_self hu)) hu.1.le
        (fun v hv => (hcon v ⟨hv.1, hv.2.trans hu.2.le⟩).le)
      have := mul_pos hk (sub_pos.mpr hu.1)
      linarith
    have hdesc := sqrt_gap_descend (x := x) (p := p) (ys := ys) (k := k)
      (by linarith : tδ + τ < tδ + τ + τ) (S.continuousOn_x.mono hsub)
      (fun u hu => S.hasDerivAt_x ⟨lt_of_le_of_lt ht₂b.1 hu.1, lt_of_lt_of_le hu.2 ht₃b.2⟩)
      (fun u hu => hlt_ys u (hsub (Ioo_subset_Icc_self hu)) (hneg u hu).ne)
      (fun u hu => (hneg u hu).le)
      (fun u hu => hsq_gap u (hsub (Ioo_subset_Icc_self hu)) (hcon u (Ioo_subset_Icc_self hu)).le)
      hk.le
    rw [show tδ + τ + τ - (tδ + τ) = τ by ring, hrate] at hdesc
    have h1 : Real.sqrt (L - δ) ≤ Real.sqrt (ys - x (tδ + τ + τ)) := by
      have := Real.sqrt_nonneg (ys - x (tδ + τ))
      linarith
    have h2 : L - δ ≤ ys - x (tδ + τ + τ) :=
      (Real.sqrt_le_sqrt_iff (by linarith [hle_ys _ ht₃b])).mp h1
    have h3 := hcon (tδ + τ + τ) ⟨by linarith, le_rfl⟩
    linarith [hys.2]
  have ht₃b : t₃ ∈ Icc a b := ⟨by linarith [ht₃.1, htδ.1], by linarith [ht₃.2, htδ.2]⟩
  have hp₃ : p t₃ < 0 := by
    have h1 : p t₃ ≤ 0 := le_trans (S.p_antitone ht₂b ht₃b ht₃.1) hp₂
    have h2 := S.sqrtE_le_abs_p ht₃b hxt₃
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · rw [h, abs_zero, hs] at h2; linarith
  -- **Phase 4**: the particle returns past `-d` within `δ/s + d/c`
  obtain ⟨t₅, ht₅, hxt₅⟩ : ∃ t₅ ∈ Icc t₃ (t₃ + δ / s + d / c), x t₅ ≤ -d := by
    by_contra hcon
    push Not at hcon
    have hT₅b : t₃ + δ / s + d / c ≤ b := by linarith [ht₃.2, htδ.2]
    have hsub : Icc t₃ (t₃ + δ / s + d / c) ⊆ Icc a b := Icc_subset_Icc ht₃b.1 hT₅b
    have hpneg : ∀ u ∈ Icc t₃ (t₃ + δ / s + d / c), p u < 0 := fun u hu =>
      lt_of_le_of_lt (S.p_antitone ht₃b (hsub hu) hu.1) hp₃
    have hxle : ∀ u ∈ Icc t₃ (t₃ + δ / s + d / c), x u ≤ x t₃ := by
      intro u hu
      have h := S.x_upper ht₃b (hsub hu) hu.1 (C := 0)
        (fun v hv => (hpneg v ⟨hv.1, hv.2.trans hu.2⟩).le)
      linarith
    have hple : ∀ u ∈ Icc t₃ (t₃ + δ / s + d / c), p u ≤ -s := by
      intro u hu
      have h := S.sqrtE_le_abs_p (hsub hu) ((hxle u hu).trans hxt₃)
      rw [hs, abs_of_neg (hpneg u hu)] at h
      linarith
    have ht₄ : t₃ + δ / s ∈ Icc t₃ (t₃ + δ / s + d / c) := ⟨by linarith, by linarith⟩
    have hx₄ : x (t₃ + δ / s) ≤ 0 := by
      have h := S.x_upper ht₃b (hsub ht₄) ht₄.1 (C := -s)
        (fun v hv => hple v ⟨hv.1, hv.2.trans ht₄.2⟩)
      have : -s * (t₃ + δ / s - t₃) = -δ := by field_simp; ring
      linarith
    have hpc : ∀ u ∈ Icc (t₃ + δ / s) (t₃ + δ / s + d / c), p u ≤ -c := by
      intro u hu
      have hu' : u ∈ Icc t₃ (t₃ + δ / s + d / c) := ⟨ht₄.1.trans hu.1, hu.2⟩
      have hxu : x u ≤ 0 := by
        have h := S.x_upper (hsub ht₄) (hsub hu') hu.1 (C := 0)
          (fun v hv => (hpneg v ⟨ht₄.1.trans hv.1, hv.2.trans hu.2⟩).le)
        linarith
      have h := S.abs_p_of_nonpos (hsub hu') hxu
      rw [hc, abs_of_neg (hpneg u hu')] at h
      linarith
    have h := S.x_upper (hsub ht₄) (hsub ⟨by linarith, le_rfl⟩) (by linarith) (C := -c) hpc
    have : -c * (t₃ + δ / s + d / c - (t₃ + δ / s)) = -d := by field_simp; ring
    have := hcon (t₃ + δ / s + d / c) ⟨by linarith, le_rfl⟩
    linarith
  -- the return time
  have ht₅b : t₅ ∈ Icc a b := ⟨by linarith [ht₅.1, ht₃b.1], by linarith [ht₅.2, ht₃.2, htδ.2]⟩
  have hδt₅ : tδ ≤ t₅ := by linarith [ht₃.1, ht₅.1]
  have hcontx : ContinuousOn x (Icc tδ t₅) :=
    S.continuousOn_x.mono (Icc_subset_Icc htδb.1 ht₅b.2)
  obtain ⟨t₁, ht₁, hxt₁⟩ := intermediate_value_Icc' hδt₅ hcontx
    (show -d ∈ Icc (x t₅) (x tδ) from ⟨hxt₅, by linarith⟩)
  have ht₁b : t₁ ∈ Icc a b := ⟨htδb.1.trans ht₁.1, ht₁.2.trans ht₅b.2⟩
  have hsign : p t₁ < 0 := by
    by_contra hcon
    push Not at hcon
    have h := S.x_lower htδb ht₁b ht₁.1 (C := 0)
      (fun u hu => le_trans hcon (S.p_antitone ⟨htδb.1.trans hu.1, hu.2.trans ht₁b.2⟩ ht₁b hu.2))
    rw [hxt₁] at h
    linarith
  have hp₁ : p t₁ = -c := by
    have h := S.abs_p_of_nonpos ht₁b (by rw [hxt₁]; linarith)
    rw [hc, abs_of_neg hsign] at h
    linarith
  -- between arrival and return the particle stays strictly beyond the arrival point `-d`:
  -- at a time `t` with `x t ≤ -d` the speed is exactly `c`; moving forward contradicts the start,
  -- moving backward contradicts the return at `t₁`
  have hbeyond : ∀ t ∈ Ioo a t₁, -d < x t := by
    intro t ht
    have htb : t ∈ Icc a b := ⟨ht.1.le, ht.2.le.trans ht₁b.2⟩
    have hamem : a ∈ Icc a b := ⟨le_rfl, S.le_b⟩
    by_contra hcon
    rw [not_lt] at hcon
    have habs := S.abs_p_of_nonpos htb (by linarith)
    rw [hc] at habs
    rcases le_or_gt 0 (p t) with hpt | hpt
    · rw [abs_of_nonneg hpt] at habs
      have hpc : ∀ u ∈ Icc a t, c ≤ p u := fun u hu => by
        rw [← habs]; exact S.p_antitone ⟨hu.1, hu.2.trans htb.2⟩ htb hu.2
      have h := S.x_lower hamem htb ht.1.le hpc
      rw [S.init_x] at h
      have := mul_pos hc0 (sub_pos.mpr ht.1)
      linarith
    · rw [abs_of_neg hpt] at habs
      have hpc : ∀ u ∈ Icc t t₁, p u ≤ -c := fun u hu => by
        have := S.p_antitone htb ⟨htb.1.trans hu.1, hu.2.trans ht₁b.2⟩ hu.1
        linarith
      have h := S.x_upper htb ht₁b ht.2.le hpc
      have := mul_pos hc0 (sub_pos.mpr ht.2)
      linarith
  refine ⟨t₁, ⟨lt_of_lt_of_le htδ.1 ht₁.1, ?_⟩, hxt₁, hp₁,
    fun t ht => S.lt_L ⟨ht.1, ht.2.trans ht₁b.2⟩, hbeyond⟩
  linarith [ht₁.2, ht₅.2, ht₃.2, htδ.2]

end Reflection

/-! ### The scaled barrier: the paper's `eq:cap-time` -/

variable {ε c d : ℝ}

/-- A numerical upper bound on `e³`, sharper than `exp_three_le`. -/
theorem exp_three_lt : exp 3 < 201 / 10 := by
  have h : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h3 : exp 3 = exp 1 * (exp 1 * exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have hpos := Real.exp_pos 1
  rw [h3]
  have h2 : exp 1 * exp 1 < 2.7182818286 * 2.7182818286 := by nlinarith
  nlinarith

/-- **The sharp turning time of the scaled barrier `B(y/ε)`** (`barrierProfile`), entered from the
distance `d` at the speed `c`, i.e. at the energy `E = c²/2`: the foot is at `δ = ε/4`, the height
`4` is reached at `L = ε`, and the slope is at least `k = 4/(e³ε)` in between
(Lemma IX.7). -/
noncomputable def barrierTime (ε c d : ℝ) : ℝ :=
  Reflection.sharpTime (ε / 4) ε (4 / (exp 3 * ε)) (c ^ 2 / 2) d

theorem sqrt_two_mul_half_sq (hc : 0 ≤ c) : Real.sqrt (2 * (c ^ 2 / 2)) = c := by
  rw [show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc]

/-- The climbing term of a scaled barrier of slope `κ/(e³ε)`: `2 · 2√(3ε/4)/√(2κ/(e³ε))`, whose
square is `6 e³ ε²/κ`. -/
theorem climb_sq (hε : 0 < ε) {κ : ℝ} (hκ : 0 < κ) :
    (2 * Real.sqrt (ε - ε / 4) / Real.sqrt (2 * (κ / (exp 3 * ε)))) ^ 2
      = 3 * exp 3 * ε ^ 2 / (2 * κ) := by
  have he := exp_pos 3
  rw [div_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by positivity)]
  field_simp
  ring

theorem barrierTime_pos (hε : 0 < ε) (hc : 1 ≤ c) (hd : 0 ≤ d) : 0 < barrierTime ε c d := by
  have hc0 : (0 : ℝ) < c := by linarith
  unfold barrierTime Reflection.sharpTime
  have h1 : 0 ≤ 2 * d / Real.sqrt (2 * (c ^ 2 / 2)) := by positivity
  have h2 : 0 < 2 * (ε / 4) / Real.sqrt (c ^ 2 / 2) :=
    div_pos (by linarith) (Real.sqrt_pos.mpr (by positivity))
  have h3 : 0 ≤ 2 * (2 * Real.sqrt (ε - ε / 4) / Real.sqrt (2 * (4 / (exp 3 * ε)))) := by
    positivity
  linarith

/-- **The paper's `eq:cap-time`.**  For the scaled barrier `B(y/ε)` and every energy
`E = c²/2 ≥ 1/2`, the sharp turning time satisfies `t_* < 2d/c + 7ε`: the foot is crossed twice
in time at most `ε`, and the two climbs take at most `2ε√(3e³/8) < 6ε`. -/
theorem barrierTime_lt (hε : 0 < ε) (hc : 1 ≤ c) :
    barrierTime ε c d < 2 * d / c + 7 * ε := by
  have hc0 : (0 : ℝ) < c := by linarith
  have he := exp_pos 3
  have he3 : exp 3 < 201 / 10 := exp_three_lt
  unfold barrierTime Reflection.sharpTime
  rw [sqrt_two_mul_half_sq hc0.le]
  -- the foot: `2δ/√E ≤ ε`
  have hsE : (1 : ℝ) / 2 ≤ Real.sqrt (c ^ 2 / 2) := by
    rw [show (1 : ℝ) / 2 = Real.sqrt ((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 : 2 * (ε / 4) / Real.sqrt (c ^ 2 / 2) ≤ ε := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  -- the two climbs: `2 · 2√(3ε/4)/√(8/(e³ε)) < 6ε`
  have h3 : 2 * Real.sqrt (ε - ε / 4) / Real.sqrt (2 * (4 / (exp 3 * ε))) < 3 * ε := by
    refine lt_of_pow_lt_pow_left₀ 2 (by linarith) ?_
    rw [climb_sq hε (by norm_num : (0 : ℝ) < 4)]
    rw [div_lt_iff₀ (by norm_num)]
    nlinarith [sq_nonneg ε, mul_pos hε hε]
  linarith

/-- The sharp time of a cap reflection, entered from the junction boundary `8ε` away from the
foot: `t_* < 16ε/c + 7ε ≤ 23ε`. -/
theorem capTime_lt (hε : 0 < ε) (hc : 1 ≤ c) : barrierTime ε c (8 * ε) < 23 * ε := by
  have h := barrierTime_lt (d := 8 * ε) hε hc
  have h1 : 2 * (8 * ε) / c ≤ 16 * ε := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- The sharp time of the junction-barrier reflection of the arm, entered from `ε` away from the
foot: `t_* < 2ε/c + 7ε ≤ 9ε`. -/
theorem armTime_lt (hε : 0 < ε) (hc : 1 ≤ c) : barrierTime ε c ε < 9 * ε := by
  have h := barrierTime_lt (d := ε) hε hc
  have h1 : 2 * ε / c ≤ 2 * ε := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

end HamiltonianMetricGraphs
