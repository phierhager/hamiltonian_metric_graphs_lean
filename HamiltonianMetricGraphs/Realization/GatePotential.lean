/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ArmDynamics

/-!
# The energy-gated three-channel potential

This file adds a **finite-height gate** to the junction of the explicit three-channel model of
`MicroscopicPotential.lean`: the gate `G_ε` of Sec. IX.E of the paper, with
`g₀ = gateHeight = 7/10`, a smooth bump sitting across the through channel at `u = 0`, supported
in `|u| ≤ 2ε`:

  `gateBump ε u = (h/4) · ((1 - m) · wallPot ε (u + 2ε) + m · wallPot ε (2ε - u))`,
  `m = mixG ε u = plateau (-ε) ε u`.

Its two halves are *exactly* scaled copies of the reflecting wall `wallPot ε` of
`CapDynamics.lean`:

* for `u ≤ -ε` we have `m = 0`, so `gateBump ε u = (h/4) · wallPot ε (u + 2ε)` — a monotone
  barrier of height `h` whose foot is at `u = -2ε`, exactly the shape handled by
  `Reflection.reflect_of_barrier_sharp` (Lemma IX.8);
* for `u ≥ ε` we have `m = 1`, so `gateBump ε u = (h/4) · wallPot ε (2ε - u)` — its mirror image;
* on the overlap `|u| ≤ ε` both wall arguments lie in `[ε, 3ε]`, so the convex combination is
  between `h` and `h e^{2/3}` (`gateBump_ge`, `gateBump_le_sharp`);
* outside `|u| ≥ 2ε` the gate and its derivative vanish identically, so the edge flights and the
  outer cap reflections of the model are completely unaffected.

The resulting longitudinal potential of the through channel is `gatePot ε = capPot ε + gateBump ε`
and the full microscopic potential is `gatePot2 ε`, obtained from `microPot ε` by that single
replacement.  In the third-arm region `gatePot2 ε = microPot ε` **identically**, so the whole
arm analysis of `ArmDynamics.lean` applies verbatim.

The point of the gate is that it is *energetically selective*: a longitudinal energy below
`g₀ = h` cannot reach the core `[-ε, ε]`, where `G_ε ≥ g₀`, while a longitudinal energy above the
gate height `E_c = max G_ε` crosses it freely.  The gate height is `gateCritical`; it does not
depend on `ε`, because `G_ε(u) = G_1(u/ε)` (`gateBump_scale`, `gateCritical_isGreatest`), and
`G_ε(0) = g₀ e^{1/2}` and `G_ε ≤ g₀ e^{2/3}` give `1.15 < E_c < 1.365` (`gateCritical_gt`,
`gateCritical_lt`).  Hence the two disjoint compact windows `K₋ = [1/2, 3/5]` and
`K₊ = [3/2, 2]` lie on either side of the gate, `max K₋ < g₀ < E_c < min K₊`, and the same
microscopic Hamiltonian family induces **two different deterministic routing laws**.
-/

namespace HamiltonianMetricGraphs

open Set Real

/-! ### The gate -/

/-- The paper's `g₀ = 7/10`: the lower bound of the gate on its core `[-ε, ε]` (`gateBump_ge`).
Every longitudinal energy below it is reflected.  The gate height itself, `E_c = max G_ε`, is
`gateCritical`, with `g₀ < 1.15 < E_c < 1.365`. -/
noncomputable def gateHeight : ℝ := 7 / 10

theorem gateHeight_pos : 0 < gateHeight := by rw [gateHeight]; norm_num

/-- The smooth switch between the two halves of the gate: `0` for `u ≤ -ε`, `1` for `u ≥ ε`. -/
noncomputable def mixG (ε u : ℝ) : ℝ := plateau (-ε) ε u

theorem mixG_nonneg (ε u : ℝ) : 0 ≤ mixG ε u := plateau_nonneg _ _ _

theorem mixG_le_one (ε u : ℝ) : mixG ε u ≤ 1 := plateau_le_one _ _ _

theorem mixG_of_le (hε : 0 < ε) {u : ℝ} (h : u ≤ -ε) : mixG ε u = 0 :=
  plateau_of_le (by linarith) h

theorem mixG_of_ge (hε : 0 < ε) {u : ℝ} (h : ε ≤ u) : mixG ε u = 1 :=
  plateau_of_ge (by linarith) h

theorem contDiff_mixG (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (mixG ε) := contDiff_plateau _ _

/-- **The energy gate**: a smooth bump of height between `gateHeight` and `2 * gateHeight`,
supported in `|u| ≤ 2ε`, whose two flanks are exactly scaled copies of the reflecting wall. -/
noncomputable def gateBump (ε u : ℝ) : ℝ :=
  gateHeight / 4 *
    ((1 - mixG ε u) * wallPot ε (u + 2 * ε) + mixG ε u * wallPot ε (2 * ε - u))

/-! #### The two flanks -/

/-- On the left flank the gate is exactly a scaled reflecting wall with foot at `u = -2ε`. -/
theorem gateBump_of_le (hε : 0 < ε) {u : ℝ} (h : u ≤ -ε) :
    gateBump ε u = gateHeight / 4 * wallPot ε (u + 2 * ε) := by
  rw [gateBump, mixG_of_le hε h]
  ring

/-- On the right flank the gate is the mirror image. -/
theorem gateBump_of_ge (hε : 0 < ε) {u : ℝ} (h : ε ≤ u) :
    gateBump ε u = gateHeight / 4 * wallPot ε (2 * ε - u) := by
  rw [gateBump, mixG_of_ge hε h]
  ring

/-! #### Values -/

theorem gateBump_nonneg (ε u : ℝ) : 0 ≤ gateBump ε u := by
  have h1 := wallPot_nonneg ε (u + 2 * ε)
  have h2 := wallPot_nonneg ε (2 * ε - u)
  have h3 := mixG_nonneg ε u
  have h4 := mixG_le_one ε u
  have h5 := gateHeight_pos
  rw [gateBump]
  have : 0 ≤ (1 - mixG ε u) * wallPot ε (u + 2 * ε) + mixG ε u * wallPot ε (2 * ε - u) := by
    have ha : 0 ≤ (1 - mixG ε u) * wallPot ε (u + 2 * ε) := mul_nonneg (by linarith) h1
    have hb : 0 ≤ mixG ε u * wallPot ε (2 * ε - u) := mul_nonneg h3 h2
    linarith
  positivity

/-- A scaled wall never exceeds its nominal height on the near side of its shoulder. -/
theorem wallPot_le_four_of_le (hε : 0 < ε) {y : ℝ} (h : y ≤ ε) : wallPot ε y ≤ 4 := by
  have hle : y / ε ≤ 1 := by rw [div_le_one hε]; exact h
  calc wallPot ε y = barrierProfile (y / ε) := rfl
    _ ≤ barrierProfile 1 := barrierProfile_monotone hle
    _ = 4 := barrierProfile_one

/-- `exp (2/3) < 2`, the numeric fact that keeps the gate below `2 * gateHeight`. -/
theorem exp_two_thirds_lt_two : exp (2 / 3) < 2 := by
  have hlog : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h2 : (0 : ℝ) < 2 := by norm_num
  exact (Real.lt_log_iff_exp_lt h2).mp hlog

/-- The scaled wall stays below `8` up to three shoulders: `barrierProfile 3 = 4 exp (2/3) < 8`. -/
theorem barrierProfile_le_eight_of_le_three {s : ℝ} (h : s ≤ 3) : barrierProfile s ≤ 8 := by
  rcases le_or_gt s 0 with hs | hs
  · rw [barrierProfile_of_nonpos hs]; norm_num
  · have hinv : (1 : ℝ) / 3 ≤ 1 / s := one_div_le_one_div_of_le hs h
    have hg : glue s ≤ exp (-(1 / 3)) := by
      rw [glue_of_pos hs]
      refine Real.exp_le_exp.mpr ?_
      rw [← one_div]
      linarith
    have hexp : 4 * exp 1 * exp (-(1 / 3)) = 4 * exp (2 / 3) := by
      rw [mul_assoc, ← Real.exp_add]
      norm_num
    have hpos : (0 : ℝ) < 4 * exp 1 := by positivity
    calc barrierProfile s = 4 * exp 1 * glue s := rfl
      _ ≤ 4 * exp 1 * exp (-(1 / 3)) := by nlinarith [glue_nonneg s]
      _ = 4 * exp (2 / 3) := hexp
      _ ≤ 8 := by nlinarith [exp_two_thirds_lt_two]

theorem wallPot_le_eight_of_le (hε : 0 < ε) {y : ℝ} (h : y ≤ 3 * ε) : wallPot ε y ≤ 8 := by
  refine barrierProfile_le_eight_of_le_three ?_
  rw [div_le_iff₀ hε]
  linarith

/-- **The gate never exceeds `2 · gateHeight`.**  A crude bound; the sharp one is
`gateBump_le_sharp` (`G_ε ≤ g₀ e^{2/3} < 1.365`). -/
theorem gateBump_le (hε : 0 < ε) (u : ℝ) : gateBump ε u ≤ 2 * gateHeight := by
  have hh := gateHeight_pos
  have hm0 := mixG_nonneg ε u
  have hm1 := mixG_le_one ε u
  rcases le_or_gt u (-ε) with h | h
  · rw [gateBump_of_le hε h]
    have := wallPot_le_four_of_le hε (show u + 2 * ε ≤ ε by linarith)
    nlinarith
  · rcases le_or_gt ε u with h' | h'
    · rw [gateBump_of_ge hε h']
      have := wallPot_le_four_of_le hε (show 2 * ε - u ≤ ε by linarith)
      nlinarith
    · have hA := wallPot_le_eight_of_le hε (show u + 2 * ε ≤ 3 * ε by linarith)
      have hB := wallPot_le_eight_of_le hε (show 2 * ε - u ≤ 3 * ε by linarith)
      have hAn := wallPot_nonneg ε (u + 2 * ε)
      have hBn := wallPot_nonneg ε (2 * ε - u)
      have h1 : (1 - mixG ε u) * wallPot ε (u + 2 * ε) ≤ (1 - mixG ε u) * 8 :=
        mul_le_mul_of_nonneg_left hA (by linarith)
      have h2 : mixG ε u * wallPot ε (2 * ε - u) ≤ mixG ε u * 8 :=
        mul_le_mul_of_nonneg_left hB hm0
      have hkey : (1 - mixG ε u) * wallPot ε (u + 2 * ε)
          + mixG ε u * wallPot ε (2 * ε - u) ≤ 8 := by nlinarith
      have hkey0 : (0 : ℝ) ≤ (1 - mixG ε u) * wallPot ε (u + 2 * ε)
          + mixG ε u * wallPot ε (2 * ε - u) := by
        have ha : 0 ≤ (1 - mixG ε u) * wallPot ε (u + 2 * ε) :=
          mul_nonneg (by linarith) hAn
        have hb : 0 ≤ mixG ε u * wallPot ε (2 * ε - u) := mul_nonneg hm0 hBn
        linarith
      have hmul : gateHeight / 4 * ((1 - mixG ε u) * wallPot ε (u + 2 * ε)
          + mixG ε u * wallPot ε (2 * ε - u)) ≤ gateHeight / 4 * 8 :=
        mul_le_mul_of_nonneg_left hkey (by linarith)
      rw [gateBump]
      linarith

/-- **The gate reaches `gateHeight` across the whole core `|u| ≤ ε`.**  This is the reflection
threshold: an energy below it cannot cross the junction. -/
theorem gateBump_ge (hε : 0 < ε) {u : ℝ} (h : |u| ≤ ε) : gateHeight ≤ gateBump ε u := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hA := wallPot_ge_of_le hε (show ε ≤ u + 2 * ε by linarith)
  have hB := wallPot_ge_of_le hε (show ε ≤ 2 * ε - u by linarith)
  have hm0 := mixG_nonneg ε u
  have hm1 := mixG_le_one ε u
  have hh := gateHeight_pos
  have h1 : (1 - mixG ε u) * 4 ≤ (1 - mixG ε u) * wallPot ε (u + 2 * ε) :=
    mul_le_mul_of_nonneg_left hA (by linarith)
  have h2 : mixG ε u * 4 ≤ mixG ε u * wallPot ε (2 * ε - u) :=
    mul_le_mul_of_nonneg_left hB hm0
  have hkey : (4 : ℝ) ≤ (1 - mixG ε u) * wallPot ε (u + 2 * ε)
      + mixG ε u * wallPot ε (2 * ε - u) := by nlinarith
  have hmul : gateHeight / 4 * 4 ≤ gateHeight / 4 * ((1 - mixG ε u) * wallPot ε (u + 2 * ε)
      + mixG ε u * wallPot ε (2 * ε - u)) :=
    mul_le_mul_of_nonneg_left hkey (by linarith)
  rw [gateBump]
  linarith

/-! #### The paper's bounds: `G_ε ≤ g₀ e^{2/3} < 1.365` and `G_ε(0) = g₀ e^{1/2} > 1.15` -/

/-- `B ≤ 4 e^{2/3}` on `(-∞, 3]` (Lemma IX.7). -/
theorem barrierProfile_le_of_le_three {s : ℝ} (h : s ≤ 3) :
    barrierProfile s ≤ 4 * exp (2 / 3) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [barrierProfile_of_nonpos hs]; positivity
  · have hinv : (1 : ℝ) / 3 ≤ 1 / s := one_div_le_one_div_of_le hs h
    have hg : glue s ≤ exp (-(1 / 3)) := by
      rw [glue_of_pos hs]
      refine Real.exp_le_exp.mpr ?_
      rw [← one_div]
      linarith
    have hexp : 4 * exp 1 * exp (-(1 / 3)) = 4 * exp (2 / 3) := by
      rw [mul_assoc, ← Real.exp_add]
      norm_num
    have hpos : (0 : ℝ) < 4 * exp 1 := by positivity
    calc barrierProfile s = 4 * exp 1 * glue s := rfl
      _ ≤ 4 * exp 1 * exp (-(1 / 3)) := by nlinarith [glue_nonneg s]
      _ = 4 * exp (2 / 3) := hexp

/-- `e^{2/3} < 1.95`, since `e² < 7.41 < 1.95³`. -/
theorem exp_two_thirds_lt : exp (2 / 3) < 39 / 20 := by
  have h : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos := Real.exp_pos 1
  have h3 : exp (2 / 3) ^ 3 = exp 1 * exp 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  by_contra hcon
  rw [not_lt] at hcon
  have h1 : ((39 : ℝ) / 20) ^ 3 ≤ exp (2 / 3) ^ 3 := by
    exact pow_le_pow_left₀ (by norm_num) hcon 3
  rw [h3] at h1
  nlinarith

/-- `e^{1/2} > 23/14`, since `e > (23/14)² = 529/196`. -/
theorem exp_half_gt : (23 : ℝ) / 14 < exp (1 / 2) := by
  have h : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
  have h2 : exp (1 / 2) ^ 2 = exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  by_contra hcon
  rw [not_lt] at hcon
  have h1 : exp (1 / 2) ^ 2 ≤ ((23 : ℝ) / 14) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hcon 2
  rw [h2] at h1
  norm_num at h1
  linarith

/-- **The gate never exceeds `g₀ e^{2/3}`**: each argument of `B` is below `3` where its weight
is nonzero. -/
theorem gateBump_le_sharp (hε : 0 < ε) (u : ℝ) :
    gateBump ε u ≤ gateHeight * exp (2 / 3) := by
  have hh := gateHeight_pos
  have hm0 := mixG_nonneg ε u
  have hm1 := mixG_le_one ε u
  have he1 : (1 : ℝ) ≤ exp (2 / 3) := Real.one_le_exp (by norm_num)
  rcases le_or_gt u (-ε) with h | h
  · rw [gateBump_of_le hε h]
    have := wallPot_le_four_of_le hε (show u + 2 * ε ≤ ε by linarith)
    nlinarith
  · rcases le_or_gt ε u with h' | h'
    · rw [gateBump_of_ge hε h']
      have := wallPot_le_four_of_le hε (show 2 * ε - u ≤ ε by linarith)
      nlinarith
    · have hA : wallPot ε (u + 2 * ε) ≤ 4 * exp (2 / 3) := by
        refine barrierProfile_le_of_le_three ?_
        rw [div_le_iff₀ hε]; linarith
      have hB : wallPot ε (2 * ε - u) ≤ 4 * exp (2 / 3) := by
        refine barrierProfile_le_of_le_three ?_
        rw [div_le_iff₀ hε]; linarith
      have h1 : (1 - mixG ε u) * wallPot ε (u + 2 * ε) ≤ (1 - mixG ε u) * (4 * exp (2 / 3)) :=
        mul_le_mul_of_nonneg_left hA (by linarith)
      have h2 : mixG ε u * wallPot ε (2 * ε - u) ≤ mixG ε u * (4 * exp (2 / 3)) :=
        mul_le_mul_of_nonneg_left hB hm0
      have hkey : (1 - mixG ε u) * wallPot ε (u + 2 * ε)
          + mixG ε u * wallPot ε (2 * ε - u) ≤ 4 * exp (2 / 3) := by nlinarith
      have hmul : gateHeight / 4 * ((1 - mixG ε u) * wallPot ε (u + 2 * ε)
          + mixG ε u * wallPot ε (2 * ε - u)) ≤ gateHeight / 4 * (4 * exp (2 / 3)) :=
        mul_le_mul_of_nonneg_left hkey (by linarith)
      rw [gateBump]
      linarith

/-- The gate stays below `1.365`. -/
theorem gateBump_lt (hε : 0 < ε) (u : ℝ) : gateBump ε u < 1365 / 1000 := by
  have h1 := gateBump_le_sharp hε u
  have h2 := exp_two_thirds_lt
  have hh : gateHeight = 7 / 10 := rfl
  rw [hh] at h1
  linarith

/-- **The value at the centre**: `G_ε(0) = (g₀/4) B(2) = g₀ e^{1/2}`. -/
theorem gateBump_zero (hε : 0 < ε) : gateBump ε 0 = gateHeight * exp (1 / 2) := by
  have hB : wallPot ε (2 * ε) = 4 * exp (1 / 2) := by
    rw [wallPot, show 2 * ε / ε = 2 by field_simp, barrierProfile, glue_of_pos (by norm_num),
      mul_assoc, ← Real.exp_add]
    norm_num
  rw [gateBump, zero_add, sub_zero, hB]
  ring

/-- **The gate scales with `ε`**: `G_ε(u) = G_1(u/ε)`. -/
theorem gateBump_scale (hε : 0 < ε) (u : ℝ) : gateBump ε u = gateBump 1 (u / ε) := by
  have hne : ε ≠ 0 := ne_of_gt hε
  unfold gateBump mixG plateau wallPot
  have e1 : (ε - -ε)⁻¹ * (u - -ε) = (1 - -1)⁻¹ * (u / ε - -1) := by field_simp
  have e2 : (u + 2 * ε) / ε = (u / ε + 2 * 1) / 1 := by field_simp
  have e3 : (2 * ε - u) / ε = (2 * 1 - u / ε) / 1 := by field_simp
  rw [e1, e2, e3]

/-! #### Support -/

theorem gateBump_of_le_neg (hε : 0 < ε) {u : ℝ} (h : u ≤ -(2 * ε)) : gateBump ε u = 0 := by
  rw [gateBump_of_le hε (by linarith), wallPot_of_nonpos hε (by linarith), mul_zero]

theorem gateBump_of_ge_pos (hε : 0 < ε) {u : ℝ} (h : 2 * ε ≤ u) : gateBump ε u = 0 := by
  rw [gateBump_of_ge hε (by linarith), wallPot_of_nonpos hε (by linarith), mul_zero]

/-! #### Smoothness -/

theorem contDiff_gateBump (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (gateBump ε) := by
  apply ContDiff.mul contDiff_const
  apply ContDiff.add
  · exact (contDiff_const.sub (contDiff_mixG ε)).mul
      ((contDiff_wallPot ε).comp (contDiff_id.add contDiff_const))
  · exact (contDiff_mixG ε).mul ((contDiff_wallPot ε).comp (contDiff_const.sub contDiff_id))

/-! ### The gate height `E_c = max G_ε` -/

/-- **The gate height** `E_c = max G_ε` of the paper.  It does not depend on `ε`
(`gateCritical_isGreatest`). -/
noncomputable def gateCritical : ℝ := sSup (Set.range (gateBump 1))

/-- The maximum of `G_1` is attained: `G_1` is continuous and vanishes outside `[-2, 2]`. -/
theorem exists_isGreatest_gateBump_one :
    ∃ u₀, IsGreatest (Set.range (gateBump 1)) (gateBump 1 u₀) := by
  obtain ⟨u₀, -, hmax⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_isMaxOn
    (nonempty_Icc.mpr (by norm_num)) (contDiff_gateBump 1 (n := 0)).continuous.continuousOn
  refine ⟨u₀, ⟨u₀, rfl⟩, ?_⟩
  rintro _ ⟨u, rfl⟩
  have h0 : gateBump 1 0 ≤ gateBump 1 u₀ :=
    isMaxOn_iff.mp hmax 0 (show (0 : ℝ) ∈ Icc (-2) 2 by norm_num)
  have hnn := gateBump_nonneg 1 0
  rcases le_or_gt u (-2) with h | h
  · rw [gateBump_of_le_neg one_pos (by linarith)]; linarith
  · rcases le_or_gt 2 u with h' | h'
    · rw [gateBump_of_ge_pos one_pos (by linarith)]; linarith
    · exact isMaxOn_iff.mp hmax u ⟨h.le, h'.le⟩

/-- **`E_c` is the maximum of the gate `G_ε`, for every `ε > 0`.**  In particular it does not
depend on `ε`. -/
theorem gateCritical_isGreatest (hε : 0 < ε) :
    IsGreatest (Set.range (gateBump ε)) gateCritical := by
  have hrange : Set.range (gateBump ε) = Set.range (gateBump 1) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u / ε, (gateBump_scale hε u).symm⟩
    · rintro ⟨v, rfl⟩
      refine ⟨v * ε, ?_⟩
      rw [gateBump_scale hε, mul_div_cancel_right₀ v (ne_of_gt hε)]
  obtain ⟨u₀, hu₀⟩ := exists_isGreatest_gateBump_one
  rw [hrange, gateCritical, hu₀.csSup_eq]
  exact hu₀

theorem gateBump_le_gateCritical (hε : 0 < ε) (u : ℝ) : gateBump ε u ≤ gateCritical :=
  (gateCritical_isGreatest hε).2 ⟨u, rfl⟩

/-- **`1.15 < E_c`**, from `E_c ≥ G_ε(0) = g₀ e^{1/2}`. -/
theorem gateCritical_gt : (115 : ℝ) / 100 < gateCritical := by
  have h1 := gateBump_le_gateCritical one_pos 0
  rw [gateBump_zero one_pos] at h1
  have h2 := exp_half_gt
  have hh : gateHeight = 7 / 10 := rfl
  rw [hh] at h1
  linarith

/-- **`E_c < 1.365`**, from `G_ε ≤ g₀ e^{2/3}`. -/
theorem gateCritical_lt : gateCritical < 1365 / 1000 := by
  obtain ⟨u, hu⟩ := (gateCritical_isGreatest one_pos).1
  rw [← hu]
  exact gateBump_lt one_pos u

/-- `g₀ < E_c`: the gate height exceeds the lower bound `g₀` of the gate on its core. -/
theorem gateHeight_lt_gateCritical : gateHeight < gateCritical := by
  have h := gateCritical_gt
  have hh : gateHeight = 7 / 10 := rfl
  rw [hh]
  linarith

/-! #### The derivative on the two flanks -/

theorem deriv_gateBump_of_lt (hε : 0 < ε) {u : ℝ} (h : u < -ε) :
    deriv (gateBump ε) u = gateHeight / 4 * deriv (wallPot ε) (u + 2 * ε) := by
  have heq : gateBump ε =ᶠ[nhds u] fun s => gateHeight / 4 * wallPot ε (s + 2 * ε) := by
    filter_upwards [Iio_mem_nhds h] with s hs
    exact gateBump_of_le hε (le_of_lt hs)
  rw [heq.deriv_eq]
  have hw : HasDerivAt (wallPot ε) (deriv (wallPot ε) (u + 2 * ε)) (u + 2 * ε) :=
    ((contDiff_wallPot ε (n := 1)).differentiable (by norm_num) _).hasDerivAt
  have hs : HasDerivAt (fun s : ℝ => s + 2 * ε) 1 u := by
    simpa using (hasDerivAt_id u).add_const (2 * ε)
  have hc := (hw.comp u hs).const_mul (gateHeight / 4)
  rw [mul_one] at hc
  exact hc.deriv

theorem deriv_gateBump_of_gt (hε : 0 < ε) {u : ℝ} (h : ε < u) :
    deriv (gateBump ε) u = -(gateHeight / 4 * deriv (wallPot ε) (2 * ε - u)) := by
  have heq : gateBump ε =ᶠ[nhds u] fun s => gateHeight / 4 * wallPot ε (2 * ε - s) := by
    filter_upwards [Ioi_mem_nhds h] with s hs
    exact gateBump_of_ge hε (le_of_lt hs)
  rw [heq.deriv_eq]
  have hw : HasDerivAt (wallPot ε) (deriv (wallPot ε) (2 * ε - u)) (2 * ε - u) :=
    ((contDiff_wallPot ε (n := 1)).differentiable (by norm_num) _).hasDerivAt
  have hs : HasDerivAt (fun s : ℝ => 2 * ε - s) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub (2 * ε)
  have hc := (hw.comp u hs).const_mul (gateHeight / 4)
  have hrw : gateHeight / 4 * (deriv (wallPot ε) (2 * ε - u) * -1)
      = -(gateHeight / 4 * deriv (wallPot ε) (2 * ε - u)) := by ring
  rw [hrw] at hc
  exact hc.deriv

/-- **The gate is flat outside its support**: no force beyond `|u| ≥ 2ε`. -/
theorem deriv_gateBump_of_two_le (hε : 0 < ε) {u : ℝ} (h : 2 * ε ≤ u) :
    deriv (gateBump ε) u = 0 := by
  rw [deriv_gateBump_of_gt hε (by linarith), deriv_wallPot_of_nonpos hε (by linarith)]
  ring

theorem deriv_gateBump_of_le_neg (hε : 0 < ε) {u : ℝ} (h : u ≤ -(2 * ε)) :
    deriv (gateBump ε) u = 0 := by
  rw [deriv_gateBump_of_lt hε (by linarith), deriv_wallPot_of_nonpos hε (by linarith)]
  ring

/-! ### The gated longitudinal potential of the through channel -/

/-- The longitudinal potential of the gated through channel: the two reflecting caps at the outer
vertices `u = ±1`, plus the gate at the junction. -/
noncomputable def gatePot (ε u : ℝ) : ℝ := capPot ε u + gateBump ε u

theorem gatePot_nonneg (ε u : ℝ) : 0 ≤ gatePot ε u :=
  add_nonneg (capPot_nonneg _ _) (gateBump_nonneg _ _)

theorem contDiff_gatePot (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (gatePot ε) :=
  (contDiff_capPot ε).add (contDiff_gateBump ε)

theorem hasDerivAt_gatePot (ε u : ℝ) :
    HasDerivAt (gatePot ε) (deriv (capPot ε) u + deriv (gateBump ε) u) u := by
  have h1 : HasDerivAt (capPot ε) (deriv (capPot ε) u) u :=
    ((contDiff_capPot ε (n := 1)).differentiable (by norm_num) u).hasDerivAt
  have h2 : HasDerivAt (gateBump ε) (deriv (gateBump ε) u) u :=
    ((contDiff_gateBump ε (n := 1)).differentiable (by norm_num) u).hasDerivAt
  exact h1.add h2

theorem deriv_gatePot (ε u : ℝ) :
    deriv (gatePot ε) u = deriv (capPot ε) u + deriv (gateBump ε) u :=
  (hasDerivAt_gatePot ε u).deriv

/-- **The gated tube is flat between the gate and the cap**: on `[2ε, 1]` — and by symmetry on
`[-1, -2ε]` — the longitudinal motion of the gated through channel is exactly free. -/
theorem deriv_gatePot_of_mem_right (hε : 0 < ε) {u : ℝ} (h₁ : 2 * ε ≤ u) (h₂ : u ≤ 1) :
    deriv (gatePot ε) u = 0 := by
  rw [deriv_gatePot, deriv_gateBump_of_two_le hε h₁,
    deriv_capPot_of_abs_le_one hε (abs_le.mpr ⟨by linarith, h₂⟩), add_zero]

theorem deriv_gatePot_of_mem_left (hε : 0 < ε) {u : ℝ} (h₁ : -1 ≤ u) (h₂ : u ≤ -(2 * ε)) :
    deriv (gatePot ε) u = 0 := by
  rw [deriv_gatePot, deriv_gateBump_of_le_neg hε h₂,
    deriv_capPot_of_abs_le_one hε (abs_le.mpr ⟨h₁, by linarith⟩), add_zero]

/-- On the left flank the gated potential is exactly the scaled reflecting wall. -/
theorem deriv_gatePot_of_lt (hε : 0 < ε) {u : ℝ} (h : u < -ε) (h₁ : -1 ≤ u) :
    deriv (gatePot ε) u = gateHeight / 4 * deriv (wallPot ε) (u + 2 * ε) := by
  rw [deriv_gatePot, deriv_gateBump_of_lt hε h,
    deriv_capPot_of_abs_le_one hε (abs_le.mpr ⟨h₁, by linarith⟩), zero_add]

/-- On the right flank, the mirror image. -/
theorem deriv_gatePot_of_gt (hε : 0 < ε) {u : ℝ} (h : ε < u) (h₁ : u ≤ 1) :
    deriv (gatePot ε) u = -(gateHeight / 4 * deriv (wallPot ε) (2 * ε - u)) := by
  rw [deriv_gatePot, deriv_gateBump_of_gt hε h,
    deriv_capPot_of_abs_le_one hε (abs_le.mpr ⟨by linarith, h₁⟩), zero_add]

/-- The gated potential vanishes on the flight region of a through edge. -/
theorem gatePot_of_mem (hε : 0 < ε) {u : ℝ} (h₁ : 2 * ε ≤ |u|) (h₂ : |u| ≤ 1) :
    gatePot ε u = 0 := by
  rw [gatePot, capPot_of_abs_le_one hε h₂]
  rcases le_or_gt 0 u with h | h
  · rw [gateBump_of_ge_pos hε (by rw [abs_of_nonneg h] at h₁; exact h₁), add_zero]
  · rw [gateBump_of_le_neg hε (by rw [abs_of_neg h] at h₁; linarith), add_zero]

/-! ### Global force bounds -/

/-- The gate force is globally bounded: the gate is `C²` and locally constant outside the compact
interval `[-2ε, 2ε]`. -/
theorem exists_bound_deriv_gateBump (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u, |deriv (gateBump ε) u| ≤ M := by
  have hcont : Continuous (deriv (gateBump ε)) :=
    (contDiff_gateBump ε (n := 2)).continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -(2 * ε)) (b := 2 * ε)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun u => ?_⟩
  rcases le_or_gt |u| (2 * ε) with h | h
  · have hmem : u ∈ Icc (-(2 * ε)) (2 * ε) := abs_le.mp h
    have := hC u hmem
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  · rcases le_or_gt 0 u with hu | hu
    · rw [deriv_gateBump_of_two_le hε (by rw [abs_of_nonneg hu] at h; linarith), abs_zero]
      exact le_max_right _ _
    · rw [deriv_gateBump_of_le_neg hε (by rw [abs_of_neg hu] at h; linarith), abs_zero]
      exact le_max_right _ _

theorem exists_bound_deriv_gatePot (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u, |deriv (gatePot ε) u| ≤ M := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_bound_deriv_capPot hε
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_bound_deriv_gateBump hε
  refine ⟨M₁ + M₂, by linarith, fun u => ?_⟩
  rw [deriv_gatePot]
  exact le_trans (abs_add_le _ _) (add_le_add (hM₁ u) (hM₂ u))

/-! ### The gated microscopic potential -/

/-- **The microscopic potential of the energy-gated thin three-channel network.**  It is obtained
from `microPot` by the single replacement `capPot ↦ gatePot` in the through-channel branch; in the
third-arm region it is *identical* to `microPot`. -/
noncomputable def gatePot2 (ε : ℝ) (x : ℝ × ℝ) : ℝ :=
  (1 - mixW ε x.2) * (wellPot ε x.2 + gatePot ε x.1)
    + mixW ε x.2 * (wellPot ε x.1 + armPot ε x.2)

theorem gatePot2_of_through (hε : 0 < ε) {x : ℝ × ℝ} (h : x.2 ≤ 3 * ε) :
    gatePot2 ε x = wellPot ε x.2 + gatePot ε x.1 := by
  rw [gatePot2, mixW_of_le hε h]
  ring

/-- **In the third arm the gated potential is the ungated one.**  The whole arm analysis of
`ArmDynamics.lean` therefore applies verbatim. -/
theorem gatePot2_of_arm (hε : 0 < ε) {x : ℝ × ℝ} (h : 6 * ε ≤ x.2) :
    gatePot2 ε x = armPot2 ε x := by
  rw [gatePot2, mixW_of_ge hε h, armPot2]
  ring

theorem gatePot2_eq_microPot_of_arm (hε : 0 < ε) {x : ℝ × ℝ} (h : 6 * ε ≤ x.2) :
    gatePot2 ε x = microPot ε x := by
  rw [gatePot2_of_arm hε h, microPot_of_arm hε h]

/-- **The interpolation zone is still inside the barrier.** -/
theorem gatePot2_ge_four_of_mid (hε : 0 < ε) {x : ℝ × ℝ} (h₁ : 3 * ε ≤ x.2)
    (h₂ : x.2 ≤ 6 * ε) : 4 ≤ gatePot2 ε x := by
  have hthrough : 4 ≤ wellPot ε x.2 + gatePot ε x.1 := by
    have hw : wellPot ε x.2 = 4 := by
      refine wellPot_of_two_le_abs hε ?_
      rw [abs_of_nonneg (by linarith)]
      linarith
    have := gatePot_nonneg ε x.1
    linarith
  have harm : 4 ≤ wellPot ε x.1 + armPot ε x.2 := by
    have := armPot_ge_of_le_six hε h₂
    have := wellPot_nonneg ε x.1
    linarith
  have hm0 := mixW_nonneg ε x.2
  have hm1 := mixW_le_one ε x.2
  rw [gatePot2]
  nlinarith

theorem gatePot2_nonneg (ε : ℝ) (x : ℝ × ℝ) : 0 ≤ gatePot2 ε x := by
  have h1 : 0 ≤ wellPot ε x.2 + gatePot ε x.1 :=
    add_nonneg (wellPot_nonneg _ _) (gatePot_nonneg _ _)
  have h2 : 0 ≤ wellPot ε x.1 + armPot ε x.2 :=
    add_nonneg (wellPot_nonneg _ _) (armPot_nonneg _ _)
  have hm0 := mixW_nonneg ε x.2
  have hm1 := mixW_le_one ε x.2
  rw [gatePot2]
  nlinarith

theorem contDiff_gatePot2 (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (gatePot2 ε) := by
  have hs : ContDiff ℝ n (fun x : ℝ × ℝ => x.2) := contDiff_snd
  have hf : ContDiff ℝ n (fun x : ℝ × ℝ => x.1) := contDiff_fst
  apply ContDiff.add
  · exact (contDiff_const.sub ((contDiff_mixW ε).comp hs)).mul
      (((contDiff_wellPot ε).comp hs).add ((contDiff_gatePot ε).comp hf))
  · exact ((contDiff_mixW ε).comp hs).mul
      (((contDiff_wellPot ε).comp hf).add ((contDiff_armPot ε).comp hs))

/-! ### The force field -/

/-- The force of the gated microscopic Hamiltonian. -/
noncomputable def gateForce (ε : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (-deriv (fun s => gatePot2 ε (s, x.2)) x.1, -deriv (fun s => gatePot2 ε (x.1, s)) x.2)

/-- **Exact separability in the through-channel region.** -/
theorem gateForce_of_through (hε : 0 < ε) {x : ℝ × ℝ} (h : x.2 < 3 * ε) :
    gateForce ε x = (-deriv (gatePot ε) x.1, -deriv (wellPot ε) x.2) := by
  have hfst : (fun s => gatePot2 ε (s, x.2)) = fun s => wellPot ε x.2 + gatePot ε s := by
    funext s
    exact gatePot2_of_through hε (x := (s, x.2)) h.le
  have hsnd : (fun s => gatePot2 ε (x.1, s)) =ᶠ[nhds x.2]
      fun s => wellPot ε s + gatePot ε x.1 := by
    filter_upwards [Iio_mem_nhds h] with s hs
    exact gatePot2_of_through hε (x := (x.1, s)) (le_of_lt hs)
  rw [gateForce, hfst, hsnd.deriv_eq]
  congr 1
  · rw [deriv_const_add']
  · rw [deriv_add_const']

/-- **Exact separability in the third-arm region** — the same statement as for `microPot`. -/
theorem gateForce_of_arm (hε : 0 < ε) {x : ℝ × ℝ} (h : 6 * ε < x.2) :
    gateForce ε x = (-deriv (wellPot ε) x.1, -deriv (armPot ε) x.2) := by
  have hfst : (fun s => gatePot2 ε (s, x.2)) = fun s => wellPot ε s + armPot ε x.2 := by
    funext s
    exact gatePot2_of_arm hε (x := (s, x.2)) h.le
  have hsnd : (fun s => gatePot2 ε (x.1, s)) =ᶠ[nhds x.2]
      fun s => wellPot ε x.1 + armPot ε s := by
    filter_upwards [Ioi_mem_nhds h] with s hs
    have := gatePot2_of_arm hε (x := (x.1, s)) (le_of_lt hs)
    rw [this, armPot2]
  rw [gateForce, hfst, hsnd.deriv_eq]
  congr 1
  · rw [deriv_add_const']
  · rw [deriv_const_add']

end HamiltonianMetricGraphs
