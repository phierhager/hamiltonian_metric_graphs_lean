/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.SmoothPlateau

/-!
# The barrier and well profiles of the microscopic model

The microscopic potential is assembled from two fixed (scale-independent) one-dimensional
profiles.

* `barrierProfile s = 4e · exp(-1/s)` for `s > 0` and `0` for `s ≤ 0` — the reflecting barrier
  placed at every vertex.  It is built from Mathlib's `expNegInvGlue`, the one smooth one-sided
  profile in Mathlib with an **explicit derivative formula**
  (`expNegInvGlue' s = s⁻² · expNegInvGlue s`).  That formula is what makes the reflection
  analysis possible: it yields an explicit positive lower bound for the slope on `[1/4, 1]`, hence
  an explicit bound on the time a particle spends turning around, hence a vanishing dwell time.
  A profile built from `Real.smoothTransition` would not do, because Mathlib proves nothing about
  its derivative.

* `wellProfile s = 4 · plateau 1 4 (s²)` — the transverse confining wall of a tube: it vanishes on
  the core `|s| ≤ 1` and equals `4` outside `|s| ≥ 2`, so a particle whose transverse energy is
  below `4` stays in `|s| < 2`.

The numerical constants are chosen for the energy window `K⋆ = [1/2, 2]`:

* `barrierProfile 1 = 4 > 2 ≥ E`, so a particle never reaches `s = 1`
  (`barrierProfile_ge_of_one_le`);
* `barrierProfile s ≤ 1/4 ≤ E/2` for `s ≤ 1/4`, so while approaching the barrier the particle
  keeps at least half its kinetic energy (`barrierProfile_le_quarter`);
* `deriv barrierProfile ≥ 4 e⁻³ > 0` on `[1/4, 1]` (`deriv_barrierProfile_ge`) — the explicit
  deceleration used for the turning-time bound.
-/

namespace HamiltonianMetricGraphs

open Real Set

/-! ### The one-sided smooth glue -/

/-- Mathlib's one-sided smooth glue `s ↦ exp (-1/s)`, renamed for readability. -/
noncomputable def glue (s : ℝ) : ℝ := expNegInvGlue s

theorem glue_of_nonpos {s : ℝ} (h : s ≤ 0) : glue s = 0 := expNegInvGlue.zero_of_nonpos h

theorem glue_pos_of_pos {s : ℝ} (h : 0 < s) : 0 < glue s := expNegInvGlue.pos_of_pos h

theorem glue_nonneg (s : ℝ) : 0 ≤ glue s := expNegInvGlue.nonneg s

theorem glue_monotone : Monotone glue := expNegInvGlue.monotone

theorem contDiff_glue {n : ℕ∞} : ContDiff ℝ n glue := expNegInvGlue.contDiff

/-- The explicit value of the glue at a positive argument. -/
theorem glue_of_pos {s : ℝ} (h : 0 < s) : glue s = exp (-s⁻¹) := by
  change expNegInvGlue s = _
  rw [expNegInvGlue, if_neg (not_le.mpr h)]

theorem glue_le_one (s : ℝ) : glue s ≤ 1 := by
  rcases le_or_gt s 0 with h | h
  · rw [glue_of_nonpos h]; norm_num
  · rw [glue_of_pos h, Real.exp_le_one_iff, neg_nonpos]
    exact (inv_pos.mpr h).le

/-- **The explicit derivative of the glue.**  Mathlib proves it for `expNegInvGlue` with the
constant polynomial `1`.  This is the fact that makes the reflection analysis possible. -/
theorem hasDerivAt_glue (s : ℝ) : HasDerivAt glue ((s ^ 2)⁻¹ * glue s) s := by
  unfold glue
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) s
  simpa using h

theorem deriv_glue (s : ℝ) : deriv glue s = (s ^ 2)⁻¹ * glue s := (hasDerivAt_glue s).deriv

/-- On `[1/4, ∞)` the glue is bounded below by `e⁻⁴`. -/
theorem glue_ge_of_quarter_le {s : ℝ} (h : 1 / 4 ≤ s) : exp (-4) ≤ glue s := by
  have hs : (0 : ℝ) < s := by linarith
  have hc : s⁻¹ * s = 1 := inv_mul_cancel₀ (ne_of_gt hs)
  have hp : 0 < s⁻¹ := inv_pos.mpr hs
  have hinv : s⁻¹ ≤ 4 := by nlinarith
  rw [glue_of_pos hs, Real.exp_le_exp]
  linarith

/-- On `(-∞, 1/4]` the glue is bounded above by `e⁻⁴`. -/
theorem glue_le_of_le_quarter {s : ℝ} (h : s ≤ 1 / 4) : glue s ≤ exp (-4) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [glue_of_nonpos hs]
    exact (Real.exp_pos _).le
  · have hc : s⁻¹ * s = 1 := inv_mul_cancel₀ (ne_of_gt hs)
    have hp : 0 < s⁻¹ := inv_pos.mpr hs
    have hinv : (4 : ℝ) ≤ s⁻¹ := by nlinarith
    rw [glue_of_pos hs, Real.exp_le_exp]
    linarith

/-! ### The barrier profile -/

/-- The reflecting barrier profile, normalised so that `barrierProfile 1 = 4`. -/
noncomputable def barrierProfile (s : ℝ) : ℝ := 4 * exp 1 * glue s

/-- The derivative of the barrier profile, explicitly. -/
theorem hasDerivAt_barrierProfile (s : ℝ) :
    HasDerivAt barrierProfile (4 * exp 1 * ((s ^ 2)⁻¹ * glue s)) s :=
  (hasDerivAt_glue s).const_mul (4 * exp 1)

theorem deriv_barrierProfile (s : ℝ) :
    deriv barrierProfile s = 4 * exp 1 * ((s ^ 2)⁻¹ * glue s) :=
  (hasDerivAt_barrierProfile s).deriv

theorem barrierProfile_of_nonpos {s : ℝ} (h : s ≤ 0) : barrierProfile s = 0 := by
  rw [barrierProfile, glue_of_nonpos h, mul_zero]

theorem barrierProfile_nonneg (s : ℝ) : 0 ≤ barrierProfile s := by
  have := glue_nonneg s
  rw [barrierProfile]
  positivity

theorem barrierProfile_monotone : Monotone barrierProfile := by
  intro a b hab
  have h : (0 : ℝ) ≤ 4 * exp 1 := by positivity
  exact mul_le_mul_of_nonneg_left (glue_monotone hab) h

theorem contDiff_barrierProfile {n : ℕ∞} : ContDiff ℝ n barrierProfile :=
  contDiff_const.mul contDiff_glue

/-- The barrier profile is globally bounded. -/
theorem barrierProfile_le (s : ℝ) : barrierProfile s ≤ 4 * exp 1 := by
  have h := glue_le_one s
  have hp : (0 : ℝ) ≤ 4 * exp 1 := by positivity
  calc barrierProfile s = 4 * exp 1 * glue s := rfl
    _ ≤ 4 * exp 1 * 1 := mul_le_mul_of_nonneg_left h hp
    _ = 4 * exp 1 := by ring

/-- `barrierProfile 1 = 4`: the barrier reaches the confining height at `s = 1`. -/
theorem barrierProfile_one : barrierProfile 1 = 4 := by
  rw [barrierProfile, glue_of_pos one_pos, inv_one, mul_assoc, ← Real.exp_add]
  norm_num

/-- **Confinement height.**  Beyond `s = 1` the barrier is at least `4`, exceeding every energy
in the window `K⋆ = [1/2, 2]`. -/
theorem barrierProfile_ge_of_one_le {s : ℝ} (h : 1 ≤ s) : 4 ≤ barrierProfile s := by
  rw [← barrierProfile_one]
  exact barrierProfile_monotone h

/-- A numerical bound on `e³`, used to calibrate the barrier. -/
theorem sixteen_le_exp_three : (16 : ℝ) ≤ exp 3 := by
  have h : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
  have h3 : exp 3 = exp 1 * (exp 1 * exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (1 : ℝ)]

theorem four_div_exp_three : 4 * exp 1 * exp (-4) = 4 / exp 3 := by
  rw [show (-4 : ℝ) = -(3 : ℝ) + -1 by norm_num, Real.exp_add, Real.exp_neg, Real.exp_neg]
  field_simp

/-- **Low barrier near the foot.**  On `s ≤ 1/4` the barrier is at most `1/4`, which is at most
half of every energy in `K⋆`.  This keeps the particle fast while it approaches the barrier. -/
theorem barrierProfile_le_quarter {s : ℝ} (h : s ≤ 1 / 4) : barrierProfile s ≤ 1 / 4 := by
  have hg := glue_le_of_le_quarter h
  have hpos : (0 : ℝ) ≤ 4 * exp 1 := by positivity
  calc barrierProfile s = 4 * exp 1 * glue s := rfl
    _ ≤ 4 * exp 1 * exp (-4) := mul_le_mul_of_nonneg_left hg hpos
    _ = 4 / exp 3 := four_div_exp_three
    _ ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (Real.exp_pos 3) (by norm_num)]
        linarith [sixteen_le_exp_three]

/-- **Explicit deceleration.**  On `[1/4, 1]` the slope of the barrier is at least `4 e⁻³ > 0`.
This is the bound that makes the turning time explicit. -/
theorem deriv_barrierProfile_ge {s : ℝ} (h₁ : 1 / 4 ≤ s) (h₂ : s ≤ 1) :
    4 / exp 3 ≤ deriv barrierProfile s := by
  have hs : (0 : ℝ) < s := by linarith
  have hsq : (0 : ℝ) < s ^ 2 := by positivity
  have hc : (s ^ 2)⁻¹ * s ^ 2 = 1 := inv_mul_cancel₀ (ne_of_gt hsq)
  have hp : 0 < (s ^ 2)⁻¹ := inv_pos.mpr hsq
  have hs1 : s ^ 2 ≤ 1 := by nlinarith
  have hinv : (1 : ℝ) ≤ (s ^ 2)⁻¹ := by nlinarith
  have hg := glue_ge_of_quarter_le h₁
  have hgn : 0 ≤ glue s := glue_nonneg s
  have hpos : (0 : ℝ) ≤ 4 * exp 1 := by positivity
  rw [deriv_barrierProfile]
  calc 4 / exp 3 = 4 * exp 1 * exp (-4) := four_div_exp_three.symm
    _ ≤ 4 * exp 1 * glue s := mul_le_mul_of_nonneg_left hg hpos
    _ ≤ 4 * exp 1 * ((s ^ 2)⁻¹ * glue s) := by
        apply mul_le_mul_of_nonneg_left _ hpos
        nlinarith [mul_nonneg (sub_nonneg.mpr hinv) hgn]

theorem deriv_barrierProfile_nonneg (s : ℝ) : 0 ≤ deriv barrierProfile s := by
  have h := glue_nonneg s
  rw [deriv_barrierProfile]
  have : (0 : ℝ) ≤ (s ^ 2)⁻¹ := by positivity
  positivity

/-- The slope of the barrier profile is globally bounded. -/
theorem exists_bound_deriv_barrierProfile :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, |deriv barrierProfile s| ≤ M := by
  have hcont : Continuous (deriv barrierProfile) :=
    (contDiff_barrierProfile (n := 2)).continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C (4 * exp 1), le_trans (by positivity) (le_max_right _ _), fun s => ?_⟩
  rcases le_or_gt s 0 with h0 | h0
  · rw [deriv_barrierProfile, glue_of_nonpos h0, mul_zero, mul_zero, abs_zero]
    exact le_trans (by positivity) (le_max_right C (4 * exp 1))
  · rcases le_or_gt s 1 with h1 | h1
    · have := hC s ⟨h0.le, h1⟩
      rw [Real.norm_eq_abs] at this
      exact le_trans this (le_max_left _ _)
    · have hsq : (0 : ℝ) < s ^ 2 := by positivity
      have hc : (s ^ 2)⁻¹ * s ^ 2 = 1 := inv_mul_cancel₀ (ne_of_gt hsq)
      have hp : 0 < (s ^ 2)⁻¹ := inv_pos.mpr hsq
      have hs1 : (1 : ℝ) ≤ s ^ 2 := by nlinarith
      have hinv : (s ^ 2)⁻¹ ≤ 1 := by nlinarith
      have hg := glue_le_one s
      have hgn := glue_nonneg s
      have hpos : (0 : ℝ) ≤ 4 * exp 1 := by positivity
      rw [deriv_barrierProfile, abs_of_nonneg (by positivity)]
      refine le_trans ?_ (le_max_right C (4 * exp 1))
      calc 4 * exp 1 * ((s ^ 2)⁻¹ * glue s) ≤ 4 * exp 1 * 1 := by
            apply mul_le_mul_of_nonneg_left _ hpos
            nlinarith
        _ = 4 * exp 1 := by ring

/-! ### The transverse well profile -/

/-- The transverse confining wall: it vanishes on the core `|s| ≤ 1` and equals `4` outside
`|s| ≥ 2`. -/
noncomputable def wellProfile (s : ℝ) : ℝ := 4 * plateau 1 4 (s ^ 2)

theorem wellProfile_nonneg (s : ℝ) : 0 ≤ wellProfile s := by
  have := plateau_nonneg 1 4 (s ^ 2)
  rw [wellProfile]
  positivity

theorem wellProfile_le (s : ℝ) : wellProfile s ≤ 4 := by
  have := plateau_le_one 1 4 (s ^ 2)
  rw [wellProfile]
  linarith

/-- The tube core is flat: there is no transverse force for `|s| ≤ 1`. -/
theorem wellProfile_of_abs_le_one {s : ℝ} (h : |s| ≤ 1) : wellProfile s = 0 := by
  have hs : s ^ 2 ≤ 1 := by nlinarith [sq_abs s, abs_nonneg s]
  rw [wellProfile, plateau_of_le (by norm_num) hs, mul_zero]

/-- Outside `|s| ≥ 2` the wall is at full height. -/
theorem wellProfile_of_two_le_abs {s : ℝ} (h : 2 ≤ |s|) : wellProfile s = 4 := by
  have hs : (4 : ℝ) ≤ s ^ 2 := by nlinarith [sq_abs s, abs_nonneg s]
  rw [wellProfile, plateau_of_ge (by norm_num) hs, mul_one]

/-- **Transverse confinement.**  A transverse energy below `4` forces `|s| < 2`. -/
theorem abs_lt_two_of_wellProfile_lt {s : ℝ} (h : wellProfile s < 4) : |s| < 2 := by
  by_contra hcon
  rw [not_lt] at hcon
  rw [wellProfile_of_two_le_abs hcon] at h
  exact lt_irrefl _ h

theorem contDiff_wellProfile {n : ℕ∞} : ContDiff ℝ n wellProfile := by
  apply contDiff_const.mul
  exact (contDiff_plateau 1 4).comp (contDiff_id.pow 2)

/-- The slope of the well profile is globally bounded: it is continuous and vanishes outside the
compact interval `[-2, 2]`, where the profile is locally constant. -/
theorem exists_bound_deriv_wellProfile :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, |deriv wellProfile s| ≤ M := by
  have hcont : Continuous (deriv wellProfile) :=
    (contDiff_wellProfile (n := 2)).continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun s => ?_⟩
  rcases le_or_gt |s| 2 with h | h
  · have hmem : s ∈ Icc (-2 : ℝ) 2 := abs_le.mp h
    have := hC s hmem
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  · have hopen : {y : ℝ | 2 < |y|} ∈ nhds s :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds h
    have heq : wellProfile =ᶠ[nhds s] fun _ => (4 : ℝ) := by
      filter_upwards [hopen] with y hy
      exact wellProfile_of_two_le_abs (le_of_lt hy)
    rw [heq.deriv_eq, deriv_const, abs_zero]
    exact le_max_right _ _

end HamiltonianMetricGraphs
