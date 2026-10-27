/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import Mathlib

/-!
# Smooth plateau functions

To build an *explicit* smooth potential on a metric graph we need smooth bump/plateau shapes:
functions that vanish identically to the left of a point `a`, equal `1` identically to the right
of a point `b`, and interpolate monotonically in between.  Mathlib's `Real.smoothTransition`
provides the model case `a = 0`, `b = 1`; here we rescale it to an arbitrary interval and record
the properties needed downstream:

* `plateau_of_le`, `plateau_of_ge` — the two flat pieces;
* `plateau_nonneg`, `plateau_le_one`, `plateau_monotone` — the shape;
* `contDiff_plateau` — smoothness of every order;
* `exists_bound_deriv_smoothTransition`, `exists_bound_deriv_plateau` — a *global* Lipschitz
  bound.  Mathlib has no closed formula for `deriv Real.smoothTransition`, so the bound is
  obtained qualitatively: the derivative is continuous, hence bounded on the compact set
  `Set.Icc 0 1`, and it vanishes off `[0, 1]` because `Real.smoothTransition` is locally
  constant there.
-/

open Set Filter
open scoped Topology

namespace HamiltonianMetricGraphs

/-- A smooth step: `0` for `t ≤ a`, `1` for `t ≥ b`, monotone in between. -/
noncomputable def plateau (a b t : ℝ) : ℝ := Real.smoothTransition ((b - a)⁻¹ * (t - a))

/-- Below the left endpoint the plateau vanishes. -/
theorem plateau_of_le {a b t : ℝ} (hab : a < b) (h : t ≤ a) : plateau a b t = 0 := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hinv : (0 : ℝ) ≤ (b - a)⁻¹ := (inv_pos.mpr hba).le
  have hle : (b - a)⁻¹ * (t - a) ≤ (b - a)⁻¹ * 0 :=
    mul_le_mul_of_nonneg_left (by linarith) hinv
  exact Real.smoothTransition.zero_of_nonpos (by simpa using hle)

/-- Above the right endpoint the plateau equals `1`. -/
theorem plateau_of_ge {a b t : ℝ} (hab : a < b) (h : b ≤ t) : plateau a b t = 1 := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hinv : (0 : ℝ) ≤ (b - a)⁻¹ := (inv_pos.mpr hba).le
  have hcancel : (b - a)⁻¹ * (b - a) = 1 := inv_mul_cancel₀ (ne_of_gt hba)
  have hle : (b - a)⁻¹ * (b - a) ≤ (b - a)⁻¹ * (t - a) :=
    mul_le_mul_of_nonneg_left (by linarith) hinv
  exact Real.smoothTransition.one_of_one_le (by linarith)

/-- A plateau is nonnegative. -/
theorem plateau_nonneg (a b t : ℝ) : 0 ≤ plateau a b t :=
  Real.smoothTransition.nonneg _

/-- A plateau is bounded above by `1`. -/
theorem plateau_le_one (a b t : ℝ) : plateau a b t ≤ 1 :=
  Real.smoothTransition.le_one _

/-- A plateau with `a < b` is monotone. -/
theorem plateau_monotone {a b : ℝ} (hab : a < b) : Monotone (plateau a b) := by
  have hinv : (0 : ℝ) ≤ (b - a)⁻¹ := (inv_pos.mpr (sub_pos.mpr hab)).le
  intro s t hst
  exact Real.smoothTransition.monotone (mul_le_mul_of_nonneg_left (by linarith) hinv)

/-- A plateau is `C^n` for every `n`. -/
theorem contDiff_plateau (a b : ℝ) {n : ℕ∞} : ContDiff ℝ n (plateau a b) := by
  have h : ContDiff ℝ (n : WithTop ℕ∞) fun t : ℝ => (b - a)⁻¹ * (t - a) :=
    contDiff_const.mul (contDiff_id.sub contDiff_const)
  exact Real.smoothTransition.contDiff.comp h

section DerivBounds

/-- `Real.smoothTransition` is differentiable. -/
theorem differentiable_smoothTransition : Differentiable ℝ Real.smoothTransition :=
  (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)

/-- The derivative of `Real.smoothTransition` is continuous. -/
theorem continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

/-- To the left of `0` the transition is locally constant, so its derivative vanishes. -/
theorem deriv_smoothTransition_of_neg {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds (show x ∈ Iio (0 : ℝ) from hx)] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  rw [h.deriv_eq]
  simp

/-- To the right of `1` the transition is locally constant, so its derivative vanishes. -/
theorem deriv_smoothTransition_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi (1 : ℝ) from hx)] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
  rw [h.deriv_eq]
  simp

/-- The derivative of `Real.smoothTransition` is globally bounded. -/
theorem exists_bound_deriv_smoothTransition :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ M := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (f := deriv Real.smoothTransition) continuous_deriv_smoothTransition.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  rcases lt_or_ge x 0 with hx | hx
  · rw [deriv_smoothTransition_of_neg hx]
    simp
  · rcases le_or_gt x 1 with hx1 | hx1
    · have := hC x ⟨hx, hx1⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left C 0)
    · rw [deriv_smoothTransition_of_one_lt hx1]
      simp

/-- The chain rule for a plateau.  This holds for all `a b`, including the degenerate case
`b = a`, where `(b - a)⁻¹ = 0` and `plateau a a` is the constant function `0`. -/
theorem deriv_plateau (a b t : ℝ) :
    deriv (plateau a b) t
      = deriv Real.smoothTransition ((b - a)⁻¹ * (t - a)) * (b - a)⁻¹ := by
  have hg : HasDerivAt (fun s : ℝ => (b - a)⁻¹ * (s - a)) (b - a)⁻¹ t := by
    simpa using HasDerivAt.const_mul (b - a)⁻¹ ((hasDerivAt_id t).sub_const a)
  have hf : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((b - a)⁻¹ * (t - a))) ((b - a)⁻¹ * (t - a)) :=
    (differentiable_smoothTransition _).hasDerivAt
  exact (hf.comp t hg).deriv

/-- The derivative of a plateau is globally bounded. -/
theorem exists_bound_deriv_plateau (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv (plateau a b) t| ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_bound_deriv_smoothTransition
  refine ⟨M * |(b - a)⁻¹|, mul_nonneg hM (abs_nonneg _), fun t => ?_⟩
  rw [deriv_plateau, abs_mul]
  exact mul_le_mul_of_nonneg_right (hbound _) (abs_nonneg _)

end DerivBounds

end HamiltonianMetricGraphs
