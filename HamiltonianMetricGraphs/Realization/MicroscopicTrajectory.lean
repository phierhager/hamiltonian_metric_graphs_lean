/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.MicroscopicPotential
import HamiltonianMetricGraphs.Realization.GlobalFlow
import HamiltonianMetricGraphs.Realization.Newton1D
import HamiltonianMetricGraphs.Realization.IntervalEstimates

/-!
# Trajectories of the microscopic Hamiltonian

We construct genuine trajectories of the two-dimensional microscopic Hamiltonian

  `H_ε(x, p) = ½|p|² + microPot ε x`

for well-prepared initial data, and establish the two facts the realization theorem needs:

* **Transverse confinement.**  The transverse energy `½p_w² + wellPot ε w` is exactly conserved,
  because in the through-channel region the potential is an exact sum.  A transverse energy below
  the wall height `4` therefore keeps the trajectory in the tube `|w| < 2ε` — width `O(ε)`.
* **Exactly free longitudinal motion.**  On the closed edge `|u| ≤ 1` the longitudinal potential
  vanishes identically, so `p_u` is exactly constant there and `u' = p_u`: the projected motion
  is *exactly* the graph dynamics of the zero potential, i.e. the ODE error is `0`, not merely
  small.

The construction is by *pairing two one-dimensional motions*: since the potential is an exact sum
in the through-channel region, the pair of a longitudinal and a transverse one-dimensional
solution is a solution of the two-dimensional system.  This avoids any two-dimensional existence
theory.  One-dimensional existence is obtained from `exists_integralCurve_Icc` after truncating
the momentum, which is legitimate because the momentum is a priori bounded by
`|p₀| + R·T` along any solution.
-/

namespace HamiltonianMetricGraphs

open Set

/-! ### A momentum cutoff -/

/-- A smooth momentum cutoff: `1` for `|v| ≤ P` and `0` for `|v| ≥ 2P`. -/
noncomputable def momCut (P v : ℝ) : ℝ := 1 - plateau (P ^ 2) (4 * P ^ 2) (v ^ 2)

theorem momCut_nonneg (P v : ℝ) : 0 ≤ momCut P v := by
  have := plateau_le_one (P ^ 2) (4 * P ^ 2) (v ^ 2)
  rw [momCut]; linarith

theorem momCut_le_one (P v : ℝ) : momCut P v ≤ 1 := by
  have := plateau_nonneg (P ^ 2) (4 * P ^ 2) (v ^ 2)
  rw [momCut]; linarith

theorem momCut_of_abs_le {P v : ℝ} (hP : 0 < P) (h : |v| ≤ P) : momCut P v = 1 := by
  have hsq : v ^ 2 ≤ P ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
  rw [momCut, plateau_of_le (by nlinarith) hsq, sub_zero]

theorem momCut_of_two_le_abs {P v : ℝ} (hP : 0 < P) (h : 2 * P ≤ |v|) : momCut P v = 0 := by
  have hsq : 4 * P ^ 2 ≤ v ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
  rw [momCut, plateau_of_ge (by nlinarith) hsq, sub_self]

theorem abs_momCut_mul_le {P : ℝ} (hP : 0 < P) (v : ℝ) : |momCut P v * v| ≤ 2 * P := by
  rcases le_or_gt |v| (2 * P) with h | h
  · rw [abs_mul, abs_of_nonneg (momCut_nonneg P v)]
    calc momCut P v * |v| ≤ 1 * |v| :=
          mul_le_mul_of_nonneg_right (momCut_le_one P v) (abs_nonneg v)
      _ = |v| := one_mul _
      _ ≤ 2 * P := h
  · rw [momCut_of_two_le_abs hP h.le, zero_mul, abs_zero]
    linarith

theorem contDiff_momCut (P : ℝ) {n : ℕ∞} : ContDiff ℝ n (momCut P) :=
  contDiff_const.sub ((contDiff_plateau _ _).comp (contDiff_id.pow 2))

/-! ### One-dimensional existence with a bounded force -/

/-- **Existence of a one-dimensional Newtonian motion.**  A `C²` potential with a globally
bounded force has a solution of `q' = p`, `p' = -Φ'(q)` on every interval `[0, T]`, through every
initial state.  The momentum cutoff used in the proof is inactive along the solution, because the
momentum grows at most linearly. -/
theorem exists_newton1D {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ y, |deriv Φ y| ≤ R) (q₀ p₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ x p : ℝ → ℝ, x 0 = q₀ ∧ p 0 = p₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt x (p t) (Icc (0 : ℝ) T) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt p (-deriv Φ (x t)) (Icc (0 : ℝ) T) t) := by
  classical
  set P : ℝ := |p₀| + R * T + 1 with hPdef
  have hPpos : 0 < P := by
    have := abs_nonneg p₀
    have : 0 ≤ R * T := mul_nonneg hR0 hT
    rw [hPdef]; linarith [abs_nonneg p₀]
  have hderivΦ : ContDiff ℝ 1 (deriv Φ) := by
    have h : ContDiff ℝ (1 + 1 : ℕ) Φ := by norm_num at hΦ ⊢; exact hΦ
    exact (contDiff_succ_iff_deriv.mp h).2.2
  -- the truncated field
  set f : ℝ × ℝ → ℝ × ℝ := fun z => (momCut P z.2 * z.2, -deriv Φ z.1) with hf
  have hfC : ContDiff ℝ 1 f := by
    apply ContDiff.prodMk
    · exact ((contDiff_momCut P).comp contDiff_snd).mul contDiff_snd
    · exact (hderivΦ.comp contDiff_fst).neg
  have hfb : ∀ z : ℝ × ℝ, ‖f z‖ ≤ 2 * P + R := by
    intro z
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    apply max_le
    · have := abs_momCut_mul_le hPpos z.2; linarith
    · have := hR z.1; rw [abs_neg]; linarith [abs_nonneg (deriv Φ z.1)]
  obtain ⟨α, hα0, hα⟩ :=
    exists_integralCurve_Icc hfC (by linarith : (0 : ℝ) ≤ 2 * P + R) hfb (q₀, p₀) hT
  refine ⟨fun t => (α t).1, fun t => (α t).2, show (α 0).1 = q₀ by rw [hα0],
    show (α 0).2 = p₀ by rw [hα0], ?_, ?_⟩
  · -- the momentum stays below the cutoff, so the position equation is the true one
    have hpderiv : ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => (α s).2) (-deriv Φ (α t).1) (Icc (0 : ℝ) T) t := by
      intro t ht
      have := (hα t ht).snd_comp
      simpa [hf] using this
    have hbound : ∀ t ∈ Icc (0 : ℝ) T, |(α t).2| ≤ |p₀| + R * T := by
      intro t ht
      have hdrift := abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le
        (f := fun s => (α s).2) (f' := fun s => -deriv Φ (α s).1) (C := R)
        hpderiv (fun u _ => by rw [abs_neg]; exact hR _) (left_mem_Icc.mpr hT) ht ht.1
      have h0 : (α 0).2 = p₀ := by rw [hα0]
      rw [h0] at hdrift
      have h1 : |(α t).2| ≤ |(α t).2 - p₀| + |p₀| := by
        calc |(α t).2| = |((α t).2 - p₀) + p₀| := by ring_nf
          _ ≤ |(α t).2 - p₀| + |p₀| := abs_add_le _ _
      have h2 : R * (t - 0) ≤ R * T := by
        apply mul_le_mul_of_nonneg_left _ hR0
        linarith [ht.2, ht.1]
      linarith
    intro t ht
    have hcut : momCut P (α t).2 = 1 := by
      refine momCut_of_abs_le hPpos ?_
      have := hbound t ht
      rw [hPdef]; linarith
    have := (hα t ht).fst_comp
    simp only [hf] at this
    rwa [hcut, one_mul] at this
  · intro t ht
    have := (hα t ht).snd_comp
    simpa [hf] using this

/-! ### The two-dimensional microscopic trajectory -/

variable {ε : ℝ}

/-- **A microscopic trajectory of the thin network.**  For well-prepared initial data — inside
the tube, with transverse energy below the wall height — there is a genuine trajectory of the
two-dimensional Hamiltonian `H_ε = ½|p|² + microPot ε` on `[0, T]`, and along it

* the transverse coordinate stays in the tube `|w| < 2ε` (thin-tube confinement), and
* the longitudinal pair solves the one-dimensional system of the cap potential exactly.

Both statements are proved, not assumed. -/
theorem exists_microTrajectory (hε : 0 < ε) (u₀ pu₀ w₀ pw₀ : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hprep : pw₀ ^ 2 / 2 + wellPot ε w₀ < 4) :
    ∃ u pu w pw : ℝ → ℝ,
      u 0 = u₀ ∧ pu 0 = pu₀ ∧ w 0 = w₀ ∧ pw 0 = pw₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T, |w t| < 2 * ε) ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (pu t) (Icc (0 : ℝ) T) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt pu (-deriv (capPot ε) (u t)) (Icc (0 : ℝ) T) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => (u s, w s)) (pu t, pw t) (Icc (0 : ℝ) T) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => (pu s, pw s)) (microForce ε (u t, w t)) (Icc (0 : ℝ) T) t) := by
  obtain ⟨Rc, hRc0, hRc⟩ := exists_bound_deriv_capPot hε
  obtain ⟨Rw, hRw0, hRw⟩ := exists_bound_deriv_wellPot hε
  obtain ⟨u, pu, hu0, hpu0, hu, hpu⟩ :=
    exists_newton1D (contDiff_capPot ε (n := 2)) hRc0 hRc u₀ pu₀ hT
  obtain ⟨w, pw, hw0, hpw0, hw, hpw⟩ :=
    exists_newton1D (contDiff_wellPot ε (n := 2)) hRw0 hRw w₀ pw₀ hT
  -- transverse confinement, from exact conservation of the transverse energy
  have hconf : ∀ t ∈ Icc (0 : ℝ) T, |w t| < 2 * ε := by
    intro t ht
    have hS : ∀ z ∈ {z : ℝ | 2 * ε ≤ |z|}, (4 : ℝ) ≤ wellPot ε z := by
      intro z hz
      rw [wellPot_of_two_le_abs hε hz]
    have hE : energy1D (wellPot ε) (w 0) (pw 0) < 4 := by
      rw [energy1D, hw0, hpw0]
      exact hprep
    have := not_mem_of_energy_lt (contDiff_wellPot ε (n := 1)) hS hw hpw hE t ht
    by_contra hcon
    rw [not_lt] at hcon
    exact this hcon
  refine ⟨u, pu, w, pw, hu0, hpu0, hw0, hpw0, hconf, hu, hpu, ?_, ?_⟩
  · intro t ht
    exact (hu t ht).prodMk (hw t ht)
  · intro t ht
    have hthrough : (u t, w t).2 < 3 * ε := by
      have h1 := hconf t ht
      have h2 : w t ≤ |w t| := le_abs_self _
      simp only
      linarith
    rw [microForce_of_through hε hthrough]
    exact (hpu t ht).prodMk (hpw t ht)

end HamiltonianMetricGraphs
