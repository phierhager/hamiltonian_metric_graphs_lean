/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalNetwork
import HamiltonianMetricGraphs.Realization.MicroscopicTrajectory

/-!
# Trajectories of the universal thin network

The microscopic Hamiltonian of the universal model is

  `H_ε(x, p) = ½ |p|² + netPot ε m Λ x`   on   `ℝ² × ℝ²`.

This file constructs genuine solutions of Hamilton's equations for it and proves the two facts
which make the projection to the graph exact:

* **thin-tube confinement**: a particle prepared inside the tube of corridor `i` with transverse
  energy below the wall height `4` stays in `|w - i| < 2ε` forever (`exists_netTrajectory`);
* **exact separability**: on that tube the potential is the exact sum of the transverse well and
  the corridor potential, so the longitudinal pair `(u, p_u)` solves the one-dimensional corridor
  system *exactly* — the projected ODE error is `0`, not `O(ε)` (`corridorSolution_of_net`).

Nothing here is assumed: both statements are derived from the explicit smooth potential.
-/

namespace HamiltonianMetricGraphs

open Set Real

variable {ε : ℝ} {m : ℕ}

/-! ### The transverse well of corridor `i` -/

/-- The transverse well of the tube of corridor `i`, which sits at height `w = i`. -/
noncomputable def wellShift (ε : ℝ) (i : ℕ) (z : ℝ) : ℝ := wellPot ε (z - i)

theorem contDiff_wellShift (ε : ℝ) (i : ℕ) {n : ℕ∞} : ContDiff ℝ n (wellShift ε i) :=
  (contDiff_wellPot ε).comp (contDiff_id.sub contDiff_const)

theorem hasDerivAt_wellShift (ε : ℝ) (i : ℕ) (z : ℝ) :
    HasDerivAt (wellShift ε i) (deriv (wellPot ε) (z - (i : ℝ))) z := by
  have h1 : HasDerivAt (fun s : ℝ => s - (i : ℝ)) 1 z := by
    simpa using (hasDerivAt_id z).sub_const ((i : ℝ))
  have h2 : HasDerivAt (wellPot ε) (deriv (wellPot ε) (z - (i : ℝ))) (z - (i : ℝ)) :=
    ((contDiff_wellPot ε (n := 1)).differentiable (by norm_num) _).hasDerivAt
  have h3 := HasDerivAt.comp z h2 h1
  rw [mul_one] at h3
  exact h3

theorem deriv_wellShift (ε : ℝ) (i : ℕ) (z : ℝ) :
    deriv (wellShift ε i) z = deriv (wellPot ε) (z - (i : ℝ)) :=
  (hasDerivAt_wellShift ε i z).deriv

theorem exists_bound_deriv_wellShift (hε : 0 < ε) (i : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z, |deriv (wellShift ε i) z| ≤ R := by
  obtain ⟨R, hR0, hR⟩ := exists_bound_deriv_wellPot hε
  exact ⟨R, hR0, fun z => by rw [deriv_wellShift]; exact hR _⟩

theorem wellShift_of_two_le_abs (hε : 0 < ε) {i : ℕ} {z : ℝ} (h : 2 * ε ≤ |z - (i : ℝ)|) :
    wellShift ε i z = 4 := wellPot_of_two_le_abs hε h

theorem wellShift_of_abs_le (hε : 0 < ε) {i : ℕ} {z : ℝ} (h : |z - (i : ℝ)| ≤ ε) :
    wellShift ε i z = 0 := wellPot_of_abs_le hε h

/-! ### The force of the network -/

/-- The force of the universal microscopic Hamiltonian, given componentwise by the two partial
derivatives.  Together with `x' = p` this is Hamilton's equations for
`H_ε(x, p) = ½ |p|² + netPot ε m Λ x`. -/
noncomputable def netForce (ε : ℝ) (m : ℕ) (Λ : Fin m → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (-deriv (fun s => netPot ε m Λ (s, x.2)) x.1, -deriv (fun s => netPot ε m Λ (x.1, s)) x.2)

/-- **The force is separable inside a corridor.**  This is what makes the projected longitudinal
motion *exactly* the one-dimensional corridor system. -/
theorem netForce_of_corridor (hε : 0 < ε) (hεs : ε ≤ 1 / 8) (Λ : Fin m → ℝ) (i : Fin m)
    {x : ℝ × ℝ} (h : |x.2 - ((i : ℕ) : ℝ)| < 2 * ε) :
    netForce ε m Λ x =
      (-deriv (corridorPot ε (Λ i)) x.1, -deriv (wellShift ε (i : ℕ)) x.2) := by
  have hfst : (fun s => netPot ε m Λ (s, x.2)) =
      fun s => wellShift ε (i : ℕ) x.2 + corridorPot ε (Λ i) s := by
    funext s
    exact netPot_of_corridor hε hεs Λ i h.le
  have hsnd : (fun s => netPot ε m Λ (x.1, s)) =ᶠ[nhds x.2]
      fun s => wellShift ε (i : ℕ) s + corridorPot ε (Λ i) x.1 := by
    have hopen : Ioo (((i : ℕ) : ℝ) - 2 * ε) (((i : ℕ) : ℝ) + 2 * ε) ∈ nhds x.2 := by
      obtain ⟨h1, h2⟩ := abs_lt.mp h
      exact Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hopen] with s hs
    have hs' : |s - ((i : ℕ) : ℝ)| ≤ 2 * ε := by
      rw [abs_le]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact netPot_of_corridor hε hεs Λ i hs'
  rw [netForce, hfst, hsnd.deriv_eq]
  congr 1
  · rw [deriv_const_add']
  · rw [deriv_add_const']

/-! ### Existence of a microscopic trajectory -/

/-- **A microscopic trajectory of the universal thin network.**  For well-prepared initial data —
inside the tube of corridor `i`, with transverse energy below the wall height — there is a genuine
trajectory of the two-dimensional Hamiltonian `H_ε = ½ |p|² + netPot ε m Λ` on `[0, T]`, and
along it

* the transverse coordinate stays in the tube `|w - i| < 2ε` (thin-tube confinement), and
* the longitudinal pair solves the one-dimensional corridor system exactly.

Both statements are proved, not assumed. -/
theorem exists_netTrajectory (hε : 0 < ε) (hεs : ε ≤ 1 / 8) (Λ : Fin m → ℝ) (i : Fin m)
    (u₀ pu₀ w₀ pw₀ : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hprep : pw₀ ^ 2 / 2 + wellShift ε (i : ℕ) w₀ < 4) :
    ∃ u pu w pw : ℝ → ℝ,
      u 0 = u₀ ∧ pu 0 = pu₀ ∧ w 0 = w₀ ∧ pw 0 = pw₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T, |w t - ((i : ℕ) : ℝ)| < 2 * ε) ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (pu t) (Icc (0 : ℝ) T) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt pu (-deriv (corridorPot ε (Λ i)) (u t)) (Icc (0 : ℝ) T) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => (u s, w s)) (pu t, pw t) (Icc (0 : ℝ) T) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => (pu s, pw s)) (netForce ε m Λ (u t, w t))
          (Icc (0 : ℝ) T) t) := by
  obtain ⟨Rc, hRc0, hRc⟩ := exists_bound_deriv_corridorPot hε (Λ i)
  obtain ⟨Rw, hRw0, hRw⟩ := exists_bound_deriv_wellShift hε (i : ℕ)
  obtain ⟨u, pu, hu0, hpu0, hu, hpu⟩ :=
    exists_newton1D (contDiff_corridorPot ε (Λ i) (n := 2)) hRc0 hRc u₀ pu₀ hT
  obtain ⟨w, pw, hw0, hpw0, hw, hpw⟩ :=
    exists_newton1D (contDiff_wellShift ε (i : ℕ) (n := 2)) hRw0 hRw w₀ pw₀ hT
  have hconf : ∀ t ∈ Icc (0 : ℝ) T, |w t - ((i : ℕ) : ℝ)| < 2 * ε := by
    intro t ht
    have hS : ∀ z ∈ {z : ℝ | 2 * ε ≤ |z - ((i : ℕ) : ℝ)|}, (4 : ℝ) ≤ wellShift ε (i : ℕ) z := by
      intro z hz
      rw [wellShift_of_two_le_abs hε hz]
    have hE : energy1D (wellShift ε (i : ℕ)) (w 0) (pw 0) < 4 := by
      rw [energy1D, hw0, hpw0]
      exact hprep
    have hnot := not_mem_of_energy_lt (contDiff_wellShift ε (i : ℕ) (n := 1)) hS hw hpw hE t ht
    by_contra hcon
    rw [not_lt] at hcon
    exact hnot hcon
  refine ⟨u, pu, w, pw, hu0, hpu0, hw0, hpw0, hconf, hu, hpu, ?_, ?_⟩
  · intro t ht
    exact (hu t ht).prodMk (hw t ht)
  · intro t ht
    rw [netForce_of_corridor hε hεs Λ i (x := (u t, w t)) (hconf t ht)]
    exact (hpu t ht).prodMk (hpw t ht)

/-! ### The projected one-dimensional corridor system -/

/-- **The longitudinal projection of a network trajectory is an exact corridor solution.** -/
theorem corridorSolution_of_net {Λ : Fin m → ℝ} {i : Fin m} {c T : ℝ} {u pu : ℝ → ℝ}
    (hε : 0 < ε) (hlen : 1000 * ε ≤ Λ i) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hT : 0 ≤ T)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (pu t) (Icc (0 : ℝ) T) t)
    (hpu : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt pu (-deriv (corridorPot ε (Λ i)) (u t)) (Icc (0 : ℝ) T) t)
    (hinit : pu 0 ^ 2 / 2 + corridorPot ε (Λ i) (u 0) = c ^ 2 / 2) :
    CorridorSolution ε (Λ i) c T u pu where
  eps_pos := hε
  len := hlen
  c_ge := hc1
  c_le := hc2
  time_nonneg := hT
  ode_pos := hu
  ode_mom := hpu
  energy := by
    intro t ht
    have h := energy1D_eq (contDiff_corridorPot ε (Λ i) (n := 1)) hu hpu t ht
    rw [energy1D, energy1D] at h
    rw [h]
    exact hinit

end HamiltonianMetricGraphs
