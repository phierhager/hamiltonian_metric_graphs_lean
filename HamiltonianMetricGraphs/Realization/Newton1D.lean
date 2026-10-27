/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import Mathlib

/-!
# One-dimensional Newtonian dynamics

Conservation of energy for the one-dimensional Newtonian system `q' = p`, `p' = -U'(q)`, together
with the elementary consequences used to confine a particle behind a potential barrier.

All hypotheses are stated in the one-sided (within-`Icc`) derivative form, because the
trajectories under consideration are produced by Picard-Lindelöf on a closed interval and hence
have only one-sided derivatives at the endpoints.

## Main results

* `energy1D_eq`: the mechanical energy is constant along a solution.
* `potential_le_energy`: the particle stays in the classically allowed region `{U ≤ E}`.
* `not_mem_of_energy_lt`: a particle of energy below `B` never enters a set on which `B ≤ U`.
* `sq_momentum_eq`: the momentum is determined, up to sign, by the position.
-/

namespace HamiltonianMetricGraphs

open Set

/-- The mechanical energy of a one-dimensional system. -/
noncomputable def energy1D (U : ℝ → ℝ) (q p : ℝ) : ℝ := p ^ 2 / 2 + U q

/-- Along a one-sided solution of Newton's equations the mechanical energy has vanishing
within-derivative.  This is the infinitesimal form of energy conservation. -/
theorem energy1D_hasDerivWithinAt_zero {U : ℝ → ℝ} (hU : ContDiff ℝ 1 U) {x p : ℝ → ℝ}
    {s : Set ℝ} {t : ℝ} (hx : HasDerivWithinAt x (p t) s t)
    (hp : HasDerivWithinAt p (-deriv U (x t)) s t) :
    HasDerivWithinAt (fun u => energy1D U (x u) (p u)) 0 s t := by
  have hU₀ : HasDerivAt U (deriv U (x t)) (x t) :=
    (hU.differentiable (by norm_num) (x t)).hasDerivAt
  have hUx : HasDerivWithinAt (U ∘ x) (deriv U (x t) * p t) s t := by
    simpa only [Function.comp_apply] using hU₀.comp_hasDerivWithinAt t hx
  have hsum := ((hp.pow 2).div_const 2).add hUx
  refine (hsum.congr_of_eventuallyEq ?_ ?_).congr_deriv ?_
  · filter_upwards [] with u
    simp [energy1D, Function.comp_def]
  · simp [energy1D, Function.comp_def]
  · push_cast
    ring

/-- **Conservation of energy.**  Along a solution of `q' = p`, `p' = -U'(q)` on `[a,b]`
the mechanical energy is constant. -/
theorem energy1D_eq {U : ℝ → ℝ} (hU : ContDiff ℝ 1 U) {x p : ℝ → ℝ} {a b : ℝ}
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (p t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (-deriv U (x t)) (Icc a b) t) :
    ∀ t ∈ Icc a b, energy1D U (x t) (p t) = energy1D U (x a) (p a) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · apply constant_of_derivWithin_zero
    · intro t ht
      exact (energy1D_hasDerivWithinAt_zero hU (hx t ht) (hp t ht)).differentiableWithinAt
    · intro t ht
      exact (energy1D_hasDerivWithinAt_zero hU (hx t (mem_Icc_of_Ico ht))
        (hp t (mem_Icc_of_Ico ht))).derivWithin
          ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt (mem_Icc_of_Ico ht))
  · intro t ht
    have hta : t = a := le_antisymm ht.2 ht.1
    subst hta
    rfl
  · intro t ht
    exact (not_lt_of_ge (le_trans ht.1 ht.2) hba).elim

/-- A particle never enters a region where the potential exceeds its energy. -/
theorem potential_le_energy {U : ℝ → ℝ} (hU : ContDiff ℝ 1 U) {x p : ℝ → ℝ} {a b : ℝ}
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (p t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (-deriv U (x t)) (Icc a b) t) :
    ∀ t ∈ Icc a b, U (x t) ≤ energy1D U (x a) (p a) := by
  intro t ht
  have hcons : energy1D U (x t) (p t) = energy1D U (x a) (p a) := energy1D_eq hU hx hp t ht
  have hsq : (0 : ℝ) ≤ p t ^ 2 := sq_nonneg (p t)
  simp only [energy1D] at hcons ⊢
  linarith

/-- **Barrier confinement.**  If the potential is at least `B` on a set `S`, and the energy
is below `B`, the trajectory never meets `S`. -/
theorem not_mem_of_energy_lt {U : ℝ → ℝ} (hU : ContDiff ℝ 1 U) {x p : ℝ → ℝ} {a b B : ℝ}
    {S : Set ℝ} (hS : ∀ q ∈ S, B ≤ U q)
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (p t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (-deriv U (x t)) (Icc a b) t)
    (hE : energy1D U (x a) (p a) < B) :
    ∀ t ∈ Icc a b, x t ∉ S := by
  intro t ht hmem
  have hB : B ≤ U (x t) := hS (x t) hmem
  have hle : U (x t) ≤ energy1D U (x a) (p a) := potential_le_energy hU hx hp t ht
  exact absurd (hB.trans hle) (not_le_of_gt hE)

/-- The speed is determined by the position up to sign. -/
theorem sq_momentum_eq {U : ℝ → ℝ} (hU : ContDiff ℝ 1 U) {x p : ℝ → ℝ} {a b : ℝ}
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (p t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (-deriv U (x t)) (Icc a b) t) :
    ∀ t ∈ Icc a b, p t ^ 2 = 2 * (energy1D U (x a) (p a) - U (x t)) := by
  intro t ht
  have hcons : energy1D U (x t) (p t) = energy1D U (x a) (p a) := energy1D_eq hU hx hp t ht
  simp only [energy1D] at hcons ⊢
  linarith

end HamiltonianMetricGraphs
