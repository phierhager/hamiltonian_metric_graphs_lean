/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalNetworkDynamics

/-!
# Trajectories of the uniform network exist for all time

The uniform realization theorem is stated for *every* trajectory of `½|p|² + uniPot F ε` on
`[0, ∞)`.  This file shows that such trajectories exist for every initial state in the tube of a
corridor with energy below the wall height `4` (`exists_uniTrajectory`), so the theorem is not
vacuous.

The construction glues solutions on unit time intervals (`exists_global_of_unitTime`): an autonomous
ODE which can be solved for one unit of time from every initial state can be solved on `[0, ∞)`.
It is applied to the two one-dimensional Newton systems into which the motion separates on the
tube: the longitudinal motion in the corridor potential and the transverse motion in the well.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph
open scoped Topology

variable {Γ : FiniteMetricGraph} {ε : ℝ}

/-! ### Gluing unit-time solutions -/

/-- **Global solutions from unit-time solutions.**  If the autonomous equation `y' = v(y)` has a
solution on `[0, 1]` from every initial state, it has a solution on `[0, ∞)` from every initial
state. -/
theorem exists_global_of_unitTime {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : E → E}
    (hloc : ∀ a : E, ∃ y : ℝ → E, y 0 = a ∧
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt y (v (y t)) (Icc 0 1) t) (a : E) :
    ∃ Y : ℝ → E, Y 0 = a ∧ ∀ t, 0 ≤ t → HasDerivWithinAt Y (v (Y t)) (Ici 0) t := by
  choose S hS0 hS using hloc
  let s : ℕ → E := fun n => Nat.rec a (fun _ b => S b 1) n
  have hs0 : s 0 = a := rfl
  have hsucc : ∀ n, s (n + 1) = S (s n) 1 := fun n => rfl
  let Y : ℝ → E := fun t => S (s ⌊t⌋₊) (t - ⌊t⌋₊)
  -- on `[n, n + 1]` the glued curve is the `n`-th piece
  have hpiece : ∀ n : ℕ, ∀ t ∈ Icc (n : ℝ) (n + 1), Y t = S (s n) (t - n) := by
    intro n t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · have hfl : ⌊t⌋₊ = n := by
        rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg n) ht.1)]
        exact ⟨ht.1, hlt⟩
      change S (s ⌊t⌋₊) (t - ⌊t⌋₊) = _
      rw [hfl]
    · have hfl : ⌊t⌋₊ = n + 1 := by
        rw [heq]; exact_mod_cast Nat.floor_natCast (n + 1)
      change S (s ⌊t⌋₊) (t - ⌊t⌋₊) = _
      rw [hfl, heq, hsucc]
      push_cast
      rw [sub_self, hS0, show (n : ℝ) + 1 - n = 1 by ring]
  have hderiv : ∀ n : ℕ, ∀ t ∈ Icc (n : ℝ) (n + 1),
      HasDerivWithinAt Y (v (Y t)) (Icc (n : ℝ) (n + 1)) t := by
    intro n t ht
    have hmaps : MapsTo (fun r : ℝ => r - n) (Icc (n : ℝ) (n + 1)) (Icc 0 1) := by
      intro r hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hsh : HasDerivWithinAt (fun r : ℝ => r - n) 1 (Icc (n : ℝ) (n + 1)) t :=
      (hasDerivWithinAt_id t _).sub_const _
    have hc := (hS (s n) (t - n) (hmaps ht)).scomp t hsh hmaps
    rw [one_smul] at hc
    have heq : ∀ r ∈ Icc (n : ℝ) (n + 1), Y r = ((S (s n)) ∘ fun r : ℝ => r - n) r :=
      fun r hr => hpiece n r hr
    rw [hpiece n t ht]
    exact hc.congr heq (heq t ht)
  refine ⟨Y, ?_, ?_⟩
  · change S (s ⌊(0 : ℝ)⌋₊) (0 - ⌊(0 : ℝ)⌋₊) = a
    simp [hs0, hS0]
  intro t ht
  set n := ⌊t⌋₊ with hn
  have hnt : (n : ℝ) ≤ t := Nat.floor_le ht
  have htn : t < n + 1 := Nat.lt_floor_add_one t
  have hmem : t ∈ Icc (n : ℝ) (n + 1) := ⟨hnt, htn.le⟩
  rcases lt_or_eq_of_le hnt with hlt | heq
  · exact ((hderiv n t hmem).hasDerivAt (Icc_mem_nhds hlt htn)).hasDerivWithinAt
  · cases hn' : n with
    | zero =>
        rw [hn'] at heq hmem
        push_cast at heq hmem
        subst heq
        refine (hderiv 0 0 (by simp)).mono_of_mem_nhdsWithin ?_
        simp [Icc_mem_nhdsGE (zero_lt_one' ℝ)]
    | succ m =>
        rw [hn'] at heq hmem
        push_cast at heq hmem
        have h1 := hderiv m t ⟨by linarith, by linarith⟩
        have h2 := hderiv (m + 1) t (by push_cast; exact hmem)
        push_cast at h2
        have hu := h1.union h2
        rw [Icc_union_Icc_eq_Icc (by linarith) (by linarith)] at hu
        exact (hu.hasDerivAt (Icc_mem_nhds (by linarith) (by linarith))).hasDerivWithinAt

/-- **One-dimensional Newton systems with a bounded smooth force have global solutions.** -/
theorem exists_newton1D_Ici {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ y, |deriv Φ y| ≤ R) (q₀ p₀ : ℝ) :
    ∃ x p : ℝ → ℝ, x 0 = q₀ ∧ p 0 = p₀ ∧ ∀ t, 0 ≤ t →
      HasDerivWithinAt x (p t) (Ici 0) t ∧ HasDerivWithinAt p (-deriv Φ (x t)) (Ici 0) t := by
  have hloc : ∀ a : ℝ × ℝ, ∃ y : ℝ → ℝ × ℝ, y 0 = a ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt y ((y t).2, -deriv Φ (y t).1) (Icc 0 1) t := by
    intro a
    obtain ⟨x, p, hx0, hp0, hx, hp⟩ := exists_newton1D hΦ hR0 hR a.1 a.2 zero_le_one
    exact ⟨fun t => (x t, p t), Prod.ext hx0 hp0, fun t ht => (hx t ht).prodMk (hp t ht)⟩
  obtain ⟨Y, hY0, hY⟩ := exists_global_of_unitTime (v := fun y : ℝ × ℝ => (y.2, -deriv Φ y.1))
    hloc (q₀, p₀)
  refine ⟨fun t => (Y t).1, fun t => (Y t).2, by simp [hY0], by simp [hY0], fun t ht => ?_⟩
  exact ⟨hasDerivWithinAt_pairFst (hY t ht), hasDerivWithinAt_pairSnd (hY t ht)⟩

/-! ### Trajectories of the uniform network -/

theorem exists_bound_deriv_longPot (F : RoutingLaw Γ) (hε : 0 < ε) (ζ : Γ.EdgeEnd) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, |deriv (longPot F ε ζ) y| ≤ R := by
  by_cases h : ∃ k, IsFold F ζ k
  · rw [longPot_of_fold F ε ζ h]; exact exists_bound_deriv_corridorPot hε _
  · rw [longPot_of_not_fold F ε ζ h]; exact ⟨0, le_rfl, fun y => by simp⟩

/-- **Existence of trajectories of the uniform network.**  From every state in the tube of the
corridor of `ζ` with energy below the wall height `4` there is a trajectory of
`½|p|² + uniPot F ε` on `[0, ∞)`. -/
theorem exists_uniTrajectory (F : RoutingLaw Γ) (hε : 0 < ε) (hεs : ε ≤ 1 / 8) (ζ : Γ.EdgeEnd)
    (y₀ q₀ : ℝ × ℝ) (htube : |y₀.2 - uniRow ζ| < 2 * ε)
    (hE : hamEnergy (uniPot F ε) y₀ q₀ < 4) :
    ∃ x p : ℝ → ℝ × ℝ, x 0 = y₀ ∧ p 0 = q₀ ∧ IsHamiltonianTrajectory (uniPot F ε) x p := by
  obtain ⟨Ru, hRu0, hRu⟩ := exists_bound_deriv_longPot F hε ζ
  obtain ⟨u, pu, hu0, hpu0, hu⟩ :=
    exists_newton1D_Ici (contDiff_longPot F ε ζ (n := 2)) hRu0 hRu y₀.1 q₀.1
  set Φw : ℝ → ℝ := fun s => wellPot ε (s - uniRow ζ) with hΦw
  have hΦwc : ∀ {n : ℕ∞}, ContDiff ℝ n Φw :=
    (contDiff_wellPot ε).comp (contDiff_id.sub contDiff_const)
  have hderivΦw : ∀ s, deriv Φw s = deriv (wellPot ε) (s - uniRow ζ) := fun s =>
    deriv_comp_sub_const (f := wellPot ε) (a := uniRow ζ) s
  obtain ⟨Rw, hRw0, hRw⟩ := exists_bound_deriv_wellPot hε
  obtain ⟨w, pw, hw0, hpw0, hw⟩ := exists_newton1D_Ici (hΦwc (n := 2)) hRw0
    (fun s => by rw [hderivΦw]; exact hRw _) y₀.2 q₀.2
  -- the transverse motion stays in the tube
  have hEw : energy1D Φw (w 0) (pw 0) < 4 := by
    have hpot : uniPot F ε y₀ = wellPot ε (y₀.2 - uniRow ζ) + longPot F ε ζ y₀.1 :=
      uniPot_of_tube F hε hεs ζ htube.le
    have := longPot_nonneg F ε ζ y₀.1
    rw [hamEnergy, hpot] at hE
    rw [energy1D, hw0, hpw0]
    nlinarith [sq_nonneg q₀.1]
  have hconf : ∀ t, 0 ≤ t → |w t - uniRow ζ| < 2 * ε := by
    intro t ht
    have hS : ∀ z ∈ {z : ℝ | 2 * ε ≤ |z - uniRow ζ|}, (4 : ℝ) ≤ Φw z := by
      intro z hz
      rw [hΦw]
      exact (wellPot_of_two_le_abs hε hz).ge
    have hnot := not_mem_of_energy_lt (hΦwc (n := 1)) hS
      (fun s hs => (hw s hs.1).1.mono Icc_subset_Ici_self)
      (fun s hs => (hw s hs.1).2.mono Icc_subset_Ici_self) hEw t ⟨ht, le_rfl⟩
    by_contra hcon
    exact hnot (not_lt.mp hcon)
  refine ⟨fun t => (u t, w t), fun t => (pu t, pw t), Prod.ext hu0 hw0, Prod.ext hpu0 hpw0,
    fun t ht => ⟨(hu t ht).1.prodMk (hw t ht).1, ?_⟩⟩
  rw [gradForce_uniPot_of_tube F hε hεs ζ (y := (u t, w t)) (hconf t ht)]
  exact (hu t ht).2.prodMk (hw t ht).2

end HamiltonianMetricGraphs
