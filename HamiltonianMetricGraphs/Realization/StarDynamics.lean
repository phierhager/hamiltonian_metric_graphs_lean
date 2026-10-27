/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.StarReflection

/-!
# The longitudinal dynamics of the star network, with the paper's constants

The one-dimensional systems of the through channel (`u'' = -capPot ε '(u)`) and of the third arm
(`w'' = -armPot ε '(w)`) are those of `CapDynamics.lean` and `ArmDynamics.lean`.  Here they are
packaged for the star network at **every** scale `0 < ε ≤ 1/100` — the paper's `ε₀ = 1/100` —
and their reflections are timed by the **sharp** bound of Lemma IX.8 (`StarReflection.lean`):

* `CapMotion.reflect` — the outer caps reverse the momentum exactly, within `t_* < 23ε`
  (`d = 8ε`: `t_* < 16ε/c + 7ε`);
* `ArmMotion.reflect_cap` — the same at the outer cap of the arm;
* `ArmMotion.reflect_junction` — the junction barrier of the arm reverses the momentum exactly,
  within `t_* < 9ε` (`d = ε`: `t_* < 2ε/c + 7ε`).

These are exactly the times `23ε` and `9ε` of the proof of Theorem IX.9.  (`CapSolution` and
`ArmSolution` themselves, which the universal and branching constructions share, are unchanged.)
-/

namespace HamiltonianMetricGraphs

open Set Real

variable {ε c Tmax : ℝ}

/-! ### The through channel -/

/-- **A longitudinal solution of the through channel** on `[0, Tmax]`, at a scale
`0 < ε ≤ 1/100` and energy `c²/2`, `c ∈ [1, 2]`. -/
structure CapMotion (ε c Tmax : ℝ) (u pu : ℝ → ℝ) : Prop where
  eps_pos : 0 < ε
  eps_small : ε ≤ 1 / 100
  c_ge : 1 ≤ c
  c_le : c ≤ 2
  time_nonneg : 0 ≤ Tmax
  ode_pos : ∀ t ∈ Icc (0 : ℝ) Tmax, HasDerivWithinAt u (pu t) (Icc (0 : ℝ) Tmax) t
  ode_mom : ∀ t ∈ Icc (0 : ℝ) Tmax,
    HasDerivWithinAt pu (-deriv (capPot ε) (u t)) (Icc (0 : ℝ) Tmax) t
  energy : ∀ t ∈ Icc (0 : ℝ) Tmax, pu t ^ 2 / 2 + capPot ε (u t) = c ^ 2 / 2

namespace CapMotion

variable {u pu : ℝ → ℝ}

theorem c_pos (S : CapMotion ε c Tmax u pu) : 0 < c := by linarith [S.c_ge]

/-- The speed never exceeds the nominal speed `c`. -/
theorem abs_mom_le (S : CapMotion ε c Tmax u pu) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Tmax) :
    |pu t| ≤ c := by
  have h := S.energy t ht
  have hp := capPot_nonneg ε (u t)
  have hsq : pu t ^ 2 ≤ c ^ 2 := by linarith
  calc |pu t| = Real.sqrt (pu t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hsq
    _ = c := Real.sqrt_sq S.c_pos.le

/-- Travelled distance bound: the particle moves at speed at most `c`. -/
theorem travel_le (S : CapMotion ε c Tmax u pu) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) Tmax) (ht : t ∈ Icc (0 : ℝ) Tmax) (hst : s ≤ t) :
    |u t - u s| ≤ c * (t - s) :=
  abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le S.ode_pos
    (fun _ hv => S.abs_mom_le hv) hs ht hst

/-- **The motion between the caps is exactly free.** -/
theorem free (S : CapMotion ε c Tmax u pu) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (hbnd : ∀ t ∈ Icc a b, |u a + pu a * (t - a)| < 1) :
    ∀ t ∈ Icc a b, u t = u a + pu a * (t - a) ∧ pu t = pu a := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha.1 hb.2
  refine free_motion (Φ := capPot ε) (A := -1) (B := 1)
    (fun y hy => deriv_capPot_of_abs_le_one S.eps_pos (abs_le.mpr ⟨hy.1, hy.2⟩)) hab
    (fun t ht => (S.ode_pos t (hsub ht)).mono hsub)
    (fun t ht => (S.ode_mom t (hsub ht)).mono hsub) (fun t ht => ?_)
  exact mem_Ioo.mpr (abs_lt.mp (hbnd t ht))

/-- The convenient form of `free`: it is enough to check the two endpoints. -/
theorem free_of_endpoints (S : CapMotion ε c Tmax u pu) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (h1 : |u a| < 1) (h2 : |u a + pu a * (b - a)| < 1) :
    ∀ t ∈ Icc a b, u t = u a + pu a * (t - a) ∧ pu t = pu a := by
  refine S.free ha hb hab ?_
  intro t ht
  rw [abs_lt] at h1 h2 ⊢
  rcases le_or_gt 0 (pu a) with hs | hs
  · exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  · exact ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩

/-- **Exact reflection at the right cap, within `23ε`.** -/
theorem reflect_right (S : CapMotion ε c Tmax u pu) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + 23 * ε ≤ Tmax)
    (hua : u a = 1 - 8 * ε) (hpa : pu a = c) :
    ∃ t₁ ∈ Ioo a (a + 23 * ε), u t₁ = 1 - 8 * ε ∧ pu t₁ = -c := by
  have hε := S.eps_pos
  have hεs := S.eps_small
  have hc0 := S.c_pos
  have hτpos : 0 < barrierTime ε c (8 * ε) := barrierTime_pos hε S.c_ge (by linarith)
  have hτlt : barrierTime ε c (8 * ε) < 23 * ε := capTime_lt hε S.c_ge
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + barrierTime ε c (8 * ε) ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, by linarith⟩
  have hsub : Icc a (a + barrierTime ε c (8 * ε)) ⊆ Icc (0 : ℝ) Tmax :=
    Icc_subset_Icc ha hbmem.2
  -- the passage is short, so the particle stays on the right half of the tube
  have hnear : ∀ t ∈ Icc a (a + barrierTime ε c (8 * ε)), 0 ≤ u t := by
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
      E_pos := by nlinarith
      E_lt := by nlinarith [S.c_le]
      d_nonneg := by linarith
      hx := fun t ht =>
        ((hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht).sub_const 1
      hp := fun t ht => by
        have h := (hasDerivWithinAt_sub_interval S.ode_mom hamem hbmem) t ht
        rwa [deriv_capPot_right hε (by linarith [hnear t ht])] at h
      init_x := by rw [hua]; ring
      init_p := by rw [hpa, sqrt_two_mul_half_sq hc0.le]
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier_sharp hsetup
  have ht₁2 : t₁ ≤ a + barrierTime ε c (8 * ε) := ht₁.2
  refine ⟨t₁, ⟨ht₁.1, by linarith⟩, by linarith [hx₁], ?_⟩
  rw [hp₁, sqrt_two_mul_half_sq hc0.le]

/-- **Exact reflection at the left cap, within `23ε`**, by the mirror symmetry. -/
theorem reflect_left (S : CapMotion ε c Tmax u pu) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + 23 * ε ≤ Tmax)
    (hua : u a = -(1 - 8 * ε)) (hpa : pu a = -c) :
    ∃ t₁ ∈ Ioo a (a + 23 * ε), u t₁ = -(1 - 8 * ε) ∧ pu t₁ = c := by
  have hε := S.eps_pos
  have hεs := S.eps_small
  have hc0 := S.c_pos
  have hτpos : 0 < barrierTime ε c (8 * ε) := barrierTime_pos hε S.c_ge (by linarith)
  have hτlt : barrierTime ε c (8 * ε) < 23 * ε := capTime_lt hε S.c_ge
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + barrierTime ε c (8 * ε) ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, by linarith⟩
  have hsub : Icc a (a + barrierTime ε c (8 * ε)) ⊆ Icc (0 : ℝ) Tmax :=
    Icc_subset_Icc ha hbmem.2
  have hnear : ∀ t ∈ Icc a (a + barrierTime ε c (8 * ε)), u t ≤ 0 := by
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
      E_pos := by nlinarith
      E_lt := by nlinarith [S.c_le]
      d_nonneg := by linarith
      hx := fun t ht =>
        (((hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht).neg).sub_const 1
      hp := fun t ht => by
        have h := ((hasDerivWithinAt_sub_interval S.ode_mom hamem hbmem) t ht).neg
        rw [neg_neg, deriv_capPot_left hε (by linarith [hnear t ht])] at h
        exact h
      init_x := by
        show -u a - 1 = -(8 * ε)
        rw [hua]; ring
      init_p := by
        show -pu a = Real.sqrt (2 * (c ^ 2 / 2))
        rw [hpa, sqrt_two_mul_half_sq hc0.le]; ring
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier_sharp hsetup
  have ht₁2 : t₁ ≤ a + barrierTime ε c (8 * ε) := ht₁.2
  have hx₁' : -u t₁ - 1 = -(8 * ε) := hx₁
  have hp₁' : -pu t₁ = -Real.sqrt (2 * (c ^ 2 / 2)) := hp₁
  rw [sqrt_two_mul_half_sq hc0.le] at hp₁'
  exact ⟨t₁, ⟨ht₁.1, by linarith⟩, by linarith, by linarith⟩

/-- **The cap reflection, uniformly in the side** (`s = ±1`), within `23ε`. -/
theorem reflect (S : CapMotion ε c Tmax u pu) {a s : ℝ} (hs : s = 1 ∨ s = -1)
    (ha : 0 ≤ a) (hb : a + 23 * ε ≤ Tmax)
    (hua : u a = s * (1 - 8 * ε)) (hpa : pu a = s * c) :
    ∃ t₁ ∈ Ioo a (a + 23 * ε), u t₁ = s * (1 - 8 * ε) ∧ pu t₁ = -(s * c) := by
  rcases hs with rfl | rfl
  · obtain ⟨t₁, ht₁, h1, h2⟩ := S.reflect_right ha hb (by linarith [hua]) (by linarith [hpa])
    exact ⟨t₁, ht₁, by linarith, by linarith⟩
  · obtain ⟨t₁, ht₁, h1, h2⟩ := S.reflect_left ha hb (by linarith [hua]) (by linarith [hpa])
    exact ⟨t₁, ht₁, by linarith, by linarith⟩

end CapMotion

/-! ### The third arm -/

/-- **A longitudinal solution of the third arm** on `[0, Tmax]`, at a scale `0 < ε ≤ 1/100` and
energy `c²/2`, `c ∈ [1, 2]`. -/
structure ArmMotion (ε c Tmax : ℝ) (w pw : ℝ → ℝ) : Prop where
  eps_pos : 0 < ε
  eps_small : ε ≤ 1 / 100
  c_ge : 1 ≤ c
  c_le : c ≤ 2
  time_nonneg : 0 ≤ Tmax
  ode_pos : ∀ t ∈ Icc (0 : ℝ) Tmax, HasDerivWithinAt w (pw t) (Icc (0 : ℝ) Tmax) t
  ode_mom : ∀ t ∈ Icc (0 : ℝ) Tmax,
    HasDerivWithinAt pw (-deriv (armPot ε) (w t)) (Icc (0 : ℝ) Tmax) t
  energy : ∀ t ∈ Icc (0 : ℝ) Tmax, pw t ^ 2 / 2 + armPot ε (w t) = c ^ 2 / 2

namespace ArmMotion

variable {w pw : ℝ → ℝ}

theorem c_pos (S : ArmMotion ε c Tmax w pw) : 0 < c := by linarith [S.c_ge]

theorem abs_mom_le (S : ArmMotion ε c Tmax w pw) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Tmax) :
    |pw t| ≤ c := by
  have h := S.energy t ht
  have hp := armPot_nonneg ε (w t)
  have hsq : pw t ^ 2 ≤ c ^ 2 := by linarith
  calc |pw t| = Real.sqrt (pw t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hsq
    _ = c := Real.sqrt_sq S.c_pos.le

theorem travel_le (S : ArmMotion ε c Tmax w pw) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) Tmax) (ht : t ∈ Icc (0 : ℝ) Tmax) (hst : s ≤ t) :
    |w t - w s| ≤ c * (t - s) :=
  abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le S.ode_pos
    (fun _ hv => S.abs_mom_le hv) hs ht hst

/-- **`3 ↦ 3`: the arm never reaches the junction.**  The junction barrier has height `4`, above
the whole window `K⋆`, so the particle stays at `w > 6ε`. -/
theorem gt_six (S : ArmMotion ε c Tmax w pw) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Tmax) :
    6 * ε < w t := by
  by_contra hcon
  rw [not_lt] at hcon
  have h1 := armPot_ge_of_le_six S.eps_pos hcon
  have h2 := S.energy t ht
  have h3 : (0 : ℝ) ≤ pw t ^ 2 := sq_nonneg _
  nlinarith [S.c_le, S.c_ge]

/-- **The motion between the barriers is exactly free.** -/
theorem free (S : ArmMotion ε c Tmax w pw) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (hbnd : ∀ t ∈ Icc a b, w a + pw a * (t - a) ∈ Ioo (7 * ε) 1) :
    ∀ t ∈ Icc a b, w t = w a + pw a * (t - a) ∧ pw t = pw a := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha.1 hb.2
  exact free_motion (Φ := armPot ε) (A := 7 * ε) (B := 1)
    (fun y hy => deriv_armPot_of_mem S.eps_pos hy.1 hy.2) hab
    (fun t ht => (S.ode_pos t (hsub ht)).mono hsub)
    (fun t ht => (S.ode_mom t (hsub ht)).mono hsub) hbnd

/-- The convenient form: it is enough to check the two endpoints. -/
theorem free_of_endpoints (S : ArmMotion ε c Tmax w pw) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (h1 : w a ∈ Ioo (7 * ε) 1) (h2 : w a + pw a * (b - a) ∈ Ioo (7 * ε) 1) :
    ∀ t ∈ Icc a b, w t = w a + pw a * (t - a) ∧ pw t = pw a := by
  refine S.free ha hb hab ?_
  intro t ht
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  rcases le_or_gt 0 (pw a) with hs | hs
  · exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  · exact ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩

/-- **Exact reflection at the outer cap of the arm, within `23ε`.** -/
theorem reflect_cap (S : ArmMotion ε c Tmax w pw) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + 23 * ε ≤ Tmax)
    (hwa : w a = 1 - 8 * ε) (hpa : pw a = c) :
    ∃ t₁ ∈ Ioo a (a + 23 * ε), w t₁ = 1 - 8 * ε ∧ pw t₁ = -c := by
  have hε := S.eps_pos
  have hεs := S.eps_small
  have hc0 := S.c_pos
  have hτpos : 0 < barrierTime ε c (8 * ε) := barrierTime_pos hε S.c_ge (by linarith)
  have hτlt : barrierTime ε c (8 * ε) < 23 * ε := capTime_lt hε S.c_ge
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + barrierTime ε c (8 * ε) ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, by linarith⟩
  have hsub : Icc a (a + barrierTime ε c (8 * ε)) ⊆ Icc (0 : ℝ) Tmax :=
    Icc_subset_Icc ha hbmem.2
  have hnear : ∀ t ∈ Icc a (a + barrierTime ε c (8 * ε)), 7 * ε ≤ w t := by
    intro t ht
    have h1 := abs_le.mp (S.travel_le hamem (hsub ht) ht.1)
    have h2 : c * (t - a) ≤ 2 * (23 * ε) := by
      have : t - a ≤ 23 * ε := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    linarith [h1.1]
  have hsetup : Reflection.SharpSetup (wallPot ε) (ε / 4) ε 4 (4 / (exp 3 * ε)) (c ^ 2 / 2)
      (8 * ε) a (a + barrierTime ε c (8 * ε)) (fun t => w t - 1) pw :=
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
      E_pos := by nlinarith
      E_lt := by nlinarith [S.c_le]
      d_nonneg := by linarith
      hx := fun t ht =>
        ((hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht).sub_const 1
      hp := fun t ht => by
        have h := (hasDerivWithinAt_sub_interval S.ode_mom hamem hbmem) t ht
        rwa [deriv_armPot_cap hε (hnear t ht)] at h
      init_x := by rw [hwa]; ring
      init_p := by rw [hpa, sqrt_two_mul_half_sq hc0.le]
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier_sharp hsetup
  have ht₁2 : t₁ ≤ a + barrierTime ε c (8 * ε) := ht₁.2
  refine ⟨t₁, ⟨ht₁.1, by linarith⟩, by linarith [hx₁], ?_⟩
  rw [hp₁, sqrt_two_mul_half_sq hc0.le]

/-- **Exact reflection at the junction barrier of the arm, within `9ε`.**  This is the dynamical
form of `F⋆(η₃) = η₃`: the particle arriving at the junction boundary `w = 8ε` is turned around by
the barrier `B((7ε - w)/ε)` and leaves along the third channel with exactly reversed momentum. -/
theorem reflect_junction (S : ArmMotion ε c Tmax w pw) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + 9 * ε ≤ Tmax)
    (hwa : w a = 8 * ε) (hpa : pw a = -c) :
    ∃ t₁ ∈ Ioo a (a + 9 * ε), w t₁ = 8 * ε ∧ pw t₁ = c := by
  have hε := S.eps_pos
  have hεs := S.eps_small
  have hc0 := S.c_pos
  have hτpos : 0 < barrierTime ε c ε := barrierTime_pos hε S.c_ge hε.le
  have hτlt : barrierTime ε c ε < 9 * ε := armTime_lt hε S.c_ge
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + barrierTime ε c ε ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, by linarith⟩
  have hsub : Icc a (a + barrierTime ε c ε) ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha hbmem.2
  have hnear : ∀ t ∈ Icc a (a + barrierTime ε c ε), w t ≤ 1 := by
    intro t ht
    have h1 := abs_le.mp (S.travel_le hamem (hsub ht) ht.1)
    have h2 : c * (t - a) ≤ 2 * (9 * ε) := by
      have : t - a ≤ 9 * ε := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    linarith [h1.2]
  have hsetup : Reflection.SharpSetup (wallPot ε) (ε / 4) ε 4 (4 / (exp 3 * ε)) (c ^ 2 / 2) ε
      a (a + barrierTime ε c ε) (fun t => 7 * ε - w t) (fun t => -pw t) :=
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
      E_pos := by nlinarith
      E_lt := by nlinarith [S.c_le]
      d_nonneg := hε.le
      hx := fun t ht => by
        have h := (hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht
        simpa using h.const_sub (7 * ε)
      hp := fun t ht => by
        have h := ((hasDerivWithinAt_sub_interval S.ode_mom hamem hbmem) t ht).neg
        rw [neg_neg, deriv_armPot_junction hε (hnear t ht)] at h
        exact h
      init_x := by
        show 7 * ε - w a = -ε
        rw [hwa]; ring
      init_p := by
        show -pw a = Real.sqrt (2 * (c ^ 2 / 2))
        rw [hpa, sqrt_two_mul_half_sq hc0.le]; ring
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier_sharp hsetup
  have ht₁2 : t₁ ≤ a + barrierTime ε c ε := ht₁.2
  have hx₁' : 7 * ε - w t₁ = -ε := hx₁
  have hp₁' : -pw t₁ = -Real.sqrt (2 * (c ^ 2 / 2)) := hp₁
  rw [sqrt_two_mul_half_sq hc0.le] at hp₁'
  exact ⟨t₁, ⟨ht₁.1, by linarith⟩, by linarith, by linarith⟩

end ArmMotion

end HamiltonianMetricGraphs
