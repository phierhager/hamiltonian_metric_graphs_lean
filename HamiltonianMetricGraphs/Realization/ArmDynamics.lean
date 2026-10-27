/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.CapDynamics
import HamiltonianMetricGraphs.Realization.MicroscopicTrajectory

/-!
# The dynamics of the third arm

The third channel of the network is the `w`-axis above the junction.  In the arm region `w ≥ 6ε`
the microscopic potential is again an exact sum,

  `microPot ε (u, w) = wellPot ε u + armPot ε w`,  `armPot ε w = wallPot ε (7ε - w) + wallPot ε (w - 1)`,

so the longitudinal motion along the arm is the one-dimensional Newtonian system of `armPot ε`.
That potential is flat on `[7ε, 1]` and rises to the confining height `4` on both sides: the
**junction barrier** just below `7ε`, which is what realizes `F⋆(η₃) = η₃`, and the **cap** at the
outer vertex `w = 1`.

## Main results

* `microForce_of_arm` — exact separability of the force in the arm region;
* `exists_armTrajectory` — a genuine two-dimensional trajectory of `H_ε` along the arm, which by
  conservation of energy never descends below `w = 6ε`: the third channel is closed off from the
  junction (`3 ↦ 3`);
* `ArmSolution.free` — the motion between the barriers is exactly free (`odeErr = 0`);
* `ArmSolution.reflect_cap`, `ArmSolution.reflect_junction` — both barriers reverse the momentum
  exactly, within the time `capReflTime ε c ≤ 100 ε` (`momErr = 0`, `dwell = O(ε)`).
-/

namespace HamiltonianMetricGraphs

open Set Real

variable {ε c Tmax : ℝ} {w pw : ℝ → ℝ}

/-! ### The arm potential -/

theorem armPot_eq_wall (ε w : ℝ) : armPot ε w = wallPot ε (7 * ε - w) + wallPot ε (w - 1) := rfl

theorem hasDerivAt_armPot (ε w : ℝ) :
    HasDerivAt (armPot ε) (-deriv (wallPot ε) (7 * ε - w) + deriv (wallPot ε) (w - 1)) w := by
  have hw : ∀ y : ℝ, HasDerivAt (wallPot ε) (deriv (wallPot ε) y) y := fun y =>
    ((contDiff_wallPot ε (n := 1)).differentiable (by norm_num) y).hasDerivAt
  have e1 : HasDerivAt (fun s : ℝ => 7 * ε - s) (-1 : ℝ) w := by
    simpa using (hasDerivAt_id w).const_sub (7 * ε)
  have e2 : HasDerivAt (fun s : ℝ => s - 1) 1 w := by
    simpa using (hasDerivAt_id w).sub_const 1
  have h1 := (hw (7 * ε - w)).comp w e1
  have h2 := (hw (w - 1)).comp w e2
  have h := h1.add h2
  have hrw : deriv (wallPot ε) (7 * ε - w) * (-1) + deriv (wallPot ε) (w - 1) * 1 =
      -deriv (wallPot ε) (7 * ε - w) + deriv (wallPot ε) (w - 1) := by ring
  rw [hrw] at h
  exact h

theorem deriv_armPot_eq (ε w : ℝ) :
    deriv (armPot ε) w = -deriv (wallPot ε) (7 * ε - w) + deriv (wallPot ε) (w - 1) :=
  (hasDerivAt_armPot ε w).deriv

/-- Near the junction barrier only that barrier acts. -/
theorem deriv_armPot_junction (hε : 0 < ε) {v : ℝ} (h : v ≤ 1) :
    deriv (armPot ε) v = -deriv (wallPot ε) (7 * ε - v) := by
  rw [deriv_armPot_eq, deriv_wallPot_of_nonpos hε (y := v - 1) (by linarith), add_zero]

/-- Near the cap only the cap acts. -/
theorem deriv_armPot_cap (hε : 0 < ε) {v : ℝ} (h : 7 * ε ≤ v) :
    deriv (armPot ε) v = deriv (wallPot ε) (v - 1) := by
  rw [deriv_armPot_eq, deriv_wallPot_of_nonpos hε (y := 7 * ε - v) (by linarith), neg_zero,
    zero_add]

/-- **The arm is flat between the two barriers.** -/
theorem deriv_armPot_of_mem (hε : 0 < ε) {v : ℝ} (h₁ : 7 * ε ≤ v) (h₂ : v ≤ 1) :
    deriv (armPot ε) v = 0 := by
  rw [deriv_armPot_eq, deriv_wallPot_of_nonpos hε (y := 7 * ε - v) (by linarith),
    deriv_wallPot_of_nonpos hε (y := v - 1) (by linarith), neg_zero, add_zero]

theorem armPot_eq_affine (hε : ε ≠ 0) :
    armPot ε = fun v => barrierProfile (-ε⁻¹ * v + 7) + barrierProfile (ε⁻¹ * v + -ε⁻¹) := by
  funext v
  rw [armPot]
  congr 2 <;> field_simp <;> ring

/-- The force along the arm is globally bounded. -/
theorem exists_bound_deriv_armPot (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v, |deriv (armPot ε) v| ≤ R := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_barrierProfile
  refine ⟨M * |(-ε⁻¹)| + M * |ε⁻¹|, by positivity, fun v => ?_⟩
  rw [armPot_eq_affine (ne_of_gt hε)]
  have hd : Differentiable ℝ barrierProfile :=
    (contDiff_barrierProfile (n := 1)).differentiable (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => -ε⁻¹ * s + 7) (-ε⁻¹) v := by
    simpa using ((hasDerivAt_id v).const_mul (-ε⁻¹)).add_const 7
  have h2 : HasDerivAt (fun s : ℝ => ε⁻¹ * s + -ε⁻¹) ε⁻¹ v := by
    simpa using ((hasDerivAt_id v).const_mul ε⁻¹).add_const (-ε⁻¹)
  have g1 : HasDerivAt (fun s => barrierProfile (-ε⁻¹ * s + 7))
      (deriv barrierProfile (-ε⁻¹ * v + 7) * -ε⁻¹) v := ((hd _).hasDerivAt).comp v h1
  have g2 : HasDerivAt (fun s => barrierProfile (ε⁻¹ * s + -ε⁻¹))
      (deriv barrierProfile (ε⁻¹ * v + -ε⁻¹) * ε⁻¹) v := ((hd _).hasDerivAt).comp v h2
  have g12 : HasDerivAt (fun s => barrierProfile (-ε⁻¹ * s + 7) +
      barrierProfile (ε⁻¹ * s + -ε⁻¹))
      (deriv barrierProfile (-ε⁻¹ * v + 7) * -ε⁻¹ +
        deriv barrierProfile (ε⁻¹ * v + -ε⁻¹) * ε⁻¹) v := g1.add g2
  rw [g12.deriv]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_) <;> rw [abs_mul] <;>
    exact mul_le_mul (hM _) le_rfl (abs_nonneg _) hM0

/-! ### The force of the microscopic Hamiltonian in the arm region -/

/-- **The force is separable in the third-arm region.** -/
theorem microForce_of_arm (hε : 0 < ε) {x : ℝ × ℝ} (h : 6 * ε < x.2) :
    microForce ε x = (-deriv (wellPot ε) x.1, -deriv (armPot ε) x.2) := by
  have hfst : (fun s => microPot ε (s, x.2)) = fun s => wellPot ε s + armPot ε x.2 := by
    funext s
    exact microPot_of_arm hε (x := (s, x.2)) h.le
  have hsnd : (fun s => microPot ε (x.1, s)) =ᶠ[nhds x.2]
      fun s => wellPot ε x.1 + armPot ε s := by
    filter_upwards [Ioi_mem_nhds h] with s hs
    have := microPot_of_arm hε (x := (x.1, s)) (le_of_lt hs)
    rw [this, armPot2]
  rw [microForce, hfst, hsnd.deriv_eq]
  congr 1
  · rw [deriv_add_const']
  · rw [deriv_const_add']

/-! ### Solutions along the arm -/

/-- **A longitudinal solution of the third arm** on the time window `[0, Tmax]`, at scale `ε` and
energy `c²/2`.  These are exactly the hypotheses supplied by `exists_armTrajectory`. -/
structure ArmSolution (ε c Tmax : ℝ) (w pw : ℝ → ℝ) : Prop where
  eps_pos : 0 < ε
  eps_small : ε ≤ 1 / 1000
  c_ge : 1 ≤ c
  c_le : c ≤ 2
  time_nonneg : 0 ≤ Tmax
  ode_pos : ∀ t ∈ Icc (0 : ℝ) Tmax, HasDerivWithinAt w (pw t) (Icc (0 : ℝ) Tmax) t
  ode_mom : ∀ t ∈ Icc (0 : ℝ) Tmax,
    HasDerivWithinAt pw (-deriv (armPot ε) (w t)) (Icc (0 : ℝ) Tmax) t
  energy : ∀ t ∈ Icc (0 : ℝ) Tmax, pw t ^ 2 / 2 + armPot ε (w t) = c ^ 2 / 2

namespace ArmSolution

theorem c_pos (S : ArmSolution ε c Tmax w pw) : 0 < c := by linarith [S.c_ge]

theorem abs_mom_le (S : ArmSolution ε c Tmax w pw) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Tmax) :
    |pw t| ≤ c := by
  have h := S.energy t ht
  have hp := armPot_nonneg ε (w t)
  have hsq : pw t ^ 2 ≤ c ^ 2 := by linarith
  calc |pw t| = Real.sqrt (pw t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hsq
    _ = c := Real.sqrt_sq S.c_pos.le

theorem travel_le (S : ArmSolution ε c Tmax w pw) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) Tmax) (ht : t ∈ Icc (0 : ℝ) Tmax) (hst : s ≤ t) :
    |w t - w s| ≤ c * (t - s) :=
  abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le S.ode_pos
    (fun v hv => S.abs_mom_le hv) hs ht hst

/-- **`3 ↦ 3`: the arm never reaches the junction.**  The junction barrier has height `4`, above
the whole window `K⋆`, so a particle of the window that is in the arm stays at `w > 6ε` and can
never enter the interpolation zone, let alone the through channel. -/
theorem gt_six (S : ArmSolution ε c Tmax w pw) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Tmax) :
    6 * ε < w t := by
  by_contra hcon
  rw [not_lt] at hcon
  have h1 := armPot_ge_of_le_six S.eps_pos hcon
  have h2 := S.energy t ht
  have h3 : (0 : ℝ) ≤ pw t ^ 2 := sq_nonneg _
  nlinarith [S.c_le, S.c_ge]

/-- **The motion between the barriers is exactly free.** -/
theorem free (S : ArmSolution ε c Tmax w pw) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (hbnd : ∀ t ∈ Icc a b, w a + pw a * (t - a) ∈ Ioo (7 * ε) 1) :
    ∀ t ∈ Icc a b, w t = w a + pw a * (t - a) ∧ pw t = pw a := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha.1 hb.2
  exact free_motion (Φ := armPot ε) (A := 7 * ε) (B := 1)
    (fun y hy => deriv_armPot_of_mem S.eps_pos hy.1 hy.2) hab
    (fun t ht => (S.ode_pos t (hsub ht)).mono hsub)
    (fun t ht => (S.ode_mom t (hsub ht)).mono hsub) hbnd

/-- The convenient form: it is enough to check the two endpoints. -/
theorem free_of_endpoints (S : ArmSolution ε c Tmax w pw) {a b : ℝ}
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

/-! #### Reflection at the two barriers -/

/-- **Exact reflection at the outer cap of the arm.** -/
theorem reflect_cap (S : ArmSolution ε c Tmax w pw) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + capReflTime ε c ≤ Tmax)
    (hwa : w a = 1 - 8 * ε) (hpa : pw a = c) :
    ∃ t₁ ∈ Ioc a (a + capReflTime ε c), w t₁ = 1 - 8 * ε ∧ pw t₁ = -c := by
  have hε := S.eps_pos
  have hc0 := S.c_pos
  have hτpos : 0 < capReflTime ε c := capReflTime_pos hε S.c_ge
  have hτle : capReflTime ε c ≤ 100 * ε := capReflTime_le hε S.c_ge S.c_le
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + capReflTime ε c ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, hb⟩
  have hsub : Icc a (a + capReflTime ε c) ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha hb
  have hnear : ∀ t ∈ Icc a (a + capReflTime ε c), 7 * ε ≤ w t := by
    intro t ht
    have h1 := abs_le.mp (S.travel_le hamem (hsub ht) ht.1)
    have h2 : c * (t - a) ≤ 2 * (100 * ε) := by
      have : t - a ≤ capReflTime ε c := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    have := S.eps_small
    linarith [h1.1]
  have hsetup : Reflection.Setup (wallPot ε) (ε / 4) ε 4 (4 / (exp 3 * ε)) (c ^ 2 / 2) (8 * ε)
      a (a + capReflTime ε c) (fun t => w t - 1) pw :=
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
      d_pos := by linarith
      hx := fun t ht =>
        ((hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht).sub_const 1
      hp := fun t ht => by
        have h := (hasDerivWithinAt_sub_interval S.ode_mom hamem hbmem) t ht
        rwa [deriv_armPot_cap hε (hnear t ht)] at h
      init_x := by rw [hwa]; ring
      init_p := by
        rw [hpa, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier hsetup
  refine ⟨t₁, ht₁, by linarith [hx₁], ?_⟩
  rw [hp₁, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]

/-- The dwell time of a junction-barrier passage of the arm: the router boundary sits at `8ε` and
the barrier foot at `7ε`, so the entry distance is `d = ε`. -/
noncomputable def armReflTime (ε c : ℝ) : ℝ :=
  reflectionTime (ε / 4) (4 / (exp 3 * ε)) (c ^ 2 / 2) ε

theorem armReflTime_pos (hε : 0 < ε) {c : ℝ} (hc : 1 ≤ c) : 0 < armReflTime ε c := by
  have hE : (0 : ℝ) < c ^ 2 / 2 := by nlinarith
  have h1 : 0 < Real.sqrt (c ^ 2 / 2) := Real.sqrt_pos.mpr hE
  have h2 : 0 < Real.sqrt (2 * (c ^ 2 / 2)) := Real.sqrt_pos.mpr (by linarith)
  have h3 : (0 : ℝ) < 4 / (exp 3 * ε) := by positivity
  unfold armReflTime reflectionTime
  have hA : 0 < 2 * (ε + ε / 4) / Real.sqrt (c ^ 2 / 2) := div_pos (by linarith) h1
  have hB : 0 < 3 * Real.sqrt (2 * (c ^ 2 / 2)) / (4 / (exp 3 * ε)) := div_pos (by linarith) h3
  linarith

theorem armReflTime_le_cap (hε : 0 < ε) {c : ℝ} (hc : 1 ≤ c) :
    armReflTime ε c ≤ capReflTime ε c := by
  have hE : (0 : ℝ) < c ^ 2 / 2 := by nlinarith
  have hs : (0 : ℝ) < Real.sqrt (c ^ 2 / 2) := Real.sqrt_pos.mpr hE
  unfold armReflTime capReflTime reflectionTime
  have h : 2 * (ε + ε / 4) / Real.sqrt (c ^ 2 / 2) ≤
      2 * (8 * ε + ε / 4) / Real.sqrt (c ^ 2 / 2) := by
    gcongr
    linarith
  linarith

/-- **Exact reflection at the junction barrier of the arm.**  This is the dynamical form of
`F⋆(η₃) = η₃`: a particle of the window arriving at the branching vertex along the third channel
is turned around and leaves along the third channel, with exactly reversed momentum. -/
theorem reflect_junction (S : ArmSolution ε c Tmax w pw) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + capReflTime ε c ≤ Tmax)
    (hwa : w a = 8 * ε) (hpa : pw a = -c) :
    ∃ t₁ ∈ Ioc a (a + capReflTime ε c), w t₁ = 8 * ε ∧ pw t₁ = c := by
  have hε := S.eps_pos
  have hc0 := S.c_pos
  have hτpos : 0 < capReflTime ε c := capReflTime_pos hε S.c_ge
  have hτle : capReflTime ε c ≤ 100 * ε := capReflTime_le hε S.c_ge S.c_le
  have hle : armReflTime ε c ≤ capReflTime ε c := armReflTime_le_cap hε S.c_ge
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hapos : 0 < armReflTime ε c := armReflTime_pos hε S.c_ge
  have hbmem : a + armReflTime ε c ∈ Icc (0 : ℝ) Tmax :=
    ⟨by linarith, by linarith⟩
  have hsub : Icc a (a + armReflTime ε c) ⊆ Icc (0 : ℝ) Tmax :=
    Icc_subset_Icc ha (by linarith)
  have hnear : ∀ t ∈ Icc a (a + armReflTime ε c), w t ≤ 1 := by
    intro t ht
    have h1 := abs_le.mp (S.travel_le hamem (hsub ht) ht.1)
    have h2 : c * (t - a) ≤ 2 * (100 * ε) := by
      have : t - a ≤ capReflTime ε c := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    have := S.eps_small
    linarith [h1.2]
  have hsetup : Reflection.Setup (wallPot ε) (ε / 4) ε 4 (4 / (exp 3 * ε)) (c ^ 2 / 2) ε
      a (a + armReflTime ε c) (fun t => 7 * ε - w t) (fun t => -pw t) :=
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
      d_pos := hε
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
        rw [hpa, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]; ring
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier hsetup
  have hx₁' : 7 * ε - w t₁ = -ε := hx₁
  have hp₁' : -pw t₁ = -Real.sqrt (2 * (c ^ 2 / 2)) := hp₁
  rw [show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le] at hp₁'
  have hbound : a + armReflTime ε c ≤ a + capReflTime ε c := by linarith
  exact ⟨t₁, ⟨ht₁.1, le_trans ht₁.2 hbound⟩, by linarith, by linarith⟩

end ArmSolution

/-! ### A genuine two-dimensional trajectory along the arm -/

/-- **A microscopic trajectory of the third arm.**  For a state on the axis of the arm with energy
in the window, there is a genuine trajectory of the two-dimensional Hamiltonian `H_ε` that stays
in the arm (`w > 6ε`), on the axis (`u = 0`), and whose longitudinal part is an `ArmSolution`.

This is the dynamical form of the `3 ↦ 3` half of the channel selection: the junction barrier of
the arm has height `4`, above the whole window `K⋆`, so the particle can never reach the
junction. -/
theorem exists_armTrajectory (hε : 0 < ε) (hεs : ε ≤ 1 / 1000) {c : ℝ} (hc1 : 1 ≤ c)
    (hc2 : c ≤ 2) (w₀ pw₀ : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hw₀ : 7 * ε ≤ w₀) (hw₀' : w₀ ≤ 1) (hpw₀ : pw₀ ^ 2 = c ^ 2) :
    ∃ w pw : ℝ → ℝ, w 0 = w₀ ∧ pw 0 = pw₀ ∧
      ArmSolution ε c T w pw ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => ((0 : ℝ), w s)) ((0 : ℝ), pw t) (Icc (0 : ℝ) T) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => ((0 : ℝ), pw s)) (microForce ε (0, w t))
          (Icc (0 : ℝ) T) t) := by
  obtain ⟨Ra, hRa0, hRa⟩ := exists_bound_deriv_armPot hε
  obtain ⟨w, pw, hw0, hpw0, hw, hpw⟩ :=
    exists_newton1D (contDiff_armPot ε (n := 2)) hRa0 hRa w₀ pw₀ hT
  have harm0 : armPot ε (w 0) = 0 := by
    rw [hw0, armPot_eq_wall, wallPot_of_nonpos hε (by linarith), wallPot_of_nonpos hε (by linarith),
      add_zero]
  have hen : ∀ t ∈ Icc (0 : ℝ) T, pw t ^ 2 / 2 + armPot ε (w t) = c ^ 2 / 2 := by
    intro t ht
    have h := energy1D_eq (contDiff_armPot ε (n := 1)) hw hpw t ht
    simp only [energy1D] at h
    rw [h, hpw0, harm0, hpw₀]
    ring
  have hS : ArmSolution ε c T w pw := ⟨hε, hεs, hc1, hc2, hT, hw, hpw, hen⟩
  refine ⟨w, pw, hw0, hpw0, hS, fun t ht => ?_, fun t ht => ?_⟩
  · exact ((hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt).prodMk (hw t ht)
  · have hforce : microForce ε ((0 : ℝ), w t) = ((0 : ℝ), -deriv (armPot ε) (w t)) := by
      have h := microForce_of_arm hε (x := ((0 : ℝ), w t)) (hS.gt_six ht)
      simp only at h
      rw [h, deriv_wellPot_of_abs_lt hε (show |(0 : ℝ)| < ε by rw [abs_zero]; exact hε), neg_zero]
    rw [hforce]
    exact ((hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt).prodMk (hpw t ht)

end HamiltonianMetricGraphs
