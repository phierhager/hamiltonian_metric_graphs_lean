/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.CapDynamics

/-!
# The universal corridor: longitudinal dynamics on an interval of arbitrary length

The universal microscopic network of `(Γ, F)` is a finite family of **straight parallel
corridors**.  This file analyses the longitudinal dynamics inside one corridor of arbitrary
length `Λ`:

  `corridorPot ε Λ u = wallPot ε (u - Λ) + wallPot ε (-u)`,

which vanishes identically on `[0, Λ]` and rises to the confining height `4` outside
`[-ε, Λ + ε]`.  Everything is the analysis of `CapDynamics.lean` for the interval `[-1, 1]`,
carried out for an arbitrary interval `[0, Λ]`; the two caps stay exactly decoupled because
`barrierProfile` vanishes together with its derivative on the whole flat side.

## Main results

* `CorridorSolution.free` — the motion between the caps is *exactly* free, so the projected
  longitudinal dynamics has `odeErr = 0`;
* `CorridorSolution.reflect_top`, `reflect_bot`, `reflect` — each cap reverses the momentum
  *exactly*, within `capReflTime ε c ≤ 100 ε`, so `momErr = 0` and `dwell = O(ε)`.

Both hold for **every** corridor length `Λ` with `1000 ε ≤ Λ`, which is the only smallness
assumption; it is satisfied eventually as `ε → 0⁺` for each of the finitely many corridors.
-/

namespace HamiltonianMetricGraphs

open Set Real

variable {ε Λ c Tmax : ℝ} {u pu : ℝ → ℝ}

/-! ### The corridor potential -/

/-- **The longitudinal potential of a corridor of length `Λ`**: reflecting caps at both ends and
nothing in between. -/
noncomputable def corridorPot (ε Λ u : ℝ) : ℝ := wallPot ε (u - Λ) + wallPot ε (-u)

theorem contDiff_corridorPot (ε Λ : ℝ) {n : ℕ∞} : ContDiff ℝ n (corridorPot ε Λ) := by
  apply ContDiff.add
  · exact (contDiff_wallPot ε).comp (contDiff_id.sub contDiff_const)
  · exact (contDiff_wallPot ε).comp contDiff_id.neg

theorem corridorPot_nonneg (ε Λ u : ℝ) : 0 ≤ corridorPot ε Λ u :=
  add_nonneg (wallPot_nonneg ε _) (wallPot_nonneg ε _)

/-- **The corridor is flat.** -/
theorem corridorPot_of_mem (hε : 0 < ε) {u : ℝ} (h₁ : 0 ≤ u) (h₂ : u ≤ Λ) :
    corridorPot ε Λ u = 0 := by
  rw [corridorPot, wallPot_of_nonpos hε (by linarith), wallPot_of_nonpos hε (by linarith),
    add_zero]

/-- Beyond the top cap the potential is at the confining height. -/
theorem corridorPot_ge_of_top (hε : 0 < ε) {u : ℝ} (h : Λ + ε ≤ u) : 4 ≤ corridorPot ε Λ u := by
  have hb : 4 ≤ wallPot ε (u - Λ) := wallPot_ge_of_le hε (by linarith)
  have := wallPot_nonneg ε (-u)
  rw [corridorPot]
  linarith

/-- Beyond the bottom cap the potential is at the confining height. -/
theorem corridorPot_ge_of_bot (hε : 0 < ε) {u : ℝ} (h : u ≤ -ε) : 4 ≤ corridorPot ε Λ u := by
  have hb : 4 ≤ wallPot ε (-u) := wallPot_ge_of_le hε (by linarith)
  have := wallPot_nonneg ε (u - Λ)
  rw [corridorPot]
  linarith

theorem hasDerivAt_corridorPot (ε Λ u : ℝ) :
    HasDerivAt (corridorPot ε Λ)
      (deriv (wallPot ε) (u - Λ) - deriv (wallPot ε) (-u)) u := by
  have hw : ∀ y : ℝ, HasDerivAt (wallPot ε) (deriv (wallPot ε) y) y := fun y =>
    ((contDiff_wallPot ε (n := 1)).differentiable (by norm_num) y).hasDerivAt
  have e1 : HasDerivAt (fun s : ℝ => s - Λ) 1 u := by
    simpa using (hasDerivAt_id u).sub_const Λ
  have e2 : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) u := by
    simpa using (hasDerivAt_id u).const_sub (0 : ℝ)
  have h1 := (hw (u - Λ)).comp u e1
  have h2 := (hw (-u)).comp u e2
  have h := h1.add h2
  have hrw : deriv (wallPot ε) (u - Λ) * 1 + deriv (wallPot ε) (-u) * (-1) =
      deriv (wallPot ε) (u - Λ) - deriv (wallPot ε) (-u) := by ring
  rw [hrw] at h
  exact h

theorem deriv_corridorPot_eq (ε Λ u : ℝ) :
    deriv (corridorPot ε Λ) u = deriv (wallPot ε) (u - Λ) - deriv (wallPot ε) (-u) :=
  (hasDerivAt_corridorPot ε Λ u).deriv

/-- Near the top cap only that cap acts. -/
theorem deriv_corridorPot_top (hε : 0 < ε) {v : ℝ} (h : 0 ≤ v) :
    deriv (corridorPot ε Λ) v = deriv (wallPot ε) (v - Λ) := by
  rw [deriv_corridorPot_eq, deriv_wallPot_of_nonpos hε (y := -v) (by linarith), sub_zero]

/-- Near the bottom cap only that cap acts. -/
theorem deriv_corridorPot_bot (hε : 0 < ε) {v : ℝ} (h : v ≤ Λ) :
    deriv (corridorPot ε Λ) v = -deriv (wallPot ε) (-v) := by
  rw [deriv_corridorPot_eq, deriv_wallPot_of_nonpos hε (y := v - Λ) (by linarith), zero_sub]

/-- **No force inside the corridor.** -/
theorem deriv_corridorPot_of_mem (hε : 0 < ε) {v : ℝ} (h₁ : 0 ≤ v) (h₂ : v ≤ Λ) :
    deriv (corridorPot ε Λ) v = 0 := by
  rw [deriv_corridorPot_eq, deriv_wallPot_of_nonpos hε (y := v - Λ) (by linarith),
    deriv_wallPot_of_nonpos hε (y := -v) (by linarith), sub_zero]

theorem corridorPot_eq_affine (hε : ε ≠ 0) (Λ : ℝ) :
    corridorPot ε Λ = fun v => barrierProfile (ε⁻¹ * v + -(ε⁻¹ * Λ)) +
      barrierProfile (-ε⁻¹ * v + 0) := by
  funext v
  rw [corridorPot, wallPot, wallPot]
  congr 2 <;> field_simp <;> ring

/-- The longitudinal force in a corridor is globally bounded. -/
theorem exists_bound_deriv_corridorPot (hε : 0 < ε) (Λ : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v, |deriv (corridorPot ε Λ) v| ≤ R := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_barrierProfile
  refine ⟨M * |ε⁻¹| + M * |(-ε⁻¹)|, by positivity, fun v => ?_⟩
  rw [corridorPot_eq_affine (ne_of_gt hε) Λ]
  have hd : Differentiable ℝ barrierProfile :=
    (contDiff_barrierProfile (n := 1)).differentiable (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => ε⁻¹ * s + -(ε⁻¹ * Λ)) ε⁻¹ v := by
    simpa using ((hasDerivAt_id v).const_mul ε⁻¹).add_const (-(ε⁻¹ * Λ))
  have h2 : HasDerivAt (fun s : ℝ => -ε⁻¹ * s + 0) (-ε⁻¹) v := by
    simpa using ((hasDerivAt_id v).const_mul (-ε⁻¹)).add_const (0 : ℝ)
  have g1 : HasDerivAt (fun s => barrierProfile (ε⁻¹ * s + -(ε⁻¹ * Λ)))
      (deriv barrierProfile (ε⁻¹ * v + -(ε⁻¹ * Λ)) * ε⁻¹) v := ((hd _).hasDerivAt).comp v h1
  have g2 : HasDerivAt (fun s => barrierProfile (-ε⁻¹ * s + 0))
      (deriv barrierProfile (-ε⁻¹ * v + 0) * -ε⁻¹) v := ((hd _).hasDerivAt).comp v h2
  have g12 : HasDerivAt (fun s => barrierProfile (ε⁻¹ * s + -(ε⁻¹ * Λ)) +
      barrierProfile (-ε⁻¹ * s + 0))
      (deriv barrierProfile (ε⁻¹ * v + -(ε⁻¹ * Λ)) * ε⁻¹ +
        deriv barrierProfile (-ε⁻¹ * v + 0) * -ε⁻¹) v := g1.add g2
  rw [g12.deriv]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_) <;> rw [abs_mul] <;>
    exact mul_le_mul (hM _) le_rfl (abs_nonneg _) hM0

/-! ### Solutions inside a corridor -/

/-- **A longitudinal solution inside a corridor** of length `Λ` on the time window `[0, Tmax]`,
at scale `ε` and energy `c²/2`.  The only smallness assumption is `1000 ε ≤ Λ`: the corridor is
long compared with the routers. -/
structure CorridorSolution (ε Λ c Tmax : ℝ) (u pu : ℝ → ℝ) : Prop where
  eps_pos : 0 < ε
  len : 1000 * ε ≤ Λ
  c_ge : 1 ≤ c
  c_le : c ≤ 2
  time_nonneg : 0 ≤ Tmax
  ode_pos : ∀ t ∈ Icc (0 : ℝ) Tmax, HasDerivWithinAt u (pu t) (Icc (0 : ℝ) Tmax) t
  ode_mom : ∀ t ∈ Icc (0 : ℝ) Tmax,
    HasDerivWithinAt pu (-deriv (corridorPot ε Λ) (u t)) (Icc (0 : ℝ) Tmax) t
  energy : ∀ t ∈ Icc (0 : ℝ) Tmax, pu t ^ 2 / 2 + corridorPot ε Λ (u t) = c ^ 2 / 2

namespace CorridorSolution

theorem c_pos (S : CorridorSolution ε Λ c Tmax u pu) : 0 < c := by linarith [S.c_ge]

theorem eps_pos' (S : CorridorSolution ε Λ c Tmax u pu) : 0 < ε := S.eps_pos

theorem len_pos (S : CorridorSolution ε Λ c Tmax u pu) : 0 < Λ := by
  have := S.eps_pos
  linarith [S.len]

theorem abs_mom_le (S : CorridorSolution ε Λ c Tmax u pu) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) Tmax) : |pu t| ≤ c := by
  have h := S.energy t ht
  have hp := corridorPot_nonneg ε Λ (u t)
  have hsq : pu t ^ 2 ≤ c ^ 2 := by linarith
  calc |pu t| = Real.sqrt (pu t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hsq
    _ = c := Real.sqrt_sq S.c_pos.le

theorem travel_le (S : CorridorSolution ε Λ c Tmax u pu) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) Tmax) (ht : t ∈ Icc (0 : ℝ) Tmax) (hst : s ≤ t) :
    |u t - u s| ≤ c * (t - s) :=
  abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le S.ode_pos
    (fun v hv => S.abs_mom_le hv) hs ht hst

/-- **The motion inside a corridor is exactly free.** -/
theorem free (S : CorridorSolution ε Λ c Tmax u pu) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (hbnd : ∀ t ∈ Icc a b, u a + pu a * (t - a) ∈ Ioo 0 Λ) :
    ∀ t ∈ Icc a b, u t = u a + pu a * (t - a) ∧ pu t = pu a := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha.1 hb.2
  exact free_motion (Φ := corridorPot ε Λ) (A := 0) (B := Λ)
    (fun y hy => deriv_corridorPot_of_mem S.eps_pos hy.1 hy.2) hab
    (fun t ht => (S.ode_pos t (hsub ht)).mono hsub)
    (fun t ht => (S.ode_mom t (hsub ht)).mono hsub) hbnd

/-- The convenient form: it is enough to check the two endpoints. -/
theorem free_of_endpoints (S : CorridorSolution ε Λ c Tmax u pu) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (h1 : u a ∈ Ioo 0 Λ) (h2 : u a + pu a * (b - a) ∈ Ioo 0 Λ) :
    ∀ t ∈ Icc a b, u t = u a + pu a * (t - a) ∧ pu t = pu a := by
  refine S.free ha hb hab ?_
  intro t ht
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  rcases le_or_gt 0 (pu a) with hs | hs
  · exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  · exact ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩

/-! #### Reflection at the two caps -/

/-- **Exact reflection at the top cap.**  Entering the router region at `u = Λ - 8ε` with
momentum `+c`, the particle returns to `u = Λ - 8ε` with momentum exactly `-c`, within the time
`capReflTime ε c ≤ 100 ε`. -/
theorem reflect_top (S : CorridorSolution ε Λ c Tmax u pu) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + capReflTime ε c ≤ Tmax)
    (hua : u a = Λ - 8 * ε) (hpa : pu a = c) :
    ∃ t₁ ∈ Ioc a (a + capReflTime ε c), u t₁ = Λ - 8 * ε ∧ pu t₁ = -c := by
  have hε := S.eps_pos
  have hc0 := S.c_pos
  have hlen := S.len
  have hτpos : 0 < capReflTime ε c := capReflTime_pos hε S.c_ge
  have hτle : capReflTime ε c ≤ 100 * ε := capReflTime_le hε S.c_ge S.c_le
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + capReflTime ε c ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, hb⟩
  have hsub : Icc a (a + capReflTime ε c) ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha hb
  have hnear : ∀ t ∈ Icc a (a + capReflTime ε c), 0 ≤ u t := by
    intro t ht
    have h1 := abs_le.mp (S.travel_le hamem (hsub ht) ht.1)
    have h2 : c * (t - a) ≤ 2 * (100 * ε) := by
      have : t - a ≤ capReflTime ε c := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    linarith [h1.1]
  have hsetup : Reflection.Setup (wallPot ε) (ε / 4) ε 4 (4 / (exp 3 * ε)) (c ^ 2 / 2) (8 * ε)
      a (a + capReflTime ε c) (fun t => u t - Λ) pu :=
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
        ((hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht).sub_const Λ
      hp := fun t ht => by
        have h := (hasDerivWithinAt_sub_interval S.ode_mom hamem hbmem) t ht
        rwa [deriv_corridorPot_top hε (hnear t ht)] at h
      init_x := by rw [hua]; ring
      init_p := by
        rw [hpa, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier hsetup
  refine ⟨t₁, ht₁, by linarith [hx₁], ?_⟩
  rw [hp₁, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]

/-- **Exact reflection at the bottom cap.** -/
theorem reflect_bot (S : CorridorSolution ε Λ c Tmax u pu) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + capReflTime ε c ≤ Tmax)
    (hua : u a = 8 * ε) (hpa : pu a = -c) :
    ∃ t₁ ∈ Ioc a (a + capReflTime ε c), u t₁ = 8 * ε ∧ pu t₁ = c := by
  have hε := S.eps_pos
  have hc0 := S.c_pos
  have hlen := S.len
  have hτpos : 0 < capReflTime ε c := capReflTime_pos hε S.c_ge
  have hτle : capReflTime ε c ≤ 100 * ε := capReflTime_le hε S.c_ge S.c_le
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + capReflTime ε c ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, hb⟩
  have hsub : Icc a (a + capReflTime ε c) ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha hb
  have hnear : ∀ t ∈ Icc a (a + capReflTime ε c), u t ≤ Λ := by
    intro t ht
    have h1 := abs_le.mp (S.travel_le hamem (hsub ht) ht.1)
    have h2 : c * (t - a) ≤ 2 * (100 * ε) := by
      have : t - a ≤ capReflTime ε c := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    linarith [h1.2]
  have hsetup : Reflection.Setup (wallPot ε) (ε / 4) ε 4 (4 / (exp 3 * ε)) (c ^ 2 / 2) (8 * ε)
      a (a + capReflTime ε c) (fun t => -u t) (fun t => -pu t) :=
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
        ((hasDerivWithinAt_sub_interval S.ode_pos hamem hbmem) t ht).neg
      hp := fun t ht => by
        have h := ((hasDerivWithinAt_sub_interval S.ode_mom hamem hbmem) t ht).neg
        rw [neg_neg, deriv_corridorPot_bot hε (hnear t ht)] at h
        exact h
      init_x := by
        show -u a = -(8 * ε)
        rw [hua]
      init_p := by
        show -pu a = Real.sqrt (2 * (c ^ 2 / 2))
        rw [hpa, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]; ring
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier hsetup
  have hx₁' : -u t₁ = -(8 * ε) := hx₁
  have hp₁' : -pu t₁ = -Real.sqrt (2 * (c ^ 2 / 2)) := hp₁
  rw [show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le] at hp₁'
  exact ⟨t₁, ht₁, by linarith, by linarith⟩

/-- **The cap reflection, uniformly in the side**: `s = 1` is the top cap, `s = -1` the bottom
one.  In both cases the momentum is reversed exactly and the position is unchanged. -/
theorem reflect (S : CorridorSolution ε Λ c Tmax u pu) {a s : ℝ} (hs : s = 1 ∨ s = -1)
    (ha : 0 ≤ a) (hb : a + capReflTime ε c ≤ Tmax)
    (hua : u a = (Λ / 2) + s * (Λ / 2 - 8 * ε)) (hpa : pu a = s * c) :
    ∃ t₁ ∈ Ioc a (a + capReflTime ε c),
      u t₁ = (Λ / 2) + s * (Λ / 2 - 8 * ε) ∧ pu t₁ = -(s * c) := by
  rcases hs with rfl | rfl
  · obtain ⟨t₁, ht₁, h1, h2⟩ := S.reflect_top ha hb (by linarith [hua]) (by linarith [hpa])
    exact ⟨t₁, ht₁, by linarith, by linarith⟩
  · obtain ⟨t₁, ht₁, h1, h2⟩ := S.reflect_bot ha hb (by linarith [hua]) (by linarith [hpa])
    exact ⟨t₁, ht₁, by linarith, by linarith⟩

end CorridorSolution

end HamiltonianMetricGraphs
