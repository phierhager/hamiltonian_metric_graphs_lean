/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.MicroscopicPotential
import HamiltonianMetricGraphs.Realization.Reflection

/-!
# The longitudinal dynamics of the through channel

This file analyses completely the one-dimensional motion

  `u' = p_u`,  `p_u' = -capPot ε '(u)`

which — by the exact separability of `microPot` in the through-channel region — is *exactly* the
longitudinal part of the microscopic Hamiltonian dynamics (`MicroscopicTrajectory.lean`).

The potential `capPot ε` is the sum of two copies of the single scaled barrier
`wallPot ε y = barrierProfile (y / ε)`, placed at the two outer vertices `u = ±1`:

  `capPot ε u = wallPot ε (u - 1) + wallPot ε (-u - 1)`.

Because `barrierProfile` vanishes identically on `(-∞, 0]`, together with its derivative, the two
barriers are *exactly* decoupled: near the right cap only `wallPot ε (u-1)` is active and near the
left cap only `wallPot ε (-u-1)`.  This is what lets the general reflection theorem
`Reflection.reflect_of_barrier` be applied verbatim.

## Main results

* `free` — **the motion between the caps is exactly free**: on any interval on which the particle
  cannot leave `[-1, 1]` the momentum is *constant* and the position affine.  This is the source of
  `odeErr = 0`.
* `reflect` — **the caps reflect exactly**: entering the router region at `u = ±(1 - 8ε)` with
  momentum `±c`, the particle returns to the same position with momentum `∓c` — an exact reversal,
  no error — within the time `capReflTime ε c ≤ 100 ε`.  This is the source of `momErr = 0` and of
  `dwell = O(ε)`.
-/

namespace HamiltonianMetricGraphs

open Set Real

/-! ### One scaled barrier -/

/-- One reflecting cap of the through channel, as a function of the signed distance `y` past the
outer vertex.  `capPot ε u = wallPot ε (u - 1) + wallPot ε (-u - 1)`. -/
noncomputable def wallPot (ε y : ℝ) : ℝ := barrierProfile (y / ε)

variable {ε c Tmax : ℝ} {u pu : ℝ → ℝ}

theorem contDiff_wallPot (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (wallPot ε) :=
  contDiff_barrierProfile.comp (contDiff_id.div_const ε)

theorem hasDerivAt_wallPot (ε y : ℝ) :
    HasDerivAt (wallPot ε) (deriv barrierProfile (y / ε) / ε) y := by
  have h1 : HasDerivAt (fun s : ℝ => s / ε) (1 / ε) y := by
    simpa using (hasDerivAt_id y).div_const ε
  have h2 : HasDerivAt barrierProfile (deriv barrierProfile (y / ε)) (y / ε) :=
    ((contDiff_barrierProfile (n := 1)).differentiable (by norm_num) _).hasDerivAt
  have h3 := h2.comp y h1
  have hrw : deriv barrierProfile (y / ε) * (1 / ε) = deriv barrierProfile (y / ε) / ε := by ring
  rw [hrw] at h3
  exact h3

theorem deriv_wallPot (ε y : ℝ) :
    deriv (wallPot ε) y = deriv barrierProfile (y / ε) / ε :=
  (hasDerivAt_wallPot ε y).deriv

/-- The derivative of the barrier profile vanishes on the flat side, **including at the foot**:
`expNegInvGlue` is flat to infinite order at `0`. -/
theorem deriv_barrierProfile_of_nonpos {s : ℝ} (h : s ≤ 0) : deriv barrierProfile s = 0 := by
  rw [deriv_barrierProfile, glue_of_nonpos h, mul_zero, mul_zero]

theorem wallPot_of_nonpos (hε : 0 < ε) {y : ℝ} (h : y ≤ 0) : wallPot ε y = 0 :=
  barrierProfile_of_nonpos (div_nonpos_of_nonpos_of_nonneg h hε.le)

theorem wallPot_nonneg (ε : ℝ) : ∀ y : ℝ, 0 ≤ wallPot ε y := fun _ => barrierProfile_nonneg _

theorem deriv_wallPot_nonneg (hε : 0 < ε) (y : ℝ) : 0 ≤ deriv (wallPot ε) y := by
  rw [deriv_wallPot]
  exact div_nonneg (deriv_barrierProfile_nonneg _) hε.le

/-- **Exact decoupling of the two caps.**  On the flat side the slope vanishes identically, so the
far cap contributes nothing to the force near the near cap. -/
theorem deriv_wallPot_of_nonpos (hε : 0 < ε) {y : ℝ} (h : y ≤ 0) :
    deriv (wallPot ε) y = 0 := by
  rw [deriv_wallPot, deriv_barrierProfile_of_nonpos (div_nonpos_of_nonpos_of_nonneg h hε.le),
    zero_div]

theorem wallPot_ge_of_le (hε : 0 < ε) {y : ℝ} (h : ε ≤ y) : 4 ≤ wallPot ε y := by
  refine barrierProfile_ge_of_one_le ?_
  rw [le_div_iff₀ hε]
  linarith

theorem wallPot_le_quarter (hε : 0 < ε) {y : ℝ} (h : y ≤ ε / 4) : wallPot ε y ≤ 1 / 4 := by
  refine barrierProfile_le_quarter ?_
  rw [div_le_iff₀ hε]
  linarith

/-- **Explicit deceleration of the scaled cap**: the slope is of order `1/ε` on the working
region, which is what makes the dwell time `O(ε)`. -/
theorem deriv_wallPot_ge (hε : 0 < ε) {y : ℝ} (h₁ : ε / 4 ≤ y) (h₂ : y ≤ ε) :
    4 / (exp 3 * ε) ≤ deriv (wallPot ε) y := by
  have hd : 4 / exp 3 ≤ deriv barrierProfile (y / ε) := by
    refine deriv_barrierProfile_ge ?_ ?_
    · rw [le_div_iff₀ hε]; linarith
    · rw [div_le_one hε]; exact h₂
  have hrw : (4 : ℝ) / (exp 3 * ε) = 4 / exp 3 / ε := by
    rw [div_div]
  rw [deriv_wallPot, hrw]
  gcongr

/-! ### The cap potential as a sum of two decoupled barriers -/

theorem capPot_eq_wall (ε u : ℝ) : capPot ε u = wallPot ε (u - 1) + wallPot ε (-u - 1) := rfl

theorem hasDerivAt_capPot (ε u : ℝ) :
    HasDerivAt (capPot ε) (deriv (wallPot ε) (u - 1) - deriv (wallPot ε) (-u - 1)) u := by
  have hw : ∀ y : ℝ, HasDerivAt (wallPot ε) (deriv (wallPot ε) y) y := fun y =>
    ((contDiff_wallPot ε (n := 1)).differentiable (by norm_num) y).hasDerivAt
  have e1 : HasDerivAt (fun s : ℝ => s - 1) 1 u := by
    simpa using (hasDerivAt_id u).sub_const 1
  have e2 : HasDerivAt (fun s : ℝ => -s - 1) (-1 : ℝ) u := by
    simpa using (hasDerivAt_id u).neg.sub_const 1
  have h1 := (hw (u - 1)).comp u e1
  have h2 := (hw (-u - 1)).comp u e2
  have h := h1.add h2
  have hrw : deriv (wallPot ε) (u - 1) * 1 + deriv (wallPot ε) (-u - 1) * (-1) =
      deriv (wallPot ε) (u - 1) - deriv (wallPot ε) (-u - 1) := by ring
  rw [hrw] at h
  exact h

theorem deriv_capPot_eq (ε u : ℝ) :
    deriv (capPot ε) u = deriv (wallPot ε) (u - 1) - deriv (wallPot ε) (-u - 1) :=
  (hasDerivAt_capPot ε u).deriv

/-- Near the right cap only the right barrier acts. -/
theorem deriv_capPot_right (hε : 0 < ε) {v : ℝ} (h : -1 ≤ v) :
    deriv (capPot ε) v = deriv (wallPot ε) (v - 1) := by
  rw [deriv_capPot_eq, deriv_wallPot_of_nonpos hε (y := -v - 1) (by linarith), sub_zero]

/-- Near the left cap only the left barrier acts. -/
theorem deriv_capPot_left (hε : 0 < ε) {v : ℝ} (h : v ≤ 1) :
    deriv (capPot ε) v = -deriv (wallPot ε) (-v - 1) := by
  rw [deriv_capPot_eq, deriv_wallPot_of_nonpos hε (y := v - 1) (by linarith), zero_sub]

/-- **No force inside the tube**: `capPot ε` is flat on the whole closed edge, caps included. -/
theorem deriv_capPot_of_abs_le_one (hε : 0 < ε) {v : ℝ} (h : |v| ≤ 1) :
    deriv (capPot ε) v = 0 := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  rw [deriv_capPot_eq, deriv_wallPot_of_nonpos hε (y := v - 1) (by linarith),
    deriv_wallPot_of_nonpos hε (y := -v - 1) (by linarith), sub_zero]

/-! ### The dwell time of a cap passage -/

/-- A numerical upper bound on `e³`. -/
theorem exp_three_le : exp 3 ≤ 21 := by
  have h : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h3 : exp 3 = exp 1 * (exp 1 * exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (1 : ℝ)]

/-- **The dwell time of one cap passage** of the model, at scale `ε` and speed `c`: the explicit
`reflectionTime` for the barrier `wallPot ε`, whose foot is at `δ = ε/4`, whose confining height
`4` is reached at `L = ε`, whose slope is at least `4/(e³ε)` in between, and which is entered from
the distance `d = 8ε`. -/
noncomputable def capReflTime (ε c : ℝ) : ℝ :=
  reflectionTime (ε / 4) (4 / (exp 3 * ε)) (c ^ 2 / 2) (8 * ε)

theorem capReflTime_pos (hε : 0 < ε) {c : ℝ} (hc : 1 ≤ c) : 0 < capReflTime ε c := by
  have hE : (0 : ℝ) < c ^ 2 / 2 := by nlinarith
  have h1 : 0 < Real.sqrt (c ^ 2 / 2) := Real.sqrt_pos.mpr hE
  have h2 : 0 < Real.sqrt (2 * (c ^ 2 / 2)) := Real.sqrt_pos.mpr (by linarith)
  have h3 : (0 : ℝ) < 4 / (exp 3 * ε) := by positivity
  unfold capReflTime reflectionTime
  have hA : 0 < 2 * (8 * ε + ε / 4) / Real.sqrt (c ^ 2 / 2) := by
    apply div_pos (by linarith) h1
  have hB : 0 < 3 * Real.sqrt (2 * (c ^ 2 / 2)) / (4 / (exp 3 * ε)) := by
    apply div_pos (by linarith) h3
  linarith

/-- **The dwell time is `O(ε)`.**  The two contributions are the crossing of the `O(ε)` router
region at speed `≥ √E`, and the turning time `3√(2E)/k` with the slope `k` of order `1/ε`. -/
theorem capReflTime_le (hε : 0 < ε) {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    capReflTime ε c ≤ 100 * ε := by
  have he : (0 : ℝ) < exp 3 := exp_pos 3
  have he21 : exp 3 ≤ 21 := exp_three_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hEpos : (0 : ℝ) < c ^ 2 / 2 := by nlinarith
  have hsE : (2 : ℝ) / 3 ≤ Real.sqrt (c ^ 2 / 2) := by
    have h49 : ((2 : ℝ) / 3) ^ 2 ≤ c ^ 2 / 2 := by nlinarith
    calc (2 : ℝ) / 3 = Real.sqrt (((2 : ℝ) / 3) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (c ^ 2 / 2) := Real.sqrt_le_sqrt h49
  have hs2E : Real.sqrt (2 * (c ^ 2 / 2)) = c := by
    rw [show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]
  have hsEpos : (0 : ℝ) < Real.sqrt (c ^ 2 / 2) := by linarith
  have h1 : 2 * (8 * ε + ε / 4) / Real.sqrt (c ^ 2 / 2) ≤ 25 * ε := by
    rw [div_le_iff₀ hsEpos]
    nlinarith [mul_le_mul_of_nonneg_left hsE (by positivity : (0 : ℝ) ≤ 25 * ε)]
  have h2 : 3 * Real.sqrt (2 * (c ^ 2 / 2)) / (4 / (exp 3 * ε)) ≤ 40 * ε := by
    rw [hs2E]
    have hk : (0 : ℝ) < 4 / (exp 3 * ε) := by positivity
    rw [div_le_iff₀ hk]
    have hr : (40 : ℝ) * ε * (4 / (exp 3 * ε)) = 160 / exp 3 := by
      field_simp
      ring
    rw [hr, le_div_iff₀ he]
    nlinarith
  unfold capReflTime reflectionTime
  linarith

/-! ### Exactly free motion in a flat region -/

/-- **Exactly free motion in a flat region.**  If the potential has vanishing derivative on
`[A, B]` and the *free* motion through the initial state stays strictly inside `(A, B)` during
`[a, b]`, then the true motion coincides with it: the momentum is *exactly* constant and the
position *exactly* affine.  This is the reason the model's `odeErr` is `0` and not merely small.

The bootstrap is the standard one: at the first time the true motion would reach the edge of the
flat region it still coincides with the free motion, which by hypothesis is strictly inside. -/
theorem free_motion {Φ : ℝ → ℝ} {A B : ℝ} (hΦ : ∀ y ∈ Icc A B, deriv Φ y = 0)
    {a b : ℝ} {q p : ℝ → ℝ} (hab : a ≤ b)
    (hq : ∀ t ∈ Icc a b, HasDerivWithinAt q (p t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (-deriv Φ (q t)) (Icc a b) t)
    (hbnd : ∀ t ∈ Icc a b, q a + p a * (t - a) ∈ Ioo A B) :
    ∀ t ∈ Icc a b, q t = q a + p a * (t - a) ∧ p t = p a := by
  set mid : ℝ := (A + B) / 2 with hmid
  set rad : ℝ := (B - A) / 2 with hrad
  have hle : ∀ y : ℝ, |y - mid| ≤ rad ↔ y ∈ Icc A B := by
    intro y
    rw [abs_le, mem_Icc, hmid, hrad]
    constructor <;> (intro h; constructor <;> linarith [h.1, h.2])
  have hlt : ∀ y : ℝ, |y - mid| < rad ↔ y ∈ Ioo A B := by
    intro y
    rw [abs_lt, mem_Ioo, hmid, hrad]
    constructor <;> (intro h; constructor <;> linarith [h.1, h.2])
  have hcontq : ContinuousOn q (Icc a b) := fun t ht => (hq t ht).continuousWithinAt
  have hcontabs : ContinuousOn (fun t => |q t - mid|) (Icc a b) :=
    (hcontq.sub continuousOn_const).abs
  have hqa : |q a - mid| < rad := by
    refine (hlt (q a)).mpr ?_
    simpa using hbnd a (left_mem_Icc.mpr hab)
  -- the motion cannot leave the flat region
  have hflat : ∀ t ∈ Icc a b, |q t - mid| ≤ rad := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨t₀, ht₀mem, ht₀⟩ := hcon
    have hZclosed : IsClosed (Icc a b ∩ (fun t => |q t - mid|) ⁻¹' Ici rad) :=
      hcontabs.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hZcpt : IsCompact (Icc a b ∩ (fun t => |q t - mid|) ⁻¹' Ici rad) :=
      isCompact_Icc.of_isClosed_subset hZclosed inter_subset_left
    obtain ⟨m, hmZ, hmin⟩ := hZcpt.exists_isLeast ⟨t₀, ht₀mem, ht₀.le⟩
    have hmab : m ∈ Icc a b := hmZ.1
    have hmr : rad ≤ |q m - mid| := hmZ.2
    have hma : a < m := by
      rcases eq_or_lt_of_le hmab.1 with heq | hlt'
      · rw [← heq] at hmr; linarith
      · exact hlt'
    have hin : ∀ s ∈ Ico a m, |q s - mid| < rad := by
      intro s hs
      by_contra hc
      rw [not_lt] at hc
      have hsZ : s ∈ Icc a b ∩ (fun t => |q t - mid|) ⁻¹' Ici rad :=
        ⟨⟨hs.1, le_trans hs.2.le hmab.2⟩, hc⟩
      exact absurd (hmin hsZ) (not_le.mpr hs.2)
    -- by continuity the motion is exactly at the edge at time `m`
    have hmeq : |q m - mid| = rad := by
      have hsubm : Icc a m ⊆ Icc a b := Icc_subset_Icc le_rfl hmab.2
      obtain ⟨m', hm', hval⟩ := intermediate_value_Icc hma.le (hcontabs.mono hsubm)
        (⟨hqa.le, hmr⟩ : rad ∈ Icc (|q a - mid|) (|q m - mid|))
      have hm'Z : m' ∈ Icc a b ∩ (fun t => |q t - mid|) ⁻¹' Ici rad :=
        ⟨⟨hm'.1, le_trans hm'.2 hmab.2⟩, hval.ge⟩
      have hm'm : m' = m := le_antisymm hm'.2 (hmin hm'Z)
      rw [← hm'm]; exact hval
    have hflatm : ∀ s ∈ Icc a m, |q s - mid| ≤ rad := by
      intro s hs
      rcases eq_or_lt_of_le hs.2 with heq | hlt'
      · rw [heq, hmeq]
      · exact (hin s ⟨hs.1, hlt'⟩).le
    -- on `[a, m]` the motion is still free, so it is strictly inside — contradiction
    have hsubm : Icc a m ⊆ Icc a b := Icc_subset_Icc le_rfl hmab.2
    have hd : ∀ v ∈ Icc a m, HasDerivWithinAt p (0 : ℝ) (Icc a m) v := by
      intro v hv
      have h := (hp v (hsubm hv)).mono hsubm
      rwa [hΦ _ ((hle _).mp (hflatm v hv)), neg_zero] at h
    have hmomconst : ∀ s ∈ Icc a m, p s = p a := by
      intro s hs
      have h := abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le
        (f := p) (f' := fun _ => (0 : ℝ)) (C := 0) hd (fun _ _ => by simp)
        (left_mem_Icc.mpr hma.le) hs hs.1
      have h0 : |p s - p a| ≤ 0 := by simpa using h
      linarith [abs_nonpos_iff.mp h0]
    have hd2 : ∀ v ∈ Icc a m, HasDerivWithinAt q (p a) (Icc a m) v := by
      intro v hv
      have h := (hq v (hsubm hv)).mono hsubm
      rwa [hmomconst v hv] at h
    have hup := image_sub_le_mul_sub_of_hasDerivWithinAt_le' (f := q) (f' := fun _ => p a)
      (C := p a) hd2 (fun _ _ => le_rfl) (left_mem_Icc.mpr hma.le)
      (right_mem_Icc.mpr hma.le) hma.le
    have hlo := mul_sub_le_image_sub_of_le_hasDerivWithinAt' (f := q) (f' := fun _ => p a)
      (C := p a) hd2 (fun _ _ => le_rfl) (left_mem_Icc.mpr hma.le)
      (right_mem_Icc.mpr hma.le) hma.le
    have hqm : q m = q a + p a * (m - a) := by linarith
    have hstrict := (hlt _).mpr (hbnd m hmab)
    rw [← hqm] at hstrict
    linarith
  -- hence no force, hence a constant momentum and an affine position
  have hforce : ∀ t ∈ Icc a b, deriv Φ (q t) = 0 := fun t ht => hΦ _ ((hle _).mp (hflat t ht))
  have hmom : ∀ t ∈ Icc a b, p t = p a := by
    have hd : ∀ v ∈ Icc a b, HasDerivWithinAt p (0 : ℝ) (Icc a b) v := by
      intro v hv
      have h := hp v hv
      rwa [hforce v hv, neg_zero] at h
    intro t ht
    have h := abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le
      (f := p) (f' := fun _ => (0 : ℝ)) (C := 0) hd (fun _ _ => by simp)
      (left_mem_Icc.mpr hab) ht ht.1
    have h0 : |p t - p a| ≤ 0 := by simpa using h
    linarith [abs_nonpos_iff.mp h0]
  refine fun t ht => ⟨?_, hmom t ht⟩
  have hd : ∀ v ∈ Icc a b, HasDerivWithinAt q (p a) (Icc a b) v := by
    intro v hv
    have h := hq v hv
    rwa [hmom v hv] at h
  have hup := image_sub_le_mul_sub_of_hasDerivWithinAt_le' (f := q) (f' := fun _ => p a)
    (C := p a) hd (fun _ _ => le_rfl) (left_mem_Icc.mpr hab) ht ht.1
  have hlo := mul_sub_le_image_sub_of_le_hasDerivWithinAt' (f := q) (f' := fun _ => p a)
    (C := p a) hd (fun _ _ => le_rfl) (left_mem_Icc.mpr hab) ht ht.1
  linarith

/-! ### Longitudinal solutions -/

/-- **A longitudinal solution of the through channel** on the time window `[0, Tmax]`, at scale
`ε` and energy `c²/2`.  These are exactly the hypotheses supplied by
`exists_microTrajectory`: the longitudinal pair of a genuine trajectory of the two-dimensional
microscopic Hamiltonian solves this system exactly, whatever the transverse motion does, because
`microPot` is an exact sum in the through-channel region. -/
structure CapSolution (ε c Tmax : ℝ) (u pu : ℝ → ℝ) : Prop where
  eps_pos : 0 < ε
  eps_small : ε ≤ 1 / 1000
  c_ge : 1 ≤ c
  c_le : c ≤ 2
  time_nonneg : 0 ≤ Tmax
  ode_pos : ∀ t ∈ Icc (0 : ℝ) Tmax, HasDerivWithinAt u (pu t) (Icc (0 : ℝ) Tmax) t
  ode_mom : ∀ t ∈ Icc (0 : ℝ) Tmax,
    HasDerivWithinAt pu (-deriv (capPot ε) (u t)) (Icc (0 : ℝ) Tmax) t
  energy : ∀ t ∈ Icc (0 : ℝ) Tmax, pu t ^ 2 / 2 + capPot ε (u t) = c ^ 2 / 2

namespace CapSolution

theorem c_pos (S : CapSolution ε c Tmax u pu) : 0 < c := by linarith [S.c_ge]

/-- The speed never exceeds the nominal speed `c`. -/
theorem abs_mom_le (S : CapSolution ε c Tmax u pu) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Tmax) :
    |pu t| ≤ c := by
  have h := S.energy t ht
  have hp := capPot_nonneg ε (u t)
  have hsq : pu t ^ 2 ≤ c ^ 2 := by linarith
  calc |pu t| = Real.sqrt (pu t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hsq
    _ = c := Real.sqrt_sq S.c_pos.le

/-- Travelled distance bound: the particle moves at speed at most `c`. -/
theorem travel_le (S : CapSolution ε c Tmax u pu) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) Tmax) (ht : t ∈ Icc (0 : ℝ) Tmax) (hst : s ≤ t) :
    |u t - u s| ≤ c * (t - s) :=
  abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le S.ode_pos
    (fun v hv => S.abs_mom_le hv) hs ht hst

/-- **The motion between the caps is exactly free.**  If the *free* motion through the initial
state stays strictly inside the closed edge during `[a, b]`, then so does the true motion, the
longitudinal potential is flat along the whole flight, the momentum is *exactly* constant and the
position *exactly* affine.  This is the reason the model's `odeErr` is `0` and not merely small.

The bootstrap is the standard one: at the first time the true motion would reach the edge of the
flat region it still coincides with the free motion, which by hypothesis is strictly inside. -/
theorem free (S : CapSolution ε c Tmax u pu) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (hbnd : ∀ t ∈ Icc a b, |u a + pu a * (t - a)| < 1) :
    ∀ t ∈ Icc a b, u t = u a + pu a * (t - a) ∧ pu t = pu a := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha.1 hb.2
  refine free_motion (Φ := capPot ε) (A := -1) (B := 1)
    (fun y hy => deriv_capPot_of_abs_le_one S.eps_pos (abs_le.mpr ⟨hy.1, hy.2⟩)) hab
    (fun t ht => (S.ode_pos t (hsub ht)).mono hsub)
    (fun t ht => (S.ode_mom t (hsub ht)).mono hsub) (fun t ht => ?_)
  exact mem_Ioo.mpr (abs_lt.mp (hbnd t ht))

/-- The convenient form of `free`: it is enough to check the two endpoints, because the free
motion is affine. -/
theorem free_of_endpoints (S : CapSolution ε c Tmax u pu) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (hab : a ≤ b)
    (h1 : |u a| < 1) (h2 : |u a + pu a * (b - a)| < 1) :
    ∀ t ∈ Icc a b, u t = u a + pu a * (t - a) ∧ pu t = pu a := by
  refine S.free ha hb hab ?_
  intro t ht
  rw [abs_lt] at h1 h2 ⊢
  rcases le_or_gt 0 (pu a) with hs | hs
  · exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  · exact ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩

/-! #### Reflection at the caps -/

/-- **Exact reflection at the right cap.**  Entering the router region at `u = 1 - 8ε` with
momentum `+c`, the particle returns to `u = 1 - 8ε` with momentum exactly `-c`, within the time
`capReflTime ε c = O(ε)`. -/
theorem reflect_right (S : CapSolution ε c Tmax u pu) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + capReflTime ε c ≤ Tmax)
    (hua : u a = 1 - 8 * ε) (hpa : pu a = c) :
    ∃ t₁ ∈ Ioc a (a + capReflTime ε c), u t₁ = 1 - 8 * ε ∧ pu t₁ = -c := by
  have hε := S.eps_pos
  have hc0 := S.c_pos
  have hτpos : 0 < capReflTime ε c := capReflTime_pos hε S.c_ge
  have hτle : capReflTime ε c ≤ 100 * ε := capReflTime_le hε S.c_ge S.c_le
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + capReflTime ε c ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, hb⟩
  have hsub : Icc a (a + capReflTime ε c) ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha hb
  -- the passage is short, so the particle stays on the right half of the tube
  have hnear : ∀ t ∈ Icc a (a + capReflTime ε c), 0 ≤ u t := by
    intro t ht
    have h1 := abs_le.mp (S.travel_le hamem (hsub ht) ht.1)
    have h2 : c * (t - a) ≤ 2 * (100 * ε) := by
      have : t - a ≤ capReflTime ε c := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    have := S.eps_small
    linarith [h1.1]
  have hsetup : Reflection.Setup (wallPot ε) (ε / 4) ε 4 (4 / (exp 3 * ε)) (c ^ 2 / 2) (8 * ε)
      a (a + capReflTime ε c) (fun t => u t - 1) pu :=
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
        rwa [deriv_capPot_right hε (by linarith [hnear t ht])] at h
      init_x := by rw [hua]; ring
      init_p := by
        rw [hpa, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier hsetup
  refine ⟨t₁, ht₁, by linarith [hx₁], ?_⟩
  rw [hp₁, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]

/-- **Exact reflection at the left cap**, by the mirror symmetry `capPot ε (-v) = capPot ε v`. -/
theorem reflect_left (S : CapSolution ε c Tmax u pu) {a : ℝ}
    (ha : 0 ≤ a) (hb : a + capReflTime ε c ≤ Tmax)
    (hua : u a = -(1 - 8 * ε)) (hpa : pu a = -c) :
    ∃ t₁ ∈ Ioc a (a + capReflTime ε c), u t₁ = -(1 - 8 * ε) ∧ pu t₁ = c := by
  have hε := S.eps_pos
  have hc0 := S.c_pos
  have hτpos : 0 < capReflTime ε c := capReflTime_pos hε S.c_ge
  have hτle : capReflTime ε c ≤ 100 * ε := capReflTime_le hε S.c_ge S.c_le
  have hamem : a ∈ Icc (0 : ℝ) Tmax := ⟨ha, by linarith⟩
  have hbmem : a + capReflTime ε c ∈ Icc (0 : ℝ) Tmax := ⟨by linarith, hb⟩
  have hsub : Icc a (a + capReflTime ε c) ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha hb
  have hnear : ∀ t ∈ Icc a (a + capReflTime ε c), u t ≤ 0 := by
    intro t ht
    have h1 := abs_le.mp (S.travel_le hamem (hsub ht) ht.1)
    have h2 : c * (t - a) ≤ 2 * (100 * ε) := by
      have : t - a ≤ capReflTime ε c := by linarith [ht.2]
      nlinarith [S.c_le, ht.1]
    have := S.eps_small
    linarith [h1.2]
  have hsetup : Reflection.Setup (wallPot ε) (ε / 4) ε 4 (4 / (exp 3 * ε)) (c ^ 2 / 2) (8 * ε)
      a (a + capReflTime ε c) (fun t => -u t - 1) (fun t => -pu t) :=
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
        rw [hpa, show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le]; ring
      long := le_rfl }
  obtain ⟨t₁, ht₁, hx₁, hp₁, -⟩ := Reflection.reflect_of_barrier hsetup
  have hx₁' : -u t₁ - 1 = -(8 * ε) := hx₁
  have hp₁' : -pu t₁ = -Real.sqrt (2 * (c ^ 2 / 2)) := hp₁
  rw [show 2 * (c ^ 2 / 2) = c ^ 2 by ring, Real.sqrt_sq hc0.le] at hp₁'
  exact ⟨t₁, ht₁, by linarith, by linarith⟩

/-- **The cap reflection, uniformly in the side.**  `s = ±1` selects the right or the left cap;
in both cases the momentum is reversed exactly. -/
theorem reflect (S : CapSolution ε c Tmax u pu) {a s : ℝ} (hs : s = 1 ∨ s = -1)
    (ha : 0 ≤ a) (hb : a + capReflTime ε c ≤ Tmax)
    (hua : u a = s * (1 - 8 * ε)) (hpa : pu a = s * c) :
    ∃ t₁ ∈ Ioc a (a + capReflTime ε c), u t₁ = s * (1 - 8 * ε) ∧ pu t₁ = -(s * c) := by
  rcases hs with rfl | rfl
  · obtain ⟨t₁, ht₁, h1, h2⟩ := S.reflect_right ha hb (by linarith [hua]) (by linarith [hpa])
    exact ⟨t₁, ht₁, by linarith, by linarith⟩
  · obtain ⟨t₁, ht₁, h1, h2⟩ := S.reflect_left ha hb (by linarith [hua]) (by linarith [hpa])
    exact ⟨t₁, ht₁, by linarith, by linarith⟩

end CapSolution

end HamiltonianMetricGraphs
