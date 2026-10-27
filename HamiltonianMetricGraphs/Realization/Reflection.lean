/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.Newton1D
import HamiltonianMetricGraphs.Realization.IntervalEstimates

/-!
# Reflection at a one-dimensional barrier

This is the analytic core of the microscopic router.  A particle enters a barrier region from the
flat side with energy `E` below the confining height `B` of the barrier.  We prove that it comes
back to its entry point with **exactly reversed momentum**, after a time bounded by the explicit

  `reflectionTime δ k E d = 2 (d + δ) / √E + 3 √(2E) / k`.

The proof is elementary and uses only conservation of energy plus mean-value estimates:

* the momentum is *antitone*, because `p' = -Φ'(x) ≤ 0` for a monotone barrier;
* while `x ≤ δ` the potential is at most `E/2`, hence `p² ≥ E` — the particle is fast near the
  foot of the barrier and cannot linger there;
* on `[δ, L]` the slope is at least `k`, hence `p' ≤ -k` — the particle is decelerated at a
  definite rate and must turn around;
* on the way back, at the entry point the potential vanishes again, so `p² = 2E` and the sign
  forces `p = -√(2E)`.

Since `√E` and `k` are explicit for the model's barrier (`BarrierProfile`), the dwell time is
`O(ε)`, which is what makes `dwell_tendsto` true.
-/

namespace HamiltonianMetricGraphs

open Set

/-- The explicit bound on the time a particle spends inside a reflecting barrier region. -/
noncomputable def reflectionTime (δ k E d : ℝ) : ℝ :=
  2 * (d + δ) / Real.sqrt E + 3 * Real.sqrt (2 * E) / k

/-- A continuous nowhere-vanishing function that starts positive stays positive. -/
theorem pos_on_of_ne_zero {f : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Icc a b))
    (hne : ∀ t ∈ Icc a b, f t ≠ 0) (ha : 0 < f a) : ∀ t ∈ Icc a b, 0 < f t := by
  intro t ht
  by_contra hcon
  rw [not_lt] at hcon
  have hneg : f t < 0 := lt_of_le_of_ne hcon (hne t ht)
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  obtain ⟨s, hs, hzero⟩ := intermediate_value_Icc' ht.1 (hc.mono hsub) ⟨hneg.le, ha.le⟩
  exact hne s (hsub hs) hzero

/-- Restrict a within-`Icc` derivative hypothesis to a subinterval. -/
theorem hasDerivWithinAt_sub_interval {f f' : ℝ → ℝ} {a b s t : ℝ}
    (hf : ∀ u ∈ Icc a b, HasDerivWithinAt f (f' u) (Icc a b) u)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∀ u ∈ Icc s t, HasDerivWithinAt f (f' u) (Icc s t) u := by
  intro u hu
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  exact (hf u (hsub hu)).mono hsub

namespace Reflection

variable {Φ : ℝ → ℝ} {δ L B k E d a b : ℝ} {x p : ℝ → ℝ}

/-- The hypotheses describing a reflecting barrier together with a trajectory entering it. -/
structure Setup (Φ : ℝ → ℝ) (δ L B k E d a b : ℝ) (x p : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 Φ
  nonneg : ∀ y, 0 ≤ Φ y
  flat : ∀ y ≤ (0 : ℝ), Φ y = 0
  mono : ∀ y, 0 ≤ deriv Φ y
  high : ∀ y, L ≤ y → B ≤ Φ y
  slope : ∀ y ∈ Icc δ L, k ≤ deriv Φ y
  low : ∀ y ≤ δ, Φ y ≤ E / 2
  δ_pos : 0 < δ
  δ_lt : δ < L
  k_pos : 0 < k
  E_pos : 0 < E
  E_lt : E < B
  d_pos : 0 < d
  hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (p t) (Icc a b) t
  hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (-deriv Φ (x t)) (Icc a b) t
  init_x : x a = -d
  init_p : p a = Real.sqrt (2 * E)
  long : a + reflectionTime δ k E d ≤ b

theorem le_b (S : Setup Φ δ L B k E d a b x p) : a ≤ b := by
  have h1 : 0 ≤ reflectionTime δ k E d := by
    have h2 : 0 < Real.sqrt E := Real.sqrt_pos.mpr S.E_pos
    have h3 : 0 ≤ Real.sqrt (2 * E) := Real.sqrt_nonneg _
    have := S.δ_pos
    have := S.d_pos
    have := S.k_pos
    unfold reflectionTime
    positivity
  linarith [S.long]

theorem sqrtE_pos (S : Setup Φ δ L B k E d a b x p) : 0 < Real.sqrt E :=
  Real.sqrt_pos.mpr S.E_pos

theorem sqrt2E_pos (S : Setup Φ δ L B k E d a b x p) : 0 < Real.sqrt (2 * E) :=
  Real.sqrt_pos.mpr (by linarith [S.E_pos])

theorem sq_sqrtE (S : Setup Φ δ L B k E d a b x p) : Real.sqrt E ^ 2 = E :=
  Real.sq_sqrt S.E_pos.le

theorem sq_sqrt2E (S : Setup Φ δ L B k E d a b x p) : Real.sqrt (2 * E) ^ 2 = 2 * E :=
  Real.sq_sqrt (by linarith [S.E_pos])

/-- The conserved energy of the trajectory is `E`. -/
theorem energy_eq (S : Setup Φ δ L B k E d a b x p) : energy1D Φ (x a) (p a) = E := by
  simp only [energy1D]
  rw [S.init_x, S.init_p, S.flat (-d) (by linarith [S.d_pos]), sq_sqrt2E S]
  ring

/-- The momentum–position relation along the trajectory. -/
theorem sq_mom (S : Setup Φ δ L B k E d a b x p) (t : ℝ) (ht : t ∈ Icc a b) :
    p t ^ 2 = 2 * (E - Φ (x t)) := by
  have h := sq_momentum_eq S.contDiff S.hx S.hp t ht
  rwa [energy_eq S] at h

/-- The potential never exceeds the energy. -/
theorem pot_le (S : Setup Φ δ L B k E d a b x p) (t : ℝ) (ht : t ∈ Icc a b) :
    Φ (x t) ≤ E := by
  have h := sq_mom S t ht
  nlinarith [sq_nonneg (p t)]

/-- **Confinement**: the particle never reaches the far side of the barrier. -/
theorem lt_L (S : Setup Φ δ L B k E d a b x p) (t : ℝ) (ht : t ∈ Icc a b) : x t < L := by
  by_contra hcon
  rw [not_lt] at hcon
  have h1 := S.high _ hcon
  have h2 := pot_le S t ht
  linarith [S.E_lt]

/-- The speed never exceeds the entry speed. -/
theorem abs_p_le (S : Setup Φ δ L B k E d a b x p) (t : ℝ) (ht : t ∈ Icc a b) :
    |p t| ≤ Real.sqrt (2 * E) := by
  have h := sq_mom S t ht
  have hn := S.nonneg (x t)
  have hsq : p t ^ 2 ≤ 2 * E := by linarith
  calc |p t| = Real.sqrt (p t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (2 * E) := Real.sqrt_le_sqrt hsq

/-- Near the foot of the barrier the particle keeps at least half its kinetic energy. -/
theorem sqrtE_le_abs_p (S : Setup Φ δ L B k E d a b x p) (t : ℝ) (ht : t ∈ Icc a b)
    (hxt : x t ≤ δ) : Real.sqrt E ≤ |p t| := by
  have h := sq_mom S t ht
  have hlow := S.low _ hxt
  have hsq : E ≤ p t ^ 2 := by linarith
  calc Real.sqrt E ≤ Real.sqrt (p t ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |p t| := Real.sqrt_sq_eq_abs _

/-- **The momentum is antitone**: the barrier only ever decelerates. -/
theorem p_antitone (S : Setup Φ δ L B k E d a b x p) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (hst : s ≤ t) : p t ≤ p s := by
  have hsub := hasDerivWithinAt_sub_interval S.hp hs ht
  have hbound : ∀ u ∈ Icc s t, -deriv Φ (x u) ≤ 0 := by
    intro u _
    linarith [S.mono (x u)]
  have := image_sub_le_mul_sub_of_hasDerivWithinAt_le hst hsub hbound
  linarith

/-- The position is antitone on any interval on which the momentum is nonpositive. -/
theorem x_antitone_of_p_nonpos (S : Setup Φ δ L B k E d a b x p) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hnp : ∀ u ∈ Icc s t, p u ≤ 0) : x t ≤ x s := by
  have hsub := hasDerivWithinAt_sub_interval S.hx hs ht
  have := image_sub_le_mul_sub_of_hasDerivWithinAt_le hst hsub hnp
  linarith

/-- The position is monotone on any interval on which the momentum is nonnegative. -/
theorem x_monotone_of_p_nonneg (S : Setup Φ δ L B k E d a b x p) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hnp : ∀ u ∈ Icc s t, 0 ≤ p u) : x s ≤ x t := by
  have hsub := hasDerivWithinAt_sub_interval S.hx hs ht
  have := mul_sub_le_image_sub_of_le_hasDerivWithinAt hst hsub hnp
  linarith

/-! ### The three phases -/

/-- `reflectionTime` split into the three phase durations. -/
theorem reflectionTime_eq (δ k E d : ℝ) :
    reflectionTime δ k E d =
      (d + δ) / Real.sqrt E + 3 * Real.sqrt (2 * E) / k + (d + δ) / Real.sqrt E := by
  unfold reflectionTime
  ring

/-- **Phase 1.**  The particle reaches the deceleration region `x ≥ δ` within time
`(d + δ)/√E`: near the foot of the barrier its potential is at most `E/2`, so it keeps at least
half its kinetic energy and cannot linger. -/
theorem exists_reach_delta (S : Setup Φ δ L B k E d a b x p) :
    ∃ t ∈ Icc a (a + (d + δ) / Real.sqrt E), a < t ∧ δ ≤ x t := by
  have hsE := sqrtE_pos S
  have hs2E := sqrt2E_pos S
  have hdδ : 0 < d + δ := by linarith [S.d_pos, S.δ_pos]
  have hT₁pos : 0 < (d + δ) / Real.sqrt E := by positivity
  have hT₂nn : 0 ≤ 3 * Real.sqrt (2 * E) / k := by have := S.k_pos; positivity
  have hlong := S.long
  rw [reflectionTime_eq] at hlong
  have hTb : a + (d + δ) / Real.sqrt E ≤ b := by linarith
  have hab1 : a ≤ a + (d + δ) / Real.sqrt E := by linarith
  have hsub : Icc a (a + (d + δ) / Real.sqrt E) ⊆ Icc a b := Icc_subset_Icc le_rfl hTb
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ t ∈ Icc a (a + (d + δ) / Real.sqrt E), x t < δ := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with heq | hgt
    · rw [← heq, S.init_x]; linarith [S.d_pos, S.δ_pos]
    · exact hcon t ht hgt
  have hne : ∀ t ∈ Icc a (a + (d + δ) / Real.sqrt E), p t ≠ 0 := by
    intro t ht h0
    have h1 := sqrtE_le_abs_p S t (hsub ht) (hlt t ht).le
    rw [h0, abs_zero] at h1
    linarith
  have hcont : ContinuousOn p (Icc a (a + (d + δ) / Real.sqrt E)) := fun t ht =>
    ((S.hp t (hsub ht)).continuousWithinAt).mono hsub
  have hpos : ∀ t ∈ Icc a (a + (d + δ) / Real.sqrt E), 0 < p t := by
    refine pos_on_of_ne_zero hcont hne ?_
    rw [S.init_p]
    exact hs2E
  have hge : ∀ t ∈ Icc a (a + (d + δ) / Real.sqrt E), Real.sqrt E ≤ p t := by
    intro t ht
    have h1 := sqrtE_le_abs_p S t (hsub ht) (hlt t ht).le
    rwa [abs_of_pos (hpos t ht)] at h1
  have hderiv := hasDerivWithinAt_sub_interval S.hx (left_mem_Icc.mpr (le_b S))
    (hsub (right_mem_Icc.mpr hab1))
  have hmvt := mul_sub_le_image_sub_of_le_hasDerivWithinAt hab1 hderiv hge
  have hcalc : Real.sqrt E * (a + (d + δ) / Real.sqrt E - a) = d + δ := by
    field_simp
    ring
  rw [hcalc, S.init_x] at hmvt
  have := hlt _ (right_mem_Icc.mpr hab1)
  linarith

/-- **Phase 2.**  Once in the deceleration region the particle is pushed back below `δ` within
time `3√(2E)/k`: the slope of the barrier is at least `k`, so the momentum decreases at that
rate, while it can never fall below `-√(2E)`. -/
theorem exists_return_below (S : Setup Φ δ L B k E d a b x p) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (_hxt₀ : δ ≤ x t₀)
    (hlong : t₀ + 3 * Real.sqrt (2 * E) / k ≤ b) :
    ∃ t ∈ Icc t₀ (t₀ + 3 * Real.sqrt (2 * E) / k), x t < δ := by
  have hs2E := sqrt2E_pos S
  have hkpos := S.k_pos
  have hT₂pos : 0 < 3 * Real.sqrt (2 * E) / k := by positivity
  have hab2 : t₀ ≤ t₀ + 3 * Real.sqrt (2 * E) / k := by linarith
  have hsub : Icc t₀ (t₀ + 3 * Real.sqrt (2 * E) / k) ⊆ Icc a b :=
    Icc_subset_Icc ht₀.1 hlong
  by_contra hcon
  push_neg at hcon
  have hslope : ∀ t ∈ Icc t₀ (t₀ + 3 * Real.sqrt (2 * E) / k), -deriv Φ (x t) ≤ -k := by
    intro t ht
    have h1 : x t ∈ Icc δ L := ⟨hcon t ht, (lt_L S t (hsub ht)).le⟩
    linarith [S.slope _ h1]
  have hderiv := hasDerivWithinAt_sub_interval S.hp (hsub (left_mem_Icc.mpr hab2))
    (hsub (right_mem_Icc.mpr hab2))
  have hmvt := image_sub_le_mul_sub_of_hasDerivWithinAt_le hab2 hderiv hslope
  have hcalc : -k * (t₀ + 3 * Real.sqrt (2 * E) / k - t₀) = -(3 * Real.sqrt (2 * E)) := by
    field_simp
    ring
  rw [hcalc] at hmvt
  have h1 := abs_le.mp (abs_p_le S t₀ (hsub (left_mem_Icc.mpr hab2)))
  have h2 := abs_le.mp (abs_p_le S _ (hsub (right_mem_Icc.mpr hab2)))
  linarith [h1.2, h2.1]

/-- **Phase 3.**  Moving back with speed at least `√E` the particle returns past its entry point
within time `(d + δ)/√E`. -/
theorem exists_return_entry (S : Setup Φ δ L B k E d a b x p) {t' : ℝ}
    (ht' : t' ∈ Icc a b) (hx' : x t' < δ) (hp' : p t' < 0)
    (hlong : t' + (d + δ) / Real.sqrt E ≤ b) :
    ∃ t ∈ Icc t' (t' + (d + δ) / Real.sqrt E), x t ≤ -d := by
  have hsE := sqrtE_pos S
  have hdδ : 0 < d + δ := by linarith [S.d_pos, S.δ_pos]
  have hT₃pos : 0 < (d + δ) / Real.sqrt E := by positivity
  have hab3 : t' ≤ t' + (d + δ) / Real.sqrt E := by linarith
  have hsub : Icc t' (t' + (d + δ) / Real.sqrt E) ⊆ Icc a b := Icc_subset_Icc ht'.1 hlong
  by_contra hcon
  push_neg at hcon
  have hpneg : ∀ t ∈ Icc t' (t' + (d + δ) / Real.sqrt E), p t ≤ p t' :=
    fun t ht => p_antitone S ht' (hsub ht) ht.1
  have hxle : ∀ t ∈ Icc t' (t' + (d + δ) / Real.sqrt E), x t ≤ x t' := by
    intro t ht
    refine x_antitone_of_p_nonpos S ht' (hsub ht) ht.1 ?_
    intro u hu
    have husub : u ∈ Icc t' (t' + (d + δ) / Real.sqrt E) := ⟨hu.1, le_trans hu.2 ht.2⟩
    linarith [hpneg u husub]
  have hle : ∀ t ∈ Icc t' (t' + (d + δ) / Real.sqrt E), p t ≤ -Real.sqrt E := by
    intro t ht
    have h1 := sqrtE_le_abs_p S t (hsub ht) (le_trans (hxle t ht) hx'.le)
    have h2 : p t < 0 := lt_of_le_of_lt (hpneg t ht) hp'
    rw [abs_of_neg h2] at h1
    linarith
  have hderiv := hasDerivWithinAt_sub_interval S.hx (hsub (left_mem_Icc.mpr hab3))
    (hsub (right_mem_Icc.mpr hab3))
  have hmvt := image_sub_le_mul_sub_of_hasDerivWithinAt_le hab3 hderiv hle
  have hcalc : -Real.sqrt E * (t' + (d + δ) / Real.sqrt E - t') = -(d + δ) := by
    field_simp
    ring
  rw [hcalc] at hmvt
  have := hcon _ (right_mem_Icc.mpr hab3)
  linarith

/-! ### The reflection theorem -/

/-- **Reflection at a monotone barrier.**  A particle entering the barrier region from the flat
side with energy `E` below the confining height `B` returns to its entry point `-d` with exactly
reversed momentum `-√(2E)`, within the explicit time `reflectionTime δ k E d`, and never reaches
the far side `L` of the barrier.

This is the microscopic router: the entry momentum `√(2E)` becomes the exit momentum `-√(2E)` —
an exact reflection, with no error at all — and the passage takes a time that is `O(ε)` for the
model's barrier, where `δ` and `d` are `O(ε)` and `k` is of order `1/ε`. -/
theorem reflect_of_barrier (S : Setup Φ δ L B k E d a b x p) :
    ∃ t₁ ∈ Ioc a (a + reflectionTime δ k E d),
      x t₁ = -d ∧ p t₁ = -Real.sqrt (2 * E) ∧ ∀ t ∈ Icc a t₁, x t < L := by
  have hsE := sqrtE_pos S
  have hs2E := sqrt2E_pos S
  have hkpos := S.k_pos
  have hdδ : 0 < d + δ := by linarith [S.d_pos, S.δ_pos]
  have hT₁ : 0 < (d + δ) / Real.sqrt E := by positivity
  have hT₂ : 0 < 3 * Real.sqrt (2 * E) / k := by positivity
  have hlong := S.long
  rw [reflectionTime_eq] at hlong
  -- Phase 1
  obtain ⟨t₀, ht₀mem, ht₀gt, hxt₀⟩ := exists_reach_delta S
  have ht₀b : t₀ ∈ Icc a b := ⟨ht₀mem.1, by linarith [ht₀mem.2]⟩
  -- Phase 2
  have hlong2 : t₀ + 3 * Real.sqrt (2 * E) / k ≤ b := by linarith [ht₀mem.2]
  obtain ⟨t', ht'mem, hx'⟩ := exists_return_below S ht₀b hxt₀ hlong2
  have ht'b : t' ∈ Icc a b :=
    ⟨le_trans ht₀b.1 ht'mem.1, le_trans ht'mem.2 hlong2⟩
  -- the momentum has become negative
  have hp' : p t' < 0 := by
    by_contra hcon
    push_neg at hcon
    have hnn : ∀ u ∈ Icc t₀ t', 0 ≤ p u := by
      intro u hu
      have hub : u ∈ Icc a b := ⟨le_trans ht₀b.1 hu.1, le_trans hu.2 ht'b.2⟩
      exact le_trans hcon (p_antitone S hub ht'b hu.2)
    have := x_monotone_of_p_nonneg S ht₀b ht'b ht'mem.1 hnn
    linarith
  -- Phase 3
  have hlong3 : t' + (d + δ) / Real.sqrt E ≤ b := by
    linarith [ht₀mem.2, ht'mem.2]
  obtain ⟨tb, htbmem, hxtb⟩ := exists_return_entry S ht'b hx' hp' hlong3
  have htbb : tb ∈ Icc a b :=
    ⟨le_trans ht'b.1 htbmem.1, le_trans htbmem.2 hlong3⟩
  have ht₀tb : t₀ ≤ tb := le_trans ht'mem.1 htbmem.1
  -- the position crosses the entry point
  have hcontx : ContinuousOn x (Icc t₀ tb) := by
    intro t ht
    have hsub : Icc t₀ tb ⊆ Icc a b := Icc_subset_Icc ht₀b.1 htbb.2
    exact ((S.hx t (hsub ht)).continuousWithinAt).mono hsub
  have hmem : -d ∈ Icc (x tb) (x t₀) := ⟨hxtb, by linarith [S.δ_pos, S.d_pos]⟩
  obtain ⟨t₁, ht₁mem, hxt₁⟩ := intermediate_value_Icc' ht₀tb hcontx hmem
  have ht₁b : t₁ ∈ Icc a b :=
    ⟨le_trans ht₀b.1 ht₁mem.1, le_trans ht₁mem.2 htbb.2⟩
  -- the momentum at the return time is negative
  have hsign : p t₁ < 0 := by
    by_contra hcon
    push_neg at hcon
    have hnn : ∀ u ∈ Icc t₀ t₁, 0 ≤ p u := by
      intro u hu
      have hub : u ∈ Icc a b := ⟨le_trans ht₀b.1 hu.1, le_trans hu.2 ht₁b.2⟩
      exact le_trans hcon (p_antitone S hub ht₁b hu.2)
    have hmono := x_monotone_of_p_nonneg S ht₀b ht₁b ht₁mem.1 hnn
    rw [hxt₁] at hmono
    linarith [S.δ_pos, S.d_pos]
  -- and by conservation of energy it is exactly reversed
  have hsq : p t₁ ^ 2 = 2 * E := by
    have h := sq_mom S t₁ ht₁b
    rw [hxt₁, S.flat (-d) (by linarith [S.d_pos])] at h
    linarith
  have habs : -p t₁ = Real.sqrt (2 * E) := by
    have : |p t₁| = Real.sqrt (2 * E) := by
      rw [← Real.sqrt_sq_eq_abs, hsq]
    rwa [abs_of_neg hsign] at this
  refine ⟨t₁, ⟨lt_of_lt_of_le ht₀gt ht₁mem.1, ?_⟩, hxt₁, by linarith, ?_⟩
  · rw [reflectionTime_eq]
    linarith [ht₀mem.2, ht'mem.2, htbmem.2, ht₁mem.2]
  · intro t ht
    exact lt_L S t ⟨ht.1, le_trans ht.2 ht₁b.2⟩

end Reflection

end HamiltonianMetricGraphs
