/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalCorridor

/-!
# The longitudinal motion in an interval corridor is close to the billiard

Inside the corridor of an interval component the longitudinal motion solves `ü = -P'(u)`, with
`P` the two caps `B(-u/ε) + B((u - L)/ε)` (`CorridorSolution`).  The motion is free on `[0, L]`, and
by the cap reflection lemma (`CorridorSolution.reflect`, Lemma IX.3 of the paper) each excursion
beyond an endpoint lasts `O(ε)` and returns with reversed velocity.

Deleting the excursions turns the motion into the billiard on `[0, L]`: in the lifted coordinate
`ρ u + 2 L n` (`ρ = ±1`, `n ∈ ℤ`) the particle moves uniformly, like `s̄(t) = u(0) + ξ t`, up to a
drift of `216 ε` per excursion.  This file proves that, on a time window `[0, T]` with at most `K`
excursions, at every time `t` either `s̄(t)` is within `(K + 1) · 216 ε` of a point of `L ℤ`
(an endpoint of the billiard), or the particle is in `[0, L]` with

  `|ρ u(t) + 2 L n - s̄(t)| ≤ K · 216 ε` and `u̇(t) = ρ ξ`

for some `ρ = ±1`, `n ∈ ℤ` (`billiard_good`).  This is the estimate
`|s_ε(t) - s(t)| ≤ |u_ε - u₀| + t |ξ - v₀| + 14 ε (1 + 2t/L)` of the proof of Proposition IX.11,
with `u = f(s_ε)` outside the excursions.
-/

namespace HamiltonianMetricGraphs

open Set

variable {ε L c Tmax : ℝ} {u pu : ℝ → ℝ}

/-- **The billiard alternative at time `t`**: either the free lifted coordinate
`s̄(t) = x₀ + σ c t` is within `D₂` of `L ℤ`, or the particle is in `[0, L]` and its lifted
position `ρ u(t) + 2 L n` is within `D₁` of `s̄(t)`, with momentum `ρ σ c`. -/
def BilliardGood (L c : ℝ) (σ : ℤ) (x₀ : ℝ) (u pu : ℝ → ℝ) (D₁ D₂ t : ℝ) : Prop :=
  (∃ M : ℤ, |x₀ + σ * c * t - M * L| ≤ D₂) ∨
    ∃ n ρ : ℤ, (ρ = 1 ∨ ρ = -1) ∧ u t ∈ Icc 0 L ∧
      |ρ * u t + 2 * L * n - (x₀ + σ * c * t)| ≤ D₁ ∧ pu t = ρ * σ * c

theorem int_sign_sq {ρ : ℤ} (hρ : ρ = 1 ∨ ρ = -1) : (ρ : ℝ) * ρ = 1 := by
  rcases hρ with rfl | rfl <;> norm_num

/-- **The leg invariant** after `k` excursions: either the alternative holds on all of `[0, T]`,
or at some time `a ≤ T` the particle leaves an excursion (or starts, `k = 0`) inside
`[8ε, L - 8ε]` with momentum `ρ σ c`, at lifted drift at most `k · 216 ε`, and the alternative
holds on `[0, a]`. -/
def LegInv (L c ε T : ℝ) (σ : ℤ) (u pu : ℝ → ℝ) (D₁ D₂ : ℝ) (k : ℕ) : Prop :=
  (∀ t ∈ Icc 0 T, BilliardGood L c σ (u 0) u pu D₁ D₂ t) ∨
    ∃ a : ℝ, ∃ n ρ : ℤ, a ∈ Icc 0 T ∧ (ρ = 1 ∨ ρ = -1) ∧ ((k : ℝ) - 1) * (L / 4) ≤ a ∧
      (k = 0 ∨ u a = L / 2 - ρ * σ * (L / 2 - 8 * ε)) ∧ u a ∈ Icc (8 * ε) (L - 8 * ε) ∧
      pu a = ρ * σ * c ∧ |ρ * u a + 2 * L * n - (u 0 + σ * c * a)| ≤ k * (216 * ε) ∧
      ∀ t ∈ Icc 0 a, BilliardGood L c σ (u 0) u pu D₁ D₂ t

/-- **One leg of the billiard**: free flight to the next cap, and the reflection there. -/
theorem legInv_succ (S : CorridorSolution ε L c Tmax u pu) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {T D₁ D₂ : ℝ} (hT : T + 100 * ε ≤ Tmax) {k : ℕ} (hD₁ : k * (216 * ε) ≤ D₁)
    (hD₂ : (k + 1) * (216 * ε) ≤ D₂) (hk : LegInv L c ε T σ u pu D₁ D₂ k) :
    LegInv L c ε T σ u pu D₁ D₂ (k + 1) := by
  rcases hk with hall | ⟨a, n, ρ, ha, hρ, hka, hentry, hya, hpa, hdrift, hgood⟩
  · exact Or.inl hall
  have hε := S.eps_pos
  have hc1 := S.c_ge
  have hc2 := S.c_le
  have hc0 : 0 < c := S.c_pos
  have hlen := S.len
  set d : ℤ := ρ * σ with hd
  have hd1 : d = 1 ∨ d = -1 := by
    rw [hd]; rcases hρ with rfl | rfl <;> rcases hσ with rfl | rfl <;> norm_num
  have hdd : (d : ℝ) * d = 1 := int_sign_sq hd1
  have hρρ : (ρ : ℝ) * ρ = 1 := int_sign_sq hρ
  have hρd : (ρ : ℝ) * d = σ := by
    rw [hd]; push_cast; rw [← mul_assoc, hρρ, one_mul]
  have hpa' : pu a = d * c := by rw [hpa, hd]; push_cast; ring
  set y := u a
  set y' : ℝ := L / 2 + d * (L / 2 - 8 * ε) with hy'
  have hdist : 0 ≤ d * (y' - y) := by
    rcases hd1 with h | h <;> rw [h] <;> simp only [hy', h] <;> push_cast <;>
      linarith [hya.1, hya.2]
  set b : ℝ := a + d * (y' - y) / c with hb
  have hab : a ≤ b := by rw [hb]; have := div_nonneg hdist hc0.le; linarith
  have hfree_val : ∀ t, a ≤ t → t ≤ b → y + d * c * (t - a) ∈ Icc (8 * ε) (L - 8 * ε) := by
    intro t h1 h2
    have h3 : c * (t - a) ≤ d * (y' - y) := by
      have : t - a ≤ d * (y' - y) / c := by linarith
      rwa [le_div_iff₀ hc0, mul_comm] at this
    have h4 : 0 ≤ c * (t - a) := mul_nonneg hc0.le (by linarith)
    rcases hd1 with h | h <;> rw [h] at h3 ⊢ <;> simp only [hy', h] at h3 <;> push_cast at h3 ⊢ <;>
      constructor <;> nlinarith [hya.1, hya.2]
  -- the free leg up to `min b T`
  have hfree : ∀ t ∈ Icc a (min b T), u t = y + d * c * (t - a) ∧ pu t = d * c := by
    have hmT : min b T ≤ T := min_le_right _ _
    have hmb : min b T ≤ b := min_le_left _ _
    have hamin : a ≤ min b T := le_min hab ha.2
    have h := S.free_of_endpoints (a := a) (b := min b T) ⟨ha.1, by linarith [ha.2]⟩
      ⟨by linarith [ha.1], by linarith⟩ hamin
      ⟨by linarith [hya.1], by linarith [hya.2]⟩
      (by
        have := hfree_val (min b T) hamin hmb
        rw [hpa']
        exact ⟨by linarith [this.1], by linarith [this.2]⟩)
    intro t ht
    obtain ⟨h1, h2⟩ := h t ht
    rw [hpa'] at h1 h2
    exact ⟨by linarith [h1], h2⟩
  -- the alternative holds along the free leg
  have hgood_free : ∀ t ∈ Icc a (min b T), BilliardGood L c σ (u 0) u pu D₁ D₂ t := by
    intro t ht
    obtain ⟨h1, h2⟩ := hfree t ht
    have hv := hfree_val t ht.1 (le_trans ht.2 (min_le_left _ _))
    refine Or.inr ⟨n, ρ, hρ, ⟨by rw [h1]; linarith [hv.1], by rw [h1]; linarith [hv.2]⟩, ?_, ?_⟩
    · rw [h1]
      have : (ρ : ℝ) * (y + d * c * (t - a)) + 2 * L * n - (u 0 + σ * c * t) =
          ρ * y + 2 * L * n - (u 0 + σ * c * a) := by
        rw [show (ρ : ℝ) * (y + d * c * (t - a)) = ρ * y + (ρ * d) * c * (t - a) by ring, hρd]
        ring
      rw [this]
      exact le_trans hdrift hD₁
    · rw [h2, hd]; push_cast; try ring
  have hgood_upto : ∀ t ∈ Icc 0 (min b T), BilliardGood L c σ (u 0) u pu D₁ D₂ t := by
    intro t ht
    rcases le_or_gt t a with h | h
    · exact hgood t ⟨ht.1, h⟩
    · exact hgood_free t ⟨h.le, ht.2⟩
  by_cases hbT : T < b
  · left
    intro t ht
    exact hgood_upto t ⟨ht.1, le_min (by linarith [ht.2]) ht.2⟩
  push Not at hbT
  have hminb : min b T = b := min_eq_left hbT
  rw [hminb] at hfree hgood_upto
  obtain ⟨hub, hpub⟩ := hfree b ⟨hab, le_rfl⟩
  have hba : b - a = d * (y' - y) / c := by rw [hb]; ring
  have hdcb : (d : ℝ) * c * (b - a) = y' - y := by
    rw [hba, show (d : ℝ) * c * (d * (y' - y) / c) = (d * d) * (y' - y) * (c / c) by ring,
      div_self hc0.ne', hdd]
    ring
  have hub' : u b = L / 2 + d * (L / 2 - 8 * ε) := by
    rw [hub, hdcb]; ring
  have hτ := capReflTime_le hε hc1 hc2
  obtain ⟨a', ha', hua', hpua'⟩ := S.reflect (s := d) (a := b)
    (by rcases hd1 with h | h <;> rw [h] <;> norm_num) (by linarith [ha.1])
    (by linarith) (by rw [hub']) hpub
  -- the excursion: the free coordinate is near the wall `M L`
  set M : ℤ := (if d = 1 then ρ else 0) + 2 * n with hM
  have hwall : (ρ : ℝ) * (L / 2 + d * (L / 2)) + 2 * L * n = M * L := by
    rw [hM]
    rcases hd1 with h | h <;> rw [h] <;> simp <;> ring
  have hbdrift : |ρ * u b + 2 * L * n - (u 0 + σ * c * b)| ≤ k * (216 * ε) := by
    have : (ρ : ℝ) * u b + 2 * L * n - (u 0 + σ * c * b) =
        ρ * y + 2 * L * n - (u 0 + σ * c * a) := by
      rw [hub, show (ρ : ℝ) * (y + d * c * (b - a)) = ρ * y + (ρ * d) * c * (b - a) by ring, hρd]
      ring
    rw [this]; exact hdrift
  have hnearwall : (ρ : ℝ) * u b + 2 * L * n - M * L = -(ρ * d * (8 * ε)) := by
    rw [← hwall, hub']; ring
  have hρa : |(ρ : ℝ)| = 1 := by rcases hρ with h | h <;> rw [h] <;> norm_num
  have hda : |(d : ℝ)| = 1 := by rcases hd1 with h | h <;> rw [h] <;> norm_num
  have hρdε : |(ρ : ℝ) * d * (8 * ε)| = 8 * ε := by
    rw [abs_mul, abs_mul, hρa, hda, one_mul, one_mul, abs_of_pos (by linarith)]
  have hgood_exc : ∀ t ∈ Icc b a', BilliardGood L c σ (u 0) u pu D₁ D₂ t := by
    intro t ht
    left
    refine ⟨M, ?_⟩
    have hct : |(σ : ℝ) * c * (t - b)| ≤ 200 * ε := by
      rw [abs_mul, abs_mul]
      have hs : |(σ : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> norm_num
      rw [hs, one_mul, abs_of_pos hc0, abs_of_nonneg (by linarith [ht.1])]
      have h1 : t - b ≤ 100 * ε := by linarith [ht.2, ha'.2]
      have h2 : c * (t - b) ≤ 2 * (t - b) :=
        mul_le_mul_of_nonneg_right hc2 (by linarith [ht.1])
      linarith
    have e : u 0 + σ * c * t - M * L = -((ρ * u b + 2 * L * n - (u 0 + σ * c * b))) +
        ((ρ : ℝ) * u b + 2 * L * n - M * L) + σ * c * (t - b) := by ring
    rw [e, hnearwall]
    calc |-((ρ : ℝ) * u b + 2 * L * n - (u 0 + σ * c * b)) + -(ρ * d * (8 * ε)) +
          σ * c * (t - b)|
        ≤ |-((ρ : ℝ) * u b + 2 * L * n - (u 0 + σ * c * b))| + |-(ρ * d * (8 * ε))| +
          |σ * c * (t - b)| := abs_add_three _ _ _
      _ ≤ k * (216 * ε) + 8 * ε + 200 * ε := by
          rw [abs_neg, abs_neg, hρdε]; linarith
      _ ≤ D₂ := by linarith
  have hgood_a' : ∀ t ∈ Icc 0 a', BilliardGood L c σ (u 0) u pu D₁ D₂ t := by
    intro t ht
    rcases le_or_gt t b with h | h
    · exact hgood_upto t ⟨ht.1, h⟩
    · exact hgood_exc t ⟨h.le, ht.2⟩
  by_cases ha'T : T < a'
  · left
    intro t ht
    exact hgood_a' t ⟨ht.1, by linarith [ht.2]⟩
  push Not at ha'T
  right
  refine ⟨a', M - n, -ρ, ⟨by linarith [ha.1, ha'.1], ha'T⟩,
    by rcases hρ with rfl | rfl <;> simp, ?_, Or.inr ?_, ?_, ?_, ?_, hgood_a'⟩
  · -- the lower bound on the time
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; push_cast; linarith [ha.1, ha'.1, hab]
    · rcases hentry with h | h
      · omega
      · have hy : y = L / 2 - d * (L / 2 - 8 * ε) := by
          rw [h, hd]; push_cast; ring
        have hlegd : d * (y' - y) = L - 16 * ε := by
          rw [hy, hy']
          linear_combination (L - 16 * ε) * hdd
        have hleg : L / 4 ≤ d * (y' - y) / c := by
          rw [hlegd, le_div_iff₀ hc0]
          have : L / 4 * c ≤ L / 4 * 2 :=
            mul_le_mul_of_nonneg_left hc2 (by linarith)
          linarith
        have e : (((k + 1 : ℕ) : ℝ) - 1) * (L / 4) = ((k : ℝ) - 1) * (L / 4) + L / 4 := by
          push_cast; ring
        rw [e]
        linarith [ha'.1, hka]
  · rw [hua', hd]; push_cast; ring
  · rw [hua']
    rcases hd1 with h | h <;> rw [h] <;> push_cast <;> constructor <;> linarith
  · rw [hpua', hd]; push_cast; ring
  · -- the drift after the reflection
    have e : ((-ρ : ℤ) : ℝ) * u a' + 2 * L * ((M - n : ℤ) : ℝ) - (u 0 + σ * c * a') =
        (ρ * u b + 2 * L * n - (u 0 + σ * c * b)) - 2 * (ρ * u b + 2 * L * n - M * L) -
          σ * c * (a' - b) := by
      rw [hua', ← hub']; push_cast; ring
    rw [e, hnearwall]
    have hct : |(σ : ℝ) * c * (a' - b)| ≤ 200 * ε := by
      rw [abs_mul, abs_mul]
      have hs : |(σ : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> norm_num
      rw [hs, one_mul, abs_of_pos hc0, abs_of_nonneg (by linarith [ha'.1])]
      have h1 : a' - b ≤ 100 * ε := by linarith [ha'.2]
      have h2 : c * (a' - b) ≤ 2 * (a' - b) :=
        mul_le_mul_of_nonneg_right hc2 (by linarith [ha'.1])
      linarith
    have h2 : |2 * -((ρ : ℝ) * d * (8 * ε))| = 16 * ε := by
      rw [abs_mul, abs_neg, hρdε, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
    have t1 := norm_sub_le ((ρ : ℝ) * u b + 2 * L * n - (u 0 + σ * c * b))
      (2 * -((ρ : ℝ) * d * (8 * ε)))
    have t2 := norm_sub_le ((ρ : ℝ) * u b + 2 * L * n - (u 0 + σ * c * b) -
      2 * -((ρ : ℝ) * d * (8 * ε))) (σ * c * (a' - b))
    simp only [Real.norm_eq_abs] at t1 t2
    have : ((k + 1 : ℕ) : ℝ) * (216 * ε) = k * (216 * ε) + 16 * ε + 200 * ε := by
      push_cast; ring
    rw [this]
    linarith

/-- **The billiard approximation.**  Let `(u, u̇)` solve the corridor system of length `L` at scale
`ε` and energy `c²/2`, starting in `[8ε, L - 8ε]` with velocity `σ c`, `σ = ±1`.  If the window
`[0, T]` is shorter than `(K - 1) L / 4` (so it contains at most `K` excursions), then at every
`t ∈ [0, T]` the billiard alternative `BilliardGood` holds with `D₁ = K · 216 ε` and
`D₂ = (K + 1) · 216 ε`. -/
theorem billiard_good (S : CorridorSolution ε L c Tmax u pu) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hp0 : pu 0 = σ * c) (hx0 : u 0 ∈ Icc (8 * ε) (L - 8 * ε)) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : T + 100 * ε ≤ Tmax) {K : ℕ} (hK : T < ((K : ℝ) - 1) * (L / 4)) :
    ∀ t ∈ Icc 0 T, BilliardGood L c σ (u 0) u pu (K * (216 * ε)) ((K + 1) * (216 * ε)) t := by
  have hε := S.eps_pos
  have hinv : ∀ k : ℕ, k ≤ K → LegInv L c ε T σ u pu (K * (216 * ε)) ((K + 1) * (216 * ε)) k := by
    intro k hk
    induction k with
    | zero =>
        refine Or.inr ⟨0, 0, 1, ⟨le_rfl, hT0⟩, Or.inl rfl, ?_, Or.inl rfl, hx0, ?_, ?_, ?_⟩
        · have := S.len_pos; push_cast; nlinarith
        · rw [hp0]; push_cast; ring
        · push_cast; simp
        · intro t ht
          have ht0 : t = 0 := le_antisymm ht.2 ht.1
          subst ht0
          refine Or.inr ⟨0, 1, Or.inl rfl, ⟨by linarith [hx0.1], by linarith [hx0.2]⟩, ?_, ?_⟩
          · push_cast; simp only [mul_zero, add_zero, one_mul, sub_self, abs_zero]; positivity
          · rw [hp0]; push_cast; ring
    | succ j ih =>
        have hjK : (j : ℝ) ≤ K := by exact_mod_cast (Nat.le_of_succ_le hk)
        exact legInv_succ S hσ hT (by nlinarith) (by nlinarith) (ih (Nat.le_of_succ_le hk))
  rcases hinv K le_rfl with hall | ⟨a, -, -, ha, -, hka, -⟩
  · exact hall
  · exfalso; linarith [ha.2]

end HamiltonianMetricGraphs
