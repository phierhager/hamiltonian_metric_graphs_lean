/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.StarReflection
import HamiltonianMetricGraphs.Realization.GatePotential

/-!
# Lemmas IX.7 and IX.8 as printed

* `barrier_profile` — **Lemma IX.7** (`lem:barrier-profile`), together with the printed
  properties of the transverse well `A_ε`: the claims scattered over `BarrierProfile.lean`,
  `MicroscopicPotential.lean` and `GatePotential.lean`, collected in one statement.
* `barrier_reflection` — **Lemma IX.8** (`lem:barrier-reflection`) as printed: the longitudinal
  potential `P` is only assumed to agree with `Ψ(y/ε)` on `[-d, ε]`.  It is derived from the global
  version `Reflection.reflect_of_barrier_sharp`: by conservation of energy the trajectory never
  reaches `ε` (`P(ε) = Ψ(1) > E`), and up to the first time it falls below `-d` it solves the
  equation of the global barrier `Φ(y) = Ψ(y/ε)`; after that time it is replaced by the free
  continuation `-d - c(t - σ)`, which solves the global equation too.  The global theorem, applied
  to the glued curve, returns before it can leave `[-d, ε)`.
-/

namespace HamiltonianMetricGraphs

open Set Real

/-! ### Lemma IX.7 -/

/-- **Lemma IX.7 (barrier profile)**, and the printed properties of the transverse well.
`B = barrierProfile` is `B(s) = 4e^{1-1/s}` for `s > 0` and `0` for `s ≤ 0`; it is smooth,
nondecreasing, `B(1) = 4`, `B ≤ 4e⁻³ < 1/4` on `(-∞, 1/4]`, `B' ≥ 4e⁻³` on `[1/4, 1]` and
`B ≤ 4e^{2/3}` on `(-∞, 3]`.  `A_ε = wellPot ε` is `4 χ_{1,4}(s²/ε²)` (`χ = smoothTransition`,
`χ_{a,b} = plateau a b`); it is smooth, `0 ≤ A_ε ≤ 4`, `A_ε = 0` on `[-ε, ε]` and `A_ε = 4`
outside `(-2ε, 2ε)`. -/
theorem barrier_profile :
    (∀ s, 0 < s → barrierProfile s = 4 * exp (1 - 1 / s)) ∧
    (∀ s ≤ 0, barrierProfile s = 0) ∧
    ContDiff ℝ (⊤ : ℕ∞) barrierProfile ∧ Monotone barrierProfile ∧
    barrierProfile 1 = 4 ∧
    (∀ s ≤ 1 / 4, barrierProfile s ≤ 4 * exp (-3)) ∧ 4 * exp (-3) < 1 / 4 ∧
    (∀ s ∈ Icc (1 / 4 : ℝ) 1, 4 * exp (-3) ≤ deriv barrierProfile s) ∧
    (∀ s ≤ 3, barrierProfile s ≤ 4 * exp (2 / 3)) ∧
    ∀ ε, 0 < ε →
      (∀ s, wellPot ε s = 4 * plateau 1 4 (s ^ 2 / ε ^ 2)) ∧
      ContDiff ℝ (⊤ : ℕ∞) (wellPot ε) ∧
      (∀ s, 0 ≤ wellPot ε s ∧ wellPot ε s ≤ 4) ∧
      (∀ s, |s| ≤ ε → wellPot ε s = 0) ∧
      (∀ s, 2 * ε ≤ |s| → wellPot ε s = 4) := by
  have he3 : 4 * exp (-3) = 4 / exp 3 := by rw [Real.exp_neg]; ring
  have h16 : (16 : ℝ) < exp 3 := by
    have h : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
    have h3 : exp 3 = exp 1 * (exp 1 * exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [h3]
    have : (2.7 : ℝ) * 2.7 < exp 1 * exp 1 := by nlinarith
    nlinarith
  refine ⟨fun s hs => ?_, fun s hs => barrierProfile_of_nonpos hs, contDiff_barrierProfile,
    barrierProfile_monotone, barrierProfile_one, fun s hs => ?_, ?_, fun s hs => ?_,
    fun s hs => barrierProfile_le_of_le_three hs, fun ε hε => ⟨fun s => ?_, ?_,
    fun s => ⟨wellPot_nonneg ε s, wellPot_le ε s⟩, fun s hs => wellPot_of_abs_le hε hs,
    fun s hs => wellPot_of_two_le_abs hε hs⟩⟩
  · rw [barrierProfile, glue_of_pos hs, mul_assoc, ← Real.exp_add, one_div]
    ring_nf
  · have hg := glue_le_of_le_quarter hs
    have hpos : (0 : ℝ) ≤ 4 * exp 1 := by positivity
    calc barrierProfile s = 4 * exp 1 * glue s := rfl
      _ ≤ 4 * exp 1 * exp (-4) := mul_le_mul_of_nonneg_left hg hpos
      _ = 4 * exp (-3) := by rw [four_div_exp_three, he3]
  · rw [he3, div_lt_iff₀ (exp_pos 3)]; linarith
  · rw [he3]; exact deriv_barrierProfile_ge hs.1 hs.2
  · rw [wellPot, wellProfile, div_pow]
  · exact contDiff_wellPot ε

/-! ### Lemma IX.8 -/

/-- Gluing two one-sided derivatives at an interior point `σ`. -/
theorem hasDerivWithinAt_glue {f g f' g' : ℝ → ℝ} {a σ b t : ℝ} (hσ : σ ∈ Icc a b)
    (ht : t ∈ Icc a b)
    (hf : ∀ u ∈ Icc a σ, HasDerivWithinAt f (f' u) (Icc a σ) u)
    (hg : ∀ u ∈ Icc σ b, HasDerivWithinAt g (g' u) (Icc σ b) u)
    (hfg : f σ = g σ) (hfg' : f' σ = g' σ) :
    HasDerivWithinAt (fun u => if u ≤ σ then f u else g u) (if t ≤ σ then f' t else g' t)
      (Icc a b) t := by
  rw [← Icc_union_Icc_eq_Icc hσ.1 hσ.2]
  refine HasDerivWithinAt.union ?_ ?_
  · by_cases h : t ≤ σ
    · rw [if_pos h]
      exact (hf t ⟨ht.1, h⟩).congr (fun u hu => if_pos hu.2) (if_pos h)
    · rw [not_le] at h
      refine HasFDerivWithinAt.of_notMem_closure ?_
      intro hcl
      rw [closure_Icc] at hcl
      linarith [hcl.2]
  · by_cases h : σ ≤ t
    · have hval : (if t ≤ σ then f' t else g' t) = g' t := by
        by_cases h' : t ≤ σ
        · rw [if_pos h', le_antisymm h' h, hfg']
        · rw [if_neg h']
      rw [hval]
      refine (hg t ⟨h, ht.2⟩).congr (fun u hu => ?_) ?_
      · by_cases h' : u ≤ σ
        · rw [if_pos h', le_antisymm h' hu.1, hfg]
        · rw [if_neg h']
      · by_cases h' : t ≤ σ
        · rw [if_pos h', le_antisymm h' h, hfg]
        · rw [if_neg h']
    · rw [not_le] at h
      refine HasFDerivWithinAt.of_notMem_closure ?_
      intro hcl
      rw [closure_Icc] at hcl
      linarith [hcl.1]

/-- A function that vanishes on `(-∞, 0]` has vanishing derivative there, at `0` included. -/
theorem deriv_eq_zero_of_flat {Ψ : ℝ → ℝ} (hd : Differentiable ℝ Ψ) (hflat : ∀ s ≤ 0, Ψ s = 0)
    {s : ℝ} (hs : s ≤ 0) : deriv Ψ s = 0 := by
  have h1 : HasDerivWithinAt Ψ (deriv Ψ s) (Iic s) s := (hd s).hasDerivAt.hasDerivWithinAt
  have h2 : HasDerivWithinAt Ψ 0 (Iic s) s :=
    (hasDerivWithinAt_const s (Iic s) (0 : ℝ)).congr
      (fun u hu => hflat u (le_trans hu hs)) (hflat s hs)
  exact (uniqueDiffWithinAt_Iic s).eq_deriv _ h1 h2

set_option maxHeartbeats 1000000 in
-- the gluing and the transfer of the eight hypotheses of the global version
/-- **Lemma IX.8 (reflection at a barrier), as printed.**  Let `Ψ ∈ C²(ℝ)` be nondecreasing with
`Ψ = 0` on `(-∞, 0]`, and let `E, k > 0` with `Ψ ≤ E/2` on `(-∞, 1/4]`, `Ψ' ≥ k` on `[1/4, 1]` and
`Ψ(1) > E`.  Let `ε > 0`, `d ≥ 0`, and `P ∈ C²(ℝ)` with `P(y) = Ψ(y/ε)` for `-d ≤ y ≤ ε`.  Let
`(y, v)` solve `y' = v`, `v' = -P'(y)` on `[0, T]` with `y(0) = -d` and `v(0) = c = √(2E)`, where
`T` is at least the bound below.  Then there is a time
`0 < t_* ≤ 2d/c + 2ε(1/(4√E) + √(3/(2k)))` with `y(t_*) = -d`, `v(t_*) = -c`, and
`-d < y(t) < ε` for `0 < t < t_*`. -/
theorem barrier_reflection {Ψ P y v : ℝ → ℝ} {E k ε d T : ℝ}
    (hΨ : ContDiff ℝ 2 Ψ) (hmono : Monotone Ψ) (hflat : ∀ s ≤ 0, Ψ s = 0)
    (hE : 0 < E) (hk : 0 < k) (hlow : ∀ s ≤ 1 / 4, Ψ s ≤ E / 2)
    (hslope : ∀ s ∈ Icc (1 / 4 : ℝ) 1, k ≤ deriv Ψ s) (hhigh : E < Ψ 1)
    (hε : 0 < ε) (hd : 0 ≤ d) (hP : ContDiff ℝ 2 P) (hPΨ : ∀ s ∈ Icc (-d) ε, P s = Ψ (s / ε))
    (hy : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (v t) (Icc 0 T) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivWithinAt v (-deriv P (y t)) (Icc 0 T) t)
    (hy0 : y 0 = -d) (hv0 : v 0 = Real.sqrt (2 * E))
    (hT : 2 * d / Real.sqrt (2 * E) + 2 * ε * (1 / (4 * Real.sqrt E) + Real.sqrt (3 / (2 * k)))
      ≤ T) :
    ∃ tstar, 0 < tstar ∧
      tstar ≤ 2 * d / Real.sqrt (2 * E) + 2 * ε * (1 / (4 * Real.sqrt E) + Real.sqrt (3 / (2 * k)))
      ∧ y tstar = -d ∧ v tstar = -Real.sqrt (2 * E) ∧ ∀ t ∈ Ioo 0 tstar, -d < y t ∧ y t < ε := by
  set c := Real.sqrt (2 * E) with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hcsq : c ^ 2 = 2 * E := Real.sq_sqrt (by linarith)
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hPd : Differentiable ℝ P := hP.differentiable (by norm_num)
  have hP1 : ContDiff ℝ 1 P := hP.of_le (by norm_num)
  -- the global barrier `Φ(y) = Ψ(y/ε)`
  set Φ : ℝ → ℝ := fun s => Ψ (s / ε) with hΦ
  have hΦ1 : ContDiff ℝ 1 Φ := (hΨ.of_le (by norm_num)).comp (contDiff_id.div_const ε)
  have hderivΦ : ∀ s, deriv Φ s = deriv Ψ (s / ε) / ε := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => s / ε) (1 / ε) s := by
      simpa using (hasDerivAt_id s).div_const ε
    have h2 := ((hΨd (s / ε)).hasDerivAt).comp s h1
    have h3 : deriv Φ s = deriv Ψ (s / ε) * (1 / ε) := h2.deriv
    rw [h3]; ring
  have hΦflat : ∀ s ≤ 0, deriv Φ s = 0 := by
    intro s hs
    rw [hderivΦ, deriv_eq_zero_of_flat hΨd hflat (div_nonpos_of_nonpos_of_nonneg hs hε.le),
      zero_div]
  -- `P` and `Φ` have the same derivative on `[-d, ε]`
  have hPΦ' : ∀ s ∈ Icc (-d) ε, deriv P s = deriv Φ s := by
    intro s hs
    have h1 : HasDerivWithinAt Φ (deriv P s) (Icc (-d) ε) s :=
      ((hPd s).hasDerivAt.hasDerivWithinAt).congr (fun u hu => (hPΨ u hu).symm)
        (hPΨ s hs).symm
    have h2 : HasDerivWithinAt Φ (deriv Φ s) (Icc (-d) ε) s :=
      ((hΦ1.differentiable (by norm_num)) s).hasDerivAt.hasDerivWithinAt
    exact (uniqueDiffOn_Icc (by linarith) s hs).eq_deriv _ h1 h2
  -- conservation of energy for the true potential `P`
  have hP0 : P (-d) = 0 := by
    rw [hPΨ (-d) ⟨le_rfl, by linarith⟩, hflat _ (div_nonpos_of_nonpos_of_nonneg (by linarith)
      hε.le)]
  have hen : ∀ t ∈ Icc 0 T, v t ^ 2 = 2 * (E - P (y t)) := by
    intro t ht
    have h := sq_momentum_eq hP1 hy hv t ht
    simp only [energy1D] at h
    rw [hy0, hv0, hP0] at h
    rw [h, hcsq]; ring
  have hcont : ContinuousOn y (Icc 0 T) := fun t ht => (hy t ht).continuousWithinAt
  have hcontv : ContinuousOn v (Icc 0 T) := fun t ht => (hv t ht).continuousWithinAt
  have hbound0 : 0 < 2 * d / c + 2 * ε * (1 / (4 * Real.sqrt E) + Real.sqrt (3 / (2 * k))) := by
    have : 0 < Real.sqrt E := Real.sqrt_pos.mpr hE
    have : 0 ≤ Real.sqrt (3 / (2 * k)) := Real.sqrt_nonneg _
    positivity
  have hT0 : 0 ≤ T := by linarith
  -- **the particle never reaches `ε`**: there `P = Ψ(1) > E`
  have hyε : ∀ t ∈ Icc 0 T, y t < ε := by
    intro t ht
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨s, hs, hval⟩ := intermediate_value_Icc ht.1 (hcont.mono (Icc_subset_Icc le_rfl ht.2))
      (show ε ∈ Icc (y 0) (y t) from ⟨by rw [hy0]; linarith, hcon⟩)
    have h1 := hen s ⟨hs.1, hs.2.trans ht.2⟩
    rw [hval, hPΨ ε ⟨by linarith, le_rfl⟩, div_self (ne_of_gt hε)] at h1
    nlinarith [sq_nonneg (v s)]
  -- **the first time the particle falls below `-d`**
  set A : Set ℝ := {s | s ∈ Icc 0 T ∧ ∀ u ∈ Icc 0 s, -d ≤ y u} with hA
  have hA0 : (0 : ℝ) ∈ A := ⟨⟨le_rfl, hT0⟩, fun u hu => by
    rw [show u = 0 from le_antisymm hu.2 hu.1, hy0]⟩
  have hAbdd : BddAbove A := ⟨T, fun s hs => hs.1.2⟩
  set σ := sSup A with hσdef
  have hσ0 : 0 ≤ σ := le_csSup hAbdd hA0
  have hσT : σ ≤ T := csSup_le ⟨0, hA0⟩ (fun s hs => hs.1.2)
  have hσmem : σ ∈ Icc 0 T := ⟨hσ0, hσT⟩
  have hbefore : ∀ u ∈ Icc 0 σ, u < σ → -d ≤ y u := by
    intro u hu hlt
    obtain ⟨s, hs, hus⟩ := exists_lt_of_lt_csSup ⟨0, hA0⟩ hlt
    exact hs.2 u ⟨hu.1, hus.le⟩
  have hge : ∀ u ∈ Icc 0 σ, -d ≤ y u := by
    intro u hu
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · exact hbefore u hu hlt
    · subst heq
      by_contra hcon
      rw [not_le] at hcon
      rcases eq_or_lt_of_le hσ0 with h0 | hpos
      · rw [← h0, hy0] at hcon; linarith
      · -- continuity at `σ` from the left
        have hcw := (hcont σ hσmem)
        rw [Metric.continuousWithinAt_iff] at hcw
        obtain ⟨η, hη, hη'⟩ := hcw (-d - y σ) (by linarith)
        set u := max 0 (σ - η / 2) with hu
        have hu0 : 0 ≤ u := le_max_left _ _
        have huσ : u < σ := max_lt hpos (by linarith)
        have hdist : dist u σ < η := by
          rw [Real.dist_eq, abs_lt]
          constructor
          · have : σ - η / 2 ≤ u := le_max_right _ _
            linarith
          · linarith
        have h1 := hη' ⟨hu0, huσ.le.trans hσT⟩ hdist
        rw [Real.dist_eq, abs_lt] at h1
        have h2 := hbefore u ⟨hu0, huσ.le⟩ huσ
        linarith [h1.2]
  -- on `[0, σ]` the particle solves the equation of the global barrier
  have hyΦ : ∀ t ∈ Icc 0 σ, deriv P (y t) = deriv Φ (y t) := fun t ht =>
    hPΦ' (y t) ⟨hge t ht, (hyε t ⟨ht.1, ht.2.trans hσT⟩).le⟩
  -- **the glued curve**: the true motion up to `σ`, the free continuation after it
  obtain ⟨x, p, hx, hp, hx0, hp0, hxy⟩ : ∃ x p : ℝ → ℝ,
      (∀ t ∈ Icc 0 T, HasDerivWithinAt x (p t) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt p (-deriv Φ (x t)) (Icc 0 T) t) ∧
      x 0 = -d ∧ p 0 = c ∧
      ∀ t ∈ Icc 0 T, -d ≤ x t → x t = y t ∧ p t = v t := by
    rcases eq_or_lt_of_le hσT with hσT' | hσT'
    · -- the particle never falls below `-d` on `[0, T]`
      refine ⟨y, v, hy, fun t ht => ?_, hy0, hv0, fun t _ _ => ⟨rfl, rfl⟩⟩
      rw [← hyΦ t ⟨ht.1, hσT'.symm ▸ ht.2⟩]
      exact hv t ht
    · -- at `σ < T` the particle is at `-d`, moving backward at speed `c`
      have hnot : ∀ η > 0, σ + η ≤ T → ∃ u ∈ Icc σ (σ + η), y u < -d := by
        intro η hη hηT
        by_contra hcon
        push Not at hcon
        have hmem : σ + η ∈ A := ⟨⟨by linarith, hηT⟩, fun u hu => by
          rcases le_or_gt u σ with h | h
          · exact hge u ⟨hu.1, h⟩
          · exact hcon u ⟨h.le, hu.2⟩⟩
        have := le_csSup hAbdd hmem
        linarith
      have hyσ : y σ = -d := by
        refine le_antisymm ?_ (hge σ ⟨hσ0, le_rfl⟩)
        by_contra hcon
        rw [not_le] at hcon
        have hcw := hcont σ hσmem
        rw [Metric.continuousWithinAt_iff] at hcw
        obtain ⟨η, hη, hη'⟩ := hcw (y σ + d) (by linarith)
        set η₁ := min (η / 2) (T - σ) with hη₁
        have hη₁pos : 0 < η₁ := lt_min (by linarith) (by linarith)
        obtain ⟨u, hu, hyu⟩ := hnot η₁ hη₁pos (by linarith [min_le_right (η / 2) (T - σ)])
        have hd : dist u σ < η := by
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hu.1, hu.2, min_le_left (η / 2) (T - σ)]
        have h1 := hη' ⟨by linarith [hu.1], by linarith [hu.2, min_le_right (η / 2) (T - σ)]⟩ hd
        rw [Real.dist_eq, abs_lt] at h1
        linarith [h1.1]
      have hvσ : v σ = -c := by
        have h1 := hen σ hσmem
        rw [hyσ, hP0, sub_zero, ← hcsq] at h1
        have hle : v σ ≤ 0 := by
          by_contra hcon
          rw [not_le] at hcon
          have hcw := hcontv σ hσmem
          rw [Metric.continuousWithinAt_iff] at hcw
          obtain ⟨η, hη, hη'⟩ := hcw (v σ) hcon
          set η₁ := min (η / 2) (T - σ) with hη₁
          have hη₁pos : 0 < η₁ := lt_min (by linarith) (by linarith)
          have hη₁T : σ + η₁ ≤ T := by linarith [min_le_right (η / 2) (T - σ)]
          obtain ⟨u, hu, hyu⟩ := hnot η₁ hη₁pos hη₁T
          have hvpos : ∀ w ∈ Icc σ u, 0 ≤ v w := by
            intro w hw
            have hd : dist w σ < η := by
              rw [Real.dist_eq, abs_lt]
              constructor <;> linarith [hw.1, hw.2, hu.2, min_le_left (η / 2) (T - σ)]
            have h2 := hη' ⟨by linarith [hw.1], by linarith [hw.2, hu.2]⟩ hd
            rw [Real.dist_eq, abs_lt] at h2
            linarith [h2.1]
          have hu' : u ∈ Icc 0 T := ⟨by linarith [hu.1], by linarith [hu.2]⟩
          have hmv := mul_sub_le_image_sub_of_le_hasDerivWithinAt hu.1
            (hasDerivWithinAt_sub_interval hy hσmem hu') hvpos
          linarith
        have h3 : (v σ + c) * (v σ - c) = 0 := by nlinarith
        rcases mul_eq_zero.mp h3 with h | h
        · linarith
        · linarith
      have hf : ∀ u ∈ Icc 0 σ, HasDerivWithinAt y (v u) (Icc 0 σ) u := fun u hu =>
        (hy u ⟨hu.1, hu.2.trans hσT⟩).mono (Icc_subset_Icc le_rfl hσT)
      have hg : ∀ u ∈ Icc σ T, HasDerivWithinAt (fun t => -d - c * (t - σ)) (-c) (Icc σ T) u :=
        fun u _ => ((((hasDerivAt_id u).sub_const σ).const_mul c).const_sub (-d)).congr_deriv
          (by ring) |>.hasDerivWithinAt
      have hf' : ∀ u ∈ Icc 0 σ, HasDerivWithinAt v (-deriv Φ (y u)) (Icc 0 σ) u := by
        intro u hu
        rw [← hyΦ u hu]
        exact (hv u ⟨hu.1, hu.2.trans hσT⟩).mono (Icc_subset_Icc le_rfl hσT)
      have hg' : ∀ u ∈ Icc σ T, HasDerivWithinAt (fun _ => -c) (0 : ℝ) (Icc σ T) u :=
        fun u _ => hasDerivWithinAt_const u _ _
      refine ⟨fun t => if t ≤ σ then y t else -d - c * (t - σ),
        fun t => if t ≤ σ then v t else -c, fun t ht => ?_, fun t ht => ?_, ?_, ?_, ?_⟩
      · exact hasDerivWithinAt_glue (g' := fun _ => -c) hσmem ht hf hg (by rw [hyσ]; ring) hvσ
      · refine (hasDerivWithinAt_glue (f' := fun u => -deriv Φ (y u)) (g' := fun _ => 0) hσmem ht
          hf' hg' hvσ (by rw [hyσ, hΦflat _ (by linarith), neg_zero])).congr_deriv ?_
        by_cases h : t ≤ σ
        · simp only [if_pos h]
        · simp only [if_neg h]
          rw [hΦflat _ (by nlinarith [lt_of_not_ge h]), neg_zero]
      · change (if (0 : ℝ) ≤ σ then y 0 else _) = -d
        rw [if_pos hσ0, hy0]
      · change (if (0 : ℝ) ≤ σ then v 0 else _) = c
        rw [if_pos hσ0, hv0]
      · intro t ht hxt
        by_cases h : t ≤ σ
        · simp only [if_pos h]
          exact ⟨trivial, trivial⟩
        · exfalso
          simp only [if_neg h] at hxt
          nlinarith [lt_of_not_ge h]
  -- the time bound of the global version is the printed one
  have hsharp : Reflection.sharpTime (ε / 4) ε (k / ε) E d
      = 2 * d / c + 2 * ε * (1 / (4 * Real.sqrt E) + Real.sqrt (3 / (2 * k))) := by
    have hsE : 0 < Real.sqrt E := Real.sqrt_pos.mpr hE
    have h3 : 2 * Real.sqrt (ε - ε / 4) / Real.sqrt (2 * (k / ε))
        = ε * Real.sqrt (3 / (2 * k)) := by
      refine (sq_eq_sq₀ (by positivity) (by positivity)).mp ?_
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity)]
      field_simp
      ring
    unfold Reflection.sharpTime
    rw [h3]
    field_simp
    ring
  have hsetup : Reflection.SharpSetup Φ (ε / 4) ε (Ψ 1) (k / ε) E d 0 T x p :=
    { contDiff := hΦ1
      nonneg := fun s => by
        change 0 ≤ Ψ (s / ε)
        rcases le_total (s / ε) 0 with h | h
        · rw [hflat _ h]
        · have := hmono h
          rwa [hflat 0 le_rfl] at this
      flat := fun s hs => hflat _ (div_nonpos_of_nonpos_of_nonneg hs hε.le)
      mono := fun s => by rw [hderivΦ]; exact div_nonneg hmono.deriv_nonneg hε.le
      high := fun s hs => hmono (by rw [le_div_iff₀ hε]; linarith)
      slope := fun s hs => by
        rw [hderivΦ]
        refine div_le_div_of_nonneg_right (hslope _ ⟨?_, ?_⟩) hε.le
        · rw [le_div_iff₀ hε]; linarith [hs.1]
        · rw [div_le_one hε]; exact hs.2
      low := fun s hs => hlow _ (by rw [div_le_iff₀ hε]; linarith)
      δ_pos := by linarith
      δ_lt := by linarith
      k_pos := div_pos hk hε
      E_pos := hE
      E_lt := hhigh
      d_nonneg := hd
      hx := hx
      hp := hp
      init_x := hx0
      init_p := hp0
      long := by rw [hsharp]; linarith }
  obtain ⟨t₁, ht₁, hxt₁, hpt₁, -, hbeyond⟩ := Reflection.reflect_of_barrier_sharp hsetup
  rw [zero_add, hsharp] at ht₁
  have ht₁T : t₁ ∈ Icc 0 T := ⟨ht₁.1.le, by linarith [ht₁.2]⟩
  obtain ⟨hxy₁, hpy₁⟩ := hxy t₁ ht₁T (by rw [hxt₁])
  refine ⟨t₁, ht₁.1, ht₁.2, by rw [← hxy₁, hxt₁], by rw [← hpy₁, hpt₁], fun t ht => ?_⟩
  have htT : t ∈ Icc 0 T := ⟨ht.1.le, by linarith [ht.2, ht₁.2]⟩
  have hb := hbeyond t (by simpa using ht)
  obtain ⟨hxyt, -⟩ := hxy t htT hb.le
  exact ⟨by rw [← hxyt]; exact hb, hyε t htT⟩

end HamiltonianMetricGraphs
