/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.WorkedExamplesTheta

/-!
# The periods diverge at the barrier height (Section XI.B)

The paper states, for the theta graph with an interior barrier of height `h` on `e₃`:

  as `E → h`, the flight time near the barrier top diverges, so `T₁, T₂ → ∞` as `E ↑ h` and
  `T → ∞` as `E ↓ h`.

We prove it from the `C²` regularity of `V₃` alone.  Near the critical point `q_*`,
`h - V₃(q) ≤ M (q - q_*)²` (`IsBarrier.exists_quadratic`, by the mean value theorem applied to
`V₃'` and then to `V₃`).  Hence, on `[q_* ± ε, q_* ± δ]` and for `E` close enough to `h`,
`E - V₃(q) ≤ 2M (q - q_*)²`, the integrand `1/√(2(E - V₃))` is at least `1/(2√M |q - q_*|)`
(`one_div_le_integrand`), and the flight time is at least `log(δ/ε)/(2√M)`; letting `ε → 0`
gives the divergence.

Below the barrier the integral `∫_0^{q₋} dq / √(2(E - V₃))` is improper; its integrability is
read off from the positivity of the flight time.

The packaged statement of Section XI.B is `example_theta`.
-/

namespace HamiltonianMetricGraphs

namespace WorkedExamples

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

namespace BarrierProfile

variable {L : ℝ} {B : BarrierProfile L} {q h : ℝ}

/-- **Quadratic behaviour at the barrier top**: `h - V₃(x) ≤ M (x - q_*)²` near `q_*`. -/
theorem IsBarrier.exists_quadratic (hB : B.IsBarrier q h) :
    ∃ M > 0, ∃ δ > 0, δ < q ∧ q + δ < L ∧
      ∀ x ∈ Icc (q - δ) (q + δ), h - B.V₃ x ≤ M * (x - q) ^ 2 := by
  obtain ⟨hq0, hqL⟩ := hB.mem
  have hD : IsOpen (B.domain ∩ Ioo 0 L) := B.isOpen_domain.inter isOpen_Ioo
  have hqD : q ∈ B.domain ∩ Ioo 0 L :=
    ⟨B.Icc_subset_domain (Ioo_subset_Icc_self hB.mem), hB.mem⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD q hqD
  set δ := r / 2 with hδ
  have hIcc : Icc (q - δ) (q + δ) ⊆ B.domain ∩ Ioo 0 L := fun x hx => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2])
  have hd1 : ContDiffOn ℝ 1 (deriv B.V₃) B.domain :=
    B.contDiffOn.deriv_of_isOpen B.isOpen_domain (by norm_num)
  have hdiff1 : DifferentiableOn ℝ (deriv B.V₃) B.domain := hd1.differentiableOn (by norm_num)
  have hcont2 : ContinuousOn (deriv (deriv B.V₃)) B.domain :=
    hd1.continuousOn_deriv_of_isOpen B.isOpen_domain le_rfl
  have hdiff0 : DifferentiableOn ℝ B.V₃ B.domain := B.contDiffOn.differentiableOn (by norm_num)
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont2.mono fun x hx => (hIcc hx).1)
  have hqmem : q ∈ Icc (q - δ) (q + δ) := ⟨by linarith, by linarith⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK q hqmem)
  have hcrit : deriv B.V₃ q = 0 := (hB.critical_iff q hB.mem).mpr rfl
  -- `|V₃'(x)| ≤ K |x - q_*|`
  have h1 : ∀ x ∈ Icc (q - δ) (q + δ), |deriv B.V₃ x| ≤ K * |x - q| := by
    intro x hx
    have := (convex_Icc (q - δ) (q + δ)).norm_image_sub_le_of_norm_deriv_le
      (fun y hy => hdiff1.differentiableAt (B.isOpen_domain.mem_nhds (hIcc hy).1))
      (fun y hy => hK y hy) hqmem hx
    simpa [hcrit, Real.norm_eq_abs] using this
  have hδpos : 0 < δ := by positivity
  refine ⟨K + 1, by linarith, δ, hδpos,
    by have := (hIcc (left_mem_Icc.2 (by linarith))).2.1; linarith,
    by have := (hIcc (right_mem_Icc.2 (by linarith))).2.2; linarith, fun x hx => ?_⟩
  -- `|V₃(x) - h| ≤ K (x - q_*)²`
  have hsub : uIcc q x ⊆ Icc (q - δ) (q + δ) :=
    (ordConnected_Icc).uIcc_subset hqmem hx
  have h2 := (convex_uIcc q x).norm_image_sub_le_of_norm_deriv_le
    (f := B.V₃) (C := K * |x - q|)
    (fun y hy => hdiff0.differentiableAt (B.isOpen_domain.mem_nhds (hIcc (hsub hy)).1))
    (fun y hy => by
      rw [Real.norm_eq_abs]
      exact (h1 y (hsub hy)).trans (mul_le_mul_of_nonneg_left
        (abs_sub_left_of_mem_uIcc hy) hK0))
    left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hB.value] at h2
  have h3 : h - B.V₃ x ≤ |B.V₃ x - h| := by rw [abs_sub_comm]; exact le_abs_self _
  have h4 : K * |x - q| * |x - q| = K * (x - q) ^ 2 := by
    rw [mul_assoc, ← sq, sq_abs]
  nlinarith [sq_nonneg (x - q)]

end BarrierProfile

/-! ### Elementary estimates -/

/-- The integrand lower bound: if `0 < E - V ≤ 2M (x - q)²` then
`1/(2√M |x - q|) ≤ 1/√(2(E - V))`. -/
theorem one_div_le_integrand {M E v x q : ℝ} (hM : 0 < M) (hpos : 0 < E - v)
    (hle : E - v ≤ 2 * M * (x - q) ^ 2) :
    1 / (2 * Real.sqrt M * |x - q|) ≤ 1 / Real.sqrt (2 * (E - v)) := by
  have hs : Real.sqrt (2 * (E - v)) ≤ 2 * Real.sqrt M * |x - q| := by
    have hsq : (2 * Real.sqrt M * |x - q|) ^ 2 = 4 * M * (x - q) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hM.le, sq_abs]; ring
    calc Real.sqrt (2 * (E - v)) ≤ Real.sqrt ((2 * Real.sqrt M * |x - q|) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [hsq]; linarith)
      _ = 2 * Real.sqrt M * |x - q| := Real.sqrt_sq (by positivity)
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by linarith)) hs

/-- `∫_{q+ε}^{q+δ} dx / (c (x - q)) = log(δ/ε) / c`. -/
theorem integral_inv_right {c q ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∫ x in (q + ε)..(q + δ), 1 / (c * (x - q)) = Real.log (δ / ε) / c := by
  rw [intervalIntegral.integral_comp_sub_right (fun y => 1 / (c * y)) q]
  simp only [add_sub_cancel_left, one_div, mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hε hδ, inv_mul_eq_div]

/-- `∫_{q-δ}^{q-ε} dx / (c (q - x)) = log(δ/ε) / c`. -/
theorem integral_inv_left {c q ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∫ x in (q - δ)..(q - ε), 1 / (c * (q - x)) = Real.log (δ / ε) / c := by
  rw [intervalIntegral.integral_comp_sub_left (fun y => 1 / (c * y)) q]
  simp only [sub_sub_cancel, one_div, mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hε hδ, inv_mul_eq_div]

/-- Given a scale `δ > 0`, a constant `c > 0` and a target `N`, the radius
`ε = δ e^{-c(|N|+1)}` lies in `(0, δ)` and makes `log(δ/ε)/c = |N| + 1`. -/
theorem log_radius {c δ N : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    let ε := δ * Real.exp (-(c * (|N| + 1)))
    0 < ε ∧ ε < δ ∧ Real.log (δ / ε) / c = |N| + 1 := by
  intro ε
  have hexp : Real.exp (-(c * (|N| + 1))) < 1 :=
    Real.exp_lt_one_iff.mpr (by have := abs_nonneg N; nlinarith)
  refine ⟨by positivity, by nlinarith [Real.exp_pos (-(c * (|N| + 1)))], ?_⟩
  rw [show δ / ε = Real.exp (c * (|N| + 1)) by
    simp only [ε]
    rw [Real.exp_neg]
    field_simp]
  rw [Real.log_exp]
  field_simp

variable {ℓ : Fin 3 → ℝ} {hℓ : ∀ i, 0 < ℓ i} {B : BarrierProfile (ℓ 2)} {q h : ℝ}

/-- The integrand `1/√(2(E - V₃))` is continuous where `V₃ < E`. -/
theorem continuousOn_integrand {E : ℝ} {s : Set ℝ} (hs : s ⊆ Icc 0 (ℓ 2))
    (hlt : ∀ x ∈ s, B.V₃ x < E) :
    ContinuousOn (fun x => 1 / Real.sqrt (2 * (E - B.V₃ x))) s :=
  continuousOn_const.div (Real.continuous_sqrt.comp_continuousOn
    (continuousOn_const.mul (continuousOn_const.sub (B.continuousOn_Icc.mono hs))))
    (fun x hx => (Real.sqrt_pos.mpr (by linarith [hlt x hx])).ne')

theorem integrand_nonneg (E x : ℝ) : 0 ≤ 1 / Real.sqrt (2 * (E - B.V₃ x)) :=
  one_div_nonneg.mpr (Real.sqrt_nonneg _)

/-! ### Divergence of the periods -/

open Classical in
/-- **`T → ∞` as `E ↓ h`.**  Above the barrier the period of the single cycle diverges as the
energy decreases to the barrier height. -/
theorem theta_tendsto_above (hB : B.IsBarrier q h) (η : (theta ℓ hℓ).EdgeEnd) :
    Tendsto (fun E => (thetaPotential ℓ hℓ B).cyclePeriod (thetaS ℓ hℓ B) E η) (𝓝[>] h)
      atTop := by
  obtain ⟨M, hM, δ, hδ, hδq, hqδ, hquad⟩ := hB.exists_quadratic
  set c := 2 * Real.sqrt M with hcdef
  have hc : 0 < c := by positivity
  rw [tendsto_atTop]
  intro N
  obtain ⟨hε, hεδ, hlog⟩ := log_radius (N := N) hc hδ
  set ε := δ * Real.exp (-(c * (|N| + 1))) with hεdef
  filter_upwards [Ioo_mem_nhdsGT (show h < h + M * ε ^ 2 by have := sq_pos_of_pos hε; nlinarith)]
    with E hE
  have hhE : h < E := hE.1
  rw [(theta_above (ℓ := ℓ) (hℓ := hℓ) hB hhE).2.2.2.2 η]
  set f := fun x => 1 / Real.sqrt (2 * (E - B.V₃ x)) with hf
  have hq := hB.mem
  have hsubI : Icc (q + ε) (q + δ) ⊆ Icc 0 (ℓ 2) :=
    Icc_subset_Icc (by linarith [hq.1]) hqδ.le
  have hltall : ∀ x ∈ Icc 0 (ℓ 2), B.V₃ x < E := fun x hx => (hB.le hx).trans_lt hhE
  have hint : ∫ x in (q + ε)..(q + δ), f x ≤ ∫ x in (0 : ℝ)..ℓ 2, f x :=
    intervalIntegral.integral_mono_interval (by linarith [hq.1]) (by linarith) hqδ.le
      (Filter.Eventually.of_forall fun x => integrand_nonneg E x)
      ((continuousOn_integrand le_rfl hltall).intervalIntegrable_of_Icc
        (by linarith [hq.1, hq.2]))
  have hlower : ∫ x in (q + ε)..(q + δ), 1 / (c * (x - q)) ≤ ∫ x in (q + ε)..(q + δ), f x := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_
      ((continuousOn_integrand hsubI fun x hx => hltall x (hsubI hx)).intervalIntegrable_of_Icc
        (by linarith)) fun x hx => ?_
    · refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) ?_
      exact continuousOn_const.div (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
        (fun x hx => mul_ne_zero hc.ne' (by linarith [hx.1]))
    · have hxq : 0 < x - q := by linarith [hx.1]
      have hb := hquad x ⟨by linarith [hx.1], hx.2⟩
      have hεx : ε ^ 2 ≤ (x - q) ^ 2 := pow_le_pow_left₀ hε.le (by linarith [hx.1]) 2
      have h1 := one_div_le_integrand (v := B.V₃ x) hM (by linarith [hltall x (hsubI hx)])
        (show E - B.V₃ x ≤ 2 * M * (x - q) ^ 2 by nlinarith [hE.2])
      rw [abs_of_pos hxq] at h1
      exact h1
  rw [integral_inv_right hε hδ, hlog] at hlower
  have key : |N| + 1 ≤ intervalIntegral f 0 (ℓ 2) MeasureTheory.volume := hlower.trans hint
  calc N ≤ 2 * (|N| + 1) := by linarith [abs_nonneg N, le_abs_self N]
    _ ≤ 2 * intervalIntegral f 0 (ℓ 2) MeasureTheory.volume := by linarith
    _ ≤ _ := le_add_of_nonneg_left (by have := hℓ 0; have := hℓ 1; positivity)

open Classical in
/-- **`T₁ → ∞` as `E ↑ h`.**  Below the barrier the period of the cycle `(η₁ η₂' η₃)` diverges
as the energy increases to the barrier height. -/
theorem theta_tendsto_below_one (hB : B.IsBarrier q h) :
    Tendsto (fun E => (thetaPotential ℓ hℓ B).cyclePeriod (thetaS ℓ hℓ B) E ((0 : Fin 3), false))
      (𝓝[<] h) atTop := by
  obtain ⟨M, hM, δ, hδ, hδq, hqδ, hquad⟩ := hB.exists_quadratic
  set c := 2 * Real.sqrt M with hcdef
  have hc : 0 < c := by positivity
  have hq := hB.mem
  rw [tendsto_atTop]
  intro N
  obtain ⟨hε, hεδ, hlog⟩ := log_radius (N := N) hc hδ
  set ε := δ * Real.exp (-(c * (|N| + 1))) with hεdef
  have hmono := hB.strictMonoOn
  have hqε : q - ε ∈ Icc 0 q := ⟨by linarith, by linarith⟩
  have hVε : B.V₃ (q - ε) < h := by
    rw [← hB.value]; exact hmono hqε (right_mem_Icc.2 hq.1.le) (by linarith)
  filter_upwards [Ioo_mem_nhdsLT hVε] with E hE
  have hVε0 : 0 ≤ B.V₃ (q - ε) := by
    rw [← B.left_eq_zero]; exact hmono.monotoneOn (left_mem_Icc.2 hq.1.le) hqε hqε.1
  have hE0 : 0 < E := by linarith [hE.1]
  obtain ⟨⟨qm, ⟨hqm, hqmE⟩, -⟩, ⟨qp, ⟨hqp, hqpE⟩, -⟩⟩ := hB.exists_turning hE0 hE.2
  -- the turning point lies beyond `q - ε`
  have hqmε : q - ε < qm := by
    by_contra hcon
    push Not at hcon
    have := hmono.monotoneOn ⟨hqm.1.le, hqm.2.le⟩ hqε hcon
    linarith [hE.1]
  rw [(theta_below (ℓ := ℓ) (hℓ := hℓ) hB hE0 hE.2 hqm hqmE hqp hqpE).2.2.2.2.2.2.2.1]
  set f := fun x => 1 / Real.sqrt (2 * (E - B.V₃ x)) with hf
  -- integrability of the improper integral, from the positivity of the flight time
  have hS := theta_shellRegular (ℓ := ℓ) (hℓ := hℓ) hB hE0 hE.2.ne
  have hft := theta_flightTime_below_left (ℓ := ℓ) (hℓ := hℓ) hB hE0 hE.2 hqm hqmE
  have hftpos := (thetaPotential ℓ hℓ B).flightTime_pos hS
    (theta_mem_allowedGerms ℓ hℓ B hE0 ((2 : Fin 3), false))
  have hII : IntervalIntegrable f MeasureTheory.volume 0 qm := by
    by_contra hcon
    rw [intervalIntegral.integral_undef hcon, mul_zero] at hft
    linarith
  have hsubI : Icc (q - δ) (q - ε) ⊆ Icc 0 (ℓ 2) :=
    Icc_subset_Icc (by linarith) (by linarith [hq.2])
  have hltI : ∀ x ∈ Icc (q - δ) (q - ε), B.V₃ x < E := fun x hx => by
    rw [← hqmE]
    exact hB.lt_left ⟨hqm.1.le, hqm.2.le⟩ ⟨by linarith [hx.1], by linarith [hx.2]⟩
      (by linarith [hx.2])
  have hint : ∫ x in (q - δ)..(q - ε), f x ≤ ∫ x in (0 : ℝ)..qm, f x :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) hqmε.le
      (Filter.Eventually.of_forall fun x => integrand_nonneg E x) hII
  have hlower : ∫ x in (q - δ)..(q - ε), 1 / (c * (q - x)) ≤ ∫ x in (q - δ)..(q - ε), f x := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_
      ((continuousOn_integrand hsubI hltI).intervalIntegrable_of_Icc (by linarith))
      fun x hx => ?_
    · refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) ?_
      exact continuousOn_const.div (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))
        (fun x hx => mul_ne_zero hc.ne' (by linarith [hx.2]))
    · have hxq : 0 < q - x := by linarith [hx.2]
      have hb := hquad x ⟨hx.1, by linarith [hx.2]⟩
      have h1 := one_div_le_integrand (v := B.V₃ x) hM (by linarith [hltI x hx])
        (show E - B.V₃ x ≤ 2 * M * (x - q) ^ 2 by nlinarith [hE.2, sq_nonneg (x - q)])
      rw [abs_sub_comm, abs_of_pos hxq] at h1
      exact h1
  rw [integral_inv_left hε hδ, hlog] at hlower
  have key : |N| + 1 ≤ intervalIntegral f 0 qm MeasureTheory.volume := hlower.trans hint
  calc N ≤ 2 * (|N| + 1) := by linarith [abs_nonneg N, le_abs_self N]
    _ ≤ 2 * intervalIntegral f 0 qm MeasureTheory.volume := by linarith
    _ ≤ _ := le_add_of_nonneg_left (by have := hℓ 0; have := hℓ 1; positivity)

open Classical in
/-- **`T₂ → ∞` as `E ↑ h`.**  Below the barrier the period of the cycle `(η₂ η₃' η₁')` diverges
as the energy increases to the barrier height. -/
theorem theta_tendsto_below_two (hB : B.IsBarrier q h) :
    Tendsto (fun E => (thetaPotential ℓ hℓ B).cyclePeriod (thetaS ℓ hℓ B) E ((1 : Fin 3), false))
      (𝓝[<] h) atTop := by
  obtain ⟨M, hM, δ, hδ, hδq, hqδ, hquad⟩ := hB.exists_quadratic
  set c := 2 * Real.sqrt M with hcdef
  have hc : 0 < c := by positivity
  have hq := hB.mem
  rw [tendsto_atTop]
  intro N
  obtain ⟨hε, hεδ, hlog⟩ := log_radius (N := N) hc hδ
  set ε := δ * Real.exp (-(c * (|N| + 1))) with hεdef
  have hanti := hB.strictAntiOn
  have hqε : q + ε ∈ Icc q (ℓ 2) := ⟨by linarith, by linarith⟩
  have hVε : B.V₃ (q + ε) < h := by
    rw [← hB.value]; exact hanti (left_mem_Icc.2 hq.2.le) hqε (by linarith)
  filter_upwards [Ioo_mem_nhdsLT hVε] with E hE
  have hVε0 : 0 ≤ B.V₃ (q + ε) := by
    rw [← B.right_eq_zero]; exact hanti.antitoneOn hqε (right_mem_Icc.2 hq.2.le) hqε.2
  have hE0 : 0 < E := by linarith [hE.1]
  obtain ⟨⟨qm, ⟨hqm, hqmE⟩, -⟩, ⟨qp, ⟨hqp, hqpE⟩, -⟩⟩ := hB.exists_turning hE0 hE.2
  -- the turning point lies before `q + ε`
  have hqpε : qp < q + ε := by
    by_contra hcon
    push Not at hcon
    have := hanti.antitoneOn hqε ⟨hqp.1.le, hqp.2.le⟩ hcon
    linarith [hE.1]
  rw [(theta_below (ℓ := ℓ) (hℓ := hℓ) hB hE0 hE.2 hqm hqmE hqp hqpE).2.2.2.2.2.2.2.2]
  set f := fun x => 1 / Real.sqrt (2 * (E - B.V₃ x)) with hf
  have hS := theta_shellRegular (ℓ := ℓ) (hℓ := hℓ) hB hE0 hE.2.ne
  have hft := theta_flightTime_below_right (ℓ := ℓ) (hℓ := hℓ) hB hE0 hE.2 hqp hqpE
  have hftpos := (thetaPotential ℓ hℓ B).flightTime_pos hS
    (theta_mem_allowedGerms ℓ hℓ B hE0 ((2 : Fin 3), true))
  have hII : IntervalIntegrable f MeasureTheory.volume qp (ℓ 2) := by
    by_contra hcon
    rw [intervalIntegral.integral_undef hcon, mul_zero] at hft
    linarith
  have hsubI : Icc (q + ε) (q + δ) ⊆ Icc 0 (ℓ 2) :=
    Icc_subset_Icc (by linarith [hq.1]) hqδ.le
  have hltI : ∀ x ∈ Icc (q + ε) (q + δ), B.V₃ x < E := fun x hx => by
    rw [← hqpE]
    exact hB.lt_right ⟨hqp.1.le, hqp.2.le⟩ ⟨by linarith [hx.1], by linarith [hx.2]⟩
      (by linarith [hx.1])
  have hint : ∫ x in (q + ε)..(q + δ), f x ≤ ∫ x in qp..ℓ 2, f x :=
    intervalIntegral.integral_mono_interval hqpε.le (by linarith) hqδ.le
      (Filter.Eventually.of_forall fun x => integrand_nonneg E x) hII
  have hlower : ∫ x in (q + ε)..(q + δ), 1 / (c * (x - q)) ≤ ∫ x in (q + ε)..(q + δ), f x := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_
      ((continuousOn_integrand hsubI hltI).intervalIntegrable_of_Icc (by linarith))
      fun x hx => ?_
    · refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) ?_
      exact continuousOn_const.div (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
        (fun x hx => mul_ne_zero hc.ne' (by linarith [hx.1]))
    · have hxq : 0 < x - q := by linarith [hx.1]
      have hb := hquad x ⟨by linarith [hx.1], hx.2⟩
      have h1 := one_div_le_integrand (v := B.V₃ x) hM (by linarith [hltI x hx])
        (show E - B.V₃ x ≤ 2 * M * (x - q) ^ 2 by nlinarith [hE.2, sq_nonneg (x - q)])
      rw [abs_of_pos hxq] at h1
      exact h1
  rw [integral_inv_right hε hδ, hlog] at hlower
  have key : |N| + 1 ≤ intervalIntegral f qp (ℓ 2) MeasureTheory.volume := hlower.trans hint
  calc N ≤ 2 * (|N| + 1) := by linarith [abs_nonneg N, le_abs_self N]
    _ ≤ 2 * intervalIntegral f qp (ℓ 2) MeasureTheory.volume := by linarith
    _ ≤ _ := le_add_of_nonneg_left (by have := hℓ 0; have := hℓ 1; positivity)

/-! ### Section XI.B, packaged -/

open Classical in
/-- **Section XI.B (an interior barrier), packaged.**  On the theta graph with `V₁ = V₂ = 0`, a
barrier `V₃` (vanishing at both endpoints, `C²` near `[0, ℓ₃]`, with a unique interior critical
point `q_*` and `V₃(q_*) = h > 0`) and the vertex laws `F_a = (η₁ η₂ η₃)`,
`F_b = (η₁' η₂' η₃')`:

* `Exc = {0}`, every `E > 0` with `E ≠ h` is shell-regular, and `E = h` is not;
* for `E > h`: `Π_E = (η₁ η₂' η₃ η₁' η₂ η₃')`, cycle type `(6)`, one cycle and one periodic
  orbit on `Σ_E`, with period
  `T(E) = 2(ℓ₁+ℓ₂)/√(2E) + 2 ∫_0^{ℓ₃} dq/√(2(E - V₃(q)))`;
* for `0 < E < h` and `q₋ < q_* < q₊` with `V₃(q±) = E` (these exist and are unique):
  `κ_E(η₃) = η₃`, `κ_E(η₃') = η₃'`, `Π_E = (η₁ η₂' η₃)(η₂ η₃' η₁')`, cycle type `(3,3)`, two
  cycles and two periodic orbits on `Σ_E`, with periods
  `T₁(E) = (ℓ₁+ℓ₂)/√(2E) + 2 ∫_0^{q₋} dq/√(2(E - V₃(q)))` and
  `T₂(E) = (ℓ₁+ℓ₂)/√(2E) + 2 ∫_{q₊}^{ℓ₃} dq/√(2(E - V₃(q)))`;
* `T₁, T₂ → ∞` as `E ↑ h` and `T → ∞` as `E ↓ h`. -/
theorem example_theta (hB : B.IsBarrier q h) :
    (thetaPotential ℓ hℓ B).exceptionalEnergies = {0} ∧
      (∀ E, 0 < E → E ≠ h → (thetaPotential ℓ hℓ B).ShellRegular E) ∧
      ¬ (thetaPotential ℓ hℓ B).ShellRegular h ∧
      -- above the barrier
      (∀ E (hhE : h < E),
        (∀ η, (thetaPotential ℓ hℓ B).retraceEnd E η = (η.1, !η.2)) ∧
        (∀ η, (thetaPotential ℓ hℓ B).germStep (thetaS ℓ hℓ B) E η = thetaAbovePerm η) ∧
        ((thetaPotential ℓ hℓ B).shellGermPerm (thetaS ℓ hℓ B)
          (theta_shellRegular hB (hB.pos.trans hhE) (ne_of_gt hhE))).cycleType = {6} ∧
        ((thetaPotential ℓ hℓ B).germCycles (thetaS ℓ hℓ B) E).card = 1 ∧
        Nat.card {O : Set (RegularScatteringPhaseSpace (V := thetaPotential ℓ hℓ B)
            (thetaS ℓ hℓ B)) //
          ∃ (η : (theta ℓ hℓ).EdgeEnd) (hη : η ∈ (thetaPotential ℓ hℓ B).allowedGerms E),
            O = (thetaPotential ℓ hℓ B).shellOrbit (thetaS ℓ hℓ B)
              (theta_shellRegular hB (hB.pos.trans hhE) (ne_of_gt hhE)) η hη} = 1 ∧
        ∀ η, (thetaPotential ℓ hℓ B).cyclePeriod (thetaS ℓ hℓ B) E η =
          2 * (ℓ 0 + ℓ 1) / Real.sqrt (2 * E) +
            2 * ∫ x in (0 : ℝ)..ℓ 2, 1 / Real.sqrt (2 * (E - B.V₃ x))) ∧
      -- below the barrier
      (∀ E (hE0 : 0 < E) (hEh : E < h),
        (∃! x, x ∈ Ioo 0 q ∧ B.V₃ x = E) ∧ (∃! x, x ∈ Ioo q (ℓ 2) ∧ B.V₃ x = E) ∧
        ∀ qm qp, qm ∈ Ioo 0 q → B.V₃ qm = E → qp ∈ Ioo q (ℓ 2) → B.V₃ qp = E →
          (thetaPotential ℓ hℓ B).retraceEnd E ((2 : Fin 3), false) = ((2 : Fin 3), false) ∧
          (thetaPotential ℓ hℓ B).retraceEnd E ((2 : Fin 3), true) = ((2 : Fin 3), true) ∧
          (∀ η, (thetaPotential ℓ hℓ B).germStep (thetaS ℓ hℓ B) E η = thetaBelowPerm η) ∧
          ((thetaPotential ℓ hℓ B).shellGermPerm (thetaS ℓ hℓ B)
            (theta_shellRegular hB hE0 hEh.ne)).cycleType = {3, 3} ∧
          ((thetaPotential ℓ hℓ B).germCycles (thetaS ℓ hℓ B) E).card = 2 ∧
          Nat.card {O : Set (RegularScatteringPhaseSpace (V := thetaPotential ℓ hℓ B)
              (thetaS ℓ hℓ B)) //
            ∃ (η : (theta ℓ hℓ).EdgeEnd) (hη : η ∈ (thetaPotential ℓ hℓ B).allowedGerms E),
              O = (thetaPotential ℓ hℓ B).shellOrbit (thetaS ℓ hℓ B)
                (theta_shellRegular hB hE0 hEh.ne) η hη} = 2 ∧
          (thetaPotential ℓ hℓ B).cyclePeriod (thetaS ℓ hℓ B) E ((0 : Fin 3), false) =
            (ℓ 0 + ℓ 1) / Real.sqrt (2 * E) +
              2 * ∫ x in (0 : ℝ)..qm, 1 / Real.sqrt (2 * (E - B.V₃ x)) ∧
          (thetaPotential ℓ hℓ B).cyclePeriod (thetaS ℓ hℓ B) E ((1 : Fin 3), false) =
            (ℓ 0 + ℓ 1) / Real.sqrt (2 * E) +
              2 * ∫ x in qp..ℓ 2, 1 / Real.sqrt (2 * (E - B.V₃ x))) ∧
      -- divergence of the periods at the barrier height
      Tendsto (fun E => (thetaPotential ℓ hℓ B).cyclePeriod (thetaS ℓ hℓ B) E
        ((0 : Fin 3), false)) (𝓝[<] h) atTop ∧
      Tendsto (fun E => (thetaPotential ℓ hℓ B).cyclePeriod (thetaS ℓ hℓ B) E
        ((1 : Fin 3), false)) (𝓝[<] h) atTop ∧
      ∀ η, Tendsto (fun E => (thetaPotential ℓ hℓ B).cyclePeriod (thetaS ℓ hℓ B) E η)
        (𝓝[>] h) atTop := by
  refine ⟨theta_exceptionalEnergies ℓ hℓ B, fun E hE0 hEh => theta_shellRegular hB hE0 hEh,
    theta_not_shellRegular hB, fun E hhE => ?_, fun E hE0 hEh => ?_,
    theta_tendsto_below_one hB, theta_tendsto_below_two hB, theta_tendsto_above hB⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := theta_above (ℓ := ℓ) (hℓ := hℓ) hB hhE
    have hc : ((thetaPotential ℓ hℓ B).germCycles (thetaS ℓ hℓ B) E).card = 1 := by
      rw [h4]; rfl
    exact ⟨h1, h2, h3, hc, by rw [card_shellOrbits_eq_card_germCycles, hc], h5⟩
  · refine ⟨(hB.exists_turning hE0 hEh).1, (hB.exists_turning hE0 hEh).2,
      fun qm qp hqm hqmE hqp hqpE => ?_⟩
    obtain ⟨h1, h2, h3, h4, -, -, h7, h8, h9⟩ :=
      theta_below (ℓ := ℓ) (hℓ := hℓ) hB hE0 hEh hqm hqmE hqp hqpE
    exact ⟨h1, h2, h3, h4, h7, by rw [card_shellOrbits_eq_card_germCycles, h7], h8, h9⟩

end WorkedExamples

end HamiltonianMetricGraphs
