/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/
import Mathlib

/-!
# Real-analyticity of flight times (Proposition VIII.7, last sentence)

Proposition VIII.7 ends: *if `V` is edgewise real-analytic, each period `T_c(E)` is
real-analytic on `I`.* A period is a finite sum of flight times, and a flight time has one of two
shapes, with `f` the edge potential and `√(2 (E - f q))` the speed:

* a **crossing flight** `E ↦ ∫ q in a..b, 1 / √(2 (E - f q))`, at energies with `f < E` on
  `[a, b]`;
* a **reflected flight** from the end `a` with a simple turning point,
  `E ↦ 2 * |∫ q in a..τ E, 1 / √(2 (E - f q))|`, where `f (τ E) = E` and `f' (τ E) ≠ 0`.

This file proves that both are real-analytic in `E`.

## Main results

* `HamiltonianMetricGraphs.FlightTimeAnalytic.analyticAt_intervalIntegral`: if `(x, w) ↦ h x w`
  is jointly real-analytic on `{x₀} × [α, β]`, then `x ↦ ∫ w in α..β, h x w` is analytic at `x₀`.
* `HamiltonianMetricGraphs.analyticAt_crossingTime`: crossing flight times are analytic.
* `HamiltonianMetricGraphs.exists_analyticAt_turningPoint`: the turning point is an analytic
  function of the energy (analytic inverse function theorem, from Mathlib).
* `HamiltonianMetricGraphs.analyticAt_reflectionTime` and
  `HamiltonianMetricGraphs.analyticAt_reflectionTime_two_mul_abs`: reflected flight times are
  analytic.

## Proof outline

*Parametric integrals.* Let `H` have the power series `p` at `(x₀, w₀)`. The average
`K y = ∫ s in 0..1, H ((x₀, w₀) + (y.1, s * y.2))` has the power series
`n ↦ ∫ s in 0..1, (p n).compContinuousLinearMap (fun _ => (e, d) ↦ (e, s d))`, with no loss of
radius (dominated convergence, term by term). Since
`∫ w in w₀..w₀ + d, H (x, w) = d • K (x - x₀, d)`, integrals over short intervals are analytic
in the parameter; a connectedness argument (`IsPreconnected.induction₂'`) on `[α, β]` glues these.

*Crossing flights* are then immediate: the integrand is jointly analytic where `f q < E`.

*Reflected flights.* The substitution `q = τ E - (τ E - a) w²`, `w ∈ [0, 1]`, is made with the
one-dimensional change of variables for injective maps
(`MeasureTheory.integral_image_eq_integral_abs_deriv_smul`), which needs no integrability of the
singular integrand. Writing `f x - f (x - v) = v * D x v` with the divided difference
`D x v = ∫ θ in 0..1, f' (x - θ v)` (jointly analytic, again by the parametric-integral theorem),
the integral becomes `∫ w in 0..1, 2 (τ E - a) / √(2 (τ E - a) D (τ E) ((τ E - a) w²))`, whose
integrand is jointly analytic: the radicand is positive at `E₀` (at `w = 0` it is
`2 (t₀ - a) f' t₀`, whose sign is forced by `f < E₀` between `a` and `t₀`).
-/

namespace HamiltonianMetricGraphs

open Set Filter MeasureTheory intervalIntegral
open scoped Topology NNReal ENNReal ContDiff

namespace FlightTimeAnalytic

/-! ### Analyticity of parametric integrals -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The linear map `(e, d) ↦ (e, s * d)`. -/
noncomputable def sliceCLM (s : ℝ) : P × ℝ →L[ℝ] P × ℝ :=
  (ContinuousLinearMap.fst ℝ P ℝ).prod 0 +
    s • (0 : P × ℝ →L[ℝ] P).prod (ContinuousLinearMap.snd ℝ P ℝ)

/-- `sliceCLM` evaluated. -/
lemma sliceCLM_apply (s : ℝ) (y : P × ℝ) : sliceCLM s y = (y.1, s * y.2) := by
  ext <;> simp [sliceCLM]

lemma continuous_sliceCLM : Continuous (sliceCLM (P := P)) := by
  unfold sliceCLM
  fun_prop

lemma norm_sliceCLM_apply_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (y : P × ℝ) :
    ‖sliceCLM s y‖ ≤ ‖y‖ := by
  rw [sliceCLM_apply, Prod.norm_def, Prod.norm_def]
  refine max_le_max le_rfl ?_
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hs.2

lemma norm_sliceCLM_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : ‖sliceCLM (P := P) s‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    simpa using norm_sliceCLM_apply_le hs y

/-- The power series of the averaged function `y ↦ ∫ s in 0..1, H (z₀ + (y.1, s * y.2))`. -/
noncomputable def sliceSeries [CompleteSpace F] (p : FormalMultilinearSeries ℝ (P × ℝ) F) :
    FormalMultilinearSeries ℝ (P × ℝ) F := fun n =>
  ∫ s in (0 : ℝ)..1, (p n).compContinuousLinearMap (fun _ => sliceCLM s)

lemma continuous_compSlice (p : FormalMultilinearSeries ℝ (P × ℝ) F) (n : ℕ) :
    Continuous fun s : ℝ =>
      (p n).compContinuousLinearMap (fun _ : Fin n => sliceCLM (P := P) s) := by
  have h := (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n => P × ℝ) (fun _ : Fin n => P × ℝ) F).cont.comp
      (continuous_pi fun _ : Fin n => continuous_sliceCLM (P := P))
  have := h.clm_apply (continuous_const (y := p n))
  simpa using this

lemma norm_sliceSeries_le [CompleteSpace F] (p : FormalMultilinearSeries ℝ (P × ℝ) F) (n : ℕ) :
    ‖sliceSeries p n‖ ≤ ‖p n‖ := by
  have := norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := ‖p n‖)
    (f := fun s : ℝ => (p n).compContinuousLinearMap (fun _ : Fin n => sliceCLM (P := P) s))
    (fun s hs => by
      have hs' : s ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le zero_le_one] at hs; exact ⟨hs.1.le, hs.2⟩
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_sliceCLM_le hs')
  simpa [sliceSeries] using this

lemma radius_le_radius_sliceSeries [CompleteSpace F] (p : FormalMultilinearSeries ℝ (P × ℝ) F) :
    p.radius ≤ (sliceSeries p).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr
  exact (sliceSeries p).le_radius_of_bound C fun n =>
    (mul_le_mul_of_nonneg_right (norm_sliceSeries_le p n) (by positivity)).trans (hC n)

lemma sliceSeries_apply [CompleteSpace F] (p : FormalMultilinearSeries ℝ (P × ℝ) F) (n : ℕ)
    (y : P × ℝ) :
    sliceSeries p n (fun _ => y) = ∫ s in (0 : ℝ)..1, p n (fun _ => sliceCLM s y) := by
  have hint : IntervalIntegrable
      (fun s : ℝ => (p n).compContinuousLinearMap (fun _ : Fin n => sliceCLM (P := P) s))
      volume 0 1 := (continuous_compSlice p n).intervalIntegrable _ _
  have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => P × ℝ) F
    (fun _ => y)).intervalIntegral_comp_comm hint
  simpa [sliceSeries] using this.symm

/-- The averaged function has the power series `sliceSeries p`. -/
lemma hasFPowerSeriesOnBall_slice [CompleteSpace F] {H : P × ℝ → F}
    {p : FormalMultilinearSeries ℝ (P × ℝ) F} {z₀ : P × ℝ} {r : ℝ≥0∞}
    (hH : HasFPowerSeriesOnBall H p z₀ r) :
    HasFPowerSeriesOnBall (fun y => ∫ s in (0 : ℝ)..1, H (z₀ + sliceCLM s y))
      (sliceSeries p) 0 r := by
  refine ⟨hH.r_le.trans (radius_le_radius_sliceSeries p), hH.r_pos, fun {y} hy => ?_⟩
  simp only [sliceSeries_apply, zero_add]
  have hy' : (‖y‖₊ : ℝ≥0∞) < p.radius := by
    have := mem_eball_zero_iff.1 hy
    exact lt_of_lt_of_le (by simpa [enorm_eq_nnnorm] using this) hH.r_le
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => ‖p n‖ * ‖y‖ ^ n) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · exact ((p n).cont.comp (continuous_pi fun _ =>
      (continuous_sliceCLM.clm_apply continuous_const))).aestronglyMeasurable
  · refine Eventually.of_forall fun s hs => ?_
    have hs' : s ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hs; exact ⟨hs.1.le, hs.2⟩
    refine ((p n).le_opNorm _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
    exact norm_sliceCLM_apply_le hs' y
  · exact Eventually.of_forall fun _ _ => by
      simpa using p.summable_norm_mul_pow hy'
  · exact _root_.intervalIntegrable_const
  · refine Eventually.of_forall fun s hs => ?_
    have hs' : s ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hs; exact ⟨hs.1.le, hs.2⟩
    apply hH.hasSum
    rw [mem_eball_zero_iff] at hy ⊢
    refine lt_of_le_of_lt ?_ hy
    have h := norm_sliceCLM_apply_le hs' y
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe]
    exact_mod_cast h

/-- Local version: integrating a jointly analytic function over a short interval starting at
`w₀` gives a function analytic in the parameter. -/
lemma eventually_analyticAt_integral_local [CompleteSpace F] {H : P × ℝ → F} {x₀ : P} {w₀ : ℝ}
    (hH : AnalyticAt ℝ H (x₀, w₀)) :
    ∀ᶠ v in 𝓝 w₀, AnalyticAt ℝ (fun x => ∫ w in w₀..v, H (x, w)) x₀ := by
  obtain ⟨p, r, hp⟩ := hH
  set K : P × ℝ → F := fun y => ∫ s in (0 : ℝ)..1, H ((x₀, w₀) + sliceCLM s y) with hKdef
  have hK : AnalyticAt ℝ K 0 := (hasFPowerSeriesOnBall_slice hp).analyticAt
  have hev : ∀ᶠ y in 𝓝 (0 : P × ℝ), AnalyticAt ℝ K y := hK.eventually_analyticAt
  have ht : Tendsto (fun v : ℝ => ((0 : P), v - w₀)) (𝓝 w₀) (𝓝 0) := by
    have : Continuous (fun v : ℝ => ((0 : P), v - w₀)) := by fun_prop
    rw [show (0 : P × ℝ) = ((0 : P), w₀ - w₀) by ext <;> simp]
    exact this.tendsto w₀
  filter_upwards [ht.eventually hev] with v hv
  have h1 : AnalyticAt ℝ (fun x : P => (x - x₀, v - w₀)) x₀ :=
    (analyticAt_id.sub analyticAt_const).prod analyticAt_const
  have h2 : AnalyticAt ℝ K ((fun x : P => (x - x₀, v - w₀)) x₀) := by simpa using hv
  have hcomp : AnalyticAt ℝ (fun x : P => (v - w₀) • K (x - x₀, v - w₀)) x₀ :=
    analyticAt_const.smul
      (AnalyticAt.comp (g := K) (f := fun x : P => (x - x₀, v - w₀)) h2 h1)
  refine hcomp.congr (Eventually.of_forall fun x => ?_)
  have : ∀ s : ℝ, (x₀, w₀) + sliceCLM s (x - x₀, v - w₀) = (x, w₀ + (v - w₀) * s) := by
    intro s; rw [sliceCLM_apply]; ext <;> simp; ring
  simp only [hKdef, this]
  rw [intervalIntegral.smul_integral_comp_add_mul (fun w => H (x, w))]
  simp

/-- **Analyticity of parametric integrals.** If `(x, w) ↦ h x w` is jointly real-analytic at
every point of `{x₀} × [α, β]`, then `x ↦ ∫ w in α..β, h x w` is real-analytic at `x₀`. -/
theorem analyticAt_intervalIntegral [CompleteSpace F] {h : P → ℝ → F} {x₀ : P} {α β : ℝ}
    (hh : ∀ w ∈ uIcc α β, AnalyticAt ℝ (fun z : P × ℝ => h z.1 z.2) (x₀, w)) :
    AnalyticAt ℝ (fun x => ∫ w in α..β, h x w) x₀ := by
  set H : P × ℝ → F := fun z => h z.1 z.2 with hHdef
  have hcont : ∀ᶠ x in 𝓝 x₀, ∀ w ∈ uIcc α β, ContinuousAt H (x, w) := by
    refine isCompact_uIcc.eventually_forall_of_forall_eventually fun w hw => ?_
    exact (hh w hw).eventually_analyticAt.mono fun z hz => hz.continuousAt
  have hint : ∀ᶠ x in 𝓝 x₀, ∀ u ∈ uIcc α β, ∀ v ∈ uIcc α β,
      IntervalIntegrable (h x) volume u v := by
    filter_upwards [hcont] with x hx u hu v hv
    refine ContinuousOn.intervalIntegrable fun w hw => ?_
    have hw' : w ∈ uIcc α β := uIcc_subset_uIcc hu hv hw
    have hc : ContinuousAt (fun w' : ℝ => (x, w')) w := by fun_prop
    exact (ContinuousAt.comp (g := H) (hx w hw') hc).continuousWithinAt
  refine isPreconnected_uIcc.induction₂'
    (fun u v => AnalyticAt ℝ (fun x => ∫ w in u..v, h x w) x₀) ?_ ?_ left_mem_uIcc
    right_mem_uIcc
  · intro u hu
    have := eventually_analyticAt_integral_local (hh u hu)
    refine (this.filter_mono nhdsWithin_le_nhds).mono fun v hv => ⟨hv, ?_⟩
    refine hv.neg.congr (Eventually.of_forall fun x => ?_)
    change -(∫ w in u..v, h x w) = ∫ w in v..u, h x w
    rw [intervalIntegral.integral_symm u v]
  · intro u v z hu hv hz huv hvz
    refine (huv.add hvz).congr ?_
    filter_upwards [hint] with x hx
    exact intervalIntegral.integral_add_adjacent_intervals (hx u hu v hv) (hx v hv z hz)

/-! ### Elementary analyticity facts -/

/-- `Real.sqrt` is analytic at positive points. -/
lemma analyticAt_sqrt {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.sqrt x :=
  (Real.contDiffAt_sqrt (n := ω) hx.ne').analyticAt

/-- The flight-time integrand `(E, q) ↦ 1 / √(2 (E - f q))` is jointly analytic wherever `f` is
analytic and `f q < E`. -/
lemma analyticAt_flightIntegrand {f : ℝ → ℝ} {E₀ q₀ : ℝ} (hf : AnalyticAt ℝ f q₀)
    (h : f q₀ < E₀) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => 1 / Real.sqrt (2 * (z.1 - f z.2))) (E₀, q₀) := by
  have hin : AnalyticAt ℝ (fun z : ℝ × ℝ => 2 * (z.1 - f z.2)) (E₀, q₀) :=
    analyticAt_const.mul (analyticAt_fst.sub (AnalyticAt.comp (g := f) hf analyticAt_snd))
  have hpos : 0 < 2 * (E₀ - f q₀) := by linarith
  have hsq : AnalyticAt ℝ (fun z : ℝ × ℝ => Real.sqrt (2 * (z.1 - f z.2))) (E₀, q₀) :=
    AnalyticAt.comp (g := Real.sqrt) (analyticAt_sqrt hpos) hin
  exact analyticAt_const.div hsq (Real.sqrt_pos.2 hpos).ne'

/-- Points `t - l (t - a)`, `l ∈ [0, 1]`, lie on the segment between `a` and `t`. -/
lemma sub_mul_mem_uIcc {a t l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) : t - l * (t - a) ∈ uIcc a t := by
  rcases le_total a t with h | h
  · rw [uIcc_of_le h]; constructor <;> nlinarith [hl.1, hl.2]
  · rw [uIcc_of_ge h]; constructor <;> nlinarith [hl.1, hl.2]

/-- Points `t - θ (t - a) w²`, `θ, w ∈ [0, 1]`, lie on the segment between `a` and `t`. -/
lemma sub_mul_sq_mem_uIcc {a t w θ : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    t - θ * ((t - a) * w ^ 2) ∈ uIcc a t := by
  have : t - θ * ((t - a) * w ^ 2) = t - (θ * w ^ 2) * (t - a) := by ring
  rw [this]
  apply sub_mul_mem_uIcc
  exact ⟨by have := hθ.1; positivity,
    mul_le_one₀ hθ.2 (sq_nonneg w) (pow_le_one₀ hw.1 hw.2)⟩

/-- The image of `(0, 1)` under `w ↦ T - (T - a) w²`, for `a < T`. -/
lemma image_turningSubst_of_lt {a T : ℝ} (h : a < T) :
    (fun w : ℝ => T - (T - a) * w ^ 2) '' Ioo 0 1 = Ioo a T := by
  ext q
  constructor
  · rintro ⟨w, ⟨hw0, hw1⟩, rfl⟩
    have h1 : 0 < w ^ 2 := by positivity
    have h2 : w ^ 2 < 1 := by nlinarith
    constructor <;> nlinarith
  · rintro ⟨hq1, hq2⟩
    have hd : 0 < (T - q) / (T - a) := div_pos (by linarith) (by linarith)
    refine ⟨Real.sqrt ((T - q) / (T - a)), ⟨Real.sqrt_pos.2 hd, ?_⟩, ?_⟩
    · rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]
      linarith
    · simp only
      rw [Real.sq_sqrt hd.le]
      have hne : T - a ≠ 0 := by intro h0; linarith
      field_simp
      ring

/-- The image of `(0, 1)` under `w ↦ T - (T - a) w²`, for `T < a`. -/
lemma image_turningSubst_of_gt {a T : ℝ} (h : T < a) :
    (fun w : ℝ => T - (T - a) * w ^ 2) '' Ioo 0 1 = Ioo T a := by
  ext q
  constructor
  · rintro ⟨w, ⟨hw0, hw1⟩, rfl⟩
    have h1 : 0 < w ^ 2 := by positivity
    have h2 : w ^ 2 < 1 := by nlinarith
    constructor <;> nlinarith
  · rintro ⟨hq1, hq2⟩
    have hd : 0 < (T - q) / (T - a) := div_pos_of_neg_of_neg (by linarith) (by linarith)
    refine ⟨Real.sqrt ((T - q) / (T - a)), ⟨Real.sqrt_pos.2 hd, ?_⟩, ?_⟩
    · rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one_of_neg (by linarith)]
      linarith
    · simp only
      rw [Real.sq_sqrt hd.le]
      have hne : T - a ≠ 0 := by intro h0; linarith
      field_simp
      ring

/-- The substitution `q = T - (T - a) w²`, valid for an arbitrary (possibly non-integrable)
integrand: both sides are Bochner integrals and vanish together if not integrable. -/
lemma integral_turningSubst (k : ℝ → ℝ) {a T : ℝ} (hT : T ≠ a) :
    ∫ q in a..T, k q = ∫ w in (0 : ℝ)..1, 2 * (T - a) * w * k (T - (T - a) * w ^ 2) := by
  set φ : ℝ → ℝ := fun w => T - (T - a) * w ^ 2 with hφdef
  have hφ : ∀ w ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt φ (-(2 * (T - a) * w)) (Ioo 0 1) w := by
    intro w _
    have h := ((hasDerivAt_pow 2 w).const_mul (T - a)).const_sub T
    have : HasDerivAt φ (-(2 * (T - a) * w)) w := h.congr_deriv (by norm_num; ring)
    exact this.hasDerivWithinAt
  have hinj : InjOn φ (Ioo 0 1) := by
    intro w₁ hw₁ w₂ hw₂ he
    have hsub : T - a ≠ 0 := sub_ne_zero.2 hT
    have h2 : w₁ ^ 2 = w₂ ^ 2 := by
      have : (T - a) * w₁ ^ 2 = (T - a) * w₂ ^ 2 := by simp only [φ] at he; linarith
      exact mul_left_cancel₀ hsub this
    exact (pow_left_inj₀ hw₁.1.le hw₂.1.le two_ne_zero).1 h2
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hφ hinj k
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rcases lt_or_gt_of_ne hT with h | h
  · rw [image_turningSubst_of_gt h] at hcv
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le h.le,
      integral_Ioc_eq_integral_Ioo, hcv, ← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
    have : 0 ≤ -(2 * (T - a) * w) := by nlinarith [hw.1]
    simp only [smul_eq_mul, φ, abs_of_nonneg this]
    ring
  · rw [image_turningSubst_of_lt h] at hcv
    rw [intervalIntegral.integral_of_le h.le, integral_Ioc_eq_integral_Ioo, hcv]
    refine setIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
    have : -(2 * (T - a) * w) ≤ 0 := by nlinarith [hw.1]
    simp only [smul_eq_mul, φ, abs_of_nonpos this]
    ring

/-- The absolute value of an analytic function is analytic where the function does not vanish. -/
lemma analyticAt_abs_of_ne_zero {g : ℝ → ℝ} {x : ℝ} (hg : AnalyticAt ℝ g x) (h0 : g x ≠ 0) :
    AnalyticAt ℝ (fun y => |g y|) x := by
  rcases lt_or_gt_of_ne h0 with h | h
  · refine hg.neg.congr ?_
    filter_upwards [hg.continuousAt.eventually_lt continuousAt_const h] with y hy
    simp [abs_of_neg hy]
  · refine hg.congr ?_
    filter_upwards [continuousAt_const.eventually_lt hg.continuousAt h] with y hy
    simp [abs_of_pos hy]

end FlightTimeAnalytic

open FlightTimeAnalytic

/-! ### Crossing flights -/

/-- **Analyticity of a crossing flight time.** If the edge potential `f` is real-analytic on a set
containing `[a, b]` and lies strictly below `E₀` there, the crossing time
`E ↦ ∫ q in a..b, 1 / √(2 (E - f q))` is real-analytic at `E₀`. -/
theorem analyticAt_crossingTime {f : ℝ → ℝ} {U : Set ℝ} {a b E₀ : ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hU : Set.Icc a b ⊆ U) (hab : a ≤ b)
    (hE : ∀ q ∈ Set.Icc a b, f q < E₀) :
    AnalyticAt ℝ (fun E => ∫ q in a..b, 1 / Real.sqrt (2 * (E - f q))) E₀ :=
  analyticAt_intervalIntegral (h := fun E q => 1 / Real.sqrt (2 * (E - f q))) fun q hq => by
    rw [uIcc_of_le hab] at hq
    exact analyticAt_flightIntegrand (hf q (hU hq)) (hE q hq)

/-! ### The turning point -/

/-- **The turning point is analytic in the energy.** If `f` is analytic at `t₀` with
`f t₀ = E₀` and `f' t₀ ≠ 0`, there is a function `τ`, analytic at `E₀`, with `τ E₀ = t₀`,
`f (τ E) = E` for `E` near `E₀`, and `τ (f t) = t` for `t` near `t₀`. -/
theorem exists_analyticAt_turningPoint {f : ℝ → ℝ} {t₀ E₀ : ℝ} (hf : AnalyticAt ℝ f t₀)
    (hft : f t₀ = E₀) (hdf : deriv f t₀ ≠ 0) :
    ∃ τ : ℝ → ℝ, AnalyticAt ℝ τ E₀ ∧ τ E₀ = t₀ ∧ (∀ᶠ E in 𝓝 E₀, f (τ E) = E) ∧
      ∀ᶠ t in 𝓝 t₀, τ (f t) = t := by
  subst hft
  refine ⟨hf.hasStrictDerivAt.localInverse f (deriv f t₀) t₀ hdf,
    hf.analyticAt_localInverse hdf, ?_, hf.hasStrictDerivAt.eventually_right_inverse hdf,
    hf.hasStrictDerivAt.eventually_left_inverse hdf⟩
  exact HasStrictFDerivAt.localInverse_apply_image ..

namespace FlightTimeAnalytic

/-! ### Reflected flights: removing the turning-point singularity -/

/-- The divided difference `D x v = ∫₀¹ f' (x - θ v) dθ`, so that
`f x - f (x - v) = v * D x v`. -/
noncomputable def divDiff (f : ℝ → ℝ) (x v : ℝ) : ℝ := ∫ θ in (0 : ℝ)..1, deriv f (x - θ * v)

/-- At `v = 0` the divided difference is the derivative. -/
lemma divDiff_zero (f : ℝ → ℝ) (x : ℝ) : divDiff f x 0 = deriv f x := by
  simp [divDiff]

/-- The defining identity `f x - f (x - v) = v * D x v` of the divided difference. -/
lemma sub_eq_mul_divDiff {f : ℝ → ℝ} {x v : ℝ}
    (hf : ∀ θ ∈ Icc (0 : ℝ) 1, AnalyticAt ℝ f (x - θ * v)) :
    f x - f (x - v) = v * divDiff f x v := by
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun θ => f (x - θ * v))
      (deriv f (x - θ * v) * (-v)) θ := by
    intro θ hθ
    rw [uIcc_of_le zero_le_one] at hθ
    have h1 : HasDerivAt (fun θ : ℝ => x - θ * v) (-v) θ := by
      simpa using ((hasDerivAt_id θ).mul_const v).const_sub x
    exact (hf θ hθ).differentiableAt.hasDerivAt.comp θ h1
  have hint : IntervalIntegrable (fun θ => deriv f (x - θ * v) * (-v)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable fun θ hθ => ?_
    rw [uIcc_of_le zero_le_one] at hθ
    have hc : ContinuousAt (fun θ : ℝ => x - θ * v) θ := by fun_prop
    exact ((ContinuousAt.comp (g := deriv f) (f := fun θ : ℝ => x - θ * v)
      (hf θ hθ).deriv.continuousAt hc).mul
      continuousAt_const).continuousWithinAt
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_mul_const] at this
  simp only [one_mul, zero_mul, sub_zero] at this
  rw [divDiff]
  linarith

/-- The divided difference is jointly analytic wherever `f` is analytic along the segment. -/
lemma analyticAt_divDiff {f : ℝ → ℝ} {x₀ v₀ : ℝ}
    (hf : ∀ θ ∈ Icc (0 : ℝ) 1, AnalyticAt ℝ f (x₀ - θ * v₀)) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => divDiff f z.1 z.2) (x₀, v₀) := by
  refine analyticAt_intervalIntegral (P := ℝ × ℝ) (h := fun z θ => deriv f (z.1 - θ * z.2))
    fun θ hθ => ?_
  rw [uIcc_of_le zero_le_one] at hθ
  have hin : AnalyticAt ℝ (fun z : (ℝ × ℝ) × ℝ => z.1.1 - z.2 * z.1.2) ((x₀, v₀), θ) :=
    AnalyticAt.sub (AnalyticAt.comp analyticAt_fst analyticAt_fst)
      (AnalyticAt.mul analyticAt_snd (AnalyticAt.comp analyticAt_snd analyticAt_fst))
  exact AnalyticAt.comp (g := deriv f) (hf θ hθ).deriv hin

end FlightTimeAnalytic


namespace FlightTimeAnalytic

/-- The desingularised reflection integral. Under the hypotheses of
`analyticAt_reflectionTime`, the substitution `q = τ E - (τ E - a) w²` turns the reflected
flight integral into `∫ w in 0..1, Hh E w` with `Hh` jointly analytic on `{E₀} × [0, 1]` and
of the strict sign of `t₀ - a` at `E₀`. -/
lemma reflection_desingularize {f τ : ℝ → ℝ} {U : Set ℝ} {a t₀ E₀ : ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hU : Set.uIcc a t₀ ⊆ U) (hft : f t₀ = E₀)
    (hdf : deriv f t₀ ≠ 0) (hfa : f a < E₀)
    (hlt : ∀ q ∈ Set.Ioo (min a t₀) (max a t₀), f q < E₀)
    (hτ : AnalyticAt ℝ τ E₀) (hτ₀ : τ E₀ = t₀) (hfτ : ∀ᶠ E in 𝓝 E₀, f (τ E) = E) :
    ∃ Hh : ℝ → ℝ → ℝ, (∀ w ∈ uIcc (0 : ℝ) 1, AnalyticAt ℝ (fun z : ℝ × ℝ => Hh z.1 z.2) (E₀, w)) ∧
      (∀ w ∈ Icc (0 : ℝ) 1, 0 < (t₀ - a) * Hh E₀ w) ∧
      (fun E => ∫ w in (0 : ℝ)..1, Hh E w) =ᶠ[𝓝 E₀]
        fun E => ∫ q in a..τ E, 1 / Real.sqrt (2 * (E - f q)) := by
  have hat : a ≠ t₀ := by rintro rfl; linarith
  have hlt' : ∀ q ∈ uIcc a t₀, q ≠ t₀ → f q < E₀ := by
    intro q hq hqt
    by_cases hqa : q = a
    · subst hqa; exact hfa
    · apply hlt
      rcases le_total a t₀ with h | h
      · rw [uIcc_of_le h] at hq
        rw [min_eq_left h, max_eq_right h]
        exact ⟨lt_of_le_of_ne hq.1 (Ne.symm hqa), lt_of_le_of_ne hq.2 hqt⟩
      · rw [uIcc_of_ge h] at hq
        rw [min_eq_right h, max_eq_left h]
        exact ⟨lt_of_le_of_ne hq.1 (Ne.symm hqt), lt_of_le_of_ne hq.2 hqa⟩
  have hU' : ∀ q ∈ uIcc a t₀, AnalyticAt ℝ f q := fun q hq => hf q (hU hq)
  -- the divided difference at the turning point
  have hDan : ∀ w ∈ Icc (0 : ℝ) 1,
      AnalyticAt ℝ (fun z : ℝ × ℝ => divDiff f z.1 z.2) (t₀, (t₀ - a) * w ^ 2) :=
    fun w hw => analyticAt_divDiff fun θ hθ => hU' _ (sub_mul_sq_mem_uIcc hw hθ)
  have hidt : ∀ w ∈ Icc (0 : ℝ) 1, E₀ - f (t₀ - (t₀ - a) * w ^ 2) =
      (t₀ - a) * w ^ 2 * divDiff f t₀ ((t₀ - a) * w ^ 2) := by
    intro w hw
    rw [← hft]
    exact sub_eq_mul_divDiff fun θ hθ => hU' _ (sub_mul_sq_mem_uIcc hw hθ)
  have hpos' : ∀ w ∈ Ioc (0 : ℝ) 1, 0 < (t₀ - a) * divDiff f t₀ ((t₀ - a) * w ^ 2) := by
    intro w hw
    have hw' : w ∈ Icc (0 : ℝ) 1 := ⟨hw.1.le, hw.2⟩
    have hq : t₀ - (t₀ - a) * w ^ 2 ∈ uIcc a t₀ := by
      simpa using sub_mul_sq_mem_uIcc (t := t₀) (a := a) hw' ⟨zero_le_one, le_rfl⟩
    have hne : t₀ - (t₀ - a) * w ^ 2 ≠ t₀ := by
      have : (t₀ - a) * w ^ 2 ≠ 0 :=
        mul_ne_zero (sub_ne_zero.2 hat.symm) (pow_ne_zero 2 hw.1.ne')
      intro h; apply this; linarith
    have h1 := hlt' _ hq hne
    have h2 := hidt w hw'
    have hw2 : 0 < w ^ 2 := by have := hw.1; positivity
    have : 0 < w ^ 2 * ((t₀ - a) * divDiff f t₀ ((t₀ - a) * w ^ 2)) := by nlinarith
    exact (mul_pos_iff_of_pos_left hw2).1 this
  have hpos : ∀ w ∈ Icc (0 : ℝ) 1, 0 < (t₀ - a) * divDiff f t₀ ((t₀ - a) * w ^ 2) := by
    intro w hw
    rcases eq_or_lt_of_le hw.1 with h0 | h0
    · subst h0
      have hcont : ContinuousAt
          (fun w : ℝ => (t₀ - a) * divDiff f t₀ ((t₀ - a) * w ^ 2)) 0 := by
        have hc := (hDan 0 ⟨le_rfl, zero_le_one⟩).continuousAt
        have hg : ContinuousAt (fun w : ℝ => (t₀, (t₀ - a) * w ^ 2)) 0 := by fun_prop
        exact continuousAt_const.mul
          (ContinuousAt.comp (g := fun z : ℝ × ℝ => divDiff f z.1 z.2)
            (f := fun w : ℝ => (t₀, (t₀ - a) * w ^ 2)) hc hg)
      have hge : 0 ≤ (t₀ - a) * divDiff f t₀ ((t₀ - a) * 0 ^ 2) := by
        refine ge_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))) ?_
        filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with w hw
        exact (hpos' w ⟨hw.1, hw.2.le⟩).le
      have hne : (t₀ - a) * divDiff f t₀ ((t₀ - a) * 0 ^ 2) ≠ 0 := by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
        rw [divDiff_zero]
        exact mul_ne_zero (sub_ne_zero.2 hat.symm) hdf
      exact lt_of_le_of_ne hge hne.symm
    · exact hpos' w ⟨h0, hw.2⟩
  -- the desingularised integrand
  set Hh : ℝ → ℝ → ℝ := fun E w =>
    2 * (τ E - a) / Real.sqrt (2 * (τ E - a) * divDiff f (τ E) ((τ E - a) * w ^ 2)) with hHh
  refine ⟨Hh, ?_, ?_, ?_⟩
  · intro w hw
    rw [uIcc_of_le zero_le_one] at hw
    have g1 : AnalyticAt ℝ (fun z : ℝ × ℝ => τ z.1) (E₀, w) :=
      AnalyticAt.comp (g := τ) hτ analyticAt_fst
    have g2 : AnalyticAt ℝ (fun z : ℝ × ℝ => (τ z.1, (τ z.1 - a) * z.2 ^ 2)) (E₀, w) :=
      g1.prod ((g1.sub analyticAt_const).mul (analyticAt_snd.pow 2))
    have g3 : AnalyticAt ℝ (fun z : ℝ × ℝ => divDiff f (τ z.1) ((τ z.1 - a) * z.2 ^ 2))
        (E₀, w) := by
      have := hDan w hw
      rw [← hτ₀] at this
      exact AnalyticAt.comp (g := fun z : ℝ × ℝ => divDiff f z.1 z.2)
        (f := fun z : ℝ × ℝ => (τ z.1, (τ z.1 - a) * z.2 ^ 2)) this g2
    have hX : AnalyticAt ℝ
        (fun z : ℝ × ℝ => 2 * (τ z.1 - a) * divDiff f (τ z.1) ((τ z.1 - a) * z.2 ^ 2))
        (E₀, w) :=
      (analyticAt_const.mul (g1.sub analyticAt_const)).mul g3
    have hXpos : 0 < 2 * (τ E₀ - a) * divDiff f (τ E₀) ((τ E₀ - a) * w ^ 2) := by
      rw [hτ₀]; have := hpos w hw; nlinarith
    have hsq := AnalyticAt.comp (g := Real.sqrt)
      (f := fun z : ℝ × ℝ => 2 * (τ z.1 - a) * divDiff f (τ z.1) ((τ z.1 - a) * z.2 ^ 2))
      (analyticAt_sqrt hXpos) hX
    exact (analyticAt_const.mul (g1.sub analyticAt_const)).div hsq
      (Real.sqrt_pos.2 hXpos).ne'
  · intro w hw
    have hXpos : 0 < 2 * (t₀ - a) * divDiff f t₀ ((t₀ - a) * w ^ 2) := by
      have := hpos w hw; nlinarith
    show 0 < (t₀ - a) * (2 * (τ E₀ - a) /
      Real.sqrt (2 * (τ E₀ - a) * divDiff f (τ E₀) ((τ E₀ - a) * w ^ 2)))
    rw [hτ₀, ← mul_div_assoc]
    refine div_pos ?_ (Real.sqrt_pos.2 hXpos)
    have : 0 < (t₀ - a) ^ 2 := by
      have := sub_ne_zero.2 hat.symm; positivity
    nlinarith
  · -- the change of variables, for `E` near `E₀`
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_analyticAt ℝ f) t₀
      (hU' t₀ right_mem_uIcc)
    have hτt : Tendsto τ (𝓝 E₀) (𝓝 t₀) := hτ₀ ▸ hτ.continuousAt.tendsto
    filter_upwards [hτt (Metric.ball_mem_nhds t₀ hε), hτt.eventually_ne hat.symm, hfτ]
      with E hE1 hE2 hE3
    have hseg : ∀ q ∈ uIcc a (τ E), AnalyticAt ℝ f q := by
      intro q hq
      rcases uIcc_subset_uIcc_union_uIcc (b := t₀) hq with h | h
      · exact hU' q h
      · apply hball
        rw [Real.ball_eq_Ioo] at hE1 ⊢
        exact Set.ordConnected_Ioo.uIcc_subset ⟨by linarith, by linarith⟩ hE1 h
    rw [integral_turningSubst _ hE2]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun w hw => ?_)
    rw [uIoc_of_le zero_le_one] at hw
    have hw' : w ∈ Icc (0 : ℝ) 1 := ⟨hw.1.le, hw.2⟩
    set T := τ E with hT
    have hid : E - f (T - (T - a) * w ^ 2) = (T - a) * w ^ 2 * divDiff f T ((T - a) * w ^ 2) := by
      calc E - f (T - (T - a) * w ^ 2) = f T - f (T - (T - a) * w ^ 2) := by rw [hE3]
        _ = _ := sub_eq_mul_divDiff fun θ hθ => hseg _ (sub_mul_sq_mem_uIcc hw' hθ)
    rw [hid]
    have hre : 2 * ((T - a) * w ^ 2 * divDiff f T ((T - a) * w ^ 2)) =
        w ^ 2 * (2 * (T - a) * divDiff f T ((T - a) * w ^ 2)) := by ring
    rw [hre, Real.sqrt_mul (sq_nonneg w), Real.sqrt_sq hw.1.le]
    show 2 * (T - a) / Real.sqrt (2 * (T - a) * divDiff f T ((T - a) * w ^ 2)) =
      2 * (T - a) * w * (1 / (w * Real.sqrt (2 * (T - a) * divDiff f T ((T - a) * w ^ 2))))
    by_cases hs : Real.sqrt (2 * (T - a) * divDiff f T ((T - a) * w ^ 2)) = 0
    · rw [hs]; simp
    · have := hw.1.ne'
      field_simp

end FlightTimeAnalytic

open FlightTimeAnalytic

/-- **Analyticity of a reflected flight time.** Let the edge potential `f` be real-analytic on a
set containing the segment between the end `a` and a simple turning point `t₀` (`f t₀ = E₀`,
`f' t₀ ≠ 0`), with `f < E₀` at `a` and strictly between `a` and `t₀`, and let `τ` be an analytic
branch of the turning point (`τ E₀ = t₀`, `f (τ E) = E` near `E₀`; see
`exists_analyticAt_turningPoint`). Then `E ↦ ∫ q in a..τ E, 1 / √(2 (E - f q))` is
real-analytic at `E₀`. -/
theorem analyticAt_reflectionTime {f τ : ℝ → ℝ} {U : Set ℝ} {a t₀ E₀ : ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hU : Set.uIcc a t₀ ⊆ U) (hft : f t₀ = E₀)
    (hdf : deriv f t₀ ≠ 0) (hfa : f a < E₀)
    (hlt : ∀ q ∈ Set.Ioo (min a t₀) (max a t₀), f q < E₀)
    (hτ : AnalyticAt ℝ τ E₀) (hτ₀ : τ E₀ = t₀) (hfτ : ∀ᶠ E in 𝓝 E₀, f (τ E) = E) :
    AnalyticAt ℝ (fun E => ∫ q in a..τ E, 1 / Real.sqrt (2 * (E - f q))) E₀ := by
  obtain ⟨Hh, hHan, -, hev⟩ :=
    reflection_desingularize hf hU hft hdf hfa hlt hτ hτ₀ hfτ
  exact (analyticAt_intervalIntegral hHan).congr hev

/-- **Analyticity of a reflected flight time, `2 |∫ …|` form.** Under the hypotheses of
`analyticAt_reflectionTime`, the reflected flight time
`E ↦ 2 * |∫ q in a..τ E, 1 / √(2 (E - f q))|` is real-analytic at `E₀`: the integral has the
strict sign of `t₀ - a` near `E₀`. -/
theorem analyticAt_reflectionTime_two_mul_abs {f τ : ℝ → ℝ} {U : Set ℝ} {a t₀ E₀ : ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hU : Set.uIcc a t₀ ⊆ U) (hft : f t₀ = E₀)
    (hdf : deriv f t₀ ≠ 0) (hfa : f a < E₀)
    (hlt : ∀ q ∈ Set.Ioo (min a t₀) (max a t₀), f q < E₀)
    (hτ : AnalyticAt ℝ τ E₀) (hτ₀ : τ E₀ = t₀) (hfτ : ∀ᶠ E in 𝓝 E₀, f (τ E) = E) :
    AnalyticAt ℝ (fun E => 2 * |∫ q in a..τ E, 1 / Real.sqrt (2 * (E - f q))|) E₀ := by
  obtain ⟨Hh, hHan, hsign, hev⟩ :=
    reflection_desingularize hf hU hft hdf hfa hlt hτ hτ₀ hfτ
  have hg := (analyticAt_intervalIntegral hHan).congr hev
  refine analyticAt_const.mul (analyticAt_abs_of_ne_zero hg ?_)
  have h1 := hev.self_of_nhds
  simp only at h1
  rw [← h1]
  have hcont : ContinuousOn (fun w => Hh E₀ w) (uIcc 0 1) := fun w hw =>
    (ContinuousAt.comp (g := fun z : ℝ × ℝ => Hh z.1 z.2) (hHan w hw).continuousAt
      (by fun_prop : ContinuousAt (fun w : ℝ => (E₀, w)) w)).continuousWithinAt
  have hpos : 0 < ∫ w in (0 : ℝ)..1, (t₀ - a) * Hh E₀ w := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hcont.intervalIntegrable).const_mul _) (fun w hw => hsign w ⟨hw.1.le, hw.2.le⟩)
      zero_lt_one
  rw [intervalIntegral.integral_const_mul] at hpos
  intro h0
  rw [h0, mul_zero] at hpos
  exact lt_irrefl _ hpos

end HamiltonianMetricGraphs
