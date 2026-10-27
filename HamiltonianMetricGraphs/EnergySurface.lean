/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition VII.1: the invariant time measure of a regular energy surface
-/

import HamiltonianMetricGraphs.EnergyTime

/-!
# The invariant time measure on an energy surface (Proposition VII.1)

On the energy level `E` of an edge the paper's invariant measure is

`dμ_E = dq / |p| = dq / √(2(E - V_e(q)))`,

one copy for each sign of the momentum.  This module proves the two statements about it that
Proposition VII.1 asserts.

* **Invariance.**  `lintegral_timeDensity_Ioo` identifies the `μ_E`-mass of a position interval
  with the increment of the travel-time coordinate `u(q) = ∫ dq/p` of `EnergyTime.lean`, and
  `lintegral_timeDensity_flow` turns this into the invariance statement in its sharpest form: the
  mass of the arc swept by the flow between the times `w₁ ≤ w₂` is exactly `w₂ - w₁`.  In the time
  coordinate the flow is a translation and `μ_E` is Lebesgue measure, which is what invariance
  means.

* **Finiteness.**  `exists_lintegral_timeDensity_lt_top_of_turningPoint` is the estimate at a
  *simple* turning point: if `V_e(q₀) = E` and `V_e'(q₀) ≠ 0`, then `E - V_e` grows at least
  linearly away from `q₀`, so the density is dominated by `|q - q₀|^{-1/2}`, which is integrable.
  `lintegral_timeDensity_edge_lt_top` assembles this with a compactness argument: on a closed edge
  whose turning points are all simple, `μ_E` is a finite measure.  The three local regimes are the
  classically allowed region (bounded density), the turning points (the estimate above) and the
  classically forbidden region (vanishing density).
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory intervalIntegral
open scoped Topology ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The invariant density -/

/-- The **invariant density** of Proposition VII.1 on the energy level `E` of the edge `e`:
`1/√(2(E - V_e(q)))`, the reciprocal speed.  Outside the classically allowed region the speed
vanishes, so with the convention `1/0 = 0` the density is zero there. -/
noncomputable def timeDensity (e : Γ.Edge) (E q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / V.speedAt e E q)

theorem timeDensity_eq_zero_of_le (e : Γ.Edge) {E q : ℝ} (h : E ≤ V.extension e q) :
    V.timeDensity e E q = 0 := by
  have hs : V.speedAt e E q = 0 := by
    unfold speedAt
    exact Real.sqrt_eq_zero_of_nonpos (by linarith)
  rw [timeDensity, hs, div_zero, ENNReal.ofReal_zero]

/-- The **time measure** of the energy level `E` on the edge `e`: the invariant measure of
Proposition VII.1 on one momentum sheet. -/
noncomputable def edgeTimeMeasure (e : Γ.Edge) (E : ℝ) : Measure ℝ :=
  (volume.restrict (Icc (0 : ℝ) (Γ.length e))).withDensity (V.timeDensity e E)

/-! ### Invariance: the time measure is the Lebesgue measure of the travel time -/

/-- The `μ_E`-mass of a position interval inside the classically allowed region is the increment
of the travel-time coordinate. -/
theorem lintegral_timeDensity_Ioo (e : Γ.Edge) {E q₀ : ℝ} {α β : ℝ} (hq₀ : q₀ ∈ Ioo α β)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hpos : ∀ x ∈ Ioo α β, V.extension e x < E)
    {a b : ℝ} (ha : a ∈ Ioo α β) (hb : b ∈ Ioo α β) (hab : a ≤ b) :
    ∫⁻ q in Ioo a b, V.timeDensity e E q =
      ENNReal.ofReal (V.timeAt e E q₀ b - V.timeAt e E q₀ a) := by
  have hsub : Ioo a b ⊆ Ioo α β := fun x hx => ⟨lt_trans ha.1 hx.1, lt_trans hx.2 hb.2⟩
  have hIcc : Icc a b ⊆ Ioo α β := fun x hx =>
    ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  have h := V.lintegral_position_eq_time e hq₀ hdom hpos hsub (fun _ => 1)
  simp only [mul_one] at h
  have hcont : ContinuousOn (fun x => V.timeAt e E q₀ x) (Icc a b) := fun x hx =>
    ((V.hasDerivAt_timeAt e (hIcc hx) hq₀ hdom hpos).continuousAt).continuousWithinAt
  have hmono : StrictMonoOn (fun x => V.timeAt e E q₀ x) (Icc a b) :=
    (V.strictMonoOn_timeAt e hq₀ hdom hpos).mono hIcc
  have himg : (fun x => V.timeAt e E q₀ x) '' Ioo a b =
      Ioo (V.timeAt e E q₀ a) (V.timeAt e E q₀ b) :=
    image_Ioo_of_strictMonoOn hab hcont hmono
  calc ∫⁻ q in Ioo a b, V.timeDensity e E q
      = ∫⁻ q in Ioo a b, ENNReal.ofReal (1 / V.speedAt e E q) := rfl
    _ = ∫⁻ u in (fun x => V.timeAt e E q₀ x) '' Ioo a b, (1 : ℝ≥0∞) := h.symm
    _ = volume ((fun x => V.timeAt e E q₀ x) '' Ioo a b) := by rw [setLIntegral_one]
    _ = ENNReal.ofReal (V.timeAt e E q₀ b - V.timeAt e E q₀ a) := by
        rw [himg, Real.volume_Ioo]

/-- **Proposition VII.1 (invariance).**  The `μ_E`-mass of the position arc swept by an energy-`E`
flight between the times `w₁ ≤ w₂` is exactly the elapsed time `w₂ - w₁`.

Equivalently: in the travel-time coordinate the flow is a translation and `μ_E` is Lebesgue
measure, so `μ_E` is invariant under the flow. -/
theorem lintegral_timeDensity_flow (e : Γ.Edge) {E D : ℝ} (hD : 0 < D) {γ : ℝ → ℝ × ℝ}
    {α β q₀ : ℝ}
    (hderiv : ∀ w ∈ Icc (0 : ℝ) D, HasDerivWithinAt γ (V.edgeVectorField e (γ w)) (Icc 0 D) w)
    (henergy : ∀ w ∈ Icc (0 : ℝ) D, V.hamiltonian e (γ w).1 (γ w).2 = E)
    (hmem : ∀ w ∈ Icc (0 : ℝ) D, (γ w).1 ∈ Ioo α β)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hpos : ∀ x ∈ Ioo α β, V.extension e x < E)
    (hmom : ∀ w ∈ Icc (0 : ℝ) D, 0 < (γ w).2) (hq₀ : q₀ ∈ Ioo α β)
    {w₁ w₂ : ℝ} (hw₁ : w₁ ∈ Icc (0 : ℝ) D) (hw₂ : w₂ ∈ Icc (0 : ℝ) D) (hw : w₁ ≤ w₂) :
    ∫⁻ q in Ioo (γ w₁).1 (γ w₂).1, V.timeDensity e E q = ENNReal.ofReal (w₂ - w₁) := by
  have hflow := V.timeAt_flow_add e hD hderiv henergy hmem hdom hpos hmom hq₀
  have h1 := hflow w₁ hw₁
  have h2 := hflow w₂ hw₂
  have hmono := V.strictMonoOn_timeAt e hq₀ hdom hpos
  have hle : (γ w₁).1 ≤ (γ w₂).1 := by
    rw [← hmono.le_iff_le (hmem w₁ hw₁) (hmem w₂ hw₂)]
    change V.timeAt e E q₀ (γ w₁).1 ≤ V.timeAt e E q₀ (γ w₂).1
    rw [h1, h2]
    linarith
  rw [V.lintegral_timeDensity_Ioo e hq₀ hdom hpos (hmem w₁ hw₁) (hmem w₂ hw₂) hle, h1, h2]
  congr 1
  ring

/-! ### The comparison density `|q - q₀|^{-1/2}` -/

/-- `1/√x` is the real power `x ^ (-1/2)`: both vanish for `x ≤ 0`. -/
theorem one_div_sqrt_eq_rpow (x : ℝ) : 1 / Real.sqrt x = x ^ (-(1 : ℝ) / 2) := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sqrt_eq_zero_of_nonpos h.le, div_zero, Real.rpow_def_of_neg h]
    have hcos : Real.cos (-(1 : ℝ) / 2 * Real.pi) = 0 := by
      rw [show (-(1 : ℝ) / 2 * Real.pi) = -(Real.pi / 2) by ring, Real.cos_neg,
        Real.cos_pi_div_two]
    rw [hcos, mul_zero]
  · simp [h]
  · rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg h.le]
    norm_num

/-- `1/√x` is interval integrable across the origin: the exponent `-1/2` is above `-1`. -/
theorem intervalIntegrable_one_div_sqrt (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt x) volume a b := by
  have h := intervalIntegral.intervalIntegrable_rpow' (r := -(1 : ℝ) / 2) (a := a) (b := b)
    (by norm_num)
  have heq : (fun x : ℝ => 1 / Real.sqrt x) = fun x : ℝ => x ^ (-(1 : ℝ) / 2) :=
    funext one_div_sqrt_eq_rpow
  rw [heq]
  exact h

theorem intervalIntegrable_one_div_sqrt_sub (c a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (x - c)) volume a b := by
  have h := (intervalIntegrable_one_div_sqrt (a - c) (b - c)).comp_sub_right c
  simpa using h

theorem intervalIntegrable_one_div_sqrt_sub' (c a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (c - x)) volume a b := by
  have h := (intervalIntegrable_one_div_sqrt (c - a) (c - b)).comp_sub_left c
  simpa using h

/-- The comparison density of a simple turning point. -/
noncomputable def turningComparison (c q₀ q : ℝ) : ℝ :=
  1 / Real.sqrt c * (1 / Real.sqrt (q - q₀) + 1 / Real.sqrt (q₀ - q))

theorem turningComparison_nonneg (c q₀ q : ℝ) : 0 ≤ turningComparison c q₀ q := by
  unfold turningComparison
  have h1 : (0 : ℝ) ≤ 1 / Real.sqrt c := by positivity
  have h2 : (0 : ℝ) ≤ 1 / Real.sqrt (q - q₀) := by positivity
  have h3 : (0 : ℝ) ≤ 1 / Real.sqrt (q₀ - q) := by positivity
  exact mul_nonneg h1 (by linarith)

theorem intervalIntegrable_turningComparison (c q₀ a b : ℝ) :
    IntervalIntegrable (fun q => turningComparison c q₀ q) volume a b := by
  unfold turningComparison
  exact ((intervalIntegrable_one_div_sqrt_sub q₀ a b).add
    (intervalIntegrable_one_div_sqrt_sub' q₀ a b)).const_mul _

theorem lintegral_turningComparison_lt_top (c q₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ q in Ioo (q₀ - δ) (q₀ + δ), ENNReal.ofReal (turningComparison c q₀ q) < ⊤ := by
  have hle : q₀ - δ ≤ q₀ + δ := by linarith
  have hint : IntegrableOn (fun q => turningComparison c q₀ q) (Ioc (q₀ - δ) (q₀ + δ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (intervalIntegrable_turningComparison c q₀ _ _)
  have hfin : ∫⁻ q in Ioc (q₀ - δ) (q₀ + δ),
      ENNReal.ofReal (turningComparison c q₀ q) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun q => turningComparison_nonneg c q₀ q)).mp hint.2
  exact lt_of_le_of_lt (lintegral_mono_set Ioo_subset_Ioc_self) hfin

/-! ### Finiteness at a simple turning point -/

/-- **Finiteness at a simple turning point.**  If the potential meets the energy level
transversally at `q₀`, the invariant density is integrable near `q₀`: the classical travel time to
a simple turning point is finite. -/
theorem exists_lintegral_timeDensity_lt_top_of_turningPoint (e : Γ.Edge) {E q₀ : ℝ}
    (hq₀ : q₀ ∈ V.domain e) (hturn : V.extension e q₀ = E)
    (hsimple : deriv (V.extension e) q₀ ≠ 0) :
    ∃ δ > (0 : ℝ), ∫⁻ q in Ioo (q₀ - δ) (q₀ + δ), V.timeDensity e E q < ⊤ := by
  classical
  set g : ℝ → ℝ := fun x => E - V.extension e x with hgdef
  set m : ℝ := -deriv (V.extension e) q₀ with hmdef
  have hm0 : m ≠ 0 := by rw [hmdef]; simpa using hsimple
  have hgq₀ : g q₀ = 0 := by rw [hgdef]; simp [hturn]
  have hV : HasDerivAt (V.extension e) (deriv (V.extension e) q₀) q₀ :=
    ((V.extension_contDiffAt_of_mem hq₀).differentiableAt (by norm_num)).hasDerivAt
  have hg : HasDerivAt g m q₀ := by
    rw [hgdef, hmdef]
    simpa using hV.const_sub E
  set c : ℝ := |m| / 2 with hcdef
  have hmabs : 0 < |m| := abs_pos.mpr hm0
  have hcpos : 0 < c := by rw [hcdef]; linarith
  -- the slope of `g` at `q₀` is eventually at least `c` in absolute value
  have hslope : Tendsto (slope g q₀) (𝓝[≠] q₀) (𝓝 m) := hasDerivAt_iff_tendsto_slope.mp hg
  have heven : ∀ᶠ q in 𝓝[≠] q₀, c < |slope g q₀ q| :=
    hslope.abs.eventually (eventually_gt_nhds (by rw [hcdef]; linarith))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at heven
  obtain ⟨δ, hδ, hspec⟩ := heven
  -- the density is dominated by the comparison density
  have hbound : ∀ q ∈ Ioo (q₀ - δ) (q₀ + δ),
      V.timeDensity e E q ≤ ENNReal.ofReal (turningComparison (2 * c) q₀ q) := by
    intro q hq
    by_cases hq₀q : q = q₀
    · rw [hq₀q, V.timeDensity_eq_zero_of_le e (by rw [hturn])]
      exact zero_le
    -- the linear lower bound `c * |q - q₀| < |g q|`
    have hdist : dist q q₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> [linarith [hq.1]; linarith [hq.2]]
    have hslopelt : c < |slope g q₀ q| := hspec hdist hq₀q
    have hsub : q - q₀ ≠ 0 := sub_ne_zero.mpr hq₀q
    have hslopeeq : |slope g q₀ q| = |g q| / |q - q₀| := by
      rw [slope_def_field, hgq₀, sub_zero, abs_div]
    have hlin : c * |q - q₀| < |g q| := by
      rw [hslopeeq, lt_div_iff₀ (abs_pos.mpr hsub)] at hslopelt
      linarith
    -- on the allowed side the speed is bounded below by the comparison speed
    by_cases hgpos : 0 < g q
    · have hgabs : |g q| = g q := abs_of_pos hgpos
      have hspeed : Real.sqrt (2 * c * |q - q₀|) ≤ V.speedAt e E q := by
        unfold speedAt
        refine Real.sqrt_le_sqrt ?_
        rw [hgabs] at hlin
        have : 2 * (E - V.extension e q) = 2 * g q := by rw [hgdef]
        rw [this]
        nlinarith
      have hsqpos : 0 < Real.sqrt (2 * c * |q - q₀|) :=
        Real.sqrt_pos.mpr (by positivity)
      have hle1 : 1 / V.speedAt e E q ≤ 1 / Real.sqrt (2 * c * |q - q₀|) :=
        one_div_le_one_div_of_le hsqpos hspeed
      refine le_trans (ENNReal.ofReal_le_ofReal hle1) (ENNReal.ofReal_le_ofReal ?_)
      -- the comparison density is exactly the one-sided branch on each side of `q₀`
      simp only [turningComparison]
      rcases lt_or_gt_of_ne hq₀q with hlt | hgt
      · have h1 : |q - q₀| = q₀ - q := by rw [abs_sub_comm, abs_of_pos (by linarith)]
        have h2 : Real.sqrt (q - q₀) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
        rw [h1, h2, div_zero, zero_add,
          Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * c), div_mul_div_comm, one_mul]
      · have h1 : |q - q₀| = q - q₀ := abs_of_pos (by linarith)
        have h2 : Real.sqrt (q₀ - q) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
        rw [h1, h2, div_zero, add_zero,
          Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * c), div_mul_div_comm, one_mul]
    · rw [V.timeDensity_eq_zero_of_le e (by rw [hgdef] at hgpos; linarith [not_lt.mp hgpos])]
      exact zero_le
  refine ⟨δ, hδ, ?_⟩
  refine lt_of_le_of_lt ?_ (lintegral_turningComparison_lt_top (2 * c) q₀ hδ)
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
  exact hbound q hq

/-! ### Finiteness of the time measure of a closed edge -/

/-- Where the energy exceeds the potential, the invariant density is locally bounded, so its
integral over a small ball is finite. -/
theorem exists_nhds_lintegral_timeDensity_lt_top (e : Γ.Edge) {E q : ℝ} (hq : q ∈ V.domain e)
    (hlt : V.extension e q < E) :
    ∃ U ∈ 𝓝 q, ∫⁻ x in U, V.timeDensity e E x < ⊤ := by
  have hspeed : 0 < V.speedAt e E q := V.speedAt_pos e hlt
  have hcont : ContinuousAt (fun x => 1 / V.speedAt e E x) q :=
    ContinuousAt.div continuousAt_const (V.continuousAt_speedAt e hq) (ne_of_gt hspeed)
  obtain ⟨δ, hδ, hspec⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  refine ⟨Metric.ball q δ, Metric.ball_mem_nhds q hδ, ?_⟩
  have hb : ∀ x ∈ Metric.ball q δ,
      V.timeDensity e E x ≤ ENNReal.ofReal (1 / V.speedAt e E q + 1) := by
    intro x hx
    have h := hspec (Metric.mem_ball.mp hx)
    rw [Real.dist_eq] at h
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp h).2])
  calc ∫⁻ x in Metric.ball q δ, V.timeDensity e E x
      ≤ ∫⁻ _ in Metric.ball q δ, ENNReal.ofReal (1 / V.speedAt e E q + 1) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        exact hb x hx
    _ = ENNReal.ofReal (1 / V.speedAt e E q + 1) * volume (Metric.ball q δ) := by
        rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- Where the potential exceeds the energy, the invariant density vanishes locally. -/
theorem exists_nhds_lintegral_timeDensity_eq_zero (e : Γ.Edge) {E q : ℝ} (hq : q ∈ V.domain e)
    (hgt : E < V.extension e q) :
    ∃ U ∈ 𝓝 q, ∫⁻ x in U, V.timeDensity e E x = 0 := by
  have hcont : ContinuousAt (V.extension e) q := V.extension_continuousAt_of_mem hq
  have h : ∀ᶠ x in 𝓝 q, E < V.extension e x := hcont.eventually (eventually_gt_nhds hgt)
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hspec⟩ := h
  refine ⟨Metric.ball q δ, Metric.ball_mem_nhds q hδ, ?_⟩
  rw [setLIntegral_congr_fun measurableSet_ball
    (fun x hx => V.timeDensity_eq_zero_of_le e (hspec (Metric.mem_ball.mp hx)).le)]
  simp

/-- **Proposition VII.1 (finiteness).**  If every turning point of the energy level `E` on the
closed edge is simple — the potential meets the level transversally — then the invariant time
measure of the edge is finite.  The proof is a compactness argument over the three local regimes:
bounded density in the classically allowed region, the turning-point estimate
`exists_lintegral_timeDensity_lt_top_of_turningPoint`, and vanishing density in the classically
forbidden region. -/
theorem lintegral_timeDensity_edge_lt_top (e : Γ.Edge) {E : ℝ}
    (hsimple : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), V.extension e q = E →
      deriv (V.extension e) q ≠ 0) :
    ∫⁻ q in Icc (0 : ℝ) (Γ.length e), V.timeDensity e E q < ⊤ := by
  classical
  have hlocal : ∀ q : ℝ, ∃ U : Set ℝ, U ∈ 𝓝 q ∧
      (q ∈ Icc (0 : ℝ) (Γ.length e) → ∫⁻ x in U, V.timeDensity e E x < ⊤) := by
    intro q
    by_cases hq : q ∈ Icc (0 : ℝ) (Γ.length e)
    · have hqdom : q ∈ V.domain e := V.closedEdge_subset_domain e hq
      rcases lt_trichotomy (V.extension e q) E with hlt | heq | hgt
      · obtain ⟨U, hUnhds, hUfin⟩ := V.exists_nhds_lintegral_timeDensity_lt_top e hqdom hlt
        exact ⟨U, hUnhds, fun _ => hUfin⟩
      · obtain ⟨δ, hδ, hfin⟩ :=
          V.exists_lintegral_timeDensity_lt_top_of_turningPoint e hqdom heq (hsimple q hq heq)
        exact ⟨Ioo (q - δ) (q + δ), Ioo_mem_nhds (by linarith) (by linarith), fun _ => hfin⟩
      · obtain ⟨U, hUnhds, hUzero⟩ := V.exists_nhds_lintegral_timeDensity_eq_zero e hqdom hgt
        exact ⟨U, hUnhds, fun _ => by rw [hUzero]; exact ENNReal.zero_lt_top⟩
    · exact ⟨univ, univ_mem, fun h => absurd h hq⟩
  choose U hUnhds hUfin using hlocal
  obtain ⟨t, hts, htcover⟩ := isCompact_Icc.elim_nhds_subcover U (fun q _ => hUnhds q)
  have hiUnion : Icc (0 : ℝ) (Γ.length e) ⊆ ⋃ i : (↑t : Set ℝ), U (i : ℝ) := by
    rw [← Set.biUnion_eq_iUnion (↑t : Set ℝ) fun q _ => U q]
    intro x hx
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp (htcover hx)
    exact Set.mem_iUnion₂.mpr ⟨q, Finset.mem_coe.mpr hq, hxq⟩
  refine lt_of_le_of_lt (le_trans (lintegral_mono_set hiUnion)
    (lintegral_iUnion_le (fun i : (↑t : Set ℝ) => U (i : ℝ)) (V.timeDensity e E))) ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr fun i _ => hUfin (i : ℝ) (hts (i : ℝ) (Finset.mem_coe.mp i.2))

end MechanicalPotential

end HamiltonianMetricGraphs
