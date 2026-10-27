/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition VIII.7, last sentence: the periods are real-analytic in the energy
-/

import HamiltonianMetricGraphs.ShellTravelTime
import HamiltonianMetricGraphs.Bifurcation
import HamiltonianMetricGraphs.FlightTimeAnalytic

/-!
# Real-analyticity of the periods (Proposition VIII.7)

The last sentence of Proposition VIII.7: *if `V` is edgewise real-analytic, each period `T_c(E)` is
real-analytic on `I`*, `I` being the neighbourhood of a shell-regular energy `E₀` on which the end
permutation is constant (`bifurcation_locallyConstant`).

## Proof

* **The cycle is locally constant** (`germCycle_eventually_eq`): near `E₀` the end step `Π_E`
  agrees with `Π_{E₀}` on the admissible ends (`bifurcation_locallyConstant`), hence so do its
  iterates and the minimal period of every end, so the cycle `germCycle S E η` is the fixed finite
  set `germCycle S E₀ η`, and `T_c(E) = ∑_{ζ ∈ c} t_E(ζ)` with a fixed index set.
* **Each flight time is analytic** (`analyticAt_flightTime`).  At `E₀` the flight of `ζ` either
  crosses its edge or turns at a first interior point `t₀` of the level `E₀`
  (`crossing_or_exists_turning`).
  - *Crossing.*  `V_e < E₀` on the closed edge, so `V_e < E` on the closed edge for `E` near `E₀`,
    the flight still crosses, and `t_E(ζ) = ∫_0^ℓ dq / √(2(E - V_e(q)))`
    (`flightTime_eq_integral_of_crossing`), analytic by `analyticAt_crossingTime`.
  - *Reflection.*  `V_e'(t₀) ≠ 0` by shell-regularity, so the turning point continues as an
    analytic function `τ(E)` with `τ(E₀) = t₀`, `V_e(τ(E)) = E` (`exists_analyticAt_turningPoint`).
    Since `V_e` is strictly monotone near `t₀` and stays below `E` away from `t₀` between the end
    `a` and `t₀` (a compactness argument), `τ(E)` is still the *first* point of the level `E` seen
    from `a` (`eventually_lt_of_turning_right`, `eventually_lt_of_turning_left`).  Hence
    `t_E(ζ) = 2 |∫_a^{τ(E)} dq / √(2(E - V_e(q)))|` for `E` near `E₀`
    (`flightTime_eq_two_mul_integral_of_turning`), analytic by
    `analyticAt_reflectionTime_two_mul_abs`.
* **The period** is then a finite sum of analytic functions (`analyticAt_cyclePeriod`), and an
  analytic function at `E₀` is analytic on a neighbourhood of `E₀`
  (`eventually_analyticAt_cyclePeriod`).
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter
open scoped Topology

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### Strict monotonicity where the derivative does not vanish -/

/-- Near a point where the derivative of a `C²` function is nonzero, a whole neighbourhood lies
in the domain and the derivative keeps its sign there. -/
theorem exists_deriv_sign_near {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hfU : ContDiffOn ℝ 2 f U) {t₀ : ℝ} (ht₀ : t₀ ∈ U) {ε : ℝ} (hε : 0 < ε) (hd : deriv f t₀ ≠ 0) :
    ∃ δ, 0 < δ ∧ δ < ε ∧ Icc (t₀ - δ) (t₀ + δ) ⊆ U ∧
      ∀ x ∈ Icc (t₀ - δ) (t₀ + δ), 0 < deriv f x * deriv f t₀ := by
  have hcont : ContinuousAt (deriv f) t₀ :=
    (hfU.continuousOn_deriv_of_isOpen hU (by norm_num)).continuousAt (hU.mem_nhds ht₀)
  have hsq : 0 < deriv f t₀ * deriv f t₀ := mul_self_pos.mpr hd
  have hev : ∀ᶠ x in 𝓝 t₀, x ∈ U ∧ 0 < deriv f x * deriv f t₀ :=
    Filter.Eventually.and (hU.mem_nhds ht₀)
      ((hcont.mul continuousAt_const).eventually (eventually_gt_nhds hsq))
  obtain ⟨δ₀, hδ₀, hspec⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min δ₀ ε / 2, by positivity, by linarith [min_le_right δ₀ ε], ?_, ?_⟩
  · intro x hx
    refine (hspec ?_).1
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2, min_le_left δ₀ ε, lt_min hδ₀ hε]
  · intro x hx
    refine (hspec ?_).2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2, min_le_left δ₀ ε, lt_min hδ₀ hε]

theorem strictMonoOn_or_strictAntiOn_near {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hfU : ContDiffOn ℝ 2 f U) {t₀ : ℝ} (ht₀ : t₀ ∈ U) {ε : ℝ} (hε : 0 < ε) (hd : deriv f t₀ ≠ 0) :
    ∃ δ, 0 < δ ∧ δ < ε ∧ Icc (t₀ - δ) (t₀ + δ) ⊆ U ∧
      (0 < deriv f t₀ → StrictMonoOn f (Icc (t₀ - δ) (t₀ + δ))) ∧
      (deriv f t₀ < 0 → StrictAntiOn f (Icc (t₀ - δ) (t₀ + δ))) := by
  obtain ⟨δ, hδ, hδε, hsub, hsign⟩ := exists_deriv_sign_near hU hfU ht₀ hε hd
  have hcont : ContinuousOn f (Icc (t₀ - δ) (t₀ + δ)) := hfU.continuousOn.mono hsub
  refine ⟨δ, hδ, hδε, hsub, fun hpos => ?_, fun hneg => ?_⟩
  · refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont (fun x hx => ?_)
    have h := hsign x (interior_subset hx)
    by_contra hle
    nlinarith [not_lt.mp hle]
  · refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont (fun x hx => ?_)
    have h := hsign x (interior_subset hx)
    by_contra hle
    nlinarith [not_lt.mp hle]

/-! ### The first point of the level persists -/

/-- **The first turning point persists, seen from the left.**  Let `t₀` be the first point to the
right of `a` where `f` reaches `E₀`, with `f'(t₀) ≠ 0`, and let `τ` be a continuous branch of the
level, `τ(E₀) = t₀`, `f(τ(E)) = E`.  Then for `E` near `E₀`, `τ(E)` is still the first point to the
right of `a` where `f` reaches `E`. -/
theorem eventually_lt_of_turning_right {f τ : ℝ → ℝ} {U : Set ℝ} {a t₀ E₀ : ℝ}
    (hU : IsOpen U) (hfU : ContDiffOn ℝ 2 f U) (hsub : Icc a t₀ ⊆ U) (hat : a < t₀)
    (hft : f t₀ = E₀) (hd : deriv f t₀ ≠ 0) (hfa : f a < E₀) (hlt : ∀ x ∈ Ioo a t₀, f x < E₀)
    (hτc : ContinuousAt τ E₀) (hτ₀ : τ E₀ = t₀) (hfτ : ∀ᶠ E in 𝓝 E₀, f (τ E) = E) :
    ∀ᶠ E in 𝓝 E₀, a < τ E ∧ τ E < t₀ + (t₀ - a) ∧ ∀ x ∈ Ioo a (τ E), f x < E := by
  have ht₀U : t₀ ∈ U := hsub ⟨hat.le, le_rfl⟩
  obtain ⟨δ, hδ, hδε, -, hmono, hanti⟩ :=
    strictMonoOn_or_strictAntiOn_near hU hfU ht₀U (by linarith : 0 < t₀ - a) hd
  have hpos : 0 < deriv f t₀ := by
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · exfalso
      have h1 := hanti hneg ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
        (by linarith : t₀ - δ / 2 < t₀)
      have h2 := hlt (t₀ - δ / 2) ⟨by linarith, by linarith⟩
      linarith
    · exact hpos
  have hm := hmono hpos
  set c := t₀ - δ with hc
  have hac : a < c := by rw [hc]; linarith
  obtain ⟨m, hmem, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hac.le)
    (hfU.continuousOn.mono ((Icc_subset_Icc le_rfl (by linarith)).trans hsub))
  have hM : f m < E₀ := by
    rcases eq_or_lt_of_le hmem.1 with h | h
    · rw [← h]; exact hfa
    · exact hlt m ⟨h, by linarith [hmem.2]⟩
  have hτmem : ∀ᶠ E in 𝓝 E₀, τ E ∈ Ioo c (t₀ + δ) :=
    hτc.preimage_mem_nhds (by rw [hτ₀]; exact Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [Ioi_mem_nhds hM, hτmem, hfτ] with E hEM hτE hfτE
  refine ⟨by linarith [hτE.1], by linarith [hτE.2], fun x hx => ?_⟩
  by_cases hxc : x ≤ c
  · exact lt_of_le_of_lt (hmax ⟨hx.1.le, hxc⟩) hEM
  · rw [not_le] at hxc
    have := hm ⟨by linarith, by linarith [hx.2, hτE.2]⟩ ⟨by linarith [hτE.1], hτE.2.le⟩ hx.2
    rw [hfτE] at this
    exact this

/-- **The first turning point persists, seen from the right.** -/
theorem eventually_lt_of_turning_left {f τ : ℝ → ℝ} {U : Set ℝ} {a t₀ E₀ : ℝ}
    (hU : IsOpen U) (hfU : ContDiffOn ℝ 2 f U) (hsub : Icc t₀ a ⊆ U) (hta : t₀ < a)
    (hft : f t₀ = E₀) (hd : deriv f t₀ ≠ 0) (hfa : f a < E₀) (hlt : ∀ x ∈ Ioo t₀ a, f x < E₀)
    (hτc : ContinuousAt τ E₀) (hτ₀ : τ E₀ = t₀) (hfτ : ∀ᶠ E in 𝓝 E₀, f (τ E) = E) :
    ∀ᶠ E in 𝓝 E₀, τ E < a ∧ t₀ - (a - t₀) < τ E ∧ ∀ x ∈ Ioo (τ E) a, f x < E := by
  have ht₀U : t₀ ∈ U := hsub ⟨le_rfl, hta.le⟩
  obtain ⟨δ, hδ, hδε, -, hmono, hanti⟩ :=
    strictMonoOn_or_strictAntiOn_near hU hfU ht₀U (by linarith : 0 < a - t₀) hd
  have hneg : deriv f t₀ < 0 := by
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · exact hneg
    · exfalso
      have h1 := hmono hpos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
        (by linarith : t₀ < t₀ + δ / 2)
      have h2 := hlt (t₀ + δ / 2) ⟨by linarith, by linarith⟩
      linarith
  have hm := hanti hneg
  set c := t₀ + δ with hc
  have hca : c < a := by rw [hc]; linarith
  obtain ⟨m, hmem, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hca.le)
    (hfU.continuousOn.mono ((Icc_subset_Icc (by linarith) le_rfl).trans hsub))
  have hM : f m < E₀ := by
    rcases eq_or_lt_of_le hmem.2 with h | h
    · rw [h]; exact hfa
    · exact hlt m ⟨by linarith [hmem.1], h⟩
  have hτmem : ∀ᶠ E in 𝓝 E₀, τ E ∈ Ioo (t₀ - δ) c :=
    hτc.preimage_mem_nhds (by rw [hτ₀]; exact Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [Ioi_mem_nhds hM, hτmem, hfτ] with E hEM hτE hfτE
  refine ⟨by linarith [hτE.2], by linarith [hτE.1], fun x hx => ?_⟩
  by_cases hxc : c ≤ x
  · exact lt_of_le_of_lt (hmax ⟨hxc, hx.2.le⟩) hEM
  · rw [not_le] at hxc
    have := hm ⟨hτE.1.le, by linarith [hτE.2]⟩ ⟨by linarith [hx.1, hτE.1], by linarith⟩ hx.1
    rw [hfτE] at this
    exact this

/-! ### Analyticity of a flight time -/

/-- If the potential is below the level on the open edge, it is below the level on the closed
edge: the end values are vertex values, which are not the level. -/
theorem extension_lt_of_forall_Ioo {e : Γ.Edge} {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hcross : ∀ x ∈ Ioo (0 : ℝ) (Γ.length e), V.extension e x < E) :
    ∀ q ∈ Icc (0 : ℝ) (Γ.length e), V.extension e q < E := by
  intro q hq
  by_cases hint : q ∈ Ioo (0 : ℝ) (Γ.length e)
  · exact hcross q hint
  have hend : ∃ b : Bool, q = FiniteMetricGraph.EdgeEnd.coordinate Γ (e, b) := by
    rcases eq_or_lt_of_le hq.1 with h | h
    · exact ⟨false, h.symm⟩
    rcases eq_or_lt_of_le hq.2 with h' | h'
    · exact ⟨true, h'⟩
    · exact absurd ⟨h, h'⟩ hint
  obtain ⟨b, hb⟩ := hend
  have hne : V.extension e q ≠ E := by
    intro h
    apply hE
    rw [V.mem_exceptionalEnergies_iff]
    exact ⟨FiniteMetricGraph.EdgeEnd.vertex Γ (e, b), by rw [← V.endpoint_value (e, b), ← hb, h]⟩
  refine lt_of_le_of_ne (not_lt.mp fun hgt => ?_) hne
  have hcont := V.extension_continuousAt_of_mem (V.closedEdge_subset_domain e hq)
  obtain ⟨δ, hδ, hspec⟩ :=
    Metric.eventually_nhds_iff.mp (hcont.eventually (eventually_gt_nhds hgt))
  have hl := Γ.length_pos e
  have hxint : ∃ x ∈ Ioo (0 : ℝ) (Γ.length e), dist x q < δ := by
    cases b
    · simp only [FiniteMetricGraph.edgeEnd_coordinate_false] at hb
      refine ⟨min (Γ.length e / 2) (δ / 2), ⟨lt_min (by linarith) (by linarith),
        by linarith [min_le_left (Γ.length e / 2) (δ / 2)]⟩, ?_⟩
      rw [hb, Real.dist_eq, sub_zero, abs_of_pos (lt_min (by linarith) (by linarith))]
      linarith [min_le_right (Γ.length e / 2) (δ / 2)]
    · simp only [FiniteMetricGraph.edgeEnd_coordinate_true] at hb
      have hlt' : max (Γ.length e / 2) (Γ.length e - δ / 2) < Γ.length e :=
        max_lt (by linarith) (by linarith)
      refine ⟨max (Γ.length e / 2) (Γ.length e - δ / 2),
        ⟨by linarith [le_max_left (Γ.length e / 2) (Γ.length e - δ / 2)], hlt'⟩, ?_⟩
      rw [hb, Real.dist_eq, abs_of_neg (by linarith)]
      linarith [le_max_right (Γ.length e / 2) (Γ.length e - δ / 2)]
  obtain ⟨x, hx, hxq⟩ := hxint
  linarith [hspec hxq, hcross x hx]

/-- **A flight time is real-analytic in the energy.**  If the potential is edgewise real-analytic
and `E₀` is shell-regular, the flight time `E ↦ t_E(η)` of an end admissible at `E₀` is
real-analytic at `E₀`. -/
theorem analyticAt_flightTime (hA : ∀ e, AnalyticOnNhd ℝ (V.extension e) (V.domain e))
    {E₀ : ℝ} (hE₀ : V.ShellRegular E₀) {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E₀) :
    AnalyticAt ℝ (fun E => V.flightTime E η) E₀ := by
  set e := η.1 with he
  set a := FiniteMetricGraph.EdgeEnd.coordinate Γ η with ha
  have hVa : V.extension e a < E₀ := by rw [he, ha, V.endpoint_value η]; exact hη
  have hamem : a ∈ Icc (0 : ℝ) (Γ.length e) := by
    rcases edgeEnd_coordinate_mem η with h | h <;> rw [ha, h]
    · exact ⟨le_rfl, (Γ.length_pos _).le⟩
    · exact ⟨(Γ.length_pos _).le, le_rfl⟩
  -- near `E₀`: shell-regular and `η` admissible
  have hnear : ∀ᶠ E in 𝓝 E₀, ∃ hE : V.ShellRegular E, η ∈ V.allowedGerms E := by
    filter_upwards [V.eventually_shellRegular_bifurcationWindow hE₀] with E ⟨hw, hE⟩
    exact ⟨hE, by rw [hw.allowedGerms_eq]; exact hη⟩
  rcases V.crossing_or_exists_turning (edgeEnd_coordinate_mem η) hVa with
    hcross | ⟨t₀, ht₀, hVt₀, hlt⟩
  · -- the crossing flight
    have hclosed := V.extension_lt_of_forall_Ioo hE₀.not_exceptional hcross
    obtain ⟨m, hmem, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr (Γ.length_pos e).le) (V.extension_continuousOn_closedEdge e)
    have hM := hclosed m hmem
    have han := analyticAt_crossingTime (hA e) (V.closedEdge_subset_domain e)
      (Γ.length_pos e).le hclosed
    refine han.congr ?_
    filter_upwards [hnear, Ioi_mem_nhds hM] with E ⟨hE, hηE⟩ hEM
    have hcrossE : ∀ x ∈ Ioo (0 : ℝ) (Γ.length η.1), V.extension η.1 x < E :=
      fun x hx => lt_of_le_of_lt (hmax (Ioo_subset_Icc_self hx)) hEM
    exact (V.flightTime_eq_integral_of_crossing hE hηE hcrossE).1.symm
  · -- the reflected flight
    have ht₀dom : t₀ ∈ V.domain e := V.closedEdge_subset_domain e (Ioo_subset_Icc_self ht₀)
    have hd := V.deriv_extension_ne_zero_of_shellRegular hE₀ ht₀ hVt₀
    obtain ⟨τ, hτ, hτ₀, hfτ, -⟩ := exists_analyticAt_turningPoint (hA e t₀ ht₀dom) hVt₀ hd
    have hsubU : uIcc a t₀ ⊆ V.domain e :=
      (uIcc_subset_Icc hamem (Ioo_subset_Icc_self ht₀)).trans (V.closedEdge_subset_domain e)
    have han := analyticAt_reflectionTime_two_mul_abs (hA e) hsubU hVt₀ hd hVa hlt hτ hτ₀ hfτ
    refine han.congr ?_
    -- the turning point of the level `E` is `τ E`
    have hpersist : ∀ᶠ E in 𝓝 E₀, τ E ∈ Ioo (0 : ℝ) (Γ.length e) ∧
        ∀ x ∈ uIoo a (τ E), V.extension e x < E := by
      rcases edgeEnd_coordinate_mem η with h0 | h0
      · have hat : a < t₀ := by rw [ha, h0]; exact ht₀.1
        rw [uIoo_of_lt hat] at hlt
        have hsub : Icc a t₀ ⊆ V.domain e := by rw [← uIcc_of_le hat.le]; exact hsubU
        filter_upwards [eventually_lt_of_turning_right (V.domain_isOpen e)
          (V.contDiffOn_extension e)
          hsub hat hVt₀ hd hVa hlt hτ.continuousAt hτ₀ hfτ,
          hτ.continuousAt.preimage_mem_nhds (by rw [hτ₀]; exact Ioo_mem_nhds ht₀.1 ht₀.2)]
          with E ⟨haτ, _, hbelow⟩ hτE
        refine ⟨hτE, ?_⟩
        rw [uIoo_of_lt haτ]
        exact hbelow
      · have hta : t₀ < a := by rw [ha, h0]; exact ht₀.2
        rw [uIoo_of_gt hta] at hlt
        have hsub : Icc t₀ a ⊆ V.domain e := by rw [← uIcc_of_ge hta.le]; exact hsubU
        filter_upwards [eventually_lt_of_turning_left (V.domain_isOpen e)
          (V.contDiffOn_extension e)
          hsub hta hVt₀ hd hVa hlt hτ.continuousAt hτ₀ hfτ,
          hτ.continuousAt.preimage_mem_nhds (by rw [hτ₀]; exact Ioo_mem_nhds ht₀.1 ht₀.2)]
          with E ⟨hτa, _, hbelow⟩ hτE
        refine ⟨hτE, ?_⟩
        rw [uIoo_of_gt hτa]
        exact hbelow
    filter_upwards [hnear, hpersist, hfτ] with E ⟨hE, hηE⟩ ⟨hτE, hbelow⟩ hfτE
    exact (V.flightTime_eq_two_mul_integral_of_turning hE hηE hτE hfτE hbelow).1.symm

/-! ### Analyticity of the periods -/

section Periods

variable (S : BorelEnergyPreservingScattering V)

/-- **The cycle is locally constant.**  Under the hypotheses of `bifurcation_locallyConstant`, the
cycle of `Π_E` through an end admissible at `E₀` is, for `E` near `E₀`, the cycle of `Π_{E₀}`. -/
theorem germCycle_eventually_eq {E₀ : ℝ} (hE₀ : V.ShellRegular E₀)
    (hF : ∀ (v : Γ.Vertex) (r₀ : FiniteMetricGraph.PositiveSpeed),
      r₀.1 = Real.sqrt (2 * (E₀ - V.vertexValue v)) →
      ∀ᶠ r in 𝓝 r₀,
        EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r =
          EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r₀)
    {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E₀) :
    ∀ᶠ E in 𝓝 E₀, V.germCycle S E η = V.germCycle S E₀ η := by
  filter_upwards [V.bifurcation_locallyConstant S hE₀ hF] with E ⟨hE, hG, hstep⟩
  have hηE : η ∈ V.allowedGerms E := by rw [hG]; exact hη
  have hiter : ∀ k : ℕ, (V.germStep S E)^[k] η = (V.germStep S E₀)^[k] η := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
          hstep _ (V.germStep_iterate_mem S hE₀ hη k)]
  have hper : Function.minimalPeriod (V.germStep S E) η =
      Function.minimalPeriod (V.germStep S E₀) η := by
    apply le_antisymm
    · refine Function.IsPeriodicPt.minimalPeriod_le (V.minimalPeriod_germStep_pos S hE₀ hη) ?_
      change (V.germStep S E)^[_] η = η
      rw [hiter]
      exact Function.isPeriodicPt_minimalPeriod _ _
    · refine Function.IsPeriodicPt.minimalPeriod_le (V.minimalPeriod_germStep_pos S hE hηE) ?_
      change (V.germStep S E₀)^[_] η = η
      rw [← hiter]
      exact Function.isPeriodicPt_minimalPeriod _ _
  unfold germCycle
  rw [hper]
  exact Finset.image_congr fun k _ => hiter k

/-- **Proposition VIII.7, last sentence: the periods are real-analytic.**  Let every edge potential
be real-analytic on its domain, let `E₀` be shell-regular, and let the vertex law satisfy the speed
hypothesis of `bifurcation_locallyConstant`.  Then for every end `η` admissible at `E₀`, the period
`E ↦ T_c(E)` of the cycle of `Π_E` through `η` is real-analytic at `E₀`. -/
theorem analyticAt_cyclePeriod (hA : ∀ e, AnalyticOnNhd ℝ (V.extension e) (V.domain e))
    {E₀ : ℝ} (hE₀ : V.ShellRegular E₀)
    (hF : ∀ (v : Γ.Vertex) (r₀ : FiniteMetricGraph.PositiveSpeed),
      r₀.1 = Real.sqrt (2 * (E₀ - V.vertexValue v)) →
      ∀ᶠ r in 𝓝 r₀,
        EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r =
          EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r₀)
    {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E₀) :
    AnalyticAt ℝ (fun E => V.cyclePeriod S E η) E₀ := by
  have hsum : AnalyticAt ℝ (∑ ζ ∈ V.germCycle S E₀ η, fun E => V.flightTime E ζ) E₀ :=
    Finset.analyticAt_sum _ fun ζ hζ =>
      V.analyticAt_flightTime hA hE₀ (V.germCycle_subset S hE₀ hη hζ)
  refine hsum.congr ?_
  filter_upwards [V.germCycle_eventually_eq S hE₀ hF hη] with E hE
  rw [Finset.sum_apply, cyclePeriod, hE]

/-- The periods are real-analytic on a whole neighbourhood of `E₀`. -/
theorem eventually_analyticAt_cyclePeriod (hA : ∀ e, AnalyticOnNhd ℝ (V.extension e) (V.domain e))
    {E₀ : ℝ} (hE₀ : V.ShellRegular E₀)
    (hF : ∀ (v : Γ.Vertex) (r₀ : FiniteMetricGraph.PositiveSpeed),
      r₀.1 = Real.sqrt (2 * (E₀ - V.vertexValue v)) →
      ∀ᶠ r in 𝓝 r₀,
        EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r =
          EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r₀)
    {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E₀) :
    ∀ᶠ E in 𝓝 E₀, AnalyticAt ℝ (fun E => V.cyclePeriod S E η) E :=
  (V.analyticAt_cyclePeriod S hA hE₀ hF hη).eventually_analyticAt

/-- **Proposition VIII.7 in full.**  Under the hypotheses of `bifurcation_locallyConstant` and for
an edgewise real-analytic potential, one neighbourhood `I` of `E₀` carries all the conclusions:
every `E ∈ I` is shell-regular with `G_E = G_{E₀}` and `Π_E = Π_{E₀}`, and every period
`E ↦ T_c(E)` is real-analytic at every point of `I`. -/
theorem bifurcation_locallyConstant_analytic
    (hA : ∀ e, AnalyticOnNhd ℝ (V.extension e) (V.domain e))
    {E₀ : ℝ} (hE₀ : V.ShellRegular E₀)
    (hF : ∀ (v : Γ.Vertex) (r₀ : FiniteMetricGraph.PositiveSpeed),
      r₀.1 = Real.sqrt (2 * (E₀ - V.vertexValue v)) →
      ∀ᶠ r in 𝓝 r₀,
        EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r =
          EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r₀) :
    ∀ᶠ E in 𝓝 E₀, (V.ShellRegular E ∧ V.allowedGerms E = V.allowedGerms E₀ ∧
      ∀ η ∈ V.allowedGerms E₀, V.germStep S E η = V.germStep S E₀ η) ∧
      ∀ η ∈ V.allowedGerms E₀, AnalyticAt ℝ (fun E => V.cyclePeriod S E η) E := by
  have hT : ∀ᶠ E in 𝓝 E₀, ∀ η : Γ.EdgeEnd, η ∈ V.allowedGerms E₀ →
      AnalyticAt ℝ (fun E => V.cyclePeriod S E η) E := by
    refine Filter.eventually_all.2 fun η => ?_
    by_cases hη : η ∈ V.allowedGerms E₀
    · exact (V.eventually_analyticAt_cyclePeriod S hA hE₀ hF hη).mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => absurd h hη
  filter_upwards [V.bifurcation_locallyConstant S hE₀ hF, hT] with E h1 h2
  exact ⟨h1, h2⟩

end Periods

end MechanicalPotential

end HamiltonianMetricGraphs
