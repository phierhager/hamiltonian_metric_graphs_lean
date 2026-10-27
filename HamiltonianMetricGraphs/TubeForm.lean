/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.1 in tube coordinates: dq dp = dE du
-/

import HamiltonianMetricGraphs.EnergySurface
import HamiltonianMetricGraphs.NoImpact

/-!
# The Liouville measure of a tube (Lemma VI.1 in tube coordinates)

Lemma VI.1 expresses the edge Liouville measure as `dq dp = dq dE / p` (`lintegral_flux_form`) and
identifies `dq / p` with the Lebesgue measure `du` of the travel-time coordinate
(`lintegral_position_eq_time`).  Chaining the two gives the paper's tube form

`dq dp = dE du`,

whose measure-theoretic content is the disintegration of the Liouville measure of a tube over the
energy, with density the *travel time across the position window*:

`lintegral_tube_form`:
`∫⁻ (tube) g(H(x)) dq dp = ∫⁻_J (u(E,b) - u(E,a)) g(E) dE`.

The only new ingredient beyond Lemma VI.1 is Tonelli's theorem, applied to exchange the position
and energy integrations; the joint measurability needed for it is the joint continuity of the speed
`(q, E) ↦ √(2(E - V_e(q)))` on the extension domain (`continuousAt_speedAt_prod`).

Substituting `dE = r dr` on a boundary section (`lintegral_energy_eq_speed`) turns this into
`lintegral_tube_form_speed`, the form `dq dp = r dr du` in which the impact step of
`TubeMeasure.lean` acts, and whose invariance is Lemma VI.3 at an impact.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### Two auxiliary measurability facts -/

/-- Measurability of an indicator from measurability of the restriction. -/
theorem measurable_indicator_of_restrict {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Zero β] {s : Set α} (hs : MeasurableSet s) {f : α → β}
    (hf : Measurable (s.restrict f)) : Measurable (s.indicator f) := by
  refine measurable_of_measurable_union_cover s sᶜ hs hs.compl (by rw [union_compl_self]) ?_ ?_
  · change Measurable (s.restrict (s.indicator f))
    have heq : s.restrict (s.indicator f) = s.restrict f :=
      funext fun z => Set.indicator_of_mem z.2 f
    rw [heq]
    exact hf
  · change Measurable (sᶜ.restrict (s.indicator f))
    have heq : sᶜ.restrict (s.indicator f) = fun _ => (0 : β) :=
      funext fun z => Set.indicator_of_notMem z.2 f
    rw [heq]
    exact measurable_const

/-- **Joint continuity of the speed** in the position and the energy, at every position inside the
extension domain. -/
theorem continuousAt_speedAt_prod (e : Γ.Edge) {q E : ℝ} (hq : q ∈ V.domain e) :
    ContinuousAt (fun z : ℝ × ℝ => V.speedAt e z.2 z.1) (q, E) := by
  have hV : ContinuousAt (fun z : ℝ × ℝ => V.extension e z.1) (q, E) :=
    (V.extension_continuousAt_of_mem hq).comp continuousAt_fst
  have h1 : ContinuousAt (fun z : ℝ × ℝ => 2 * (z.2 - V.extension e z.1)) (q, E) :=
    (continuousAt_snd.sub hV).const_mul 2
  exact Real.continuous_sqrt.continuousAt.comp h1

/-! ### The tube form -/

/-- **Lemma VI.1 in tube coordinates.**  Let `Ioo α β` be a position window inside the extension
domain of the edge `e`, classically allowed for every energy of the window `J`, and let
`Ioo a b ⊆ Ioo α β`.  Then the Liouville measure of the tube of positive-momentum states with
position in `Ioo a b` and energy in `J` disintegrates over the energy, with density the travel time
across the position window:

`∫⁻ (tube) g(H x) dq dp = ∫⁻_J (u(E, b) - u(E, a)) g(E) dE`.

This is the paper's `dq dp = dE du`.  The momentum bounds `p₁ < p₂` only serve to fix a strip
containing the tube; the hypothesis `hJsub` says that the energy window is inside the energy range
of the strip at every relevant position, so the energy condition already confines the momentum. -/
theorem lintegral_tube_form (e : Γ.Edge) {α β : ℝ} {J : Set ℝ} (hJ : MeasurableSet J)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e)
    (hposE : ∀ E ∈ J, ∀ x ∈ Ioo α β, V.extension e x < E)
    {a b : ℝ} (ha : a ∈ Ioo α β) (hb : b ∈ Ioo α β) (hab : a ≤ b)
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo α β)
    {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂)
    (hJsub : ∀ q ∈ Ioo a b, J ⊆ Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂))
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in (Ioo a b) ×ˢ (Ioo p₁ p₂),
        J.indicator g (V.hamiltonian e x.1 x.2) ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ E in J, ENNReal.ofReal (V.timeAt e E q₀ b - V.timeAt e E q₀ a) * g E := by
  classical
  have hsub : Ioo a b ⊆ Ioo α β := fun x hx => ⟨lt_trans ha.1 hx.1, lt_trans hx.2 hb.2⟩
  -- Step 0: replace the integrand by a globally measurable one
  set f : ℝ × ℝ → ℝ≥0∞ := (Ioo a b ×ˢ (univ : Set ℝ)).indicator
    (fun y : ℝ × ℝ => J.indicator g (V.hamiltonian e y.1 y.2)) with hfdef
  have hsetmeas : MeasurableSet (Ioo a b ×ˢ (univ : Set ℝ)) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have hfmeas : Measurable f := by
    rw [hfdef]
    refine measurable_indicator_of_restrict hsetmeas ?_
    have hcont : ContinuousOn (fun y : ℝ × ℝ => V.hamiltonian e y.1 y.2)
        (Ioo a b ×ˢ (univ : Set ℝ)) := by
      intro y hy
      exact (V.continuousAt_hamiltonian_prod (hdom y.1 (hsub hy.1))).continuousWithinAt
    have hHmeas : Measurable ((Ioo a b ×ˢ (univ : Set ℝ)).restrict
        (fun y : ℝ × ℝ => V.hamiltonian e y.1 y.2)) :=
      (continuousOn_iff_continuous_restrict.mp hcont).measurable
    exact (hg.indicator hJ).comp hHmeas
  have hstep0 : ∫⁻ x in (Ioo a b) ×ˢ (Ioo p₁ p₂),
      J.indicator g (V.hamiltonian e x.1 x.2) ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ x in (Ioo a b) ×ˢ (Ioo p₁ p₂), f x ∂(volume : Measure (ℝ × ℝ)) := by
    refine setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) (fun x hx => ?_)
    rw [hfdef, Set.indicator_of_mem (Set.mem_prod.mpr ⟨hx.1, mem_univ _⟩)]
  -- Step 1: the flux form
  rw [hstep0, V.lintegral_flux_form e hp₁ hp₁₂ f hfmeas]
  -- Step 2: evaluate the inner energy integral
  have hinner : ∀ q ∈ Ioo a b,
      ∫⁻ E in Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂),
          ENNReal.ofReal (1 / V.speedAt e E q) * f (q, V.speedAt e E q)
        = ∫⁻ E in J, ENNReal.ofReal (1 / V.speedAt e E q) * g E := by
    intro q hq
    have hlow : ∀ E ∈ Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂),
        V.extension e q < E := by
      intro E hE
      have h1 : V.energyOfMomentum e q p₁ = p₁ ^ 2 / 2 + V.extension e q := rfl
      have hp : 0 < p₁ ^ 2 / 2 := by positivity
      have := hE.1
      rw [h1] at this
      linarith
    have hrw : ∀ E ∈ Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂),
        ENNReal.ofReal (1 / V.speedAt e E q) * f (q, V.speedAt e E q)
          = J.indicator (fun E' => ENNReal.ofReal (1 / V.speedAt e E' q) * g E') E := by
      intro E hE
      have hH : V.hamiltonian e q (V.speedAt e E q) = E := by
        have h := V.hamiltonian_speedAt e (ε := 1) (by norm_num) (hlow E hE).le
        rwa [one_mul] at h
      have hfval : f (q, V.speedAt e E q) = J.indicator g E := by
        rw [hfdef, Set.indicator_of_mem (Set.mem_prod.mpr ⟨hq, mem_univ _⟩), hH]
      rw [hfval]
      by_cases hEJ : E ∈ J
      · rw [Set.indicator_of_mem hEJ, Set.indicator_of_mem hEJ]
      · rw [Set.indicator_of_notMem hEJ, Set.indicator_of_notMem hEJ, mul_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioo hrw, lintegral_indicator hJ,
      Measure.restrict_restrict hJ, inter_eq_left.mpr (hJsub q hq)]
  rw [setLIntegral_congr_fun measurableSet_Ioo hinner]
  -- Step 3: Tonelli
  set F : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (1 / V.speedAt e z.2 z.1) * g z.2 with hFdef
  have hFae : AEMeasurable F (((volume : Measure ℝ).prod volume).restrict ((Ioo a b) ×ˢ J)) := by
    have hcont : ContinuousOn (fun z : ℝ × ℝ => ENNReal.ofReal (1 / V.speedAt e z.2 z.1))
        ((Ioo a b) ×ˢ J) := by
      intro z hz
      refine ContinuousAt.continuousWithinAt ?_
      have hpos : 0 < V.speedAt e z.2 z.1 :=
        V.speedAt_pos e (hposE z.2 hz.2 z.1 (hsub hz.1))
      have h1 : ContinuousAt (fun w : ℝ × ℝ => 1 / V.speedAt e w.2 w.1) z := by
        have := V.continuousAt_speedAt_prod e (hdom z.1 (hsub hz.1)) (E := z.2)
        exact ContinuousAt.div continuousAt_const (by simpa using this) (ne_of_gt hpos)
      exact ENNReal.continuous_ofReal.continuousAt.comp h1
    exact (hcont.aemeasurable (measurableSet_Ioo.prod hJ)).mul
      ((hg.comp measurable_snd).aemeasurable)
  have hswap : ∫⁻ q in Ioo a b, ∫⁻ E in J, F (q, E)
      = ∫⁻ E in J, ∫⁻ q in Ioo a b, F (q, E) :=
    (setLIntegral_prod F hFae).symm.trans (setLIntegral_prod_symm F hFae)
  have hgoal : ∫⁻ q in Ioo a b, ∫⁻ E in J, ENNReal.ofReal (1 / V.speedAt e E q) * g E
      = ∫⁻ E in J, ∫⁻ q in Ioo a b, ENNReal.ofReal (1 / V.speedAt e E q) * g E := hswap
  rw [hgoal]
  -- Step 4: the inner position integral is the travel time
  refine setLIntegral_congr_fun hJ (fun E hEJ => ?_)
  have hposq : ∀ x ∈ Ioo α β, V.extension e x < E := hposE E hEJ
  have hae : AEMeasurable (fun q => ENNReal.ofReal (1 / V.speedAt e E q))
      (volume.restrict (Ioo a b)) := by
    have hcont : ContinuousOn (fun q => ENNReal.ofReal (1 / V.speedAt e E q)) (Ioo a b) := by
      intro q hq
      refine ContinuousAt.continuousWithinAt ?_
      have hpos : 0 < V.speedAt e E q := V.speedAt_pos e (hposq q (hsub hq))
      exact ENNReal.continuous_ofReal.continuousAt.comp
        (ContinuousAt.div continuousAt_const (V.continuousAt_speedAt e (hdom q (hsub hq)))
          (ne_of_gt hpos))
    exact hcont.aemeasurable measurableSet_Ioo
  rw [lintegral_mul_const'' _ hae]
  have htime : ∫⁻ q in Ioo a b, ENNReal.ofReal (1 / V.speedAt e E q)
      = ENNReal.ofReal (V.timeAt e E q₀ b - V.timeAt e E q₀ a) :=
    V.lintegral_timeDensity_Ioo e hq₀ hdom hposq ha hb hab
  rw [htime]


/-- **The tube form in flux coordinates.**  Substituting `dE = r dr` on a boundary section
(`lintegral_energy_eq_speed`) turns the energy disintegration of `lintegral_tube_form` into the
paper's `dq dp = r dr du`: the Liouville measure of the tube disintegrates over the *boundary
speed* `r` with density `r` times the travel time across the position window.

This is the form in which the impact step of `TubeMeasure.lean` acts: there the boundary flux
measure `counting × r dr` and the Lebesgue measure `du` of the elapsed time are preserved by
scattering and by the reflection `u ↦ Δ - u`, which together is Lemma VI.3 at an impact. -/
theorem lintegral_tube_form_speed (e : Γ.Edge) {α β : ℝ}
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e)
    {r₁ r₂ c : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hposE : ∀ E ∈ Ioo (r₁ ^ 2 / 2 + c) (r₂ ^ 2 / 2 + c), ∀ x ∈ Ioo α β, V.extension e x < E)
    {a b : ℝ} (ha : a ∈ Ioo α β) (hb : b ∈ Ioo α β) (hab : a ≤ b)
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo α β)
    {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂)
    (hJsub : ∀ q ∈ Ioo a b, Ioo (r₁ ^ 2 / 2 + c) (r₂ ^ 2 / 2 + c) ⊆
      Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂))
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in (Ioo a b) ×ˢ (Ioo p₁ p₂),
        (Ioo (r₁ ^ 2 / 2 + c) (r₂ ^ 2 / 2 + c)).indicator g (V.hamiltonian e x.1 x.2)
          ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ r in Ioo r₁ r₂, ENNReal.ofReal r *
          (ENNReal.ofReal (V.timeAt e (r ^ 2 / 2 + c) q₀ b -
              V.timeAt e (r ^ 2 / 2 + c) q₀ a) * g (r ^ 2 / 2 + c)) := by
  rw [V.lintegral_tube_form e measurableSet_Ioo hdom hposE ha hb hab hq₀ hp₁ hp₁₂ hJsub g hg]
  exact lintegral_energy_eq_speed c hr₁ hr₁₂
    (fun E => ENNReal.ofReal (V.timeAt e E q₀ b - V.timeAt e E q₀ a) * g E)

/-! ### The tube chart for an arbitrary integrand -/

/-- **The tube form for an arbitrary integrand, in energy coordinates.**  With the hypotheses of
`lintegral_tube_form`, the Liouville measure of the tube disintegrates over the energy for *every*
measurable integrand, not only for functions of the energy:

`∫⁻_{tube} g dq dp = ∫⁻_J ∫⁻_{Ioo a b} g (q, p(E, q)) dq/p(E,q) dE`.

Taking `g` an indicator, this says that `dq dp` restricted to the tube is the pushforward of
`(1/p) dq dE` under the chart `(q, E) ↦ (q, p(E, q))`, which is the measure form of the paper's
`dq dp = dq dE / p`. -/
theorem lintegral_tube_form_energy (e : Γ.Edge) {α β : ℝ} {J : Set ℝ} (hJ : MeasurableSet J)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e)
    (hposE : ∀ E ∈ J, ∀ x ∈ Ioo α β, V.extension e x < E)
    {a b : ℝ} (ha : a ∈ Ioo α β) (hb : b ∈ Ioo α β)
    {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂)
    (hJsub : ∀ q ∈ Ioo a b, J ⊆ Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂))
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in (Ioo a b) ×ˢ (Ioo p₁ p₂),
        J.indicator (fun _ => (1 : ℝ≥0∞)) (V.hamiltonian e x.1 x.2) * g x
          ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ E in J, ∫⁻ q in Ioo a b,
          ENNReal.ofReal (1 / V.speedAt e E q) * g (q, V.speedAt e E q) := by
  classical
  have hsub : Ioo a b ⊆ Ioo α β := fun x hx => ⟨lt_trans ha.1 hx.1, lt_trans hx.2 hb.2⟩
  -- Step 0: replace the integrand by a globally measurable one
  set f : ℝ × ℝ → ℝ≥0∞ := (Ioo a b ×ˢ (univ : Set ℝ)).indicator
    (fun y : ℝ × ℝ => J.indicator (fun _ => (1 : ℝ≥0∞)) (V.hamiltonian e y.1 y.2) * g y)
    with hfdef
  have hsetmeas : MeasurableSet (Ioo a b ×ˢ (univ : Set ℝ)) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have hfmeas : Measurable f := by
    rw [hfdef]
    refine measurable_indicator_of_restrict hsetmeas ?_
    have hcont : ContinuousOn (fun y : ℝ × ℝ => V.hamiltonian e y.1 y.2)
        (Ioo a b ×ˢ (univ : Set ℝ)) := by
      intro y hy
      exact (V.continuousAt_hamiltonian_prod (hdom y.1 (hsub hy.1))).continuousWithinAt
    have hHmeas : Measurable ((Ioo a b ×ˢ (univ : Set ℝ)).restrict
        (fun y : ℝ × ℝ => V.hamiltonian e y.1 y.2)) :=
      (continuousOn_iff_continuous_restrict.mp hcont).measurable
    exact ((measurable_const.indicator hJ).comp hHmeas).mul (hg.comp measurable_subtype_coe)
  have hstep0 : ∫⁻ x in (Ioo a b) ×ˢ (Ioo p₁ p₂),
      J.indicator (fun _ => (1 : ℝ≥0∞)) (V.hamiltonian e x.1 x.2) * g x
        ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ x in (Ioo a b) ×ˢ (Ioo p₁ p₂), f x ∂(volume : Measure (ℝ × ℝ)) := by
    refine setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) (fun x hx => ?_)
    rw [hfdef, Set.indicator_of_mem (Set.mem_prod.mpr ⟨hx.1, mem_univ _⟩)]
  -- Step 1: the flux form
  rw [hstep0, V.lintegral_flux_form e hp₁ hp₁₂ f hfmeas]
  -- Step 2: evaluate the inner energy integral against the fixed window `J`
  have hinner : ∀ q ∈ Ioo a b,
      ∫⁻ E in Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂),
          ENNReal.ofReal (1 / V.speedAt e E q) * f (q, V.speedAt e E q)
        = ∫⁻ E in J, ENNReal.ofReal (1 / V.speedAt e E q) * g (q, V.speedAt e E q) := by
    intro q hq
    have hlow : ∀ E ∈ Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂),
        V.extension e q < E := by
      intro E hE
      have h1 : V.energyOfMomentum e q p₁ = p₁ ^ 2 / 2 + V.extension e q := rfl
      have hp : 0 < p₁ ^ 2 / 2 := by positivity
      have h2 := hE.1
      rw [h1] at h2
      linarith
    have hrw : ∀ E ∈ Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂),
        ENNReal.ofReal (1 / V.speedAt e E q) * f (q, V.speedAt e E q)
          = J.indicator
              (fun E' => ENNReal.ofReal (1 / V.speedAt e E' q) * g (q, V.speedAt e E' q)) E := by
      intro E hE
      have hH : V.hamiltonian e q (V.speedAt e E q) = E := by
        have h := V.hamiltonian_speedAt e (ε := 1) (by norm_num) (hlow E hE).le
        rwa [one_mul] at h
      have hfval : f (q, V.speedAt e E q) =
          J.indicator (fun _ => (1 : ℝ≥0∞)) E * g (q, V.speedAt e E q) := by
        rw [hfdef, Set.indicator_of_mem (Set.mem_prod.mpr ⟨hq, mem_univ _⟩), hH]
      rw [hfval]
      by_cases hEJ : E ∈ J
      · rw [Set.indicator_of_mem hEJ, Set.indicator_of_mem hEJ, one_mul]
      · rw [Set.indicator_of_notMem hEJ, Set.indicator_of_notMem hEJ, zero_mul, mul_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioo hrw, lintegral_indicator hJ,
      Measure.restrict_restrict hJ, inter_eq_left.mpr (hJsub q hq)]
  rw [setLIntegral_congr_fun measurableSet_Ioo hinner]
  -- Step 3: Tonelli
  set F : ℝ × ℝ → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (1 / V.speedAt e z.2 z.1) * g (z.1, V.speedAt e z.2 z.1) with hFdef
  have hspeed : ContinuousOn (fun z : ℝ × ℝ => (z.1, V.speedAt e z.2 z.1)) ((Ioo a b) ×ˢ J) := by
    intro z hz
    refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_fst.prodMk
      (by simpa using V.continuousAt_speedAt_prod e (hdom z.1 (hsub hz.1)) (E := z.2))
  have hFae : AEMeasurable F (((volume : Measure ℝ).prod volume).restrict ((Ioo a b) ×ˢ J)) := by
    have hcont : ContinuousOn (fun z : ℝ × ℝ => ENNReal.ofReal (1 / V.speedAt e z.2 z.1))
        ((Ioo a b) ×ˢ J) := by
      intro z hz
      refine ContinuousAt.continuousWithinAt ?_
      have hpos : 0 < V.speedAt e z.2 z.1 :=
        V.speedAt_pos e (hposE z.2 hz.2 z.1 (hsub hz.1))
      have h1 : ContinuousAt (fun w : ℝ × ℝ => 1 / V.speedAt e w.2 w.1) z := by
        have := V.continuousAt_speedAt_prod e (hdom z.1 (hsub hz.1)) (E := z.2)
        exact ContinuousAt.div continuousAt_const (by simpa using this) (ne_of_gt hpos)
      exact ENNReal.continuous_ofReal.continuousAt.comp h1
    exact (hcont.aemeasurable (measurableSet_Ioo.prod hJ)).mul
      (hg.comp_aemeasurable (hspeed.aemeasurable (measurableSet_Ioo.prod hJ)))
  exact (setLIntegral_prod F hFae).symm.trans (setLIntegral_prod_symm F hFae)

/-- **The tube chart.**  Chaining `lintegral_tube_form_energy` with the substitution
`dq / p = du` (`lintegral_time_form`) puts the Liouville measure of a tube in the paper's
energy--time coordinates, for an arbitrary measurable integrand:

`∫⁻_{tube} g dq dp = ∫⁻_J ∫⁻_{u(E, (a,b))} g (Θ_E(u)) du dE`,

where `Θ_E(u)` is the state of energy `E` reached at time `u` from the reference position `q₀`.
Taking `g` an indicator, this is the measure identity `dq dp = dE du` of Lemma VI.1, i.e. the flow
box in which the impact step of `TubeMeasure.lean` acts.  Since the flow is a translation in `u`
(`timeAt_flow_add`) and the impact step preserves `(counting × r dr) × du`
(`map_impactStep_flux_prod`), this is the remaining coordinate input to Lemma VI.3. -/
theorem lintegral_tube_chart (e : Γ.Edge) {α β : ℝ} {J : Set ℝ} (hJ : MeasurableSet J)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e)
    (hposE : ∀ E ∈ J, ∀ x ∈ Ioo α β, V.extension e x < E)
    {a b : ℝ} (ha : a ∈ Ioo α β) (hb : b ∈ Ioo α β)
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo α β)
    {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂)
    (hJsub : ∀ q ∈ Ioo a b, J ⊆ Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂))
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in (Ioo a b) ×ˢ (Ioo p₁ p₂),
        J.indicator (fun _ => (1 : ℝ≥0∞)) (V.hamiltonian e x.1 x.2) * g x
          ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ E in J, ∫⁻ u in (fun q => V.timeAt e E q₀ q) '' Ioo a b,
          g (Function.invFunOn (fun q => V.timeAt e E q₀ q) (Ioo a b) u,
            V.speedAt e E
              (Function.invFunOn (fun q => V.timeAt e E q₀ q) (Ioo a b) u)) := by
  have hsub : Ioo a b ⊆ Ioo α β := fun x hx => ⟨lt_trans ha.1 hx.1, lt_trans hx.2 hb.2⟩
  rw [V.lintegral_tube_form_energy e hJ hdom hposE ha hb hp₁ hp₁₂ hJsub g hg]
  refine setLIntegral_congr_fun hJ (fun E hEJ => ?_)
  exact V.lintegral_time_form e hq₀ hdom (hposE E hEJ) hsub
    (fun q => g (q, V.speedAt e E q))

/-- **The tube chart in flux coordinates.**  Substituting `dE = r dr` on a boundary section
(`lintegral_energy_eq_speed`) puts `lintegral_tube_chart` in the paper's flux form
`dq dp = r dr du`, for an arbitrary measurable integrand.  This is exactly the measure
`(r dr) ⊗ du` that the impact step of `TubeMeasure.lean` preserves
(`map_impactStep_flux_prod`, with the germ counting measure supplying the finitely many incident
ends), so on a tube based at a vertex (`q₀ = 0`, `c = V(v)`) the two displays compose. -/
theorem lintegral_tube_chart_speed (e : Γ.Edge) {α β : ℝ}
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e)
    {r₁ r₂ c : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hposE : ∀ E ∈ Ioo (r₁ ^ 2 / 2 + c) (r₂ ^ 2 / 2 + c), ∀ x ∈ Ioo α β, V.extension e x < E)
    {a b : ℝ} (ha : a ∈ Ioo α β) (hb : b ∈ Ioo α β)
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo α β)
    {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂)
    (hJsub : ∀ q ∈ Ioo a b, Ioo (r₁ ^ 2 / 2 + c) (r₂ ^ 2 / 2 + c) ⊆
      Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂))
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in (Ioo a b) ×ˢ (Ioo p₁ p₂),
        (Ioo (r₁ ^ 2 / 2 + c) (r₂ ^ 2 / 2 + c)).indicator (fun _ => (1 : ℝ≥0∞))
          (V.hamiltonian e x.1 x.2) * g x ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ r in Ioo r₁ r₂, ENNReal.ofReal r *
          ∫⁻ u in (fun q => V.timeAt e (r ^ 2 / 2 + c) q₀ q) '' Ioo a b,
            g (Function.invFunOn (fun q => V.timeAt e (r ^ 2 / 2 + c) q₀ q) (Ioo a b) u,
              V.speedAt e (r ^ 2 / 2 + c)
                (Function.invFunOn (fun q => V.timeAt e (r ^ 2 / 2 + c) q₀ q) (Ioo a b) u)) := by
  rw [V.lintegral_tube_chart e measurableSet_Ioo hdom hposE ha hb hq₀ hp₁ hp₁₂ hJsub g hg]
  exact lintegral_energy_eq_speed c hr₁ hr₁₂
    (fun E => ∫⁻ u in (fun q => V.timeAt e E q₀ q) '' Ioo a b,
      g (Function.invFunOn (fun q => V.timeAt e E q₀ q) (Ioo a b) u,
        V.speedAt e E (Function.invFunOn (fun q => V.timeAt e E q₀ q) (Ioo a b) u)))

/-! ### The tube chart for the leftward flights -/

/-- The momentum reflection of the plane is a measurable embedding. -/
theorem measurableEmbedding_momentumReflection :
    MeasurableEmbedding (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)) :=
  MeasurableEmbedding.prodMap (MeasurableEquiv.refl ℝ).measurableEmbedding
    (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding

/-- The momentum reflection preserves the planar Lebesgue measure. -/
theorem measurePreserving_momentumReflection :
    MeasurePreserving (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p))
      (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- **The tube form on a negative momentum strip.**  The Hamiltonian is even in the momentum and the
momentum reflection preserves `dq dp`, so the flux form of `lintegral_tube_form_energy` holds on the
strip `-p₂ < p < -p₁` with the momentum read as `-p(E, q)`.  This is the half of the tube chart that
carries the flights leaving a *right* endpoint of an edge. -/
theorem lintegral_tube_form_energy_neg (e : Γ.Edge) {α β : ℝ} {J : Set ℝ}
    (hJ : MeasurableSet J)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e)
    (hposE : ∀ E ∈ J, ∀ x ∈ Ioo α β, V.extension e x < E)
    {a b : ℝ} (ha : a ∈ Ioo α β) (hb : b ∈ Ioo α β)
    {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂)
    (hJsub : ∀ q ∈ Ioo a b, J ⊆ Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂))
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in (Ioo a b) ×ˢ (Ioo (-p₂) (-p₁)),
        J.indicator (fun _ => (1 : ℝ≥0∞)) (V.hamiltonian e x.1 x.2) * g x
          ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ E in J, ∫⁻ q in Ioo a b,
          ENNReal.ofReal (1 / V.speedAt e E q) * g (q, -V.speedAt e E q) := by
  classical
  have hg' : Measurable (fun y : ℝ × ℝ => g (y.1, -y.2)) :=
    hg.comp (measurable_fst.prodMk measurable_snd.neg)
  have hpre : (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)) ⁻¹'
      ((Ioo a b) ×ˢ (Ioo (-p₂) (-p₁))) = (Ioo a b) ×ˢ (Ioo p₁ p₂) := by
    ext x
    constructor
    · intro hx
      have h1 : x.1 ∈ Ioo a b := hx.1
      have h2 : -x.2 ∈ Ioo (-p₂) (-p₁) := hx.2
      exact ⟨h1, by linarith [h2.2], by linarith [h2.1]⟩
    · intro hx
      have h1 : x.1 ∈ Ioo a b := hx.1
      have h2 : x.2 ∈ Ioo p₁ p₂ := hx.2
      refine ⟨h1, ?_⟩
      change -x.2 ∈ Ioo (-p₂) (-p₁)
      exact ⟨by linarith [h2.2], by linarith [h2.1]⟩
  have hstep := measurePreserving_momentumReflection.setLIntegral_comp_preimage_emb
    measurableEmbedding_momentumReflection
    (fun x : ℝ × ℝ => J.indicator (fun _ => (1 : ℝ≥0∞)) (V.hamiltonian e x.1 x.2) * g x)
    ((Ioo a b) ×ˢ (Ioo (-p₂) (-p₁)))
  rw [hpre] at hstep
  have hfun : (fun x : ℝ × ℝ =>
        J.indicator (fun _ => (1 : ℝ≥0∞))
          (V.hamiltonian e (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) x).1
            (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) x).2) *
          g (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) x))
      = fun x : ℝ × ℝ =>
        J.indicator (fun _ => (1 : ℝ≥0∞)) (V.hamiltonian e x.1 x.2) * g (x.1, -x.2) := by
    funext x
    have hH : V.hamiltonian e x.1 (-x.2) = V.hamiltonian e x.1 x.2 := by
      unfold hamiltonian
      ring_nf
    change J.indicator (fun _ => (1 : ℝ≥0∞)) (V.hamiltonian e x.1 (-x.2)) * g (x.1, -x.2)
      = J.indicator (fun _ => (1 : ℝ≥0∞)) (V.hamiltonian e x.1 x.2) * g (x.1, -x.2)
    rw [hH]
  rw [← hstep, hfun,
    V.lintegral_tube_form_energy e hJ hdom hposE ha hb hp₁ hp₁₂ hJsub
      (fun y : ℝ × ℝ => g (y.1, -y.2)) hg']

/-- **The tube chart for the leftward flights.**  The negative-momentum flux form chained with
`dq / p = du`: the energy--time coordinates of Lemma VI.1 on a tube of leftward flights. -/
theorem lintegral_tube_chart_neg (e : Γ.Edge) {α β : ℝ} {J : Set ℝ} (hJ : MeasurableSet J)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e)
    (hposE : ∀ E ∈ J, ∀ x ∈ Ioo α β, V.extension e x < E)
    {a b : ℝ} (ha : a ∈ Ioo α β) (hb : b ∈ Ioo α β)
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo α β)
    {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂)
    (hJsub : ∀ q ∈ Ioo a b, J ⊆ Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂))
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in (Ioo a b) ×ˢ (Ioo (-p₂) (-p₁)),
        J.indicator (fun _ => (1 : ℝ≥0∞)) (V.hamiltonian e x.1 x.2) * g x
          ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ E in J, ∫⁻ u in (fun q => V.timeAt e E q₀ q) '' Ioo a b,
          g (Function.invFunOn (fun q => V.timeAt e E q₀ q) (Ioo a b) u,
            -V.speedAt e E
              (Function.invFunOn (fun q => V.timeAt e E q₀ q) (Ioo a b) u)) := by
  have hsub : Ioo a b ⊆ Ioo α β := fun x hx => ⟨lt_trans ha.1 hx.1, lt_trans hx.2 hb.2⟩
  rw [V.lintegral_tube_form_energy_neg e hJ hdom hposE ha hb hp₁ hp₁₂ hJsub g hg]
  refine setLIntegral_congr_fun hJ (fun E hEJ => ?_)
  exact V.lintegral_time_form e hq₀ hdom (hposE E hEJ) hsub
    (fun q => g (q, -V.speedAt e E q))

/-- **The tube chart for the leftward flights, in flux coordinates.**  The negative-momentum
counterpart of `lintegral_tube_chart_speed`: `dq dp = r dr du` on a tube of leftward flights. -/
theorem lintegral_tube_chart_speed_neg (e : Γ.Edge) {α β : ℝ}
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e)
    {r₁ r₂ c : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hposE : ∀ E ∈ Ioo (r₁ ^ 2 / 2 + c) (r₂ ^ 2 / 2 + c), ∀ x ∈ Ioo α β, V.extension e x < E)
    {a b : ℝ} (ha : a ∈ Ioo α β) (hb : b ∈ Ioo α β)
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo α β)
    {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂)
    (hJsub : ∀ q ∈ Ioo a b, Ioo (r₁ ^ 2 / 2 + c) (r₂ ^ 2 / 2 + c) ⊆
      Ioo (V.energyOfMomentum e q p₁) (V.energyOfMomentum e q p₂))
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in (Ioo a b) ×ˢ (Ioo (-p₂) (-p₁)),
        (Ioo (r₁ ^ 2 / 2 + c) (r₂ ^ 2 / 2 + c)).indicator (fun _ => (1 : ℝ≥0∞))
          (V.hamiltonian e x.1 x.2) * g x ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ r in Ioo r₁ r₂, ENNReal.ofReal r *
          ∫⁻ u in (fun q => V.timeAt e (r ^ 2 / 2 + c) q₀ q) '' Ioo a b,
            g (Function.invFunOn (fun q => V.timeAt e (r ^ 2 / 2 + c) q₀ q) (Ioo a b) u,
              -V.speedAt e (r ^ 2 / 2 + c)
                (Function.invFunOn (fun q => V.timeAt e (r ^ 2 / 2 + c) q₀ q) (Ioo a b) u)) := by
  rw [V.lintegral_tube_chart_neg e measurableSet_Ioo hdom hposE ha hb hq₀ hp₁ hp₁₂ hJsub g hg]
  exact lintegral_energy_eq_speed c hr₁ hr₁₂
    (fun E => ∫⁻ u in (fun q => V.timeAt e E q₀ q) '' Ioo a b,
      g (Function.invFunOn (fun q => V.timeAt e E q₀ q) (Ioo a b) u,
        -V.speedAt e E (Function.invFunOn (fun q => V.timeAt e E q₀ q) (Ioo a b) u)))

/-! ### Every positive-momentum state lies in a tube -/

/-- **The tubes cover.**  Around every edge state with positive momentum there is a tube
satisfying all the hypotheses of `lintegral_tube_chart`: a position window inside the extension
domain, an energy window `J` classically allowed on it, and a momentum strip whose energy range
contains `J` at every position of the window.  So the energy--time coordinates of Lemma VI.1 are
available in a neighbourhood of every state with `p > 0` (and, by momentum reversal, of every
state with `p ≠ 0`; the turning set `{p = 0}` is Liouville-null). -/
theorem exists_tube_window (e : Γ.Edge) {q p : ℝ} (hq : q ∈ V.domain e) (hp : 0 < p) :
    ∃ α β a b : ℝ, ∃ J : Set ℝ,
      MeasurableSet J ∧
      (∀ x ∈ Ioo α β, x ∈ V.domain e) ∧
      (∀ E ∈ J, ∀ x ∈ Ioo α β, V.extension e x < E) ∧
      a ∈ Ioo α β ∧ b ∈ Ioo α β ∧ q ∈ Ioo a b ∧
      V.hamiltonian e q p ∈ J ∧
      (∀ x ∈ Ioo a b, J ⊆ Ioo (V.energyOfMomentum e x (p / 2))
        (V.energyOfMomentum e x (2 * p))) := by
  classical
  set ε : ℝ := p ^ 2 / 8 with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  -- a position window inside the domain on which the potential varies by less than `ε`
  have hcont := V.extension_continuousAt_of_mem hq
  have hnhds : {x : ℝ | |V.extension e x - V.extension e q| < ε} ∈ nhds q := by
    have h := hcont (Metric.ball_mem_nhds (V.extension e q) hε0)
    refine Filter.mem_of_superset h (fun x hx => ?_)
    simpa [Real.dist_eq] using hx
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hnhds ((V.domain_isOpen e).mem_nhds hq))
  refine ⟨q - δ, q + δ, q - δ / 2, q + δ / 2, Ioo (V.hamiltonian e q p - ε)
    (V.hamiltonian e q p + ε), measurableSet_Ioo, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the position window lies in the extension domain
  · intro x hx
    exact (hδ (by rw [Real.ball_eq_Ioo]; exact hx)).2
  -- the energy window is classically allowed on the position window
  · intro E hE x hx
    have hVx : |V.extension e x - V.extension e q| < ε :=
      (hδ (by rw [Real.ball_eq_Ioo]; exact hx)).1
    have hVx' : V.extension e x < V.extension e q + ε := by
      have := abs_lt.mp hVx
      linarith [this.2]
    have hEq : V.hamiltonian e q p = p ^ 2 / 2 + V.extension e q := rfl
    have hEl : V.hamiltonian e q p - ε < E := hE.1
    have hsq : 2 * ε ≤ p ^ 2 / 2 := by rw [hε]; nlinarith [sq_nonneg p, hp]
    rw [hEq] at hEl
    linarith
  -- the endpoints of the inner window lie in the outer window
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩
  -- the reference energy lies in the window
  · exact ⟨by linarith, by linarith⟩
  -- the momentum strip covers the energy window at every position of the inner window
  · intro x hx E hE
    have hxmem : x ∈ Ioo (q - δ) (q + δ) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hVx : |V.extension e x - V.extension e q| < ε :=
      (hδ (by rw [Real.ball_eq_Ioo]; exact hxmem)).1
    obtain ⟨hV1, hV2⟩ := abs_lt.mp hVx
    have hEq : V.hamiltonian e q p = p ^ 2 / 2 + V.extension e q := rfl
    have h1 : V.energyOfMomentum e x (p / 2) = (p / 2) ^ 2 / 2 + V.extension e x := rfl
    have h2 : V.energyOfMomentum e x (2 * p) = (2 * p) ^ 2 / 2 + V.extension e x := rfl
    obtain ⟨hE1, hE2⟩ := hE
    rw [hEq] at hE1 hE2
    refine ⟨?_, ?_⟩
    · rw [h1, hε] at *
      nlinarith [sq_nonneg p, hp]
    · rw [h2, hε] at *
      nlinarith [sq_nonneg p, hp]

/-- **The tubes cover the negative-momentum states too.**  The Hamiltonian is even in the momentum,
so the window produced for `-p` serves for `p`; with `p₁ = -p/2` and `p₂ = -2p` the strip
`Ioo (-p₂) (-p₁)` of `lintegral_tube_chart_neg` is `Ioo (2p) (p/2)`, which contains `p`. -/
theorem exists_tube_window_neg (e : Γ.Edge) {q p : ℝ} (hq : q ∈ V.domain e) (hp : p < 0) :
    ∃ α β a b : ℝ, ∃ J : Set ℝ,
      MeasurableSet J ∧
      (∀ x ∈ Ioo α β, x ∈ V.domain e) ∧
      (∀ E ∈ J, ∀ x ∈ Ioo α β, V.extension e x < E) ∧
      a ∈ Ioo α β ∧ b ∈ Ioo α β ∧ q ∈ Ioo a b ∧
      V.hamiltonian e q p ∈ J ∧
      (∀ x ∈ Ioo a b, J ⊆ Ioo (V.energyOfMomentum e x (-p / 2))
        (V.energyOfMomentum e x (2 * -p))) := by
  obtain ⟨α, β, a, b, J, hJ, hdom, hposE, ha, hb, hqab, hE, hJsub⟩ :=
    V.exists_tube_window e hq (neg_pos.mpr hp)
  refine ⟨α, β, a, b, J, hJ, hdom, hposE, ha, hb, hqab, ?_, hJsub⟩
  have hH : V.hamiltonian e q p = V.hamiltonian e q (-p) := by
    unfold hamiltonian
    ring_nf
  rw [hH]
  exact hE

end MechanicalPotential

end HamiltonianMetricGraphs
