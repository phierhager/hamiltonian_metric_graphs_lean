/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.VertexLaw
import HamiltonianMetricGraphs.BoundaryFlux
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Families of Markov vertex laws and the full boundary flux (Sec. X, after Proposition X.2)

The paper states, after Proposition X.2:

> For a family `r ↦ P_v(r)` with Borel measurable entries, the full boundary flux
> `μ_v = (counting measure on E_v^∂) ⊗ r dr` is preserved if and only if `P_v(r)` is doubly
> stochastic for `r dr`-almost every `r > 0`.

A family of Markov vertex laws is a **random** scattering rule: a particle arriving through `η` at
speed `r` departs through `ζ` with probability `P_v(r)(η, ζ)`, at the same speed.  This file
makes it a Markov kernel and proves the statement in two forms.

* `MeasurableVertexLawFamily Γ v` — a family `r ↦ P_v(r)` of Markov vertex laws (Definition X.1)
  with Borel measurable entries.
* `speedKernel` — the induced Markov kernel on the speed chart `E_v^∂ × (0, ∞)`:
  `(η, r) ↦ ∑_ζ P_v(r)(η, ζ) δ_{(ζ, r)}`; and `boundaryKernel` — the same kernel read on the
  boundary sections of Definition III.6, from `D^in_v` to `D^out_v`:
  `α^in_{η,r} ↦ ∑_ζ P_v(r)(η, ζ) δ_{α^out_{ζ,r}}` (`boundaryKernel_incomingAtSpeed`).
* `speedKernel_preserves_iff` — **the printed statement**: the kernel preserves
  `μ_v = count ⊗ r dr`, i.e. `μ_v.bind κ = μ_v`, iff `P_v(r)` is doubly stochastic for
  `r dr`-a.e. `r`.
* `boundaryKernel_preserves_iff` — the same with the flux measures of Definition III.6: the kernel
  carries `μ_v^in` to `μ_v^out` (the probabilistic analogue of Lemma III.7,
  `(S_v)_# μ_v^in = μ_v^out`) iff `P_v(r)` is doubly stochastic for `r dr`-a.e. `r`.
* `ae_speedFluxMeasure_iff` / `boundaryKernel_preserves_iff_ae_lebesgue` — "`r dr`-almost every
  `r > 0`" is the same as "Lebesgue-almost every `r > 0`".

The heart is `bind_matrixKernel_eq_iff`, for an arbitrary finite discrete `ι` and an arbitrary
σ-finite measure `ν`; `speedFluxMeasure` (the measure `r dr`) is σ-finite
(`sigmaFinite_speedFluxMeasure`).
-/

namespace HamiltonianMetricGraphs

open MeasureTheory ProbabilityTheory Set FiniteMetricGraph
open scoped ENNReal

/-! ### The kernel of a measurable family of matrices -/

section General

variable {ι X : Type*} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
  [MeasurableSpace X]

/-- The kernel on `ι × X` induced by a measurable family `x ↦ P(x)` of matrices on `ι`: from
`(i, x)` it moves to `(j, x)` with weight `P(x)(i, j)`. -/
noncomputable def matrixKernel (P : X → Matrix ι ι ℝ) (hP : ∀ i j, Measurable fun x => P x i j) :
    Kernel (ι × X) (ι × X) where
  toFun p := ∑ j, ENNReal.ofReal (P p.2 p.1 j) • Measure.dirac (j, p.2)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hs]
    refine Finset.measurable_sum _ fun j _ => ?_
    have hPj : Measurable fun p : ι × X => P p.2 p.1 j :=
      measurable_from_prod_countable_right fun i => hP i j
    exact hPj.ennreal_ofReal.mul
      ((measurable_const.indicator hs).comp (measurable_const.prodMk measurable_snd))

theorem matrixKernel_apply (P : X → Matrix ι ι ℝ) (hP : ∀ i j, Measurable fun x => P x i j)
    (p : ι × X) :
    matrixKernel P hP p = ∑ j, ENNReal.ofReal (P p.2 p.1 j) • Measure.dirac (j, p.2) := rfl

theorem matrixKernel_apply_set (P : X → Matrix ι ι ℝ) (hP : ∀ i j, Measurable fun x => P x i j)
    (p : ι × X) {A : Set (ι × X)} (hA : MeasurableSet A) :
    matrixKernel P hP p A = ∑ j, ENNReal.ofReal (P p.2 p.1 j) * A.indicator 1 (j, p.2) := by
  rw [matrixKernel_apply]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hA]

/-- With row-stochastic matrices the kernel is a Markov kernel. -/
theorem isMarkovKernel_matrixKernel (P : X → Matrix ι ι ℝ)
    (hP : ∀ i j, Measurable fun x => P x i j) (hnn : ∀ x i j, 0 ≤ P x i j)
    (hrow : ∀ x i, ∑ j, P x i j = 1) : IsMarkovKernel (matrixKernel P hP) := by
  refine ⟨fun p => ⟨?_⟩⟩
  rw [matrixKernel_apply_set P hP p MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => hnn p.2 p.1 j, hrow, ENNReal.ofReal_one]

/-- `∫⁻ (count ⊗ ν)` is a sum of fibre integrals. -/
theorem lintegral_count_prod (ν : Measure X) [SFinite ν] {f : ι × X → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ p, f p ∂(Measure.count.prod ν) = ∫⁻ x, ∑ i, f (i, x) ∂ν := by
  rw [lintegral_prod f hf.aemeasurable, lintegral_fintype]
  simp only [Measure.count_singleton, mul_one]
  exact (lintegral_finsetSum _ fun i _ => hf.comp (measurable_const.prodMk measurable_id)).symm

/-- The measure `count ⊗ ν` in fibre form. -/
theorem count_prod_apply (ν : Measure X) [SFinite ν] {A : Set (ι × X)} (hA : MeasurableSet A) :
    (Measure.count.prod ν) A = ∫⁻ x, ∑ j, A.indicator 1 (j, x) ∂ν := by
  rw [← lintegral_indicator_one hA, lintegral_count_prod ν (measurable_one.indicator hA)]

/-- The image of `count ⊗ ν` under the kernel, in fibre form: the outgoing mass at `(j, x)` is the
`j`-th column sum of `P(x)`. -/
theorem bind_matrixKernel_apply (P : X → Matrix ι ι ℝ) (hP : ∀ i j, Measurable fun x => P x i j)
    (ν : Measure X) [SFinite ν] {A : Set (ι × X)} (hA : MeasurableSet A) :
    (Measure.count.prod ν).bind (matrixKernel P hP) A =
      ∫⁻ x, ∑ j, (∑ i, ENNReal.ofReal (P x i j)) * A.indicator 1 (j, x) ∂ν := by
  rw [Measure.bind_apply hA (matrixKernel P hP).measurable.aemeasurable,
    lintegral_count_prod ν (Kernel.measurable_coe _ hA)]
  refine lintegral_congr fun x => ?_
  simp only [matrixKernel_apply_set P hP _ hA, Finset.sum_mul]
  exact Finset.sum_comm

/-- **Preservation of `count ⊗ ν` by a measurable family of matrices.**  For a σ-finite `ν` and
nonnegative entries, the kernel of `x ↦ P(x)` maps `count ⊗ ν` to itself iff the columns of `P(x)`
sum to one for `ν`-almost every `x`. -/
theorem bind_matrixKernel_eq_iff (P : X → Matrix ι ι ℝ) (hP : ∀ i j, Measurable fun x => P x i j)
    (hnn : ∀ x i j, 0 ≤ P x i j) (ν : Measure X) [SigmaFinite ν] :
    (Measure.count.prod ν).bind (matrixKernel P hP) = Measure.count.prod ν ↔
      ∀ᵐ x ∂ν, ∀ j, ∑ i, P x i j = 1 := by
  classical
  have hcol : ∀ x j, ∑ i, ENNReal.ofReal (P x i j) = ENNReal.ofReal (∑ i, P x i j) :=
    fun x j => (ENNReal.ofReal_sum_of_nonneg fun i _ => hnn x i j).symm
  constructor
  · intro h
    rw [ae_all_iff]
    intro j
    have hmeas : Measurable fun x => ENNReal.ofReal (∑ i, P x i j) :=
      (Finset.measurable_sum _ fun i _ => hP i j).ennreal_ofReal
    have hset : ∀ B : Set X, MeasurableSet B →
        ∫⁻ x in B, ENNReal.ofReal (∑ i, P x i j) ∂ν = ∫⁻ x in B, 1 ∂ν := by
      intro B hB
      have hA : MeasurableSet (({j} : Set ι) ×ˢ B) := (MeasurableSet.singleton j).prod hB
      have hind : ∀ (k : ι) (x : X), (({j} : Set ι) ×ˢ B).indicator 1 (k, x) =
          if k = j then B.indicator (1 : X → ℝ≥0∞) x else 0 := by
        intro k x
        by_cases hk : k = j
        · subst hk
          simp [Set.indicator_apply]
        · simp [hk]
      have h1 := bind_matrixKernel_apply P hP ν hA
      rw [h, count_prod_apply ν hA] at h1
      simp only [hind, mul_ite, mul_zero, Finset.sum_ite_eq' Finset.univ j, Finset.mem_univ,
        if_true] at h1
      rw [← lintegral_indicator hB, ← lintegral_indicator hB]
      have e1 : (B.indicator fun x => ENNReal.ofReal (∑ i, P x i j)) =
          fun x => (∑ i, ENNReal.ofReal (P x i j)) * B.indicator 1 x := by
        funext x
        rw [hcol]
        by_cases hx : x ∈ B <;> simp [hx]
      have e2 : (B.indicator fun _ => (1 : ℝ≥0∞)) = B.indicator 1 := rfl
      rw [e1, e2, ← h1]
    have hae := ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hmeas measurable_const
      (fun B hB _ => hset B hB)
    filter_upwards [hae] with x hx
    have hx' : ENNReal.ofReal (∑ i, P x i j) = 1 := hx
    rwa [ENNReal.ofReal_eq_one] at hx'
  · intro h
    ext A hA
    rw [bind_matrixKernel_apply P hP ν hA, count_prod_apply ν hA]
    refine lintegral_congr_ae ?_
    filter_upwards [h] with x hx
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcol, hx j, ENNReal.ofReal_one, one_mul]

end General

/-! ### The measure `r dr` is σ-finite -/

namespace FiniteMetricGraph

/-- **`r dr` on `(0, ∞)` is σ-finite.**  Its image under the inclusion `(0, ∞) ⊆ ℝ` is the
σ-finite measure `r dr` on `ℝ` restricted to `(0, ∞)`. -/
theorem sigmaFinite_speedFluxMeasure : SigmaFinite speedFluxMeasure := by
  set W : Measure ℝ := (volume.restrict (Ioi (0 : ℝ))).withDensity fun r => ENNReal.ofReal r
  have hmap : speedFluxMeasure.map (Subtype.val : PositiveSpeed → ℝ) = W := by
    unfold speedFluxMeasure
    rw [Measure.map_map measurable_subtype_coe measurable_positiveSpeedOf]
    have hae : (Subtype.val ∘ positiveSpeedOf : ℝ → ℝ) =ᵐ[W] id := by
      have h0 : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∈ Ioi (0 : ℝ) :=
        ae_restrict_mem measurableSet_Ioi
      filter_upwards [withDensity_absolutelyContinuous _ _ h0] with r hr
      simp [positiveSpeedOf_of_pos (show (0 : ℝ) < r from hr)]
    rw [Measure.map_congr hae, Measure.map_id]
  exact SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable
    (by rw [hmap]; exact SigmaFinite.withDensity_ofReal _)

instance : SigmaFinite speedFluxMeasure := sigmaFinite_speedFluxMeasure

/-- **"`r dr`-almost every `r > 0`" is "Lebesgue-almost every `r > 0`"**, for a Borel property of
the speed. -/
theorem ae_speedFluxMeasure_iff {p : PositiveSpeed → Prop} (hp : MeasurableSet {r | p r}) :
    (∀ᵐ r ∂speedFluxMeasure, p r) ↔ ∀ᵐ r : ℝ, ∀ hr : 0 < r, p ⟨r, hr⟩ := by
  unfold speedFluxMeasure
  rw [ae_map_iff measurable_positiveSpeedOf.aemeasurable hp,
    ae_withDensity_iff ENNReal.measurable_ofReal, ae_restrict_iff' measurableSet_Ioi]
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun r => ?_)
  constructor
  · intro h hr
    have := h hr (by simpa using hr)
    rwa [positiveSpeedOf_of_pos hr] at this
  · intro h hr _
    rw [positiveSpeedOf_of_pos hr]
    exact h hr

end FiniteMetricGraph

/-! ### Measurable families of Markov vertex laws -/

/-- **A family `r ↦ P_v(r)` of Markov vertex laws with Borel measurable entries** at the vertex
`v`: for every speed `r > 0`, `P_v(r)` is a Markov vertex law (Definition X.1). -/
structure MeasurableVertexLawFamily (Γ : FiniteMetricGraph) (v : Γ.Vertex) where
  /-- The vertex law at speed `r`. -/
  P : PositiveSpeed → Matrix (Γ.IncidentEnds v) (Γ.IncidentEnds v) ℝ
  /-- The entries are Borel functions of the speed. -/
  measurable : ∀ η ζ, Measurable fun r => P r η ζ
  /-- Each `P_v(r)` is a Markov vertex law: nonnegative entries, rows summing to one. -/
  isMarkov : ∀ r, MechanicalPotential.IsMarkovVertexLaw (P r)

namespace MeasurableVertexLawFamily

variable {Γ : FiniteMetricGraph} {v : Γ.Vertex} (F : MeasurableVertexLawFamily Γ v)

/-- **The induced Markov kernel in the speed chart** `E_v^∂ × (0, ∞)`: arriving through `η` at
speed `r`, depart through `ζ` with probability `P_v(r)(η, ζ)`, at the same speed. -/
noncomputable def speedKernel :
    Kernel (Γ.IncidentEnds v × PositiveSpeed) (Γ.IncidentEnds v × PositiveSpeed) :=
  matrixKernel F.P F.measurable

theorem speedKernel_apply (η : Γ.IncidentEnds v) (r : PositiveSpeed) :
    F.speedKernel (η, r) = ∑ ζ, ENNReal.ofReal (F.P r η ζ) • Measure.dirac (ζ, r) := rfl

instance : IsMarkovKernel F.speedKernel :=
  isMarkovKernel_matrixKernel F.P F.measurable (fun r => (F.isMarkov r).1)
    (fun r => (F.isMarkov r).2)

/-- **The induced Markov kernel on the boundary sections of Definition III.6**, from incoming
covectors `D^in_v` to outgoing covectors `D^out_v` (`boundaryKernel_incomingAtSpeed`). -/
noncomputable def boundaryKernel : Kernel (Γ.IncomingBoundary v) (Γ.OutgoingBoundary v) :=
  (F.speedKernel.map (Γ.outgoingSpeedChart v)).comap (Γ.incomingSpeedChart v).symm
    (Γ.incomingSpeedChart v).symm.measurable

/-- The boundary kernel sends `α^in_{η,r}` to `∑_ζ P_v(r)(η, ζ) δ_{α^out_{ζ,r}}`. -/
theorem boundaryKernel_incomingAtSpeed (η : Γ.IncidentEnds v) (r : PositiveSpeed) :
    F.boundaryKernel (Γ.incomingAtSpeed η r) =
      ∑ ζ, ENNReal.ofReal (F.P r η ζ) • Measure.dirac (Γ.outgoingAtSpeed ζ r) := by
  have h1 : (Γ.incomingSpeedChart v).symm (Γ.incomingAtSpeed η r) = (η, r) :=
    (Γ.incomingSpeedChart v).symm_apply_apply (η, r)
  rw [boundaryKernel, Kernel.comap_apply, h1,
    Kernel.map_apply _ (Γ.outgoingSpeedChart v).measurable, speedKernel_apply,
    Measure.map_finset_sum' (Γ.outgoingSpeedChart v).measurable.aemeasurable]
  · refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [Measure.map_smul, Measure.map_dirac' (Γ.outgoingSpeedChart v).measurable]
    rfl

instance : IsMarkovKernel F.boundaryKernel := by
  unfold boundaryKernel
  have : IsMarkovKernel (F.speedKernel.map (Γ.outgoingSpeedChart v)) :=
    Kernel.IsMarkovKernel.map _ (Γ.outgoingSpeedChart v).measurable
  infer_instance

/-- Pulling the boundary kernel back to the speed chart. -/
theorem bind_boundaryFluxIn (ν : Measure PositiveSpeed) [SFinite ν] :
    (Measure.map (Γ.incomingSpeedChart v) (Measure.count.prod ν)).bind F.boundaryKernel =
      Measure.map (Γ.outgoingSpeedChart v) ((Measure.count.prod ν).bind F.speedKernel) := by
  ext B hB
  rw [Measure.bind_apply hB F.boundaryKernel.measurable.aemeasurable,
    lintegral_map (Kernel.measurable_coe _ hB) (Γ.incomingSpeedChart v).measurable,
    Measure.map_apply (Γ.outgoingSpeedChart v).measurable hB,
    Measure.bind_apply ((Γ.outgoingSpeedChart v).measurable hB)
      F.speedKernel.measurable.aemeasurable]
  refine lintegral_congr fun p => ?_
  rw [boundaryKernel, Kernel.comap_apply, MeasurableEquiv.symm_apply_apply,
    Kernel.map_apply' _ (Γ.outgoingSpeedChart v).measurable _ hB]

/-- Membership in the doubly stochastic matrices for a Markov vertex law is the column
condition. -/
theorem mem_doublyStochastic_iff (r : PositiveSpeed) :
    F.P r ∈ doublyStochastic ℝ (Γ.IncidentEnds v) ↔ ∀ ζ, ∑ η, F.P r η ζ = 1 := by
  classical
  rw [MechanicalPotential.mem_doublyStochastic_iff_vertexLaw]
  exact ⟨fun h => h.2, fun h => ⟨F.isMarkov r, h⟩⟩

/-- **After Proposition X.2, in the speed chart.**  The induced Markov kernel preserves the full
boundary flux `μ_v = (counting measure on E_v^∂) ⊗ r dr` iff `P_v(r)` is doubly stochastic for
`r dr`-almost every `r > 0`. -/
theorem speedKernel_preserves_iff :
    (Measure.count.prod speedFluxMeasure).bind F.speedKernel =
        Measure.count.prod speedFluxMeasure ↔
      ∀ᵐ r ∂speedFluxMeasure, F.P r ∈ doublyStochastic ℝ (Γ.IncidentEnds v) := by
  classical
  rw [speedKernel, bind_matrixKernel_eq_iff F.P F.measurable (fun r => (F.isMarkov r).1)]
  simp only [F.mem_doublyStochastic_iff]

/-- **After Proposition X.2, with the flux measures of Definition III.6.**  The induced Markov
kernel carries the incoming boundary flux `μ_v^in` to the outgoing boundary flux `μ_v^out` iff
`P_v(r)` is doubly stochastic for `r dr`-almost every `r > 0`.  For a deterministic law this is
Lemma III.7, `(S_v)_# μ_v^in = μ_v^out`. -/
theorem boundaryKernel_preserves_iff :
    (Γ.boundaryFluxIn v).bind F.boundaryKernel = Γ.boundaryFluxOut v ↔
      ∀ᵐ r ∂speedFluxMeasure, F.P r ∈ doublyStochastic ℝ (Γ.IncidentEnds v) := by
  rw [← F.speedKernel_preserves_iff, Γ.boundaryFluxIn_eq_map, Γ.boundaryFluxOut_eq_map,
    F.bind_boundaryFluxIn]
  constructor
  · intro h
    have := congrArg (Measure.map (Γ.outgoingSpeedChart v).symm) h
    rwa [MeasurableEquiv.map_symm_map, MeasurableEquiv.map_symm_map] at this
  · intro h
    rw [h]

/-- The set of speeds at which the law is doubly stochastic is Borel. -/
theorem measurableSet_doublyStochastic :
    MeasurableSet {r | F.P r ∈ doublyStochastic ℝ (Γ.IncidentEnds v)} := by
  classical
  simp only [F.mem_doublyStochastic_iff, Set.setOf_forall]
  exact MeasurableSet.iInter fun ζ =>
    measurableSet_eq_fun (Finset.measurable_sum _ fun η _ => F.measurable η ζ) measurable_const

/-- **After Proposition X.2, "almost every `r > 0`" read with Lebesgue measure.**  Since `r dr`
and Lebesgue measure on `(0, ∞)` have the same null sets, the condition is that `P_v(r)` be doubly
stochastic for Lebesgue-almost every `r > 0`. -/
theorem boundaryKernel_preserves_iff_ae_lebesgue :
    (Γ.boundaryFluxIn v).bind F.boundaryKernel = Γ.boundaryFluxOut v ↔
      ∀ᵐ r : ℝ, ∀ hr : 0 < r, F.P ⟨r, hr⟩ ∈ doublyStochastic ℝ (Γ.IncidentEnds v) := by
  rw [F.boundaryKernel_preserves_iff, ae_speedFluxMeasure_iff F.measurableSet_doublyStochastic]

end MeasurableVertexLawFamily

end HamiltonianMetricGraphs
