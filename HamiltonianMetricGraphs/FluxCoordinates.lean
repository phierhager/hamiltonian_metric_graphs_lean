/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.BorelScattering

/-!
# Flux coordinates and the flux measure (towards Lemma III.7)

The boundary flux measure of the paper is `counting × r dr` in the speed chart
`IncidentEnds v × PositiveSpeed`.  Scattering, read in speed coordinates, is a *fixed-speed*
germ permutation (Proposition III.2, already proved as `speedPermutation`).  The key measure-theoretic
fact making the flux measure invariant is a general lemma about **skew permutations of a product
with counting measure on a finite factor**: a fibrewise permutation of a finite factor preserves the
product of counting measure with any (s-finite) measure.  This file proves that general lemma; it is
the abstract heart of Lemma III.7.
-/

namespace HamiltonianMetricGraphs

open MeasureTheory ENNReal

/-- **Skew-permutation invariance of a counting product measure.**  Let `ι` be a finite measurable
space with singletons measurable, `μ` an s-finite measure on `X`, and for each `x : X` let `σ x` be a
permutation of `ι` such that the fibrewise map `T (i,x) = (σ x i, x)` is measurable.  Then `T`
preserves the product measure `count × μ`.  This is the abstract content of the flux-measure
preservation (Lemma III.7): counting measure is permutation-invariant on each `x`-fibre, and the
`x`-coordinate (hence `μ`) is untouched. -/
theorem map_skewPermutation_count_prod {ι X : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (σ : X → Equiv.Perm ι)
    (hσ : Measurable (fun p : ι × X => ((σ p.2) p.1, p.2))) :
    Measure.map (fun p : ι × X => ((σ p.2) p.1, p.2)) (Measure.count.prod μ)
      = Measure.count.prod μ := by
  set T : ι × X → ι × X := fun p => ((σ p.2) p.1, p.2) with hT
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hσ hA, Measure.prod_apply (hσ hA), Measure.prod_apply hA,
    lintegral_fintype, lintegral_fintype]
  simp only [Measure.count_singleton, mul_one]
  -- Rewrite each fibre measure as the integral of an indicator, swap sum and integral, reindex.
  have hmeasA : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) :=
    (measurable_const).indicator hA
  have hcompS : ∀ i : ι, Measurable (fun x : X => ((σ x) i, x)) := by
    intro i
    exact hσ.comp (measurable_prodMk_left)
  have hcompR : ∀ i : ι, Measurable (fun x : X => (i, x)) := by
    intro i
    exact measurable_prodMk_left
  -- Each fibre measure equals the integral of an indicator; the preimage-indicator identity is
  -- definitional (membership in a preimage unfolds to membership of the image point).
  have hLHS : ∀ i : ι, μ (Prod.mk i ⁻¹' (T ⁻¹' A))
      = ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) ((σ x) i, x) ∂μ := by
    intro i
    rw [show Prod.mk i ⁻¹' (T ⁻¹' A) = (fun x : X => ((σ x) i, x)) ⁻¹' A from rfl,
      ← lintegral_indicator_one ((hcompS i) hA)]
    exact lintegral_congr fun x => rfl
  have hRHS : ∀ i : ι, μ (Prod.mk i ⁻¹' A)
      = ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) (i, x) ∂μ := by
    intro i
    rw [show Prod.mk i ⁻¹' A = (fun x : X => (i, x)) ⁻¹' A from rfl,
      ← lintegral_indicator_one ((hcompR i) hA)]
    exact lintegral_congr fun x => rfl
  have hLsum : ∑ i, ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) ((σ x) i, x) ∂μ
      = ∫⁻ x, ∑ i, A.indicator (fun _ => (1 : ℝ≥0∞)) ((σ x) i, x) ∂μ :=
    (lintegral_finsetSum Finset.univ (fun i _ => hmeasA.comp (hcompS i))).symm
  have hRsum : ∑ i, ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) (i, x) ∂μ
      = ∫⁻ x, ∑ i, A.indicator (fun _ => (1 : ℝ≥0∞)) (i, x) ∂μ :=
    (lintegral_finsetSum Finset.univ (fun i _ => hmeasA.comp (hcompR i))).symm
  have hswap : ∫⁻ x, ∑ i, A.indicator (fun _ => (1 : ℝ≥0∞)) ((σ x) i, x) ∂μ
      = ∫⁻ x, ∑ i, A.indicator (fun _ => (1 : ℝ≥0∞)) (i, x) ∂μ := by
    refine lintegral_congr fun x => ?_
    exact Equiv.sum_comp (σ x) (fun j => A.indicator (fun _ => (1 : ℝ≥0∞)) (j, x))
  simp only [hLHS, hRHS]
  rw [hLsum, hRsum, hswap]

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

namespace BorelEnergyPreservingScattering

variable (S : BorelEnergyPreservingScattering V)

/-- **Flux-measure invariance in speed coordinates (Lemma III.7, core form).**  The fixed-speed
germ permutation induced by scattering (`speedEndpoint`, Proposition III.2) preserves `counting × μ`
for every s-finite speed measure `μ` — in particular the flux measure `counting × r dr`.  This is
exactly the invariance of Lemma III.7 read in the incoming/outgoing speed chart, and it is an
immediate instance of `map_skewPermutation_count_prod` because scattering fixes the speed `r` and
only permutes the finite incident-end germ. -/
theorem map_speedScattering_count_prod (v : Γ.Vertex)
    (μ : Measure FiniteMetricGraph.PositiveSpeed) [SFinite μ] :
    Measure.map (fun p : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed =>
        (EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v p.1 p.2, p.2))
        (Measure.count.prod μ)
      = Measure.count.prod μ := by
  refine map_skewPermutation_count_prod μ
    (fun r => EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r) ?_
  exact (BorelEnergyPreservingScattering.measurable_speedEndpoint V S v).prodMk measurable_snd

/-- **Lemma III.7 (flux preservation).**  Scattering `S.map v` pushes the incoming flux measure
(`counting × μ` read through the incoming speed chart) exactly onto the outgoing flux measure (the
same `counting × μ` read through the outgoing speed chart), for every s-finite speed measure `μ`; in
particular for the paper's flux measure `counting × r dr`.  The proof intertwines `S.map v` with the
fixed-speed germ permutation via `scattered_incomingAtSpeed` and applies the speed-coordinate
invariance `map_speedScattering_count_prod`. -/
theorem map_scattering_speedFlux (v : Γ.Vertex)
    (μ : Measure FiniteMetricGraph.PositiveSpeed) [SFinite μ] :
    Measure.map (S.map v) (Measure.map (Γ.incomingSpeedChart v) (Measure.count.prod μ))
      = Measure.map (Γ.outgoingSpeedChart v) (Measure.count.prod μ) := by
  rw [Measure.map_map (S.map v).measurable (Γ.incomingSpeedChart v).measurable]
  have hinter : (S.map v) ∘ (Γ.incomingSpeedChart v)
      = (Γ.outgoingSpeedChart v) ∘
        (fun p : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed =>
          (EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v p.1 p.2,
            p.2)) := by
    funext p
    obtain ⟨η, r⟩ := p
    exact scattered_incomingAtSpeed (V := V) S v η r
  rw [hinter, ← Measure.map_map (Γ.outgoingSpeedChart v).measurable
      ((BorelEnergyPreservingScattering.measurable_speedEndpoint V S v).prodMk measurable_snd),
    map_speedScattering_count_prod V S v μ]

end BorelEnergyPreservingScattering
end MechanicalPotential

end HamiltonianMetricGraphs
