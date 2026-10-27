/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Reversibility

/-!
# Finite-valued Borel criteria

The endpoint part of a speed-coordinate scattering law has finite discrete codomain.  Its
measurability is therefore exactly the measurability of its singleton fibres.
-/

namespace HamiltonianMetricGraphs

theorem measurable_iff_preimage_singletons {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [Finite Y] [DiscreteMeasurableSpace Y] (f : X → Y) :
    Measurable f ↔ ∀ y : Y, MeasurableSet (f ⁻¹' {y}) := by
  classical
  letI := Fintype.ofFinite Y
  constructor
  · intro hf y
    exact hf (MeasurableSet.singleton y)
  · intro hf s hs
    have hpiece : ∀ y : Y, MeasurableSet (if y ∈ s then f ⁻¹' {y} else ∅) := by
      intro y
      split_ifs with hy
      · exact hf y
      · exact MeasurableSet.empty
    have hunion : MeasurableSet (⋃ y ∈ (Finset.univ : Finset Y),
        if y ∈ s then f ⁻¹' {y} else ∅) :=
      (Finset.univ.measurableSet_biUnion fun y _ => hpiece y)
    rw [show f ⁻¹' s = ⋃ y ∈ (Finset.univ : Finset Y),
      if y ∈ s then f ⁻¹' {y} else ∅ by
        ext x
        simp]
    exact hunion

/-- For a finite discrete first coordinate, a subset of a product is Borel exactly when all its
coordinate sections are Borel. -/
theorem measurableSet_finite_prod_iff_sections {A X : Type*} [MeasurableSpace A]
    [MeasurableSpace X] [Finite A] [DiscreteMeasurableSpace A] (s : Set (A × X)) :
    MeasurableSet s ↔ ∀ a : A, MeasurableSet {x : X | (a, x) ∈ s} := by
  classical
  letI := Fintype.ofFinite A
  constructor
  · intro hs a
    change MeasurableSet ((fun x : X => (a, x)) ⁻¹' s)
    exact hs.preimage (Measurable.prodMk measurable_const measurable_id)
  · intro hsections
    have hpiece : ∀ a : A, MeasurableSet ({a} ×ˢ {x : X | (a, x) ∈ s}) := by
      intro a
      exact (MeasurableSet.singleton a).prod (hsections a)
    have hunion : MeasurableSet (⋃ a ∈ (Finset.univ : Finset A),
        ({a} ×ˢ {x : X | (a, x) ∈ s})) :=
      Finset.univ.measurableSet_biUnion fun a _ => hpiece a
    rw [show s = ⋃ a ∈ (Finset.univ : Finset A),
      ({a} ×ˢ {x : X | (a, x) ∈ s}) by
        ext x
        simp]
    exact hunion

namespace MechanicalPotential.BorelEnergyPreservingScattering

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-- A finite-valued form of Lemma III.3 for the full speed-coordinate endpoint function. -/
theorem measurable_speedEndpoint_iff_fibers (v : Γ.Vertex) :
    Measurable (fun x : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed =>
      EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v x.1 x.2) ↔
    ∀ ζ : Γ.IncidentEnds v, MeasurableSet {x : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed |
      EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v x.1 x.2 = ζ} :=
  measurable_iff_preimage_singletons _

/-- Lemma III.3 in the paper's per-incoming-end form.  The Borel condition on every set
`{r > 0 | F_v(η,r)=ζ}` is equivalent to Borel measurability of the full speed-endpoint map. -/
theorem measurable_speedEndpoint_iff_coordinateFibers (v : Γ.Vertex) :
    Measurable (fun x : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed =>
      EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v x.1 x.2) ↔
    ∀ η ζ : Γ.IncidentEnds v, MeasurableSet {r : FiniteMetricGraph.PositiveSpeed |
      EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v η r = ζ} := by
  rw [measurable_speedEndpoint_iff_fibers V S v]
  constructor
  · intro h η ζ
    have hsections := (measurableSet_finite_prod_iff_sections
      {x : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed |
        EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v x.1 x.2 = ζ
      }).mp
      (h ζ)
    simpa using hsections η
  · intro h ζ
    apply (measurableSet_finite_prod_iff_sections
      {x : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed |
        EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v x.1 x.2 = ζ
      }).mpr
    intro η
    simpa using h η ζ

end MechanicalPotential.BorelEnergyPreservingScattering
end HamiltonianMetricGraphs
