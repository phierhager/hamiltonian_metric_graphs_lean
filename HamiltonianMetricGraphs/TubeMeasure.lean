/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3: the impact step preserves the tube measure
-/

import HamiltonianMetricGraphs.FluxCoordinates

/-!
# The impact step preserves the tube measure (Lemma VI.3, impact part)

In the tube coordinates of the paper a short-time neighbourhood of one impact is described by a
boundary covector together with the elapsed time, and the Liouville measure becomes the product of
the boundary flux measure with Lebesgue measure in the time:

`dq dp = (counting × r dr) × du`.

The impact step maps such a tube to the tube on the outgoing side by scattering the covector and
reflecting the time, `u ↦ Δ - u`.  This module proves that this composite preserves the tube
measure:

* `map_reflect_volume`: the reflection `u ↦ Δ - u` preserves Lebesgue measure.
* `map_impactStep_speedFlux_prod`: in speed coordinates the impact step is a fibrewise germ
  permutation times the reflection, hence preserves `(counting × μ) × volume` for every s-finite
  speed measure `μ` — in particular for the paper's flux measure `r dr`.
* `map_impactStep_flux_prod`: the same statement in the incoming/outgoing charts, i.e. the impact
  step `(α, u) ↦ (S α, Δ - u)` pushes the incoming tube measure exactly onto the outgoing tube
  measure.

Together with Lemma VI.1 (`lintegral_flux_form`, which turns `dq dp` into `dq dE / p`, and
`lintegral_position_eq_time`, which turns `dq / p` into `du`) and Lemma III.7 (flux preservation at
a vertex, used here through `map_speedScattering_count_prod`) this is the measure-preservation
content of Lemma VI.3 at an impact.
-/

namespace HamiltonianMetricGraphs

open MeasureTheory Set
open scoped ENNReal

/-- The reflection `u ↦ Δ - u` preserves Lebesgue measure on the line. -/
theorem map_reflect_volume (Δ : ℝ) :
    Measure.map (fun u : ℝ => Δ - u) volume = volume :=
  (Measure.measurePreserving_sub_left volume Δ).map_eq

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

namespace BorelEnergyPreservingScattering

variable (S : BorelEnergyPreservingScattering V)

/-- **The impact step preserves the tube measure, in speed coordinates.**  Scattering is a
fixed-speed permutation of the finite incident-end germ (Proposition III.2), and the time
reflection preserves Lebesgue measure, so their product preserves `(counting × μ) × volume` for
every s-finite speed measure `μ`. -/
theorem map_impactStep_speedFlux_prod (v : Γ.Vertex)
    (μ : Measure FiniteMetricGraph.PositiveSpeed) [SFinite μ] (Δ : ℝ) :
    Measure.map (Prod.map
        (fun p : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed =>
          (EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v p.1 p.2,
            p.2))
        (fun u : ℝ => Δ - u))
      ((Measure.count.prod μ).prod volume)
      = (Measure.count.prod μ).prod volume := by
  have hscat : Measurable (fun p : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed =>
      (EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v p.1 p.2,
        p.2)) :=
    (BorelEnergyPreservingScattering.measurable_speedEndpoint V S v).prodMk measurable_snd
  have hrefl : Measurable (fun u : ℝ => Δ - u) := measurable_const.sub measurable_id
  rw [← Measure.map_prod_map (Measure.count.prod μ) volume hscat hrefl,
    map_speedScattering_count_prod V S v μ, map_reflect_volume]

/-- **Lemma VI.3 (impact part).**  The impact step — scatter the boundary covector through `S` and
reflect the elapsed time `u ↦ Δ - u` — pushes the incoming tube measure exactly onto the outgoing
tube measure, for every s-finite speed measure `μ`; in particular for the paper's flux measure
`counting × r dr`.

This is the invariance of the Liouville measure across one impact, read in the tube coordinates in
which Lemma VI.1 expresses `dq dp` as `(counting × r dr) × du`. -/
theorem map_impactStep_flux_prod (v : Γ.Vertex)
    (μ : Measure FiniteMetricGraph.PositiveSpeed) [SFinite μ] (Δ : ℝ) :
    Measure.map (Prod.map (S.map v) (fun u : ℝ => Δ - u))
        (Measure.map (Prod.map (Γ.incomingSpeedChart v) (id : ℝ → ℝ))
          ((Measure.count.prod μ).prod volume))
      = Measure.map (Prod.map (Γ.outgoingSpeedChart v) (id : ℝ → ℝ))
          ((Measure.count.prod μ).prod volume) := by
  have hscat : Measurable (fun p : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed =>
      (EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v p.1 p.2,
        p.2)) :=
    (BorelEnergyPreservingScattering.measurable_speedEndpoint V S v).prodMk measurable_snd
  have hrefl : Measurable (fun u : ℝ => Δ - u) := measurable_const.sub measurable_id
  have hin : Measurable (Prod.map (Γ.incomingSpeedChart v) (id : ℝ → ℝ)) :=
    (Γ.incomingSpeedChart v).measurable.prodMap measurable_id
  have hout : Measurable (Prod.map (Γ.outgoingSpeedChart v) (id : ℝ → ℝ)) :=
    (Γ.outgoingSpeedChart v).measurable.prodMap measurable_id
  have hstep : Measurable (Prod.map (S.map v) (fun u : ℝ => Δ - u)) :=
    (S.map v).measurable.prodMap hrefl
  -- the impact step in the incoming chart is the outgoing chart of the speed-coordinate step
  have hinter : (Prod.map (S.map v) (fun u : ℝ => Δ - u)) ∘
      (Prod.map (Γ.incomingSpeedChart v) (id : ℝ → ℝ))
      = (Prod.map (Γ.outgoingSpeedChart v) (id : ℝ → ℝ)) ∘
        (Prod.map
          (fun p : Γ.IncidentEnds v × FiniteMetricGraph.PositiveSpeed =>
            (EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering v p.1 p.2,
              p.2))
          (fun u : ℝ => Δ - u)) := by
    funext z
    obtain ⟨⟨η, r⟩, u⟩ := z
    exact Prod.ext (scattered_incomingAtSpeed (V := V) S v η r) rfl
  rw [Measure.map_map hstep hin, hinter, ← Measure.map_map hout
    (hscat.prodMap hrefl), map_impactStep_speedFlux_prod V S v μ Δ]

end BorelEnergyPreservingScattering

end MechanicalPotential

end HamiltonianMetricGraphs
