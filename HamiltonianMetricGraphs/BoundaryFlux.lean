/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.FluxCoordinates

/-!
# The boundary flux measures (Definition III.6, Lemma III.7)

Definition III.6 of the paper defines the incoming and outgoing flux measures at a vertex `v` by
```
  μ_v^in(A)  = ∑_{η ∈ E_v^∂} ∫_0^∞ 1_A(α^in_{η,r})  r dr,
  μ_v^out(B) = ∑_{η ∈ E_v^∂} ∫_0^∞ 1_B(α^out_{η,r}) r dr.
```
This module defines `boundaryFluxIn v` and `boundaryFluxOut v` as measures on the incoming and
outgoing boundary sections `D^in_v`, `D^out_v`: each is the finite sum over the incident edge-ends
`η` of the pushforward of the speed measure `r dr` on `(0, ∞)` under the speed chart
`r ↦ α^in_{η,r}` (resp. `r ↦ α^out_{η,r}`).  The theorems `boundaryFluxIn_apply` and
`boundaryFluxOut_apply` prove that on every measurable set they are given by exactly the displayed
formula, with `∫_0^∞ … r dr` the Lebesgue integral over `Ioi 0` against the density `r`.

`boundaryFluxIn_eq_map` and `boundaryFluxOut_eq_map` identify them with the pushforwards
`(ι_in)_# (count × r dr)` and `(ι_out)_# (count × r dr)` used by `map_scattering_speedFlux`
(the speed-chart form of Lemma III.7), and `map_scattering_boundaryFlux` restates Lemma III.7
literally: `(S_v)_# μ_v^in = μ_v^out`.
-/

namespace HamiltonianMetricGraphs

open MeasureTheory ENNReal Set

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- A real number read as a positive speed.  On `(0, ∞)` it is the number itself
(`positiveSpeedOf_of_pos`); off `(0, ∞)` it takes the junk value `1`, which is never seen by the
speed measure `r dr` on `(0, ∞)`. -/
noncomputable def positiveSpeedOf (r : ℝ) : PositiveSpeed :=
  ⟨if 0 < r then r else 1, by
    change 0 < if 0 < r then r else 1
    split_ifs with h
    · exact h
    · exact one_pos⟩

@[simp] theorem positiveSpeedOf_of_pos {r : ℝ} (hr : 0 < r) :
    positiveSpeedOf r = ⟨r, hr⟩ := by
  apply Subtype.ext
  change (if 0 < r then r else 1) = r
  rw [if_pos hr]

theorem measurable_positiveSpeedOf : Measurable positiveSpeedOf := by
  refine Measurable.subtype_mk ?_
  exact Measurable.ite measurableSet_Ioi measurable_id measurable_const

/-- **The speed measure `r dr` on `(0, ∞)`**, as a measure on the positive speeds: Lebesgue measure
on `(0, ∞)` with density `r`, transported to the speed type. -/
noncomputable def speedFluxMeasure : Measure PositiveSpeed :=
  Measure.map positiveSpeedOf
    ((volume.restrict (Ioi (0 : ℝ))).withDensity fun r => ENNReal.ofReal r)

instance : SFinite speedFluxMeasure := by
  unfold speedFluxMeasure
  infer_instance

/-- Integrals against `r dr` are integrals over `(0, ∞)` with density `r`. -/
theorem lintegral_speedFluxMeasure (f : PositiveSpeed → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ r, f r ∂speedFluxMeasure =
      ∫⁻ r in Ioi (0 : ℝ), f (positiveSpeedOf r) * ENNReal.ofReal r := by
  unfold speedFluxMeasure
  have h := lintegral_withDensity_eq_lintegral_mul (volume.restrict (Ioi (0 : ℝ)))
    (f := fun r => ENNReal.ofReal r) ENNReal.measurable_ofReal
    (hf.comp measurable_positiveSpeedOf)
  rw [lintegral_map hf measurable_positiveSpeedOf]
  refine h.trans (lintegral_congr fun r => ?_)
  simp only [Pi.mul_apply, Function.comp_apply]
  ring

variable {Γ}

theorem measurable_incomingAtSpeed_left {v : Γ.Vertex} (η : Γ.IncidentEnds v) :
    Measurable (fun r : PositiveSpeed => Γ.incomingAtSpeed η r) :=
  (Γ.measurable_incomingAtSpeed v).comp (measurable_const.prodMk measurable_id)

theorem measurable_outgoingAtSpeed_left {v : Γ.Vertex} (η : Γ.IncidentEnds v) :
    Measurable (fun r : PositiveSpeed => Γ.outgoingAtSpeed η r) :=
  (Γ.measurable_outgoingAtSpeed v).comp (measurable_const.prodMk measurable_id)

variable (Γ)

/-- **The incoming flux measure `μ_v^in` (Definition III.6)**, a measure on the incoming boundary
section `D^in_v`: the sum over the incident edge-ends `η` of the image of `r dr` under the speed
chart `r ↦ α^in_{η,r}`.  Its values are the displayed formula of the paper
(`boundaryFluxIn_apply`). -/
noncomputable def boundaryFluxIn (v : Γ.Vertex) : Measure (Γ.IncomingBoundary v) :=
  ∑ η : Γ.IncidentEnds v, Measure.map (fun r => Γ.incomingAtSpeed η r) speedFluxMeasure

/-- **The outgoing flux measure `μ_v^out` (Definition III.6)**, a measure on the outgoing boundary
section `D^out_v`: the sum over `η` of the image of `r dr` under `r ↦ α^out_{η,r}`
(`boundaryFluxOut_apply`). -/
noncomputable def boundaryFluxOut (v : Γ.Vertex) : Measure (Γ.OutgoingBoundary v) :=
  ∑ η : Γ.IncidentEnds v, Measure.map (fun r => Γ.outgoingAtSpeed η r) speedFluxMeasure

/-- **Definition III.6, incoming formula.**  For every measurable `A ⊆ D^in_v`,
`μ_v^in(A) = ∑_η ∫_0^∞ 1_A(α^in_{η,r}) r dr`. -/
theorem boundaryFluxIn_apply (v : Γ.Vertex) {A : Set (Γ.IncomingBoundary v)}
    (hA : MeasurableSet A) :
    Γ.boundaryFluxIn v A = ∑ η : Γ.IncidentEnds v,
      ∫⁻ r in Ioi (0 : ℝ),
        A.indicator 1 (Γ.incomingAtSpeed η (positiveSpeedOf r)) * ENNReal.ofReal r := by
  unfold boundaryFluxIn
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [Measure.map_apply (measurable_incomingAtSpeed_left η) hA,
    ← lintegral_indicator_one ((measurable_incomingAtSpeed_left η) hA),
    lintegral_speedFluxMeasure _ (measurable_one.indicator
      ((measurable_incomingAtSpeed_left η) hA))]
  rfl

/-- **Definition III.6, outgoing formula.**  For every measurable `B ⊆ D^out_v`,
`μ_v^out(B) = ∑_η ∫_0^∞ 1_B(α^out_{η,r}) r dr`. -/
theorem boundaryFluxOut_apply (v : Γ.Vertex) {B : Set (Γ.OutgoingBoundary v)}
    (hB : MeasurableSet B) :
    Γ.boundaryFluxOut v B = ∑ η : Γ.IncidentEnds v,
      ∫⁻ r in Ioi (0 : ℝ),
        B.indicator 1 (Γ.outgoingAtSpeed η (positiveSpeedOf r)) * ENNReal.ofReal r := by
  unfold boundaryFluxOut
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [Measure.map_apply (measurable_outgoingAtSpeed_left η) hB,
    ← lintegral_indicator_one ((measurable_outgoingAtSpeed_left η) hB),
    lintegral_speedFluxMeasure _ (measurable_one.indicator
      ((measurable_outgoingAtSpeed_left η) hB))]
  rfl

/-- On `(0, ∞)` the integrand of `boundaryFluxIn_apply` is literally `1_A(α^in_{η,r}) r`. -/
theorem incomingAtSpeed_positiveSpeedOf {v : Γ.Vertex} (η : Γ.IncidentEnds v) {r : ℝ}
    (hr : 0 < r) : Γ.incomingAtSpeed η (positiveSpeedOf r) = Γ.incomingAtSpeed η ⟨r, hr⟩ := by
  rw [positiveSpeedOf_of_pos hr]

/-- On `(0, ∞)` the integrand of `boundaryFluxOut_apply` is literally `1_B(α^out_{η,r}) r`. -/
theorem outgoingAtSpeed_positiveSpeedOf {v : Γ.Vertex} (η : Γ.IncidentEnds v) {r : ℝ}
    (hr : 0 < r) : Γ.outgoingAtSpeed η (positiveSpeedOf r) = Γ.outgoingAtSpeed η ⟨r, hr⟩ := by
  rw [positiveSpeedOf_of_pos hr]

/-- A sum over the finite edge-end factor of a fibre measure is the counting-product measure. -/
private theorem sum_map_eq_map_count_prod {v : Γ.Vertex} {X : Type*} [MeasurableSpace X]
    (φ : Γ.IncidentEnds v × PositiveSpeed → X) (hφ : Measurable φ) :
    ∑ η : Γ.IncidentEnds v, Measure.map (fun r => φ (η, r)) speedFluxMeasure =
      Measure.map φ (Measure.count.prod speedFluxMeasure) := by
  have hφη : ∀ η : Γ.IncidentEnds v, Measurable (fun r : PositiveSpeed => φ (η, r)) :=
    fun η => hφ.comp (measurable_const.prodMk measurable_id)
  ext A hA
  rw [Measure.coe_finsetSum, Finset.sum_apply, Measure.map_apply hφ hA,
    Measure.prod_apply (hφ hA), lintegral_fintype]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [Measure.map_apply (hφη η) hA, Measure.count_singleton, mul_one]
  rfl

/-- `μ_v^in` is the pushforward of `count × r dr` under the incoming speed chart: the incoming
flux measure in the form used by `map_scattering_speedFlux`. -/
theorem boundaryFluxIn_eq_map (v : Γ.Vertex) :
    Γ.boundaryFluxIn v =
      Measure.map (Γ.incomingSpeedChart v) (Measure.count.prod speedFluxMeasure) :=
  sum_map_eq_map_count_prod Γ (Γ.incomingSpeedChart v) (Γ.incomingSpeedChart v).measurable

/-- `μ_v^out` is the pushforward of `count × r dr` under the outgoing speed chart. -/
theorem boundaryFluxOut_eq_map (v : Γ.Vertex) :
    Γ.boundaryFluxOut v =
      Measure.map (Γ.outgoingSpeedChart v) (Measure.count.prod speedFluxMeasure) :=
  sum_map_eq_map_count_prod Γ (Γ.outgoingSpeedChart v) (Γ.outgoingSpeedChart v).measurable

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

namespace BorelEnergyPreservingScattering

variable (S : BorelEnergyPreservingScattering V)

/-- **Lemma III.7 (flux preservation)**, stated with the flux measures of Definition III.6:
every deterministic energy-preserving scattering law satisfies `(S_v)_# μ_v^in = μ_v^out`. -/
theorem map_scattering_boundaryFlux (v : Γ.Vertex) :
    Measure.map (S.map v) (Γ.boundaryFluxIn v) = Γ.boundaryFluxOut v := by
  rw [Γ.boundaryFluxIn_eq_map, Γ.boundaryFluxOut_eq_map]
  exact map_scattering_speedFlux V S v FiniteMetricGraph.speedFluxMeasure

end BorelEnergyPreservingScattering
end MechanicalPotential

end HamiltonianMetricGraphs
