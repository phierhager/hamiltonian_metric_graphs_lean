/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ChannelKernel
import HamiltonianMetricGraphs.VertexLawExact

/-!
# Proposition X.7 (coarse-graining) as printed

For a microscopic junction let `ξ ∈ Ξ` be the unresolved transverse data and
`C_v(η, r, ξ) ∈ E_v^∂` the outgoing end for the incoming end `η` and the longitudinal speed `r`.
Given a probability measure `μ` on `Ξ` the coarse-grained law is

  `P_v(ζ ∣ η, r) = μ {ξ : C_v(η, r, ξ) = ζ}`     (X.5)

(`vertexChannelKernel`; it is the `channelKernel` of `ChannelKernel.lean` for the map
`ξ ↦ C_v(η, r, ξ)`, `vertexChannelKernel_eq_channelKernel`).  **Proposition X.7**: if
`ξ ↦ C_v(η, r, ξ)` is measurable for every `(η, r)`, then

* (a) `P_v(· ∣ η, r)` is a probability distribution (`sum_vertexChannelKernel`), so the matrix
  `channelMatrix μ C r` of these distributions is a Markov vertex law
  (`isMarkovVertexLaw_channelMatrix`);
* (b) it is the Dirac mass at `ζ` iff `C_v(η, r, ξ) = ζ` for `μ`-a.e. `ξ`
  (`isDiracRow_iff_ae`; as measures, `map_eq_dirac_iff_ae`);
* (c) if every incoming end yields a Dirac distribution, these define a unique routing map
  `F_v(·, r)`; it is a permutation iff the resulting Markov matrix preserves the end flux
  (`routing_bijective_iff_preservesGermCounting`), and then the matrix is the deterministic vertex
  law of a Borel deterministic scattering structure (`channelMatrix_mem_borelSpeedMatrices`);
* (d) if two distinct outgoing ends have positive probability for the same incoming state, the
  law is genuinely probabilistic: not a Dirac mass at any end (`not_isDiracRow_of_two_pos`).

`coarse_graining` packages (a)–(d).  `ChannelKernel.channelKernel_eq_dirac_iff` adds the
converse of (b) for the edge-end-valued `channelKernel` of `ChannelKernel.lean`.
-/

namespace HamiltonianMetricGraphs

open MeasureTheory Set FiniteMetricGraph
open scoped ENNReal

/-! ### The converse of the Dirac criterion for `channelKernel` -/

namespace ChannelKernel

variable {Γ : FiniteMetricGraph} {Ξ : Type*} [MeasurableSpace Ξ]

/-- A fibre of full probability is almost sure. -/
theorem ae_eq_of_channelKernel_eq_one (μ : Measure Ξ) [IsProbabilityMeasure μ]
    {C : Ξ → Γ.EdgeEnd} {ζ₀ : Γ.EdgeEnd} (hmeas : MeasurableSet {ξ | C ξ = ζ₀})
    (h : channelKernel μ C ζ₀ = 1) : ∀ᵐ ξ ∂μ, C ξ = ζ₀ := by
  rw [ae_iff]
  have := (prob_compl_eq_zero_iff hmeas).mpr h
  exact this

/-- **Proposition X.7 (b) for `channelKernel`.**  With measurable fibres, the kernel is the Dirac
mass at `ζ₀` iff the channel map equals `ζ₀` almost surely. -/
theorem channelKernel_eq_dirac_iff (μ : Measure Ξ) [IsProbabilityMeasure μ] {C : Ξ → Γ.EdgeEnd}
    (hmeas : ∀ ζ, MeasurableSet {ξ | C ξ = ζ}) (ζ₀ : Γ.EdgeEnd) :
    (∀ ζ, channelKernel μ C ζ = if ζ = ζ₀ then 1 else 0) ↔ ∀ᵐ ξ ∂μ, C ξ = ζ₀ := by
  constructor
  · intro h
    exact ae_eq_of_channelKernel_eq_one μ (hmeas ζ₀) (by rw [h ζ₀, if_pos rfl])
  · exact fun h => channelKernel_of_ae_eq μ h

end ChannelKernel

/-! ### The coarse-grained vertex law -/

namespace CoarseGraining

variable {Γ : FiniteMetricGraph} {v : Γ.Vertex} {Ξ : Type*} [MeasurableSpace Ξ]

/-- **The coarse-grained law (X.5)**: `P_v(ζ ∣ η, r) = μ {ξ : C_v(η, r, ξ) = ζ}`. -/
noncomputable def vertexChannelKernel (μ : Measure Ξ)
    (C : Γ.IncidentEnds v → PositiveSpeed → Ξ → Γ.IncidentEnds v)
    (η : Γ.IncidentEnds v) (r : PositiveSpeed) (ζ : Γ.IncidentEnds v) : ℝ≥0∞ :=
  μ {ξ | C η r ξ = ζ}

/-- `P_v(· ∣ η, r)` is the `channelKernel` of `ξ ↦ C_v(η, r, ξ)`, read as an edge-end. -/
theorem vertexChannelKernel_eq_channelKernel (μ : Measure Ξ)
    (C : Γ.IncidentEnds v → PositiveSpeed → Ξ → Γ.IncidentEnds v)
    (η : Γ.IncidentEnds v) (r : PositiveSpeed) (ζ : Γ.IncidentEnds v) :
    vertexChannelKernel μ C η r ζ = ChannelKernel.channelKernel μ (fun ξ => (C η r ξ).1) ζ.1 := by
  unfold vertexChannelKernel ChannelKernel.channelKernel
  congr 1
  ext ξ
  exact Subtype.ext_iff

/-- The Markov matrix of the coarse-grained law at the speed `r`. -/
noncomputable def channelMatrix (μ : Measure Ξ)
    (C : Γ.IncidentEnds v → PositiveSpeed → Ξ → Γ.IncidentEnds v) (r : PositiveSpeed) :
    Matrix (Γ.IncidentEnds v) (Γ.IncidentEnds v) ℝ :=
  Matrix.of fun η ζ => (vertexChannelKernel μ C η r ζ).toReal

/-- `P_v(· ∣ η, r)` is the Dirac mass at `ζ₀`. -/
def IsDiracRow (μ : Measure Ξ) (C : Γ.IncidentEnds v → PositiveSpeed → Ξ → Γ.IncidentEnds v)
    (η : Γ.IncidentEnds v) (r : PositiveSpeed) (ζ₀ : Γ.IncidentEnds v) : Prop :=
  ∀ ζ, vertexChannelKernel μ C η r ζ = if ζ = ζ₀ then 1 else 0

omit [MeasurableSpace Ξ] in
theorem ends_ext_iff {a b : Γ.IncidentEnds v} : a = b ↔ a.1 = b.1 := Subtype.ext_iff

variable (μ : Measure Ξ) [IsProbabilityMeasure μ]
  (C : Γ.IncidentEnds v → PositiveSpeed → Ξ → Γ.IncidentEnds v)

theorem measurableSet_fiber (hC : ∀ η r, Measurable (C η r)) (η : Γ.IncidentEnds v)
    (r : PositiveSpeed) (ζ : Γ.IncidentEnds v) : MeasurableSet {ξ | C η r ξ = ζ} :=
  hC η r (MeasurableSet.of_discrete (s := {ζ}))

/-- **Proposition X.7 (a).**  `P_v(· ∣ η, r)` is a probability distribution on `E_v^∂`. -/
theorem sum_vertexChannelKernel (hC : ∀ η r, Measurable (C η r)) (η : Γ.IncidentEnds v)
    (r : PositiveSpeed) : ∑ ζ, vertexChannelKernel μ C η r ζ = 1 := by
  have h := sum_measure_preimage_singleton (μ := μ) (Finset.univ : Finset (Γ.IncidentEnds v))
    (f := C η r) fun ζ _ => measurableSet_fiber C hC η r ζ
  rw [Finset.coe_univ, Set.preimage_univ, measure_univ] at h
  exact h

theorem vertexChannelKernel_ne_top (η : Γ.IncidentEnds v) (r : PositiveSpeed)
    (ζ : Γ.IncidentEnds v) : vertexChannelKernel μ C η r ζ ≠ ∞ :=
  measure_ne_top μ _

/-- **Proposition X.7 (a), matrix form.**  The coarse-grained law is a Markov vertex law. -/
theorem isMarkovVertexLaw_channelMatrix (hC : ∀ η r, Measurable (C η r)) (r : PositiveSpeed) :
    MechanicalPotential.IsMarkovVertexLaw (channelMatrix μ C r) := by
  refine ⟨fun η ζ => ENNReal.toReal_nonneg, fun η => ?_⟩
  simp only [channelMatrix, Matrix.of_apply]
  rw [← ENNReal.toReal_sum fun ζ _ => vertexChannelKernel_ne_top μ C η r ζ,
    sum_vertexChannelKernel μ C hC η r, ENNReal.toReal_one]

/-- **Proposition X.7 (b).**  `P_v(· ∣ η, r)` is the Dirac mass at `ζ₀` iff
`C_v(η, r, ξ) = ζ₀` for `μ`-almost every `ξ`. -/
theorem isDiracRow_iff_ae (hC : ∀ η r, Measurable (C η r)) (η : Γ.IncidentEnds v)
    (r : PositiveSpeed) (ζ₀ : Γ.IncidentEnds v) :
    IsDiracRow μ C η r ζ₀ ↔ ∀ᵐ ξ ∂μ, C η r ξ = ζ₀ := by
  have hae : (∀ᵐ ξ ∂μ, C η r ξ = ζ₀) ↔ ∀ᵐ ξ ∂μ, (C η r ξ).1 = ζ₀.1 :=
    Filter.eventually_congr (Filter.Eventually.of_forall fun ξ => Subtype.ext_iff)
  rw [hae, ← ChannelKernel.channelKernel_eq_dirac_iff μ (C := fun ξ => (C η r ξ).1) ?_ ζ₀.1]
  · constructor
    · intro h ζ
      by_cases hζ : ζ.vertex = v
      · have := h ⟨ζ, hζ⟩
        rw [vertexChannelKernel_eq_channelKernel] at this
        rw [this]
        by_cases h' : ζ = ζ₀.1
        · rw [if_pos (ends_ext_iff.mpr h'), if_pos h']
        · rw [if_neg (fun e => h' (ends_ext_iff.mp e)), if_neg h']
      · have hne : ζ ≠ ζ₀.1 := fun h' => hζ (h' ▸ ζ₀.2)
        rw [if_neg hne]
        refine measure_mono_null (fun ξ hξ => ?_) (measure_empty (μ := μ))
        exact hζ (hξ ▸ (C η r ξ).2)
    · intro h ζ
      rw [vertexChannelKernel_eq_channelKernel, h ζ.1]
      by_cases h' : ζ = ζ₀
      · rw [if_pos h', if_pos (ends_ext_iff.mp h')]
      · rw [if_neg h', if_neg (fun e => h' (ends_ext_iff.mpr e))]
  · intro ζ
    by_cases hζ : ζ.vertex = v
    · have : {ξ | (C η r ξ).1 = ζ} = {ξ | C η r ξ = ⟨ζ, hζ⟩} := by
        ext ξ
        exact ⟨fun h' => ends_ext_iff.mpr h', fun h' => congrArg Subtype.val h'⟩
      rw [this]
      exact measurableSet_fiber C hC η r _
    · have : {ξ | (C η r ξ).1 = ζ} = ∅ := by
        ext ξ
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
        exact fun h' => hζ (h' ▸ (C η r ξ).2)
      rw [this]
      exact MeasurableSet.empty

/-- **Proposition X.7 (b), as measures.**  The law of the outgoing end under `μ` is `δ_{ζ₀}` iff
`C_v(η, r, ξ) = ζ₀` for `μ`-almost every `ξ`. -/
theorem map_eq_dirac_iff_ae (hC : ∀ η r, Measurable (C η r)) (η : Γ.IncidentEnds v)
    (r : PositiveSpeed) (ζ₀ : Γ.IncidentEnds v) :
    μ.map (C η r) = Measure.dirac ζ₀ ↔ ∀ᵐ ξ ∂μ, C η r ξ = ζ₀ := by
  classical
  rw [← isDiracRow_iff_ae μ C hC η r ζ₀]
  constructor
  · intro h ζ
    have := congrArg (fun m : Measure (Γ.IncidentEnds v) => m {ζ}) h
    simp only [Measure.map_apply (hC η r) (MeasurableSet.of_discrete (s := {ζ})),
      Measure.dirac_apply' _ (MeasurableSet.of_discrete (s := {ζ}))] at this
    unfold vertexChannelKernel
    rw [show {ξ | C η r ξ = ζ} = C η r ⁻¹' {ζ} from rfl, this]
    by_cases hζ : ζ = ζ₀
    · simp [hζ]
    · simp [hζ, Ne.symm hζ]
  · intro h
    have h' : ∀ ζ, vertexChannelKernel μ C η r ζ = if ζ = ζ₀ then 1 else 0 := h
    ext s hs
    rw [Measure.map_apply (hC η r) hs, Measure.dirac_apply' _ hs]
    have hsum := sum_measure_preimage_singleton (μ := μ) (f := C η r) (s.toFinite.toFinset)
      fun ζ _ => measurableSet_fiber C hC η r ζ
    rw [Set.Finite.coe_toFinset] at hsum
    rw [← hsum]
    simp only [show ∀ ζ, C η r ⁻¹' {ζ} = {ξ | C η r ξ = ζ} from fun _ => rfl]
    simp only [show ∀ ζ, μ {ξ | C η r ξ = ζ} = vertexChannelKernel μ C η r ζ from fun _ => rfl,
      h', Finset.sum_ite_eq', Set.Finite.mem_toFinset]
    by_cases hs0 : ζ₀ ∈ s <;> simp [hs0]

omit [IsProbabilityMeasure μ] in
/-- The Dirac mass of a row is unique. -/
theorem isDiracRow_unique {η : Γ.IncidentEnds v} {r : PositiveSpeed} {ζ₀ ζ₁ : Γ.IncidentEnds v}
    (h₀ : IsDiracRow μ C η r ζ₀) (h₁ : IsDiracRow μ C η r ζ₁) : ζ₀ = ζ₁ := by
  have := h₁ ζ₀
  rw [h₀ ζ₀, if_pos rfl] at this
  by_contra hne
  rw [if_neg hne] at this
  exact one_ne_zero this

omit [IsProbabilityMeasure μ] in
/-- On a Dirac row the matrix entries are `0/1`: `P_v(ζ ∣ η, r) = 1` iff `ζ = F_v(η, r)`. -/
theorem channelMatrix_of_isDiracRow {η : Γ.IncidentEnds v} {r : PositiveSpeed}
    {ζ₀ : Γ.IncidentEnds v} (h : IsDiracRow μ C η r ζ₀) (ζ : Γ.IncidentEnds v) :
    channelMatrix μ C r η ζ = if ζ₀ = ζ then 1 else 0 := by
  simp only [channelMatrix, Matrix.of_apply, h ζ]
  by_cases hζ : ζ = ζ₀
  · rw [if_pos hζ, if_pos hζ.symm, ENNReal.toReal_one]
  · rw [if_neg hζ, if_neg (Ne.symm hζ), ENNReal.toReal_zero]

omit [IsProbabilityMeasure μ] in
/-- **Proposition X.7 (c).**  If every incoming end yields a Dirac distribution, these
distributions define a unique routing map `F_v(·, r)`; the Markov matrix is its `0/1` matrix, and
`F_v(·, r)` is a permutation iff the matrix preserves the end flux. -/
theorem routing_bijective_iff_preservesGermCounting (r : PositiveSpeed)
    (hdirac : ∀ η, ∃ ζ₀, IsDiracRow μ C η r ζ₀) :
    ∃! F : Γ.IncidentEnds v → Γ.IncidentEnds v,
      (∀ η, IsDiracRow μ C η r (F η)) ∧
      (∀ η ζ, channelMatrix μ C r η ζ = if F η = ζ then 1 else 0) ∧
      (Function.Bijective F ↔ MechanicalPotential.PreservesGermCounting (channelMatrix μ C r)) := by
  classical
  choose F hF using hdirac
  have hmat : ∀ η ζ, channelMatrix μ C r η ζ = if F η = ζ then 1 else 0 :=
    fun η ζ => channelMatrix_of_isDiracRow μ C (hF η) ζ
  refine ⟨F, ⟨hF, hmat, ?_⟩, fun G hG => funext fun η => isDiracRow_unique μ C (hG.1 η) (hF η)⟩
  rw [← sum_ite_eq_one_iff_bijective F, MechanicalPotential.PreservesGermCounting]
  exact forall_congr' fun ζ => by simp only [hmat]

omit [IsProbabilityMeasure μ] in
/-- **Proposition X.7 (c), together with Theorem X.4.**  When the routing map is a permutation,
the coarse-grained matrix is the deterministic vertex law of a Borel deterministic scattering
structure. -/
theorem channelMatrix_mem_borelSpeedMatrices (V : MechanicalPotential Γ) (r : PositiveSpeed)
    {F : Γ.IncidentEnds v → Γ.IncidentEnds v} (hF : ∀ η, IsDiracRow μ C η r (F η))
    (hbij : Function.Bijective F) : channelMatrix μ C r ∈ V.borelSpeedMatrices v r := by
  classical
  rw [V.borelSpeedMatrices_eq v r]
  refine ⟨Equiv.ofBijective F hbij, ?_⟩
  ext η ζ
  rw [permMatrix_apply', channelMatrix_of_isDiracRow μ C (hF η) ζ]
  rfl

omit [IsProbabilityMeasure μ] in
/-- **Proposition X.7 (d).**  If two distinct outgoing ends have positive probability for the
same incoming state, the law is genuinely probabilistic: it is not a Dirac mass at any end. -/
theorem not_isDiracRow_of_two_pos {η : Γ.IncidentEnds v} {r : PositiveSpeed}
    {ζ₁ ζ₂ : Γ.IncidentEnds v} (hne : ζ₁ ≠ ζ₂) (h₁ : 0 < vertexChannelKernel μ C η r ζ₁)
    (h₂ : 0 < vertexChannelKernel μ C η r ζ₂) (ζ₀ : Γ.IncidentEnds v) :
    ¬ IsDiracRow μ C η r ζ₀ := by
  intro hdirac
  by_cases h : ζ₁ = ζ₀
  · have hz : ζ₂ ≠ ζ₀ := by rw [← h]; exact fun hc => hne hc.symm
    rw [hdirac ζ₂, if_neg hz] at h₂
    exact lt_irrefl 0 h₂
  · rw [hdirac ζ₁, if_neg h] at h₁
    exact lt_irrefl 0 h₁

/-- **Proposition X.7 (coarse-graining).**  Let `μ` be a probability measure on the unresolved
data and let `ξ ↦ C_v(η, r, ξ)` be measurable for every `(η, r)`.  Then
(a) `P_v(· ∣ η, r)` is a probability distribution;
(b) it is the Dirac mass at `ζ` iff `C_v(η, r, ξ) = ζ` for `μ`-almost every `ξ`;
(c) if every incoming end yields a Dirac distribution, these define a (unique) deterministic
    routing map `F_v(·, r)`, the Markov matrix is its `0/1` matrix, and `F_v(·, r)` is a
    permutation iff the Markov matrix preserves the end flux;
(d) if two distinct outgoing ends have positive probability for the same incoming state, the
    law is not a Dirac mass, i.e. genuinely probabilistic. -/
theorem coarse_graining (hC : ∀ η r, Measurable (C η r)) :
    (∀ η r, ∑ ζ, vertexChannelKernel μ C η r ζ = 1) ∧
    (∀ η r ζ₀, IsDiracRow μ C η r ζ₀ ↔ ∀ᵐ ξ ∂μ, C η r ξ = ζ₀) ∧
    (∀ r, (∀ η, ∃ ζ₀, IsDiracRow μ C η r ζ₀) →
      ∃! F : Γ.IncidentEnds v → Γ.IncidentEnds v,
        (∀ η, IsDiracRow μ C η r (F η)) ∧
        (∀ η ζ, channelMatrix μ C r η ζ = if F η = ζ then 1 else 0) ∧
        (Function.Bijective F ↔
          MechanicalPotential.PreservesGermCounting (channelMatrix μ C r))) ∧
    (∀ η r ζ₁ ζ₂, ζ₁ ≠ ζ₂ → 0 < vertexChannelKernel μ C η r ζ₁ →
      0 < vertexChannelKernel μ C η r ζ₂ → ∀ ζ₀, ¬ IsDiracRow μ C η r ζ₀) :=
  ⟨sum_vertexChannelKernel μ C hC, isDiracRow_iff_ae μ C hC,
    fun r hdirac => routing_bijective_iff_preservesGermCounting μ C r hdirac,
    fun _ _ _ _ hne h₁ h₂ ζ₀ => not_isDiracRow_of_two_pos μ C hne h₁ h₂ ζ₀⟩

end CoarseGraining

end HamiltonianMetricGraphs
