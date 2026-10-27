/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.ScatterMap

/-!
# Lemma IV.4: the outgoing and the incoming quotient charts

The paper (Sec. IV) defines the positive and negative boundary representatives
```
P̃⁺ = P̃° ∪ ∐_v ∂⁻_v (outgoing covectors),     P̃⁻ = P̃° ∪ ∐_v ∂⁺_v (incoming covectors),
```
where `P̃° = ∐_e (0, ℓ_e) × ℝ` is the union of the open edge cylinders, and states

**Lemma IV.4 (Outgoing and incoming quotient charts).**  The restrictions
`π₊ = π|_{P̃⁺} : P̃⁺ → P_S` and `π₋ = π|_{P̃⁻} : P̃⁻ → P_S` are bimeasurable bijections.

`ScatterMap.lean` proves the outgoing half in the form
`outgoingChartMeasurableEquiv : ScatteringPhaseSpace S ≃ᵐ OutgoingRepresentativeSpace S`, where
`OutgoingRepresentativeSpace S` is the *complement of the incoming points*.  This file

* defines the two sets `P̃⁺` and `P̃⁻` literally, as printed (`positiveRepresentatives`,
  `negativeRepresentatives`: the interior points together with the outgoing, resp. incoming,
  boundary covectors), and proves that `OutgoingRepresentativeSpace S` is exactly `P̃⁺`;
* proves that `π₋` is a bimeasurable bijection (`negativeChart`, `incomingChartMeasurableEquiv`),
  following the printed proof: every scattering class meets `P̃⁻` exactly once, `π₋` is measurable
  by the definition of the quotient σ-algebra, and its inverse is measurable because the image
  `π(B)` of a Borel set `B ⊂ P̃⁻` is measurable (Lemma IV.2, `measurableSet_saturation`);
* packages both charts as `quotient_charts`.

The statement is about the scattering law `S` itself; no time reversal or momentum reversal is
used.
-/

namespace HamiltonianMetricGraphs

open Set

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-! ### The interior and the two boundary pieces of `P̃^×` -/

/-- A point of `P̃^×` lying in the open edge cylinder `P̃° = ∐_e (0, ℓ_e) × ℝ`. -/
def IsInteriorPoint (x : Γ.NonzeroPrequotientPhase) : Prop :=
  x.1.2.1.1 ∈ Ioo (0 : ℝ) (Γ.length x.1.1)

/-- A point of `P̃^×` which is an incoming boundary covector `(η, p) ∈ ∂⁺_v` for some vertex `v`. -/
def IsIncomingBoundaryPoint (x : Γ.NonzeroPrequotientPhase) : Prop :=
  ∃ (v : Γ.Vertex) (α : Γ.IncomingBoundary v), x = α.1.toNonzeroPrequotientPhase Γ

/-- A point of `P̃^×` which is an outgoing boundary covector `(η, p) ∈ ∂⁻_v` for some vertex `v`. -/
def IsOutgoingBoundaryPoint (x : Γ.NonzeroPrequotientPhase) : Prop :=
  ∃ (v : Γ.Vertex) (β : Γ.OutgoingBoundary v), x = β.1.toNonzeroPrequotientPhase Γ

/-- **The positive boundary representatives** `P̃⁺ = P̃° ∪ ∐_v ∂⁻_v` (Sec. IV), as printed: the
interior points together with the outgoing boundary covectors. -/
def positiveRepresentatives : Set Γ.NonzeroPrequotientPhase :=
  {x | Γ.IsInteriorPoint x ∨ Γ.IsOutgoingBoundaryPoint x}

/-- **The negative boundary representatives** `P̃⁻ = P̃° ∪ ∐_v ∂⁺_v` (Sec. IV), as printed: the
interior points together with the incoming boundary covectors. -/
def negativeRepresentatives : Set Γ.NonzeroPrequotientPhase :=
  {x | Γ.IsInteriorPoint x ∨ Γ.IsIncomingBoundaryPoint x}

theorem measurable_position :
    Measurable (fun x : Γ.NonzeroPrequotientPhase => x.1.2.1.1) :=
  MechanicalPotential.measurable_prequotientPosition.comp measurable_subtype_coe

theorem measurable_momentum :
    Measurable (fun x : Γ.NonzeroPrequotientPhase => x.1.2.1.2) :=
  MechanicalPotential.measurable_prequotientMomentum.comp measurable_subtype_coe

theorem measurable_edgeLength :
    Measurable (fun x : Γ.NonzeroPrequotientPhase => Γ.length x.1.1) :=
  MechanicalPotential.measurable_prequotientLength.comp measurable_subtype_coe

/-- The interior `P̃°` is a Borel subset of `P̃^×`. -/
theorem measurableSet_isInteriorPoint :
    MeasurableSet {x : Γ.NonzeroPrequotientPhase | Γ.IsInteriorPoint x} := by
  have h : {x : Γ.NonzeroPrequotientPhase | Γ.IsInteriorPoint x} =
      {x | (0 : ℝ) < x.1.2.1.1} ∩ {x | x.1.2.1.1 < Γ.length x.1.1} := by
    ext x; rfl
  rw [h]
  exact (measurableSet_lt measurable_const Γ.measurable_position).inter
    (measurableSet_lt Γ.measurable_position Γ.measurable_edgeLength)

/-- Closed-form description of the incoming boundary points: inward momentum at an endpoint. -/
theorem isIncomingBoundaryPoint_iff (x : Γ.NonzeroPrequotientPhase) :
    Γ.IsIncomingBoundaryPoint x ↔
      (x.1.2.1.1 = 0 ∧ x.1.2.1.2 < 0) ∨ (x.1.2.1.1 = Γ.length x.1.1 ∧ 0 < x.1.2.1.2) := by
  -- `IsIncomingPoint` of `QuotientPhaseSpace` is the same predicate; its parameters are unused.
  constructor
  · rintro ⟨v, ⟨⟨⟨e', b⟩, mom, hmom⟩, hv, hsign⟩, hxeq⟩
    have hval := congrArg Subtype.val hxeq
    have hcoord : x.1.2.1.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ (e', b) :=
      congrArg (fun z : Γ.PrequotientPhase => z.2.1.1) hval
    have hmomeq : x.1.2.1.2 = mom :=
      congrArg (fun z : Γ.PrequotientPhase => z.2.1.2) hval
    have hedge : x.1.1 = e' := congrArg Sigma.fst hval
    cases b
    · left
      refine ⟨by rw [hcoord]; rfl, ?_⟩
      rw [hmomeq]
      have hs : FiniteMetricGraph.EdgeEnd.sign Γ (e', false) = -1 := rfl
      rw [hs] at hsign; linarith
    · right
      refine ⟨by rw [hcoord, hedge]; rfl, ?_⟩
      rw [hmomeq]
      have hs : FiniteMetricGraph.EdgeEnd.sign Γ (e', true) = 1 := rfl
      rw [hs] at hsign; linarith
  · intro h
    obtain ⟨⟨e, ⟨⟨q, p⟩, hq⟩⟩, hp⟩ := x
    rcases h with ⟨hpos, hmom⟩ | ⟨hpos, hmom⟩
    · change q = 0 at hpos
      change p < 0 at hmom
      refine ⟨Γ.endpoint e false, ⟨⟨(e, false), p, hmom.ne⟩, rfl, ?_⟩, ?_⟩
      · change FiniteMetricGraph.EdgeEnd.sign Γ (e, false) * p > 0
        have hs : FiniteMetricGraph.EdgeEnd.sign Γ (e, false) = -1 := rfl
        rw [hs]; linarith
      · apply Subtype.ext
        subst hpos
        rfl
    · change q = Γ.length e at hpos
      change 0 < p at hmom
      refine ⟨Γ.endpoint e true, ⟨⟨(e, true), p, hmom.ne'⟩, rfl, ?_⟩, ?_⟩
      · change FiniteMetricGraph.EdgeEnd.sign Γ (e, true) * p > 0
        have hs : FiniteMetricGraph.EdgeEnd.sign Γ (e, true) = 1 := rfl
        rw [hs]; linarith
      · apply Subtype.ext
        subst hpos
        rfl

/-- Closed-form description of the outgoing boundary points: outward momentum at an endpoint. -/
theorem isOutgoingBoundaryPoint_iff (x : Γ.NonzeroPrequotientPhase) :
    Γ.IsOutgoingBoundaryPoint x ↔
      (x.1.2.1.1 = 0 ∧ 0 < x.1.2.1.2) ∨ (x.1.2.1.1 = Γ.length x.1.1 ∧ x.1.2.1.2 < 0) := by
  constructor
  · rintro ⟨v, ⟨⟨⟨e', b⟩, mom, hmom⟩, hv, hsign⟩, hxeq⟩
    have hval := congrArg Subtype.val hxeq
    have hcoord : x.1.2.1.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ (e', b) :=
      congrArg (fun z : Γ.PrequotientPhase => z.2.1.1) hval
    have hmomeq : x.1.2.1.2 = mom :=
      congrArg (fun z : Γ.PrequotientPhase => z.2.1.2) hval
    have hedge : x.1.1 = e' := congrArg Sigma.fst hval
    cases b
    · left
      refine ⟨by rw [hcoord]; rfl, ?_⟩
      rw [hmomeq]
      have hs : FiniteMetricGraph.EdgeEnd.sign Γ (e', false) = -1 := rfl
      rw [hs] at hsign; linarith
    · right
      refine ⟨by rw [hcoord, hedge]; rfl, ?_⟩
      rw [hmomeq]
      have hs : FiniteMetricGraph.EdgeEnd.sign Γ (e', true) = 1 := rfl
      rw [hs] at hsign; linarith
  · intro h
    obtain ⟨⟨e, ⟨⟨q, p⟩, hq⟩⟩, hp⟩ := x
    rcases h with ⟨hpos, hmom⟩ | ⟨hpos, hmom⟩
    · change q = 0 at hpos
      change 0 < p at hmom
      refine ⟨Γ.endpoint e false, ⟨⟨(e, false), p, hmom.ne'⟩, rfl, ?_⟩, ?_⟩
      · change FiniteMetricGraph.EdgeEnd.sign Γ (e, false) * p < 0
        have hs : FiniteMetricGraph.EdgeEnd.sign Γ (e, false) = -1 := rfl
        rw [hs]; linarith
      · apply Subtype.ext
        subst hpos
        rfl
    · change q = Γ.length e at hpos
      change p < 0 at hmom
      refine ⟨Γ.endpoint e true, ⟨⟨(e, true), p, hmom.ne⟩, rfl, ?_⟩, ?_⟩
      · change FiniteMetricGraph.EdgeEnd.sign Γ (e, true) * p < 0
        have hs : FiniteMetricGraph.EdgeEnd.sign Γ (e, true) = 1 := rfl
        rw [hs]; linarith
      · apply Subtype.ext
        subst hpos
        rfl

/-- The incoming boundary points form a Borel subset of `P̃^×`. -/
theorem measurableSet_isIncomingBoundaryPoint :
    MeasurableSet {x : Γ.NonzeroPrequotientPhase | Γ.IsIncomingBoundaryPoint x} := by
  have hset : {x : Γ.NonzeroPrequotientPhase | Γ.IsIncomingBoundaryPoint x} =
      ((fun x : Γ.NonzeroPrequotientPhase => x.1.2.1.1) ⁻¹' {0} ∩
        (fun x : Γ.NonzeroPrequotientPhase => x.1.2.1.2) ⁻¹' Set.Iio 0) ∪
      ((fun x : Γ.NonzeroPrequotientPhase => x.1.2.1.1 - Γ.length x.1.1) ⁻¹' {0} ∩
        (fun x : Γ.NonzeroPrequotientPhase => x.1.2.1.2) ⁻¹' Set.Ioi 0) := by
    ext x
    rw [Set.mem_setOf_eq, isIncomingBoundaryPoint_iff]
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_Iio, Set.mem_Ioi, sub_eq_zero]
  rw [hset]
  exact ((Γ.measurable_position (measurableSet_singleton 0)).inter
      (Γ.measurable_momentum measurableSet_Iio)).union
    (((Γ.measurable_position.sub Γ.measurable_edgeLength) (measurableSet_singleton 0)).inter
      (Γ.measurable_momentum measurableSet_Ioi))

/-- A boundary covector does not lie in the open edge cylinder. -/
theorem not_isInteriorPoint_covector (α : Γ.BoundaryCovector) :
    ¬ Γ.IsInteriorPoint (α.toNonzeroPrequotientPhase Γ) := by
  rintro ⟨h0, hl⟩
  rcases α with ⟨⟨e, b⟩, p, hp⟩
  cases b
  · exact lt_irrefl _ h0
  · exact lt_irrefl _ hl

theorem not_isInteriorPoint_of_isIncoming {x : Γ.NonzeroPrequotientPhase}
    (hx : Γ.IsIncomingBoundaryPoint x) : ¬ Γ.IsInteriorPoint x := by
  obtain ⟨v, α, rfl⟩ := hx
  exact Γ.not_isInteriorPoint_covector α.1

theorem not_isInteriorPoint_of_isOutgoing {x : Γ.NonzeroPrequotientPhase}
    (hx : Γ.IsOutgoingBoundaryPoint x) : ¬ Γ.IsInteriorPoint x := by
  obtain ⟨v, β, rfl⟩ := hx
  exact Γ.not_isInteriorPoint_covector β.1

/-- No point of `P̃^×` is both an incoming and an outgoing boundary covector. -/
theorem not_isOutgoing_of_isIncoming {x : Γ.NonzeroPrequotientPhase}
    (hx : Γ.IsIncomingBoundaryPoint x) : ¬ Γ.IsOutgoingBoundaryPoint x := by
  obtain ⟨v, α, rfl⟩ := hx
  rintro ⟨w, β, h⟩
  exact Γ.incoming_outgoing_nonzeroPrequotient_ne α β h

/-- **Trichotomy on `P̃^×`.**  Every point with the zero-momentum boundary points removed is an
interior point, an incoming boundary covector, or an outgoing boundary covector. -/
theorem isInterior_or_isIncoming_or_isOutgoing (x : Γ.NonzeroPrequotientPhase) :
    Γ.IsInteriorPoint x ∨ Γ.IsIncomingBoundaryPoint x ∨ Γ.IsOutgoingBoundaryPoint x := by
  by_cases hint : Γ.IsInteriorPoint x
  · exact Or.inl hint
  right
  have hq : x.1.2.1.1 ∈ Icc (0 : ℝ) (Γ.length x.1.1) := x.1.2.2
  have hbd : x.1.2.1.1 = 0 ∨ x.1.2.1.1 = Γ.length x.1.1 := by
    by_contra hne
    push Not at hne
    exact hint ⟨lt_of_le_of_ne hq.1 (Ne.symm hne.1), lt_of_le_of_ne hq.2 hne.2⟩
  have hp : x.1.2.1.2 ≠ 0 := NonzeroPrequotientPhase.momentum_ne_zero_of_boundary Γ x hbd
  rw [Γ.isIncomingBoundaryPoint_iff, Γ.isOutgoingBoundaryPoint_iff]
  rcases hbd with h | h <;> rcases lt_or_gt_of_ne hp with hp' | hp'
  · exact Or.inl (Or.inl ⟨h, hp'⟩)
  · exact Or.inr (Or.inl ⟨h, hp'⟩)
  · exact Or.inr (Or.inr ⟨h, hp'⟩)
  · exact Or.inl (Or.inr ⟨h, hp'⟩)

/-- The negative representatives `P̃⁻` form a Borel subset of `P̃^×`. -/
theorem measurableSet_negativeRepresentatives : MeasurableSet Γ.negativeRepresentatives :=
  Γ.measurableSet_isInteriorPoint.union Γ.measurableSet_isIncomingBoundaryPoint

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-- The incoming points of `QuotientPhaseSpace` are the incoming boundary covectors. -/
theorem isIncomingPoint_iff_isIncomingBoundaryPoint (x : Γ.NonzeroPrequotientPhase) :
    IsIncomingPoint V S x ↔ Γ.IsIncomingBoundaryPoint x := Iff.rfl

/-- **The formal outgoing section is the printed `P̃⁺`.**  `OutgoingRepresentativeSpace S`, defined
in `QuotientPhaseSpace` as the complement of the incoming points, is exactly
`P̃° ∪ ∐_v ∂⁻_v`. -/
theorem outgoingRepresentativeSpace_eq_positiveRepresentatives :
    OutgoingRepresentativeSpace V S = Γ.positiveRepresentatives := by
  ext x
  change ¬ Γ.IsIncomingBoundaryPoint x ↔ Γ.IsInteriorPoint x ∨ Γ.IsOutgoingBoundaryPoint x
  constructor
  · intro hx
    rcases Γ.isInterior_or_isIncoming_or_isOutgoing x with h | h | h
    · exact Or.inl h
    · exact absurd h hx
    · exact Or.inr h
  · rintro (h | h) hin
    · exact Γ.not_isInteriorPoint_of_isIncoming hin h
    · exact Γ.not_isOutgoing_of_isIncoming hin h

/-- The target of a scattering identification is an outgoing boundary covector. -/
theorem scatteringStep_target_isOutgoing {x y : Γ.NonzeroPrequotientPhase}
    (hxy : scatteringStep V S x y) : Γ.IsOutgoingBoundaryPoint y := by
  rcases hxy with ⟨v, α, -, hy⟩
  exact ⟨v, S.map v α, hy⟩

/-- A point of `P̃⁻` is never the target of a scattering identification. -/
theorem not_scatteringStep_to_negative {x y : Γ.NonzeroPrequotientPhase}
    (hy : y ∈ Γ.negativeRepresentatives) : ¬ scatteringStep V S x y := by
  intro hxy
  have hout := scatteringStep_target_isOutgoing V S hxy
  rcases hy with hy | hy
  · exact Γ.not_isInteriorPoint_of_isOutgoing hout hy
  · exact Γ.not_isOutgoing_of_isIncoming hy hout

/-- The restriction `π₋ = π|_{P̃⁻}` of the quotient map to the negative representatives. -/
def negativeRepresentativeMap :
    Γ.negativeRepresentatives → ScatteringPhaseSpace V S :=
  fun x => quotientMap V S x.1

/-- The restriction `π₊ = π|_{P̃⁺}` of the quotient map to the positive representatives. -/
def positiveRepresentativeMap :
    Γ.positiveRepresentatives → ScatteringPhaseSpace V S :=
  fun x => quotientMap V S x.1

/-- Each scattering class contains exactly one point of `P̃⁻`: `π₋` is a bijection. -/
theorem negativeRepresentativeMap_bijective :
    Function.Bijective (negativeRepresentativeMap V S) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    apply Subtype.ext
    have hrel : (scatteringSetoid V S) x y := Quotient.exact hxy
    rcases (scatteringEqv_iff_neighbor V S x y).mp hrel with h | h | h
    · exact h
    · exact absurd h (not_scatteringStep_to_negative V S hy)
    · exact absurd h (not_scatteringStep_to_negative V S hx)
  · intro z
    refine Quotient.inductionOn' z ?_
    intro x
    rcases Γ.isInterior_or_isIncoming_or_isOutgoing x with h | h | h
    · exact ⟨⟨x, Or.inl h⟩, rfl⟩
    · exact ⟨⟨x, Or.inr h⟩, rfl⟩
    · obtain ⟨v, β, hx⟩ := h
      let α : Γ.IncomingBoundary v := (S.map v).symm β
      have hstep : scatteringStep V S (α.1.toNonzeroPrequotientPhase Γ) x :=
        ⟨v, α, rfl, by rw [hx, MeasurableEquiv.apply_symm_apply]⟩
      exact ⟨⟨α.1.toNonzeroPrequotientPhase Γ, Or.inr ⟨v, α, rfl⟩⟩,
        Quotient.sound (Relation.EqvGen.rel _ _ hstep)⟩

/-- `π₋` is measurable (quotient σ-algebra). -/
theorem measurable_negativeRepresentativeMap :
    Measurable (negativeRepresentativeMap V S) :=
  (measurable_quotientMap V S).comp measurable_subtype_coe

/-- `π₋` maps Borel subsets of `P̃⁻` to measurable subsets of `P_S` (Lemma IV.2). -/
theorem measurableSet_image_negativeRepresentativeMap {B : Set Γ.negativeRepresentatives}
    (hB : MeasurableSet B) : MeasurableSet (negativeRepresentativeMap V S '' B) := by
  rw [measurableSet_quotient_iff]
  have himg : negativeRepresentativeMap V S '' B =
      quotientMap V S '' ((Subtype.val : Γ.negativeRepresentatives → _) '' B) := by
    rw [Set.image_image]; rfl
  rw [himg]
  exact measurableSet_saturation V S
    (MeasurableSet.subtype_image Γ.measurableSet_negativeRepresentatives hB)

/-- **The negative chart of Lemma IV.4.**  `π₋ = π|_{P̃⁻} : P̃⁻ → P_S` as a measurable
equivalence (a bimeasurable bijection); its underlying function is the restriction of the
quotient map (`negativeChart_apply`). -/
noncomputable def negativeChart : Γ.negativeRepresentatives ≃ᵐ ScatteringPhaseSpace V S where
  toEquiv := Equiv.ofBijective _ (negativeRepresentativeMap_bijective V S)
  measurable_toFun := measurable_negativeRepresentativeMap V S
  measurable_invFun := by
    intro A hA
    have h : (Equiv.ofBijective _ (negativeRepresentativeMap_bijective V S)).symm ⁻¹' A =
        negativeRepresentativeMap V S '' A := by
      rw [← Equiv.image_eq_preimage_symm]; rfl
    rw [h]
    exact measurableSet_image_negativeRepresentativeMap V S hA

@[simp] theorem negativeChart_apply (x : Γ.negativeRepresentatives) :
    negativeChart V S x = quotientMap V S x.1 := rfl

/-- The incoming representative space `P̃⁻ = P̃° ∪ ∐_v ∂⁺_v`, as a type, named in parallel to
`OutgoingRepresentativeSpace`. -/
abbrev IncomingRepresentativeSpace := (Γ.negativeRepresentatives : Type)

/-- **The incoming chart `j₋ = π₋⁻¹ : P_S ≃ᵐ P̃⁻` (Lemma IV.4)**, the counterpart of
`outgoingChartMeasurableEquiv`. -/
noncomputable def incomingChartMeasurableEquiv :
    ScatteringPhaseSpace V S ≃ᵐ IncomingRepresentativeSpace (Γ := Γ) :=
  (negativeChart V S).symm

/-- The incoming chart is the inverse of the restricted quotient map: `π (j₋ z) = z`. -/
theorem quotientMap_incomingChart (z : ScatteringPhaseSpace V S) :
    quotientMap V S (incomingChartMeasurableEquiv V S z).1 = z :=
  (negativeChart V S).apply_symm_apply z

/-- On a point of `P̃⁻`, the incoming chart returns that point: `j₋ (π x) = x`. -/
theorem incomingChart_quotientMap (x : Γ.negativeRepresentatives) :
    incomingChartMeasurableEquiv V S (quotientMap V S x.1) = x :=
  (negativeChart V S).symm_apply_apply x

/-- **The positive chart of Lemma IV.4.**  `π₊ = π|_{P̃⁺} : P̃⁺ → P_S`, with `P̃⁺` the printed set
`P̃° ∪ ∐_v ∂⁻_v`, as a measurable equivalence.  It is `outgoingChartMeasurableEquiv⁻¹`
transported along `OutgoingRepresentativeSpace S = P̃⁺`. -/
noncomputable def positiveChart : Γ.positiveRepresentatives ≃ᵐ ScatteringPhaseSpace V S where
  toEquiv := (Equiv.setCongr
      (outgoingRepresentativeSpace_eq_positiveRepresentatives V S).symm).trans
    (outgoingChart V S).symm
  measurable_toFun :=
    (outgoingChartMeasurableEquiv V S).symm.measurable.comp
      (measurable_subtype_coe.subtype_mk)
  measurable_invFun :=
    (measurable_subtype_coe.subtype_mk).comp (outgoingChartMeasurableEquiv V S).measurable

@[simp] theorem positiveChart_apply (x : Γ.positiveRepresentatives) :
    positiveChart V S x = quotientMap V S x.1 := by
  change (outgoingChart V S).symm _ = _
  rw [outgoingChart, Equiv.symm_symm]
  rfl

/-- **Lemma IV.4 (Outgoing and incoming quotient charts).**  The restrictions of the quotient map
`π : P̃^× → P_S` to the positive representatives `P̃⁺ = P̃° ∪ ∐_v ∂⁻_v` and to the negative
representatives `P̃⁻ = P̃° ∪ ∐_v ∂⁺_v` are bimeasurable bijections: each is the underlying
function of a measurable equivalence onto the scattering phase space. -/
theorem quotient_charts :
    (∃ chartPlus : Γ.positiveRepresentatives ≃ᵐ ScatteringPhaseSpace V S,
        ∀ x, chartPlus x = quotientMap V S x.1) ∧
    (∃ chartMinus : Γ.negativeRepresentatives ≃ᵐ ScatteringPhaseSpace V S,
        ∀ x, chartMinus x = quotientMap V S x.1) :=
  ⟨⟨positiveChart V S, positiveChart_apply V S⟩, ⟨negativeChart V S, negativeChart_apply V S⟩⟩

/-- Lemma IV.4 in the explicit form "bijective, measurable, measurable inverse" for the two
restrictions `π₊ = positiveRepresentativeMap` and `π₋ = negativeRepresentativeMap`. -/
theorem quotient_charts_bimeasurable :
    (Function.Bijective (positiveRepresentativeMap V S) ∧
        Measurable (positiveRepresentativeMap V S) ∧
        ∀ B : Set Γ.positiveRepresentatives, MeasurableSet B →
          MeasurableSet (positiveRepresentativeMap V S '' B)) ∧
    (Function.Bijective (negativeRepresentativeMap V S) ∧
        Measurable (negativeRepresentativeMap V S) ∧
        ∀ B : Set Γ.negativeRepresentatives, MeasurableSet B →
          MeasurableSet (negativeRepresentativeMap V S '' B)) := by
  have hpos : positiveRepresentativeMap V S = positiveChart V S :=
    funext fun x => (positiveChart_apply V S x).symm
  have hneg : negativeRepresentativeMap V S = negativeChart V S :=
    funext fun x => (negativeChart_apply V S x).symm
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [hpos]; exact (positiveChart V S).bijective
  · rw [hpos]; exact (positiveChart V S).measurable
  · intro B hB; rw [hpos]; exact (positiveChart V S).measurableEmbedding.measurableSet_image.mpr hB
  · rw [hneg]; exact (negativeChart V S).bijective
  · rw [hneg]; exact (negativeChart V S).measurable
  · intro B hB; rw [hneg]; exact (negativeChart V S).measurableEmbedding.measurableSet_image.mpr hB

end MechanicalPotential

end HamiltonianMetricGraphs
