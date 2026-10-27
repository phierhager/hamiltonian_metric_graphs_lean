/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.ScatteringExact

/-!
# Examples III.8 and III.9: permutation laws

A permutation `σ` of the edge-ends at `v` defines the speed-independent vertex law
`α^in_{η,r} ↦ α^out_{σ η,r}` (`permutationLaw`).  It is an energy-preserving Borel isomorphism,
and by Lemma III.5 it is reversible exactly when `σ` is an involution.

* **Example III.8 ("Basic reversible laws").**  Reflection `F_v(η,r) = η` is the law of the
  identity permutation; it is momentum reversal itself (`reflectionLaw_apply`).  Transmission
  through a two-valent vertex is the law of the transposition of its two edge-ends.  Both are
  reversible energy-preserving Borel laws.  A reversible law is, at each fixed speed, a product of
  fixed points and transpositions (`cycleType_speedPermutation_of_isReversibleAt`), and a
  nonreflecting reversible law exists only at even valence
  (`even_card_of_isReversibleAt_of_nonreflecting`).
* **Example III.9 ("A nonreversible cyclic law").**  At three distinct edge-ends
  `η₁, η₂, η₃` the cyclic law `F_v(η₁,r) = η₂`, `F_v(η₂,r) = η₃`, `F_v(η₃,r) = η₁` is an
  energy-preserving Borel law which is not reversible (`not_isReversibleAt_cyclicLaw`); more
  generally, so is the law of any cycle of length `≥ 3`.  The construction of the scattered flow
  takes an arbitrary `BorelEnergyPreservingScattering`, so it applies to
  `permutationScattering` with a cyclic law at a vertex, which is not reversible.
-/

namespace HamiltonianMetricGraphs

open FiniteMetricGraph (PositiveSpeed)

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- A permutation of the (finite, discrete) edge-ends at `v`, as a Borel automorphism. -/
noncomputable def incidentPermMeasurableEquiv {v : Γ.Vertex}
    (σ : Equiv.Perm (Γ.IncidentEnds v)) : Γ.IncidentEnds v ≃ᵐ Γ.IncidentEnds v where
  toEquiv := σ
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := Measurable.of_discrete

/-- The speed-independent vertex law of a permutation `σ` of the edge-ends at `v`:
`α^in_{η,r} ↦ α^out_{σ η,r}`, as a Borel isomorphism `D^in_v → D^out_v`. -/
noncomputable def permutationLaw (v : Γ.Vertex) (σ : Equiv.Perm (Γ.IncidentEnds v)) :
    Γ.IncomingBoundary v ≃ᵐ Γ.OutgoingBoundary v :=
  (Γ.incomingSpeedChart v).symm.trans
    ((MeasurableEquiv.prodCongr (Γ.incidentPermMeasurableEquiv σ) (MeasurableEquiv.refl _)).trans
      (Γ.outgoingSpeedChart v))

variable {Γ}

@[simp] theorem permutationLaw_incomingAtSpeed {v : Γ.Vertex}
    (σ : Equiv.Perm (Γ.IncidentEnds v)) (η : Γ.IncidentEnds v) (r : PositiveSpeed) :
    Γ.permutationLaw v σ (Γ.incomingAtSpeed η r) = Γ.outgoingAtSpeed (σ η) r := by
  simp only [permutationLaw, MeasurableEquiv.trans_apply,
    incomingSpeedChart_symm_incomingAtSpeed]
  rfl

/-- The speed representation of a permutation law is `F_v(η,r) = σ η`. -/
theorem isSpeedRepresentation_permutationLaw {v : Γ.Vertex}
    (σ : Equiv.Perm (Γ.IncidentEnds v)) :
    Γ.IsSpeedRepresentation (Γ.permutationLaw v σ) (fun η _ => σ η) :=
  fun η r => permutationLaw_incomingAtSpeed σ η r

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- A permutation law is energy-preserving. -/
theorem isEnergyPreservingAt_permutationLaw {v : Γ.Vertex}
    (σ : Equiv.Perm (Γ.IncidentEnds v)) :
    V.IsEnergyPreservingAt v (Γ.permutationLaw v σ) :=
  isEnergyPreservingAt_of_isSpeedRepresentation
    (FiniteMetricGraph.isSpeedRepresentation_permutationLaw σ)

/-- A permutation law is reversible (Definition III.4) iff the permutation is an involution. -/
theorem isReversibleAt_permutationLaw_iff {v : Γ.Vertex} (σ : Equiv.Perm (Γ.IncidentEnds v)) :
    IsReversibleAt (Γ.permutationLaw v σ).toEquiv ↔ Function.Involutive σ := by
  rw [isReversibleAt_iff_involutive (Γ.permutationLaw v σ).toEquiv
    (FiniteMetricGraph.isSpeedRepresentation_permutationLaw σ)]
  exact ⟨fun h => h ⟨1, Set.mem_Ioi.mpr one_pos⟩, fun h _ => h⟩

/-- A Borel energy-preserving scattering structure given by one permutation law per vertex. -/
noncomputable def permutationScattering (σ : ∀ v : Γ.Vertex, Equiv.Perm (Γ.IncidentEnds v)) :
    BorelEnergyPreservingScattering V where
  map v := Γ.permutationLaw v (σ v)
  preserves_energy v := V.isEnergyPreservingAt_permutationLaw (σ v)

/-- The scattering structure of permutation laws is reversible iff every permutation is an
involution. -/
theorem permutationScattering_isReversible_iff
    (σ : ∀ v : Γ.Vertex, Equiv.Perm (Γ.IncidentEnds v)) :
    (V.permutationScattering σ).toEnergyPreservingScattering.IsReversible ↔
      ∀ v, Function.Involutive (σ v) := by
  rw [EnergyPreservingScattering.isReversible_iff_forall_isReversibleAt]
  exact forall_congr' fun v => isReversibleAt_permutationLaw_iff (σ v)

/-! ### Example III.8: reflection and transmission -/

/-- **Reflection** (Example III.8): the law with `F_v(η,r) = η`. -/
noncomputable def reflectionLaw (v : Γ.Vertex) : Γ.IncomingBoundary v ≃ᵐ Γ.OutgoingBoundary v :=
  Γ.permutationLaw v 1

/-- Reflection is momentum reversal: `α ↦ ρ̃ α`. -/
theorem reflectionLaw_apply (v : Γ.Vertex) (α : Γ.IncomingBoundary v) :
    reflectionLaw v α = Γ.incomingMomentumReversal v α := by
  rw [← (Γ.incomingSpeedChart v).apply_symm_apply α]
  obtain ⟨η, r⟩ := (Γ.incomingSpeedChart v).symm α
  simp [reflectionLaw]

/-- **Example III.8, reflection.**  The reflection law has speed representation
`F_v(η,r) = η`, is an energy-preserving Borel isomorphism, and is reversible. -/
theorem reflectionLaw_spec (v : Γ.Vertex) :
    Γ.IsSpeedRepresentation (reflectionLaw v) (fun η _ => η) ∧
      V.IsEnergyPreservingAt v (reflectionLaw v) ∧
      Measurable (reflectionLaw v) ∧ Measurable (reflectionLaw v).symm ∧
      IsReversibleAt (reflectionLaw v).toEquiv :=
  ⟨FiniteMetricGraph.isSpeedRepresentation_permutationLaw 1,
    V.isEnergyPreservingAt_permutationLaw 1, (reflectionLaw v).measurable,
    (reflectionLaw v).symm.measurable,
    (isReversibleAt_permutationLaw_iff 1).mpr fun _ => rfl⟩

/-- **Transmission** (Example III.8): the law of the transposition of two edge-ends. -/
noncomputable def transmissionLaw {v : Γ.Vertex} (η₁ η₂ : Γ.IncidentEnds v) :
    Γ.IncomingBoundary v ≃ᵐ Γ.OutgoingBoundary v :=
  Γ.permutationLaw v (Equiv.swap η₁ η₂)

/-- **Example III.8, transmission.**  The transposition law of two edge-ends `η₁, η₂` at `v`
sends `α^in_{η₁,r}` to `α^out_{η₂,r}` and `α^in_{η₂,r}` to `α^out_{η₁,r}`; it is an
energy-preserving Borel isomorphism and it is reversible. -/
theorem transmissionLaw_spec {v : Γ.Vertex} (η₁ η₂ : Γ.IncidentEnds v) :
    (∀ r : PositiveSpeed, transmissionLaw η₁ η₂ (Γ.incomingAtSpeed η₁ r) =
        Γ.outgoingAtSpeed η₂ r ∧
      transmissionLaw η₁ η₂ (Γ.incomingAtSpeed η₂ r) = Γ.outgoingAtSpeed η₁ r) ∧
      V.IsEnergyPreservingAt v (transmissionLaw η₁ η₂) ∧
      Measurable (transmissionLaw η₁ η₂) ∧ Measurable (transmissionLaw η₁ η₂).symm ∧
      IsReversibleAt (transmissionLaw η₁ η₂).toEquiv := by
  refine ⟨fun r => ?_, V.isEnergyPreservingAt_permutationLaw _,
    (transmissionLaw η₁ η₂).measurable, (transmissionLaw η₁ η₂).symm.measurable,
    (isReversibleAt_permutationLaw_iff _).mpr (Equiv.swap_apply_self η₁ η₂)⟩
  simp [transmissionLaw]

/-- At a two-valent vertex the transmission law reflects nothing: `F_v(η,r) ≠ η` for every
edge-end `η` at `v`. -/
theorem transmissionLaw_nonreflecting {v : Γ.Vertex} {η₁ η₂ : Γ.IncidentEnds v}
    (hne : η₁ ≠ η₂) (hval : ∀ η : Γ.IncidentEnds v, η = η₁ ∨ η = η₂) (η : Γ.IncidentEnds v)
    (r : PositiveSpeed) :
    Γ.endpointOf (transmissionLaw η₁ η₂) η r ≠ η := by
  unfold transmissionLaw
  rw [← (FiniteMetricGraph.isSpeedRepresentation_permutationLaw _).eq_endpointOf]
  rcases hval η with rfl | rfl
  · simpa using hne.symm
  · simpa using hne

/-- **Example III.8, structure of reversible laws.**  At each fixed speed, the endpoint
permutation of a reversible vertex law is a product of fixed points (reflections) and
transpositions (transmissions): every cycle in its cycle type has length `2`. -/
theorem cycleType_speedPermutation_of_isReversibleAt (S : EnergyPreservingScattering V)
    {v : Γ.Vertex} (hS : IsReversibleAt (S.map v)) (r : PositiveSpeed) :
    ∀ n ∈ (EnergyPreservingScattering.speedPermutation V S v r).cycleType, n = 2 := by
  intro n hn
  set σ := EnergyPreservingScattering.speedPermutation V S v r
  have hinv : σ * σ = 1 := Equiv.ext fun η =>
    (isReversibleAt_iff (S.map v) (S.isSpeedRepresentation_speedEndpoint v)).mp hS η r
  have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hinv)
  have hdvd : n ∣ 2 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans hord
  have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
  have hle : n ≤ 2 := Nat.le_of_dvd two_pos hdvd
  omega

/-- **Example III.8, parity.**  A reversible vertex law which reflects nothing at some speed
(`F_v(η,r) ≠ η` for all `η`) exists only at even valence. -/
theorem even_card_of_isReversibleAt_of_nonreflecting (S : EnergyPreservingScattering V)
    {v : Γ.Vertex} (hS : IsReversibleAt (S.map v)) (r : PositiveSpeed)
    (hnr : ∀ η : Γ.IncidentEnds v, EnergyPreservingScattering.speedEndpoint V S v η r ≠ η) :
    Even (Fintype.card (Γ.IncidentEnds v)) := by
  classical
  set σ := EnergyPreservingScattering.speedPermutation V S v r
  have hinv : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    exact Equiv.ext fun η =>
      (isReversibleAt_iff (S.map v) (S.isSpeedRepresentation_speedEndpoint v)).mp hS η r
  have hsupp : σ.supportᶜ = ∅ := by
    ext η
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.notMem_empty,
      iff_false]
    exact hnr η
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1) hinv
  rw [hsupp, Finset.card_empty] at hmod
  exact Nat.even_iff.mpr hmod.symm

/-! ### Example III.9: a nonreversible cyclic law -/

/-- A cycle of length at least `3` is not an involution. -/
theorem not_involutive_of_isCycle {α : Type*} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (hσ : σ.IsCycle) (h3 : 3 ≤ σ.support.card) : ¬ Function.Involutive σ := by
  intro hinv
  have h1 : σ ^ 2 = 1 := by
    ext x
    simp [sq, hinv x]
  have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h1
  rw [hσ.orderOf] at hord
  have := Nat.le_of_dvd two_pos hord
  omega

/-- The law of a cycle of length `≥ 3` of the edge-ends at `v` is not reversible. -/
theorem not_isReversibleAt_permutationLaw_of_isCycle {v : Γ.Vertex}
    {σ : Equiv.Perm (Γ.IncidentEnds v)} (hσ : σ.IsCycle) (h3 : 3 ≤ σ.support.card) :
    ¬ IsReversibleAt (Γ.permutationLaw v σ).toEquiv := by
  rw [isReversibleAt_permutationLaw_iff]
  exact not_involutive_of_isCycle hσ h3

/-- The cyclic law of Example III.9 at three edge-ends `η₁, η₂, η₃`:
`η₁ ↦ η₂ ↦ η₃ ↦ η₁`, at every speed. -/
noncomputable def cyclicLaw {v : Γ.Vertex} (η₁ η₂ η₃ : Γ.IncidentEnds v) :
    Γ.IncomingBoundary v ≃ᵐ Γ.OutgoingBoundary v :=
  Γ.permutationLaw v (Equiv.swap η₁ η₂ * Equiv.swap η₂ η₃)

/-- The cyclic law in speed coordinates: `F_v(η₁,r) = η₂`, `F_v(η₂,r) = η₃`,
`F_v(η₃,r) = η₁`. -/
theorem cyclicLaw_incomingAtSpeed {v : Γ.Vertex} {η₁ η₂ η₃ : Γ.IncidentEnds v}
    (h12 : η₁ ≠ η₂) (h13 : η₁ ≠ η₃) (h23 : η₂ ≠ η₃) (r : PositiveSpeed) :
    cyclicLaw η₁ η₂ η₃ (Γ.incomingAtSpeed η₁ r) = Γ.outgoingAtSpeed η₂ r ∧
      cyclicLaw η₁ η₂ η₃ (Γ.incomingAtSpeed η₂ r) = Γ.outgoingAtSpeed η₃ r ∧
      cyclicLaw η₁ η₂ η₃ (Γ.incomingAtSpeed η₃ r) = Γ.outgoingAtSpeed η₁ r := by
  have e1 : (Equiv.swap η₁ η₂ * Equiv.swap η₂ η₃) η₁ = η₂ := by
    simp [Equiv.swap_apply_of_ne_of_ne h12 h13]
  have e2 : (Equiv.swap η₁ η₂ * Equiv.swap η₂ η₃) η₂ = η₃ := by
    simp [Equiv.swap_apply_of_ne_of_ne h13.symm h23.symm]
  have e3 : (Equiv.swap η₁ η₂ * Equiv.swap η₂ η₃) η₃ = η₁ := by
    simp
  simp only [cyclicLaw, FiniteMetricGraph.permutationLaw_incomingAtSpeed, e1, e2, e3, and_self]

/-- **Example III.9.**  Let `η₁, η₂, η₃` be distinct edge-ends at `v`.  The cyclic law has
`F_v(η₁,r) = η₂`, `F_v(η₂,r) = η₃`, `F_v(η₃,r) = η₁` for every `r > 0`; it is an
energy-preserving Borel isomorphism; and it is not reversible. -/
theorem cyclicLaw_spec {v : Γ.Vertex} {η₁ η₂ η₃ : Γ.IncidentEnds v}
    (h12 : η₁ ≠ η₂) (h13 : η₁ ≠ η₃) (h23 : η₂ ≠ η₃) :
    (∀ r : PositiveSpeed,
      cyclicLaw η₁ η₂ η₃ (Γ.incomingAtSpeed η₁ r) = Γ.outgoingAtSpeed η₂ r ∧
      cyclicLaw η₁ η₂ η₃ (Γ.incomingAtSpeed η₂ r) = Γ.outgoingAtSpeed η₃ r ∧
      cyclicLaw η₁ η₂ η₃ (Γ.incomingAtSpeed η₃ r) = Γ.outgoingAtSpeed η₁ r) ∧
      V.IsEnergyPreservingAt v (cyclicLaw η₁ η₂ η₃) ∧
      Measurable (cyclicLaw η₁ η₂ η₃) ∧ Measurable (cyclicLaw η₁ η₂ η₃).symm ∧
      ¬ IsReversibleAt (cyclicLaw η₁ η₂ η₃).toEquiv := by
  refine ⟨cyclicLaw_incomingAtSpeed h12 h13 h23, V.isEnergyPreservingAt_permutationLaw _,
    (cyclicLaw η₁ η₂ η₃).measurable, (cyclicLaw η₁ η₂ η₃).symm.measurable, ?_⟩
  rw [cyclicLaw, isReversibleAt_permutationLaw_iff]
  intro hinv
  have e1 : (Equiv.swap η₁ η₂ * Equiv.swap η₂ η₃) η₁ = η₂ := by
    simp [Equiv.swap_apply_of_ne_of_ne h12 h13]
  have e2 : (Equiv.swap η₁ η₂ * Equiv.swap η₂ η₃) η₂ = η₃ := by
    simp [Equiv.swap_apply_of_ne_of_ne h13.symm h23.symm]
  have := hinv η₁
  rw [e1, e2] at this
  exact h13 this.symm

/-- At a vertex of valence three with edge-ends `η₁, η₂, η₃`, the displayed `F_v` determines the
law: any vertex map with this speed representation is the cyclic law. -/
theorem eq_cyclicLaw_of_speedRepresentation {v : Γ.Vertex} {η₁ η₂ η₃ : Γ.IncidentEnds v}
    (h12 : η₁ ≠ η₂) (h13 : η₁ ≠ η₃) (h23 : η₂ ≠ η₃)
    (hval : ∀ η : Γ.IncidentEnds v, η = η₁ ∨ η = η₂ ∨ η = η₃)
    {S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v}
    {F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v}
    (hF : Γ.IsSpeedRepresentation S F)
    (hF1 : ∀ r, F η₁ r = η₂) (hF2 : ∀ r, F η₂ r = η₃) (hF3 : ∀ r, F η₃ r = η₁) :
    S = cyclicLaw η₁ η₂ η₃ := by
  have hspec := cyclicLaw_incomingAtSpeed h12 h13 h23
  funext α
  rw [← (Γ.incomingSpeedChart v).apply_symm_apply α]
  obtain ⟨η, r⟩ := (Γ.incomingSpeedChart v).symm α
  rw [FiniteMetricGraph.incomingSpeedChart_apply, hF]
  rcases hval η with rfl | rfl | rfl
  · rw [hF1, (hspec r).1]
  · rw [hF2, (hspec r).2.1]
  · rw [hF3, (hspec r).2.2]

end MechanicalPotential
end HamiltonianMetricGraphs
