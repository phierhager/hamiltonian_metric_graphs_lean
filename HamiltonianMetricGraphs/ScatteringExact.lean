/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.BorelCriterion

/-!
# Proposition III.2, Lemma III.3 and Lemma III.5, as printed

The structures `EnergyPreservingScattering` and `BorelEnergyPreservingScattering` package a
whole scattering structure whose vertex maps are already equivalences (resp. measurable
equivalences).  The printed results of Sec. III are per vertex and start from weaker data.  This
module states them in that form.

* **Proposition III.2 (`prop:speed-representation`).**  For an energy-preserving *map*
  `S_v : D^in_v → D^out_v`, not assumed bijective, there is a unique `F_v` with
  `S_v(α^in_{η,r}) = α^out_{F_v(η,r),r}` (`existsUnique_speedRepresentation`), and `S_v` is
  bijective iff every `F_v(·,r)` is (`bijective_iff_forall_bijective`); together in
  `speed_representation_exact`.
* **Lemma III.3 (`lem:borel-criterion`).**  For an energy-preserving *bijection* (an `Equiv`, no
  measurability assumed), `S_v` and `S_v⁻¹` are Borel iff every set `{r > 0 : F_v(η,r) = ζ}` is
  Borel (`borel_criterion`); `toMeasurableEquiv` builds the Borel isomorphism from the fibre
  condition, and `BorelEnergyPreservingScattering.ofFibers` the full Borel scattering structure.
* **Lemma III.5 (`lem:reversibility-involution`).**  Reversibility of a single vertex law, taken
  literally from Definition III.4 (`IsReversibleAt`), is equivalent to `F_v(F_v(η,r),r) = η`
  (`isReversibleAt_iff`, `isReversibleAt_iff_involutive`); the global statement
  `reversible_iff_speedEndpoint_involutive` is re-derived from it.
-/

namespace HamiltonianMetricGraphs

open FiniteMetricGraph (PositiveSpeed)

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

@[simp] theorem incomingSpeedChart_apply (v : Γ.Vertex) (x : Γ.IncidentEnds v × PositiveSpeed) :
    Γ.incomingSpeedChart v x = Γ.incomingAtSpeed x.1 x.2 := rfl

@[simp] theorem outgoingSpeedChart_apply (v : Γ.Vertex) (x : Γ.IncidentEnds v × PositiveSpeed) :
    Γ.outgoingSpeedChart v x = Γ.outgoingAtSpeed x.1 x.2 := rfl

theorem incomingAtSpeed_inj {v : Γ.Vertex} {η ζ : Γ.IncidentEnds v} {r s : PositiveSpeed} :
    Γ.incomingAtSpeed η r = Γ.incomingAtSpeed ζ s ↔ η = ζ ∧ r = s := by
  rw [← incomingSpeedChart_apply Γ v (η, r), ← incomingSpeedChart_apply Γ v (ζ, s),
    (Γ.incomingSpeedChart v).injective.eq_iff, Prod.mk.injEq]

theorem outgoingAtSpeed_inj {v : Γ.Vertex} {η ζ : Γ.IncidentEnds v} {r s : PositiveSpeed} :
    Γ.outgoingAtSpeed η r = Γ.outgoingAtSpeed ζ s ↔ η = ζ ∧ r = s := by
  rw [← outgoingSpeedChart_apply Γ v (η, r), ← outgoingSpeedChart_apply Γ v (ζ, s),
    (Γ.outgoingSpeedChart v).injective.eq_iff, Prod.mk.injEq]

@[simp] theorem incomingSpeedChart_symm_incomingAtSpeed {v : Γ.Vertex} (η : Γ.IncidentEnds v)
    (r : PositiveSpeed) : (Γ.incomingSpeedChart v).symm (Γ.incomingAtSpeed η r) = (η, r) :=
  (Γ.incomingSpeedChart v).symm_apply_apply (η, r)

@[simp] theorem outgoingSpeedChart_symm_outgoingAtSpeed {v : Γ.Vertex} (η : Γ.IncidentEnds v)
    (r : PositiveSpeed) : (Γ.outgoingSpeedChart v).symm (Γ.outgoingAtSpeed η r) = (η, r) :=
  (Γ.outgoingSpeedChart v).symm_apply_apply (η, r)

/-- `F` is a speed representation of the vertex map `S`:
`S(α^in_{η,r}) = α^out_{F(η,r),r}` for all edge-ends `η` at `v` and all speeds `r > 0`. -/
def IsSpeedRepresentation {v : Γ.Vertex} (S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v)
    (F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v) : Prop :=
  ∀ (η : Γ.IncidentEnds v) (r : PositiveSpeed),
    S (Γ.incomingAtSpeed η r) = Γ.outgoingAtSpeed (F η r) r

/-- The edge-end selected by a vertex map at the incoming covector `α^in_{η,r}`. -/
def endpointOf {v : Γ.Vertex} (S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v)
    (η : Γ.IncidentEnds v) (r : PositiveSpeed) : Γ.IncidentEnds v :=
  ⟨(S (Γ.incomingAtSpeed η r)).1.germ, (S (Γ.incomingAtSpeed η r)).2.1⟩

variable {Γ}

/-- Uniqueness in Proposition III.2: a speed representation is determined by the map. -/
theorem IsSpeedRepresentation.unique {v : Γ.Vertex}
    {S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v}
    {F G : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v}
    (hF : Γ.IsSpeedRepresentation S F) (hG : Γ.IsSpeedRepresentation S G) : F = G := by
  funext η r
  exact (Γ.outgoingAtSpeed_inj.mp ((hF η r).symm.trans (hG η r))).1

/-- Any speed representation is the selected edge-end `endpointOf`. -/
theorem IsSpeedRepresentation.eq_endpointOf {v : Γ.Vertex}
    {S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v}
    {F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v}
    (hF : Γ.IsSpeedRepresentation S F) : F = Γ.endpointOf S := by
  funext η r
  apply Subtype.ext
  simp [endpointOf, hF η r]

/-- The bijectivity criterion of Proposition III.2: a vertex map with a speed representation `F`
is bijective iff `F(·,r)` is a bijection of the edge-ends at `v` for every `r > 0`. -/
theorem IsSpeedRepresentation.bijective_iff_forall_bijective {v : Γ.Vertex}
    {S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v}
    {F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v}
    (hF : Γ.IsSpeedRepresentation S F) :
    Function.Bijective S ↔ ∀ r : PositiveSpeed, Function.Bijective (fun η => F η r) := by
  have hin : ∀ α : Γ.IncomingBoundary v, α = Γ.incomingAtSpeed
      ((Γ.incomingSpeedChart v).symm α).1 ((Γ.incomingSpeedChart v).symm α).2 :=
    fun α => ((Γ.incomingSpeedChart v).apply_symm_apply α).symm
  have hout : ∀ β : Γ.OutgoingBoundary v, β = Γ.outgoingAtSpeed
      ((Γ.outgoingSpeedChart v).symm β).1 ((Γ.outgoingSpeedChart v).symm β).2 :=
    fun β => ((Γ.outgoingSpeedChart v).apply_symm_apply β).symm
  constructor
  · rintro ⟨hinj, hsurj⟩ r
    refine ⟨fun η ζ h => ?_, fun ζ => ?_⟩
    · have h' : S (Γ.incomingAtSpeed η r) = S (Γ.incomingAtSpeed ζ r) := by
        rw [hF, hF]
        exact congrArg (fun ξ => Γ.outgoingAtSpeed ξ r) h
      exact (Γ.incomingAtSpeed_inj.mp (hinj h')).1
    · obtain ⟨α, hα⟩ := hsurj (Γ.outgoingAtSpeed ζ r)
      rw [hin α, hF] at hα
      obtain ⟨h1, h2⟩ := Γ.outgoingAtSpeed_inj.mp hα
      exact ⟨((Γ.incomingSpeedChart v).symm α).1, by rw [← h2]; exact h1⟩
  · intro hbij
    refine ⟨fun α β h => ?_, fun β => ?_⟩
    · rw [hin α, hin β, hF, hF] at h
      obtain ⟨h1, h2⟩ := Γ.outgoingAtSpeed_inj.mp h
      rw [hin α, hin β]
      rw [h2] at h1 ⊢
      rw [(hbij _).1 h1]
    · obtain ⟨η, hη⟩ := (hbij ((Γ.outgoingSpeedChart v).symm β).2).2
        ((Γ.outgoingSpeedChart v).symm β).1
      refine ⟨Γ.incomingAtSpeed η ((Γ.outgoingSpeedChart v).symm β).2, ?_⟩
      rw [hF]
      conv_rhs => rw [hout β]
      simp only at hη
      rw [hη]

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- A map `S_v : D^in_v → D^out_v` (not assumed bijective) is *energy-preserving* in the sense
of Definition III.1: `E_v(S_v α) = E_v(α)` for every incoming covector `α`. -/
def IsEnergyPreservingAt (v : Γ.Vertex) (S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v) :
    Prop :=
  ∀ α : Γ.IncomingBoundary v, V.boundaryEnergy (S α).1 = V.boundaryEnergy α.1

variable {V}

/-- The speed representation exists for every energy-preserving vertex map. -/
theorem IsEnergyPreservingAt.isSpeedRepresentation_endpointOf {v : Γ.Vertex}
    {S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v} (hS : V.IsEnergyPreservingAt v S) :
    Γ.IsSpeedRepresentation S (Γ.endpointOf S) := by
  intro η r
  have hE := hS (Γ.incomingAtSpeed η r)
  rw [V.boundaryEnergy_at_vertex (S (Γ.incomingAtSpeed η r)).1 (S (Γ.incomingAtSpeed η r)).2.1,
    V.boundaryEnergy_incomingAtSpeed] at hE
  have hsq : (S (Γ.incomingAtSpeed η r)).1.momentum ^ 2 = r.1 ^ 2 := by linarith
  have hr : 0 < r.1 := r.2
  have habs : |(S (Γ.incomingAtSpeed η r)).1.momentum| = r.1 := by
    rw [← Real.sqrt_sq_eq_abs, hsq, Real.sqrt_sq hr.le]
  rw [Γ.outgoing_eq_outgoingAtSpeed (S (Γ.incomingAtSpeed η r))]
  congr 1
  exact Subtype.ext habs

/-- Conversely, a vertex map with a speed representation is energy-preserving: both
`α^in_{η,r}` and `α^out_{ζ,r}` have boundary energy `r²/2 + V(v)`. -/
theorem isEnergyPreservingAt_of_isSpeedRepresentation {v : Γ.Vertex}
    {S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v}
    {F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v}
    (hF : Γ.IsSpeedRepresentation S F) : V.IsEnergyPreservingAt v S := by
  intro α
  rw [← (Γ.incomingSpeedChart v).apply_symm_apply α, FiniteMetricGraph.incomingSpeedChart_apply,
    hF, V.boundaryEnergy_outgoingAtSpeed, V.boundaryEnergy_incomingAtSpeed]

/-- A vertex map is energy-preserving iff it admits a speed representation. -/
theorem isEnergyPreservingAt_iff_exists_isSpeedRepresentation {v : Γ.Vertex}
    (S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v) :
    V.IsEnergyPreservingAt v S ↔ ∃ F, Γ.IsSpeedRepresentation S F :=
  ⟨fun hS => ⟨_, hS.isSpeedRepresentation_endpointOf⟩,
    fun ⟨_, hF⟩ => isEnergyPreservingAt_of_isSpeedRepresentation hF⟩

/-- The existence-and-uniqueness half of Proposition III.2. -/
theorem IsEnergyPreservingAt.existsUnique_speedRepresentation {v : Γ.Vertex}
    {S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v} (hS : V.IsEnergyPreservingAt v S) :
    ∃! F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v,
      Γ.IsSpeedRepresentation S F :=
  ⟨_, hS.isSpeedRepresentation_endpointOf,
    fun _ hG => hG.unique hS.isSpeedRepresentation_endpointOf⟩

/-- **Proposition III.2 (`prop:speed-representation`), as printed.**  Let
`S_v : D^in_v → D^out_v` be energy-preserving (a map, not assumed bijective).  Then there is a
unique `F_v : E_v^∂ × (0,∞) → E_v^∂` with `S_v(α^in_{η,r}) = α^out_{F_v(η,r),r}`, and `S_v` is
bijective iff `F_v(·,r)` is a bijection of `E_v^∂` for every `r > 0`. -/
theorem speed_representation_exact {v : Γ.Vertex}
    {S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v} (hS : V.IsEnergyPreservingAt v S) :
    (∃! F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v,
        Γ.IsSpeedRepresentation S F) ∧
      ∀ F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v,
        Γ.IsSpeedRepresentation S F →
          (Function.Bijective S ↔ ∀ r : PositiveSpeed, Function.Bijective (fun η => F η r)) :=
  ⟨hS.existsUnique_speedRepresentation, fun _ hF => hF.bijective_iff_forall_bijective⟩

/-! ### Relation to `EnergyPreservingScattering` -/

namespace EnergyPreservingScattering

variable (S : EnergyPreservingScattering V)

/-- Each vertex map of an `EnergyPreservingScattering` is energy-preserving. -/
theorem isEnergyPreservingAt (v : Γ.Vertex) : V.IsEnergyPreservingAt v (S.map v) :=
  S.preserves_energy v

/-- The existing `speedEndpoint` is the selected edge-end of the vertex map. -/
theorem endpointOf_map (v : Γ.Vertex) :
    Γ.endpointOf (S.map v) = EnergyPreservingScattering.speedEndpoint V S v := rfl

/-- The existing `speedEndpoint` is the unique speed representation of Proposition III.2. -/
theorem isSpeedRepresentation_speedEndpoint (v : Γ.Vertex) :
    Γ.IsSpeedRepresentation (S.map v) (EnergyPreservingScattering.speedEndpoint V S v) :=
  EnergyPreservingScattering.speed_representation V S v

end EnergyPreservingScattering

/-- The converse direction of Proposition III.2 at the level of scattering structures: a family
of energy-preserving vertex maps whose speed representations are bijective at every speed is an
`EnergyPreservingScattering`. -/
noncomputable def EnergyPreservingScattering.ofSpeedBijective
    (S : ∀ v : Γ.Vertex, Γ.IncomingBoundary v → Γ.OutgoingBoundary v)
    (hS : ∀ v, V.IsEnergyPreservingAt v (S v))
    (hbij : ∀ v (r : PositiveSpeed), Function.Bijective (fun η => Γ.endpointOf (S v) η r)) :
    EnergyPreservingScattering V where
  map v := Equiv.ofBijective (S v)
    ((hS v).isSpeedRepresentation_endpointOf.bijective_iff_forall_bijective.mpr (hbij v))
  preserves_energy v := hS v

@[simp] theorem EnergyPreservingScattering.ofSpeedBijective_map_apply
    (S : ∀ v : Γ.Vertex, Γ.IncomingBoundary v → Γ.OutgoingBoundary v)
    (hS : ∀ v, V.IsEnergyPreservingAt v (S v))
    (hbij : ∀ v (r : PositiveSpeed), Function.Bijective (fun η => Γ.endpointOf (S v) η r))
    (v : Γ.Vertex) (α : Γ.IncomingBoundary v) :
    (EnergyPreservingScattering.ofSpeedBijective S hS hbij).map v α = S v α := rfl

/-! ### Lemma III.3 -/

section BorelCriterion

variable {v : Γ.Vertex}

/-- The coordinate representative `(η,r) ↦ (F(η,r), r)`. -/
private def coordMap (F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v) :
    Γ.IncidentEnds v × PositiveSpeed → Γ.IncidentEnds v × PositiveSpeed :=
  fun x => (F x.1 x.2, x.2)

/-- Finite-valued criterion: `(η,r) ↦ F(η,r)` is Borel iff all coordinate fibres are Borel. -/
theorem measurable_uncurry_iff_fibers (F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v) :
    Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed => F x.1 x.2) ↔
      ∀ η ζ : Γ.IncidentEnds v, MeasurableSet {r : PositiveSpeed | F η r = ζ} := by
  rw [measurable_iff_preimage_singletons]
  constructor
  · intro h η ζ
    have hs := (measurableSet_finite_prod_iff_sections _).mp (h ζ) η
    simpa using hs
  · intro h ζ
    apply (measurableSet_finite_prod_iff_sections _).mpr
    intro η
    simpa using h η ζ

private theorem measurable_coordMap {F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v}
    (hF : Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed => F x.1 x.2)) :
    Measurable (coordMap F) :=
  hF.prodMk measurable_snd

variable (S : Γ.IncomingBoundary v ≃ Γ.OutgoingBoundary v)
  {F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v}

/-- The inverse speed representation `G(ζ,r) = F(·,r)⁻¹(ζ)`, read off from `S⁻¹`. -/
private noncomputable def invEndpoint (ζ : Γ.IncidentEnds v) (r : PositiveSpeed) :
    Γ.IncidentEnds v :=
  ((Γ.incomingSpeedChart v).symm (S.symm (Γ.outgoingAtSpeed ζ r))).1

private theorem inv_speed_and_endpoint (hF : Γ.IsSpeedRepresentation S F)
    (ζ : Γ.IncidentEnds v) (r : PositiveSpeed) :
    ((Γ.incomingSpeedChart v).symm (S.symm (Γ.outgoingAtSpeed ζ r))).2 = r ∧
      F (invEndpoint S ζ r) r = ζ := by
  set x := (Γ.incomingSpeedChart v).symm (S.symm (Γ.outgoingAtSpeed ζ r)) with hx
  have hα : S.symm (Γ.outgoingAtSpeed ζ r) = Γ.incomingAtSpeed x.1 x.2 :=
    ((Γ.incomingSpeedChart v).apply_symm_apply _).symm
  have h := congrArg S hα
  rw [S.apply_symm_apply, hF] at h
  obtain ⟨h1, h2⟩ := Γ.outgoingAtSpeed_inj.mp h
  refine ⟨h2.symm, ?_⟩
  change F x.1 r = ζ
  rw [h2]
  exact h1.symm

private theorem symm_eq_coord (hF : Γ.IsSpeedRepresentation S F) (β : Γ.OutgoingBoundary v) :
    S.symm β = Γ.incomingSpeedChart v
      (coordMap (invEndpoint S) ((Γ.outgoingSpeedChart v).symm β)) := by
  set y := (Γ.outgoingSpeedChart v).symm β
  have hβ : β = Γ.outgoingAtSpeed y.1 y.2 := ((Γ.outgoingSpeedChart v).apply_symm_apply β).symm
  have h := inv_speed_and_endpoint S hF y.1 y.2
  rw [FiniteMetricGraph.incomingSpeedChart_apply]
  change S.symm β = Γ.incomingAtSpeed (invEndpoint S y.1 y.2) y.2
  conv_lhs => rw [hβ, ← (Γ.incomingSpeedChart v).apply_symm_apply (S.symm _)]
  rw [FiniteMetricGraph.incomingSpeedChart_apply, h.1]
  rfl

private theorem invEndpoint_eq_iff (hF : Γ.IsSpeedRepresentation S F)
    (η ζ : Γ.IncidentEnds v) (r : PositiveSpeed) : invEndpoint S ζ r = η ↔ F η r = ζ := by
  constructor
  · rintro rfl
    exact (inv_speed_and_endpoint S hF ζ r).2
  · rintro rfl
    unfold invEndpoint
    rw [← hF, S.symm_apply_apply, FiniteMetricGraph.incomingSpeedChart_symm_incomingAtSpeed]

private theorem apply_eq_coord (hF : Γ.IsSpeedRepresentation S F) (α : Γ.IncomingBoundary v) :
    S α = Γ.outgoingSpeedChart v (coordMap F ((Γ.incomingSpeedChart v).symm α)) := by
  conv_lhs => rw [← (Γ.incomingSpeedChart v).apply_symm_apply α]
  exact hF _ _

/-- One direction of Lemma III.3: if `S_v` is Borel, every fibre `{r > 0 : F(η,r) = ζ}` is. -/
theorem measurableSet_fibers_of_measurable {S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v}
    (hF : Γ.IsSpeedRepresentation S F) (hS : Measurable S) (η ζ : Γ.IncidentEnds v) :
    MeasurableSet {r : PositiveSpeed | F η r = ζ} := by
  revert η ζ
  rw [← measurable_uncurry_iff_fibers]
  have hEq : (fun x : Γ.IncidentEnds v × PositiveSpeed => F x.1 x.2) =
      fun x => ⟨(S (Γ.incomingAtSpeed x.1 x.2)).1.germ, (S (Γ.incomingAtSpeed x.1 x.2)).2.1⟩ := by
    rw [hF.eq_endpointOf]
    rfl
  rw [hEq]
  exact ((FiniteMetricGraph.measurable_boundary_germ Γ).comp
    (measurable_subtype_coe.comp (hS.comp (Γ.measurable_incomingAtSpeed v)))).subtype_mk

/-- **Lemma III.3 (`lem:borel-criterion`), as printed.**  Let `S_v` be an energy-preserving
bijection (an `Equiv`, no measurability assumed) with speed representation `F_v`.  Then `S_v` is
a Borel isomorphism (`S_v` and `S_v⁻¹` both Borel) iff for all `η, ζ` the set
`{r > 0 : F_v(η,r) = ζ}` is Borel in `(0,∞)`. -/
theorem borel_criterion (hF : Γ.IsSpeedRepresentation S F) :
    (Measurable S ∧ Measurable S.symm) ↔
      ∀ η ζ : Γ.IncidentEnds v, MeasurableSet {r : PositiveSpeed | F η r = ζ} := by
  constructor
  · exact fun h => measurableSet_fibers_of_measurable hF h.1
  · intro hfib
    have hFm := (measurable_uncurry_iff_fibers F).mpr hfib
    have hGm : Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed => invEndpoint S x.1 x.2) := by
      rw [measurable_uncurry_iff_fibers]
      intro ζ η
      have : {r : PositiveSpeed | invEndpoint S ζ r = η} = {r | F η r = ζ} := by
        ext r
        exact invEndpoint_eq_iff S hF η ζ r
      rw [this]
      exact hfib η ζ
    refine ⟨?_, ?_⟩
    · have : (S : Γ.IncomingBoundary v → Γ.OutgoingBoundary v) =
          Γ.outgoingSpeedChart v ∘ coordMap F ∘ (Γ.incomingSpeedChart v).symm :=
        funext (apply_eq_coord S hF)
      rw [this]
      exact (Γ.outgoingSpeedChart v).measurable.comp
        ((measurable_coordMap hFm).comp (Γ.incomingSpeedChart v).symm.measurable)
    · have : (S.symm : Γ.OutgoingBoundary v → Γ.IncomingBoundary v) =
          Γ.incomingSpeedChart v ∘ coordMap (invEndpoint S) ∘ (Γ.outgoingSpeedChart v).symm :=
        funext (symm_eq_coord S hF)
      rw [this]
      exact (Γ.incomingSpeedChart v).measurable.comp
        ((measurable_coordMap hGm).comp (Γ.outgoingSpeedChart v).symm.measurable)

/-- Lemma III.3 for an energy-preserving bijection, with the speed representation of
Proposition III.2 (`endpointOf`). -/
theorem borel_criterion_of_isEnergyPreservingAt (hS : V.IsEnergyPreservingAt v S) :
    (Measurable S ∧ Measurable S.symm) ↔
      ∀ η ζ : Γ.IncidentEnds v, MeasurableSet {r : PositiveSpeed | Γ.endpointOf S η r = ζ} :=
  borel_criterion S hS.isSpeedRepresentation_endpointOf

/-- The Borel isomorphism `S_v` produced by Lemma III.3 from the fibre condition. -/
noncomputable def toMeasurableEquiv (hF : Γ.IsSpeedRepresentation S F)
    (hfib : ∀ η ζ : Γ.IncidentEnds v, MeasurableSet {r : PositiveSpeed | F η r = ζ}) :
    Γ.IncomingBoundary v ≃ᵐ Γ.OutgoingBoundary v where
  toEquiv := S
  measurable_toFun := ((borel_criterion S hF).mpr hfib).1
  measurable_invFun := ((borel_criterion S hF).mpr hfib).2

@[simp] theorem toMeasurableEquiv_toEquiv (hF : Γ.IsSpeedRepresentation S F)
    (hfib : ∀ η ζ : Γ.IncidentEnds v, MeasurableSet {r : PositiveSpeed | F η r = ζ}) :
    (toMeasurableEquiv S hF hfib).toEquiv = S := rfl

end BorelCriterion

/-- Lemma III.3 at the level of scattering structures: an `EnergyPreservingScattering` whose
coordinate fibres are Borel is the underlying law of a `BorelEnergyPreservingScattering`. -/
noncomputable def BorelEnergyPreservingScattering.ofFibers (S : EnergyPreservingScattering V)
    (hfib : ∀ (v : Γ.Vertex) (η ζ : Γ.IncidentEnds v), MeasurableSet {r : PositiveSpeed |
      EnergyPreservingScattering.speedEndpoint V S v η r = ζ}) :
    BorelEnergyPreservingScattering V where
  map v := toMeasurableEquiv (S.map v) (S.isSpeedRepresentation_speedEndpoint v) (hfib v)
  preserves_energy := S.preserves_energy

@[simp] theorem BorelEnergyPreservingScattering.ofFibers_toEnergyPreservingScattering
    (S : EnergyPreservingScattering V)
    (hfib : ∀ (v : Γ.Vertex) (η ζ : Γ.IncidentEnds v), MeasurableSet {r : PositiveSpeed |
      EnergyPreservingScattering.speedEndpoint V S v η r = ζ}) :
    (BorelEnergyPreservingScattering.ofFibers S hfib).toEnergyPreservingScattering = S := rfl

/-- Lemma III.3 for scattering structures: an energy-preserving scattering structure underlies a
Borel one iff all its coordinate fibres are Borel. -/
theorem EnergyPreservingScattering.exists_borel_iff_fibers (S : EnergyPreservingScattering V) :
    (∃ B : BorelEnergyPreservingScattering V, B.toEnergyPreservingScattering = S) ↔
      ∀ (v : Γ.Vertex) (η ζ : Γ.IncidentEnds v), MeasurableSet {r : PositiveSpeed |
        EnergyPreservingScattering.speedEndpoint V S v η r = ζ} := by
  constructor
  · rintro ⟨B, rfl⟩ v η ζ
    exact BorelEnergyPreservingScattering.measurable_speedEndpoint_fiber V B v η ζ
  · intro h
    exact ⟨_, BorelEnergyPreservingScattering.ofFibers_toEnergyPreservingScattering S h⟩

/-! ### Lemma III.5 -/

section Reversibility

variable {v : Γ.Vertex}

/-- **Definition III.4 (`def:reversible-scattering`), per vertex.**  A vertex law
`S_v : D^in_v → D^out_v` is reversible if `S_v⁻¹ = ρ̃ ∘ S_v ∘ ρ̃` as maps `D^out_v → D^in_v`,
where `ρ̃(η,p) = (η,-p)` is momentum reversal (here from outgoing to incoming covectors). -/
def IsReversibleAt (S : Γ.IncomingBoundary v ≃ Γ.OutgoingBoundary v) : Prop :=
  (S.symm : Γ.OutgoingBoundary v → Γ.IncomingBoundary v) =
    (Γ.incomingMomentumReversal v).symm ∘ S ∘ (Γ.incomingMomentumReversal v).symm

/-- `ρ̃` on outgoing covectors, in speed coordinates: `α^out_{η,r} ↦ α^in_{η,r}`. -/
@[simp] theorem momentumReversal_symm_outgoingAtSpeed (η : Γ.IncidentEnds v) (r : PositiveSpeed) :
    (Γ.incomingMomentumReversal v).symm (Γ.outgoingAtSpeed η r) = Γ.incomingAtSpeed η r :=
  FiniteMetricGraph.incomingMomentumReversal_symm_outgoingAtSpeed Γ η r

/-- **Lemma III.5 (`lem:reversibility-involution`), per vertex.**  Let `S_v` be an
energy-preserving bijection with speed representation `F_v`.  Then `S_v` is reversible iff
`F_v(F_v(η,r),r) = η` for all edge-ends `η` at `v` and all `r > 0`. -/
theorem isReversibleAt_iff (S : Γ.IncomingBoundary v ≃ Γ.OutgoingBoundary v)
    {F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v}
    (hF : Γ.IsSpeedRepresentation S F) :
    IsReversibleAt S ↔ ∀ (η : Γ.IncidentEnds v) (r : PositiveSpeed), F (F η r) r = η := by
  have hsymm : ∀ η r, S.symm (Γ.outgoingAtSpeed (F η r) r) = Γ.incomingAtSpeed η r := by
    intro η r
    rw [← hF, S.symm_apply_apply]
  constructor
  · intro h η r
    have h' := congrFun h (Γ.outgoingAtSpeed (F η r) r)
    simp only [Function.comp_apply, momentumReversal_symm_outgoingAtSpeed, hsymm] at h'
    rw [hF, momentumReversal_symm_outgoingAtSpeed] at h'
    exact ((Γ.incomingAtSpeed_inj.mp h').1).symm
  · intro h
    funext β
    rw [← (Γ.outgoingSpeedChart v).apply_symm_apply β]
    obtain ⟨ζ, r⟩ := (Γ.outgoingSpeedChart v).symm β
    simp only [FiniteMetricGraph.outgoingSpeedChart_apply, Function.comp_apply,
      momentumReversal_symm_outgoingAtSpeed]
    rw [hF, momentumReversal_symm_outgoingAtSpeed]
    conv_lhs => rw [← h ζ r]
    rw [hsymm]

/-- Lemma III.5, second form: reversibility iff `F_v(·,r)` is an involution for each `r > 0`. -/
theorem isReversibleAt_iff_involutive (S : Γ.IncomingBoundary v ≃ Γ.OutgoingBoundary v)
    {F : Γ.IncidentEnds v → PositiveSpeed → Γ.IncidentEnds v}
    (hF : Γ.IsSpeedRepresentation S F) :
    IsReversibleAt S ↔ ∀ r : PositiveSpeed, Function.Involutive (fun η => F η r) := by
  rw [isReversibleAt_iff S hF]
  exact ⟨fun h r η => h η r, fun h η r => h r η⟩

/-- Lemma III.5 for an energy-preserving bijection, with its speed representation `endpointOf`
from Proposition III.2. -/
theorem isReversibleAt_iff_of_isEnergyPreservingAt
    (S : Γ.IncomingBoundary v ≃ Γ.OutgoingBoundary v) (hS : V.IsEnergyPreservingAt v S) :
    IsReversibleAt S ↔ ∀ (η : Γ.IncidentEnds v) (r : PositiveSpeed),
      Γ.endpointOf S (Γ.endpointOf S η r) r = η :=
  isReversibleAt_iff S hS.isSpeedRepresentation_endpointOf

end Reversibility

namespace EnergyPreservingScattering

variable (S : EnergyPreservingScattering V)

/-- The global reversibility predicate `IsReversible` is reversibility at every vertex. -/
theorem isReversible_iff_forall_isReversibleAt :
    S.IsReversible ↔ ∀ v : Γ.Vertex, IsReversibleAt (S.map v) := by
  unfold IsReversible IsReversibleAt
  refine forall_congr' fun v => ?_
  rw [← Equiv.coe_inj]
  rfl

/-- Lemma III.5 globally, derived from the per-vertex statement `isReversibleAt_iff`. -/
theorem isReversible_iff_speedEndpoint_involutive' : S.IsReversible ↔
    ∀ (v : Γ.Vertex) (η : Γ.IncidentEnds v) (r : PositiveSpeed),
      EnergyPreservingScattering.speedEndpoint V S v
        (EnergyPreservingScattering.speedEndpoint V S v η r) r = η := by
  rw [isReversible_iff_forall_isReversibleAt]
  exact forall_congr' fun v =>
    isReversibleAt_iff (S.map v) (S.isSpeedRepresentation_speedEndpoint v)

end EnergyPreservingScattering

end MechanicalPotential
end HamiltonianMetricGraphs
