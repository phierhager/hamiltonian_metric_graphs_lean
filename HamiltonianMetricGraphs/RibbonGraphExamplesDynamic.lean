/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition XI.1: the examples after the proof, through the dynamics
-/

import HamiltonianMetricGraphs.RibbonGraphFaces
import HamiltonianMetricGraphs.RibbonGraphExamples
import HamiltonianMetricGraphs.ScatteringExactExamples
import HamiltonianMetricGraphs.WorkedExamplesStar
import HamiltonianMetricGraphs.WorkedExamplesTheta

/-!
# The ribbon-graph examples of Sec. XI.E, through the dynamics

`RibbonGraphExamples.lean` computes the faces and genera of the three ribbon graphs of Sec. XI.E
combinatorially.  Here they are read as the paper reads them: as the high-energy ribbon graphs
`highEnergyRibbon` of concrete metric graphs with concrete vertex laws, so that Proposition XI.1
(`ribbon_faces`) turns the face counts into **orbit counts of the energy shell `Σ_E`**.

* **The cyclic star** `Γ^⋆ = threeStar ℓ` (Sec. XI.A): central law the cyclic permutation
  `(η₁ η₂ η₃)`, leaf laws the identity (`starCyclicScattering`).
* **The theta graph** `Θ = theta ℓ` (Sec. XI.B, two vertices `a`, `b` joined by three edges) with
  the same cyclic order `(η₁ η₂ η₃)`, `(η₁' η₂' η₃')` at both vertices
  (`thetaSameScattering`), and with the order at `b` reversed, `(η₃' η₂' η₁')`
  (`thetaReversedScattering`).

The lengths `ℓ` are arbitrary and the potential `V` is any potential with `E > max_Γ V`
(`V_e < E` on every closed edge, `V(v) < E` at every vertex); `V ≡ 0` with `E > 0` is the special
case `*_zero`.  The vertex laws are speed-independent permutation laws
(`permutationScattering`).  For each example:

* `Σ_E` has `1`, `1`, `3` periodic orbits (the number of orbits `shellOrbit` of Theorem VIII.5,
  `Nat.card`), and `Π_E` has as many cycles;
* the ribbon graph has genus `0`, `1`, `0`.
-/

namespace HamiltonianMetricGraphs

open Finset Equiv FiniteMetricGraph

namespace FiniteMetricGraph

variable {Γ : FiniteMetricGraph}

/-- The permutation of the edge-ends at `v` induced by a permutation of all edge-ends which
preserves the vertex of every end. -/
def vertexRestrict (τ : Perm Γ.EdgeEnd) (hτ : ∀ η, EdgeEnd.vertex Γ (τ η) = EdgeEnd.vertex Γ η)
    (v : Γ.Vertex) : Perm (Γ.IncidentEnds v) :=
  τ.subtypePerm fun η => by rw [hτ]

theorem rotationOf_vertexRestrict (τ : Perm Γ.EdgeEnd)
    (hτ : ∀ η, EdgeEnd.vertex Γ (τ η) = EdgeEnd.vertex Γ η) :
    rotationOf (vertexRestrict τ hτ) = τ := by
  ext1 η
  rw [rotationOf_apply _ (⟨η, rfl⟩ : Γ.IncidentEnds (EdgeEnd.vertex Γ η))]
  rfl

end FiniteMetricGraph

namespace MechanicalPotential

open Set

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- The fixed-speed vertex law of a permutation scattering structure is its permutation, at every
speed. -/
theorem speedPermutation_permutationScattering (σ : ∀ v : Γ.Vertex, Perm (Γ.IncidentEnds v))
    (v : Γ.Vertex) (r : PositiveSpeed) :
    EnergyPreservingScattering.speedPermutation V
      (V.permutationScattering σ).toEnergyPreservingScattering v r = σ v := by
  ext η
  simp only [EnergyPreservingScattering.speedPermutation_apply,
    EnergyPreservingScattering.speedEndpoint]
  apply Subtype.ext
  change ((Γ.permutationLaw v (σ v)) (Γ.incomingAtSpeed η r)).1.germ = _
  rw [permutationLaw_incomingAtSpeed]
  rfl

/-- **Proposition XI.1 for a permutation law.**  Let the vertex law be the speed-independent
permutation law of a vertex-preserving permutation `τ` of the edge-ends whose restriction to
every vertex is a single cycle.  Above the potential, the high-energy ribbon graph is the ribbon
graph with rotation `τ`, and `Σ_E` has as many periodic orbits, and `Π_E` as many cycles, as the
ribbon graph has faces. -/
theorem ribbon_counts_of_perm [Nonempty Γ.Edge] (hΓ : Γ.Connected) (τ : Perm Γ.EdgeEnd)
    (hτ : ∀ η, EdgeEnd.vertex Γ (τ η) = EdgeEnd.vertex Γ η)
    (htr : ∀ η ζ, EdgeEnd.vertex Γ η = EdgeEnd.vertex Γ ζ → τ.SameCycle η ζ) {E : ℝ}
    (hedge : ∀ e, ∀ q ∈ Icc 0 (Γ.length e), V.extension e q < E)
    (hv : ∀ v : Γ.Vertex, V.vertexValue v < E) :
    ∃ hE : V.ShellRegular E,
      V.highEnergyRibbon (V.permutationScattering (vertexRestrict τ hτ)) hv = ⟨τ⟩ ∧
      (V.germCycles (V.permutationScattering (vertexRestrict τ hτ)) E).card =
        (V.highEnergyRibbon (V.permutationScattering (vertexRestrict τ hτ)) hv).numFaces ∧
      Nat.card {O : Set (RegularScatteringPhaseSpace (V := V)
          (V.permutationScattering (vertexRestrict τ hτ))) //
        ∃ (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E),
          O = V.shellOrbit (V.permutationScattering (vertexRestrict τ hτ)) hE η hη} =
        (V.highEnergyRibbon (V.permutationScattering (vertexRestrict τ hτ)) hv).numFaces := by
  set S := V.permutationScattering (vertexRestrict τ hτ) with hS
  have hcyc : ∀ (v : Γ.Vertex) (r : PositiveSpeed),
      r.1 = Real.sqrt (2 * (E - V.vertexValue v)) → ∀ a b : Γ.IncidentEnds v,
        (EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r).SameCycle
          a b := by
    intro v r _ a b
    rw [hS, speedPermutation_permutationScattering]
    exact Perm.sameCycle_subtypePerm.mpr (htr a.1 b.1 (a.2.trans b.2.symm))
  obtain ⟨hE, -, -, -, hfaces, ⟨f, -, -⟩, -⟩ := V.ribbon_faces S hΓ hedge hv hcyc
  have hrot : V.highEnergyRibbon S hv = ⟨τ⟩ := by
    change (⟨rotationOf (V.highEnergyRotation S hv)⟩ : RibbonGraph Γ.Edge) = ⟨τ⟩
    have : V.highEnergyRotation S hv = vertexRestrict τ hτ := by
      funext v
      rw [highEnergyRotation, hS, speedPermutation_permutationScattering]
    rw [this, rotationOf_vertexRestrict]
  refine ⟨hE, hrot, by rw [hfaces]; rfl, ?_⟩
  rw [Nat.card_congr f.symm, Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

end MechanicalPotential

namespace RibbonExamples

open WorkedExamples MechanicalPotential Set

variable (ℓ : Fin 3 → ℝ) (hℓ : ∀ i, 0 < ℓ i)

/-! ### The cyclic star -/

instance : Nonempty (threeStar ℓ hℓ).Edge := ⟨(0 : Fin 3)⟩

theorem threeStar_connected : (threeStar ℓ hℓ).Connected := by
  rw [FiniteMetricGraph.Connected, SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨none, fun w => ?_⟩
  rcases w with _ | i
  · exact SimpleGraph.Reachable.refl _
  · refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.fromRel_adj]
    exact ⟨by simp, Or.inl ⟨i, rfl, rfl⟩⟩

theorem starTurn_vertex (η : (threeStar ℓ hℓ).EdgeEnd) :
    EdgeEnd.vertex (threeStar ℓ hℓ) (turn 1 0 η) = EdgeEnd.vertex (threeStar ℓ hℓ) η := by
  revert η
  change ∀ η : Fin 3 × Bool, starEndpoint (turn 1 0 η).1 (turn 1 0 η).2 = starEndpoint η.1 η.2
  decide

theorem starTurn_sameCycle (η ζ : (threeStar ℓ hℓ).EdgeEnd)
    (h : EdgeEnd.vertex (threeStar ℓ hℓ) η = EdgeEnd.vertex (threeStar ℓ hℓ) ζ) :
    (turn 1 0).SameCycle η ζ := by
  revert η ζ
  change ∀ η ζ : Fin 3 × Bool, starEndpoint η.1 η.2 = starEndpoint ζ.1 ζ.2 →
    (turn 1 0).SameCycle η ζ
  decide

/-- **The cyclic star's vertex law** (Sec. XI.A): `F_c = (η₁ η₂ η₃)` at the centre, the identity
at the leaves, at every speed. -/
noncomputable def starCyclicScattering (V : MechanicalPotential (threeStar ℓ hℓ)) :
    BorelEnergyPreservingScattering V :=
  V.permutationScattering (vertexRestrict (turn 1 0) (starTurn_vertex ℓ hℓ))

/-- The law of `starCyclicScattering` at every speed is `turn 1 0`: `η_i ↦ η_{i+1}` on the central
ends `(i, false)`, the identity on the leaf ends `(i, true)`. -/
theorem starCyclicScattering_law (V : MechanicalPotential (threeStar ℓ hℓ)) (v : Option (Fin 3))
    (r : PositiveSpeed) (a : (threeStar ℓ hℓ).IncidentEnds v) :
    (EnergyPreservingScattering.speedPermutation V
      (starCyclicScattering ℓ hℓ V).toEnergyPreservingScattering v r a).1 = turn 1 0 a.1 := by
  rw [starCyclicScattering, speedPermutation_permutationScattering]
  rfl

/-- **The cyclic star above the potential (Sec. XI.E).**  For any lengths, any potential and any
`E > max_Γ V`, the energy shell `Σ_E` of the cyclic star consists of a single periodic orbit,
`Π_E` is a single cycle, and the ribbon graph has genus `0`. -/
theorem ribbon_cyclicStar_dynamic (V : MechanicalPotential (threeStar ℓ hℓ)) {E : ℝ}
    (hedge : ∀ e, ∀ q ∈ Icc 0 ((threeStar ℓ hℓ).length e), V.extension e q < E)
    (hv : ∀ v, V.vertexValue v < E) :
    ∃ hE : V.ShellRegular E,
      Nat.card {O : Set (RegularScatteringPhaseSpace (V := V) (starCyclicScattering ℓ hℓ V)) //
        ∃ (η : (threeStar ℓ hℓ).EdgeEnd) (hη : η ∈ V.allowedGerms E),
          O = V.shellOrbit (starCyclicScattering ℓ hℓ V) hE η hη} = 1 ∧
      (V.germCycles (starCyclicScattering ℓ hℓ V) E).card = 1 ∧
      (V.highEnergyRibbon (starCyclicScattering ℓ hℓ V) hv).genus = 0 := by
  obtain ⟨hE, hrot, hcyc, horb⟩ := V.ribbon_counts_of_perm (threeStar_connected ℓ hℓ)
    (turn 1 0) (starTurn_vertex ℓ hℓ) (starTurn_sameCycle ℓ hℓ) hedge hv
  unfold starCyclicScattering
  rw [hrot] at hcyc horb ⊢
  exact ⟨hE, horb.trans ribbon_cyclicStar.2.2.2.2.1, hcyc.trans ribbon_cyclicStar.2.2.2.2.1,
    ribbon_cyclicStar.2.2.2.2.2.2⟩

/-- The cyclic star at `V ≡ 0` and `E > 0`: one periodic orbit, genus `0`. -/
theorem ribbon_cyclicStar_zero {E : ℝ} (hE0 : 0 < E) :
    ∃ hE : (zeroPotential (threeStar ℓ hℓ)).ShellRegular E,
      Nat.card {O : Set (RegularScatteringPhaseSpace (V := zeroPotential (threeStar ℓ hℓ))
          (starCyclicScattering ℓ hℓ (zeroPotential (threeStar ℓ hℓ)))) //
        ∃ (η : (threeStar ℓ hℓ).EdgeEnd)
          (hη : η ∈ (zeroPotential (threeStar ℓ hℓ)).allowedGerms E),
          O = (zeroPotential (threeStar ℓ hℓ)).shellOrbit
            (starCyclicScattering ℓ hℓ (zeroPotential (threeStar ℓ hℓ))) hE η hη} = 1 ∧
      ((zeroPotential (threeStar ℓ hℓ)).highEnergyRibbon
        (starCyclicScattering ℓ hℓ (zeroPotential (threeStar ℓ hℓ))) (fun _ => hE0)).genus = 0 := by
  obtain ⟨hE, h1, -, h3⟩ := ribbon_cyclicStar_dynamic ℓ hℓ (zeroPotential (threeStar ℓ hℓ))
    (fun _ _ _ => hE0) (fun _ => hE0)
  exact ⟨hE, h1, h3⟩

/-! ### The theta graph -/

instance : Nonempty (theta ℓ hℓ).Edge := ⟨(0 : Fin 3)⟩

theorem theta_connected : (theta ℓ hℓ).Connected := by
  rw [FiniteMetricGraph.Connected, SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨false, fun w => ?_⟩
  cases w
  · exact SimpleGraph.Reachable.refl _
  · refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.fromRel_adj]
    exact ⟨by simp, Or.inl ⟨0, rfl, rfl⟩⟩

theorem thetaTurn_vertex (b : Fin 3) (η : (theta ℓ hℓ).EdgeEnd) :
    EdgeEnd.vertex (theta ℓ hℓ) (turn 1 b η) = EdgeEnd.vertex (theta ℓ hℓ) η := by
  rcases η with ⟨i, c⟩
  cases c <;> rfl

theorem thetaTurn_sameCycle (b : Fin 3) (hb : b ≠ 0) (η ζ : (theta ℓ hℓ).EdgeEnd)
    (h : EdgeEnd.vertex (theta ℓ hℓ) η = EdgeEnd.vertex (theta ℓ hℓ) ζ) :
    (turn 1 b).SameCycle η ζ := by
  revert η ζ
  change ∀ η ζ : Fin 3 × Bool, η.2 = ζ.2 → (turn 1 b).SameCycle η ζ
  revert b
  decide

/-- **The theta graph's vertex law with equal cyclic orders**: `(η₁ η₂ η₃)` at `a` and
`(η₁' η₂' η₃')` at `b`, at every speed. -/
noncomputable def thetaSameScattering (V : MechanicalPotential (theta ℓ hℓ)) :
    BorelEnergyPreservingScattering V :=
  V.permutationScattering (vertexRestrict (turn 1 1) (thetaTurn_vertex ℓ hℓ 1))

/-- **The theta graph's vertex law with the order at `b` reversed**: `(η₁ η₂ η₃)` at `a` and
`(η₃' η₂' η₁')` at `b`, at every speed. -/
noncomputable def thetaReversedScattering (V : MechanicalPotential (theta ℓ hℓ)) :
    BorelEnergyPreservingScattering V :=
  V.permutationScattering (vertexRestrict (turn 1 2) (thetaTurn_vertex ℓ hℓ 2))

/-- The law of `thetaSameScattering` at every speed is `turn 1 1`: `η_i ↦ η_{i+1}` at `a` and
`η_i' ↦ η_{i+1}'` at `b`. -/
theorem thetaSameScattering_law (V : MechanicalPotential (theta ℓ hℓ)) (v : Bool)
    (r : PositiveSpeed) (a : (theta ℓ hℓ).IncidentEnds v) :
    (EnergyPreservingScattering.speedPermutation V
      (thetaSameScattering ℓ hℓ V).toEnergyPreservingScattering v r a).1 = turn 1 1 a.1 := by
  rw [thetaSameScattering, speedPermutation_permutationScattering]
  rfl

/-- The law of `thetaReversedScattering` at every speed is `turn 1 2`: `η_i ↦ η_{i+1}` at `a` and
`η_i' ↦ η_{i+2}' = η_{i-1}'` at `b`. -/
theorem thetaReversedScattering_law (V : MechanicalPotential (theta ℓ hℓ)) (v : Bool)
    (r : PositiveSpeed) (a : (theta ℓ hℓ).IncidentEnds v) :
    (EnergyPreservingScattering.speedPermutation V
      (thetaReversedScattering ℓ hℓ V).toEnergyPreservingScattering v r a).1 = turn 1 2 a.1 := by
  rw [thetaReversedScattering, speedPermutation_permutationScattering]
  rfl

/-- **The theta graph with equal cyclic orders, above the potential (Sec. XI.E).**  For any
lengths, any potential and any `E > max_Γ V`, `Σ_E` consists of a single periodic orbit, `Π_E` is
a single cycle, and the ribbon graph has genus `1`. -/
theorem ribbon_theta_same_dynamic (V : MechanicalPotential (theta ℓ hℓ)) {E : ℝ}
    (hedge : ∀ e, ∀ q ∈ Icc 0 ((theta ℓ hℓ).length e), V.extension e q < E)
    (hv : ∀ v, V.vertexValue v < E) :
    ∃ hE : V.ShellRegular E,
      Nat.card {O : Set (RegularScatteringPhaseSpace (V := V) (thetaSameScattering ℓ hℓ V)) //
        ∃ (η : (theta ℓ hℓ).EdgeEnd) (hη : η ∈ V.allowedGerms E),
          O = V.shellOrbit (thetaSameScattering ℓ hℓ V) hE η hη} = 1 ∧
      (V.germCycles (thetaSameScattering ℓ hℓ V) E).card = 1 ∧
      (V.highEnergyRibbon (thetaSameScattering ℓ hℓ V) hv).genus = 1 := by
  obtain ⟨hE, hrot, hcyc, horb⟩ := V.ribbon_counts_of_perm (theta_connected ℓ hℓ)
    (turn 1 1) (thetaTurn_vertex ℓ hℓ 1) (thetaTurn_sameCycle ℓ hℓ 1 (by decide)) hedge hv
  unfold thetaSameScattering
  rw [hrot] at hcyc horb ⊢
  exact ⟨hE, horb.trans ribbon_theta_same.2.2.2.2.1, hcyc.trans ribbon_theta_same.2.2.2.2.1,
    ribbon_theta_same.2.2.2.2.2.2⟩

/-- **The theta graph with one cyclic order reversed, above the potential (Sec. XI.E).**  For any
lengths, any potential and any `E > max_Γ V`, `Σ_E` consists of three periodic orbits, `Π_E` has
three cycles, and the ribbon graph has genus `0`. -/
theorem ribbon_theta_reversed_dynamic (V : MechanicalPotential (theta ℓ hℓ)) {E : ℝ}
    (hedge : ∀ e, ∀ q ∈ Icc 0 ((theta ℓ hℓ).length e), V.extension e q < E)
    (hv : ∀ v, V.vertexValue v < E) :
    ∃ hE : V.ShellRegular E,
      Nat.card {O : Set (RegularScatteringPhaseSpace (V := V) (thetaReversedScattering ℓ hℓ V)) //
        ∃ (η : (theta ℓ hℓ).EdgeEnd) (hη : η ∈ V.allowedGerms E),
          O = V.shellOrbit (thetaReversedScattering ℓ hℓ V) hE η hη} = 3 ∧
      (V.germCycles (thetaReversedScattering ℓ hℓ V) E).card = 3 ∧
      (V.highEnergyRibbon (thetaReversedScattering ℓ hℓ V) hv).genus = 0 := by
  obtain ⟨hE, hrot, hcyc, horb⟩ := V.ribbon_counts_of_perm (theta_connected ℓ hℓ)
    (turn 1 2) (thetaTurn_vertex ℓ hℓ 2) (thetaTurn_sameCycle ℓ hℓ 2 (by decide)) hedge hv
  unfold thetaReversedScattering
  rw [hrot] at hcyc horb ⊢
  exact ⟨hE, horb.trans ribbon_theta_reversed.2.2.2.2.1,
    hcyc.trans ribbon_theta_reversed.2.2.2.2.1, ribbon_theta_reversed.2.2.2.2.2.2⟩

/-- The theta graph with equal orders at `V ≡ 0` and `E > 0`: one periodic orbit, genus `1`. -/
theorem ribbon_theta_same_zero {E : ℝ} (hE0 : 0 < E) :
    ∃ hE : (zeroPotential (theta ℓ hℓ)).ShellRegular E,
      Nat.card {O : Set (RegularScatteringPhaseSpace (V := zeroPotential (theta ℓ hℓ))
          (thetaSameScattering ℓ hℓ (zeroPotential (theta ℓ hℓ)))) //
        ∃ (η : (theta ℓ hℓ).EdgeEnd) (hη : η ∈ (zeroPotential (theta ℓ hℓ)).allowedGerms E),
          O = (zeroPotential (theta ℓ hℓ)).shellOrbit
            (thetaSameScattering ℓ hℓ (zeroPotential (theta ℓ hℓ))) hE η hη} = 1 ∧
      ((zeroPotential (theta ℓ hℓ)).highEnergyRibbon
        (thetaSameScattering ℓ hℓ (zeroPotential (theta ℓ hℓ))) (fun _ => hE0)).genus = 1 := by
  obtain ⟨hE, h1, -, h3⟩ := ribbon_theta_same_dynamic ℓ hℓ (zeroPotential (theta ℓ hℓ))
    (fun _ _ _ => hE0) (fun _ => hE0)
  exact ⟨hE, h1, h3⟩

/-- The theta graph with one order reversed at `V ≡ 0` and `E > 0`: three periodic orbits,
genus `0`. -/
theorem ribbon_theta_reversed_zero {E : ℝ} (hE0 : 0 < E) :
    ∃ hE : (zeroPotential (theta ℓ hℓ)).ShellRegular E,
      Nat.card {O : Set (RegularScatteringPhaseSpace (V := zeroPotential (theta ℓ hℓ))
          (thetaReversedScattering ℓ hℓ (zeroPotential (theta ℓ hℓ)))) //
        ∃ (η : (theta ℓ hℓ).EdgeEnd) (hη : η ∈ (zeroPotential (theta ℓ hℓ)).allowedGerms E),
          O = (zeroPotential (theta ℓ hℓ)).shellOrbit
            (thetaReversedScattering ℓ hℓ (zeroPotential (theta ℓ hℓ))) hE η hη} = 3 ∧
      ((zeroPotential (theta ℓ hℓ)).highEnergyRibbon
        (thetaReversedScattering ℓ hℓ (zeroPotential (theta ℓ hℓ))) (fun _ => hE0)).genus = 0 := by
  obtain ⟨hE, h1, -, h3⟩ := ribbon_theta_reversed_dynamic ℓ hℓ (zeroPotential (theta ℓ hℓ))
    (fun _ _ _ => hE0) (fun _ => hE0)
  exact ⟨hE, h1, h3⟩

end RibbonExamples

end HamiltonianMetricGraphs
