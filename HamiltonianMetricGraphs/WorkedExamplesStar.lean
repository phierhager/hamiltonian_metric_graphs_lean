/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.WorkedExamplesBasic
import HamiltonianMetricGraphs.Realization.GateLimit
import HamiltonianMetricGraphs.Realization.GraphFlow

/-!
# The three-star and the gate (Sections XI.A and XI.C)

## The graph

`threeStar ℓ hℓ` is the star `Γ⋆` with three edges `e_i` (`i : Fin 3`, the paper's `e₁, e₂, e₃`
being `0, 1, 2`) of lengths `ℓ_i`, joining a centre `c` (`none`) to three leaves (`some i`).  The
coordinate of `e_i` starts at the centre, so the central end is `η_i = (i, false)` and the leaf
end is `η_i' = (i, true)`.  The potential is `V ≡ 0` (`zeroPotential`).

## Section XI.A: dependence on the vertex law

* every `E > 0` is shell-regular, `κ_E(η_i) = η_i'`, `κ_E(η_i') = η_i` and
  `t_E(η_i) = t_E(η_i') = ℓ_i / √(2E)` (`threeStar_retrace_flightTime`);
* **cyclic routing** `F_c = (η₁ η₂ η₃)` (`starCyclicLaw`): `Π_E = (η₁ η₁' η₂ η₂' η₃ η₃')`, cycle
  type `(6)`, one cycle, of period `2L/√(2E)`, and the law is nonreversible
  (`threeStar_cyclic`);
* **reflection** `F_c = id` (`starReflectionLaw`): `Π_E = (η₁ η₁')(η₂ η₂')(η₃ η₃')`, cycle type
  `(2,2,2)`, three cycles, of periods `2ℓ_i/√(2E)` (`threeStar_reflection`);
* in both cases the shell mass (14) is `2L/√(2E)` (`threeStar_shellMass`).

The leaf laws are identities: a leaf has a single incident end, so *every* vertex law is the
identity there (`threeStar_incident_leaf`); this is why only the central law appears.

## Section XI.C: the gate

The paper compares the two central laws realized by Theorem IX.10 on the two energy windows
`K₋ = [1/2, 3/5]` and `K₊ = [3/2, 2]`: `F₋ = id` on `K₋` and `F₊ = (η₁ η₂)(η₃)` on `K₊`.  It makes
no claim about the law between the windows.  We therefore state the result for an *arbitrary*
Borel vertex law `S` of the paper on `(Γ⋆, V ≡ 0)` whose fixed-speed central permutation is `F₋`
at the speeds `√(2E)`, `E ∈ K₋`, and `F₊` at the speeds `√(2E)`, `E ∈ K₊` (`GateLaw`): each window
carries its constant law, and the energy-dependent law of the gate junction is one such `S`.  The
two constant laws themselves are instances (`gateLowLaw_isGateLow`, `gateHighLaw_isGateHigh`).
The laws actually realized by Theorem IX.10 (`gateRoutingLow`, `gateRoutingHigh` on the
realization's `starGraph`, windows `windowLow`, `windowHigh`) are treated in
`example_gate_realized`, which also restates the two realizations.
For `E ∈ K₋`: `Π_E = (η₁ η₁')(η₂ η₂')(η₃ η₃')`, cycle type `(2,2,2)`, three cycles of periods
`2ℓ_i/√(2E)`; for `E ∈ K₊`: `Π_E = (η₁ η₁' η₂ η₂')(η₃ η₃')`, cycle type `(4,2)`, two cycles of
periods `2(ℓ₁+ℓ₂)/√(2E)` and `2ℓ₃/√(2E)` (`example_gate`).

The cycles of `Π_E` are the periodic orbits of the shell by Theorem VIII.5 (`ShellCycles.lean`):
each cycle `c` gives one periodic orbit of least period `cyclePeriod`; the orbit counts are stated
at flow level, as the number of distinct `shellOrbit`s (`card_shellOrbits_eq_card_germCycles`).

## Proof strategy

All combinatorics happens on the length-free type `Fin 3 × Bool`, where it is decided by
`decide`; the graph `threeStar ℓ hℓ` has `EdgeEnd = Fin 3 × Bool` definitionally.
-/

namespace HamiltonianMetricGraphs

namespace WorkedExamples

open Set FiniteMetricGraph MechanicalPotential

/-! ### The graph -/

/-- The endpoints of the three-star: the coordinate of `e_i` starts at the centre `none` and ends
at the leaf `some i`. -/
def starEndpoint : Fin 3 → Bool → Option (Fin 3)
  | _, false => none
  | i, true => some i

/-- **The three-star** `Γ⋆` with edge lengths `ℓ_i`. -/
def threeStar (ℓ : Fin 3 → ℝ) (hℓ : ∀ i, 0 < ℓ i) : FiniteMetricGraph where
  Vertex := Option (Fin 3)
  Edge := Fin 3
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  endpoint := starEndpoint
  length := ℓ
  length_pos := hℓ

variable (ℓ : Fin 3 → ℝ) (hℓ : ∀ i, 0 < ℓ i)

instance threeStar_nonempty_edge : Nonempty (threeStar ℓ hℓ).Edge := ⟨(0 : Fin 3)⟩

/-- The potential `V ≡ 0` on the three-star. -/
abbrev starV : MechanicalPotential (threeStar ℓ hℓ) := zeroPotential (threeStar ℓ hℓ)

/-- The total length `L = ℓ₁ + ℓ₂ + ℓ₃`. -/
def totalLength : ℝ := ℓ 0 + ℓ 1 + ℓ 2

/-- A leaf has exactly one incident end, so every vertex law is the identity at a leaf. -/
theorem threeStar_incident_leaf {i : Fin 3} (ζ : (threeStar ℓ hℓ).IncidentEnds (some i)) :
    ζ.1 = (i, true) := by
  obtain ⟨⟨e, b⟩, h⟩ := ζ
  have h' : starEndpoint e b = some i := h
  cases b
  · exact absurd h' (by simp [starEndpoint])
  · simp only [starEndpoint, Option.some.injEq] at h'
    subst h'
    rfl

/-! ### Length-free combinatorics -/

/-- The cyclic central law `F_c = (η₁ η₂ η₃)`, identity at the leaves. -/
def cyclicRoute : Fin 3 × Bool → Fin 3 × Bool
  | (i, false) => (i + 1, false)
  | (i, true) => (i, true)

/-- The transmitting central law `F₊ = (η₁ η₂)(η₃)` of the gate, identity at the leaves. -/
def gateRoute : Fin 3 × Bool → Fin 3 × Bool
  | (0, false) => (1, false)
  | (1, false) => (0, false)
  | η => η

/-- The end step of the three-star with `V ≡ 0`, given the central routing `σ`: the flight from
`η_i` lands at the leaf end `η_i'` and is routed back to it; the flight from `η_i'` lands at
`η_i` and is routed to `σ(η_i)`. -/
def starPi (σ : Fin 3 × Bool → Fin 3 × Bool) : Fin 3 × Bool → Fin 3 × Bool
  | (i, false) => (i, true)
  | (i, true) => σ (i, false)

theorem cyclicRoute_vertex :
    ∀ η : Fin 3 × Bool,
      starEndpoint (cyclicRoute η).1 (cyclicRoute η).2 = starEndpoint η.1 η.2 := by
  decide

theorem gateRoute_vertex :
    ∀ η : Fin 3 × Bool, starEndpoint (gateRoute η).1 (gateRoute η).2 = starEndpoint η.1 η.2 := by
  decide

theorem cyclicRoute_bijective : Function.Bijective cyclicRoute := by decide

theorem gateRoute_bijective : Function.Bijective gateRoute := by decide

/-- The 6-cycle `(η₁ η₁' η₂ η₂' η₃ η₃')`. -/
def cyclicPerm : Equiv.Perm (Fin 3 × Bool) :=
  List.formPerm [(0, false), (0, true), (1, false), (1, true), (2, false), (2, true)]

/-- The product of transpositions `(η₁ η₁')(η₂ η₂')(η₃ η₃')`. -/
def reflectionPerm : Equiv.Perm (Fin 3 × Bool) :=
  List.formPerm [(0, false), (0, true)] * List.formPerm [(1, false), (1, true)] *
    List.formPerm [(2, false), (2, true)]

/-- The permutation `(η₁ η₁' η₂ η₂')(η₃ η₃')`. -/
def gatePerm : Equiv.Perm (Fin 3 × Bool) :=
  List.formPerm [(0, false), (0, true), (1, false), (1, true)] *
    List.formPerm [(2, false), (2, true)]

theorem starPi_cyclic : ∀ η, starPi cyclicRoute η = cyclicPerm η := by decide
theorem starPi_id : ∀ η, starPi id η = reflectionPerm η := by decide
theorem starPi_gate : ∀ η, starPi gateRoute η = gatePerm η := by decide

theorem cyclicPerm_cycleType : cyclicPerm.cycleType = {6} := by decide
theorem reflectionPerm_cycleType : reflectionPerm.cycleType = {2, 2, 2} := by decide
theorem gatePerm_cycleType : gatePerm.cycleType = {4, 2} := by decide

/-- The pair of ends `{η_i, η_i'}` of `e_i`. -/
def edgePair (i : Fin 3) : Finset (Fin 3 × Bool) := {(i, false), (i, true)}

/-- The 4-element cycle `{η₁, η₁', η₂, η₂'}` of the transmitting gate. -/
def throughPair : Finset (Fin 3 × Bool) := {(0, false), (0, true), (1, false), (1, true)}

theorem cyclic_reach :
    ∀ ζ ∈ (Finset.univ : Finset (Fin 3 × Bool)),
      ∃ k < 6, (starPi cyclicRoute)^[k] (0, false) = ζ := by
  decide

theorem edgePair_closed (i : Fin 3) : ∀ ζ ∈ edgePair i, starPi id ζ ∈ edgePair i := by
  revert i; decide

theorem edgePair_reach (i : Fin 3) :
    ∀ ζ ∈ edgePair i, ∃ k < 2, (starPi id)^[k] (i, false) = ζ := by
  revert i; decide

theorem throughPair_closed : ∀ ζ ∈ throughPair, starPi gateRoute ζ ∈ throughPair := by decide

theorem throughPair_reach :
    ∀ ζ ∈ throughPair, ∃ k < 4, (starPi gateRoute)^[k] (0, false) = ζ := by decide

theorem edgePair_two_closed : ∀ ζ ∈ edgePair 2, starPi gateRoute ζ ∈ edgePair 2 := by decide

theorem edgePair_two_reach :
    ∀ ζ ∈ edgePair 2, ∃ k < 2, (starPi gateRoute)^[k] (2, false) = ζ := by decide

theorem mem_edgePair (η : Fin 3 × Bool) : η ∈ edgePair η.1 := by
  revert η; decide

/-- The cycle map of the gate on `K₊`. -/
def gateCycle (η : Fin 3 × Bool) : Finset (Fin 3 × Bool) :=
  if η.1 = 2 then edgePair 2 else throughPair

theorem mem_gateCycle (η : Fin 3 × Bool) : η ∈ gateCycle η := by
  revert η; decide

theorem image_univ_eq :
    Finset.univ.image (fun _ : Fin 3 × Bool => (Finset.univ : Finset (Fin 3 × Bool))) =
      {Finset.univ} := by
  decide

theorem zero_mem_throughPair : ((0 : Fin 3), false) ∈ throughPair := by decide

theorem two_mem_edgePair : ((2 : Fin 3), false) ∈ edgePair 2 := by decide

theorem image_univ_card :
    (Finset.univ.image
      (fun _ : Fin 3 × Bool => (Finset.univ : Finset (Fin 3 × Bool)))).card = 1 := by
  decide

theorem image_edgePair_card :
    (Finset.univ.image (fun η : Fin 3 × Bool => edgePair η.1)).card = 3 := by decide

theorem image_gateCycle_card : (Finset.univ.image gateCycle).card = 2 := by decide

theorem cyclicRoute_not_involutive : ∃ η, cyclicRoute (cyclicRoute η) ≠ η :=
  ⟨(0, false), by decide⟩

/-! ### The vertex laws -/

/-- The cyclic central law `F_c = (η₁ η₂ η₃)` as a permutation vertex law. -/
def starCyclicLaw : PermutationLaw (threeStar ℓ hℓ) where
  route := cyclicRoute
  route_vertex := cyclicRoute_vertex
  route_bijective := cyclicRoute_bijective

/-- The reflecting central law `F_c = id` (identity everywhere) as a permutation vertex law. -/
def starReflectionLaw : PermutationLaw (threeStar ℓ hℓ) where
  route := id
  route_vertex _ := rfl
  route_bijective := Function.bijective_id

/-- The transmitting central law `F₊ = (η₁ η₂)(η₃)` as a permutation vertex law. -/
def starGateLaw : PermutationLaw (threeStar ℓ hℓ) where
  route := gateRoute
  route_vertex := gateRoute_vertex
  route_bijective := gateRoute_bijective

/-! ### Retrace map and flight times -/

theorem threeStar_shellRegular {E : ℝ} (hE0 : 0 < E) : (starV ℓ hℓ).ShellRegular E :=
  zeroPotential_shellRegular hE0

/-- **Sec. XI.A**: `κ_E(η_i) = η_i'`, `κ_E(η_i') = η_i` and `t_E(η_i) = t_E(η_i') = ℓ_i/√(2E)`. -/
theorem threeStar_retrace_flightTime {E : ℝ} (hE0 : 0 < E) (i : Fin 3) :
    (starV ℓ hℓ).retraceEnd E (i, false) = (i, true) ∧
      (starV ℓ hℓ).retraceEnd E (i, true) = (i, false) ∧
      (starV ℓ hℓ).flightTime E (i, false) = ℓ i / Real.sqrt (2 * E) ∧
      (starV ℓ hℓ).flightTime E (i, true) = ℓ i / Real.sqrt (2 * E) :=
  ⟨zeroPotential_retraceEnd (Γ := threeStar ℓ hℓ) hE0 (i, false),
    zeroPotential_retraceEnd (Γ := threeStar ℓ hℓ) hE0 (i, true),
    zeroPotential_flightTime (Γ := threeStar ℓ hℓ) hE0 (i, false),
    zeroPotential_flightTime (Γ := threeStar ℓ hℓ) hE0 (i, true)⟩

theorem threeStar_flightTime {E : ℝ} (hE0 : 0 < E) (η : (threeStar ℓ hℓ).EdgeEnd) :
    (starV ℓ hℓ).flightTime E η = ℓ η.1 / Real.sqrt (2 * E) :=
  zeroPotential_flightTime hE0 η

/-- The sum of the flight times over all six ends is `2L/√(2E)`. -/
theorem threeStar_sum_flightTime {E : ℝ} (hE0 : 0 < E) :
    ∑ η : (threeStar ℓ hℓ).EdgeEnd, (starV ℓ hℓ).flightTime E η =
      2 * totalLength ℓ / Real.sqrt (2 * E) := by
  simp only [threeStar_flightTime ℓ hℓ hE0]
  change ∑ η : Fin 3 × Bool, ℓ η.1 / Real.sqrt (2 * E) = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fin.sum_univ_three, totalLength]
  ring

/-- The sum of the flight times over the two ends of `e_i` is `2ℓ_i/√(2E)`. -/
theorem threeStar_sum_edgePair {E : ℝ} (hE0 : 0 < E) (i : Fin 3) :
    ∑ η ∈ (edgePair i : Finset (threeStar ℓ hℓ).EdgeEnd), (starV ℓ hℓ).flightTime E η =
      2 * ℓ i / Real.sqrt (2 * E) := by
  have hne : ((i, false) : Fin 3 × Bool) ≠ (i, true) := by simp
  change ∑ η ∈ ({(i, false), (i, true)} : Finset (Fin 3 × Bool)),
    (starV ℓ hℓ).flightTime E η = _
  rw [Finset.sum_pair hne, threeStar_flightTime ℓ hℓ hE0, threeStar_flightTime ℓ hℓ hE0]
  ring

/-! ### The end step of the star -/

/-- **The end step of the star with `V ≡ 0`.**  If at the speed `√(2E)` the fixed-speed vertex
permutation of `S` at the centre is `σ` on the central ends, then `Π_E = starPi σ`.  No
hypothesis is needed at the leaves (`threeStar_incident_leaf`). -/
theorem threeStar_germStep (S : BorelEnergyPreservingScattering (starV ℓ hℓ)) {E : ℝ}
    (hE0 : 0 < E) (σ : Fin 3 × Bool → Fin 3 × Bool)
    (hσ : ∀ r : PositiveSpeed, r.1 = Real.sqrt (2 * E) → ∀ i : Fin 3,
      (EnergyPreservingScattering.speedEndpoint (starV ℓ hℓ) S.toEnergyPreservingScattering
        none ⟨(i, false), rfl⟩ r).1 = σ (i, false))
    (η : (threeStar ℓ hℓ).EdgeEnd) :
    (starV ℓ hℓ).germStep S E η = starPi σ η := by
  have hE := threeStar_shellRegular ℓ hℓ hE0
  have hη := zeroPotential_mem_allowedGerms (Γ := threeStar ℓ hℓ) hE0 η
  rcases η with ⟨i, b⟩
  cases b
  · have hζ : ((starV ℓ hℓ).retraceStep (i, false)
        ((starV ℓ hℓ).germSpeed (i, false) E)).1 = ((i, true) : (threeStar ℓ hℓ).EdgeEnd) :=
      zeroPotential_retraceEnd hE0 (i, false)
    have hζa := zeroPotential_mem_allowedGerms (Γ := threeStar ℓ hℓ) hE0 (i, true)
    rw [(starV ℓ hℓ).germStep_eq_speedPermutation S hE hη hζ
      ⟨_, (starV ℓ hℓ).germSpeed_pos_iff.mpr hζa⟩ rfl]
    exact threeStar_incident_leaf ℓ hℓ (i := i) _
  · have hζ : ((starV ℓ hℓ).retraceStep (i, true)
        ((starV ℓ hℓ).germSpeed (i, true) E)).1 = ((i, false) : (threeStar ℓ hℓ).EdgeEnd) :=
      zeroPotential_retraceEnd hE0 (i, true)
    have hζa := zeroPotential_mem_allowedGerms (Γ := threeStar ℓ hℓ) hE0 (i, false)
    rw [(starV ℓ hℓ).germStep_eq_speedPermutation S hE hη hζ
      ⟨_, (starV ℓ hℓ).germSpeed_pos_iff.mpr hζa⟩ rfl]
    refine hσ _ ?_ i
    change Real.sqrt (2 * (E - 0)) = _
    rw [sub_zero]

/-- A permutation vertex law with central routing `σ` satisfies the hypothesis of
`threeStar_germStep` at every energy. -/
theorem permutationLaw_central (F : PermutationLaw (threeStar ℓ hℓ))
    (r : PositiveSpeed) (i : Fin 3) :
    (EnergyPreservingScattering.speedEndpoint (starV ℓ hℓ)
      (F.toBorelScattering (starV ℓ hℓ)).toEnergyPreservingScattering
        none ⟨(i, false), rfl⟩ r).1 = F.route (i, false) := by
  rw [PermutationLaw.speedEndpoint_toBorelScattering]
  rfl

/-! ### Section XI.A: cyclic routing -/

section Cyclic

variable {E : ℝ} (hE0 : 0 < E)

include hE0 in
theorem threeStar_cyclic_germStep (η : (threeStar ℓ hℓ).EdgeEnd) :
    (starV ℓ hℓ).germStep ((starCyclicLaw ℓ hℓ).toBorelScattering (starV ℓ hℓ)) E η =
      cyclicPerm η := by
  rw [threeStar_germStep ℓ hℓ _ hE0 cyclicRoute
    (fun r _ i => permutationLaw_central ℓ hℓ (starCyclicLaw ℓ hℓ) r i)]
  exact starPi_cyclic η

include hE0 in
theorem threeStar_cyclic_germCycle (η : (threeStar ℓ hℓ).EdgeEnd) :
    (starV ℓ hℓ).germCycle ((starCyclicLaw ℓ hℓ).toBorelScattering (starV ℓ hℓ)) E η =
      Finset.univ :=
  (starV ℓ hℓ).germCycle_eq_of_closed_of_mem _ (threeStar_shellRegular ℓ hℓ hE0)
    (zeroPotential_mem_allowedGerms hE0)
    (fun ζ => (threeStar_germStep ℓ hℓ _ hE0 cyclicRoute
      (fun r _ i => permutationLaw_central ℓ hℓ (starCyclicLaw ℓ hℓ) r i) ζ))
    (η := ((0 : Fin 3), false)) Finset.univ 6 (fun _ _ => Finset.mem_univ _)
    (Finset.mem_univ _) cyclic_reach (Finset.mem_univ η)

open Classical in
/-- **Sec. XI.A, cyclic routing.**  For `F_c = (η₁ η₂ η₃)` and `E > 0`:
`Π_E = (η₁ η₁' η₂ η₂' η₃ η₃')`, its cycle type is `(6)`, there is exactly one cycle (one
periodic orbit), every end lies on it, its period is `T(E) = 2L/√(2E)`, and the law is
nonreversible. -/
theorem threeStar_cyclic :
    let S := (starCyclicLaw ℓ hℓ).toBorelScattering (starV ℓ hℓ)
    (∀ η, (starV ℓ hℓ).germStep S E η = cyclicPerm η) ∧
      ((starV ℓ hℓ).shellGermPerm S (threeStar_shellRegular ℓ hℓ hE0)).cycleType = {6} ∧
      (starV ℓ hℓ).germCycles S E = {Finset.univ} ∧
      ((starV ℓ hℓ).germCycles S E).card = 1 ∧
      (∀ η, (starV ℓ hℓ).cyclePeriod S E η = 2 * totalLength ℓ / Real.sqrt (2 * E)) ∧
      ¬ S.toEnergyPreservingScattering.IsReversible := by
  intro S
  have hcyc := threeStar_cyclic_germCycle ℓ hℓ hE0
  have himage : (starV ℓ hℓ).germCycles S E = {Finset.univ} := by
    rw [(starV ℓ hℓ).germCycles_eq_image S (zeroPotential_mem_allowedGerms hE0) hcyc]
    exact image_univ_eq
  refine ⟨threeStar_cyclic_germStep ℓ hℓ hE0, ?_, himage, by rw [himage]; rfl, ?_, ?_⟩
  · rw [(starV ℓ hℓ).cycleType_shellGermPerm_eq S _ (zeroPotential_mem_allowedGerms hE0)
      cyclicPerm (threeStar_cyclic_germStep ℓ hℓ hE0)]
    exact cyclicPerm_cycleType
  · intro η
    rw [(starV ℓ hℓ).cyclePeriod_eq_of_germCycle_eq S (hcyc η)]
    exact threeStar_sum_flightTime ℓ hℓ hE0
  · rw [PermutationLaw.isReversible_toBorelScattering_iff]
    intro h
    obtain ⟨η, hη⟩ := cyclicRoute_not_involutive
    exact hη (h η)

end Cyclic

/-! ### Section XI.A: reflection -/

section Reflection

variable {E : ℝ} (hE0 : 0 < E)

open Classical in
/-- The end step and cycles of the star with `V ≡ 0` and any law reflecting at the centre at the
speed `√(2E)`; shared by the reflecting three-star and the gate on `K₋`. -/
theorem threeStar_reflecting (S : BorelEnergyPreservingScattering (starV ℓ hℓ))
    (hσ : ∀ r : PositiveSpeed, r.1 = Real.sqrt (2 * E) → ∀ i : Fin 3,
      (EnergyPreservingScattering.speedEndpoint (starV ℓ hℓ) S.toEnergyPreservingScattering
        none ⟨(i, false), rfl⟩ r).1 = (i, false)) :
    (∀ η, (starV ℓ hℓ).germStep S E η = reflectionPerm η) ∧
      ((starV ℓ hℓ).shellGermPerm S (threeStar_shellRegular ℓ hℓ hE0)).cycleType = {2, 2, 2} ∧
      (∀ η : (threeStar ℓ hℓ).EdgeEnd, (starV ℓ hℓ).germCycle S E η = edgePair η.1) ∧
      ((starV ℓ hℓ).germCycles S E).card = 3 ∧
      (∀ i : Fin 3, (starV ℓ hℓ).cyclePeriod S E (i, false) = 2 * ℓ i / Real.sqrt (2 * E) ∧
        (starV ℓ hℓ).cyclePeriod S E (i, true) = 2 * ℓ i / Real.sqrt (2 * E)) := by
  have hstep : ∀ η, (starV ℓ hℓ).germStep S E η = starPi id η :=
    threeStar_germStep ℓ hℓ S hE0 id hσ
  have hstep' : ∀ η, (starV ℓ hℓ).germStep S E η = reflectionPerm η := fun η => by
    rw [hstep]; exact starPi_id η
  have hcyc : ∀ η : (threeStar ℓ hℓ).EdgeEnd, (starV ℓ hℓ).germCycle S E η = edgePair η.1 :=
    fun η => (starV ℓ hℓ).germCycle_eq_of_closed_of_mem S (threeStar_shellRegular ℓ hℓ hE0)
      (zeroPotential_mem_allowedGerms hE0) hstep (η := (η.1, false)) (edgePair η.1) 2
      (edgePair_closed η.1) (Finset.mem_insert_self _ _) (edgePair_reach η.1) (mem_edgePair η)
  refine ⟨hstep', ?_, hcyc, ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [(starV ℓ hℓ).cycleType_shellGermPerm_eq S _ (zeroPotential_mem_allowedGerms hE0)
      reflectionPerm hstep']
    exact reflectionPerm_cycleType
  · rw [(starV ℓ hℓ).germCycles_eq_image S (zeroPotential_mem_allowedGerms hE0) hcyc]
    exact image_edgePair_card
  · rw [(starV ℓ hℓ).cyclePeriod_eq_of_germCycle_eq S (hcyc _)]
    exact threeStar_sum_edgePair ℓ hℓ hE0 i
  · rw [(starV ℓ hℓ).cyclePeriod_eq_of_germCycle_eq S (hcyc _)]
    exact threeStar_sum_edgePair ℓ hℓ hE0 i

open Classical in
/-- **Sec. XI.A, reflection.**  For `F_c = id` and `E > 0`: `Π_E = (η₁ η₁')(η₂ η₂')(η₃ η₃')`, its
cycle type is `(2,2,2)`, the cycle of `η_i` and `η_i'` is `{η_i, η_i'}`, there are three cycles
(three periodic orbits), with periods `2ℓ_i/√(2E)`. -/
theorem threeStar_reflection :
    let S := (starReflectionLaw ℓ hℓ).toBorelScattering (starV ℓ hℓ)
    (∀ η, (starV ℓ hℓ).germStep S E η = reflectionPerm η) ∧
      ((starV ℓ hℓ).shellGermPerm S (threeStar_shellRegular ℓ hℓ hE0)).cycleType = {2, 2, 2} ∧
      (∀ η : (threeStar ℓ hℓ).EdgeEnd, (starV ℓ hℓ).germCycle S E η = edgePair η.1) ∧
      ((starV ℓ hℓ).germCycles S E).card = 3 ∧
      (∀ i : Fin 3, (starV ℓ hℓ).cyclePeriod S E (i, false) = 2 * ℓ i / Real.sqrt (2 * E) ∧
        (starV ℓ hℓ).cyclePeriod S E (i, true) = 2 * ℓ i / Real.sqrt (2 * E)) :=
  threeStar_reflecting ℓ hℓ hE0 _
    (fun r _ i => permutationLaw_central ℓ hℓ (starReflectionLaw ℓ hℓ) r i)

end Reflection

/-- **The shell mass (14) of the three-star** is `2L/√(2E)` for *every* vertex law: the vertex
law only changes its decomposition into periodic orbits. -/
theorem threeStar_shellMass (S : BorelEnergyPreservingScattering (starV ℓ hℓ)) {E : ℝ}
    (hE0 : 0 < E) :
    ∑ c ∈ (starV ℓ hℓ).germCycles S E, ∑ ζ ∈ c, (starV ℓ hℓ).flightTime E ζ =
        2 * totalLength ℓ / Real.sqrt (2 * E) ∧
      ∑ e, (starV ℓ hℓ).shellMeasure E e Set.univ =
        ENNReal.ofReal (2 * totalLength ℓ / Real.sqrt (2 * E)) := by
  have hE := threeStar_shellRegular ℓ hℓ hE0
  have hfin : (starV ℓ hℓ).allowedFinset E = Finset.univ := by
    ext η
    simp only [Finset.mem_univ, iff_true, mem_allowedFinset]
    exact zeroPotential_mem_allowedGerms hE0 η
  obtain ⟨h1, h2⟩ := (starV ℓ hℓ).shellMass hE S
  rw [h2, hfin, threeStar_sum_flightTime ℓ hℓ hE0] at h1
  rw [h2, hfin, threeStar_sum_flightTime ℓ hℓ hE0]
  exact ⟨rfl, h1⟩

open Classical in
/-- **Section XI.A (the three-star), packaged.**  On the three-star with `V ≡ 0` and leaf laws
the identities, for every `E > 0`: `E` is shell-regular; `κ_E(η_i) = η_i'`, `κ_E(η_i') = η_i`,
`t_E(η_i) = t_E(η_i') = ℓ_i/√(2E)`; for the cyclic central law `Π_E = (η₁ η₁' η₂ η₂' η₃ η₃')`
with one cycle of period `2L/√(2E)`, and the law is nonreversible; for the reflecting law
`Π_E = (η₁ η₁')(η₂ η₂')(η₃ η₃')` with three cycles of periods `2ℓ_i/√(2E)`; the total shell mass
is `2L/√(2E)` in both cases. -/
theorem example_threeStar {E : ℝ} (hE0 : 0 < E) :
    (starV ℓ hℓ).ShellRegular E ∧
      (∀ i : Fin 3, (starV ℓ hℓ).retraceEnd E (i, false) = (i, true) ∧
        (starV ℓ hℓ).retraceEnd E (i, true) = (i, false) ∧
        (starV ℓ hℓ).flightTime E (i, false) = ℓ i / Real.sqrt (2 * E) ∧
        (starV ℓ hℓ).flightTime E (i, true) = ℓ i / Real.sqrt (2 * E)) ∧
      -- cyclic routing
      (let S := (starCyclicLaw ℓ hℓ).toBorelScattering (starV ℓ hℓ);
        (∀ η, (starV ℓ hℓ).germStep S E η = cyclicPerm η) ∧
        ((starV ℓ hℓ).shellGermPerm S (threeStar_shellRegular ℓ hℓ hE0)).cycleType = {6} ∧
        ((starV ℓ hℓ).germCycles S E).card = 1 ∧
        Nat.card {O : Set (RegularScatteringPhaseSpace (V := starV ℓ hℓ) S) //
          ∃ (η : (threeStar ℓ hℓ).EdgeEnd) (hη : η ∈ (starV ℓ hℓ).allowedGerms E),
            O = (starV ℓ hℓ).shellOrbit S (threeStar_shellRegular ℓ hℓ hE0) η hη} = 1 ∧
        (∀ η, (starV ℓ hℓ).cyclePeriod S E η = 2 * totalLength ℓ / Real.sqrt (2 * E)) ∧
        ¬ S.toEnergyPreservingScattering.IsReversible ∧
        ∑ e, (starV ℓ hℓ).shellMeasure E e Set.univ =
          ENNReal.ofReal (2 * totalLength ℓ / Real.sqrt (2 * E))) ∧
      -- reflection
      (let S := (starReflectionLaw ℓ hℓ).toBorelScattering (starV ℓ hℓ);
        (∀ η, (starV ℓ hℓ).germStep S E η = reflectionPerm η) ∧
        ((starV ℓ hℓ).shellGermPerm S (threeStar_shellRegular ℓ hℓ hE0)).cycleType =
          {2, 2, 2} ∧
        ((starV ℓ hℓ).germCycles S E).card = 3 ∧
        Nat.card {O : Set (RegularScatteringPhaseSpace (V := starV ℓ hℓ) S) //
          ∃ (η : (threeStar ℓ hℓ).EdgeEnd) (hη : η ∈ (starV ℓ hℓ).allowedGerms E),
            O = (starV ℓ hℓ).shellOrbit S (threeStar_shellRegular ℓ hℓ hE0) η hη} = 3 ∧
        (∀ i : Fin 3, (starV ℓ hℓ).cyclePeriod S E (i, false) = 2 * ℓ i / Real.sqrt (2 * E) ∧
          (starV ℓ hℓ).cyclePeriod S E (i, true) = 2 * ℓ i / Real.sqrt (2 * E)) ∧
        ∑ e, (starV ℓ hℓ).shellMeasure E e Set.univ =
          ENNReal.ofReal (2 * totalLength ℓ / Real.sqrt (2 * E))) := by
  obtain ⟨c1, c2, -, c4, c5, c6⟩ := threeStar_cyclic ℓ hℓ hE0
  obtain ⟨r1, r2, -, r4, r5⟩ := threeStar_reflection ℓ hℓ hE0
  exact ⟨threeStar_shellRegular ℓ hℓ hE0, threeStar_retrace_flightTime ℓ hℓ hE0,
    ⟨c1, c2, c4, by rw [card_shellOrbits_eq_card_germCycles, c4], c5, c6, (threeStar_shellMass ℓ hℓ
      ((starCyclicLaw ℓ hℓ).toBorelScattering (starV ℓ hℓ)) hE0).2⟩,
    ⟨r1, r2, r4, by rw [card_shellOrbits_eq_card_germCycles, r4], r5, (threeStar_shellMass ℓ hℓ
      ((starReflectionLaw ℓ hℓ).toBorelScattering (starV ℓ hℓ)) hE0).2⟩⟩

/-! ### Section XI.C: the gate -/

/-- The low window `K₋ = [1/2, 3/5]`. -/
def gateWindowLow : Set ℝ := Icc (1 / 2) (3 / 5)

/-- The high window `K₊ = [3/2, 2]`. -/
def gateWindowHigh : Set ℝ := Icc (3 / 2) 2

/-- **The gate law on the two windows**: a Borel vertex law on `(Γ⋆, V ≡ 0)` whose fixed-speed
central permutation at the speed `√(2E)` is `F₋ = id` for `E ∈ K₋` and `F₊ = (η₁ η₂)(η₃)` for
`E ∈ K₊`.  Nothing is assumed between the windows. -/
structure GateLaw (S : BorelEnergyPreservingScattering (starV ℓ hℓ)) : Prop where
  low : ∀ E ∈ gateWindowLow, ∀ r : PositiveSpeed, r.1 = Real.sqrt (2 * E) → ∀ i : Fin 3,
    (EnergyPreservingScattering.speedEndpoint (starV ℓ hℓ) S.toEnergyPreservingScattering
      none ⟨(i, false), rfl⟩ r).1 = (i, false)
  high : ∀ E ∈ gateWindowHigh, ∀ r : PositiveSpeed, r.1 = Real.sqrt (2 * E) → ∀ i : Fin 3,
    (EnergyPreservingScattering.speedEndpoint (starV ℓ hℓ) S.toEnergyPreservingScattering
      none ⟨(i, false), rfl⟩ r).1 = gateRoute (i, false)

/-- The constant law `F₋ = id` satisfies the `K₋` half of `GateLaw` (at every speed). -/
theorem gateLowLaw_isGateLow : ∀ E ∈ gateWindowLow, ∀ r : PositiveSpeed,
    r.1 = Real.sqrt (2 * E) → ∀ i : Fin 3,
    (EnergyPreservingScattering.speedEndpoint (starV ℓ hℓ)
      ((starReflectionLaw ℓ hℓ).toBorelScattering (starV ℓ hℓ)).toEnergyPreservingScattering
      none ⟨(i, false), rfl⟩ r).1 = (i, false) :=
  fun _ _ r _ i => permutationLaw_central ℓ hℓ (starReflectionLaw ℓ hℓ) r i

/-- The constant law `F₊ = (η₁ η₂)(η₃)` satisfies the `K₊` half of `GateLaw` (at every speed). -/
theorem gateHighLaw_isGateHigh : ∀ E ∈ gateWindowHigh, ∀ r : PositiveSpeed,
    r.1 = Real.sqrt (2 * E) → ∀ i : Fin 3,
    (EnergyPreservingScattering.speedEndpoint (starV ℓ hℓ)
      ((starGateLaw ℓ hℓ).toBorelScattering (starV ℓ hℓ)).toEnergyPreservingScattering
      none ⟨(i, false), rfl⟩ r).1 = gateRoute (i, false) :=
  fun _ _ r _ i => permutationLaw_central ℓ hℓ (starGateLaw ℓ hℓ) r i

theorem gateWindowLow_pos {E : ℝ} (hE : E ∈ gateWindowLow) : 0 < E := by
  have := hE.1; unfold gateWindowLow at hE; linarith [hE.1]

theorem gateWindowHigh_pos {E : ℝ} (hE : E ∈ gateWindowHigh) : 0 < E := by
  unfold gateWindowHigh at hE; linarith [hE.1]

open Classical in
/-- The gate above the barrier: the end step, cycle type `(4,2)`, two cycles and their periods,
for any law transmitting `η₁ ↔ η₂` at the centre at the speed `√(2E)`. -/
theorem threeStar_transmitting (S : BorelEnergyPreservingScattering (starV ℓ hℓ)) {E : ℝ}
    (hE0 : 0 < E)
    (hσ : ∀ r : PositiveSpeed, r.1 = Real.sqrt (2 * E) → ∀ i : Fin 3,
      (EnergyPreservingScattering.speedEndpoint (starV ℓ hℓ) S.toEnergyPreservingScattering
        none ⟨(i, false), rfl⟩ r).1 = gateRoute (i, false)) :
    (∀ η, (starV ℓ hℓ).germStep S E η = gatePerm η) ∧
      ((starV ℓ hℓ).shellGermPerm S (threeStar_shellRegular ℓ hℓ hE0)).cycleType = {4, 2} ∧
      (∀ η : (threeStar ℓ hℓ).EdgeEnd, (starV ℓ hℓ).germCycle S E η = gateCycle η) ∧
      ((starV ℓ hℓ).germCycles S E).card = 2 ∧
      (starV ℓ hℓ).cyclePeriod S E ((0 : Fin 3), false) = 2 * (ℓ 0 + ℓ 1) / Real.sqrt (2 * E) ∧
      (starV ℓ hℓ).cyclePeriod S E ((2 : Fin 3), false) = 2 * ℓ 2 / Real.sqrt (2 * E) := by
  have hE := threeStar_shellRegular ℓ hℓ hE0
  have hall := zeroPotential_mem_allowedGerms (Γ := threeStar ℓ hℓ) hE0
  have hstep : ∀ η, (starV ℓ hℓ).germStep S E η = starPi gateRoute η :=
    threeStar_germStep ℓ hℓ S hE0 gateRoute hσ
  have hstep' : ∀ η, (starV ℓ hℓ).germStep S E η = gatePerm η := fun η => by
    rw [hstep]; exact starPi_gate η
  have hthrough : ∀ η ∈ (throughPair : Finset (threeStar ℓ hℓ).EdgeEnd),
      (starV ℓ hℓ).germCycle S E η = throughPair := fun η hη =>
    (starV ℓ hℓ).germCycle_eq_of_closed_of_mem S hE hall hstep (η := ((0 : Fin 3), false))
      throughPair 4 throughPair_closed zero_mem_throughPair throughPair_reach hη
  have hthird : ∀ η ∈ (edgePair 2 : Finset (threeStar ℓ hℓ).EdgeEnd),
      (starV ℓ hℓ).germCycle S E η = edgePair 2 := fun η hη =>
    (starV ℓ hℓ).germCycle_eq_of_closed_of_mem S hE hall hstep (η := ((2 : Fin 3), false))
      (edgePair 2) 2 edgePair_two_closed two_mem_edgePair edgePair_two_reach hη
  have hcyc : ∀ η : (threeStar ℓ hℓ).EdgeEnd, (starV ℓ hℓ).germCycle S E η = gateCycle η := by
    intro η
    have hmem := mem_gateCycle η
    unfold gateCycle at hmem ⊢
    split_ifs at hmem ⊢
    · exact hthird η hmem
    · exact hthrough η hmem
  refine ⟨hstep', ?_, hcyc, ?_, ?_, ?_⟩
  · rw [(starV ℓ hℓ).cycleType_shellGermPerm_eq S hE hall gatePerm hstep']
    exact gatePerm_cycleType
  · rw [(starV ℓ hℓ).germCycles_eq_image S hall hcyc]
    exact image_gateCycle_card
  · refine ((starV ℓ hℓ).cyclePeriod_eq_of_germCycle_eq S
      (hthrough _ zero_mem_throughPair)).trans ?_
    change ∑ η ∈ ({(0, false), (0, true), (1, false), (1, true)} : Finset (Fin 3 × Bool)),
      (starV ℓ hℓ).flightTime E η = _
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_pair (by decide)]
    simp only [threeStar_flightTime ℓ hℓ hE0]
    ring
  · refine ((starV ℓ hℓ).cyclePeriod_eq_of_germCycle_eq S (hthird _ two_mem_edgePair)).trans ?_
    exact threeStar_sum_edgePair ℓ hℓ hE0 2

open Classical in
/-- **Section XI.C (the gate), packaged.**  Let `S` be any Borel vertex law on the star with
`V ≡ 0` whose central law is `F₋ = id` on `K₋ = [1/2, 3/5]` and `F₊ = (η₁ η₂)(η₃)` on
`K₊ = [3/2, 2]` (`GateLaw`; the leaf laws are automatically identities).

* For `E ∈ K₋`: `Π_E = (η₁ η₁')(η₂ η₂')(η₃ η₃')`, cycle type `(2,2,2)`, three cycles (three
  periodic orbits) with periods `2ℓ_i/√(2E)`.
* For `E ∈ K₊`: `Π_E = (η₁ η₁' η₂ η₂')(η₃ η₃')`, cycle type `(4,2)`, two cycles (two periodic
  orbits) with periods `2(ℓ₁+ℓ₂)/√(2E)` and `2ℓ₃/√(2E)`.

The constant laws `F₋`, `F₊` are instances of the respective halves of `GateLaw`
(`gateLowLaw_isGateLow`, `gateHighLaw_isGateHigh`). -/
theorem example_gate (S : BorelEnergyPreservingScattering (starV ℓ hℓ)) (hS : GateLaw ℓ hℓ S) :
    (∀ E (hE : E ∈ gateWindowLow),
      (∀ η, (starV ℓ hℓ).germStep S E η = reflectionPerm η) ∧
      ((starV ℓ hℓ).shellGermPerm S
        (threeStar_shellRegular ℓ hℓ (gateWindowLow_pos hE))).cycleType = {2, 2, 2} ∧
      ((starV ℓ hℓ).germCycles S E).card = 3 ∧
      Nat.card {O : Set (RegularScatteringPhaseSpace (V := starV ℓ hℓ) S) //
        ∃ (η : (threeStar ℓ hℓ).EdgeEnd) (hη : η ∈ (starV ℓ hℓ).allowedGerms E),
          O = (starV ℓ hℓ).shellOrbit S
            (threeStar_shellRegular ℓ hℓ (gateWindowLow_pos hE)) η hη} = 3 ∧
      (∀ i : Fin 3, (starV ℓ hℓ).cyclePeriod S E (i, false) = 2 * ℓ i / Real.sqrt (2 * E))) ∧
    (∀ E (hE : E ∈ gateWindowHigh),
      (∀ η, (starV ℓ hℓ).germStep S E η = gatePerm η) ∧
      ((starV ℓ hℓ).shellGermPerm S
        (threeStar_shellRegular ℓ hℓ (gateWindowHigh_pos hE))).cycleType = {4, 2} ∧
      ((starV ℓ hℓ).germCycles S E).card = 2 ∧
      Nat.card {O : Set (RegularScatteringPhaseSpace (V := starV ℓ hℓ) S) //
        ∃ (η : (threeStar ℓ hℓ).EdgeEnd) (hη : η ∈ (starV ℓ hℓ).allowedGerms E),
          O = (starV ℓ hℓ).shellOrbit S
            (threeStar_shellRegular ℓ hℓ (gateWindowHigh_pos hE)) η hη} = 2 ∧
      (starV ℓ hℓ).cyclePeriod S E ((0 : Fin 3), false) = 2 * (ℓ 0 + ℓ 1) / Real.sqrt (2 * E) ∧
      (starV ℓ hℓ).cyclePeriod S E ((2 : Fin 3), false) = 2 * ℓ 2 / Real.sqrt (2 * E)) := by
  refine ⟨fun E hE => ?_, fun E hE => ?_⟩
  · obtain ⟨h1, h2, -, h4, h5⟩ :=
      threeStar_reflecting ℓ hℓ (gateWindowLow_pos hE) S (hS.low E hE)
    exact ⟨h1, h2, h4, by rw [card_shellOrbits_eq_card_germCycles, h4], fun i => (h5 i).1⟩
  · obtain ⟨h1, h2, -, h4, h5, h6⟩ :=
      threeStar_transmitting ℓ hℓ S (gateWindowHigh_pos hE) (hS.high E hE)
    exact ⟨h1, h2, h4, by rw [card_shellOrbits_eq_card_germCycles, h4], h5, h6⟩

/-! ### Section XI.C for the laws realized by Theorem IX.10

Section XI.C compares the two central laws *realized in Theorem IX.10*
(`explicit_energy_dependent_junction`): on the star `Γ⋆ = starGraph` of the realization (three
edges of length `1`, branching vertex `0`, the end `η_i = (i, false)` at the branching vertex and
`η_i' = (i, true)` at the outer vertex `i + 1`), with `V ≡ 0`, the gated network realizes

* total reflection `F₋ = gateRoutingLow` on `K₋ = windowLow = [1/2, 3/5]`, and
* the transmitting law `F₊ = gateRoutingHigh = (η₁ η₂)(η₃)` on `K₊ = windowHigh = [3/2, 2]`.

This file computes the end permutation of the paper's metric-graph flow for exactly these laws,
`gateRoutingLow.toBorelScattering` and `gateRoutingHigh.toBorelScattering` on
`zeroPotential starGraph` (`example_gate_realized`):

* for `E ∈ K₋`: `Π_E = (η₁ η₁')(η₂ η₂')(η₃ η₃')`, cycle type `(2,2,2)`, three periodic orbits on
  `Σ_E`, with periods `2ℓ_i/√(2E)` (`ℓ_i = 1`);
* for `E ∈ K₊`: `Π_E = (η₁ η₁' η₂ η₂')(η₃ η₃')`, cycle type `(4,2)`, two periodic orbits on `Σ_E`,
  with periods `2(ℓ₁+ℓ₂)/√(2E)` and `2ℓ₃/√(2E)`;

together with the two realization statements of Theorem IX.10 on these windows.  The length-free
permutations `reflectionPerm`, `gatePerm` and the cycle data are those of `WorkedExamplesStar.lean`.
-/

/-- At an outer vertex of `starGraph` there is a single incident end. -/
theorem starGraph_incident_leaf {i : Fin 3}
    (ζ : starGraph.IncidentEnds (EdgeEnd.vertex starGraph ((i, true) : starGraph.EdgeEnd))) :
    ζ.1 = (i, true) := by
  obtain ⟨⟨e, b⟩, h⟩ := ζ
  have h' : (if b then e.succ else (0 : Fin 4)) = i.succ := h
  cases b
  · exact absurd h'.symm (Fin.succ_ne_zero i)
  · simp only [if_true, Fin.succ_inj] at h'
    subst h'
    rfl

/-- **The end step of `starGraph` with `V ≡ 0`**, given the central fixed-speed routing `σ` at the
speed `√(2E)`: `Π_E = starPi σ`. -/
theorem starGraph_germStep (S : BorelEnergyPreservingScattering (zeroPotential starGraph))
    {E : ℝ} (hE0 : 0 < E) (σ : Fin 3 × Bool → Fin 3 × Bool)
    (hσ : ∀ r : PositiveSpeed, r.1 = Real.sqrt (2 * E) → ∀ i : Fin 3,
      (EnergyPreservingScattering.speedEndpoint (zeroPotential starGraph)
        S.toEnergyPreservingScattering 0 ⟨(i, false), rfl⟩ r).1 = σ (i, false))
    (η : starGraph.EdgeEnd) :
    (zeroPotential starGraph).germStep S E η = starPi σ η := by
  have hE := zeroPotential_shellRegular (Γ := starGraph) hE0
  have hη := zeroPotential_mem_allowedGerms (Γ := starGraph) hE0 η
  rcases η with ⟨i, b⟩
  cases b
  · have hζ : ((zeroPotential starGraph).retraceStep (i, false)
        ((zeroPotential starGraph).germSpeed (i, false) E)).1 = ((i, true) : starGraph.EdgeEnd) :=
      zeroPotential_retraceEnd hE0 (i, false)
    have hζa := zeroPotential_mem_allowedGerms (Γ := starGraph) hE0 (i, true)
    rw [(zeroPotential starGraph).germStep_eq_speedPermutation S hE hη hζ
      ⟨_, (zeroPotential starGraph).germSpeed_pos_iff.mpr hζa⟩ rfl]
    exact starGraph_incident_leaf _
  · have hζ : ((zeroPotential starGraph).retraceStep (i, true)
        ((zeroPotential starGraph).germSpeed (i, true) E)).1 = ((i, false) : starGraph.EdgeEnd) :=
      zeroPotential_retraceEnd hE0 (i, true)
    have hζa := zeroPotential_mem_allowedGerms (Γ := starGraph) hE0 (i, false)
    rw [(zeroPotential starGraph).germStep_eq_speedPermutation S hE hη hζ
      ⟨_, (zeroPotential starGraph).germSpeed_pos_iff.mpr hζa⟩ rfl]
    refine hσ _ ?_ i
    change Real.sqrt (2 * (E - 0)) = _
    rw [sub_zero]

/-- The realized laws act at the branching vertex as `id` and `gateRoute = (η₁ η₂)(η₃)`. -/
theorem gateRoutingLow_central (r : PositiveSpeed) (i : Fin 3) :
    (EnergyPreservingScattering.speedEndpoint (zeroPotential starGraph)
      (gateRoutingLow.toBorelScattering (zeroPotential starGraph)).toEnergyPreservingScattering
      0 ⟨(i, false), rfl⟩ r).1 = id (i, false) := by
  rw [RoutingLaw.speedEndpoint_toBorelScattering]
  rfl

theorem starGermMap_false_eq : ∀ i : Fin 3, starGermMap (i, false) = gateRoute (i, false) := by
  decide

theorem gateRoutingHigh_central (r : PositiveSpeed) (i : Fin 3) :
    (EnergyPreservingScattering.speedEndpoint (zeroPotential starGraph)
      (gateRoutingHigh.toBorelScattering (zeroPotential starGraph)).toEnergyPreservingScattering
      0 ⟨(i, false), rfl⟩ r).1 = gateRoute (i, false) := by
  rw [RoutingLaw.speedEndpoint_toBorelScattering]
  exact starGermMap_false_eq i

theorem windowLow_pos {E : ℝ} (hE : E ∈ windowLow) : 0 < E := by
  have := hE.1; linarith

theorem windowHigh_pos {E : ℝ} (hE : E ∈ windowHigh) : 0 < E := by
  have := hE.1; linarith

theorem starGraph_flightTime {E : ℝ} (hE0 : 0 < E) (η : starGraph.EdgeEnd) :
    (zeroPotential starGraph).flightTime E η = 1 / Real.sqrt (2 * E) :=
  zeroPotential_flightTime hE0 η

theorem starGraph_sum_edgePair {E : ℝ} (hE0 : 0 < E) (i : Fin 3) :
    ∑ η ∈ (edgePair i : Finset starGraph.EdgeEnd), (zeroPotential starGraph).flightTime E η =
      2 * 1 / Real.sqrt (2 * E) := by
  have hne : ((i, false) : Fin 3 × Bool) ≠ (i, true) := by simp
  change ∑ η ∈ ({(i, false), (i, true)} : Finset (Fin 3 × Bool)),
    (zeroPotential starGraph).flightTime E η = _
  rw [Finset.sum_pair hne, starGraph_flightTime hE0, starGraph_flightTime hE0]
  ring

/-! ### The two windows -/

open Classical in
/-- **The realized gate on `K₋`**: `Π_E = (η₁ η₁')(η₂ η₂')(η₃ η₃')`, cycle type `(2,2,2)`, three
cycles and three periodic orbits, with periods `2ℓ_i/√(2E)`, `ℓ_i = 1`. -/
theorem realizedGate_low {E : ℝ} (hE : E ∈ windowLow) :
    let S := gateRoutingLow.toBorelScattering (zeroPotential starGraph)
    (∀ η, (zeroPotential starGraph).germStep S E η = reflectionPerm η) ∧
      ((zeroPotential starGraph).shellGermPerm S
        (zeroPotential_shellRegular (windowLow_pos hE))).cycleType = {2, 2, 2} ∧
      ((zeroPotential starGraph).germCycles S E).card = 3 ∧
      Nat.card {O : Set (RegularScatteringPhaseSpace (V := zeroPotential starGraph) S) //
        ∃ (η : starGraph.EdgeEnd) (hη : η ∈ (zeroPotential starGraph).allowedGerms E),
          O = (zeroPotential starGraph).shellOrbit S
            (zeroPotential_shellRegular (windowLow_pos hE)) η hη} = 3 ∧
      ∀ i : Fin 3, (zeroPotential starGraph).cyclePeriod S E (i, false) =
        2 * starGraph.length i / Real.sqrt (2 * E) := by
  intro S
  have hE0 := windowLow_pos hE
  have hS := zeroPotential_shellRegular (Γ := starGraph) hE0
  have hall := zeroPotential_mem_allowedGerms (Γ := starGraph) hE0
  have hstep : ∀ η, (zeroPotential starGraph).germStep S E η = starPi id η :=
    starGraph_germStep S hE0 id (fun r _ i => gateRoutingLow_central r i)
  have hstep' : ∀ η, (zeroPotential starGraph).germStep S E η = reflectionPerm η := fun η => by
    rw [hstep]; exact starPi_id η
  have hcyc : ∀ η : starGraph.EdgeEnd,
      (zeroPotential starGraph).germCycle S E η = edgePair η.1 :=
    fun η => (zeroPotential starGraph).germCycle_eq_of_closed_of_mem S hS hall hstep
      (η := (η.1, false)) (edgePair η.1) 2 (edgePair_closed η.1) (Finset.mem_insert_self _ _)
      (edgePair_reach η.1) (mem_edgePair η)
  have hcard : ((zeroPotential starGraph).germCycles S E).card = 3 := by
    rw [(zeroPotential starGraph).germCycles_eq_image S hall hcyc]
    exact image_edgePair_card
  refine ⟨hstep', ?_, hcard, by rw [card_shellOrbits_eq_card_germCycles, hcard], fun i => ?_⟩
  · rw [(zeroPotential starGraph).cycleType_shellGermPerm_eq S hS hall reflectionPerm hstep']
    exact reflectionPerm_cycleType
  · rw [(zeroPotential starGraph).cyclePeriod_eq_of_germCycle_eq S (hcyc _)]
    exact starGraph_sum_edgePair hE0 i

open Classical in
/-- **The realized gate on `K₊`**: `Π_E = (η₁ η₁' η₂ η₂')(η₃ η₃')`, cycle type `(4,2)`, two cycles
and two periodic orbits, with periods `2(ℓ₁+ℓ₂)/√(2E)` and `2ℓ₃/√(2E)`, `ℓ_i = 1`. -/
theorem realizedGate_high {E : ℝ} (hE : E ∈ windowHigh) :
    let S := gateRoutingHigh.toBorelScattering (zeroPotential starGraph)
    (∀ η, (zeroPotential starGraph).germStep S E η = gatePerm η) ∧
      ((zeroPotential starGraph).shellGermPerm S
        (zeroPotential_shellRegular (windowHigh_pos hE))).cycleType = {4, 2} ∧
      ((zeroPotential starGraph).germCycles S E).card = 2 ∧
      Nat.card {O : Set (RegularScatteringPhaseSpace (V := zeroPotential starGraph) S) //
        ∃ (η : starGraph.EdgeEnd) (hη : η ∈ (zeroPotential starGraph).allowedGerms E),
          O = (zeroPotential starGraph).shellOrbit S
            (zeroPotential_shellRegular (windowHigh_pos hE)) η hη} = 2 ∧
      (zeroPotential starGraph).cyclePeriod S E (0, false) =
        2 * (starGraph.length 0 + starGraph.length 1) / Real.sqrt (2 * E) ∧
      (zeroPotential starGraph).cyclePeriod S E (2, false) =
        2 * starGraph.length 2 / Real.sqrt (2 * E) := by
  intro S
  have hE0 := windowHigh_pos hE
  have hS := zeroPotential_shellRegular (Γ := starGraph) hE0
  have hall := zeroPotential_mem_allowedGerms (Γ := starGraph) hE0
  have hstep : ∀ η, (zeroPotential starGraph).germStep S E η = starPi gateRoute η :=
    starGraph_germStep S hE0 gateRoute (fun r _ i => gateRoutingHigh_central r i)
  have hstep' : ∀ η, (zeroPotential starGraph).germStep S E η = gatePerm η := fun η => by
    rw [hstep]; exact starPi_gate η
  have hthrough : ∀ η ∈ (throughPair : Finset starGraph.EdgeEnd),
      (zeroPotential starGraph).germCycle S E η = throughPair := fun η hη =>
    (zeroPotential starGraph).germCycle_eq_of_closed_of_mem S hS hall hstep
      (η := ((0 : Fin 3), false)) throughPair 4 throughPair_closed zero_mem_throughPair
      throughPair_reach hη
  have hthird : ∀ η ∈ (edgePair 2 : Finset starGraph.EdgeEnd),
      (zeroPotential starGraph).germCycle S E η = edgePair 2 := fun η hη =>
    (zeroPotential starGraph).germCycle_eq_of_closed_of_mem S hS hall hstep
      (η := ((2 : Fin 3), false)) (edgePair 2) 2 edgePair_two_closed two_mem_edgePair
      edgePair_two_reach hη
  have hcyc : ∀ η : starGraph.EdgeEnd, (zeroPotential starGraph).germCycle S E η = gateCycle η := by
    intro η
    have hmem := mem_gateCycle η
    unfold gateCycle at hmem ⊢
    split_ifs at hmem ⊢
    · exact hthird η hmem
    · exact hthrough η hmem
  have hcard : ((zeroPotential starGraph).germCycles S E).card = 2 := by
    rw [(zeroPotential starGraph).germCycles_eq_image S hall hcyc]
    exact image_gateCycle_card
  refine ⟨hstep', ?_, hcard, by rw [card_shellOrbits_eq_card_germCycles, hcard], ?_, ?_⟩
  · rw [(zeroPotential starGraph).cycleType_shellGermPerm_eq S hS hall gatePerm hstep']
    exact gatePerm_cycleType
  · rw [(zeroPotential starGraph).cyclePeriod_eq_of_germCycle_eq S
      (hthrough _ zero_mem_throughPair)]
    change ∑ η ∈ ({(0, false), (0, true), (1, false), (1, true)} : Finset (Fin 3 × Bool)),
      (zeroPotential starGraph).flightTime E η = _
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_pair (by decide)]
    simp only [starGraph_flightTime hE0]
    ring
  · rw [(zeroPotential starGraph).cyclePeriod_eq_of_germCycle_eq S (hthird _ two_mem_edgePair)]
    exact starGraph_sum_edgePair hE0 2

open Classical in
/-- **Section XI.C for the laws realized by Theorem IX.10.**  The gated network realizes
`gateRoutingLow = F₋ = id` on `K₋ = windowLow` and `gateRoutingHigh = F₊ = (η₁ η₂)(η₃)` on
`K₊ = windowHigh` (Theorem IX.10); for the paper's flow with these laws on `(starGraph, V ≡ 0)`:

* for `E ∈ K₋`: `Π_E = (η₁ η₁')(η₂ η₂')(η₃ η₃')`, cycle type `(2,2,2)`, three periodic orbits on
  `Σ_E`, with periods `2ℓ_i/√(2E)`;
* for `E ∈ K₊`: `Π_E = (η₁ η₁' η₂ η₂')(η₃ η₃')`, cycle type `(4,2)`, two periodic orbits on `Σ_E`,
  with periods `2(ℓ₁+ℓ₂)/√(2E)` and `2ℓ₃/√(2E)`.

The edges of `starGraph` have length `ℓ_i = 1` (`starGraph_length_eq_one`). -/
theorem example_gate_realized :
    gateNetwork.RealizesOnEnergyWindow (zeroPotential starGraph) windowLow gateRoutingLow
        (1 / 100) ∧
      gateNetwork.RealizesOnEnergyWindow (zeroPotential starGraph) windowHigh gateRoutingHigh
        (1 / 100) ∧
      (∀ E (hE : E ∈ windowLow),
        let S := gateRoutingLow.toBorelScattering (zeroPotential starGraph)
        (∀ η, (zeroPotential starGraph).germStep S E η = reflectionPerm η) ∧
        ((zeroPotential starGraph).shellGermPerm S
          (zeroPotential_shellRegular (windowLow_pos hE))).cycleType = {2, 2, 2} ∧
        Nat.card {O : Set (RegularScatteringPhaseSpace (V := zeroPotential starGraph) S) //
          ∃ (η : starGraph.EdgeEnd) (hη : η ∈ (zeroPotential starGraph).allowedGerms E),
            O = (zeroPotential starGraph).shellOrbit S
              (zeroPotential_shellRegular (windowLow_pos hE)) η hη} = 3 ∧
        ∀ i : Fin 3, (zeroPotential starGraph).cyclePeriod S E (i, false) =
          2 * starGraph.length i / Real.sqrt (2 * E)) ∧
      ∀ E (hE : E ∈ windowHigh),
        let S := gateRoutingHigh.toBorelScattering (zeroPotential starGraph)
        (∀ η, (zeroPotential starGraph).germStep S E η = gatePerm η) ∧
        ((zeroPotential starGraph).shellGermPerm S
          (zeroPotential_shellRegular (windowHigh_pos hE))).cycleType = {4, 2} ∧
        Nat.card {O : Set (RegularScatteringPhaseSpace (V := zeroPotential starGraph) S) //
          ∃ (η : starGraph.EdgeEnd) (hη : η ∈ (zeroPotential starGraph).allowedGerms E),
            O = (zeroPotential starGraph).shellOrbit S
              (zeroPotential_shellRegular (windowHigh_pos hE)) η hη} = 2 ∧
        (zeroPotential starGraph).cyclePeriod S E (0, false) =
          2 * (starGraph.length 0 + starGraph.length 1) / Real.sqrt (2 * E) ∧
        (zeroPotential starGraph).cyclePeriod S E (2, false) =
          2 * starGraph.length 2 / Real.sqrt (2 * E) := by
  refine ⟨gateNetwork_realizes_low, gateNetwork_realizes_high, fun E hE => ?_, fun E hE => ?_⟩
  · obtain ⟨h1, h2, -, h4, h5⟩ := realizedGate_low hE
    exact ⟨h1, h2, h4, h5⟩
  · obtain ⟨h1, h2, -, h4, h5, h6⟩ := realizedGate_high hE
    exact ⟨h1, h2, h4, h5, h6⟩

end WorkedExamples

end HamiltonianMetricGraphs
