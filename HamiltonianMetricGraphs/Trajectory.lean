/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.EdgeFlight
import HamiltonianMetricGraphs.NoZeno

/-!
# Recursive scattered flight states

This module packages the concrete one-flight dichotomy into a typed recursive state.  A state
contains a physical segment starting at a regular energy.  Its successor is present exactly when
the segment-duration set is bounded, in which case the maximal arrival is scattered and a new
outgoing physical segment is selected.  An absent successor is the genuine global no-hit branch,
not a failed choice.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- A concrete edge flight together with the regularity of its initial mechanical energy. -/
structure FlightState where
  edge : Γ.Edge
  state : ℝ × ℝ
  segment : V.PhysicalEdgeSegment edge state
  regular : V.hamiltonian edge state.1 state.2 ∉ V.exceptionalEnergies

namespace FlightState

/-- The energy carried by a flight state. -/
noncomputable def energy (a : V.FlightState) : ℝ := V.hamiltonian a.edge a.state.1 a.state.2

@[simp] theorem energy_eq (a : V.FlightState) : a.energy =
    V.hamiltonian a.edge a.state.1 a.state.2 := rfl

/-- A flight state departs a vertex germ with outgoing momentum.  Every recursive scattered
successor has this shape, which is exactly the hypothesis of the uniform no-Zeno separation
estimate. -/
def IsOutgoing (b : V.FlightState) : Prop :=
  ∃ η₀ : Γ.EdgeEnd, η₀.1 = b.edge ∧
    b.state.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ η₀ ∧
    FiniteMetricGraph.EdgeEnd.sign Γ η₀ * b.state.2 < 0

/-- A regular interior edge state starts a recursive flight state. -/
noncomputable def ofInterior {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x.1 ∈ Ioo (0 : ℝ) (Γ.length e))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) : V.FlightState :=
  {
    edge := e
    state := x
    segment := Classical.choose (V.exists_physicalEdgeSegment_from_interior hx)
    regular := hregular
  }

/-- A regular outgoing boundary covector starts a recursive flight state. -/
noncomputable def ofOutgoingBoundary {v : Γ.Vertex} (α : Γ.OutgoingBoundary v)
    (hregular : V.boundaryEnergy α.1 ∉ V.exceptionalEnergies) : V.FlightState :=
  {
    edge := α.1.germ.1
    state := (FiniteMetricGraph.EdgeEnd.coordinate Γ α.1.germ, α.1.momentum)
    segment := Classical.choose (V.exists_physicalEdgeSegment_from_outgoingBoundary α)
    regular := by
      rw [← V.boundaryEnergy_eq_edgeHamiltonian α.1]
      exact hregular
  }

@[simp] theorem ofInterior_state {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x.1 ∈ Ioo (0 : ℝ) (Γ.length e))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    (ofInterior (V := V) hx hregular).state = x := rfl

@[simp] theorem ofInterior_edge {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x.1 ∈ Ioo (0 : ℝ) (Γ.length e))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    (ofInterior (V := V) hx hregular).edge = e := rfl

@[simp] theorem ofOutgoingBoundary_state {v : Γ.Vertex} (α : Γ.OutgoingBoundary v)
    (hregular : V.boundaryEnergy α.1 ∉ V.exceptionalEnergies) :
    (ofOutgoingBoundary (V := V) α hregular).state =
      (FiniteMetricGraph.EdgeEnd.coordinate Γ α.1.germ, α.1.momentum) := rfl

/-- The deterministic successor of a flight state.  It is `none` precisely in the unbounded
duration (global no-hit) alternative. -/
noncomputable def next (S : BorelEnergyPreservingScattering V) :
    V.FlightState → Option (V.FlightState) := by
  classical
  exact fun a => if hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state) then
    let α := a.segment.maximalArrivalIncoming hbdd a.regular
    let β := S.map α.1.germ.vertex α
    let k := Classical.choose
      (V.exists_physicalEdgeSegment_after_maximalArrival a.segment hbdd a.regular S)
    some {
      edge := β.1.germ.1
      state := (FiniteMetricGraph.EdgeEnd.coordinate Γ β.1.germ, β.1.momentum)
      segment := k
      regular := by
        change V.hamiltonian β.1.germ.1
          (FiniteMetricGraph.EdgeEnd.coordinate Γ β.1.germ) β.1.momentum ∉ V.exceptionalEnergies
        rw [← V.boundaryEnergy_eq_edgeHamiltonian β.1]
        have hE := V.scattered_maximalArrival_energy_eq_initial a.segment hbdd a.regular S
        rw [show V.boundaryEnergy β.1 = V.hamiltonian a.edge a.state.1 a.state.2 by
          simpa [α, β] using hE]
        exact a.regular
    }
  else none

/-- A nonterminal recursive successor is regular and begins at exactly the scattered maximal
arrival of the preceding state. -/
theorem next_eq_some_of_bddAbove (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    ∃ b : V.FlightState, next (V := V) S a = some b ∧
      b.state =
        (FiniteMetricGraph.EdgeEnd.coordinate Γ
          (S.map (a.segment.maximalArrivalIncoming hbdd a.regular).1.germ.vertex
            (a.segment.maximalArrivalIncoming hbdd a.regular)).1.germ,
          (S.map (a.segment.maximalArrivalIncoming hbdd a.regular).1.germ.vertex
            (a.segment.maximalArrivalIncoming hbdd a.regular)).1.momentum) ∧
      b.energy = a.energy ∧ b.IsOutgoing ∧
      b.edge = (S.map (a.segment.maximalArrivalIncoming hbdd a.regular).1.germ.vertex
        (a.segment.maximalArrivalIncoming hbdd a.regular)).1.germ.1 := by
  classical
  unfold next
  simp only [if_pos hbdd]
  let α := a.segment.maximalArrivalIncoming hbdd a.regular
  let β := S.map α.1.germ.vertex α
  let k := Classical.choose
    (V.exists_physicalEdgeSegment_after_maximalArrival a.segment hbdd a.regular S)
  let b : V.FlightState := {
    edge := β.1.germ.1
    state := (FiniteMetricGraph.EdgeEnd.coordinate Γ β.1.germ, β.1.momentum)
    segment := k
    regular := by
      change V.hamiltonian β.1.germ.1
        (FiniteMetricGraph.EdgeEnd.coordinate Γ β.1.germ) β.1.momentum ∉ V.exceptionalEnergies
      rw [← V.boundaryEnergy_eq_edgeHamiltonian β.1]
      have hE := V.scattered_maximalArrival_energy_eq_initial a.segment hbdd a.regular S
      rw [show V.boundaryEnergy β.1 = V.hamiltonian a.edge a.state.1 a.state.2 by
        simpa [α, β] using hE]
      exact a.regular
  }
  refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
  · simp [next, hbdd, α, β, k, b]
  · rfl
  · change V.hamiltonian β.1.germ.1
      (FiniteMetricGraph.EdgeEnd.coordinate Γ β.1.germ) β.1.momentum =
        V.hamiltonian a.edge a.state.1 a.state.2
    rw [← V.boundaryEnergy_eq_edgeHamiltonian β.1]
    have hE := V.scattered_maximalArrival_energy_eq_initial a.segment hbdd a.regular S
    simpa [α, β] using hE
  · exact ⟨β.1.germ, rfl, rfl, β.2.2⟩
  · rfl

/-- The recursive successor is absent exactly when the preceding state has an unbounded
duration set, and then its already-constructed `unboundedCurve` is the no-hit evolution. -/
theorem next_eq_none_of_not_bddAbove (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hub : ¬ BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    next (V := V) S a = none := by
  classical
  unfold next
  simp [hub]

/-- **Termination criterion.**  The recursive chain stops at a flight state exactly when that
flight has unbounded duration (the global no-hit / escape branch).  This is the case split
underlying the forward trajectory of a *terminating* chain: past the last impact the trajectory is
the single unbounded escape flight. -/
theorem next_eq_none_iff (S : BorelEnergyPreservingScattering V) (a : V.FlightState) :
    next (V := V) S a = none ↔
      ¬ BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state) := by
  constructor
  · intro h
    by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)
    · obtain ⟨c, hc, -, -, -, -⟩ := next_eq_some_of_bddAbove (V := V) S a hbdd
      rw [hc] at h
      simp at h
    · exact hbdd
  · exact next_eq_none_of_not_bddAbove (V := V) S a

/-- Every recursive scattered successor departs a vertex germ with outgoing momentum. -/
theorem next_isOutgoing (S : BorelEnergyPreservingScattering V) {a b : V.FlightState}
    (hnext : next (V := V) S a = some b) : b.IsOutgoing := by
  classical
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)
  · obtain ⟨c, hc, -, -, hout, -⟩ := next_eq_some_of_bddAbove (V := V) S a hbdd
    rw [hc] at hnext
    injection hnext with hbc
    rwa [← hbc]
  · rw [next_eq_none_of_not_bddAbove (V := V) S a hbdd] at hnext
    exact absurd hnext (by simp)

/-- The uniform no-Zeno separation constant at the flight-state level: over a compact regular
energy window `K`, every outgoing flight state whose flight terminates lasts at least a fixed
positive time before its next impact. -/
theorem exists_uniform_impactDuration_lower_bound [Nonempty Γ.Edge] (K : Set ℝ)
    (hKcompact : IsCompact K) (hregular : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (b : V.FlightState), b.IsOutgoing → b.energy ∈ K →
      (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state)) →
      τ ≤ sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
  obtain ⟨τ, hτ, hbound⟩ :=
    EdgeFirstHit.exists_uniform_duration_lower_bound_outgoing V K hKcompact hregular
  refine ⟨τ, hτ, ?_⟩
  intro b hout hEK hbdd
  obtain ⟨η₀, hη₀, hstate, hsign⟩ := hout
  have hle := hbound (b.segment.toEdgeFirstHit hbdd) hEK hη₀ hstate hsign
  rwa [PhysicalEdgeSegment.toEdgeFirstHit_duration] at hle

/-- The duration to the next impact, when the flight has a finite maximal endpoint. -/
noncomputable def impactDuration (a : V.FlightState) : Option ℝ :=
  by
    classical
    exact if hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state) then
      some (sSup (PhysicalEdgeSegment.durationSet V a.edge a.state))
    else none

theorem impactDuration_eq_some_of_bddAbove (a : V.FlightState)
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    a.impactDuration = some (sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) := by
  simp [impactDuration, hbdd]

theorem impactDuration_eq_none_of_not_bddAbove (a : V.FlightState)
    (hub : ¬ BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    a.impactDuration = none := by
  simp [impactDuration, hub]

theorem impactDuration_pos_of_bddAbove (a : V.FlightState)
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    0 < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state) := by
  exact lt_of_lt_of_le a.segment.duration_pos
    (le_csSup hbdd a.segment.mem_durationSet)

/-- Every actual successor has exactly the predecessor's mechanical energy. -/
theorem next_energy_eq_of_eq_some (S : BorelEnergyPreservingScattering V)
    (a b : V.FlightState) (hnext : next (V := V) S a = some b) :
    b.energy = a.energy := by
  classical
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)
  · obtain ⟨c, hc, -, henergy, -, -⟩ := next_eq_some_of_bddAbove (V := V) S a hbdd
    rw [hc] at hnext
    injection hnext with hbc
    simpa [hbc] using henergy
  · rw [next_eq_none_of_not_bddAbove (V := V) S a hbdd] at hnext
    contradiction

/-- The concrete phase-space curve of a single flight state: the completed maximal curve if the
flight terminates at an impact, and the global no-hit curve otherwise.  Its position component is
continuous throughout and it solves Hamilton's equation on the open flight interval. -/
noncomputable def flightCurve (a : V.FlightState) : ℝ → ℝ × ℝ := by
  classical
  exact if hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state) then
    a.segment.maximalCurveClosed hbdd
  else a.segment.unboundedCurve hbdd

@[simp] theorem flightCurve_zero (a : V.FlightState) : flightCurve V a 0 = a.state := by
  classical
  unfold flightCurve
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)
  · rw [dif_pos hbdd]; exact a.segment.maximalCurveClosed_initial hbdd
  · rw [dif_neg hbdd]; exact a.segment.unboundedCurve_initial hbdd

/-- The position component of a flight state's curve stays on the closed physical edge for every
nonnegative time (up to the impact time in the terminating case). -/
theorem flightCurve_physical (a : V.FlightState) {t : ℝ} (ht0 : 0 ≤ t)
    (htdur : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      t ≤ sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    (flightCurve V a t).1 ∈ Set.Icc (0 : ℝ) (Γ.length a.edge) := by
  classical
  unfold flightCurve
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)
  · rw [dif_pos hbdd]
    exact a.segment.maximalCurveClosed_physical hbdd ⟨ht0, htdur hbdd⟩
  · rw [dif_neg hbdd]
    exact a.segment.unboundedCurve_physical_at hbdd ht0

/-- Strictly before the first impact (and always at positive time in the no-hit case) the flight
curve is in the open edge. -/
theorem flightCurve_interior (a : V.FlightState) {t : ℝ} (ht0 : 0 < t)
    (ht : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      t < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    (flightCurve V a t).1 ∈ Set.Ioo (0 : ℝ) (Γ.length a.edge) := by
  classical
  unfold flightCurve
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)
  · rw [dif_pos hbdd]
    exact a.segment.maximalCurveClosed_interior hbdd ⟨ht0, ht hbdd⟩
  · rw [dif_neg hbdd]
    exact a.segment.unboundedCurve_interior_at hbdd ht0

/-- Energy is conserved along a flight state's curve at every valid nonnegative time. -/
theorem flightCurve_hamiltonian_eq (a : V.FlightState) {t : ℝ} (ht0 : 0 ≤ t)
    (htdur : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      t ≤ sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    V.hamiltonian a.edge (flightCurve V a t).1 (flightCurve V a t).2 = a.energy := by
  classical
  rw [energy_eq]
  unfold flightCurve
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)
  · rw [dif_pos hbdd]
    exact a.segment.maximalCurveClosed_hamiltonian_eq_initial hbdd ⟨ht0, htdur hbdd⟩
  · rw [dif_neg hbdd]
    exact a.segment.unboundedCurve_hamiltonian_eq_initial hbdd ht0

/-- The momentum-reversed flight curve carries the same energy: the energy conservation of the
time-reversed (backward) trajectory, needed to build backward flights by inverse scattering. -/
theorem flightCurve_reversed_hamiltonian_eq (a : V.FlightState) {t : ℝ} (ht0 : 0 ≤ t)
    (htdur : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      t ≤ sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    V.hamiltonian a.edge (flightCurve V a t).1 (-(flightCurve V a t).2) = a.energy := by
  rw [V.hamiltonian_neg_momentum a.edge (flightCurve V a t).1 (flightCurve V a t).2]
  exact flightCurve_hamiltonian_eq V a ht0 htdur

/-- The **backward** flight state at interior time `s`: the momentum-reversed point
`((flightCurve a s).1, -(flightCurve a s).2)` starts a fresh (forward) flight state whose forward
evolution retraces the original flight toward its departure vertex.  This is the inverse-scattering
building block of the backward trajectory (step 5); it is regular because momentum reversal
preserves the (regular) energy, and it is interior because it shares the position of an interior
flight point. -/
noncomputable def backwardRestart (a : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) : V.FlightState :=
  ofInterior (V := V) (e := a.edge)
    (x := ((flightCurve V a s).1, -(flightCurve V a s).2))
    (flightCurve_interior V a hs0 hs)
    (by
      rw [show V.hamiltonian a.edge (flightCurve V a s).1 (-(flightCurve V a s).2) = a.energy from
        flightCurve_reversed_hamiltonian_eq V a hs0.le (fun hbdd => (hs hbdd).le)]
      exact a.regular)

@[simp] theorem backwardRestart_edge (a : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    (backwardRestart V a hs0 hs).edge = a.edge := rfl

@[simp] theorem backwardRestart_state (a : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    (backwardRestart V a hs0 hs).state = ((flightCurve V a s).1, -(flightCurve V a s).2) := rfl

/-- The backward flight state carries the same conserved energy as the original flight. -/
theorem backwardRestart_energy (a : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    (backwardRestart V a hs0 hs).energy = a.energy := by
  rw [energy_eq, backwardRestart_state]
  exact flightCurve_reversed_hamiltonian_eq V a hs0.le (fun hbdd => (hs hbdd).le)

/-- The flight state reached after time `s` (strictly before the first impact, or any positive
time in the no-hit case): a fresh flight state based at `flightCurve a s`. -/
noncomputable def restart (a : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) : V.FlightState :=
  ofInterior (V := V) (e := a.edge) (x := flightCurve V a s) (flightCurve_interior V a hs0 hs)
    (by
      rw [show V.hamiltonian a.edge (flightCurve V a s).1 (flightCurve V a s).2 = a.energy from
        flightCurve_hamiltonian_eq V a hs0.le (fun hbdd => (hs hbdd).le)]
      exact a.regular)

@[simp] theorem restart_edge (a : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    (restart V a hs0 hs).edge = a.edge := rfl

@[simp] theorem restart_state (a : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    (restart V a hs0 hs).state = flightCurve V a s := rfl

/-- Two flight states with the same edge and initial state have the same flight curve at every
nonnegative time: the curve depends only on the edge and state, not the witnessing segment. -/
theorem flightCurve_congr {a b : V.FlightState} (hedge : a.edge = b.edge)
    (hstate : a.state = b.state) {t : ℝ} (ht0 : 0 ≤ t) :
    flightCurve V a t = flightCurve V b t := by
  classical
  obtain ⟨ae, ax, aseg, areg⟩ := a
  obtain ⟨be, bx, bseg, breg⟩ := b
  change ae = be at hedge
  change ax = bx at hstate
  subst hedge
  subst hstate
  show flightCurve V ⟨ae, ax, aseg, areg⟩ t = flightCurve V ⟨ae, ax, bseg, breg⟩ t
  unfold flightCurve
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V ae ax)
  · simp only [dif_pos hbdd]
    exact aseg.maximalCurveClosed_indep bseg hbdd ht0
  · simp only [dif_neg hbdd]
    exact aseg.unboundedCurve_indep bseg hbdd ht0

/-- A flight state's canonical flight curve agrees with its own physical segment's curve for the
whole certified segment duration.  This is the bridge from the abstract `flightCurve` to the
concrete segment data, used to transport per-segment ODE/physical facts to `flightCurve`. -/
theorem flightCurve_eq_segment_curve (c : V.FlightState) {t : ℝ} (ht0 : 0 ≤ t)
    (htd : t < c.segment.duration) :
    flightCurve V c t = c.segment.curve t := by
  classical
  unfold flightCurve
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V c.edge c.state)
  · rw [dif_pos hbdd]
    have htsSup : t < sSup (PhysicalEdgeSegment.durationSet V c.edge c.state) :=
      lt_of_lt_of_le htd (le_csSup hbdd c.segment.mem_durationSet)
    rw [c.segment.maximalCurveClosed_eq_maximalCurve hbdd htsSup]
    exact c.segment.maximalCurve_eq_segment_curve hbdd ht0 htsSup c.segment htd
  · rw [dif_neg hbdd]
    exact c.segment.unboundedCurve_eq_segment_curve hbdd ht0 c.segment htd

/-- A flight state's curve solves the concrete Hamiltonian edge ODE at every strictly interior
time of its flight interval. -/
theorem flightCurve_hasDerivAt (a : V.FlightState) {t : ℝ} (ht0 : 0 < t)
    (htdur : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      t < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    HasDerivAt (flightCurve V a)
      (V.edgeVectorField a.edge (flightCurve V a t)) t := by
  classical
  unfold flightCurve
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)
  · rw [dif_pos hbdd]
    exact a.segment.maximalCurveClosed_hasDerivAt hbdd ⟨ht0, htdur hbdd⟩
  · rw [dif_neg hbdd]
    exact a.segment.unboundedCurve_hasDerivAt hbdd ht0

/-- The momentum-and-time reversal of a flight curve solves the Hamiltonian edge ODE at every
strictly-negative time inside the (reflected) flight interval.  This is the backward edge flight,
obtained from the edge time-reversal symmetry alone (no scattering reversibility assumed). -/
theorem flightCurve_timeReversal_hasDerivAt (a : V.FlightState) {s : ℝ} (hs : s < 0)
    (htdur : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      -s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    HasDerivAt (fun u => ((flightCurve V a (-u)).1, -(flightCurve V a (-u)).2))
      (V.edgeVectorField a.edge ((flightCurve V a (-s)).1, -(flightCurve V a (-s)).2)) s := by
  apply V.edgeIntegralCurve_timeReversal
  exact flightCurve_hasDerivAt V a (show (0 : ℝ) < -s by linarith) htdur

/-- The backward-retracing curve reflected about an arbitrary center time `s` solves the edge ODE
forward.  Writing `g u = ((flightCurve a (s-u)).1, -(flightCurve a (s-u)).2)`, the position runs the
original flight backward from `flightCurve a s` while the momentum is flipped, and this is a genuine
forward solution of the Hamiltonian edge ODE.  This is the derivative identity used to identify the
backward flight of `backwardRestart` with the reversal of the original flight. -/
theorem flightCurve_reflectAt_hasDerivAt (a : V.FlightState) {s u : ℝ} (hus : u < s)
    (htdur : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      s - u < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    HasDerivAt (fun w => ((flightCurve V a (s - w)).1, -(flightCurve V a (s - w)).2))
      (V.edgeVectorField a.edge ((flightCurve V a (s - u)).1, -(flightCurve V a (s - u)).2)) u := by
  have hfwd : HasDerivAt (flightCurve V a)
      (V.edgeVectorField a.edge (flightCurve V a (s - u))) (s - u) :=
    flightCurve_hasDerivAt V a (show (0 : ℝ) < s - u by linarith)
      (fun hbdd => htdur hbdd)
  have hinner : HasDerivAt (fun w : ℝ => s - w) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub s
  have hq := V.edgeIntegralCurve_hasDerivAt_fst hfwd
  have hp := V.edgeIntegralCurve_hasDerivAt_snd hfwd
  have hqrev := hq.comp u hinner
  have hprev := (hp.comp u hinner).neg
  simpa [edgeVectorField, Function.comp_def] using hqrev.prodMk hprev

/-- The reflection of the flight of `a` about a strictly-pre-first-impact time `s`, packaged as a
genuine physical edge segment based at the momentum-reversed point.  Its curve retraces the
original flight toward the departure vertex; it stays strictly inside the edge on `(0,d)` because it
mirrors interior points of the original flight, and it conserves the (regular) energy.  This is the
concrete backward flight used, via `flightCurve` choice-independence, to identify the forward flight
of `backwardRestart` with the reversed original flight. -/
noncomputable def backwardSegment (a : V.FlightState) {s : ℝ}
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state))
    {d : ℝ} (hd0 : 0 < d) (hds : d < s) :
    V.PhysicalEdgeSegment a.edge ((flightCurve V a s).1, -(flightCurve V a s).2) where
  duration := d
  duration_pos := hd0
  curve := fun w => ((flightCurve V a (s - w)).1, -(flightCurve V a (s - w)).2)
  initial := by simp
  initial_physical := by
    have hs0 : (0 : ℝ) < s := lt_trans hd0 hds
    exact flightCurve_physical V a hs0.le (fun hbdd => (hs hbdd).le)
  physical := fun w hw => by
    have hsw0 : (0 : ℝ) ≤ s - w := by have := hw.2; linarith
    exact flightCurve_physical V a hsw0 (fun hbdd => le_of_lt (by have := hs hbdd; linarith [hw.1]))
  in_domain := fun w hw => by
    have hsw0 : (0 : ℝ) ≤ s - w := by have := hw.2; linarith
    exact V.closedEdge_subset_domain a.edge
      (flightCurve_physical V a hsw0 (fun hbdd => le_of_lt (by have := hs hbdd; linarith [hw.1])))
  integralCurve := fun w hw =>
    flightCurve_reflectAt_hasDerivAt V a (show w < s by linarith [hw.2])
      (fun hbdd => by have := hs hbdd; linarith [hw.1])
  interior_after_initial := fun w hw => by
    have hsw0 : (0 : ℝ) < s - w := by have := hw.2; linarith
    exact flightCurve_interior V a hsw0 (fun hbdd => by have := hs hbdd; linarith [hw.1])

/-- **Backward-flight retracing identity (step 5).**  The forward flight of `backwardRestart a s`
retraces the original flight of `a` toward its departure vertex with reversed momentum: at every
time `0 ≤ w < s`,
`flightCurve (backwardRestart a s) w = ((flightCurve a (s-w)).1, -(flightCurve a (s-w)).2)`.
The proof identifies the abstract backward flight with the concrete `backwardSegment` reflection
using `flightCurve` choice-independence (both share the edge and reversed initial state), so no new
ODE is solved — the reflection is already certified to solve the edge ODE forward. -/
theorem flightCurve_backwardRestart_eq (a : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state))
    {w : ℝ} (hw0 : 0 ≤ w) (hwd : w < s) :
    flightCurve V (backwardRestart V a hs0 hs) w
      = ((flightCurve V a (s - w)).1, -(flightCurve V a (s - w)).2) := by
  set d : ℝ := (w + s) / 2 with hd
  have hwd' : w < d := by rw [hd]; linarith
  have hds : d < s := by rw [hd]; linarith
  have hd0 : 0 < d := lt_of_le_of_lt hw0 hwd'
  let b' : V.FlightState :=
    { edge := a.edge
      state := ((flightCurve V a s).1, -(flightCurve V a s).2)
      segment := backwardSegment V a hs hd0 hds
      regular := (backwardRestart V a hs0 hs).regular }
  have hcongr : flightCurve V (backwardRestart V a hs0 hs) w = flightCurve V b' w :=
    flightCurve_congr (V := V) (a := backwardRestart V a hs0 hs) (b := b') rfl rfl hw0
  rw [hcongr, flightCurve_eq_segment_curve V b' hw0 (show w < b'.segment.duration from hwd')]
  rfl

/-- The within-flight semigroup: the flight curve of the state restarted at time `s` agrees with
the original flight curve shifted by `s`, throughout the remaining first flight.  This is the
`FlightState`-level lift of `maximalCurve_restart_eq`. -/
theorem flightCurve_restart_eq (a : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (hs : s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state))
    {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state) - s) :
    flightCurve V (restart V a hs0 (fun _ => hs)) t = flightCurve V a (s + t) := by
  classical
  have hfcs : flightCurve V a s = a.segment.maximalCurve hbdd s := by
    unfold flightCurve; rw [dif_pos hbdd]
    exact a.segment.maximalCurveClosed_eq_maximalCurve hbdd hs
  have hsu : s + t < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state) := by linarith
  have hRHS : flightCurve V a (s + t) = a.segment.maximalCurve hbdd (s + t) := by
    unfold flightCurve; rw [dif_pos hbdd]
    exact a.segment.maximalCurveClosed_eq_maximalCurve hbdd hsu
  set a' := restart V a hs0 (fun _ => hs) with ha'
  have ha'bdd : BddAbove (PhysicalEdgeSegment.durationSet V a'.edge a'.state) := by
    show BddAbove (PhysicalEdgeSegment.durationSet V a.edge (flightCurve V a s))
    rw [hfcs]
    exact (a.segment.bddAbove_durationSet_maximalCurve_iff hbdd hs0.le hs).mpr hbdd
  have ha'sSup : sSup (PhysicalEdgeSegment.durationSet V a'.edge a'.state) =
      sSup (PhysicalEdgeSegment.durationSet V a.edge a.state) - s := by
    show sSup (PhysicalEdgeSegment.durationSet V a.edge (flightCurve V a s)) = _
    rw [hfcs]
    exact a.segment.sSup_durationSet_maximalCurve_eq hbdd hs0.le hs
  have htlt : t < sSup (PhysicalEdgeSegment.durationSet V a'.edge a'.state) := by
    rw [ha'sSup]; linarith
  have hLHS : flightCurve V a' t = a'.segment.maximalCurve ha'bdd t := by
    unfold flightCurve; rw [dif_pos ha'bdd]
    exact a'.segment.maximalCurveClosed_eq_maximalCurve ha'bdd htlt
  have hb' : BddAbove (PhysicalEdgeSegment.durationSet V a.edge (a.segment.maximalCurve hbdd s)) := by
    rw [← hfcs]; exact ha'bdd
  rw [hLHS, hRHS]
  exact (a'.segment.maximalCurve_cast hfcs ha'bdd hb' t).symm.trans
    (a.segment.maximalCurve_restart_eq hbdd hs0.le hs (hfcs ▸ a'.segment) hb' ht0 ht)

/-- The state restarted at time `s` has the same maximal arrival covector as the original: the
next scattering event sees identical incoming data. -/
theorem arrivalCovector_restart_eq (a : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (hs : s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (ha'bdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge (flightCurve V a s))) :
    (restart V a hs0 (fun _ => hs)).segment.maximalArrivalCovector ha'bdd
        (restart V a hs0 (fun _ => hs)).regular =
      a.segment.maximalArrivalCovector hbdd a.regular := by
  have hfcs : flightCurve V a s = a.segment.maximalCurve hbdd s := by
    unfold flightCurve; rw [dif_pos hbdd]
    exact a.segment.maximalCurveClosed_eq_maximalCurve hbdd hs
  have hb' : BddAbove (PhysicalEdgeSegment.durationSet V a.edge (a.segment.maximalCurve hbdd s)) := by
    rw [← hfcs]; exact ha'bdd
  have hreg_g : V.hamiltonian a.edge (a.segment.maximalCurve hbdd s).1
      (a.segment.maximalCurve hbdd s).2 ∉ V.exceptionalEnergies := by
    rw [← hfcs]; exact (restart V a hs0 (fun _ => hs)).regular
  exact ((restart V a hs0 (fun _ => hs)).segment.maximalArrivalCovector_cast hfcs ha'bdd hb'
      (restart V a hs0 (fun _ => hs)).regular hreg_g).symm.trans
    (a.segment.maximalArrivalCovector_restart_eq hbdd hs0.le hs
      (hfcs ▸ (restart V a hs0 (fun _ => hs)).segment) hb' hreg_g a.regular)

/-- The `next` correspondence: the scattered successor of the state restarted at time `s` has the
same edge and state as the scattered successor of the original.  Both see the identical incoming
covector, so the same scattering event fires. -/
theorem next_restart_congr (S : BorelEnergyPreservingScattering V) (a : V.FlightState) {s : ℝ}
    (hs0 : 0 < s) (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (hs : s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (ha'bdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge (flightCurve V a s))) :
    ∃ b b' : V.FlightState, next V S a = some b ∧
      next V S (restart V a hs0 (fun _ => hs)) = some b' ∧
      b'.edge = b.edge ∧ b'.state = b.state := by
  classical
  obtain ⟨b, hb, hbstate, -, -, hbedge⟩ := next_eq_some_of_bddAbove (V := V) S a hbdd
  obtain ⟨b', hb', hb'state, -, -, hb'edge⟩ :=
    next_eq_some_of_bddAbove (V := V) S (restart V a hs0 (fun _ => hs)) ha'bdd
  set αa := a.segment.maximalArrivalIncoming hbdd a.regular with hαa
  set αr := (restart V a hs0 (fun _ => hs)).segment.maximalArrivalIncoming ha'bdd
    (restart V a hs0 (fun _ => hs)).regular with hαr
  have hcov : αr.1 = αa.1 := arrivalCovector_restart_eq (V := V) a hs0 hbdd hs ha'bdd
  have valcast : ∀ {v v' : Γ.Vertex} (hvv : v = v') (γ : Γ.IncomingBoundary v),
      (hvv ▸ γ).1 = γ.1 := by intro v v' hvv γ; subst hvv; rfl
  have smapcast : ∀ {v v' : Γ.Vertex} (hvv : v = v') (γ : Γ.IncomingBoundary v),
      (S.map v' (hvv ▸ γ)).1 = (S.map v γ).1 := by intro v v' hvv γ; subst hvv; rfl
  have hv : αr.1.germ.vertex = αa.1.germ.vertex := by rw [hcov]
  have hαeq : hv ▸ αr = αa := Subtype.ext ((valcast hv αr).trans hcov)
  have hβ : (S.map αr.1.germ.vertex αr).1 = (S.map αa.1.germ.vertex αa).1 := by
    rw [← smapcast hv αr, hαeq]
  refine ⟨b, b', hb, hb', ?_, ?_⟩
  · rw [hbedge, hb'edge, hβ]
  · rw [hbstate, hb'state, hβ]

/-- The `next` map respects edge+state equivalence: successors of edge+state-equal states are
themselves edge+state-equal (or both absent).  This is the inductive step of the chain
correspondence, proved from choice-independence of the maximal arrival. -/
theorem next_congr (S : BorelEnergyPreservingScattering V) {a₁ a₂ : V.FlightState}
    (hedge : a₁.edge = a₂.edge) (hstate : a₁.state = a₂.state) :
    (next V S a₁ = none ∧ next V S a₂ = none) ∨
    (∃ b₁ b₂ : V.FlightState, next V S a₁ = some b₁ ∧ next V S a₂ = some b₂ ∧
      b₁.edge = b₂.edge ∧ b₁.state = b₂.state) := by
  classical
  obtain ⟨e, x, seg₁, reg₁⟩ := a₁
  obtain ⟨e₂, x₂, seg₂, reg₂⟩ := a₂
  change e = e₂ at hedge
  change x = x₂ at hstate
  subst hedge
  subst hstate
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V e x)
  · right
    obtain ⟨b₁, hb₁, hb₁state, -, -, hb₁edge⟩ :=
      next_eq_some_of_bddAbove (V := V) S ⟨e, x, seg₁, reg₁⟩ hbdd
    obtain ⟨b₂, hb₂, hb₂state, -, -, hb₂edge⟩ :=
      next_eq_some_of_bddAbove (V := V) S ⟨e, x, seg₂, reg₂⟩ hbdd
    set α₁ := (⟨e, x, seg₁, reg₁⟩ : V.FlightState).segment.maximalArrivalIncoming hbdd reg₁ with hα₁
    set α₂ := (⟨e, x, seg₂, reg₂⟩ : V.FlightState).segment.maximalArrivalIncoming hbdd reg₂ with hα₂
    have hcov : α₁.1 = α₂.1 := seg₁.maximalArrivalCovector_indep seg₂ hbdd reg₁ reg₂
    have valcast : ∀ {v v' : Γ.Vertex} (hvv : v = v') (γ : Γ.IncomingBoundary v),
        (hvv ▸ γ).1 = γ.1 := by intro v v' hvv γ; subst hvv; rfl
    have smapcast : ∀ {v v' : Γ.Vertex} (hvv : v = v') (γ : Γ.IncomingBoundary v),
        (S.map v' (hvv ▸ γ)).1 = (S.map v γ).1 := by intro v v' hvv γ; subst hvv; rfl
    have hv : α₁.1.germ.vertex = α₂.1.germ.vertex := by rw [hcov]
    have hαeq : hv ▸ α₁ = α₂ := Subtype.ext ((valcast hv α₁).trans hcov)
    have hβ : (S.map α₁.1.germ.vertex α₁).1 = (S.map α₂.1.germ.vertex α₂).1 := by
      rw [← smapcast hv α₁, hαeq]
    refine ⟨b₁, b₂, hb₁, hb₂, ?_, ?_⟩
    · rw [hb₁edge, hb₂edge, hβ]
    · rw [hb₁state, hb₂state, hβ]
  · exact Or.inl ⟨next_eq_none_of_not_bddAbove (V := V) S ⟨e, x, seg₁, reg₁⟩ hbdd,
      next_eq_none_of_not_bddAbove (V := V) S ⟨e, x, seg₂, reg₂⟩ hbdd⟩

/-- Two optional flight states are equivalent when both are absent, or both present with equal
edge and state.  This is the invariant carried along the chain correspondence. -/
def OptEquiv (o₁ o₂ : Option (V.FlightState)) : Prop :=
  (o₁ = none ∧ o₂ = none) ∨
  (∃ b₁ b₂ : V.FlightState, o₁ = some b₁ ∧ o₂ = some b₂ ∧
    b₁.edge = b₂.edge ∧ b₁.state = b₂.state)

/-- `Option.bind · next` preserves edge+state equivalence, by `next_congr`. -/
theorem optEquiv_bind_next (S : BorelEnergyPreservingScattering V) {o₁ o₂ : Option (V.FlightState)}
    (h : OptEquiv (V := V) o₁ o₂) :
    OptEquiv (V := V) (Option.bind o₁ (next V S)) (Option.bind o₂ (next V S)) := by
  rcases h with ⟨h1, h2⟩ | ⟨b₁, b₂, h1, h2, hedge, hstate⟩
  · rw [h1, h2]; exact Or.inl ⟨rfl, rfl⟩
  · rw [h1, h2]
    show OptEquiv (V := V) (next V S b₁) (next V S b₂)
    exact next_congr (V := V) S hedge hstate

/-- The forward deterministic event chain, stopped after its first global no-hit flight. -/
noncomputable def iterate (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) : ℕ → Option (V.FlightState)
  | 0 => some a
  | n + 1 => Option.bind (iterate S a n) (next (V := V) S)

/-- The elapsed time of the `n`-th impact, when the recursive chain has not yet reached its
global no-hit branch. Each successor adds the actual maximal-flight duration of its predecessor. -/
noncomputable def impactTime (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) : ℕ → Option ℝ
  | 0 => some 0
  | n + 1 =>
      Option.bind (iterate V S a n) fun b =>
        Option.bind (impactTime S a n) fun t =>
          Option.map (fun d => t + d) b.impactDuration

@[simp] theorem iterate_zero (S : BorelEnergyPreservingScattering V) (a : V.FlightState) :
    iterate V S a 0 = some a := rfl

@[simp] theorem iterate_succ (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (n : ℕ) : iterate V S a (n + 1) = Option.bind (iterate V S a n) (next V S) := rfl

/-- If the flight state reached at step `n` escapes (its successor is `none`), the chain terminates
there. -/
theorem iterate_succ_eq_none_of_next_eq_none (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) {n : ℕ} {b : V.FlightState}
    (hn : iterate V S a n = some b) (hb : next V S b = none) :
    iterate V S a (n + 1) = none := by
  rw [iterate_succ, hn]; exact hb

/-- Once the recursive chain has terminated it stays terminated: a `none` at step `m` propagates to
every later step. -/
theorem iterate_eq_none_of_le {S : BorelEnergyPreservingScattering V} {a : V.FlightState}
    {m n : ℕ} (hmn : m ≤ n) (hm : iterate V S a m = none) : iterate V S a n = none := by
  induction n with
  | zero => obtain rfl : m = 0 := Nat.le_zero.mp hmn; exact hm
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · rw [iterate_succ, ih (Nat.lt_succ_iff.mp hlt)]; rfl
      · obtain rfl : m = k + 1 := le_antisymm hmn hge; exact hm

/-- The chain is defined on a prefix: if step `n` is present then so is every earlier step. -/
theorem iterate_isSome_of_le {S : BorelEnergyPreservingScattering V} {a : V.FlightState}
    {m n : ℕ} (hmn : m ≤ n) (hn : (iterate V S a n).isSome) :
    (iterate V S a m).isSome := by
  by_contra h
  rw [Option.not_isSome_iff_eq_none] at h
  rw [iterate_eq_none_of_le (V := V) hmn h] at hn
  simp at hn

/-- **Terminating-chain structure.**  If the recursive chain ever reaches `none`, then it has a
last flight state, and that state escapes to infinity (unbounded duration, `next = none`).  This is
the escape flight whose unbounded curve is the tail of the forward trajectory of a terminating
chain. -/
theorem exists_escape_of_terminates {S : BorelEnergyPreservingScattering V} {a : V.FlightState}
    (hterm : ∃ n, iterate V S a n = none) :
    ∃ (N : ℕ) (b : V.FlightState), iterate V S a N = some b ∧ next V S b = none := by
  classical
  have hM : iterate V S a (Nat.find hterm) = none := Nat.find_spec hterm
  have hM0 : Nat.find hterm ≠ 0 := by
    intro h; rw [h, iterate_zero] at hM; simp at hM
  obtain ⟨N, hN⟩ : ∃ N, Nat.find hterm = N + 1 := ⟨Nat.find hterm - 1, by omega⟩
  rw [hN] at hM
  have hNsome : iterate V S a N ≠ none :=
    Nat.find_min hterm (by rw [hN]; exact Nat.lt_succ_self N)
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hNsome
  refine ⟨N, b, hb, ?_⟩
  rw [iterate_succ, hb] at hM
  exact hM

/-- A flight state with a genuine successor has bounded flight duration (it does not escape). -/
theorem bddAbove_of_next_isSome {S : BorelEnergyPreservingScattering V} {a : V.FlightState}
    (h : (next V S a).isSome) :
    BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state) := by
  by_contra hbdd
  rw [next_eq_none_of_not_bddAbove (V := V) S a hbdd] at h
  simp at h

@[simp] theorem impactTime_zero (S : BorelEnergyPreservingScattering V) (a : V.FlightState) :
    impactTime V S a 0 = some 0 := rfl

@[simp] theorem impactTime_succ (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (n : ℕ) : impactTime V S a (n + 1) =
      Option.bind (iterate V S a n) fun b =>
        Option.bind (impactTime V S a n) fun t =>
          Option.map (fun d => t + d) b.impactDuration := rfl

/-- On a finite flight, the next impact time is obtained by adding its true maximal duration. -/
theorem impactTime_succ_eq_some_of_bddAbove (S : BorelEnergyPreservingScattering V)
    (a b : V.FlightState) (n : ℕ) (hbdd : BddAbove
      (PhysicalEdgeSegment.durationSet V b.edge b.state))
    (hstate : iterate V S a n = some b) (htime : impactTime V S a n = some t) :
    impactTime V S a (n + 1) =
      some (t + sSup (PhysicalEdgeSegment.durationSet V b.edge b.state)) := by
  rw [impactTime_succ]
  simp [hstate, htime, impactDuration_eq_some_of_bddAbove (V := V) b hbdd]

/-- The impact time is defined wherever the chain is defined (a finite-prefix version of
`impactTime_isSome_of_chain`, requiring no global no-Zeno hypothesis). -/
theorem impactTime_isSome_of_isSome {S : BorelEnergyPreservingScattering V} {a : V.FlightState}
    {n : ℕ} (hn : (iterate V S a n).isSome) : (impactTime V S a n).isSome := by
  induction n with
  | zero => rw [impactTime_zero]; rfl
  | succ k ih =>
      have hk : (iterate V S a k).isSome := iterate_isSome_of_le (V := V) (Nat.le_succ k) hn
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hk
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (ih hk)
      have hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
        apply bddAbove_of_next_isSome (S := S)
        rw [iterate_succ, hb] at hn
        exact hn
      rw [impactTime_succ_eq_some_of_bddAbove (V := V) S a b k hbdd hb ht]
      rfl

/-- Energy is invariant along every defined member of the recursive forward chain. -/
theorem iterate_energy_eq {S : BorelEnergyPreservingScattering V} {a b : V.FlightState}
    (n : ℕ) (h : iterate V S a n = some b) : b.energy = a.energy := by
  induction n generalizing b with
  | zero =>
      simp only [iterate_zero, Option.some.injEq] at h
      subst b
      rfl
  | succ n ih =>
      rw [iterate_succ] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨c, hc, hcb⟩
      calc
        b.energy = c.energy := next_energy_eq_of_eq_some (V := V) S c b hcb
        _ = a.energy := ih hc

/-- The chain correspondence: from the first impact on, the recursive chain of the state restarted
at time `s` is edge+state equivalent to that of the original.  Both scatter identically after the
common first impact. -/
theorem iterate_restart_congr (S : BorelEnergyPreservingScattering V) (a : V.FlightState) {s : ℝ}
    (hs0 : 0 < s) (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (hs : s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (ha'bdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge (flightCurve V a s))) (n : ℕ) :
    OptEquiv (V := V) (iterate V S (restart V a hs0 (fun _ => hs)) (n + 1)) (iterate V S a (n + 1)) := by
  induction n with
  | zero =>
      obtain ⟨b, b', hb, hb', hedge, hstate⟩ := next_restart_congr (V := V) S a hs0 hbdd hs ha'bdd
      refine Or.inr ⟨b', b, ?_, ?_, hedge, hstate⟩
      · rw [iterate_succ, iterate_zero]; exact hb'
      · rw [iterate_succ, iterate_zero]; exact hb
  | succ n ih =>
      rw [iterate_succ, iterate_succ]
      exact optEquiv_bind_next (V := V) S ih

/-- If the original chain is infinite, so is the restart chain. -/
theorem restart_chain_infinite (S : BorelEnergyPreservingScattering V) (a : V.FlightState) {s : ℝ}
    (hs0 : 0 < s) (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (hs : s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (ha'bdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge (flightCurve V a s)))
    (hchain : ∀ n, (iterate V S a n).isSome) (n : ℕ) :
    (iterate V S (restart V a hs0 (fun _ => hs)) n).isSome := by
  cases n with
  | zero => rw [iterate_zero]; rfl
  | succ m =>
      rcases iterate_restart_congr (V := V) S a hs0 hbdd hs ha'bdd m with ⟨-, h2⟩ | ⟨b₁, _, h1, -, -, -⟩
      · have hcon := hchain (m + 1); rw [h2] at hcon; simp at hcon
      · rw [h1]; rfl

/-- On an infinite scattered chain, every flight terminates: each defined iterate has a bounded
duration set, since the next iterate exists. -/
theorem bddAbove_of_chain (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (hchain : ∀ n, (iterate V S a n).isSome) (n : ℕ) {b : V.FlightState}
    (hb : iterate V S a n = some b) :
    BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
  by_contra hnb
  have hnone : next (V := V) S b = none := next_eq_none_of_not_bddAbove (V := V) S b hnb
  have hns := hchain (n + 1)
  rw [iterate_succ, hb] at hns
  rw [show (some b).bind (next (V := V) S) = next (V := V) S b from rfl, hnone] at hns
  simp at hns

/-- On an infinite scattered chain, every impact time is defined. -/
theorem impactTime_isSome_of_chain (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (hchain : ∀ n, (iterate V S a n).isSome) (n : ℕ) :
    ∃ t : ℝ, impactTime V S a n = some t := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hchain n)
      exact ⟨t + sSup (PhysicalEdgeSegment.durationSet V b.edge b.state),
        impactTime_succ_eq_some_of_bddAbove (V := V) S a b n
          (bddAbove_of_chain (V := V) S a hchain n hb) hb ht⟩

/-- No finite-time accumulation of scattered impacts: on an infinite chain from a regular
initial energy, impact times exceed every fixed bound eventually.  This is the trajectory-level
form of Lemma V.3, obtained by instantiating the abstract `ForwardImpactSchedule` with the
uniform collar-exit separation constant. -/
theorem impactTime_eventually_gt [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) (B : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℝ, impactTime V S a n = some t → B < t := by
  classical
  -- Uniform separation constant on the compact singleton energy window {a.energy}.
  obtain ⟨τ, hτ, hsep⟩ :=
    exists_uniform_impactDuration_lower_bound (V := V) {a.energy} isCompact_singleton
      (by intro E hE; rw [mem_singleton_iff] at hE; subst hE; exact a.regular)
  -- Real-valued impact times.
  set r : ℕ → ℝ := fun n => (impactTime V S a n).getD 0 with hr
  have hval : ∀ n, impactTime V S a n = some (r n) := by
    intro n
    obtain ⟨t, ht⟩ := impactTime_isSome_of_chain (V := V) S a hchain n
    simp [hr, ht]
  -- Each step adds the bounded flight duration of the current iterate.
  have hstep : ∀ n, r (n + 1) = r n + sSup (PhysicalEdgeSegment.durationSet V
      (Option.get (iterate V S a n) (hchain n)).edge
      (Option.get (iterate V S a n) (hchain n)).state) := by
    intro n
    set b := Option.get (iterate V S a n) (hchain n) with hb
    have hbeq : iterate V S a n = some b := by rw [hb]; exact (Option.some_get _).symm
    have := impactTime_succ_eq_some_of_bddAbove (V := V) S a b n
      (bddAbove_of_chain (V := V) S a hchain n hbeq) hbeq (hval n)
    have h2 := hval (n + 1)
    rw [this] at h2
    exact (Option.some.inj h2).symm
  -- Consecutive separation for n ≥ 1: the (n+1)-th iterate is an outgoing successor.
  have hnext_sep : ∀ n, τ ≤ r (n + 2) - r (n + 1) := by
    intro n
    have hstepn := hstep (n + 1)
    set b := Option.get (iterate V S a (n + 1)) (hchain (n + 1)) with hb
    have hbeq : iterate V S a (n + 1) = some b := by rw [hb]; exact (Option.some_get _).symm
    -- b is an outgoing successor of iterate n
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hchain n)
    have hnextcb : next (V := V) S c = some b := by
      have hbind : iterate V S a (n + 1) = Option.bind (iterate V S a n) (next (V := V) S) :=
        iterate_succ (V := V) S a n
      rw [hbeq, hc] at hbind
      rw [show (some c).bind (next (V := V) S) = next (V := V) S c from rfl] at hbind
      exact hbind.symm
    have hout : b.IsOutgoing := next_isOutgoing (V := V) S hnextcb
    have hEK : b.energy ∈ ({a.energy} : Set ℝ) := by
      rw [mem_singleton_iff]; exact iterate_energy_eq (V := V) n.succ hbeq
    have hbddb := bddAbove_of_chain (V := V) S a hchain (n + 1) hbeq
    have hge := hsep b hout hEK hbddb
    rw [hstepn]; linarith
  -- Package into a ForwardImpactSchedule shifted by one.
  let I : ForwardImpactSchedule :=
    { time := fun n => r (n + 1)
      separation := τ
      separation_pos := hτ
      next_separated := hnext_sep }
  obtain ⟨N, hN⟩ := I.eventually_gt B
  refine ⟨N + 1, ?_⟩
  intro n hn t ht
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hNm : N ≤ m := by omega
  have := hN m hNm
  have hrt : r (m + 1) = t := by rw [hval (m + 1)] at ht; exact Option.some.inj ht
  change B < I.time m at this
  simp only [I] at this
  rw [hrt] at this
  exact this

/-- Real-valued impact times.  On an infinite chain these are the genuine elapsed times of the
successive scattering events. -/
noncomputable def impactReal (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (n : ℕ) : ℝ := (impactTime V S a n).getD 0

theorem impactTime_eq_some_impactReal (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (hchain : ∀ n, (iterate V S a n).isSome) (n : ℕ) :
    impactTime V S a n = some (impactReal V S a n) := by
  obtain ⟨t, ht⟩ := impactTime_isSome_of_chain (V := V) S a hchain n
  unfold impactReal; rw [ht]; rfl

@[simp] theorem impactReal_zero (S : BorelEnergyPreservingScattering V) (a : V.FlightState) :
    impactReal V S a 0 = 0 := by unfold impactReal; rw [impactTime_zero]; rfl

theorem impactReal_succ_eq (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (hchain : ∀ n, (iterate V S a n).isSome) (n : ℕ) {b : V.FlightState}
    (hb : iterate V S a n = some b) :
    impactReal V S a (n + 1) =
      impactReal V S a n + sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
  have hstep := impactTime_succ_eq_some_of_bddAbove (V := V) S a b n
    (bddAbove_of_chain (V := V) S a hchain n hb) hb
    (impactTime_eq_some_impactReal V S a hchain n)
  show (impactTime V S a (n + 1)).getD 0 = _
  rw [hstep, Option.getD_some]

/-- Finite-prefix version of `impactReal_succ_eq`: whenever step `n+1` is defined, the impact time
grows by the current flight's true maximal duration — no global no-Zeno hypothesis required. -/
theorem impactReal_succ_eq_of_isSome {S : BorelEnergyPreservingScattering V} {a : V.FlightState}
    {n : ℕ} {b : V.FlightState} (hn : iterate V S a n = some b)
    (hsucc : (iterate V S a (n + 1)).isSome) :
    impactReal V S a (n + 1) =
      impactReal V S a n + sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
  have hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
    apply bddAbove_of_next_isSome (S := S)
    rw [iterate_succ, hn] at hsucc; exact hsucc
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
    (impactTime_isSome_of_isSome (V := V) (a := a) (n := n) (by rw [hn]; rfl))
  have hstep := impactTime_succ_eq_some_of_bddAbove (V := V) S a b n hbdd hn ht
  show (impactTime V S a (n + 1)).getD 0 = (impactTime V S a n).getD 0 + _
  rw [hstep, ht, Option.getD_some, Option.getD_some]

/-- The impact time strictly increases across any defined step (finite-prefix strict monotonicity,
no global no-Zeno hypothesis). -/
theorem impactReal_lt_succ_of_isSome {S : BorelEnergyPreservingScattering V} {a : V.FlightState}
    {n : ℕ} (hsucc : (iterate V S a (n + 1)).isSome) :
    impactReal V S a n < impactReal V S a (n + 1) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
    (iterate_isSome_of_le (V := V) (Nat.le_succ n) hsucc)
  have hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
    apply bddAbove_of_next_isSome (S := S)
    rw [iterate_succ, hb] at hsucc; exact hsucc
  rw [impactReal_succ_eq_of_isSome (V := V) hb hsucc]
  linarith [impactDuration_pos_of_bddAbove (V := V) b hbdd]

/-- Finite-prefix strict monotonicity of impact times up to a defined index. -/
theorem impactReal_strictMonoOn_of_isSome {S : BorelEnergyPreservingScattering V}
    {a : V.FlightState} {m n : ℕ} (hn : (iterate V S a n).isSome) (hmn : m < n) :
    impactReal V S a m < impactReal V S a n := by
  induction n with
  | zero => omega
  | succ k ih =>
      have hk : (iterate V S a k).isSome := iterate_isSome_of_le (V := V) (Nat.le_succ k) hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | heq
      · exact lt_trans (ih hk hlt) (impactReal_lt_succ_of_isSome (V := V) hn)
      · subst heq; exact impactReal_lt_succ_of_isSome (V := V) hn

theorem impactReal_strictMono (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (hchain : ∀ n, (iterate V S a n).isSome) : StrictMono (impactReal V S a) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hchain n)
  rw [impactReal_succ_eq V S a hchain n hb]
  have hpos := impactDuration_pos_of_bddAbove (V := V) b (bddAbove_of_chain (V := V) S a hchain n hb)
  linarith

/-- The impact times of the restart chain are those of the original, shifted back by `s`: the
restart evolves the same events, having consumed time `s` of the first flight. -/
theorem impactReal_restart_eq (S : BorelEnergyPreservingScattering V) (a : V.FlightState) {s : ℝ}
    (hs0 : 0 < s) (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (hs : s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (ha'bdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge (flightCurve V a s)))
    (hchain : ∀ n, (iterate V S a n).isSome) (n : ℕ) :
    impactReal V S (restart V a hs0 (fun _ => hs)) (n + 1) = impactReal V S a (n + 1) - s := by
  have hchain' := restart_chain_infinite (V := V) S a hs0 hbdd hs ha'bdd hchain
  have hfcs : flightCurve V a s = a.segment.maximalCurve hbdd s := by
    unfold flightCurve; rw [dif_pos hbdd]
    exact a.segment.maximalCurveClosed_eq_maximalCurve hbdd hs
  induction n with
  | zero =>
      rw [impactReal_succ_eq (V := V) S _ hchain' 0 (iterate_zero (V := V) S _),
        impactReal_succ_eq (V := V) S a hchain 0 (iterate_zero (V := V) S a),
        impactReal_zero, impactReal_zero]
      show (0 : ℝ) + sSup (PhysicalEdgeSegment.durationSet V a.edge (flightCurve V a s)) =
        0 + sSup (PhysicalEdgeSegment.durationSet V a.edge a.state) - s
      rw [hfcs, a.segment.sSup_durationSet_maximalCurve_eq hbdd hs0.le hs]
      ring
  | succ n ih =>
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hchain (n + 1))
      obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp (hchain' (n + 1))
      rw [impactReal_succ_eq (V := V) S _ hchain' (n + 1) hb',
        impactReal_succ_eq (V := V) S a hchain (n + 1) hb]
      have hdur : sSup (PhysicalEdgeSegment.durationSet V b'.edge b'.state) =
          sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
        rcases iterate_restart_congr (V := V) S a hs0 hbdd hs ha'bdd n with ⟨hn1, -⟩ | ⟨c₁, c₂, hc1, hc2, hce, hcs⟩
        · rw [hn1] at hb'; simp at hb'
        · have hb'eq : c₁ = b' := Option.some.inj (hc1.symm.trans hb')
          have hbeq : c₂ = b := Option.some.inj (hc2.symm.trans hb)
          rw [← hb'eq, ← hbeq, hce, hcs]
      rw [hdur, ih]
      ring

/-- **Flight index for a terminating chain.**  When the chain escapes after step `N`, every time
`t ≥ 0` lies in a unique flight `n ≤ N`: either the last (escape) flight `n = N` when `t` is past its
onset, or a genuine flight with `t < impactReal (n+1)` before it.  This is the terminating-chain
analogue of `exists_forward_flightIndex`; together they cover every scattered forward trajectory. -/
theorem exists_terminating_flightIndex (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    {N : ℕ} (hesc : iterate V S a (N + 1) = none) {t : ℝ} (ht : 0 ≤ t) :
    ∃ n : ℕ, n ≤ N ∧ impactReal V S a n ≤ t ∧
      (n = N ∨ t < impactReal V S a (n + 1)) := by
  classical
  by_cases htN : impactReal V S a N ≤ t
  · exact ⟨N, le_rfl, htN, Or.inl rfl⟩
  · rw [not_le] at htN
    have hP0 : impactReal V S a 0 ≤ t := by rw [impactReal_zero]; exact ht
    set n := Nat.findGreatest (fun k => impactReal V S a k ≤ t) N with hndef
    have hnle : n ≤ N := Nat.findGreatest_le N
    have hPn : impactReal V S a n ≤ t :=
      Nat.findGreatest_spec (P := fun k => impactReal V S a k ≤ t) (Nat.zero_le N) hP0
    have hnltN : n < N := lt_of_le_of_ne hnle (by intro h; rw [h] at hPn; linarith)
    refine ⟨n, hnle, hPn, Or.inr ?_⟩
    have hgreat := Nat.findGreatest_is_greatest (P := fun k => impactReal V S a k ≤ t)
      (Nat.lt_succ_self n) (Nat.succ_le_of_lt hnltN)
    exact not_le.mp hgreat

theorem exists_forward_flightIndex [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) {t : ℝ} (ht : 0 ≤ t) :
    ∃ n : ℕ, impactReal V S a n ≤ t ∧ t < impactReal V S a (n + 1) := by
  classical
  obtain ⟨N, hN⟩ := impactTime_eventually_gt (V := V) S a hchain t
  have hex : ∃ m, t < impactReal V S a m :=
    ⟨N, hN N le_rfl _ (impactTime_eq_some_impactReal V S a hchain N)⟩
  have hm₀ : t < impactReal V S a (Nat.find hex) := Nat.find_spec hex
  have hm₀pos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, impactReal_zero] at hm₀; linarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm₀pos
  rw [hn] at hm₀
  refine ⟨n, ?_, hm₀⟩
  have hmin := Nat.find_min hex (m := n) (by rw [hn]; exact Nat.lt_succ_self n)
  exact not_lt.mp hmin

/-- The half-open impact interval containing a time is unique. -/
theorem flightIndex_unique (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (hchain : ∀ n, (iterate V S a n).isSome) {t : ℝ} {n m : ℕ}
    (hn : impactReal V S a n ≤ t ∧ t < impactReal V S a (n + 1))
    (hm : impactReal V S a m ≤ t ∧ t < impactReal V S a (m + 1)) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · have hle : impactReal V S a (n + 1) ≤ impactReal V S a m :=
      (impactReal_strictMono V S a hchain).monotone (by omega)
    linarith [hn.2, hm.1]
  · exact h
  · have hle : impactReal V S a (m + 1) ≤ impactReal V S a n :=
      (impactReal_strictMono V S a hchain).monotone (by omega)
    linarith [hm.2, hn.1]

/-- The forward scattered trajectory of an infinite chain: at every nonnegative time it evaluates
the active flight's curve; before time zero it is pinned at the initial state.  Its value is a
graph phase point `(edge, position, momentum)`. -/
noncomputable def forwardPhase [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) (t : ℝ) : Γ.Edge × ℝ × ℝ :=
  if ht : 0 ≤ t then
    (fun n => (((iterate V S a n).get (hchain n)).edge,
        flightCurve V ((iterate V S a n).get (hchain n)) (t - impactReal V S a n)))
      (Classical.choose (exists_forward_flightIndex V S a hchain ht))
  else (a.edge, a.state)

/-- On its active interval the forward trajectory is exactly the current flight's curve. -/
theorem forwardPhase_eq [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) {t : ℝ} (ht : 0 ≤ t) {n : ℕ}
    (hn : impactReal V S a n ≤ t ∧ t < impactReal V S a (n + 1)) {b : V.FlightState}
    (hb : iterate V S a n = some b) :
    forwardPhase V S a hchain t = (b.edge, flightCurve V b (t - impactReal V S a n)) := by
  classical
  have hget : (iterate V S a n).get (hchain n) = b :=
    Option.some.inj (by rw [Option.some_get, hb])
  unfold forwardPhase
  rw [dif_pos ht]
  have hspec := Classical.choose_spec (exists_forward_flightIndex V S a hchain ht)
  have hnn : Classical.choose (exists_forward_flightIndex V S a hchain ht) = n :=
    flightIndex_unique V S a hchain hspec hn
  simp only [hnn, hget]

/-- Energy is conserved along the whole forward scattered trajectory. -/
theorem forwardPhase_hamiltonian_eq [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) {t : ℝ} (ht : 0 ≤ t) :
    V.hamiltonian (forwardPhase V S a hchain t).1 (forwardPhase V S a hchain t).2.1
      (forwardPhase V S a hchain t).2.2 = a.energy := by
  obtain ⟨n, hn⟩ := exists_forward_flightIndex V S a hchain ht
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hchain n)
  rw [forwardPhase_eq V S a hchain ht hn hb]
  have hstep := impactReal_succ_eq V S a hchain n hb
  have h0 : 0 ≤ t - impactReal V S a n := by linarith [hn.1]
  have hdur : ∀ _ : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      t - impactReal V S a n ≤ sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
    intro _
    have hlt : t < impactReal V S a n + sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
      rw [← hstep]; exact hn.2
    linarith
  show V.hamiltonian b.edge (flightCurve V b (t - impactReal V S a n)).1
      (flightCurve V b (t - impactReal V S a n)).2 = a.energy
  rw [flightCurve_hamiltonian_eq V b h0 hdur]
  exact iterate_energy_eq (V := V) n hb

/-- The forward scattered trajectory always lies on the closed physical edge of its current
edge. -/
theorem forwardPhase_physical [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) {t : ℝ} (ht : 0 ≤ t) :
    (forwardPhase V S a hchain t).2.1 ∈
      Set.Icc (0 : ℝ) (Γ.length (forwardPhase V S a hchain t).1) := by
  obtain ⟨n, hn⟩ := exists_forward_flightIndex V S a hchain ht
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hchain n)
  rw [forwardPhase_eq V S a hchain ht hn hb]
  have hstep := impactReal_succ_eq V S a hchain n hb
  have h0 : 0 ≤ t - impactReal V S a n := by linarith [hn.1]
  have hdur : ∀ _ : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      t - impactReal V S a n ≤ sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
    intro _
    have hlt : t < impactReal V S a n + sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
      rw [← hstep]; exact hn.2
    linarith
  exact flightCurve_physical V b h0 hdur

/-- Between two consecutive impacts the forward trajectory's phase component genuinely solves the
concrete Hamiltonian edge ODE.  This certifies that `forwardPhase` is a real physical evolution,
not merely a bookkeeping device. -/
theorem forwardPhase_snd_hasDerivAt [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) {n : ℕ} {b : V.FlightState}
    (hb : iterate V S a n = some b) {t : ℝ}
    (ht : t ∈ Set.Ioo (impactReal V S a n) (impactReal V S a (n + 1))) :
    HasDerivAt (fun s => (forwardPhase V S a hchain s).2)
      (V.edgeVectorField b.edge (flightCurve V b (t - impactReal V S a n))) t := by
  classical
  have hstep := impactReal_succ_eq V S a hchain n hb
  have hin : 0 < t - impactReal V S a n := by linarith [ht.1]
  have hlt : ∀ _ : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      t - impactReal V S a n < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
    intro _
    have hb2 : t < impactReal V S a n +
        sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by rw [← hstep]; exact ht.2
    linarith
  have hg := flightCurve_hasDerivAt V b hin hlt
  have hfc : HasDerivAt (fun s => flightCurve V b (s - impactReal V S a n))
      (V.edgeVectorField b.edge (flightCurve V b (t - impactReal V S a n))) t :=
    HasDerivAt.comp_sub_const t (impactReal V S a n) hg
  have hnn0 : 0 ≤ impactReal V S a n := by
    have := (impactReal_strictMono V S a hchain).monotone (Nat.zero_le n)
    rwa [impactReal_zero] at this
  have heq : (fun s => (forwardPhase V S a hchain s).2) =ᶠ[nhds t]
      (fun s => flightCurve V b (s - impactReal V S a n)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hs0 : 0 ≤ s := le_of_lt (lt_of_le_of_lt hnn0 hs.1)
    rw [forwardPhase_eq V S a hchain hs0 ⟨hs.1.le, hs.2⟩ hb]
  exact hfc.congr_of_eventuallyEq heq

@[simp] theorem forwardPhase_zero [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) :
    forwardPhase V S a hchain 0 = (a.edge, a.state) := by
  have hn : impactReal V S a 0 ≤ (0 : ℝ) ∧ (0 : ℝ) < impactReal V S a 1 := by
    refine ⟨by rw [impactReal_zero], ?_⟩
    have := impactReal_strictMono V S a hchain (show 0 < 1 by norm_num)
    rwa [impactReal_zero] at this
  rw [forwardPhase_eq V S a hchain le_rfl hn (iterate_zero V S a)]
  rw [impactReal_zero, sub_zero, flightCurve_zero]

/-- The forward trajectory stays at the regular initial energy, hence in the regular sector. -/
theorem forwardPhase_regular [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) {t : ℝ} (ht : 0 ≤ t) :
    V.hamiltonian (forwardPhase V S a hchain t).1 (forwardPhase V S a hchain t).2.1
      (forwardPhase V S a hchain t).2.2 ∉ V.exceptionalEnergies := by
  rw [forwardPhase_hamiltonian_eq V S a hchain ht]
  exact a.regular

/-- The momentum along the forward trajectory is uniformly bounded by the compact-window speed
bound of its (conserved) energy. -/
theorem forwardPhase_absMomentum_le [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) (K : Set ℝ) (hKcompact : IsCompact K)
    (hEK : a.energy ∈ K) {t : ℝ} (ht : 0 ≤ t) :
    ∃ P : ℝ, 0 < P ∧ |(forwardPhase V S a hchain t).2.2| ≤ P := by
  obtain ⟨P, hP, hbound⟩ := V.exists_compact_energy_speed_bound K hKcompact
  refine ⟨P, hP, ?_⟩
  exact hbound (forwardPhase V S a hchain t).1 (forwardPhase V S a hchain t).2.1
    (forwardPhase V S a hchain t).2.2 a.energy
    (forwardPhase_physical V S a hchain ht) hEK
    (forwardPhase_hamiltonian_eq V S a hchain ht)

/-- At each impact time the forward trajectory equals the initial phase of the next flight state,
i.e. the post-scattering restart.  The trajectory is thus right-continuous at impacts with the
scattered value. -/
theorem forwardPhase_at_impact [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) (n : ℕ) {b : V.FlightState}
    (hb : iterate V S a (n + 1) = some b) :
    forwardPhase V S a hchain (impactReal V S a (n + 1)) = (b.edge, b.state) := by
  have hnn0 : 0 ≤ impactReal V S a (n + 1) := by
    have := (impactReal_strictMono V S a hchain).monotone (Nat.zero_le (n + 1))
    rwa [impactReal_zero] at this
  have hn : impactReal V S a (n + 1) ≤ impactReal V S a (n + 1) ∧
      impactReal V S a (n + 1) < impactReal V S a (n + 1 + 1) :=
    ⟨le_rfl, impactReal_strictMono V S a hchain (Nat.lt_succ_self _)⟩
  rw [forwardPhase_eq V S a hchain hnn0 hn hb, sub_self, flightCurve_zero]

/-- The forward flow semigroup for a restart within the first flight:
`Φ(s+t) = Φ t ∘ Φ s`, where `Φ s` is realized by the restarted flight state.  The restart evolves
the identical events, so both trajectories agree at every later time. -/
theorem forwardPhase_semigroup [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) {s t : ℝ} (hs0 : 0 < s)
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (hs : s < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) (ht0 : 0 ≤ t)
    (ha'bdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge (flightCurve V a s)))
    (hchain' : ∀ n, (iterate V S (restart V a hs0 (fun _ => hs)) n).isSome) :
    forwardPhase V S a hchain (s + t) =
      forwardPhase V S (restart V a hs0 (fun _ => hs)) hchain' t := by
  have hst0 : 0 ≤ s + t := by linarith
  have himp1 : impactReal V S a 1 = sSup (PhysicalEdgeSegment.durationSet V a.edge a.state) := by
    rw [impactReal_succ_eq (V := V) S a hchain 0 (iterate_zero (V := V) S a), impactReal_zero]; ring
  obtain ⟨n, hn⟩ := exists_forward_flightIndex (V := V) S a hchain hst0
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hchain n)
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp (hchain' n)
  cases n with
  | zero =>
      have hbeq : b = a := Option.some.inj (hb.symm.trans (iterate_zero (V := V) S a))
      have hb'eq : b' = restart V a hs0 (fun _ => hs) :=
        Option.some.inj (hb'.symm.trans (iterate_zero (V := V) S _))
      have hnr : impactReal V S (restart V a hs0 (fun _ => hs)) 0 ≤ t ∧
          t < impactReal V S (restart V a hs0 (fun _ => hs)) 1 := by
        refine ⟨by rw [impactReal_zero]; exact ht0, ?_⟩
        rw [impactReal_restart_eq (V := V) S a hs0 hbdd hs ha'bdd hchain 0]
        have := hn.2; rw [himp1] at this; linarith
      rw [forwardPhase_eq (V := V) S a hchain hst0 hn hb,
        forwardPhase_eq (V := V) S (restart V a hs0 (fun _ => hs)) hchain' ht0 hnr hb']
      rw [impactReal_zero, impactReal_zero, sub_zero, sub_zero, hbeq, hb'eq, Prod.mk.injEq]
      have hlt : t < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state) - s := by
        have := hn.2; rw [himp1] at this; linarith
      exact ⟨rfl, (flightCurve_restart_eq (V := V) a hs0 hbdd hs ht0 hlt).symm⟩
  | succ m =>
      have hnr : impactReal V S (restart V a hs0 (fun _ => hs)) (m + 1) ≤ t ∧
          t < impactReal V S (restart V a hs0 (fun _ => hs)) (m + 1 + 1) := by
        rw [impactReal_restart_eq (V := V) S a hs0 hbdd hs ha'bdd hchain m,
          impactReal_restart_eq (V := V) S a hs0 hbdd hs ha'bdd hchain (m + 1)]
        exact ⟨by linarith [hn.1], by linarith [hn.2]⟩
      rw [forwardPhase_eq (V := V) S a hchain hst0 hn hb,
        forwardPhase_eq (V := V) S (restart V a hs0 (fun _ => hs)) hchain' ht0 hnr hb']
      rcases iterate_restart_congr (V := V) S a hs0 hbdd hs ha'bdd m with ⟨hz, -⟩ | ⟨c₁, c₂, hc1, hc2, hce, hcs⟩
      · rw [hz] at hb'; simp at hb'
      · have hb'eq : c₁ = b' := Option.some.inj (hc1.symm.trans hb')
        have hbeq : c₂ = b := Option.some.inj (hc2.symm.trans hb)
        subst hb'eq; subst hbeq
        rw [impactReal_restart_eq (V := V) S a hs0 hbdd hs ha'bdd hchain m, Prod.mk.injEq]
        refine ⟨hce.symm, ?_⟩
        rw [show t - (impactReal V S a (m + 1) - s) = s + t - impactReal V S a (m + 1) from by ring]
        exact flightCurve_congr (V := V) hce.symm hcs.symm (by linarith [hn.1])

end FlightState
end MechanicalPotential
end HamiltonianMetricGraphs
