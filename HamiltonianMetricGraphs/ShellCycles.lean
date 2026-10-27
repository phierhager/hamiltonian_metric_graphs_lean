/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Theorem VIII.5 (b), (c): the periodic orbits of a regular energy shell
-/

import HamiltonianMetricGraphs.Structure
import HamiltonianMetricGraphs.MainTheorem

/-!
# The periodic orbits of a shell-regular energy surface

`Structure.lean` proves part (a) of Theorem VIII.5: at a shell-regular energy `E` the end step
`Π_E = germStep S E` is a permutation of the finite set `G_E = allowedGerms E` of admissible ends
(`shellGermPerm`).  This module proves the dynamical half of parts (b) and (c) for the global flow
`Φ_t = flow V S · t` of Theorem VI.5 on the regular quotient phase space.

## Cycles and periods

* `flightTime E η = t_E(η)` is the duration of the flight departing `η` at the speed
  `germSpeed η E = r_η(E)`; it is positive (`flightTime_pos`).
* `germCycle S E η` is the cycle of `Π_E` through `η`, as a finite set of ends; it is the set of
  ends in the same cycle of the permutation `shellGermPerm` (`mem_germCycle_iff_sameCycle`), and
  any two of its members have the same cycle (`germCycle_eq_of_mem`).
* `cyclePeriod S E η = T_c(E) = ∑_{ζ ∈ c} t_E(ζ)` is the period (8.4) of that cycle; it is the
  time of the `k`-th impact of the departing trajectory for `k` the cycle length
  (`cyclePeriod_eq_chainTime`).
* `sum_germCycles`: `∑_{c} T_c(E) = ∑_{η ∈ G_E} t_E(η)`, the combinatorial half of (8.5).

## The orbit of a cycle

`departureClass S hE η hη` is the departure state of `η` at energy `E` as a point of the regular
quotient phase space.  The main results are:

* **(b) periodicity with least period** (`flow_cyclePeriod_departureClass`,
  `flow_departureClass_ne_self`, and on the edge phase space `germTrajectory_cyclePeriod`,
  `germTrajectory_ne_zero`): `Φ_{T_c}` fixes the departure state, and no time in `(0, T_c)` does.
* **(b) every point of the shell is periodic** (`shell_periodic`): every `z` with
  `H(z) = E` lies on the orbit of a departure state and satisfies `Φ_{T_c}(z) = z`, `T_c` being the
  least positive period of `z`.
* **(c) decomposition** (`mem_shell_iff_exists_mem_shellOrbit`, `shellOrbit_eq_iff`,
  `disjoint_shellOrbit`): the shell is the union of the orbits of the departure states, two such
  orbits coincide exactly when the ends lie in the same cycle of `Π_E`, and are disjoint otherwise.
* **(c) suspension** (`suspension_injOn`, `suspension_image`, `flow_suspension`,
  `flow_departureClass_flightTime`, `flow_departureClass_ne_departureClass`):
  `u ↦ Φ_u(departure state)` is a bijection from `[0, T_c)` onto the orbit, the flow acts on it as
  the translation `u ↦ u + t mod T_c`, and the first return to the section of departure states
  happens after `t_E(η)`, at the departure state of `Π_E(η)`.

The travel-time formula and the measure statements are in `ShellTravelTime.lean` and
`ShellMeasure.lean`.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter
open scoped Topology

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### Flight times -/

/-- The **flight time** `t_E(η)` of Theorem VIII.5: the duration of the flight departing the end
`η` at the speed `r_η(E) = germSpeed η E`. -/
noncomputable def flightTime (E : ℝ) (η : Γ.EdgeEnd) : ℝ :=
  V.departureDurationTotal η (V.germSpeed η E)

theorem flightTime_eq_sSup {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    V.flightTime E η = sSup (PhysicalEdgeSegment.durationSet V η.1
      (departurePoint η (V.germSpeed η E))) :=
  V.departureDurationTotal_of_mem (V.germSpeed_mem_regularSpeeds hE hη)

/-- Flight times are positive. -/
theorem flightTime_pos {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) : 0 < V.flightTime E η := by
  have hr := V.germSpeed_mem_regularSpeeds hE hη
  rw [V.flightTime_eq_sSup hE hη]
  exact FlightState.impactDuration_pos_of_bddAbove (V := V) (V.ofDeparture η hr.1 hr.2)
    (V.bddAbove_departurePoint_germSpeed hE hη)

/-! ### Two ends of the same edge at the same coordinate are equal -/

theorem edgeEnd_eq_of_coordinate_eq {η ζ : Γ.EdgeEnd} (he : η.1 = ζ.1)
    (hc : FiniteMetricGraph.EdgeEnd.coordinate Γ η = FiniteMetricGraph.EdgeEnd.coordinate Γ ζ) :
    η = ζ := by
  rcases η with ⟨e, b⟩
  rcases ζ with ⟨e', b'⟩
  simp only at he
  subst he
  have hl := Γ.length_pos e
  cases b <;> cases b' <;> simp [FiniteMetricGraph.EdgeEnd.coordinate] at hc ⊢ <;> linarith

theorem edgeEnd_coordinate_mem (η : Γ.EdgeEnd) :
    FiniteMetricGraph.EdgeEnd.coordinate Γ η = 0 ∨
      FiniteMetricGraph.EdgeEnd.coordinate Γ η = Γ.length η.1 := by
  rcases η with ⟨e, b⟩
  cases b
  · left; rfl
  · right; rfl

theorem edgeEnd_coordinate_notMem_Ioo (η : Γ.EdgeEnd) :
    FiniteMetricGraph.EdgeEnd.coordinate Γ η ∉ Ioo (0 : ℝ) (Γ.length η.1) := by
  rintro ⟨h1, h2⟩
  rcases edgeEnd_coordinate_mem η with h | h <;> rw [h] at h1 h2 <;> linarith

/-! ### Cycles of the end step -/

section Cycles

variable (S : BorelEnergyPreservingScattering V)

theorem germStep_iterate_mem {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (k : ℕ) : (V.germStep S E)^[k] η ∈ V.allowedGerms E := by
  induction k with
  | zero => exact hη
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact V.germStep_mem S hE ih

/-- The chain times of the departing trajectory are the partial sums of the flight times along
the end-step orbit. -/
theorem chainTime_germSpeed_eq_sum {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (n : ℕ) :
    chainTime V S (η, V.germSpeed η E) n =
      ∑ k ∈ Finset.range n, V.flightTime E ((V.germStep S E)^[k] η) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [chainTime_succ, ih, Finset.sum_range_succ, (V.chainIterate_germStep S hE hη n).2]
      rfl

theorem chainTime_germSpeed_strictMono {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    StrictMono fun n => chainTime V S (η, V.germSpeed η E) n :=
  strictMono_nat_of_lt_succ (V.chainTime_lt_succ S hE hη)

/-- An allowed end is a periodic point of the end step. -/
theorem mem_periodicPts_germStep {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) : η ∈ Function.periodicPts (V.germStep S E) := by
  obtain ⟨n, hn, h⟩ := V.exists_germStep_period S hE hη
  exact ⟨n, hn, h⟩

theorem minimalPeriod_germStep_pos {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) : 0 < Function.minimalPeriod (V.germStep S E) η :=
  Function.minimalPeriod_pos_of_mem_periodicPts (V.mem_periodicPts_germStep S hE hη)

/-- **The cycle of `Π_E` through `η`**, as a finite set of ends: the end-step orbit of `η`. -/
noncomputable def germCycle (E : ℝ) (η : Γ.EdgeEnd) : Finset Γ.EdgeEnd :=
  (Finset.range (Function.minimalPeriod (V.germStep S E) η)).image
    fun k => (V.germStep S E)^[k] η

/-- **The period `T_c(E)` of the cycle `c` through `η`** (equation (8.4)): the sum of the flight
times of the ends of the cycle. -/
noncomputable def cyclePeriod (E : ℝ) (η : Γ.EdgeEnd) : ℝ :=
  ∑ ζ ∈ V.germCycle S E η, V.flightTime E ζ

theorem mem_germCycle_iff {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {ζ : Γ.EdgeEnd} :
    ζ ∈ V.germCycle S E η ↔ ∃ k : ℕ, (V.germStep S E)^[k] η = ζ := by
  unfold germCycle
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨k % Function.minimalPeriod (V.germStep S E) η,
      Finset.mem_range.mpr (Nat.mod_lt _ (V.minimalPeriod_germStep_pos S hE hη)), ?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq, hk]

theorem self_mem_germCycle {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) : η ∈ V.germCycle S E η :=
  (V.mem_germCycle_iff S hE hη).mpr ⟨0, rfl⟩

theorem germCycle_subset {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {ζ : Γ.EdgeEnd} (hζ : ζ ∈ V.germCycle S E η) :
    ζ ∈ V.allowedGerms E := by
  obtain ⟨k, rfl⟩ := (V.mem_germCycle_iff S hE hη).mp hζ
  exact V.germStep_iterate_mem S hE hη k

/-- The members of a cycle all have the same cycle. -/
theorem germCycle_eq_of_mem {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {ζ : Γ.EdgeEnd} (hζ : ζ ∈ V.germCycle S E η) :
    V.germCycle S E ζ = V.germCycle S E η := by
  have hζa := V.germCycle_subset S hE hη hζ
  obtain ⟨k, rfl⟩ := (V.mem_germCycle_iff S hE hη).mp hζ
  ext ξ
  rw [V.mem_germCycle_iff S hE hζa, V.mem_germCycle_iff S hE hη]
  set n := Function.minimalPeriod (V.germStep S E) η with hn
  have hn0 : 0 < n := V.minimalPeriod_germStep_pos S hE hη
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j + k, by rw [Function.iterate_add_apply]⟩
  · rintro ⟨i, rfl⟩
    refine ⟨i + n * k - k, ?_⟩
    have hk : k ≤ n * k := Nat.le_mul_of_pos_left k hn0
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega),
      ← Function.iterate_mod_minimalPeriod_eq, ← hn, Nat.add_mul_mod_self_left,
      Function.iterate_mod_minimalPeriod_eq]

theorem cyclePeriod_eq_of_mem {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {ζ : Γ.EdgeEnd} (hζ : ζ ∈ V.germCycle S E η) :
    V.cyclePeriod S E ζ = V.cyclePeriod S E η := by
  unfold cyclePeriod
  rw [V.germCycle_eq_of_mem S hE hη hζ]

/-- The cycle of `η` is the set of ends in the same cycle of the permutation `Π_E`. -/
theorem mem_germCycle_iff_sameCycle {E : ℝ} (hE : V.ShellRegular E) (η ζ : V.allowedGerms E) :
    (ζ : Γ.EdgeEnd) ∈ V.germCycle S E η ↔ (V.shellGermPerm S hE).SameCycle η ζ := by
  rw [V.mem_germCycle_iff S hE η.2]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(k : ℤ), ?_⟩
    rw [zpow_natCast]
    apply Subtype.ext
    rw [V.shellGermPerm_pow_apply S hE η k, hk]
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    refine ⟨k, ?_⟩
    rw [← V.shellGermPerm_pow_apply S hE η k, hk]

/-- The period of a cycle as a sum over one traversal of the end-step orbit. -/
theorem cyclePeriod_eq_sum_range {E : ℝ} (η : Γ.EdgeEnd) :
    V.cyclePeriod S E η = ∑ k ∈ Finset.range (Function.minimalPeriod (V.germStep S E) η),
      V.flightTime E ((V.germStep S E)^[k] η) := by
  unfold cyclePeriod germCycle
  rw [Finset.sum_image]
  intro i hi j hj hij
  refine Function.iterate_injOn_Iio_minimalPeriod ?_ ?_ hij
  · exact Finset.mem_range.mp hi
  · exact Finset.mem_range.mp hj

/-- The period of a cycle is the time of the impact closing the cycle. -/
theorem cyclePeriod_eq_chainTime {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    V.cyclePeriod S E η =
      chainTime V S (η, V.germSpeed η E) (Function.minimalPeriod (V.germStep S E) η) := by
  rw [V.cyclePeriod_eq_sum_range S η, V.chainTime_germSpeed_eq_sum S hE hη]

/-- Periods are positive. -/
theorem cyclePeriod_pos {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) : 0 < V.cyclePeriod S E η := by
  rw [V.cyclePeriod_eq_chainTime S hE hη]
  have h := V.chainTime_germSpeed_strictMono S hE hη (V.minimalPeriod_germStep_pos S hE hη)
  simpa using h

/-- The finite set of admissible ends. -/
noncomputable def allowedFinset (E : ℝ) : Finset Γ.EdgeEnd := by
  classical
  exact Finset.univ.filter fun η => η ∈ V.allowedGerms E

theorem mem_allowedFinset {E : ℝ} {η : Γ.EdgeEnd} :
    η ∈ V.allowedFinset E ↔ η ∈ V.allowedGerms E := by
  classical
  unfold allowedFinset
  simp

/-- **The cycles of `Π_E`**, as a finite set of finite sets of ends. -/
noncomputable def germCycles (E : ℝ) : Finset (Finset Γ.EdgeEnd) := by
  classical
  exact (V.allowedFinset E).image (V.germCycle S E)

theorem mem_germCycles {E : ℝ} {c : Finset Γ.EdgeEnd} :
    c ∈ V.germCycles S E ↔ ∃ η ∈ V.allowedGerms E, V.germCycle S E η = c := by
  classical
  unfold germCycles
  simp only [Finset.mem_image, mem_allowedFinset]

/-- Distinct cycles are disjoint. -/
theorem disjoint_germCycle {E : ℝ} (hE : V.ShellRegular E) {η ζ : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (hζ : ζ ∈ V.allowedGerms E)
    (hne : V.germCycle S E η ≠ V.germCycle S E ζ) :
    Disjoint (V.germCycle S E η) (V.germCycle S E ζ) := by
  rw [Finset.disjoint_left]
  intro ξ h1 h2
  exact hne ((V.germCycle_eq_of_mem S hE hη h1).symm.trans (V.germCycle_eq_of_mem S hE hζ h2))

/-- **The combinatorial half of (8.5).**  The periods of the cycles sum to the total flight time
of the admissible ends: `∑_{c} T_c(E) = ∑_{η ∈ G_E} t_E(η)`. -/
theorem sum_germCycles {E : ℝ} (hE : V.ShellRegular E) :
    ∑ c ∈ V.germCycles S E, ∑ ζ ∈ c, V.flightTime E ζ =
      ∑ η ∈ V.allowedFinset E, V.flightTime E η := by
  classical
  have hunion : (V.germCycles S E).biUnion id = V.allowedFinset E := by
    ext ξ
    simp only [Finset.mem_biUnion, id, mem_allowedFinset, mem_germCycles]
    constructor
    · rintro ⟨c, ⟨η, hη, rfl⟩, hξ⟩
      exact V.germCycle_subset S hE hη hξ
    · intro hξ
      exact ⟨_, ⟨ξ, hξ, rfl⟩, V.self_mem_germCycle S hE hξ⟩
  have hdisj : (↑(V.germCycles S E) : Set (Finset Γ.EdgeEnd)).PairwiseDisjoint id := by
    intro c hc d hd hcd
    obtain ⟨η, hη, rfl⟩ := (V.mem_germCycles S).mp hc
    obtain ⟨ζ, hζ, rfl⟩ := (V.mem_germCycles S).mp hd
    exact V.disjoint_germCycle S hE hη hζ hcd
  rw [← hunion, Finset.sum_biUnion hdisj]
  rfl

theorem sum_cyclePeriod_germCycles {E : ℝ} (hE : V.ShellRegular E) :
    ∑ c ∈ V.germCycles S E, ∑ ζ ∈ c, V.flightTime E ζ =
      ∑ η ∈ V.allowedFinset E, V.flightTime E η :=
  V.sum_germCycles S hE

end Cycles

/-! ### The departure flight of an admissible end -/

/-- The flight state departing the admissible end `η` at energy `E`. -/
noncomputable def germFlight {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) : V.FlightState :=
  V.ofDeparture η (V.germSpeed_mem_regularSpeeds hE hη).1 (V.germSpeed_mem_regularSpeeds hE hη).2

@[simp] theorem germFlight_edge {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) : (V.germFlight hE η hη).edge = η.1 := rfl

@[simp] theorem germFlight_state {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) :
    (V.germFlight hE η hη).state = departurePoint η (V.germSpeed η E) := rfl

theorem germFlight_energy {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) : (V.germFlight hE η hη).energy = E :=
  V.departureEnergy_germSpeed hη

theorem germFlight_notIncoming {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) : (V.germFlight hE η hη).NotIncoming :=
  (V.isOutgoing_ofDeparture η _ _).notIncoming

theorem germFlight_bddAbove {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) :
    BddAbove (PhysicalEdgeSegment.durationSet V (V.germFlight hE η hη).edge
      (V.germFlight hE η hη).state) :=
  V.bddAbove_departurePoint_germSpeed hE hη

theorem germFlight_sSup {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) :
    sSup (PhysicalEdgeSegment.durationSet V (V.germFlight hE η hη).edge
      (V.germFlight hE η hη).state) = V.flightTime E η :=
  (V.flightTime_eq_sSup hE hη).symm

/-! ### Classes of trajectory points -/

section Flow

variable (S : BorelEnergyPreservingScattering V) [Nonempty Γ.Edge]

/-- The point of the regular quotient phase space reached by the trajectory of `a` at time `t`. -/
noncomputable def trajClass (a : V.FlightState) (t : ℝ) : RegularScatteringPhaseSpace (V := V) S :=
  ⟨graphClass V S (FlightState.trajectory V S a t), by
    change quotientHamiltonian (V := V) S
      (graphClass V S (FlightState.trajectory V S a t)) ∉ V.exceptionalEnergies
    rw [quotientHamiltonian_graphClass V S (FlightState.trajectory_admissible S _ t),
      FlightState.trajectory_hamiltonian_eq']
    exact a.regular⟩

theorem trajClass_val (a : V.FlightState) (t : ℝ) :
    (V.trajClass S a t).1 = graphClass V S (FlightState.trajectory V S a t) := rfl

theorem quotientHamiltonian_trajClass (a : V.FlightState) (t : ℝ) :
    quotientHamiltonian (V := V) S (V.trajClass S a t).1 = a.energy := by
  rw [trajClass_val, quotientHamiltonian_graphClass V S (FlightState.trajectory_admissible S _ t),
    FlightState.trajectory_hamiltonian_eq']

theorem rep_trajClass {a : V.FlightState} (ha : a.NotIncoming) (t : ℝ) :
    rep V S (V.trajClass S a t).1 = Γ.graphPoint (FlightState.trajectory V S a t) := by
  rw [trajClass_val, graphClass]
  exact rep_quotientMap_of_not_incoming V S _ (FlightState.trajectory_notIncoming S ha t)

/-- Two trajectory points of non-incoming flights with the same class are the same point. -/
theorem trajectory_eq_of_trajClass_eq {a b : V.FlightState} (ha : a.NotIncoming)
    (hb : b.NotIncoming) {s t : ℝ} (h : V.trajClass S a s = V.trajClass S b t) :
    FlightState.trajectory V S a s = FlightState.trajectory V S b t := by
  have hrep : rep V S (V.trajClass S a s).1 = rep V S (V.trajClass S b t).1 := by rw [h]
  rw [V.rep_trajClass S ha, V.rep_trajClass S hb] at hrep
  have h1 := Γ.graphPoint_edge (FlightState.trajectory_admissible S a s)
  have h2 := Γ.graphPoint_state (FlightState.trajectory_admissible S a s)
  have h3 := Γ.graphPoint_edge (FlightState.trajectory_admissible S b t)
  have h4 := Γ.graphPoint_state (FlightState.trajectory_admissible S b t)
  rw [hrep] at h1 h2
  exact Prod.ext (h1.symm.trans h3) (h2.symm.trans h4)

/-- The flow started at the class of the initial point of a non-incoming flight runs along its
trajectory. -/
theorem flow_trajClass_zero {a : V.FlightState} (ha : a.NotIncoming) {t : ℝ} (ht : 0 ≤ t) :
    flow V S (V.trajClass S a 0) t = V.trajClass S a t := by
  rw [flow_of_nonneg V S _ ht]
  apply Subtype.ext
  rw [forwardFlow_val, trajClass_val]
  congr 1
  have hadm := FlightState.trajectory_admissible S a 0
  refine FlightState.trajectory_congr V S ?_ ?_ ht
  · rw [repFlight_edge, V.rep_trajClass S ha 0, Γ.graphPoint_edge hadm,
      FlightState.trajectory_zero]
  · rw [repFlight_state, V.rep_trajClass S ha 0, Γ.graphPoint_state hadm,
      FlightState.trajectory_zero]

/-! ### The departure states and their trajectories -/

/-- The trajectory departing the admissible end `η` at energy `E`, on the edge phase spaces. -/
noncomputable def germTrajectory {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) (t : ℝ) : Γ.Edge × ℝ × ℝ :=
  FlightState.trajectory V S (V.germFlight hE η hη) t

/-- **The departure state** of the admissible end `η` at energy `E`, as a point of the regular
quotient phase space. -/
noncomputable def departureClass {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) : RegularScatteringPhaseSpace (V := V) S :=
  V.trajClass S (V.germFlight hE η hη) 0

theorem germTrajectory_zero {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) :
    V.germTrajectory S hE η hη 0 = (η.1, departurePoint η (V.germSpeed η E)) := by
  unfold germTrajectory
  rw [FlightState.trajectory_zero]
  rfl

theorem departureClass_val {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) :
    (V.departureClass S hE η hη).1 = graphClass V S (η.1, departurePoint η (V.germSpeed η E)) := by
  rw [departureClass, trajClass_val]
  exact congrArg (graphClass V S) (V.germTrajectory_zero S hE η hη)

theorem departureClass_congr {E : ℝ} (hE : V.ShellRegular E) {η ζ : Γ.EdgeEnd} (h : η = ζ)
    (hη : η ∈ V.allowedGerms E) (hζ : ζ ∈ V.allowedGerms E) :
    V.departureClass S hE η hη = V.departureClass S hE ζ hζ := by
  subst h; rfl

theorem quotientHamiltonian_departureClass {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) :
    quotientHamiltonian (V := V) S (V.departureClass S hE η hη).1 = E := by
  rw [departureClass, quotientHamiltonian_trajClass, germFlight_energy]

/-- From its departure state, the flow runs along the departing trajectory. -/
theorem flow_departureClass {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) {t : ℝ} (ht : 0 ≤ t) :
    flow V S (V.departureClass S hE η hη) t = V.trajClass S (V.germFlight hE η hη) t :=
  V.flow_trajClass_zero S (V.germFlight_notIncoming hE η hη) ht

/-- At its `k`-th impact time the departing trajectory is at the departure state of
`Π_E^k(η)`. -/
theorem germTrajectory_chainTime {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (k : ℕ) :
    V.germTrajectory S hE η hη (chainTime V S (η, V.germSpeed η E) k) =
      (((V.germStep S E)^[k] η).1,
        departurePoint ((V.germStep S E)^[k] η) (V.germSpeed ((V.germStep S E)^[k] η) E)) := by
  have hr := V.germSpeed_mem_regularSpeeds hE hη
  have hact : FlightState.ActiveAt V S (V.ofDeparture η hr.1 hr.2) k
      (chainTime V S (η, V.germSpeed η E) k) := by
    rw [V.activeAt_iff_chain S η hr k]
    exact ⟨V.chainLands_germSpeed S hE hη k, le_rfl, fun _ => V.chainTime_lt_succ S hE hη k⟩
  have ht0 : 0 ≤ chainTime V S (η, V.germSpeed η E) k := V.chainTime_nonneg S _ k
  unfold germTrajectory germFlight
  rw [V.trajectory_chain_eq S η hr ht0 hact]
  obtain ⟨hmem, hchain⟩ := V.chainIterate_germStep S hE hη k
  rw [hchain, sub_self]
  have hr' := V.germSpeed_mem_regularSpeeds hE hmem
  have hpre : ((V.germSpeed ((V.germStep S E)^[k] η) E : ℝ), (0 : ℝ)) ∈
      V.departurePreImpact ((V.germStep S E)^[k] η) := by
    refine ⟨hr', le_rfl, ?_⟩
    refine V.ofReal_lt_impactTime_of_le (V.durationSet_nonempty_of_regularSpeed hr') le_rfl ?_
    intro hbdd
    exact FlightState.impactDuration_pos_of_bddAbove (V := V) (V.ofDeparture _ hr'.1 hr'.2) hbdd
  rw [V.departureFlow_of_mem hpre]
  refine Prod.ext rfl ?_
  change V.departureFlight _ _ 0 = _
  rw [V.departureFlight_of_mem hr', FlightState.flightCurve_zero]
  rfl

/-- After its `k`-th impact the departing trajectory is the trajectory departing `Π_E^k(η)`. -/
theorem germTrajectory_chainTime_add {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    V.germTrajectory S hE η hη (chainTime V S (η, V.germSpeed η E) k + u) =
      V.germTrajectory S hE ((V.germStep S E)^[k] η) (V.germStep_iterate_mem S hE hη k) u := by
  have h := V.germTrajectory_chainTime S hE hη k
  unfold germTrajectory at h ⊢
  exact FlightState.trajectory_semigroup V S _ (V.chainTime_nonneg S _ k) hu _
    (by rw [h]; rfl) (by rw [h]; rfl)

omit [Nonempty Γ.Edge] in
theorem chainTime_succ_germSpeed {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (k : ℕ) :
    chainTime V S (η, V.germSpeed η E) (k + 1) =
      chainTime V S (η, V.germSpeed η E) k + V.flightTime E ((V.germStep S E)^[k] η) := by
  rw [V.chainTime_germSpeed_eq_sum S hE hη, V.chainTime_germSpeed_eq_sum S hE hη,
    Finset.sum_range_succ]

omit [Nonempty Γ.Edge] in
theorem chainTime_one_germSpeed {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    chainTime V S (η, V.germSpeed η E) 1 = V.flightTime E η := by
  rw [V.chainTime_succ_germSpeed S hE hη 0, chainTime_zero, zero_add]
  rfl

/-- During its first flight the departing trajectory follows the departure flight curve. -/
theorem germTrajectory_of_lt {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {u : ℝ} (hu0 : 0 ≤ u) (hu : u < V.flightTime E η) :
    V.germTrajectory S hE η hη u =
      (η.1, FlightState.flightCurve V (V.germFlight hE η hη) u) := by
  have hact : FlightState.ActiveAt V S (V.germFlight hE η hη) 0 u := by
    refine ⟨by rw [FlightState.iterate_zero]; rfl, by rw [FlightState.impactReal_zero]; exact hu0,
      fun hsucc => ?_⟩
    rw [FlightState.impactReal_succ_eq_of_isSome (V := V) (FlightState.iterate_zero V S _) hsucc,
      FlightState.impactReal_zero, zero_add, V.germFlight_sSup hE η hη]
    exact hu
  unfold germTrajectory
  rw [FlightState.trajectory_eq V S _ hu0 hact (FlightState.iterate_zero V S _),
    FlightState.impactReal_zero, sub_zero]
  rfl

/-- Strictly inside its first flight the departing trajectory is in the open edge. -/
theorem germTrajectory_interior {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {u : ℝ} (hu0 : 0 < u) (hu : u < V.flightTime E η) :
    (V.germTrajectory S hE η hη u).1 = η.1 ∧
      (V.germTrajectory S hE η hη u).2.1 ∈ Ioo (0 : ℝ) (Γ.length η.1) := by
  rw [V.germTrajectory_of_lt S hE hη hu0.le hu]
  refine ⟨rfl, ?_⟩
  exact FlightState.flightCurve_interior V _ hu0
    (fun _ => by rw [V.germFlight_sSup hE η hη]; exact hu)

/-- Strictly inside its first flight, the departing trajectory is not at any departure state. -/
theorem germTrajectory_ne_departure {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {u : ℝ} (hu0 : 0 < u) (hu : u < V.flightTime E η)
    (ζ : Γ.EdgeEnd) (r : ℝ) :
    V.germTrajectory S hE η hη u ≠ (ζ.1, departurePoint ζ r) := by
  intro h
  obtain ⟨he, hint⟩ := V.germTrajectory_interior S hE hη hu0 hu
  rw [h] at he hint
  simp only at he hint
  rw [← he] at hint
  exact edgeEnd_coordinate_notMem_Ioo ζ hint

/-- `Φ_{t_k}` maps the departure state of `η` to that of `Π_E^k(η)`, `t_k` being the `k`-th impact
time. -/
theorem flow_departureClass_chainTime {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (k : ℕ) :
    flow V S (V.departureClass S hE η hη) (chainTime V S (η, V.germSpeed η E) k) =
      V.departureClass S hE ((V.germStep S E)^[k] η) (V.germStep_iterate_mem S hE hη k) := by
  rw [V.flow_departureClass S hE η hη (V.chainTime_nonneg S _ k)]
  apply Subtype.ext
  rw [trajClass_val, departureClass_val]
  exact congrArg (graphClass V S) (V.germTrajectory_chainTime S hE hη k)

/-- **The suspension structure: the return map.**  After the flight time `t_E(η)` the flow carries
the departure state of `η` to the departure state of `Π_E(η)`. -/
theorem flow_departureClass_flightTime {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    flow V S (V.departureClass S hE η hη) (V.flightTime E η) =
      V.departureClass S hE (V.germStep S E η) (V.germStep_mem S hE hη) := by
  have h := V.flow_departureClass_chainTime S hE hη 1
  rw [V.chainTime_one_germSpeed S hE hη] at h
  exact h

/-- Strictly inside its first flight the flow from a departure state meets no departure state:
`t_E(η)` is the first return time to the section of departure states. -/
theorem flow_departureClass_ne_departureClass {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {u : ℝ} (hu0 : 0 < u) (hu : u < V.flightTime E η)
    (ζ : Γ.EdgeEnd) (hζ : ζ ∈ V.allowedGerms E) :
    flow V S (V.departureClass S hE η hη) u ≠ V.departureClass S hE ζ hζ := by
  intro h
  rw [V.flow_departureClass S hE η hη hu0.le, departureClass] at h
  have htr := V.trajectory_eq_of_trajClass_eq S (V.germFlight_notIncoming hE η hη)
    (V.germFlight_notIncoming hE ζ hζ) h
  have h0 := V.germTrajectory_zero S hE ζ hζ
  unfold germTrajectory at h0
  rw [h0] at htr
  exact V.germTrajectory_ne_departure S hE hη hu0 hu ζ _ htr

/-! ### Periodic points of the flow -/

/-- An integer number of periods returns a periodic point. -/
theorem flow_zsmul_of_flow_eq (z : RegularScatteringPhaseSpace (V := V) S) {T : ℝ}
    (hT : flow V S z T = z) (m : ℤ) : flow V S z (m • T) = z := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih => rw [add_smul, one_smul, ← flow_flow, ih, hT]
  | pred k ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg, ← flow_flow, ih]
      have h := flow_flow_neg_self V S z T
      rwa [hT] at h

theorem flow_add_zsmul_of_flow_eq (z : RegularScatteringPhaseSpace (V := V) S) {T : ℝ}
    (hT : flow V S z T = z) (t : ℝ) (m : ℤ) : flow V S z (t + m • T) = flow V S z t := by
  rw [add_comm, ← flow_flow, V.flow_zsmul_of_flow_eq S z hT]

theorem flow_toIcoMod_of_flow_eq (z : RegularScatteringPhaseSpace (V := V) S) {T : ℝ}
    (hTpos : 0 < T) (hT : flow V S z T = z) (t : ℝ) :
    flow V S z (toIcoMod hTpos 0 t) = flow V S z t := by
  rw [← self_sub_toIcoDiv_zsmul hTpos 0 t, sub_eq_add_neg, ← neg_smul,
    V.flow_add_zsmul_of_flow_eq S z hT]

/-- At a point of least period `T`, two times give the same point exactly when they differ by an
integer multiple of `T`. -/
theorem flow_eq_flow_iff_of_period (z : RegularScatteringPhaseSpace (V := V) S) {T : ℝ}
    (hTpos : 0 < T) (hT : flow V S z T = z) (hmin : ∀ u ∈ Ioo 0 T, flow V S z u ≠ z)
    (s t : ℝ) : flow V S z s = flow V S z t ↔ ∃ m : ℤ, s = t + m • T := by
  constructor
  · intro h
    have hst : flow V S z (s - t) = z := by
      have h1 : flow V S (flow V S z s) (-t) = flow V S z (s - t) := by
        rw [flow_flow, sub_eq_add_neg]
      rw [← h1, h, flow_flow_neg_self]
    have hmod := V.flow_toIcoMod_of_flow_eq S z hTpos hT (s - t)
    rw [hst] at hmod
    have hmem := toIcoMod_mem_Ico hTpos 0 (s - t)
    rw [zero_add] at hmem
    have hzero : toIcoMod hTpos 0 (s - t) = 0 := by
      by_contra hne
      exact hmin _ ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne), hmem.2⟩ hmod
    refine ⟨toIcoDiv hTpos 0 (s - t), ?_⟩
    have h2 := self_sub_toIcoDiv_zsmul hTpos 0 (s - t)
    rw [hzero] at h2
    linarith
  · rintro ⟨m, rfl⟩
    exact V.flow_add_zsmul_of_flow_eq S z hT t m

theorem flow_injOn_Ico_of_period (z : RegularScatteringPhaseSpace (V := V) S) {T : ℝ}
    (hTpos : 0 < T) (hT : flow V S z T = z) (hmin : ∀ u ∈ Ioo 0 T, flow V S z u ≠ z) :
    InjOn (fun u => flow V S z u) (Ico 0 T) := by
  intro s hs t ht h
  obtain ⟨m, hm⟩ := (V.flow_eq_flow_iff_of_period S z hTpos hT hmin s t).mp h
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with hlt | heq | hgt
    · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      have hmT : m • T ≤ -T := by rw [zsmul_eq_mul]; nlinarith
      linarith [hs.1, ht.2]
    · exact heq
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hgt
      have hmT : T ≤ m • T := by rw [zsmul_eq_mul]; nlinarith
      linarith [hs.2, ht.1]
  rw [hm, hm0, zero_smul, add_zero]

theorem flow_image_Ico_of_period (z : RegularScatteringPhaseSpace (V := V) S) {T : ℝ}
    (hTpos : 0 < T) (hT : flow V S z T = z) :
    (fun u => flow V S z u) '' Ico 0 T = range fun u => flow V S z u := by
  refine Subset.antisymm (image_subset_range _ _) ?_
  rintro _ ⟨t, rfl⟩
  refine ⟨toIcoMod hTpos 0 t, ?_, V.flow_toIcoMod_of_flow_eq S z hTpos hT t⟩
  have h := toIcoMod_mem_Ico hTpos 0 t
  rwa [zero_add] at h

/-! ### The orbit of a departure state: least period `T_c(E)` -/

omit [Nonempty Γ.Edge] in
/-- Every time in `[0, T_c)` lies in one flight of the first traversal of the cycle. -/
theorem exists_chainTime_le_lt {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {u : ℝ} (hu0 : 0 ≤ u) (hu : u < V.cyclePeriod S E η) :
    ∃ k < Function.minimalPeriod (V.germStep S E) η,
      chainTime V S (η, V.germSpeed η E) k ≤ u ∧
        u < chainTime V S (η, V.germSpeed η E) (k + 1) := by
  classical
  set n := Function.minimalPeriod (V.germStep S E) η with hn
  set c : ℕ → ℝ := fun j => chainTime V S (η, V.germSpeed η E) j with hc
  have hcn : u < c n := by
    rw [hc]; simp only
    rw [← V.cyclePeriod_eq_chainTime S hE hη]; exact hu
  set k := Nat.findGreatest (fun j => c j ≤ u) n with hk
  have hck : c k ≤ u :=
    Nat.findGreatest_spec (P := fun j => c j ≤ u) (Nat.zero_le n) (by simpa [hc] using hu0)
  have hkn : k ≤ n := Nat.findGreatest_le n
  have hkn' : k < n := lt_of_le_of_ne hkn (fun h => by rw [h] at hck; linarith)
  refine ⟨k, hkn', hck, ?_⟩
  by_contra hcon
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self k) (Nat.succ_le_of_lt hkn')
    (not_lt.mp hcon)

/-- **The departure states on an orbit.**  If, within one traversal `[0, T_c)` of the cycle, the
flow from the departure state of `η` reaches the departure state of `ζ`, then it does so at an
impact time and `ζ = Π_E^k(η)`. -/
theorem exists_iterate_of_flow_departureClass_eq {E : ℝ} (hE : V.ShellRegular E)
    {η ζ : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) (hζ : ζ ∈ V.allowedGerms E) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u < V.cyclePeriod S E η)
    (h : flow V S (V.departureClass S hE η hη) u = V.departureClass S hE ζ hζ) :
    ∃ k < Function.minimalPeriod (V.germStep S E) η,
      u = chainTime V S (η, V.germSpeed η E) k ∧ (V.germStep S E)^[k] η = ζ := by
  obtain ⟨k, hkn, hk1, hk2⟩ := V.exists_chainTime_le_lt S hE hη hu0 hu
  set ξ := (V.germStep S E)^[k] η with hξdef
  have hξ : ξ ∈ V.allowedGerms E := V.germStep_iterate_mem S hE hη k
  set w := u - chainTime V S (η, V.germSpeed η E) k with hw
  have hw0 : 0 ≤ w := by rw [hw]; linarith
  have hwlt : w < V.flightTime E ξ := by
    rw [V.chainTime_succ_germSpeed S hE hη k] at hk2
    rw [hw]; linarith
  have hflow : flow V S (V.departureClass S hE ξ hξ) w = V.departureClass S hE ζ hζ := by
    rw [← V.flow_departureClass_chainTime S hE hη k, flow_flow, hw, add_sub_cancel]
    exact h
  rcases eq_or_lt_of_le hw0 with hw0' | hwpos
  · refine ⟨k, hkn, by linarith, ?_⟩
    rw [← hw0', flow_zero] at hflow
    have htr := V.trajectory_eq_of_trajClass_eq S (V.germFlight_notIncoming hE ξ hξ)
      (V.germFlight_notIncoming hE ζ hζ) hflow
    have h1 := V.germTrajectory_zero S hE ξ hξ
    have h2 := V.germTrajectory_zero S hE ζ hζ
    unfold germTrajectory at h1 h2
    rw [h1, h2] at htr
    have he := congrArg Prod.fst htr
    simp only at he
    have hcoord := congrArg (fun y => y.2.1) htr
    simp only [departurePoint] at hcoord
    exact edgeEnd_eq_of_coordinate_eq he hcoord
  · exact absurd hflow (V.flow_departureClass_ne_departureClass S hE hξ hwpos hwlt ζ hζ)

/-- **Theorem VIII.5 (b): the period.**  The flow returns the departure state of `η` to itself
after the period `T_c(E)` of its cycle. -/
theorem flow_cyclePeriod_departureClass {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    flow V S (V.departureClass S hE η hη) (V.cyclePeriod S E η) = V.departureClass S hE η hη := by
  rw [V.cyclePeriod_eq_chainTime S hE hη, V.flow_departureClass_chainTime S hE hη]
  exact V.departureClass_congr S hE (Function.isPeriodicPt_minimalPeriod _ _) _ _

/-- **Theorem VIII.5 (b): the period is least.**  No time strictly between `0` and `T_c(E)`
returns the departure state of `η` to itself. -/
theorem flow_departureClass_ne_self {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {u : ℝ} (hu : u ∈ Ioo 0 (V.cyclePeriod S E η)) :
    flow V S (V.departureClass S hE η hη) u ≠ V.departureClass S hE η hη := by
  intro h
  obtain ⟨k, hkn, hku, hkη⟩ :=
    V.exists_iterate_of_flow_departureClass_eq S hE hη hη hu.1.le hu.2 h
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk, chainTime_zero] at hku; linarith [hu.1]
    · exact hk
  exact absurd (Function.IsPeriodicPt.minimalPeriod_le hk0 hkη) (not_le.mpr hkn)

/-- **Theorem VIII.5 (b), on the edge phase spaces.**  The trajectory departing `η` is back at its
departure point at time `T_c(E)`. -/
theorem germTrajectory_cyclePeriod {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    V.germTrajectory S hE η hη (V.cyclePeriod S E η) = V.germTrajectory S hE η hη 0 := by
  rw [V.cyclePeriod_eq_chainTime S hE hη, V.germTrajectory_chainTime S hE hη,
    V.germTrajectory_zero S hE η hη, Function.isPeriodicPt_minimalPeriod]

/-- **Theorem VIII.5 (b), on the edge phase spaces: the period is least.** -/
theorem germTrajectory_ne_zero {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {u : ℝ} (hu : u ∈ Ioo 0 (V.cyclePeriod S E η)) :
    V.germTrajectory S hE η hη u ≠ V.germTrajectory S hE η hη 0 := by
  intro h
  apply V.flow_departureClass_ne_self S hE hη hu
  rw [V.flow_departureClass S hE η hη hu.1.le, departureClass]
  apply Subtype.ext
  rw [trajClass_val, trajClass_val]
  exact congrArg (graphClass V S) h

/-- The trajectory departing `η` is periodic with period `T_c(E)` at all nonnegative times. -/
theorem germTrajectory_add_cyclePeriod {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {u : ℝ} (hu : 0 ≤ u) :
    V.germTrajectory S hE η hη (V.cyclePeriod S E η + u) = V.germTrajectory S hE η hη u := by
  have h := V.germTrajectory_cyclePeriod S hE hη
  have h0 := V.germTrajectory_zero S hE η hη
  unfold germTrajectory at h h0 ⊢
  rw [h0] at h
  exact FlightState.trajectory_semigroup V S _ (V.cyclePeriod_pos S hE hη).le hu _
    (by rw [h]; rfl) (by rw [h]; rfl)

/-! ### The suspension structure -/

/-- **The orbit** of the departure state of `η`. -/
def shellOrbit {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E) :
    Set (RegularScatteringPhaseSpace (V := V) S) :=
  range fun t => flow V S (V.departureClass S hE η hη) t

/-- **The energy shell** `Σ_E = H⁻¹(E) ∩ P^Reg_S`. -/
def shell (E : ℝ) : Set (RegularScatteringPhaseSpace (V := V) S) :=
  {z | quotientHamiltonian (V := V) S z.1 = E}

/-- **Theorem VIII.5 (c): the suspension chart is injective.**  `u ↦ Φ_u(departure state of η)` is
injective on `[0, T_c)`. -/
theorem suspension_injOn {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    InjOn (fun u => flow V S (V.departureClass S hE η hη) u) (Ico 0 (V.cyclePeriod S E η)) :=
  V.flow_injOn_Ico_of_period S _ (V.cyclePeriod_pos S hE hη)
    (V.flow_cyclePeriod_departureClass S hE hη)
    (fun _ hu => V.flow_departureClass_ne_self S hE hη hu)

/-- **Theorem VIII.5 (c): the suspension chart is onto the orbit.** -/
theorem suspension_image {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    (fun u => flow V S (V.departureClass S hE η hη) u) '' Ico 0 (V.cyclePeriod S E η) =
      V.shellOrbit S hE η hη :=
  V.flow_image_Ico_of_period S _ (V.cyclePeriod_pos S hE hη)
    (V.flow_cyclePeriod_departureClass S hE hη)

/-- **Theorem VIII.5 (c): the flow is a translation in the suspension chart.**  In the chart
`u ∈ [0, T_c) ↦ Φ_u(departure state of η)` the flow `Φ_t` is `u ↦ u + t mod T_c`. -/
theorem flow_suspension {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (u t : ℝ) :
    flow V S (flow V S (V.departureClass S hE η hη) u) t =
      flow V S (V.departureClass S hE η hη)
        (toIcoMod (V.cyclePeriod_pos S hE hη) 0 (u + t)) := by
  rw [flow_flow, V.flow_toIcoMod_of_flow_eq S _ (V.cyclePeriod_pos S hE hη)
    (V.flow_cyclePeriod_departureClass S hE hη)]

theorem shellOrbit_subset_shell {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) : V.shellOrbit S hE η hη ⊆ V.shell S E := by
  rintro _ ⟨t, rfl⟩
  change quotientHamiltonian (V := V) S _ = E
  rw [quotientHamiltonian_flow, quotientHamiltonian_departureClass]

/-- Every point of a shell-regular energy surface reaches a departure state in positive time. -/
theorem exists_flow_eq_departureClass {E : ℝ} (hE : V.ShellRegular E)
    {z : RegularScatteringPhaseSpace (V := V) S} (hz : z ∈ V.shell S E) :
    ∃ ζ : Γ.EdgeEnd, ∃ hζ : ζ ∈ V.allowedGerms E, ∃ θ : ℝ, 0 < θ ∧
      flow V S z θ = V.departureClass S hE ζ hζ := by
  set a := repFlight V S z with ha
  have haE : a.energy = E := by rw [ha, repFlight_energy]; exact hz
  have hbdd : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state) :=
    hE.lands a.edge a.state haE
  obtain ⟨b, hb, -⟩ := FlightState.next_eq_some_of_bddAbove (V := V) S a hbdd
  have hout : b.IsOutgoing := FlightState.next_isOutgoing (V := V) S hb
  have hbE : b.energy = E := (FlightState.next_energy_eq_of_eq_some V S a b hb).trans haE
  have hit : FlightState.iterate V S a (0 + 1) = some b := by
    rw [FlightState.iterate_succ, FlightState.iterate_zero]
    exact hb
  have hθ : 0 < FlightState.impactReal V S a 1 := by
    have h := FlightState.impactReal_lt_succ_of_isSome (V := V) (S := S) (a := a) (n := 0)
      (by rw [hit]; rfl)
    simpa using h
  have htraj : FlightState.trajectory V S a (FlightState.impactReal V S a 1) = (b.edge, b.state) :=
    FlightState.trajectory_at_impact V S a 0 hit
  obtain ⟨ζ, hζe, hζc, hζs⟩ := hout
  set r := |b.state.2| with hr
  have hsign := edgeEnd_sign_mul_self ζ
  have hstate : b.state = departurePoint ζ r := by
    refine Prod.ext hζc ?_
    change b.state.2 = -(FiniteMetricGraph.EdgeEnd.sign Γ ζ * |b.state.2|)
    have habs : |b.state.2| = -(FiniteMetricGraph.EdgeEnd.sign Γ ζ * b.state.2) := by
      have h1 : |FiniteMetricGraph.EdgeEnd.sign Γ ζ * b.state.2| = |b.state.2| := by
        rw [abs_mul, abs_edgeEnd_sign, one_mul]
      rw [← h1, abs_of_neg hζs]
    rw [habs]
    linear_combination (-b.state.2) * hsign
  have hr0 : 0 < r := by
    rw [hr, abs_pos]
    intro h0
    rw [h0, mul_zero] at hζs
    exact lt_irrefl _ hζs
  have hEr : V.departureEnergy ζ r = E := by
    rw [← hbE, FlightState.energy_eq, ← hζe, hstate]
    rfl
  have hrs : V.germSpeed ζ E = r := by rw [← hEr]; exact V.germSpeed_departureEnergy ζ hr0.le
  have hζa : ζ ∈ V.allowedGerms E := by rw [← V.germSpeed_pos_iff, hrs]; exact hr0
  refine ⟨ζ, hζa, FlightState.impactReal V S a 1, hθ, ?_⟩
  rw [flow_of_nonneg V S z hθ.le]
  apply Subtype.ext
  rw [forwardFlow_val, ← ha, htraj, departureClass_val, hrs, ← hstate, ← hζe]

/-- Every point of the shell is on the orbit of a departure state, at a time in `[0, T_c)`. -/
theorem exists_mem_suspension {E : ℝ} (hE : V.ShellRegular E)
    {z : RegularScatteringPhaseSpace (V := V) S} (hz : z ∈ V.shell S E) :
    ∃ η : Γ.EdgeEnd, ∃ hη : η ∈ V.allowedGerms E, ∃ u ∈ Ico 0 (V.cyclePeriod S E η),
      z = flow V S (V.departureClass S hE η hη) u := by
  obtain ⟨ζ, hζ, θ, -, hθ⟩ := V.exists_flow_eq_departureClass S hE hz
  have hz' : z = flow V S (V.departureClass S hE ζ hζ) (-θ) := by
    rw [← hθ, flow_flow_neg_self]
  have hmem : (V.shellOrbit S hE ζ hζ) z := ⟨-θ, hz'.symm⟩
  rw [← V.suspension_image S hE hζ] at hmem
  obtain ⟨u, hu, hzu⟩ := hmem
  exact ⟨ζ, hζ, u, hu, hzu.symm⟩

/-- **Theorem VIII.5 (c): the shell is the union of the orbits of the departure states.** -/
theorem mem_shell_iff_exists_mem_shellOrbit {E : ℝ} (hE : V.ShellRegular E)
    (z : RegularScatteringPhaseSpace (V := V) S) :
    z ∈ V.shell S E ↔ ∃ η : Γ.EdgeEnd, ∃ hη : η ∈ V.allowedGerms E, z ∈ V.shellOrbit S hE η hη := by
  constructor
  · intro hz
    obtain ⟨η, hη, u, -, rfl⟩ := V.exists_mem_suspension S hE hz
    exact ⟨η, hη, u, rfl⟩
  · rintro ⟨η, hη, hz⟩
    exact V.shellOrbit_subset_shell S hE hη hz

/-- The departure states along a cycle lie on one orbit. -/
theorem departureClass_mem_shellOrbit {E : ℝ} (hE : V.ShellRegular E) {η ζ : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (hζ : ζ ∈ V.allowedGerms E) (h : ζ ∈ V.germCycle S E η) :
    ∃ k : ℕ, V.departureClass S hE ζ hζ =
      flow V S (V.departureClass S hE η hη) (chainTime V S (η, V.germSpeed η E) k) := by
  obtain ⟨k, rfl⟩ := (V.mem_germCycle_iff S hE hη).mp h
  exact ⟨k, (V.flow_departureClass_chainTime S hE hη k).symm⟩

/-- **Theorem VIII.5 (c): ends of one cycle have the same orbit.** -/
theorem shellOrbit_eq_of_mem_germCycle {E : ℝ} (hE : V.ShellRegular E) {η ζ : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (hζ : ζ ∈ V.allowedGerms E) (h : ζ ∈ V.germCycle S E η) :
    V.shellOrbit S hE ζ hζ = V.shellOrbit S hE η hη := by
  obtain ⟨k, hk⟩ := V.departureClass_mem_shellOrbit S hE hη hζ h
  unfold shellOrbit
  rw [hk]
  ext w
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_ + t, (flow_flow V S _ _ t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t - chainTime V S (η, V.germSpeed η E) k, ?_⟩
    simp only
    rw [flow_flow, add_sub_cancel]

/-- **Theorem VIII.5 (c): ends of different cycles have disjoint orbits.** -/
theorem disjoint_shellOrbit {E : ℝ} (hE : V.ShellRegular E) {η ζ : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (hζ : ζ ∈ V.allowedGerms E) (h : ζ ∉ V.germCycle S E η) :
    Disjoint (V.shellOrbit S hE η hη) (V.shellOrbit S hE ζ hζ) := by
  rw [Set.disjoint_left]
  rintro _ ⟨s, rfl⟩ ⟨t, hts⟩
  apply h
  have hdc : V.departureClass S hE ζ hζ = flow V S (V.departureClass S hE η hη) (s - t) := by
    have h1 := congrArg (fun w => flow V S w (-t)) hts
    simp only at h1
    rw [flow_flow_neg_self, flow_flow, ← sub_eq_add_neg] at h1
    exact h1
  have hTpos := V.cyclePeriod_pos S hE hη
  rw [← V.flow_toIcoMod_of_flow_eq S _ hTpos (V.flow_cyclePeriod_departureClass S hE hη)] at hdc
  have hmem := toIcoMod_mem_Ico hTpos 0 (s - t)
  rw [zero_add] at hmem
  obtain ⟨k, -, -, hk⟩ :=
    V.exists_iterate_of_flow_departureClass_eq S hE hη hζ hmem.1 hmem.2 hdc.symm
  exact (V.mem_germCycle_iff S hE hη).mpr ⟨k, hk⟩

/-- **Theorem VIII.5 (c): one orbit per cycle.**  Two departure states have the same orbit exactly
when their ends lie in the same cycle of the permutation `Π_E`; otherwise the orbits are
disjoint (`disjoint_shellOrbit`). -/
theorem shellOrbit_eq_iff {E : ℝ} (hE : V.ShellRegular E) (η ζ : V.allowedGerms E) :
    V.shellOrbit S hE η η.2 = V.shellOrbit S hE ζ ζ.2 ↔ (V.shellGermPerm S hE).SameCycle η ζ := by
  rw [← V.mem_germCycle_iff_sameCycle S hE]
  constructor
  · intro heq
    by_contra hne
    have hdisj := V.disjoint_shellOrbit S hE η.2 ζ.2 hne
    rw [heq, disjoint_self, Set.bot_eq_empty] at hdisj
    have : V.departureClass S hE ζ ζ.2 ∈ V.shellOrbit S hE ζ ζ.2 := ⟨0, flow_zero V S _⟩
    rw [hdisj] at this
    exact this
  · intro h
    exact (V.shellOrbit_eq_of_mem_germCycle S hE η.2 ζ.2 h).symm

/-- **Theorem VIII.5 (b): every point of the shell is periodic.**  A point on the orbit of the
departure state of `η` returns to itself after the period `T_c(E)` of the cycle of `η`, and after
no shorter positive time. -/
theorem flow_cyclePeriod_of_mem_shellOrbit {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {z : RegularScatteringPhaseSpace (V := V) S}
    (hz : z ∈ V.shellOrbit S hE η hη) :
    flow V S z (V.cyclePeriod S E η) = z ∧ ∀ t ∈ Ioo 0 (V.cyclePeriod S E η), flow V S z t ≠ z := by
  obtain ⟨u, rfl⟩ := hz
  have hTpos := V.cyclePeriod_pos S hE hη
  have hper := V.flow_cyclePeriod_departureClass S hE hη
  have hmin : ∀ v ∈ Ioo 0 (V.cyclePeriod S E η),
      flow V S (V.departureClass S hE η hη) v ≠ V.departureClass S hE η hη :=
    fun v hv => V.flow_departureClass_ne_self S hE hη hv
  refine ⟨?_, fun t ht h => ?_⟩
  · simp only
    rw [flow_flow, add_comm, ← flow_flow, hper]
  · simp only at h
    rw [flow_flow] at h
    obtain ⟨m, hm⟩ := (V.flow_eq_flow_iff_of_period S _ hTpos hper hmin (u + t) u).mp h
    have hmT : t = m • V.cyclePeriod S E η := by linarith
    rw [zsmul_eq_mul] at hmT
    rcases lt_or_ge m 0 with hlt | hge
    · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      nlinarith [ht.1]
    · rcases eq_or_lt_of_le hge with h0 | hpos
      · rw [← h0] at hmT; simp at hmT; linarith [ht.1]
      · have : (1 : ℝ) ≤ m := by exact_mod_cast hpos
        nlinarith [ht.2]

/-- **Theorem VIII.5 (b): every trajectory on `Σ_E` is periodic.**  Every point `z` of the shell
lies on the orbit of the departure state of an admissible end `η`, and returns to itself exactly
after the period `T_c(E) > 0` of the cycle of `η`: `Φ_{T_c}(z) = z`, and `Φ_t(z) ≠ z` for
`0 < t < T_c`. -/
theorem shell_periodic {E : ℝ} (hE : V.ShellRegular E) {z : RegularScatteringPhaseSpace (V := V) S}
    (hz : z ∈ V.shell S E) :
    ∃ η : Γ.EdgeEnd, ∃ hη : η ∈ V.allowedGerms E, z ∈ V.shellOrbit S hE η hη ∧
      0 < V.cyclePeriod S E η ∧ flow V S z (V.cyclePeriod S E η) = z ∧
      ∀ t ∈ Ioo 0 (V.cyclePeriod S E η), flow V S z t ≠ z := by
  obtain ⟨η, hη, hzη⟩ := (V.mem_shell_iff_exists_mem_shellOrbit S hE z).mp hz
  exact ⟨η, hη, hzη, V.cyclePeriod_pos S hE hη,
    V.flow_cyclePeriod_of_mem_shellOrbit S hE hη hzη⟩

/-! ### Uniqueness of the flight through a point of the shell -/

/-- Distinct admissible ends have distinct departure states. -/
theorem eq_of_departureClass_eq {E : ℝ} (hE : V.ShellRegular E) {η ζ : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (hζ : ζ ∈ V.allowedGerms E)
    (h : V.departureClass S hE η hη = V.departureClass S hE ζ hζ) : η = ζ := by
  have htr := V.trajectory_eq_of_trajClass_eq S (V.germFlight_notIncoming hE η hη)
    (V.germFlight_notIncoming hE ζ hζ) h
  have h1 := V.germTrajectory_zero S hE η hη
  have h2 := V.germTrajectory_zero S hE ζ hζ
  unfold germTrajectory at h1 h2
  rw [h1, h2] at htr
  have he := congrArg Prod.fst htr
  simp only at he
  have hcoord := congrArg (fun y => y.2.1) htr
  simp only [departurePoint] at hcoord
  exact edgeEnd_eq_of_coordinate_eq he hcoord

/-- **Uniqueness of the flight through a point.**  A point reached from the departure state of `η`
within its first flight is reached from no other departure state within that state's first
flight, and at only one time. -/
theorem eq_of_flow_departureClass_eq {E : ℝ} (hE : V.ShellRegular E) {η ζ : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (hζ : ζ ∈ V.allowedGerms E) {u u' : ℝ}
    (hu : u ∈ Ico 0 (V.flightTime E η)) (hu' : u' ∈ Ico 0 (V.flightTime E ζ))
    (h : flow V S (V.departureClass S hE η hη) u = flow V S (V.departureClass S hE ζ hζ) u') :
    η = ζ ∧ u = u' := by
  have hback : ∀ s, flow V S (flow V S (V.departureClass S hE η hη) u) (-s) =
      flow V S (flow V S (V.departureClass S hE ζ hζ) u') (-s) := fun s => by rw [h]
  rcases lt_trichotomy u u' with hlt | heq | hgt
  · exfalso
    have h1 := hback u
    rw [flow_flow_neg_self, flow_flow, ← sub_eq_add_neg] at h1
    exact V.flow_departureClass_ne_departureClass S hE hζ (by linarith)
      (by linarith [hu'.2, hu.1]) η hη
      h1.symm
  · refine ⟨?_, heq⟩
    have h1 := hback u
    rw [flow_flow_neg_self, heq, flow_flow_neg_self] at h1
    exact V.eq_of_departureClass_eq S hE hη hζ h1
  · exfalso
    have h1 := hback u'
    rw [flow_flow_neg_self, flow_flow, ← sub_eq_add_neg] at h1
    exact V.flow_departureClass_ne_departureClass S hE hη (by linarith)
      (by linarith [hu.2, hu'.1]) ζ hζ h1

/-- **Every point of the shell lies on a first flight.**  Each point of `Σ_E` is `Φ_w` of the
departure state of some admissible end `ξ`, with `0 ≤ w < t_E(ξ)`. -/
theorem exists_departureClass_flow_lt {E : ℝ} (hE : V.ShellRegular E)
    {z : RegularScatteringPhaseSpace (V := V) S} (hz : z ∈ V.shell S E) :
    ∃ ξ : Γ.EdgeEnd, ∃ hξ : ξ ∈ V.allowedGerms E, ∃ w ∈ Ico 0 (V.flightTime E ξ),
      z = flow V S (V.departureClass S hE ξ hξ) w := by
  obtain ⟨η, hη, u, hu, rfl⟩ := V.exists_mem_suspension S hE hz
  obtain ⟨k, -, hk1, hk2⟩ := V.exists_chainTime_le_lt S hE hη hu.1 hu.2
  refine ⟨(V.germStep S E)^[k] η, V.germStep_iterate_mem S hE hη k,
    u - chainTime V S (η, V.germSpeed η E) k, ⟨by linarith, ?_⟩, ?_⟩
  · rw [V.chainTime_succ_germSpeed S hE hη k] at hk2
    linarith
  · rw [← V.flow_departureClass_chainTime S hE hη k, flow_flow, add_sub_cancel]

end Flow

end MechanicalPotential

end HamiltonianMetricGraphs
