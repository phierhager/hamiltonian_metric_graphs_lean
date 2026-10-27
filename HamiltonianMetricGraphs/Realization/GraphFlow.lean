/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.RoutingScattering
import HamiltonianMetricGraphs.Realization.HybridChain
import HamiltonianMetricGraphs.FlightRetrace

/-!
# Routing laws as Borel vertex data, and the flow they generate

The realization programme drives its graph dynamics by a `RoutingLaw Γ`; the paper's global
metric-graph flow `MechanicalPotential.FlightState.trajectory` is driven by a
`BorelEnergyPreservingScattering V`.  `RoutingScattering.lean` already produces the *algebraic*
scattering law `F.toScattering V`; what is missing for the paper's flow is Borel measurability of
the vertex bijection.

That is supplied here.  In the speed charts of `Measurable.lean` the routing law is literally the
map `(η, r) ↦ (F_v η, r)`: it permutes the finitely many incident germs and leaves the speed
alone.  Since the germ space carries the discrete σ-algebra, this is measurable for trivial
reasons, and `F.toBorelScattering V` is therefore a genuine vertex datum of the paper.

Consequently the paper's flow `Φ_t^{Γ,F}` is defined for every routing law, and the realization
programme and the paper's global theory speak about the *same* dynamics.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

namespace RoutingLaw

variable {Γ : FiniteMetricGraph} (F : RoutingLaw Γ)

/-- In the speed charts the routing law acts as `(η, r) ↦ (F_v η, r)`. -/
theorem scatterEquiv_eq_chart (v : Γ.Vertex) (α : Γ.IncomingBoundary v) :
    F.scatterEquiv v α =
      (Γ.outgoingSpeedChart v)
        ((F.routePerm v ((Γ.incomingSpeedChart v).symm α).1),
          ((Γ.incomingSpeedChart v).symm α).2) := rfl

/-- The permutation of the incident germs is measurable: the germ space is discrete. -/
theorem measurable_routePerm (v : Γ.Vertex) : Measurable (F.routePerm v) :=
  Measurable.of_discrete

theorem measurable_routePerm_symm (v : Γ.Vertex) : Measurable (F.routePerm v).symm :=
  Measurable.of_discrete

/-- **A routing law is a Borel vertex datum.**  Its scattering bijection and the inverse are
measurable, because in speed coordinates both are a discrete germ permutation times the identity
on the speed. -/
noncomputable def scatterMeasurableEquiv (v : Γ.Vertex) :
    Γ.IncomingBoundary v ≃ᵐ Γ.OutgoingBoundary v where
  toEquiv := F.scatterEquiv v
  measurable_toFun := by
    have hchart : (fun α : Γ.IncomingBoundary v => F.scatterEquiv v α) =
        (fun x : Γ.IncidentEnds v × PositiveSpeed =>
            (Γ.outgoingSpeedChart v) (F.routePerm v x.1, x.2)) ∘
          (Γ.incomingSpeedChart v).symm := by
      funext α
      exact F.scatterEquiv_eq_chart v α
    change Measurable (fun α : Γ.IncomingBoundary v => F.scatterEquiv v α)
    rw [hchart]
    exact (((Γ.outgoingSpeedChart v).measurable_toFun).comp
      (((F.measurable_routePerm v).comp measurable_fst).prodMk measurable_snd)).comp
      (Γ.incomingSpeedChart v).measurable_invFun
  measurable_invFun := by
    have hchart : (fun β : Γ.OutgoingBoundary v => (F.scatterEquiv v).symm β) =
        (fun x : Γ.IncidentEnds v × PositiveSpeed =>
            (Γ.incomingSpeedChart v) ((F.routePerm v).symm x.1, x.2)) ∘
          (Γ.outgoingSpeedChart v).symm := by
      funext β
      have h : (F.scatterEquiv v).symm β = F.unscatter v β := rfl
      rw [h]
      rfl
    change Measurable (fun β : Γ.OutgoingBoundary v => (F.scatterEquiv v).symm β)
    rw [hchart]
    exact (((Γ.incomingSpeedChart v).measurable_toFun).comp
      (((F.measurable_routePerm_symm v).comp measurable_fst).prodMk measurable_snd)).comp
      (Γ.outgoingSpeedChart v).measurable_invFun

@[simp] theorem scatterMeasurableEquiv_apply (v : Γ.Vertex) (α : Γ.IncomingBoundary v) :
    F.scatterMeasurableEquiv v α = F.scatter v α := rfl

/-- **The routing law as a Borel energy-preserving vertex scattering law.**  This is the datum the
paper's global flow `FlightState.trajectory` takes as input, so the deterministic graph dynamics
of the realization programme is literally an instance of the paper's flow. -/
noncomputable def toBorelScattering (V : MechanicalPotential Γ) :
    MechanicalPotential.BorelEnergyPreservingScattering V where
  map := F.scatterMeasurableEquiv
  preserves_energy := (F.toScattering V).preserves_energy

@[simp] theorem toBorelScattering_map_apply (V : MechanicalPotential Γ) (v : Γ.Vertex)
    (α : Γ.IncomingBoundary v) : (F.toBorelScattering V).map v α = F.scatter v α := rfl

/-- Forgetting measurability returns the algebraic scattering law of `RoutingScattering.lean`. -/
theorem toBorelScattering_toEnergyPreservingScattering (V : MechanicalPotential Γ) :
    (F.toBorelScattering V).toEnergyPreservingScattering = F.toScattering V := rfl

/-- **Proposition III.2 for the Borel form**: the fixed-speed endpoint permutation of the vertex
law induced by `F` is `F_v` itself, at every speed. -/
theorem speedEndpoint_toBorelScattering (V : MechanicalPotential Γ) (v : Γ.Vertex)
    (η : Γ.IncidentEnds v) (r : PositiveSpeed) :
    MechanicalPotential.EnergyPreservingScattering.speedEndpoint V
        (F.toBorelScattering V).toEnergyPreservingScattering v η r = F.route v η :=
  F.speedEndpoint_toScattering V v η r

/-- The germ through which a particle arriving along `η` leaves the vertex is `F.routeGerm η`. -/
theorem scatter_germ (v : Γ.Vertex) (α : Γ.IncomingBoundary v) :
    (F.scatter v α).1.germ = F.routeGerm α.1.germ := by
  have h : (F.scatter v α).1.germ = (F.route v ⟨α.1.germ, α.2.1⟩).1 := by
    rw [scatter, outgoingAtSpeed_end]
  rw [h, F.route_fst_eq_routeGerm]

/-- The outgoing momentum after the passage is the routed momentum of the incoming one. -/
theorem scatter_momentum (v : Γ.Vertex) (α : Γ.IncomingBoundary v) :
    (F.scatter v α).1.momentum = F.departureMomentum α.1.germ α.1.momentum := by
  rw [scatter, outgoingAtSpeed_momentum, departureMomentum, ← F.scatter_germ v α]
  rw [scatter, outgoingAtSpeed_end]
  ring

end RoutingLaw

/-!
## The arrival germ of a flight

The within-`Icc` form of the flight ODE (`flightCurve_hasDerivWithinAt_Icc`) and the landing-point
identity (`flightCurve_sSup`) now live in `FlightRetrace`; here they are read on the chain.
-/

namespace MechanicalPotential

namespace FlightState

variable {Γ : FiniteMetricGraph} {V : MechanicalPotential Γ}

open PhysicalEdgeSegment

/-- **The germ through which a terminating flight leaves its edge.**  In the escaping case there is
no arrival and the value is the (irrelevant) default `(edge, false)`. -/
noncomputable def arrivalGerm (b : V.FlightState) : Γ.EdgeEnd := by
  classical
  exact if hbdd : BddAbove (durationSet V b.edge b.state) then
    (b.segment.maximalArrivalCovector hbdd b.regular).germ
  else (b.edge, false)

/-- The arrival germ sits on the flight's own edge. -/
@[simp] theorem arrivalGerm_fst (b : V.FlightState) : b.arrivalGerm.1 = b.edge := by
  classical
  unfold arrivalGerm
  by_cases hbdd : BddAbove (durationSet V b.edge b.state)
  · rw [dif_pos hbdd]
    exact b.segment.maximalArrivalCovector_germ_fst hbdd b.regular
  · rw [dif_neg hbdd]

theorem arrivalGerm_eq_of_bddAbove (b : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) :
    b.arrivalGerm = (b.segment.maximalArrivalCovector hbdd b.regular).germ := by
  classical
  unfold arrivalGerm; rw [dif_pos hbdd]

/-- **The flight arrives at the vertex coordinate of its arrival germ.**  This is the analytic
first-hit alternative in the form `HybridChain.arrive` needs. -/
theorem flightCurve_sSup_fst (b : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) :
    (flightCurve V b (sSup (durationSet V b.edge b.state))).1 =
      EdgeEnd.coordinate Γ b.arrivalGerm := by
  rw [flightCurve_sSup b hbdd, arrivalGerm_eq_of_bddAbove b hbdd,
    b.segment.maximalArrivalCovector_coordinate hbdd b.regular]

theorem flightCurve_sSup_snd (b : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) :
    (flightCurve V b (sSup (durationSet V b.edge b.state))).2 =
      (b.segment.maximalArrivalCovector hbdd b.regular).momentum := by
  rw [flightCurve_sSup b hbdd, b.segment.maximalArrivalCovector_momentum hbdd b.regular]

/-! ### The chain of the paper's flow -/

/-- The flight state reached after `j` scattering events. -/
noncomputable def flowState (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (j : ℕ) : V.FlightState := (iterate V S a j).getD a

@[simp] theorem flowState_zero (S : BorelEnergyPreservingScattering V) (a : V.FlightState) :
    flowState S a 0 = a := by rw [flowState, iterate_zero]; rfl

theorem iterate_eq_flowState {S : BorelEnergyPreservingScattering V} {a : V.FlightState} {j : ℕ}
    (hj : (iterate V S a j).isSome) : iterate V S a j = some (flowState S a j) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hj
  rw [hb, flowState, hb]; rfl

theorem iterate_succ_flowState {S : BorelEnergyPreservingScattering V} {a : V.FlightState}
    {j : ℕ} (hj : (iterate V S a j).isSome) :
    iterate V S a (j + 1) = next V S (flowState S a j) := by
  rw [iterate_succ, iterate_eq_flowState hj]
  rfl

/-- The duration of the `j`-th flight of the chain. -/
noncomputable def flowDur (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (j : ℕ) : ℝ :=
  sSup (durationSet V (flowState S a j).edge (flowState S a j).state)

theorem bddAbove_flow {S : BorelEnergyPreservingScattering V} {a : V.FlightState} {j : ℕ}
    (hj : (iterate V S a (j + 1)).isSome) :
    BddAbove (durationSet V (flowState S a j).edge (flowState S a j).state) := by
  rw [iterate_succ_flowState (iterate_isSome_of_le (V := V) (Nat.le_succ j) hj)] at hj
  exact bddAbove_of_next_isSome (V := V) (S := S) hj

theorem not_bddAbove_flow {S : BorelEnergyPreservingScattering V} {a : V.FlightState} {j : ℕ}
    (hj : (iterate V S a j).isSome) (hj' : ¬ (iterate V S a (j + 1)).isSome) :
    ¬ BddAbove (durationSet V (flowState S a j).edge (flowState S a j).state) := by
  rw [Option.not_isSome_iff_eq_none, iterate_succ_flowState hj] at hj'
  exact (next_eq_none_iff (V := V) S _).mp hj'

theorem impactReal_succ_flow {S : BorelEnergyPreservingScattering V} {a : V.FlightState} {j : ℕ}
    (hj : (iterate V S a (j + 1)).isSome) :
    impactReal V S a (j + 1) = impactReal V S a j + flowDur S a j :=
  impactReal_succ_eq_of_isSome (V := V)
    (iterate_eq_flowState (iterate_isSome_of_le (V := V) (Nat.le_succ j) hj)) hj

/-- **The scattering step of a routing law, read on the chain.**  The next flight is on the routed
edge, starts at the routed vertex and carries the routed momentum. -/
theorem flowState_succ_routing (F : RoutingLaw Γ) {a : V.FlightState} {j : ℕ}
    (hj : (iterate V (F.toBorelScattering V) a (j + 1)).isSome) :
    (flowState (F.toBorelScattering V) a (j + 1)).edge =
        (F.routeGerm (flowState (F.toBorelScattering V) a j).arrivalGerm).1 ∧
      (flowState (F.toBorelScattering V) a (j + 1)).state =
        (EdgeEnd.coordinate Γ (F.routeGerm (flowState (F.toBorelScattering V) a j).arrivalGerm),
          F.departureMomentum (flowState (F.toBorelScattering V) a j).arrivalGerm
            (flightCurve V (flowState (F.toBorelScattering V) a j)
              (flowDur (F.toBorelScattering V) a j)).2) := by
  set S := F.toBorelScattering V with hS
  set b := flowState S a j with hb
  have hjS : (iterate V S a j).isSome := iterate_isSome_of_le (V := V) (Nat.le_succ j) hj
  have hbdd : BddAbove (durationSet V b.edge b.state) := bddAbove_flow hj
  obtain ⟨c, hc, hcstate, -, -, hcedge⟩ := next_eq_some_of_bddAbove (V := V) S b hbdd
  have hstep : iterate V S a (j + 1) = some c := by
    rw [iterate_succ_flowState hjS]; exact hc
  have hflow : flowState S a (j + 1) = c := by rw [flowState, hstep]; rfl
  set α := b.segment.maximalArrivalIncoming hbdd b.regular with hα
  have hα1 : α.1 = b.segment.maximalArrivalCovector hbdd b.regular := rfl
  have hgerm : (S.map α.1.germ.vertex α).1.germ = F.routeGerm b.arrivalGerm := by
    rw [hS, RoutingLaw.toBorelScattering_map_apply, F.scatter_germ, hα1,
      ← arrivalGerm_eq_of_bddAbove b hbdd]
  have hmom : (S.map α.1.germ.vertex α).1.momentum =
      F.departureMomentum b.arrivalGerm (flightCurve V b (flowDur S a j)).2 := by
    rw [hS, RoutingLaw.toBorelScattering_map_apply, F.scatter_momentum, hα1,
      ← arrivalGerm_eq_of_bddAbove b hbdd, flowDur, ← hb, flightCurve_sSup_snd b hbdd]
  refine ⟨?_, ?_⟩
  · rw [hflow, hcedge, hgerm]
  · rw [hflow, hcstate, hgerm, hmom]

/-! ### The time grid of the chain -/

/-- The start time of the `j`-th flight of the chain. -/
noncomputable def flowStart (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (j : ℕ) : ℝ := impactReal V S a j

/-- The end time of the `j`-th flight: the next impact, or the window end `TM` on the final
flight. -/
noncomputable def flowStop (S : BorelEnergyPreservingScattering V) (a : V.FlightState)
    (M : ℕ) (TM : ℝ) (j : ℕ) : ℝ := if j < M then impactReal V S a (j + 1) else TM

theorem flowStop_of_lt {S : BorelEnergyPreservingScattering V} {a : V.FlightState} {M : ℕ}
    {TM : ℝ} {j : ℕ} (hj : j < M) : flowStop S a M TM j = impactReal V S a (j + 1) := by
  rw [flowStop, if_pos hj]

theorem flowStop_of_not_lt {S : BorelEnergyPreservingScattering V} {a : V.FlightState} {M : ℕ}
    {TM : ℝ} {j : ℕ} (hj : ¬ j < M) : flowStop S a M TM j = TM := by rw [flowStop, if_neg hj]

/-- **A finite window of the paper's flow.**  The chain of `a` is defined through `M` scattering
events, and the final flight is followed up to the time `TM`, still strictly before its own
(possibly infinite) impact. -/
structure FlowRun (S : BorelEnergyPreservingScattering V) (a : V.FlightState) (M : ℕ) (TM : ℝ) :
    Prop where
  defined : (iterate V S a M).isSome
  last_lt : impactReal V S a M < TM
  last_dur : ∀ _ : BddAbove (durationSet V (flowState S a M).edge (flowState S a M).state),
    TM - impactReal V S a M < flowDur S a M

namespace FlowRun

variable {S : BorelEnergyPreservingScattering V} {a : V.FlightState} {M : ℕ} {TM : ℝ}

theorem isSome_of_le (R : FlowRun S a M TM) {j : ℕ} (hj : j ≤ M) : (iterate V S a j).isSome :=
  iterate_isSome_of_le (V := V) hj R.defined

theorem start_lt_stop (R : FlowRun S a M TM) {j : ℕ} (hj : j ≤ M) :
    flowStart S a j < flowStop S a M TM j := by
  rcases lt_or_ge j M with h | h
  · rw [flowStop_of_lt h, flowStart]
    exact impactReal_lt_succ_of_isSome (V := V) (R.isSome_of_le h)
  · have hjM : j = M := le_antisymm hj h
    subst hjM
    rw [flowStop_of_not_lt (lt_irrefl j), flowStart]
    exact R.last_lt

/-- The length of flight `j` never exceeds the flight's own maximal duration. -/
theorem stop_sub_start_le (R : FlowRun S a M TM) {j : ℕ} (hj : j ≤ M)
    (hbdd : BddAbove (durationSet V (flowState S a j).edge (flowState S a j).state)) :
    flowStop S a M TM j - flowStart S a j ≤ flowDur S a j := by
  rcases lt_or_ge j M with h | h
  · rw [flowStop_of_lt h, flowStart, impactReal_succ_flow (R.isSome_of_le h)]
    linarith
  · have hjM : j = M := le_antisymm hj h
    subst hjM
    rw [flowStop_of_not_lt (lt_irrefl j), flowStart]
    exact le_of_lt (R.last_dur hbdd)

/-- Strictly inside a flight, the elapsed time is strictly below the maximal duration. -/
theorem sub_start_lt (R : FlowRun S a M TM) {j : ℕ} (hj : j ≤ M) {t : ℝ}
    (ht : t < flowStop S a M TM j)
    (hbdd : BddAbove (durationSet V (flowState S a j).edge (flowState S a j).state)) :
    t - flowStart S a j < flowDur S a j := by
  have := R.stop_sub_start_le hj hbdd
  linarith

end FlowRun
/-! ### The graph trajectory recorded by a window of the flow -/

theorem hasDerivWithinAt_shift {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {A B t : ℝ}
    (h : HasDerivWithinAt f f' (Icc 0 (B - A)) (t - A)) (_ : t ∈ Icc A B) :
    HasDerivWithinAt (fun s => f (s - A)) f' (Icc A B) t := by
  have hf : HasDerivWithinAt (fun s : ℝ => s - A) 1 (Icc A B) t :=
    (hasDerivWithinAt_id t (Icc A B)).sub_const A
  have hmaps : MapsTo (fun s : ℝ => s - A) (Icc A B) (Icc 0 (B - A)) := by
    intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h2 := h.scomp t hf hmaps
  rw [one_smul] at h2
  exact h2

namespace FlowRun

variable {S : BorelEnergyPreservingScattering V} {a : V.FlightState} {M : ℕ} {TM : ℝ}

theorem mem_shift {j : ℕ} {t : ℝ}
    (ht : t ∈ Icc (flowStart S a j) (flowStop S a M TM j)) :
    t - flowStart S a j ∈ Icc (0 : ℝ) (flowStop S a M TM j - flowStart S a j) :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Hamilton's equations along a flight of the chain, in the `HasDerivWithinAt` form of
`HybridChain.flight_ode`. -/
theorem flight_deriv (R : FlowRun S a M TM) {j : ℕ} (hj : j ≤ M) {t : ℝ}
    (ht : t ∈ Icc (flowStart S a j) (flowStop S a M TM j)) :
    HasDerivWithinAt (fun s => flightCurve V (flowState S a j) (s - flowStart S a j))
      (V.edgeVectorField (flowState S a j).edge
        (flightCurve V (flowState S a j) (t - flowStart S a j)))
      (Icc (flowStart S a j) (flowStop S a M TM j)) t :=
  hasDerivWithinAt_shift
    (flightCurve_hasDerivWithinAt_Icc (flowState S a j)
      (fun hbdd => R.stop_sub_start_le hj hbdd) (mem_shift ht)) ht

/-- A flight of the chain stays on the closed physical edge. -/
theorem flight_closed (R : FlowRun S a M TM) {j : ℕ} (hj : j ≤ M) {t : ℝ}
    (ht : t ∈ Icc (flowStart S a j) (flowStop S a M TM j)) :
    (flightCurve V (flowState S a j) (t - flowStart S a j)).1 ∈
      Icc (0 : ℝ) (Γ.length (flowState S a j).edge) :=
  flightCurve_physical V (flowState S a j) (mem_shift ht).1
    (fun hbdd => le_trans (mem_shift ht).2 (R.stop_sub_start_le hj hbdd))

/-- Strictly inside a flight the chain is in the open edge. -/
theorem flight_open (R : FlowRun S a M TM) {j : ℕ} (hj : j ≤ M) {t : ℝ}
    (ht : t ∈ Ioo (flowStart S a j) (flowStop S a M TM j)) :
    (flightCurve V (flowState S a j) (t - flowStart S a j)).1 ∈
      Ioo (0 : ℝ) (Γ.length (flowState S a j).edge) :=
  flightCurve_interior V (flowState S a j) (by linarith [ht.1])
    (fun hbdd => R.sub_start_lt hj ht.2 hbdd)

/-- The last flight of the window ends strictly inside its edge. -/
theorem final_open (R : FlowRun S a M TM) :
    (flightCurve V (flowState S a M) (flowStop S a M TM M - flowStart S a M)).1 ∈
      Ioo (0 : ℝ) (Γ.length (flowState S a M).edge) := by
  rw [flowStop_of_not_lt (lt_irrefl M), flowStart]
  exact flightCurve_interior V (flowState S a M) (by linarith [R.last_lt]) R.last_dur

/-- The length of a non-final flight is exactly its maximal duration. -/
theorem stop_sub_start_eq (R : FlowRun S a M TM) {j : ℕ} (hj : j < M) :
    flowStop S a M TM j - flowStart S a j = flowDur S a j := by
  rw [flowStop_of_lt hj, flowStart, impactReal_succ_flow (R.isSome_of_le (Nat.succ_le_of_lt hj))]
  ring

/-- **The flight arrives at the vertex coordinate of its arrival germ.** -/
theorem arrive_coord (R : FlowRun S a M TM) {j : ℕ} (hj : j < M) :
    (flightCurve V (flowState S a j) (flowStop S a M TM j - flowStart S a j)).1 =
      EdgeEnd.coordinate Γ (flowState S a j).arrivalGerm := by
  rw [R.stop_sub_start_eq hj, flowDur]
  exact flightCurve_sSup_fst (flowState S a j) (bddAbove_flow (R.isSome_of_le
    (Nat.succ_le_of_lt hj)))

end FlowRun

namespace FlowRun
/-! ### The graph trajectory itself -/

variable {F : RoutingLaw Γ}

/-- **The graph trajectory recorded by a finite window of the paper's flow.**  Its flights are the
flights of the scattered chain of `a`, its impacts are the scattering events, and its routing is
the routing law `F` that generated the vertex data. -/
noncomputable def chain {a : V.FlightState} {M : ℕ} {TM : ℝ}
    (R : FlowRun (F.toBorelScattering V) a M TM) : GraphTrajectory V F where
  N := M
  start := flowStart (F.toBorelScattering V) a
  stop := flowStop (F.toBorelScattering V) a M TM
  edge j := (flowState (F.toBorelScattering V) a j).edge
  curve j t := flightCurve V (flowState (F.toBorelScattering V) a j)
    (t - flowStart (F.toBorelScattering V) a j)
  germ j := (flowState (F.toBorelScattering V) a j).arrivalGerm
  start_zero := by rw [flowStart, impactReal_zero]
  start_lt_stop := fun _ hj => R.start_lt_stop hj
  stop_le_start_succ := fun _ hj => by rw [flowStop_of_lt hj, flowStart]
  start_succ_le := fun _ hj => by rw [flowStop_of_lt hj, flowStart]; simp
  flight_ode := fun j hj =>
    ⟨fun t => V.edgeVectorField (flowState (F.toBorelScattering V) a j).edge
        (flightCurve V (flowState (F.toBorelScattering V) a j)
          (t - flowStart (F.toBorelScattering V) a j)),
      fun _ ht => ⟨by simp, R.flight_deriv hj ht⟩⟩
  flight_tube := fun _ hj _ ht => by simpa using R.flight_closed hj ht
  flight_inside := fun _ hj _ ht => by simpa using R.flight_open hj ht
  final_inside := by simpa using R.final_open
  germ_edge := fun _ _ => arrivalGerm_fst _
  arrive := fun _ hj => by simpa using R.arrive_coord hj
  edge_succ := fun _ hj => (flowState_succ_routing F (R.isSome_of_le (Nat.succ_le_of_lt hj))).1
  depart_coord := fun j hj => by
    have h := (flowState_succ_routing F (R.isSome_of_le (Nat.succ_le_of_lt hj))).2
    change (flightCurve V (flowState (F.toBorelScattering V) a (j + 1))
      (flowStart (F.toBorelScattering V) a (j + 1)
        - flowStart (F.toBorelScattering V) a (j + 1))).1 = _
    rw [sub_self, flightCurve_zero, h]
    simp
  depart_mom := fun j hj => by
    have h := (flowState_succ_routing F (R.isSome_of_le (Nat.succ_le_of_lt hj))).2
    change |(flightCurve V (flowState (F.toBorelScattering V) a (j + 1))
        (flowStart (F.toBorelScattering V) a (j + 1)
          - flowStart (F.toBorelScattering V) a (j + 1))).2
      - F.departureMomentum (flowState (F.toBorelScattering V) a j).arrivalGerm
        (flightCurve V (flowState (F.toBorelScattering V) a j)
          (flowStop (F.toBorelScattering V) a M TM j
            - flowStart (F.toBorelScattering V) a j)).2| ≤ _
    rw [sub_self, flightCurve_zero, h, R.stop_sub_start_eq hj]
    simp

variable {a : V.FlightState} {M : ℕ} {TM : ℝ}

@[simp] theorem chain_N (R : FlowRun (F.toBorelScattering V) a M TM) : R.chain.N = M := rfl

@[simp] theorem chain_edge (R : FlowRun (F.toBorelScattering V) a M TM) (j : ℕ) :
    (R.chain (F := F)).edge j = (flowState (F.toBorelScattering V) a j).edge := rfl

@[simp] theorem chain_germ (R : FlowRun (F.toBorelScattering V) a M TM) (j : ℕ) :
    (R.chain (F := F)).germ j = (flowState (F.toBorelScattering V) a j).arrivalGerm := rfl

@[simp] theorem chain_start (R : FlowRun (F.toBorelScattering V) a M TM) (j : ℕ) :
    (R.chain (F := F)).start j = impactReal V (F.toBorelScattering V) a j := rfl

@[simp] theorem chain_stop (R : FlowRun (F.toBorelScattering V) a M TM) (j : ℕ) :
    (R.chain (F := F)).stop j = flowStop (F.toBorelScattering V) a M TM j := rfl

@[simp] theorem chain_curve (R : FlowRun (F.toBorelScattering V) a M TM) (j : ℕ) (t : ℝ) :
    (R.chain (F := F)).curve j t =
      flightCurve V (flowState (F.toBorelScattering V) a j)
        (t - impactReal V (F.toBorelScattering V) a j) := rfl

theorem chain_curve_zero (R : FlowRun (F.toBorelScattering V) a M TM) :
    (R.chain (F := F)).curve 0 0 = a.state := by
  rw [chain_curve, impactReal_zero, sub_zero, flowState_zero, flightCurve_zero]

theorem chain_edge_zero (R : FlowRun (F.toBorelScattering V) a M TM) :
    (R.chain (F := F)).edge 0 = a.edge := by rw [chain_edge, flowState_zero]

theorem chain_germ_zero (R : FlowRun (F.toBorelScattering V) a M TM) :
    (R.chain (F := F)).germ 0 = a.arrivalGerm := by rw [chain_germ, flowState_zero]

theorem chain_stop_N (R : FlowRun (F.toBorelScattering V) a M TM) :
    (R.chain (F := F)).stop (R.chain (F := F)).N = TM := by
  rw [chain_N, chain_stop, flowStop_of_not_lt (lt_irrefl M)]

/-! ### The chain is the paper's flow -/

/-- Inside the window the flight index of the chain is the active index of the flow. -/
theorem chain_flightIndex [Nonempty Γ.Edge] (R : FlowRun (F.toBorelScattering V) a M TM) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) TM) {n : ℕ}
    (hact : ActiveAt V (F.toBorelScattering V) a n t) :
    (R.chain (F := F)).flightIndex t = n := by
  set S := F.toBorelScattering V with hS
  have hnM : n ≤ M := by
    by_contra hcon
    rw [not_le] at hcon
    have hsucc : (iterate V S a (M + 1)).isSome :=
      iterate_isSome_of_le (V := V) (Nat.succ_le_of_lt hcon) hact.1
    have hdur : impactReal V S a (M + 1) = impactReal V S a M + flowDur S a M :=
      impactReal_succ_flow hsucc
    have hbdd := bddAbove_flow (S := S) (a := a) (j := M) hsucc
    have h1 := R.last_dur hbdd
    have h2 : impactReal V S a (M + 1) ≤ impactReal V S a n :=
      impactReal_monotone_of_isSome (V := V) hact.1 (Nat.succ_le_of_lt hcon)
    have h3 := hact.2.1
    linarith [ht.2]
  refine (R.chain (F := F)).flightIndex_eq_of_mem (by rw [chain_N]; exact hnM) ?_ ?_
  · rw [chain_start]; exact hact.2.1
  · intro hlt
    rw [chain_N] at hlt
    rw [chain_start]
    exact hact.2.2 (R.isSome_of_le (Nat.succ_le_of_lt hlt))

/-- **The graph trajectory of the window is exactly the paper's global flow.**  Every projected
state of the chain is the value of `FlightState.trajectory` at the same time. -/
theorem chain_state_eq [Nonempty Γ.Edge] (R : FlowRun (F.toBorelScattering V) a M TM) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) TM) :
    (R.chain (F := F)).state t = trajectory V (F.toBorelScattering V) a t := by
  obtain ⟨n, hact⟩ := exists_activeAt V (F.toBorelScattering V) a ht.1
  rw [(R.chain (F := F)).state_eq_of_flightIndex_eq (R.chain_flightIndex ht hact),
    trajectory_eq V (F.toBorelScattering V) a ht.1 hact (iterate_eq_flowState hact.1)]
  rfl

end FlowRun

/-! ### Every finite time window of the flow is a graph trajectory -/

/-- A finite window of the flow of any Borel vertex law exists past every time. -/
theorem exists_flowRun [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) {T : ℝ} (hT : 0 ≤ T) :
    ∃ (M : ℕ) (TM : ℝ), T ≤ TM ∧ FlowRun S a M TM := by
  classical
  obtain ⟨n, hact⟩ := exists_activeAt V S a hT
  by_cases hsucc : (iterate V S a (n + 1)).isSome
  · have hdur : impactReal V S a (n + 1) = impactReal V S a n + flowDur S a n :=
      impactReal_succ_flow hsucc
    have hlt : impactReal V S a n < impactReal V S a (n + 1) :=
      impactReal_lt_succ_of_isSome (V := V) hsucc
    have hT' : T < impactReal V S a (n + 1) := hact.2.2 hsucc
    refine ⟨n, max T ((impactReal V S a n + impactReal V S a (n + 1)) / 2), le_max_left _ _,
      hact.1, ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · intro _
      have h1 : max T ((impactReal V S a n + impactReal V S a (n + 1)) / 2)
          < impactReal V S a (n + 1) := max_lt hT' (by linarith)
      linarith
  · refine ⟨n, max T (impactReal V S a n + 1), le_max_left _ _, hact.1, ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · intro hbdd
      exact absurd hbdd (not_bddAbove_flow hact.1 hsucc)

/-- **Every finite window of the paper's global metric-graph flow is a graph trajectory of the
realization programme.**

Given a routing law `F`, a regular flight state `a`, and a horizon `T ≥ 0`, there is a
`GraphTrajectory V F` which starts at `a` and whose projected state function coincides with the
paper's flow `Φ_t^{Γ,F}` on the whole of `[0, T]`.

This is the interface between the two developments: the deterministic graph dynamics that
`thin_junction_hamiltonian_limit` produces as its limit *is* the paper's flow, restricted to a
finite window. -/
theorem exists_graphTrajectory_of_flow [Nonempty Γ.Edge] (F : RoutingLaw Γ) (a : V.FlightState)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ g : GraphTrajectory V F, g.edge 0 = a.edge ∧ g.germ 0 = a.arrivalGerm ∧
      g.curve 0 0 = a.state ∧ T ≤ g.stop g.N ∧
      ∀ t ∈ Icc (0 : ℝ) (g.stop g.N),
        g.state t = trajectory V (F.toBorelScattering V) a t := by
  obtain ⟨M, TM, hTM, R⟩ := exists_flowRun (F.toBorelScattering V) a hT
  refine ⟨R.chain (F := F), R.chain_edge_zero, R.chain_germ_zero, R.chain_curve_zero, ?_, ?_⟩
  · rw [R.chain_stop_N]; exact hTM
  · intro t ht
    rw [R.chain_stop_N] at ht
    exact R.chain_state_eq ht

end FlightState

end MechanicalPotential

end HamiltonianMetricGraphs
