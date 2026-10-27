/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

The germ permutation of a regular energy shell
-/

import HamiltonianMetricGraphs.ChainModel
import HamiltonianMetricGraphs.GermTube

/-!
# The germ permutation of a regular energy shell

Fix an energy `E` which is not one of the finitely many vertex values and at which every flight
reaches a vertex in finite time (`ShellRegular`).  A flight at energy `E` departing the germ `η`
does so at the speed `germSpeed η E = sqrt (2 * (E - V (vertex η)))`, so between impacts the state
of the trajectory is described by the germ alone: the germ-speed chain of `ChainModel.lean`
collapses to a self-map

`germStep E : Γ.EdgeEnd → Γ.EdgeEnd`

of the finite set of germs `η` with `V (vertex η) < E` (`allowedGerms E`).

The main result is that `germStep E` is a **permutation** of `allowedGerms E`.  It factors as
scattering after a retrace step,

`germStep E = scattering ∘ retraceStep E`,

where `retraceStep` sends a departing germ to the germ at which its flight lands, with the momentum
reversed so that it departs again.  Both factors are injective:

* `retraceStep` is an **involution** (`retraceStep_involutive`): the flight from a reversed landing
  point runs the original flight backwards and lands at the reversed departure point, by the
  retrace lemmas of `FlightRetrace.lean`;
* the scattering factor is injective because the vertex law is a bijection of the incoming
  boundary section (Proposition III.2), and at a fixed energy every germ at a given vertex carries
  the same speed, so a single fixed-speed bijection is applied
  (`retraceStep_eq_of_departureStep_eq`).

Since `Γ.EdgeEnd` is finite, an injective self-map of `allowedGerms E` is a bijection
(`shellGermPerm`), so every germ is periodic: `germStep E ^[n] η = η` for some `n ≥ 1`
(`exists_germStep_period`).  Translating back through the chain model, the trajectory of the flight
departing `η` returns to its departure point after the finite time accumulated along that germ
cycle (`trajectory_period`).

A shell of a shell-regular energy is therefore a finite disjoint union of periodic orbits, and the
flow on it is the suspension of the finite permutation `germStep E` with the flight durations as
return times.  The cycle type of `germStep E` is the combinatorial invariant of the shell, and it
can only change where the hypotheses of `ShellRegular` fail — at a vertex value, or at a critical
value of the potential inside an edge — or where the vertex law itself changes with the speed.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory PhysicalEdgeSegment
open scoped Topology ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The landing point of a departure flight -/

/-- The landing point of a departure flight is the maximal endpoint of the flight state. -/
theorem departureLanding_eq_maximalEndpoint {η : Γ.EdgeEnd} {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V (V.ofDeparture η hr.1 hr.2).edge
      (V.ofDeparture η hr.1 hr.2).state)) :
    V.departureLanding η r = (V.ofDeparture η hr.1 hr.2).segment.maximalEndpoint hbdd := by
  rw [departureLanding, V.departureFlight_of_mem hr]
  exact FlightState.flightCurve_sSup (V.ofDeparture η hr.1 hr.2) hbdd

/-- A departure flight lands with nonzero momentum. -/
theorem departureLanding_momentum_ne_zero {η : Γ.EdgeEnd} {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    (V.departureLanding η r).2 ≠ 0 := by
  have hbdd' : BddAbove (durationSet V (V.ofDeparture η hr.1 hr.2).edge
      (V.ofDeparture η hr.1 hr.2).state) := hbdd
  rw [V.departureLanding_eq_maximalEndpoint hr hbdd']
  exact (V.ofDeparture η hr.1 hr.2).segment.maximalEndpoint_momentum_ne_zero hbdd'
    (V.ofDeparture η hr.1 hr.2).regular

/-- The energy at the landing point is the departure energy. -/
theorem hamiltonian_departureLanding {η : Γ.EdgeEnd} {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    V.hamiltonian η.1 (V.departureLanding η r).1 (V.departureLanding η r).2
      = V.departureEnergy η r := by
  have hbdd' : BddAbove (durationSet V (V.ofDeparture η hr.1 hr.2).edge
      (V.ofDeparture η hr.1 hr.2).state) := hbdd
  rw [V.departureLanding_eq_maximalEndpoint hr hbdd']
  exact (V.ofDeparture η hr.1 hr.2).segment.maximalEndpoint_hamiltonian_eq_initial hbdd'

/-! ### The arrival covector of a departure flight -/

/-- The covector read off the landing point of a departure flight is the maximal arrival covector
of that flight. -/
theorem edgeCovector_departureLanding {η : Γ.EdgeEnd} {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)
      = (V.ofDeparture η hr.1 hr.2).segment.maximalArrivalCovector hbdd
          (V.ofDeparture η hr.1 hr.2).regular := by
  have hbdd' : BddAbove (durationSet V (V.ofDeparture η hr.1 hr.2).edge
      (V.ofDeparture η hr.1 hr.2).state) := hbdd
  rw [V.departureLanding_eq_maximalEndpoint hr hbdd']
  exact V.edgeCovector_eq_maximalArrivalCovector (V.ofDeparture η hr.1 hr.2).segment hbdd'
    (V.ofDeparture η hr.1 hr.2).regular

/-- The landing covector of a departure flight is genuinely incoming at its vertex. -/
theorem edgeCovector_departureLanding_incoming {η : Γ.EdgeEnd} {r : ℝ}
    (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    FiniteMetricGraph.EdgeEnd.sign Γ (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)).germ *
      (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)).momentum > 0 := by
  have hbdd' : BddAbove (durationSet V (V.ofDeparture η hr.1 hr.2).edge
      (V.ofDeparture η hr.1 hr.2).state) := hbdd
  rw [V.edgeCovector_departureLanding hr hbdd]
  exact ((V.ofDeparture η hr.1 hr.2).segment.maximalArrivalIncoming hbdd'
    (V.ofDeparture η hr.1 hr.2).regular).2.2

/-- The momentum of the landing covector is the landing momentum. -/
theorem edgeCovector_departureLanding_momentum {η : Γ.EdgeEnd} {r : ℝ}
    (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)).momentum
      = (V.departureLanding η r).2 := by
  rw [edgeCovector_momentum, if_neg (V.departureLanding_momentum_ne_zero hr hbdd)]

/-- The coordinate of the landing germ is the landing position. -/
theorem edgeCovector_departureLanding_coordinate {η : Γ.EdgeEnd} {r : ℝ}
    (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    FiniteMetricGraph.EdgeEnd.coordinate Γ
        (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)).germ
      = (V.departureLanding η r).1 := by
  have hbdd' : BddAbove (durationSet V (V.ofDeparture η hr.1 hr.2).edge
      (V.ofDeparture η hr.1 hr.2).state) := hbdd
  rw [V.edgeCovector_departureLanding hr hbdd,
    (V.ofDeparture η hr.1 hr.2).segment.maximalArrivalCovector_coordinate hbdd'
      (V.ofDeparture η hr.1 hr.2).regular,
    V.departureLanding_eq_maximalEndpoint hr hbdd']

/-! ### The retrace step -/

/-- The **retrace step**: the germ and inward speed with which the momentum reversal of the landing
point of the departure flight from `(η, r)` departs the graph again.  This is the impact step
*before* scattering, so it does not involve the vertex law. -/
noncomputable def retraceStep (η : Γ.EdgeEnd) (r : ℝ) : Γ.EdgeEnd × ℝ :=
  ((edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)).germ,
    |(edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)).momentum|)

theorem retraceStep_fst (η : Γ.EdgeEnd) (r : ℝ) :
    (V.retraceStep η r).1 = (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)).germ := rfl

theorem retraceStep_snd (η : Γ.EdgeEnd) (r : ℝ) :
    (V.retraceStep η r).2 = |(edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)).momentum| := rfl

/-- The retrace step stays on the edge of the flight. -/
@[simp] theorem retraceStep_fst_edge (η : Γ.EdgeEnd) (r : ℝ) : (V.retraceStep η r).1.1 = η.1 := rfl

/-- The retrace speed is positive. -/
theorem retraceStep_pos (η : Γ.EdgeEnd) (r : ℝ) : 0 < (V.retraceStep η r).2 :=
  abs_pos.mpr (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)).momentum_ne_zero

/-- The departure point of the retrace step is the momentum reversal of the landing point. -/
theorem departurePoint_retraceStep {η : Γ.EdgeEnd} {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    departurePoint (V.retraceStep η r).1 (V.retraceStep η r).2
      = ((V.departureLanding η r).1, -(V.departureLanding η r).2) := by
  set α := edgeCovector (Γ := Γ) η.1 (V.departureLanding η r) with hα
  have hin : FiniteMetricGraph.EdgeEnd.sign Γ α.germ * α.momentum > 0 :=
    V.edgeCovector_departureLanding_incoming hr hbdd
  have hmom : α.momentum = (V.departureLanding η r).2 :=
    V.edgeCovector_departureLanding_momentum hr hbdd
  have hcoord : FiniteMetricGraph.EdgeEnd.coordinate Γ α.germ = (V.departureLanding η r).1 :=
    V.edgeCovector_departureLanding_coordinate hr hbdd
  refine Prod.ext hcoord ?_
  show -(FiniteMetricGraph.EdgeEnd.sign Γ α.germ * |α.momentum|) = -(V.departureLanding η r).2
  rw [← hmom]
  have habs : |FiniteMetricGraph.EdgeEnd.sign Γ α.germ| = 1 := abs_edgeEnd_sign α.germ
  have hs : FiniteMetricGraph.EdgeEnd.sign Γ α.germ *
      FiniteMetricGraph.EdgeEnd.sign Γ α.germ = 1 := edgeEnd_sign_mul_self α.germ
  have h1 : FiniteMetricGraph.EdgeEnd.sign Γ α.germ * α.momentum = |α.momentum| := by
    have h2 : |FiniteMetricGraph.EdgeEnd.sign Γ α.germ * α.momentum| = |α.momentum| := by
      rw [abs_mul, habs, one_mul]
    rw [← h2, abs_of_pos hin]
  have h3 : FiniteMetricGraph.EdgeEnd.sign Γ α.germ * |α.momentum| = α.momentum := by
    rw [← h1, ← mul_assoc, hs, one_mul]
  rw [h3]

/-- The retrace step carries the energy of the flight it retraces. -/
theorem departureEnergy_retraceStep {η : Γ.EdgeEnd} {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    V.departureEnergy (V.retraceStep η r).1 (V.retraceStep η r).2 = V.departureEnergy η r := by
  have hgoal : V.departureEnergy (V.retraceStep η r).1 (V.retraceStep η r).2
      = V.hamiltonian η.1 (departurePoint (V.retraceStep η r).1 (V.retraceStep η r).2).1
          (departurePoint (V.retraceStep η r).1 (V.retraceStep η r).2).2 := rfl
  rw [hgoal, V.departurePoint_retraceStep hr hbdd]
  show V.hamiltonian η.1 (V.departureLanding η r).1 (-(V.departureLanding η r).2) = _
  rw [V.hamiltonian_neg_momentum, V.hamiltonian_departureLanding hr hbdd]

/-- The retrace step is again a regular departure speed. -/
theorem retraceStep_mem_regularSpeeds {η : Γ.EdgeEnd} {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    (V.retraceStep η r).2 ∈ V.regularSpeeds (V.retraceStep η r).1 :=
  ⟨V.retraceStep_pos η r, by rw [V.departureEnergy_retraceStep hr hbdd]; exact hr.2⟩

/-- **The retrace lands at the reversed departure point.**  The flight from the reversed landing
point of the departure flight from `(η, r)` lasts exactly as long as that flight and lands at the
momentum reversal of `departurePoint η r`. -/
theorem retraceStep_exact {η : Γ.EdgeEnd} {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    BddAbove (durationSet V (V.retraceStep η r).1.1
        (departurePoint (V.retraceStep η r).1 (V.retraceStep η r).2)) ∧
      sSup (durationSet V (V.retraceStep η r).1.1
          (departurePoint (V.retraceStep η r).1 (V.retraceStep η r).2))
        = sSup (durationSet V η.1 (departurePoint η r)) ∧
      V.departureLanding (V.retraceStep η r).1 (V.retraceStep η r).2
        = ((departurePoint η r).1, -(departurePoint η r).2) := by
  have hq := V.retraceStep_mem_regularSpeeds hr hbdd
  set b : V.FlightState := V.ofDeparture η hr.1 hr.2 with hb
  set c : V.FlightState := V.ofDeparture (V.retraceStep η r).1 hq.1 hq.2 with hc
  have hbbdd : BddAbove (durationSet V b.edge b.state) := hbdd
  have hce : c.edge = b.edge := by rw [hb, hc]; rfl
  have hcs : c.state = ((b.segment.maximalEndpoint hbbdd).1,
      -(b.segment.maximalEndpoint hbbdd).2) := by
    rw [hc, V.ofDeparture_state, V.departurePoint_retraceStep hr hbdd,
      V.departureLanding_eq_maximalEndpoint hr hbbdd]
  have hout : b.IsOutgoing := V.isOutgoing_ofDeparture η hr.1 hr.2
  obtain ⟨hcbdd, hsup, hend⟩ :=
    FlightState.reversedEndpoint_exact_of_isOutgoing b c hbbdd hce hcs hout
  refine ⟨hcbdd, hsup, ?_⟩
  rw [V.departureLanding_eq_maximalEndpoint hq hcbdd, hend, hb]
  rfl

/-- **The retrace step is an involution.**  Retracing twice returns to the original germ and
speed. -/
theorem retraceStep_involutive {η : Γ.EdgeEnd} {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    V.retraceStep (V.retraceStep η r).1 (V.retraceStep η r).2 = (η, r) := by
  obtain ⟨-, -, hland⟩ := V.retraceStep_exact hr hbdd
  have hcov : edgeCovector (Γ := Γ) (V.retraceStep η r).1.1
      (V.departureLanding (V.retraceStep η r).1 (V.retraceStep η r).2)
      = ⟨η, FiniteMetricGraph.EdgeEnd.sign Γ η * r, by
          have hr0 : 0 < r := hr.1
          have habs : |FiniteMetricGraph.EdgeEnd.sign Γ η| = 1 := abs_edgeEnd_sign η
          intro h0
          have : |FiniteMetricGraph.EdgeEnd.sign Γ η * r| = 0 := by rw [h0, abs_zero]
          rw [abs_mul, habs, one_mul, abs_of_pos hr0] at this
          exact absurd this hr0.ne'⟩ := by
    refine FiniteMetricGraph.BoundaryCovector.ext Γ ?_ ?_
    · show ((V.retraceStep η r).1.1,
        if (V.departureLanding (V.retraceStep η r).1 (V.retraceStep η r).2).1
          = Γ.length (V.retraceStep η r).1.1 then true else false) = η
      rw [hland, V.retraceStep_fst_edge]
      show (η.1, if (departurePoint η r).1 = Γ.length η.1 then true else false) = η
      exact Prod.ext rfl (Γ.edgeEnd_bool_of_coordinate η)
    · show (if (V.departureLanding (V.retraceStep η r).1 (V.retraceStep η r).2).2 = 0 then (1 : ℝ)
        else (V.departureLanding (V.retraceStep η r).1 (V.retraceStep η r).2).2)
        = FiniteMetricGraph.EdgeEnd.sign Γ η * r
      rw [hland]
      show (if -(departurePoint η r).2 = 0 then (1 : ℝ) else -(departurePoint η r).2)
        = FiniteMetricGraph.EdgeEnd.sign Γ η * r
      have hval : -(departurePoint η r).2 = FiniteMetricGraph.EdgeEnd.sign Γ η * r := by
        show -(-(FiniteMetricGraph.EdgeEnd.sign Γ η * r)) = _
        ring
      rw [hval, if_neg]
      have hr0 : 0 < r := hr.1
      have habs : |FiniteMetricGraph.EdgeEnd.sign Γ η| = 1 := abs_edgeEnd_sign η
      intro h0
      have h1 : |FiniteMetricGraph.EdgeEnd.sign Γ η * r| = 0 := by rw [h0, abs_zero]
      rw [abs_mul, habs, one_mul, abs_of_pos hr0] at h1
      exact absurd h1 hr0.ne'
  have hfst : (V.retraceStep (V.retraceStep η r).1 (V.retraceStep η r).2).1 = η := by
    rw [retraceStep_fst, hcov]
  have hsnd : (V.retraceStep (V.retraceStep η r).1 (V.retraceStep η r).2).2 = r := by
    rw [retraceStep_snd, hcov]
    show |FiniteMetricGraph.EdgeEnd.sign Γ η * r| = r
    rw [abs_mul, abs_edgeEnd_sign, one_mul, abs_of_pos hr.1]
  exact Prod.ext hfst hsnd

/-! ### The impact step factors through the retrace step -/

section Step

variable (S : BorelEnergyPreservingScattering V)

/-- The impact step keeps the speed of the retrace step: scattering preserves the boundary speed. -/
theorem departureStep_snd_eq {η : Γ.EdgeEnd} {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    (departureStep V S η r).2 = (V.retraceStep η r).2 := by
  have hin : FiniteMetricGraph.EdgeEnd.sign Γ
      (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)).germ *
      (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)).momentum > 0 :=
    V.edgeCovector_departureLanding_incoming hr hbdd
  show |(scatterCovector (V := V) S
    (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r))).momentum| = _
  rw [scatterCovector_incoming (V := V) S hin, S.scattered_speed_eq]
  rfl

/-- The impact step carries the energy of the flight. -/
theorem departureEnergy_departureStep {η : Γ.EdgeEnd} {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    V.departureEnergy (departureStep V S η r).1 (departureStep V S η r).2
      = V.departureEnergy η r := by
  have hbdd' : BddAbove (durationSet V (V.ofDeparture η hr.1 hr.2).edge
      (V.ofDeparture η hr.1 hr.2).state) := hbdd
  obtain ⟨b, hb, -, hbenergy, -, -⟩ :=
    FlightState.next_eq_some_of_bddAbove (V := V) S (V.ofDeparture η hr.1 hr.2) hbdd'
  obtain ⟨he, hs⟩ := V.departureStep_next S η hr hbdd hb
  have heq : V.departureEnergy (departureStep V S η r).1 (departureStep V S η r).2 = b.energy := by
    rw [FlightState.energy_eq, he, hs]
    rfl
  rw [heq, hbenergy, V.ofDeparture_energy]

/-- **Scattering is injective on incoming covectors at a common vertex.** -/
theorem incoming_val_eq_of_scatter_eq {v w : Γ.Vertex} (γ : Γ.IncomingBoundary v)
    (δ : Γ.IncomingBoundary w) (hvw : v = w)
    (h : (S.map v γ).1 = (S.map w δ).1) : γ.1 = δ.1 := by
  subst hvw
  have hmap : S.map v γ = S.map v δ := Subtype.ext h
  exact congrArg (fun x : Γ.IncomingBoundary v => x.1) ((S.map v).injective hmap)

/-- Two outgoing covectors with the same germ and the same speed are equal. -/
theorem outgoing_covector_eq {γ δ : Γ.BoundaryCovector}
    (hγ : FiniteMetricGraph.EdgeEnd.sign Γ γ.germ * γ.momentum < 0)
    (hδ : FiniteMetricGraph.EdgeEnd.sign Γ δ.germ * δ.momentum < 0)
    (hgerm : γ.germ = δ.germ) (habs : |γ.momentum| = |δ.momentum|) : γ = δ := by
  refine FiniteMetricGraph.BoundaryCovector.ext Γ hgerm ?_
  rcases abs_eq_abs.mp habs with h | h
  · exact h
  · exfalso
    rw [h, hgerm] at hγ
    nlinarith [hγ, hδ]

/-- **The impact step determines the retrace step.**  This is the injectivity of the scattering
factor of the impact step: at a fixed energy all germs at a given vertex carry the same speed, so
the impact step applies one fixed-speed bijection of the incoming boundary section. -/
theorem retraceStep_eq_of_departureStep_eq {η ζ : Γ.EdgeEnd} {r q : ℝ}
    (hr : r ∈ V.regularSpeeds η) (hbdd : BddAbove (durationSet V η.1 (departurePoint η r)))
    (hq : q ∈ V.regularSpeeds ζ) (hbdd' : BddAbove (durationSet V ζ.1 (departurePoint ζ q)))
    (h : departureStep V S η r = departureStep V S ζ q) :
    V.retraceStep η r = V.retraceStep ζ q := by
  set α := edgeCovector (Γ := Γ) η.1 (V.departureLanding η r) with hα
  set β := edgeCovector (Γ := Γ) ζ.1 (V.departureLanding ζ q) with hβ
  have hinα : FiniteMetricGraph.EdgeEnd.sign Γ α.germ * α.momentum > 0 :=
    V.edgeCovector_departureLanding_incoming hr hbdd
  have hinβ : FiniteMetricGraph.EdgeEnd.sign Γ β.germ * β.momentum > 0 :=
    V.edgeCovector_departureLanding_incoming hq hbdd'
  set A := S.map α.germ.vertex ⟨α, rfl, hinα⟩ with hA
  set B := S.map β.germ.vertex ⟨β, rfl, hinβ⟩ with hB
  have hscA : scatterCovector (V := V) S α = A.1 := scatterCovector_incoming (V := V) S hinα
  have hscB : scatterCovector (V := V) S β = B.1 := scatterCovector_incoming (V := V) S hinβ
  -- the two impact steps read off the germ and speed of `A` and `B`
  have hstepα : departureStep V S η r = ((scatterCovector (V := V) S α).germ,
      |(scatterCovector (V := V) S α).momentum|) := rfl
  have hstepβ : departureStep V S ζ q = ((scatterCovector (V := V) S β).germ,
      |(scatterCovector (V := V) S β).momentum|) := rfl
  rw [hstepα, hstepβ, hscA, hscB] at h
  have hgerm : A.1.germ = B.1.germ := congrArg Prod.fst h
  have habs : |A.1.momentum| = |B.1.momentum| := congrArg Prod.snd h
  -- the images are outgoing, so they agree as covectors
  have hAB : A.1 = B.1 := outgoing_covector_eq A.2.2 B.2.2 hgerm habs
  -- the scattering vertices agree
  have hv : α.germ.vertex = β.germ.vertex := by
    rw [← A.2.1, ← B.2.1, hgerm]
  have hαβ : α = β := V.incoming_val_eq_of_scatter_eq S ⟨α, rfl, hinα⟩ ⟨β, rfl, hinβ⟩ hv (by
    rw [← hA, ← hB]; exact hAB)
  unfold retraceStep
  rw [← hα, ← hβ, hαβ]

end Step

/-! ### Shell-regular energies -/

/-- An energy `E` is **shell-regular** when it is not one of the finitely many vertex values and
every flight at energy `E` reaches a vertex in finite time.  The second condition is exactly what
fails at a critical value of the potential in the interior of an edge: there a flight creeps
towards an interior equilibrium and never lands. -/
structure ShellRegular (E : ℝ) : Prop where
  /-- `E` avoids the finitely many vertex values, so no flight at energy `E` stalls at a vertex. -/
  not_exceptional : E ∉ V.exceptionalEnergies
  /-- Every flight at energy `E` lands at a vertex in finite time. -/
  lands : ∀ (e : Γ.Edge) (x : ℝ × ℝ), V.hamiltonian e x.1 x.2 = E → BddAbove (durationSet V e x)

/-- The germs a flight of energy `E` can depart: those whose vertex value is below `E`. -/
def allowedGerms (E : ℝ) : Set Γ.EdgeEnd := {η | V.vertexValue η.vertex < E}

theorem germSpeed_pos_iff {η : Γ.EdgeEnd} {E : ℝ} :
    0 < V.germSpeed η E ↔ η ∈ V.allowedGerms E := by
  rw [V.germSpeed_def, Real.sqrt_pos]
  show 0 < 2 * (E - V.vertexValue η.vertex) ↔ V.vertexValue η.vertex < E
  constructor <;> intro h <;> linarith

theorem departureEnergy_germSpeed {η : Γ.EdgeEnd} {E : ℝ} (h : η ∈ V.allowedGerms E) :
    V.departureEnergy η (V.germSpeed η E) = E := by
  have h' : V.vertexValue η.vertex < E := h
  rw [V.departureEnergy_eq, V.germSpeed_def, Real.sq_sqrt (by linarith)]
  ring

theorem germSpeed_mem_regularSpeeds {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (h : η ∈ V.allowedGerms E) : V.germSpeed η E ∈ V.regularSpeeds η :=
  ⟨V.germSpeed_pos_iff.mpr h, by rw [V.departureEnergy_germSpeed h]; exact hE.not_exceptional⟩

theorem bddAbove_departurePoint_germSpeed {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (h : η ∈ V.allowedGerms E) :
    BddAbove (durationSet V η.1 (departurePoint η (V.germSpeed η E))) :=
  hE.lands η.1 (departurePoint η (V.germSpeed η E)) (V.departureEnergy_germSpeed h)

/-! ### The germ step -/

section Germ

variable (S : BorelEnergyPreservingScattering V)

/-- The **germ step** at energy `E`: where the flight departing `η` at energy `E` departs again
after its impact. -/
noncomputable def germStep (E : ℝ) (η : Γ.EdgeEnd) : Γ.EdgeEnd :=
  (departureStep V S η (V.germSpeed η E)).1

/-- After the impact the germ step still departs at the energy `E`, hence at the speed of its own
germ. -/
theorem germSpeed_germStep {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (h : η ∈ V.allowedGerms E) :
    V.germSpeed (V.germStep S E η) E = (departureStep V S η (V.germSpeed η E)).2 := by
  have hr := V.germSpeed_mem_regularSpeeds hE h
  have hbdd := V.bddAbove_departurePoint_germSpeed hE h
  have hpos : 0 < (departureStep V S η (V.germSpeed η E)).2 :=
    (V.departureStep_mem_regularSpeeds S η hr hbdd).1
  have henergy := V.departureEnergy_departureStep S hr hbdd
  rw [V.departureEnergy_germSpeed h] at henergy
  have hgs : V.germSpeed (departureStep V S η (V.germSpeed η E)).1
      (V.departureEnergy (departureStep V S η (V.germSpeed η E)).1
        (departureStep V S η (V.germSpeed η E)).2)
      = (departureStep V S η (V.germSpeed η E)).2 :=
    V.germSpeed_departureEnergy _ hpos.le
  rw [henergy] at hgs
  show V.germSpeed (departureStep V S η (V.germSpeed η E)).1 E = _
  exact hgs

theorem germStep_mem {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (h : η ∈ V.allowedGerms E) : V.germStep S E η ∈ V.allowedGerms E := by
  rw [← V.germSpeed_pos_iff, V.germSpeed_germStep S hE h]
  have hr := V.germSpeed_mem_regularSpeeds hE h
  have hbdd := V.bddAbove_departurePoint_germSpeed hE h
  exact (V.departureStep_mem_regularSpeeds S η hr hbdd).1

/-- **The germ step is injective on the allowed germs.**  This is the combinatorial heart of the
structure theorem: the impact step is the composition of the retrace involution with a fixed-speed
bijection of the incoming boundary section. -/
theorem germStep_injOn {E : ℝ} (hE : V.ShellRegular E) :
    Set.InjOn (V.germStep S E) (V.allowedGerms E) := by
  intro η hη ζ hζ hstep
  have hrη := V.germSpeed_mem_regularSpeeds hE hη
  have hrζ := V.germSpeed_mem_regularSpeeds hE hζ
  have hbη := V.bddAbove_departurePoint_germSpeed hE hη
  have hbζ := V.bddAbove_departurePoint_germSpeed hE hζ
  -- the impact steps agree as germ-speed pairs
  have hsnd : (departureStep V S η (V.germSpeed η E)).2
      = (departureStep V S ζ (V.germSpeed ζ E)).2 := by
    rw [← V.germSpeed_germStep S hE hη, ← V.germSpeed_germStep S hE hζ, hstep]
  have hpair : departureStep V S η (V.germSpeed η E) = departureStep V S ζ (V.germSpeed ζ E) :=
    Prod.ext hstep hsnd
  -- hence the retrace steps agree, and the retrace involution identifies the germs
  have hret := V.retraceStep_eq_of_departureStep_eq S hrη hbη hrζ hbζ hpair
  have h1 := V.retraceStep_involutive hrη hbη
  have h2 := V.retraceStep_involutive hrζ hbζ
  rw [hret] at h1
  rw [h1] at h2
  exact (Prod.ext_iff.mp h2).1

/-- The germ step as a self-map of the finite set of allowed germs. -/
noncomputable def shellGermMap {E : ℝ} (hE : V.ShellRegular E) :
    V.allowedGerms E → V.allowedGerms E :=
  fun η => ⟨V.germStep S E η, V.germStep_mem S hE η.2⟩

theorem shellGermMap_injective {E : ℝ} (hE : V.ShellRegular E) :
    Function.Injective (V.shellGermMap S hE) := by
  intro η ζ h
  exact Subtype.ext (V.germStep_injOn S hE η.2 ζ.2 (Subtype.ext_iff.mp h))

theorem shellGermMap_bijective {E : ℝ} (hE : V.ShellRegular E) :
    Function.Bijective (V.shellGermMap S hE) :=
  Finite.injective_iff_bijective.mp (V.shellGermMap_injective S hE)

/-- **The germ permutation of the shell.**  At a shell-regular energy the impact dynamics is a
permutation of the finite set of allowed germs; its cycle decomposition is the decomposition of
the shell into periodic orbits. -/
noncomputable def shellGermPerm {E : ℝ} (hE : V.ShellRegular E) :
    Equiv.Perm (V.allowedGerms E) :=
  Equiv.ofBijective (V.shellGermMap S hE) (V.shellGermMap_bijective S hE)

@[simp] theorem shellGermPerm_apply {E : ℝ} (hE : V.ShellRegular E) (η : V.allowedGerms E) :
    ((V.shellGermPerm S hE η : Γ.EdgeEnd)) = V.germStep S E (η : Γ.EdgeEnd) := rfl

theorem shellGermPerm_pow_apply {E : ℝ} (hE : V.ShellRegular E) (η : V.allowedGerms E) :
    ∀ n : ℕ, (((V.shellGermPerm S hE ^ n) η : V.allowedGerms E) : Γ.EdgeEnd)
      = (V.germStep S E)^[n] (η : Γ.EdgeEnd) := by
  intro n
  induction n generalizing η with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Function.iterate_succ_apply]
      exact ih (V.shellGermPerm S hE η)

/-- **Every germ of a shell-regular energy is periodic.** -/
theorem exists_germStep_period {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    ∃ n : ℕ, 0 < n ∧ (V.germStep S E)^[n] η = η := by
  classical
  refine ⟨orderOf (V.shellGermPerm S hE), orderOf_pos _, ?_⟩
  have h := V.shellGermPerm_pow_apply S hE ⟨η, hη⟩ (orderOf (V.shellGermPerm S hE))
  rw [pow_orderOf_eq_one] at h
  exact h.symm

end Germ

/-! ### The orbits of a shell-regular energy are periodic -/

section Period

variable [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)

omit [Nonempty Γ.Edge] in
/-- At a shell-regular energy the germ–speed chain is the iteration of the germ step: the speed is
determined by the germ, so the chain collapses to a map of the finite germ set. -/
theorem chainIterate_germStep {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) : ∀ n : ℕ,
      (V.germStep S E)^[n] η ∈ V.allowedGerms E ∧
        chainIterate V S (η, V.germSpeed η E) n
          = ((V.germStep S E)^[n] η, V.germSpeed ((V.germStep S E)^[n] η) E) := by
  intro n
  induction n with
  | zero => exact ⟨hη, rfl⟩
  | succ k ih =>
      obtain ⟨hmem, hchain⟩ := ih
      refine ⟨by rw [Function.iterate_succ_apply']; exact V.germStep_mem S hE hmem, ?_⟩
      rw [chainIterate_succ, hchain, Function.iterate_succ_apply']
      exact Prod.ext rfl (V.germSpeed_germStep S hE hmem).symm

omit [Nonempty Γ.Edge] in
/-- At a shell-regular energy every flight of the chain lands. -/
theorem chainLands_germSpeed {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (n : ℕ) : ChainLands V S (η, V.germSpeed η E) n := by
  induction n with
  | zero => exact trivial
  | succ k ih =>
      obtain ⟨hmem, hchain⟩ := V.chainIterate_germStep S hE hη k
      refine ⟨ih, ?_⟩
      rw [hchain]
      exact ⟨V.germSpeed_mem_regularSpeeds hE hmem, V.bddAbove_departurePoint_germSpeed hE hmem⟩

omit [Nonempty Γ.Edge] in
/-- The impact times along the chain are strictly increasing. -/
theorem chainTime_lt_succ {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (n : ℕ) :
    chainTime V S (η, V.germSpeed η E) n < chainTime V S (η, V.germSpeed η E) (n + 1) := by
  obtain ⟨hmem, hchain⟩ := V.chainIterate_germStep S hE hη n
  rw [chainTime_succ, hchain]
  have hr := V.germSpeed_mem_regularSpeeds hE hmem
  have hbdd := V.bddAbove_departurePoint_germSpeed hE hmem
  have hpos : 0 < V.departureDurationTotal ((V.germStep S E)^[n] η)
      (V.germSpeed ((V.germStep S E)^[n] η) E) := by
    rw [V.departureDurationTotal_of_mem hr]
    exact FlightState.impactDuration_pos_of_bddAbove (V := V)
      (V.ofDeparture ((V.germStep S E)^[n] η) hr.1 hr.2) hbdd
  linarith

theorem chainTime_pos {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {n : ℕ} (hn : 0 < n) :
    0 < chainTime V S (η, V.germSpeed η E) n := by
  have hmono : StrictMono fun m => chainTime V S (η, V.germSpeed η E) m :=
    strictMono_nat_of_lt_succ (V.chainTime_lt_succ S hE hη)
  have h : chainTime V S (η, V.germSpeed η E) 0 < chainTime V S (η, V.germSpeed η E) n := hmono hn
  rwa [chainTime_zero] at h

/-- **The orbits of a shell-regular energy are periodic.**  The trajectory of the flight departing
an allowed germ returns to its departure point after the finite time accumulated along the germ
cycle of that germ.  Together with `shellGermPerm` this exhibits the shell as a finite disjoint
union of periodic orbits and the flow on it as the suspension of a finite permutation. -/
theorem trajectory_period {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    ∃ T : ℝ, 0 < T ∧
      FlightState.trajectory V S (V.ofDeparture η (V.germSpeed_mem_regularSpeeds hE hη).1
          (V.germSpeed_mem_regularSpeeds hE hη).2) T
        = (η.1, departurePoint η (V.germSpeed η E)) := by
  obtain ⟨n, hn, hperiod⟩ := V.exists_germStep_period S hE hη
  have hr := V.germSpeed_mem_regularSpeeds hE hη
  refine ⟨chainTime V S (η, V.germSpeed η E) n, V.chainTime_pos S hE hη hn, ?_⟩
  have hact : FlightState.ActiveAt V S (V.ofDeparture η hr.1 hr.2) n
      (chainTime V S (η, V.germSpeed η E) n) := by
    rw [V.activeAt_iff_chain S η hr n]
    exact ⟨V.chainLands_germSpeed S hE hη n, le_rfl, fun _ => V.chainTime_lt_succ S hE hη n⟩
  have ht0 : 0 ≤ chainTime V S (η, V.germSpeed η E) n := V.chainTime_nonneg S _ n
  rw [V.trajectory_chain_eq S η hr ht0 hact]
  obtain ⟨-, hchain⟩ := V.chainIterate_germStep S hE hη n
  rw [hchain, hperiod, sub_self]
  have hpre : ((V.germSpeed η E : ℝ), (0 : ℝ)) ∈ V.departurePreImpact η := by
    refine ⟨hr, le_rfl, ?_⟩
    refine V.ofReal_lt_impactTime_of_le (V.durationSet_nonempty_of_regularSpeed hr) le_rfl ?_
    intro hbdd
    exact FlightState.impactDuration_pos_of_bddAbove (V := V) (V.ofDeparture η hr.1 hr.2) hbdd
  rw [V.departureFlow_of_mem hpre]
  refine Prod.ext rfl ?_
  show V.departureFlight η (V.germSpeed η E) 0 = departurePoint η (V.germSpeed η E)
  rw [V.departureFlight_of_mem hr, FlightState.flightCurve_zero]
  rfl

end Period

end MechanicalPotential

end HamiltonianMetricGraphs
