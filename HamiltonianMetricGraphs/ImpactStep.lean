/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.4: the impact step is Borel in germ-speed coordinates
-/

import HamiltonianMetricGraphs.DepartureFlight
import HamiltonianMetricGraphs.ScatterMap

/-!
# The impact step in germ–speed coordinates

After its first impact a flight departs a vertex, and from then on its state is described by a
*germ* together with an *inward speed*: `departurePoint η r`.  This module builds the one-impact
step in those coordinates and proves it Borel:

`(η, r) ↦ (η', r')`,  `η' = ` departure germ after scattering,  `r' = ` inward speed after
scattering,

as the composition of four Borel maps: the departure landing (`measurable_departureLanding`), the
boundary covector of the landing point (`edgeCovector`), the scattering step of Lemma IV.4
(`scatterCovector`), and the germ/speed read-off.

`edgeCovector_eq_maximalArrivalCovector` and `departureStep_next` identify this composite with the
recursive successor `FlightState.next` of the paper's event chain, so the Borel step really is the
step of the trajectory.  These are the maps whose iteration gives the measurability of `Φ_Δ`
(Lemma VI.4).
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory PhysicalEdgeSegment
open scoped Topology ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The boundary covector of a landing point -/

/-- The boundary covector read off a landing point of the edge `e`: its germ is `e` with the
boundary flag `position = length e`, and its momentum is the landing momentum (junk-guarded by `1`
at zero momentum, where it is never used). -/
noncomputable def edgeCovector (e : Γ.Edge) (y : ℝ × ℝ) : Γ.BoundaryCovector := by
  classical
  exact ⟨(e, if y.1 = Γ.length e then true else false), if y.2 = 0 then 1 else y.2, by
    split_ifs with h
    · exact one_ne_zero
    · exact h⟩

theorem edgeCovector_germ (e : Γ.Edge) (y : ℝ × ℝ) :
    (edgeCovector (Γ := Γ) e y).germ = (e, if y.1 = Γ.length e then true else false) := rfl

theorem edgeCovector_momentum (e : Γ.Edge) (y : ℝ × ℝ) :
    (edgeCovector (Γ := Γ) e y).momentum = if y.2 = 0 then 1 else y.2 := rfl

theorem measurable_edgeCovector (e : Γ.Edge) : Measurable (edgeCovector (Γ := Γ) e) := by
  classical
  have hbset : MeasurableSet {y : ℝ × ℝ | y.1 = Γ.length e} := by
    have heq : {y : ℝ × ℝ | y.1 = Γ.length e} = (fun y : ℝ × ℝ => y.1) ⁻¹' {Γ.length e} := rfl
    rw [heq]
    exact measurable_fst (measurableSet_singleton _)
  have hbool : Measurable (fun y : ℝ × ℝ => if y.1 = Γ.length e then true else false) :=
    Measurable.ite hbset measurable_const measurable_const
  have hgerm : Measurable (fun y : ℝ × ℝ =>
      ((e, if y.1 = Γ.length e then true else false) : Γ.EdgeEnd)) := by
    apply measurable_to_countable'
    intro η
    have hpre : (fun y : ℝ × ℝ =>
        ((e, if y.1 = Γ.length e then true else false) : Γ.EdgeEnd)) ⁻¹' {η} =
        (fun _ : ℝ × ℝ => e) ⁻¹' {η.1} ∩
        (fun y : ℝ × ℝ => if y.1 = Γ.length e then true else false) ⁻¹' {η.2} := by
      ext y
      rcases η with ⟨e', b⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Prod.ext_iff]
    rw [hpre]
    exact (measurable_const (measurableSet_singleton η.1)).inter
      (hbool (measurableSet_singleton η.2))
  have hmom : Measurable (fun y : ℝ × ℝ => if y.2 = 0 then (1 : ℝ) else y.2) :=
    Measurable.ite (measurable_snd (measurableSet_singleton 0)) measurable_const measurable_snd
  have hpair : Measurable (fun y : ℝ × ℝ =>
      (((e, if y.1 = Γ.length e then true else false) : Γ.EdgeEnd),
        if y.2 = 0 then (1 : ℝ) else y.2)) := hgerm.prodMk hmom
  intro B hB
  obtain ⟨C, hC, rfl⟩ := hB
  exact hpair hC

/-- **The covector of a landing point is the arrival covector of the flight.**  This identifies the
Borel read-off `edgeCovector` with the covector `maximalArrivalCovector` selected by the flight
machinery: both have the germ of the endpoint the flight lands at and the landing momentum. -/
theorem edgeCovector_eq_maximalArrivalCovector {e : Γ.Edge} {x : ℝ × ℝ}
    (h : V.PhysicalEdgeSegment e x) (hbdd : BddAbove (durationSet V e x))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    edgeCovector (Γ := Γ) e (h.maximalEndpoint hbdd) =
      h.maximalArrivalCovector hbdd hregular := by
  classical
  apply FiniteMetricGraph.BoundaryCovector.ext
  · rw [edgeCovector_germ]
    by_cases hleft : (h.maximalEndpoint hbdd).1 = 0
    · rw [show (h.maximalArrivalCovector hbdd hregular).germ = (e, false) from by
        simp [PhysicalEdgeSegment.maximalArrivalCovector, hleft],
        if_neg (by rw [hleft]; exact (Γ.length_pos e).ne)]
    · have hl : (h.maximalEndpoint hbdd).1 = Γ.length e :=
        (h.maximalEndpoint_coordinate_eq_zero_or_length hbdd).resolve_left hleft
      rw [show (h.maximalArrivalCovector hbdd hregular).germ = (e, true) from by
        simp [PhysicalEdgeSegment.maximalArrivalCovector, hleft], if_pos hl]
  · rw [edgeCovector_momentum, PhysicalEdgeSegment.maximalArrivalCovector_momentum,
      if_neg (h.maximalEndpoint_momentum_ne_zero hbdd hregular)]

/-! ### The point of a boundary covector -/

/-- The edge and phase point at which a boundary covector sits. -/
def covectorPoint (β : Γ.BoundaryCovector) : Γ.Edge × ℝ × ℝ :=
  (β.germ.1, (FiniteMetricGraph.EdgeEnd.coordinate Γ β.germ, β.momentum))

theorem measurable_covectorPoint : Measurable (covectorPoint (Γ := Γ)) := by
  have hdata : Measurable (fun β : Γ.BoundaryCovector => (β.germ, β.momentum)) :=
    (Γ.measurable_boundary_germ).prodMk (Γ.measurable_boundary_momentum)
  have hinner : Measurable (fun p : Γ.EdgeEnd × ℝ =>
      ((p.1.1, (FiniteMetricGraph.EdgeEnd.coordinate Γ p.1, p.2)) : Γ.Edge × ℝ × ℝ)) := by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ measurable_snd)
    · exact (measurable_from_top (f := fun η : Γ.EdgeEnd => η.1)).comp measurable_fst
    · exact (measurable_from_top
        (f := fun η : Γ.EdgeEnd => FiniteMetricGraph.EdgeEnd.coordinate Γ η)).comp measurable_fst
  exact hinner.comp hdata

/-- A boundary covector that is outgoing at its vertex sits at the departure point of its germ with
the inward speed `|momentum|`. -/
theorem covectorPoint_eq_departurePoint {β : Γ.BoundaryCovector}
    (hout : FiniteMetricGraph.EdgeEnd.sign Γ β.germ * β.momentum < 0) :
    (covectorPoint (Γ := Γ) β).2 = departurePoint β.germ |β.momentum| := by
  rw [covectorPoint, departurePoint]
  refine Prod.ext rfl ?_
  have hs : FiniteMetricGraph.EdgeEnd.sign Γ β.germ *
      FiniteMetricGraph.EdgeEnd.sign Γ β.germ = 1 := edgeEnd_sign_mul_self β.germ
  have habs : |FiniteMetricGraph.EdgeEnd.sign Γ β.germ| = 1 := abs_edgeEnd_sign β.germ
  have h1 : FiniteMetricGraph.EdgeEnd.sign Γ β.germ * β.momentum = -|β.momentum| := by
    have h2 : |FiniteMetricGraph.EdgeEnd.sign Γ β.germ * β.momentum| = |β.momentum| := by
      rw [abs_mul, habs, one_mul]
    rw [← h2, abs_of_neg hout]
    ring
  have h3 : FiniteMetricGraph.EdgeEnd.sign Γ β.germ *
      (FiniteMetricGraph.EdgeEnd.sign Γ β.germ * β.momentum) =
      FiniteMetricGraph.EdgeEnd.sign Γ β.germ * (-|β.momentum|) := by rw [h1]
  calc β.momentum
      = (FiniteMetricGraph.EdgeEnd.sign Γ β.germ *
          FiniteMetricGraph.EdgeEnd.sign Γ β.germ) * β.momentum := by rw [hs, one_mul]
    _ = FiniteMetricGraph.EdgeEnd.sign Γ β.germ *
          (FiniteMetricGraph.EdgeEnd.sign Γ β.germ * β.momentum) := by ring
    _ = FiniteMetricGraph.EdgeEnd.sign Γ β.germ * (-|β.momentum|) := h3
    _ = -(FiniteMetricGraph.EdgeEnd.sign Γ β.germ * |β.momentum|) := by ring

/-! ### The impact step -/

variable (S : BorelEnergyPreservingScattering V)

/-- The **impact step in germ–speed coordinates**: the germ and inward speed with which the flight
leaving `η` at inward speed `r` departs again after its impact. -/
noncomputable def departureStep (η : Γ.EdgeEnd) (r : ℝ) : Γ.EdgeEnd × ℝ :=
  ((scatterCovector (V := V) S (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r))).germ,
    |(scatterCovector (V := V) S (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r))).momentum|)

section Step

variable [Nonempty Γ.Edge]

/-- **The impact step is Borel.**  It is the composition of the Borel departure landing map, the
Borel covector read-off, the Borel scattering step of Lemma IV.4, and the germ/speed projections. -/
theorem measurable_departureStep (η : Γ.EdgeEnd) (Δ : ℝ) :
    Measurable fun s : V.departureImpactSet η Δ => departureStep V S η (s : ℝ) := by
  have hland : Measurable fun s : V.departureImpactSet η Δ => V.departureLanding η (s : ℝ) :=
    V.measurable_departureLanding η Δ
  have hcov : Measurable fun s : V.departureImpactSet η Δ =>
      scatterCovector (V := V) S (edgeCovector (Γ := Γ) η.1 (V.departureLanding η (s : ℝ))) :=
    (measurable_scatterCovector (V := V) S).comp
      ((measurable_edgeCovector (Γ := Γ) η.1).comp hland)
  exact ((Γ.measurable_boundary_germ).comp hcov).prodMk
    (((Γ.measurable_boundary_momentum).comp hcov).abs)

omit [Nonempty Γ.Edge] in
/-- **The impact step is the recursive successor.**  If the flight leaving `η` at inward speed `r`
has a successor `b` in the paper's event chain, then `b` departs the germ and speed produced by
`departureStep`. -/
theorem departureStep_next (η : Γ.EdgeEnd) {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r)))
    {b : V.FlightState}
    (hb : FlightState.next (V := V) S (V.ofDeparture η hr.1 hr.2) = some b) :
    b.edge = (departureStep V S η r).1.1 ∧
      b.state = departurePoint (departureStep V S η r).1 (departureStep V S η r).2 := by
  classical
  set a : V.FlightState := V.ofDeparture η hr.1 hr.2 with hadef
  have hbdd' : BddAbove (durationSet V a.edge a.state) := hbdd
  obtain ⟨c, hc, hcstate, -, -, hcedge⟩ :=
    FlightState.next_eq_some_of_bddAbove (V := V) S a hbdd'
  obtain rfl : c = b := Option.some_injective _ (hc.symm.trans hb)
  -- the arrival covector is the covector of the landing point
  have hland : V.departureLanding η r = a.segment.maximalEndpoint hbdd' := by
    rw [departureLanding, V.departureFlight_of_mem hr]
    exact FlightState.flightCurve_sSup a hbdd'
  have hcoveq : edgeCovector (Γ := Γ) η.1 (V.departureLanding η r) =
      a.segment.maximalArrivalCovector hbdd' a.regular := by
    rw [hland]
    exact V.edgeCovector_eq_maximalArrivalCovector a.segment hbdd' a.regular
  -- the scattering step of `next` is the global Borel scattering map
  have hincoming : FiniteMetricGraph.EdgeEnd.sign Γ
      (a.segment.maximalArrivalCovector hbdd' a.regular).germ *
      (a.segment.maximalArrivalCovector hbdd' a.regular).momentum > 0 :=
    (a.segment.maximalArrivalIncoming hbdd' a.regular).2.2
  have hscat : scatterCovector (V := V) S (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r))
      = (S.map (a.segment.maximalArrivalCovector hbdd' a.regular).germ.vertex
          (a.segment.maximalArrivalIncoming hbdd' a.regular)).1 := by
    rw [hcoveq, scatterCovector_incoming (V := V) S hincoming]
    rfl
  have hstepgerm : (departureStep V S η r).1 =
      (S.map (a.segment.maximalArrivalCovector hbdd' a.regular).germ.vertex
        (a.segment.maximalArrivalIncoming hbdd' a.regular)).1.germ := by
    rw [departureStep, hscat]
  have hstepspeed : (departureStep V S η r).2 =
      |(S.map (a.segment.maximalArrivalCovector hbdd' a.regular).germ.vertex
        (a.segment.maximalArrivalIncoming hbdd' a.regular)).1.momentum| := by
    rw [departureStep, hscat]
  have hout : FiniteMetricGraph.EdgeEnd.sign Γ
      (S.map (a.segment.maximalArrivalCovector hbdd' a.regular).germ.vertex
        (a.segment.maximalArrivalIncoming hbdd' a.regular)).1.germ *
      (S.map (a.segment.maximalArrivalCovector hbdd' a.regular).germ.vertex
        (a.segment.maximalArrivalIncoming hbdd' a.regular)).1.momentum < 0 :=
    (S.map (a.segment.maximalArrivalCovector hbdd' a.regular).germ.vertex
      (a.segment.maximalArrivalIncoming hbdd' a.regular)).2.2
  refine ⟨?_, ?_⟩
  · rw [hcedge, hstepgerm]
    rfl
  · rw [hcstate, hstepgerm, hstepspeed]
    have h := covectorPoint_eq_departurePoint (Γ := Γ) hout
    rw [covectorPoint] at h
    exact h

end Step


/-! ### The first impact step, from an interior state -/

/-- The **first impact step**: the germ and inward speed with which the flight from the interior
regular state `x` of the edge `e` departs again after its impact.  This is the entry point of the
chain; from then on `departureStep` applies. -/
noncomputable def interiorStep (e : Γ.Edge) (x : ℝ × ℝ) : Γ.EdgeEnd × ℝ :=
  ((scatterCovector (V := V) S (edgeCovector (Γ := Γ) e (V.landingState e x))).germ,
    |(scatterCovector (V := V) S (edgeCovector (Γ := Γ) e (V.landingState e x))).momentum|)

/-- **The first impact step is Borel.** -/
theorem measurable_interiorStep (e : Γ.Edge) (Δ : ℝ) :
    Measurable fun y : V.impactSetAt e Δ => interiorStep V S e (y : ℝ × ℝ) := by
  have hland : Measurable fun y : V.impactSetAt e Δ => V.landingState e (y : ℝ × ℝ) :=
    V.measurable_landingState e Δ
  have hcov : Measurable fun y : V.impactSetAt e Δ =>
      scatterCovector (V := V) S (edgeCovector (Γ := Γ) e (V.landingState e (y : ℝ × ℝ))) :=
    (measurable_scatterCovector (V := V) S).comp
      ((measurable_edgeCovector (Γ := Γ) e).comp hland)
  exact ((Γ.measurable_boundary_germ).comp hcov).prodMk
    (((Γ.measurable_boundary_momentum).comp hcov).abs)

/-- **The first impact step is the recursive successor.** -/
theorem interiorStep_next {e : Γ.Edge} {x : ℝ × ℝ} (hx : x ∈ V.interiorRegular e)
    (hbdd : BddAbove (durationSet V e x)) {b : V.FlightState}
    (hb : FlightState.next (V := V) S (FlightState.ofInterior V hx.1 hx.2) = some b) :
    b.edge = (interiorStep V S e x).1.1 ∧
      b.state = departurePoint (interiorStep V S e x).1 (interiorStep V S e x).2 := by
  classical
  set a : V.FlightState := FlightState.ofInterior V hx.1 hx.2 with hadef
  have hbdd' : BddAbove (durationSet V a.edge a.state) := hbdd
  obtain ⟨c, hc, hcstate, -, -, hcedge⟩ :=
    FlightState.next_eq_some_of_bddAbove (V := V) S a hbdd'
  obtain rfl : c = b := Option.some_injective _ (hc.symm.trans hb)
  have hland : V.landingState e x = a.segment.maximalEndpoint hbdd' := by
    rw [landingState, V.edgeFlight_of_mem hx]
    exact FlightState.flightCurve_sSup a hbdd'
  have hcoveq : edgeCovector (Γ := Γ) e (V.landingState e x) =
      a.segment.maximalArrivalCovector hbdd' a.regular := by
    rw [hland]
    exact V.edgeCovector_eq_maximalArrivalCovector a.segment hbdd' a.regular
  have hincoming : FiniteMetricGraph.EdgeEnd.sign Γ
      (a.segment.maximalArrivalCovector hbdd' a.regular).germ *
      (a.segment.maximalArrivalCovector hbdd' a.regular).momentum > 0 :=
    (a.segment.maximalArrivalIncoming hbdd' a.regular).2.2
  have hscat : scatterCovector (V := V) S (edgeCovector (Γ := Γ) e (V.landingState e x))
      = (S.map (a.segment.maximalArrivalCovector hbdd' a.regular).germ.vertex
          (a.segment.maximalArrivalIncoming hbdd' a.regular)).1 := by
    rw [hcoveq, scatterCovector_incoming (V := V) S hincoming]
    rfl
  have hstepgerm : (interiorStep V S e x).1 =
      (S.map (a.segment.maximalArrivalCovector hbdd' a.regular).germ.vertex
        (a.segment.maximalArrivalIncoming hbdd' a.regular)).1.germ := by
    rw [interiorStep, hscat]
  have hstepspeed : (interiorStep V S e x).2 =
      |(S.map (a.segment.maximalArrivalCovector hbdd' a.regular).germ.vertex
        (a.segment.maximalArrivalIncoming hbdd' a.regular)).1.momentum| := by
    rw [interiorStep, hscat]
  have hout : FiniteMetricGraph.EdgeEnd.sign Γ
      (S.map (a.segment.maximalArrivalCovector hbdd' a.regular).germ.vertex
        (a.segment.maximalArrivalIncoming hbdd' a.regular)).1.germ *
      (S.map (a.segment.maximalArrivalCovector hbdd' a.regular).germ.vertex
        (a.segment.maximalArrivalIncoming hbdd' a.regular)).1.momentum < 0 :=
    (S.map (a.segment.maximalArrivalCovector hbdd' a.regular).germ.vertex
      (a.segment.maximalArrivalIncoming hbdd' a.regular)).2.2
  refine ⟨?_, ?_⟩
  · rw [hcedge, hstepgerm]
    rfl
  · rw [hcstate, hstepgerm, hstepspeed]
    have h := covectorPoint_eq_departurePoint (Γ := Γ) hout
    rw [covectorPoint] at h
    exact h

end MechanicalPotential

end HamiltonianMetricGraphs
