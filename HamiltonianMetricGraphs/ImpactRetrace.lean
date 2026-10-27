/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3: the one-impact stratum is a reversed departure flight
-/

import HamiltonianMetricGraphs.ImpactSlice

/-!
# The one-impact stratum is a reversed departure flight

The two dynamical facts about the stratum `impactSlice η η' A s` of `ImpactSlice.lean` that make
the tube charts of `GermTube.lean` applicable on both sides of an impact.

* `departureFlight_impactSlice`: a state of the stratum is the *momentum reversal* of the state
  reached by the departure flight of `(η, r)` after the time that separates it from its impact.
  The flight of the state lands at the reversed departure point of `(η, r)`, so the backward
  retrace of `FlightRetrace.lean` identifies the two — the incoming tube of a germ is the momentum
  reflection of its outgoing tube.
* `pointTrajectory_impactSlice`: past its impact the trajectory of such a state is the departure
  flight of the scattered datum `(η', r)`, run for the time elapsed since the impact.  This is
  step one of the chain of `ImpactStep.lean`, with the flow box supplying the estimate that the
  next impact has not yet happened.

Scattering preserves the boundary speed (`scattered_speed_eq`), so the *same* speed `r` appears on
both sides — which is why one speed set `A` serves for both germs.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set MeasureTheory PhysicalEdgeSegment
open FiniteMetricGraph.EdgeEnd (coordinate vertex)

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-! ### The landing point of a one-impact state -/

/-- **The landing point of a one-impact state.**  The flight of a state of `impactSlice η η' A s`
lands at the coordinate of `η` with inward momentum of size the speed read off after the impact:
scattering preserves the boundary speed, so that speed is also the arrival speed. -/
theorem landingState_impactSlice {η η' : Γ.EdgeEnd} {A : Set ℝ} {s : ℝ}
    {x : ℝ × ℝ} (hx : x ∈ V.impactSlice S η η' A s) :
    V.landingState η.1 x =
      (coordinate Γ η, FiniteMetricGraph.EdgeEnd.sign Γ η * (interiorStep V S η.1 x).2) := by
  classical
  obtain ⟨⟨hxreg, hbdd⟩, -, hgerm, -, -⟩ := hx
  set a : V.FlightState := FlightState.ofInterior V hxreg.1 hxreg.2 with hadef
  have hbdd' : BddAbove (durationSet V a.edge a.state) := hbdd
  have hland : V.landingState η.1 x = a.segment.maximalEndpoint hbdd' := by
    rw [landingState, V.edgeFlight_of_mem hxreg]
    exact FlightState.flightCurve_sSup a hbdd'
  have hcoveq : edgeCovector (Γ := Γ) η.1 (V.landingState η.1 x)
      = a.segment.maximalArrivalCovector hbdd' a.regular := by
    rw [hland]
    exact V.edgeCovector_eq_maximalArrivalCovector a.segment hbdd' a.regular
  have hgermη : (a.segment.maximalArrivalCovector hbdd' a.regular).germ = η := by
    rw [← hcoveq]; exact hgerm
  have hcoord : (a.segment.maximalEndpoint hbdd').1 = coordinate Γ η := by
    have h := a.segment.maximalArrivalCovector_coordinate hbdd' a.regular
    rw [hgermη] at h
    exact h.symm
  have hmomcov : (a.segment.maximalArrivalCovector hbdd' a.regular).momentum
      = (a.segment.maximalEndpoint hbdd').2 :=
    a.segment.maximalArrivalCovector_momentum hbdd' a.regular
  have hinraw := (a.segment.maximalArrivalIncoming hbdd' a.regular).2.2
  have hin : FiniteMetricGraph.EdgeEnd.sign Γ η * (a.segment.maximalEndpoint hbdd').2 > 0 := by
    have h : FiniteMetricGraph.EdgeEnd.sign Γ
        (a.segment.maximalArrivalCovector hbdd' a.regular).germ *
        (a.segment.maximalArrivalCovector hbdd' a.regular).momentum > 0 := hinraw
    rwa [hgermη, hmomcov] at h
  -- the speed read off after the impact is the arrival speed
  have hpos : (edgeCovector (Γ := Γ) η.1 (V.landingState η.1 x)).germ.sign *
      (edgeCovector (Γ := Γ) η.1 (V.landingState η.1 x)).momentum > 0 := by
    rw [hcoveq]; exact hinraw
  have hstep2 : (interiorStep V S η.1 x).2 =
      |(scatterCovector (V := V) S
        (edgeCovector (Γ := Γ) η.1 (V.landingState η.1 x))).momentum| := rfl
  have hspeed : (interiorStep V S η.1 x).2 = |(a.segment.maximalEndpoint hbdd').2| := by
    rw [hstep2, scatterCovector_incoming (V := V) S hpos, S.scattered_speed_eq]
    change |(edgeCovector (Γ := Γ) η.1 (V.landingState η.1 x)).momentum|
      = |(a.segment.maximalEndpoint hbdd').2|
    rw [hcoveq, hmomcov]
  have hmomval : (a.segment.maximalEndpoint hbdd').2 =
      FiniteMetricGraph.EdgeEnd.sign Γ η * (interiorStep V S η.1 x).2 := by
    rw [hspeed]
    by_cases hbo : η.2 = true
    · have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η = 1 := by
        simp [FiniteMetricGraph.EdgeEnd.sign, hbo]
      rw [hsgn] at hin ⊢
      rw [one_mul, abs_of_pos (by linarith [hin])]
    · have hbo' : η.2 = false := by
        cases h : η.2 with
        | false => rfl
        | true => exact absurd h hbo
      have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η = -1 := by
        simp [FiniteMetricGraph.EdgeEnd.sign, hbo']
      rw [hsgn] at hin ⊢
      rw [abs_of_neg (by linarith [hin])]
      ring
  rw [hland]
  exact Prod.ext hcoord hmomval

/-! ### The backward retrace -/

/-- **A one-impact state is a reversed departure flight.**  The flight of a state `x` of
`impactSlice η η' A s` lands at the momentum reversal of the departure point of `(η, r)`, and the
departure flight of `(η, r)` lasts longer than that flight does (the flow box), so the backward
retrace of `FlightRetrace.lean` puts the departure flight at the momentum reversal of `x` exactly
at the impact time of `x`. -/
theorem departureFlight_impactSlice {η η' : Γ.EdgeEnd} {A : Set ℝ} {s r₁ r₂ δ u₀ : ℝ}
    (hbox : V.GermFlowBox η A r₁ r₂ δ u₀) (hsu : s ≤ u₀)
    {x : ℝ × ℝ} (hx : x ∈ V.impactSlice S η η' A s) :
    V.departureFlight η (interiorStep V S η.1 x).2 (V.interiorDurationTotal η.1 x)
      = (x.1, -x.2) := by
  classical
  have hland := V.landingState_impactSlice S hx
  obtain ⟨⟨hxreg, hbdd⟩, hdur, -, -, hsp⟩ := hx
  have hrA : (interiorStep V S η.1 x).2 ∈ A := hsp
  have hreg : (interiorStep V S η.1 x).2 ∈ V.regularSpeeds η :=
    hbox.regular _ hrA
  set a : V.FlightState := FlightState.ofInterior V hxreg.1 hxreg.2 with hadef
  have hbdd' : BddAbove (durationSet V a.edge a.state) := hbdd
  set c : V.FlightState := V.ofDeparture η hreg.1 hreg.2 with hcdef
  have hce : c.edge = a.edge := rfl
  have hendeq : V.landingState η.1 x = a.segment.maximalEndpoint hbdd' := by
    rw [landingState, V.edgeFlight_of_mem hxreg]
    exact FlightState.flightCurve_sSup a hbdd'
  have hcs : c.state = ((a.segment.maximalEndpoint hbdd').1,
      -(a.segment.maximalEndpoint hbdd').2) := by
    rw [← hendeq, hland]
    show departurePoint η ((interiorStep V S η.1 x).2) =
      (coordinate Γ η, -(FiniteMetricGraph.EdgeEnd.sign Γ η * (interiorStep V S η.1 x).2))
    rw [departurePoint]
  have hθ : V.interiorDurationTotal η.1 x = sSup (durationSet V a.edge a.state) :=
    V.interiorDurationTotal_of_mem hxreg
  have hlong : ∀ _ : BddAbove (durationSet V c.edge c.state),
      sSup (durationSet V a.edge a.state) < sSup (durationSet V c.edge c.state) := by
    intro hcbdd
    have h1 : u₀ ≤ sSup (durationSet V c.edge c.state) := hbox.duration _ hrA hcbdd
    have h2 : sSup (durationSet V a.edge a.state) < s := by rw [← hθ]; exact hdur.2
    linarith
  have hkey := FlightState.flightCurve_of_reversedEndpoint_at_sSup a c hbdd' hce hcs hlong
  rw [hθ, V.departureFlight_of_mem hreg]
  exact hkey

/-! ### The trajectory past the impact -/

section Flow

variable [Nonempty Γ.Edge]

/-- **The trajectory of a one-impact state past its impact.**  Step one of the chain: the state
departs the scattered germ `η'` with the same speed, and the flow box guarantees that the next
impact has not yet happened before the time `s`. -/
theorem pointTrajectory_impactSlice {η η' : Γ.EdgeEnd} {A : Set ℝ} {s r₁ r₂ δ u₀ : ℝ}
    (hbox' : V.GermFlowBox η' A r₁ r₂ δ u₀) (hsu : s ≤ u₀)
    {x : ℝ × ℝ} (hx : x ∈ V.impactSlice S η η' A s) {t : ℝ}
    (hθt : V.interiorDurationTotal η.1 x ≤ t) (hts : t ≤ s) :
    V.pointTrajectory S ((η.1, x) : Γ.Edge × ℝ × ℝ) t =
      (η'.1, V.departureFlight η' (interiorStep V S η.1 x).2
        (t - V.interiorDurationTotal η.1 x)) := by
  classical
  obtain ⟨⟨hxreg, hbdd⟩, hdur, -, hstepgerm, hsp⟩ := hx
  have hrA : (interiorStep V S η.1 x).2 ∈ A := hsp
  have hreg' : (interiorStep V S η.1 x).2 ∈ V.regularSpeeds η' := hbox'.regular _ hrA
  set a : V.FlightState := FlightState.ofInterior V hxreg.1 hxreg.2 with hadef
  have hbdd' : BddAbove (durationSet V a.edge a.state) := hbdd
  have hθ : V.interiorDurationTotal η.1 x = sSup (durationSet V a.edge a.state) :=
    V.interiorDurationTotal_of_mem hxreg
  have ht0 : 0 ≤ t := le_trans (V.interiorDurationTotal_nonneg η.1 x) hθt
  have hsub0 : 0 ≤ t - V.interiorDurationTotal η.1 x := sub_nonneg.mpr hθt
  obtain ⟨b, hb, -, -, -, -⟩ := FlightState.next_eq_some_of_bddAbove (V := V) S a hbdd'
  have hb' : FlightState.next (V := V) S (FlightState.ofInterior V hxreg.1 hxreg.2) = some b := by
    rw [← hadef]; exact hb
  obtain ⟨hbe, hbs⟩ := V.interiorStep_next S hxreg hbdd hb'
  have hbe' : b.edge = η'.1 := by rw [hbe, hstepgerm]
  have hbs' : b.state = departurePoint η' ((interiorStep V S η.1 x).2) := by
    rw [hbs, hstepgerm]
  have hit1 : FlightState.iterate V S a 1 = some b := by
    rw [FlightState.iterate_succ, FlightState.iterate_zero, Option.bind_some]
    exact hb
  have hit1s : (FlightState.iterate V S a 1).isSome := by rw [hit1]; rfl
  have hir1 : FlightState.impactReal V S a 1 = sSup (durationSet V a.edge a.state) := by
    have h := FlightState.impactReal_succ_eq_of_isSome (V := V)
      (FlightState.iterate_zero (V := V) S a) hit1s
    rw [FlightState.impactReal_zero] at h
    linarith [h]
  have hact : FlightState.ActiveAt V S a 1 t := by
    refine ⟨hit1s, ?_, ?_⟩
    · rw [hir1, ← hθ]; exact hθt
    · intro hsucc
      have hbbdd : BddAbove (durationSet V b.edge b.state) := by
        refine FlightState.bddAbove_of_next_isSome (V := V) (S := S) ?_
        rw [FlightState.iterate_succ, hit1, Option.bind_some] at hsucc
        exact hsucc
      have hbbdd' : BddAbove
          (durationSet V η'.1 (departurePoint η' ((interiorStep V S η.1 x).2))) := by
        rw [← hbe', ← hbs']; exact hbbdd
      have hdu := hbox'.duration _ hrA hbbdd'
      have hsupeq : sSup (durationSet V b.edge b.state)
          = sSup (durationSet V η'.1
            (departurePoint η' ((interiorStep V S η.1 x).2))) := by rw [hbe', hbs']
      have hir2 := FlightState.impactReal_succ_eq_of_isSome (V := V) hit1 hsucc
      rw [hir1] at hir2
      have hθpos : 0 < sSup (durationSet V a.edge a.state) := by rw [← hθ]; exact hdur.1
      rw [hir2, hsupeq]
      linarith
  have htraj := FlightState.trajectory_eq V S a ht0 hact hit1
  rw [V.pointTrajectory_of_interior S (y := ((η.1, x) : Γ.Edge × ℝ × ℝ)) hxreg ht0,
    ← V.trajectory_eq_interiorTrajectory S hxreg (a := a) rfl rfl ht0, htraj, hir1, ← hθ]
  refine Prod.ext hbe' ?_
  have hcongr : FlightState.flightCurve V b (t - V.interiorDurationTotal η.1 x)
      = FlightState.flightCurve V (V.ofDeparture η' hreg'.1 hreg'.2)
        (t - V.interiorDurationTotal η.1 x) :=
    FlightState.flightCurve_congr (V := V) (by rw [hbe']; rfl) (by rw [hbs']; rfl) hsub0
  rw [hcongr, ← V.departureFlight_of_mem hreg']

end Flow

end MechanicalPotential

end HamiltonianMetricGraphs
