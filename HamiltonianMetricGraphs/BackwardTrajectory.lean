/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.UnifiedTrajectory

/-!
# The backward flight: exact retracing to the departure germ

This module supplies the analytic heart of the backward trajectory.  The retracing identity
`flightCurve_backwardRestart_eq` already says that the forward flight of `backwardRestart b s` runs
the original flight backwards with reversed momentum on `[0, s)`.  What the backward *chain* needs
in addition is that this backward flight **terminates exactly at time `s`, at the germ the original
flight departed from**:

`sSup (durationSet (backwardRestart b s)) = s`   (`sSup_durationSet_backwardRestart_eq`)

for an *outgoing* flight state `b`, i.e. one that departs a vertex germ.  Both inequalities are
proved here:

* `s ≤ sSup`: every `d < s` is realised by the concrete reflected segment `backwardSegment`, so it
  lies in the duration set;
* `sSup ≤ s`: if the backward flight outlasted `s` it would be *strictly inside* the edge at time
  `s` (`flightCurve_interior`).  But by continuity its value at `s` is the reversal of `b.state`,
  whose position is a vertex coordinate — not an interior point.  The same argument rules out the
  escape branch, so the backward flight is automatically bounded.

The limit input is `flightCurve_tendsto_initial`: a flight curve tends to its initial state as time
decreases to `0`.  This holds because a `PhysicalEdgeSegment` carries a genuine (two-sided)
`HasDerivAt` at every point of `Icc 0 duration`, in particular at `0`, hence is continuous there.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter Topology

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

namespace FlightState

/-- A flight curve is continuous at time `0` from the right: it tends to its initial state.  The
segment's `integralCurve` field supplies a two-sided derivative at `0`, hence continuity there. -/
theorem flightCurve_tendsto_initial (a : V.FlightState) :
    Tendsto (flightCurve V a) (𝓝[≥] (0 : ℝ)) (𝓝 a.state) := by
  classical
  -- the flight curve agrees with its own segment's curve on `[0, duration)`
  have hev : flightCurve V a =ᶠ[𝓝[≥] (0 : ℝ)] a.segment.curve := by
    filter_upwards [Ico_mem_nhdsGE a.segment.duration_pos] with w hw
    exact flightCurve_eq_segment_curve V a hw.1 hw.2
  have hcont : ContinuousAt a.segment.curve 0 :=
    (a.segment.integralCurve 0 ⟨le_rfl, a.segment.duration_pos.le⟩).continuousAt
  have hlim : Tendsto a.segment.curve (𝓝[≥] (0 : ℝ)) (𝓝 (a.segment.curve 0)) :=
    hcont.continuousWithinAt.tendsto
  rw [a.segment.initial] at hlim
  exact hlim.congr' hev.symm

/-- The backward flight tends, as the elapsed time approaches `s` from below, to the momentum
reversal of the state the original flight departed from: on `[0, s)` the backward flight is the
reflected original flight, and `w → s⁻` sends `s - w → 0⁺`, where the original flight is at
`b.state`. -/
theorem flightCurve_backwardRestart_tendsto (b : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      s < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state)) :
    Tendsto (flightCurve V (backwardRestart V b hs0 hs)) (𝓝[<] s)
      (𝓝 (b.state.1, -b.state.2)) := by
  classical
  -- `w ↦ s - w` sends `𝓝[<] s` into `𝓝[≥] 0`
  have hsub : Tendsto (fun w : ℝ => s - w) (𝓝[<] s) (𝓝[≥] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Tendsto (fun w : ℝ => s - w) (𝓝 s) (𝓝 (s - s)) :=
        (continuous_const.sub continuous_id).tendsto s
      rw [sub_self] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact le_of_lt (sub_pos.mpr (mem_Iio.mp hw))
  have hcomp : Tendsto (fun w : ℝ => flightCurve V b (s - w)) (𝓝[<] s) (𝓝 b.state) :=
    (flightCurve_tendsto_initial V b).comp hsub
  have hmap : Continuous (fun y : ℝ × ℝ => (y.1, -y.2)) := by fun_prop
  have hrev : Tendsto (fun w : ℝ => ((flightCurve V b (s - w)).1, -(flightCurve V b (s - w)).2))
      (𝓝[<] s) (𝓝 (b.state.1, -b.state.2)) := by
    simpa [Function.comp_def] using (hmap.tendsto b.state).comp hcomp
  refine hrev.congr' ?_
  filter_upwards [Ico_mem_nhdsLT hs0] with w hw
  exact (flightCurve_backwardRestart_eq V b hs0 hs hw.1 hw.2).symm

/-- If the backward flight outlasted the elapsed time `s`, then at time `s` it would sit exactly at
the momentum reversal of the departure state — a limit computation.  This is the step that
contradicts interiority, and it is stated separately because it is the identification of the
backward flight's terminal point. -/
theorem flightCurve_backwardRestart_at_end (b : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      s < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state))
    (hlong : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V
        (backwardRestart V b hs0 hs).edge (backwardRestart V b hs0 hs).state),
      s < sSup (PhysicalEdgeSegment.durationSet V (backwardRestart V b hs0 hs).edge
        (backwardRestart V b hs0 hs).state)) :
    flightCurve V (backwardRestart V b hs0 hs) s = (b.state.1, -b.state.2) := by
  classical
  set r := backwardRestart V b hs0 hs with hr
  -- the backward flight is differentiable, hence continuous, at `s`
  have hcont : ContinuousAt (flightCurve V r) s :=
    (flightCurve_hasDerivAt V r hs0 hlong).continuousAt
  have h1 : Tendsto (flightCurve V r) (𝓝[<] s) (𝓝 (flightCurve V r s)) :=
    hcont.continuousWithinAt.tendsto
  have h2 : Tendsto (flightCurve V r) (𝓝[<] s) (𝓝 (b.state.1, -b.state.2)) :=
    flightCurve_backwardRestart_tendsto V b hs0 hs
  exact tendsto_nhds_unique h1 h2

/-- **The backward flight of an outgoing flight terminates exactly at its departure germ.**  For an
outgoing flight state `b` and any time `s` strictly inside its flight, the flight started at the
momentum-reversed point `backwardRestart b s` has a bounded duration set with supremum exactly `s`:
it retraces `b` and stops on arrival at the vertex germ that `b` departed from.

This is what will let the backward chain be identified with the forward chain of the time-reversed
scattering law: the backward flight's maximal arrival is the reversal of `b`'s departure. -/
theorem sSup_durationSet_backwardRestart_eq (b : V.FlightState) (hout : b.IsOutgoing) {s : ℝ}
    (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      s < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state)) :
    BddAbove (PhysicalEdgeSegment.durationSet V (backwardRestart V b hs0 hs).edge
        (backwardRestart V b hs0 hs).state) ∧
      sSup (PhysicalEdgeSegment.durationSet V (backwardRestart V b hs0 hs).edge
        (backwardRestart V b hs0 hs).state) = s := by
  classical
  set r := backwardRestart V b hs0 hs with hr
  -- `b.state.1` is a vertex coordinate, hence not interior to the edge
  obtain ⟨η₀, hη₀, hstate, -⟩ := hout
  have hnotint : b.state.1 ∉ Ioo (0 : ℝ) (Γ.length b.edge) := by
    rw [hstate]
    unfold FiniteMetricGraph.EdgeEnd.coordinate
    by_cases hη2 : η₀.2
    · rw [if_pos hη2, hη₀]
      exact fun hmem => absurd hmem.2 (lt_irrefl _)
    · rw [if_neg hη2]
      exact fun hmem => absurd hmem.1 (lt_irrefl 0)
  -- every `d ∈ (0, s)` is realised by the reflected segment
  have hmemdur : ∀ d : ℝ, 0 < d → d < s →
      d ∈ PhysicalEdgeSegment.durationSet V r.edge r.state :=
    fun d hd0 hds => ⟨backwardSegment V b hs hd0 hds, rfl⟩
  -- the backward flight cannot outlast `s`: it would then be interior at the departure germ
  have hnotlong : ¬ ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V r.edge r.state),
      s < sSup (PhysicalEdgeSegment.durationSet V r.edge r.state) := by
    intro hlong
    have hval := flightCurve_backwardRestart_at_end V b hs0 hs hlong
    have hint := flightCurve_interior V r hs0 hlong
    rw [hval] at hint
    exact hnotint hint
  -- hence the flight is bounded with `sSup ≤ s`
  have hbdd : BddAbove (PhysicalEdgeSegment.durationSet V r.edge r.state) := by
    by_contra hub
    exact hnotlong (fun hbdd => absurd hbdd hub)
  have hle : sSup (PhysicalEdgeSegment.durationSet V r.edge r.state) ≤ s := by
    by_contra hgt
    exact hnotlong (fun _ => lt_of_not_ge hgt)
  refine ⟨hbdd, le_antisymm hle ?_⟩
  -- and `s ≤ sSup`, since every `d < s` is a certified duration
  by_contra hlt
  rw [not_le] at hlt
  set d : ℝ := (sSup (PhysicalEdgeSegment.durationSet V r.edge r.state) + s) / 2 with hd
  have hs2 : s / 2 ≤ sSup (PhysicalEdgeSegment.durationSet V r.edge r.state) :=
    le_csSup hbdd (hmemdur (s / 2) (by linarith) (by linarith))
  have hd0 : 0 < d := by rw [hd]; linarith
  have hds : d < s := by rw [hd]; linarith
  have hdle : d ≤ sSup (PhysicalEdgeSegment.durationSet V r.edge r.state) :=
    le_csSup hbdd (hmemdur d hd0 hds)
  rw [hd] at hdle
  linarith

/-- **The backward flight's maximal endpoint is the reversed departure state.**  Combining the
exact retracing time `sSup = s` with the limit computation identifies where the backward flight
lands: at the momentum reversal of the state the original flight departed from.

This is the geometric input to the backward chain's scattering event — the incoming covector of the
backward flight is built from this endpoint, and it is exactly the reversal of `b`'s outgoing
departure covector. -/
theorem maximalEndpoint_backwardRestart_eq (b : V.FlightState) (hout : b.IsOutgoing) {s : ℝ}
    (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      s < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state))
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V (backwardRestart V b hs0 hs).edge
      (backwardRestart V b hs0 hs).state)) :
    (backwardRestart V b hs0 hs).segment.maximalEndpoint hbdd = (b.state.1, -b.state.2) := by
  classical
  set r := backwardRestart V b hs0 hs with hr
  have hsup : sSup (PhysicalEdgeSegment.durationSet V r.edge r.state) = s :=
    (sSup_durationSet_backwardRestart_eq V b hout hs0 hs).2
  -- the canonical maximal curve tends to the maximal endpoint
  have h1 : Tendsto (r.segment.maximalCurve hbdd)
      (𝓝[<] sSup (PhysicalEdgeSegment.durationSet V r.edge r.state))
      (𝓝 (r.segment.maximalEndpoint hbdd)) :=
    r.segment.tendsto_maximalCurve_maximalEndpoint hbdd
  rw [hsup] at h1
  -- below the supremum it agrees with the flight curve, which tends to the reversed departure
  have heq : flightCurve V r =ᶠ[𝓝[<] s] r.segment.maximalCurve hbdd := by
    filter_upwards [Ico_mem_nhdsLT hs0] with w hw
    unfold flightCurve
    rw [dif_pos hbdd]
    exact r.segment.maximalCurveClosed_eq_maximalCurve hbdd (by rw [hsup]; exact hw.2)
  have h2 : Tendsto (r.segment.maximalCurve hbdd) (𝓝[<] s) (𝓝 (b.state.1, -b.state.2)) :=
    (flightCurve_backwardRestart_tendsto V b hs0 hs).congr' heq
  exact tendsto_nhds_unique h1 h2

/-!
## The backward arrival covector

The backward flight lands on the reversed departure state; it remains to see that the covector the
first-hit interface builds there is exactly the **momentum reversal of the departure covector**.
This is a matching of conventions: `maximalArrivalCovector` selects the germ `(e, false)` or
`(e, true)` according to whether the endpoint coordinate is `0` or `length e`, and an outgoing
flight state departs a germ `η₀` whose coordinate is its initial position.  Since edge lengths are
strictly positive the two endpoint coordinates are distinct, so the germ is determined.
-/

/-- The momentum of an outgoing flight state is nonzero: it departs its germ transversally. -/
theorem IsOutgoing.momentum_ne_zero {b : V.FlightState} {η₀ : Γ.EdgeEnd}
    (hsign : FiniteMetricGraph.EdgeEnd.sign Γ η₀ * b.state.2 < 0) : b.state.2 ≠ 0 := by
  intro h
  rw [h, mul_zero] at hsign
  exact absurd hsign (lt_irrefl 0)

/-- **The backward flight's arrival covector is the reversed departure covector.**  For an outgoing
flight state `b` departing the germ `η₀` with momentum `b.state.2`, the backward flight from
`backwardRestart b s` arrives at `η₀` carrying momentum `-b.state.2`:

`maximalArrivalCovector (backwardRestart b s) = momentumReversal ⟨η₀, b.state.2⟩`.

This is the bridge from the backward flight's geometry to the scattering interface.  Because
`timeReversed S = R ∘ S⁻¹ ∘ R`, applying `S*` to this covector yields `R` of `S⁻¹` of `b`'s
departure covector — that is, `R` of the arrival covector of the flight that scattered *into* `b`,
which is precisely the outgoing covector restarting the retraced predecessor. -/
theorem maximalArrivalCovector_backwardRestart_eq (b : V.FlightState) {η₀ : Γ.EdgeEnd}
    (hη₀ : η₀.1 = b.edge) (hstate : b.state.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ η₀)
    (hsign : FiniteMetricGraph.EdgeEnd.sign Γ η₀ * b.state.2 < 0) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      s < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state))
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V (backwardRestart V b hs0 hs).edge
      (backwardRestart V b hs0 hs).state)) :
    (backwardRestart V b hs0 hs).segment.maximalArrivalCovector hbdd
        (backwardRestart V b hs0 hs).regular =
      FiniteMetricGraph.BoundaryCovector.momentumReversal Γ
        ⟨η₀, b.state.2, IsOutgoing.momentum_ne_zero V hsign⟩ := by
  classical
  set r := backwardRestart V b hs0 hs with hr
  have hout : b.IsOutgoing := ⟨η₀, hη₀, hstate, hsign⟩
  have hend : r.segment.maximalEndpoint hbdd = (b.state.1, -b.state.2) :=
    maximalEndpoint_backwardRestart_eq V b hout hs0 hs hbdd
  refine FiniteMetricGraph.BoundaryCovector.ext Γ ?_ ?_
  · -- the germ: determined by whether the landing coordinate is `0` or `length`
    show (r.segment.maximalArrivalCovector hbdd r.regular).germ = η₀
    by_cases hleft : (r.segment.maximalEndpoint hbdd).1 = 0
    · -- landing at coordinate `0`, so `η₀` is the left germ
      have hb0 : b.state.1 = 0 := by rw [hend] at hleft; exact hleft
      have hη2 : η₀.2 = false := by
        by_contra hne
        rw [Bool.not_eq_false] at hne
        rw [hstate] at hb0
        unfold FiniteMetricGraph.EdgeEnd.coordinate at hb0
        rw [if_pos hne] at hb0
        exact absurd hb0 (ne_of_gt (Γ.length_pos η₀.1))
      have : (r.segment.maximalArrivalCovector hbdd r.regular).germ = (r.edge, false) := by
        simp [PhysicalEdgeSegment.maximalArrivalCovector, hleft]
      rw [this]
      exact Prod.ext hη₀.symm hη2.symm
    · -- landing at coordinate `length`, so `η₀` is the right germ
      have hb0 : b.state.1 ≠ 0 := by rw [hend] at hleft; exact hleft
      have hη2 : η₀.2 = true := by
        by_contra hne
        rw [Bool.not_eq_true] at hne
        apply hb0
        rw [hstate]
        unfold FiniteMetricGraph.EdgeEnd.coordinate
        rw [if_neg (by simp [hne])]
      have : (r.segment.maximalArrivalCovector hbdd r.regular).germ = (r.edge, true) := by
        simp [PhysicalEdgeSegment.maximalArrivalCovector, hleft]
      rw [this]
      exact Prod.ext hη₀.symm hη2.symm
  · -- the momentum: the reversed departure momentum
    show (r.segment.maximalArrivalCovector hbdd r.regular).momentum = -b.state.2
    rw [PhysicalEdgeSegment.maximalArrivalCovector_momentum, hend]

/-!
## The backward chain retraces the forward chain

With the arrival covector identified, the chain correspondence is an algebraic computation in the
time-reversed law.  If `a` scatters into `b` (so `b` departs the germ of `β = S α`, where `α` is
`a`'s arrival covector), then the backward flight from inside `b` arrives carrying `R β`, and

`S* (R β) = R (S⁻¹ (R (R β))) = R (S⁻¹ β) = R α`,

so the backward chain's next flight departs `a`'s **arrival** germ with reversed momentum — it
retraces `a`.  Only the invertibility of `S` is used; reversibility is never assumed.
-/

/-- Transport of a scattering value along an equality of base vertices. -/
private theorem smap_cast (S : BorelEnergyPreservingScattering V) {v v' : Γ.Vertex} (hvv : v = v')
    (γ : Γ.IncomingBoundary v) : (S.map v' (hvv ▸ γ)).1 = (S.map v γ).1 := by
  subst hvv; rfl

/-- Transport of an incoming covector along an equality of base vertices. -/
private theorem incoming_val_cast {v v' : Γ.Vertex} (hvv : v = v') (γ : Γ.IncomingBoundary v) :
    (hvv ▸ γ).1 = γ.1 := by subst hvv; rfl

/-- **The backward chain retraces the forward chain across an impact.**  If `a` scatters into `b`
under `S`, then the backward flight started strictly inside `b` scatters, under the time-reversed
law `S*`, into the flight that departs `a`'s arrival germ with reversed momentum — i.e. into the
momentum reversal of `a`'s terminal state, which retraces `a`.

This is the step-5 backward↔forward correspondence at the level of one scattering event.  Combined
with the retracing identity on each flight it identifies the whole backward chain of `S` with the
forward chain of `S*`. -/
theorem next_timeReversed_backwardRestart (S : BorelEnergyPreservingScattering V)
    {a b : V.FlightState}
    (hbddA : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state))
    (hnext : next V S a = some b) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      s < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state)) :
    ∃ c : V.FlightState,
      next V (BorelEnergyPreservingScattering.timeReversed V S)
          (backwardRestart V b hs0 hs) = some c ∧
        c.edge = a.edge ∧
        c.state = ((a.segment.maximalEndpoint hbddA).1, -(a.segment.maximalEndpoint hbddA).2) := by
  classical
  set α := a.segment.maximalArrivalIncoming hbddA a.regular with hαdef
  set β := S.map α.1.germ.vertex α with hβdef
  -- unpack the forward successor `b`
  obtain ⟨b₀, hb₀, hb₀state, -, hb₀out, hb₀edge⟩ := next_eq_some_of_bddAbove (V := V) S a hbddA
  have hbb : b = b₀ := Option.some.inj (hnext.symm.trans hb₀)
  have hbedge : b.edge = β.1.germ.1 := by rw [hbb]; exact hb₀edge
  have hbstate : b.state =
      (FiniteMetricGraph.EdgeEnd.coordinate Γ β.1.germ, β.1.momentum) := by
    rw [hbb]; exact hb₀state
  have hbout : b.IsOutgoing := by rw [hbb]; exact hb₀out
  set r := backwardRestart V b hs0 hs with hrdef
  have hrbdd : BddAbove (PhysicalEdgeSegment.durationSet V r.edge r.state) :=
    (sSup_durationSet_backwardRestart_eq V b hbout hs0 hs).1
  -- the backward arrival covector is the reversal of `b`'s departure covector `β`
  have hsign : FiniteMetricGraph.EdgeEnd.sign Γ β.1.germ * b.state.2 < 0 := by
    rw [hbstate]; exact β.2.2
  have hcov : r.segment.maximalArrivalCovector hrbdd r.regular =
      FiniteMetricGraph.BoundaryCovector.momentumReversal Γ
        ⟨β.1.germ, b.state.2, IsOutgoing.momentum_ne_zero V hsign⟩ :=
    maximalArrivalCovector_backwardRestart_eq V b hbedge.symm (by rw [hbstate]) hsign hs0 hs hrbdd
  set γ := r.segment.maximalArrivalIncoming hrbdd r.regular with hγdef
  have hγ1 : γ.1 = ⟨β.1.germ, -β.1.momentum, neg_ne_zero.mpr β.1.momentum_ne_zero⟩ := by
    show r.segment.maximalArrivalCovector hrbdd r.regular = _
    rw [hcov]
    refine FiniteMetricGraph.BoundaryCovector.ext Γ rfl ?_
    show -b.state.2 = -β.1.momentum
    rw [hbstate]
  -- the two vertices agree
  have hv : γ.1.germ.vertex = α.1.germ.vertex := by rw [hγ1]; exact β.2.1
  have hδ1 : (hv ▸ γ).1 = γ.1 := incoming_val_cast hv γ
  -- reversing the backward arrival returns `b`'s departure covector `β`
  have hRδ : (Γ.incomingMomentumReversalMeasurableEquiv (α.1.germ.vertex)) (hv ▸ γ) = β := by
    apply Subtype.ext
    refine FiniteMetricGraph.BoundaryCovector.ext Γ ?_ ?_
    · show (hv ▸ γ).1.germ = β.1.germ
      rw [hδ1, hγ1]
    · show -(hv ▸ γ).1.momentum = β.1.momentum
      rw [hδ1, hγ1]
      show - -β.1.momentum = β.1.momentum
      rw [neg_neg]
  -- so the time-reversed law returns the reversal of `a`'s arrival covector `α`
  have hstarE : (BorelEnergyPreservingScattering.timeReversed V S).map (α.1.germ.vertex)
      (hv ▸ γ) = (Γ.incomingMomentumReversalMeasurableEquiv (α.1.germ.vertex)) α := by
    show (Γ.incomingMomentumReversalMeasurableEquiv (α.1.germ.vertex))
      ((S.map (α.1.germ.vertex)).symm
        ((Γ.incomingMomentumReversalMeasurableEquiv (α.1.germ.vertex)) (hv ▸ γ))) = _
    rw [hRδ, hβdef, MeasurableEquiv.symm_apply_apply]
  -- read off the successor of the backward flight
  obtain ⟨c, hc, hcstate, -, -, hcedge⟩ :=
    next_eq_some_of_bddAbove (V := V) (BorelEnergyPreservingScattering.timeReversed V S) r hrbdd
  have hval : ((BorelEnergyPreservingScattering.timeReversed V S).map γ.1.germ.vertex γ).1 =
      ⟨α.1.germ, -α.1.momentum, neg_ne_zero.mpr α.1.momentum_ne_zero⟩ := by
    rw [← smap_cast V (BorelEnergyPreservingScattering.timeReversed V S) hv γ, hstarE]
    rfl
  refine ⟨c, hc, ?_, ?_⟩
  · rw [hcedge, hval]
    show α.1.germ.1 = a.edge
    exact a.segment.maximalArrivalCovector_germ_fst hbddA a.regular
  · rw [hcstate, hval]
    show (FiniteMetricGraph.EdgeEnd.coordinate Γ α.1.germ, -α.1.momentum) = _
    rw [show FiniteMetricGraph.EdgeEnd.coordinate Γ α.1.germ =
        (a.segment.maximalEndpoint hbddA).1 from
      a.segment.maximalArrivalCovector_coordinate hbddA a.regular,
      show α.1.momentum = (a.segment.maximalEndpoint hbddA).2 from
        a.segment.maximalArrivalCovector_momentum hbddA a.regular]

/-- **The backward trajectory retraces the forward flight.**  Under the time-reversed law `S*`, the
trajectory started at the momentum-reversed point `backwardRestart b s` runs the flight of `b`
backwards, with reversed momentum, for the whole retracing time `0 ≤ u < s`:

`Φ⁺_{S*}(u) (R (flightCurve b s)) = R (flightCurve b (s - u))`.

The exact retracing time `sSup = s` is what makes this hold on the *whole* of `[0, s)`: the
backward flight is flight `0` of its `S*`-chain throughout, and its first `S*`-impact happens
exactly at `s`, on arrival at `b`'s departure germ.  Past `s` the `S*`-chain continues into the
retraced predecessor, by `next_timeReversed_backwardRestart`. -/
theorem trajectory_timeReversed_backwardRestart [Nonempty Γ.Edge]
    (S : BorelEnergyPreservingScattering V) (b : V.FlightState) (hout : b.IsOutgoing) {s : ℝ}
    (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      s < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state))
    {u : ℝ} (hu0 : 0 ≤ u) (hus : u < s) :
    trajectory V (BorelEnergyPreservingScattering.timeReversed V S)
        (backwardRestart V b hs0 hs) u =
      (b.edge, ((flightCurve V b (s - u)).1, -(flightCurve V b (s - u)).2)) := by
  classical
  set r := backwardRestart V b hs0 hs with hrdef
  have hsup : sSup (PhysicalEdgeSegment.durationSet V r.edge r.state) = s :=
    (sSup_durationSet_backwardRestart_eq V b hout hs0 hs).2
  -- the backward flight governs the whole retracing interval: its first impact is exactly at `s`
  have hact : ActiveAt V (BorelEnergyPreservingScattering.timeReversed V S) r 0 u := by
    refine ⟨by rw [iterate_zero]; rfl, by rw [impactReal_zero]; exact hu0, fun hsucc => ?_⟩
    rw [impactReal_succ_eq_of_isSome (V := V)
      (iterate_zero (V := V) (BorelEnergyPreservingScattering.timeReversed V S) r) hsucc,
      impactReal_zero, hsup]
    linarith
  rw [trajectory_eq V (BorelEnergyPreservingScattering.timeReversed V S) r hu0 hact
    (iterate_zero (V := V) (BorelEnergyPreservingScattering.timeReversed V S) r),
    impactReal_zero, sub_zero]
  exact congrArg (fun y => (b.edge, y)) (flightCurve_backwardRestart_eq V b hs0 hs hu0 hus)

/-!
## The backward phase

`backwardPhase` is the backward-time evolution of an interior regular state, defined by conjugating
the forward trajectory of the **time-reversed law** with momentum reversal:

`Φ⁻_S(t) = R ∘ Φ⁺_{S*}(t) ∘ R`,   `S* = R ∘ S⁻¹ ∘ R`.

Only the invertibility of `S` enters, so this is the backward dynamics of a general (not
necessarily reversible) scattering law.
-/

/-- The momentum reversal of an interior flight state.  It is regular because momentum reversal
preserves the mechanical energy. -/
noncomputable def momentumReversed (a : V.FlightState)
    (hint : a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge)) : V.FlightState :=
  ofInterior (V := V) (e := a.edge) (x := (a.state.1, -a.state.2)) hint
    (by rw [V.hamiltonian_neg_momentum]; exact a.regular)

@[simp] theorem momentumReversed_edge (a : V.FlightState)
    (hint : a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge)) :
    (momentumReversed V a hint).edge = a.edge := rfl

@[simp] theorem momentumReversed_state (a : V.FlightState)
    (hint : a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge)) :
    (momentumReversed V a hint).state = (a.state.1, -a.state.2) := rfl

/-- **The backward scattered trajectory** of an interior regular state: the forward trajectory of
the time-reversed law `S*`, conjugated by momentum reversal. -/
noncomputable def backwardPhase [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hint : a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge)) (t : ℝ) :
    Γ.Edge × ℝ × ℝ :=
  ((trajectory V (BorelEnergyPreservingScattering.timeReversed V S)
      (momentumReversed V a hint) t).1,
   (trajectory V (BorelEnergyPreservingScattering.timeReversed V S)
      (momentumReversed V a hint) t).2.1,
   -(trajectory V (BorelEnergyPreservingScattering.timeReversed V S)
      (momentumReversed V a hint) t).2.2)

/-- The backward trajectory starts where it should. -/
@[simp] theorem backwardPhase_zero [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hint : a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge)) :
    backwardPhase V S a hint 0 = (a.edge, a.state) := by
  unfold backwardPhase
  rw [trajectory_zero]
  show (a.edge, a.state.1, - -a.state.2) = (a.edge, a.state)
  rw [neg_neg]

/-- **Forward/backward correspondence within a flight.**  Running forward to time `s` inside a
flight and then backward for a time `u < s` returns to the forward trajectory at time `s - u`:

`Φ⁻(u) (Φ⁺(s) x) = Φ⁺(s - u) x`.

This is the flight-level content of `Φ(-t) = (Φ t)⁻¹`; taking `u = s` (in the limit) returns to `x`
itself.  The proof conjugates `trajectory_timeReversed_backwardRestart`: the momentum reversal of
the state at time `s` is exactly `backwardRestart b s`, whose `S*`-trajectory retraces the
flight. -/
theorem backwardPhase_restart_eq [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (b : V.FlightState) (hout : b.IsOutgoing) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      s < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state))
    (hint : (restart V b hs0 hs).state.1 ∈ Ioo (0 : ℝ) (Γ.length (restart V b hs0 hs).edge))
    {u : ℝ} (hu0 : 0 ≤ u) (hus : u < s) :
    backwardPhase V S (restart V b hs0 hs) hint u = (b.edge, flightCurve V b (s - u)) := by
  classical
  -- the momentum reversal of the time-`s` state is exactly the backward restart
  have hcongr : trajectory V (BorelEnergyPreservingScattering.timeReversed V S)
      (momentumReversed V (restart V b hs0 hs) hint) u =
        trajectory V (BorelEnergyPreservingScattering.timeReversed V S)
          (backwardRestart V b hs0 hs) u :=
    trajectory_congr (V := V) (BorelEnergyPreservingScattering.timeReversed V S) rfl rfl hu0
  unfold backwardPhase
  rw [hcongr, trajectory_timeReversed_backwardRestart V S b hout hs0 hs hu0 hus]
  show (b.edge, (flightCurve V b (s - u)).1, - -(flightCurve V b (s - u)).2) = _
  rw [neg_neg]

end FlightState
end MechanicalPotential
end HamiltonianMetricGraphs
