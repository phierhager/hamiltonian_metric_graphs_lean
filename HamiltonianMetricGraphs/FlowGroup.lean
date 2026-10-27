/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition V.5: the group law `Φ_{s+t} = Φ_t ∘ Φ_s`, `Φ₀ = id`, `Φₜ⁻¹ = Φ₋ₜ`.
-/

import HamiltonianMetricGraphs.QuotientFlow

/-!
# The group law of the scattered evolution

`QuotientFlow` defines `Φₜ` for every real `t` and proves the semigroup laws on each half-line.
This module proves the two inverse identities `Φ₋ₜ ∘ Φₜ = id` and `Φₜ ∘ Φ₋ₜ = id`, and deduces the
full group law (3) of the paper: `Φ_{s+t} = Φ_t ∘ Φ_s` for all real `s, t`.

The inverse identities rest on the **backward–forward identity**
`Φ⁺_{w,T} (ρ (Φ⁺_{u,S} z)) = ρ (Φ⁺_{u-w,S} z)` for `0 ≤ w ≤ u`, where `T` is a time reversal of
`S`: running the reversed dynamics for time `w` from the reversed time-`u` point retraces the
trajectory back to time `u - w`.  It is proved by induction over the impacts of the forward
trajectory, using

* the within-flight retrace of `BackwardTrajectory` (`flightCurve_backwardRestart_eq`),
* the retrace from an arrival point of `FlightRetrace` (`flightCurve_of_reversedEndpoint`), and
* the scattering step of the backward chain (`next_of_landing_at_reversedDeparture`), which sends
  the backward flight of a scattered flight to the reversed arrival point of its predecessor.

At an impact time the reversed point is an *incoming* boundary point, whose outgoing representative
in `Q(T)` is its `T`-image: this is where the quotient identification `α ∼ S α` enters, and it is
handled uniformly by `graphClass_reverse_eq_of_step`.

Since `IsTimeReversal` is symmetric, the identity applies to the pair `(S, S*)` and to the pair
`(S*, S)`, which gives both inverse identities from the same theorem.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter Topology FlightState PhysicalEdgeSegment

variable {Γ : FiniteMetricGraph} {V : MechanicalPotential Γ}

/-! ### Within-flight retrace, without an outgoing hypothesis -/

namespace FlightState

/-- The backward flight started strictly inside a flight lasts at least until the retrace is
complete: every shorter time is a certified duration of the reflected segment. -/
theorem le_sSup_durationSet_backwardRestart (b : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (durationSet V b.edge b.state),
      s < sSup (durationSet V b.edge b.state))
    (hbdd : BddAbove (durationSet V (backwardRestart V b hs0 hs).edge
      (backwardRestart V b hs0 hs).state)) :
    s ≤ sSup (durationSet V (backwardRestart V b hs0 hs).edge
      (backwardRestart V b hs0 hs).state) := by
  set r := backwardRestart V b hs0 hs with hr
  have hmemdur : ∀ d : ℝ, 0 < d → d < s → d ∈ durationSet V r.edge r.state :=
    fun d hd0 hds => ⟨backwardSegment V b hs hd0 hds, rfl⟩
  by_contra hlt
  rw [not_le] at hlt
  set d : ℝ := (sSup (durationSet V r.edge r.state) + s) / 2 with hd
  have hs2 : s / 2 ≤ sSup (durationSet V r.edge r.state) :=
    le_csSup hbdd (hmemdur (s / 2) (by linarith) (by linarith))
  have hd0 : 0 < d := by rw [hd]; linarith
  have hds : d < s := by rw [hd]; linarith
  have hdle : d ≤ sSup (durationSet V r.edge r.state) := le_csSup hbdd (hmemdur d hd0 hds)
  rw [hd] at hdle
  linarith

/-- If the flight starts strictly inside its edge, its backward flight from an interior time
outlasts the retrace: at the retrace time it sits at the reversed start point, which is interior,
so it cannot land there. -/
theorem backwardRestart_long_of_interior (b : V.FlightState)
    (hint : b.state.1 ∈ Ioo (0 : ℝ) (Γ.length b.edge)) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (durationSet V b.edge b.state),
      s < sSup (durationSet V b.edge b.state)) :
    ∀ hbdd : BddAbove (durationSet V (backwardRestart V b hs0 hs).edge
        (backwardRestart V b hs0 hs).state),
      s < sSup (durationSet V (backwardRestart V b hs0 hs).edge
        (backwardRestart V b hs0 hs).state) := by
  intro hbdd
  set r := backwardRestart V b hs0 hs with hr
  rcases eq_or_lt_of_le (le_sSup_durationSet_backwardRestart b hs0 hs hbdd) with heq | hlt
  · exfalso
    have h1 : Tendsto (flightCurve V r) (𝓝[<] s) (𝓝 (r.segment.maximalEndpoint hbdd)) := by
      have := r.segment.tendsto_maximalCurve_maximalEndpoint hbdd
      rw [← heq] at this
      refine this.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hs0] with w hw
      unfold flightCurve; rw [dif_pos hbdd]
      exact (r.segment.maximalCurveClosed_eq_maximalCurve hbdd (by rw [← heq]; exact hw.2)).symm
    have h2 := flightCurve_backwardRestart_tendsto V b hs0 hs
    have heq2 := tendsto_nhds_unique h1 h2
    apply r.segment.maximalEndpoint_not_interior hbdd
    rw [heq2]
    exact hint
  · exact hlt

/-- The backward flight retraces the flight for any law `T`, before the retrace time. -/
theorem trajectory_backwardRestart_of_lt [Nonempty Γ.Edge] (T : BorelEnergyPreservingScattering V)
    (b : V.FlightState) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (durationSet V b.edge b.state),
      s < sSup (durationSet V b.edge b.state))
    {u : ℝ} (hu0 : 0 ≤ u) (hus : u < s) :
    trajectory V T (backwardRestart V b hs0 hs) u =
      (b.edge, ((flightCurve V b (s - u)).1, -(flightCurve V b (s - u)).2)) := by
  set r := backwardRestart V b hs0 hs with hr
  have hact : ActiveAt V T r 0 u := by
    refine ⟨by rw [iterate_zero]; rfl, by rw [impactReal_zero]; exact hu0, fun hsucc => ?_⟩
    have hrbdd : BddAbove (durationSet V r.edge r.state) := by
      apply bddAbove_of_next_isSome (S := T)
      rw [iterate_succ, iterate_zero] at hsucc
      exact hsucc
    rw [impactReal_succ_eq_of_isSome (V := V) (iterate_zero V T r) hsucc, impactReal_zero, zero_add]
    exact lt_of_lt_of_le hus (le_sSup_durationSet_backwardRestart b hs0 hs hrbdd)
  rw [trajectory_eq V T r hu0 hact (iterate_zero V T r), impactReal_zero, sub_zero]
  exact congrArg (fun y => (b.edge, y)) (flightCurve_backwardRestart_eq V b hs0 hs hu0 hus)

/-! ### The scattering step of the backward chain, read on the forward chain -/

private theorem outgoing_val_cast {v v' : Γ.Vertex} (hvv : v = v') (β : Γ.OutgoingBoundary v) :
    (hvv ▸ β).1 = β.1 := by subst hvv; rfl

private theorem smap_symm_cast (S : BorelEnergyPreservingScattering V) {v v' : Γ.Vertex}
    (hvv : v = v') (β : Γ.OutgoingBoundary v) :
    ((S.map v').symm (hvv ▸ β)).1 = ((S.map v).symm β).1 := by subst hvv; rfl

/-- The `S`-preimage of the departure covector of a scattered successor is the arrival covector
of its predecessor. -/
theorem exists_departure_of_next (S : BorelEnergyPreservingScattering V) {b' b : V.FlightState}
    (hbdd' : BddAbove (durationSet V b'.edge b'.state)) (hnext : next V S b' = some b) :
    ∃ (η₀ : Γ.EdgeEnd) (hη₀ : η₀.1 = b.edge)
      (hstate : b.state.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ η₀)
      (hsign : FiniteMetricGraph.EdgeEnd.sign Γ η₀ * b.state.2 < 0),
      ((S.map η₀.vertex).symm (departureCovector b hsign)).1 =
        b'.segment.maximalArrivalCovector hbdd' b'.regular := by
  obtain ⟨b₀, hb₀, hb₀state, -, -, hb₀edge⟩ := next_eq_some_of_bddAbove (V := V) S b' hbdd'
  have hbb : b = b₀ := Option.some.inj (hnext.symm.trans hb₀)
  subst hbb
  set α' := b'.segment.maximalArrivalIncoming hbdd' b'.regular with hα'
  set β := S.map α'.1.germ.vertex α' with hβ
  have hstate : b.state.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ β.1.germ := by rw [hb₀state]
  have hsign : FiniteMetricGraph.EdgeEnd.sign Γ β.1.germ * b.state.2 < 0 := by
    rw [hb₀state]; exact β.2.2
  refine ⟨β.1.germ, hb₀edge.symm, hstate, hsign, ?_⟩
  have hv : β.1.germ.vertex = α'.1.germ.vertex := β.2.1
  have hdep : hv ▸ departureCovector b hsign = β := by
    apply Subtype.ext
    rw [outgoing_val_cast hv]
    refine FiniteMetricGraph.BoundaryCovector.ext Γ rfl ?_
    change b.state.2 = β.1.momentum
    rw [hb₀state]
  rw [← smap_symm_cast S hv (departureCovector b hsign), hdep, hβ,
    (S.map α'.1.germ.vertex).symm_apply_apply α']
  rfl

/-- **The backward chain steps to the reversed arrival point of the predecessor.**  If `b'`
scatters into `b` under `S`, then any flight state `k` landing at the reversed departure state of
`b` scatters, under a time reversal `T`, into a flight state based at the reversed arrival point
of `b'`. -/
theorem next_reversed_of_next {S T : BorelEnergyPreservingScattering V}
    (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T) {b' b : V.FlightState}
    (hbdd' : BddAbove (durationSet V b'.edge b'.state)) (hnext : next V S b' = some b)
    (k : V.FlightState) (hke : k.edge = b.edge) (hk : BddAbove (durationSet V k.edge k.state))
    (hend : k.segment.maximalEndpoint hk = (b.state.1, -b.state.2)) :
    ∃ c : V.FlightState, next V T k = some c ∧ c.edge = b'.edge ∧
      c.state = ((b'.segment.maximalEndpoint hbdd').1, -(b'.segment.maximalEndpoint hbdd').2) := by
  obtain ⟨η₀, hη₀, hstate, hsign, hsymm⟩ := exists_departure_of_next S hbdd' hnext
  obtain ⟨c, hc, hce, hcs⟩ :=
    next_of_landing_at_reversedDeparture hST b k hη₀ hstate hsign hke hk hend
  refine ⟨c, hc, ?_, ?_⟩
  · rw [hce, hsymm]
    exact b'.segment.maximalArrivalCovector_germ_fst hbdd' b'.regular
  · rw [hcs, hsymm, maximalEndpoint_eq_of_arrivalCovector b' hbdd']

end FlightState

/-! ### Reversed boundary classes -/

section Classes

variable (V)

/-- The graph point of the reversal of a covector's point is the reversed covector's point. -/
theorem graphPoint_reversePoint_covector (δ : Γ.BoundaryCovector) :
    Γ.graphPoint (Γ.reversePoint
        (δ.germ.1, FiniteMetricGraph.EdgeEnd.coordinate Γ δ.germ, δ.momentum)) =
      δ.momentumReversal.toNonzeroPrequotientPhase Γ :=
  Γ.graphPoint_covector δ.momentumReversal

variable {V}

/-- **The reversed classes of an outgoing covector and of its `S`-preimage agree in `Q(T)`**, for a
time reversal `T` of `S`: `R β` is incoming and `T (R β) = R (S⁻¹ β)`. -/
theorem graphClass_reverse_eq_of_step {S T : BorelEnergyPreservingScattering V}
    (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T) {v : Γ.Vertex}
    (β : Γ.OutgoingBoundary v) :
    graphClass V T (Γ.reversePoint
        (β.1.germ.1, FiniteMetricGraph.EdgeEnd.coordinate Γ β.1.germ, β.1.momentum)) =
      graphClass V T (Γ.reversePoint
        (((S.map v).symm β).1.germ.1,
          FiniteMetricGraph.EdgeEnd.coordinate Γ ((S.map v).symm β).1.germ,
          ((S.map v).symm β).1.momentum)) := by
  unfold graphClass
  rw [graphPoint_reversePoint_covector, graphPoint_reversePoint_covector]
  set γ : Γ.IncomingBoundary v := (Γ.incomingMomentumReversal v).symm β with hγ
  have hγ1 : γ.1 = β.1.momentumReversal := FiniteMetricGraph.BoundaryCovector.ext Γ rfl rfl
  have hT : (T.map v γ).1 = ((S.map v).symm β).1.momentumReversal := by
    rw [hγ, hST v β]
    exact FiniteMetricGraph.BoundaryCovector.ext Γ rfl rfl
  have hstep : scatteringStep (V := V) T (β.1.momentumReversal.toNonzeroPrequotientPhase Γ)
      (((S.map v).symm β).1.momentumReversal.toNonzeroPrequotientPhase Γ) :=
    ⟨v, γ, by rw [hγ1], by rw [hT]⟩
  exact Quotient.sound (Relation.EqvGen.rel _ _ hstep)

/-- The outgoing representative of the reversed class of a scattered state `b = next b'` is the
reversed arrival point of `b'`. -/
theorem rep_reverse_next {S T : BorelEnergyPreservingScattering V}
    (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T) {b' b : V.FlightState}
    (hbdd' : BddAbove (durationSet V b'.edge b'.state)) (hnext : next V S b' = some b) :
    (rep V T (graphClass V T (Γ.reversePoint (b.edge, b.state)))).1.1 = b'.edge ∧
      (rep V T (graphClass V T (Γ.reversePoint (b.edge, b.state)))).1.2.1 =
        ((b'.segment.maximalEndpoint hbdd').1, -(b'.segment.maximalEndpoint hbdd').2) := by
  obtain ⟨b₀, hb₀, hb₀state, -, -, hb₀edge⟩ := next_eq_some_of_bddAbove (V := V) S b' hbdd'
  have hbb : b = b₀ := Option.some.inj (hnext.symm.trans hb₀)
  subst hbb
  set α' := b'.segment.maximalArrivalIncoming hbdd' b'.regular with hα'
  set v := α'.1.germ.vertex with hv
  set β := S.map v α' with hβ
  have hpt : (b.edge, b.state) =
      (β.1.germ.1, FiniteMetricGraph.EdgeEnd.coordinate Γ β.1.germ, β.1.momentum) :=
    Prod.ext hb₀edge hb₀state
  rw [hpt]
  unfold graphClass
  rw [graphPoint_reversePoint_covector, rep_quotientMap]
  set γ : Γ.IncomingBoundary v := (Γ.incomingMomentumReversal v).symm β with hγ
  have hγ1 : γ.1 = β.1.momentumReversal := FiniteMetricGraph.BoundaryCovector.ext Γ rfl rfl
  have hT : (T.map v γ).1 = α'.1.momentumReversal := by
    rw [hγ, hST v β, hβ, (S.map v).symm_apply_apply α']
    exact FiniteMetricGraph.BoundaryCovector.ext Γ rfl rfl
  have hx : IsIncomingPoint (V := V) T (β.1.momentumReversal.toNonzeroPrequotientPhase Γ) :=
    ⟨v, γ, by rw [hγ1]⟩
  have hstep1 := scatteringStep_repOf (V := V) T hx
  have hstep2 : scatteringStep (V := V) T (β.1.momentumReversal.toNonzeroPrequotientPhase Γ)
      (α'.1.momentumReversal.toNonzeroPrequotientPhase Γ) := ⟨v, γ, by rw [hγ1], by rw [hT]⟩
  have hrep := scatteringStep_functional (V := V) T hstep1 hstep2
  rw [hrep]
  refine ⟨?_, ?_⟩
  · change α'.1.germ.1 = b'.edge
    exact b'.segment.maximalArrivalCovector_germ_fst hbdd' b'.regular
  · change (FiniteMetricGraph.EdgeEnd.coordinate Γ α'.1.germ, -α'.1.momentum) = _
    rw [maximalEndpoint_eq_of_arrivalCovector b' hbdd']
    rfl

end Classes

/-! ### The retrace of the forward chain -/

section Retrace

variable [Nonempty Γ.Edge] {S T : BorelEnergyPreservingScattering V}
  (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T)

include hST

/-- **Retrace from an arrival point, within one flight.**  Let `b` be the flight reached at step
`n` of the forward chain of `a`, with finite duration `D`, and let `c` be based at the reversed
arrival point of `b`.  For `0 ≤ w ≤ D` the `T`-trajectory of `c` at time `w` has, in `Q(T)`, the
reversed class of the forward trajectory of `a` at time `impactReal (n+1) - w`. -/
theorem graphClass_trajectory_of_reversedEndpoint_le {n : ℕ} {a b : V.FlightState}
    (hb : iterate V S a n = some b) (hbdd : BddAbove (durationSet V b.edge b.state))
    (c : V.FlightState) (hce : c.edge = b.edge)
    (hcs : c.state = ((b.segment.maximalEndpoint hbdd).1, -(b.segment.maximalEndpoint hbdd).2))
    {w : ℝ} (hw0 : 0 ≤ w) (hwD : w ≤ sSup (durationSet V b.edge b.state)) :
    graphClass V T (trajectory V T c w) =
      graphClass V T (Γ.reversePoint (trajectory V S a (impactReal V S a (n + 1) - w))) := by
  set D := sSup (durationSet V b.edge b.state) with hD
  have hD0 : 0 < D := impactDuration_pos_of_bddAbove (V := V) b hbdd
  obtain ⟨b₁, hb₁, hb₁state, -, -, hb₁edge⟩ := next_eq_some_of_bddAbove (V := V) S b hbdd
  have hsucc : iterate V S a (n + 1) = some b₁ := by rw [iterate_succ, hb]; exact hb₁
  have hsuccS : (iterate V S a (n + 1)).isSome := by rw [hsucc]; rfl
  have himp : impactReal V S a (n + 1) = impactReal V S a n + D :=
    impactReal_succ_eq_of_isSome (V := V) hb hsuccS
  have hnn : 0 ≤ impactReal V S a n := impactReal_nonneg_of_isSome (V := V) (by rw [hb]; rfl)
  rcases eq_or_lt_of_le hw0 with hw_zero | hwpos
  · -- `w = 0`: the impact itself; the reversed classes of `b`'s arrival and of `b₁`'s departure
    -- agree in `Q(T)`.
    rw [← hw_zero, trajectory_zero, sub_zero, trajectory_impactReal S a hsucc]
    set α := b.segment.maximalArrivalIncoming hbdd b.regular with hα
    set v := α.1.germ.vertex with hv
    set β := S.map v α with hβ
    have hL : (c.edge, c.state) = Γ.reversePoint
        (α.1.germ.1, FiniteMetricGraph.EdgeEnd.coordinate Γ α.1.germ, α.1.momentum) := by
      rw [hce, hcs, maximalEndpoint_eq_of_arrivalCovector b hbdd]
      exact Prod.ext (b.segment.maximalArrivalCovector_germ_fst hbdd b.regular).symm rfl
    have hR : (b₁.edge, b₁.state) =
        (β.1.germ.1, FiniteMetricGraph.EdgeEnd.coordinate Γ β.1.germ, β.1.momentum) :=
      Prod.ext hb₁edge hb₁state
    rw [hL, hR, graphClass_reverse_eq_of_step hST β, hβ, (S.map v).symm_apply_apply α]
  · rcases eq_or_lt_of_le hwD with hwD' | hwlt
    · -- `w = D`: the retrace reaches the start of `b`
      rw [himp, hwD', show impactReal V S a n + D - D = impactReal V S a n by ring,
        trajectory_impactReal S a hb]
      rcases interior_or_isOutgoing b with hint | hout
      · have hlong : ∀ _ : BddAbove (durationSet V c.edge c.state),
            D < sSup (durationSet V c.edge c.state) :=
          reversedEndpoint_long_of_interior b c hbdd hce hcs hint
        have hval : flightCurve V c D = (b.state.1, -b.state.2) :=
          flightCurve_of_reversedEndpoint_at_sSup b c hbdd hce hcs hlong
        have hact : ActiveAt V T c 0 D := by
          refine ⟨by rw [iterate_zero]; rfl, by rw [impactReal_zero]; exact hD0.le, fun hs => ?_⟩
          have hcbdd : BddAbove (durationSet V c.edge c.state) := by
            apply bddAbove_of_next_isSome (V := V) (S := T)
            rw [iterate_succ, iterate_zero] at hs
            exact hs
          rw [impactReal_succ_eq_of_isSome (V := V) (iterate_zero V T c) hs, impactReal_zero,
            zero_add]
          exact hlong hcbdd
        rw [trajectory_eq V T c hD0.le hact (iterate_zero V T c), impactReal_zero, sub_zero, hval,
          hce]
        rfl
      · obtain ⟨η₀, hη₀, hstate, hsign⟩ := hout
        obtain ⟨hc, c', hsup, hc', hc'e, hc's⟩ :=
          next_of_reversedEndpoint_of_isOutgoing hST b c hbdd hce hcs hη₀ hstate hsign
        have hsup' : sSup (durationSet V c.edge c.state) = D := hsup
        have hc'1 : iterate V T c 1 = some c' := by rw [iterate_succ, iterate_zero]; exact hc'
        have himpc : impactReal V T c 1 = D := by
          rw [impactReal_succ_eq_of_isSome (V := V) (iterate_zero V T c) (by rw [hc'1]; rfl),
            impactReal_zero, zero_add, hsup']
        rw [← himpc, trajectory_at_impact V T c 0 hc'1]
        have hL : (c'.edge, c'.state) = Γ.reversePoint
            (((S.map η₀.vertex).symm (departureCovector b hsign)).1.germ.1,
              FiniteMetricGraph.EdgeEnd.coordinate Γ
                ((S.map η₀.vertex).symm (departureCovector b hsign)).1.germ,
              ((S.map η₀.vertex).symm (departureCovector b hsign)).1.momentum) :=
          Prod.ext hc'e hc's
        have hR : (b.edge, b.state) = ((departureCovector b hsign).1.germ.1,
            FiniteMetricGraph.EdgeEnd.coordinate Γ (departureCovector b hsign).1.germ,
            (departureCovector b hsign).1.momentum) :=
          Prod.ext hη₀.symm (Prod.ext hstate rfl)
        rw [hL, hR]
        exact (graphClass_reverse_eq_of_step hST (departureCovector b hsign)).symm
    · -- `0 < w < D`: strictly inside the retraced flight
      have hcle : ∀ hc : BddAbove (durationSet V c.edge c.state),
          D ≤ sSup (durationSet V c.edge c.state) :=
        fun hc => sSup_le_of_reversedEndpoint b c hbdd hce hcs hc
      have hact : ActiveAt V T c 0 w := by
        refine ⟨by rw [iterate_zero]; rfl, by rw [impactReal_zero]; exact hw0, fun hs => ?_⟩
        have hcbdd : BddAbove (durationSet V c.edge c.state) := by
          apply bddAbove_of_next_isSome (V := V) (S := T)
          rw [iterate_succ, iterate_zero] at hs
          exact hs
        rw [impactReal_succ_eq_of_isSome (V := V) (iterate_zero V T c) hs, impactReal_zero,
          zero_add]
        exact lt_of_lt_of_le hwlt (hcle hcbdd)
      rw [trajectory_eq V T c hw0 hact (iterate_zero V T c), impactReal_zero, sub_zero,
        flightCurve_of_reversedEndpoint b c hbdd hce hcs hwpos hwlt
          (fun hc => lt_of_lt_of_le hwlt (hcle hc))]
      have hactS : ActiveAt V S a n (impactReal V S a n + (D - w)) := by
        refine ⟨by rw [hb]; rfl, by linarith, fun _ => ?_⟩
        rw [himp]; linarith
      rw [himp, show impactReal V S a n + D - w = impactReal V S a n + (D - w) by ring,
        trajectory_eq V S a (by linarith) hactS hb, add_sub_cancel_left, hce]
      rfl

/-- **Retrace from an arrival point, across all earlier impacts.**  With `b`, `c` as above, for
every `0 ≤ w ≤ impactReal (n+1)` the `T`-trajectory of `c` at time `w` has the reversed class of
the forward trajectory of `a` at time `impactReal (n+1) - w`.  The induction on `n` passes from
flight `n` to flight `n - 1` through the scattering step of the backward chain. -/
theorem graphClass_trajectory_of_reversedEndpoint (n : ℕ) :
    ∀ (a b : V.FlightState), iterate V S a n = some b →
      ∀ (hbdd : BddAbove (durationSet V b.edge b.state)) (c : V.FlightState), c.edge = b.edge →
        c.state = ((b.segment.maximalEndpoint hbdd).1, -(b.segment.maximalEndpoint hbdd).2) →
        ∀ w : ℝ, 0 ≤ w → w ≤ impactReal V S a (n + 1) →
          graphClass V T (trajectory V T c w) =
            graphClass V T (Γ.reversePoint (trajectory V S a (impactReal V S a (n + 1) - w))) := by
  induction n with
  | zero =>
      intro a b hb hbdd c hce hcs w hw0 hw
      have hsuccS : (iterate V S a 1).isSome := by
        rw [iterate_succ, hb]
        obtain ⟨b₁, hb₁, -, -, -, -⟩ := next_eq_some_of_bddAbove (V := V) S b hbdd
        change (next V S b).isSome
        rw [hb₁]; rfl
      have himp : impactReal V S a 1 = impactReal V S a 0 + sSup (durationSet V b.edge b.state) :=
        impactReal_succ_eq_of_isSome (V := V) hb hsuccS
      rw [himp, impactReal_zero, zero_add] at hw
      exact graphClass_trajectory_of_reversedEndpoint_le hST hb hbdd c hce hcs hw0 hw
  | succ m ih =>
      intro a b hb hbdd c hce hcs w hw0 hw
      set D := sSup (durationSet V b.edge b.state) with hD
      by_cases hwD : w ≤ D
      · exact graphClass_trajectory_of_reversedEndpoint_le hST hb hbdd c hce hcs hw0 hwD
      · rw [not_le] at hwD
        obtain ⟨b', hb', hnext⟩ : ∃ b', iterate V S a m = some b' ∧ next V S b' = some b := by
          rw [iterate_succ] at hb
          exact Option.bind_eq_some_iff.mp hb
        have hbdd' : BddAbove (durationSet V b'.edge b'.state) :=
          bddAbove_of_next_isSome (V := V) (S := S) (by rw [hnext]; rfl)
        have hout : b.IsOutgoing := next_isOutgoing (V := V) S hnext
        obtain ⟨hc, hsup, hend⟩ := reversedEndpoint_exact_of_isOutgoing b c hbdd hce hcs hout
        obtain ⟨c', hc', hc'e, hc's⟩ := next_reversed_of_next hST hbdd' hnext c hce hc hend
        have hc'1 : iterate V T c 1 = some c' := by rw [iterate_succ, iterate_zero]; exact hc'
        have himpc : impactReal V T c 1 = D := by
          rw [impactReal_succ_eq_of_isSome (V := V) (iterate_zero V T c) (by rw [hc'1]; rfl),
            impactReal_zero, zero_add, hsup]
        have hshift : trajectory V T c w = trajectory V T c' (w - D) := by
          have h := trajectory_shift_eq V T c hc'1 (w := w - D) (by linarith)
          rwa [himpc, show D + (w - D) = w by ring] at h
        rw [hshift]
        have hsuccS : (iterate V S a (m + 1 + 1)).isSome := by
          rw [iterate_succ, hb]
          obtain ⟨b₁, hb₁, -, -, -, -⟩ := next_eq_some_of_bddAbove (V := V) S b hbdd
          change (next V S b).isSome
          rw [hb₁]; rfl
        have himp : impactReal V S a (m + 1 + 1) = impactReal V S a (m + 1) + D :=
          impactReal_succ_eq_of_isSome (V := V) hb hsuccS
        rw [himp] at hw ⊢
        rw [ih a b' hb' hbdd' c' hc'e hc's (w - D) (by linarith) (by linarith),
          show impactReal V S a (m + 1) - (w - D) = impactReal V S a (m + 1) + D - w by ring]

/-- **Retrace from inside a flight.**  Let `b` be the flight reached at step `n` of the forward
chain of `a`, and `0 < e` a time strictly inside it.  The `T`-trajectory of the backward restart of
`b` at time `e`, evaluated at any `0 ≤ w ≤ impactReal n + e`, has the reversed class of the forward
trajectory of `a` at time `impactReal n + e - w`. -/
theorem graphClass_trajectory_backwardRestart {n : ℕ} {a b : V.FlightState}
    (hb : iterate V S a n = some b) {e : ℝ} (he0 : 0 < e)
    (he : ∀ hbdd : BddAbove (durationSet V b.edge b.state),
      e < sSup (durationSet V b.edge b.state))
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ impactReal V S a n + e) :
    graphClass V T (trajectory V T (backwardRestart V b he0 he) w) =
      graphClass V T (Γ.reversePoint (trajectory V S a (impactReal V S a n + e - w))) := by
  set r := backwardRestart V b he0 he with hr
  have hnn : 0 ≤ impactReal V S a n := impactReal_nonneg_of_isSome (V := V) (by rw [hb]; rfl)
  rcases lt_trichotomy w e with hwe | hwe | hwe
  · -- before the retrace time
    rw [trajectory_backwardRestart_of_lt T b he0 he hw0 hwe]
    have hactS : ActiveAt V S a n (impactReal V S a n + (e - w)) := by
      refine ⟨by rw [hb]; rfl, by linarith, fun hs => ?_⟩
      have hbdd : BddAbove (durationSet V b.edge b.state) := by
        apply bddAbove_of_next_isSome (S := S)
        rw [iterate_succ, hb] at hs
        exact hs
      rw [impactReal_succ_eq_of_isSome (V := V) hb hs]
      have := he hbdd
      linarith
    rw [show impactReal V S a n + e - w = impactReal V S a n + (e - w) by ring,
      trajectory_eq V S a (by linarith) hactS hb, add_sub_cancel_left]
    rfl
  · -- exactly the retrace time: the reversed start of `b`
    subst hwe
    rw [show impactReal V S a n + w - w = impactReal V S a n by ring, trajectory_impactReal S a hb]
    rcases interior_or_isOutgoing b with hint | hout
    · have hlong := backwardRestart_long_of_interior b hint he0 he
      have hact : ActiveAt V T r 0 w := by
        refine ⟨by rw [iterate_zero]; rfl, by rw [impactReal_zero]; exact hw0, fun hs => ?_⟩
        have hrbdd : BddAbove (durationSet V r.edge r.state) := by
          apply bddAbove_of_next_isSome (V := V) (S := T)
          rw [iterate_succ, iterate_zero] at hs
          exact hs
        rw [impactReal_succ_eq_of_isSome (V := V) (iterate_zero V T r) hs, impactReal_zero,
          zero_add]
        exact hlong hrbdd
      rw [trajectory_eq V T r hw0 hact (iterate_zero V T r), impactReal_zero, sub_zero,
        flightCurve_backwardRestart_at_end V b he0 he hlong]
      rfl
    · obtain ⟨η₀, hη₀, hstate, hsign⟩ := hout
      obtain ⟨hrbdd, hrsup⟩ :=
        sSup_durationSet_backwardRestart_eq V b ⟨η₀, hη₀, hstate, hsign⟩ he0 he
      obtain ⟨c', hc', hc'e, hc's⟩ :=
        next_backwardRestart_of_isOutgoing hST b hη₀ hstate hsign he0 he
      have hc'1 : iterate V T r 1 = some c' := by rw [iterate_succ, iterate_zero]; exact hc'
      have himpr : impactReal V T r 1 = w := by
        rw [impactReal_succ_eq_of_isSome (V := V) (iterate_zero V T r) (by rw [hc'1]; rfl),
          impactReal_zero, zero_add, hrsup]
      rw [← himpr, trajectory_at_impact V T r 0 hc'1]
      have hL : (c'.edge, c'.state) = Γ.reversePoint
          (((S.map η₀.vertex).symm (departureCovector b hsign)).1.germ.1,
            FiniteMetricGraph.EdgeEnd.coordinate Γ
              ((S.map η₀.vertex).symm (departureCovector b hsign)).1.germ,
            ((S.map η₀.vertex).symm (departureCovector b hsign)).1.momentum) :=
        Prod.ext hc'e hc's
      have hR : (b.edge, b.state) = ((departureCovector b hsign).1.germ.1,
          FiniteMetricGraph.EdgeEnd.coordinate Γ (departureCovector b hsign).1.germ,
          (departureCovector b hsign).1.momentum) :=
        Prod.ext hη₀.symm (Prod.ext hstate rfl)
      rw [hL, hR]
      exact (graphClass_reverse_eq_of_step hST (departureCovector b hsign)).symm
  · -- past the retrace time: continue through the previous impact
    have hn : n ≠ 0 := by
      rintro rfl
      rw [impactReal_zero, zero_add] at hw
      linarith
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    obtain ⟨b', hb', hnext⟩ : ∃ b', iterate V S a m = some b' ∧ next V S b' = some b := by
      rw [iterate_succ] at hb
      exact Option.bind_eq_some_iff.mp hb
    have hbdd' : BddAbove (durationSet V b'.edge b'.state) :=
      bddAbove_of_next_isSome (V := V) (S := S) (by rw [hnext]; rfl)
    have hout : b.IsOutgoing := next_isOutgoing (V := V) S hnext
    obtain ⟨hrbdd, hrsup⟩ := sSup_durationSet_backwardRestart_eq V b hout he0 he
    obtain ⟨c, hc, hce, hcs⟩ := next_reversed_of_next hST hbdd' hnext r rfl hrbdd
      (maximalEndpoint_backwardRestart_eq V b hout he0 he hrbdd)
    have hc1 : iterate V T r 1 = some c := by rw [iterate_succ, iterate_zero]; exact hc
    have himpr : impactReal V T r 1 = e := by
      rw [impactReal_succ_eq_of_isSome (V := V) (iterate_zero V T r) (by rw [hc1]; rfl),
        impactReal_zero, zero_add, hrsup]
    have hshift : trajectory V T r w = trajectory V T c (w - e) := by
      have h := trajectory_shift_eq V T r hc1 (w := w - e) (by linarith)
      rwa [himpr, show e + (w - e) = w by ring] at h
    rw [hshift, graphClass_trajectory_of_reversedEndpoint hST m a b' hb' hbdd' c hce hcs (w - e)
      (by linarith) (by linarith),
      show impactReal V S a (m + 1) - (w - e) = impactReal V S a (m + 1) + e - w by ring]

end Retrace

/-! ### The backward–forward identity on the quotient -/

section BackwardForward

variable [Nonempty Γ.Edge] {S T : BorelEnergyPreservingScattering V}
  (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T)

include hST

/-- **The backward–forward identity.**  Running the reversed dynamics `T` for a time `w ≤ u` from
the reversal of `Φ⁺_u z` retraces the forward evolution back to time `u - w`:
`Φ⁺_{w,T} (ρ (Φ⁺_{u,S} z)) = ρ (Φ⁺_{u-w,S} z)`. -/
theorem forwardFlow_reverseRegular_forwardFlow (z : RegularScatteringPhaseSpace (V := V) S)
    {u w : ℝ} (hu : 0 ≤ u) (hw0 : 0 ≤ w) (hwu : w ≤ u) :
    forwardFlow V T (reverseRegular hST (forwardFlow V S z u)) w =
      reverseRegular hST (forwardFlow V S z (u - w)) := by
  set a := repFlight V S z with ha
  obtain ⟨n, hact⟩ := exists_activeAt V S a hu
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hact.1
  set e := u - impactReal V S a n with he
  have hnn : 0 ≤ impactReal V S a n := impactReal_nonneg_of_isSome (V := V) hact.1
  have he0 : 0 ≤ e := by rw [he]; linarith [hact.2.1]
  have hu_val : trajectory V S a u = (b.edge, flightCurve V b e) := trajectory_eq V S a hu hact hb
  set c := repFlight V T (reverseRegular hST (forwardFlow V S z u)) with hc
  have hcedge : c.edge = (rep V T (reverseRegular hST (forwardFlow V S z u)).1).1.1 := rfl
  have hcstate : c.state = (rep V T (reverseRegular hST (forwardFlow V S z u)).1).1.2.1 := rfl
  have hrepval : (reverseRegular hST (forwardFlow V S z u)).1 =
      graphClass V T (Γ.reversePoint (trajectory V S a u)) := by
    rw [reverseRegular_val, forwardFlow_val, reverseQuotient_graphClass]
  apply Subtype.ext
  rw [forwardFlow_val, reverseRegular_val, forwardFlow_val, reverseQuotient_graphClass, ← hc]
  rcases eq_or_lt_of_le he0 with he_eq | he_pos
  · -- `u` is the onset of flight `n`
    cases n with
    | zero =>
        have hu0 : u = 0 := by rw [he, impactReal_zero, sub_zero] at he_eq; exact he_eq.symm
        have hw_zero : w = 0 := le_antisymm (hu0 ▸ hwu) hw0
        rw [hw_zero, trajectory_zero, hc,
          graphClass_repFlight V T (reverseRegular hST (forwardFlow V S z u)), hrepval, sub_zero]
    | succ m =>
        obtain ⟨b', hb', hnext⟩ : ∃ b', iterate V S a m = some b' ∧ next V S b' = some b := by
          rw [iterate_succ] at hb
          exact Option.bind_eq_some_iff.mp hb
        have hbdd' : BddAbove (durationSet V b'.edge b'.state) :=
          bddAbove_of_next_isSome (V := V) (S := S) (by rw [hnext]; rfl)
        have hu_imp : u = impactReal V S a (m + 1) := by rw [he] at he_eq; linarith
        have hu_pt : trajectory V S a u = (b.edge, b.state) := by
          rw [hu_imp]; exact trajectory_impactReal S a hb
        obtain ⟨hre, hrs⟩ := rep_reverse_next hST hbdd' hnext (T := T)
        have hce : c.edge = b'.edge := by rw [hcedge, hrepval, hu_pt, hre]
        have hcs : c.state = ((b'.segment.maximalEndpoint hbdd').1,
            -(b'.segment.maximalEndpoint hbdd').2) := by rw [hcstate, hrepval, hu_pt, hrs]
        rw [graphClass_trajectory_of_reversedEndpoint hST m a b' hb' hbdd' c hce hcs w hw0
          (by rw [← hu_imp]; exact hwu), ← hu_imp]
  · -- `u` is strictly inside flight `n`: the reversed point is interior
    have hlift : ∀ hbdd : BddAbove (durationSet V b.edge b.state),
        e < sSup (durationSet V b.edge b.state) :=
      (hact.elapsed_lt (V := V) hb (by rw [he] at he_pos; linarith)).2
    have hint_pt : Γ.reversePoint (trajectory V S a u) =
        (b.edge, ((flightCurve V b e).1, -(flightCurve V b e).2)) := by
      rw [hu_val]; rfl
    have hadm : Γ.AdmissiblePoint (Γ.reversePoint (trajectory V S a u)) :=
      (Γ.admissiblePoint_reversePoint_iff _).mpr (trajectory_admissible S a u)
    have hnotinc : ¬ IsIncomingPoint (V := V) T
        (Γ.graphPoint (Γ.reversePoint (trajectory V S a u))) := by
      rw [isIncomingPoint_graphPoint_iff V T hadm, hint_pt]
      have hint := flightCurve_interior V b he_pos hlift
      rintro (⟨h0, -⟩ | ⟨hl, -⟩)
      · change (flightCurve V b e).1 = 0 at h0
        rw [h0] at hint; exact lt_irrefl _ hint.1
      · change (flightCurve V b e).1 = Γ.length b.edge at hl
        rw [hl] at hint; exact lt_irrefl _ hint.2
    have hrep : rep V T (reverseRegular hST (forwardFlow V S z u)).1 =
        Γ.graphPoint (Γ.reversePoint (trajectory V S a u)) := by
      rw [hrepval]
      exact rep_quotientMap_of_not_incoming V T _ hnotinc
    have hce' : c.edge = (backwardRestart V b he_pos hlift).edge := by
      rw [hcedge, hrep, Γ.graphPoint_edge hadm, hint_pt]; rfl
    have hcs' : c.state = (backwardRestart V b he_pos hlift).state := by
      rw [hcstate, hrep, Γ.graphPoint_state hadm, hint_pt]; rfl
    rw [trajectory_congr V T hce' hcs' hw0,
      graphClass_trajectory_backwardRestart hST hb he_pos hlift hw0 (by rw [he]; linarith),
      show impactReal V S a n + e - w = u - w by rw [he]; ring]

end BackwardForward

/-! ### The inverse identities and the group law -/

section Group

variable (V) (S : BorelEnergyPreservingScattering V) [Nonempty Γ.Edge]

/-- `Φ₋ₜ ∘ Φₜ = id` for `t ≥ 0`. -/
theorem flow_neg_flow (z : RegularScatteringPhaseSpace (V := V) S) {t : ℝ} (ht : 0 ≤ t) :
    flow V S (flow V S z t) (-t) = z := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp
  · rw [flow_of_nonneg V S z ht, flow_of_neg V S _ (by linarith), neg_neg,
      forwardFlow_reverseRegular_forwardFlow
        (BorelEnergyPreservingScattering.isTimeReversal_timeReversed V S) z ht ht le_rfl,
      sub_self, forwardFlow_zero, reverseRegular_reverseRegular]

/-- `Φₜ ∘ Φ₋ₜ = id` for `t ≥ 0`. -/
theorem flow_flow_neg (z : RegularScatteringPhaseSpace (V := V) S) {t : ℝ} (ht : 0 ≤ t) :
    flow V S (flow V S z (-t)) t = z := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp
  · rw [flow_of_neg V S z (by linarith), neg_neg, flow_of_nonneg V S _ ht,
      forwardFlow_reverseRegular_forwardFlow (isTimeReversal_symm_timeReversed V S) _ ht ht le_rfl,
      sub_self, forwardFlow_zero, reverseRegular_reverseRegular]

/-- **`Φ₋ₜ` is the inverse of `Φₜ`**, for every real `t`. -/
theorem flow_flow_neg_self (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ) :
    flow V S (flow V S z t) (-t) = z := by
  rcases le_or_gt 0 t with ht | ht
  · exact flow_neg_flow V S z ht
  · have h := flow_flow_neg V S z (by linarith : 0 ≤ -t)
    rwa [neg_neg] at h

/-- **The group law (3) of the paper**: `Φₜ (Φₛ z) = Φ_{s+t} z` for all real `s, t`. -/
theorem flow_flow (z : RegularScatteringPhaseSpace (V := V) S) (s t : ℝ) :
    flow V S (flow V S z s) t = flow V S z (s + t) := by
  rcases le_or_gt 0 s with hs | hs <;> rcases le_or_gt 0 t with ht | ht
  · exact flow_flow_of_nonneg V S z hs ht
  · rcases le_or_gt 0 (s + t) with hst | hst
    · have h1 : flow V S z s = flow V S (flow V S z (s + t)) (-t) := by
        rw [flow_flow_of_nonneg V S z hst (by linarith), show s + t + -t = s by ring]
      rw [h1]
      have h := flow_flow_neg_self V S (flow V S z (s + t)) (-t)
      rwa [neg_neg] at h
    · have h1 : flow V S (flow V S (flow V S z s) (-s)) (s + t) = flow V S (flow V S z s) t := by
        rw [flow_flow_of_nonpos V S _ (by linarith) hst.le, show -s + (s + t) = t by ring]
      rw [← h1, flow_flow_neg_self V S z s]
  · rcases le_or_gt 0 (s + t) with hst | hst
    · have h1 : flow V S (flow V S (flow V S z s) (-s)) (s + t) = flow V S (flow V S z s) t := by
        rw [flow_flow_of_nonneg V S _ (by linarith) hst, show -s + (s + t) = t by ring]
      rw [← h1, flow_flow_neg_self V S z s]
    · have h1 : flow V S z s = flow V S (flow V S z (s + t)) (-t) := by
        rw [flow_flow_of_nonpos V S z hst.le (by linarith), show s + t + -t = s by ring]
      rw [h1]
      have h := flow_flow_neg_self V S (flow V S z (s + t)) (-t)
      rwa [neg_neg] at h
  · exact flow_flow_of_nonpos V S z hs.le ht.le

/-- The scattered evolution at time `t` as a bijection of the regular quotient phase space, with
inverse `Φ₋ₜ`. -/
noncomputable def flowEquiv (t : ℝ) :
    RegularScatteringPhaseSpace (V := V) S ≃ RegularScatteringPhaseSpace (V := V) S where
  toFun z := flow V S z t
  invFun z := flow V S z (-t)
  left_inv z := flow_flow_neg_self V S z t
  right_inv z := by
    have h := flow_flow_neg_self V S z (-t)
    rwa [neg_neg] at h

@[simp] theorem flowEquiv_apply (t : ℝ) (z : RegularScatteringPhaseSpace (V := V) S) :
    flowEquiv V S t z = flow V S z t := rfl

@[simp] theorem flowEquiv_symm_apply (t : ℝ) (z : RegularScatteringPhaseSpace (V := V) S) :
    (flowEquiv V S t).symm z = flow V S z (-t) := rfl

theorem flow_bijective (t : ℝ) : Function.Bijective (fun z => flow V S z t) :=
  (flowEquiv V S t).bijective

/-- `Φₜ⁻¹ = Φ₋ₜ` as equivalences. -/
theorem flowEquiv_symm (t : ℝ) : (flowEquiv V S t).symm = flowEquiv V S (-t) :=
  Equiv.ext fun _ => rfl

/-- The flow is a one-parameter group: `Φ_{s+t} = Φ_t ∘ Φ_s` as equivalences. -/
theorem flowEquiv_add (s t : ℝ) :
    flowEquiv V S (s + t) = (flowEquiv V S s).trans (flowEquiv V S t) :=
  Equiv.ext fun z => (flow_flow V S z s t).symm

end Group

end MechanicalPotential

end HamiltonianMetricGraphs
