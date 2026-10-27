/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.BackwardTrajectory

/-!
# Backward retrace from an arrival point

`BackwardTrajectory` retraces a flight *from a point strictly inside it*.  The backward chain also
has to retrace a flight **from its landing point**: after the backward flight of the next flight
arrives at a vertex and is scattered by the time-reversed law, it restarts at the momentum reversal
of the *arrival point* of the previous flight, and from there it must run that previous flight
backwards.

The analytic input is a **landing uniqueness** statement (`flightCurve_eq_of_landing`): two flights
on the same edge with the same finite duration and the same landing point coincide.  This is the
backward form of the Picard–Lindelöf uniqueness (`ODE_solution_unique_of_mem_Icc_left`), applied to
the completed maximal curves, which carry a one-sided derivative at their landing time.

From it, `flightCurve_of_reversedEndpoint` identifies the flight started at the reversed landing
point `R (maximalEndpoint b)` with the reversed flight of `b`, `t ↦ R (flightCurve b (D - t))`:
the flight of the reversed endpoint, restarted at any of its points and reversed again, is a flight
that lands at `maximalEndpoint b` after the same time as the restart of `b` — so by landing
uniqueness the two restarts start at the same point.

The module also introduces the relation `IsTimeReversal S T` (`T ∘ R = R ∘ S⁻¹` on outgoing
covectors), which holds for `T = timeReversed S` and is symmetric, and proves the scattering
steps of the backward chain for *any* such `T`.  This symmetry is what later yields both
inverse identities `Φ₋ₜ ∘ Φₜ = id` and `Φₜ ∘ Φ₋ₜ = id` from a single retrace theorem.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter Topology

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The time-reversal relation between scattering laws -/

namespace BorelEnergyPreservingScattering

/-- `T` is a time reversal of `S`: at every vertex, scattering the momentum reversal of an
outgoing covector with `T` gives the momentum reversal of its `S`-preimage,
`T (R β) = R (S⁻¹ β)`. -/
def IsTimeReversal (S T : BorelEnergyPreservingScattering V) : Prop :=
  ∀ (v : Γ.Vertex) (β : Γ.OutgoingBoundary v),
    T.map v ((Γ.incomingMomentumReversal v).symm β) =
      Γ.incomingMomentumReversal v ((S.map v).symm β)

/-- The time-reversed law of `BorelScattering` is a time reversal. -/
theorem isTimeReversal_timeReversed (S : BorelEnergyPreservingScattering V) :
    IsTimeReversal V S (timeReversed V S) := by
  intro v β
  change (Γ.incomingMomentumReversalMeasurableEquiv v)
      ((S.map v).symm ((Γ.incomingMomentumReversalMeasurableEquiv v)
        ((Γ.incomingMomentumReversal v).symm β))) = _
  have h : (Γ.incomingMomentumReversalMeasurableEquiv v)
      ((Γ.incomingMomentumReversal v).symm β) = β :=
    (Γ.incomingMomentumReversal v).apply_symm_apply β
  rw [h]
  rfl

variable {V}

/-- The time-reversal relation is symmetric: `T ∘ R = R ∘ S⁻¹` implies `S ∘ R = R ∘ T⁻¹`. -/
theorem IsTimeReversal.symm {S T : BorelEnergyPreservingScattering V}
    (h : IsTimeReversal V S T) : IsTimeReversal V T S := by
  intro v β
  set α : Γ.IncomingBoundary v := (T.map v).symm β with hα
  set β' : Γ.OutgoingBoundary v := Γ.incomingMomentumReversal v α with hβ'
  have hαβ' : (Γ.incomingMomentumReversal v).symm β' = α := by
    rw [hβ']; exact (Γ.incomingMomentumReversal v).symm_apply_apply α
  have h1 := h v β'
  rw [hαβ'] at h1
  -- `h1 : T.map v α = R (S⁻¹ β')`, and `T.map v α = β`
  have h2 : (T.map v) α = β := by rw [hα]; exact (T.map v).apply_symm_apply β
  rw [h2] at h1
  -- so `S⁻¹ β' = R⁻¹ β`, hence `S (R⁻¹ β) = β' = R α`
  have h3 : (S.map v).symm β' = (Γ.incomingMomentumReversal v).symm β := by
    rw [h1]; exact ((Γ.incomingMomentumReversal v).symm_apply_apply _).symm
  calc S.map v ((Γ.incomingMomentumReversal v).symm β)
      = S.map v ((S.map v).symm β') := by rw [h3]
    _ = β' := (S.map v).apply_symm_apply β'
    _ = Γ.incomingMomentumReversal v ((T.map v).symm β) := by rw [hβ', hα]

/-- The time-reversal relation in the form used by the backward chain: for an incoming covector
`γ` whose momentum reversal is the outgoing covector `β`, `T γ = R (S⁻¹ β)`. -/
theorem IsTimeReversal.map_of_reversal {S T : BorelEnergyPreservingScattering V}
    (h : IsTimeReversal V S T) {v : Γ.Vertex} {γ : Γ.IncomingBoundary v}
    {β : Γ.OutgoingBoundary v} (hγ : Γ.incomingMomentumReversal v γ = β) :
    T.map v γ = Γ.incomingMomentumReversal v ((S.map v).symm β) := by
  have hγ' : γ = (Γ.incomingMomentumReversal v).symm β := by
    rw [← hγ]; exact ((Γ.incomingMomentumReversal v).symm_apply_apply γ).symm
  rw [hγ']
  exact h v β

end BorelEnergyPreservingScattering

namespace FlightState

open PhysicalEdgeSegment

section

variable {V}

/-- **The flight curve solves the edge Hamiltonian system on the whole closed flight interval**, in
the one-sided `HasDerivWithinAt` sense at the two ends. -/
theorem flightCurve_hasDerivWithinAt_Icc (b : V.FlightState) {D t : ℝ}
    (hDle : ∀ _ : BddAbove (durationSet V b.edge b.state),
      D ≤ sSup (durationSet V b.edge b.state))
    (ht : t ∈ Icc (0 : ℝ) D) :
    HasDerivWithinAt (flightCurve V b) (V.edgeVectorField b.edge (flightCurve V b t))
      (Icc (0 : ℝ) D) t := by
  classical
  by_cases hbdd : BddAbove (durationSet V b.edge b.state)
  · have hfc : flightCurve V b = b.segment.maximalCurveClosed hbdd := by
      unfold flightCurve; rw [dif_pos hbdd]
    rw [hfc]
    exact (b.segment.maximalCurveClosed_hasDerivWithinAt_Icc hbdd
      ⟨ht.1, ht.2.trans (hDle hbdd)⟩).mono (Icc_subset_Icc le_rfl (hDle hbdd))
  · rcases eq_or_lt_of_le ht.1 with h0 | h0
    · -- the initial time: compare with the witnessing segment
      have hfc0 : flightCurve V b 0 = b.state := flightCurve_zero V b
      have hderiv0 : HasDerivAt b.segment.curve (V.edgeVectorField b.edge b.state) 0 := by
        have hd := b.segment.integralCurve 0 ⟨le_rfl, b.segment.duration_pos.le⟩
        rwa [b.segment.initial] at hd
      have heq : flightCurve V b =ᶠ[𝓝[Icc (0 : ℝ) D] 0] b.segment.curve := by
        have hmem : Icc (0 : ℝ) D ∩ Iio b.segment.duration ∈ 𝓝[Icc (0 : ℝ) D] (0 : ℝ) :=
          inter_mem_nhdsWithin _ (Iio_mem_nhds b.segment.duration_pos)
        filter_upwards [hmem] with y hy
        have hy0 : (0 : ℝ) ≤ y := hy.1.1
        have hfcy : flightCurve V b y = b.segment.unboundedCurve hbdd y := by
          unfold flightCurve; rw [dif_neg hbdd]
        rw [hfcy]
        exact b.segment.unboundedCurve_eq_segment_curve hbdd hy0 b.segment hy.2
      subst h0
      rw [hfc0]
      exact (hderiv0.hasDerivWithinAt (s := Icc (0 : ℝ) D)).congr_of_eventuallyEq heq
        (by rw [hfc0, b.segment.initial])
    · exact (flightCurve_hasDerivAt V b h0 (fun hb => absurd hb hbdd)).hasDerivWithinAt

/-- A flight curve is continuous on every closed initial interval of its flight. -/
theorem flightCurve_continuousOn_Icc (b : V.FlightState) {D : ℝ}
    (hDle : ∀ _ : BddAbove (durationSet V b.edge b.state),
      D ≤ sSup (durationSet V b.edge b.state)) :
    ContinuousOn (flightCurve V b) (Icc (0 : ℝ) D) :=
  fun t ht => (flightCurve_hasDerivWithinAt_Icc b hDle ht).continuousWithinAt

/-- At the end of a terminating flight the curve is exactly the maximal endpoint. -/
theorem flightCurve_sSup (b : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) :
    flightCurve V b (sSup (durationSet V b.edge b.state)) = b.segment.maximalEndpoint hbdd := by
  classical
  unfold flightCurve
  rw [dif_pos hbdd]
  exact b.segment.maximalCurveClosed_eq_endpoint hbdd

/-- The one-sided derivative of a terminating flight at its landing time. -/
theorem flightCurve_hasDerivWithinAt_Iic_sSup (b : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) :
    HasDerivWithinAt (flightCurve V b)
      (V.edgeVectorField b.edge (flightCurve V b (sSup (durationSet V b.edge b.state))))
      (Iic (sSup (durationSet V b.edge b.state))) (sSup (durationSet V b.edge b.state)) := by
  classical
  have hfc : flightCurve V b = b.segment.maximalCurveClosed hbdd := by
    unfold flightCurve; rw [dif_pos hbdd]
  rw [hfc, b.segment.maximalCurveClosed_eq_endpoint hbdd]
  exact b.segment.maximalCurveClosed_hasDerivWithinAt_leftEndpoint hbdd

/-- The landing point of a flight is determined by its arrival covector. -/
theorem maximalEndpoint_eq_of_arrivalCovector (b : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) :
    b.segment.maximalEndpoint hbdd =
      (FiniteMetricGraph.EdgeEnd.coordinate Γ
          (b.segment.maximalArrivalCovector hbdd b.regular).germ,
        (b.segment.maximalArrivalCovector hbdd b.regular).momentum) :=
  Prod.ext (b.segment.maximalArrivalCovector_coordinate hbdd b.regular).symm
    (b.segment.maximalArrivalCovector_momentum hbdd b.regular).symm

/-- **Landing uniqueness.**  Two flights on the same edge with the same finite duration and the
same landing point coincide throughout: the edge flow is deterministic backwards in time as well.
In particular they start at the same point. -/
theorem flightCurve_eq_of_landing {k₁ k₂ : V.FlightState} (hedge : k₂.edge = k₁.edge)
    (h₁ : BddAbove (durationSet V k₁.edge k₁.state))
    (h₂ : BddAbove (durationSet V k₂.edge k₂.state))
    (hT : sSup (durationSet V k₁.edge k₁.state) = sSup (durationSet V k₂.edge k₂.state))
    (hend : k₁.segment.maximalEndpoint h₁ = k₂.segment.maximalEndpoint h₂) :
    EqOn (flightCurve V k₁) (flightCurve V k₂)
      (Icc (0 : ℝ) (sSup (durationSet V k₁.edge k₁.state))) := by
  classical
  set T := sSup (durationSet V k₁.edge k₁.state) with hTdef
  obtain ⟨C, hC⟩ := V.exists_lowerBound_extension_closedEdge k₁.edge
  set E : ℝ := k₁.energy with hE
  set P : ℝ := Real.sqrt (2 * (E - C)) with hP
  obtain ⟨K, hK⟩ := V.exists_lipschitzOnWith_edgeVectorField_closedMomentumBox k₁.edge P
  -- both flights carry the energy of the common landing point
  have hE₂ : k₂.energy = E := by
    have hfun : ∀ y : ℝ × ℝ, V.hamiltonian k₂.edge y.1 y.2 = V.hamiltonian k₁.edge y.1 y.2 :=
      fun y => by rw [hedge]
    rw [hE, energy_eq, energy_eq, ← k₂.segment.maximalEndpoint_hamiltonian_eq_initial h₂,
      ← k₁.segment.maximalEndpoint_hamiltonian_eq_initial h₁, hend]
    exact hfun _
  have hT₂ : sSup (durationSet V k₂.edge k₂.state) = T := hT.symm
  -- the two flights land at the same point at the same time
  have hval : flightCurve V k₁ T = flightCurve V k₂ T := by
    have h1 : flightCurve V k₁ T = k₁.segment.maximalEndpoint h₁ := flightCurve_sSup k₁ h₁
    have h2 : flightCurve V k₂ T = k₂.segment.maximalEndpoint h₂ := by
      rw [← hT₂]; exact flightCurve_sSup k₂ h₂
    rw [h1, h2, hend]
  refine ODE_solution_unique_of_mem_Icc_left (v := fun _ => V.edgeVectorField k₁.edge)
    (s := fun _ => closedEdgeMomentumBox k₁.edge P) (K := K) (a := 0) (b := T)
    (f := flightCurve V k₁) (g := flightCurve V k₂) (fun _ _ => hK) ?_ ?_ ?_ ?_ ?_ ?_ hval
  · exact flightCurve_continuousOn_Icc k₁ (fun _ => le_rfl)
  · intro t ht
    rcases eq_or_lt_of_le ht.2 with htT | htT
    · rw [htT]; exact flightCurve_hasDerivWithinAt_Iic_sSup k₁ h₁
    · exact (flightCurve_hasDerivAt V k₁ ht.1 (fun _ => htT)).hasDerivWithinAt
  · intro t ht
    have hphys := flightCurve_physical V k₁ ht.1.le (fun _ => ht.2)
    refine V.mem_closedEdgeMomentumBox_of_hamiltonian_le hphys (hC _ hphys) ?_
    exact (flightCurve_hamiltonian_eq V k₁ ht.1.le (fun _ => ht.2)).le
  · exact flightCurve_continuousOn_Icc k₂ (fun _ => hT₂.ge)
  · intro t ht
    rcases eq_or_lt_of_le ht.2 with htT | htT
    · rw [htT]
      have h := flightCurve_hasDerivWithinAt_Iic_sSup k₂ h₂
      rw [hT₂, hedge] at h
      exact h
    · have h := (flightCurve_hasDerivAt V k₂ ht.1 (fun _ => by rw [hT₂]; exact htT)).hasDerivWithinAt
        (s := Iic t)
      rw [hedge] at h
      exact h
  · intro t ht
    have hphys := flightCurve_physical V k₂ ht.1.le (fun _ => by rw [hT₂]; exact ht.2)
    rw [hedge] at hphys
    refine V.mem_closedEdgeMomentumBox_of_hamiltonian_le hphys (hC _ hphys) ?_
    have h := (flightCurve_hamiltonian_eq V k₂ ht.1.le (fun _ => by rw [hT₂]; exact ht.2))
    rw [hedge, hE₂] at h
    exact h.le

/-! ### The reversed landing point starts the reversed flight -/

/-- A flight state based at the momentum reversal of a landing point departs the arrival germ with
outgoing momentum. -/
theorem isOutgoing_of_reversedEndpoint (b c : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) (hce : c.edge = b.edge)
    (hcs : c.state =
      ((b.segment.maximalEndpoint hbdd).1, -(b.segment.maximalEndpoint hbdd).2)) :
    c.IsOutgoing := by
  refine ⟨(b.segment.maximalArrivalCovector hbdd b.regular).germ, ?_, ?_, ?_⟩
  · rw [hce]; exact b.segment.maximalArrivalCovector_germ_fst hbdd b.regular
  · rw [hcs]; exact (b.segment.maximalArrivalCovector_coordinate hbdd b.regular).symm
  · rw [hcs]
    have hin := (b.segment.maximalArrivalIncoming hbdd b.regular).2.2
    change FiniteMetricGraph.EdgeEnd.sign Γ (b.segment.maximalArrivalCovector hbdd b.regular).germ *
      (b.segment.maximalArrivalCovector hbdd b.regular).momentum > 0 at hin
    rw [b.segment.maximalArrivalCovector_momentum hbdd b.regular] at hin
    rw [mul_neg]
    linarith

/-- **Backward retrace from the landing point.**  The flight started at the reversed landing point
`R (maximalEndpoint b)` runs the flight of `b` backwards with reversed momentum:
`flightCurve c t = R (flightCurve b (D - t))` for `0 < t < D`, as long as `t` is inside the flight
of `c`.  Proof: reverse the flight of `c` at time `t`; it lands at `maximalEndpoint b` after time
`t`, as does the restart of `b` at time `D - t`; landing uniqueness identifies their start
points. -/
theorem flightCurve_of_reversedEndpoint (b c : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) (hce : c.edge = b.edge)
    (hcs : c.state = ((b.segment.maximalEndpoint hbdd).1, -(b.segment.maximalEndpoint hbdd).2))
    {t : ℝ} (ht0 : 0 < t) (htD : t < sSup (durationSet V b.edge b.state))
    (htc : ∀ _ : BddAbove (durationSet V c.edge c.state),
      t < sSup (durationSet V c.edge c.state)) :
    flightCurve V c t =
      ((flightCurve V b (sSup (durationSet V b.edge b.state) - t)).1,
        -(flightCurve V b (sSup (durationSet V b.edge b.state) - t)).2) := by
  classical
  set D := sSup (durationSet V b.edge b.state) with hD
  have hout : c.IsOutgoing := isOutgoing_of_reversedEndpoint b c hbdd hce hcs
  -- the reversal of the flight of `c` at time `t`
  set k₁ := backwardRestart V c ht0 htc with hk₁
  obtain ⟨hk₁bdd, hk₁sup⟩ := sSup_durationSet_backwardRestart_eq V c hout ht0 htc
  have hk₁end : k₁.segment.maximalEndpoint hk₁bdd = (c.state.1, -c.state.2) :=
    maximalEndpoint_backwardRestart_eq V c hout ht0 htc hk₁bdd
  -- the restart of `b` at time `D - t`
  have hDt0 : 0 < D - t := by linarith
  have hDt : D - t < sSup (durationSet V b.edge b.state) := by rw [← hD]; linarith
  set k₂ := restart V b hDt0 (fun _ => hDt) with hk₂
  have hfcs : flightCurve V b (D - t) = b.segment.maximalCurve hbdd (D - t) := by
    unfold flightCurve; rw [dif_pos hbdd]
    exact b.segment.maximalCurveClosed_eq_maximalCurve hbdd hDt
  have hk₂bdd : BddAbove (durationSet V k₂.edge k₂.state) := by
    change BddAbove (durationSet V b.edge (flightCurve V b (D - t)))
    rw [hfcs]
    exact (b.segment.bddAbove_durationSet_maximalCurve_iff hbdd hDt0.le hDt).mpr hbdd
  have hk₂sup : sSup (durationSet V k₂.edge k₂.state) = t := by
    change sSup (durationSet V b.edge (flightCurve V b (D - t))) = t
    rw [hfcs, b.segment.sSup_durationSet_maximalCurve_eq hbdd hDt0.le hDt, ← hD]
    ring
  have hk₂cov : k₂.segment.maximalArrivalCovector hk₂bdd k₂.regular =
      b.segment.maximalArrivalCovector hbdd b.regular :=
    arrivalCovector_restart_eq V b hDt0 hbdd hDt hk₂bdd
  have hk₂end : k₂.segment.maximalEndpoint hk₂bdd = b.segment.maximalEndpoint hbdd := by
    rw [maximalEndpoint_eq_of_arrivalCovector k₂ hk₂bdd, hk₂cov,
      ← maximalEndpoint_eq_of_arrivalCovector b hbdd]
  -- both land at `maximalEndpoint b` after time `t`
  have hedge : k₂.edge = k₁.edge := by change b.edge = c.edge; exact hce.symm
  have hT : sSup (durationSet V k₁.edge k₁.state) = sSup (durationSet V k₂.edge k₂.state) := by
    rw [hk₁sup, hk₂sup]
  have hend : k₁.segment.maximalEndpoint hk₁bdd = k₂.segment.maximalEndpoint hk₂bdd := by
    rw [hk₁end, hk₂end, hcs]
    exact Prod.ext rfl (neg_neg _)
  have key := flightCurve_eq_of_landing hedge hk₁bdd hk₂bdd hT hend
    (show (0 : ℝ) ∈ Icc 0 (sSup (durationSet V k₁.edge k₁.state)) from
      ⟨le_rfl, by rw [hk₁sup]; exact ht0.le⟩)
  rw [flightCurve_zero, flightCurve_zero] at key
  change ((flightCurve V c t).1, -(flightCurve V c t).2) = flightCurve V b (D - t) at key
  rw [← key]
  exact Prod.ext rfl (neg_neg _).symm

/-- The flight from the reversed landing point lasts at least as long as the flight it retraces:
otherwise it would end at a reversed *interior* point of that flight. -/
theorem sSup_le_of_reversedEndpoint (b c : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) (hce : c.edge = b.edge)
    (hcs : c.state = ((b.segment.maximalEndpoint hbdd).1, -(b.segment.maximalEndpoint hbdd).2))
    (hc : BddAbove (durationSet V c.edge c.state)) :
    sSup (durationSet V b.edge b.state) ≤ sSup (durationSet V c.edge c.state) := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  set D := sSup (durationSet V b.edge b.state) with hD
  set Tc := sSup (durationSet V c.edge c.state) with hTc
  have hTc0 : 0 < Tc := impactDuration_pos_of_bddAbove (V := V) c hc
  -- the flight of `c` tends to its landing point
  have h1 : Tendsto (flightCurve V c) (𝓝[<] Tc) (𝓝 (c.segment.maximalEndpoint hc)) := by
    refine (c.segment.tendsto_maximalCurve_maximalEndpoint hc).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hTc0] with w hw
    unfold flightCurve; rw [dif_pos hc]
    exact (c.segment.maximalCurveClosed_eq_maximalCurve hc hw.2).symm
  -- but along the retrace it tends to the reversal of an interior point of `b`
  have h2 : Tendsto (flightCurve V c) (𝓝[<] Tc)
      (𝓝 ((flightCurve V b (D - Tc)).1, -(flightCurve V b (D - Tc)).2)) := by
    have hcont : ContinuousAt (flightCurve V b) (D - Tc) :=
      (flightCurve_hasDerivAt V b (by linarith) (fun _ => by rw [← hD]; linarith)).continuousAt
    have hsub : Tendsto (fun w : ℝ => D - w) (𝓝[<] Tc) (𝓝 (D - Tc)) :=
      ((continuous_const.sub continuous_id).tendsto Tc).mono_left nhdsWithin_le_nhds
    have hR : Continuous (fun y : ℝ × ℝ => (y.1, -y.2)) := by fun_prop
    have hcomp := (hR.tendsto _).comp (hcont.tendsto.comp hsub)
    refine hcomp.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hTc0] with w hw
    exact (flightCurve_of_reversedEndpoint b c hbdd hce hcs hw.1 (by rw [← hD]; linarith [hw.2])
      (fun _ => hw.2)).symm
  have heq := tendsto_nhds_unique h1 h2
  have hint : (c.segment.maximalEndpoint hc).1 ∈ Ioo (0 : ℝ) (Γ.length c.edge) := by
    rw [heq, hce]
    exact flightCurve_interior V b (by linarith) (fun _ => by rw [← hD]; linarith)
  exact c.segment.maximalEndpoint_not_interior hc hint

/-- The retrace from the landing point reaches the reversed start point of `b` at time `D`, as a
limit from the left. -/
theorem tendsto_flightCurve_of_reversedEndpoint (b c : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) (hce : c.edge = b.edge)
    (hcs : c.state = ((b.segment.maximalEndpoint hbdd).1, -(b.segment.maximalEndpoint hbdd).2)) :
    Tendsto (flightCurve V c) (𝓝[<] sSup (durationSet V b.edge b.state))
      (𝓝 (b.state.1, -b.state.2)) := by
  set D := sSup (durationSet V b.edge b.state) with hD
  have hD0 : 0 < D := impactDuration_pos_of_bddAbove (V := V) b hbdd
  have hsub : Tendsto (fun w : ℝ => D - w) (𝓝[<] D) (𝓝[≥] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Tendsto (fun w : ℝ => D - w) (𝓝 D) (𝓝 (D - D)) :=
        (continuous_const.sub continuous_id).tendsto D
      rw [sub_self] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact le_of_lt (sub_pos.mpr (mem_Iio.mp hw))
  have hcomp : Tendsto (fun w : ℝ => flightCurve V b (D - w)) (𝓝[<] D) (𝓝 b.state) :=
    (flightCurve_tendsto_initial V b).comp hsub
  have hR : Continuous (fun y : ℝ × ℝ => (y.1, -y.2)) := by fun_prop
  have hrev : Tendsto (fun w : ℝ => ((flightCurve V b (D - w)).1, -(flightCurve V b (D - w)).2))
      (𝓝[<] D) (𝓝 (b.state.1, -b.state.2)) := by
    simpa [Function.comp_def] using (hR.tendsto b.state).comp hcomp
  refine hrev.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hD0] with w hw
  refine (flightCurve_of_reversedEndpoint b c hbdd hce hcs hw.1 hw.2 (fun hc => ?_)).symm
  exact lt_of_lt_of_le hw.2 (sSup_le_of_reversedEndpoint b c hbdd hce hcs hc)

/-- If the retrace from the landing point outlasts the flight it retraces, it sits at the reversed
start point of `b` at time `D`. -/
theorem flightCurve_of_reversedEndpoint_at_sSup (b c : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) (hce : c.edge = b.edge)
    (hcs : c.state = ((b.segment.maximalEndpoint hbdd).1, -(b.segment.maximalEndpoint hbdd).2))
    (hlong : ∀ _ : BddAbove (durationSet V c.edge c.state),
      sSup (durationSet V b.edge b.state) < sSup (durationSet V c.edge c.state)) :
    flightCurve V c (sSup (durationSet V b.edge b.state)) = (b.state.1, -b.state.2) := by
  have hD0 : 0 < sSup (durationSet V b.edge b.state) := impactDuration_pos_of_bddAbove (V := V) b hbdd
  have hcont : ContinuousAt (flightCurve V c) (sSup (durationSet V b.edge b.state)) :=
    (flightCurve_hasDerivAt V c hD0 hlong).continuousAt
  exact tendsto_nhds_unique hcont.continuousWithinAt.tendsto
    (tendsto_flightCurve_of_reversedEndpoint b c hbdd hce hcs)

/-- If the retrace from the landing point lasts exactly as long as the flight it retraces, it lands
at the reversed start point of `b`. -/
theorem maximalEndpoint_of_reversedEndpoint (b c : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) (hce : c.edge = b.edge)
    (hcs : c.state = ((b.segment.maximalEndpoint hbdd).1, -(b.segment.maximalEndpoint hbdd).2))
    (hc : BddAbove (durationSet V c.edge c.state))
    (hsup : sSup (durationSet V c.edge c.state) = sSup (durationSet V b.edge b.state)) :
    c.segment.maximalEndpoint hc = (b.state.1, -b.state.2) := by
  classical
  have hD0 : 0 < sSup (durationSet V b.edge b.state) := impactDuration_pos_of_bddAbove (V := V) b hbdd
  have h1 : Tendsto (flightCurve V c) (𝓝[<] sSup (durationSet V b.edge b.state))
      (𝓝 (c.segment.maximalEndpoint hc)) := by
    have := c.segment.tendsto_maximalCurve_maximalEndpoint hc
    rw [hsup] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hD0] with w hw
    unfold flightCurve; rw [dif_pos hc]
    exact (c.segment.maximalCurveClosed_eq_maximalCurve hc (by rw [hsup]; exact hw.2)).symm
  exact tendsto_nhds_unique h1 (tendsto_flightCurve_of_reversedEndpoint b c hbdd hce hcs)

/-- The dichotomy for the retrace from the landing point: it either outlasts the retraced flight
or lasts exactly as long. -/
theorem reversedEndpoint_dichotomy (b c : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) (hce : c.edge = b.edge)
    (hcs : c.state = ((b.segment.maximalEndpoint hbdd).1, -(b.segment.maximalEndpoint hbdd).2)) :
    (∀ _ : BddAbove (durationSet V c.edge c.state),
        sSup (durationSet V b.edge b.state) < sSup (durationSet V c.edge c.state)) ∨
      (∃ hc : BddAbove (durationSet V c.edge c.state),
        sSup (durationSet V c.edge c.state) = sSup (durationSet V b.edge b.state)) := by
  by_cases hc : BddAbove (durationSet V c.edge c.state)
  · rcases eq_or_lt_of_le (sSup_le_of_reversedEndpoint b c hbdd hce hcs hc) with h | h
    · exact Or.inr ⟨hc, h.symm⟩
    · exact Or.inl (fun _ => h)
  · exact Or.inl (fun h => absurd h hc)

/-- If `b` starts strictly inside its edge, the retrace from its landing point outlasts it. -/
theorem reversedEndpoint_long_of_interior (b c : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) (hce : c.edge = b.edge)
    (hcs : c.state = ((b.segment.maximalEndpoint hbdd).1, -(b.segment.maximalEndpoint hbdd).2))
    (hint : b.state.1 ∈ Ioo (0 : ℝ) (Γ.length b.edge)) :
    ∀ _ : BddAbove (durationSet V c.edge c.state),
      sSup (durationSet V b.edge b.state) < sSup (durationSet V c.edge c.state) := by
  rcases reversedEndpoint_dichotomy b c hbdd hce hcs with h | ⟨hc, hsup⟩
  · exact h
  · exfalso
    have hend := maximalEndpoint_of_reversedEndpoint b c hbdd hce hcs hc hsup
    apply c.segment.maximalEndpoint_not_interior hc
    rw [hend, hce]
    exact hint

/-- If `b` departs a vertex germ, the retrace from its landing point lasts exactly as long as `b`
and lands at the reversed departure state. -/
theorem reversedEndpoint_exact_of_isOutgoing (b c : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) (hce : c.edge = b.edge)
    (hcs : c.state = ((b.segment.maximalEndpoint hbdd).1, -(b.segment.maximalEndpoint hbdd).2))
    (hout : b.IsOutgoing) :
    ∃ hc : BddAbove (durationSet V c.edge c.state),
      sSup (durationSet V c.edge c.state) = sSup (durationSet V b.edge b.state) ∧
        c.segment.maximalEndpoint hc = (b.state.1, -b.state.2) := by
  rcases reversedEndpoint_dichotomy b c hbdd hce hcs with hlong | ⟨hc, hsup⟩
  · exfalso
    obtain ⟨η₀, hη₀, hstate, -⟩ := hout
    have hval := flightCurve_of_reversedEndpoint_at_sSup b c hbdd hce hcs hlong
    have hint := flightCurve_interior V c (impactDuration_pos_of_bddAbove (V := V) b hbdd) hlong
    rw [hval, hce] at hint
    change b.state.1 ∈ Ioo (0 : ℝ) (Γ.length b.edge) at hint
    rw [hstate] at hint
    unfold FiniteMetricGraph.EdgeEnd.coordinate at hint
    by_cases hη2 : η₀.2
    · rw [if_pos hη2, hη₀] at hint
      exact lt_irrefl _ hint.2
    · rw [if_neg hη2] at hint
      exact lt_irrefl _ hint.1
  · exact ⟨hc, hsup, maximalEndpoint_of_reversedEndpoint b c hbdd hce hcs hc hsup⟩

/-- The arrival covector of a flight landing at a germ coordinate with a given momentum. -/
theorem maximalArrivalCovector_eq_of_endpoint (k : V.FlightState)
    (hk : BddAbove (durationSet V k.edge k.state)) {η₀ : Γ.EdgeEnd} (hη₀ : η₀.1 = k.edge)
    {m : ℝ} (hm : m ≠ 0)
    (hend : k.segment.maximalEndpoint hk = (FiniteMetricGraph.EdgeEnd.coordinate Γ η₀, m)) :
    k.segment.maximalArrivalCovector hk k.regular = ⟨η₀, m, hm⟩ := by
  refine FiniteMetricGraph.BoundaryCovector.ext Γ ?_ ?_
  · change (k.segment.maximalArrivalCovector hk k.regular).germ = η₀
    by_cases hleft : (k.segment.maximalEndpoint hk).1 = 0
    · have hc : FiniteMetricGraph.EdgeEnd.coordinate Γ η₀ = 0 := by
        rw [hend] at hleft; exact hleft
      have hη2 : η₀.2 = false := by
        by_contra hne
        rw [Bool.not_eq_false] at hne
        unfold FiniteMetricGraph.EdgeEnd.coordinate at hc
        rw [if_pos hne] at hc
        exact absurd hc (ne_of_gt (Γ.length_pos η₀.1))
      have : (k.segment.maximalArrivalCovector hk k.regular).germ = (k.edge, false) := by
        simp [PhysicalEdgeSegment.maximalArrivalCovector, hleft]
      rw [this]
      exact Prod.ext hη₀.symm hη2.symm
    · have hc : FiniteMetricGraph.EdgeEnd.coordinate Γ η₀ ≠ 0 := by
        rw [hend] at hleft; exact hleft
      have hη2 : η₀.2 = true := by
        by_contra hne
        rw [Bool.not_eq_true] at hne
        apply hc
        unfold FiniteMetricGraph.EdgeEnd.coordinate
        rw [if_neg (by simp [hne])]
      have : (k.segment.maximalArrivalCovector hk k.regular).germ = (k.edge, true) := by
        simp [PhysicalEdgeSegment.maximalArrivalCovector, hleft]
      rw [this]
      exact Prod.ext hη₀.symm hη2.symm
  · change (k.segment.maximalArrivalCovector hk k.regular).momentum = m
    rw [PhysicalEdgeSegment.maximalArrivalCovector_momentum, hend]

end

/-! ### The scattering step of the backward chain, for a general time reversal -/

section

variable {V}

/-- Transport of a scattering value along an equality of base vertices. -/
private theorem smap_cast (T : BorelEnergyPreservingScattering V) {v v' : Γ.Vertex} (hvv : v = v')
    (γ : Γ.IncomingBoundary v) : (T.map v' (hvv ▸ γ)).1 = (T.map v γ).1 := by
  subst hvv; rfl

private theorem incoming_val_cast {v v' : Γ.Vertex} (hvv : v = v') (γ : Γ.IncomingBoundary v) :
    (hvv ▸ γ).1 = γ.1 := by subst hvv; rfl

/-- The outgoing departure covector of an outgoing flight state. -/
def departureCovector (b : V.FlightState) {η₀ : Γ.EdgeEnd}
    (hsign : FiniteMetricGraph.EdgeEnd.sign Γ η₀ * b.state.2 < 0) :
    Γ.OutgoingBoundary η₀.vertex :=
  ⟨⟨η₀, b.state.2, IsOutgoing.momentum_ne_zero V hsign⟩, rfl, hsign⟩

/-- **The scattering step of a backward chain at a departure germ.**  Let `k` be a flight state
whose flight lands at the momentum reversal of the departure state of an outgoing flight `b`
(departing the germ `η₀`).  Under any time reversal `T` of `S`, the successor of `k` departs the
germ of `S⁻¹ β₀` with reversed momentum, where `β₀` is the departure covector of `b`: it is the
momentum reversal of the state that scattered into `b`. -/
theorem next_of_landing_at_reversedDeparture {S T : BorelEnergyPreservingScattering V}
    (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T) (b k : V.FlightState)
    {η₀ : Γ.EdgeEnd} (hη₀ : η₀.1 = b.edge)
    (hstate : b.state.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ η₀)
    (hsign : FiniteMetricGraph.EdgeEnd.sign Γ η₀ * b.state.2 < 0)
    (hke : k.edge = b.edge) (hk : BddAbove (durationSet V k.edge k.state))
    (hend : k.segment.maximalEndpoint hk = (b.state.1, -b.state.2)) :
    ∃ c : V.FlightState, next V T k = some c ∧
      c.edge = ((S.map η₀.vertex).symm (departureCovector b hsign)).1.germ.1 ∧
      c.state = (FiniteMetricGraph.EdgeEnd.coordinate Γ
          ((S.map η₀.vertex).symm (departureCovector b hsign)).1.germ,
        -((S.map η₀.vertex).symm (departureCovector b hsign)).1.momentum) := by
  classical
  set β₀ := departureCovector b hsign with hβ₀
  -- the arrival covector of `k` is the reversal of the departure covector
  have hcov : k.segment.maximalArrivalCovector hk k.regular =
      ⟨η₀, -b.state.2, neg_ne_zero.mpr (IsOutgoing.momentum_ne_zero V hsign)⟩ := by
    refine maximalArrivalCovector_eq_of_endpoint k hk (hη₀.trans hke.symm) _ ?_
    rw [hend, hstate]
  set γ := k.segment.maximalArrivalIncoming hk k.regular with hγdef
  have hγ1 : γ.1 = ⟨η₀, -b.state.2, neg_ne_zero.mpr (IsOutgoing.momentum_ne_zero V hsign)⟩ := by
    change k.segment.maximalArrivalCovector hk k.regular = _
    exact hcov
  have hv : γ.1.germ.vertex = η₀.vertex := by rw [hγ1]
  have hδ1 : (hv ▸ γ).1 = γ.1 := incoming_val_cast hv γ
  -- reversing the arrival covector returns the departure covector
  have hRδ : Γ.incomingMomentumReversal η₀.vertex (hv ▸ γ) = β₀ := by
    apply Subtype.ext
    refine FiniteMetricGraph.BoundaryCovector.ext Γ ?_ ?_
    · change (hv ▸ γ).1.germ = β₀.1.germ
      rw [hδ1, hγ1]
      rfl
    · change -(hv ▸ γ).1.momentum = β₀.1.momentum
      rw [hδ1, hγ1]
      change - -b.state.2 = b.state.2
      rw [neg_neg]
  have hstarE : T.map η₀.vertex (hv ▸ γ) =
      Γ.incomingMomentumReversal η₀.vertex ((S.map η₀.vertex).symm β₀) :=
    hST.map_of_reversal hRδ
  obtain ⟨c, hc, hcstate, -, -, hcedge⟩ := next_eq_some_of_bddAbove (V := V) T k hk
  have hval : (T.map γ.1.germ.vertex γ).1 =
      (Γ.incomingMomentumReversal η₀.vertex ((S.map η₀.vertex).symm β₀)).1 := by
    rw [← smap_cast T hv γ, hstarE]
  refine ⟨c, hc, ?_, ?_⟩
  · rw [hcedge, hval]; rfl
  · rw [hcstate, hval]; rfl

/-- The scattering step of the backward chain from inside an outgoing flight: the backward flight
of `b` started strictly inside it lands at the reversed departure state, and under a time
reversal `T` of `S` scatters into the reversal of the `S`-preimage of `b`'s departure covector. -/
theorem next_backwardRestart_of_isOutgoing {S T : BorelEnergyPreservingScattering V}
    (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T) (b : V.FlightState)
    {η₀ : Γ.EdgeEnd} (hη₀ : η₀.1 = b.edge)
    (hstate : b.state.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ η₀)
    (hsign : FiniteMetricGraph.EdgeEnd.sign Γ η₀ * b.state.2 < 0) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ hbdd : BddAbove (durationSet V b.edge b.state),
      s < sSup (durationSet V b.edge b.state)) :
    ∃ c : V.FlightState, next V T (backwardRestart V b hs0 hs) = some c ∧
      c.edge = ((S.map η₀.vertex).symm (departureCovector b hsign)).1.germ.1 ∧
      c.state = (FiniteMetricGraph.EdgeEnd.coordinate Γ
          ((S.map η₀.vertex).symm (departureCovector b hsign)).1.germ,
        -((S.map η₀.vertex).symm (departureCovector b hsign)).1.momentum) := by
  have hout : b.IsOutgoing := ⟨η₀, hη₀, hstate, hsign⟩
  obtain ⟨hrbdd, -⟩ := sSup_durationSet_backwardRestart_eq V b hout hs0 hs
  exact next_of_landing_at_reversedDeparture hST b (backwardRestart V b hs0 hs) hη₀ hstate hsign
    rfl hrbdd (maximalEndpoint_backwardRestart_eq V b hout hs0 hs hrbdd)

/-- The scattering step of the backward chain from the landing point of an outgoing flight. -/
theorem next_of_reversedEndpoint_of_isOutgoing {S T : BorelEnergyPreservingScattering V}
    (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T) (b c : V.FlightState)
    (hbdd : BddAbove (durationSet V b.edge b.state)) (hce : c.edge = b.edge)
    (hcs : c.state = ((b.segment.maximalEndpoint hbdd).1, -(b.segment.maximalEndpoint hbdd).2))
    {η₀ : Γ.EdgeEnd} (hη₀ : η₀.1 = b.edge)
    (hstate : b.state.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ η₀)
    (hsign : FiniteMetricGraph.EdgeEnd.sign Γ η₀ * b.state.2 < 0) :
    ∃ (hc : BddAbove (durationSet V c.edge c.state)) (c' : V.FlightState),
      sSup (durationSet V c.edge c.state) = sSup (durationSet V b.edge b.state) ∧
      next V T c = some c' ∧
      c'.edge = ((S.map η₀.vertex).symm (departureCovector b hsign)).1.germ.1 ∧
      c'.state = (FiniteMetricGraph.EdgeEnd.coordinate Γ
          ((S.map η₀.vertex).symm (departureCovector b hsign)).1.germ,
        -((S.map η₀.vertex).symm (departureCovector b hsign)).1.momentum) := by
  obtain ⟨hc, hsup, hend⟩ :=
    reversedEndpoint_exact_of_isOutgoing b c hbdd hce hcs ⟨η₀, hη₀, hstate, hsign⟩
  obtain ⟨c', hc', hce', hcs'⟩ :=
    next_of_landing_at_reversedDeparture hST b c hη₀ hstate hsign hce hc hend
  exact ⟨hc, c', hsup, hc', hce', hcs'⟩

end

end FlightState

end MechanicalPotential

end HamiltonianMetricGraphs
