/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3: the flow preserves the measure of the no-impact stratum
-/

import HamiltonianMetricGraphs.OneImpact
import HamiltonianMetricGraphs.NoImpactMeasure

/-!
# The flow preserves the measure of the no-impact stratum

The complement of the one-impact strata of `OneImpact.lean`: the regular points whose outgoing
representative is an interior state of one edge whose flight survives past the time `s`.  On such a
stratum the quotient flow *is* the edge flight map, so Lemma V.1 in the uniform form of
`NoImpactMeasure.lean` (`exists_uniform_measure_image_flightCurve`) gives the invariance directly,
once the stratum and its image are read in the interior coordinates of that one edge.

The two ingredients are `flightCurve_mem_interiorRegular` — a flight is strictly inside its edge
before its impact, so the image points are again interior and are their own representatives — and
`flow_val_of_noImpact`, which identifies the flow with the flight curve at step zero of the chain.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set MeasureTheory PhysicalEdgeSegment

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### A flight is interior before its impact -/

/-- **A flight is strictly inside its edge before its impact.** -/
theorem flightCurve_mem_interiorRegular (a : V.FlightState) {t : ℝ} (ht : 0 < t)
    (hsurv : ∀ _ : BddAbove (durationSet V a.edge a.state),
      t < sSup (durationSet V a.edge a.state)) :
    FlightState.flightCurve V a t ∈ V.interiorRegular a.edge := by
  classical
  refine ⟨?_, ?_⟩
  · by_cases hbdd : BddAbove (durationSet V a.edge a.state)
    · have heq : FlightState.flightCurve V a t = a.segment.maximalCurveClosed hbdd t := by
        unfold FlightState.flightCurve
        rw [dif_pos hbdd]
      rw [heq]
      exact a.segment.maximalCurveClosed_interior hbdd ⟨ht, hsurv hbdd⟩
    · have heq : FlightState.flightCurve V a t = a.segment.unboundedCurve hbdd t := by
        unfold FlightState.flightCurve
        rw [dif_neg hbdd]
      rw [heq]
      exact a.segment.unboundedCurve_interior_at hbdd ht
  · have h := FlightState.flightCurve_hamiltonian_eq V a ht.le (fun hbdd => (hsurv hbdd).le)
    rw [h, FlightState.energy_eq]
    exact a.regular

variable (S : BorelEnergyPreservingScattering V)

/-! ### The no-impact stratum -/

/-- The no-impact stratum at the edge `e`: the regular points with energy in `K` whose outgoing
representative is an interior state of `e` whose flight survives past the time `s`. -/
def noImpactPiece (e : Γ.Edge) (K : Set ℝ) (s : ℝ) :
    Set (RegularScatteringPhaseSpace (V := V) S) :=
  {z | quotientHamiltonian (V := V) S (z : ScatteringPhaseSpace (V := V) S) ∈ K ∧
    (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 = e ∧
    (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 ∈ V.noImpactSet e s}

theorem measurableSet_noImpactPiece (e : Γ.Edge) {K : Set ℝ} (hK : MeasurableSet K)
    {s : ℝ} (hs : 0 < s) : MeasurableSet (V.noImpactPiece S e K s) := by
  classical
  have hpair : Measurable fun z : RegularScatteringPhaseSpace (V := V) S =>
      (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
        (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) :=
    (V.measurable_repPair S).comp measurable_subtype_coe
  have h0 : MeasurableSet {z : RegularScatteringPhaseSpace (V := V) S |
      quotientHamiltonian (V := V) S (z : ScatteringPhaseSpace (V := V) S) ∈ K } :=
    ((measurable_quotientHamiltonian (V := V) S).comp measurable_subtype_coe) hK
  have h1 : MeasurableSet {z : RegularScatteringPhaseSpace (V := V) S |
      (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 = e} :=
    hpair.fst (measurableSet_singleton e)
  have h2 : MeasurableSet {z : RegularScatteringPhaseSpace (V := V) S |
      (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 ∈ V.noImpactSet e s} :=
    hpair.snd (V.measurableSet_noImpactSet e hs)
  exact h0.inter (h1.inter h2)

section Flow

variable [Nonempty Γ.Edge]

/-- **The flow of a no-impact point.**  Before its impact the point flows along its own flight
curve, on the same edge. -/
theorem flow_val_of_noImpact {e : Γ.Edge} {x : ℝ × ℝ} (hx : x ∈ V.interiorRegular e)
    {s : ℝ} (hs : 0 < s)
    (hsurv : ∀ _ : BddAbove (durationSet V e x), s < sSup (durationSet V e x))
    {a : V.FlightState} (hae : a.edge = e) (has : a.state = x)
    {z : RegularScatteringPhaseSpace (V := V) S}
    (hedge : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 = e)
    (hstate : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 = x) :
    (flow V S z s).1 =
      graphClass V S ((e, FlightState.flightCurve V a s) : Γ.Edge × ℝ × ℝ) := by
  classical
  have hs0 : (0 : ℝ) ≤ s := hs.le
  have hsurva : ∀ _ : BddAbove (durationSet V a.edge a.state),
      s < sSup (durationSet V a.edge a.state) := by
    rw [hae, has]
    exact hsurv
  have hact : FlightState.ActiveAt V S a 0 s := by
    refine ⟨by rw [FlightState.iterate_zero]; rfl, ?_, ?_⟩
    · rw [FlightState.impactReal_zero]; exact hs0
    · intro hsucc
      have hbdd : BddAbove (durationSet V a.edge a.state) := by
        refine FlightState.bddAbove_of_next_isSome (V := V) (S := S) ?_
        rw [FlightState.iterate_succ, FlightState.iterate_zero, Option.bind_some] at hsucc
        exact hsucc
      have hir := FlightState.impactReal_succ_eq_of_isSome (V := V)
        (FlightState.iterate_zero (V := V) S a) hsucc
      rw [FlightState.impactReal_zero] at hir
      have h := hsurva hbdd
      linarith
  have htraj := FlightState.trajectory_eq V S a hs0 hact (FlightState.iterate_zero (V := V) S a)
  rw [FlightState.impactReal_zero, sub_zero] at htraj
  rw [V.flow_of_nonneg S z hs0, V.forwardFlow_eq_graphClass S z s]
  have hpair : (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
        (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ)
      = ((e, x) : Γ.Edge × ℝ × ℝ) := Prod.ext hedge hstate
  rw [hpair, V.pointTrajectory_of_interior S (y := ((e, x) : Γ.Edge × ℝ × ℝ)) hx hs0,
    ← V.trajectory_eq_interiorTrajectory S hx hae has hs0, htraj, hae]

/-! ### The no-impact invariance -/

/-- **The flow preserves the measure of the no-impact stratum.**  In the interior coordinates of
the edge the flow is the flight map, which preserves `dq dp` by Lemma V.1. -/
theorem measure_image_flow_noImpactPiece (e : Γ.Edge) (K : Set ℝ) {s : ℝ} (hs : 0 < s)
    (hnoimp : ∀ (W : Set (ℝ × ℝ)) (b : ℝ × ℝ → V.FlightState),
      MeasurableSet W → (∀ x ∈ W, (b x).edge = e) → (∀ x ∈ W, (b x).state = x) →
      (∀ x ∈ W, (b x).energy ∈ K) →
      (∀ x ∈ W, ∀ _ : BddAbove (durationSet V (b x).edge (b x).state),
        s ≤ sSup (durationSet V (b x).edge (b x).state)) →
      volume ((fun x => FlightState.flightCurve V (b x) s) '' W) = volume W)
    {W : Set (RegularScatteringPhaseSpace (V := V) S)} (hWm : MeasurableSet W)
    (hW : W ⊆ V.noImpactPiece S e K s) :
    regularLiouville V S ((fun z => flow V S z s) '' W) = regularLiouville V S W := by
  classical
  have hvalW : MeasurableSet (Subtype.val '' W) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_regularScatteringPhaseSpace V S)).measurableSet_image' hWm
  have hYm : MeasurableSet ((fun z => flow V S z s) '' W) := V.measurableSet_image_flow S s hWm
  have hvalY : MeasurableSet (Subtype.val '' ((fun z => flow V S z s) '' W)) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_regularScatteringPhaseSpace V S)).measurableSet_image' hYm
  set T : Set (ℝ × ℝ) := V.interiorSlice S (Subtype.val '' W) e with hTdef
  set T' : Set (ℝ × ℝ) :=
    V.interiorSlice S (Subtype.val '' ((fun z => flow V S z s) '' W)) e with hT'def
  have hTm : MeasurableSet T := V.measurableSet_interiorSlice S hvalW e
  -- the representative of a point of `W`
  have hzrep : ∀ z ∈ W, (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 ∈ T ∧
      (z : ScatteringPhaseSpace (V := V) S) = graphClass V S ((e,
        (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) := by
    intro z hzW
    obtain ⟨hE, hedge, hnoi⟩ := hW hzW
    have h1 := V.val_eq_graphClass_rep S z
    have hpair : (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
          (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ)
        = ((e, (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) :=
      Prod.ext hedge rfl
    rw [hpair] at h1
    exact ⟨⟨hnoi.1.1, ⟨z, hzW, h1⟩⟩, h1⟩
  -- the slice of `W` is a no-impact set of states of energy in `K`
  have hTsub : ∀ x ∈ T, x ∈ V.noImpactSet e s ∧ V.hamiltonian e x.1 x.2 ∈ K := by
    rintro x ⟨hx1, z, hzW, hzv⟩
    have hadm : Γ.AdmissiblePoint ((e, x) : Γ.Edge × ℝ × ℝ) :=
      ⟨Set.Ioo_subset_Icc_self hx1, Or.inl hx1⟩
    have hxreg : x ∈ V.interiorRegular e := by
      refine ⟨hx1, ?_⟩
      have h : quotientHamiltonian (V := V) S (z : ScatteringPhaseSpace (V := V) S) ∉
        V.exceptionalEnergies := z.2
      rw [hzv, quotientHamiltonian_graphClass V S hadm] at h
      exact h
    have hrep : rep V S (graphClass V S ((e, x) : Γ.Edge × ℝ × ℝ))
        = Γ.graphPoint ((e, x) : Γ.Edge × ℝ × ℝ) := V.rep_interiorClass S hxreg
    have hstate : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 = x := by
      rw [hzv, hrep]
      exact Γ.graphPoint_state hadm
    obtain ⟨hE, -, hnoi⟩ := hW hzW
    rw [hstate] at hnoi
    rw [hzv, quotientHamiltonian_graphClass V S hadm] at hE
    exact ⟨hnoi, hE⟩
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · -- the slice is empty, so both strata are null
    have hWnull : regularLiouville V S W = 0 := by
      rw [V.regularLiouville_eq_volume_interiorSlice S e hWm (fun z hz => (hW hz).2.1), ← hTdef,
        hTe, measure_empty]
    have hYnull : regularLiouville V S ((fun z => flow V S z s) '' W) = 0 := by
      have hempty : W = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro z hzW
        have h := (hzrep z hzW).1
        rw [hTe] at h
        exact h
      rw [hempty]
      simp
    rw [hWnull, hYnull]
  · obtain ⟨x₀, hx₀⟩ := hTne
    have hx₀reg : x₀ ∈ V.interiorRegular e := (hTsub x₀ hx₀).1.1
    obtain ⟨b, hb⟩ : ∃ b : ℝ × ℝ → V.FlightState,
        ∀ x, ∀ h : x ∈ V.interiorRegular e, b x = FlightState.ofInterior V h.1 h.2 := by
      refine ⟨fun x => if h : x ∈ V.interiorRegular e then FlightState.ofInterior V h.1 h.2
        else FlightState.ofInterior V hx₀reg.1 hx₀reg.2, fun x h => ?_⟩
      simp only [dif_pos h]
    have hbe : ∀ x : ℝ × ℝ, x ∈ V.interiorRegular e → (b x).edge = e := by
      intro x h
      simp only [hb x h, FlightState.ofInterior_edge]
    have hbs : ∀ x : ℝ × ℝ, x ∈ V.interiorRegular e → (b x).state = x := by
      intro x h
      simp only [hb x h, FlightState.ofInterior_state]
    -- the image slice is the flight image of the source slice
    have himg : T' = (fun x => FlightState.flightCurve V (b x) s) '' T := by
      apply Subset.antisymm
      · rintro x' ⟨hx'1, y, hyY, hyv⟩
        obtain ⟨z, hzW, rfl⟩ := hyY
        obtain ⟨hTz, hzval⟩ := hzrep z hzW
        obtain ⟨hE, hedge, hnoi⟩ := hW hzW
        have hxreg : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 ∈
            V.interiorRegular e := hnoi.1
        have hflow := V.flow_val_of_noImpact S hxreg hs hnoi.2
          (hbe _ hxreg)
          (hbs _ hxreg) hedge rfl
        have hint : FlightState.flightCurve V
            (b (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) s ∈
            V.interiorRegular e := by
          have h := V.flightCurve_mem_interiorRegular
            (b (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) hs ?_
          · rwa [hbe _ hxreg] at h
          · rw [hbe _ hxreg, hbs _ hxreg]
            exact hnoi.2
        have hx'reg : x' ∈ V.interiorRegular e := by
          refine ⟨hx'1, ?_⟩
          have h : quotientHamiltonian (V := V) S
              ((flow V S z s : RegularScatteringPhaseSpace (V := V) S) :
                ScatteringPhaseSpace (V := V) S) ∉ V.exceptionalEnergies := (flow V S z s).2
          rw [hyv, quotientHamiltonian_graphClass V S
            ⟨Set.Ioo_subset_Icc_self hx'1, Or.inl hx'1⟩] at h
          exact h
        have heq : x' = FlightState.flightCurve V
            (b (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) s := by
          refine V.eq_of_graphClass_eq_interior S hx'reg hint ?_
          rw [← hyv, hflow]
        exact ⟨(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1, hTz, heq.symm⟩
      · rintro x' ⟨x, hxT, rfl⟩
        obtain ⟨hnoi, hE⟩ := hTsub x hxT
        obtain ⟨hx1, z, hzW, hzv⟩ := hxT
        obtain ⟨-, hedge, -⟩ := hW hzW
        have hxreg : x ∈ V.interiorRegular e := hnoi.1
        have hadm : Γ.AdmissiblePoint ((e, x) : Γ.Edge × ℝ × ℝ) :=
          ⟨Set.Ioo_subset_Icc_self hx1, Or.inl hx1⟩
        have hrep : rep V S (graphClass V S ((e, x) : Γ.Edge × ℝ × ℝ))
            = Γ.graphPoint ((e, x) : Γ.Edge × ℝ × ℝ) := V.rep_interiorClass S hxreg
        have hstate : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 = x := by
          rw [hzv, hrep]
          exact Γ.graphPoint_state hadm
        have hflow := V.flow_val_of_noImpact S hxreg hs hnoi.2 (hbe x hxreg) (hbs x hxreg)
          hedge hstate
        have hint : FlightState.flightCurve V (b x) s ∈ V.interiorRegular e := by
          have h := V.flightCurve_mem_interiorRegular (b x) hs ?_
          · rwa [hbe x hxreg] at h
          · rw [hbe x hxreg, hbs x hxreg]
            exact hnoi.2
        exact ⟨hint.1, ⟨flow V S z s, ⟨z, hzW, rfl⟩, hflow⟩⟩
    -- the image points are again their own representatives on the edge `e`
    have hYrep : ∀ y ∈ (fun z => flow V S z s) '' W,
        (rep V S (y : ScatteringPhaseSpace (V := V) S)).1.1 = e := by
      rintro y ⟨z, hzW, rfl⟩
      obtain ⟨hE, hedge, hnoi⟩ := hW hzW
      have hxreg : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 ∈
          V.interiorRegular e := hnoi.1
      have hflow := V.flow_val_of_noImpact S hxreg hs hnoi.2
        (hbe _ hxreg) (hbs _ hxreg) hedge rfl
      have hint : FlightState.flightCurve V
          (b (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) s ∈
          V.interiorRegular e := by
        have h := V.flightCurve_mem_interiorRegular
          (b (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) hs ?_
        · rwa [hbe _ hxreg] at h
        · rw [hbe _ hxreg, hbs _ hxreg]
          exact hnoi.2
      have hadm : Γ.AdmissiblePoint ((e, FlightState.flightCurve V
          (b (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) s) : Γ.Edge × ℝ × ℝ) :=
        ⟨Set.Ioo_subset_Icc_self hint.1, Or.inl hint.1⟩
      have hrep : rep V S (graphClass V S ((e, FlightState.flightCurve V
            (b (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) s) : Γ.Edge × ℝ × ℝ))
          = Γ.graphPoint ((e, FlightState.flightCurve V
            (b (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) s) : Γ.Edge × ℝ × ℝ) :=
        V.rep_interiorClass S hint
      rw [hflow, hrep]
      exact Γ.graphPoint_edge hadm
    rw [V.regularLiouville_eq_volume_interiorSlice S e hYm hYrep,
      V.regularLiouville_eq_volume_interiorSlice S e hWm (fun z hz => (hW hz).2.1),
      ← hTdef, ← hT'def, himg]
    exact hnoimp T b hTm (fun x hx => hbe x (hTsub x hx).1.1)
      (fun x hx => hbs x (hTsub x hx).1.1)
      (fun x hx => by
        rw [FlightState.energy_eq, hbe x (hTsub x hx).1.1, hbs x (hTsub x hx).1.1]
        exact (hTsub x hx).2)
      (fun x hx hbdd => by
        have hbdd' : BddAbove (durationSet V e x) := by
          rw [hbe x (hTsub x hx).1.1, hbs x (hTsub x hx).1.1] at hbdd
          exact hbdd
        have h := (hTsub x hx).1.2 hbdd'
        rw [hbe x (hTsub x hx).1.1, hbs x (hTsub x hx).1.1]
        linarith)

end Flow

end MechanicalPotential

end HamiltonianMetricGraphs
