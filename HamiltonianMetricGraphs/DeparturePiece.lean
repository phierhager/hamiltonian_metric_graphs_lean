/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3: the strata whose representative sits at a vertex
-/

import HamiltonianMetricGraphs.NoImpactPiece

/-!
# The strata whose representative sits at a vertex

A class of the scattering quotient whose outgoing representative sits *at* a vertex is not covered
by the interior strata of `OneImpact.lean` and `NoImpactPiece.lean`.  Such classes form a
one-parameter family — one speed line per germ — so they are Liouville-null, and this module shows
that their images under the flow are null as well, which is all the partition criterion needs.

* `regularLiouville_eq_zero_of_boundary`: a set of classes whose representatives sit at edge
  endpoints is null, because all its interior slices are empty.
* `departurePiece η₀ A`: the classes whose representative is the departure point of the germ `η₀`
  at a speed of `A`.  Its flow image is `{[departure flight of (η₀, r) at time s] : r ∈ A}`, whose
  interior slice is carried by the *single time* `u = s` in the tube chart of `GermTube.lean`,
  hence null.

The same argument disposes of the classes whose first impact happens exactly at the time `s`
(`exactPiece`): those are one-impact states, so the incoming tube chart applies to them, and their
impact time is pinned to the single value `θ = s`; their images sit at a vertex, so the first item
applies to them.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set MeasureTheory PhysicalEdgeSegment
open FiniteMetricGraph.EdgeEnd (coordinate vertex)
open scoped ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-! ### Classes at a vertex are null -/

/-- **A set of classes sitting at edge endpoints is Liouville-null**: all its interior slices are
empty, because an interior point is its own representative. -/
theorem regularLiouville_eq_zero_of_boundary
    {W : Set (RegularScatteringPhaseSpace (V := V) S)} (hWm : MeasurableSet W)
    (hW : ∀ z ∈ W, (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.1 = 0 ∨
      (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.1
        = Γ.length ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1)) :
    regularLiouville V S W = 0 := by
  classical
  rw [V.regularLiouville_eq_tsum_interiorSlice S hWm]
  have hz : ∀ e : Γ.Edge, volume (V.interiorSlice S (Subtype.val '' W) e) = 0 := by
    intro e
    have hempty : V.interiorSlice S (Subtype.val '' W) e = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨hx1, z, hzW, hzv⟩
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
      have hedge : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 = e := by
        rw [hzv, hrep]
        exact Γ.graphPoint_edge hadm
      have hstate : (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 = x := by
        rw [hzv, hrep]
        exact Γ.graphPoint_state hadm
      have h := hW z hzW
      rw [hstate, hedge] at h
      rcases h with h | h
      · exact absurd h (ne_of_gt hx1.1)
      · exact absurd h (ne_of_lt hx1.2)
    rw [hempty, measure_empty]
  rw [tsum_congr hz, tsum_zero]

/-! ### The departure stratum -/

/-- The departure stratum at the germ `η₀`: the classes whose outgoing representative is the
departure point of `η₀` at a speed of `A`. -/
def departurePiece (η₀ : Γ.EdgeEnd) (A : Set ℝ) :
    Set (RegularScatteringPhaseSpace (V := V) S) :=
  {z | (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 = η₀.1 ∧
    (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.1 = coordinate Γ η₀ ∧
    FiniteMetricGraph.EdgeEnd.sign Γ η₀ *
      (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2 < 0 ∧
    |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| ∈ A}

theorem measurableSet_departurePiece (η₀ : Γ.EdgeEnd) {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (V.departurePiece S η₀ A) := by
  classical
  have hpair : Measurable fun z : RegularScatteringPhaseSpace (V := V) S =>
      (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
        (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) :=
    (V.measurable_repPair S).comp measurable_subtype_coe
  have hq : Measurable fun z : RegularScatteringPhaseSpace (V := V) S =>
      (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.1 := hpair.snd.fst
  have hp : Measurable fun z : RegularScatteringPhaseSpace (V := V) S =>
      (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2 := hpair.snd.snd
  have h1 : MeasurableSet {z : RegularScatteringPhaseSpace (V := V) S |
      (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 = η₀.1} :=
    hpair.fst (measurableSet_singleton η₀.1)
  have h2 : MeasurableSet {z : RegularScatteringPhaseSpace (V := V) S |
      (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.1 = coordinate Γ η₀} :=
    hq (measurableSet_singleton _)
  have h3 : MeasurableSet {z : RegularScatteringPhaseSpace (V := V) S |
      FiniteMetricGraph.EdgeEnd.sign Γ η₀ *
        (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2 < 0} :=
    measurableSet_lt (measurable_const.mul hp) measurable_const
  have h4 : MeasurableSet {z : RegularScatteringPhaseSpace (V := V) S |
      |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| ∈ A} := hp.abs hA
  exact h1.inter (h2.inter (h3.inter h4))

/-- The representative of a point of the departure stratum is the departure point of its speed. -/
theorem rep_eq_departurePoint {η₀ : Γ.EdgeEnd} {A : Set ℝ}
    {z : RegularScatteringPhaseSpace (V := V) S} (hz : z ∈ V.departurePiece S η₀ A) :
    (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1
      = departurePoint η₀ |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| := by
  classical
  obtain ⟨-, hpos, hsign, -⟩ := hz
  have h1 : (departurePoint η₀
      |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|).1 = coordinate Γ η₀ := rfl
  have h2 : (departurePoint η₀
        |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|).2
      = -(FiniteMetricGraph.EdgeEnd.sign Γ η₀ *
        |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|) := rfl
  refine Prod.ext ?_ ?_
  · rw [h1]; exact hpos
  · rw [h2]
    by_cases hbo : η₀.2 = true
    · have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η₀ = 1 := by
        simp [FiniteMetricGraph.EdgeEnd.sign, hbo]
      rw [hsgn] at hsign ⊢
      rw [one_mul, abs_of_neg (by linarith), neg_neg]
    · have hbo' : η₀.2 = false := by
        cases h : η₀.2 with
        | false => rfl
        | true => exact absurd h hbo
      have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η₀ = -1 := by
        simp [FiniteMetricGraph.EdgeEnd.sign, hbo']
      rw [hsgn] at hsign ⊢
      rw [abs_of_pos (by linarith)]
      ring

/-- The departure stratum is Liouville-null. -/
theorem regularLiouville_departurePiece_eq_zero (η₀ : Γ.EdgeEnd) {A : Set ℝ}
    {W : Set (RegularScatteringPhaseSpace (V := V) S)} (hWm : MeasurableSet W)
    (hW : W ⊆ V.departurePiece S η₀ A) : regularLiouville V S W = 0 := by
  refine V.regularLiouville_eq_zero_of_boundary S hWm (fun z hz => ?_)
  have hedge := (hW hz).1
  have hpos := (hW hz).2.1
  by_cases hbo : η₀.2 = true
  · refine Or.inr ?_
    rw [hpos, hedge]
    simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo]
  · refine Or.inl ?_
    have hbo' : η₀.2 = false := by
      cases h : η₀.2 with
      | false => rfl
      | true => exact absurd h hbo
    rw [hpos]
    simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo']

section Flow

variable [Nonempty Γ.Edge]

/-- **The flow of a departure point.**  Inside the flow box the class of a departure point flows
along the departure flight of its germ and speed. -/
theorem flow_val_of_departurePiece {η₀ : Γ.EdgeEnd} {A : Set ℝ} {r₁ r₂ δ u₀ : ℝ}
    (hbox : V.GermFlowBox η₀ A r₁ r₂ δ u₀) {s : ℝ} (hs : 0 < s) (hsu : s < u₀)
    {z : RegularScatteringPhaseSpace (V := V) S} (hz : z ∈ V.departurePiece S η₀ A) :
    (flow V S z s).1 = graphClass V S ((η₀.1,
      V.departureFlight η₀ |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| s)
        : Γ.Edge × ℝ × ℝ) := by
  classical
  have hstate := V.rep_eq_departurePoint S hz
  obtain ⟨hedge, hposc, hsign, hrA⟩ := hz
  have hreg : |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| ∈
    V.regularSpeeds η₀ := hbox.regular _ hrA
  have hr0 : (0 : ℝ) ≤ |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| := abs_nonneg _
  have hs0 : (0 : ℝ) ≤ s := hs.le
  set a : V.FlightState := V.ofDeparture η₀ hreg.1 hreg.2 with hadef
  have hlenpos : 0 < Γ.length η₀.1 := Γ.length_pos η₀.1
  -- the representative is not an interior point
  have hnotint : departurePoint η₀ |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| ∉
      V.interiorRegular η₀.1 := by
    intro hcon
    have h : (departurePoint η₀
        |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|).1 = coordinate Γ η₀ := rfl
    have hcon1 : (departurePoint η₀
        |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|).1 ∈
        Ioo (0 : ℝ) (Γ.length η₀.1) := hcon.1
    rw [h] at hcon1
    by_cases hbo : η₀.2 = true
    · have hcoord : coordinate Γ η₀ = Γ.length η₀.1 := by
        simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo]
      rw [hcoord] at hcon1
      exact absurd hcon1.2 (lt_irrefl _)
    · have hbo' : η₀.2 = false := by
        cases h' : η₀.2 with
        | false => rfl
        | true => exact absurd h' hbo
      have hcoord : coordinate Γ η₀ = 0 := by
        simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo']
      rw [hcoord] at hcon1
      exact absurd hcon1.1 (lt_irrefl _)
  -- the germ read off the representative is `η₀`
  have hgerm : pointGerm (Γ := Γ) ((η₀.1,
      departurePoint η₀ |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|)
        : Γ.Edge × ℝ × ℝ) = η₀ := by
    have h : (departurePoint η₀
        |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|).1 = coordinate Γ η₀ := rfl
    by_cases hbo : η₀.2 = true
    · have hcoord : coordinate Γ η₀ = Γ.length η₀.1 := by
        simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo]
      have hne : (departurePoint η₀
          |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|).1 ≠ 0 := by
        rw [h, hcoord]; exact ne_of_gt hlenpos
      unfold pointGerm
      rw [if_neg hne]
      exact Prod.ext rfl hbo.symm
    · have hbo' : η₀.2 = false := by
        cases h' : η₀.2 with
        | false => rfl
        | true => exact absurd h' hbo
      have hcoord : coordinate Γ η₀ = 0 := by
        simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo']
      have heq0 : (departurePoint η₀
          |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|).1 = 0 := by
        rw [h, hcoord]
      unfold pointGerm
      rw [if_pos heq0]
      exact Prod.ext rfl hbo'.symm
  -- the speed read off the representative is its own speed
  have hspeedeq : |(departurePoint η₀
        |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|).2|
      = |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| := by
    have h2 : (departurePoint η₀
          |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|).2
        = -(FiniteMetricGraph.EdgeEnd.sign Γ η₀ *
          |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|) := rfl
    rw [h2, abs_neg, abs_mul, abs_edgeEnd_sign, one_mul, abs_abs]
  -- the chain is at step zero
  have hact : FlightState.ActiveAt V S a 0 s := by
    refine ⟨by rw [FlightState.iterate_zero]; rfl, ?_, ?_⟩
    · rw [FlightState.impactReal_zero]; exact hs0
    · intro hsucc
      have hbdd : BddAbove (durationSet V a.edge a.state) := by
        refine FlightState.bddAbove_of_next_isSome (V := V) (S := S) ?_
        rw [FlightState.iterate_succ, FlightState.iterate_zero, Option.bind_some] at hsucc
        exact hsucc
      have hdu : u₀ ≤ sSup (durationSet V a.edge a.state) := hbox.duration _ hrA hbdd
      have hir := FlightState.impactReal_succ_eq_of_isSome (V := V)
        (FlightState.iterate_zero (V := V) S a) hsucc
      rw [FlightState.impactReal_zero] at hir
      linarith
  have htraj := FlightState.trajectory_eq V S a hs0 hact (FlightState.iterate_zero (V := V) S a)
  rw [FlightState.impactReal_zero, sub_zero] at htraj
  rw [V.flow_of_nonneg S z hs0, V.forwardFlow_eq_graphClass S z s]
  have hpair : (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
        (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ)
      = ((η₀.1, departurePoint η₀
        |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|) : Γ.Edge × ℝ × ℝ) :=
    Prod.ext hedge hstate
  rw [hpair, V.pointTrajectory_of_not_interior S
      (y := ((η₀.1, departurePoint η₀
        |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2|) : Γ.Edge × ℝ × ℝ))
      hnotint hs0, hgerm, hspeedeq, V.departureTrajectory_of_mem S hreg, htraj,
    ← V.departureFlight_of_mem hreg]
  rfl

/-- **The image of the departure stratum is Liouville-null.**  In the tube chart of the germ the
image sits at the single time `u = s`, which is Lebesgue-null in the time variable. -/
theorem measure_image_flow_departurePiece (η₀ : Γ.EdgeEnd) {A : Set ℝ} (hA : MeasurableSet A)
    {r₁ r₂ δ u₀ s : ℝ} (hbox : V.GermFlowBox η₀ A r₁ r₂ δ u₀)
    (hlen : δ < Γ.length η₀.1 / 2) (hs : 0 < s) (h2s : 2 * s ≤ u₀)
    {W : Set (RegularScatteringPhaseSpace (V := V) S)} (hWm : MeasurableSet W)
    (hW : W ⊆ V.departurePiece S η₀ A) :
    regularLiouville V S ((fun z => flow V S z s) '' W) = regularLiouville V S W := by
  classical
  have hsu : s < u₀ := by linarith
  have hsu' : s ≤ u₀ := le_of_lt hsu
  have hYm : MeasurableSet ((fun z => flow V S z s) '' W) := V.measurableSet_image_flow S s hWm
  have hvalY : MeasurableSet (Subtype.val '' ((fun z => flow V S z s) '' W)) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_regularScatteringPhaseSpace V S)).measurableSet_image' hYm
  set T' : Set (ℝ × ℝ) :=
    V.interiorSlice S (Subtype.val '' ((fun z => flow V S z s) '' W)) η₀.1 with hT'def
  have hT'm : MeasurableSet T' := V.measurableSet_interiorSlice S hvalY η₀.1
  have hsmem : s ∈ Ioo (0 : ℝ) u₀ := ⟨hs, hsu⟩
  -- every point of the image slice is the departure flight at the single time `s`
  have hT'char : ∀ x' ∈ T', ∃ r ∈ A, x' = V.departureFlight η₀ r s := by
    intro x' hx'
    obtain ⟨y, hyY, hyv⟩ := hx'.2
    obtain ⟨z, hzW, rfl⟩ := hyY
    have hrA := (hW hzW).2.2.2
    have hflow := V.flow_val_of_departurePiece S hbox hs hsu (hW hzW)
    have hint : V.departureFlight η₀
        |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| s ∈
        V.interiorRegular η₀.1 :=
      V.departureFlight_mem_interiorRegular η₀ hbox hlen hrA hsmem
    have hx'reg : x' ∈ V.interiorRegular η₀.1 := by
      refine ⟨hx'.1, ?_⟩
      have h : quotientHamiltonian (V := V) S
          ((flow V S z s : RegularScatteringPhaseSpace (V := V) S) :
            ScatteringPhaseSpace (V := V) S) ∉ V.exceptionalEnergies := (flow V S z s).2
      rw [hyv, quotientHamiltonian_graphClass V S
        ⟨Set.Ioo_subset_Icc_self hx'.1, Or.inl hx'.1⟩] at h
      exact h
    refine ⟨_, hrA, ?_⟩
    refine V.eq_of_graphClass_eq_interior S hx'reg hint ?_
    rw [← hyv, hflow]
  have hT'tube : T' ⊆ V.germTube η₀ A δ (2 * s) := by
    intro x' hx'
    obtain ⟨r, hrA, rfl⟩ := hT'char x' hx'
    exact V.departureFlight_mem_germTube η₀ hbox hrA h2s ⟨hs, by linarith⟩
  -- the image measure in the tube chart
  have hvolT' : volume T' = ∫⁻ r in A, ENNReal.ofReal r *
      ∫⁻ u in Ioo (0 : ℝ) (2 * s), T'.indicator (fun _ => (1 : ℝ≥0∞))
        (V.departureFlight η₀ r u) := by
    rw [← setLIntegral_one T']
    exact V.lintegral_germTube η₀ hA hbox h2s hT'm hT'tube measurable_const
  have hinner : ∀ r ∈ A,
      ∫⁻ u in Ioo (0 : ℝ) (2 * s), T'.indicator (fun _ => (1 : ℝ≥0∞))
        (V.departureFlight η₀ r u) = 0 := by
    intro r hrA
    have hvan : ∀ u ∈ Ioo (0 : ℝ) (2 * s),
        T'.indicator (fun _ => (1 : ℝ≥0∞)) (V.departureFlight η₀ r u)
          = ({s} : Set ℝ).indicator (fun u => T'.indicator (fun _ => (1 : ℝ≥0∞))
            (V.departureFlight η₀ r u)) u := by
      intro u hu
      by_cases hus : u = s
      · have hmem : u ∈ ({s} : Set ℝ) := hus
        rw [Set.indicator_of_mem hmem]
      · have hnmem : u ∉ ({s} : Set ℝ) := hus
        have hnT : V.departureFlight η₀ r u ∉ T' := by
          intro hcon
          obtain ⟨r', hr'A, heq⟩ := hT'char _ hcon
          obtain ⟨-, hus'⟩ := V.departureFlight_inj hbox hrA hr'A
            ⟨hu.1.le, by linarith [hu.2]⟩ ⟨hs.le, hsu'⟩ heq
          exact hus hus'
        rw [Set.indicator_of_notMem hnT, Set.indicator_of_notMem hnmem]
    rw [setLIntegral_congr_fun measurableSet_Ioo hvan,
      lintegral_indicator (measurableSet_singleton s),
      Measure.restrict_restrict (measurableSet_singleton s)]
    have hnull : (volume : Measure ℝ) ({s} ∩ Ioo (0 : ℝ) (2 * s)) = 0 :=
      measure_mono_null inter_subset_left (measure_singleton s)
    rw [Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]
  -- both sides vanish
  have hYnull : regularLiouville V S ((fun z => flow V S z s) '' W) = 0 := by
    have hedgeY : ∀ y ∈ (fun z => flow V S z s) '' W,
        (rep V S (y : ScatteringPhaseSpace (V := V) S)).1.1 = η₀.1 := by
      rintro y ⟨z, hzW, rfl⟩
      have hrA := (hW hzW).2.2.2
      have hflow := V.flow_val_of_departurePiece S hbox hs hsu (hW hzW)
      have hint : V.departureFlight η₀
          |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| s ∈
          V.interiorRegular η₀.1 :=
        V.departureFlight_mem_interiorRegular η₀ hbox hlen hrA hsmem
      have hadm : Γ.AdmissiblePoint ((η₀.1, V.departureFlight η₀
          |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| s) : Γ.Edge × ℝ × ℝ) :=
        ⟨Set.Ioo_subset_Icc_self hint.1, Or.inl hint.1⟩
      have hrep : rep V S (graphClass V S ((η₀.1, V.departureFlight η₀
            |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| s) : Γ.Edge × ℝ × ℝ))
          = Γ.graphPoint ((η₀.1, V.departureFlight η₀
            |(rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1.2| s) : Γ.Edge × ℝ × ℝ) :=
        V.rep_interiorClass S hint
      rw [hflow, hrep]
      exact Γ.graphPoint_edge hadm
    rw [V.regularLiouville_eq_volume_interiorSlice S η₀.1 hYm hedgeY, ← hT'def, hvolT',
      setLIntegral_congr_fun hA (fun r hr => by rw [hinner r hr, mul_zero])]
    simp
  rw [hYnull, V.regularLiouville_departurePiece_eq_zero S η₀ hWm hW]

end Flow

end MechanicalPotential

end HamiltonianMetricGraphs
