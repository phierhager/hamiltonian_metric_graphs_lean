/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3: the stratum whose impact happens exactly at the end of the step
-/

import HamiltonianMetricGraphs.DeparturePiece

/-!
# The stratum whose impact happens exactly at the end of the step

The last stratum of the partition of Lemma VI.3: the classes whose first impact happens exactly at
the time `s`.  These are one-impact states, so the incoming tube chart of `GermTube.lean` applies
to them; but their impact time is pinned to the single value `θ = s`, which is Lebesgue-null in the
time variable of the chart, so the stratum is Liouville-null.  Their images sit *at* a vertex — the
flow moves them onto the departure point of the scattered germ — so they are null as well by
`regularLiouville_eq_zero_of_boundary`.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set MeasureTheory PhysicalEdgeSegment
open FiniteMetricGraph.EdgeEnd (coordinate vertex)
open scoped ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-! ### Reading the representative off an interior slice -/

/-- A point of an interior slice is the outgoing representative of one of the classes of the set. -/
theorem interiorSlice_rep {W : Set (RegularScatteringPhaseSpace (V := V) S)} {e : Γ.Edge}
    {x : ℝ × ℝ} (hx : x ∈ V.interiorSlice S (Subtype.val '' W) e) :
    ∃ z ∈ W, (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1 = e ∧
      (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 = x ∧
      x ∈ V.interiorRegular e := by
  obtain ⟨hx1, z, hzW, hzv⟩ := hx
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
  refine ⟨z, hzW, ?_, ?_, hxreg⟩
  · rw [hzv, hrep]
    exact Γ.graphPoint_edge hadm
  · rw [hzv, hrep]
    exact Γ.graphPoint_state hadm

/-! ### The stratum of the impacts at the end of the step -/

/-- The classes whose first impact happens exactly at the time `s`, lands at the germ `η` and
scatters into the germ `η'` with a speed of `A`. -/
def exactPiece (η η' : Γ.EdgeEnd) (A : Set ℝ) (s : ℝ) :
    Set (RegularScatteringPhaseSpace (V := V) S) :=
  V.impactPiece S η η' A (2 * s) ∩
    {z | V.interiorDurationTotal η.1
      ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) = s}

theorem measurableSet_exactPiece (η η' : Γ.EdgeEnd) {A : Set ℝ} (hA : MeasurableSet A)
    (s : ℝ) : MeasurableSet (V.exactPiece S η η' A s) := by
  classical
  have hpair : Measurable fun z : RegularScatteringPhaseSpace (V := V) S =>
      (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
        (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) :=
    (V.measurable_repPair S).comp measurable_subtype_coe
  have h2 : MeasurableSet {z : RegularScatteringPhaseSpace (V := V) S |
      V.interiorDurationTotal η.1
        ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) = s} :=
    ((V.measurable_interiorDurationTotal η.1).comp hpair.snd) (measurableSet_singleton s)
  exact (V.measurableSet_impactPiece S η η' hA (2 * s)).inter h2

section Flow

variable [Nonempty Γ.Edge]

/-- **The stratum of the impacts at the end of the step is Liouville-null.**  In the incoming tube
chart of the germ its impact time is pinned to `θ = s`. -/
theorem regularLiouville_exactPiece_eq_zero {η η' : Γ.EdgeEnd} {A : Set ℝ}
    (hA : MeasurableSet A) {r₁ r₂ δ u₀ s : ℝ} (hbox : V.GermFlowBox η A r₁ r₂ δ u₀)
    (hs : 0 < s) (h2s : 2 * s ≤ u₀)
    {W : Set (RegularScatteringPhaseSpace (V := V) S)} (hWm : MeasurableSet W)
    (hW : W ⊆ V.exactPiece S η η' A s) : regularLiouville V S W = 0 := by
  classical
  have hvalW : MeasurableSet (Subtype.val '' W) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_regularScatteringPhaseSpace V S)).measurableSet_image' hWm
  set T : Set (ℝ × ℝ) := V.interiorSlice S (Subtype.val '' W) η.1 with hTdef
  have hTm : MeasurableSet T := V.measurableSet_interiorSlice S hvalW η.1
  have hTchar : ∀ x ∈ T, x ∈ V.impactSlice S η η' A (2 * s) ∧
      V.interiorDurationTotal η.1 x = s := by
    intro x hx
    obtain ⟨z, hzW, -, hstate, -⟩ := V.interiorSlice_rep S hx
    obtain ⟨hpiece, hexact⟩ := hW hzW
    have hexact' : V.interiorDurationTotal η.1
        ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) = s := hexact
    have h1 := hpiece.2
    rw [hstate] at h1 hexact'
    exact ⟨h1, hexact'⟩
  have hTtube : T ⊆ V.germTubeIn η A δ (2 * s) := by
    intro x hx
    have hxs := (hTchar x hx).1
    have hkey := V.departureFlight_impactSlice S hbox h2s hxs
    have hmem := V.departureFlight_mem_germTube η hbox hxs.2.2.2.2 h2s hxs.2.1
    rw [hkey] at hmem
    exact hmem
  have hvolT : volume T = ∫⁻ r in A, ENNReal.ofReal r *
      ∫⁻ θ in Ioo (0 : ℝ) (2 * s), T.indicator (fun _ => (1 : ℝ≥0∞))
        (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) (V.departureFlight η r θ)) := by
    rw [← setLIntegral_one T]
    exact V.lintegral_germTubeIn η hA hbox h2s hTm hTtube measurable_const
  have hinner : ∀ r ∈ A,
      ∫⁻ θ in Ioo (0 : ℝ) (2 * s), T.indicator (fun _ => (1 : ℝ≥0∞))
        (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) (V.departureFlight η r θ)) = 0 := by
    intro r hrA
    have hvan : ∀ θ ∈ Ioo (0 : ℝ) (2 * s),
        T.indicator (fun _ => (1 : ℝ≥0∞))
            (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) (V.departureFlight η r θ))
          = ({s} : Set ℝ).indicator (fun θ => T.indicator (fun _ => (1 : ℝ≥0∞))
            (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) (V.departureFlight η r θ))) θ := by
      intro θ hθ
      by_cases hθs : θ = s
      · have hmem : θ ∈ ({s} : Set ℝ) := hθs
        rw [Set.indicator_of_mem hmem]
      · have hnmem : θ ∉ ({s} : Set ℝ) := hθs
        have hnT : Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)
            (V.departureFlight η r θ) ∉ T := by
          intro hcon
          obtain ⟨hcs1, hcs2⟩ := hTchar _ hcon
          have hretr := V.departureFlight_impactSlice S hbox h2s hcs1
          have hxx : ((Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)
                (V.departureFlight η r θ)).1,
              -(Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)
                (V.departureFlight η r θ)).2) = V.departureFlight η r θ :=
            Prod.ext rfl (neg_neg _)
          rw [hxx] at hretr
          obtain ⟨-, hθθ⟩ := V.departureFlight_inj hbox hcs1.2.2.2.2 hrA
            ⟨V.interiorDurationTotal_nonneg _ _, le_trans hcs1.2.1.2.le h2s⟩
            ⟨hθ.1.le, le_trans hθ.2.le h2s⟩ hretr
          rw [hcs2] at hθθ
          exact hθs hθθ.symm
        rw [Set.indicator_of_notMem hnT, Set.indicator_of_notMem hnmem]
    rw [setLIntegral_congr_fun measurableSet_Ioo hvan,
      lintegral_indicator (measurableSet_singleton s),
      Measure.restrict_restrict (measurableSet_singleton s)]
    have hnull : (volume : Measure ℝ) ({s} ∩ Ioo (0 : ℝ) (2 * s)) = 0 :=
      measure_mono_null inter_subset_left (measure_singleton s)
    rw [Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]
  rw [V.regularLiouville_impactPiece_eq S hWm (fun z hz => (hW hz).1), ← hTdef, hvolT,
    setLIntegral_congr_fun hA (fun r hr => by rw [hinner r hr, mul_zero])]
  simp

/-- **The image of the stratum of the impacts at the end of the step is Liouville-null.**  The flow
carries such a class onto the departure point of the scattered germ, which sits at a vertex. -/
theorem measure_image_flow_exactPiece {η η' : Γ.EdgeEnd} {A : Set ℝ} (hA : MeasurableSet A)
    {r₁ r₂ δ u₀ s : ℝ} (hbox : V.GermFlowBox η A r₁ r₂ δ u₀)
    (hbox' : V.GermFlowBox η' A r₁ r₂ δ u₀) (hs : 0 < s) (h2s : 2 * s ≤ u₀)
    {W : Set (RegularScatteringPhaseSpace (V := V) S)} (hWm : MeasurableSet W)
    (hW : W ⊆ V.exactPiece S η η' A s) :
    regularLiouville V S ((fun z => flow V S z s) '' W) = regularLiouville V S W := by
  classical
  have hYnull : regularLiouville V S ((fun z => flow V S z s) '' W) = 0 := by
    refine V.regularLiouville_eq_zero_of_boundary S (V.measurableSet_image_flow S s hWm) ?_
    rintro y ⟨z, hzW, rfl⟩
    obtain ⟨hpiece, hexact⟩ := hW hzW
    have hexact' : V.interiorDurationTotal η.1
        ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) = s := hexact
    have hrA : (interiorStep V S η.1
        ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2 ∈ A := hpiece.2.2.2.2.2
    have hrpos : 0 < (interiorStep V S η.1
        ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2 :=
      lt_trans hbox.speed_pos (hbox.speeds hrA).1
    have hflow := V.flow_val_of_impactPiece S hbox' h2s hpiece (t := s)
      (le_of_eq hexact') (by linarith)
    rw [hexact', sub_self, V.departureFlight_zero] at hflow
    -- the departure point is an outgoing boundary point, hence its own representative
    have hne : (departurePoint η' (interiorStep V S η.1
        ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2).2 ≠ 0 := by
      have h2 : (departurePoint η' (interiorStep V S η.1
              ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2).2
          = -(FiniteMetricGraph.EdgeEnd.sign Γ η' * (interiorStep V S η.1
            ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2) := rfl
      rw [h2]
      have habs : |FiniteMetricGraph.EdgeEnd.sign Γ η' * (interiorStep V S η.1
          ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2|
          = (interiorStep V S η.1
            ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2 := by
        rw [abs_mul, abs_edgeEnd_sign, one_mul, abs_of_pos hrpos]
      intro hcon
      rw [neg_eq_zero] at hcon
      rw [hcon, abs_zero] at habs
      exact absurd habs.symm (ne_of_gt hrpos)
    have hadm : Γ.AdmissiblePoint ((η'.1, departurePoint η' (interiorStep V S η.1
        ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2) : Γ.Edge × ℝ × ℝ) :=
      ⟨Γ.edgeEnd_coordinate_mem_closedEdge η', Or.inr hne⟩
    have hnotin : ¬ IsIncomingPoint (V := V) S (Γ.graphPoint ((η'.1,
        departurePoint η' (interiorStep V S η.1
          ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2) : Γ.Edge × ℝ × ℝ)) := by
      rw [isIncomingPoint_graphPoint_iff V S hadm]
      have hq : (departurePoint η' (interiorStep V S η.1
          ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2).1
          = coordinate Γ η' := rfl
      have hp : (departurePoint η' (interiorStep V S η.1
              ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2).2
          = -(FiniteMetricGraph.EdgeEnd.sign Γ η' * (interiorStep V S η.1
            ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2) := rfl
      have hlenpos : 0 < Γ.length η'.1 := Γ.length_pos η'.1
      by_cases hbo : η'.2 = true
      · have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η' = 1 := by
          simp [FiniteMetricGraph.EdgeEnd.sign, hbo]
        have hcoord : coordinate Γ η' = Γ.length η'.1 := by
          simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo]
        rintro (⟨h0, -⟩ | ⟨-, hpp⟩)
        · rw [hq, hcoord] at h0
          exact absurd h0 (ne_of_gt hlenpos)
        · rw [hp, hsgn, one_mul] at hpp
          linarith
      · have hbo' : η'.2 = false := by
          cases h : η'.2 with
          | false => rfl
          | true => exact absurd h hbo
        have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η' = -1 := by
          simp [FiniteMetricGraph.EdgeEnd.sign, hbo']
        have hcoord : coordinate Γ η' = 0 := by
          simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo']
        rintro (⟨-, hpn⟩ | ⟨hl, -⟩)
        · rw [hp, hsgn] at hpn
          linarith
        · rw [hq, hcoord] at hl
          exact absurd hl.symm (ne_of_gt hlenpos)
    have hrep : rep V S (graphClass V S ((η'.1, departurePoint η' (interiorStep V S η.1
          ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2) : Γ.Edge × ℝ × ℝ))
        = Γ.graphPoint ((η'.1, departurePoint η' (interiorStep V S η.1
          ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2) : Γ.Edge × ℝ × ℝ) :=
      rep_quotientMap_of_not_incoming V S _ hnotin
    rw [hflow, hrep, Γ.graphPoint_state hadm, Γ.graphPoint_edge hadm]
    have hq : (departurePoint η' (interiorStep V S η.1
        ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2).1
        = coordinate Γ η' := rfl
    rw [hq]
    by_cases hbo : η'.2 = true
    · exact Or.inr (by simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo])
    · have hbo' : η'.2 = false := by
        cases h : η'.2 with
        | false => rfl
        | true => exact absurd h hbo
      exact Or.inl (by simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo'])
  rw [hYnull, V.regularLiouville_exactPiece_eq_zero S hA hbox hs h2s hWm hW]

end Flow

end MechanicalPotential

end HamiltonianMetricGraphs
