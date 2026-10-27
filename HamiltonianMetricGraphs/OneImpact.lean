/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3: the flow preserves the measure of a one-impact stratum
-/

import HamiltonianMetricGraphs.ImpactRetrace
import HamiltonianMetricGraphs.FlowInvariance

/-!
# The flow preserves the measure of a one-impact stratum

This is the geometric heart of Lemma VI.3.  On the stratum `impactPiece η η' A s` — the regular
points whose first impact happens strictly within the time `s`, lands at the germ `η` and scatters
into the germ `η'` — the flow `Φ_s` preserves the quotient Liouville measure.

Both sides are read in flux coordinates by the charts of `GermTube.lean`:

* the stratum itself lies in the *incoming* tube of `η`, because a one-impact state is a reversed
  departure flight (`departureFlight_impactSlice`), so
  `m (W) = ∫_A r ∫_{(0,s)} 1_W (reversed departure flight of (η, r) at time θ) dθ dr`;
* its image lies in the *outgoing* tube of `η'`, because past the impact the trajectory is the
  departure flight of `(η', r)` (`pointTrajectory_impactSlice`), so
  `m (Φ_s W) = ∫_A r ∫_{(0,s)} 1_{Φ_s W} (departure flight of (η', r) at time u) du dr`.

Scattering preserves the speed, so the *same* `r` appears in both displays, and the flow moves the
parameter by `u = s - θ`.  Since `θ ↦ s - θ` preserves Lebesgue measure on `(0, s)`, the two
integrals agree.  Splitting the stratum by the pair of germs — rather than by the vertex — is what
makes the germ counting measure of `map_impactStep_flux_prod` unnecessary here: the scattered germ
is constant on each piece.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set MeasureTheory PhysicalEdgeSegment
open FiniteMetricGraph.EdgeEnd (coordinate vertex)
open scoped ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The departure chart is injective -/

/-- **The departure chart is injective on the flow box.**  The energy of the state recovers the
speed and the time coordinate recovers the elapsed time. -/
theorem departureFlight_inj {η : Γ.EdgeEnd} {A : Set ℝ} {r₁ r₂ δ u₀ : ℝ}
    (hbox : V.GermFlowBox η A r₁ r₂ δ u₀) {r r' w w' : ℝ} (hr : r ∈ A) (hr' : r' ∈ A)
    (hw : w ∈ Icc (0 : ℝ) u₀) (hw' : w' ∈ Icc (0 : ℝ) u₀)
    (h : V.departureFlight η r w = V.departureFlight η r' w') : r = r' ∧ w = w' := by
  have hE := hbox.energy r hr w hw
  have hE' := hbox.energy r' hr' w' hw'
  have hr0 : 0 ≤ r := le_of_lt (lt_trans hbox.speed_pos (hbox.speeds hr).1)
  have hr0' : 0 ≤ r' := le_of_lt (lt_trans hbox.speed_pos (hbox.speeds hr').1)
  have hEE : V.departureEnergy η r = V.departureEnergy η r' := by rw [← hE, ← hE', h]
  have hrr : r = r' := by
    have h1 : V.germSpeed η (V.departureEnergy η r) = V.germSpeed η (V.departureEnergy η r') := by
      rw [hEE]
    rwa [V.germSpeed_departureEnergy η hr0, V.germSpeed_departureEnergy η hr0'] at h1
  refine ⟨hrr, ?_⟩
  have ht := hbox.time r hr w hw
  have ht' := hbox.time r' hr' w' hw'
  rw [← hrr] at ht' h
  have heq : -(FiniteMetricGraph.EdgeEnd.sign Γ η) * w
      = -(FiniteMetricGraph.EdgeEnd.sign Γ η) * w' := by
    rw [← ht, ← ht', h]
  have hself := edgeEnd_sign_mul_self η
  have h2 : (FiniteMetricGraph.EdgeEnd.sign Γ η * FiniteMetricGraph.EdgeEnd.sign Γ η) * w
      = (FiniteMetricGraph.EdgeEnd.sign Γ η * FiniteMetricGraph.EdgeEnd.sign Γ η) * w' := by
    have e1 : (FiniteMetricGraph.EdgeEnd.sign Γ η * FiniteMetricGraph.EdgeEnd.sign Γ η) * w
        = -(FiniteMetricGraph.EdgeEnd.sign Γ η) *
          (-(FiniteMetricGraph.EdgeEnd.sign Γ η) * w) := by ring
    have e2 : (FiniteMetricGraph.EdgeEnd.sign Γ η * FiniteMetricGraph.EdgeEnd.sign Γ η) * w'
        = -(FiniteMetricGraph.EdgeEnd.sign Γ η) *
          (-(FiniteMetricGraph.EdgeEnd.sign Γ η) * w') := by ring
    rw [e1, e2, heq]
  rwa [hself, one_mul, one_mul] at h2

variable (S : BorelEnergyPreservingScattering V)

/-- **The quotient map is injective on the interior of an edge.** -/
theorem eq_of_graphClass_eq_interior {e : Γ.Edge} {x y : ℝ × ℝ}
    (hx : x ∈ V.interiorRegular e) (hy : y ∈ V.interiorRegular e)
    (h : graphClass V S ((e, x) : Γ.Edge × ℝ × ℝ)
      = graphClass V S ((e, y) : Γ.Edge × ℝ × ℝ)) : x = y := by
  have hadmx : Γ.AdmissiblePoint ((e, x) : Γ.Edge × ℝ × ℝ) :=
    ⟨Set.Ioo_subset_Icc_self hx.1, Or.inl hx.1⟩
  have hadmy : Γ.AdmissiblePoint ((e, y) : Γ.Edge × ℝ × ℝ) :=
    ⟨Set.Ioo_subset_Icc_self hy.1, Or.inl hy.1⟩
  have h1 : rep V S (graphClass V S ((e, x) : Γ.Edge × ℝ × ℝ))
      = Γ.graphPoint ((e, x) : Γ.Edge × ℝ × ℝ) := V.rep_interiorClass S hx
  have h2 : rep V S (graphClass V S ((e, y) : Γ.Edge × ℝ × ℝ))
      = Γ.graphPoint ((e, y) : Γ.Edge × ℝ × ℝ) := V.rep_interiorClass S hy
  rw [← h] at h2
  have hgp : Γ.graphPoint ((e, x) : Γ.Edge × ℝ × ℝ)
      = Γ.graphPoint ((e, y) : Γ.Edge × ℝ × ℝ) := h1.symm.trans h2
  have h3 : (Γ.graphPoint ((e, x) : Γ.Edge × ℝ × ℝ)).1.2.1
      = (Γ.graphPoint ((e, y) : Γ.Edge × ℝ × ℝ)).1.2.1 := by rw [hgp]
  rwa [Γ.graphPoint_state hadmx, Γ.graphPoint_state hadmy] at h3

section Flow

variable [Nonempty Γ.Edge]

omit [Nonempty Γ.Edge] in
/-- A regular point is the class of its own outgoing representative. -/
theorem val_eq_graphClass_rep (z : RegularScatteringPhaseSpace (V := V) S) :
    (z : ScatteringPhaseSpace (V := V) S)
      = graphClass V S (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
        (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) :=
  (V.graphClass_repFlight S z).symm

/-- **The flow of a one-impact point.**  Past the impact the point is the class of the departure
flight of the scattered datum. -/
theorem flow_val_of_impactPiece {η η' : Γ.EdgeEnd} {A : Set ℝ} {s r₁ r₂ δ u₀ : ℝ}
    (hbox' : V.GermFlowBox η' A r₁ r₂ δ u₀) (hsu : s ≤ u₀)
    {z : RegularScatteringPhaseSpace (V := V) S} (hz : z ∈ V.impactPiece S η η' A s)
    {t : ℝ}
    (hθt : V.interiorDurationTotal η.1
      ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) ≤ t) (hts : t ≤ s) :
    (flow V S z t).1 = graphClass V S ((η'.1,
      V.departureFlight η'
        (interiorStep V S η.1 ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2
        (t - V.interiorDurationTotal η.1
          ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1))) : Γ.Edge × ℝ × ℝ) := by
  obtain ⟨hedge, hslice⟩ := hz
  have ht0 : 0 ≤ t := le_trans (V.interiorDurationTotal_nonneg _ _) hθt
  rw [V.flow_of_nonneg S z ht0, V.forwardFlow_eq_graphClass S z t]
  have hpair : (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
        (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ)
      = ((η.1, (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) :=
    Prod.ext hedge rfl
  rw [hpair, V.pointTrajectory_impactSlice S hbox' hsu hslice hθt hts]

/-! ### The one-impact invariance -/

/-- **The flow preserves the measure of a one-impact stratum.**  The incoming tube chart of `η` and
the outgoing tube chart of `η'` express the two measures by the same flux integral, with the time
parameter reflected by `θ ↦ s - θ`. -/
theorem measure_image_flow_impactPiece {η η' : Γ.EdgeEnd} {A : Set ℝ} (hA : MeasurableSet A)
    {r₁ r₂ δ u₀ s : ℝ} (hbox : V.GermFlowBox η A r₁ r₂ δ u₀)
    (hbox' : V.GermFlowBox η' A r₁ r₂ δ u₀)
    (hlen : δ < Γ.length η.1 / 2) (hlen' : δ < Γ.length η'.1 / 2)
    (hsu : s ≤ u₀)
    {W : Set (RegularScatteringPhaseSpace (V := V) S)} (hWm : MeasurableSet W)
    (hW : W ⊆ V.impactPiece S η η' A s) :
    regularLiouville V S ((fun z => flow V S z s) '' W) = regularLiouville V S W := by
  classical
  have hvalW : MeasurableSet (Subtype.val '' W) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_regularScatteringPhaseSpace V S)).measurableSet_image' hWm
  have hYm : MeasurableSet ((fun z => flow V S z s) '' W) := V.measurableSet_image_flow S s hWm
  have hvalY : MeasurableSet (Subtype.val '' ((fun z => flow V S z s) '' W)) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_regularScatteringPhaseSpace V S)).measurableSet_image' hYm
  set T : Set (ℝ × ℝ) := V.interiorSlice S (Subtype.val '' W) η.1 with hTdef
  set T' : Set (ℝ × ℝ) :=
    V.interiorSlice S (Subtype.val '' ((fun z => flow V S z s) '' W)) η'.1 with hT'def
  have hTm : MeasurableSet T := V.measurableSet_interiorSlice S hvalW η.1
  have hT'm : MeasurableSet T' := V.measurableSet_interiorSlice S hvalY η'.1
  have hTslice : T ⊆ V.impactSlice S η η' A s := V.interiorSlice_subset_impactSlice S hW
  -- the stratum lies in the incoming tube of `η`
  have hTtube : T ⊆ V.germTubeIn η A δ s := by
    intro x hx
    have hxs := hTslice hx
    have hkey := V.departureFlight_impactSlice S hbox hsu hxs
    have hmem := V.departureFlight_mem_germTube η hbox hxs.2.2.2.2 hsu hxs.2.1
    rw [hkey] at hmem
    exact hmem
  -- the impact data of a point of `W`
  have hzdata : ∀ z ∈ W, ∃ r₀ θ₀ : ℝ, r₀ ∈ A ∧ θ₀ ∈ Ioo (0 : ℝ) s ∧
      Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) (V.departureFlight η r₀ θ₀) ∈
        V.interiorRegular η.1 ∧
      (z : ScatteringPhaseSpace (V := V) S) = graphClass V S ((η.1,
        Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)
          (V.departureFlight η r₀ θ₀)) : Γ.Edge × ℝ × ℝ) ∧
      (flow V S z s).1 = graphClass V S ((η'.1,
        V.departureFlight η' r₀ (s - θ₀)) : Γ.Edge × ℝ × ℝ) := by
    intro z hzW
    obtain ⟨hedge, hslice⟩ := hW hzW
    have hretr := V.departureFlight_impactSlice S hbox hsu hslice
    have hxx : Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)
        (V.departureFlight η
          (interiorStep V S η.1 ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2
          (V.interiorDurationTotal η.1
            ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)))
        = (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1 := by
      rw [hretr]
      exact Prod.ext rfl (neg_neg _)
    refine ⟨(interiorStep V S η.1 ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1)).2,
      V.interiorDurationTotal η.1 ((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1),
      hslice.2.2.2.2, hslice.2.1, ?_, ?_, ?_⟩
    · rw [hxx]; exact hslice.1.1
    · rw [hxx]
      have h1 := V.val_eq_graphClass_rep S z
      have hpair : (((rep V S (z : ScatteringPhaseSpace (V := V) S)).1.1,
            (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ)
          = ((η.1, (rep V S (z : ScatteringPhaseSpace (V := V) S)).1.2.1) : Γ.Edge × ℝ × ℝ) :=
        Prod.ext hedge rfl
      rwa [hpair] at h1
    · exact V.flow_val_of_impactPiece S hbox' hsu (hW hzW) (le_of_lt hslice.2.1.2) le_rfl
  -- the image of the stratum lies in the outgoing tube of `η'`
  have hT'char : ∀ x' ∈ T', ∃ r₀ θ₀ : ℝ, r₀ ∈ A ∧ θ₀ ∈ Ioo (0 : ℝ) s ∧
      x' = V.departureFlight η' r₀ (s - θ₀) := by
    intro x' hx'
    obtain ⟨y, hyY, hyv⟩ := hx'.2
    obtain ⟨z, hzW, rfl⟩ := hyY
    obtain ⟨r₀, θ₀, hr₀, hθ₀, -, -, hflow⟩ := hzdata z hzW
    refine ⟨r₀, θ₀, hr₀, hθ₀, ?_⟩
    have hsθ : s - θ₀ ∈ Ioo (0 : ℝ) u₀ := ⟨by linarith [hθ₀.2], by linarith [hθ₀.1]⟩
    have hint' : V.departureFlight η' r₀ (s - θ₀) ∈ V.interiorRegular η'.1 :=
      V.departureFlight_mem_interiorRegular η' hbox' hlen' hr₀ hsθ
    have hxreg : x' ∈ V.interiorRegular η'.1 := by
      refine ⟨hx'.1, ?_⟩
      have h : quotientHamiltonian (V := V) S
          ((flow V S z s : RegularScatteringPhaseSpace (V := V) S) :
            ScatteringPhaseSpace (V := V) S) ∉ V.exceptionalEnergies := (flow V S z s).2
      rw [hyv, quotientHamiltonian_graphClass V S
        ⟨Set.Ioo_subset_Icc_self hx'.1, Or.inl hx'.1⟩] at h
      exact h
    refine V.eq_of_graphClass_eq_interior S hxreg hint' ?_
    rw [← hyv, hflow]
  have hT'tube : T' ⊆ V.germTube η' A δ s := by
    intro x' hx'
    obtain ⟨r₀, θ₀, hr₀, hθ₀, rfl⟩ := hT'char x' hx'
    exact V.departureFlight_mem_germTube η' hbox' hr₀ hsu
      ⟨by linarith [hθ₀.2], by linarith [hθ₀.1]⟩
  -- the two charts describe the same set
  have hkey : ∀ r ∈ A, ∀ θ ∈ Ioo (0 : ℝ) s,
      (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) (V.departureFlight η r θ) ∈ T
        ↔ V.departureFlight η' r (s - θ) ∈ T') := by
    intro r hrA θ hθ
    have hθu : θ ∈ Icc (0 : ℝ) u₀ := ⟨hθ.1.le, le_trans hθ.2.le hsu⟩
    have hsθ : s - θ ∈ Ioo (0 : ℝ) u₀ := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    constructor
    · intro hx
      obtain ⟨z, hzW, hzv⟩ := hx.2
      obtain ⟨r₀, θ₀, hr₀, hθ₀, hint₀', hzval, hflow⟩ := hzdata z hzW
      have hθ₀u : θ₀ ∈ Icc (0 : ℝ) u₀ := ⟨hθ₀.1.le, le_trans hθ₀.2.le hsu⟩
      -- the two reversed flights agree
      have hint : Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) (V.departureFlight η r θ) ∈
          V.interiorRegular η.1 := (hTslice hx).1.1
      have hint₀ : Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) (V.departureFlight η r₀ θ₀) ∈
          V.interiorRegular η.1 := hint₀'
      have heqcls : graphClass V S ((η.1, Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)
            (V.departureFlight η r θ)) : Γ.Edge × ℝ × ℝ)
          = graphClass V S ((η.1, Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)
            (V.departureFlight η r₀ θ₀)) : Γ.Edge × ℝ × ℝ) := by
        rw [← hzv, hzval]
      have hpteq := V.eq_of_graphClass_eq_interior S hint hint₀ heqcls
      have hfleq : V.departureFlight η r θ = V.departureFlight η r₀ θ₀ := by
        have h := congrArg (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)) hpteq
        have e1 : ∀ y : ℝ × ℝ, Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)
            (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) y) = y :=
          fun y => Prod.ext rfl (neg_neg y.2)
        rwa [e1, e1] at h
      obtain ⟨hrr, hθθ⟩ := V.departureFlight_inj hbox hrA hr₀ hθu hθ₀u hfleq
      refine ⟨?_, ⟨flow V S z s, ⟨z, hzW, rfl⟩, ?_⟩⟩
      · exact (V.departureFlight_mem_interiorRegular η' hbox' hlen' hrA hsθ).1
      · rw [hflow, hrr, hθθ]
    · intro hx'
      obtain ⟨y, hyY, hyv⟩ := hx'.2
      obtain ⟨z, hzW, rfl⟩ := hyY
      obtain ⟨r₀, θ₀, hr₀, hθ₀, hint₀', hzval, hflow⟩ := hzdata z hzW
      have hsθ₀ : s - θ₀ ∈ Ioo (0 : ℝ) u₀ := ⟨by linarith [hθ₀.2], by linarith [hθ₀.1]⟩
      have hint : V.departureFlight η' r (s - θ) ∈ V.interiorRegular η'.1 :=
        V.departureFlight_mem_interiorRegular η' hbox' hlen' hrA hsθ
      have hint₀ : V.departureFlight η' r₀ (s - θ₀) ∈ V.interiorRegular η'.1 :=
        V.departureFlight_mem_interiorRegular η' hbox' hlen' hr₀ hsθ₀
      have heqcls : graphClass V S ((η'.1, V.departureFlight η' r (s - θ)) : Γ.Edge × ℝ × ℝ)
          = graphClass V S ((η'.1, V.departureFlight η' r₀ (s - θ₀)) : Γ.Edge × ℝ × ℝ) := by
        rw [← hyv, hflow]
      have hfleq := V.eq_of_graphClass_eq_interior S hint hint₀ heqcls
      obtain ⟨hrr, hww⟩ := V.departureFlight_inj hbox' hrA hr₀
        ⟨hsθ.1.le, hsθ.2.le⟩ ⟨hsθ₀.1.le, hsθ₀.2.le⟩ hfleq
      have hθθ : θ = θ₀ := by linarith
      refine ⟨?_, ⟨z, hzW, ?_⟩⟩
      · exact (V.departureFlight_mem_interiorRegular η hbox hlen hrA
          ⟨hθ.1, lt_of_lt_of_le hθ.2 hsu⟩).1
      · rw [hzval, hrr, hθθ]
  -- the two measures in flux coordinates
  have hmW : regularLiouville V S W = volume T :=
    V.regularLiouville_impactPiece_eq S hWm hW
  have hmY : regularLiouville V S ((fun z => flow V S z s) '' W) = volume T' := by
    refine V.regularLiouville_eq_volume_interiorSlice S η'.1 hYm ?_
    rintro y ⟨z, hzW, rfl⟩
    obtain ⟨r₀, θ₀, hr₀, hθ₀, -, -, hflow⟩ := hzdata z hzW
    have hsθ₀ : s - θ₀ ∈ Ioo (0 : ℝ) u₀ := ⟨by linarith [hθ₀.2], by linarith [hθ₀.1]⟩
    have hint₀ : V.departureFlight η' r₀ (s - θ₀) ∈ V.interiorRegular η'.1 :=
      V.departureFlight_mem_interiorRegular η' hbox' hlen' hr₀ hsθ₀
    have hadm : Γ.AdmissiblePoint
        ((η'.1, V.departureFlight η' r₀ (s - θ₀)) : Γ.Edge × ℝ × ℝ) :=
      ⟨Set.Ioo_subset_Icc_self hint₀.1, Or.inl hint₀.1⟩
    have hrep : rep V S (graphClass V S ((η'.1, V.departureFlight η' r₀ (s - θ₀))
          : Γ.Edge × ℝ × ℝ))
        = Γ.graphPoint ((η'.1, V.departureFlight η' r₀ (s - θ₀)) : Γ.Edge × ℝ × ℝ) :=
      V.rep_interiorClass S hint₀
    rw [hflow, hrep]
    exact Γ.graphPoint_edge hadm
  have hvolT : volume T = ∫⁻ r in A, ENNReal.ofReal r *
      ∫⁻ θ in Ioo (0 : ℝ) s, T.indicator (fun _ => (1 : ℝ≥0∞))
        (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) (V.departureFlight η r θ)) := by
    rw [← setLIntegral_one T]
    exact V.lintegral_germTubeIn η hA hbox hsu hTm hTtube measurable_const
  have hvolT' : volume T' = ∫⁻ r in A, ENNReal.ofReal r *
      ∫⁻ u in Ioo (0 : ℝ) s, T'.indicator (fun _ => (1 : ℝ≥0∞))
        (V.departureFlight η' r u) := by
    rw [← setLIntegral_one T']
    exact V.lintegral_germTube η' hA hbox' hsu hT'm hT'tube measurable_const
  rw [hmY, hmW, hvolT, hvolT']
  refine setLIntegral_congr_fun hA (fun r hr => ?_)
  refine congrArg (fun y => ENNReal.ofReal r * y) ?_
  have hemb : MeasurableEmbedding (fun u : ℝ => s - u) :=
    (MeasurableEquiv.subLeft s).measurableEmbedding
  have hmp : MeasurePreserving (fun u : ℝ => s - u)
      (volume : Measure ℝ) (volume : Measure ℝ) :=
    Measure.measurePreserving_sub_left (volume : Measure ℝ) s
  have hpre : (fun u : ℝ => s - u) ⁻¹' Ioo (0 : ℝ) s = Ioo (0 : ℝ) s := by
    ext u
    constructor
    · intro h
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
    · intro h
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have hstep := hmp.setLIntegral_comp_preimage_emb hemb
    (fun u => T'.indicator (fun _ => (1 : ℝ≥0∞)) (V.departureFlight η' r u)) (Ioo (0 : ℝ) s)
  rw [hpre] at hstep
  rw [← hstep]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
  by_cases hc : V.departureFlight η' r (s - θ) ∈ T'
  · rw [Set.indicator_of_mem hc, Set.indicator_of_mem ((hkey r hr θ hθ).mpr hc)]
  · rw [Set.indicator_of_notMem hc,
      Set.indicator_of_notMem (fun hcon => hc ((hkey r hr θ hθ).mp hcon))]

end Flow

end MechanicalPotential

end HamiltonianMetricGraphs
