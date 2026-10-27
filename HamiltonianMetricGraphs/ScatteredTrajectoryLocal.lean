/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.FlowGroup

/-!
# Local lemmas for scattered trajectories (towards Definition V.4 and Proposition V.5)

This module collects the local facts used in `ScatteredTrajectory` to show that the flow `Φₜ` is
the unique scattered trajectory of Definition V.4 of the paper.

* **Edge solutions.**  A solution of the edge Hamilton equations which stays in the closed edge
  cylinder on an open time set and is never a zero-momentum vertex state lies in the open edge
  (`position_mem_Ioo_of_edgeSolution`); two solutions on an open interval with the same one-sided
  limit at its left end coincide (`eqOn_Ioo_of_tendsto_nhdsGT`).  The latter is Picard–Lindelöf
  uniqueness (Lemma V.1) from a *one-sided* initial value, the form needed at an outgoing boundary
  covector, where a lift only has a right limit.
* **Classes.**  The quotient map is injective at interior points
  (`eq_of_quotientMap_eq_of_interior`), so an interior lift is determined by the quotient point;
  two incoming covectors in one class are equal; the outgoing representative of the class `π(α)`
  of an incoming covector is `S_v α`.
* **Vertex impacts.**  `IsVertexImpactClass w` says that `w = π(α)` for an incoming boundary
  covector `α`, i.e. that `w` sits over a vertex: the vertex impacts of eq. (impact) of the paper.
* **The first flight of `Φₜ`.**  For `0 ≤ h` before the first impact, `Φ_h w` is the class of the
  flight curve of the outgoing representative of `w` (`flow_val_eq_graphClass_flightCurve`); at
  the first impact it is the class of the arrival covector (`flow_val_sSup`).
* **Lifts determine the flow.**  If `c` solves the edge equations in the open edge on `(a, b)` and
  tends to a non-incoming point `x₀` at `a⁺` with `w = π(e, x₀)`, then `Φ_h w = π(e, c (a + h))`
  for `0 < h < b - a`, and if `c` lands at an incoming point `x₁` at `b⁻` then
  `Φ_{b-a} w = π(e, x₁)` (`flow_val_of_lift`, `flow_val_of_lift_landing`).
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter Topology
open scoped NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### Solutions of the edge equations -/

/-- **A lift on an open time set lies in the open edge.**  If `c` solves the edge Hamilton
equations on an open set `U` of times, takes values in the closed edge cylinder and is never a
zero-momentum vertex state, then `c` never touches a vertex: at a vertex the momentum `q' = p` is
nonzero, so `q` would leave `[0, ℓₑ]` on one side. -/
theorem position_mem_Ioo_of_edgeSolution {e : Γ.Edge} {c : ℝ → ℝ × ℝ} {U : Set ℝ}
    (hU : IsOpen U)
    (hc : ∀ s ∈ U, Γ.AdmissiblePoint (e, c s) ∧ HasDerivAt c (V.edgeVectorField e (c s)) s)
    {s : ℝ} (hs : s ∈ U) : (c s).1 ∈ Ioo (0 : ℝ) (Γ.length e) := by
  obtain ⟨hadm, hderiv⟩ := hc s hs
  rcases hadm.2 with hint | hp
  · exact hint
  have hq : HasDerivAt (fun u => (c u).1) (c s).2 s := V.edgeIntegralCurve_hasDerivAt_fst hderiv
  have hphys : ∀ᶠ u in 𝓝 s, (c u).1 ∈ Icc (0 : ℝ) (Γ.length e) :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun u hu => (hc u hu).1.1
  obtain ⟨h0, hl⟩ := hadm.1
  refine ⟨lt_of_le_of_ne h0 ?_, lt_of_le_of_ne hl ?_⟩
  · intro h0eq
    rcases lt_or_gt_of_ne hp with hneg | hpos
    · have hev := eventually_neg_right_of_hasDerivAt_neg hq hneg h0eq.symm
      obtain ⟨u, hu1, hu2⟩ := (hev.and (nhdsWithin_le_nhds hphys)).exists
      linarith [hu2.1]
    · have hev := eventually_neg_left_of_hasDerivAt_pos hq hpos h0eq.symm
      obtain ⟨u, hu1, hu2⟩ := (hev.and (nhdsWithin_le_nhds hphys)).exists
      linarith [hu2.1]
  · intro hleq
    have hq' : HasDerivAt (fun u => (c u).1 - Γ.length e) (c s).2 s := hq.sub_const _
    have hf0 : (fun u => (c u).1 - Γ.length e) s = 0 := by
      change (c s).1 - Γ.length e = 0
      rw [hleq, sub_self]
    rcases lt_or_gt_of_ne hp with hneg | hpos
    · have hev := eventually_pos_left_of_hasDerivAt_neg hq' hneg hf0
      obtain ⟨u, hu1, hu2⟩ := (hev.and (nhdsWithin_le_nhds hphys)).exists
      change 0 < (c u).1 - Γ.length e at hu1
      linarith [hu2.2]
    · have hev := eventually_pos_right_of_hasDerivAt_pos hq' hpos hf0
      obtain ⟨u, hu1, hu2⟩ := (hev.and (nhdsWithin_le_nhds hphys)).exists
      change 0 < (c u).1 - Γ.length e at hu1
      linarith [hu2.2]

/-- Completing a solution on `(a, b)` by its right limit at `a`: the completed curve is continuous
on `[a, T]` and solves the edge equations in the one-sided sense on `[a, T)`, for every `T < b`.
At `a` the one-sided derivative is the limit of the derivatives, by continuity of the vector
field. -/
private theorem update_solution {e : Γ.Edge} {f : ℝ → ℝ × ℝ} {a b : ℝ} {x₀ : ℝ × ℝ}
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (V.edgeVectorField e (f t)) t)
    (hx₀ : x₀.1 ∈ V.domain e) (hfa : Tendsto f (𝓝[>] a) (𝓝 x₀)) {T : ℝ} (haT : a < T)
    (hTb : T < b) :
    ContinuousOn (Function.update f a x₀) (Icc a T) ∧
      ∀ t ∈ Ico a T, HasDerivWithinAt (Function.update f a x₀)
        (V.edgeVectorField e (Function.update f a x₀ t)) (Ici t) t := by
  classical
  have hFa : Function.update f a x₀ a = x₀ := Function.update_self _ _ _
  have hFne : ∀ t, t ≠ a → Function.update f a x₀ t = f t :=
    fun t ht => Function.update_of_ne ht _ _
  have heq : ∀ t, t ≠ a → Function.update f a x₀ =ᶠ[𝓝 t] f := fun t ht => by
    filter_upwards [compl_singleton_mem_nhds ht] with u hu using hFne u hu
  have hderiv_int : ∀ t ∈ Ioo a b,
      HasDerivAt (Function.update f a x₀) (V.edgeVectorField e (Function.update f a x₀ t)) t :=
    fun t ht => by
      rw [hFne t (ne_of_gt ht.1)]
      exact (hf t ht).congr_of_eventuallyEq (heq t (ne_of_gt ht.1))
  have hcontA : ∀ s : Set ℝ, s ⊆ Ici a → ContinuousWithinAt (Function.update f a x₀) s a :=
    fun s hs => by
      rw [continuousWithinAt_update_same]
      exact hfa.mono_left (nhdsWithin_mono _ fun u hu =>
        lt_of_le_of_ne (hs hu.1) (fun h => hu.2 h.symm))
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rcases eq_or_lt_of_le ht.1 with hat | hat
    · subst hat
      exact hcontA _ fun u hu => hu.1
    · exact (hderiv_int t ⟨hat, ht.2.trans_lt hTb⟩).continuousAt.continuousWithinAt
  · rcases eq_or_lt_of_le ht.1 with hat | hat
    · subst hat
      rw [hFa]
      refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo a T) ?_ ?_ (Ioo_mem_nhdsGT haT) ?_
      · intro u hu
        exact (hderiv_int u ⟨hu.1, hu.2.trans hTb⟩).differentiableAt.differentiableWithinAt
      · exact hcontA _ fun u hu => hu.1.le
      · have hX : ContinuousAt (V.edgeVectorField e) x₀ :=
          (V.continuousOn_edgeVectorField e).continuousAt
            (((V.domain_isOpen e).prod isOpen_univ).mem_nhds ⟨hx₀, trivial⟩)
        have h1 : Tendsto (fun u => V.edgeVectorField e (f u)) (𝓝[>] a)
            (𝓝 (V.edgeVectorField e x₀)) := hX.tendsto.comp hfa
        refine h1.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (haT.trans hTb)] with u hu
        rw [(hderiv_int u hu).deriv, hFne u (ne_of_gt hu.1)]
    · exact (hderiv_int t ⟨hat, ht.2.trans hTb⟩).hasDerivWithinAt

/-- **Edgewise uniqueness from a one-sided initial value (Lemma V.1).**  Two solutions of the edge
Hamilton equations on `(a, b)` which stay in the closed edge and have the same right limit at `a`
coincide on `(a, b)`. -/
theorem eqOn_Ioo_of_tendsto_nhdsGT {e : Γ.Edge} {f g : ℝ → ℝ × ℝ} {a b : ℝ} {x₀ : ℝ × ℝ}
    (hf : ∀ t ∈ Ioo a b,
      HasDerivAt f (V.edgeVectorField e (f t)) t ∧ (f t).1 ∈ Icc (0 : ℝ) (Γ.length e))
    (hg : ∀ t ∈ Ioo a b,
      HasDerivAt g (V.edgeVectorField e (g t)) t ∧ (g t).1 ∈ Icc (0 : ℝ) (Γ.length e))
    (hx₀ : x₀.1 ∈ Icc (0 : ℝ) (Γ.length e))
    (hfa : Tendsto f (𝓝[>] a) (𝓝 x₀)) (hga : Tendsto g (𝓝[>] a) (𝓝 x₀)) :
    EqOn f g (Ioo a b) := by
  classical
  intro t ht
  have hdom := V.closedEdge_subset_domain e hx₀
  obtain ⟨hFc, hFd⟩ := update_solution V (fun s hs => (hf s hs).1) hdom hfa ht.1 ht.2
  obtain ⟨hGc, hGd⟩ := update_solution V (fun s hs => (hg s hs).1) hdom hga ht.1 ht.2
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hFc
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc
  obtain ⟨K, hK⟩ := V.exists_lipschitzOnWith_edgeVectorField_closedMomentumBox e (max Cf Cg)
  have hbox : ∀ (F : ℝ → ℝ × ℝ) (C : ℝ), (∀ u ∈ Icc a t, ‖F u‖ ≤ C) → C ≤ max Cf Cg →
      (∀ u ∈ Ico a t, (F u).1 ∈ Icc (0 : ℝ) (Γ.length e)) →
      ∀ u ∈ Ico a t, F u ∈ closedEdgeMomentumBox e (max Cf Cg) :=
    fun F C hC hCP hpos u hu => ⟨hpos u hu, abs_le.mp ((norm_snd_le (F u)).trans
      ((hC u (Ico_subset_Icc_self hu)).trans hCP))⟩
  have hpos : ∀ (F : ℝ → ℝ × ℝ), (∀ s ∈ Ioo a b, (F s).1 ∈ Icc (0 : ℝ) (Γ.length e)) →
      ∀ u ∈ Ico a t, (Function.update F a x₀ u).1 ∈ Icc (0 : ℝ) (Γ.length e) := by
    intro F hF u hu
    rcases eq_or_lt_of_le hu.1 with hau | hau
    · subst hau
      rw [Function.update_self]
      exact hx₀
    · rw [Function.update_of_ne (ne_of_gt hau)]
      exact hF u ⟨hau, hu.2.trans ht.2⟩
  have hEq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => V.edgeVectorField e)
    (s := fun _ => closedEdgeMomentumBox e (max Cf Cg)) (fun _ _ => hK) hFc hFd
    (hbox _ Cf hCf (le_max_left _ _) (hpos f fun s hs => (hf s hs).2)) hGc hGd
    (hbox _ Cg hCg (le_max_right _ _) (hpos g fun s hs => (hg s hs).2))
    (by rw [Function.update_self, Function.update_self])
  have h := hEq ⟨ht.1.le, le_rfl⟩
  rwa [Function.update_of_ne (ne_of_gt ht.1), Function.update_of_ne (ne_of_gt ht.1)] at h

/-! ### Classes of boundary and interior points -/

/-- The prequotient point of a boundary covector sits at a vertex coordinate of its edge. -/
theorem toNonzeroPrequotientPhase_position (δ : Γ.BoundaryCovector) :
    (δ.toNonzeroPrequotientPhase Γ).1.2.1.1 = 0 ∨
      (δ.toNonzeroPrequotientPhase Γ).1.2.1.1 = Γ.length (δ.toNonzeroPrequotientPhase Γ).1.1 := by
  rcases δ with ⟨⟨e, b⟩, p, hp⟩
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem toNonzeroPrequotientPhase_not_interior (δ : Γ.BoundaryCovector) :
    (δ.toNonzeroPrequotientPhase Γ).1.2.1.1 ∉
      Ioo (0 : ℝ) (Γ.length (δ.toNonzeroPrequotientPhase Γ).1.1) := by
  intro h
  rcases toNonzeroPrequotientPhase_position δ with h0 | hl
  · rw [h0] at h; exact lt_irrefl _ h.1
  · rw [hl] at h; exact lt_irrefl _ h.2

variable (S : BorelEnergyPreservingScattering V)

/-- **The quotient map is injective at interior points**: the class of a point strictly inside an
edge is a singleton. -/
theorem eq_of_quotientMap_eq_of_interior {x y : Γ.NonzeroPrequotientPhase}
    (hx : x.1.2.1.1 ∈ Ioo (0 : ℝ) (Γ.length x.1.1))
    (h : quotientMap (V := V) S x = quotientMap (V := V) S y) : x = y := by
  rcases (scatteringEqv_iff_neighbor (V := V) S x y).mp (Quotient.exact h) with
    hxy | ⟨v, α, hx', -⟩ | ⟨v, α, -, hx'⟩
  · exact hxy
  · rw [hx'] at hx
    exact absurd hx (toNonzeroPrequotientPhase_not_interior _)
  · rw [hx'] at hx
    exact absurd hx (toNonzeroPrequotientPhase_not_interior _)

/-- **Interior lifts are unique**: if the class of an interior point `(e, x)` is the class of an
admissible point `(e', x')`, then `e' = e` and `x' = x`. -/
theorem eq_of_graphClass_eq_of_interior {e e' : Γ.Edge} {x x' : ℝ × ℝ}
    (hx : x.1 ∈ Ioo (0 : ℝ) (Γ.length e)) (hadm' : Γ.AdmissiblePoint (e', x'))
    (h : graphClass V S (e, x) = graphClass V S (e', x')) : e' = e ∧ x' = x := by
  have hadm : Γ.AdmissiblePoint (e, x) := ⟨Ioo_subset_Icc_self hx, Or.inl hx⟩
  have hint : (Γ.graphPoint (e, x)).1.2.1.1 ∈ Ioo (0 : ℝ) (Γ.length (Γ.graphPoint (e, x)).1.1) := by
    rw [Γ.graphPoint_val hadm]
    exact hx
  have hgp := eq_of_quotientMap_eq_of_interior V S hint h
  have hedge := congrArg (fun y : Γ.NonzeroPrequotientPhase => y.1.1) hgp
  have hstate := congrArg (fun y : Γ.NonzeroPrequotientPhase => y.1.2.1) hgp
  rw [Γ.graphPoint_edge hadm, Γ.graphPoint_edge hadm'] at hedge
  rw [Γ.graphPoint_state hadm, Γ.graphPoint_state hadm'] at hstate
  exact ⟨hedge.symm, hstate.symm⟩

/-- A quotient point **sits over a vertex** (is a vertex impact in the sense of eq. (impact) of the
paper) when it is the class `π(α)` of an incoming boundary covector `α`; equivalently the class of
the outgoing covector `S_v α`. -/
def IsVertexImpactClass (w : ScatteringPhaseSpace (V := V) S) : Prop :=
  ∃ (v : Γ.Vertex) (α : Γ.IncomingBoundary v),
    w = quotientMap (V := V) S (α.1.toNonzeroPrequotientPhase Γ)

/-- The class of an interior point does not sit over a vertex. -/
theorem not_isVertexImpactClass_graphClass {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x.1 ∈ Ioo (0 : ℝ) (Γ.length e)) :
    ¬ IsVertexImpactClass V S (graphClass V S (e, x)) := by
  rintro ⟨v, α, h⟩
  have hadm : Γ.AdmissiblePoint (e, x) := ⟨Ioo_subset_Icc_self hx, Or.inl hx⟩
  have hint : (Γ.graphPoint (e, x)).1.2.1.1 ∈ Ioo (0 : ℝ) (Γ.length (Γ.graphPoint (e, x)).1.1) := by
    rw [Γ.graphPoint_val hadm]
    exact hx
  have hgp := eq_of_quotientMap_eq_of_interior V S hint h
  rw [hgp] at hint
  exact toNonzeroPrequotientPhase_not_interior _ hint

/-- The two points of a scattering pair have the same class: `π(α) = π(S_v α)`. -/
theorem quotientMap_scatter {v : Γ.Vertex} (α : Γ.IncomingBoundary v) :
    quotientMap (V := V) S (α.1.toNonzeroPrequotientPhase Γ) =
      quotientMap (V := V) S ((S.map v α).1.toNonzeroPrequotientPhase Γ) :=
  Quotient.sound (Relation.EqvGen.rel _ _ ⟨v, α, rfl, rfl⟩)

/-- Two incoming covectors with the same class are equal. -/
theorem incoming_eq_of_quotientMap_eq {v w : Γ.Vertex} (α : Γ.IncomingBoundary v)
    (β : Γ.IncomingBoundary w)
    (h : quotientMap (V := V) S (α.1.toNonzeroPrequotientPhase Γ) =
      quotientMap (V := V) S (β.1.toNonzeroPrequotientPhase Γ)) : α.1 = β.1 := by
  rcases (scatteringEqv_iff_neighbor (V := V) S _ _).mp (Quotient.exact h) with
    hxy | hxy | hxy
  · exact FiniteMetricGraph.BoundaryCovector.toNonzeroPrequotientPhase_injective Γ hxy
  · exact absurd ⟨w, β, rfl⟩ (scatteringStep_target_notIncoming (V := V) S hxy)
  · exact absurd ⟨v, α, rfl⟩ (scatteringStep_target_notIncoming (V := V) S hxy)

/-- The outgoing representative of the class `π(α)` of an incoming covector is `S_v α`. -/
theorem rep_quotientMap_incoming {v : Γ.Vertex} (α : Γ.IncomingBoundary v) :
    rep V S (quotientMap (V := V) S (α.1.toNonzeroPrequotientPhase Γ)) =
      (S.map v α).1.toNonzeroPrequotientPhase Γ := by
  rw [quotientMap_scatter V S α]
  exact rep_quotientMap_of_not_incoming V S _
    (scatteringStep_target_notIncoming (V := V) S ⟨v, α, rfl, rfl⟩)

/-- At a vertex impact the representative flight is the flight of `S_v α`. -/
theorem repFlight_of_isVertexImpact (w : RegularScatteringPhaseSpace (V := V) S) {v : Γ.Vertex}
    (α : Γ.IncomingBoundary v)
    (hw : w.1 = quotientMap (V := V) S (α.1.toNonzeroPrequotientPhase Γ)) :
    (repFlight V S w).edge = (S.map v α).1.germ.1 ∧
      (repFlight V S w).state =
        (FiniteMetricGraph.EdgeEnd.coordinate Γ (S.map v α).1.germ, (S.map v α).1.momentum) := by
  rw [repFlight_edge, repFlight_state, hw, rep_quotientMap_incoming]
  exact ⟨rfl, rfl⟩

/-- At a vertex impact the representative flight departs with outgoing momentum. -/
theorem repFlight_isOutgoing_of_isVertexImpact (w : RegularScatteringPhaseSpace (V := V) S)
    {v : Γ.Vertex} (α : Γ.IncomingBoundary v)
    (hw : w.1 = quotientMap (V := V) S (α.1.toNonzeroPrequotientPhase Γ)) :
    (repFlight V S w).IsOutgoing := by
  obtain ⟨hedge, hstate⟩ := repFlight_of_isVertexImpact V S w α hw
  refine ⟨(S.map v α).1.germ, hedge.symm, ?_, ?_⟩
  · rw [hstate]
  · rw [hstate]
    exact (S.map v α).2.2

/-! ### The first flight of the scattered evolution -/

/-- The landing point of a terminating flight is its arrival covector. -/
theorem flightCurve_sSup_eq_arrival (A : V.FlightState)
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state)) :
    ((A.edge, FlightState.flightCurve V A
        (sSup (PhysicalEdgeSegment.durationSet V A.edge A.state))) : Γ.Edge × ℝ × ℝ) =
      ((A.segment.maximalArrivalCovector hbdd A.regular).germ.1,
        FiniteMetricGraph.EdgeEnd.coordinate Γ
          (A.segment.maximalArrivalCovector hbdd A.regular).germ,
        (A.segment.maximalArrivalCovector hbdd A.regular).momentum) := by
  refine Prod.ext (A.segment.maximalArrivalCovector_germ_fst hbdd A.regular).symm ?_
  change FlightState.flightCurve V A _ = _
  rw [FlightState.flightCurve_sSup A hbdd]
  exact FlightState.maximalEndpoint_eq_of_arrivalCovector A hbdd

/-- The class of the landing point of a terminating flight is the class of its arrival covector. -/
theorem graphClass_flightCurve_sSup (A : V.FlightState)
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state)) :
    graphClass V S (A.edge, FlightState.flightCurve V A
        (sSup (PhysicalEdgeSegment.durationSet V A.edge A.state)))
      = quotientMap (V := V) S
        ((A.segment.maximalArrivalIncoming hbdd A.regular).1.toNonzeroPrequotientPhase Γ) := by
  unfold graphClass
  rw [flightCurve_sSup_eq_arrival V A hbdd, Γ.graphPoint_covector]
  rfl

variable [Nonempty Γ.Edge]

/-- **Before the first impact, `Φ_h w` is the class of the first flight.**  For `0 ≤ h` below the
duration of the flight of the outgoing representative of `w`, the flow is the class of that
flight's curve at time `h`. -/
theorem flow_val_eq_graphClass_flightCurve (w : RegularScatteringPhaseSpace (V := V) S) {h : ℝ}
    (h0 : 0 ≤ h)
    (hd : ∀ _ : BddAbove (PhysicalEdgeSegment.durationSet V (repFlight V S w).edge
        (repFlight V S w).state),
      h < sSup (PhysicalEdgeSegment.durationSet V (repFlight V S w).edge
        (repFlight V S w).state)) :
    (flow V S w h).1 =
      graphClass V S ((repFlight V S w).edge, FlightState.flightCurve V (repFlight V S w) h) := by
  set A := repFlight V S w with hA
  have hact : FlightState.ActiveAt V S A 0 h := by
    refine ⟨by rw [FlightState.iterate_zero]; rfl, by rw [FlightState.impactReal_zero]; exact h0,
      fun hs => ?_⟩
    rw [FlightState.impactReal_succ_eq_of_isSome (V := V) (FlightState.iterate_zero V S A) hs,
      FlightState.impactReal_zero, zero_add]
    exact hd (FlightState.bddAbove_of_next_isSome (V := V) (S := S) hs)
  rw [flow_of_nonneg V S w h0, forwardFlow_val,
    FlightState.trajectory_eq V S A h0 hact (FlightState.iterate_zero V S A),
    FlightState.impactReal_zero, sub_zero]

/-- **At the first impact, `Φ_d w` is the class of the arrival covector** `π(α) = π(S_v α)`. -/
theorem flow_val_sSup (w : RegularScatteringPhaseSpace (V := V) S)
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V (repFlight V S w).edge
      (repFlight V S w).state)) :
    (flow V S w (sSup (PhysicalEdgeSegment.durationSet V (repFlight V S w).edge
        (repFlight V S w).state))).1 =
      graphClass V S ((repFlight V S w).edge, FlightState.flightCurve V (repFlight V S w)
        (sSup (PhysicalEdgeSegment.durationSet V (repFlight V S w).edge
          (repFlight V S w).state))) := by
  set A := repFlight V S w with hA
  set d := sSup (PhysicalEdgeSegment.durationSet V A.edge A.state) with hd
  have hd0 : 0 ≤ d := (FlightState.impactDuration_pos_of_bddAbove V A hbdd).le
  obtain ⟨b, hnext, hstate, -, -, hedge⟩ := FlightState.next_eq_some_of_bddAbove (V := V) S A hbdd
  have hb : FlightState.iterate V S A (0 + 1) = some b := by
    rw [FlightState.iterate_succ, FlightState.iterate_zero]
    exact hnext
  have hsome : (FlightState.iterate V S A (0 + 1)).isSome := by rw [hb]; rfl
  have himp : FlightState.impactReal V S A (0 + 1) = d := by
    rw [FlightState.impactReal_succ_eq_of_isSome (V := V) (FlightState.iterate_zero V S A) hsome,
      FlightState.impactReal_zero, zero_add]
  have htraj := FlightState.trajectory_at_impact V S A 0 hb
  rw [himp] at htraj
  rw [flow_of_nonneg V S w hd0, forwardFlow_val, htraj, graphClass_flightCurve_sSup V S A hbdd]
  unfold graphClass
  have hpt : ((b.edge, b.state) : Γ.Edge × ℝ × ℝ) =
      ((S.map _ (A.segment.maximalArrivalIncoming hbdd A.regular)).1.germ.1,
        FiniteMetricGraph.EdgeEnd.coordinate Γ
          (S.map _ (A.segment.maximalArrivalIncoming hbdd A.regular)).1.germ,
        (S.map _ (A.segment.maximalArrivalIncoming hbdd A.regular)).1.momentum) :=
    Prod.ext hedge hstate
  rw [hpt, Γ.graphPoint_covector]
  exact (quotientMap_scatter V S _).symm

/-! ### A lift determines the flow -/

omit [Nonempty Γ.Edge] in
/-- The flight curve starts at the flight's initial state, from the right. -/
theorem tendsto_flightCurve_nhdsGT_zero (A : V.FlightState) :
    Tendsto (FlightState.flightCurve V A) (𝓝[>] 0) (𝓝 A.state) := by
  have hcont := FlightState.flightCurve_continuousOn_Icc A (D := A.segment.duration)
    (fun hbdd => le_csSup hbdd A.segment.mem_durationSet) 0
    ⟨le_rfl, A.segment.duration_pos.le⟩
  have h := hcont.tendsto
  rw [FlightState.flightCurve_zero] at h
  rw [← nhdsWithin_Ioo_eq_nhdsGT A.segment.duration_pos]
  exact h.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)

omit [Nonempty Γ.Edge] in
/-- The flight curve is continuous from the left at any time of its flight. -/
theorem tendsto_flightCurve_nhdsLT (A : V.FlightState) {D : ℝ} (hD : 0 < D)
    (hDle : ∀ _ : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state),
      D ≤ sSup (PhysicalEdgeSegment.durationSet V A.edge A.state)) :
    Tendsto (FlightState.flightCurve V A) (𝓝[<] D) (𝓝 (FlightState.flightCurve V A D)) := by
  have h := (FlightState.flightCurve_continuousOn_Icc A hDle D ⟨hD.le, le_rfl⟩).tendsto
  rw [← nhdsWithin_Ioo_eq_nhdsLT hD]
  exact h.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)

omit [Nonempty Γ.Edge] in
/-- The shift `h ↦ a + h` maps right neighbourhoods of `0` to right neighbourhoods of `a`. -/
theorem tendsto_const_add_nhdsGT (a : ℝ) :
    Tendsto (fun h : ℝ => a + h) (𝓝[>] 0) (𝓝[>] a) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h := ((continuous_const_add a).tendsto 0)
    rw [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    change a < a + h
    linarith [show (0 : ℝ) < h from hh]

omit [Nonempty Γ.Edge] in
/-- The shift `h ↦ a + h` maps left neighbourhoods of `D` to left neighbourhoods of `a + D`. -/
theorem tendsto_const_add_nhdsLT (a D : ℝ) :
    Tendsto (fun h : ℝ => a + h) (𝓝[<] D) (𝓝[<] (a + D)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact ((continuous_const_add a).tendsto D).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    change a + h < a + D
    linarith [show h < D from hh]

omit [Nonempty Γ.Edge] in
/-- **A flight agrees with any lift starting at its initial state.**  If `c` solves the edge
equations in the open edge of `A` on `(a, b)` and `c → A.state` at `a⁺`, then the flight of `A`
lasts at least `b - a` and its curve is `c (a + ·)` on `(0, b - a)`. -/
theorem flightCurve_eq_of_lift (A : V.FlightState) {c : ℝ → ℝ × ℝ} {a b : ℝ}
    (hc : ∀ s ∈ Ioo a b, HasDerivAt c (V.edgeVectorField A.edge (c s)) s ∧
      (c s).1 ∈ Ioo (0 : ℝ) (Γ.length A.edge))
    (hca : Tendsto c (𝓝[>] a) (𝓝 A.state)) :
    (∀ _ : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state),
      b - a ≤ sSup (PhysicalEdgeSegment.durationSet V A.edge A.state)) ∧
      ∀ h ∈ Ioo 0 (b - a), FlightState.flightCurve V A h = c (a + h) := by
  -- the shifted lift
  have hg : ∀ h ∈ Ioo 0 (b - a), HasDerivAt (fun h => c (a + h))
      (V.edgeVectorField A.edge (c (a + h))) h ∧ (c (a + h)).1 ∈ Icc (0 : ℝ) (Γ.length A.edge) := by
    intro h hh
    have hmem : a + h ∈ Ioo a b := ⟨by linarith [hh.1], by linarith [hh.2]⟩
    exact ⟨(hc (a + h) hmem).1.comp_const_add a h, Ioo_subset_Icc_self (hc (a + h) hmem).2⟩
  have hga : Tendsto (fun h => c (a + h)) (𝓝[>] 0) (𝓝 A.state) :=
    hca.comp (tendsto_const_add_nhdsGT a)
  have hagree : ∀ T, T ≤ b - a →
      (∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state),
        T ≤ sSup (PhysicalEdgeSegment.durationSet V A.edge A.state)) →
      EqOn (FlightState.flightCurve V A) (fun h => c (a + h)) (Ioo 0 T) := by
    intro T hT hTd
    refine eqOn_Ioo_of_tendsto_nhdsGT V (x₀ := A.state) ?_ ?_ A.segment.initial_physical
      (tendsto_flightCurve_nhdsGT_zero V A) hga
    · intro h hh
      have hlt : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state),
          h < sSup (PhysicalEdgeSegment.durationSet V A.edge A.state) :=
        fun hbdd => lt_of_lt_of_le hh.2 (hTd hbdd)
      exact ⟨FlightState.flightCurve_hasDerivAt V A hh.1 hlt,
        FlightState.flightCurve_physical V A hh.1.le fun hbdd => (hlt hbdd).le⟩
    · intro h hh
      exact hg h ⟨hh.1, lt_of_lt_of_le hh.2 hT⟩
  have hlong : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state),
      b - a ≤ sSup (PhysicalEdgeSegment.durationSet V A.edge A.state) := by
    intro hbdd
    by_contra hlt
    push Not at hlt
    set d := sSup (PhysicalEdgeSegment.durationSet V A.edge A.state) with hd
    have hd0 : 0 < d := FlightState.impactDuration_pos_of_bddAbove V A hbdd
    have hEq := hagree d hlt.le (fun _ => le_rfl)
    -- both curves are continuous from the left at `d`
    have h1 := tendsto_flightCurve_nhdsLT V A hd0 (fun _ => le_rfl)
    have hmem : a + d ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have h2 : Tendsto (fun h => c (a + h)) (𝓝[<] d) (𝓝 (c (a + d))) :=
      ((hc (a + d) hmem).1.continuousAt.tendsto.comp
        ((continuous_const_add a).tendsto d)).mono_left nhdsWithin_le_nhds
    have h1' : Tendsto (fun h => c (a + h)) (𝓝[<] d) (𝓝 (FlightState.flightCurve V A d)) := by
      refine h1.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hd0] with h hh using hEq hh
    have heq := tendsto_nhds_unique h1' h2
    have hint := (hc (a + d) hmem).2
    rw [← heq, hd, FlightState.flightCurve_sSup A hbdd] at hint
    exact A.segment.maximalEndpoint_not_interior hbdd hint
  exact ⟨hlong, hagree (b - a) le_rfl hlong⟩

omit [Nonempty Γ.Edge] in
/-- **A landing lift ends the flight.**  If moreover `c` tends at `b⁻` to a point `x₁` at a vertex
of the edge, then the flight of `A` terminates exactly at time `b - a`, landing at `x₁`. -/
theorem flightCurve_eq_of_lift_landing (A : V.FlightState) {c : ℝ → ℝ × ℝ} {a b : ℝ}
    (hab : a < b)
    (hc : ∀ s ∈ Ioo a b, HasDerivAt c (V.edgeVectorField A.edge (c s)) s ∧
      (c s).1 ∈ Ioo (0 : ℝ) (Γ.length A.edge))
    (hca : Tendsto c (𝓝[>] a) (𝓝 A.state)) {x₁ : ℝ × ℝ}
    (hx₁ : x₁.1 ∉ Ioo (0 : ℝ) (Γ.length A.edge)) (hcb : Tendsto c (𝓝[<] b) (𝓝 x₁)) :
    ∃ _ : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state),
      sSup (PhysicalEdgeSegment.durationSet V A.edge A.state) = b - a ∧
        FlightState.flightCurve V A (b - a) = x₁ := by
  obtain ⟨hlong, hEq⟩ := flightCurve_eq_of_lift V A hc hca
  have hD : 0 < b - a := sub_pos.mpr hab
  have hlim : Tendsto (fun h => c (a + h)) (𝓝[<] (b - a)) (𝓝 x₁) := by
    have hsh := tendsto_const_add_nhdsLT a (b - a)
    rw [show a + (b - a) = b by ring] at hsh
    exact hcb.comp hsh
  have hfc : Tendsto (FlightState.flightCurve V A) (𝓝[<] (b - a)) (𝓝 x₁) := by
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hD] with h hh using (hEq h hh).symm
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state)
  · rcases eq_or_lt_of_le (hlong hbdd) with heq | hlt
    · refine ⟨hbdd, heq.symm, ?_⟩
      exact tendsto_nhds_unique (tendsto_flightCurve_nhdsLT V A hD fun h => (hlong h)) hfc
    · exfalso
      have hcont := (FlightState.flightCurve_hasDerivAt V A hD fun _ => hlt).continuousAt
      have heq := tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds) hfc
      exact hx₁ (heq ▸ FlightState.flightCurve_interior V A hD fun _ => hlt)
  · exfalso
    have hlt : ∀ hb : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state),
        b - a < sSup (PhysicalEdgeSegment.durationSet V A.edge A.state) :=
      fun hb => absurd hb hbdd
    have hcont := (FlightState.flightCurve_hasDerivAt V A hD hlt).continuousAt
    have heq := tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds) hfc
    exact hx₁ (heq ▸ FlightState.flightCurve_interior V A hD hlt)

omit [Nonempty Γ.Edge] in
/-- The representative flight of the class of a non-incoming admissible point `(e, x₀)` is the
flight started at `(e, x₀)`. -/
theorem repFlight_of_graphClass (w : RegularScatteringPhaseSpace (V := V) S) {e : Γ.Edge}
    {x₀ : ℝ × ℝ} (hadm : Γ.AdmissiblePoint (e, x₀))
    (hnot : ¬ IsIncomingPoint (V := V) S (Γ.graphPoint (e, x₀)))
    (hw : w.1 = graphClass V S (e, x₀)) :
    (repFlight V S w).edge = e ∧ (repFlight V S w).state = x₀ := by
  have hrep : rep V S w.1 = Γ.graphPoint (e, x₀) := by
    rw [hw]
    exact rep_quotientMap_of_not_incoming V S _ hnot
  rw [repFlight_edge, repFlight_state, hrep]
  exact ⟨Γ.graphPoint_edge hadm, Γ.graphPoint_state hadm⟩

/-- **A lift determines the flow (Proposition V.5, uniqueness between impacts).**  Let `c` solve
the edge equations of `e` in the open edge on `(a, b)`, with right limit `x₀` at `a`, where
`(e, x₀)` is an admissible non-incoming point (an interior point or an outgoing covector) whose
class is `w`.  Then `Φ_h w = π(e, c (a + h))` for `0 < h < b - a`. -/
theorem flow_val_of_lift (w : RegularScatteringPhaseSpace (V := V) S) {e : Γ.Edge}
    {x₀ : ℝ × ℝ} (hadm : Γ.AdmissiblePoint (e, x₀))
    (hnot : ¬ IsIncomingPoint (V := V) S (Γ.graphPoint (e, x₀)))
    (hw : w.1 = graphClass V S (e, x₀)) {c : ℝ → ℝ × ℝ} {a b : ℝ}
    (hc : ∀ s ∈ Ioo a b, HasDerivAt c (V.edgeVectorField e (c s)) s ∧
      (c s).1 ∈ Ioo (0 : ℝ) (Γ.length e))
    (hca : Tendsto c (𝓝[>] a) (𝓝 x₀)) {h : ℝ} (hh : h ∈ Ioo 0 (b - a)) :
    (flow V S w h).1 = graphClass V S (e, c (a + h)) := by
  obtain ⟨hedge, hstate⟩ := repFlight_of_graphClass V S w hadm hnot hw
  set A := repFlight V S w with hA
  subst hedge hstate
  obtain ⟨hlong, hEq⟩ := flightCurve_eq_of_lift V A hc hca
  rw [flow_val_eq_graphClass_flightCurve V S w hh.1.le
    (fun hbdd => lt_of_lt_of_le hh.2 (hlong hbdd)), ← hA, hEq h hh]

/-- **A landing lift determines the flow at the impact.**  If in addition `c` tends at `b⁻` to a
point `x₁` at a vertex of `e`, then `Φ_{b-a} w = π(e, x₁)`. -/
theorem flow_val_of_lift_landing (w : RegularScatteringPhaseSpace (V := V) S) {e : Γ.Edge}
    {x₀ : ℝ × ℝ} (hadm : Γ.AdmissiblePoint (e, x₀))
    (hnot : ¬ IsIncomingPoint (V := V) S (Γ.graphPoint (e, x₀)))
    (hw : w.1 = graphClass V S (e, x₀)) {c : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a < b)
    (hc : ∀ s ∈ Ioo a b, HasDerivAt c (V.edgeVectorField e (c s)) s ∧
      (c s).1 ∈ Ioo (0 : ℝ) (Γ.length e))
    (hca : Tendsto c (𝓝[>] a) (𝓝 x₀)) {x₁ : ℝ × ℝ}
    (hx₁ : x₁.1 ∉ Ioo (0 : ℝ) (Γ.length e)) (hcb : Tendsto c (𝓝[<] b) (𝓝 x₁)) :
    (flow V S w (b - a)).1 = graphClass V S (e, x₁) := by
  obtain ⟨hedge, hstate⟩ := repFlight_of_graphClass V S w hadm hnot hw
  set A := repFlight V S w with hA
  subst hedge hstate
  obtain ⟨hbdd, hd, hland⟩ := flightCurve_eq_of_lift_landing V A hab hc hca hx₁ hcb
  have h := flow_val_sSup V S w hbdd
  rw [← hA, hd, hland] at h
  exact h

end MechanicalPotential

end HamiltonianMetricGraphs
