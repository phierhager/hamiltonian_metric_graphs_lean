/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.ScatteredTrajectoryLocal

/-!
# Scattered trajectories: Definition V.4 and Proposition V.5

**Definition V.4.**  A scattered trajectory through `z ∈ P^Reg_S` is a map `γ : ℝ → P^Reg_S` with
`γ(0) = z` such that there is a locally finite set `I ⊂ ℝ` with the following properties.  On
every component of `ℝ \ I`, `γ` lifts to a single edge cylinder and solves the edge Hamilton
equations.  At each `t₀ ∈ I`, the left and right one-sided lifts are an incoming covector
`α ∈ D^in_v` and the outgoing covector `S_v α ∈ D^out_v`, and `γ(t₀) = π(α) = π(S_v α)`.

**Proposition V.5.**  For every `z ∈ P^Reg_S` there is a unique scattered trajectory through `z`.

## Formalization

* `IsEdgeLift V S γ J e c`: on the time set `J`, `c` is a lift of `γ` to the edge cylinder
  `[0, ℓₑ] × ℝ` of `e` — every `c t` is a point of `P̃×` (`AdmissiblePoint`) with
  `γ t = π(e, c t)` (`graphClass`) — which solves the edge Hamilton equations
  `c' = X_e(c)`, `X_e(q, p) = (p, -V_e'(q))` (`edgeVectorField`).
* `IsScatteringImpact V S γ I t₀`: the impact condition at `t₀`.  There are a vertex `v` and an
  incoming covector `α ∈ D^in_v` with `γ t₀ = π(α) = π(S_v α)`, such that every lift of `γ` on an
  interval `(t, t₀)` free of `I` (the left one-sided lift) lies on the edge of `α` and tends to `α`
  as `t → t₀⁻`, and every lift on an interval `(t₀, t)` free of `I` (the right one-sided lift) lies
  on the edge of `S_v α` and tends to `S_v α` as `t → t₀⁺`.  The condition is the same for
  negative `t₀`; read backwards in time it says that the incoming covector of the reversed motion
  is `S_v α` and is sent to `α = S_v⁻¹ (S_v α)`, which is the paper's "read with `S_v⁻¹`".
* `IsScatteredTrajectory V S z γ`: `γ 0 = z` and there is a set `I` meeting every compact set in a
  finite set (locally finite), such that `γ` has an edge lift on every connected component
  `connectedComponentIn Iᶜ t` of `ℝ \ I`, and every `t₀ ∈ I` is a scattering impact.

The main results are

* `flow_isScatteredTrajectory`: `t ↦ Φₜ z` is a scattered trajectory through `z` (existence in
  Proposition V.5), with `I` the set of vertex impacts of eq. (impact) of the paper
  (`flowImpactSet`), which is separated by the no-Zeno constant (`flowImpactSet_separated`,
  Lemmas V.2–V.3);
* `IsScatteredTrajectory.eq_flow` and `IsScatteredTrajectory.unique`: every scattered trajectory
  through `z` is `t ↦ Φₜ z`, so any two coincide (uniqueness in Proposition V.5);
* `existsUnique_scatteredTrajectory`: Proposition V.5.

The uniqueness proof follows the paper's induction over impact intervals in a local form: between
impacts edgewise ODE uniqueness (`flow_val_of_lift`), at an impact the deterministic law
(`flow_val_of_lift_landing`, `flow_val_of_lift` from the outgoing covector), so that every
scattered trajectory agrees with the flow on a neighbourhood of each time, on both sides; the set
of times where it agrees with `t ↦ Φₜ z` is then open with open complement, and it contains `0`.
-/

namespace HamiltonianMetricGraphs

open Set Filter Topology

/-! ### Locally finite sets of times -/

/-- A set of reals meeting every compact set in a finite set has a punctured neighbourhood of
every point which it does not meet. -/
theorem exists_punctured_nhd_disjoint {I : Set ℝ}
    (hI : ∀ K : Set ℝ, IsCompact K → (I ∩ K).Finite) (t : ℝ) :
    ∃ ε > 0, ∀ u ∈ Ioo (t - ε) (t + ε), u ≠ t → u ∉ I := by
  have hF : ((I ∩ Icc (t - 1) (t + 1)) \ {t}).Finite := (hI _ isCompact_Icc).sdiff
  have htF : t ∉ (I ∩ Icc (t - 1) (t + 1)) \ {t} := fun h => h.2 rfl
  have hmem : ((I ∩ Icc (t - 1) (t + 1)) \ {t})ᶜ ∩ Ioo (t - 1) (t + 1) ∈ 𝓝 t :=
    Filter.inter_mem (hF.isClosed.isOpen_compl.mem_nhds htF)
      (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨ε, hε, fun u hu hut huI => ?_⟩
  have hu' : u ∈ Metric.ball t ε := by rw [Real.ball_eq_Ioo]; exact hu
  obtain ⟨hFu, hIoo⟩ := hball hu'
  exact hFu ⟨⟨huI, Ioo_subset_Icc_self hIoo⟩, hut⟩

/-- A locally finite set of reals is closed. -/
theorem isClosed_of_finite_inter_isCompact {I : Set ℝ}
    (hI : ∀ K : Set ℝ, IsCompact K → (I ∩ K).Finite) : IsClosed I := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨ε, hε, hfree⟩ := exists_punctured_nhd_disjoint hI t
  filter_upwards [Ioo_mem_nhds (by linarith : t - ε < t) (by linarith : t < t + ε)] with u hu
  by_cases hut : u = t
  · rw [hut]; exact ht
  · exact hfree u hu hut

/-- A set of reals whose distinct points are separated by a fixed positive distance is locally
finite. -/
theorem finite_inter_isCompact_of_separated {I : Set ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hsep : ∀ s ∈ I, ∀ u ∈ I, s < u → s + τ ≤ u) (K : Set ℝ) (hK : IsCompact K) :
    (I ∩ K).Finite := by
  obtain ⟨m, hm⟩ := hK.bddBelow
  obtain ⟨M, hM⟩ := hK.bddAbove
  have key : ∀ a ∈ I, ∀ b ∈ I, a < b → ⌊a / τ⌋ < ⌊b / τ⌋ := by
    intro a ha b hb hab
    have h1 : a / τ + 1 ≤ b / τ := by
      rw [div_add_one hτ.ne', div_le_div_iff_of_pos_right hτ]
      exact hsep a ha b hb hab
    calc ⌊a / τ⌋ < ⌊a / τ⌋ + 1 := lt_add_one _
      _ = ⌊a / τ + 1⌋ := (Int.floor_add_one _).symm
      _ ≤ ⌊b / τ⌋ := Int.floor_mono h1
  refine Set.Finite.of_finite_image (f := fun t => ⌊t / τ⌋)
    ((Set.finite_Icc ⌊m / τ⌋ ⌊M / τ⌋).subset ?_) ?_
  · rintro _ ⟨t, ⟨-, htK⟩, rfl⟩
    exact ⟨Int.floor_mono (div_le_div_of_nonneg_right (hm htK) hτ.le),
      Int.floor_mono (div_le_div_of_nonneg_right (hM htK) hτ.le)⟩
  · intro s hs u hu hsu
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hsu (key s hs.1 u hu.1 h).ne
    · exact absurd hsu (key u hu.1 s hs.1 h).ne'

/-- The shift `u ↦ u - t` maps right neighbourhoods of `t` to right neighbourhoods of `0`. -/
theorem tendsto_sub_const_nhdsGT (t : ℝ) :
    Tendsto (fun u : ℝ => u - t) (𝓝[>] t) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h := (continuous_sub_right t).tendsto t
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact sub_pos.mpr (mem_Ioi.mp hu)

/-- The shift `u ↦ u - t` maps left neighbourhoods of `s` to left neighbourhoods of `s - t`. -/
theorem tendsto_sub_const_nhdsLT (t s : ℝ) :
    Tendsto (fun u : ℝ => u - t) (𝓝[<] s) (𝓝[<] (s - t)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact ((continuous_sub_right t).tendsto s).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact sub_lt_sub_right hu t

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-! ### Points of the edge cylinders -/

/-- A boundary covector is a point of `P̃×`. -/
theorem admissiblePoint_covector (δ : Γ.BoundaryCovector) :
    Γ.AdmissiblePoint (δ.germ.1, FiniteMetricGraph.EdgeEnd.coordinate Γ δ.germ, δ.momentum) :=
  ⟨Γ.edgeEnd_coordinate_mem_closedEdge δ.germ, Or.inr δ.momentum_ne_zero⟩

/-- An endpoint coordinate is not in the open edge. -/
theorem coordinate_not_mem_Ioo (η : Γ.EdgeEnd) :
    FiniteMetricGraph.EdgeEnd.coordinate Γ η ∉ Ioo (0 : ℝ) (Γ.length η.1) := by
  rcases η with ⟨e, b⟩
  cases b
  · intro h; exact lt_irrefl _ h.1
  · intro h; exact lt_irrefl _ h.2

/-- The class of a boundary covector, read as a point of its edge cylinder. -/
theorem graphClass_covector (δ : Γ.BoundaryCovector) :
    graphClass V S (δ.germ.1, FiniteMetricGraph.EdgeEnd.coordinate Γ δ.germ, δ.momentum) =
      quotientMap (V := V) S (δ.toNonzeroPrequotientPhase Γ) := by
  unfold graphClass
  rw [Γ.graphPoint_covector]

/-- An interior point is not an incoming point. -/
theorem not_isIncomingPoint_graphPoint_of_interior' {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x.1 ∈ Ioo (0 : ℝ) (Γ.length e)) :
    ¬ IsIncomingPoint (V := V) S (Γ.graphPoint (e, x)) := by
  rw [isIncomingPoint_graphPoint_iff V S ⟨Ioo_subset_Icc_self hx, Or.inl hx⟩]
  rintro (⟨h0, -⟩ | ⟨hl, -⟩)
  · exact absurd h0 (ne_of_gt hx.1)
  · exact absurd hl (ne_of_lt hx.2)

/-- The outgoing representative of the class of an interior point is the point itself. -/
theorem rep_graphClass_of_interior {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x.1 ∈ Ioo (0 : ℝ) (Γ.length e)) :
    rep V S (graphClass V S (e, x)) = Γ.graphPoint (e, x) :=
  rep_quotientMap_of_not_incoming V S _ (not_isIncomingPoint_graphPoint_of_interior' V S hx)

/-! ### Definition V.4 -/

/-- **Edge lift.**  On the set of times `J`, `c` lifts `γ` to the edge cylinder `[0, ℓₑ] × ℝ` of
the edge `e` and solves the edge Hamilton equations there: for every `t ∈ J`, `(e, c t)` is a point
of `P̃×` (a point of the closed edge cylinder which is not a zero-momentum vertex state), its class
is `γ t`, and `c' = X_e(c)` at `t`, where `X_e(q, p) = (p, -V_e'(q))`. -/
def IsEdgeLift (γ : ℝ → RegularScatteringPhaseSpace (V := V) S) (J : Set ℝ) (e : Γ.Edge)
    (c : ℝ → ℝ × ℝ) : Prop :=
  ∀ t ∈ J, Γ.AdmissiblePoint (e, c t) ∧ (γ t).1 = graphClass V S (e, c t) ∧
    HasDerivAt c (V.edgeVectorField e (c t)) t

theorem IsEdgeLift.mono {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} {J J' : Set ℝ}
    {e : Γ.Edge} {c : ℝ → ℝ × ℝ} (h : IsEdgeLift V S γ J e c) (hJ : J' ⊆ J) :
    IsEdgeLift V S γ J' e c :=
  fun t ht => h t (hJ ht)

/-- **The impact condition of Definition V.4 at `t₀`.**  There are a vertex `v` and an incoming
covector `α ∈ D^in_v` with `γ t₀ = π(α) = π(S_v α)`, such that the left one-sided lift is `α` and
the right one-sided lift is `S_v α`: every edge lift of `γ` on an interval `(t, t₀)` which does not
meet `I` lies on the edge of `α` and tends to the boundary point `α` of that edge as the time
tends to `t₀` from the left, and every edge lift on an interval `(t₀, t)` which does not meet `I`
lies on the edge of `S_v α` and tends to `S_v α` from the right. -/
def IsScatteringImpact (γ : ℝ → RegularScatteringPhaseSpace (V := V) S) (I : Set ℝ) (t₀ : ℝ) :
    Prop :=
  ∃ (v : Γ.Vertex) (α : Γ.IncomingBoundary v),
    (γ t₀).1 = quotientMap (V := V) S (α.1.toNonzeroPrequotientPhase Γ) ∧
    (γ t₀).1 = quotientMap (V := V) S ((S.map v α).1.toNonzeroPrequotientPhase Γ) ∧
    (∀ t < t₀, Disjoint (Ioo t t₀) I → ∀ (e : Γ.Edge) (c : ℝ → ℝ × ℝ),
      IsEdgeLift V S γ (Ioo t t₀) e c →
        e = α.1.germ.1 ∧
          Tendsto c (𝓝[<] t₀)
            (𝓝 (FiniteMetricGraph.EdgeEnd.coordinate Γ α.1.germ, α.1.momentum))) ∧
    (∀ t > t₀, Disjoint (Ioo t₀ t) I → ∀ (e : Γ.Edge) (c : ℝ → ℝ × ℝ),
      IsEdgeLift V S γ (Ioo t₀ t) e c →
        e = (S.map v α).1.germ.1 ∧
          Tendsto c (𝓝[>] t₀)
            (𝓝 (FiniteMetricGraph.EdgeEnd.coordinate Γ (S.map v α).1.germ,
              (S.map v α).1.momentum)))

/-- The conditions of Definition V.4 on a curve `γ`, for a given set `I` of impact times: `I` is
locally finite (it meets every compact set in a finite set), on every connected component of
`ℝ \ I` the curve has an edge lift, and every `t₀ ∈ I` is a scattering impact. -/
structure IsScatteredTrajectoryWith (γ : ℝ → RegularScatteringPhaseSpace (V := V) S)
    (I : Set ℝ) : Prop where
  locallyFinite : ∀ K : Set ℝ, IsCompact K → (I ∩ K).Finite
  lift : ∀ t ∉ I, ∃ (e : Γ.Edge) (c : ℝ → ℝ × ℝ),
    IsEdgeLift V S γ (connectedComponentIn Iᶜ t) e c
  impact : ∀ t₀ ∈ I, IsScatteringImpact V S γ I t₀

/-- **Definition V.4 (scattered trajectory).**  A scattered trajectory through `z ∈ P^Reg_S` is a
map `γ : ℝ → P^Reg_S` with `γ 0 = z` for which there is a locally finite set `I ⊂ ℝ` such that
`γ` lifts to a single edge cylinder and solves the edge Hamilton equations on every component of
`ℝ \ I`, and at each `t₀ ∈ I` its left and right one-sided lifts are an incoming covector `α` and
`S_v α`, with `γ t₀ = π(α) = π(S_v α)`. -/
def IsScatteredTrajectory (z : RegularScatteringPhaseSpace (V := V) S)
    (γ : ℝ → RegularScatteringPhaseSpace (V := V) S) : Prop :=
  γ 0 = z ∧ ∃ I : Set ℝ, IsScatteredTrajectoryWith V S γ I

variable [Nonempty Γ.Edge]

/-! ### Existence: the flow is a scattered trajectory -/

/-- The vertex impacts of the orbit of `z` (eq. (impact) of the paper): the times at which
`Φₜ z` sits over a vertex. -/
def flowImpactSet (z : RegularScatteringPhaseSpace (V := V) S) : Set ℝ :=
  {t | IsVertexImpactClass V S (flow V S z t).1}

/-- **No-Zeno separation (Lemmas V.2–V.3).**  Distinct vertex impacts of an orbit are separated by
a positive time. -/
theorem flowImpactSet_separated (z : RegularScatteringPhaseSpace (V := V) S) :
    ∃ τ > 0, ∀ s ∈ flowImpactSet V S z, ∀ u ∈ flowImpactSet V S z, s < u → s + τ ≤ u := by
  set E := quotientHamiltonian (V := V) S z.1 with hE
  obtain ⟨τ, hτ, hbound⟩ := FlightState.exists_uniform_impactDuration_lower_bound (V := V) {E}
    isCompact_singleton (fun E' hE' => by rw [mem_singleton_iff.mp hE']; exact z.2)
  refine ⟨τ, hτ, ?_⟩
  rintro s ⟨v, α, hs⟩ u hu hsu
  by_contra hlt
  push Not at hlt
  set w := flow V S z s with hw
  set A := repFlight V S w with hA
  have hout : A.IsOutgoing := repFlight_isOutgoing_of_isVertexImpact V S w α hs
  have henergy : A.energy ∈ ({E} : Set ℝ) := by
    rw [mem_singleton_iff, hA, repFlight_energy, hw, quotientHamiltonian_flow]
  have hh : u - s < τ := by linarith
  have hdur : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state),
      u - s < sSup (PhysicalEdgeSegment.durationSet V A.edge A.state) :=
    fun hbdd => lt_of_lt_of_le hh (hbound A hout henergy hbdd)
  have hval := flow_val_eq_graphClass_flightCurve V S w (sub_pos.mpr hsu).le hdur
  rw [hw, flow_flow, show s + (u - s) = u by ring] at hval
  have hint := FlightState.flightCurve_interior V A (sub_pos.mpr hsu) hdur
  exact not_isVertexImpactClass_graphClass V S hint (hval ▸ hu)

/-- The vertex impacts of an orbit form a locally finite set. -/
theorem flowImpactSet_locallyFinite (z : RegularScatteringPhaseSpace (V := V) S) (K : Set ℝ)
    (hK : IsCompact K) : (flowImpactSet V S z ∩ K).Finite := by
  obtain ⟨τ, hτ, hsep⟩ := flowImpactSet_separated V S z
  exact finite_inter_isCompact_of_separated hτ hsep K hK

/-- On an interval free of vertex impacts, the flight started at its left end lasts at least as
long as the interval. -/
theorem le_sSup_of_disjoint_flowImpactSet (z : RegularScatteringPhaseSpace (V := V) S)
    {s₁ s₂ : ℝ} (hfree : Disjoint (Ioo s₁ s₂) (flowImpactSet V S z))
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V (repFlight V S (flow V S z s₁)).edge
      (repFlight V S (flow V S z s₁)).state)) :
    s₂ - s₁ ≤ sSup (PhysicalEdgeSegment.durationSet V (repFlight V S (flow V S z s₁)).edge
      (repFlight V S (flow V S z s₁)).state) := by
  set A := repFlight V S (flow V S z s₁) with hA
  set d := sSup (PhysicalEdgeSegment.durationSet V A.edge A.state) with hd
  by_contra hlt
  push Not at hlt
  have hd0 : 0 < d := FlightState.impactDuration_pos_of_bddAbove V A hbdd
  have hmem : s₁ + d ∈ Ioo s₁ s₂ := ⟨by linarith, by linarith⟩
  have himp : s₁ + d ∈ flowImpactSet V S z := by
    have h := flow_val_sSup V S (flow V S z s₁) hbdd
    rw [← hA, ← hd, flow_flow, graphClass_flightCurve_sSup V S A hbdd] at h
    exact ⟨_, _, h⟩
  exact Set.disjoint_left.mp hfree hmem himp

/-- On an interval free of vertex impacts, the orbit is the class of the flight started at the
left end of the interval, which runs in the open edge and solves the edge equations. -/
theorem flow_val_of_disjoint_flowImpactSet (z : RegularScatteringPhaseSpace (V := V) S)
    {s₁ s₂ : ℝ} (hfree : Disjoint (Ioo s₁ s₂) (flowImpactSet V S z)) {h : ℝ}
    (hh : h ∈ Ioo 0 (s₂ - s₁)) :
    (flow V S z (s₁ + h)).1 = graphClass V S ((repFlight V S (flow V S z s₁)).edge,
        FlightState.flightCurve V (repFlight V S (flow V S z s₁)) h) ∧
      (FlightState.flightCurve V (repFlight V S (flow V S z s₁)) h).1 ∈
        Ioo (0 : ℝ) (Γ.length (repFlight V S (flow V S z s₁)).edge) ∧
      HasDerivAt (FlightState.flightCurve V (repFlight V S (flow V S z s₁)))
        (V.edgeVectorField (repFlight V S (flow V S z s₁)).edge
          (FlightState.flightCurve V (repFlight V S (flow V S z s₁)) h)) h := by
  have hdur : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V
      (repFlight V S (flow V S z s₁)).edge (repFlight V S (flow V S z s₁)).state),
      h < sSup (PhysicalEdgeSegment.durationSet V (repFlight V S (flow V S z s₁)).edge
        (repFlight V S (flow V S z s₁)).state) :=
    fun hbdd => lt_of_lt_of_le hh.2 (le_sSup_of_disjoint_flowImpactSet V S z hfree hbdd)
  refine ⟨?_, FlightState.flightCurve_interior V _ hh.1 hdur,
    FlightState.flightCurve_hasDerivAt V _ hh.1 hdur⟩
  rw [← flow_flow]
  exact flow_val_eq_graphClass_flightCurve V S _ hh.1.le hdur

/-- **Lifts of the orbit on the components of `ℝ \ I`.**  On every connected component of the
complement of the vertex impacts, the orbit has an edge lift: the outgoing representative of
`Φₜ z`, which stays on one edge and solves the edge equations. -/
theorem flow_lift_component (z : RegularScatteringPhaseSpace (V := V) S) {t : ℝ}
    (ht : t ∉ flowImpactSet V S z) :
    ∃ (e : Γ.Edge) (c : ℝ → ℝ × ℝ), IsEdgeLift V S (flow V S z)
      (connectedComponentIn (flowImpactSet V S z)ᶜ t) e c := by
  set I := flowImpactSet V S z with hI
  set J := connectedComponentIn Iᶜ t with hJ
  have hIc : IsClosed I :=
    isClosed_of_finite_inter_isCompact (flowImpactSet_locallyFinite V S z)
  have hJo : IsOpen J := hIc.isOpen_compl.connectedComponentIn
  have hJsub : J ⊆ Iᶜ := connectedComponentIn_subset _ _
  have htJ : t ∈ J := mem_connectedComponentIn ht
  have hJord : J.OrdConnected := isPreconnected_connectedComponentIn.ordConnected
  refine ⟨(rep V S (flow V S z t).1).1.1, fun s => (rep V S (flow V S z s).1).1.2.1, ?_⟩
  intro s hs
  have hm : min s t ∈ J := by
    rcases min_choice s t with h | h <;> rw [h] <;> assumption
  have hM : max s t ∈ J := by
    rcases max_choice s t with h | h <;> rw [h] <;> assumption
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.mp hJo _ hm
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.isOpen_iff.mp hJo _ hM
  set s₁ := min s t - ε₁ / 2 with hs₁def
  set s₂ := max s t + ε₂ / 2 with hs₂def
  have hs₁ : s₁ ∈ J := hb₁ (by rw [Real.ball_eq_Ioo]; constructor <;> linarith)
  have hs₂ : s₂ ∈ J := hb₂ (by rw [Real.ball_eq_Ioo]; constructor <;> linarith)
  have hfree : Disjoint (Ioo s₁ s₂) I := Set.disjoint_left.mpr fun u hu huI =>
    hJsub (hJord.out hs₁ hs₂ (Ioo_subset_Icc_self hu)) huI
  set A := repFlight V S (flow V S z s₁) with hA
  have hcan : ∀ u ∈ Ioo s₁ s₂, (rep V S (flow V S z u).1).1.1 = A.edge ∧
      (rep V S (flow V S z u).1).1.2.1 = FlightState.flightCurve V A (u - s₁) ∧
      (flow V S z u).1 = graphClass V S (A.edge, FlightState.flightCurve V A (u - s₁)) ∧
      (FlightState.flightCurve V A (u - s₁)).1 ∈ Ioo (0 : ℝ) (Γ.length A.edge) ∧
      HasDerivAt (FlightState.flightCurve V A)
        (V.edgeVectorField A.edge (FlightState.flightCurve V A (u - s₁))) (u - s₁) := by
    intro u hu
    obtain ⟨hval, hint, hder⟩ := flow_val_of_disjoint_flowImpactSet V S z hfree
      (h := u - s₁) ⟨sub_pos.mpr hu.1, by linarith [hu.2]⟩
    rw [show s₁ + (u - s₁) = u by ring] at hval
    have hadm : Γ.AdmissiblePoint (A.edge, FlightState.flightCurve V A (u - s₁)) :=
      ⟨Ioo_subset_Icc_self hint, Or.inl hint⟩
    have hrep : rep V S (flow V S z u).1 =
        Γ.graphPoint (A.edge, FlightState.flightCurve V A (u - s₁)) := by
      rw [hval]
      exact rep_graphClass_of_interior V S hint
    rw [hrep]
    exact ⟨Γ.graphPoint_edge hadm, Γ.graphPoint_state hadm, hval, hint, hder⟩
  have hsI : s ∈ Ioo s₁ s₂ := ⟨by
    have := min_le_left s t; linarith, by have := le_max_left s t; linarith⟩
  have htI : t ∈ Ioo s₁ s₂ := ⟨by
    have := min_le_right s t; linarith, by have := le_max_right s t; linarith⟩
  obtain ⟨hedge_t, -⟩ := hcan t htI
  obtain ⟨-, hstate_s, hval_s, hint_s, hder_s⟩ := hcan s hsI
  simp only
  rw [hedge_t, hstate_s]
  refine ⟨⟨Ioo_subset_Icc_self hint_s, Or.inl hint_s⟩, hval_s, ?_⟩
  have hshift : HasDerivAt (fun u => FlightState.flightCurve V A (u - s₁))
      (V.edgeVectorField A.edge (FlightState.flightCurve V A (s - s₁))) s :=
    hder_s.comp_sub_const s s₁
  refine hshift.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hsI.1 hsI.2] with u hu
  exact (hcan u hu).2.1

/-- **The impact condition along the orbit.**  At every vertex impact `t₀` of the orbit, with
`Φ_{t₀} z = π(α)`, the left lifts tend to `α` and the right lifts tend to `S_v α`. -/
theorem flow_isScatteringImpact (z : RegularScatteringPhaseSpace (V := V) S) {t₀ : ℝ}
    (ht₀ : t₀ ∈ flowImpactSet V S z) :
    IsScatteringImpact V S (flow V S z) (flowImpactSet V S z) t₀ := by
  obtain ⟨v, α, hα⟩ := ht₀
  refine ⟨v, α, hα, hα.trans (quotientMap_scatter V S α), ?_, ?_⟩
  · -- the left one-sided lift
    intro t htt₀ hfree e c hlift
    set A := repFlight V S (flow V S z t) with hA
    have hD : 0 < t₀ - t := sub_pos.mpr htt₀
    -- the flight from `t` lands exactly at `t₀`
    have hland : ∃ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state),
        sSup (PhysicalEdgeSegment.durationSet V A.edge A.state) = t₀ - t := by
      by_contra hno
      have hdur : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state),
          t₀ - t < sSup (PhysicalEdgeSegment.durationSet V A.edge A.state) := by
        intro hbdd
        rcases eq_or_lt_of_le (le_sSup_of_disjoint_flowImpactSet V S z hfree hbdd) with h | h
        · exact absurd ⟨hbdd, h.symm⟩ hno
        · exact h
      have hval := flow_val_eq_graphClass_flightCurve V S (flow V S z t) hD.le hdur
      rw [flow_flow, show t + (t₀ - t) = t₀ by ring] at hval
      exact not_isVertexImpactClass_graphClass V S
        (FlightState.flightCurve_interior V A hD hdur) (hval ▸ ⟨v, α, hα⟩)
    obtain ⟨hbdd, hd⟩ := hland
    -- the arrival covector of that flight is `α`
    have hval := flow_val_sSup V S (flow V S z t) hbdd
    rw [← hA, graphClass_flightCurve_sSup V S A hbdd, hd, flow_flow,
      show t + (t₀ - t) = t₀ by ring, hα] at hval
    have hαeq : A.segment.maximalArrivalCovector hbdd A.regular = α.1 :=
      (incoming_eq_of_quotientMap_eq V S _ _ hval).symm
    have harr := flightCurve_sSup_eq_arrival V A hbdd
    rw [hd, hαeq] at harr
    have hAedge : A.edge = α.1.germ.1 := congrArg Prod.fst harr
    have hAend : FlightState.flightCurve V A (t₀ - t) =
        (FiniteMetricGraph.EdgeEnd.coordinate Γ α.1.germ, α.1.momentum) := congrArg Prod.snd harr
    -- any lift on `(t, t₀)` is the flight of `A`
    have hcmp : ∀ u ∈ Ioo t t₀, e = A.edge ∧ c u = FlightState.flightCurve V A (u - t) := by
      intro u hu
      obtain ⟨hval', hint, -⟩ := flow_val_of_disjoint_flowImpactSet V S z hfree
        (h := u - t) ⟨sub_pos.mpr hu.1, by linarith [hu.2]⟩
      rw [show t + (u - t) = u by ring] at hval'
      obtain ⟨hadm, hγu, -⟩ := hlift u hu
      exact eq_of_graphClass_eq_of_interior V S hint hadm (hval'.symm.trans hγu)
    refine ⟨(hcmp ((t + t₀) / 2) ⟨by linarith, by linarith⟩).1.trans hAedge, ?_⟩
    rw [← hAend]
    have hlim := (tendsto_flightCurve_nhdsLT V A hD
      (fun hb => le_sSup_of_disjoint_flowImpactSet V S z hfree hb)).comp
      (tendsto_sub_const_nhdsLT t t₀)
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT htt₀] with u hu
    exact ((hcmp u hu).2).symm
  · -- the right one-sided lift
    intro t htt₀ hfree e c hlift
    set A := repFlight V S (flow V S z t₀) with hA
    obtain ⟨hAedge, hAstate⟩ := repFlight_of_isVertexImpact V S (flow V S z t₀) α hα
    have hcmp : ∀ u ∈ Ioo t₀ t, e = A.edge ∧ c u = FlightState.flightCurve V A (u - t₀) := by
      intro u hu
      obtain ⟨hval', hint, -⟩ := flow_val_of_disjoint_flowImpactSet V S z hfree
        (h := u - t₀) ⟨sub_pos.mpr hu.1, by linarith [hu.2]⟩
      rw [show t₀ + (u - t₀) = u by ring] at hval'
      obtain ⟨hadm, hγu, -⟩ := hlift u hu
      exact eq_of_graphClass_eq_of_interior V S hint hadm (hval'.symm.trans hγu)
    refine ⟨(hcmp ((t₀ + t) / 2) ⟨by linarith, by linarith⟩).1.trans hAedge, ?_⟩
    rw [← hAstate]
    have hlim := (tendsto_flightCurve_nhdsGT_zero V A).comp (tendsto_sub_const_nhdsGT t₀)
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT htt₀] with u hu
    exact ((hcmp u hu).2).symm

/-- **Proposition V.5, existence.**  The orbit `t ↦ Φₜ z` of the scattered evolution is a scattered
trajectory through `z`; its impact set is the set of vertex impacts of eq. (impact). -/
theorem flow_isScatteredTrajectory (z : RegularScatteringPhaseSpace (V := V) S) :
    IsScatteredTrajectory V S z (flow V S z) :=
  ⟨flow_zero V S z, flowImpactSet V S z,
    { locallyFinite := flowImpactSet_locallyFinite V S z
      lift := fun _ ht => flow_lift_component V S z ht
      impact := fun _ ht₀ => flow_isScatteringImpact V S z ht₀ }⟩

/-! ### Uniqueness -/

section Uniqueness

variable {V S}

omit [Nonempty Γ.Edge] in
/-- An edge lift on an open set stays in the open edge. -/
theorem IsEdgeLift.interior {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} {J : Set ℝ}
    {e : Γ.Edge} {c : ℝ → ℝ × ℝ} (h : IsEdgeLift V S γ J e c) (hJ : IsOpen J) {s : ℝ}
    (hs : s ∈ J) : (c s).1 ∈ Ioo (0 : ℝ) (Γ.length e) :=
  position_mem_Ioo_of_edgeSolution V hJ (fun u hu => ⟨(h u hu).1, (h u hu).2.2⟩) hs

omit [Nonempty Γ.Edge] in
/-- An edge lift on an open interval in the form used by `flow_val_of_lift`. -/
theorem IsEdgeLift.solution {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} {a b : ℝ}
    {e : Γ.Edge} {c : ℝ → ℝ × ℝ} (h : IsEdgeLift V S γ (Ioo a b) e c) :
    ∀ s ∈ Ioo a b, HasDerivAt c (V.edgeVectorField e (c s)) s ∧
      (c s).1 ∈ Ioo (0 : ℝ) (Γ.length e) :=
  fun s hs => ⟨(h s hs).2.2, h.interior isOpen_Ioo hs⟩

omit [Nonempty Γ.Edge] in
/-- An edge lift on a set `J'` free of `I` which is preconnected and contains a point of
`ℝ \ I`, obtained from the lift on the component of that point. -/
theorem IsScatteredTrajectoryWith.exists_lift {γ : ℝ → RegularScatteringPhaseSpace (V := V) S}
    {I : Set ℝ} (hγ : IsScatteredTrajectoryWith V S γ I) {J' : Set ℝ} (hJ' : IsPreconnected J')
    (hJ'I : Disjoint J' I) {u : ℝ} (hu : u ∈ J') :
    ∃ (e : Γ.Edge) (c : ℝ → ℝ × ℝ), IsEdgeLift V S γ J' e c := by
  have huI : u ∉ I := Set.disjoint_left.mp hJ'I hu
  obtain ⟨e, c, hc⟩ := hγ.lift u huI
  exact ⟨e, c, hc.mono V S (hJ'.subset_connectedComponentIn hu
    (fun x hx => Set.disjoint_left.mp hJ'I hx))⟩

/-- **Right agreement.**  A scattered trajectory agrees with the flow of its own value for a short
positive time after every time `t`. -/
theorem IsScatteredTrajectoryWith.right_flow {γ : ℝ → RegularScatteringPhaseSpace (V := V) S}
    {I : Set ℝ} (hγ : IsScatteredTrajectoryWith V S γ I) (t : ℝ) :
    ∃ ε > 0, ∀ h ∈ Ioo 0 ε, γ (t + h) = flow V S (γ t) h := by
  obtain ⟨ε, hε, hfree⟩ := exists_punctured_nhd_disjoint hγ.locallyFinite t
  have hdisj : Disjoint (Ioo t (t + ε)) I := Set.disjoint_left.mpr fun u hu =>
    hfree u ⟨by linarith [hu.1], hu.2⟩ (ne_of_gt hu.1)
  obtain ⟨e, c, hc⟩ := hγ.exists_lift isPreconnected_Ioo hdisj
    (show t + ε / 2 ∈ Ioo t (t + ε) from ⟨by linarith, by linarith⟩)
  refine ⟨ε, hε, fun h hh => Subtype.ext ?_⟩
  have hht : t + h ∈ Ioo t (t + ε) := ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hh' : h ∈ Ioo 0 (t + ε - t) := by rw [add_sub_cancel_left]; exact hh
  rw [(hc (t + h) hht).2.1]
  by_cases htI : t ∈ I
  · -- `t` is an impact: start from the outgoing covector `S_v α`
    obtain ⟨v, α, -, hαS, -, hright⟩ := hγ.impact t htI
    obtain ⟨he, hlim⟩ := hright (t + ε) (by linarith) hdisj e c hc
    subst he
    refine (flow_val_of_lift V S (γ t) (admissiblePoint_covector (S.map v α).1) ?_ ?_
      hc.solution hlim hh').symm
    · rw [Γ.graphPoint_covector]
      exact scatteringStep_target_notIncoming (V := V) S ⟨v, α, rfl, rfl⟩
    · rw [hαS, graphClass_covector]
  · -- `t` is not an impact: start from the lift at `t`
    obtain ⟨e', c', hc'⟩ := hγ.lift t htI
    have hJo : IsOpen (connectedComponentIn Iᶜ t) :=
      (isClosed_of_finite_inter_isCompact hγ.locallyFinite).isOpen_compl.connectedComponentIn
    have htJ : t ∈ connectedComponentIn Iᶜ t := mem_connectedComponentIn htI
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hJo t htJ
    have hsub : Ioo (t - δ) (t + δ) ⊆ connectedComponentIn Iᶜ t := by
      rw [← Real.ball_eq_Ioo]; exact hball
    -- the two lifts agree on `(t, t + min ε δ)`
    have hint' := hc'.interior hJo htJ
    obtain ⟨hadm', hγt, hder'⟩ := hc' t htJ
    have hagree : ∀ u ∈ Ioo t (t + min ε δ), e = e' ∧ c u = c' u := by
      intro u hu
      have hu1 : u ∈ Ioo t (t + ε) := ⟨hu.1, by linarith [hu.2, min_le_left ε δ]⟩
      have hu2 : u ∈ connectedComponentIn Iᶜ t :=
        hsub ⟨by linarith [hu.1], by linarith [hu.2, min_le_right ε δ]⟩
      obtain ⟨hadm, hγu, -⟩ := hc u hu1
      obtain ⟨-, hγu', -⟩ := hc' u hu2
      exact eq_of_graphClass_eq_of_interior V S (hc'.interior hJo hu2) hadm
        (hγu'.symm.trans hγu)
    have hεδ : 0 < min ε δ := lt_min hε hδ
    obtain ⟨he, -⟩ := hagree (t + min ε δ / 2) ⟨by linarith, by linarith⟩
    subst he
    have hlim : Tendsto c (𝓝[>] t) (𝓝 (c' t)) := by
      refine (hder'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show t < t + min ε δ by linarith)] with u hu
      exact ((hagree u hu).2).symm
    exact (flow_val_of_lift V S (γ t) hadm'
      (not_isIncomingPoint_graphPoint_of_interior' V S hint') hγt hc.solution hlim hh').symm

/-- **Left agreement.**  A scattered trajectory at time `t` is the flow, for a short time `h`, of
its own value at `t - h`. -/
theorem IsScatteredTrajectoryWith.left_flow {γ : ℝ → RegularScatteringPhaseSpace (V := V) S}
    {I : Set ℝ} (hγ : IsScatteredTrajectoryWith V S γ I) (t : ℝ) :
    ∃ ε > 0, ∀ h ∈ Ioo 0 ε, γ t = flow V S (γ (t - h)) h := by
  obtain ⟨ε, hε, hfree⟩ := exists_punctured_nhd_disjoint hγ.locallyFinite t
  have hdisj : Disjoint (Ioo (t - ε) t) I := Set.disjoint_left.mpr fun u hu =>
    hfree u ⟨hu.1, by linarith [hu.2]⟩ (ne_of_lt hu.2)
  obtain ⟨e, c, hc⟩ := hγ.exists_lift isPreconnected_Ioo hdisj
    (show t - ε / 2 ∈ Ioo (t - ε) t from ⟨by linarith, by linarith⟩)
  refine ⟨ε, hε, fun h hh => Subtype.ext ?_⟩
  have hht : t - h ∈ Ioo (t - ε) t := ⟨by linarith [hh.2], by linarith [hh.1]⟩
  obtain ⟨hadm, hγth, hder⟩ := hc (t - h) hht
  have hint := hc.interior isOpen_Ioo hht
  have hsol : ∀ s ∈ Ioo (t - h) t, HasDerivAt c (V.edgeVectorField e (c s)) s ∧
      (c s).1 ∈ Ioo (0 : ℝ) (Γ.length e) :=
    fun s hs => hc.solution s ⟨by linarith [hs.1, hh.2], hs.2⟩
  have hlim0 : Tendsto c (𝓝[>] (t - h)) (𝓝 (c (t - h))) :=
    hder.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hnot := not_isIncomingPoint_graphPoint_of_interior' V S (e := e) hint
  by_cases htI : t ∈ I
  · -- `t` is an impact: the lift lands at the incoming covector `α`
    obtain ⟨v, α, hα, -, hleft, -⟩ := hγ.impact t htI
    obtain ⟨he, hlim⟩ := hleft (t - ε) (by linarith) hdisj e c hc
    subst he
    have hland := flow_val_of_lift_landing V S (γ (t - h)) hadm hnot hγth
      (show t - h < t by linarith [hh.1]) hsol hlim0 (coordinate_not_mem_Ioo α.1.germ) hlim
    rw [show t - (t - h) = h by ring] at hland
    rw [hland, hα, graphClass_covector]
  · -- `t` is not an impact: the lift continues through `t`
    obtain ⟨e', c', hc'⟩ := hγ.lift t htI
    have hJo : IsOpen (connectedComponentIn Iᶜ t) :=
      (isClosed_of_finite_inter_isCompact hγ.locallyFinite).isOpen_compl.connectedComponentIn
    have htJ : t ∈ connectedComponentIn Iᶜ t := mem_connectedComponentIn htI
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hJo t htJ
    have hsub : Ioo (t - δ) (t + δ) ⊆ connectedComponentIn Iᶜ t := by
      rw [← Real.ball_eq_Ioo]; exact hball
    -- glue the two lifts along their overlap
    have hpre : IsPreconnected (Ioo (t - ε) t ∪ connectedComponentIn Iᶜ t) := by
      refine isPreconnected_Ioo.union (t - min ε δ / 2) ⟨?_, ?_⟩ ?_
        isPreconnected_connectedComponentIn
      · linarith [min_le_left ε δ, lt_min hε hδ]
      · linarith [lt_min hε hδ]
      · exact hsub ⟨by linarith [min_le_right ε δ, lt_min hε hδ], by linarith [lt_min hε hδ]⟩
    have hJ'I : Disjoint (Ioo (t - ε) t ∪ connectedComponentIn Iᶜ t) I :=
      Set.disjoint_union_left.mpr ⟨hdisj, Set.disjoint_left.mpr fun x hx =>
        connectedComponentIn_subset _ _ hx⟩
    obtain ⟨e'', c'', hc''⟩ := hγ.exists_lift hpre hJ'I (Or.inr htJ)
    -- `c''` is a lift on the open set `(t - ε, t) ∪ J`, so it agrees with `c` on `(t - ε, t)`
    have hUo : IsOpen (Ioo (t - ε) t ∪ connectedComponentIn Iᶜ t) := isOpen_Ioo.union hJo
    have hagree : ∀ u ∈ Ioo (t - ε) t, e = e'' ∧ c u = c'' u := by
      intro u hu
      obtain ⟨hadmu, hγu, -⟩ := hc u hu
      obtain ⟨-, hγu'', -⟩ := hc'' u (Or.inl hu)
      exact eq_of_graphClass_eq_of_interior V S (hc''.interior hUo (Or.inl hu)) hadmu
        (hγu''.symm.trans hγu)
    obtain ⟨he, -⟩ := hagree (t - h) hht
    subst he
    obtain ⟨hadm'', hγt'', -⟩ := hc'' t (Or.inr htJ)
    have hsol'' : ∀ s ∈ Ioo (t - h) (t + δ), HasDerivAt c'' (V.edgeVectorField e (c'' s)) s ∧
        (c'' s).1 ∈ Ioo (0 : ℝ) (Γ.length e) := by
      intro s hs
      have hsU : s ∈ Ioo (t - ε) t ∪ connectedComponentIn Iᶜ t := by
        rcases lt_or_ge s t with hst | hst
        · exact Or.inl ⟨by linarith [hs.1, hh.2], hst⟩
        · exact Or.inr (hsub ⟨by linarith, hs.2⟩)
      exact ⟨(hc'' s hsU).2.2, hc''.interior hUo hsU⟩
    have hlim'' : Tendsto c'' (𝓝[>] (t - h)) (𝓝 (c (t - h))) := by
      rw [(hagree (t - h) hht).2]
      exact (hc'' (t - h) (Or.inl hht)).2.2.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hval := flow_val_of_lift V S (γ (t - h)) hadm hnot hγth hsol'' hlim'' (h := h)
      ⟨hh.1, by linarith⟩
    rw [show t - h + h = t by ring] at hval
    rw [hval, hγt'']

/-- **Proposition V.5, uniqueness.**  Every scattered trajectory through `z` is the orbit
`t ↦ Φₜ z`. -/
theorem IsScatteredTrajectory.eq_flow {z : RegularScatteringPhaseSpace (V := V) S}
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} (hγ : IsScatteredTrajectory V S z γ) :
    γ = flow V S z := by
  obtain ⟨h0, I, hI⟩ := hγ
  set A : Set ℝ := {t | γ t = flow V S z t} with hA
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨ε₁, hε₁, hR⟩ := hI.right_flow t
    obtain ⟨ε₂, hε₂, hL⟩ := hI.left_flow t
    filter_upwards [Ioo_mem_nhds (show t - ε₂ < t by linarith) (show t < t + ε₁ by linarith)]
      with u hu
    rcases lt_trichotomy u t with hut | hut | hut
    · have hh : t - u ∈ Ioo 0 ε₂ := ⟨by linarith, by linarith [hu.1]⟩
      have h1 := hL (t - u) hh
      rw [show t - (t - u) = u by ring] at h1
      change γ t = flow V S z t at ht
      have h2 : flow V S (flow V S z u) (t - u) = flow V S z t := by
        rw [flow_flow, show u + (t - u) = t by ring]
      exact (flow_bijective V S (t - u)).1 (h1.symm.trans (ht.trans h2.symm))
    · rw [hut]; exact ht
    · have hh : u - t ∈ Ioo 0 ε₁ := ⟨by linarith, by linarith [hu.2]⟩
      have h1 := hR (u - t) hh
      rw [show t + (u - t) = u by ring] at h1
      change γ u = flow V S z u
      change γ t = flow V S z t at ht
      rw [h1, ht, flow_flow, show t + (u - t) = u by ring]
  have hclosed : IsOpen Aᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨ε₁, hε₁, hR⟩ := hI.right_flow t
    obtain ⟨ε₂, hε₂, hL⟩ := hI.left_flow t
    filter_upwards [Ioo_mem_nhds (show t - ε₂ < t by linarith) (show t < t + ε₁ by linarith)]
      with u hu hAu
    apply ht
    change γ u = flow V S z u at hAu
    change γ t = flow V S z t
    rcases lt_trichotomy u t with hut | hut | hut
    · have hh : t - u ∈ Ioo 0 ε₂ := ⟨by linarith, by linarith [hu.1]⟩
      have h1 := hL (t - u) hh
      rw [show t - (t - u) = u by ring] at h1
      rw [h1, hAu, flow_flow, show u + (t - u) = t by ring]
    · rw [← hut]; exact hAu
    · have hh : u - t ∈ Ioo 0 ε₁ := ⟨by linarith, by linarith [hu.2]⟩
      have h1 := hR (u - t) hh
      rw [show t + (u - t) = u by ring] at h1
      have h2 : flow V S (flow V S z t) (u - t) = flow V S z u := by
        rw [flow_flow, show t + (u - t) = u by ring]
      exact (flow_bijective V S (u - t)).1 (h1.symm.trans (hAu.trans h2.symm))
  have hclopen : IsClopen A := ⟨isOpen_compl_iff.mp hclosed, hopen⟩
  have h0A : (0 : ℝ) ∈ A := by
    change γ 0 = flow V S z 0
    rw [h0, flow_zero]
  rcases isClopen_iff.mp hclopen with h | h
  · rw [h] at h0A; exact absurd h0A (notMem_empty 0)
  · funext t
    have ht : t ∈ A := by rw [h]; exact mem_univ t
    exact ht

/-- **Proposition V.5, uniqueness.**  Any two scattered trajectories through the same point
coincide. -/
theorem IsScatteredTrajectory.unique {z : RegularScatteringPhaseSpace (V := V) S}
    {γ₁ γ₂ : ℝ → RegularScatteringPhaseSpace (V := V) S}
    (h₁ : IsScatteredTrajectory V S z γ₁) (h₂ : IsScatteredTrajectory V S z γ₂) : γ₁ = γ₂ :=
  h₁.eq_flow.trans h₂.eq_flow.symm

end Uniqueness

/-- **Proposition V.5 (existence and uniqueness).**  For every `z ∈ P^Reg_S` there is a unique
scattered trajectory `γ_z : ℝ → P^Reg_S` through `z`; it is the orbit `t ↦ Φₜ z`. -/
theorem existsUnique_scatteredTrajectory (z : RegularScatteringPhaseSpace (V := V) S) :
    ∃! γ : ℝ → RegularScatteringPhaseSpace (V := V) S, IsScatteredTrajectory V S z γ :=
  ⟨flow V S z, flow_isScatteredTrajectory V S z, fun _ hγ => hγ.eq_flow⟩

end MechanicalPotential

end HamiltonianMetricGraphs
