/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition VIII.7: the bifurcation set of the end-step permutation
-/

import HamiltonianMetricGraphs.ShellRegularity

/-!
# The bifurcation set (Proposition VIII.7)

At a shell-regular energy `E` the dynamics on the energy shell is the suspension of the end
permutation `Π_E = F_E ∘ κ_E` of the admissible ends `G_E` (`germStep`, `allowedGerms`,
`shellGermPerm` of `Structure.lean`; Definition VIII.4 and Theorem VIII.5).  This file proves
Proposition VIII.7 of the paper, except its statement on real-analyticity of the periods: the
end permutation, and with it its cycle structure, is locally constant in the energy away from
an explicit bifurcation set.

## The analytic part: regular windows

`BifurcationWindow E₀ E` says that the closed energy interval between `E₀` and `E` contains no
vertex value and no value of an edge potential `V_e` at an interior critical point.  The maximum
or minimum of `V_e` on any subinterval of the closed edge is attained at an end of the subinterval
or at an interior critical point, and this gives, for energies spanning a window:

* `BifurcationWindow.edge_dichotomy`: on every edge either `V_e` lies below both energies on the
  whole closed edge, or it exceeds both somewhere — the maximum of `V_e` is not in the window;
* `BifurcationWindow.allowedComponentsReachEnds'`: condition (ii) of Lemma VIII.2 (every component
  of `{V_e ≤ E}` meets an endpoint) passes from `E₀` to `E`: the bottom of a well at `E` is an
  interior critical point below the window and its two barriers rise above the window, so the
  well exists at `E₀` as well;
* `eventually_bifurcationWindow`: if `E₀` is neither a vertex value nor an interior critical value,
  all energies near `E₀` span a window with it, because the critical values of `V_e` on the
  compact critical set of the closed edge (`V_e` is `C²` on an open set containing the closed
  edge) form a compact set.

Lemma VIII.2 enters through `shellRegular_iff` of `ShellRegularity.lean`.  With it,
shell-regularity is an open condition (`eventually_shellRegular_bifurcationWindow`).

## The dynamical part: the retrace step

At a shell-regular energy the retrace step `κ_E` of a germ on the edge `e` is decided by the
potential alone:

* `retraceStep_fst_of_forall_lt`: if `V_e < E` on the closed edge, the momentum never vanishes, so
  the flight keeps the sign of its departure momentum and lands at the opposite end;
* `retraceStep_fst_of_exists_gt`: if `V_e > E` somewhere, the flight cannot reach the opposite
  end, since by the intermediate value theorem it would pass a point of negative kinetic energy;
  it returns to its own end.

Hence `κ_E` is constant across a window (`retraceStep_fst_eq_of_bifurcationWindow`).
`germStep_eq_speedPermutation` writes the germ step as `F_v(κ_E η, r)` with the fixed-speed vertex
permutation `F_v(·, r)` of Proposition III.2 (`speedPermutation`) at the landing speed
`r = √(2(E - V(v)))`.

## Main results

* `bifurcation_locallyConstant` — **Proposition VIII.7**: if `E₀` is shell-regular and every
  `F_v(·, r)` with `V(v) < E₀` is constant for `r` near `r_v(E₀)`, then for all `E` near `E₀`,
  `E` is shell-regular, `G_E = G_{E₀}` and `Π_E = Π_{E₀}`;
* `bifurcation_cycleType_locallyConstant` — in particular the cycle type of the end permutation
  is locally constant;
* `bifurcationEnergies`, `locallyConstant_of_notMem_bifurcationEnergies`,
  `mem_bifurcationEnergies_of_frequently_cycleType_ne` — the "consequently" sentence: if the cycle
  structure changes arbitrarily close to `E₀`, then `E₀` is a vertex value, an interior critical
  value of an edge potential, or an energy `V(v) + r²/2` at which `r ↦ F_v(·, r)` is
  discontinuous (`speedPermutation_eventually_eq_iff_continuousAt`).
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter PhysicalEdgeSegment
open scoped Topology

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### Endpoint values and extremal points of an edge potential -/

private theorem extension_zero_eq (e : Γ.Edge) :
    V.extension e 0 = V.vertexValue (Γ.endpoint e false) :=
  V.endpoint_value (e, false)

private theorem extension_length_eq (e : Γ.Edge) :
    V.extension e (Γ.length e) = V.vertexValue (Γ.endpoint e true) :=
  V.endpoint_value (e, true)

private theorem continuousOn_extension_Icc {e : Γ.Edge} {a b : ℝ} (ha : 0 ≤ a)
    (hb : b ≤ Γ.length e) : ContinuousOn (V.extension e) (Icc a b) :=
  (V.extension_continuousOn_closedEdge e).mono (Icc_subset_Icc ha hb)

/-- The derivative of an edge potential is continuous on the closed edge (the potential is `C²`
on an open neighbourhood of it). -/
private theorem continuousOn_deriv_extension (e : Γ.Edge) :
    ContinuousOn (deriv (V.extension e)) (Icc 0 (Γ.length e)) :=
  ((V.contDiffOn_extension e).continuousOn_deriv_of_isOpen (V.domain_isOpen e)
    (by norm_num)).mono (V.closedEdge_subset_domain e)

private theorem notMem_uIcc_iff {x a b : ℝ} :
    x ∉ uIcc a b ↔ (x < a ∧ x < b) ∨ (a < x ∧ b < x) := by
  rw [mem_uIcc]
  constructor
  · intro h
    rcases lt_or_ge x a with hxa | hxa <;> rcases lt_or_ge x b with hxb | hxb
    · exact Or.inl ⟨hxa, hxb⟩
    · exact absurd (Or.inr ⟨hxb, hxa.le⟩) h
    · exact absurd (Or.inl ⟨hxa, hxb.le⟩) h
    · rcases eq_or_lt_of_le hxa with hxa' | hxa'
      · exact absurd (Or.inr ⟨hxb, hxa'.ge⟩) h
      · rcases eq_or_lt_of_le hxb with hxb' | hxb'
        · exact absurd (Or.inl ⟨hxa, hxb'.ge⟩) h
        · exact Or.inr ⟨hxa', hxb'⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) (⟨h3, h4⟩ | ⟨h3, h4⟩) <;> linarith

/-- On a subinterval `[a, b]` of the closed edge, `V_e` attains its maximum at a point which is
either an end of `[a, b]` or an interior critical point of `V_e`. -/
private theorem exists_isMaxOn_Icc {e : Γ.Edge} {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    (hb : b ≤ Γ.length e) :
    ∃ m ∈ Icc a b, IsMaxOn (V.extension e) (Icc a b) m ∧
      (m = a ∨ m = b ∨ (m ∈ Ioo a b ∧ deriv (V.extension e) m = 0)) := by
  obtain ⟨m, hm, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) (V.continuousOn_extension_Icc ha hb)
  refine ⟨m, hm, hmax, ?_⟩
  rcases eq_or_lt_of_le hm.1 with h | h
  · exact Or.inl h.symm
  rcases eq_or_lt_of_le hm.2 with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr ⟨⟨h, h'⟩, (hmax.isLocalMax (Icc_mem_nhds h h')).deriv_eq_zero⟩)

/-- The minimum version of `exists_isMaxOn_Icc`. -/
private theorem exists_isMinOn_Icc {e : Γ.Edge} {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    (hb : b ≤ Γ.length e) :
    ∃ m ∈ Icc a b, IsMinOn (V.extension e) (Icc a b) m ∧
      (m = a ∨ m = b ∨ (m ∈ Ioo a b ∧ deriv (V.extension e) m = 0)) := by
  obtain ⟨m, hm, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) (V.continuousOn_extension_Icc ha hb)
  refine ⟨m, hm, hmin, ?_⟩
  rcases eq_or_lt_of_le hm.1 with h | h
  · exact Or.inl h.symm
  rcases eq_or_lt_of_le hm.2 with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr ⟨⟨h, h'⟩, (hmin.isLocalMin (Icc_mem_nhds h h')).deriv_eq_zero⟩)

/-! ### Regular energy windows -/

/-- A **regular window** between the energies `E₀` and `E`: the closed energy interval between
them contains no vertex value and no critical value of an edge potential at an interior point.
Every value of `V_e` at an endpoint or at an interior critical point then lies strictly on one side
of the window.  This is the only input of the analytic part of Proposition VIII.7. -/
def BifurcationWindow (E₀ E : ℝ) : Prop :=
  (∀ v : Γ.Vertex, V.vertexValue v ∉ uIcc E₀ E) ∧
    ∀ (e : Γ.Edge) (q : ℝ), q ∈ Ioo 0 (Γ.length e) → deriv (V.extension e) q = 0 →
      V.extension e q ∉ uIcc E₀ E

namespace BifurcationWindow

variable {V} {E₀ E : ℝ}

/-- Regular windows are symmetric. -/
theorem symm (hw : V.BifurcationWindow E₀ E) : V.BifurcationWindow E E₀ :=
  ⟨fun v => by rw [uIcc_comm]; exact hw.1 v,
    fun e q hq hd => by rw [uIcc_comm]; exact hw.2 e q hq hd⟩

/-- The far end of a regular window is not a vertex value. -/
theorem notMem_exceptionalEnergies_right (hw : V.BifurcationWindow E₀ E) :
    E ∉ V.exceptionalEnergies := by
  rw [V.mem_exceptionalEnergies_iff]
  rintro ⟨v, hv⟩
  exact hw.1 v (hv ▸ right_mem_uIcc)

/-- The near end of a regular window is not a vertex value. -/
theorem notMem_exceptionalEnergies_left (hw : V.BifurcationWindow E₀ E) :
    E₀ ∉ V.exceptionalEnergies :=
  hw.symm.notMem_exceptionalEnergies_right

/-- The value of `V_e` at an endpoint or at an interior critical point avoids the window. -/
private theorem extension_notMem {e : Γ.Edge} {m : ℝ} (hw : V.BifurcationWindow E₀ E)
    (hm : m = 0 ∨ m = Γ.length e ∨ (m ∈ Ioo 0 (Γ.length e) ∧ deriv (V.extension e) m = 0)) :
    V.extension e m ∉ uIcc E₀ E := by
  rcases hm with rfl | rfl | ⟨hm, hd⟩
  · rw [extension_zero_eq]; exact hw.1 _
  · rw [extension_length_eq]; exact hw.1 _
  · exact hw.2 e m hm hd

/-- The far end of a regular window is not an interior critical value. -/
theorem noInteriorCriticalValue'_right (hw : V.BifurcationWindow E₀ E) :
    V.NoInteriorCriticalValue E := by
  intro e q hq hqE hd
  exact hw.2 e q hq hd (hqE ▸ right_mem_uIcc)

/-- No vertex value separates the two ends of a regular window. -/
theorem vertexValue_lt_iff (hw : V.BifurcationWindow E₀ E) (v : Γ.Vertex) :
    V.vertexValue v < E ↔ V.vertexValue v < E₀ := by
  rcases notMem_uIcc_iff.1 (hw.1 v) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h1, fun _ => h2⟩
  · exact ⟨fun h => absurd h (not_lt.2 h2.le), fun h => absurd h (not_lt.2 h1.le)⟩

/-- The admissible ends agree at the two ends of a regular window: `G_E = G_{E₀}`. -/
theorem allowedGerms_eq (hw : V.BifurcationWindow E₀ E) :
    V.allowedGerms E = V.allowedGerms E₀ := by
  ext η
  exact hw.vertexValue_lt_iff η.vertex

/-- **The crossing alternative is the same throughout a window.**  On every edge, either `V_e`
stays below both energies on the whole closed edge, or it exceeds both somewhere: the maximum of
`V_e` is attained at an endpoint (a vertex value) or at an interior critical point, so it is not in
the window. -/
theorem edge_dichotomy (hw : V.BifurcationWindow E₀ E) (e : Γ.Edge) :
    (∀ q ∈ Icc 0 (Γ.length e), V.extension e q < E₀ ∧ V.extension e q < E) ∨
      (∃ q ∈ Icc 0 (Γ.length e), E₀ < V.extension e q ∧ E < V.extension e q) := by
  obtain ⟨m, hm, hmax, hcase⟩ :=
    V.exists_isMaxOn_Icc (e := e) (Γ.length_pos e).le le_rfl le_rfl
  have hbad : V.extension e m ∉ uIcc E₀ E := hw.extension_notMem (by
    rcases hcase with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h))
  rcases notMem_uIcc_iff.1 hbad with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl fun q hq => ⟨lt_of_le_of_lt (hmax hq) h1, lt_of_le_of_lt (hmax hq) h2⟩
  · exact Or.inr ⟨m, hm, h1, h2⟩

/-- **Condition (ii) of Lemma VIII.2 propagates through a window.**  If a well of `{V_e ≤ E}`
(a point of it separated from both endpoints) exists at `E`, then its bottom is an interior
critical point with value below the window, and the barriers on both sides contain an endpoint or
an interior critical point with value above the window; so the well exists already at `E₀`. -/
theorem allowedComponentsReachEnds' (hw : V.BifurcationWindow E₀ E)
    (h₀ : V.AllowedComponentsReachEnds E₀) : V.AllowedComponentsReachEnds E := by
  intro e q hq hqE
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hl, hr⟩ := hcon
  push Not at hl hr
  obtain ⟨s₁, hs₁, h₁⟩ := hl
  obtain ⟨s₂, hs₂, h₂⟩ := hr
  have hs₁q : s₁ < q := lt_of_le_of_ne hs₁.2 (by rintro rfl; linarith)
  have hqs₂ : q < s₂ := lt_of_le_of_ne hs₂.1 (by rintro rfl; linarith)
  -- the bottom of the well
  obtain ⟨m, hm, hmin, hcase⟩ :=
    V.exists_isMinOn_Icc (e := e) (hs₁q.trans hqs₂).le hs₁.1 hs₂.2
  have hmq : V.extension e m ≤ V.extension e q := hmin ⟨hs₁q.le, hqs₂.le⟩
  have hm_int : m ∈ Ioo 0 (Γ.length e) ∧ deriv (V.extension e) m = 0 := by
    rcases hcase with rfl | rfl | ⟨hmI, hd⟩
    · linarith
    · linarith
    · exact ⟨⟨lt_of_le_of_lt hs₁.1 hmI.1, lt_of_lt_of_le hmI.2 hs₂.2⟩, hd⟩
  have hmE₀ : V.extension e m < E₀ := by
    rcases notMem_uIcc_iff.1 (hw.2 e m hm_int.1 hm_int.2) with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · linarith
  have hmIcc : m ∈ Icc 0 (Γ.length e) := Ioo_subset_Icc_self hm_int.1
  rcases h₀ e m hmIcc hmE₀.le with hleft | hright
  · -- the left barrier rises above the window
    obtain ⟨M, hM, hmax, hcaseM⟩ := V.exists_isMaxOn_Icc (e := e) hmIcc.1 le_rfl hmIcc.2
    have hs₁m : s₁ ∈ Icc 0 m := ⟨hs₁.1, hm.1⟩
    have hEM : E < V.extension e M := lt_of_lt_of_le h₁ (hmax hs₁m)
    have hbad : V.extension e M ∉ uIcc E₀ E := hw.extension_notMem (by
      rcases hcaseM with h | h | ⟨hMI, hd⟩
      · exact Or.inl h
      · subst h; linarith
      · exact Or.inr (Or.inr ⟨⟨hMI.1, lt_of_lt_of_le hMI.2 hmIcc.2⟩, hd⟩))
    rcases notMem_uIcc_iff.1 hbad with ⟨-, h⟩ | ⟨h, -⟩
    · linarith
    · exact absurd (hleft M hM) (not_le.2 h)
  · -- the right barrier rises above the window
    obtain ⟨M, hM, hmax, hcaseM⟩ :=
      V.exists_isMaxOn_Icc (e := e) hmIcc.2 hmIcc.1 le_rfl
    have hs₂m : s₂ ∈ Icc m (Γ.length e) := ⟨hm.2, hs₂.2⟩
    have hEM : E < V.extension e M := lt_of_lt_of_le h₂ (hmax hs₂m)
    have hbad : V.extension e M ∉ uIcc E₀ E := hw.extension_notMem (by
      rcases hcaseM with h | h | ⟨hMI, hd⟩
      · subst h; linarith
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨⟨lt_of_le_of_lt hmIcc.1 hMI.1, hMI.2⟩, hd⟩))
    rcases notMem_uIcc_iff.1 hbad with ⟨-, h⟩ | ⟨h, -⟩
    · linarith
    · exact absurd (hright M hM) (not_le.2 h)

end BifurcationWindow

/-- **Regular windows exist around every non-bifurcating energy.**  If `E₀` is neither a vertex
value nor a critical value of an edge potential at an interior point, then every energy close to
`E₀` spans a regular window with it.  The values of `V_e` on the compact set of critical points
of the closed edge, together with the vertex values, form a compact set not containing `E₀`. -/
theorem eventually_bifurcationWindow {E₀ : ℝ} (hexc : E₀ ∉ V.exceptionalEnergies)
    (hcrit : V.NoInteriorCriticalValue E₀) : ∀ᶠ E in 𝓝 E₀, V.BifurcationWindow E₀ E := by
  set K : Γ.Edge → Set ℝ := fun e => Icc 0 (Γ.length e) ∩ deriv (V.extension e) ⁻¹' {0} with hK
  have hKc : ∀ e, IsCompact (K e) := fun e =>
    isCompact_Icc.of_isClosed_subset
      ((V.continuousOn_deriv_extension e).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_singleton) inter_subset_left
  set B : Set ℝ := (⋃ e, V.extension e '' K e) ∪ range V.vertexValue with hB
  have hBc : IsClosed B := by
    refine (isCompact_iUnion fun e => (hKc e).image_of_continuousOn
      ((V.extension_continuousOn_closedEdge e).mono inter_subset_left)).isClosed.union ?_
    exact (finite_range V.vertexValue).isClosed
  have hE₀ : E₀ ∉ B := by
    rintro (h | ⟨v, hv⟩)
    · obtain ⟨e, he⟩ := mem_iUnion.1 h
      obtain ⟨q, ⟨hq, hd⟩, hqE⟩ := he
      apply hexc
      rw [V.mem_exceptionalEnergies_iff]
      rcases eq_or_lt_of_le hq.1 with h0 | h0
      · exact ⟨_, by rw [← extension_zero_eq, h0, hqE]⟩
      rcases eq_or_lt_of_le hq.2 with hl | hl
      · exact ⟨_, by rw [← extension_length_eq, ← hl, hqE]⟩
      exact absurd hd (hcrit e q ⟨h0, hl⟩ hqE)
    · exact hexc ((V.mem_exceptionalEnergies_iff).2 ⟨v, hv⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hBc.isOpen_compl E₀ hE₀
  filter_upwards [Metric.ball_mem_nhds E₀ hε] with E hE
  have hsub : uIcc E₀ E ⊆ Bᶜ := fun x hx => hball (by
    rw [Metric.mem_ball, Real.dist_eq] at hE ⊢
    exact lt_of_le_of_lt (abs_sub_left_of_mem_uIcc hx) hE)
  refine ⟨fun v hv => hsub hv (Or.inr ⟨v, rfl⟩), fun e q hq hd hv => hsub hv (Or.inl ?_)⟩
  exact mem_iUnion.2 ⟨e, q, ⟨Ioo_subset_Icc_self hq, hd⟩, rfl⟩

/-! ### The retrace step at a shell-regular energy -/

/-- The departure flight at a shell-regular energy, completed by its landing point: a continuous
curve on `[0, T]` from the departure point of `η` to the landing point, inside the closed edge and
at energy `E`; it lands at an endpoint with incoming momentum. -/
private theorem departureLanding_spec {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    ∃ (T : ℝ) (c : ℝ → ℝ × ℝ), 0 ≤ T ∧ ContinuousOn c (Icc 0 T) ∧
      c 0 = departurePoint η (V.germSpeed η E) ∧
      c T = V.departureLanding η (V.germSpeed η E) ∧
      (∀ t ∈ Icc 0 T, (c t).1 ∈ Icc 0 (Γ.length η.1)) ∧
      (∀ t ∈ Icc 0 T, V.hamiltonian η.1 (c t).1 (c t).2 = E) ∧
      ((V.departureLanding η (V.germSpeed η E)).1 = 0 ∨
        (V.departureLanding η (V.germSpeed η E)).1 = Γ.length η.1) ∧
      ((V.departureLanding η (V.germSpeed η E)).1 = 0 →
        (V.departureLanding η (V.germSpeed η E)).2 < 0) ∧
      ((V.departureLanding η (V.germSpeed η E)).1 = Γ.length η.1 →
        0 < (V.departureLanding η (V.germSpeed η E)).2) := by
  have hr := V.germSpeed_mem_regularSpeeds hE hη
  have hbdd := V.bddAbove_departurePoint_germSpeed hE hη
  set a : V.FlightState := V.ofDeparture η hr.1 hr.2 with ha
  have hbdd' : BddAbove (durationSet V a.edge a.state) := hbdd
  have hland : V.departureLanding η (V.germSpeed η E) = a.segment.maximalEndpoint hbdd' :=
    V.departureLanding_eq_maximalEndpoint hr hbdd'
  have henergy : V.hamiltonian a.edge a.state.1 a.state.2 = E :=
    V.departureEnergy_germSpeed hη
  refine ⟨sSup (durationSet V a.edge a.state), a.segment.maximalCurveClosed hbdd',
    (lt_of_lt_of_le a.segment.duration_pos (le_csSup hbdd' a.segment.mem_durationSet)).le,
    fun t ht => (a.segment.maximalCurveClosed_hasDerivWithinAt_Icc hbdd' ht).continuousWithinAt,
    a.segment.maximalCurveClosed_initial hbdd',
    by rw [hland]; exact a.segment.maximalCurveClosed_eq_endpoint hbdd',
    fun t ht => a.segment.maximalCurveClosed_physical hbdd' ht,
    fun t ht => (a.segment.maximalCurveClosed_hamiltonian_eq_initial hbdd' ht).trans henergy,
    ?_, ?_, ?_⟩
  · rw [hland]; exact a.segment.maximalEndpoint_coordinate_eq_zero_or_length hbdd'
  · rw [hland]; exact a.segment.maximalEndpoint_left_momentum_neg hbdd' a.regular
  · rw [hland]; exact a.segment.maximalEndpoint_right_momentum_pos hbdd' a.regular

/-- **A flight below the potential crosses its edge.**  At a shell-regular energy `E`, if
`V_e < E` on the whole closed edge then the momentum never vanishes along the flight, so its sign
is that of the departure, and the flight lands at the opposite end of the edge. -/
theorem retraceStep_fst_of_forall_lt {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E)
    (hlt : ∀ q ∈ Icc 0 (Γ.length η.1), V.extension η.1 q < E) :
    (V.retraceStep η (V.germSpeed η E)).1 = (η.1, !η.2) := by
  obtain ⟨T, c, hT, hc, h0, hTland, hphys, hen, hend, hleft, hright⟩ :=
    V.departureLanding_spec hE hη
  have hne : ∀ t ∈ Icc 0 T, (c t).2 ≠ 0 := by
    intro t ht hp
    have h1 := hen t ht
    have h2 := hlt _ (hphys t ht)
    rw [hamiltonian, hp] at h1
    linarith
  have hcont : ContinuousOn (fun t => (c t).2) (Icc 0 T) := continuous_snd.comp_continuousOn hc
  have hspeed : 0 < V.germSpeed η E := V.germSpeed_pos_iff.2 hη
  have hTmem : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  rw [retraceStep_fst, edgeCovector_germ]
  rcases η with ⟨e, b⟩
  cases b
  · have hp0 : 0 < (fun t => (c t).2) 0 := by
      simp only [h0, departurePoint, FiniteMetricGraph.edgeEnd_sign_false]
      linarith
    have hpT := positive_on_Icc_of_continuousOn_ne_zero hcont hne hp0 T hTmem
    simp only [hTland] at hpT
    rcases hend with h | h
    · exact absurd (hleft h) (not_lt.2 hpT.le)
    · simp [h]
  · have hp0 : (fun t => (c t).2) 0 < 0 := by
      simp only [h0, departurePoint, FiniteMetricGraph.edgeEnd_sign_true]
      linarith
    have hpT := negative_on_Icc_of_continuousOn_ne_zero hcont hne hp0 T hTmem
    simp only [hTland] at hpT
    rcases hend with h | h
    · have hne' : (0 : ℝ) ≠ Γ.length e := (Γ.length_pos e).ne
      simp [h, hne']
    · exact absurd (hright h) (not_lt.2 hpT.le)

/-- **A flight below a barrier returns to its own end.**  At a shell-regular energy `E`, if
`V_e > E` somewhere on the closed edge then the flight cannot reach the opposite end: by the
intermediate value theorem it would pass the barrier, where its kinetic energy would be negative. -/
theorem retraceStep_fst_of_exists_gt {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E)
    (hgt : ∃ q ∈ Icc 0 (Γ.length η.1), E < V.extension η.1 q) :
    (V.retraceStep η (V.germSpeed η E)).1 = η := by
  obtain ⟨T, c, hT, hc, h0, hTland, hphys, hen, hend, -, -⟩ := V.departureLanding_spec hE hη
  obtain ⟨q₀, hq₀, hq₀E⟩ := hgt
  have hnever : ∀ t ∈ Icc 0 T, (c t).1 ≠ q₀ := by
    intro t ht hq
    have h1 := hen t ht
    rw [hamiltonian, hq] at h1
    nlinarith [sq_nonneg (c t).2]
  have hcont : ContinuousOn (fun t => (c t).1) (Icc 0 T) := continuous_fst.comp_continuousOn hc
  rw [retraceStep_fst, edgeCovector_germ]
  rcases η with ⟨e, b⟩
  cases b
  · have hq0 : (c 0).1 = 0 := by simp [h0, departurePoint]
    rcases hend with h | h
    · have hne' : (0 : ℝ) ≠ Γ.length e := (Γ.length_pos e).ne
      simp [h, hne']
    · exfalso
      have hqT : (c T).1 = Γ.length e := by rw [hTland]; exact h
      obtain ⟨t, ht, htq⟩ := intermediate_value_Icc hT hcont
        (show q₀ ∈ Icc ((c 0).1) ((c T).1) by rw [hq0, hqT]; exact hq₀)
      exact hnever t ht htq
  · have hq0 : (c 0).1 = Γ.length e := by simp [h0, departurePoint]
    rcases hend with h | h
    · exfalso
      have hqT : (c T).1 = 0 := by rw [hTland]; exact h
      obtain ⟨t, ht, htq⟩ := intermediate_value_Icc' hT hcont
        (show q₀ ∈ Icc ((c T).1) ((c 0).1) by rw [hq0, hqT]; exact hq₀)
      exact hnever t ht htq
    · simp [h]

/-- **The retrace step is constant across a regular window** (`κ_E = κ_{E₀}` in the paper).
Both energies fall into the same case of the crossing alternative (`edge_dichotomy`). -/
theorem retraceStep_fst_eq_of_bifurcationWindow {E₀ E : ℝ} (hw : V.BifurcationWindow E₀ E)
    (hE₀ : V.ShellRegular E₀) (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E₀) :
    (V.retraceStep η (V.germSpeed η E)).1 = (V.retraceStep η (V.germSpeed η E₀)).1 := by
  have hηE : η ∈ V.allowedGerms E := by rw [hw.allowedGerms_eq]; exact hη
  rcases hw.edge_dichotomy η.1 with hlt | ⟨q, hq, h₀, h⟩
  · rw [V.retraceStep_fst_of_forall_lt hE hηE (fun q hq => (hlt q hq).2),
      V.retraceStep_fst_of_forall_lt hE₀ hη (fun q hq => (hlt q hq).1)]
  · rw [V.retraceStep_fst_of_exists_gt hE hηE ⟨q, hq, h⟩,
      V.retraceStep_fst_of_exists_gt hE₀ hη ⟨q, hq, h₀⟩]

/-- The retrace step lands at an allowed germ. -/
theorem retraceStep_fst_mem_allowedGerms {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    (V.retraceStep η (V.germSpeed η E)).1 ∈ V.allowedGerms E := by
  have hr := V.germSpeed_mem_regularSpeeds hE hη
  have hbdd := V.bddAbove_departurePoint_germSpeed hE hη
  have h2 := V.departureEnergy_retraceStep hr hbdd
  rw [V.departureEnergy_germSpeed hη] at h2
  have h3 := V.germSpeed_departureEnergy (V.retraceStep η (V.germSpeed η E)).1
    (V.retraceStep_pos η (V.germSpeed η E)).le
  rw [h2] at h3
  rw [← V.germSpeed_pos_iff, h3]
  exact V.retraceStep_pos η _

section Step

variable (S : BorelEnergyPreservingScattering V)

/-- **The end step factors as `Π_E = F_E ∘ κ_E`** (Definition VIII.4).  At a shell-regular energy
the germ step of `η` is the image of the retrace germ `ζ = κ_E(η)` under the fixed-speed vertex
permutation `F_v(·, r)` of Proposition III.2 at the vertex of `ζ`, evaluated at the speed
`r = r_ζ(E)` with which `ζ` is left at energy `E`. -/
theorem germStep_eq_speedPermutation {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {ζ : Γ.EdgeEnd}
    (hζ : (V.retraceStep η (V.germSpeed η E)).1 = ζ) (r : FiniteMetricGraph.PositiveSpeed)
    (hr : r.1 = V.germSpeed ζ E) :
    V.germStep S E η =
      (EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering
        ζ.vertex r ⟨ζ, rfl⟩).1 := by
  subst hζ
  have hrs := V.germSpeed_mem_regularSpeeds hE hη
  have hbdd := V.bddAbove_departurePoint_germSpeed hE hη
  set α := edgeCovector (Γ := Γ) η.1 (V.departureLanding η (V.germSpeed η E)) with hα
  have hin : FiniteMetricGraph.EdgeEnd.sign Γ α.germ * α.momentum > 0 :=
    V.edgeCovector_departureLanding_incoming hrs hbdd
  have hspeed : |α.momentum| = r.1 := by
    rw [hr]
    have h2 := V.departureEnergy_retraceStep hrs hbdd
    rw [V.departureEnergy_germSpeed hη] at h2
    have h3 := V.germSpeed_departureEnergy (V.retraceStep η (V.germSpeed η E)).1
      (V.retraceStep_pos η (V.germSpeed η E)).le
    rw [h2] at h3
    rw [h3]
    rfl
  have hinc : (⟨α, rfl, hin⟩ : Γ.IncomingBoundary α.germ.vertex) =
      Γ.incomingAtSpeed ⟨α.germ, rfl⟩ r := by
    rw [Γ.incoming_eq_incomingAtSpeed ⟨α, rfl, hin⟩]
    congr 1
    exact Subtype.ext hspeed
  show (scatterCovector (V := V) S α).germ = _
  rw [scatterCovector_incoming (V := V) S hin, hinc, S.scattered_incomingAtSpeed]
  rfl

end Step

/-! ### Proposition VIII.7 -/

section Bifurcation

variable (S : BorelEnergyPreservingScattering V)

/-- **Shell-regularity is open.**  By the characterization of Lemma VIII.2 (`shellRegular_iff`), every
energy close to a shell-regular `E₀` is shell-regular and spans a regular window with `E₀`. -/
theorem eventually_shellRegular_bifurcationWindow
    {E₀ : ℝ} (hE₀ : V.ShellRegular E₀) :
    ∀ᶠ E in 𝓝 E₀, V.BifurcationWindow E₀ E ∧ V.ShellRegular E := by
  obtain ⟨hcrit, hacre⟩ := (V.shellRegular_iff hE₀.not_exceptional).1 hE₀
  filter_upwards [V.eventually_bifurcationWindow hE₀.not_exceptional hcrit] with E hw
  exact ⟨hw, (V.shellRegular_iff hw.notMem_exceptionalEnergies_right).2
    ⟨hw.noInteriorCriticalValue'_right, hw.allowedComponentsReachEnds' hacre⟩⟩

/-- If the vertex permutation at `v` is locally constant at the speed `r_v(E₀)`, then it takes the
same value at the speeds `r_v(E)` for all energies `E` close to `E₀`. -/
private theorem eventually_speedPermutation_eq {E₀ : ℝ} (v : Γ.Vertex)
    (hF : ∀ r₀ : FiniteMetricGraph.PositiveSpeed,
      r₀.1 = Real.sqrt (2 * (E₀ - V.vertexValue v)) →
      ∀ᶠ r in 𝓝 r₀,
        EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r =
          EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r₀) :
    ∀ᶠ E in 𝓝 E₀, ∀ r r₀ : FiniteMetricGraph.PositiveSpeed,
      r.1 = Real.sqrt (2 * (E - V.vertexValue v)) →
      r₀.1 = Real.sqrt (2 * (E₀ - V.vertexValue v)) →
      EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r =
        EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r₀ := by
  by_cases hv : V.vertexValue v < E₀
  · set r₀ : FiniteMetricGraph.PositiveSpeed :=
      ⟨Real.sqrt (2 * (E₀ - V.vertexValue v)), Real.sqrt_pos.2 (by linarith)⟩ with hr₀
    have h := hF r₀ rfl
    rw [nhds_subtype_eq_comap, Filter.eventually_comap] at h
    have hcont : Tendsto (fun E => Real.sqrt (2 * (E - V.vertexValue v))) (𝓝 E₀)
        (𝓝 (r₀ : ℝ)) :=
      ((continuous_const.mul (continuous_id.sub continuous_const)).sqrt).tendsto E₀
    filter_upwards [hcont.eventually h] with E hE r r₀' hr hr₀'
    have hr₀eq : r₀' = r₀ := Subtype.ext hr₀'
    rw [hr₀eq]
    exact hE r hr
  · refine Eventually.of_forall fun E r r₀ _ hr₀ => absurd hr₀ ?_
    have hpos : (0 : ℝ) < r₀.1 := r₀.2
    rw [Real.sqrt_eq_zero'.2 (by linarith)]
    exact hpos.ne'

/-- **Proposition VIII.7 (bifurcation set): the end step is locally constant.**

Let `E₀` be shell-regular, and assume that for every vertex `v` with `V(v) < E₀` the fixed-speed
vertex permutation `F_v(·, r)` (`speedPermutation`, Proposition III.2) is constant for `r` near
`r_v(E₀) = √(2(E₀ - V(v)))`.  Then for every `E` in a neighbourhood of `E₀`:
`E` is shell-regular, `G_E = G_{E₀}` (`allowedGerms`), and `Π_E = Π_{E₀}` (`germStep` on the
allowed germs).

The speed hypothesis is stated for every `r₀ : PositiveSpeed` with `r₀ = √(2(E₀ - V(v)))`; for a
vertex with `V(v) ≥ E₀` no such positive `r₀` exists, so the hypothesis only concerns the vertices
with `V(v) < E₀`, as in the paper. -/
theorem bifurcation_locallyConstant
    {E₀ : ℝ} (hE₀ : V.ShellRegular E₀)
    (hF : ∀ (v : Γ.Vertex) (r₀ : FiniteMetricGraph.PositiveSpeed),
      r₀.1 = Real.sqrt (2 * (E₀ - V.vertexValue v)) →
      ∀ᶠ r in 𝓝 r₀,
        EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r =
          EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r₀) :
    ∀ᶠ E in 𝓝 E₀, V.ShellRegular E ∧ V.allowedGerms E = V.allowedGerms E₀ ∧
      ∀ η ∈ V.allowedGerms E₀, V.germStep S E η = V.germStep S E₀ η := by
  have hspeed := eventually_all.2 fun v => V.eventually_speedPermutation_eq S v (hF v)
  filter_upwards [V.eventually_shellRegular_bifurcationWindow hE₀, hspeed] with
    E ⟨hw, hE⟩ hsp
  refine ⟨hE, hw.allowedGerms_eq, fun η hη => ?_⟩
  have hηE : η ∈ V.allowedGerms E := by rw [hw.allowedGerms_eq]; exact hη
  set ζ := (V.retraceStep η (V.germSpeed η E₀)).1 with hζ
  have hζmem : ζ ∈ V.allowedGerms E₀ := V.retraceStep_fst_mem_allowedGerms hE₀ hη
  have hζmemE : ζ ∈ V.allowedGerms E := by rw [hw.allowedGerms_eq]; exact hζmem
  let r : FiniteMetricGraph.PositiveSpeed := ⟨V.germSpeed ζ E, V.germSpeed_pos_iff.2 hζmemE⟩
  let r₀ : FiniteMetricGraph.PositiveSpeed := ⟨V.germSpeed ζ E₀, V.germSpeed_pos_iff.2 hζmem⟩
  rw [V.germStep_eq_speedPermutation S hE hηE
      (V.retraceStep_fst_eq_of_bifurcationWindow hw hE₀ hE hη) r rfl,
    V.germStep_eq_speedPermutation S hE₀ hη rfl r₀ rfl, hsp ζ.vertex r r₀ rfl rfl]

/-- The retrace step `κ_E` is locally constant around a shell-regular energy (no hypothesis on
the vertex law is needed). -/
theorem retraceStep_locallyConstant
    {E₀ : ℝ} (hE₀ : V.ShellRegular E₀) :
    ∀ᶠ E in 𝓝 E₀, ∀ η ∈ V.allowedGerms E₀,
      (V.retraceStep η (V.germSpeed η E)).1 = (V.retraceStep η (V.germSpeed η E₀)).1 := by
  filter_upwards [V.eventually_shellRegular_bifurcationWindow hE₀] with E ⟨hw, hE⟩
  exact fun η hη => V.retraceStep_fst_eq_of_bifurcationWindow hw hE₀ hE hη

open Classical in
/-- Two permutations of equal subsets which agree pointwise have the same cycle type. -/
private theorem cycleType_eq_of_set_eq {α : Type*} [Fintype α] [DecidableEq α] {s t : Set α}
    (h : s = t) (σ : Equiv.Perm s) (τ : Equiv.Perm t) (hστ : ∀ x : s, (σ x : α) = τ ⟨x, h ▸ x.2⟩) :
    σ.cycleType = τ.cycleType := by
  subst h
  have : σ = τ := Equiv.ext fun x => Subtype.ext (hστ x)
  rw [this]

open Classical in
/-- **Proposition VIII.7, "in particular": the cycle structure is locally constant.**  Under the
hypotheses of `bifurcation_locallyConstant`, every energy near `E₀` is shell-regular and its end
permutation `shellGermPerm` has the cycle type of the end permutation at `E₀`. -/
theorem bifurcation_cycleType_locallyConstant
    {E₀ : ℝ} (hE₀ : V.ShellRegular E₀)
    (hF : ∀ (v : Γ.Vertex) (r₀ : FiniteMetricGraph.PositiveSpeed),
      r₀.1 = Real.sqrt (2 * (E₀ - V.vertexValue v)) →
      ∀ᶠ r in 𝓝 r₀,
        EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r =
          EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r₀) :
    ∀ᶠ E in 𝓝 E₀, ∃ hE : V.ShellRegular E,
      (V.shellGermPerm S hE).cycleType = (V.shellGermPerm S hE₀).cycleType := by
  filter_upwards [V.bifurcation_locallyConstant S hE₀ hF] with E ⟨hE, hG, hstep⟩
  exact ⟨hE, cycleType_eq_of_set_eq hG _ _ fun x => by
    rw [shellGermPerm_apply, shellGermPerm_apply]
    exact hstep x (hG ▸ x.2)⟩

/-! ### The bifurcation set -/

/-- The **bifurcation set** of Proposition VIII.7: the vertex values, the critical values of the
edge potentials at interior points, and the energies `E = V(v) + r²/2` at which the vertex
permutation `r ↦ F_v(·, r)` is not locally constant.  Since `F_v(·, r)` ranges over the finite set
of permutations of the ends at `v`, "not locally constant at `r`" is exactly "discontinuous at
`r`" for the discrete topology on permutations
(`speedPermutation_eventually_eq_iff_continuousAt`). -/
def bifurcationEnergies : Set ℝ :=
  (V.exceptionalEnergies : Set ℝ) ∪
    {E | ∃ (e : Γ.Edge) (q : ℝ), q ∈ Ioo 0 (Γ.length e) ∧ V.extension e q = E ∧
      deriv (V.extension e) q = 0} ∪
    {E | ∃ (v : Γ.Vertex) (r : FiniteMetricGraph.PositiveSpeed),
      E = V.vertexValue v + r.1 ^ 2 / 2 ∧
      ¬ ∀ᶠ r' in 𝓝 r,
        EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r' =
          EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r}

/-- Local constancy of `r ↦ F_v(·, r)` is continuity for the discrete topology on the finite set
of permutations of the ends at `v`. -/
theorem speedPermutation_eventually_eq_iff_continuousAt (v : Γ.Vertex)
    [TopologicalSpace (Equiv.Perm (Γ.IncidentEnds v))]
    [DiscreteTopology (Equiv.Perm (Γ.IncidentEnds v))] (r : FiniteMetricGraph.PositiveSpeed) :
    (∀ᶠ r' in 𝓝 r,
        EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r' =
          EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r) ↔
      ContinuousAt (EnergyPreservingScattering.speedPermutation V
        S.toEnergyPreservingScattering v) r := by
  rw [ContinuousAt, nhds_discrete (Equiv.Perm (Γ.IncidentEnds v)), tendsto_pure]

/-- **Proposition VIII.7, "consequently", in direct form.**  Away from the bifurcation set,
shell-regularity is locally constant, and at a shell-regular energy so are the admissible ends and
the end step. -/
theorem locallyConstant_of_notMem_bifurcationEnergies
    {E₀ : ℝ} (h : E₀ ∉ V.bifurcationEnergies S) :
    ∀ᶠ E in 𝓝 E₀, (V.ShellRegular E ↔ V.ShellRegular E₀) ∧
      (V.ShellRegular E₀ → V.allowedGerms E = V.allowedGerms E₀ ∧
        ∀ η ∈ V.allowedGerms E₀, V.germStep S E η = V.germStep S E₀ η) := by
  simp only [bifurcationEnergies, mem_union, mem_setOf_eq, not_or] at h
  obtain ⟨⟨hexc, hcrit⟩, hspeed⟩ := h
  have hcrit' : V.NoInteriorCriticalValue E₀ := fun e q hq hqE hd => hcrit ⟨e, q, hq, hqE, hd⟩
  have hF : ∀ (v : Γ.Vertex) (r₀ : FiniteMetricGraph.PositiveSpeed),
      r₀.1 = Real.sqrt (2 * (E₀ - V.vertexValue v)) →
      ∀ᶠ r in 𝓝 r₀,
        EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r =
          EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r₀ := by
    intro v r₀ hr₀
    by_contra hne
    refine hspeed ⟨v, r₀, ?_, hne⟩
    have hpos : (0 : ℝ) < r₀.1 := r₀.2
    have harg : 0 ≤ 2 * (E₀ - V.vertexValue v) := by
      by_contra h'
      rw [Real.sqrt_eq_zero'.2 (by linarith)] at hr₀
      linarith
    have hsq : r₀.1 ^ 2 = 2 * (E₀ - V.vertexValue v) := by rw [hr₀, Real.sq_sqrt harg]
    linarith
  by_cases hE₀ : V.ShellRegular E₀
  · filter_upwards [V.bifurcation_locallyConstant S hE₀ hF] with E hE
    exact ⟨⟨fun _ => hE₀, fun _ => hE.1⟩, fun _ => hE.2⟩
  · filter_upwards [V.eventually_bifurcationWindow hexc hcrit'] with E hw
    refine ⟨⟨fun hE => ?_, fun h => absurd h hE₀⟩, fun h => absurd h hE₀⟩
    obtain ⟨-, haE⟩ := (V.shellRegular_iff hw.notMem_exceptionalEnergies_right).1 hE
    exact absurd ((V.shellRegular_iff hexc).2 ⟨hcrit', hw.symm.allowedComponentsReachEnds' haE⟩) hE₀

open Classical in
/-- **Proposition VIII.7, "consequently": where the cycle structure can change.**  If, arbitrarily
close to `E₀`, the cycle structure differs from that at `E₀` — either shell-regularity itself
differs (so that the cycle structure is defined on one side only), or both energies are
shell-regular and the end permutations have different cycle types — then `E₀` is a vertex value,
a critical value of an edge potential at an interior point, or an energy `V(v) + r²/2` at which
`r ↦ F_v(·, r)` is discontinuous. -/
theorem mem_bifurcationEnergies_of_frequently_cycleType_ne
    {E₀ : ℝ}
    (hchange : ∃ᶠ E in 𝓝 E₀, ¬ (V.ShellRegular E ↔ V.ShellRegular E₀) ∨
      ∃ (hE : V.ShellRegular E) (hE₀ : V.ShellRegular E₀),
        (V.shellGermPerm S hE).cycleType ≠ (V.shellGermPerm S hE₀).cycleType) :
    E₀ ∈ V.bifurcationEnergies S := by
  by_contra h
  obtain ⟨E, hch, ⟨hiff, hE₀⟩⟩ :=
    (hchange.and_eventually (V.locallyConstant_of_notMem_bifurcationEnergies S h)).exists
  rcases hch with hne | ⟨hE, hE₀', hne⟩
  · exact hne hiff
  · obtain ⟨hG, hstep⟩ := hE₀ hE₀'
    exact hne (cycleType_eq_of_set_eq hG _ _ fun x => by
      rw [shellGermPerm_apply, shellGermPerm_apply]
      exact hstep x (hG ▸ x.2))

end Bifurcation

end MechanicalPotential

end HamiltonianMetricGraphs
