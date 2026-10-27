/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Structure

/-!
# A criterion for shell-regular energies

This file proves Lemma VIII.2 of the paper (`lem:shell-regular`).  An energy `E` which is not a
vertex value is *shell-regular* (Definition VIII.1, `MechanicalPotential.ShellRegular`) — every
flight at energy `E` reaches an endpoint of its edge in finite time — if and only if, on every
edge `e`,

1. `E` is not a critical value of `V_e` on the open edge `(0, ℓ_e)`
   (`NoInteriorCriticalValue`), and
2. every nonempty connected component of the allowed region `{V_e ≤ E} ⊆ [0, ℓ_e]` meets an
   endpoint of the edge (`AllowedComponentsReachEnds`).

In particular every energy above the maximum of the potential is shell-regular
(`shellRegular_of_forall_lt`).

## Encoding of the second condition

A connected subset of an interval is an interval, so the component of the allowed region through
an allowed point `q` contains `0` exactly when `V_e ≤ E` on `[0, q]`, and contains `ℓ_e` exactly
when `V_e ≤ E` on `[q, ℓ_e]`.  `AllowedComponentsReachEnds` is stated in this elementary form;
`allowedComponentsReachEnds_iff_connectedComponentIn` proves that it is literally the statement
about connected components (`connectedComponentIn`) of the allowed region.

## Proof

*Necessity.*  At an interior critical point `q₀` with `V_e(q₀) = E` the constant curve `(q₀, 0)`
is a physical segment of every duration, so its duration set is unbounded
(`ShellRegular.noInteriorCriticalValue`; this half needs no hypothesis on `E`).  If the component
through an allowed interior point `q` avoids both endpoints, there are points `s₁ < q < s₂` with
`V_e(s₁), V_e(s₂) > E`.  A flight from `q` would, by shell-regularity, end at an endpoint of the
edge; by the intermediate value theorem it would pass through `s₁` or `s₂`, which energy
conservation forbids (`ShellRegular.allowedComponentsReachEnds`).

*Sufficiency, without integrals.*  Fix a state `x` of energy `E`.  Every flight from `x` stays in
the connected component `[α, β]` of the allowed region through its initial position
(`exists_confining_interval`).  On `[α, β]` the only points with `V_e = E` are endpoints `α`, `β`
lying inside the open edge (because `E` is not a vertex value), and by the two conditions they
are *simple turning points of one common orientation*: there is a sign `σ = ±1` with
`σ · F(q) > 0` at every such point, where `F = -V_e'` is the force (`exists_turning_sign`).  By
compactness there are `κ ≥ 0` and `c > 0` with

`κ · 2 (E - V_e(q)) + σ · F(q) ≥ c` on `[α, β]` (`exists_uniform_drift`).

Along a flight `(q(t), p(t))` of energy `E`, the drift function `Φ = σ · exp(σ κ q) · p` then has

`Φ' = exp(σ κ q) · (κ p² + σ F(q)) ≥ exp(-κ ℓ_e) · c`,

while `|Φ| ≤ exp(κ ℓ_e) · sqrt(2 (E - min V_e))`.  The mean value theorem bounds the duration of
every flight from `x` by a constant depending only on `x`, so the duration set is bounded above.
This replaces the travel-time integral `∫ dq / sqrt(2 (E - V_e(q)))` of the paper's proof by a
single derivative estimate.

## Main results

* `NoInteriorCriticalValue`, `AllowedComponentsReachEnds`: conditions (i) and (ii).
* `ShellRegular.noInteriorCriticalValue`, `ShellRegular.allowedComponentsReachEnds`: necessity.
* `shellRegular_iff`: Lemma VIII.2.
* `shellRegular_of_forall_lt`: the final sentence of Lemma VIII.2.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter PhysicalEdgeSegment
open scoped Topology

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The two conditions of Lemma VIII.2 -/

/-- Condition (i) of Lemma VIII.2: on no edge is `E` a critical value of the potential on the
open edge `(0, ℓ_e)`. -/
def NoInteriorCriticalValue (E : ℝ) : Prop :=
  ∀ (e : Γ.Edge) (q : ℝ), q ∈ Set.Ioo 0 (Γ.length e) → V.extension e q = E →
    deriv (V.extension e) q ≠ 0

/-- Condition (ii) of Lemma VIII.2: every nonempty connected component of the allowed region
`{V_e ≤ E} ⊆ [0, ℓ_e]` meets an endpoint of the edge.  The component through an allowed point `q`
is an interval, so it meets `0` iff `V_e ≤ E` on `[0, q]` and meets `ℓ_e` iff `V_e ≤ E` on
`[q, ℓ_e]`; see `allowedComponentsReachEnds_iff_connectedComponentIn`. -/
def AllowedComponentsReachEnds (E : ℝ) : Prop :=
  ∀ (e : Γ.Edge) (q : ℝ), q ∈ Set.Icc 0 (Γ.length e) → V.extension e q ≤ E →
    (∀ s ∈ Set.Icc 0 q, V.extension e s ≤ E) ∨
      (∀ s ∈ Set.Icc q (Γ.length e), V.extension e s ≤ E)

/-- The allowed region `{V_e ≤ E}` of the closed edge `e` at energy `E`. -/
def allowedRegion (E : ℝ) (e : Γ.Edge) : Set ℝ :=
  {q | q ∈ Icc (0 : ℝ) (Γ.length e) ∧ V.extension e q ≤ E}

/-- `AllowedComponentsReachEnds` is literally the statement of condition (ii): the connected
component of the allowed region through each of its points contains an endpoint of the edge. -/
theorem allowedComponentsReachEnds_iff_connectedComponentIn {E : ℝ} :
    V.AllowedComponentsReachEnds E ↔
      ∀ (e : Γ.Edge), ∀ q ∈ V.allowedRegion E e,
        (0 : ℝ) ∈ connectedComponentIn (V.allowedRegion E e) q ∨
          Γ.length e ∈ connectedComponentIn (V.allowedRegion E e) q := by
  have hleft : ∀ (e : Γ.Edge), ∀ q ∈ V.allowedRegion E e,
      ((∀ s ∈ Icc 0 q, V.extension e s ≤ E) ↔
        (0 : ℝ) ∈ connectedComponentIn (V.allowedRegion E e) q) := by
    intro e q hq
    constructor
    · intro h
      have hsub : Icc 0 q ⊆ V.allowedRegion E e :=
        fun s hs => ⟨⟨hs.1, hs.2.trans hq.1.2⟩, h s hs⟩
      exact isPreconnected_Icc.subset_connectedComponentIn
        (right_mem_Icc.mpr hq.1.1) hsub (left_mem_Icc.mpr hq.1.1)
    · intro h s hs
      have hIcc := isPreconnected_connectedComponentIn.Icc_subset h
        (mem_connectedComponentIn hq)
      exact (connectedComponentIn_subset _ _ (hIcc hs)).2
  have hright : ∀ (e : Γ.Edge), ∀ q ∈ V.allowedRegion E e,
      ((∀ s ∈ Icc q (Γ.length e), V.extension e s ≤ E) ↔
        Γ.length e ∈ connectedComponentIn (V.allowedRegion E e) q) := by
    intro e q hq
    constructor
    · intro h
      have hsub : Icc q (Γ.length e) ⊆ V.allowedRegion E e :=
        fun s hs => ⟨⟨hq.1.1.trans hs.1, hs.2⟩, h s hs⟩
      exact isPreconnected_Icc.subset_connectedComponentIn
        (left_mem_Icc.mpr hq.1.2) hsub (right_mem_Icc.mpr hq.1.2)
    · intro h s hs
      have hIcc := isPreconnected_connectedComponentIn.Icc_subset
        (mem_connectedComponentIn hq) h
      exact (connectedComponentIn_subset _ _ (hIcc hs)).2
  constructor
  · intro h e q hq
    rcases h e q hq.1 hq.2 with h' | h'
    · exact Or.inl ((hleft e q hq).mp h')
    · exact Or.inr ((hright e q hq).mp h')
  · intro h e q hq hqE
    rcases h e q ⟨hq, hqE⟩ with h' | h'
    · exact Or.inl ((hleft e q ⟨hq, hqE⟩).mpr h')
    · exact Or.inr ((hright e q ⟨hq, hqE⟩).mpr h')

/-! ### Elementary one-variable facts -/

/-- A positive derivative at `a` produces, in every interval `(a, b]`, a point with a strictly
larger value. -/
private theorem exists_Ioc_gt_of_hasDerivAt_pos {f : ℝ → ℝ} {d a b : ℝ} (hf : HasDerivAt f d a)
    (hd : 0 < d) (hab : a < b) : ∃ x ∈ Ioc a b, f a < f x := by
  have hslope : ∀ᶠ x in 𝓝[≠] a, 0 < slope f a x :=
    (hasDerivAt_iff_tendsto_slope.mp hf).eventually (lt_mem_nhds hd)
  have hright : ∀ᶠ x in 𝓝[>] a, 0 < slope f a x :=
    nhdsWithin_mono a (fun x hx => (show a < x from hx).ne') hslope
  obtain ⟨x, hx, hxI⟩ := (hright.and (Ioc_mem_nhdsGT hab)).exists
  refine ⟨x, hxI, ?_⟩
  have hxa : 0 < x - a := sub_pos.mpr hxI.1
  have h := sub_smul_slope f a x
  simp only [smul_eq_mul, vsub_eq_sub] at h
  nlinarith [mul_pos hxa hx]

/-- A negative derivative at `a` produces, in every interval `[b, a)`, a point with a strictly
larger value. -/
private theorem exists_Ico_gt_of_hasDerivAt_neg {f : ℝ → ℝ} {d a b : ℝ} (hf : HasDerivAt f d a)
    (hd : d < 0) (hba : b < a) : ∃ x ∈ Ico b a, f a < f x := by
  have hslope : ∀ᶠ x in 𝓝[≠] a, slope f a x < 0 :=
    (hasDerivAt_iff_tendsto_slope.mp hf).eventually (gt_mem_nhds hd)
  have hleft : ∀ᶠ x in 𝓝[<] a, slope f a x < 0 :=
    nhdsWithin_mono a (fun x hx => (show x < a from hx).ne) hslope
  obtain ⟨x, hx, hxI⟩ := (hleft.and (Ico_mem_nhdsLT hba)).exists
  refine ⟨x, hxI, ?_⟩
  have hxa : x - a < 0 := sub_neg.mpr hxI.2
  have h := sub_smul_slope f a x
  simp only [smul_eq_mul, vsub_eq_sub] at h
  nlinarith [mul_pos_of_neg_of_neg hxa hx]

/-- The compactness step of the sufficiency proof.  If `w ≥ 0` and `g > 0` wherever `w`
vanishes on a nonempty compact set, then a single multiple `κ w + g` is bounded below by a
positive constant there. -/
private theorem exists_uniform_drift {K : Set ℝ} (hK : IsCompact K) (hKne : K.Nonempty)
    {w g : ℝ → ℝ} (hw : ContinuousOn w K) (hg : ContinuousOn g K)
    (hw0 : ∀ q ∈ K, 0 ≤ w q) (hpos : ∀ q ∈ K, w q = 0 → 0 < g q) :
    ∃ κ c : ℝ, 0 ≤ κ ∧ 0 < c ∧ ∀ q ∈ K, c ≤ κ * w q + g q := by
  obtain ⟨q₀, hq₀, hmin⟩ := hK.exists_isMinOn hKne (hg.sup hw)
  set c : ℝ := max (g q₀) (w q₀) with hc_def
  have hc : 0 < c := by
    rcases eq_or_lt_of_le (hw0 q₀ hq₀) with h | h
    · exact lt_max_of_lt_left (hpos q₀ hq₀ h.symm)
    · exact lt_max_of_lt_right h
  obtain ⟨G, hG⟩ := hK.bddBelow_image hg
  set G' : ℝ := min G 0 with hG'_def
  have hG'0 : G' ≤ 0 := min_le_right _ _
  refine ⟨(c - G') / c, c, div_nonneg (by linarith) hc.le, hc, ?_⟩
  intro q hq
  have hgq : G' ≤ g q := (min_le_left _ _).trans (hG ⟨q, hq, rfl⟩)
  have hκ : 0 ≤ (c - G') / c := div_nonneg (by linarith) hc.le
  have hmax : c ≤ max (g q) (w q) := isMinOn_iff.mp hmin q hq
  by_cases hgc : c ≤ g q
  · nlinarith [mul_nonneg hκ (hw0 q hq)]
  · have hwc : c ≤ w q := by
      rcases le_max_iff.mp hmax with h | h
      · exact absurd h hgc
      · exact h
    have hmul : (c - G') / c * c ≤ (c - G') / c * w q := mul_le_mul_of_nonneg_left hwc hκ
    rw [div_mul_cancel₀ _ hc.ne'] at hmul
    linarith

/-! ### Necessity -/

variable {V}

/-- **Necessity of condition (i).**  An interior critical point at energy `E` is an equilibrium
whose flight never lands, so a shell-regular energy is not an interior critical value.  This half
does not use that `E` avoids the vertex values. -/
theorem ShellRegular.noInteriorCriticalValue {E : ℝ} (hS : V.ShellRegular E) :
    V.NoInteriorCriticalValue E := by
  intro e q hq hqE hd
  have hx : V.hamiltonian e (q, (0 : ℝ)).1 (q, (0 : ℝ)).2 = E := by
    simp [hamiltonian, hqE]
  obtain ⟨B, hB⟩ := hS.lands e (q, 0) hx
  have hfield : V.edgeVectorField e (q, 0) = 0 := by
    simp [edgeVectorField, force, hd]
  let k : V.PhysicalEdgeSegment e (q, 0) :=
    { duration := |B| + 1
      duration_pos := by positivity
      curve := fun _ => (q, 0)
      initial := rfl
      initial_physical := ⟨hq.1.le, hq.2.le⟩
      physical := fun _ _ => ⟨hq.1.le, hq.2.le⟩
      in_domain := fun _ _ => V.closedEdge_subset_domain e ⟨hq.1.le, hq.2.le⟩
      integralCurve := fun t _ => by rw [hfield]; exact hasDerivAt_const t _
      interior_after_initial := fun _ _ => hq }
  have hk : |B| + 1 ≤ B := hB k.mem_durationSet
  linarith [le_abs_self B]

/-- **Necessity of condition (ii).**  A flight started in a component of the allowed region that
avoids both endpoints is confined there by energy conservation, so it cannot land. -/
theorem ShellRegular.allowedComponentsReachEnds {E : ℝ} (hS : V.ShellRegular E) :
    V.AllowedComponentsReachEnds E := by
  intro e q hq hqE
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hl, hr⟩ := hcon
  push Not at hl hr
  obtain ⟨s₁, hs₁, hVs₁⟩ := hl
  obtain ⟨s₂, hs₂, hVs₂⟩ := hr
  have hs₁q : s₁ < q := lt_of_le_of_ne hs₁.2 (by rintro rfl; linarith)
  have hqs₂ : q < s₂ := lt_of_le_of_ne hs₂.1 (by rintro rfl; linarith)
  have hqI : q ∈ Ioo (0 : ℝ) (Γ.length e) :=
    ⟨lt_of_le_of_lt hs₁.1 hs₁q, lt_of_lt_of_le hqs₂ hs₂.2⟩
  set x : ℝ × ℝ := (q, Real.sqrt (2 * (E - V.extension e q))) with hx_def
  have hx : V.hamiltonian e x.1 x.2 = E := by
    simp only [hx_def, hamiltonian]
    rw [Real.sq_sqrt (by linarith)]
    ring
  obtain ⟨k, -⟩ := V.exists_physicalEdgeSegment_from_interior (x := x) hqI
  have hbdd := hS.lands e x hx
  set T : ℝ := sSup (durationSet V e x) with hT_def
  have hT0 : 0 ≤ T := (k.duration_pos.trans_le (le_csSup hbdd k.mem_durationSet)).le
  set γ := k.maximalCurveClosed hbdd with hγ_def
  have hcont : ContinuousOn (fun t => (γ t).1) (Icc 0 T) := by
    have : ContinuousOn γ (Icc 0 T) := fun t ht =>
      (k.maximalCurveClosed_hasDerivWithinAt_Icc hbdd ht).continuousWithinAt
    exact continuous_fst.comp_continuousOn this
  have hγ0 : (γ 0).1 = q := by
    rw [hγ_def, k.maximalCurveClosed_initial hbdd]
  have hγT : (γ T).1 = 0 ∨ (γ T).1 = Γ.length e := by
    rw [hγ_def, hT_def, k.maximalCurveClosed_eq_endpoint hbdd]
    exact k.maximalEndpoint_coordinate_eq_zero_or_length hbdd
  have henergy : ∀ t ∈ Icc 0 T, V.extension e (γ t).1 ≤ E := by
    intro t ht
    have h := k.maximalCurveClosed_hamiltonian_eq_initial hbdd ht
    rw [hx] at h
    simp only [hamiltonian] at h
    nlinarith [sq_nonneg (γ t).2]
  rcases hγT with h0 | hℓ
  · obtain ⟨τ, hτ, hτs⟩ := intermediate_value_Icc' hT0 hcont
      (show s₁ ∈ Icc (γ T).1 (γ 0).1 by rw [h0, hγ0]; exact ⟨hs₁.1, hs₁.2⟩)
    have := henergy τ hτ
    simp only at hτs
    rw [hτs] at this
    linarith
  · obtain ⟨τ, hτ, hτs⟩ := intermediate_value_Icc hT0 hcont
      (show s₂ ∈ Icc (γ 0).1 (γ T).1 by rw [hℓ, hγ0]; exact ⟨hs₂.1, hs₂.2⟩)
    have := henergy τ hτ
    simp only at hτs
    rw [hτs] at this
    linarith

/-! ### Sufficiency -/

variable (V)

/-- A non-exceptional energy is not the potential at the left end of an edge. -/
private theorem extension_zero_ne {E : ℝ} (hE : E ∉ V.exceptionalEnergies) (e : Γ.Edge) :
    V.extension e 0 ≠ E := by
  intro h
  apply hE
  apply V.mem_exceptionalEnergies_iff.mpr
  refine ⟨Γ.endpoint e false, ?_⟩
  have hend := V.endpoint_value (e, false)
  simp only [FiniteMetricGraph.EdgeEnd.coordinate, FiniteMetricGraph.EdgeEnd.vertex] at hend
  simpa [h] using hend.symm

/-- A non-exceptional energy is not the potential at the right end of an edge. -/
private theorem extension_length_ne {E : ℝ} (hE : E ∉ V.exceptionalEnergies) (e : Γ.Edge) :
    V.extension e (Γ.length e) ≠ E := by
  intro h
  apply hE
  apply V.mem_exceptionalEnergies_iff.mpr
  refine ⟨Γ.endpoint e true, ?_⟩
  have hend := V.endpoint_value (e, true)
  simp only [FiniteMetricGraph.EdgeEnd.coordinate, FiniteMetricGraph.EdgeEnd.vertex] at hend
  simpa [h] using hend.symm

/-- The potential is differentiable on the closed edge. -/
private theorem hasDerivAt_extension {e : Γ.Edge} {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (Γ.length e)) :
    HasDerivAt (V.extension e) (deriv (V.extension e) q) q :=
  ((V.extension_contDiffAt_of_mem (V.closedEdge_subset_domain e hq)).differentiableAt
    (by norm_num)).hasDerivAt

/-- **The confining interval.**  The connected component `[α, β]` of the allowed region through an
allowed point `q₀`: the potential stays below `E` on it, and it contains every point `s` of the
edge joined to `q₀` by an allowed interval. -/
private theorem exists_confining_interval {E : ℝ} {e : Γ.Edge} {q₀ : ℝ}
    (hq₀ : q₀ ∈ Icc (0 : ℝ) (Γ.length e)) (hq₀E : V.extension e q₀ ≤ E) :
    ∃ α β : ℝ, α ≤ β ∧ 0 ≤ α ∧ β ≤ Γ.length e ∧
      (∀ r ∈ Icc α β, V.extension e r ≤ E) ∧
      ∀ s ∈ Icc (0 : ℝ) (Γ.length e), (∀ r ∈ uIcc q₀ s, V.extension e r ≤ E) →
        s ∈ Icc α β := by
  set A : Set ℝ :=
    {s | s ∈ Icc (0 : ℝ) (Γ.length e) ∧ ∀ r ∈ uIcc q₀ s, V.extension e r ≤ E} with hA_def
  have hq₀A : q₀ ∈ A := ⟨hq₀, fun r hr => by
    rw [uIcc_self, mem_singleton_iff] at hr
    rw [hr]; exact hq₀E⟩
  have hAne : A.Nonempty := ⟨q₀, hq₀A⟩
  have hbddB : BddBelow A := ⟨0, fun s hs => hs.1.1⟩
  have hbddA : BddAbove A := ⟨Γ.length e, fun s hs => hs.1.2⟩
  set S : Set ℝ := Icc (0 : ℝ) (Γ.length e) ∩ V.extension e ⁻¹' Iic E with hS_def
  have hSclosed : IsClosed S :=
    (V.extension_continuousOn_closedEdge e).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
  have hAS : A ⊆ S := fun s hs => ⟨hs.1, hs.2 s right_mem_uIcc⟩
  have hclS : closure A ⊆ S := closure_minimal hAS hSclosed
  have hαS : sInf A ∈ S := hclS (csInf_mem_closure hAne hbddB)
  have hβS : sSup A ∈ S := hclS (csSup_mem_closure hAne hbddA)
  refine ⟨sInf A, sSup A, (csInf_le hbddB hq₀A).trans (le_csSup hbddA hq₀A),
    le_csInf hAne (fun s hs => hs.1.1), csSup_le hAne (fun s hs => hs.1.2), ?_, ?_⟩
  · intro r hr
    rcases eq_or_lt_of_le hr.1 with hαr | hαr
    · rw [← hαr]; exact hαS.2
    rcases eq_or_lt_of_le hr.2 with hrβ | hrβ
    · rw [hrβ]; exact hβS.2
    obtain ⟨s₁, hs₁, hs₁r⟩ := exists_lt_of_csInf_lt hAne hαr
    obtain ⟨s₂, hs₂, hrs₂⟩ := exists_lt_of_lt_csSup hAne hrβ
    rcases le_total r q₀ with hrq | hqr
    · exact hs₁.2 r (mem_uIcc.mpr (Or.inr ⟨hs₁r.le, hrq⟩))
    · exact hs₂.2 r (mem_uIcc.mpr (Or.inl ⟨hqr, hrs₂.le⟩))
  · intro s hs hsr
    exact ⟨csInf_le hbddB ⟨hs, hsr⟩, le_csSup hbddA ⟨hs, hsr⟩⟩

/-- **The turning points.**  Under conditions (i) and (ii), the points of an allowed interval
`[α, β]` at which `V_e = E` are simple turning points of one common orientation: a single sign
`σ = ±1` makes `σ · F` positive at all of them, `F` being the force. -/
private theorem exists_turning_sign {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hcrit : V.NoInteriorCriticalValue E) (hreach : V.AllowedComponentsReachEnds E)
    {e : Γ.Edge} {α β : ℝ} (hαβ : α ≤ β) (hα : 0 ≤ α) (hβ : β ≤ Γ.length e)
    (hle : ∀ r ∈ Icc α β, V.extension e r ≤ E) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ q ∈ Icc α β, V.extension e q = E → 0 < σ * V.force e q := by
  set f := V.extension e with hf_def
  have hsub : Icc α β ⊆ Icc (0 : ℝ) (Γ.length e) := Icc_subset_Icc hα hβ
  -- every turning point lies in the open edge, with nonzero derivative
  have hturn : ∀ q ∈ Icc α β, f q = E →
      q ∈ Ioo (0 : ℝ) (Γ.length e) ∧ deriv f q ≠ 0 := by
    intro q hq hqE
    have hq' := hsub hq
    have h0 : q ≠ 0 := by rintro rfl; exact V.extension_zero_ne hE e hqE
    have hℓ : q ≠ Γ.length e := by rintro rfl; exact V.extension_length_ne hE e hqE
    have hI : q ∈ Ioo (0 : ℝ) (Γ.length e) :=
      ⟨lt_of_le_of_ne hq'.1 (Ne.symm h0), lt_of_le_of_ne hq'.2 hℓ⟩
    exact ⟨hI, hcrit e q hI hqE⟩
  -- a turning point below `β` has negative derivative
  have hT1 : ∀ q ∈ Icc α β, f q = E → q < β → deriv f q < 0 := by
    intro q hq hqE hqβ
    rcases lt_or_gt_of_ne (hturn q hq hqE).2 with h | h
    · exact h
    · obtain ⟨x, hx, hfx⟩ :=
        exists_Ioc_gt_of_hasDerivAt_pos (V.hasDerivAt_extension (hsub hq)) h hqβ
      have := hle x ⟨hq.1.trans hx.1.le, hx.2⟩
      rw [← hf_def] at hfx
      linarith
  -- a turning point above `α` has positive derivative
  have hT2 : ∀ q ∈ Icc α β, f q = E → α < q → 0 < deriv f q := by
    intro q hq hqE hαq
    rcases lt_or_gt_of_ne (hturn q hq hqE).2 with h | h
    · obtain ⟨x, hx, hfx⟩ :=
        exists_Ico_gt_of_hasDerivAt_neg (V.hasDerivAt_extension (hsub hq)) h hαq
      have := hle x ⟨hx.1, hx.2.le.trans hq.2⟩
      rw [← hf_def] at hfx
      linarith
    · exact h
  have hforce : ∀ q, V.force e q = -deriv f q := fun q => rfl
  by_cases hβE : f β = E ∧ 0 < deriv f β
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro q hq hqE
    rw [hforce]
    suffices 0 < deriv f q by linarith
    rcases eq_or_lt_of_le hq.1 with hαq | hαq
    · subst hαq
      rcases eq_or_lt_of_le hαβ with hαβ' | hαβ'
      · rw [hαβ']; exact hβE.2
      · -- turning points at both ends of opposite orientation contradict condition (ii)
        exfalso
        have hdα : deriv f α < 0 := hT1 α hq hqE hαβ'
        have hβI := (hturn β ⟨hαβ, le_rfl⟩ hβE.1).1
        have hαI := (hturn α hq hqE).1
        rcases hreach e α (hsub hq) (le_of_eq hqE) with hl | hr
        · obtain ⟨x, hx, hfx⟩ :=
            exists_Ico_gt_of_hasDerivAt_neg (V.hasDerivAt_extension (hsub hq)) hdα hαI.1
          have := hl x ⟨hx.1, hx.2.le⟩
          rw [← hf_def] at hfx this
          linarith
        · obtain ⟨x, hx, hfx⟩ :=
            exists_Ioc_gt_of_hasDerivAt_pos (V.hasDerivAt_extension (hsub ⟨hαβ, le_rfl⟩))
              hβE.2 hβI.2
          have := hr x ⟨hαβ'.le.trans hx.1.le, hx.2⟩
          rw [← hf_def] at hfx this
          linarith
    · exact hT2 q hq hqE hαq
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro q hq hqE
    rw [hforce, one_mul, neg_pos]
    rcases eq_or_lt_of_le hq.2 with hqβ | hqβ
    · subst hqβ
      have hne := (hturn q hq hqE).2
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · exact absurd ⟨hqE, h⟩ hβE
    · exact hT1 q hq hqE hqβ

/-- Every point visited by a physical segment is joined to its initial position by an allowed
interval: by the intermediate value theorem the segment passes through each point in between, and
energy conservation keeps the potential below the energy there. -/
private theorem segment_allowed {E : ℝ} {e : Γ.Edge} {x : ℝ × ℝ}
    (k : V.PhysicalEdgeSegment e x) (hx : V.hamiltonian e x.1 x.2 = E) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) k.duration) :
    ∀ r ∈ uIcc x.1 (k.curve t).1, V.extension e r ≤ E := by
  intro r hr
  have hcont : ContinuousOn (fun τ => (k.curve τ).1) (uIcc 0 t) := by
    rw [uIcc_of_le ht.1]
    exact continuous_fst.comp_continuousOn
      (k.continuousOn_curve.mono (Icc_subset_Icc le_rfl ht.2))
  have hr' : r ∈ uIcc (k.curve 0).1 (k.curve t).1 := by rw [k.initial]; exact hr
  obtain ⟨τ, hτ, hτr⟩ := intermediate_value_uIcc hcont hr'
  rw [uIcc_of_le ht.1] at hτ
  have h := k.hamiltonian_eq_initial_at τ ⟨hτ.1, hτ.2.trans ht.2⟩
  rw [hx] at h
  simp only [hamiltonian] at h
  simp only at hτr
  rw [← hτr]
  nlinarith [sq_nonneg (k.curve τ).2]

/-- **The uniform landing-time bound.**  Under conditions (i) and (ii), the durations of all
physical segments from a fixed state of energy `E` are bounded. -/
private theorem exists_duration_bound {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hcrit : V.NoInteriorCriticalValue E) (hreach : V.AllowedComponentsReachEnds E)
    {e : Γ.Edge} {x : ℝ × ℝ} (hx : V.hamiltonian e x.1 x.2 = E)
    (hx1 : x.1 ∈ Icc (0 : ℝ) (Γ.length e)) :
    ∃ B : ℝ, ∀ k : V.PhysicalEdgeSegment e x, k.duration ≤ B := by
  set ℓ := Γ.length e with hℓ_def
  have hx1E : V.extension e x.1 ≤ E := by
    simp only [hamiltonian] at hx
    nlinarith [sq_nonneg x.2]
  obtain ⟨α, β, hαβ, hα, hβ, hle, hconf⟩ := V.exists_confining_interval hx1 hx1E
  obtain ⟨σ, hσ, hσpos⟩ := V.exists_turning_sign hE hcrit hreach hαβ hα hβ hle
  have hsub : Icc α β ⊆ Icc (0 : ℝ) ℓ := Icc_subset_Icc hα hβ
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have habsσ : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  -- the compactness step
  obtain ⟨κ, c, hκ, hc, hdrift⟩ := exists_uniform_drift (K := Icc α β) isCompact_Icc
    (nonempty_Icc.mpr hαβ) (w := fun q => 2 * (E - V.extension e q))
    (g := fun q => σ * V.force e q)
    (continuousOn_const.mul (continuousOn_const.sub
      ((V.extension_continuousOn_closedEdge e).mono hsub)))
    (continuousOn_const.mul ((V.continuousOn_force e).mono
      (hsub.trans (V.closedEdge_subset_domain e))))
    (fun q hq => by have := hle q hq; linarith)
    (fun q hq hq0 => hσpos q hq (by linarith))
  -- the momentum bound
  obtain ⟨C, hC⟩ := V.exists_lowerBound_extension_closedEdge e
  set P : ℝ := Real.sqrt (2 * (E - C)) with hP_def
  set m : ℝ := Real.exp (-(κ * ℓ)) * c with hm_def
  have hm : 0 < m := mul_pos (Real.exp_pos _) hc
  refine ⟨2 * Real.exp (κ * ℓ) * P / m, ?_⟩
  intro k
  set D := k.duration with hD_def
  -- notation along the segment
  have hphys : ∀ t ∈ Icc (0 : ℝ) D, (k.curve t).1 ∈ Icc α β := fun t ht =>
    hconf _ (k.physical_at t ht) (V.segment_allowed k hx ht)
  have henergy : ∀ t ∈ Icc (0 : ℝ) D,
      (k.curve t).2 ^ 2 = 2 * (E - V.extension e (k.curve t).1) := by
    intro t ht
    have h := k.hamiltonian_eq_initial_at t ht
    rw [hx] at h
    simp only [hamiltonian] at h
    linarith
  let Φ : ℝ → ℝ := fun t => σ * Real.exp (σ * κ * (k.curve t).1) * (k.curve t).2
  let Φ' : ℝ → ℝ := fun t => Real.exp (σ * κ * (k.curve t).1) *
    (κ * (k.curve t).2 ^ 2 + σ * V.force e (k.curve t).1)
  have hderiv : ∀ t ∈ Icc (0 : ℝ) D, HasDerivAt Φ (Φ' t) t := by
    intro t ht
    have hq' := V.edgeIntegralCurve_hasDerivAt_fst (k.integralCurve t ht)
    have hp' := V.edgeIntegralCurve_hasDerivAt_snd (k.integralCurve t ht)
    have h := (((hq'.const_mul (σ * κ)).exp).const_mul σ).mul hp'
    refine h.congr_deriv ?_
    simp only [Φ']
    linear_combination (κ * Real.exp (σ * κ * (k.curve t).1) * (k.curve t).2 ^ 2) * hσσ
  -- the exponential weight on the closed edge
  have hexp_lo : ∀ q ∈ Icc (0 : ℝ) ℓ, Real.exp (-(κ * ℓ)) ≤ Real.exp (σ * κ * q) := by
    intro q hq
    apply Real.exp_le_exp.mpr
    have h1 := mul_nonneg hκ hq.1
    have h2 := mul_le_mul_of_nonneg_left hq.2 hκ
    rcases hσ with rfl | rfl <;> nlinarith
  have hexp_hi : ∀ q ∈ Icc (0 : ℝ) ℓ, Real.exp (σ * κ * q) ≤ Real.exp (κ * ℓ) := by
    intro q hq
    apply Real.exp_le_exp.mpr
    have h1 := mul_nonneg hκ hq.1
    have h2 := mul_le_mul_of_nonneg_left hq.2 hκ
    rcases hσ with rfl | rfl <;> nlinarith
  -- the drift is bounded below
  have hΦ'_lo : ∀ t ∈ Icc (0 : ℝ) D, m ≤ Φ' t := by
    intro t ht
    have hq := hphys t ht
    have hd := hdrift _ hq
    simp only [Φ', hm_def]
    rw [henergy t ht]
    exact mul_le_mul (hexp_lo _ (hsub hq)) hd hc.le (Real.exp_pos _).le
  -- the drift function is bounded
  have hΦ_bd : ∀ t ∈ Icc (0 : ℝ) D, |Φ t| ≤ Real.exp (κ * ℓ) * P := by
    intro t ht
    have hq := k.physical_at t ht
    have hpP : |(k.curve t).2| ≤ P :=
      V.abs_momentum_le_sqrt_of_hamiltonian_le (hC _ hq)
        (le_of_eq ((k.hamiltonian_eq_initial_at t ht).trans hx))
    simp only [Φ]
    rw [abs_mul, abs_mul, habsσ, one_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hexp_hi _ hq) hpP (abs_nonneg _) (Real.exp_pos _).le
  -- the mean value theorem
  have hDpos : 0 < D := k.duration_pos
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope Φ Φ' hDpos
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t (Ioo_subset_Icc_self ht))
  rw [sub_zero, eq_div_iff hDpos.ne'] at hslope
  have hξm := hΦ'_lo ξ (Ioo_subset_Icc_self hξ)
  have hΦD := hΦ_bd D ⟨hDpos.le, le_rfl⟩
  have hΦ0 := hΦ_bd 0 ⟨le_rfl, hDpos.le⟩
  have hmD : m * D ≤ Φ' ξ * D := mul_le_mul_of_nonneg_right hξm hDpos.le
  rw [le_div_iff₀ hm]
  have h1 := le_abs_self (Φ D)
  have h2 := neg_abs_le (Φ 0)
  linarith

/-! ### Lemma VIII.2 -/

/-- **Lemma VIII.2.**  An energy `E` which is not a vertex value is shell-regular if and only if,
on every edge, `E` is not a critical value of the potential on the open edge and every nonempty
connected component of the allowed region `{V_e ≤ E}` meets an endpoint of the edge. -/
theorem shellRegular_iff {E : ℝ} (hE : E ∉ V.exceptionalEnergies) :
    V.ShellRegular E ↔ V.NoInteriorCriticalValue E ∧ V.AllowedComponentsReachEnds E := by
  constructor
  · intro hS
    exact ⟨hS.noInteriorCriticalValue, hS.allowedComponentsReachEnds⟩
  · rintro ⟨hcrit, hreach⟩
    refine ⟨hE, fun e x hx => ?_⟩
    by_cases hne : (durationSet V e x).Nonempty
    · obtain ⟨_, k₀, -⟩ := hne
      obtain ⟨B, hB⟩ := V.exists_duration_bound hE hcrit hreach hx k₀.initial_physical
      exact ⟨B, fun _ ⟨k, hk⟩ => hk ▸ hB k⟩
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact bddAbove_empty

/-- **Energies above the potential on every edge.**  If `E` is not a vertex value and exceeds the
potential on every closed edge, then `E` is shell-regular. -/
theorem shellRegular_of_forall_lt_of_notMem {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (h : ∀ e, ∀ q ∈ Set.Icc 0 (Γ.length e), V.extension e q < E) : V.ShellRegular E := by
  refine (V.shellRegular_iff hE).mpr ⟨?_, ?_⟩
  · intro e q hq hqE _
    exact (h e q ⟨hq.1.le, hq.2.le⟩).ne hqE
  · intro e q hq _
    exact Or.inl fun s hs => (h e s ⟨hs.1, hs.2.trans hq.2⟩).le

/-- **The final sentence of Lemma VIII.2.**  Every energy above the maximum of the potential on
`Γ` — above its values on every closed edge and at every vertex — is shell-regular.  The vertex
hypothesis only matters for vertices without incident edges, whose values are not seen by any
edge. -/
theorem shellRegular_of_forall_lt {E : ℝ}
    (h : ∀ e, ∀ q ∈ Set.Icc 0 (Γ.length e), V.extension e q < E)
    (hv : ∀ v : Γ.Vertex, V.vertexValue v < E) : V.ShellRegular E := by
  refine V.shellRegular_of_forall_lt_of_notMem ?_ h
  intro hE
  obtain ⟨v, hv'⟩ := V.mem_exceptionalEnergies_iff.mp hE
  exact (hv v).ne hv'

end MechanicalPotential

end HamiltonianMetricGraphs
