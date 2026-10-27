/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.ScatteredTrajectory

/-!
# The no-Zeno estimate for scattered trajectories (Lemmas V.2 and V.3)

The paper states its no-Zeno lemmas for scattered trajectories (Definition V.4), in terms of
their **vertex impacts**, eq. (impact): the times `t₀` at which `γ(t₀) = π(α)` for a boundary
covector `α` at some vertex.  Since `π(α) = π(S_v α)` and every outgoing covector is `S_v` of an
incoming one, it suffices to range over incoming covectors; this is `IsVertexImpactClass`, and
`vertexImpactSet γ` is the set `I_γ` of vertex impacts of `γ`.

* **Lemma V.2 (`no_zeno`).**  For a compact `K` disjoint from the vertex values `{V(v)}` there is
  `τ_K > 0` such that no scattered trajectory with energy in `K` has two distinct vertex impacts
  separated by less than `τ_K` (`IsNoZenoConstant V S K τ_K`).
* **Lemma V.3 (`impact_local_finiteness`).**  For a scattered trajectory `γ` of energy `E` and the
  constant `τ_E` of Lemma V.2 for `K = {E}`, distinct vertex impacts are at least `τ_E` apart and
  `#(I_γ ∩ [a, b]) ≤ 1 + (b - a)/τ_E` for every compact interval `[a, b]`.

The energy of a scattered trajectory is its conserved energy `H(γ t) = H(z)`
(`quotientHamiltonian_isScatteredTrajectory`).  The impact set `I` of Definition V.4 consists of
vertex impacts (`subset_vertexImpactSet`), and for the orbit `t ↦ Φₜ z` the vertex impacts are
exactly the impact set `flowImpactSet z` used in `flow_isScatteredTrajectory`
(`vertexImpactSet_flow`).
-/

namespace HamiltonianMetricGraphs

open Set

/-- A set of reals whose distinct points are at least `τ > 0` apart meets a compact interval
`[a, b]` in at most `1 + (b - a)/τ` points. -/
theorem ncard_inter_Icc_le_of_separated {I : Set ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hsep : ∀ s ∈ I, ∀ u ∈ I, s < u → s + τ ≤ u) {a b : ℝ} (hab : a ≤ b) :
    (I ∩ Icc a b).Finite ∧ ((I ∩ Icc a b).ncard : ℝ) ≤ 1 + (b - a) / τ := by
  have hfin : (I ∩ Icc a b).Finite :=
    finite_inter_isCompact_of_separated hτ hsep _ isCompact_Icc
  refine ⟨hfin, ?_⟩
  set f : ℝ → ℤ := fun t => ⌊(t - a) / τ⌋ with hf
  have key : ∀ s ∈ I, ∀ u ∈ I, s < u → f s < f u := by
    intro s hs u hu hsu
    have h1 : (s - a) / τ + 1 ≤ (u - a) / τ := by
      rw [div_add_one hτ.ne', div_le_div_iff_of_pos_right hτ]
      linarith [hsep s hs u hu hsu]
    calc f s < f s + 1 := lt_add_one _
      _ = ⌊(s - a) / τ + 1⌋ := (Int.floor_add_one _).symm
      _ ≤ f u := Int.floor_mono h1
  have hmaps : Set.MapsTo f (hfin.toFinset : Set ℝ) (Finset.Icc 0 ⌊(b - a) / τ⌋ : Set ℤ) := by
    intro t ht
    rw [Set.Finite.coe_toFinset] at ht
    rw [Finset.coe_Icc, mem_Icc]
    refine ⟨Int.floor_nonneg.mpr (div_nonneg (by linarith [ht.2.1]) hτ.le), ?_⟩
    exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith [ht.2.2]) hτ.le)
  have hinj : Set.InjOn f (hfin.toFinset : Set ℝ) := by
    intro s hs u hu hsu
    rw [Set.Finite.coe_toFinset] at hs hu
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (key s hs.1 u hu.1 h).ne hsu
    · exact (key u hu.1 s hs.1 h).ne hsu.symm
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Int.card_Icc] at hcard
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have hx : (0 : ℝ) ≤ (b - a) / τ := div_nonneg (by linarith) hτ.le
  have hfl : (0 : ℤ) ≤ ⌊(b - a) / τ⌋ := Int.floor_nonneg.mpr hx
  have htoNat : (((⌊(b - a) / τ⌋ + 1 - 0).toNat : ℕ) : ℝ) = (⌊(b - a) / τ⌋ : ℝ) + 1 := by
    rw [sub_zero]
    have h := Int.toNat_of_nonneg (show (0 : ℤ) ≤ ⌊(b - a) / τ⌋ + 1 by linarith)
    exact_mod_cast h
  calc (hfin.toFinset.card : ℝ) ≤ (((⌊(b - a) / τ⌋ + 1 - 0).toNat : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = (⌊(b - a) / τ⌋ : ℝ) + 1 := htoNat
    _ ≤ 1 + (b - a) / τ := by linarith [Int.floor_le ((b - a) / τ)]

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-- The **vertex impacts** of a curve `γ` (eq. (impact) of the paper): the times at which `γ`
sits over a vertex, `γ(t₀) = π(α)` for an incoming boundary covector `α`. -/
def vertexImpactSet (γ : ℝ → RegularScatteringPhaseSpace (V := V) S) : Set ℝ :=
  {t | IsVertexImpactClass V S (γ t).1}

/-- Every point of the impact set `I` of Definition V.4 is a vertex impact. -/
theorem subset_vertexImpactSet {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} {I : Set ℝ}
    (hγ : IsScatteredTrajectoryWith V S γ I) : I ⊆ vertexImpactSet V S γ := by
  intro t₀ ht₀
  obtain ⟨v, α, hα, -⟩ := hγ.impact t₀ ht₀
  exact ⟨v, α, hα⟩

/-- **No-Zeno constant for an energy window `K`.**  `τ > 0`, and no scattered trajectory with
energy in `K` has two distinct vertex impacts separated by less than `τ`. -/
def IsNoZenoConstant (K : Set ℝ) (τ : ℝ) : Prop :=
  0 < τ ∧ ∀ (z : RegularScatteringPhaseSpace (V := V) S)
    (γ : ℝ → RegularScatteringPhaseSpace (V := V) S), IsScatteredTrajectory V S z γ →
      quotientHamiltonian (V := V) S z.1 ∈ K →
        ∀ s ∈ vertexImpactSet V S γ, ∀ u ∈ vertexImpactSet V S γ, s ≠ u → τ ≤ |u - s|

variable [Nonempty Γ.Edge]

/-- For the orbit of the flow, the vertex impacts are the impact set `flowImpactSet`. -/
theorem vertexImpactSet_flow (z : RegularScatteringPhaseSpace (V := V) S) :
    vertexImpactSet V S (flow V S z) = flowImpactSet V S z := rfl

/-- **Energy conservation along a scattered trajectory**: `H(γ t) = H(z)`. -/
theorem quotientHamiltonian_isScatteredTrajectory {z : RegularScatteringPhaseSpace (V := V) S}
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} (hγ : IsScatteredTrajectory V S z γ)
    (t : ℝ) : quotientHamiltonian (V := V) S (γ t).1 = quotientHamiltonian (V := V) S z.1 := by
  rw [hγ.eq_flow, quotientHamiltonian_flow]

/-- **Lemma V.2 (no-Zeno estimate).**  Let `K ⊂ ℝ` be compact with `K ∩ {V(v) : v ∈ 𝒱} = ∅`.
Then there is `τ_K > 0` such that no scattered trajectory with energy in `K` has two distinct
vertex impacts separated by less than `τ_K`. -/
theorem no_zeno {K : Set ℝ} (hK : IsCompact K)
    (hKV : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ τ : ℝ, IsNoZenoConstant V S K τ := by
  obtain ⟨τ, hτ, hbound⟩ :=
    FlightState.exists_uniform_impactDuration_lower_bound (V := V) K hK hKV
  refine ⟨τ, hτ, ?_⟩
  -- the ordered form, along a scattered trajectory
  have hord : ∀ (z : RegularScatteringPhaseSpace (V := V) S)
      (γ : ℝ → RegularScatteringPhaseSpace (V := V) S), IsScatteredTrajectory V S z γ →
      quotientHamiltonian (V := V) S z.1 ∈ K →
      ∀ s ∈ vertexImpactSet V S γ, ∀ u ∈ vertexImpactSet V S γ, s < u → s + τ ≤ u := by
    intro z γ hγ hzK s hs u hu hsu
    rw [hγ.eq_flow] at hs hu
    obtain ⟨v, α, hs⟩ := hs
    by_contra hlt
    push Not at hlt
    set w := flow V S z s with hw
    set A := repFlight V S w with hA
    have hout : A.IsOutgoing := repFlight_isOutgoing_of_isVertexImpact V S w α hs
    have henergy : A.energy ∈ K := by
      rw [hA, repFlight_energy, hw, quotientHamiltonian_flow]
      exact hzK
    have hdur : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V A.edge A.state),
        u - s < sSup (PhysicalEdgeSegment.durationSet V A.edge A.state) :=
      fun hbdd => lt_of_lt_of_le (by linarith) (hbound A hout henergy hbdd)
    have hval := flow_val_eq_graphClass_flightCurve V S w (sub_pos.mpr hsu).le hdur
    rw [hw, flow_flow, show s + (u - s) = u by ring] at hval
    have hint := FlightState.flightCurve_interior V A (sub_pos.mpr hsu) hdur
    exact not_isVertexImpactClass_graphClass V S hint (hval ▸ hu)
  intro z γ hγ hzK s hs u hu hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hord z γ hγ hzK s hs u hu h
    rw [abs_of_pos (by linarith)]
    linarith
  · have := hord z γ hγ hzK u hu s hs h
    rw [abs_of_neg (by linarith)]
    linarith

omit [Nonempty Γ.Edge] in
/-- **Lemma V.3 (local finiteness of impacts).**  Let `γ` be a scattered trajectory through `z`,
of energy `E = H(γ t) = H(z)`, and let `τ_E` be a no-Zeno constant of Lemma V.2 for `K = {E}`.
Then distinct vertex impacts of `γ` are separated by at least `τ_E`, and
`#(I_γ ∩ [a, b]) ≤ 1 + (b - a)/τ_E` for every compact interval `[a, b]`. -/
theorem impact_local_finiteness {z : RegularScatteringPhaseSpace (V := V) S}
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} (hγ : IsScatteredTrajectory V S z γ)
    {τ : ℝ} (hτ : IsNoZenoConstant V S {quotientHamiltonian (V := V) S z.1} τ) :
    (∀ s ∈ vertexImpactSet V S γ, ∀ u ∈ vertexImpactSet V S γ, s ≠ u → τ ≤ |u - s|) ∧
      ∀ a b : ℝ, a ≤ b → (vertexImpactSet V S γ ∩ Icc a b).Finite ∧
        ((vertexImpactSet V S γ ∩ Icc a b).ncard : ℝ) ≤ 1 + (b - a) / τ := by
  have hsep := hτ.2 z γ hγ rfl
  refine ⟨hsep, fun a b hab => ncard_inter_Icc_le_of_separated hτ.1 ?_ hab⟩
  intro s hs u hu hsu
  have h := hsep s hs u hu hsu.ne
  rw [abs_of_pos (by linarith)] at h
  linarith

/-- Lemma V.3 with the constant supplied by Lemma V.2: regularity of `E` makes `{E}` an
admissible window. -/
theorem exists_impact_local_finiteness {z : RegularScatteringPhaseSpace (V := V) S}
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} (hγ : IsScatteredTrajectory V S z γ) :
    ∃ τ > 0, (∀ s ∈ vertexImpactSet V S γ, ∀ u ∈ vertexImpactSet V S γ, s ≠ u → τ ≤ |u - s|) ∧
      ∀ a b : ℝ, a ≤ b → (vertexImpactSet V S γ ∩ Icc a b).Finite ∧
        ((vertexImpactSet V S γ ∩ Icc a b).ncard : ℝ) ≤ 1 + (b - a) / τ := by
  obtain ⟨τ, hτ⟩ := no_zeno V S (K := {quotientHamiltonian (V := V) S z.1}) isCompact_singleton
    (fun E hE => by rw [mem_singleton_iff.mp hE]; exact z.2)
  exact ⟨τ, hτ.1, impact_local_finiteness V S hγ hτ⟩

end MechanicalPotential

end HamiltonianMetricGraphs
