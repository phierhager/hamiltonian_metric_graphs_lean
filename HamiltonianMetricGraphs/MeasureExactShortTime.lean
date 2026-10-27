/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemmas VI.2 and VI.3 as printed: the short-time Borel structure and the one-impact invariance.
-/

import HamiltonianMetricGraphs.ShortTime
import HamiltonianMetricGraphs.ImpactCount
import HamiltonianMetricGraphs.FlowMeasurable
import HamiltonianMetricGraphs.NoZenoExact

/-!
# Lemmas VI.2 and VI.3 in the form printed in the paper

Fix a compact energy window `K` disjoint from the vertex values `{V(v)}` and write
`E_K = H⁻¹(K) ∩ P^Reg` (`energySector S K`).  A time `t` is a *vertex impact* of `z` when the
scattered trajectory `t ↦ Φ_t z` sits over a vertex at time `t` (`IsImpactTime`, the paper's
(5.1)).

* **The no-Zeno constant `τ_K` (Lemma V.2).**  The paper's `τ_K` is a constant in the sense of
  `IsNoZenoConstant V S K τ` (`NoZenoExact.lean`): no scattered trajectory with energy in `K` has
  two distinct vertex impacts less than `τ` apart; one exists by `no_zeno`.  Every such constant
  is an `IsImpactSeparationConstant K τ` — the same separation for the impact times `IsImpactTime`
  of the orbits `t ↦ Φ_t z` (`IsNoZenoConstant.isImpactSeparationConstant`, via
  `flow_isScatteredTrajectory` and `isVertexImpactClass_of_isImpactTime`).  The primed theorems
  `short_time_borel'` and `one_impact_measure'` take the paper's `τ_K`; the unprimed ones take the
  weaker separation hypothesis.  (`exists_noZenoConstant` also gives a separation constant
  directly, as the uniform flight-duration bound `exists_uniform_impactDuration_lower_bound`.)
* **Lemma VI.2** (`short_time_borel`).  For `0 < Δ < τ_K` the *no-impact set*
  `{z ∈ E_K | no vertex impact in [0, Δ]}` (`noImpactWindow`), the *at-most-one-impact set*
  `{z ∈ E_K | at most one vertex impact in [0, Δ]}` (`atMostOneImpactWindow`) and the
  *one-impact set* `{z ∈ E_K | exactly one vertex impact in [0, Δ]}` (`oneImpactWindow`) are
  measurable, and `Φ_Δ` restricted to each of them is measurable.  Moreover the at-most-one-impact
  set is all of `E_K`, which is the sentence "no trajectory in `E_K` has more than one vertex
  impact in `[0, Δ]`" of the paper's proof.
* **Lemma VI.3** (`one_impact_measure`).  For `0 < Δ < τ_K`,
  `m(Φ_Δ⁻¹ A ∩ E_K) = m(A ∩ E_K)` for every measurable `A ⊆ P^Reg`, and the same identity on the
  at-most-one-impact set.

## How the proofs differ from the paper's

*Measurability of the no-impact set.*  The paper obtains it as the complement of the one-impact
set, whose measurability it gets from the Lusin–Souslin theorem.  Here the no-impact set is
identified exactly (`noImpactWindow_eq_iUnion`) with the union over edges of the no-impact strata
`noImpactPiece`, i.e. the points whose outgoing representative is an interior state whose flight
survives past `Δ`; these are measurable because the edge no-impact set is *open*
(`isOpen_noImpactSet`).  The one-impact set is then `E_K` minus the no-impact set.

*Measurability of `Φ_Δ` on the pieces.*  It is the restriction of the globally measurable map
`Φ_Δ` (`measurable_flow`, Lemma VI.4, proved in `FlowMeasurable.lean` through the outgoing chart
without a Lusin–Souslin argument), so no piecewise formula is needed.

*Lemma VI.3.*  It is derived from the global invariance `measure_preimage_flow` and the energy
conservation `H ∘ Φ_t = H`: since `E_K` is invariant, `Φ_Δ⁻¹ A ∩ E_K = Φ_Δ⁻¹ (A ∩ E_K)`.  This is
mathematically valid, and the identity in fact holds for every real `Δ` and every measurable `K`
(`measure_preimage_flow_inter_energySector`); the restriction `0 < Δ < τ_K` of the printed lemma is
not needed for it.  The global invariance itself is proved in `ShortTime.lean` from a stratified
short-time argument (no-impact, one-impact, end-of-step and departure strata), which is the
paper's proof of Lemma VI.3 organized differently.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set MeasureTheory FlightState PhysicalEdgeSegment

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V) [Nonempty Γ.Edge]

/-! ### The sets of Lemma VI.2 -/

/-- The **no-impact set** for `[0, Δ]` on `E_K`: the regular points of energy in `K` whose
trajectory has no vertex impact at any time `t ∈ [0, Δ]`. -/
def noImpactWindow (K : Set ℝ) (Δ : ℝ) : Set (RegularScatteringPhaseSpace (V := V) S) :=
  {z | z ∈ V.energySector S K ∧ ∀ t ∈ Icc (0 : ℝ) Δ, ¬ IsImpactTime V S z t}

/-- The **at-most-one-impact set** for `[0, Δ]` on `E_K`: the regular points of energy in `K`
whose trajectory has at most one vertex impact in `[0, Δ]`. -/
def atMostOneImpactWindow (K : Set ℝ) (Δ : ℝ) : Set (RegularScatteringPhaseSpace (V := V) S) :=
  {z | z ∈ V.energySector S K ∧ ({t | IsImpactTime V S z t} ∩ Icc (0 : ℝ) Δ).Subsingleton}

/-- The **one-impact set** `E_K¹` for `[0, Δ]`: the regular points of energy in `K` whose
trajectory has exactly one vertex impact in `[0, Δ]`. -/
def oneImpactWindow (K : Set ℝ) (Δ : ℝ) : Set (RegularScatteringPhaseSpace (V := V) S) :=
  {z | z ∈ V.energySector S K ∧ ∃! t, t ∈ Icc (0 : ℝ) Δ ∧ IsImpactTime V S z t}

/-- **The no-Zeno constant of Lemma V.2** for the energy window `K`: `τ > 0`, and no scattered
trajectory with energy in `K` has two distinct vertex impacts separated by less than `τ`. -/
def IsImpactSeparationConstant (K : Set ℝ) (τ : ℝ) : Prop :=
  0 < τ ∧ ∀ z ∈ V.energySector S K, ∀ t t' : ℝ, IsImpactTime V S z t → IsImpactTime V S z t' →
    t ≠ t' → τ ≤ |t - t'|

/-! ### Lemma V.2 on the quotient: existence of `τ_K` -/

/-- **Lemma V.2 (no-Zeno estimate) for the two-sided quotient flow.**  For a compact `K` disjoint
from the vertex values there is `τ_K > 0` such that no trajectory with energy in `K` has two
distinct vertex impacts less than `τ_K` apart.  The constant is the uniform lower bound for the
flight durations of outgoing states with energy in `K`
(`exists_uniform_impactDuration_lower_bound`). -/
theorem exists_noZenoConstant {K : Set ℝ} (hK : IsCompact K)
    (hKreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) : ∃ τ : ℝ, V.IsImpactSeparationConstant S K τ := by
  obtain ⟨τ, hτ, hsep⟩ := exists_uniform_impactDuration_lower_bound (V := V) K hK hKreg
  refine ⟨τ, hτ, ?_⟩
  -- the ordered case
  have key : ∀ z ∈ V.energySector S K, ∀ t t' : ℝ, IsImpactTime V S z t →
      IsImpactTime V S z t' → t < t' → τ ≤ t' - t := by
    intro z hz t t' ht ht' hlt
    set a := repFlight V S (flow V S z t) with ha
    have haE : a.energy ∈ K := by
      rw [ha, repFlight_energy, quotientHamiltonian_flow]
      exact hz
    have hsep' : ∀ b : V.FlightState, b.IsOutgoing → b.energy = a.energy →
        ∀ _ : BddAbove (durationSet V b.edge b.state), τ ≤ sSup (durationSet V b.edge b.state) :=
      fun b hout hb hbdd => hsep b hout (by rw [hb]; exact haE) hbdd
    obtain ⟨hsepa, -⟩ := impactTimes_count (S := S) a hτ hsep'
    have h0 : (0 : ℝ) ∈ impactTimes S a := by
      rw [← isImpactTime_iff_of_nonneg V S (flow V S z t) le_rfl, isImpactTime_flow, add_zero]
      exact ht
    have h1 : t' - t ∈ impactTimes S a := by
      rw [← isImpactTime_iff_of_nonneg V S (flow V S z t) (by linarith), isImpactTime_flow,
        show t + (t' - t) = t' by ring]
      exact ht'
    have := hsepa 0 h0 (t' - t) h1 (by linarith)
    linarith
  intro z hz t t' ht ht' hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [abs_sub_comm, abs_of_pos (by linarith)]
    exact key z hz t t' ht ht' hlt
  · rw [abs_of_pos (by linarith)]
    exact key z hz t' t ht' ht hlt

/-! ### The no-impact set in edge coordinates -/

/-- **The no-impact condition in edge coordinates.**  A regular point has no vertex impact in
`[0, Δ]` exactly when its outgoing representative is an interior regular state of its edge whose
flight survives past `Δ`. -/
theorem noImpact_iff_mem_noImpactSet (z : RegularScatteringPhaseSpace (V := V) S) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) :
    (∀ t ∈ Icc (0 : ℝ) Δ, ¬ IsImpactTime V S z t) ↔
      (rep V S z.1).1.2.1 ∈ V.noImpactSet (rep V S z.1).1.1 Δ := by
  classical
  set a := repFlight V S z with ha
  change (∀ t ∈ Icc (0 : ℝ) Δ, ¬ IsImpactTime V S z t) ↔ a.state ∈ V.noImpactSet a.edge Δ
  have himp : ∀ t, 0 ≤ t → (IsImpactTime V S z t ↔ t ∈ impactTimes S a) :=
    fun t ht => isImpactTime_iff_of_nonneg V S z ht
  have hphys : a.state.1 ∈ Icc (0 : ℝ) (Γ.length a.edge) := by
    have h := flightCurve_physical V a le_rfl (fun hbdd => (impactDuration_pos_of_bddAbove
      (V := V) a hbdd).le)
    rwa [flightCurve_zero] at h
  have h0mem : (a.state.1 = 0 ∨ a.state.1 = Γ.length a.edge) → (0 : ℝ) ∈ impactTimes S a :=
    fun h => ⟨0, by rw [iterate_zero]; rfl, impactReal_zero V S a, Or.inr h⟩
  have hiter1 : iterate V S a 1 = next V S a := by
    rw [iterate_succ, iterate_zero, Option.bind_some]
  constructor
  · intro hno
    -- no impact at time `0`: the representative is interior
    have hint : a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge) := by
      refine ⟨lt_of_le_of_ne hphys.1 ?_, lt_of_le_of_ne hphys.2 ?_⟩
      · intro h0
        exact hno 0 ⟨le_rfl, hΔ⟩ ((himp 0 le_rfl).mpr (h0mem (Or.inl h0.symm)))
      · intro h0
        exact hno 0 ⟨le_rfl, hΔ⟩ ((himp 0 le_rfl).mpr (h0mem (Or.inr h0)))
    refine ⟨⟨hint, a.regular⟩, fun hbdd => ?_⟩
    -- the first impact happens after `Δ`
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨b, hb, -⟩ := next_eq_some_of_bddAbove (V := V) S a hbdd
    have hsome : (iterate V S a (0 + 1)).isSome := by
      rw [zero_add, hiter1, hb]; rfl
    have hir := impactReal_succ_eq_of_isSome (V := V) (iterate_zero (V := V) S a) hsome
    rw [impactReal_zero, zero_add, zero_add] at hir
    have hpos := impactDuration_pos_of_bddAbove (V := V) a hbdd
    refine hno (sSup (durationSet V a.edge a.state)) ⟨hpos.le, hle⟩ ((himp _ hpos.le).mpr ?_)
    exact ⟨1, by simpa using hsome, hir, Or.inl one_pos⟩
  · rintro ⟨⟨hint, -⟩, hsurv⟩ t ht himpt
    obtain ⟨n, hn, hnt, hcond⟩ := (himp t ht.1).mp himpt
    have hnpos : 0 < n := by
      rcases hcond with h | h | h
      · exact h
      · exact absurd h (ne_of_gt hint.1)
      · exact absurd h (ne_of_lt hint.2)
    have h1 : (iterate V S a (0 + 1)).isSome := iterate_isSome_of_le (V := V) hnpos hn
    have hbdd : BddAbove (durationSet V a.edge a.state) := by
      apply bddAbove_of_next_isSome (S := S)
      rw [← hiter1]; exact h1
    have hir := impactReal_succ_eq_of_isSome (V := V) (iterate_zero (V := V) S a) h1
    rw [impactReal_zero, zero_add, zero_add] at hir
    have hle : impactReal V S a 1 ≤ impactReal V S a n := by
      rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hnpos.ne') with h | h
      · rw [h]
      · exact (impactReal_strictMonoOn_of_isSome (V := V) hn h).le
    have := hsurv hbdd
    linarith [ht.2]

/-- The no-impact set is the union over the edges of the no-impact strata of `ShortTime.lean`. -/
theorem noImpactWindow_eq_iUnion (K : Set ℝ) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    V.noImpactWindow S K Δ = ⋃ e : Γ.Edge, V.noImpactPiece S e K Δ := by
  ext z
  simp only [noImpactWindow, mem_setOf_eq, mem_iUnion, noImpactPiece,
    V.noImpact_iff_mem_noImpactSet S z hΔ]
  constructor
  · rintro ⟨hK, h⟩
    exact ⟨_, hK, rfl, h⟩
  · rintro ⟨e, hK, rfl, h⟩
    exact ⟨hK, h⟩

/-! ### The at-most-one-impact set is all of `E_K` -/

/-- For `0 ≤ Δ < τ_K` no trajectory in `E_K` has two vertex impacts in `[0, Δ]`. -/
theorem atMostOneImpactWindow_eq {K : Set ℝ} {τ : ℝ} (hτ : V.IsImpactSeparationConstant S K τ)
    {Δ : ℝ} (hΔτ : Δ < τ) : V.atMostOneImpactWindow S K Δ = V.energySector S K := by
  ext z
  refine ⟨fun hz => hz.1, fun hz => ⟨hz, ?_⟩⟩
  rintro t ⟨ht, ht0, htΔ⟩ t' ⟨ht', ht'0, ht'Δ⟩
  by_contra hne
  have h := hτ.2 z hz t t' ht ht' hne
  have : |t - t'| ≤ Δ := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  linarith

/-- For `0 ≤ Δ < τ_K` the one-impact set is the complement of the no-impact set in `E_K`. -/
theorem oneImpactWindow_eq {K : Set ℝ} {τ : ℝ} (hτ : V.IsImpactSeparationConstant S K τ)
    {Δ : ℝ} (hΔτ : Δ < τ) :
    V.oneImpactWindow S K Δ = V.energySector S K \ V.noImpactWindow S K Δ := by
  ext z
  constructor
  · rintro ⟨hz, t, ⟨ht, himp⟩, -⟩
    exact ⟨hz, fun hno => hno.2 t ht himp⟩
  · rintro ⟨hz, hno⟩
    have hex : ∃ t ∈ Icc (0 : ℝ) Δ, IsImpactTime V S z t := by
      by_contra h
      push Not at h
      exact hno ⟨hz, h⟩
    obtain ⟨t, ht, himp⟩ := hex
    have hsub := (V.atMostOneImpactWindow_eq S hτ hΔτ ▸ hz : z ∈ V.atMostOneImpactWindow S K Δ).2
    exact ⟨hz, t, ⟨ht, himp⟩, fun t' ht' => hsub ⟨ht'.2, ht'.1⟩ ⟨himp, ht⟩⟩

/-! ### Lemma VI.2 -/

/-- **Lemma VI.2 (short-time Borel structure).**  Let `K` be compact and disjoint from the vertex
values, let `τ_K` be a no-Zeno constant for `K` (Lemma V.2; one exists by
`exists_noZenoConstant`), and let `0 < Δ < τ_K`.  On `E_K = H⁻¹(K) ∩ P^Reg`:

* the no-impact set, the at-most-one-impact set and the one-impact set for `[0, Δ]` are
  measurable;
* the at-most-one-impact set is all of `E_K` (no trajectory in `E_K` has two impacts in `[0, Δ]`);
* on each of these three sets the short-time map `Φ_Δ` is measurable.

The measurability of `Φ_Δ` on the pieces is that of the restriction of the globally measurable
`Φ_Δ` (`measurable_flow`). -/
theorem short_time_borel {K : Set ℝ} (hK : IsCompact K)
    (_hKreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) {τ : ℝ} (hτ : V.IsImpactSeparationConstant S K τ)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔτ : Δ < τ) :
    MeasurableSet (V.noImpactWindow S K Δ) ∧
      MeasurableSet (V.atMostOneImpactWindow S K Δ) ∧
      MeasurableSet (V.oneImpactWindow S K Δ) ∧
      V.atMostOneImpactWindow S K Δ = V.energySector S K ∧
      Measurable ((V.noImpactWindow S K Δ).restrict fun z => flow V S z Δ) ∧
      Measurable ((V.atMostOneImpactWindow S K Δ).restrict fun z => flow V S z Δ) ∧
      Measurable ((V.oneImpactWindow S K Δ).restrict fun z => flow V S z Δ) := by
  have hKm : MeasurableSet K := hK.measurableSet
  have hN : MeasurableSet (V.noImpactWindow S K Δ) := by
    rw [V.noImpactWindow_eq_iUnion S K hΔ.le]
    exact MeasurableSet.iUnion fun e => V.measurableSet_noImpactPiece S e hKm hΔ
  have hEK : MeasurableSet (V.energySector S K) := V.measurableSet_energySector S hKm
  have hflow : Measurable fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z Δ :=
    V.measurable_flow S Δ
  refine ⟨hN, ?_, ?_, V.atMostOneImpactWindow_eq S hτ hΔτ, hflow.comp measurable_subtype_coe,
    hflow.comp measurable_subtype_coe, hflow.comp measurable_subtype_coe⟩
  · rw [V.atMostOneImpactWindow_eq S hτ hΔτ]; exact hEK
  · rw [V.oneImpactWindow_eq S hτ hΔτ]; exact hEK.diff hN

/-! ### Lemma VI.3 -/

/-- The energy window is invariant: `Φ_t⁻¹ A ∩ E_K = Φ_t⁻¹ (A ∩ E_K)`. -/
theorem preimage_flow_inter_energySector (K : Set ℝ) (t : ℝ)
    (A : Set (RegularScatteringPhaseSpace (V := V) S)) :
    (fun z => flow V S z t) ⁻¹' A ∩ V.energySector S K =
      (fun z => flow V S z t) ⁻¹' (A ∩ V.energySector S K) := by
  ext z
  simp only [mem_inter_iff, mem_preimage, energySector, mem_setOf_eq, quotientHamiltonian_flow]

/-- The quotient Liouville measure is preserved by `Φ_t` on every energy sector `E_K`, for every
real `t` and every measurable `K`: a consequence of the global invariance `measure_preimage_flow`
and of energy conservation. -/
theorem measure_preimage_flow_inter_energySector {K : Set ℝ} (hK : MeasurableSet K) (t : ℝ)
    {A : Set (RegularScatteringPhaseSpace (V := V) S)} (hA : MeasurableSet A) :
    regularLiouville V S ((fun z => flow V S z t) ⁻¹' A ∩ V.energySector S K) =
      regularLiouville V S (A ∩ V.energySector S K) := by
  rw [V.preimage_flow_inter_energySector S K t A]
  exact V.measure_preimage_flow S t (hA.inter (V.measurableSet_energySector S hK))

/-- **Lemma VI.3 (one-impact Liouville invariance).**  Under the hypotheses of Lemma VI.2 —
`K` compact and disjoint from the vertex values, `τ_K` a no-Zeno constant for `K` and
`0 < Δ < τ_K` — the map `Φ_Δ` preserves `m` on `E_K`: for every measurable `A ⊆ P^Reg`,
`m(Φ_Δ⁻¹ A ∩ E_K) = m(A ∩ E_K)`; and equally on the at-most-one-impact set of Lemma VI.2, which
is `E_K`.

The proof derives the identity from the global invariance `measure_preimage_flow` (proved in
`ShortTime.lean` by a stratified short-time argument) and the invariance of `E_K` under the flow;
the identity holds for every `Δ` (`measure_preimage_flow_inter_energySector`), and the hypotheses
`0 < Δ < τ_K` are used only to identify the at-most-one-impact set with `E_K`. -/
theorem one_impact_measure {K : Set ℝ} (hK : IsCompact K)
    (_hKreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) {τ : ℝ} (hτ : V.IsImpactSeparationConstant S K τ)
    {Δ : ℝ} (_hΔ : 0 < Δ) (hΔτ : Δ < τ)
    {A : Set (RegularScatteringPhaseSpace (V := V) S)} (hA : MeasurableSet A) :
    regularLiouville V S ((fun z => flow V S z Δ) ⁻¹' A ∩ V.energySector S K) =
        regularLiouville V S (A ∩ V.energySector S K) ∧
      regularLiouville V S ((fun z => flow V S z Δ) ⁻¹' A ∩ V.atMostOneImpactWindow S K Δ) =
        regularLiouville V S (A ∩ V.atMostOneImpactWindow S K Δ) := by
  have h := V.measure_preimage_flow_inter_energySector S hK.measurableSet Δ hA
  rw [V.atMostOneImpactWindow_eq S hτ hΔτ]
  exact ⟨h, h⟩

/-! ### The paper's `τ_K`: Lemma V.2 for arbitrary scattered trajectories -/

/-- An impact time of `z` (the outgoing representative of `Φ_t z` sits at an edge end) is a vertex
impact of the orbit in the sense of eq. (impact): `Φ_t z = π(α)` for an incoming covector `α`. -/
theorem isVertexImpactClass_of_isImpactTime (z : RegularScatteringPhaseSpace (V := V) S) {t : ℝ}
    (h : IsImpactTime V S z t) : IsVertexImpactClass V S (flow V S z t).1 := by
  set w := flow V S z t with hw
  set A := repFlight V S w with hA
  have hb : A.state.1 = 0 ∨ A.state.1 = Γ.length A.edge := h
  have hout : A.IsOutgoing := by
    refine (FlightState.interior_or_isOutgoing A).resolve_left ?_
    rintro ⟨h1, h2⟩
    rcases hb with hb | hb <;> rw [hb] at h1 h2 <;> exact lt_irrefl _ (by assumption)
  obtain ⟨η₀, hη₀e, hq, hsign⟩ := hout
  have hp : A.state.2 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hsign; exact lt_irrefl _ hsign
  let β : Γ.OutgoingBoundary η₀.vertex := ⟨⟨η₀, A.state.2, hp⟩, rfl, hsign⟩
  refine ⟨η₀.vertex, (S.map η₀.vertex).symm β, ?_⟩
  rw [quotientMap_scatter V S, MeasurableEquiv.apply_symm_apply]
  have hpt : ((A.edge, A.state) : Γ.Edge × ℝ × ℝ) =
      (β.1.germ.1, FiniteMetricGraph.EdgeEnd.coordinate Γ β.1.germ, β.1.momentum) :=
    Prod.ext hη₀e.symm (Prod.ext hq rfl)
  rw [← graphClass_repFlight V S w, ← hA, graphClass, hpt, Γ.graphPoint_covector]

/-- **The no-Zeno constant of Lemma V.2 separates the impacts of the flow.**  A constant `τ_K`
in the sense of `IsNoZenoConstant` (no scattered trajectory with energy in `K` has two vertex
impacts less than `τ_K` apart; `no_zeno`) satisfies `IsImpactSeparationConstant`: the orbit
`t ↦ Φ_t z` is a scattered trajectory (`flow_isScatteredTrajectory`) and its impact times are
vertex impacts. -/
theorem IsNoZenoConstant.isImpactSeparationConstant {K : Set ℝ} {τ : ℝ}
    (hτ : IsNoZenoConstant V S K τ) : V.IsImpactSeparationConstant S K τ := by
  refine ⟨hτ.1, fun z hz t t' ht ht' hne => ?_⟩
  have h := hτ.2 z (flow V S z) (flow_isScatteredTrajectory V S z) hz t
    (V.isVertexImpactClass_of_isImpactTime S z ht) t'
    (V.isVertexImpactClass_of_isImpactTime S z ht') hne
  rwa [abs_sub_comm] at h

/-- **Lemma VI.2 with the paper's `τ_K`.**  As `short_time_borel`, with `τ_K` a no-Zeno constant
of Lemma V.2 (`IsNoZenoConstant`, provided by `no_zeno`). -/
theorem short_time_borel' {K : Set ℝ} (hK : IsCompact K)
    (hKreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) {τ : ℝ} (hτ : IsNoZenoConstant V S K τ)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔτ : Δ < τ) :
    MeasurableSet (V.noImpactWindow S K Δ) ∧
      MeasurableSet (V.atMostOneImpactWindow S K Δ) ∧
      MeasurableSet (V.oneImpactWindow S K Δ) ∧
      V.atMostOneImpactWindow S K Δ = V.energySector S K ∧
      Measurable ((V.noImpactWindow S K Δ).restrict fun z => flow V S z Δ) ∧
      Measurable ((V.atMostOneImpactWindow S K Δ).restrict fun z => flow V S z Δ) ∧
      Measurable ((V.oneImpactWindow S K Δ).restrict fun z => flow V S z Δ) :=
  V.short_time_borel S hK hKreg (hτ.isImpactSeparationConstant V S) hΔ hΔτ

/-- **Lemma VI.3 with the paper's `τ_K`.**  As `one_impact_measure`, with `τ_K` a no-Zeno
constant of Lemma V.2 (`IsNoZenoConstant`, provided by `no_zeno`). -/
theorem one_impact_measure' {K : Set ℝ} (hK : IsCompact K)
    (hKreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) {τ : ℝ} (hτ : IsNoZenoConstant V S K τ)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔτ : Δ < τ)
    {A : Set (RegularScatteringPhaseSpace (V := V) S)} (hA : MeasurableSet A) :
    regularLiouville V S ((fun z => flow V S z Δ) ⁻¹' A ∩ V.energySector S K) =
        regularLiouville V S (A ∩ V.energySector S K) ∧
      regularLiouville V S ((fun z => flow V S z Δ) ⁻¹' A ∩ V.atMostOneImpactWindow S K Δ) =
        regularLiouville V S (A ∩ V.atMostOneImpactWindow S K Δ) :=
  V.one_impact_measure S hK hKreg (hτ.isImpactSeparationConstant V S) hΔ hΔτ hA

end MechanicalPotential

end HamiltonianMetricGraphs
