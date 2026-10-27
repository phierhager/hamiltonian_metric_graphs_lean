/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ThinLimitInitial
import HamiltonianMetricGraphs.GermTube

/-!
# Lemma IX.2: graph trajectories above the potential

This file proves Lemma IX.2 of the paper (`lem:graph-itinerary`) in full, as `graph_itinerary`.

Let `K` be a compact window above the potential, `K ⊂ (max_Γ V, ∞)` (`V.IsWindowAbove K`), and put

  `r_K = min_{E ∈ K, x ∈ Γ} √(2(E - V(x)))`,  `R_K = max_{E ∈ K, x ∈ Γ} √(2(E - V(x)))`

(`aboveMinSpeed`, `aboveMaxSpeed`; the points of `Γ` are the points of the closed edges).  Let
`z = (e, q, p)` with `0 < q < ℓ_e` and `E = H_e(q, p) ∈ K`, let `η₀` be the end of `e` with
`σ(η₀) p > 0`, and `η_{j+1} = \overline{F(η_j)}` (`F.itinerary η₀`).  Then the vertex impacts of
`t ↦ Φ_t(z)` are times `0 < τ₁ < τ₂ < ⋯`, `τ_{j+1} - τ_j ≥ ℓ_min / R_K` for `j ≥ 1`; on
`[τ_j, τ_{j+1}]` the trajectory is a flight on `e_j` with `σ(η_j) p(t) ≥ r_K`, landing at `η_j` at
`τ_{j+1}`, and for `j ≥ 1` it leaves `η̄_j = F(η_{j-1})` at `τ_j` from
`Y_j = (a_{η̄_j}, -σ(η̄_j) r_{η̄_j}(E))`, `r_η(E) = √(2(E - V(v(η))))` (`germSpeed`).

## Main statements

* `aboveMinSpeed V K = r_K`, `aboveMaxSpeed V K = R_K`, with `0 < r_K ≤ R_K`; both are attained
  (`isLeast_aboveMinSpeed`, `isGreatest_aboveMaxSpeed`, `exists_eq_aboveMinSpeed`,
  `exists_eq_aboveMaxSpeed`).
* `FlightState.flight_above` — one flight above the potential: it lands, at the end `η` towards
  which it moves, with `σ(η) p ≥ r_K`, `|p| ≤ R_K`, and landing state `(a_η, σ(η) r_η(E))`.
* `FlightState.iterate_isSome_of_isWindowAbove`, `FlightState.existsUnique_impact_index` — the
  impacts exist, and every `T ≥ 0` lies in exactly one `[τ_n, τ_{n+1})`.
* `FlightState.flowState_itinerary` — the flights of the flow follow `F.itinerary η₀`.
* `graph_itinerary` — Lemma IX.2.

## The proof

* **One flight** (`flight_above`).  Along a flight of energy `E ∈ K`,
  `|p| = √(2(E - V_e(q))) ∈ [r_K, R_K]`, so `p` never vanishes, keeps its sign (intermediate value
  theorem) and `σ(η) p ≥ r_K` for the end `η` towards which it initially moves.  The flight lands
  (`bddAbove_durationSet_of_isWindowAbove`: by the mean value theorem a flight of duration `d`
  travels at least `d √(2g)`), and since `σ(η) q` increases it lands at `η`
  (`eq_of_sign_mul_coordinate_sub_pos`), with momentum `σ(η) r_η(E)` by energy conservation.
* **The itinerary** (`flowState_itinerary`), by induction: `S^F` maps the landing covector at
  `η_j` to the outgoing covector at `F(η_j)` at the same speed, whose momentum
  `-σ(F(η_j)) r` points towards `\overline{F(η_j)} = η_{j+1}`.
* **The impact times** are those of the flow (`impactReal`), they exist for all `j`
  (`iterate_isSome_of_isWindowAbove`), and a full flight crosses an edge of length `≥ ℓ_min` at
  speed `≤ R_K`.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The speeds `r_K` and `R_K` -/

/-- The speeds `√(2(E - V(x)))`, `E ∈ K`, `x` a point of a closed edge of `Γ`. -/
def aboveSpeeds (K : Set ℝ) : Set ℝ :=
  {r | ∃ E ∈ K, ∃ e : Γ.Edge, ∃ q ∈ Icc (0 : ℝ) (Γ.length e),
    r = Real.sqrt (2 * (E - V.extension e q))}

/-- **`r_K = min_{E ∈ K, x ∈ Γ} √(2(E - V(x)))`.** -/
noncomputable def aboveMinSpeed (K : Set ℝ) : ℝ := sInf (V.aboveSpeeds K)

/-- **`R_K = max_{E ∈ K, x ∈ Γ} √(2(E - V(x)))`.** -/
noncomputable def aboveMaxSpeed (K : Set ℝ) : ℝ := sSup (V.aboveSpeeds K)

variable {V}

theorem aboveMinSpeed_le {K : Set ℝ} {E : ℝ} (hE : E ∈ K) (e : Γ.Edge) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) (Γ.length e)) :
    V.aboveMinSpeed K ≤ Real.sqrt (2 * (E - V.extension e q)) :=
  csInf_le ⟨0, by rintro r ⟨E, -, e, q, -, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨E, hE, e, q, hq, rfl⟩

theorem le_aboveMaxSpeed {K : Set ℝ} (hK : IsCompact K) (hwin : V.IsWindowAbove K) {E : ℝ}
    (hE : E ∈ K) (e : Γ.Edge) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (Γ.length e)) :
    Real.sqrt (2 * (E - V.extension e q)) ≤ V.aboveMaxSpeed K := by
  obtain ⟨g, Kmax, Vmin, -, hKmax, hV⟩ := V.exists_window_constants hK hwin
  refine le_csSup ⟨Real.sqrt (2 * (Kmax - Vmin)), ?_⟩ ⟨E, hE, e, q, hq, rfl⟩
  rintro r ⟨E', hE', e', q', hq', rfl⟩
  exact Real.sqrt_le_sqrt (by linarith [hKmax E' hE', (hV e' q' hq').1])

/-- `r_K > 0`. -/
theorem aboveMinSpeed_pos [Nonempty Γ.Edge] {K : Set ℝ} (hK : IsCompact K)
    (hwin : V.IsWindowAbove K) (hne : K.Nonempty) : 0 < V.aboveMinSpeed K := by
  obtain ⟨g, Kmax, Vmin, hg, -, hV⟩ := V.exists_window_constants hK hwin
  obtain ⟨E, hE⟩ := hne
  obtain ⟨e⟩ := ‹Nonempty Γ.Edge›
  have hpos : 0 < Real.sqrt (2 * g) := Real.sqrt_pos.mpr (by linarith)
  refine hpos.trans_le (le_csInf ⟨_, E, hE, e, 0, ⟨le_rfl, (Γ.length_pos e).le⟩, rfl⟩ ?_)
  rintro r ⟨E', hE', e', q', hq', rfl⟩
  exact Real.sqrt_le_sqrt (by linarith [(hV e' q' hq').2 E' hE'])

/-- `R_K > 0`. -/
theorem aboveMaxSpeed_pos [Nonempty Γ.Edge] {K : Set ℝ} (hK : IsCompact K)
    (hwin : V.IsWindowAbove K) (hne : K.Nonempty) : 0 < V.aboveMaxSpeed K := by
  obtain ⟨E, hE⟩ := hne
  obtain ⟨e⟩ := ‹Nonempty Γ.Edge›
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (Γ.length e) := ⟨le_rfl, (Γ.length_pos e).le⟩
  exact (aboveMinSpeed_pos hK hwin ⟨E, hE⟩).trans_le
    ((aboveMinSpeed_le hE e h0).trans (le_aboveMaxSpeed hK hwin hE e h0))

/-- The speeds `√(2(E - V(x)))`, `E ∈ K`, `x ∈ Γ`, form a compact set. -/
theorem isCompact_aboveSpeeds {K : Set ℝ} (hK : IsCompact K) : IsCompact (V.aboveSpeeds K) := by
  have hset : V.aboveSpeeds K = ⋃ e : Γ.Edge,
      (fun x : ℝ × ℝ => Real.sqrt (2 * (x.1 - V.extension e x.2))) ''
        (K ×ˢ Icc (0 : ℝ) (Γ.length e)) := by
    ext r
    simp only [aboveSpeeds, mem_setOf_eq, mem_iUnion, mem_image, mem_prod, Prod.exists]
    constructor
    · rintro ⟨E, hE, e, q, hq, rfl⟩
      exact ⟨e, E, q, ⟨hE, hq⟩, rfl⟩
    · rintro ⟨e, E, q, ⟨hE, hq⟩, rfl⟩
      exact ⟨E, hE, e, q, hq, rfl⟩
  rw [hset]
  refine isCompact_iUnion fun e => (hK.prod isCompact_Icc).image_of_continuousOn ?_
  have hcont : ContinuousOn (V.extension e) (Icc (0 : ℝ) (Γ.length e)) :=
    (V.contDiffOn_extension e).continuousOn.mono (V.closedEdge_subset_domain e)
  refine Real.continuous_sqrt.comp_continuousOn
    (continuousOn_const.mul (continuousOn_fst.sub ?_))
  exact hcont.comp continuousOn_snd fun x hx => hx.2

/-- The speed set is nonempty if `K` is nonempty and `Γ` has an edge. -/
theorem aboveSpeeds_nonempty [Nonempty Γ.Edge] {K : Set ℝ} (hne : K.Nonempty) :
    (V.aboveSpeeds K).Nonempty := by
  obtain ⟨E, hE⟩ := hne
  obtain ⟨e⟩ := ‹Nonempty Γ.Edge›
  exact ⟨_, E, hE, e, 0, ⟨le_rfl, (Γ.length_pos e).le⟩, rfl⟩

/-- **`r_K` is a minimum**: the least element of the speeds `√(2(E - V(x)))`. -/
theorem isLeast_aboveMinSpeed [Nonempty Γ.Edge] {K : Set ℝ} (hK : IsCompact K)
    (hne : K.Nonempty) : IsLeast (V.aboveSpeeds K) (V.aboveMinSpeed K) :=
  (isCompact_aboveSpeeds hK).isLeast_sInf (aboveSpeeds_nonempty hne)

/-- **`R_K` is a maximum**: the greatest element of the speeds `√(2(E - V(x)))`. -/
theorem isGreatest_aboveMaxSpeed [Nonempty Γ.Edge] {K : Set ℝ} (hK : IsCompact K)
    (hne : K.Nonempty) : IsGreatest (V.aboveSpeeds K) (V.aboveMaxSpeed K) :=
  (isCompact_aboveSpeeds hK).isGreatest_sSup (aboveSpeeds_nonempty hne)

/-- **`r_K = min_{E ∈ K, x ∈ Γ} √(2(E - V(x)))` is attained.** -/
theorem exists_eq_aboveMinSpeed [Nonempty Γ.Edge] {K : Set ℝ} (hK : IsCompact K)
    (hne : K.Nonempty) :
    ∃ E ∈ K, ∃ e : Γ.Edge, ∃ q ∈ Icc (0 : ℝ) (Γ.length e),
      V.aboveMinSpeed K = Real.sqrt (2 * (E - V.extension e q)) :=
  (isLeast_aboveMinSpeed hK hne).1

/-- **`R_K = max_{E ∈ K, x ∈ Γ} √(2(E - V(x)))` is attained.** -/
theorem exists_eq_aboveMaxSpeed [Nonempty Γ.Edge] {K : Set ℝ} (hK : IsCompact K)
    (hne : K.Nonempty) :
    ∃ E ∈ K, ∃ e : Γ.Edge, ∃ q ∈ Icc (0 : ℝ) (Γ.length e),
      V.aboveMaxSpeed K = Real.sqrt (2 * (E - V.extension e q)) :=
  (isGreatest_aboveMaxSpeed hK hne).1

namespace FlightState

/-! ### One flight above the potential -/

/-- **Every flight above the potential lands.**  If the energy of the flight state `b` lies in a
window `K ⊂ (max_Γ V, ∞)`, its duration set is bounded: on a flight of duration `d`,
`p² = 2(E - V_e(q)) ≥ 2g > 0`, so by the mean value theorem `d √(2g) ≤ |q(d) - q(0)| ≤ ℓ_e`. -/
theorem bddAbove_durationSet_of_isWindowAbove {K : Set ℝ} (hwin : V.IsWindowAbove K)
    (b : V.FlightState) (hb : b.energy ∈ K) :
    BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
  obtain ⟨g, Kmax, Vmin, hg, -, hV⟩ :=
    V.exists_window_constants (isCompact_singleton (x := b.energy))
      (hwin.mono (singleton_subset_iff.mpr hb))
  set c : ℝ := Real.sqrt (2 * g) with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr (by linarith)
  refine ⟨Γ.length b.edge / c, ?_⟩
  rintro d ⟨h, rfl⟩
  have hd := h.duration_pos
  set Q : ℝ → ℝ := fun t => (h.curve t).1 with hQ
  set P : ℝ → ℝ := fun t => (h.curve t).2 with hP
  -- the speed is at least `c` along the whole flight
  have hspeed : ∀ t ∈ Icc (0 : ℝ) h.duration, c ≤ |P t| := by
    intro t ht
    have hen := h.hamiltonian_eq_initial_at t ht
    have hq := h.physical_at t ht
    have hgap := (hV b.edge (Q t) hq).2 b.energy rfl
    have hE : V.hamiltonian b.edge b.state.1 b.state.2 = b.energy := rfl
    rw [hE, MechanicalPotential.hamiltonian] at hen
    have hP2 : 2 * g ≤ P t ^ 2 := by
      change 2 * g ≤ (h.curve t).2 ^ 2
      change V.extension b.edge (h.curve t).1 + g ≤ b.energy at hgap
      linarith
    rw [hc, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hP2
  -- the mean value theorem on `[0, d]`
  obtain ⟨s, hs, hslope⟩ := exists_hasDerivAt_eq_slope Q P hd
    ((continuous_fst.comp_continuousOn h.continuousOn_curve))
    (fun t ht => V.edgeIntegralCurve_hasDerivAt_fst (h.integralCurve t (Ioo_subset_Icc_self ht)))
  have hsp := hspeed s (Ioo_subset_Icc_self hs)
  rw [hslope, sub_zero, abs_div, abs_of_pos hd, le_div_iff₀ hd] at hsp
  have hQd := h.physical_at h.duration ⟨hd.le, le_rfl⟩
  have hQ0 := h.physical_at 0 ⟨le_rfl, hd.le⟩
  have hdiff : |Q h.duration - Q 0| ≤ Γ.length b.edge := by
    rw [abs_le]
    change -Γ.length b.edge ≤ (h.curve h.duration).1 - (h.curve 0).1 ∧
      (h.curve h.duration).1 - (h.curve 0).1 ≤ Γ.length b.edge
    constructor <;> linarith [hQd.1, hQd.2, hQ0.1, hQ0.2]
  rw [le_div_iff₀ hc0]
  linarith

/-- **The chain of the flow above the potential is infinite** (Lemma IX.2: the vertex impacts
form an infinite sequence `0 < τ₁ < τ₂ < ⋯`).  The scattering preserves the energy, so every
flight state of the chain has its energy in `K`, and every flight lands. -/
theorem iterate_isSome_of_isWindowAbove (S : BorelEnergyPreservingScattering V) {K : Set ℝ}
    (hwin : V.IsWindowAbove K) (a : V.FlightState) (ha : a.energy ∈ K) :
    ∀ j, (iterate V S a j).isSome := by
  intro j
  induction j with
  | zero => rw [iterate_zero]; rfl
  | succ j ih =>
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ih
      have hbE : b.energy ∈ K := by rw [iterate_energy_eq (V := V) j hb]; exact ha
      obtain ⟨c, hc, -⟩ :=
        next_eq_some_of_bddAbove (V := V) S b (bddAbove_durationSet_of_isWindowAbove hwin b hbE)
      rw [iterate_succ, hb]
      change (next V S b).isSome
      rw [hc]
      rfl

/-- **The impact index of a time.**  Above the potential, for every `T ≥ 0` there is exactly one
`n` with `τ_n ≤ T < τ_{n+1}`, `τ_j = impactReal V S a j` the vertex impact times of the flow. -/
theorem existsUnique_impact_index [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    {K : Set ℝ} (hwin : V.IsWindowAbove K) (a : V.FlightState) (ha : a.energy ∈ K) {T : ℝ}
    (hT : 0 ≤ T) :
    ∃! n : ℕ, impactReal V S a n ≤ T ∧ T < impactReal V S a (n + 1) := by
  have hchain := iterate_isSome_of_isWindowAbove S hwin a ha
  obtain ⟨n, hact⟩ := exists_activeAt V S a hT
  refine ⟨n, ⟨hact.2.1, hact.2.2 (hchain (n + 1))⟩, fun m hm => ?_⟩
  exact activeAt_unique (V := V) (activeAt_of_chain (V := V) hchain hm) hact

/-- Of the two ends of an edge, the one towards which `σ(η)(a_ζ - q₀) > 0` from a point `q₀` of
the closed edge is `η` itself. -/
theorem eq_of_sign_mul_coordinate_sub_pos {η ζ : Γ.EdgeEnd} (he : ζ.1 = η.1) {q₀ : ℝ}
    (hq₀ : q₀ ∈ Icc (0 : ℝ) (Γ.length η.1))
    (h : 0 < EdgeEnd.sign Γ η * (EdgeEnd.coordinate Γ ζ - q₀)) : ζ = η := by
  obtain ⟨h0, h1⟩ := hq₀
  rcases η with ⟨e, b⟩
  rcases ζ with ⟨e', b'⟩
  simp only at he
  subst he
  cases b <;> cases b' <;> simp at h h1 ⊢ <;> linarith

/-- **A flight above the potential** (the one-flight part of Lemma IX.2).  Let the flight state
`b` have energy `E ∈ K`, `K` a compact window above the potential, and let `η` be the end of its
edge towards which it initially moves, `σ(η) p > 0`.  Then the flight lands after the finite time
`D`; it lands at `η`; along it `σ(η) p(t) ≥ r_K` and `|p(t)| ≤ R_K`; it travels at most `R_K D`;
and its landing state is `(a_η, σ(η) r_η(E))`. -/
theorem flight_above [Nonempty Γ.Edge] {K : Set ℝ} (hK : IsCompact K)
    (hwin : V.IsWindowAbove K) (b : V.FlightState) (hb : b.energy ∈ K) {η : Γ.EdgeEnd}
    (hη : η.1 = b.edge) (hσ : 0 < EdgeEnd.sign Γ η * b.state.2) :
    BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state) ∧ b.arrivalGerm = η ∧
      (∀ t ∈ Icc (0 : ℝ) (sSup (PhysicalEdgeSegment.durationSet V b.edge b.state)),
        V.aboveMinSpeed K ≤ EdgeEnd.sign Γ η * (flightCurve V b t).2 ∧
        |(flightCurve V b t).2| ≤ V.aboveMaxSpeed K) ∧
      |(flightCurve V b (sSup (PhysicalEdgeSegment.durationSet V b.edge b.state))).1 - b.state.1|
        ≤ V.aboveMaxSpeed K * sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) ∧
      flightCurve V b (sSup (PhysicalEdgeSegment.durationSet V b.edge b.state)) =
        (EdgeEnd.coordinate Γ η, EdgeEnd.sign Γ η * V.germSpeed η b.energy) := by
  have hbdd := bddAbove_durationSet_of_isWindowAbove hwin b hb
  set D := sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) with hD
  have hD0 : 0 < D := impactDuration_pos_of_bddAbove V b hbdd
  have hDle : ∀ _ : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      D ≤ sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := fun _ => le_rfl
  have hr0 : 0 < V.aboveMinSpeed K := aboveMinSpeed_pos hK hwin ⟨_, hb⟩
  have hσabs : |EdgeEnd.sign Γ η| = 1 := RoutingLaw.edgeEnd_abs_sign η
  have hσσ : EdgeEnd.sign Γ η * EdgeEnd.sign Γ η = 1 := by
    rw [← abs_mul_abs_self, hσabs, one_mul]
  have hD0mem : (0 : ℝ) ∈ Icc (0 : ℝ) D := ⟨le_rfl, hD0.le⟩
  have hDmem : D ∈ Icc (0 : ℝ) D := ⟨hD0.le, le_rfl⟩
  -- the position stays on the closed edge, and `|p| = √(2(E - V_e(q)))`
  have hmem : ∀ t ∈ Icc (0 : ℝ) D, (flightCurve V b t).1 ∈ Icc (0 : ℝ) (Γ.length b.edge) :=
    fun t ht => flightCurve_physical V b ht.1 (fun _ => ht.2)
  have habs : ∀ t ∈ Icc (0 : ℝ) D, |(flightCurve V b t).2| =
      Real.sqrt (2 * (b.energy - V.extension b.edge (flightCurve V b t).1)) := by
    intro t ht
    have hen := flightCurve_hamiltonian_eq V b ht.1 (fun _ => ht.2)
    rw [MechanicalPotential.hamiltonian] at hen
    rw [← Real.sqrt_sq_eq_abs]
    congr 1
    linarith
  have hspeed : ∀ t ∈ Icc (0 : ℝ) D, V.aboveMinSpeed K ≤ |(flightCurve V b t).2| ∧
      |(flightCurve V b t).2| ≤ V.aboveMaxSpeed K := fun t ht => by
    rw [habs t ht]
    exact ⟨aboveMinSpeed_le hb _ (hmem t ht), le_aboveMaxSpeed hK hwin hb _ (hmem t ht)⟩
  -- the momentum keeps its sign
  have hcont : ContinuousOn (fun t => EdgeEnd.sign Γ η * (flightCurve V b t).2) (Icc 0 D) :=
    continuousOn_const.mul
      (continuous_snd.comp_continuousOn (flightCurve_continuousOn_Icc b hDle))
  have hpos : ∀ t ∈ Icc (0 : ℝ) D, 0 < EdgeEnd.sign Γ η * (flightCurve V b t).2 := by
    intro t ht
    by_contra hneg
    rw [not_lt] at hneg
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) D := Icc_subset_Icc le_rfl ht.2
    have h0 : (0 : ℝ) ∈ Icc (EdgeEnd.sign Γ η * (flightCurve V b t).2)
        (EdgeEnd.sign Γ η * (flightCurve V b 0).2) := by
      rw [flightCurve_zero]
      exact ⟨hneg, hσ.le⟩
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht.1 (hcont.mono hsub) h0
    have h1 := (hspeed s (hsub hs)).1
    have hz : (flightCurve V b s).2 = 0 := by
      rcases mul_eq_zero.mp hs0 with h | h
      · rw [h, abs_zero] at hσabs
        exact absurd hσabs zero_ne_one
      · exact h
    rw [hz, abs_zero] at h1
    linarith
  have hsignP : ∀ t ∈ Icc (0 : ℝ) D,
      EdgeEnd.sign Γ η * (flightCurve V b t).2 = |(flightCurve V b t).2| := fun t ht => by
    rw [← abs_of_pos (hpos t ht), abs_mul, hσabs, one_mul]
  -- the mean value theorem for the position
  have hderivQ : ∀ t ∈ Ioo (0 : ℝ) D,
      HasDerivAt (fun s => (flightCurve V b s).1) (flightCurve V b t).2 t := by
    intro t ht
    have h := (flightCurve_hasDerivWithinAt_Icc b hDle (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
    exact V.edgeIntegralCurve_hasDerivAt_fst h
  obtain ⟨s, hs, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => (flightCurve V b s).1)
    (fun s => (flightCurve V b s).2) hD0
    (continuous_fst.comp_continuousOn (flightCurve_continuousOn_Icc b hDle)) hderivQ
  have hdiff : (flightCurve V b D).1 - (flightCurve V b 0).1 = D * (flightCurve V b s).2 := by
    rw [hslope, sub_zero]
    field_simp
  have hsmem : s ∈ Icc (0 : ℝ) D := Ioo_subset_Icc_self hs
  have hmove : 0 < EdgeEnd.sign Γ η * ((flightCurve V b D).1 - (flightCurve V b 0).1) := by
    rw [hdiff, show EdgeEnd.sign Γ η * (D * (flightCurve V b s).2) =
      D * (EdgeEnd.sign Γ η * (flightCurve V b s).2) by ring]
    exact mul_pos hD0 (hpos s hsmem)
  -- the flight lands at `η`
  have hland := flightCurve_sSup_fst b hbdd
  rw [← hD] at hland
  have hgerm : b.arrivalGerm = η := by
    refine eq_of_sign_mul_coordinate_sub_pos (by rw [arrivalGerm_fst, hη])
      (q₀ := (flightCurve V b 0).1) (by rw [hη]; exact hmem 0 hD0mem) ?_
    rw [← hland]
    exact hmove
  refine ⟨hbdd, hgerm, fun t ht => ⟨?_, (hspeed t ht).2⟩, ?_, ?_⟩
  · rw [hsignP t ht]
    exact (hspeed t ht).1
  · rw [← flightCurve_zero V b, hdiff, abs_mul, abs_of_pos hD0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hspeed s hsmem).2 hD0.le
  · have hq : (flightCurve V b D).1 = EdgeEnd.coordinate Γ η := by rw [hland, hgerm]
    have hgs : V.germSpeed η b.energy = |(flightCurve V b D).2| := by
      rw [habs D hDmem, hq, ← hη, V.endpoint_value η, germSpeed_def]
    refine Prod.ext hq ?_
    change (flightCurve V b D).2 = EdgeEnd.sign Γ η * V.germSpeed η b.energy
    rw [hgs, ← hsignP D hDmem, ← mul_assoc, hσσ, one_mul]

/-! ### The itinerary of the flow -/

/-- **The flights of the flow follow the graph itinerary.**  Above the potential, flight `j` of
the flow through `a` (`flowState`) runs on the edge of `η_j = F.itinerary η₀ j`, moves towards
`η_j`, keeps the energy of `a`, and for `j ≥ 1` starts from the departure state
`Y_j = (a_{η̄_j}, -σ(η̄_j) r_{η̄_j}(E))`. -/
theorem flowState_itinerary [Nonempty Γ.Edge] (F : RoutingLaw Γ) {K : Set ℝ} (hK : IsCompact K)
    (hwin : V.IsWindowAbove K) (a : V.FlightState) (ha : a.energy ∈ K) {η₀ : Γ.EdgeEnd}
    (hη₀ : η₀.1 = a.edge) (hσ : 0 < EdgeEnd.sign Γ η₀ * a.state.2) (j : ℕ) :
    (flowState (F.toBorelScattering V) a j).edge = (F.itinerary η₀ j).1 ∧
      0 < EdgeEnd.sign Γ (F.itinerary η₀ j) * (flowState (F.toBorelScattering V) a j).state.2 ∧
      (flowState (F.toBorelScattering V) a j).energy = a.energy ∧
      (0 < j → (flowState (F.toBorelScattering V) a j).state =
        (EdgeEnd.coordinate Γ (otherEnd (F.itinerary η₀ j)),
          -EdgeEnd.sign Γ (otherEnd (F.itinerary η₀ j)) *
            V.germSpeed (otherEnd (F.itinerary η₀ j)) a.energy)) := by
  set S := F.toBorelScattering V with hS
  have hchain := iterate_isSome_of_isWindowAbove S hwin a ha
  induction j with
  | zero =>
      rw [flowState_zero, RoutingLaw.itinerary_zero]
      exact ⟨hη₀.symm, hσ, rfl, fun h => absurd h (lt_irrefl 0)⟩
  | succ j ih =>
      obtain ⟨hedge, hsign, hen, -⟩ := ih
      set b := flowState S a j with hb
      set η := F.itinerary η₀ j with hηdef
      set ζ := F.routeGerm η with hζ
      have hbK : b.energy ∈ K := by rw [hen]; exact ha
      obtain ⟨-, hgerm, -, -, hlandst⟩ := flight_above hK hwin b hbK hedge.symm hsign
      obtain ⟨hedge', hstate'⟩ := flowState_succ_routing F (hchain (j + 1))
      rw [← hS, ← hb, hgerm, ← hζ] at hedge' hstate'
      have hland : flightCurve V b (flowDur S a j) =
          (EdgeEnd.coordinate Γ η, EdgeEnd.sign Γ η * V.germSpeed η b.energy) := hlandst
      rw [hland] at hstate'
      have hitin : F.itinerary η₀ (j + 1) = otherEnd ζ := RoutingLaw.itinerary_succ F η₀ j
      have hother : otherEnd (F.itinerary η₀ (j + 1)) = ζ := by rw [hitin, otherEnd_otherEnd]
      have hen' : (flowState S a (j + 1)).energy = a.energy :=
        iterate_energy_eq (V := V) (j + 1) (iterate_eq_flowState (hchain (j + 1)))
      -- the speed at the vertex
      have hgs : V.germSpeed ζ a.energy = V.germSpeed η a.energy := by
        rw [germSpeed_def, germSpeed_def, hζ, RoutingLaw.routeGerm_vertex]
      have hgpos : 0 < V.germSpeed η a.energy := by
        rw [germSpeed_def]
        exact Real.sqrt_pos.mpr (by linarith [(hwin _ ha).1 (EdgeEnd.vertex Γ η)])
      have hσσ : EdgeEnd.sign Γ η * EdgeEnd.sign Γ η = 1 := by
        rw [← abs_mul_abs_self, RoutingLaw.edgeEnd_abs_sign, one_mul]
      have hσζ : EdgeEnd.sign Γ ζ * EdgeEnd.sign Γ ζ = 1 := by
        rw [← abs_mul_abs_self, RoutingLaw.edgeEnd_abs_sign, one_mul]
      have hstY : (flowState S a (j + 1)).state =
          (EdgeEnd.coordinate Γ ζ, -EdgeEnd.sign Γ ζ * V.germSpeed ζ a.energy) := by
        rw [hstate', RoutingLaw.departureMomentum, hen, abs_mul, RoutingLaw.edgeEnd_abs_sign,
          one_mul, abs_of_pos hgpos, hgs]
      refine ⟨by rw [hedge', hitin, otherEnd_fst], ?_, hen', fun _ => by rw [hother]; exact hstY⟩
      rw [hstY, hitin, sign_otherEnd]
      simp only
      rw [show -EdgeEnd.sign Γ ζ * (-EdgeEnd.sign Γ ζ * V.germSpeed ζ a.energy) =
        (EdgeEnd.sign Γ ζ * EdgeEnd.sign Γ ζ) * V.germSpeed ζ a.energy by ring, hσζ, one_mul, hgs]
      exact hgpos

end FlightState

end MechanicalPotential

/-! ### Lemma IX.2 -/

variable {Γ : FiniteMetricGraph}

/-- **Graph trajectories above the potential, Lemma IX.2 of the paper (`lem:graph-itinerary`).**

Let `K` be a compact window above the potential, `z = (e, q, p)` with `0 < q < ℓ_e` and
`E = H_e(q, p) ∈ K`, and `η₀` the end of `e` with `σ(η₀) p > 0`.  Let `a` be the flight state at
`z` (`FlightState.ofInterior`), `Φ_t(z) = FlightState.trajectory V (F.toBorelScattering V) a t`
the flow of Theorem III.6 for `S^F`, `τ_j = impactReal V S a j` its vertex impact times
(`τ₀ = 0`), and `η_j = F.itinerary η₀ j` (`η_{j+1} = \overline{F(η_j)}`), `e_j = η_j.1`.  Then:

* the vertex impacts exist for all `j` and `0 = τ₀ < τ₁ < τ₂ < ⋯`, and `r_K > 0`;
* `τ_{j+1} - τ_j ≥ ℓ_min / R_K` for `j ≥ 1`;
* on `[τ_j, τ_{j+1}]` the trajectory is a flight `ψ_j` on `e_j`: `Φ_t(z) = (e_j, ψ_j(t))` for
  `τ_j ≤ t < τ_{j+1}`, `ψ_j` solves the edge equations on `[τ_j, τ_{j+1}]`, it stays on the closed
  edge, strictly inside it for `τ_j < t < τ_{j+1}` (so the vertex impacts of `Φ_t(z)`, `t > 0`,
  are exactly the `τ_j`, `j ≥ 1`), and `σ(η_j) p(t) ≥ r_K`;
* it lands at `η_j` at the time `τ_{j+1}`: `ψ_j(τ_{j+1}) = (a_{η_j}, σ(η_j) r_{η_j}(E))`;
* for `j ≥ 1` it leaves the end `η̄_j = F(η_{j-1})` at the time `τ_j` from the departure state
  `Y_j = (a_{η̄_j}, -σ(η̄_j) r_{η̄_j}(E))`.

Here `r_K = aboveMinSpeed V K`, `R_K = aboveMaxSpeed V K`, `ℓ_min = minEdgeLen Γ e` (the minimum of
the edge lengths) and `r_η(E) = germSpeed V η E = √(2(E - V(v(η))))`. -/
theorem graph_itinerary [Nonempty Γ.Edge] (V : MechanicalPotential Γ) (F : RoutingLaw Γ)
    {K : Set ℝ} (hK : IsCompact K) (hwin : V.IsWindowAbove K) {e : Γ.Edge} {z : ℝ × ℝ}
    (hz : z.1 ∈ Ioo (0 : ℝ) (Γ.length e)) (hE : V.hamiltonian e z.1 z.2 ∈ K)
    {η₀ : Γ.EdgeEnd} (hη₀ : η₀.1 = e) (hσ : 0 < EdgeEnd.sign Γ η₀ * z.2) :
    let a : V.FlightState :=
      FlightState.ofInterior (V := V) hz (hwin.not_mem_exceptionalEnergies _ hE)
    let τ : ℕ → ℝ := FlightState.impactReal V (F.toBorelScattering V) a
    let η : ℕ → Γ.EdgeEnd := F.itinerary η₀
    (∀ j, (FlightState.iterate V (F.toBorelScattering V) a j).isSome) ∧ τ 0 = 0 ∧
      StrictMono τ ∧ 0 < V.aboveMinSpeed K ∧
      (∀ j, 1 ≤ j → minEdgeLen Γ e / V.aboveMaxSpeed K ≤ τ (j + 1) - τ j) ∧
      ∃ ψ : ℕ → ℝ → ℝ × ℝ, ∀ j,
        (∀ t ∈ Ico (τ j) (τ (j + 1)),
          FlightState.trajectory V (F.toBorelScattering V) a t = ((η j).1, ψ j t)) ∧
        (∀ t ∈ Ioo (τ j) (τ (j + 1)), (ψ j t).1 ∈ Ioo (0 : ℝ) (Γ.length (η j).1)) ∧
        (∀ t ∈ Icc (τ j) (τ (j + 1)),
          HasDerivWithinAt (ψ j) (V.edgeVectorField (η j).1 (ψ j t)) (Icc (τ j) (τ (j + 1))) t ∧
          (ψ j t).1 ∈ Icc (0 : ℝ) (Γ.length (η j).1) ∧
          V.aboveMinSpeed K ≤ EdgeEnd.sign Γ (η j) * (ψ j t).2) ∧
        ψ j (τ (j + 1)) =
          (EdgeEnd.coordinate Γ (η j),
            EdgeEnd.sign Γ (η j) * V.germSpeed (η j) (V.hamiltonian e z.1 z.2)) ∧
        (1 ≤ j → otherEnd (η j) = F.routeGerm (η (j - 1)) ∧
          ψ j (τ j) = (EdgeEnd.coordinate Γ (otherEnd (η j)),
            -EdgeEnd.sign Γ (otherEnd (η j)) *
              V.germSpeed (otherEnd (η j)) (V.hamiltonian e z.1 z.2))) := by
  intro a τ η
  set S := F.toBorelScattering V with hS
  have ha : a.energy ∈ K := hE
  have hchain := FlightState.iterate_isSome_of_isWindowAbove S hwin a ha
  have hit := FlightState.flowState_itinerary F hK hwin a ha (η₀ := η₀) hη₀ hσ
  have hEa : a.energy = V.hamiltonian e z.1 z.2 := rfl
  -- the flight `j` of the flow
  have hfl : ∀ j, _ := fun j =>
    FlightState.flight_above hK hwin (FlightState.flowState S a j)
      (by rw [(hit j).2.2.1]; exact ha) (hit j).1.symm (hit j).2.1
  have hdur : ∀ j, τ (j + 1) = τ j + FlightState.flowDur S a j := fun j =>
    FlightState.impactReal_succ_flow (hchain (j + 1))
  have hτ0 : ∀ j, 0 ≤ τ j := fun j =>
    FlightState.impactReal_nonneg_of_isSome (V := V) (hchain j)
  refine ⟨hchain, FlightState.impactReal_zero V S a,
    FlightState.impactReal_strictMono V S a hchain, aboveMinSpeed_pos hK hwin ⟨_, hE⟩,
    fun j hj => ?_, fun j t => FlightState.flightCurve V (FlightState.flowState S a j) (t - τ j),
    fun j => ?_⟩
  · -- a full flight crosses its edge at speed `≤ R_K`
    obtain ⟨-, -, -, htravel, hland⟩ := hfl j
    have hstart := (hit j).2.2.2 (by omega)
    have hR := aboveMaxSpeed_pos hK hwin ⟨_, hE⟩
    rw [hdur j, add_sub_cancel_left]
    change |(FlightState.flightCurve V (FlightState.flowState S a j)
      (FlightState.flowDur S a j)).1 - (FlightState.flowState S a j).state.1| ≤
        V.aboveMaxSpeed K * FlightState.flowDur S a j at htravel
    change FlightState.flightCurve V (FlightState.flowState S a j)
      (FlightState.flowDur S a j) = _ at hland
    rw [hland, hstart] at htravel
    simp only at htravel
    have hlen : Γ.length (η j).1 = |EdgeEnd.coordinate Γ (η j) -
        EdgeEnd.coordinate Γ (otherEnd (η j))| := by
      rw [coordinate_otherEnd]
      rcases hb : (η j).2 with _ | _
      · rw [coordinate_of_false hb]
        simp [abs_of_pos (Γ.length_pos _)]
      · rw [coordinate_of_true' hb]
        simp [abs_of_pos (Γ.length_pos _)]
    have hmin : minEdgeLen Γ e ≤ Γ.length (η j).1 := minEdgeLen_le Γ e _
    rw [div_le_iff₀ hR]
    change minEdgeLen Γ e ≤ FlightState.flowDur S a j * V.aboveMaxSpeed K
    linarith
  · obtain ⟨hedge, -, -, hdep⟩ := hit j
    obtain ⟨hbdd, -, hsp, -, hland⟩ := hfl j
    set b := FlightState.flowState S a j with hb
    have hD : FlightState.flowDur S a j =
        sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := rfl
    have hdj : τ (j + 1) - τ j = FlightState.flowDur S a j := by rw [hdur j]; ring
    have hDle : ∀ _ : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
        τ (j + 1) - τ j ≤ sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) :=
      fun _ => by rw [hdj, hD]
    have hshift : ∀ t ∈ Icc (τ j) (τ (j + 1)), t - τ j ∈
        Icc (0 : ℝ) (sSup (PhysicalEdgeSegment.durationSet V b.edge b.state)) := fun t ht =>
      ⟨by linarith [ht.1], by rw [← hD, ← hdj]; linarith [ht.2]⟩
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ⟨?_, ?_, ?_⟩, ?_, fun hj => ⟨?_, ?_⟩⟩
    · -- the trajectory is the flight `j` on `[τ_j, τ_{j+1})`
      have hact : FlightState.ActiveAt V S a j t :=
        FlightState.activeAt_of_chain (V := V) hchain ⟨ht.1, ht.2⟩
      rw [FlightState.trajectory_eq V S a ((hτ0 j).trans ht.1) hact
        (FlightState.iterate_eq_flowState (hchain j)), hedge]
    · rw [← hedge]
      exact FlightState.flightCurve_interior V b (by linarith [ht.1])
        (fun _ => by rw [← hD, ← hdj]; linarith [ht.2])
    · rw [← hedge]
      exact FlightState.hasDerivWithinAt_shift
        (FlightState.flightCurve_hasDerivWithinAt_Icc b hDle
          ⟨by linarith [ht.1], by linarith [ht.2]⟩) ht
    · rw [← hedge]
      exact FlightState.flightCurve_physical V b (hshift t ht).1 (fun _ => (hshift t ht).2)
    · exact (hsp _ (hshift t ht)).1
    · change FlightState.flightCurve V b (τ (j + 1) - τ j) = _
      rw [hdj, hD, hland, (hit j).2.2.1]
      rfl
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      change otherEnd (F.itinerary η₀ (i + 1)) = F.routeGerm (F.itinerary η₀ i)
      rw [RoutingLaw.itinerary_succ, otherEnd_otherEnd]
    · change FlightState.flightCurve V b (τ j - τ j) = _
      rw [sub_self, FlightState.flightCurve_zero, hdep (by omega), hEa]

end HamiltonianMetricGraphs
