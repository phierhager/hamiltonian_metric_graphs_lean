/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma V.3: local finiteness of impacts and the cardinal estimate `#(I ∩ [a,b]) ≤ 1 + (b-a)/τ`.
-/

import HamiltonianMetricGraphs.FlowGroup

/-!
# Local finiteness of impacts (Lemma V.3)

The forward no-Zeno estimate (`impactTime_eventually_gt`) says that the impact times of a
scattered chain do not accumulate.  Lemma V.3 of the paper is the quantitative, two-sided form:
distinct impact times of a trajectory at regular energy `E` are separated by at least the no-Zeno
constant `τ_E` of Lemma V.2, hence every compact time interval `[a, b]` contains at most
`1 + (b - a)/τ_E` of them.

For the two-sided flow `Φₜ` the impact set of `z` is `{t | Φₜ z is a vertex class}`.  The group law
`Φ_{α+s} = Φ_s ∘ Φ_α` translates its intersection with `[α, β]` to the forward impact set of
`Φ_α z` in `[0, β - α]`, so the estimate on the forward chain — an index count along the linearly
growing impact times — gives the paper's bound on every interval, in particular the backward
no-Zeno property.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set FlightState PhysicalEdgeSegment

variable {Γ : FiniteMetricGraph} {V : MechanicalPotential Γ}

namespace FlightState

variable (S : BorelEnergyPreservingScattering V)

/-- **The forward impact times** of a flight state: the onsets of its flights after a scattering
event, together with time `0` when the state itself sits at a vertex. -/
def impactTimes (a : V.FlightState) : Set ℝ :=
  {t | ∃ n : ℕ, (iterate V S a n).isSome ∧ impactReal V S a n = t ∧
    (0 < n ∨ a.state.1 = 0 ∨ a.state.1 = Γ.length a.edge)}

variable {S}

/-- The flight state at an impact index departs a vertex. -/
theorem isOutgoing_of_impactIndex {a b : V.FlightState} {n : ℕ} (hb : iterate V S a n = some b)
    (hn : 0 < n ∨ a.state.1 = 0 ∨ a.state.1 = Γ.length a.edge) : b.IsOutgoing := by
  cases n with
  | zero =>
      rw [iterate_zero] at hb
      rw [← Option.some.inj hb]
      rcases interior_or_isOutgoing a with hint | hout
      · exfalso
        rcases hn with h | h | h
        · exact lt_irrefl _ h
        · rw [h] at hint; exact lt_irrefl _ hint.1
        · rw [h] at hint; exact lt_irrefl _ hint.2
      · exact hout
  | succ m => exact isOutgoing_of_iterate_succ S hb

/-- The onset of an outgoing flight is followed by an impact at least `τ` later, when `τ` is the
uniform flight-duration bound at the energy of the chain. -/
theorem impactReal_add_le_succ {a : V.FlightState} {τ : ℝ}
    (hsep : ∀ b : V.FlightState, b.IsOutgoing → b.energy = a.energy →
      ∀ _ : BddAbove (durationSet V b.edge b.state), τ ≤ sSup (durationSet V b.edge b.state))
    {n : ℕ} {b : V.FlightState} (hb : iterate V S a n = some b) (hout : b.IsOutgoing)
    (hsucc : (iterate V S a (n + 1)).isSome) :
    impactReal V S a n + τ ≤ impactReal V S a (n + 1) := by
  have hbdd : BddAbove (durationSet V b.edge b.state) := by
    apply bddAbove_of_next_isSome (V := V) (S := S)
    rw [iterate_succ, hb] at hsucc
    exact hsucc
  rw [impactReal_succ_eq_of_isSome (V := V) hb hsucc]
  have := hsep b hout (iterate_energy_eq (V := V) n hb) hbdd
  linarith

/-- Linear growth of the impact times from an outgoing onset. -/
theorem impactReal_linear_ge {a : V.FlightState} {τ : ℝ}
    (hsep : ∀ b : V.FlightState, b.IsOutgoing → b.energy = a.energy →
      ∀ _ : BddAbove (durationSet V b.edge b.state), τ ≤ sSup (durationSet V b.edge b.state))
    {n₀ : ℕ} (hn₀ : 0 < n₀ ∨ a.state.1 = 0 ∨ a.state.1 = Γ.length a.edge) (k : ℕ)
    (hk : (iterate V S a (n₀ + k)).isSome) :
    impactReal V S a n₀ + k * τ ≤ impactReal V S a (n₀ + k) := by
  induction k with
  | zero => simp
  | succ j ih =>
      have hj : (iterate V S a (n₀ + j)).isSome :=
        iterate_isSome_of_le (V := V) (by omega) hk
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hj
      have hout : b.IsOutgoing := by
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · exact isOutgoing_of_impactIndex hb hn₀
        · exact isOutgoing_of_impactIndex hb (Or.inl (by omega))
      have hstep := impactReal_add_le_succ hsep hb hout
        (by rw [show n₀ + j + 1 = n₀ + (j + 1) by ring]; exact hk)
      have := ih hj
      rw [show n₀ + (j + 1) = n₀ + j + 1 by ring]
      push_cast
      linarith

/-- **Lemma V.3 on the forward chain.**  With `τ` the uniform flight-duration bound at the energy of
`a`, distinct impact times are separated by at least `τ`, and every interval `[α, β]` contains
finitely many of them, at most `1 + (β - α)/τ`. -/
theorem impactTimes_count [Nonempty Γ.Edge] (a : V.FlightState) {τ : ℝ} (hτ : 0 < τ)
    (hsep : ∀ b : V.FlightState, b.IsOutgoing → b.energy = a.energy →
      ∀ _ : BddAbove (durationSet V b.edge b.state), τ ≤ sSup (durationSet V b.edge b.state)) :
    (∀ t₁ ∈ impactTimes S a, ∀ t₂ ∈ impactTimes S a, t₁ < t₂ → τ ≤ t₂ - t₁) ∧
      ∀ α β : ℝ, α ≤ β → (impactTimes S a ∩ Icc α β).Finite ∧
        ((impactTimes S a ∩ Icc α β).ncard : ℝ) ≤ 1 + (β - α) / τ := by
  classical
  refine ⟨?_, ?_⟩
  · rintro t₁ ⟨n₁, h₁, rfl, hn₁⟩ t₂ ⟨n₂, h₂, rfl, hn₂⟩ hlt
    have hn : n₁ < n₂ := by
      by_contra h
      rw [not_lt] at h
      exact absurd hlt (not_lt.mpr (impactReal_monotone_of_isSome (V := V) h₁ h))
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h₁
    have hout : b.IsOutgoing := isOutgoing_of_impactIndex hb hn₁
    have hsucc : (iterate V S a (n₁ + 1)).isSome := iterate_isSome_of_le (V := V) hn h₂
    have h1 := impactReal_add_le_succ hsep hb hout hsucc
    have h2 := impactReal_monotone_of_isSome (V := V) h₂ (Nat.succ_le_of_lt hn)
    linarith
  · intro α β hαβ
    set J : Set ℕ := {n | (iterate V S a n).isSome ∧ impactReal V S a n ∈ Icc α β ∧
      (0 < n ∨ a.state.1 = 0 ∨ a.state.1 = Γ.length a.edge)} with hJ
    have himage : impactTimes S a ∩ Icc α β = (impactReal V S a) '' J := by
      ext t
      constructor
      · rintro ⟨⟨n, hn, rfl, hb⟩, ht⟩
        exact ⟨n, ⟨hn, ht, hb⟩, rfl⟩
      · rintro ⟨n, ⟨hn, ht, hb⟩, rfl⟩
        exact ⟨⟨n, hn, rfl, hb⟩, ht⟩
    have hdiv : (0 : ℝ) ≤ (β - α) / τ := div_nonneg (sub_nonneg.mpr hαβ) hτ.le
    by_cases hJne : ∃ n, n ∈ J
    · set n₀ := Nat.find hJne with hn₀def
      have hn₀ : n₀ ∈ J := Nat.find_spec hJne
      have hmin : ∀ n ∈ J, n₀ ≤ n := fun n hn => Nat.find_min' hJne hn
      set N : ℕ := ⌊(β - α) / τ⌋₊ with hN
      have hsub : J ⊆ ↑(Finset.Icc n₀ (n₀ + N)) := by
        intro n hn
        rw [Finset.coe_Icc, mem_Icc]
        refine ⟨hmin n hn, ?_⟩
        obtain ⟨k, rfl⟩ : ∃ k, n = n₀ + k := ⟨n - n₀, by have := hmin n hn; omega⟩
        have hlin := impactReal_linear_ge hsep hn₀.2.2 k hn.1
        have hkτ : (k : ℝ) * τ ≤ β - α := by
          have h1 := hn.2.1.2
          have h2 := hn₀.2.1.1
          linarith
        have hk : (k : ℝ) ≤ (β - α) / τ := by
          rw [le_div_iff₀ hτ]; exact hkτ
        have : k ≤ N := Nat.le_floor hk
        omega
      have hJfin : J.Finite := (Finset.finite_toSet _).subset hsub
      have hJcard : J.ncard ≤ N + 1 := by
        calc J.ncard ≤ (↑(Finset.Icc n₀ (n₀ + N)) : Set ℕ).ncard :=
              Set.ncard_le_ncard hsub (Finset.finite_toSet _)
          _ = N + 1 := by rw [Set.ncard_coe_finset, Nat.card_Icc]; omega
      refine ⟨by rw [himage]; exact hJfin.image _, ?_⟩
      rw [himage]
      have hle : ((impactReal V S a) '' J).ncard ≤ J.ncard := Set.ncard_image_le hJfin
      have hNle : (N : ℝ) ≤ (β - α) / τ := Nat.floor_le hdiv
      calc (((impactReal V S a) '' J).ncard : ℝ) ≤ (J.ncard : ℝ) := by exact_mod_cast hle
        _ ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast hJcard
        _ = (N : ℝ) + 1 := by push_cast; ring
        _ ≤ 1 + (β - α) / τ := by linarith
    · have hJempty : J = ∅ := by
        ext n; simp only [mem_empty_iff_false, iff_false]
        exact fun hn => hJne ⟨n, hn⟩
      rw [himage, hJempty, image_empty]
      exact ⟨finite_empty, by rw [Set.ncard_empty]; push_cast; linarith⟩

end FlightState

/-! ### Impact times of the two-sided flow -/

variable (V) (S : BorelEnergyPreservingScattering V) [Nonempty Γ.Edge]

/-- `t` is an **impact time** of the regular quotient point `z`: the flow sits at a vertex class at
time `t` (its outgoing representative is a boundary point). -/
def IsImpactTime (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ) : Prop :=
  (rep V S (flow V S z t).1).1.2.1.1 = 0 ∨
    (rep V S (flow V S z t).1).1.2.1.1 = Γ.length (rep V S (flow V S z t).1).1.1

/-- The impact set of the flow is translated by the group law. -/
theorem isImpactTime_flow (z : RegularScatteringPhaseSpace (V := V) S) (s t : ℝ) :
    IsImpactTime V S (flow V S z s) t ↔ IsImpactTime V S z (s + t) := by
  unfold IsImpactTime
  rw [flow_flow]

/-- For nonnegative times the impact times of `z` are the forward impact times of its
representative flight. -/
theorem isImpactTime_iff_of_nonneg (z : RegularScatteringPhaseSpace (V := V) S) {t : ℝ}
    (ht : 0 ≤ t) : IsImpactTime V S z t ↔ t ∈ impactTimes S (repFlight V S z) := by
  set a := repFlight V S z with ha
  have hrep : rep V S (flow V S z t).1 = Γ.graphPoint (trajectory V S a t) := by
    rw [flow_of_nonneg V S z ht, rep_forwardFlow]
  have hadm := trajectory_admissible S a t
  unfold IsImpactTime
  rw [hrep, Γ.graphPoint_val hadm]
  change (trajectory V S a t).2.1 = 0 ∨ (trajectory V S a t).2.1 =
    Γ.length (trajectory V S a t).1 ↔ _
  obtain ⟨n, hact⟩ := exists_activeAt V S a ht
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hact.1
  rw [trajectory_eq V S a ht hact hb]
  constructor
  · intro hbdry
    -- a boundary position forces the onset of the flight
    rcases eq_or_lt_of_le hact.2.1 with heq | hlt
    · refine ⟨n, hact.1, heq, ?_⟩
      cases n with
      | zero =>
          right
          rw [← heq, impactReal_zero, sub_zero, flightCurve_zero] at hbdry
          rw [iterate_zero] at hb
          rw [← Option.some.inj hb] at hbdry
          exact hbdry
      | succ m => exact Or.inl (Nat.succ_pos m)
    · exfalso
      have hint := flightCurve_interior V b (by linarith) (hact.elapsed_lt (V := V) hb hlt).2
      rcases hbdry with h | h
      · change (flightCurve V b (t - impactReal V S a n)).1 = 0 at h
        rw [h] at hint; exact lt_irrefl _ hint.1
      · change (flightCurve V b (t - impactReal V S a n)).1 = Γ.length b.edge at h
        rw [h] at hint; exact lt_irrefl _ hint.2
  · rintro ⟨m, hm, hmt, hcond⟩
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hm
    have hactm : ActiveAt V S a m t :=
      ⟨hm, hmt.le, fun hs => by rw [← hmt]; exact impactReal_lt_succ_of_isSome (V := V) hs⟩
    have hnm : n = m := activeAt_unique (V := V) hact hactm
    subst hnm
    have hbc : b = c := Option.some.inj (hb.symm.trans hc)
    subst hbc
    rw [← hmt, sub_self, flightCurve_zero]
    obtain ⟨η₀, hη₀, hstate, -⟩ := isOutgoing_of_impactIndex hc hcond
    rw [hstate]
    unfold FiniteMetricGraph.EdgeEnd.coordinate
    by_cases hη2 : η₀.2
    · rw [if_pos hη2, hη₀]; exact Or.inr rfl
    · rw [if_neg hη2]; exact Or.inl rfl

/-- **Lemma V.3.**  On a regular quotient point `z` of energy `E`, with `τ_E` the no-Zeno constant
of Lemma V.2 at `K = {E}`: the impact times of the two-sided flow are locally finite, and every
compact interval `[α, β]` contains at most `1 + (β - α)/τ_E` of them.  In particular impacts do not
accumulate in backward time either. -/
theorem impactSet_locally_finite (z : RegularScatteringPhaseSpace (V := V) S) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ α β : ℝ, α ≤ β →
      ({t | IsImpactTime V S z t} ∩ Icc α β).Finite ∧
        (({t | IsImpactTime V S z t} ∩ Icc α β).ncard : ℝ) ≤ 1 + (β - α) / τ := by
  classical
  set E := quotientHamiltonian (V := V) S z.1 with hE
  have hEreg : E ∉ V.exceptionalEnergies := z.2
  obtain ⟨τ, hτ, hsep⟩ := exists_uniform_impactDuration_lower_bound (V := V) {E}
    isCompact_singleton (by intro E' hE'; rw [mem_singleton_iff] at hE'; subst hE'; exact hEreg)
  refine ⟨τ, hτ, fun α β hαβ => ?_⟩
  -- translate to the forward chain of `Φ_α z`
  set a := repFlight V S (flow V S z α) with ha
  have haE : a.energy = E := by
    rw [ha, repFlight_energy, quotientHamiltonian_flow]
  have hsep' : ∀ b : V.FlightState, b.IsOutgoing → b.energy = a.energy →
      ∀ _ : BddAbove (durationSet V b.edge b.state), τ ≤ sSup (durationSet V b.edge b.state) :=
    fun b hout hb hbdd => hsep b hout (by rw [mem_singleton_iff, hb, haE]) hbdd
  obtain ⟨-, hcount⟩ := impactTimes_count (S := S) a hτ hsep'
  obtain ⟨hfin, hcard⟩ := hcount 0 (β - α) (by linarith)
  have hset : {t | IsImpactTime V S z t} ∩ Icc α β =
      (fun s => α + s) '' (impactTimes S a ∩ Icc 0 (β - α)) := by
    ext t
    simp only [mem_inter_iff, mem_setOf_eq, mem_Icc, mem_image]
    constructor
    · rintro ⟨himp, hαt, htβ⟩
      refine ⟨t - α, ⟨?_, by linarith, by linarith⟩, by ring⟩
      rw [← isImpactTime_iff_of_nonneg V S (flow V S z α) (by linarith), isImpactTime_flow,
        show α + (t - α) = t by ring]
      exact himp
    · rintro ⟨s, ⟨hs, hs0, hsβ⟩, rfl⟩
      refine ⟨?_, by linarith, by linarith⟩
      rw [← isImpactTime_flow, isImpactTime_iff_of_nonneg V S (flow V S z α) hs0]
      exact hs
  rw [hset, Set.ncard_image_of_injective _ (add_right_injective α)]
  exact ⟨hfin.image _, by simpa using hcard⟩

end MechanicalPotential

end HamiltonianMetricGraphs
