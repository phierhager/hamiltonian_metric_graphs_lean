/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Trajectory

/-!
# The unified forward scattered trajectory

`Trajectory.forwardPhase` evolves an *infinite* scattered chain.  This module removes that
hypothesis, assembling the terminating (escaping) chains and the infinite ones into a single
forward trajectory defined for every `t ≥ 0`.

The organising notion is `FlightState.ActiveAt S a n t`: the flight state reached at step `n`
governs the trajectory at time `t`.  It requires that step `n` exists, that its onset
`impactReal n` has been reached, and that the *next* impact — **if there is one** — is still in the
future.  The conditional in the last clause is exactly what unifies the two cases:

* on an infinite chain every step has a successor, so `ActiveAt` reduces to the usual
  `impactReal n ≤ t < impactReal (n+1)`;
* on a terminating chain the last (escape) flight `N` has no successor, so its clause is vacuous
  and flight `N` governs the whole tail `[impactReal N, ∞)`.  This is correct precisely because an
  escaping flight has an unbounded duration set (`next_eq_none_iff`), so its `flightCurve` is the
  global `unboundedCurve`.

Existence of an active index is `exists_activeAt` (infinite case: the no-Zeno
`exists_forward_flightIndex`; terminating case: `exists_terminating_flightIndex`), and
`activeAt_unique` shows it is unique, using only finite-prefix monotonicity of the impact times —
no no-Zeno input.  Together they make `trajectory` well defined, and every property of
`forwardPhase` (initial value, energy conservation, physicality, the between-impacts Hamiltonian
ODE, the scattered impact rule) is re-established for it in full generality.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

namespace FlightState

/-- Finite-prefix monotonicity of the impact times: below any defined index the impact times are
monotone.  Unlike `impactReal_strictMono` this needs no no-Zeno hypothesis. -/
theorem impactReal_monotone_of_isSome {S : BorelEnergyPreservingScattering V} {a : V.FlightState}
    {m n : ℕ} (hn : (iterate V S a n).isSome) (hmn : m ≤ n) :
    impactReal V S a m ≤ impactReal V S a n := by
  rcases eq_or_lt_of_le hmn with rfl | hlt
  · exact le_rfl
  · exact (impactReal_strictMonoOn_of_isSome (V := V) hn hlt).le

/-- The impact times are nonnegative wherever they are defined. -/
theorem impactReal_nonneg_of_isSome {S : BorelEnergyPreservingScattering V} {a : V.FlightState}
    {n : ℕ} (hn : (iterate V S a n).isSome) : 0 ≤ impactReal V S a n := by
  have := impactReal_monotone_of_isSome (V := V) hn (Nat.zero_le n)
  rwa [impactReal_zero] at this

/-- **The active flight at a time.**  Step `n` of the chain governs the trajectory at time `t`
when it exists, its onset has passed, and the next impact — if the chain has one — has not yet
occurred.  On a terminating chain the final escape flight has no successor, so it governs the
entire tail; on an infinite chain this is the usual half-open impact interval. -/
def ActiveAt (S : BorelEnergyPreservingScattering V) (a : V.FlightState) (n : ℕ) (t : ℝ) : Prop :=
  (iterate V S a n).isSome ∧ impactReal V S a n ≤ t ∧
    ((iterate V S a (n + 1)).isSome → t < impactReal V S a (n + 1))

theorem ActiveAt.isSome {S : BorelEnergyPreservingScattering V} {a : V.FlightState} {n : ℕ}
    {t : ℝ} (h : ActiveAt V S a n t) : (iterate V S a n).isSome := h.1

/-- On an infinite chain, `ActiveAt` is exactly membership in the half-open impact interval. -/
theorem activeAt_of_chain {S : BorelEnergyPreservingScattering V} {a : V.FlightState}
    (hchain : ∀ n, (iterate V S a n).isSome) {n : ℕ} {t : ℝ}
    (hn : impactReal V S a n ≤ t ∧ t < impactReal V S a (n + 1)) : ActiveAt V S a n t :=
  ⟨hchain n, hn.1, fun _ => hn.2⟩

/-- **Existence of an active flight.**  Every nonnegative time is governed by some flight, whether
the chain is infinite (no-Zeno: impacts do not accumulate) or terminating (the escape flight covers
the tail). -/
theorem exists_activeAt [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) {t : ℝ} (ht : 0 ≤ t) : ∃ n : ℕ, ActiveAt V S a n t := by
  classical
  by_cases hchain : ∀ n, (iterate V S a n).isSome
  · obtain ⟨n, hn⟩ := exists_forward_flightIndex (V := V) S a hchain ht
    exact ⟨n, activeAt_of_chain (V := V) hchain hn⟩
  · -- The chain terminates: locate the escape flight and use the terminating flight index.
    rw [not_forall] at hchain
    obtain ⟨m, hm⟩ := hchain
    have hterm : ∃ n, iterate V S a n = none := ⟨m, Option.not_isSome_iff_eq_none.mp hm⟩
    obtain ⟨N, b, hbN, hbnext⟩ := exists_escape_of_terminates (V := V) hterm
    have hesc : iterate V S a (N + 1) = none :=
      iterate_succ_eq_none_of_next_eq_none (V := V) S a hbN hbnext
    obtain ⟨n, hnN, hnt, hlast⟩ := exists_terminating_flightIndex (V := V) S a hesc ht
    refine ⟨n, iterate_isSome_of_le (V := V) hnN (by rw [hbN]; rfl), hnt, ?_⟩
    · intro hsucc
      rcases hlast with rfl | hlt
      · -- `n = N` is the escape flight: it has no successor, so this case cannot occur.
        rw [hesc] at hsucc
        simp at hsucc
      · exact hlt

/-- **Uniqueness of the active flight.**  At most one flight governs a given time.  The proof only
uses finite-prefix monotonicity of the impact times, so it applies to terminating chains as well. -/
theorem activeAt_unique {S : BorelEnergyPreservingScattering V} {a : V.FlightState} {t : ℝ}
    {n m : ℕ} (hn : ActiveAt V S a n t) (hm : ActiveAt V S a m t) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · -- `n + 1 ≤ m`, so step `n+1` exists and `t < impactReal (n+1) ≤ impactReal m ≤ t`.
    have hsucc : (iterate V S a (n + 1)).isSome :=
      iterate_isSome_of_le (V := V) (Nat.succ_le_of_lt h) hm.1
    have hlt := hn.2.2 hsucc
    have hle := impactReal_monotone_of_isSome (V := V) hm.1 (Nat.succ_le_of_lt h)
    linarith [hm.2.1]
  · exact h
  · have hsucc : (iterate V S a (m + 1)).isSome :=
      iterate_isSome_of_le (V := V) (Nat.succ_le_of_lt h) hn.1
    have hlt := hm.2.2 hsucc
    have hle := impactReal_monotone_of_isSome (V := V) hn.1 (Nat.succ_le_of_lt h)
    linarith [hn.2.1]

/-- **The unified forward scattered trajectory.**  At every nonnegative time it evaluates the
curve of the unique active flight; before time zero it is pinned at the initial state.  No chain
hypothesis is needed: terminating chains are evolved by their escape flight's global no-hit curve
past the last impact. -/
noncomputable def trajectory [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (t : ℝ) : Γ.Edge × ℝ × ℝ :=
  if ht : 0 ≤ t then
    (fun n => ((iterate V S a n).map
        (fun b => (b.edge, flightCurve V b (t - impactReal V S a n)))).getD (a.edge, a.state))
      (Classical.choose (exists_activeAt V S a ht))
  else (a.edge, a.state)

/-- On its active interval the unified trajectory is exactly the active flight's curve. -/
theorem trajectory_eq [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) {t : ℝ} (ht : 0 ≤ t) {n : ℕ} (hn : ActiveAt V S a n t)
    {b : V.FlightState} (hb : iterate V S a n = some b) :
    trajectory V S a t = (b.edge, flightCurve V b (t - impactReal V S a n)) := by
  classical
  unfold trajectory
  rw [dif_pos ht]
  have hspec := Classical.choose_spec (exists_activeAt V S a ht)
  have hnn : Classical.choose (exists_activeAt V S a ht) = n := activeAt_unique (V := V) hspec hn
  simp only [hnn, hb, Option.map_some, Option.getD_some]

/-- The unified trajectory starts at the initial state. -/
@[simp] theorem trajectory_zero [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) : trajectory V S a 0 = (a.edge, a.state) := by
  have hact : ActiveAt V S a 0 0 := by
    refine ⟨by rw [iterate_zero]; rfl, by rw [impactReal_zero], fun hsucc => ?_⟩
    have := impactReal_lt_succ_of_isSome (V := V) (n := 0) hsucc
    rwa [impactReal_zero] at this
  rw [trajectory_eq V S a le_rfl hact (iterate_zero V S a), impactReal_zero, sub_zero,
    flightCurve_zero]

/-- The active flight's elapsed time is within its flight interval: nonnegative, and below the
flight's duration whenever that duration is finite. -/
theorem ActiveAt.elapsed_le {S : BorelEnergyPreservingScattering V} {a : V.FlightState} {n : ℕ}
    {t : ℝ} (hact : ActiveAt V S a n t) {b : V.FlightState} (hb : iterate V S a n = some b) :
    0 ≤ t - impactReal V S a n ∧
      ∀ _ : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
        t - impactReal V S a n ≤ sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
  refine ⟨by linarith [hact.2.1], fun hbdd => ?_⟩
  -- A bounded flight is not the escape flight, so its successor exists and bounds `t`.
  have hnext : (next V S b).isSome := by
    rw [Option.isSome_iff_ne_none]
    intro hnone
    exact ((next_eq_none_iff (V := V) S b).mp hnone) hbdd
  have hsucc : (iterate V S a (n + 1)).isSome := by rw [iterate_succ, hb]; exact hnext
  have hlt := hact.2.2 hsucc
  rw [impactReal_succ_eq_of_isSome (V := V) hb hsucc] at hlt
  linarith

/-- Strict form: strictly inside the active flight interval, the elapsed time is strictly below the
flight's duration. -/
theorem ActiveAt.elapsed_lt {S : BorelEnergyPreservingScattering V} {a : V.FlightState} {n : ℕ}
    {t : ℝ} (hact : ActiveAt V S a n t) {b : V.FlightState} (hb : iterate V S a n = some b)
    (hstrict : impactReal V S a n < t) :
    0 < t - impactReal V S a n ∧
      ∀ _ : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
        t - impactReal V S a n < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
  refine ⟨by linarith, fun hbdd => ?_⟩
  have hnext : (next V S b).isSome := by
    rw [Option.isSome_iff_ne_none]
    intro hnone
    exact ((next_eq_none_iff (V := V) S b).mp hnone) hbdd
  have hsucc : (iterate V S a (n + 1)).isSome := by rw [iterate_succ, hb]; exact hnext
  have hlt := hact.2.2 hsucc
  rw [impactReal_succ_eq_of_isSome (V := V) hb hsucc] at hlt
  linarith

/-- **Energy conservation along the unified forward trajectory**, for every chain. -/
theorem trajectory_hamiltonian_eq [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) {t : ℝ} (ht : 0 ≤ t) :
    V.hamiltonian (trajectory V S a t).1 (trajectory V S a t).2.1 (trajectory V S a t).2.2 =
      a.energy := by
  obtain ⟨n, hact⟩ := exists_activeAt V S a ht
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hact.1
  rw [trajectory_eq V S a ht hact hb]
  obtain ⟨h0, hdur⟩ := hact.elapsed_le (V := V) hb
  change V.hamiltonian b.edge (flightCurve V b (t - impactReal V S a n)).1
      (flightCurve V b (t - impactReal V S a n)).2 = a.energy
  rw [flightCurve_hamiltonian_eq V b h0 hdur]
  exact iterate_energy_eq (V := V) n hb

/-- **Physicality**: the unified trajectory always lies on the closed physical edge. -/
theorem trajectory_physical [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) {t : ℝ} (ht : 0 ≤ t) :
    (trajectory V S a t).2.1 ∈ Set.Icc (0 : ℝ) (Γ.length (trajectory V S a t).1) := by
  obtain ⟨n, hact⟩ := exists_activeAt V S a ht
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hact.1
  rw [trajectory_eq V S a ht hact hb]
  obtain ⟨h0, hdur⟩ := hact.elapsed_le (V := V) hb
  exact flightCurve_physical V b h0 hdur

/-- The unified trajectory stays at the regular initial energy. -/
theorem trajectory_regular [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) {t : ℝ} (ht : 0 ≤ t) :
    V.hamiltonian (trajectory V S a t).1 (trajectory V S a t).2.1 (trajectory V S a t).2.2 ∉
      V.exceptionalEnergies := by
  rw [trajectory_hamiltonian_eq V S a ht]
  exact a.regular

/-- **The Hamiltonian edge ODE.**  Strictly between two consecutive impacts — and, on the escape
flight of a terminating chain, at every time after the last impact — the unified trajectory's phase
component genuinely solves the concrete Hamiltonian edge ODE. -/
theorem trajectory_hasDerivAt [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) {n : ℕ} {b : V.FlightState} (hb : iterate V S a n = some b) {t : ℝ}
    (hact : ActiveAt V S a n t) (hstrict : impactReal V S a n < t) :
    HasDerivAt (fun s => (trajectory V S a s).2)
      (V.edgeVectorField b.edge (flightCurve V b (t - impactReal V S a n))) t := by
  classical
  obtain ⟨hin, hlt⟩ := hact.elapsed_lt (V := V) hb hstrict
  have hg := flightCurve_hasDerivAt V b hin hlt
  have hfc : HasDerivAt (fun s => flightCurve V b (s - impactReal V S a n))
      (V.edgeVectorField b.edge (flightCurve V b (t - impactReal V S a n))) t :=
    HasDerivAt.comp_sub_const t (impactReal V S a n) hg
  have hnn0 : 0 ≤ impactReal V S a n := impactReal_nonneg_of_isSome (V := V) hact.1
  -- Near `t` the trajectory is this flight's curve: the neighbourhood is cut at the next impact
  -- when there is one, and is a half-line `(impactReal n, ∞)` on the escape flight.
  have heq : (fun s => (trajectory V S a s).2) =ᶠ[nhds t]
      (fun s => flightCurve V b (s - impactReal V S a n)) := by
    by_cases hsucc : (iterate V S a (n + 1)).isSome
    · have hub := hact.2.2 hsucc
      filter_upwards [Ioo_mem_nhds hstrict hub] with s hs
      have hs0 : 0 ≤ s := le_of_lt (lt_of_le_of_lt hnn0 hs.1)
      rw [trajectory_eq V S a hs0 ⟨hact.1, hs.1.le, fun _ => hs.2⟩ hb]
    · filter_upwards [Ioi_mem_nhds hstrict] with s hs
      have hs0 : 0 ≤ s := le_of_lt (lt_of_le_of_lt hnn0 hs)
      rw [trajectory_eq V S a hs0 ⟨hact.1, hs.le, fun h => absurd h hsucc⟩ hb]
  exact hfc.congr_of_eventuallyEq heq

/-- **The impact rule.**  At each impact time the unified trajectory equals the initial phase of
the next flight state, i.e. the post-scattering restart: the trajectory is right-continuous at
impacts with the scattered value. -/
theorem trajectory_at_impact [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (n : ℕ) {b : V.FlightState} (hb : iterate V S a (n + 1) = some b) :
    trajectory V S a (impactReal V S a (n + 1)) = (b.edge, b.state) := by
  have hsome : (iterate V S a (n + 1)).isSome := by rw [hb]; rfl
  have hnn0 : 0 ≤ impactReal V S a (n + 1) := impactReal_nonneg_of_isSome (V := V) hsome
  have hact : ActiveAt V S a (n + 1) (impactReal V S a (n + 1)) :=
    ⟨hsome, le_rfl, fun hs => impactReal_lt_succ_of_isSome (V := V) hs⟩
  rw [trajectory_eq V S a hnn0 hact hb, sub_self, flightCurve_zero]

/-- The unified trajectory agrees with `forwardPhase` on infinite chains: it is a genuine
extension of the established infinite-chain theory, not a competing construction. -/
theorem trajectory_eq_forwardPhase [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (hchain : ∀ n, (iterate V S a n).isSome) {t : ℝ} (ht : 0 ≤ t) :
    trajectory V S a t = forwardPhase V S a hchain t := by
  obtain ⟨n, hn⟩ := exists_forward_flightIndex (V := V) S a hchain ht
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hchain n)
  rw [trajectory_eq V S a ht (activeAt_of_chain (V := V) hchain hn) hb,
    forwardPhase_eq V S a hchain ht hn hb]

/-!
## Chain congruence and composition

Two flight states with the same edge and initial state generate the same trajectory: the witnessing
segment is irrelevant.  This is what allows the flow to be restarted from a bare phase point rather
than from a distinguished flight state, and it is the flight-state precursor of the flow property.
-/

/-- The whole chain respects edge+state equivalence. -/
theorem iterate_congr (S : BorelEnergyPreservingScattering V) {a₁ a₂ : V.FlightState}
    (hedge : a₁.edge = a₂.edge) (hstate : a₁.state = a₂.state) (n : ℕ) :
    OptEquiv (V := V) (iterate V S a₁ n) (iterate V S a₂ n) := by
  induction n with
  | zero => exact Or.inr ⟨a₁, a₂, rfl, rfl, hedge, hstate⟩
  | succ k ih => exact optEquiv_bind_next (V := V) S ih

/-- The impact durations of edge+state-equal states agree: `impactDuration` sees only the edge and
the state. -/
theorem impactDuration_congr {b₁ b₂ : V.FlightState} (hedge : b₁.edge = b₂.edge)
    (hstate : b₁.state = b₂.state) : b₁.impactDuration = b₂.impactDuration := by
  unfold impactDuration
  rw [hedge, hstate]

/-- Edge+state-equal states have identical impact times. -/
theorem impactTime_congr (S : BorelEnergyPreservingScattering V) {a₁ a₂ : V.FlightState}
    (hedge : a₁.edge = a₂.edge) (hstate : a₁.state = a₂.state) (n : ℕ) :
    impactTime V S a₁ n = impactTime V S a₂ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [impactTime_succ, impactTime_succ, ih]
      rcases iterate_congr (V := V) S hedge hstate k with ⟨h1, h2⟩ | ⟨b₁, b₂, h1, h2, he, hs⟩
      · rw [h1, h2]
      · rw [h1, h2, Option.bind_some, Option.bind_some, impactDuration_congr (V := V) he hs]

theorem impactReal_congr (S : BorelEnergyPreservingScattering V) {a₁ a₂ : V.FlightState}
    (hedge : a₁.edge = a₂.edge) (hstate : a₁.state = a₂.state) (n : ℕ) :
    impactReal V S a₁ n = impactReal V S a₂ n := by
  unfold impactReal
  rw [impactTime_congr (V := V) S hedge hstate n]

/-- **Trajectory congruence.**  The unified trajectory depends only on the edge and initial state,
not on the witnessing physical segment.  This is what lets the flow restart from a bare phase
point. -/
theorem trajectory_congr [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    {a₁ a₂ : V.FlightState} (hedge : a₁.edge = a₂.edge) (hstate : a₁.state = a₂.state) {t : ℝ}
    (ht : 0 ≤ t) : trajectory V S a₁ t = trajectory V S a₂ t := by
  obtain ⟨n, hact⟩ := exists_activeAt V S a₁ ht
  obtain ⟨b₁, hb₁⟩ := Option.isSome_iff_exists.mp hact.1
  rcases iterate_congr (V := V) S hedge hstate n with ⟨h1, -⟩ | ⟨c₁, c₂, hc1, hc2, hce, hcs⟩
  · rw [h1] at hb₁; simp at hb₁
  · have hc₁b : c₁ = b₁ := Option.some.inj (hc1.symm.trans hb₁)
    subst hc₁b
    have hact₂ : ActiveAt V S a₂ n t := by
      refine ⟨by rw [hc2]; rfl, ?_, ?_⟩
      · rw [← impactReal_congr (V := V) S hedge hstate n]; exact hact.2.1
      · intro hsucc
        rw [← impactReal_congr (V := V) S hedge hstate (n + 1)]
        refine hact.2.2 ?_
        rcases iterate_congr (V := V) S hedge hstate (n + 1) with ⟨h1, h2⟩ | ⟨d₁, -, hd1, -, -, -⟩
        · rw [h2] at hsucc; simp at hsucc
        · rw [hd1]; rfl
    have hIR : impactReal V S a₁ n = impactReal V S a₂ n :=
      impactReal_congr (V := V) S hedge hstate n
    rw [trajectory_eq V S a₁ ht hact hc1, trajectory_eq V S a₂ ht hact₂ hc2, hIR, Prod.mk.injEq]
    exact ⟨hce, flightCurve_congr (V := V) hce hcs (by rw [← hIR]; linarith [hact.2.1])⟩

/-- **Chain composition.**  Running the chain `n + k` steps is running it `n` steps and then `k`
more from the state reached. -/
theorem iterate_add (S : BorelEnergyPreservingScattering V) (a : V.FlightState) (n k : ℕ) :
    iterate V S a (n + k) = Option.bind (iterate V S a n) (fun b => iterate V S b k) := by
  induction k with
  | zero => simp only [Nat.add_zero, iterate_zero, Option.bind_fun_some]
  | succ m ih =>
      rw [show n + (m + 1) = (n + m) + 1 from by omega, iterate_succ, ih]
      cases h : iterate V S a n with
      | none => rfl
      | some b => rw [Option.bind_some, Option.bind_some, iterate_succ]

/-- **Impact-time composition.**  The `(n+k)`-th impact of `a` is the `n`-th impact of `a` followed
by the `k`-th impact of the state reached there. -/
theorem impactReal_add (S : BorelEnergyPreservingScattering V) (a : V.FlightState) (n : ℕ)
    {b : V.FlightState} (hb : iterate V S a n = some b) (k : ℕ)
    (hdef : (iterate V S a (n + k)).isSome) :
    impactReal V S a (n + k) = impactReal V S a n + impactReal V S b k := by
  induction k with
  | zero => rw [show n + 0 = n from rfl, impactReal_zero]; ring
  | succ m ih =>
      have hmdef : (iterate V S a (n + m)).isSome :=
        iterate_isSome_of_le (V := V) (by omega) hdef
      -- the state at step `n + m` is the state at step `m` of the chain from `b`
      have hcomp : iterate V S a (n + m) = iterate V S b m := by
        rw [iterate_add (V := V) S a n m, hb]; rfl
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hmdef
      have hbm : iterate V S b m = some c := by rw [← hcomp]; exact hc
      have hbsucc : (iterate V S b (m + 1)).isSome := by
        have : iterate V S a (n + (m + 1)) = iterate V S b (m + 1) := by
          rw [iterate_add (V := V) S a n (m + 1), hb]; rfl
        rwa [this] at hdef
      rw [show n + (m + 1) = (n + m) + 1 from by omega,
        impactReal_succ_eq_of_isSome (V := V) hc (by
          rw [show (n + m) + 1 = n + (m + 1) from by omega]; exact hdef),
        impactReal_succ_eq_of_isSome (V := V) hbm hbsucc, ih hmdef]
      ring

/-- **The shift law.**  From the onset of flight `n` onwards, the trajectory of `a` is exactly the
trajectory of the flight state reached at step `n`.  Together with the within-flight restart law
this gives the flow property at an arbitrary time. -/
theorem trajectory_shift_eq [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) {n : ℕ} {b : V.FlightState} (hb : iterate V S a n = some b) {w : ℝ}
    (hw : 0 ≤ w) :
    trajectory V S a (impactReal V S a n + w) = trajectory V S b w := by
  classical
  obtain ⟨k, hact⟩ := exists_activeAt V S b hw
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hact.1
  -- the chain of `b` is the chain of `a` shifted by `n`
  have hcomp : ∀ j : ℕ, iterate V S a (n + j) = iterate V S b j := by
    intro j; rw [iterate_add (V := V) S a n j, hb]; rfl
  have hac : iterate V S a (n + k) = some c := by rw [hcomp k]; exact hc
  have hdef : (iterate V S a (n + k)).isSome := by rw [hac]; rfl
  have hshift : impactReal V S a (n + k) = impactReal V S a n + impactReal V S b k :=
    impactReal_add (V := V) S a n hb k hdef
  have hnn0 : 0 ≤ impactReal V S a n :=
    impactReal_nonneg_of_isSome (V := V) (by rw [hb]; rfl)
  have hactA : ActiveAt V S a (n + k) (impactReal V S a n + w) := by
    refine ⟨hdef, by rw [hshift]; linarith [hact.2.1], fun hsucc => ?_⟩
    have hbsucc : (iterate V S b (k + 1)).isSome := by
      rw [← hcomp (k + 1), show n + (k + 1) = (n + k) + 1 from by omega]; exact hsucc
    have hlt := hact.2.2 hbsucc
    have : impactReal V S a ((n + k) + 1) = impactReal V S a n + impactReal V S b (k + 1) := by
      rw [show (n + k) + 1 = n + (k + 1) from by omega]
      exact impactReal_add (V := V) S a n hb (k + 1)
        (by rw [show n + (k + 1) = (n + k) + 1 from by omega]; exact hsucc)
    rw [this]; linarith
  rw [trajectory_eq V S a (by linarith) hactA hac, trajectory_eq V S b hw hact hc, hshift]
  congr 2
  ring

/-!
## The general flow semigroup

The remaining input is the within-flight restart law for an arbitrary chain.  The bounded branch
reuses the established `flightCurve_restart_eq` and chain correspondence, now with the
infinite-chain hypothesis removed; the escape branch is new and rests on
`unboundedCurve_restart_eq`.
-/

/-- The state at time `u` of an **escaping** flight escapes as well. -/
theorem restart_not_bddAbove (b : V.FlightState) {u : ℝ} (hu0 : 0 < u)
    (hub : ¬ BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state)) :
    ¬ BddAbove (PhysicalEdgeSegment.durationSet V b.edge (flightCurve V b u)) := by
  have hfcu : flightCurve V b u = b.segment.unboundedCurve hub u := by
    unfold flightCurve; rw [dif_neg hub]
  rw [hfcu]
  exact b.segment.not_bddAbove_durationSet_unboundedCurve hub hu0.le

/-- **The within-flight restart law on an escape flight.**  On a global no-hit flight the restarted
flight curve is the original shifted by `u`, at *every* later time: there is no impact to cut the
correspondence off. -/
theorem flightCurve_restart_eq_of_not_bddAbove (b : V.FlightState) {u : ℝ} (hu0 : 0 < u)
    (hub : ¬ BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state))
    (hu : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      u < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state))
    {t : ℝ} (ht0 : 0 ≤ t) :
    flightCurve V (restart V b hu0 hu) t = flightCurve V b (u + t) := by
  classical
  set r := restart V b hu0 hu with hr
  have hfcu : flightCurve V b u = b.segment.unboundedCurve hub u := by
    unfold flightCurve; rw [dif_neg hub]
  have hrub : ¬ BddAbove (PhysicalEdgeSegment.durationSet V r.edge r.state) :=
    restart_not_bddAbove (V := V) b hu0 hub
  have hb'' : ¬ BddAbove (PhysicalEdgeSegment.durationSet V b.edge
      (b.segment.unboundedCurve hub u)) := by rw [← hfcu]; exact hrub
  have hLHS : flightCurve V r t = r.segment.unboundedCurve hrub t := by
    unfold flightCurve; rw [dif_neg hrub]
  have hRHS : flightCurve V b (u + t) = b.segment.unboundedCurve hub (u + t) := by
    unfold flightCurve; rw [dif_neg hub]
  rw [hLHS, hRHS]
  exact (PhysicalEdgeSegment.unboundedCurve_cast hfcu r.segment hrub hb'' t).symm.trans
    (b.segment.unboundedCurve_restart_eq hub hu0.le (hfcu ▸ r.segment) hb'' ht0)

/-- The within-flight restart law for an arbitrary chain: on the whole remaining first flight the
restarted flight curve is the original shifted by `u`.  The bounded branch is
`flightCurve_restart_eq`; the escape branch is `flightCurve_restart_eq_of_not_bddAbove`, where the
duration constraint on `t` is vacuous. -/
theorem flightCurve_restart_eq_general (b : V.FlightState) {u : ℝ} (hu0 : 0 < u)
    (hu : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      u < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state))
    {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      t < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) - u) :
    flightCurve V (restart V b hu0 hu) t = flightCurve V b (u + t) := by
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state)
  · exact flightCurve_restart_eq (V := V) b hu0 hbdd (hu hbdd) ht0 (ht hbdd)
  · exact flightCurve_restart_eq_of_not_bddAbove (V := V) b hu0 hbdd hu ht0

/-- On an escape flight the chain stops immediately after the restart as well. -/
theorem restart_next_eq_none (S : BorelEnergyPreservingScattering V) (b : V.FlightState) {u : ℝ}
    (hu0 : 0 < u) (hub : ¬ BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state))
    (hu : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      u < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state)) :
    next V S (restart V b hu0 hu) = none :=
  next_eq_none_of_not_bddAbove (V := V) S _ (restart_not_bddAbove (V := V) b hu0 hub)

/-- The restart chain is defined exactly where the original chain is (from the first impact on). -/
theorem restart_iterate_isSome_iff (S : BorelEnergyPreservingScattering V) (b : V.FlightState)
    {u : ℝ} (hu0 : 0 < u) (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state))
    (hu : u < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state))
    (ha'bdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge (flightCurve V b u))) (n : ℕ) :
    (iterate V S (restart V b hu0 (fun _ => hu)) (n + 1)).isSome ↔
      (iterate V S b (n + 1)).isSome := by
  rcases iterate_restart_congr (V := V) S b hu0 hbdd hu ha'bdd n with ⟨h1, h2⟩ | ⟨c₁, c₂, h1, h2, -, -⟩
  · rw [h1, h2]
  · rw [h1, h2]; simp

/-- Finite-prefix form of `impactReal_restart_eq`: the impact times of the restart chain are those
of the original shifted back by `u`, wherever they are defined.  No no-Zeno hypothesis is used, so
this applies to terminating chains. -/
theorem impactReal_restart_eq_of_isSome (S : BorelEnergyPreservingScattering V) (b : V.FlightState)
    {u : ℝ} (hu0 : 0 < u) (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state))
    (hu : u < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state))
    (ha'bdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge (flightCurve V b u))) (n : ℕ)
    (hdef : (iterate V S b (n + 1)).isSome) :
    impactReal V S (restart V b hu0 (fun _ => hu)) (n + 1) = impactReal V S b (n + 1) - u := by
  classical
  set r := restart V b hu0 (fun _ => hu) with hr
  have hfcs : flightCurve V b u = b.segment.maximalCurve hbdd u := by
    unfold flightCurve; rw [dif_pos hbdd]
    exact b.segment.maximalCurveClosed_eq_maximalCurve hbdd hu
  induction n with
  | zero =>
      have hrdef : (iterate V S r 1).isSome :=
        (restart_iterate_isSome_iff (V := V) S b hu0 hbdd hu ha'bdd 0).mpr hdef
      rw [impactReal_succ_eq_of_isSome (V := V) (iterate_zero (V := V) S r) hrdef,
        impactReal_succ_eq_of_isSome (V := V) (iterate_zero (V := V) S b) hdef,
        impactReal_zero, impactReal_zero]
      show (0 : ℝ) + sSup (PhysicalEdgeSegment.durationSet V b.edge (flightCurve V b u)) =
        0 + sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) - u
      rw [hfcs, b.segment.sSup_durationSet_maximalCurve_eq hbdd hu0.le hu]
      ring
  | succ m ih =>
      have hmdef : (iterate V S b (m + 1)).isSome :=
        iterate_isSome_of_le (V := V) (Nat.le_succ (m + 1)) hdef
      have hrdef : (iterate V S r (m + 2)).isSome :=
        (restart_iterate_isSome_iff (V := V) S b hu0 hbdd hu ha'bdd (m + 1)).mpr hdef
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hmdef
      obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp
        ((restart_iterate_isSome_iff (V := V) S b hu0 hbdd hu ha'bdd m).mpr hmdef)
      rw [impactReal_succ_eq_of_isSome (V := V) hc' hrdef,
        impactReal_succ_eq_of_isSome (V := V) hc hdef, ih hmdef]
      -- the two active flights are edge+state equal, hence have the same duration
      have hdur : sSup (PhysicalEdgeSegment.durationSet V c'.edge c'.state) =
          sSup (PhysicalEdgeSegment.durationSet V c.edge c.state) := by
        rcases iterate_restart_congr (V := V) S b hu0 hbdd hu ha'bdd m with
          ⟨h1, -⟩ | ⟨d₁, d₂, hd1, hd2, hde, hds⟩
        · rw [h1] at hc'; simp at hc'
        · have h1 : d₁ = c' := Option.some.inj (hd1.symm.trans hc')
          have h2 : d₂ = c := Option.some.inj (hd2.symm.trans hc)
          rw [← h1, ← h2, hde, hds]
      rw [hdur]
      ring

/-- **The within-flight restart semigroup for an arbitrary chain.**  Restarting the trajectory at a
time `u` strictly inside the current flight and running it for a further time `t` reproduces the
original trajectory at time `u + t`.  The infinite-chain hypothesis of `forwardPhase_semigroup` is
gone: terminating chains are handled by the escape branch, where the restart escapes too. -/
theorem trajectory_restart_eq [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (b : V.FlightState) {u : ℝ} (hu0 : 0 < u)
    (hu : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
      u < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state))
    {t : ℝ} (ht0 : 0 ≤ t) :
    trajectory V S b (u + t) = trajectory V S (restart V b hu0 hu) t := by
  classical
  set r := restart V b hu0 hu with hr
  by_cases hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state)
  · -- Bounded first flight: the chains correspond from the first impact on.
    have hfcs : flightCurve V b u = b.segment.maximalCurve hbdd u := by
      unfold flightCurve; rw [dif_pos hbdd]
      exact b.segment.maximalCurveClosed_eq_maximalCurve hbdd (hu hbdd)
    have ha'bdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge (flightCurve V b u)) := by
      rw [hfcs]
      exact (b.segment.bddAbove_durationSet_maximalCurve_iff hbdd hu0.le (hu hbdd)).mpr hbdd
    -- the first flight of `b` genuinely ends, so step 1 of its chain exists
    have hb1 : (iterate V S b 1).isSome := by
      rw [iterate_succ, iterate_zero, Option.bind_some, Option.isSome_iff_ne_none]
      intro hnone
      exact ((next_eq_none_iff (V := V) S b).mp hnone) hbdd
    have himp1 : impactReal V S b 1 = sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
      rw [impactReal_succ_eq_of_isSome (V := V) (iterate_zero (V := V) S b) hb1, impactReal_zero]
      ring
    obtain ⟨n, hact⟩ := exists_activeAt V S b (show (0:ℝ) ≤ u + t by linarith [hu0.le])
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hact.1
    cases n with
    | zero =>
        -- still inside the first flight
        have hceq : c = b := Option.some.inj (hc.symm.trans (iterate_zero (V := V) S b))
        have hub2 := hact.2.2 hb1
        rw [himp1] at hub2
        have hrbdd : BddAbove (PhysicalEdgeSegment.durationSet V r.edge r.state) := ha'bdd
        have hr1 : (iterate V S r 1).isSome :=
          (restart_iterate_isSome_iff (V := V) S b hu0 hbdd (hu hbdd) ha'bdd 0).mpr hb1
        have hactr : ActiveAt V S r 0 t := by
          refine ⟨by rw [iterate_zero]; rfl, by rw [impactReal_zero]; exact ht0, fun _ => ?_⟩
          rw [impactReal_restart_eq_of_isSome (V := V) S b hu0 hbdd (hu hbdd) ha'bdd 0 hb1, himp1]
          linarith [hact.2.1]
        rw [trajectory_eq V S b (by linarith [hu0.le]) hact hc,
          trajectory_eq V S r ht0 hactr (iterate_zero (V := V) S r),
          impactReal_zero, impactReal_zero, sub_zero, sub_zero, hceq]
        exact congrArg (fun y => (b.edge, y))
          (flightCurve_restart_eq_general (V := V) b hu0 hu ht0 (fun _ => by linarith)).symm
    | succ m =>
        -- past the first impact: transport along the chain correspondence
        have hmdef : (iterate V S b (m + 1)).isSome := by rw [hc]; rfl
        have hIR := impactReal_restart_eq_of_isSome (V := V) S b hu0 hbdd (hu hbdd) ha'bdd m hmdef
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp
          ((restart_iterate_isSome_iff (V := V) S b hu0 hbdd (hu hbdd) ha'bdd m).mpr hmdef)
        have hactr : ActiveAt V S r (m + 1) t := by
          refine ⟨by rw [hc']; rfl, by rw [hIR]; linarith [hact.2.1], fun hsucc => ?_⟩
          have hbsucc : (iterate V S b (m + 2)).isSome :=
            (restart_iterate_isSome_iff (V := V) S b hu0 hbdd (hu hbdd) ha'bdd (m + 1)).mp hsucc
          rw [impactReal_restart_eq_of_isSome (V := V) S b hu0 hbdd (hu hbdd) ha'bdd (m + 1) hbsucc]
          linarith [hact.2.2 hbsucc]
        rw [trajectory_eq V S b (by linarith [hu0.le]) hact hc,
          trajectory_eq V S r ht0 hactr hc', hIR]
        -- the two active flights are edge+state equal
        rcases iterate_restart_congr (V := V) S b hu0 hbdd (hu hbdd) ha'bdd m with
          ⟨h1, -⟩ | ⟨d₁, d₂, hd1, hd2, hde, hds⟩
        · rw [h1] at hc'; simp at hc'
        · have h1 : d₁ = c' := Option.some.inj (hd1.symm.trans hc')
          have h2 : d₂ = c := Option.some.inj (hd2.symm.trans hc)
          subst h1; subst h2
          rw [Prod.mk.injEq]
          refine ⟨hde.symm, ?_⟩
          rw [show t - (impactReal V S b (m + 1) - u) = u + t - impactReal V S b (m + 1) from by
            ring]
          exact flightCurve_congr (V := V) hde.symm hds.symm (by linarith [hact.2.1])
  · -- Escape flight: the chain stops at once, both before and after the restart.
    have hrub : ¬ BddAbove (PhysicalEdgeSegment.durationSet V r.edge r.state) :=
      restart_not_bddAbove (V := V) b hu0 hbdd
    have hb1 : ¬ (iterate V S b 1).isSome := by
      rw [iterate_succ, iterate_zero, Option.bind_some,
        next_eq_none_of_not_bddAbove (V := V) S b hbdd]
      simp
    have hr1 : ¬ (iterate V S r 1).isSome := by
      rw [iterate_succ, iterate_zero, Option.bind_some,
        next_eq_none_of_not_bddAbove (V := V) S r hrub]
      simp
    have hactb : ActiveAt V S b 0 (u + t) :=
      ⟨by rw [iterate_zero]; rfl, by rw [impactReal_zero]; linarith [hu0.le],
        fun h => absurd h hb1⟩
    have hactr : ActiveAt V S r 0 t :=
      ⟨by rw [iterate_zero]; rfl, by rw [impactReal_zero]; exact ht0, fun h => absurd h hr1⟩
    rw [trajectory_eq V S b (by linarith [hu0.le]) hactb (iterate_zero (V := V) S b),
      trajectory_eq V S r ht0 hactr (iterate_zero (V := V) S r),
      impactReal_zero, impactReal_zero, sub_zero, sub_zero]
    exact congrArg (fun y => (b.edge, y))
      (flightCurve_restart_eq_of_not_bddAbove (V := V) b hu0 hbdd hu ht0).symm

/-- **The general forward flow semigroup.**  For *any* nonnegative times `s` and `t`, and *any*
flight state `c` based at the phase point the trajectory occupies at time `s`, evolving `c` for a
further time `t` reproduces the original trajectory at time `s + t`:

`Φ⁺(s + t) a = Φ⁺ t (Φ⁺ s a)`.

This is the flight-state form of the flow property.  Nothing is assumed about the chain: `s` may
lie in any flight, at an impact, or on the escape flight of a terminating chain, and `c` need only
carry the right edge and phase point — by `trajectory_congr` its witnessing segment is irrelevant,
which is exactly what makes the flow well defined on phase points rather than on flight states. -/
theorem trajectory_semigroup [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (c : V.FlightState)
    (hce : c.edge = (trajectory V S a s).1) (hcs : c.state = (trajectory V S a s).2) :
    trajectory V S a (s + t) = trajectory V S c t := by
  classical
  obtain ⟨n, hact⟩ := exists_activeAt V S a hs
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hact.1
  set u : ℝ := s - impactReal V S a n with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith [hact.2.1]
  have hval : trajectory V S a s = (b.edge, flightCurve V b u) := trajectory_eq V S a hs hact hb
  -- reduce to the flight `b` that governs time `s`
  have hred : trajectory V S a (s + t) = trajectory V S b (u + t) := by
    rw [show s + t = impactReal V S a n + (u + t) from by rw [hu]; ring]
    exact trajectory_shift_eq (V := V) S a hb (by linarith)
  rw [hred]
  rcases eq_or_lt_of_le hu0 with hu_eq | hu_pos
  · -- `s` is exactly the onset of flight `b`
    rw [← hu_eq, zero_add]
    refine trajectory_congr (V := V) S ?_ ?_ ht
    · rw [hce, hval]
    · rw [hcs, hval, ← hu_eq, flightCurve_zero]
  · -- `s` is strictly inside flight `b`
    have hulift : ∀ hbdd : BddAbove (PhysicalEdgeSegment.durationSet V b.edge b.state),
        u < sSup (PhysicalEdgeSegment.durationSet V b.edge b.state) := by
      intro hbdd
      exact (hact.elapsed_lt (V := V) hb (by rw [hu] at hu_pos; linarith)).2 hbdd
    rw [trajectory_restart_eq (V := V) S b hu_pos hulift ht]
    refine trajectory_congr (V := V) S ?_ ?_ ht
    · rw [restart_edge, hce, hval]
    · rw [restart_state, hcs, hval]

end FlightState
end MechanicalPotential
end HamiltonianMetricGraphs
