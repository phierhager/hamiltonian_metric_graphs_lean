/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.4: the germ-speed chain model of the event chain
-/

import HamiltonianMetricGraphs.ImpactStep
import HamiltonianMetricGraphs.QuotientFlow

/-!
# The germ–speed chain model

After its first impact the trajectory is a sequence of flights departing vertices, each described
by a germ and an inward speed.  This module turns that picture into a *total* and *Borel* model of
the event chain and identifies it with `FlightState.iterate` / `FlightState.impactReal` /
`FlightState.trajectory`.

The first step is to upgrade the maps of `DepartureFlight.lean` and `ImpactStep.lean` from
"measurable on the impact stratum" to **globally measurable**: off the regular speeds and on the
speeds whose flight never lands, the landing map degenerates to the departure point itself (with
the Lean convention `sSup ∅ = 0` for an unbounded duration set), and that branch is measurable too.
Together with the countable cover by the strata `departureImpactSet η n` this makes

* `measurable_departureLandingTotal`, `measurable_departureDurationTotal`,
  `measurable_departureStepTotal`

total Borel maps, so the chain can be iterated without carrying domain hypotheses.
-/

namespace HamiltonianMetricGraphs

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

/-- **Measurability is local along a countable measurable cover.** -/
theorem measurable_of_countable_cover {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (hcover : (⋃ n, s n) = univ) (hf : ∀ n, Measurable ((s n).restrict f)) : Measurable f := by
  intro A hA
  have hpre : f ⁻¹' A = ⋃ n, (s n ∩ f ⁻¹' A) := by
    rw [← iUnion_inter, hcover, univ_inter]
  rw [hpre]
  refine MeasurableSet.iUnion fun n => ?_
  have himg := (MeasurableEmbedding.subtype_coe (hs n)).measurableSet_image.mpr (hf n hA)
  have heq : (Subtype.val '' ((s n).restrict f ⁻¹' A)) = s n ∩ f ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨x, hx1⟩, hx2, rfl⟩
  rw [← heq]
  exact himg

/-- **Measurability from a countable measurable cover together with a Borel formula on each
piece.** -/
theorem measurable_of_countable_cover_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} {F : ℕ → α → β} {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (hcover : (⋃ n, s n) = univ) (hF : ∀ n, Measurable (F n))
    (heq : ∀ n, ∀ x ∈ s n, f x = F n x) : Measurable f := by
  refine measurable_of_countable_cover hs hcover fun n => ?_
  have h : (s n).restrict f = (s n).restrict (F n) := funext fun z => heq n z z.2
  rw [h]
  exact (hF n).comp measurable_subtype_coe

namespace MechanicalPotential

open PhysicalEdgeSegment

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- A subset of `Γ.EdgeEnd × ℝ` is measurable as soon as all its slices are: the germ factor is
finite and discrete. -/
theorem measurableSet_germ_prod {A : Set (Γ.EdgeEnd × ℝ)}
    (h : ∀ η : Γ.EdgeEnd, MeasurableSet {r | (η, r) ∈ A}) : MeasurableSet A := by
  have heq : A = ⋃ η : Γ.EdgeEnd, ({η} : Set Γ.EdgeEnd) ×ˢ {r | (η, r) ∈ A} := by
    ext ⟨η, r⟩
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun η => (measurableSet_singleton η).prod (h η)

/-- A map into `Γ.EdgeEnd × ℝ` is measurable as soon as its two components are; the germ component
is measurable as soon as the preimage of every germ is. -/
theorem measurable_germ_prod {α : Type*} [MeasurableSpace α] {f : α → Γ.EdgeEnd × ℝ}
    (h1 : ∀ η : Γ.EdgeEnd, MeasurableSet ((fun x => (f x).1) ⁻¹' {η}))
    (h2 : Measurable fun x => (f x).2) : Measurable f :=
  (measurable_to_countable' h1).prodMk h2

section Total

variable [Nonempty Γ.Edge]

/-- The regular speeds at `η` whose departure flight actually lands.  It is the complement, inside
the regular speeds, of the speeds that survive every integer time. -/
theorem measurableSet_departureLands (η : Γ.EdgeEnd) :
    MeasurableSet {r | r ∈ V.regularSpeeds η ∧
      BddAbove (durationSet V η.1 (departurePoint η r))} := by
  have heq : {r | r ∈ V.regularSpeeds η ∧
      BddAbove (durationSet V η.1 (departurePoint η r))} =
      V.regularSpeeds η \ ⋂ n : ℕ, V.departureNoImpactSet η (n + 1) := by
    ext r
    constructor
    · rintro ⟨hreg, hbdd⟩
      refine ⟨hreg, ?_⟩
      intro hmem
      obtain ⟨n, hn⟩ := exists_nat_gt (sSup (durationSet V η.1 (departurePoint η r)))
      have h := (mem_iInter.mp hmem n).2 hbdd
      have hcast : ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := le_rfl
      have : ((n : ℕ) : ℝ) + 1 < sSup (durationSet V η.1 (departurePoint η r)) := h
      linarith
    · rintro ⟨hreg, hnot⟩
      refine ⟨hreg, ?_⟩
      by_contra hbdd
      exact hnot (mem_iInter.mpr fun n => ⟨hreg, fun hb => absurd hb hbdd⟩)
  rw [heq]
  exact (V.isOpen_regularSpeeds η).measurableSet.diff
    (MeasurableSet.iInter fun n =>
      V.measurableSet_departureNoImpactSet η (by positivity))

omit [Nonempty Γ.Edge] in
/-- Off the landing speeds the departure landing map is the departure point itself. -/
theorem departureLanding_of_not_lands {η : Γ.EdgeEnd} {r : ℝ}
    (h : ¬ (r ∈ V.regularSpeeds η ∧ BddAbove (durationSet V η.1 (departurePoint η r)))) :
    V.departureLanding η r = departurePoint η r := by
  by_cases hreg : r ∈ V.regularSpeeds η
  · have hbdd : ¬ BddAbove (durationSet V η.1 (departurePoint η r)) := fun hb => h ⟨hreg, hb⟩
    rw [departureLanding, Real.sSup_of_not_bddAbove hbdd, V.departureFlight_zero]
  · rw [departureLanding, V.departureFlight_of_notMem hreg]

/-- The impact duration of a departure datum, cut to zero off the regular speeds so that it is a
total function of the speed. -/
noncomputable def departureDurationTotal (η : Γ.EdgeEnd) (r : ℝ) : ℝ := by
  classical
  exact if r ∈ V.regularSpeeds η then sSup (durationSet V η.1 (departurePoint η r)) else 0

omit [Nonempty Γ.Edge] in
theorem departureDurationTotal_of_mem {η : Γ.EdgeEnd} {r : ℝ} (hr : r ∈ V.regularSpeeds η) :
    V.departureDurationTotal η r = sSup (durationSet V η.1 (departurePoint η r)) := by
  classical
  unfold departureDurationTotal
  rw [if_pos hr]

omit [Nonempty Γ.Edge] in
/-- Off the landing speeds the total impact duration vanishes. -/
theorem departureDurationTotal_of_not_lands {η : Γ.EdgeEnd} {r : ℝ}
    (h : ¬ (r ∈ V.regularSpeeds η ∧ BddAbove (durationSet V η.1 (departurePoint η r)))) :
    V.departureDurationTotal η r = 0 := by
  classical
  unfold departureDurationTotal
  by_cases hreg : r ∈ V.regularSpeeds η
  · rw [if_pos hreg, Real.sSup_of_not_bddAbove (fun hb => h ⟨hreg, hb⟩)]
  · rw [if_neg hreg]

/-- The cover of the speed line used to globalise the departure maps. -/
private def landCover (η : Γ.EdgeEnd) : ℕ → Set ℝ
  | 0 => {r | ¬ (r ∈ V.regularSpeeds η ∧ BddAbove (durationSet V η.1 (departurePoint η r)))}
  | n + 1 => V.departureImpactSet η (n + 1)

private theorem measurableSet_landCover (η : Γ.EdgeEnd) (n : ℕ) :
    MeasurableSet (V.landCover η n) := by
  cases n with
  | zero => exact (V.measurableSet_departureLands η).compl
  | succ k => exact V.measurableSet_departureImpactSet η (by positivity)

omit [Nonempty Γ.Edge] in
private theorem iUnion_landCover (η : Γ.EdgeEnd) : (⋃ n, V.landCover η n) = univ := by
  refine eq_univ_of_forall fun r => ?_
  by_cases h : r ∈ V.regularSpeeds η ∧ BddAbove (durationSet V η.1 (departurePoint η r))
  · obtain ⟨n, hn⟩ := exists_nat_gt (sSup (durationSet V η.1 (departurePoint η r)))
    refine mem_iUnion.mpr ⟨n + 1, ?_⟩
    refine ⟨h.1, fun hmem => ?_⟩
    have := hmem.2 h.2
    have hcast : ((n : ℕ) : ℝ) + 1 < sSup (durationSet V η.1 (departurePoint η r)) := this
    linarith
  · exact mem_iUnion.mpr ⟨0, h⟩

/-- **The departure landing map is globally Borel.** -/
theorem measurable_departureLandingTotal (η : Γ.EdgeEnd) :
    Measurable (V.departureLanding η) := by
  refine measurable_of_countable_cover (V.measurableSet_landCover η) (V.iUnion_landCover η) ?_
  intro n
  cases n with
  | zero =>
      have heq : (V.landCover η 0).restrict (V.departureLanding η) =
          (V.landCover η 0).restrict (departurePoint η) :=
        funext fun s => V.departureLanding_of_not_lands s.2
      rw [heq]
      exact (continuous_departurePoint η).measurable.comp measurable_subtype_coe
  | succ k => exact V.measurable_departureLanding η ((k : ℝ) + 1)

/-- **The total departure impact duration is globally Borel.** -/
theorem measurable_departureDurationTotal (η : Γ.EdgeEnd) :
    Measurable (V.departureDurationTotal η) := by
  refine measurable_of_countable_cover (V.measurableSet_landCover η) (V.iUnion_landCover η) ?_
  intro n
  cases n with
  | zero =>
      have heq : (V.landCover η 0).restrict (V.departureDurationTotal η) = fun _ => (0 : ℝ) :=
        funext fun s => V.departureDurationTotal_of_not_lands s.2
      rw [heq]
      exact measurable_const
  | succ k =>
      have heq : (V.landCover η (k + 1)).restrict (V.departureDurationTotal η) =
          fun s : V.departureImpactSet η ((k : ℝ) + 1) =>
            sSup (durationSet V η.1 (departurePoint η (s : ℝ))) :=
        funext fun s => V.departureDurationTotal_of_mem s.2.1
      rw [heq]
      exact V.measurable_departureDuration η ((k : ℝ) + 1)

variable (S : BorelEnergyPreservingScattering V)

/-- **The impact step is globally Borel.** -/
theorem measurable_departureStepTotal (η : Γ.EdgeEnd) :
    Measurable (departureStep V S η) := by
  have hcov : Measurable fun r : ℝ =>
      scatterCovector (V := V) S (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r)) :=
    (measurable_scatterCovector (V := V) S).comp
      ((measurable_edgeCovector (Γ := Γ) η.1).comp (V.measurable_departureLandingTotal η))
  exact ((Γ.measurable_boundary_germ).comp hcov).prodMk
    (((Γ.measurable_boundary_momentum).comp hcov).abs)

end Total


/-! ### The germ–speed chain -/

section Chain

variable (S : BorelEnergyPreservingScattering V)

/-- The **germ–speed chain**: iterate the impact step. -/
noncomputable def chainIterate (c : Γ.EdgeEnd × ℝ) : ℕ → Γ.EdgeEnd × ℝ
  | 0 => c
  | n + 1 => departureStep V S (chainIterate c n).1 (chainIterate c n).2

@[simp] theorem chainIterate_zero (c : Γ.EdgeEnd × ℝ) : chainIterate V S c 0 = c := rfl

theorem chainIterate_succ (c : Γ.EdgeEnd × ℝ) (n : ℕ) :
    chainIterate V S c (n + 1) =
      departureStep V S (chainIterate V S c n).1 (chainIterate V S c n).2 := rfl

/-- The elapsed time of the `n`-th impact along the chain. -/
noncomputable def chainTime (c : Γ.EdgeEnd × ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => chainTime c n +
      V.departureDurationTotal (chainIterate V S c n).1 (chainIterate V S c n).2

@[simp] theorem chainTime_zero (c : Γ.EdgeEnd × ℝ) : chainTime V S c 0 = 0 := rfl

theorem chainTime_succ (c : Γ.EdgeEnd × ℝ) (n : ℕ) :
    chainTime V S c (n + 1) = chainTime V S c n +
      V.departureDurationTotal (chainIterate V S c n).1 (chainIterate V S c n).2 := rfl

/-- **Regularity propagates along the chain.**  The scattered departure after an impact carries the
same energy, so it is again a regular departure speed. -/
theorem departureStep_mem_regularSpeeds (η : Γ.EdgeEnd) {r : ℝ} (hr : r ∈ V.regularSpeeds η)
    (hbdd : BddAbove (durationSet V η.1 (departurePoint η r))) :
    (departureStep V S η r).2 ∈ V.regularSpeeds (departureStep V S η r).1 := by
  have hbdd' : BddAbove (durationSet V (V.ofDeparture η hr.1 hr.2).edge
      (V.ofDeparture η hr.1 hr.2).state) := hbdd
  have hpos : 0 < (departureStep V S η r).2 := by
    rw [departureStep]
    exact abs_pos.mpr (scatterCovector (V := V) S
      (edgeCovector (Γ := Γ) η.1 (V.departureLanding η r))).momentum_ne_zero
  refine ⟨hpos, ?_⟩
  obtain ⟨b, hb, -, hbenergy, -, -⟩ :=
    FlightState.next_eq_some_of_bddAbove (V := V) S (V.ofDeparture η hr.1 hr.2) hbdd'
  obtain ⟨he, hs⟩ := V.departureStep_next S η hr hbdd hb
  have heq : V.departureEnergy (departureStep V S η r).1 (departureStep V S η r).2 = b.energy := by
    rw [FlightState.energy_eq, he, hs]
    rfl
  rw [heq, hbenergy, V.ofDeparture_energy]
  exact hr.2

/-- **The chain model computes the event chain.**  Whenever the event chain of the departure flight
from `(η, r)` is defined at step `n`, its `n`-th flight departs the germ and speed
`chainIterate (η, r) n` at a regular energy, and its `n`-th impact time is `chainTime (η, r) n`. -/
theorem chainIterate_correspondence (η : Γ.EdgeEnd) {r : ℝ} (hr : r ∈ V.regularSpeeds η) :
    ∀ (n : ℕ) (b : V.FlightState),
      FlightState.iterate V S (V.ofDeparture η hr.1 hr.2) n = some b →
        b.edge = (chainIterate V S (η, r) n).1.1 ∧
        b.state = departurePoint (chainIterate V S (η, r) n).1 (chainIterate V S (η, r) n).2 ∧
        (chainIterate V S (η, r) n).2 ∈ V.regularSpeeds (chainIterate V S (η, r) n).1 ∧
        FlightState.impactReal V S (V.ofDeparture η hr.1 hr.2) n = chainTime V S (η, r) n := by
  intro n
  induction n with
  | zero =>
      intro b hb
      rw [FlightState.iterate_zero] at hb
      obtain rfl : V.ofDeparture η hr.1 hr.2 = b := Option.some_injective _ hb
      exact ⟨rfl, rfl, hr, by rw [FlightState.impactReal_zero, chainTime_zero]⟩
  | succ k ih =>
      intro b hb
      rw [FlightState.iterate_succ] at hb
      obtain ⟨c, hc, hcb⟩ := Option.bind_eq_some_iff.mp hb
      obtain ⟨hce, hcs, hcreg, hct⟩ := ih c hc
      -- the current flight lands
      have hbdd : BddAbove (durationSet V (chainIterate V S (η, r) k).1.1
          (departurePoint (chainIterate V S (η, r) k).1 (chainIterate V S (η, r) k).2)) := by
        have h := FlightState.bddAbove_of_next_isSome (V := V) (S := S) (a := c)
          (by rw [hcb]; rfl)
        rwa [hce, hcs] at h
      -- compare with the canonical departure flight of the chain datum
      have hde : (V.ofDeparture (chainIterate V S (η, r) k).1 hcreg.1 hcreg.2).edge =
          (chainIterate V S (η, r) k).1.1 := rfl
      have hds : (V.ofDeparture (chainIterate V S (η, r) k).1 hcreg.1 hcreg.2).state =
          departurePoint (chainIterate V S (η, r) k).1 (chainIterate V S (η, r) k).2 := rfl
      rcases FlightState.next_congr (V := V) S (a₁ := c)
          (a₂ := V.ofDeparture (chainIterate V S (η, r) k).1 hcreg.1 hcreg.2)
          (by rw [hce, hde]) (by rw [hcs, hds]) with ⟨h1, -⟩ | ⟨b₁, b₂, h1, h2, hb12e, hb12s⟩
      · rw [h1] at hcb; exact absurd hcb (by simp)
      · obtain rfl : b₁ = b := Option.some_injective _ (h1.symm.trans hcb)
        obtain ⟨h2e, h2s⟩ := V.departureStep_next S (chainIterate V S (η, r) k).1 hcreg hbdd h2
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hb12e, h2e, chainIterate_succ]
        · rw [hb12s, h2s, chainIterate_succ]
        · rw [chainIterate_succ]
          exact V.departureStep_mem_regularSpeeds S (chainIterate V S (η, r) k).1 hcreg hbdd
        · have hsucc : (FlightState.iterate V S (V.ofDeparture η hr.1 hr.2) (k + 1)).isSome := by
            rw [FlightState.iterate_succ, hb]; rfl
          rw [FlightState.impactReal_succ_eq_of_isSome (V := V) hc hsucc, hct,
            chainTime_succ, hce, hcs,
            V.departureDurationTotal_of_mem hcreg]

end Chain


/-! ### The landing condition along the chain -/

section Lands

variable (S : BorelEnergyPreservingScattering V)

/-- The germ–speed data whose flight is regular and lands. -/
def landsSet : Set (Γ.EdgeEnd × ℝ) :=
  {c | c.2 ∈ V.regularSpeeds c.1 ∧ BddAbove (durationSet V c.1.1 (departurePoint c.1 c.2))}

/-- The chain lands at each of its first `n` flights. -/
def ChainLands (c : Γ.EdgeEnd × ℝ) : ℕ → Prop
  | 0 => True
  | n + 1 => ChainLands c n ∧ chainIterate V S c n ∈ V.landsSet

theorem chainLands_zero (c : Γ.EdgeEnd × ℝ) : ChainLands V S c 0 := trivial

theorem chainLands_succ_iff (c : Γ.EdgeEnd × ℝ) (n : ℕ) :
    ChainLands V S c (n + 1) ↔ ChainLands V S c n ∧ chainIterate V S c n ∈ V.landsSet :=
  Iff.rfl

theorem chainLands_of_le {c : Γ.EdgeEnd × ℝ} {m n : ℕ} (hmn : m ≤ n)
    (h : ChainLands V S c n) : ChainLands V S c m := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn]
  | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
      · exact ih (Nat.lt_succ_iff.mp hlt) h.1
      · rw [heq]; exact h

/-- **Regularity propagates along the chain.** -/
theorem chainIterate_mem_regularSpeeds {c : Γ.EdgeEnd × ℝ} (hc : c.2 ∈ V.regularSpeeds c.1)
    {n : ℕ} (h : ChainLands V S c n) :
    (chainIterate V S c n).2 ∈ V.regularSpeeds (chainIterate V S c n).1 := by
  induction n with
  | zero => exact hc
  | succ k ih =>
      rw [chainIterate_succ]
      exact V.departureStep_mem_regularSpeeds S (chainIterate V S c k).1 (ih h.1) h.2.2

/-- **The chain landing condition is the definedness of the event chain.** -/
theorem chainLands_iff_isSome (η : Γ.EdgeEnd) {r : ℝ} (hr : r ∈ V.regularSpeeds η) (n : ℕ) :
    ChainLands V S (η, r) n ↔ (FlightState.iterate V S (V.ofDeparture η hr.1 hr.2) n).isSome := by
  induction n with
  | zero => simp [ChainLands, FlightState.iterate_zero]
  | succ k ih =>
      constructor
      · intro h
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (ih.mp h.1)
        obtain ⟨hbe, hbs, -, -⟩ := V.chainIterate_correspondence S η hr k b hb
        have hbdd : BddAbove (durationSet V b.edge b.state) := by rw [hbe, hbs]; exact h.2.2
        obtain ⟨b', hb', -⟩ := FlightState.next_eq_some_of_bddAbove (V := V) S b hbdd
        rw [FlightState.iterate_succ, hb, Option.bind_some, hb']
        rfl
      · intro h
        have hk : (FlightState.iterate V S (V.ofDeparture η hr.1 hr.2) k).isSome :=
          FlightState.iterate_isSome_of_le (V := V) (Nat.le_succ k) h
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hk
        obtain ⟨hbe, hbs, hbreg, -⟩ := V.chainIterate_correspondence S η hr k b hb
        refine ⟨ih.mpr hk, hbreg, ?_⟩
        have hnext : (FlightState.next V S b).isSome := by
          rw [FlightState.iterate_succ, hb] at h
          exact h
        have hbdd := FlightState.bddAbove_of_next_isSome (V := V) (S := S) (a := b) hnext
        rwa [hbe, hbs] at hbdd

end Lands

/-! ### Measurability of the chain -/

section ChainMeasurable

variable [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)

theorem measurableSet_landsSet : MeasurableSet (V.landsSet (Γ := Γ)) :=
  measurableSet_germ_prod fun η => V.measurableSet_departureLands η

theorem measurable_departureStepProd :
    Measurable fun c : Γ.EdgeEnd × ℝ => departureStep V S c.1 c.2 :=
  measurable_from_prod_countable_right fun η => V.measurable_departureStepTotal S η

theorem measurable_departureDurationProd :
    Measurable fun c : Γ.EdgeEnd × ℝ => V.departureDurationTotal c.1 c.2 :=
  measurable_from_prod_countable_right fun η => V.measurable_departureDurationTotal η

theorem measurable_chainIterate {α : Type*} [MeasurableSpace α] {g : α → Γ.EdgeEnd × ℝ}
    (hg : Measurable g) (n : ℕ) : Measurable fun x => chainIterate V S (g x) n := by
  induction n with
  | zero => exact hg
  | succ k ih => exact (V.measurable_departureStepProd S).comp ih

theorem measurable_chainTime {α : Type*} [MeasurableSpace α] {g : α → Γ.EdgeEnd × ℝ}
    (hg : Measurable g) (n : ℕ) : Measurable fun x => chainTime V S (g x) n := by
  induction n with
  | zero => exact measurable_const
  | succ k ih =>
      exact ih.add ((V.measurable_departureDurationProd).comp
        (V.measurable_chainIterate S hg k))

theorem measurableSet_chainLands {α : Type*} [MeasurableSpace α] {g : α → Γ.EdgeEnd × ℝ}
    (hg : Measurable g) (n : ℕ) :
    MeasurableSet {x : α | ChainLands V S (g x) n} := by
  induction n with
  | zero =>
      have heq : {x : α | ChainLands V S (g x) 0} = univ := by
        ext x; simp [ChainLands]
      rw [heq]
      exact MeasurableSet.univ
  | succ k ih =>
      have heq : {x : α | ChainLands V S (g x) (k + 1)} =
          {x : α | ChainLands V S (g x) k} ∩
            (fun x => chainIterate V S (g x) k) ⁻¹' V.landsSet := by
        ext x
        exact V.chainLands_succ_iff S (g x) k
      rw [heq]
      exact ih.inter ((V.measurable_chainIterate S hg k) (V.measurableSet_landsSet))

end ChainMeasurable


/-! ### The total departure flow -/

section Flow

variable [Nonempty Γ.Edge]

theorem measurableSet_departurePreImpact (η : Γ.EdgeEnd) :
    MeasurableSet (V.departurePreImpact η) := by
  have heq : V.departurePreImpact η =
      ⋃ q : {q : ℚ // 0 < (q : ℝ)},
        V.departureNoImpactSet η (q : ℝ) ×ˢ Ico (0 : ℝ) ((q : ℚ) : ℝ) := by
    ext z
    constructor
    · rintro ⟨hreg, hw0, hlt⟩
      obtain ⟨d, hd0, hwd, hdT⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
      have hwd' : z.2 < d := by
        rcases lt_or_ge z.2 d with h | h
        · exact h
        · exact absurd (ENNReal.ofReal_le_ofReal h) (not_le.mpr hwd)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hwd'
      have hqpos : 0 < ((q : ℚ) : ℝ) := lt_of_le_of_lt hw0 hq1
      refine mem_iUnion.mpr ⟨⟨q, hqpos⟩, ⟨hreg, ?_⟩, ⟨hw0, hq1⟩⟩
      refine (V.ofReal_lt_impactTime_iff (V.durationSet_nonempty_of_regularSpeed hreg)
        hqpos).mp ?_
      exact lt_trans ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hqpos.le).mpr hq2) hdT
    · intro hmem
      obtain ⟨q, hrq, hwq⟩ := mem_iUnion.mp hmem
      refine ⟨hrq.1, hwq.1, ?_⟩
      have hT := (V.ofReal_lt_impactTime_iff (V.durationSet_nonempty_of_regularSpeed hrq.1)
        q.2).mpr hrq.2
      exact lt_trans ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hwq.1).mpr hwq.2) hT
  rw [heq]
  exact MeasurableSet.iUnion fun q =>
    (V.measurableSet_departureNoImpactSet η q.2).prod measurableSet_Ico

/-- The **departure flow**: the departure flight map extended by the departure point outside the
pre-impact region, so that it becomes a total Borel map of the speed and the time. -/
noncomputable def departureFlow (η : Γ.EdgeEnd) (z : ℝ × ℝ) : ℝ × ℝ := by
  classical
  exact if z ∈ V.departurePreImpact η then V.departureFlight η z.1 z.2 else departurePoint η z.1

omit [Nonempty Γ.Edge] in
theorem departureFlow_of_mem {η : Γ.EdgeEnd} {z : ℝ × ℝ} (hz : z ∈ V.departurePreImpact η) :
    V.departureFlow η z = V.departureFlight η z.1 z.2 := by
  classical
  unfold departureFlow
  rw [if_pos hz]

omit [Nonempty Γ.Edge] in
theorem departureFlow_of_notMem {η : Γ.EdgeEnd} {z : ℝ × ℝ}
    (hz : z ∉ V.departurePreImpact η) :
    V.departureFlow η z = departurePoint η z.1 := by
  classical
  unfold departureFlow
  rw [if_neg hz]

attribute [irreducible] departureFlow

theorem measurable_departureFlow (η : Γ.EdgeEnd) : Measurable (V.departureFlow η) := by
  classical
  refine measurable_of_measurable_union_cover (V.departurePreImpact η)
    (V.departurePreImpact η)ᶜ (V.measurableSet_departurePreImpact η)
    (V.measurableSet_departurePreImpact η).compl (by rw [union_compl_self]) ?_ ?_
  · change Measurable ((V.departurePreImpact η).restrict (V.departureFlow η))
    have heq : (V.departurePreImpact η).restrict (V.departureFlow η) =
        (V.departurePreImpact η).restrict (fun z => V.departureFlight η z.1 z.2) :=
      funext fun z => V.departureFlow_of_mem z.2
    rw [heq]
    exact (continuousOn_iff_continuous_restrict.mp (V.continuousOn_departureFlight η)).measurable
  · change Measurable ((V.departurePreImpact η)ᶜ.restrict (V.departureFlow η))
    have heq : (V.departurePreImpact η)ᶜ.restrict (V.departureFlow η) =
        fun z : ((V.departurePreImpact η)ᶜ : Set (ℝ × ℝ)) => departurePoint η (z : ℝ × ℝ).1 :=
      funext fun z => V.departureFlow_of_notMem z.2
    rw [heq]
    exact ((continuous_departurePoint η).comp
      (continuous_fst.comp continuous_subtype_val)).measurable

theorem measurable_departureFlowProd :
    Measurable fun p : Γ.EdgeEnd × (ℝ × ℝ) => V.departureFlow p.1 p.2 :=
  measurable_from_prod_countable_right fun η => V.measurable_departureFlow η

omit [Nonempty Γ.Edge] in
/-- A nonnegative time strictly before the impact is below the impact time. -/
theorem ofReal_lt_impactTime_of_le {e : Γ.Edge} {x : ℝ × ℝ}
    (hne : (durationSet V e x).Nonempty) {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ _ : BddAbove (durationSet V e x), w < sSup (durationSet V e x)) :
    ENNReal.ofReal w < V.impactTime e x := by
  rcases eq_or_lt_of_le hw with h0 | hpos
  · rw [← h0, ENNReal.ofReal_zero, V.lt_impactTime_iff]
    obtain ⟨T, hT⟩ := hne
    exact ⟨⟨T, hT⟩, ENNReal.ofReal_pos.mpr (V.pos_of_mem_durationSet hT)⟩
  · exact (V.ofReal_lt_impactTime_iff hne hpos).mpr h

end Flow


/-! ### The chain model computes the trajectory -/

section Trajectory

variable [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)

omit [Nonempty Γ.Edge] in
/-- The chain-model form of the active-flight condition. -/
theorem activeAt_iff_chain (η : Γ.EdgeEnd) {r : ℝ} (hr : r ∈ V.regularSpeeds η) (n : ℕ) (t : ℝ) :
    FlightState.ActiveAt V S (V.ofDeparture η hr.1 hr.2) n t ↔
      (ChainLands V S (η, r) n ∧ chainTime V S (η, r) n ≤ t ∧
        (ChainLands V S (η, r) (n + 1) → t < chainTime V S (η, r) (n + 1))) := by
  have hL : ∀ m : ℕ, ChainLands V S (η, r) m ↔
      (FlightState.iterate V S (V.ofDeparture η hr.1 hr.2) m).isSome :=
    fun m => V.chainLands_iff_isSome S η hr m
  have hT : ∀ m : ℕ, (FlightState.iterate V S (V.ofDeparture η hr.1 hr.2) m).isSome →
      FlightState.impactReal V S (V.ofDeparture η hr.1 hr.2) m = chainTime V S (η, r) m := by
    intro m hm
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hm
    exact (V.chainIterate_correspondence S η hr m b hb).2.2.2
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(hL n).mpr h1, ?_, fun hLs => ?_⟩
    · rw [← hT n h1]; exact h2
    · rw [← hT (n + 1) ((hL (n + 1)).mp hLs)]
      exact h3 ((hL (n + 1)).mp hLs)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(hL n).mp h1, ?_, fun hs => ?_⟩
    · rw [hT n ((hL n).mp h1)]; exact h2
    · rw [hT (n + 1) hs]
      exact h3 ((hL (n + 1)).mpr hs)

/-- **The chain model computes the trajectory.**  On the active interval of step `n` the trajectory
of the departure flight from `(η, r)` is the departure flow of the `n`-th chain datum, run for the
time elapsed since the `n`-th impact. -/
theorem trajectory_chain_eq (η : Γ.EdgeEnd) {r : ℝ} (hr : r ∈ V.regularSpeeds η) {t : ℝ}
    (ht : 0 ≤ t) {n : ℕ} (hact : FlightState.ActiveAt V S (V.ofDeparture η hr.1 hr.2) n t) :
    FlightState.trajectory V S (V.ofDeparture η hr.1 hr.2) t =
      ((chainIterate V S (η, r) n).1.1,
        V.departureFlow (chainIterate V S (η, r) n).1
          ((chainIterate V S (η, r) n).2, t - chainTime V S (η, r) n)) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hact.1
  obtain ⟨hbe, hbs, hbreg, hbt⟩ := V.chainIterate_correspondence S η hr n b hb
  rw [FlightState.trajectory_eq V S (V.ofDeparture η hr.1 hr.2) ht hact hb]
  have hw0 : 0 ≤ t - chainTime V S (η, r) n := by
    have h := hact.2.1
    rw [hbt] at h
    linarith
  have hmem : ((chainIterate V S (η, r) n).2, t - chainTime V S (η, r) n) ∈
      V.departurePreImpact (chainIterate V S (η, r) n).1 := by
    refine ⟨hbreg, hw0, ?_⟩
    refine V.ofReal_lt_impactTime_of_le
      (V.durationSet_nonempty_of_regularSpeed hbreg) hw0 ?_
    intro hbdd
    have hbdd' : BddAbove (durationSet V b.edge b.state) := by rw [hbe, hbs]; exact hbdd
    obtain ⟨b', hb', -⟩ := FlightState.next_eq_some_of_bddAbove (V := V) S b hbdd'
    have hsucc : (FlightState.iterate V S (V.ofDeparture η hr.1 hr.2) (n + 1)).isSome := by
      rw [FlightState.iterate_succ, hb, Option.bind_some, hb']
      rfl
    have hlt := hact.2.2 hsucc
    rw [FlightState.impactReal_succ_eq_of_isSome (V := V) hb hsucc, hbt, hbe, hbs] at hlt
    linarith
  rw [V.departureFlow_of_mem hmem]
  refine Prod.ext hbe ?_
  have hcongr : FlightState.flightCurve V b
      (t - FlightState.impactReal V S (V.ofDeparture η hr.1 hr.2) n) =
      FlightState.flightCurve V
        (V.ofDeparture (chainIterate V S (η, r) n).1 hbreg.1 hbreg.2)
        (t - chainTime V S (η, r) n) := by
    rw [hbt]
    exact FlightState.flightCurve_congr (V := V) hbe hbs hw0
  rw [hcongr]
  exact (V.departureFlight_of_mem hbreg (t - chainTime V S (η, r) n)).symm

omit [Nonempty Γ.Edge] in
/-- The impact durations along the chain are nonnegative. -/
theorem departureDurationTotal_nonneg (η : Γ.EdgeEnd) (r : ℝ) :
    0 ≤ V.departureDurationTotal η r := by
  classical
  unfold departureDurationTotal
  by_cases hreg : r ∈ V.regularSpeeds η
  · rw [if_pos hreg]
    by_cases hbdd : BddAbove (durationSet V η.1 (departurePoint η r))
    · exact le_of_lt (FlightState.impactDuration_pos_of_bddAbove (V := V)
        (V.ofDeparture η hreg.1 hreg.2) hbdd)
    · rw [Real.sSup_of_not_bddAbove hbdd]
  · rw [if_neg hreg]

omit [Nonempty Γ.Edge] in
theorem chainTime_nonneg (c : Γ.EdgeEnd × ℝ) (n : ℕ) : 0 ≤ chainTime V S c n := by
  induction n with
  | zero => exact le_rfl
  | succ k ih =>
      rw [chainTime_succ]
      exact add_nonneg ih (V.departureDurationTotal_nonneg _ _)

/-- The **total departure trajectory**: the trajectory of the departure flight from the germ `η`
with inward speed `z.1` at time `z.2`, extended by the departure point off the regular speeds so
that it is a total map. -/
noncomputable def departureTrajectory (η : Γ.EdgeEnd) (z : ℝ × ℝ) : Γ.Edge × ℝ × ℝ := by
  classical
  exact if h : z.1 ∈ V.regularSpeeds η then
    FlightState.trajectory V S (V.ofDeparture η h.1 h.2) z.2
  else (η.1, departurePoint η z.1)

theorem departureTrajectory_of_mem {η : Γ.EdgeEnd} {z : ℝ × ℝ} (h : z.1 ∈ V.regularSpeeds η) :
    V.departureTrajectory S η z =
      FlightState.trajectory V S (V.ofDeparture η h.1 h.2) z.2 := by
  classical
  unfold departureTrajectory
  rw [dif_pos h]

theorem departureTrajectory_of_notMem {η : Γ.EdgeEnd} {z : ℝ × ℝ}
    (h : z.1 ∉ V.regularSpeeds η) :
    V.departureTrajectory S η z = (η.1, departurePoint η z.1) := by
  classical
  unfold departureTrajectory
  rw [dif_neg h]

/-- The cover of the speed–time plane used to prove the departure trajectory Borel. -/
private def trajCover (η : Γ.EdgeEnd) : ℕ → Set (ℝ × ℝ)
  | 0 => {z | z.1 ∉ V.regularSpeeds η} ∪ {z | z.2 < 0}
  | n + 1 => {z | z.1 ∈ V.regularSpeeds η ∧ ChainLands V S (η, z.1) n ∧
      chainTime V S (η, z.1) n ≤ z.2 ∧
      (ChainLands V S (η, z.1) (n + 1) → z.2 < chainTime V S (η, z.1) (n + 1))}

private theorem measurableSet_trajCover (η : Γ.EdgeEnd) (n : ℕ) :
    MeasurableSet (V.trajCover S η n) := by
  have hgmeas : Measurable fun z : ℝ × ℝ => ((η, z.1) : Γ.EdgeEnd × ℝ) :=
    measurable_const.prodMk measurable_fst
  cases n with
  | zero =>
      exact ((V.isOpen_regularSpeeds η).measurableSet.preimage measurable_fst).compl.union
        (measurableSet_lt measurable_snd measurable_const)
  | succ k =>
      refine MeasurableSet.inter
        ((V.isOpen_regularSpeeds η).measurableSet.preimage measurable_fst) ?_
      refine MeasurableSet.inter (V.measurableSet_chainLands S hgmeas k) ?_
      refine MeasurableSet.inter
        (measurableSet_le (V.measurable_chainTime S hgmeas k) measurable_snd) ?_
      have h1 := (V.measurableSet_chainLands S hgmeas (k + 1)).compl
      have h2 := measurableSet_lt measurable_snd (V.measurable_chainTime S hgmeas (k + 1))
      have heq : {z : ℝ × ℝ | ChainLands V S (η, z.1) (k + 1) →
          z.2 < chainTime V S (η, z.1) (k + 1)} =
          {z : ℝ × ℝ | ChainLands V S (η, z.1) (k + 1)}ᶜ ∪
          {z : ℝ × ℝ | z.2 < chainTime V S (η, z.1) (k + 1)} := by
        ext z
        simp only [mem_setOf_eq, mem_union, mem_compl_iff]
        constructor
        · intro h
          by_cases hc : ChainLands V S (η, z.1) (k + 1)
          · exact Or.inr (h hc)
          · exact Or.inl hc
        · rintro (h | h)
          · exact fun hc => absurd hc h
          · exact fun _ => h
      exact (h1.union h2).congr heq.symm

private theorem iUnion_trajCover (η : Γ.EdgeEnd) : (⋃ n, V.trajCover S η n) = univ := by
  refine eq_univ_of_forall fun z => ?_
  by_cases hreg : z.1 ∈ V.regularSpeeds η
  · rcases lt_or_ge z.2 0 with hneg | hpos
    · exact mem_iUnion.mpr ⟨0, Or.inr hneg⟩
    · obtain ⟨n, hn⟩ := FlightState.exists_activeAt V S (V.ofDeparture η hreg.1 hreg.2) hpos
      refine mem_iUnion.mpr ⟨n + 1, hreg, ?_⟩
      exact (V.activeAt_iff_chain S η hreg n z.2).mp hn
  · exact mem_iUnion.mpr ⟨0, Or.inl hreg⟩

/-- The chain formula for the departure trajectory, as a total map of the speed and the time. -/
noncomputable def chainFormula (η : Γ.EdgeEnd) (n : ℕ) (z : ℝ × ℝ) : Γ.Edge × ℝ × ℝ :=
  (((chainIterate V S (η, z.1) n).1.1 : Γ.Edge),
    V.departureFlow (chainIterate V S (η, z.1) n).1
      ((chainIterate V S (η, z.1) n).2, z.2 - chainTime V S (η, z.1) n))

theorem measurable_chainFormula (η : Γ.EdgeEnd) (n : ℕ) :
    Measurable (V.chainFormula S η n) := by
  have hgmeas : Measurable fun z : ℝ × ℝ => ((η, z.1) : Γ.EdgeEnd × ℝ) :=
    measurable_const.prodMk measurable_fst
  have hc : Measurable fun z : ℝ × ℝ => chainIterate V S (η, z.1) n :=
    V.measurable_chainIterate S hgmeas n
  have h1 : Measurable fun z : ℝ × ℝ => (chainIterate V S (η, z.1) n).1 :=
    measurable_fst.comp hc
  have h2 : Measurable fun z : ℝ × ℝ => (chainIterate V S (η, z.1) n).2 :=
    measurable_snd.comp hc
  have h3 : Measurable fun z : ℝ × ℝ => z.2 - chainTime V S (η, z.1) n :=
    measurable_snd.sub (V.measurable_chainTime S hgmeas n)
  have hedge : Measurable fun z : ℝ × ℝ => ((chainIterate V S (η, z.1) n).1.1 : Γ.Edge) :=
    (measurable_from_top (f := fun η' : Γ.EdgeEnd => η'.1)).comp h1
  have hflow : Measurable fun z : ℝ × ℝ =>
      V.departureFlow (chainIterate V S (η, z.1) n).1
        ((chainIterate V S (η, z.1) n).2, z.2 - chainTime V S (η, z.1) n) :=
    (V.measurable_departureFlowProd).comp (h1.prodMk (h2.prodMk h3))
  exact hedge.prodMk hflow

/-- **Lemma VI.4 for a departure flight.**  The trajectory of the departure flight from a germ is
a Borel function of the inward speed and the time. -/
theorem measurable_departureTrajectory (η : Γ.EdgeEnd) :
    Measurable (V.departureTrajectory S η) := by
  classical
  refine measurable_of_countable_cover_eq
    (F := fun n => if n = 0 then (fun z : ℝ × ℝ => (η.1, departurePoint η z.1))
      else V.chainFormula S η (n - 1))
    (V.measurableSet_trajCover S η) (V.iUnion_trajCover S η) ?_ ?_
  · intro n
    cases n with
    | zero =>
        change Measurable fun z : ℝ × ℝ => ((η.1, departurePoint η z.1) : Γ.Edge × ℝ × ℝ)
        exact measurable_const.prodMk
          ((continuous_departurePoint η).measurable.comp measurable_fst)
    | succ k =>
        change Measurable (V.chainFormula S η k)
        exact V.measurable_chainFormula S η k
  · intro n z hz
    cases n with
    | zero =>
        change V.departureTrajectory S η z = (η.1, departurePoint η z.1)
        rcases hz with hz | hz
        · exact V.departureTrajectory_of_notMem S hz
        · by_cases hreg : z.1 ∈ V.regularSpeeds η
          · rw [V.departureTrajectory_of_mem S hreg,
              FlightState.trajectory_of_neg S _ hz]
            rfl
          · exact V.departureTrajectory_of_notMem S hreg
    | succ k =>
        obtain ⟨hreg, hact⟩ := hz
        have ht : 0 ≤ z.2 := le_trans (V.chainTime_nonneg S _ k) hact.2.1
        have hA : FlightState.ActiveAt V S (V.ofDeparture η hreg.1 hreg.2) k z.2 :=
          (V.activeAt_iff_chain S η hreg k z.2).mpr hact
        change V.departureTrajectory S η z = V.chainFormula S η k z
        rw [V.departureTrajectory_of_mem S hreg, V.trajectory_chain_eq S η hreg ht hA]
        rfl

/-- The departure trajectory is jointly Borel in the germ, the speed and the time. -/
theorem measurable_departureTrajectoryProd :
    Measurable fun p : Γ.EdgeEnd × (ℝ × ℝ) => V.departureTrajectory S p.1 p.2 :=
  measurable_from_prod_countable_right fun η => V.measurable_departureTrajectory S η

-- keeping the guarded definition sealed stops `isDefEq` from unfolding the whole chain
attribute [irreducible] departureTrajectory

end Trajectory

end MechanicalPotential

end HamiltonianMetricGraphs
