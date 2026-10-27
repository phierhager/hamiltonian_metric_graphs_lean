/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.4: the Borel trajectory of an arbitrary graph phase point
-/

import HamiltonianMetricGraphs.ChainModel

/-!
# The trajectory of a graph phase point is Borel

`ChainModel.lean` makes the trajectory of a *departure* flight a Borel function of the departure
speed and the time.  A general point of the phase space is not a departure point: it is either
strictly inside an edge or a vertex state with outgoing momentum.  This module closes that gap and
produces the totally defined Borel map

* `pointTrajectory : (Γ.Edge × ℝ × ℝ) → ℝ → Γ.Edge × ℝ × ℝ`

which agrees with `FlightState.trajectory` for every flight state (`trajectory_eq_pointTrajectory`).

The ingredients for a start inside an edge mirror the departure family of `DepartureFlight.lean`
and `ChainModel.lean`:

* `interiorFlow`, `measurable_interiorFlow` — the pre-impact edge flow, made total;
* `measurable_landingStateTotal`, `measurable_interiorDurationTotal`,
  `measurable_interiorStepTotal` — the first impact data, made total;
* `interiorTrajectory` — one interior flight followed by the departure chain.

Composing with the Borel quotient chart of Lemma IV.4 gives the measurability half of
Theorem VI.5: the scattered evolution `Φ_t` is a Borel isomorphism of `P^Reg_S`
(`measurable_flow`, `flowMeasurableEquiv`).
-/

namespace HamiltonianMetricGraphs

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace MechanicalPotential

open PhysicalEdgeSegment

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The interior flow -/

/-- The pre-impact region is Borel: it is the countable union of the open no-impact sets at
rational times, crossed with the corresponding time intervals. -/
theorem measurableSet_preImpactRegion (e : Γ.Edge) : MeasurableSet (V.preImpactRegion e) := by
  have heq : V.preImpactRegion e =
      ⋃ q : {q : ℚ // 0 < (q : ℝ)},
        V.noImpactSet e (q : ℝ) ×ˢ Ico (0 : ℝ) ((q : ℚ) : ℝ) := by
    ext z
    constructor
    · rintro ⟨hreg, hw0, hlt⟩
      obtain ⟨d, -, hwd, hdT⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
      have hwd' : z.2 < d := by
        rcases lt_or_ge z.2 d with h | h
        · exact h
        · exact absurd (ENNReal.ofReal_le_ofReal h) (not_le.mpr hwd)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hwd'
      have hqpos : 0 < ((q : ℚ) : ℝ) := lt_of_le_of_lt hw0 hq1
      refine mem_iUnion.mpr ⟨⟨q, hqpos⟩, ⟨hreg, ?_⟩, ⟨hw0, hq1⟩⟩
      refine (V.ofReal_lt_impactTime_iff (V.durationSet_nonempty_of_interiorRegular hreg)
        hqpos).mp ?_
      exact lt_trans ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hqpos.le).mpr hq2) hdT
    · intro hmem
      obtain ⟨q, hxq, hwq⟩ := mem_iUnion.mp hmem
      refine ⟨hxq.1, hwq.1, ?_⟩
      have hT := (V.ofReal_lt_impactTime_iff (V.durationSet_nonempty_of_interiorRegular hxq.1)
        q.2).mpr hxq.2
      exact lt_trans ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hwq.1).mpr hwq.2) hT
  rw [heq]
  exact MeasurableSet.iUnion fun q =>
    (V.measurableSet_noImpactSet e q.2).prod measurableSet_Ico

/-- The **interior flow**: the edge flight map extended by the initial state outside the pre-impact
region, so that it becomes a total Borel map of the state and the time. -/
noncomputable def interiorFlow (e : Γ.Edge) (z : (ℝ × ℝ) × ℝ) : ℝ × ℝ := by
  classical
  exact if z ∈ V.preImpactRegion e then V.edgeFlight e z.1 z.2 else z.1

theorem interiorFlow_of_mem {e : Γ.Edge} {z : (ℝ × ℝ) × ℝ} (hz : z ∈ V.preImpactRegion e) :
    V.interiorFlow e z = V.edgeFlight e z.1 z.2 := by
  classical
  unfold interiorFlow
  rw [if_pos hz]

theorem interiorFlow_of_notMem {e : Γ.Edge} {z : (ℝ × ℝ) × ℝ} (hz : z ∉ V.preImpactRegion e) :
    V.interiorFlow e z = z.1 := by
  classical
  unfold interiorFlow
  rw [if_neg hz]

attribute [irreducible] interiorFlow

/-- **The interior flow is Borel**: continuous on the pre-impact region and the identity off it. -/
theorem measurable_interiorFlow (e : Γ.Edge) : Measurable (V.interiorFlow e) := by
  classical
  refine measurable_of_measurable_union_cover (V.preImpactRegion e) (V.preImpactRegion e)ᶜ
    (V.measurableSet_preImpactRegion e) (V.measurableSet_preImpactRegion e).compl
    (by rw [union_compl_self]) ?_ ?_
  · change Measurable ((V.preImpactRegion e).restrict (V.interiorFlow e))
    have heq : (V.preImpactRegion e).restrict (V.interiorFlow e) =
        (V.preImpactRegion e).restrict (fun z => V.edgeFlight e z.1 z.2) :=
      funext fun z => V.interiorFlow_of_mem z.2
    rw [heq]
    exact (continuousOn_iff_continuous_restrict.mp (V.continuousOn_edgeFlight e)).measurable
  · change Measurable ((V.preImpactRegion e)ᶜ.restrict (V.interiorFlow e))
    have heq : (V.preImpactRegion e)ᶜ.restrict (V.interiorFlow e) =
        fun z : ((V.preImpactRegion e)ᶜ : Set ((ℝ × ℝ) × ℝ)) => (z : (ℝ × ℝ) × ℝ).1 :=
      funext fun z => V.interiorFlow_of_notMem z.2
    rw [heq]
    exact measurable_fst.comp measurable_subtype_coe

/-! ### The first impact from an interior state, globalised -/

/-- The interior regular states whose flight actually lands: the complement, inside the interior
regular sector, of the states that survive every integer time. -/
theorem measurableSet_interiorLands (e : Γ.Edge) :
    MeasurableSet {x : ℝ × ℝ | x ∈ V.interiorRegular e ∧ BddAbove (durationSet V e x)} := by
  have heq : {x : ℝ × ℝ | x ∈ V.interiorRegular e ∧ BddAbove (durationSet V e x)} =
      V.interiorRegular e \ ⋂ n : ℕ, V.noImpactSet e (n + 1) := by
    ext x
    constructor
    · rintro ⟨hreg, hbdd⟩
      refine ⟨hreg, ?_⟩
      intro hmem
      obtain ⟨n, hn⟩ := exists_nat_gt (sSup (durationSet V e x))
      have h := (mem_iInter.mp hmem n).2 hbdd
      have hcast : ((n : ℕ) : ℝ) + 1 < sSup (durationSet V e x) := h
      linarith
    · rintro ⟨hreg, hnot⟩
      refine ⟨hreg, ?_⟩
      by_contra hbdd
      exact hnot (mem_iInter.mpr fun n => ⟨hreg, fun hb => absurd hb hbdd⟩)
  rw [heq]
  exact (V.isOpen_interiorRegular e).measurableSet.diff
    (MeasurableSet.iInter fun n => V.measurableSet_noImpactSet e (by positivity))

/-- Off the landing states the landing map is the initial state itself. -/
theorem landingState_of_not_lands {e : Γ.Edge} {x : ℝ × ℝ}
    (h : ¬ (x ∈ V.interiorRegular e ∧ BddAbove (durationSet V e x))) :
    V.landingState e x = x := by
  by_cases hreg : x ∈ V.interiorRegular e
  · have hbdd : ¬ BddAbove (durationSet V e x) := fun hb => h ⟨hreg, hb⟩
    rw [landingState, Real.sSup_of_not_bddAbove hbdd, V.edgeFlight_zero]
  · rw [landingState, V.edgeFlight_of_notMem hreg]

/-- The first impact duration of an interior state, cut to zero off the interior regular sector so
that it is a total function of the state. -/
noncomputable def interiorDurationTotal (e : Γ.Edge) (x : ℝ × ℝ) : ℝ := by
  classical
  exact if x ∈ V.interiorRegular e then sSup (durationSet V e x) else 0

theorem interiorDurationTotal_of_mem {e : Γ.Edge} {x : ℝ × ℝ} (hx : x ∈ V.interiorRegular e) :
    V.interiorDurationTotal e x = sSup (durationSet V e x) := by
  classical
  unfold interiorDurationTotal
  rw [if_pos hx]

/-- Off the landing states the total first impact duration vanishes. -/
theorem interiorDurationTotal_of_not_lands {e : Γ.Edge} {x : ℝ × ℝ}
    (h : ¬ (x ∈ V.interiorRegular e ∧ BddAbove (durationSet V e x))) :
    V.interiorDurationTotal e x = 0 := by
  classical
  unfold interiorDurationTotal
  by_cases hreg : x ∈ V.interiorRegular e
  · rw [if_pos hreg, Real.sSup_of_not_bddAbove (fun hb => h ⟨hreg, hb⟩)]
  · rw [if_neg hreg]

theorem interiorDurationTotal_nonneg (e : Γ.Edge) (x : ℝ × ℝ) :
    0 ≤ V.interiorDurationTotal e x := by
  classical
  unfold interiorDurationTotal
  by_cases hreg : x ∈ V.interiorRegular e
  · rw [if_pos hreg]
    by_cases hbdd : BddAbove (durationSet V e x)
    · exact le_of_lt (FlightState.impactDuration_pos_of_bddAbove (V := V)
        (FlightState.ofInterior V hreg.1 hreg.2) hbdd)
    · rw [Real.sSup_of_not_bddAbove hbdd]
  · rw [if_neg hreg]

/-- The cover of the edge phase plane used to globalise the first impact data. -/
private def interiorCover (e : Γ.Edge) : ℕ → Set (ℝ × ℝ)
  | 0 => {x | ¬ (x ∈ V.interiorRegular e ∧ BddAbove (durationSet V e x))}
  | n + 1 => V.impactSetAt e (n + 1)

private theorem measurableSet_interiorCover (e : Γ.Edge) (n : ℕ) :
    MeasurableSet (V.interiorCover e n) := by
  cases n with
  | zero => exact (V.measurableSet_interiorLands e).compl
  | succ k => exact V.measurableSet_impactSetAt e (by positivity)

private theorem iUnion_interiorCover (e : Γ.Edge) : (⋃ n, V.interiorCover e n) = univ := by
  refine eq_univ_of_forall fun x => ?_
  by_cases h : x ∈ V.interiorRegular e ∧ BddAbove (durationSet V e x)
  · obtain ⟨n, hn⟩ := exists_nat_gt (sSup (durationSet V e x))
    refine mem_iUnion.mpr ⟨n + 1, h.1, fun hmem => ?_⟩
    have hcast : ((n : ℕ) : ℝ) + 1 < sSup (durationSet V e x) := hmem.2 h.2
    linarith
  · exact mem_iUnion.mpr ⟨0, h⟩

/-- **The landing map is globally Borel.** -/
theorem measurable_landingStateTotal (e : Γ.Edge) : Measurable (V.landingState e) := by
  refine measurable_of_countable_cover (V.measurableSet_interiorCover e)
    (V.iUnion_interiorCover e) ?_
  intro n
  cases n with
  | zero =>
      have heq : (V.interiorCover e 0).restrict (V.landingState e) =
          (V.interiorCover e 0).restrict (id : (ℝ × ℝ) → ℝ × ℝ) :=
        funext fun s => V.landingState_of_not_lands s.2
      rw [heq]
      exact measurable_subtype_coe
  | succ k => exact V.measurable_landingState e ((k : ℝ) + 1)

/-- **The total first impact duration is globally Borel.** -/
theorem measurable_interiorDurationTotal (e : Γ.Edge) :
    Measurable (V.interiorDurationTotal e) := by
  refine measurable_of_countable_cover (V.measurableSet_interiorCover e)
    (V.iUnion_interiorCover e) ?_
  intro n
  cases n with
  | zero =>
      have heq : (V.interiorCover e 0).restrict (V.interiorDurationTotal e) = fun _ => (0 : ℝ) :=
        funext fun s => V.interiorDurationTotal_of_not_lands s.2
      rw [heq]
      exact measurable_const
  | succ k =>
      have heq : (V.interiorCover e (k + 1)).restrict (V.interiorDurationTotal e) =
          fun s : V.impactSetAt e ((k : ℝ) + 1) =>
            sSup (durationSet V e (s : ℝ × ℝ)) :=
        funext fun s => V.interiorDurationTotal_of_mem s.2.1
      rw [heq]
      exact V.measurable_impactDuration e ((k : ℝ) + 1)

variable (S : BorelEnergyPreservingScattering V)

/-- **The first impact step is globally Borel.** -/
theorem measurable_interiorStepTotal (e : Γ.Edge) : Measurable (interiorStep V S e) := by
  have hcov : Measurable fun x : ℝ × ℝ =>
      scatterCovector (V := V) S (edgeCovector (Γ := Γ) e (V.landingState e x)) :=
    (measurable_scatterCovector (V := V) S).comp
      ((measurable_edgeCovector (Γ := Γ) e).comp (V.measurable_landingStateTotal e))
  exact ((Γ.measurable_boundary_germ).comp hcov).prodMk
    (((Γ.measurable_boundary_momentum).comp hcov).abs)

/-- **Regularity of the first scattered departure.**  The departure after the first impact of an
interior flight carries the same energy, so it is a regular departure speed. -/
theorem interiorStep_mem_regularSpeeds {e : Γ.Edge} {x : ℝ × ℝ} (hx : x ∈ V.interiorRegular e)
    (hbdd : BddAbove (durationSet V e x)) :
    (interiorStep V S e x).2 ∈ V.regularSpeeds (interiorStep V S e x).1 := by
  have hbdd' : BddAbove (durationSet V (FlightState.ofInterior V hx.1 hx.2).edge
      (FlightState.ofInterior V hx.1 hx.2).state) := hbdd
  have hpos : 0 < (interiorStep V S e x).2 := by
    rw [interiorStep]
    exact abs_pos.mpr (scatterCovector (V := V) S
      (edgeCovector (Γ := Γ) e (V.landingState e x))).momentum_ne_zero
  refine ⟨hpos, ?_⟩
  obtain ⟨b, hb, -, hbenergy, -, -⟩ :=
    FlightState.next_eq_some_of_bddAbove (V := V) S (FlightState.ofInterior V hx.1 hx.2) hbdd'
  obtain ⟨he, hs⟩ := V.interiorStep_next S hx hbdd hb
  have heq : V.departureEnergy (interiorStep V S e x).1 (interiorStep V S e x).2 = b.energy := by
    rw [FlightState.energy_eq, he, hs]
    rfl
  rw [heq, hbenergy]
  exact hx.2

/-! ### The trajectory of a start inside an edge -/

section Interior

variable [Nonempty Γ.Edge]

/-- The states and times at which the first interior flight has already landed. -/
def interiorLanded (e : Γ.Edge) : Set ((ℝ × ℝ) × ℝ) :=
  {z | (z.1 ∈ V.interiorRegular e ∧ BddAbove (durationSet V e z.1)) ∧
    V.interiorDurationTotal e z.1 ≤ z.2}

omit [Nonempty Γ.Edge] in
theorem measurableSet_interiorLanded (e : Γ.Edge) : MeasurableSet (V.interiorLanded e) :=
  ((V.measurableSet_interiorLands e).preimage measurable_fst).inter
    (measurableSet_le ((V.measurable_interiorDurationTotal e).comp measurable_fst)
      measurable_snd)

/-- The **interior trajectory**: one interior flight, and from its impact onwards the departure
chain of `ChainModel.lean`. -/
noncomputable def interiorTrajectory (e : Γ.Edge) (z : (ℝ × ℝ) × ℝ) : Γ.Edge × ℝ × ℝ := by
  classical
  exact if z ∈ V.interiorLanded e then
    V.departureTrajectory S (interiorStep V S e z.1).1
      ((interiorStep V S e z.1).2, z.2 - V.interiorDurationTotal e z.1)
  else (e, V.interiorFlow e z)

theorem interiorTrajectory_of_mem {e : Γ.Edge} {z : (ℝ × ℝ) × ℝ} (hz : z ∈ V.interiorLanded e) :
    V.interiorTrajectory S e z =
      V.departureTrajectory S (interiorStep V S e z.1).1
        ((interiorStep V S e z.1).2, z.2 - V.interiorDurationTotal e z.1) := by
  classical
  unfold interiorTrajectory
  rw [if_pos hz]

theorem interiorTrajectory_of_notMem {e : Γ.Edge} {z : (ℝ × ℝ) × ℝ}
    (hz : z ∉ V.interiorLanded e) :
    V.interiorTrajectory S e z = (e, V.interiorFlow e z) := by
  classical
  unfold interiorTrajectory
  rw [if_neg hz]

attribute [irreducible] interiorTrajectory

theorem measurable_interiorTrajectory (e : Γ.Edge) :
    Measurable (V.interiorTrajectory S e) := by
  classical
  refine measurable_of_measurable_union_cover (V.interiorLanded e) (V.interiorLanded e)ᶜ
    (V.measurableSet_interiorLanded e) (V.measurableSet_interiorLanded e).compl
    (by rw [union_compl_self]) ?_ ?_
  · change Measurable ((V.interiorLanded e).restrict (V.interiorTrajectory S e))
    have heq : (V.interiorLanded e).restrict (V.interiorTrajectory S e) =
        (V.interiorLanded e).restrict (fun z : (ℝ × ℝ) × ℝ =>
          V.departureTrajectory S (interiorStep V S e z.1).1
            ((interiorStep V S e z.1).2, z.2 - V.interiorDurationTotal e z.1)) :=
      funext fun z => V.interiorTrajectory_of_mem S z.2
    rw [heq]
    have hstep : Measurable fun z : (ℝ × ℝ) × ℝ => interiorStep V S e z.1 :=
      (V.measurable_interiorStepTotal S e).comp measurable_fst
    have hmain : Measurable fun z : (ℝ × ℝ) × ℝ =>
        V.departureTrajectory S (interiorStep V S e z.1).1
          ((interiorStep V S e z.1).2, z.2 - V.interiorDurationTotal e z.1) :=
      (V.measurable_departureTrajectoryProd S).comp
        ((measurable_fst.comp hstep).prodMk ((measurable_snd.comp hstep).prodMk
          (measurable_snd.sub ((V.measurable_interiorDurationTotal e).comp measurable_fst))))
    exact hmain.comp measurable_subtype_coe
  · change Measurable ((V.interiorLanded e)ᶜ.restrict (V.interiorTrajectory S e))
    have heq : (V.interiorLanded e)ᶜ.restrict (V.interiorTrajectory S e) =
        (V.interiorLanded e)ᶜ.restrict (fun z : (ℝ × ℝ) × ℝ => (e, V.interiorFlow e z)) :=
      funext fun z => V.interiorTrajectory_of_notMem S z.2
    rw [heq]
    exact (measurable_const.prodMk (V.measurable_interiorFlow e)).comp measurable_subtype_coe

/-- **The interior trajectory computes the unified trajectory.** -/
theorem trajectory_eq_interiorTrajectory {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x ∈ V.interiorRegular e) {a : V.FlightState} (hae : a.edge = e) (has : a.state = x)
    {t : ℝ} (ht : 0 ≤ t) :
    FlightState.trajectory V S a t = V.interiorTrajectory S e (x, t) := by
  classical
  set a₀ : V.FlightState := FlightState.ofInterior V hx.1 hx.2 with ha₀
  have ha₀e : a₀.edge = e := rfl
  have ha₀s : a₀.state = x := rfl
  have hcongr : FlightState.trajectory V S a t = FlightState.trajectory V S a₀ t :=
    FlightState.trajectory_congr V S (by rw [hae, ha₀e]) (by rw [has, ha₀s]) ht
  rw [hcongr]
  have hne : (durationSet V e x).Nonempty := V.durationSet_nonempty_of_interiorRegular hx
  by_cases hbdd : BddAbove (durationSet V e x)
  · set T : ℝ := sSup (durationSet V e x) with hT
    have hTeq : V.interiorDurationTotal e x = T := V.interiorDurationTotal_of_mem hx
    obtain ⟨b, hb, -, -, -, -⟩ :=
      FlightState.next_eq_some_of_bddAbove (V := V) S a₀ (by rw [ha₀e, ha₀s]; exact hbdd)
    have hb1 : FlightState.iterate V S a₀ 1 = some b := by
      rw [FlightState.iterate_succ, FlightState.iterate_zero, Option.bind_some]; exact hb
    have hsucc : (FlightState.iterate V S a₀ 1).isSome := by rw [hb1]; rfl
    have hIR1 : FlightState.impactReal V S a₀ 1 = T := by
      rw [FlightState.impactReal_succ_eq_of_isSome (V := V)
        (FlightState.iterate_zero (V := V) S a₀) hsucc, FlightState.impactReal_zero,
        ha₀e, ha₀s, zero_add]
    by_cases hlt : t < T
    · -- still on the first flight
      have hnot : ((x, t) : (ℝ × ℝ) × ℝ) ∉ V.interiorLanded e := by
        rintro ⟨-, hle⟩
        rw [hTeq] at hle
        exact absurd hle (not_le.mpr hlt)
      rw [V.interiorTrajectory_of_notMem S hnot]
      have hpre : ((x, t) : (ℝ × ℝ) × ℝ) ∈ V.preImpactRegion e :=
        ⟨hx, ht, V.ofReal_lt_impactTime_of_le hne ht fun _ => hlt⟩
      rw [V.interiorFlow_of_mem hpre, V.edgeFlight_of_mem hx]
      have hact : FlightState.ActiveAt V S a₀ 0 t := by
        refine ⟨by rw [FlightState.iterate_zero]; rfl, ?_, fun _ => ?_⟩
        · rw [FlightState.impactReal_zero]; exact ht
        · rw [hIR1]; exact hlt
      rw [FlightState.trajectory_eq V S a₀ ht hact (FlightState.iterate_zero (V := V) S a₀),
        FlightState.impactReal_zero, sub_zero]
      rfl
    · -- the first impact has happened
      have hge : T ≤ t := not_lt.mp hlt
      have hmem : ((x, t) : (ℝ × ℝ) × ℝ) ∈ V.interiorLanded e := by
        refine ⟨⟨hx, hbdd⟩, ?_⟩
        rw [hTeq]; exact hge
      rw [V.interiorTrajectory_of_mem S hmem]
      obtain ⟨hbe, hbs⟩ := V.interiorStep_next S hx hbdd hb
      have hreg : (interiorStep V S e x).2 ∈ V.regularSpeeds (interiorStep V S e x).1 :=
        V.interiorStep_mem_regularSpeeds S hx hbdd
      have hw : (0 : ℝ) ≤ t - T := by linarith
      have hshift := FlightState.trajectory_shift_eq V S a₀ hb1 hw
      rw [hIR1] at hshift
      have harg : T + (t - T) = t := by ring
      rw [harg] at hshift
      have hde : (V.ofDeparture (interiorStep V S e x).1 hreg.1 hreg.2).edge =
          (interiorStep V S e x).1.1 := rfl
      have hds : (V.ofDeparture (interiorStep V S e x).1 hreg.1 hreg.2).state =
          departurePoint (interiorStep V S e x).1 (interiorStep V S e x).2 := rfl
      have hbcongr : FlightState.trajectory V S b (t - T) =
          FlightState.trajectory V S
            (V.ofDeparture (interiorStep V S e x).1 hreg.1 hreg.2) (t - T) :=
        FlightState.trajectory_congr V S (by rw [hbe, hde]) (by rw [hbs, hds]) hw
      change FlightState.trajectory V S a₀ t =
        V.departureTrajectory S (interiorStep V S e x).1
          ((interiorStep V S e x).2, t - V.interiorDurationTotal e x)
      rw [hshift, hbcongr, hTeq,
        V.departureTrajectory_of_mem S (z := ((interiorStep V S e x).2, t - T)) hreg]
  · -- the first flight never lands
    have hnot : ((x, t) : (ℝ × ℝ) × ℝ) ∉ V.interiorLanded e := by
      rintro ⟨⟨-, hb⟩, -⟩
      exact hbdd hb
    rw [V.interiorTrajectory_of_notMem S hnot]
    have hpre : ((x, t) : (ℝ × ℝ) × ℝ) ∈ V.preImpactRegion e :=
      ⟨hx, ht, V.ofReal_lt_impactTime_of_le hne ht fun hb => absurd hb hbdd⟩
    rw [V.interiorFlow_of_mem hpre, V.edgeFlight_of_mem hx]
    have hnext : FlightState.next (V := V) S a₀ = none :=
      (FlightState.next_eq_none_iff (V := V) S a₀).mpr (by rw [ha₀e, ha₀s]; exact hbdd)
    have hact : FlightState.ActiveAt V S a₀ 0 t := by
      refine ⟨by rw [FlightState.iterate_zero]; rfl, ?_, fun hs => ?_⟩
      · rw [FlightState.impactReal_zero]; exact ht
      · rw [FlightState.iterate_succ, FlightState.iterate_zero, Option.bind_some, hnext] at hs
        exact absurd hs (by simp)
    rw [FlightState.trajectory_eq V S a₀ ht hact (FlightState.iterate_zero (V := V) S a₀),
      FlightState.impactReal_zero, sub_zero]
    rfl

end Interior

/-! ### The trajectory of an arbitrary graph phase point -/

/-- The germ of a graph point sitting at a vertex of its edge. -/
noncomputable def pointGerm (y : Γ.Edge × ℝ × ℝ) : Γ.EdgeEnd := by
  classical
  exact if y.2.1 = 0 then (y.1, false) else (y.1, true)

theorem pointGerm_edge (y : Γ.Edge × ℝ × ℝ) : (pointGerm (Γ := Γ) y).1 = y.1 := by
  classical
  unfold pointGerm
  by_cases h : y.2.1 = 0
  · rw [if_pos h]
  · rw [if_neg h]

theorem measurable_pointGerm : Measurable (pointGerm (Γ := Γ)) := by
  classical
  have hzero : MeasurableSet {y : Γ.Edge × ℝ × ℝ | y.2.1 = 0} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton (0 : ℝ))
  refine measurable_of_measurable_union_cover {y : Γ.Edge × ℝ × ℝ | y.2.1 = 0}
    {y : Γ.Edge × ℝ × ℝ | y.2.1 = 0}ᶜ hzero hzero.compl (by rw [union_compl_self]) ?_ ?_
  · change Measurable ({y : Γ.Edge × ℝ × ℝ | y.2.1 = 0}.restrict (pointGerm (Γ := Γ)))
    have heq : {y : Γ.Edge × ℝ × ℝ | y.2.1 = 0}.restrict (pointGerm (Γ := Γ)) =
        fun s => ((s.val.1, false) : Γ.EdgeEnd) := by
      funext s
      change pointGerm (Γ := Γ) s.val = _
      unfold pointGerm
      have h : s.val.2.1 = (0 : ℝ) := s.2
      rw [if_pos h]
    rw [heq]
    exact (measurable_from_top (f := fun e : Γ.Edge => ((e, false) : Γ.EdgeEnd))).comp
      (measurable_fst.comp measurable_subtype_coe)
  · change Measurable ({y : Γ.Edge × ℝ × ℝ | y.2.1 = 0}ᶜ.restrict (pointGerm (Γ := Γ)))
    have heq : {y : Γ.Edge × ℝ × ℝ | y.2.1 = 0}ᶜ.restrict (pointGerm (Γ := Γ)) =
        fun s => ((s.val.1, true) : Γ.EdgeEnd) := by
      funext s
      change pointGerm (Γ := Γ) s.val = _
      unfold pointGerm
      have h : ¬ s.val.2.1 = (0 : ℝ) := s.2
      rw [if_neg h]
    rw [heq]
    exact (measurable_from_top (f := fun e : Γ.Edge => ((e, true) : Γ.EdgeEnd))).comp
      (measurable_fst.comp measurable_subtype_coe)

section Point

variable [Nonempty Γ.Edge]

/-- **The trajectory of a graph phase point**: the identity before time zero, the interior
trajectory for a start inside an edge, and the departure trajectory for a vertex start. -/
noncomputable def pointTrajectory (y : Γ.Edge × ℝ × ℝ) (t : ℝ) : Γ.Edge × ℝ × ℝ := by
  classical
  exact if t < 0 then y
    else if y.2 ∈ V.interiorRegular y.1 then V.interiorTrajectory S y.1 (y.2, t)
    else V.departureTrajectory S (pointGerm y) (|y.2.2|, t)

theorem pointTrajectory_of_neg (y : Γ.Edge × ℝ × ℝ) {t : ℝ} (ht : t < 0) :
    V.pointTrajectory S y t = y := by
  classical
  unfold pointTrajectory
  rw [if_pos ht]

theorem pointTrajectory_of_interior {y : Γ.Edge × ℝ × ℝ} (hy : y.2 ∈ V.interiorRegular y.1)
    {t : ℝ} (ht : 0 ≤ t) :
    V.pointTrajectory S y t = V.interiorTrajectory S y.1 (y.2, t) := by
  classical
  unfold pointTrajectory
  rw [if_neg (not_lt.mpr ht), if_pos hy]

theorem pointTrajectory_of_not_interior {y : Γ.Edge × ℝ × ℝ}
    (hy : y.2 ∉ V.interiorRegular y.1) {t : ℝ} (ht : 0 ≤ t) :
    V.pointTrajectory S y t = V.departureTrajectory S (pointGerm y) (|y.2.2|, t) := by
  classical
  unfold pointTrajectory
  rw [if_neg (not_lt.mpr ht), if_neg hy]

/-- **The trajectory of an outgoing flight state in germ–speed coordinates.** -/
theorem trajectory_eq_departureTrajectory_of_isOutgoing {a : V.FlightState}
    (hout : a.IsOutgoing) {t : ℝ} (ht : 0 ≤ t) :
    FlightState.trajectory V S a t =
      V.departureTrajectory S (pointGerm (a.edge, a.state)) (|a.state.2|, t) := by
  classical
  obtain ⟨η₀, hη₀, hstate, hsign⟩ := hout
  rcases η₀ with ⟨e, bo⟩
  change e = a.edge at hη₀
  have hne : a.state.2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsign
    exact lt_irrefl 0 hsign
  have hdp : departurePoint ((e, bo) : Γ.EdgeEnd) |a.state.2| = a.state := by
    refine Prod.ext hstate.symm ?_
    change -(FiniteMetricGraph.EdgeEnd.sign Γ ((e, bo) : Γ.EdgeEnd) * |a.state.2|) = a.state.2
    cases bo
    · rw [Γ.edgeEnd_sign_false] at hsign
      rw [Γ.edgeEnd_sign_false, abs_of_pos (by linarith : (0 : ℝ) < a.state.2)]
      ring
    · rw [Γ.edgeEnd_sign_true] at hsign
      rw [Γ.edgeEnd_sign_true, abs_of_neg (by linarith : a.state.2 < 0)]
      ring
  have hreg : |a.state.2| ∈ V.regularSpeeds ((e, bo) : Γ.EdgeEnd) := by
    refine ⟨abs_pos.mpr hne, ?_⟩
    have hE : V.departureEnergy ((e, bo) : Γ.EdgeEnd) |a.state.2| =
        V.hamiltonian e a.state.1 a.state.2 := by
      rw [departureEnergy, hdp]
    rw [hE, hη₀]
    exact a.regular
  have hgerm : pointGerm (Γ := Γ) (a.edge, a.state) = ((e, bo) : Γ.EdgeEnd) := by
    unfold pointGerm
    cases bo
    · rw [Γ.edgeEnd_coordinate_false] at hstate
      rw [if_pos hstate, hη₀]
    · rw [Γ.edgeEnd_coordinate_true] at hstate
      rw [if_neg (by rw [hstate]; exact ne_of_gt (Γ.length_pos e)), hη₀]
  rw [hgerm, V.departureTrajectory_of_mem S (z := (|a.state.2|, t)) hreg]
  exact FlightState.trajectory_congr V S (a₁ := a)
    (a₂ := V.ofDeparture ((e, bo) : Γ.EdgeEnd) hreg.1 hreg.2) hη₀.symm hdp.symm ht

/-- **Lemma VI.4.**  The unified trajectory of any flight state is computed by the totally
defined map `pointTrajectory` of its edge, its initial state and the time. -/
theorem trajectory_eq_pointTrajectory (a : V.FlightState) (t : ℝ) :
    FlightState.trajectory V S a t = V.pointTrajectory S (a.edge, a.state) t := by
  classical
  by_cases ht : 0 ≤ t
  · by_cases hint : a.state ∈ V.interiorRegular a.edge
    · rw [V.pointTrajectory_of_interior S (y := (a.edge, a.state)) hint ht]
      exact V.trajectory_eq_interiorTrajectory S hint rfl rfl ht
    · rw [V.pointTrajectory_of_not_interior S (y := (a.edge, a.state)) hint ht]
      refine V.trajectory_eq_departureTrajectory_of_isOutgoing S ?_ ht
      rcases FlightState.interior_or_isOutgoing (V := V) a with hpos | hout
      · exact absurd ⟨hpos, a.regular⟩ hint
      · exact hout
  · rw [V.pointTrajectory_of_neg S _ (not_le.mp ht),
      FlightState.trajectory_of_neg S a (not_le.mp ht)]

/-- **The time-`t` graph trajectory is Borel** in the phase point. -/
theorem measurable_pointTrajectory (t : ℝ) :
    Measurable fun y : Γ.Edge × ℝ × ℝ => V.pointTrajectory S y t := by
  classical
  by_cases ht : 0 ≤ t
  · refine measurable_from_prod_countable_right fun e => ?_
    refine measurable_of_measurable_union_cover (V.interiorRegular e) (V.interiorRegular e)ᶜ
      (V.isOpen_interiorRegular e).measurableSet (V.isOpen_interiorRegular e).measurableSet.compl
      (by rw [union_compl_self]) ?_ ?_
    · change Measurable ((V.interiorRegular e).restrict
        (fun x : ℝ × ℝ => V.pointTrajectory S (e, x) t))
      have heq : (V.interiorRegular e).restrict
          (fun x : ℝ × ℝ => V.pointTrajectory S (e, x) t) =
          (V.interiorRegular e).restrict
            (fun x : ℝ × ℝ => V.interiorTrajectory S e (x, t)) :=
        funext fun s => V.pointTrajectory_of_interior S (y := (e, (s : ℝ × ℝ))) s.2 ht
      rw [heq]
      exact ((V.measurable_interiorTrajectory S e).comp
        (measurable_id.prodMk measurable_const)).comp measurable_subtype_coe
    · change Measurable ((V.interiorRegular e)ᶜ.restrict
        (fun x : ℝ × ℝ => V.pointTrajectory S (e, x) t))
      have heq : (V.interiorRegular e)ᶜ.restrict
          (fun x : ℝ × ℝ => V.pointTrajectory S (e, x) t) =
          (V.interiorRegular e)ᶜ.restrict
            (fun x : ℝ × ℝ =>
              V.departureTrajectory S (pointGerm (Γ := Γ) (e, x)) (|x.2|, t)) :=
        funext fun s => V.pointTrajectory_of_not_interior S (y := (e, (s : ℝ × ℝ))) s.2 ht
      rw [heq]
      have hmain : Measurable fun x : ℝ × ℝ =>
          V.departureTrajectory S (pointGerm (Γ := Γ) (e, x)) (|x.2|, t) :=
        (V.measurable_departureTrajectoryProd S).comp
          ((measurable_pointGerm.comp (measurable_const.prodMk measurable_id)).prodMk
            (measurable_snd.abs.prodMk measurable_const))
      exact hmain.comp measurable_subtype_coe
  · have heq : (fun y : Γ.Edge × ℝ × ℝ => V.pointTrajectory S y t) = id :=
      funext fun y => V.pointTrajectory_of_neg S y (not_le.mp ht)
    rw [heq]
    exact measurable_id

end Point

end MechanicalPotential

end HamiltonianMetricGraphs
