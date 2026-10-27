/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Theorem VIII.5 (b): the travel-time formula for the flight times of a regular shell
-/

import HamiltonianMetricGraphs.ShellCycles
import HamiltonianMetricGraphs.Examples

/-!
# The travel-time formula

Fix a shell-regular energy `E` and an admissible end `η` on the edge `e = η.1`, and let
`γ(u) = (q(u), p(u))`, `0 ≤ u ≤ t_E(η)`, be the flight departing `η` at energy `E`
(`germCurve`).  This module proves the second equality of (8.4),

`t_E(η) = ∫_{flight of η} |dq| / √(2(E - V_e(q)))`,

in three forms.

* **The general form** (`ofReal_flightTime_eq`, `lintegral_germCurve`): the flight splits, up to
  the Lebesgue-null set of its turning instants (`volume_germZero`), into its rightward part
  `p > 0` and its leftward part `p < 0` (`germSheet`), and on each part the substitution `u ↦ q(u)`
  turns `du` into `dq / |p| = dq / speedAt e E q` (`lintegral_germSheet`).  Hence
  `t_E(η) = ∫_{q(p>0)} dq/√(2(E-V_e)) + ∫_{q(p<0)} dq/√(2(E-V_e))`, and more generally
  `∫_0^{t_E(η)} G(γ(u)) du` is the corresponding sum of position integrals against the time
  density of Proposition VII.1.
* **A crossing flight** (`flightTime_eq_integral_of_crossing`): if `V_e < E` on the open edge, the
  flight crosses it, lands at the opposite end, and `t_E(η) = ∫_0^ℓ dq / speedAt e E q`.
* **A reflected flight** (`flightTime_eq_two_mul_integral_of_turning`): if the potential first
  reaches the level `E` at an interior point `t`, i.e. `V_e(t) = E` and `V_e < E` strictly between
  the end `a` of `η` and `t`, then the flight turns at `t`, comes back to `a`, and
  `t_E(η) = 2 |∫_a^t dq / speedAt e E q|`.
* **Every flight is of one of these two kinds** (`flightTime_eq_crossing_or_turning`): seen from
  its end, the potential either stays below `E` on the open edge or reaches `E` at a first interior
  point (`crossing_or_exists_turning`).

Two ingredients are used.  First, shell-regularity excludes interior critical points at level `E`
(`deriv_extension_ne_zero_of_shellRegular`): such a point is an equilibrium whose flight never
lands.
This is what makes the turning instants isolated, and what makes a turning point repel the flight
back.  Second, the flight curve is injective on `[0, t_E(η))` (`germCurve_injOn`): this follows
from the least-period statement of `ShellCycles.lean`, applied with the reflection law as an
auxiliary vertex law (the flight itself does not depend on the vertex law).

The integrals are written exactly as `∫ q in a..b, 1 / V.speedAt e E q`, the shape used for the
analyticity of the flight times in the energy.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### Shell-regularity excludes interior critical points on the shell -/

/-- At an interior critical point of the potential the rest state is an equilibrium: the constant
curve is a physical edge segment of every positive duration. -/
theorem not_bddAbove_durationSet_of_critical {e : Γ.Edge} {q₀ : ℝ}
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) (Γ.length e)) (hcrit : deriv (V.extension e) q₀ = 0) :
    ¬ BddAbove (PhysicalEdgeSegment.durationSet V e (q₀, 0)) := by
  have hdom : q₀ ∈ V.domain e := V.closedEdge_subset_domain e (Ioo_subset_Icc_self hq₀)
  have hfield : V.edgeVectorField e (q₀, 0) = 0 := by
    simp [edgeVectorField, force, hcrit]
  rintro ⟨B, hB⟩
  let seg : V.PhysicalEdgeSegment e (q₀, 0) :=
    { duration := max B 0 + 1
      duration_pos := by positivity
      curve := fun _ => (q₀, 0)
      initial := rfl
      initial_physical := Ioo_subset_Icc_self hq₀
      physical := fun _ _ => Ioo_subset_Icc_self hq₀
      in_domain := fun _ _ => hdom
      integralCurve := fun _ _ => by rw [hfield]; exact hasDerivAt_const _ _
      interior_after_initial := fun _ _ => hq₀ }
  have h := hB (PhysicalEdgeSegment.mem_durationSet seg)
  change max B 0 + 1 ≤ B at h
  linarith [le_max_left B 0]

/-- **Shell-regularity excludes interior critical values.**  If `E` is shell-regular, the
potential has no critical point at level `E` inside an edge: such a point would be an equilibrium
of energy `E` whose flight never reaches a vertex. -/
theorem deriv_extension_ne_zero_of_shellRegular {E : ℝ} (hE : V.ShellRegular E) {e : Γ.Edge}
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo (0 : ℝ) (Γ.length e)) (hV : V.extension e q₀ = E) :
    deriv (V.extension e) q₀ ≠ 0 := by
  intro hcrit
  refine V.not_bddAbove_durationSet_of_critical hq₀ hcrit (hE.lands e (q₀, 0) ?_)
  simp [hamiltonian, hV]

/-- The speed of a state of energy `E` is the modulus of its momentum. -/
theorem speedAt_eq_abs_of_hamiltonian {e : Γ.Edge} {E q p : ℝ} (h : V.hamiltonian e q p = E) :
    V.speedAt e E q = |p| := by
  rw [← h, V.speedAt_hamiltonian]

/-! ### The departure flight curve -/

section Curve

variable {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E)

/-- The flight curve `γ(u) = (q(u), p(u))` departing the admissible end `η` at energy `E`; it is
the flight of Theorem VIII.5 on `0 ≤ u ≤ t_E(η)`. -/
noncomputable def germCurve : ℝ → ℝ × ℝ :=
  FlightState.flightCurve V (V.germFlight hE η hη)

theorem germCurve_zero : V.germCurve hE hη 0 = departurePoint η (V.germSpeed η E) :=
  FlightState.flightCurve_zero V _

theorem germCurve_continuousOn : ContinuousOn (V.germCurve hE hη) (Icc 0 (V.flightTime E η)) :=
  FlightState.flightCurve_continuousOn_Icc _ (fun _ => (V.germFlight_sSup hE η hη).ge)

theorem germCurve_hasDerivAt {u : ℝ} (hu : u ∈ Ioo 0 (V.flightTime E η)) :
    HasDerivAt (V.germCurve hE hη) (V.edgeVectorField η.1 (V.germCurve hE hη u)) u :=
  FlightState.flightCurve_hasDerivAt V _ hu.1
    (fun _ => by rw [V.germFlight_sSup hE η hη]; exact hu.2)

theorem germCurve_hasDerivAt_fst {u : ℝ} (hu : u ∈ Ioo 0 (V.flightTime E η)) :
    HasDerivAt (fun s => (V.germCurve hE hη s).1) (V.germCurve hE hη u).2 u :=
  V.edgeIntegralCurve_hasDerivAt_fst (V.germCurve_hasDerivAt hE hη hu)

theorem germCurve_hasDerivAt_snd {u : ℝ} (hu : u ∈ Ioo 0 (V.flightTime E η)) :
    HasDerivAt (fun s => (V.germCurve hE hη s).2) (V.force η.1 (V.germCurve hE hη u).1) u :=
  V.edgeIntegralCurve_hasDerivAt_snd (V.germCurve_hasDerivAt hE hη hu)

theorem germCurve_continuousOn_fst :
    ContinuousOn (fun s => (V.germCurve hE hη s).1) (Icc 0 (V.flightTime E η)) :=
  continuous_fst.comp_continuousOn (V.germCurve_continuousOn hE hη)

theorem germCurve_continuousOn_snd :
    ContinuousOn (fun s => (V.germCurve hE hη s).2) (Icc 0 (V.flightTime E η)) :=
  continuous_snd.comp_continuousOn (V.germCurve_continuousOn hE hη)

theorem germCurve_hamiltonian {u : ℝ} (hu : u ∈ Icc 0 (V.flightTime E η)) :
    V.hamiltonian η.1 (V.germCurve hE hη u).1 (V.germCurve hE hη u).2 = E := by
  have h := FlightState.flightCurve_hamiltonian_eq V (V.germFlight hE η hη) hu.1
    (fun _ => by rw [V.germFlight_sSup hE η hη]; exact hu.2)
  rw [V.germFlight_energy] at h
  exact h

theorem germCurve_physical {u : ℝ} (hu : u ∈ Icc 0 (V.flightTime E η)) :
    (V.germCurve hE hη u).1 ∈ Icc (0 : ℝ) (Γ.length η.1) :=
  FlightState.flightCurve_physical V _ hu.1 (fun _ => by rw [V.germFlight_sSup hE η hη]; exact hu.2)

theorem germCurve_interior {u : ℝ} (hu : u ∈ Ioo 0 (V.flightTime E η)) :
    (V.germCurve hE hη u).1 ∈ Ioo (0 : ℝ) (Γ.length η.1) :=
  FlightState.flightCurve_interior V _ hu.1 (fun _ => by rw [V.germFlight_sSup hE η hη]; exact hu.2)

/-- The potential along the flight never exceeds the energy. -/
theorem extension_germCurve_le {u : ℝ} (hu : u ∈ Icc 0 (V.flightTime E η)) :
    V.extension η.1 (V.germCurve hE hη u).1 ≤ E := by
  have h := V.germCurve_hamiltonian hE hη hu
  unfold hamiltonian at h
  nlinarith [sq_nonneg (V.germCurve hE hη u).2]

/-- Where the momentum does not vanish the flight is strictly below the energy level. -/
theorem extension_germCurve_lt {u : ℝ} (hu : u ∈ Icc 0 (V.flightTime E η))
    (hp : (V.germCurve hE hη u).2 ≠ 0) :
    V.extension η.1 (V.germCurve hE hη u).1 < E := by
  have h := V.germCurve_hamiltonian hE hη hu
  unfold hamiltonian at h
  have := pow_pos (abs_pos.mpr hp) 2
  rw [sq_abs] at this
  linarith

/-- Where the momentum vanishes the flight is on the level `E` of the potential. -/
theorem extension_germCurve_eq {u : ℝ} (hu : u ∈ Icc 0 (V.flightTime E η))
    (hp : (V.germCurve hE hη u).2 = 0) :
    V.extension η.1 (V.germCurve hE hη u).1 = E := by
  have h := V.germCurve_hamiltonian hE hη hu
  unfold hamiltonian at h
  rw [hp] at h
  linarith

/-- The flight curve at the flight time is the landing point. -/
theorem germCurve_flightTime :
    V.germCurve hE hη (V.flightTime E η) = V.departureLanding η (V.germSpeed η E) := by
  rw [departureLanding, V.departureFlight_of_mem (V.germSpeed_mem_regularSpeeds hE hη),
    ← V.flightTime_eq_sSup hE hη]
  rfl

theorem germCurve_flightTime_eq_maximalEndpoint :
    V.germCurve hE hη (V.flightTime E η) =
      (V.germFlight hE η hη).segment.maximalEndpoint (V.germFlight_bddAbove hE η hη) := by
  rw [germCurve, ← V.germFlight_sSup hE η hη]
  exact FlightState.flightCurve_sSup _ _

/-- The flight lands at an end of its edge. -/
theorem germCurve_flightTime_fst :
    (V.germCurve hE hη (V.flightTime E η)).1 = 0 ∨
      (V.germCurve hE hη (V.flightTime E η)).1 = Γ.length η.1 := by
  rw [V.germCurve_flightTime_eq_maximalEndpoint]
  exact PhysicalEdgeSegment.maximalEndpoint_coordinate_eq_zero_or_length _ _

/-- A flight landing at the left end of its edge arrives with negative momentum. -/
theorem germCurve_flightTime_snd_of_zero (h0 : (V.germCurve hE hη (V.flightTime E η)).1 = 0) :
    (V.germCurve hE hη (V.flightTime E η)).2 < 0 := by
  rw [V.germCurve_flightTime_eq_maximalEndpoint] at h0 ⊢
  exact PhysicalEdgeSegment.maximalEndpoint_left_momentum_neg _ _ (V.germFlight hE η hη).regular h0

/-- A flight landing at the right end of its edge arrives with positive momentum. -/
theorem germCurve_flightTime_snd_of_length
    (hl : (V.germCurve hE hη (V.flightTime E η)).1 = Γ.length η.1) :
    0 < (V.germCurve hE hη (V.flightTime E η)).2 := by
  rw [V.germCurve_flightTime_eq_maximalEndpoint] at hl ⊢
  exact PhysicalEdgeSegment.maximalEndpoint_right_momentum_pos _ _ (V.germFlight hE η hη).regular hl

/-- **The flight curve is injective** on `[0, t_E(η))`.  This is the least-period statement of
Theorem VIII.5 (b), applied with the reflection law as an auxiliary vertex law: the flight from
`η` does not depend on the vertex law. -/
theorem germCurve_injOn : InjOn (V.germCurve hE hη) (Ico 0 (V.flightTime E η)) := by
  haveI : Nonempty Γ.Edge := ⟨η.1⟩
  set S := reflectionScattering V
  intro u₁ hu₁ u₂ hu₂ h
  have hT : V.flightTime E η ≤ V.cyclePeriod S E η := by
    unfold cyclePeriod
    exact Finset.single_le_sum (f := V.flightTime E)
      (fun ζ _ => V.departureDurationTotal_nonneg _ _)
      (V.self_mem_germCycle S hE hη)
  apply V.suspension_injOn S hE hη ⟨hu₁.1, lt_of_lt_of_le hu₁.2 hT⟩ ⟨hu₂.1, lt_of_lt_of_le hu₂.2 hT⟩
  simp only
  rw [V.flow_departureClass S hE η hη hu₁.1, V.flow_departureClass S hE η hη hu₂.1]
  apply Subtype.ext
  rw [trajClass_val, trajClass_val]
  have h1 := V.germTrajectory_of_lt S hE hη hu₁.1 hu₁.2
  have h2 := V.germTrajectory_of_lt S hE hη hu₂.1 hu₂.2
  unfold germTrajectory at h1 h2
  rw [h1, h2]
  exact congrArg (fun x => graphClass V S (η.1, x)) h

/-! ### The turning instants are null -/

/-- The turning instants of the flight: the interior times at which the momentum vanishes. -/
def germZero : Set ℝ := {u | u ∈ Ioo 0 (V.flightTime E η) ∧ (V.germCurve hE hη u).2 = 0}

/-- **The turning instants are isolated, hence null.**  At a turning instant the position is an
interior point of the level `E`, where the force does not vanish by shell-regularity, so the
momentum crosses zero transversally. -/
theorem volume_germZero : volume (V.germZero hE hη) = 0 := by
  apply Set.Countable.measure_zero
  refine (countable_setOf_isolated_right_within (s := V.germZero hE hη)).mono ?_
  intro u hu
  refine ⟨hu, ?_⟩
  have hint := V.germCurve_interior hE hη hu.1
  have hlev := V.extension_germCurve_eq hE hη (Ioo_subset_Icc_self hu.1) hu.2
  have hd := V.deriv_extension_ne_zero_of_shellRegular hE hint hlev
  have hforce : V.force η.1 (V.germCurve hE hη u).1 ≠ 0 := by
    unfold force; exact neg_ne_zero.mpr hd
  have hne : ∀ᶠ s in 𝓝[≠] u, (V.germCurve hE hη s).2 ≠ 0 :=
    (V.germCurve_hasDerivAt_snd hE hη hu.1).eventually_ne hforce
  have h1 : ∀ᶠ s in 𝓝[V.germZero hE hη ∩ Ioi u] u, (V.germCurve hE hη s).2 ≠ 0 :=
    hne.filter_mono (nhdsWithin_mono u (fun s hs => ne_of_gt hs.2))
  have h2 : ∀ᶠ s in 𝓝[V.germZero hE hη ∩ Ioi u] u, (V.germCurve hE hη s).2 = 0 :=
    eventually_nhdsWithin_of_forall (fun s hs => hs.1.2)
  rw [← Filter.eventually_false_iff_eq_bot]
  filter_upwards [h1, h2] with s h1 h2 using h1 h2

/-! ### The two momentum sheets of a flight -/

/-- The part of the flight on the momentum sheet of sign `ε`: the interior times with
`ε p(u) > 0`. -/
def germSheet (ε : ℝ) : Set ℝ :=
  {u | u ∈ Ioo 0 (V.flightTime E η) ∧ 0 < ε * (V.germCurve hE hη u).2}

theorem isOpen_germSheet (ε : ℝ) : IsOpen (V.germSheet hE hη ε) := by
  have hcont : ContinuousOn (fun u => ε * (V.germCurve hE hη u).2) (Ioo 0 (V.flightTime E η)) :=
    ((V.germCurve_continuousOn_snd hE hη).mono Ioo_subset_Icc_self).const_smul ε
  exact hcont.isOpen_inter_preimage isOpen_Ioo (isOpen_Ioi (a := (0 : ℝ)))

theorem measurableSet_germSheet (ε : ℝ) : MeasurableSet (V.germSheet hE hη ε) :=
  (V.isOpen_germSheet hE hη ε).measurableSet

theorem germSheet_subset (ε : ℝ) : V.germSheet hE hη ε ⊆ Ioo 0 (V.flightTime E η) :=
  fun _ hu => hu.1

/-- On the sheet of sign `ε = ±1` the momentum is `ε` times the speed of the position. -/
theorem germCurve_snd_of_mem_germSheet {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {u : ℝ}
    (hu : u ∈ V.germSheet hE hη ε) :
    (V.germCurve hE hη u).2 = ε * V.speedAt η.1 E (V.germCurve hE hη u).1 := by
  rw [V.speedAt_eq_abs_of_hamiltonian (V.germCurve_hamiltonian hE hη (Ioo_subset_Icc_self hu.1))]
  have h := hu.2
  rcases hε with rfl | rfl
  · rw [abs_of_pos (by linarith), one_mul]
  · rw [abs_of_neg (by linarith)]; ring

/-- The position is injective on each momentum sheet. -/
theorem injOn_germSheet {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    InjOn (fun u => (V.germCurve hE hη u).1) (V.germSheet hE hη ε) := by
  intro u₁ hu₁ u₂ hu₂ h
  simp only at h
  apply V.germCurve_injOn hE hη (Ioo_subset_Ico_self hu₁.1) (Ioo_subset_Ico_self hu₂.1)
  refine Prod.ext h ?_
  rw [V.germCurve_snd_of_mem_germSheet hE hη hε hu₁, V.germCurve_snd_of_mem_germSheet hE hη hε hu₂,
    h]

/-- **The substitution `u ↦ q(u)` on a momentum sheet.**  On the sheet of sign `ε`, the flight time
`du` becomes the time density `dq / speedAt e E q` of Proposition VII.1. -/
theorem lintegral_germSheet {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (G : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ u in V.germSheet hE hη ε, G (V.germCurve hE hη u) =
      ∫⁻ x in (fun u => (V.germCurve hE hη u).1) '' V.germSheet hE hη ε,
        V.timeDensity η.1 E x * G (x, ε * V.speedAt η.1 E x) := by
  rw [lintegral_image_eq_lintegral_abs_deriv_mul (V.measurableSet_germSheet hE hη ε)
    (fun u hu => (V.germCurve_hasDerivAt_fst hE hη hu.1).hasDerivWithinAt)
    (V.injOn_germSheet hE hη hε)]
  refine setLIntegral_congr_fun (V.measurableSet_germSheet hE hη ε) (fun u hu => ?_)
  have hsnd := V.germCurve_snd_of_mem_germSheet hE hη hε hu
  have hspeed := V.speedAt_eq_abs_of_hamiltonian
    (V.germCurve_hamiltonian hE hη (Ioo_subset_Icc_self hu.1))
  have hp : (V.germCurve hE hη u).2 ≠ 0 := by
    intro h0; have := hu.2; rw [h0, mul_zero] at this; exact lt_irrefl _ this
  have habs : 0 < |(V.germCurve hE hη u).2| := abs_pos.mpr hp
  rw [timeDensity, hspeed, ← mul_assoc, ← ENNReal.ofReal_mul habs.le, mul_one_div_cancel habs.ne',
    ENNReal.ofReal_one, one_mul, ← hspeed, ← hsnd]

/-- The flight interval is the union of the two momentum sheets and the turning instants. -/
theorem Ioo_eq_germSheet_union :
    Ioo 0 (V.flightTime E η) =
      V.germSheet hE hη 1 ∪ V.germSheet hE hη (-1) ∪ V.germZero hE hη := by
  ext u
  simp only [mem_union, germSheet, germZero, mem_setOf_eq]
  constructor
  · intro hu
    rcases lt_trichotomy (V.germCurve hE hη u).2 0 with h | h | h
    · left; right; exact ⟨hu, by linarith⟩
    · right; exact ⟨hu, h⟩
    · left; left; exact ⟨hu, by linarith⟩
  · rintro ((h | h) | h) <;> exact h.1

/-- **The general travel-time formula.**  Integrating along the flight is integrating over the
positions of its two momentum sheets against the time density of Proposition VII.1. -/
theorem lintegral_germCurve (G : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioo 0 (V.flightTime E η), G (V.germCurve hE hη u) =
      (∫⁻ x in (fun u => (V.germCurve hE hη u).1) '' V.germSheet hE hη 1,
          V.timeDensity η.1 E x * G (x, 1 * V.speedAt η.1 E x)) +
        ∫⁻ x in (fun u => (V.germCurve hE hη u).1) '' V.germSheet hE hη (-1),
          V.timeDensity η.1 E x * G (x, -1 * V.speedAt η.1 E x) := by
  have hdisj : Disjoint (V.germSheet hE hη 1) (V.germSheet hE hη (-1)) := by
    rw [Set.disjoint_left]
    intro u h1 h2
    have := h1.2; have := h2.2; linarith
  have hae : (Ioo 0 (V.flightTime E η) : Set ℝ) =ᵐ[volume]
      (V.germSheet hE hη 1 ∪ V.germSheet hE hη (-1) : Set ℝ) := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null (fun u hu => ?_) (V.volume_germZero hE hη)
      have h1 := hu.1
      rw [V.Ioo_eq_germSheet_union hE hη] at h1
      rcases h1 with h1 | h1
      · exact absurd h1 hu.2
      · exact h1
    · rw [sdiff_eq_empty.mpr (union_subset (V.germSheet_subset hE hη 1)
        (V.germSheet_subset hE hη (-1))), measure_empty]
  rw [setLIntegral_congr hae, lintegral_union (V.measurableSet_germSheet hE hη (-1)) hdisj,
    V.lintegral_germSheet hE hη (Or.inl rfl), V.lintegral_germSheet hE hη (Or.inr rfl)]

/-- **The travel-time formula, general form.**  The flight time is the sum of the time-density
masses of the positions swept by the two momentum sheets of the flight. -/
theorem ofReal_flightTime_eq :
    ENNReal.ofReal (V.flightTime E η) =
      (∫⁻ x in (fun u => (V.germCurve hE hη u).1) '' V.germSheet hE hη 1,
          V.timeDensity η.1 E x) +
        ∫⁻ x in (fun u => (V.germCurve hE hη u).1) '' V.germSheet hE hη (-1),
          V.timeDensity η.1 E x := by
  have h := V.lintegral_germCurve hE hη (fun _ => 1)
  simp only [mul_one, setLIntegral_const, one_mul, Real.volume_Ioo, sub_zero] at h
  exact h

end Curve

/-! ### Interval integrals of the reciprocal speed -/

/-- On an interval of the classically allowed region, the interval integral of the reciprocal
speed is the mass of the time density of Proposition VII.1. -/
theorem integral_one_div_speedAt_eq_toReal {e : Γ.Edge} {E a b : ℝ} (hab : a ≤ b)
    (hsub : Ioo a b ⊆ Icc 0 (Γ.length e)) (hlt : ∀ x ∈ Ioo a b, V.extension e x < E) :
    ∫ x in a..b, 1 / V.speedAt e E x = (∫⁻ x in Ioo a b, V.timeDensity e E x).toReal := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    integral_eq_lintegral_of_nonneg_ae]
  · rfl
  · filter_upwards with x
    exact one_div_nonneg.mpr (V.speedAt_nonneg e E x)
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioo
    refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_const.div (V.continuousAt_speedAt e (V.closedEdge_subset_domain e (hsub hx)))
      (ne_of_gt (V.speedAt_pos e (hlt x hx)))

/-- The absolute interval integral of the reciprocal speed between two points of an edge, across
the classically allowed region between them. -/
theorem abs_integral_one_div_speedAt_eq_toReal {e : Γ.Edge} {E a b : ℝ}
    (hsub : uIoo a b ⊆ Icc 0 (Γ.length e)) (hlt : ∀ x ∈ uIoo a b, V.extension e x < E) :
    |∫ x in a..b, 1 / V.speedAt e E x| = (∫⁻ x in uIoo a b, V.timeDensity e E x).toReal := by
  rcases le_total a b with hab | hab
  · rw [uIoo_of_le hab] at hsub hlt ⊢
    rw [V.integral_one_div_speedAt_eq_toReal hab hsub hlt]
    exact abs_of_nonneg ENNReal.toReal_nonneg
  · rw [uIoo_of_ge hab] at hsub hlt ⊢
    rw [intervalIntegral.integral_symm, V.integral_one_div_speedAt_eq_toReal hab hsub hlt, abs_neg]
    exact abs_of_nonneg ENNReal.toReal_nonneg

/-! ### The crossing flight -/

section Crossing

/-- **The travel-time formula for a crossing flight.**  If the potential stays below the energy on
the whole open edge, the flight departing `η` crosses the edge, lands at the opposite end, and its
duration is `t_E(η) = ∫_0^ℓ dq / √(2(E - V_e(q)))`. -/
theorem flightTime_eq_integral_of_crossing {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E)
    (hcross : ∀ x ∈ Ioo (0 : ℝ) (Γ.length η.1), V.extension η.1 x < E) :
    V.flightTime E η = ∫ x in (0 : ℝ)..Γ.length η.1, 1 / V.speedAt η.1 E x ∧
      (V.departureLanding η (V.germSpeed η E)).1 =
        Γ.length η.1 - FiniteMetricGraph.EdgeEnd.coordinate Γ η := by
  set T := V.flightTime E η with hTdef
  have hT : 0 < T := V.flightTime_pos hE hη
  set q : ℝ → ℝ := fun u => (V.germCurve hE hη u).1 with hqdef
  have hpne : ∀ u ∈ Ioo 0 T, (V.germCurve hE hη u).2 ≠ 0 := by
    intro u hu h0
    have h1 := V.extension_germCurve_eq hE hη (Ioo_subset_Icc_self hu) h0
    have h2 := hcross _ (V.germCurve_interior hE hη hu)
    linarith
  have hqc : ContinuousOn q (Icc 0 T) := V.germCurve_continuousOn_fst hE hη
  have hrolle : ∀ u₁ u₂ : ℝ, 0 ≤ u₁ → u₁ < u₂ → u₂ ≤ T → q u₁ ≠ q u₂ := by
    intro u₁ u₂ h1 h12 h2 heq
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero h12 (hqc.mono (Icc_subset_Icc h1 h2)) heq
      (fun x hx => V.germCurve_hasDerivAt_fst hE hη
        ⟨lt_of_le_of_lt h1 hx.1, lt_of_lt_of_le hx.2 h2⟩)
    exact hpne c ⟨lt_of_le_of_lt h1 hc.1, lt_of_lt_of_le hc.2 h2⟩ hc0
  have hinj : InjOn q (Ioo 0 T) := by
    intro u₁ hu₁ u₂ hu₂ h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hrolle u₁ u₂ hu₁.1.le hlt hu₂.2.le h
    · exact hrolle u₂ u₁ hu₂.1.le hlt hu₁.2.le h.symm
  have hq0 : q 0 = FiniteMetricGraph.EdgeEnd.coordinate Γ η := by
    simp only [hqdef]; rw [V.germCurve_zero]; rfl
  have hl := Γ.length_pos η.1
  have hqT : q T = Γ.length η.1 - q 0 := by
    have hne := hrolle 0 T le_rfl hT le_rfl
    rcases edgeEnd_coordinate_mem η with h0 | h0 <;>
      rcases V.germCurve_flightTime_fst hE hη with h1 | h1 <;>
      · simp only [hqdef] at hne hq0 ⊢
        rw [hq0] at hne ⊢
        rw [h0] at hne ⊢
        rw [h1] at hne ⊢
        first | exact absurd rfl hne | ring
  have himage : q '' Ioo 0 T = Ioo 0 (Γ.length η.1) := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact V.germCurve_interior hE hη hu
    · rcases edgeEnd_coordinate_mem η with h0 | h0
      · have h := intermediate_value_Ioo hT.le hqc
        rw [hqT, hq0, h0, sub_zero] at h
        exact h
      · have h := intermediate_value_Ioo' hT.le hqc
        rw [hqT, hq0, h0, sub_self] at h
        exact h
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun u hu => (V.germCurve_hasDerivAt_fst hE hη hu).hasDerivWithinAt) hinj
    (V.timeDensity η.1 E)
  rw [himage] at hcv
  have hone : ∫⁻ u in Ioo 0 T, ENNReal.ofReal |(V.germCurve hE hη u).2| *
      V.timeDensity η.1 E (q u) = ENNReal.ofReal T := by
    have hvol : ENNReal.ofReal T = ∫⁻ _ in Ioo 0 T, (1 : ℝ≥0∞) := by
      rw [setLIntegral_one, Real.volume_Ioo, sub_zero]
    rw [hvol]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
    have hspeed := V.speedAt_eq_abs_of_hamiltonian
      (V.germCurve_hamiltonian hE hη (Ioo_subset_Icc_self hu))
    have habs : 0 < |(V.germCurve hE hη u).2| := abs_pos.mpr (hpne u hu)
    rw [timeDensity, hspeed, ← ENNReal.ofReal_mul habs.le, mul_one_div_cancel habs.ne',
      ENNReal.ofReal_one]
  rw [hone] at hcv
  refine ⟨?_, ?_⟩
  · rw [V.integral_one_div_speedAt_eq_toReal (Γ.length_pos η.1).le Ioo_subset_Icc_self hcross,
      hcv, ENNReal.toReal_ofReal hT.le]
  · rw [← V.germCurve_flightTime hE hη]
    exact hqT.trans (by rw [hq0])

end Crossing

/-! ### Simple turning points -/

/-- Beyond a simple turning point approached from the left the potential exceeds the energy. -/
theorem exists_extension_gt_right {e : Γ.Edge} {E t b : ℝ} (hbt : b < t) (ht : t ∈ V.domain e)
    (hVt : V.extension e t = E) (hd : deriv (V.extension e) t ≠ 0)
    (hlt : ∀ x ∈ Ioo b t, V.extension e x < E) :
    ∃ δ > 0, ∀ x ∈ Ioo t (t + δ), E < V.extension e x := by
  set f : ℝ → ℝ := fun x => V.extension e x - E with hf
  have hdiff : DifferentiableAt ℝ (V.extension e) t :=
    (V.extension_contDiffAt_of_mem ht).differentiableAt (by norm_num)
  have hderiv : deriv f t = deriv (V.extension e) t := by
    rw [hf, deriv_sub_const]
  have hft : f t = 0 := by rw [hf]; simp [hVt]
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · exfalso
    have hev := eventually_nhdsWithin_sign_eq_of_deriv_neg (by rw [hderiv]; exact hneg) hft
    obtain ⟨δ, hδ, hspec⟩ := Metric.eventually_nhds_iff.mp hev
    set x := (max b (t - δ / 2) + t) / 2 with hx
    have hx1 : b < x := by
      rw [hx]; linarith [le_max_left b (t - δ / 2), max_lt hbt (by linarith : t - δ / 2 < t)]
    have hx2 : x < t := by
      rw [hx]; linarith [max_lt hbt (by linarith : t - δ / 2 < t)]
    have hdist : dist x t < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      rw [hx]; linarith [le_max_right b (t - δ / 2)]
    have hsign := hspec hdist
    rw [sign_pos (by linarith : (0 : ℝ) < t - x), sign_eq_one_iff] at hsign
    have := hlt x ⟨hx1, hx2⟩
    simp only [hf] at hsign
    linarith
  · have hev := eventually_nhdsWithin_sign_eq_of_deriv_pos (by rw [hderiv]; exact hpos) hft
    obtain ⟨δ, hδ, hspec⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have hdist : dist x t < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith [hx.1])]; linarith [hx.2]
    have hsign := hspec hdist
    rw [sign_pos (by linarith [hx.1] : (0 : ℝ) < x - t), sign_eq_one_iff] at hsign
    simp only [hf] at hsign
    linarith

/-- Beyond a simple turning point approached from the right the potential exceeds the energy. -/
theorem exists_extension_gt_left {e : Γ.Edge} {E t b : ℝ} (htb : t < b)
    (hVt : V.extension e t = E) (hd : deriv (V.extension e) t ≠ 0)
    (hlt : ∀ x ∈ Ioo t b, V.extension e x < E) :
    ∃ δ > 0, ∀ x ∈ Ioo (t - δ) t, E < V.extension e x := by
  set f : ℝ → ℝ := fun x => V.extension e x - E with hf
  have hderiv : deriv f t = deriv (V.extension e) t := by
    rw [hf, deriv_sub_const]
  have hft : f t = 0 := by rw [hf]; simp [hVt]
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have hev := eventually_nhdsWithin_sign_eq_of_deriv_neg (by rw [hderiv]; exact hneg) hft
    obtain ⟨δ, hδ, hspec⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have hdist : dist x t < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith [hx.2])]; linarith [hx.1]
    have hsign := hspec hdist
    rw [sign_pos (by linarith [hx.2] : (0 : ℝ) < t - x), sign_eq_one_iff] at hsign
    simp only [hf] at hsign
    linarith
  · exfalso
    have hev := eventually_nhdsWithin_sign_eq_of_deriv_pos (by rw [hderiv]; exact hpos) hft
    obtain ⟨δ, hδ, hspec⟩ := Metric.eventually_nhds_iff.mp hev
    set x := (min b (t + δ / 2) + t) / 2 with hx
    have hm : t < min b (t + δ / 2) := lt_min htb (by linarith)
    have hx1 : x < b := by
      rw [hx]; linarith [min_le_left b (t + δ / 2)]
    have hx2 : t < x := by
      rw [hx]; linarith
    have hdist : dist x t < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      rw [hx]; linarith [min_le_right b (t + δ / 2)]
    have hsign := hspec hdist
    rw [sign_pos (by linarith : (0 : ℝ) < x - t), sign_eq_one_iff] at hsign
    have := hlt x ⟨hx2, hx1⟩
    simp only [hf] at hsign
    linarith

theorem mem_uIoo_of_mem_uIcc {a b x : ℝ} (h : x ∈ uIcc a b) (ha : x ≠ a) (hb : x ≠ b) :
    x ∈ uIoo a b := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at h
    rw [uIoo_of_le hab]
    exact ⟨lt_of_le_of_ne h.1 (Ne.symm ha), lt_of_le_of_ne h.2 hb⟩
  · rw [uIcc_of_ge hab] at h
    rw [uIoo_of_ge hab]
    exact ⟨lt_of_le_of_ne h.1 (Ne.symm hb), lt_of_le_of_ne h.2 ha⟩

/-- The intermediate value theorem for an unordered open interval of values. -/
theorem uIoo_subset_image_Ioo {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) : uIoo (f a) (f b) ⊆ f '' Ioo a b := by
  rcases le_total (f a) (f b) with h | h
  · rw [uIoo_of_le h]; exact intermediate_value_Ioo hab hf
  · rw [uIoo_of_ge h]; exact intermediate_value_Ioo' hab hf

/-! ### The reflected flight -/

section Reflection

/-- **The core of the reflection case.**  A flight which stays between its end `a` and a point
`t` where the potential reaches the energy, which leaves and comes back to `a`, sweeps the open
interval between `a` and `t` exactly once on each momentum sheet. -/
theorem image_germSheet_eq_of_turning {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {a t σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (ha : a ∉ Ioo (0 : ℝ) (Γ.length η.1)) (hVa : V.extension η.1 a < E)
    (hVt : V.extension η.1 t = E) (hJ : ∀ x ∈ uIoo a t, V.extension η.1 x < E)
    (hconf : ∀ u ∈ Icc 0 (V.flightTime E η), (V.germCurve hE hη u).1 ∈ uIcc a t)
    (hq0 : (V.germCurve hE hη 0).1 = a) (hqT : (V.germCurve hE hη (V.flightTime E η)).1 = a)
    (hp0 : 0 < σ * (V.germCurve hE hη 0).2)
    (hpT : σ * (V.germCurve hE hη (V.flightTime E η)).2 < 0) :
    (fun u => (V.germCurve hE hη u).1) '' V.germSheet hE hη σ = uIoo a t ∧
      (fun u => (V.germCurve hE hη u).1) '' V.germSheet hE hη (-σ) = uIoo a t := by
  set T := V.flightTime E η with hTdef
  have hT : 0 < T := V.flightTime_pos hE hη
  set q : ℝ → ℝ := fun u => (V.germCurve hE hη u).1 with hqdef
  set p : ℝ → ℝ := fun u => (V.germCurve hE hη u).2 with hpdef
  have hqc : ContinuousOn q (Icc 0 T) := V.germCurve_continuousOn_fst hE hη
  have hpc : ContinuousOn p (Icc 0 T) := V.germCurve_continuousOn_snd hE hη
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hgc : ContinuousOn (fun u => σ * p u) (Icc 0 T) := hpc.const_smul σ
  -- the turning instants of the closed flight interval
  set Z : Set ℝ := Icc 0 T ∩ p ⁻¹' {0} with hZ
  have hZclosed : IsClosed Z := hpc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZne : Z.Nonempty := by
    obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc' hT.le hgc ⟨hpT.le, hp0.le⟩
    exact ⟨w, hw, (mul_eq_zero.mp hw0).resolve_left hσ0⟩
  have hZbb : BddBelow Z := ⟨0, fun u hu => hu.1.1⟩
  have hZba : BddAbove Z := ⟨T, fun u hu => hu.1.2⟩
  set z₁ := sInf Z with hz₁def
  set z₂ := sSup Z with hz₂def
  have hz₁ : z₁ ∈ Z := hZclosed.csInf_mem hZne hZbb
  have hz₂ : z₂ ∈ Z := hZclosed.csSup_mem hZne hZba
  -- before the first turning instant the flight moves away from `a`, after the last one towards it
  have hbefore : ∀ u ∈ Ico 0 z₁, 0 < σ * p u := by
    intro u hu
    by_contra hneg
    have huT : u ≤ T := le_trans hu.2.le hz₁.1.2
    obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc' hu.1 (hgc.mono (Icc_subset_Icc le_rfl huT))
      ⟨not_lt.mp hneg, hp0.le⟩
    have hwZ : w ∈ Z := ⟨⟨hw.1, le_trans hw.2 huT⟩, (mul_eq_zero.mp hw0).resolve_left hσ0⟩
    have := csInf_le hZbb hwZ
    linarith [hw.2, hu.2]
  have hafter : ∀ u ∈ Ioc z₂ T, σ * p u < 0 := by
    intro u hu
    by_contra hpos
    have hu0 : 0 ≤ u := le_trans hz₂.1.1 hu.1.le
    obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc' hu.2 (hgc.mono (Icc_subset_Icc hu0 le_rfl))
      ⟨hpT.le, not_lt.mp hpos⟩
    have hwZ : w ∈ Z := ⟨⟨le_trans hu0 hw.1, hw.2⟩, (mul_eq_zero.mp hw0).resolve_left hσ0⟩
    have := le_csSup hZba hwZ
    linarith [hw.1, hu.1]
  -- at a turning instant the flight is at `t`
  have hq0' : q 0 = a := hq0
  have hqT' : q T = a := hqT
  have hturn : ∀ z ∈ Z, q z = t := by
    intro z hz
    have hlev : V.extension η.1 (q z) = E := V.extension_germCurve_eq hE hη hz.1 hz.2
    by_contra hne
    have hna : q z ≠ a := by
      intro h; rw [h] at hlev; linarith
    have := hJ _ (mem_uIoo_of_mem_uIcc (hconf z hz.1) hna hne)
    linarith
  have hz₁pos : 0 < z₁ := by
    rcases eq_or_lt_of_le hz₁.1.1 with h | h
    · have h2 : p z₁ = 0 := hz₁.2
      rw [← h] at h2
      have h3 : 0 < σ * p 0 := hp0
      rw [h2, mul_zero] at h3
      exact absurd h3 (lt_irrefl 0)
    · exact h
  have hz₂T : z₂ < T := by
    rcases eq_or_lt_of_le hz₂.1.2 with h | h
    · have h2 : p z₂ = 0 := hz₂.2
      rw [h] at h2
      have h3 : σ * p T < 0 := hpT
      rw [h2, mul_zero] at h3
      exact absurd h3 (lt_irrefl 0)
    · exact h
  -- the image of each sheet is inside the open interval
  have hsub : ∀ ε, q '' V.germSheet hE hη ε ⊆ uIoo a t := by
    rintro ε _ ⟨u, hu, rfl⟩
    have hpu : p u ≠ 0 := by
      intro h0
      have h2 : 0 < ε * p u := hu.2
      rw [h0, mul_zero] at h2
      exact lt_irrefl _ h2
    have hlt := V.extension_germCurve_lt hE hη (Ioo_subset_Icc_self hu.1) hpu
    refine mem_uIoo_of_mem_uIcc (hconf u (Ioo_subset_Icc_self hu.1)) ?_ ?_
    · intro h; exact ha (h ▸ V.germCurve_interior hE hη hu.1)
    · intro h
      have hlt' : V.extension η.1 (q u) < E := hlt
      rw [h] at hlt'
      linarith
  refine ⟨Subset.antisymm (hsub σ) ?_, Subset.antisymm (hsub (-σ)) ?_⟩
  · intro x hx
    have hivt := uIoo_subset_image_Ioo hz₁.1.1 (hqc.mono (Icc_subset_Icc le_rfl hz₁.1.2))
    rw [hq0', hturn z₁ hz₁] at hivt
    obtain ⟨u, hu, rfl⟩ := hivt hx
    exact ⟨u, ⟨⟨hu.1, lt_of_lt_of_le hu.2 hz₁.1.2⟩, hbefore u ⟨hu.1.le, hu.2⟩⟩, rfl⟩
  · intro x hx
    have hivt := uIoo_subset_image_Ioo hz₂.1.2 (hqc.mono (Icc_subset_Icc hz₂.1.1 le_rfl))
    rw [hqT', hturn z₂ hz₂, uIoo_comm] at hivt
    obtain ⟨u, hu, rfl⟩ := hivt hx
    refine ⟨u, ⟨⟨lt_of_le_of_lt hz₂.1.1 hu.1, hu.2⟩, ?_⟩, rfl⟩
    have h2 : σ * p u < 0 := hafter u ⟨hu.1, hu.2.le⟩
    change 0 < -σ * p u
    linarith

/-- A flight starting below a simple turning point, beyond which the potential exceeds the
energy, stays below it. -/
theorem germCurve_le_of_turning_right {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {t δ : ℝ} (hδ : 0 < δ)
    (hbeyond : ∀ x ∈ Ioo t (t + δ), E < V.extension η.1 x)
    (hq0t : (V.germCurve hE hη 0).1 ≤ t) :
    ∀ u ∈ Icc 0 (V.flightTime E η), (V.germCurve hE hη u).1 ≤ t := by
  intro u hu
  by_contra hgt
  rw [not_le] at hgt
  set y := min (V.germCurve hE hη u).1 (t + δ / 2) with hy
  have hy1 : t < y := lt_min hgt (by linarith)
  have hy2 : y < t + δ := by linarith [min_le_right (V.germCurve hE hη u).1 (t + δ / 2)]
  obtain ⟨w, hw, hwy⟩ := intermediate_value_Icc hu.1
    ((V.germCurve_continuousOn_fst hE hη).mono (Icc_subset_Icc le_rfl hu.2))
    ⟨by linarith, min_le_left _ _⟩
  have hle := V.extension_germCurve_le hE hη ⟨hw.1, le_trans hw.2 hu.2⟩
  simp only at hwy
  rw [hwy] at hle
  linarith [hbeyond y ⟨hy1, hy2⟩]

/-- A flight starting above a simple turning point, below which the potential exceeds the
energy, stays above it. -/
theorem le_germCurve_of_turning_left {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {t δ : ℝ} (hδ : 0 < δ)
    (hbeyond : ∀ x ∈ Ioo (t - δ) t, E < V.extension η.1 x)
    (hq0t : t ≤ (V.germCurve hE hη 0).1) :
    ∀ u ∈ Icc 0 (V.flightTime E η), t ≤ (V.germCurve hE hη u).1 := by
  intro u hu
  by_contra hlt
  rw [not_le] at hlt
  set y := max (V.germCurve hE hη u).1 (t - δ / 2) with hy
  have hy1 : y < t := max_lt hlt (by linarith)
  have hy2 : t - δ < y := by linarith [le_max_right (V.germCurve hE hη u).1 (t - δ / 2)]
  obtain ⟨w, hw, hwy⟩ := intermediate_value_Icc' hu.1
    ((V.germCurve_continuousOn_fst hE hη).mono (Icc_subset_Icc le_rfl hu.2))
    ⟨le_max_left _ _, by linarith⟩
  have hle := V.extension_germCurve_le hE hη ⟨hw.1, le_trans hw.2 hu.2⟩
  simp only at hwy
  rw [hwy] at hle
  linarith [hbeyond y ⟨hy2, hy1⟩]

theorem edgeEnd_sign_of_coordinate_eq_zero {η : Γ.EdgeEnd}
    (h : FiniteMetricGraph.EdgeEnd.coordinate Γ η = 0) :
    FiniteMetricGraph.EdgeEnd.sign Γ η = -1 := by
  rcases η with ⟨e, b⟩
  cases b
  · rfl
  · exfalso
    rw [FiniteMetricGraph.edgeEnd_coordinate_true] at h
    linarith [Γ.length_pos e]

theorem edgeEnd_sign_of_coordinate_eq_length {η : Γ.EdgeEnd}
    (h : FiniteMetricGraph.EdgeEnd.coordinate Γ η = Γ.length η.1) :
    FiniteMetricGraph.EdgeEnd.sign Γ η = 1 := by
  rcases η with ⟨e, b⟩
  cases b
  · exfalso
    rw [FiniteMetricGraph.edgeEnd_coordinate_false] at h
    linarith [Γ.length_pos e]
  · rfl

/-- **The travel-time formula for a reflected flight.**  Let `a` be the end of the edge at the
admissible end `η`, and let `t` be an interior point where the potential first reaches the energy:
`V_e(t) = E` and `V_e < E` strictly between `a` and `t`.  Then the flight departing `η` turns at
`t`, comes back to its own end `a` (`κ_E(η) = η`), and its duration is

`t_E(η) = 2 |∫_a^t dq / √(2(E - V_e(q)))|`. -/
theorem flightTime_eq_two_mul_integral_of_turning {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Γ.length η.1))
    (hVt : V.extension η.1 t = E)
    (hlt : ∀ x ∈ uIoo (FiniteMetricGraph.EdgeEnd.coordinate Γ η) t, V.extension η.1 x < E) :
    V.flightTime E η =
        2 * |∫ x in (FiniteMetricGraph.EdgeEnd.coordinate Γ η)..t, 1 / V.speedAt η.1 E x| ∧
      (V.departureLanding η (V.germSpeed η E)).1 = FiniteMetricGraph.EdgeEnd.coordinate Γ η := by
  set a := FiniteMetricGraph.EdgeEnd.coordinate Γ η with hadef
  set T := V.flightTime E η with hTdef
  have hT : 0 < T := V.flightTime_pos hE hη
  have hVa : V.extension η.1 a < E := by rw [hadef, V.endpoint_value η]; exact hη
  have ha : a ∉ Ioo (0 : ℝ) (Γ.length η.1) := edgeEnd_coordinate_notMem_Ioo η
  have hd := V.deriv_extension_ne_zero_of_shellRegular hE ht hVt
  have htdom := V.closedEdge_subset_domain η.1 (Ioo_subset_Icc_self ht)
  have hq0 : (V.germCurve hE hη 0).1 = a := by rw [V.germCurve_zero]; rfl
  have hp0' : (V.germCurve hE hη 0).2 =
      -(FiniteMetricGraph.EdgeEnd.sign Γ η * V.germSpeed η E) := by rw [V.germCurve_zero]; rfl
  have hr : 0 < V.germSpeed η E := V.germSpeed_pos_iff.mpr hη
  set σ := -FiniteMetricGraph.EdgeEnd.sign Γ η with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by
    rcases η with ⟨e, b⟩
    cases b
    · left; simp [hσdef]
    · right; simp [hσdef]
  have hp0 : 0 < σ * (V.germCurve hE hη 0).2 := by
    rw [hp0', hσdef]
    have := edgeEnd_sign_mul_self η
    nlinarith
  have hl := Γ.length_pos η.1
  have hcase : (∀ u ∈ Icc 0 T, (V.germCurve hE hη u).1 ∈ uIcc a t) ∧
      (V.germCurve hE hη T).1 = a ∧ σ * (V.germCurve hE hη T).2 < 0 := by
    rcases edgeEnd_coordinate_mem η with h0 | h0
    · -- the end is the left end of the edge
      have hat : a < t := by rw [hadef, h0]; exact ht.1
      rw [uIoo_of_lt hat] at hlt
      obtain ⟨δ, hδ, hbeyond⟩ := V.exists_extension_gt_right hat htdom hVt hd hlt
      have hconf := V.germCurve_le_of_turning_right hE hη hδ hbeyond (by rw [hq0]; exact hat.le)
      have hqT : (V.germCurve hE hη T).1 = a := by
        rcases V.germCurve_flightTime_fst hE hη with h | h
        · rw [h, hadef, h0]
        · exfalso
          have := hconf T ⟨hT.le, le_rfl⟩
          rw [h] at this
          linarith [ht.2]
      refine ⟨fun u hu => ?_, hqT, ?_⟩
      · rw [uIcc_of_le hat.le]
        exact ⟨by rw [hadef, h0]; exact (V.germCurve_physical hE hη hu).1, hconf u hu⟩
      · have hsign := edgeEnd_sign_of_coordinate_eq_zero h0
        have hneg := V.germCurve_flightTime_snd_of_zero hE hη (by rw [hqT, hadef, h0])
        rw [hσdef, hsign]
        linarith
    · -- the end is the right end of the edge
      have hta : t < a := by rw [hadef, h0]; exact ht.2
      rw [uIoo_of_gt hta] at hlt
      obtain ⟨δ, hδ, hbeyond⟩ := V.exists_extension_gt_left hta hVt hd hlt
      have hconf := V.le_germCurve_of_turning_left hE hη hδ hbeyond (by rw [hq0]; exact hta.le)
      have hqT : (V.germCurve hE hη T).1 = a := by
        rcases V.germCurve_flightTime_fst hE hη with h | h
        · exfalso
          have := hconf T ⟨hT.le, le_rfl⟩
          rw [h] at this
          linarith [ht.1]
        · rw [h, hadef, h0]
      refine ⟨fun u hu => ?_, hqT, ?_⟩
      · rw [uIcc_of_ge hta.le]
        exact ⟨hconf u hu, by rw [hadef, h0]; exact (V.germCurve_physical hE hη hu).2⟩
      · have hsign := edgeEnd_sign_of_coordinate_eq_length h0
        have hpos := V.germCurve_flightTime_snd_of_length hE hη (by rw [hqT, hadef, h0])
        rw [hσdef, hsign]
        linarith
  obtain ⟨hconf, hqT, hpT⟩ := hcase
  obtain ⟨h1, h2⟩ :=
    V.image_germSheet_eq_of_turning hE hη hσ ha hVa hVt hlt hconf hq0 hqT hp0 hpT
  have himg1 : (fun u => (V.germCurve hE hη u).1) '' V.germSheet hE hη 1 = uIoo a t := by
    rcases hσ with h | h
    · rw [h] at h1; exact h1
    · rw [h, neg_neg] at h2; exact h2
  have himg2 : (fun u => (V.germCurve hE hη u).1) '' V.germSheet hE hη (-1) = uIoo a t := by
    rcases hσ with h | h
    · rw [h] at h2; exact h2
    · rw [h] at h1; exact h1
  have hsum := V.ofReal_flightTime_eq hE hη
  rw [himg1, himg2] at hsum
  have hsub : uIoo a t ⊆ Icc 0 (Γ.length η.1) := by
    intro x hx
    have hx' : x ∈ uIcc a t := Ioo_subset_Icc_self hx
    have hamem : a ∈ Icc (0 : ℝ) (Γ.length η.1) := by
      rcases edgeEnd_coordinate_mem η with h0 | h0 <;> rw [hadef, h0]
      · exact ⟨le_rfl, hl.le⟩
      · exact ⟨hl.le, le_rfl⟩
    exact uIcc_subset_Icc hamem (Ioo_subset_Icc_self ht) hx'
  refine ⟨?_, ?_⟩
  · rw [V.abs_integral_one_div_speedAt_eq_toReal hsub hlt, ← ENNReal.toReal_ofReal hT.le, hsum,
      ← two_mul, ENNReal.toReal_mul]
    simp
  · rw [← V.germCurve_flightTime hE hη]
    exact hqT

/-! ### Every flight crosses or is reflected -/

/-- Seen from an end `a` of an edge where the potential is below the energy, either the potential
stays below the energy on the whole open edge, or there is a first interior point `t` where it
reaches the energy. -/
theorem crossing_or_exists_turning {e : Γ.Edge} {E a : ℝ}
    (ha : a = 0 ∨ a = Γ.length e) (hVa : V.extension e a < E) :
    (∀ x ∈ Ioo (0 : ℝ) (Γ.length e), V.extension e x < E) ∨
      ∃ t ∈ Ioo (0 : ℝ) (Γ.length e), V.extension e t = E ∧
        ∀ x ∈ uIoo a t, V.extension e x < E := by
  by_cases hall : ∀ x ∈ Ioo (0 : ℝ) (Γ.length e), V.extension e x < E
  · exact Or.inl hall
  right
  obtain ⟨x₀, hx₀, hEx₀⟩ : ∃ x₀ ∈ Ioo (0 : ℝ) (Γ.length e), E ≤ V.extension e x₀ := by
    by_contra h
    exact hall fun x hx => not_le.mp fun hle => h ⟨x, hx, hle⟩
  have hVc : ContinuousOn (V.extension e) (Icc 0 (Γ.length e)) :=
    V.extension_continuousOn_closedEdge e
  set B : Set ℝ := Icc 0 (Γ.length e) ∩ V.extension e ⁻¹' Ici E with hB
  have hBclosed : IsClosed B := hVc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hx₀B : x₀ ∈ B := ⟨Ioo_subset_Icc_self hx₀, hEx₀⟩
  have hBne : B.Nonempty := ⟨x₀, hx₀B⟩
  -- a point strictly above the level forces nearby points above the level
  have hnear : ∀ t ∈ Icc (0 : ℝ) (Γ.length e), E < V.extension e t →
      ∃ δ > 0, ∀ q, |q - t| < δ → E < V.extension e q := by
    intro t ht hgt
    have hcont := V.extension_continuousAt_of_mem (V.closedEdge_subset_domain e ht)
    obtain ⟨δ, hδ, hspec⟩ :=
      Metric.eventually_nhds_iff.mp (hcont.eventually (eventually_gt_nhds hgt))
    exact ⟨δ, hδ, fun q hq => hspec (by rw [Real.dist_eq]; exact hq)⟩
  rcases ha with rfl | rfl
  · -- the left end: the first point of the level
    set t := sInf B with ht
    have htB : t ∈ B := hBclosed.csInf_mem hBne ⟨0, fun q hq => hq.1.1⟩
    have htx₀ : t ≤ x₀ := csInf_le ⟨0, fun q hq => hq.1.1⟩ hx₀B
    have hbelow : ∀ q ∈ Ioo 0 t, V.extension e q < E := by
      intro q hq
      by_contra hge
      have hqB : q ∈ B := ⟨⟨hq.1.le, by linarith [hx₀.2, hq.2]⟩, not_lt.mp hge⟩
      have := csInf_le ⟨0, fun q hq => hq.1.1⟩ hqB
      linarith [hq.2]
    have ht0 : 0 < t := by
      rcases eq_or_lt_of_le htB.1.1 with h | h
      · have := htB.2; rw [← h] at this; simp only [mem_preimage, mem_Ici] at this; linarith
      · exact h
    have hVt : V.extension e t = E := by
      refine le_antisymm ?_ htB.2
      by_contra hgt
      obtain ⟨δ, hδ, hspec⟩ := hnear t htB.1 (not_le.mp hgt)
      set q := max (t / 2) (t - δ / 2) with hq
      have hq1 : 0 < q := lt_max_of_lt_left (by linarith)
      have hq2 : q < t := max_lt (by linarith) (by linarith)
      have hq3 : |q - t| < δ := by
        rw [abs_of_neg (by linarith)]; linarith [le_max_right (t / 2) (t - δ / 2)]
      linarith [hspec q hq3, hbelow q ⟨hq1, hq2⟩]
    refine ⟨t, ⟨ht0, by linarith [hx₀.2]⟩, hVt, ?_⟩
    rw [uIoo_of_lt ht0]
    exact hbelow
  · -- the right end: the last point of the level
    set t := sSup B with ht
    have hBbdd : BddAbove B := ⟨Γ.length e, fun q hq => hq.1.2⟩
    have htB : t ∈ B := hBclosed.csSup_mem hBne hBbdd
    have htx₀ : x₀ ≤ t := le_csSup hBbdd hx₀B
    have habove : ∀ q ∈ Ioo t (Γ.length e), V.extension e q < E := by
      intro q hq
      by_contra hge
      have hqB : q ∈ B := ⟨⟨by linarith [hx₀.1, hq.1], hq.2.le⟩, not_lt.mp hge⟩
      have := le_csSup hBbdd hqB
      linarith [hq.1]
    have htl : t < Γ.length e := by
      rcases eq_or_lt_of_le htB.1.2 with h | h
      · have := htB.2; rw [h] at this; simp only [mem_preimage, mem_Ici] at this; linarith
      · exact h
    have hVt : V.extension e t = E := by
      refine le_antisymm ?_ htB.2
      by_contra hgt
      obtain ⟨δ, hδ, hspec⟩ := hnear t htB.1 (not_le.mp hgt)
      set q := min ((t + Γ.length e) / 2) (t + δ / 2) with hq
      have hq1 : t < q := lt_min (by linarith) (by linarith)
      have hq2 : q < Γ.length e := min_lt_of_left_lt (by linarith)
      have hq3 : |q - t| < δ := by
        rw [abs_of_pos (by linarith)]; linarith [min_le_right ((t + Γ.length e) / 2) (t + δ / 2)]
      linarith [hspec q hq3, habove q ⟨hq1, hq2⟩]
    refine ⟨t, ⟨by linarith [hx₀.1], htl⟩, hVt, ?_⟩
    rw [uIoo_of_gt htl]
    exact habove

/-- **The travel-time formula, for every flight** (Theorem VIII.5 (b)).  At a shell-regular
energy, the flight departing an admissible end `η` (at the end `a` of its edge `e`) either

* crosses the edge — the potential stays below `E` on the open edge — lands at the opposite end,
  and `t_E(η) = ∫_0^ℓ dq / √(2(E - V_e(q)))`; or
* is reflected at the first interior point `t` where the potential reaches `E`, comes back to `a`,
  and `t_E(η) = 2 |∫_a^t dq / √(2(E - V_e(q)))|`. -/
theorem flightTime_eq_crossing_or_turning {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    ((∀ x ∈ Ioo (0 : ℝ) (Γ.length η.1), V.extension η.1 x < E) ∧
        V.flightTime E η = ∫ x in (0 : ℝ)..Γ.length η.1, 1 / V.speedAt η.1 E x ∧
        (V.departureLanding η (V.germSpeed η E)).1 =
          Γ.length η.1 - FiniteMetricGraph.EdgeEnd.coordinate Γ η) ∨
      ∃ t ∈ Ioo (0 : ℝ) (Γ.length η.1), V.extension η.1 t = E ∧
        (∀ x ∈ uIoo (FiniteMetricGraph.EdgeEnd.coordinate Γ η) t, V.extension η.1 x < E) ∧
        V.flightTime E η =
          2 * |∫ x in (FiniteMetricGraph.EdgeEnd.coordinate Γ η)..t, 1 / V.speedAt η.1 E x| ∧
        (V.departureLanding η (V.germSpeed η E)).1 = FiniteMetricGraph.EdgeEnd.coordinate Γ η := by
  have hVa : V.extension η.1 (FiniteMetricGraph.EdgeEnd.coordinate Γ η) < E := by
    rw [V.endpoint_value η]; exact hη
  rcases V.crossing_or_exists_turning (edgeEnd_coordinate_mem η) hVa with hcross | ⟨t, ht, hVt, hlt⟩
  · exact Or.inl ⟨hcross, V.flightTime_eq_integral_of_crossing hE hη hcross⟩
  · exact Or.inr ⟨t, ht, hVt, hlt, V.flightTime_eq_two_mul_integral_of_turning hE hη ht hVt hlt⟩

end Reflection

end MechanicalPotential

end HamiltonianMetricGraphs
