/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Remark VIII.6: the ergodic decomposition of a shell-regular energy surface
-/

import HamiltonianMetricGraphs.ShellErgodicDisintegration
import HamiltonianMetricGraphs.ShellErgodicCircle

/-!
# Ergodic decomposition of a shell-regular energy surface (Remark VIII.6)

Remark VIII.6 states, for a shell-regular energy `E`:

1. the disintegration `m = ∫ ν_E dE` (`ShellErgodicDisintegration.lean`, `remark_disintegration`);
2. `Σ_E = ⨆_c C_{E,c}` and `ν_E = ⊕_c Leb_{[0, T_c(E))}`, from Theorem VIII.5 (c);
3. on `C_{E,c}` the flow is `u ↦ u + t mod T_c(E)`, ergodic for the normalized time measure, with
   pure point spectrum and frequencies `2πn / T_c(E)`, `n ∈ ℤ`;
4. the ergodic components of `Σ_E` are indexed by the cycles of `Π_E`, and a nonempty `Σ_E` is
   ergodic iff `Π_E` has exactly one cycle.

This module proves 2–4 on the regular quotient phase space, where the flow `Φ_t` lives.

## Encoding

* **`ν_E` on the quotient.**  `regularShellMeasure S E` is the restriction to the regular sector
  of `quotientShellMeasure S E = ∑_e (x ↦ π(e, x))_* ν_E^e`, the pushforward of the branch measures
  of Proposition VII.1 (see `ShellErgodicDisintegration.lean`).  It is carried by `Σ_E`
  (`regularShellMeasure_compl_shell`), because `ν_E^e` lives on the level `H = E` of the closed
  edge (`shellMeasure_compl_level`).
* **The orbit of a cycle.**  For a finite set `c` of ends, `cycleShellOrbit S hE c` is the union of
  the orbits `shellOrbit` of the departure states of the ends of `c`; for a cycle
  `c = germCycle η` of `Π_E` this is the orbit of the departure state of `η`
  (`cycleShellOrbit_germCycle`).  The cycles are indexed by `germCycles S E`, and `T_c(E)` is
  `∑_{ζ ∈ c} t_E(ζ)` (`= cyclePeriod S E η`).
* **The circle chart.**  `orbitChart S hE hη : ℝ / T_c(E)ℤ → C_{E,c}`, `u ↦ Φ_u(departure state of
  η)` (`AddCircle (cyclePeriod S E η)`, with a `Fact (0 < T_c(E))` instance argument, which holds
  by `cyclePeriod_pos`).  It is the suspension chart of `regularShell_decomposition` with the ends
  of `[0, T_c(E))` identified: injective, onto `C_{E,c}`, Borel, and conjugates the flow to the
  translation `CircleFlow.translate t : u ↦ u + t`.  By Lusin–Souslin, `C_{E,c}` is Borel.
* **Ergodicity of a flow.**  `FlowErgodic S μ`: every Borel set that is `μ`-almost invariant
  under every `Φ_t`, `t ∈ ℝ`, is `μ`-null or `μ`-conull.  (Almost invariance is the weaker
  hypothesis; strictly invariant sets are a special case.)  The normalized time measure is
  `normalizedShellMeasure S E = ν_E / ν_E(Σ_E)`.

## Results

* `regularShellMeasure_inter_shellOrbit`, `map_orbitChart_volume`: **`ν_E` on `C_{E,c}` is the time
  measure**, `(orbitChart)_* du = ν_E|_{C_{E,c}}`; this transports Theorem VIII.5 (c)
  (`regularShell_measure`) from the edge phase spaces to the quotient.
  `map_orbitChart_haarAddCircle` is the normalized version, and `regularShellMeasure_shellOrbit`
  the mass `T_c(E)`.
* `orbit_invariant_dichotomy`: **ergodicity on an orbit**, from the ergodicity of the translation
  flow on the circle (`ShellErgodicCircle.lean`).
* `shell_eq_biUnion_cycleShellOrbit`, `pairwiseDisjoint_cycleShellOrbit`,
  `regularShellMeasure_eq_sum`: `Σ_E = ⨆_c C_{E,c}` and `ν_E = ⊕_c ν_E|_{C_{E,c}}`.
* `measurePreserving_flow_regularShellMeasure`: `ν_E` is `Φ_t`-invariant on the quotient (the
  invariance of Proposition VII.1, recovered from the decomposition).
* `invariant_ae_eq_biUnion`: **the ergodic components are the orbits of the cycles**.
* `flowErgodic_iff_card_germCycles`, `card_germCycles_eq_one_iff`: **a nonempty `Σ_E` is ergodic
  iff `Π_E` has exactly one cycle**, i.e. iff all admissible ends are in one cycle of `Π_E`.
* `orbitEquiv`, `measurePreserving_orbitEquiv`, `orbitFourierBasis`, `koopman_orbitFourierBasis`:
  the chart as a measure-preserving Borel isomorphism `(ℝ / T_c(E)ℤ, du / T_c(E)) ≃ᵐ
  (C_{E,c}, ν_E / T_c(E))` conjugating translations to `Φ_t`, and the point spectrum stated directly
  on `L²(C_{E,c}, ν_E / T_c(E))`.
* `orbit_ergodic_pointSpectrum`, `orbit_pointSpectrum` and `shell_ergodic_iff_one_cycle` package
  claims 3 and 2, 4.

The pure point spectrum is proved on the circle model (`CircleFlow.koopman_fourierBasis`): the
characters `e_n` are eigenfunctions of the Koopman operators of the translations with eigenvalues
`exp(i 2πn t / T_c(E))` and form the Hilbert basis `fourierBasis` of `L²(du / T_c(E))`; the chart
`orbitChart` is the measure-preserving conjugacy carrying this to `(C_{E,c}, ν_E / T_c(E), Φ_t)`.

The remark's closing sentence (no classification of trajectories confined to wells at other
energies) is a disclaimer, not a claim.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory CircleFlow
open scoped Topology ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-! ### `ν_E` on the regular quotient phase space -/

/-- **The invariant time measure `ν_E` of Proposition VII.1 on the regular quotient phase space**,
the domain of the flow: the restriction of `quotientShellMeasure S E` to the regular sector. -/
noncomputable def regularShellMeasure (E : ℝ) : Measure (RegularScatteringPhaseSpace (V := V) S) :=
  (V.quotientShellMeasure S E).comap Subtype.val

theorem measurableEmbedding_regular :
    MeasurableEmbedding (Subtype.val : RegularScatteringPhaseSpace (V := V) S →
      ScatteringPhaseSpace (V := V) S) :=
  MeasurableEmbedding.subtype_coe (measurableSet_regularScatteringPhaseSpace V S)

/-- The `ν_E`-measure of a Borel set of regular states, computed on the edge phase spaces. -/
theorem regularShellMeasure_apply (E : ℝ) {A : Set (RegularScatteringPhaseSpace (V := V) S)}
    (hA : MeasurableSet A) :
    V.regularShellMeasure S E A = ∑ e, V.shellMeasure E e
      ((fun x => graphClass V S (e, x)) ⁻¹' (Subtype.val '' A)) := by
  have hA' : MeasurableSet (Subtype.val '' A) :=
    (V.measurableEmbedding_regular S).measurableSet_image.mpr hA
  rw [regularShellMeasure, (V.measurableEmbedding_regular S).comap_apply, quotientShellMeasure,
    Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Measure.map_apply (V.measurable_graphClass_edge S e) hA']

/-- **`ν_E` lives on the energy level**: the edge-phase points off the closed edge or off the level
`H = E` are `ν_E`-null. -/
theorem shellMeasure_compl_level (E : ℝ) (e : Γ.Edge) :
    V.shellMeasure E e
      {x | ¬ (x.1 ∈ Icc 0 (Γ.length e) ∧ V.hamiltonian e x.1 x.2 = E)} = 0 := by
  set N : Set (ℝ × ℝ) :=
    {x | ¬ (x.1 ∈ Icc 0 (Γ.length e) ∧ x.2 ^ 2 / 2 + V.clampedPotential e x.1 = E)} with hNdef
  have hNm : MeasurableSet N := by
    have hc := V.continuous_clampedPotential e
    have h1 : MeasurableSet {x : ℝ × ℝ | x.1 ∈ Icc 0 (Γ.length e)} :=
      measurable_fst measurableSet_Icc
    have h2 : MeasurableSet {x : ℝ × ℝ | x.2 ^ 2 / 2 + V.clampedPotential e x.1 = E} :=
      measurableSet_eq_fun (by fun_prop) measurable_const
    exact (h1.inter h2).compl
  have hsub : {x : ℝ × ℝ | ¬ (x.1 ∈ Icc 0 (Γ.length e) ∧ V.hamiltonian e x.1 x.2 = E)} ⊆ N := by
    intro x hx hN
    apply hx
    refine ⟨hN.1, ?_⟩
    rw [hamiltonian, ← V.clampedPotential_of_mem e hN.1]
    exact hN.2
  refine measure_mono_null hsub ?_
  have hsheet : ∀ ε : ℝ, ε = 1 ∨ ε = -1 → V.sheetMeasure E e ε N = 0 := by
    intro ε hε
    rw [sheetMeasure, Measure.map_apply_of_aemeasurable (V.aemeasurable_sheetLift e E ε) hNm,
      edgeTimeMeasure, withDensity_apply', Measure.restrict_restrict' measurableSet_Icc]
    refine nonpos_iff_eq_zero.mp ((lintegral_mono_set (t := {q | E ≤ V.clampedPotential e q} ∩
      Icc 0 (Γ.length e)) ?_).trans (le_of_eq ?_))
    · rintro q ⟨hqN, hq⟩
      refine ⟨?_, hq⟩
      by_contra hlt
      have hlt' : V.extension e q < E := by
        rw [← V.clampedPotential_of_mem e hq]; exact not_le.mp hlt
      apply hqN
      refine ⟨hq, ?_⟩
      simp only [sheetLift]
      rw [V.clampedPotential_of_mem e hq, mul_pow, speedAt,
        Real.sq_sqrt (by linarith [hlt'])]
      rcases hε with rfl | rfl <;> ring
    · rw [setLIntegral_congr_fun
        ((measurableSet_le measurable_const (V.continuous_clampedPotential e).measurable).inter
          measurableSet_Icc) (g := fun _ => 0) (fun q hq => ?_)]
      · simp
      · exact V.timeDensity_eq_zero_of_le e (by rw [← V.clampedPotential_of_mem e hq.2]; exact hq.1)
  rw [shellMeasure, Measure.add_apply, hsheet 1 (Or.inl rfl), hsheet (-1) (Or.inr rfl), add_zero]

theorem ae_shellMeasure_level (E : ℝ) (e : Γ.Edge) :
    ∀ᵐ x ∂(V.shellMeasure E e), x.1 ∈ Icc 0 (Γ.length e) ∧ V.hamiltonian e x.1 x.2 = E :=
  ae_iff.mpr (V.shellMeasure_compl_level E e)

theorem measurableSet_shell (E : ℝ) : MeasurableSet (V.shell S E) :=
  ((measurable_quotientHamiltonian (V := V) S).comp measurable_subtype_coe)
    (measurableSet_singleton E)

/-- **`ν_E` is carried by the energy shell `Σ_E`.** -/
theorem regularShellMeasure_compl_shell {E : ℝ} (hE : V.ShellRegular E) :
    V.regularShellMeasure S E (V.shell S E)ᶜ = 0 := by
  rw [V.regularShellMeasure_apply S E (V.measurableSet_shell S E).compl]
  refine Finset.sum_eq_zero fun e _ => measure_mono_null ?_ (V.shellMeasure_compl_level E e)
  rintro x hx ⟨hxI, hxE⟩
  obtain ⟨z, hz, hzx⟩ := hx
  apply hz
  change quotientHamiltonian (V := V) S z.1 = E
  rw [hzx, quotientHamiltonian_graphClass V S (V.admissiblePoint_of_hamiltonian hE hxI hxE)]
  exact hxE

variable [Nonempty Γ.Edge]

/-! ### The circle chart of a periodic orbit -/

section Chart

variable {z : RegularScatteringPhaseSpace (V := V) S} {T : ℝ} [hT : Fact (0 < T)]

/-- **The circle chart of a periodic point**: `u mod T ↦ Φ_u(z)`, for `z` of period `T`. -/
noncomputable def periodicChart (z : RegularScatteringPhaseSpace (V := V) S) (T : ℝ)
    [Fact (0 < T)] (x : AddCircle T) : RegularScatteringPhaseSpace (V := V) S :=
  flow V S z (AddCircle.equivIco T 0 x : ℝ)

theorem periodicChart_coe (hper : flow V S z T = z) (u : ℝ) :
    V.periodicChart S z T (u : AddCircle T) = flow V S z u := by
  unfold periodicChart
  change flow V S z (toIcoMod hT.out 0 u) = _
  exact V.flow_toIcoMod_of_flow_eq S z hT.out hper u

/-- In the circle chart the flow is the translation `u ↦ u + t mod T`. -/
theorem periodicChart_translate (hper : flow V S z T = z) (t : ℝ) (x : AddCircle T) :
    V.periodicChart S z T (translate t x) = flow V S (V.periodicChart S z T x) t := by
  induction x using QuotientAddGroup.induction_on with
  | H u => rw [translate_coe, V.periodicChart_coe S hper, V.periodicChart_coe S hper, flow_flow]

theorem periodicChart_injective (hper : flow V S z T = z)
    (hmin : ∀ u ∈ Ioo 0 T, flow V S z u ≠ z) : Function.Injective (V.periodicChart S z T) := by
  intro x y hxy
  induction x using QuotientAddGroup.induction_on with
  | H u =>
    induction y using QuotientAddGroup.induction_on with
    | H v =>
      rw [V.periodicChart_coe S hper, V.periodicChart_coe S hper] at hxy
      obtain ⟨m, hm⟩ := (V.flow_eq_flow_iff_of_period S z hT.out hper hmin u v).mp hxy
      rw [hm]
      simp

theorem range_periodicChart (hper : flow V S z T = z) :
    range (V.periodicChart S z T) = range fun u => flow V S z u := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    induction x using QuotientAddGroup.induction_on with
    | H u => exact ⟨u, (V.periodicChart_coe S hper u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, V.periodicChart_coe S hper u⟩

end Chart

/-! ### The circle chart of the orbit of a cycle -/

section OrbitChart

variable {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E)

/-- For `u ≥ 0`, the flow from the departure state of `η` is the class of the departing
trajectory. -/
theorem flow_departureClass_val {u : ℝ} (hu : 0 ≤ u) :
    (flow V S (V.departureClass S hE η hη) u).1 =
      graphClass V S (V.germTrajectory S hE η hη u) := by
  rw [V.flow_departureClass S hE η hη hu, trajClass_val]
  rfl

/-- The departing trajectory is a Borel function of time. -/
theorem measurable_germTrajectory : Measurable (V.germTrajectory S hE η hη) := by
  have hr := V.germSpeed_mem_regularSpeeds hE hη
  have heq : V.germTrajectory S hE η hη =
      fun u => V.departureTrajectory S η (V.germSpeed η E, u) := by
    funext u
    rw [V.departureTrajectory_of_mem S (z := (V.germSpeed η E, u)) hr]
    rfl
  rw [heq]
  exact (V.measurable_departureTrajectory S η).comp (measurable_const.prodMk measurable_id)

section Chart

variable [Fact (0 < V.cyclePeriod S E η)]

/-- **The circle chart of the orbit `C_{E,c}`** of the cycle `c` of `η`:
`u mod T_c(E) ↦ Φ_u(departure state of η)`.  This is the suspension chart of Theorem VIII.5 (c)
with its endpoints identified. -/
noncomputable def orbitChart :
    AddCircle (V.cyclePeriod S E η) → RegularScatteringPhaseSpace (V := V) S :=
  V.periodicChart S (V.departureClass S hE η hη) (V.cyclePeriod S E η)

theorem orbitChart_coe (u : ℝ) :
    V.orbitChart S hE hη (u : AddCircle (V.cyclePeriod S E η)) =
      flow V S (V.departureClass S hE η hη) u :=
  V.periodicChart_coe S (V.flow_cyclePeriod_departureClass S hE hη) u

/-- In the circle chart the flow on `C_{E,c}` is `u ↦ u + t mod T_c(E)`. -/
theorem orbitChart_translate (t : ℝ) (x : AddCircle (V.cyclePeriod S E η)) :
    V.orbitChart S hE hη (translate t x) = flow V S (V.orbitChart S hE hη x) t :=
  V.periodicChart_translate S (V.flow_cyclePeriod_departureClass S hE hη) t x

theorem orbitChart_injective : Function.Injective (V.orbitChart S hE hη) :=
  V.periodicChart_injective S (V.flow_cyclePeriod_departureClass S hE hη)
    (fun _ hu => V.flow_departureClass_ne_self S hE hη hu)

theorem range_orbitChart : range (V.orbitChart S hE hη) = V.shellOrbit S hE η hη :=
  V.range_periodicChart S (V.flow_cyclePeriod_departureClass S hE hη)

theorem measurable_orbitChart : Measurable (V.orbitChart S hE hη) := by
  set T := V.cyclePeriod S E η
  have hval : (fun x => (V.orbitChart S hE hη x).1) = fun x : AddCircle T =>
      graphClass V S (V.germTrajectory S hE η hη (AddCircle.equivIco T 0 x : ℝ)) := by
    funext x
    exact V.flow_departureClass_val S hE hη (AddCircle.equivIco T 0 x).2.1
  rw [measurable_comap_iff]
  change Measurable fun x => (V.orbitChart S hE hη x).1
  rw [hval]
  exact (V.measurable_graphClass S).comp ((V.measurable_germTrajectory S hE hη).comp
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco T 0).measurable))

/-- **`ν_E` on the orbit `C_{E,c}` is the time measure of the circle.**  For every Borel set `A` of
regular states, `ν_E(A ∩ C_{E,c})` is the Lebesgue measure of the times `u mod T_c(E)` at which the
orbit is in `A`.  This is Theorem VIII.5 (c) (`regularShell_measure`) transported to the
quotient. -/
theorem regularShellMeasure_inter_shellOrbit {A : Set (RegularScatteringPhaseSpace (V := V) S)}
    (hA : MeasurableSet A) (hO : MeasurableSet (V.shellOrbit S hE η hη)) :
    V.regularShellMeasure S E (A ∩ V.shellOrbit S hE η hη) =
      volume (V.orbitChart S hE hη ⁻¹' A) := by
  set B : Γ.Edge → Set (ℝ × ℝ) := fun e =>
    (fun x => graphClass V S (e, x)) ⁻¹' (Subtype.val '' A) with hBdef
  have hBm : ∀ e, MeasurableSet (B e) := fun e => V.measurable_graphClass_edge S e
    ((V.measurableEmbedding_regular S).measurableSet_image.mpr hA)
  rw [V.regularShellMeasure_apply S E (hA.inter hO)]
  have hedge : ∀ e, V.shellMeasure E e ((fun x => graphClass V S (e, x)) ⁻¹'
      (Subtype.val '' (A ∩ V.shellOrbit S hE η hη))) =
      ∫⁻ x in V.shellOrbitPreimage S hE η hη e, (B e).indicator 1 x ∂(V.shellMeasure E e) := by
    intro e
    rw [lintegral_indicator_one (hBm e), Measure.restrict_apply (hBm e)]
    refine measure_congr ?_
    filter_upwards [V.ae_shellMeasure_level E e] with x hx
    refine propext ⟨?_, ?_⟩
    · rintro ⟨z, ⟨hzA, hzO⟩, hzx⟩
      exact ⟨⟨z, hzA, hzx⟩, hx.1, hx.2, z, hzO, hzx⟩
    · rintro ⟨⟨z, hzA, hzx⟩, -, -, z', hz'O, hz'x⟩
      have hzz : z = z' := Subtype.ext (hzx.trans hz'x.symm)
      subst hzz
      exact ⟨z, ⟨hzA, hz'O⟩, hzx⟩
  rw [Finset.sum_congr rfl fun e _ => hedge e, (V.regularShell_measure S hE).1 η hη
    (fun e => (B e).indicator 1) (fun e => measurable_one.indicator (hBm e))]
  have hpt : ∀ u ∈ Ico 0 (V.cyclePeriod S E η),
      (B (V.germTrajectory S hE η hη u).1).indicator (1 : ℝ × ℝ → ℝ≥0∞)
          (V.germTrajectory S hE η hη u).2 =
        (V.orbitChart S hE hη ⁻¹' A).indicator (1 : AddCircle (V.cyclePeriod S E η) → ℝ≥0∞)
          (u : AddCircle (V.cyclePeriod S E η)) := by
    intro u hu
    have hiff : (V.germTrajectory S hE η hη u).2 ∈ B (V.germTrajectory S hE η hη u).1 ↔
        (u : AddCircle (V.cyclePeriod S E η)) ∈ V.orbitChart S hE hη ⁻¹' A := by
      change graphClass V S (V.germTrajectory S hE η hη u) ∈ Subtype.val '' A ↔
        V.orbitChart S hE hη u ∈ A
      rw [V.orbitChart_coe S hE hη u, ← V.flow_departureClass_val S hE hη hu.1,
        Subtype.val_injective.mem_set_image]
    by_cases h : (u : AddCircle (V.cyclePeriod S E η)) ∈ V.orbitChart S hE hη ⁻¹' A
    · rw [indicator_of_mem h, indicator_of_mem (hiff.mpr h)]; rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hiff.mp h'))]
  rw [setLIntegral_congr_fun measurableSet_Ico hpt, setLIntegral_congr Ico_ae_eq_Ioc]
  have hpre := AddCircle.lintegral_preimage (V.cyclePeriod S E η) 0
    ((V.orbitChart S hE hη ⁻¹' A).indicator (1 : AddCircle (V.cyclePeriod S E η) → ℝ≥0∞))
  rw [zero_add] at hpre
  rw [hpre, lintegral_indicator_one (V.measurable_orbitChart S hE hη hA)]

end Chart

/-- **The orbit `C_{E,c}` is Borel**: it is the injective Borel image of the circle
(Lusin–Souslin). -/
theorem measurableSet_shellOrbit : MeasurableSet (V.shellOrbit S hE η hη) := by
  haveI : Fact (0 < V.cyclePeriod S E η) := ⟨V.cyclePeriod_pos S hE hη⟩
  rw [← V.range_orbitChart S hE hη, ← image_univ]
  exact MeasurableSet.univ.image_of_measurable_injOn (V.measurable_orbitChart S hE hη)
    (V.orbitChart_injective S hE hη).injOn

section Measure

variable [Fact (0 < V.cyclePeriod S E η)]

/-- **`ν_E` restricted to `C_{E,c}` is the image of the time measure `du` on `ℝ / T_c(E)ℤ`.** -/
theorem map_orbitChart_volume :
    Measure.map (V.orbitChart S hE hη) volume =
      (V.regularShellMeasure S E).restrict (V.shellOrbit S hE η hη) := by
  ext A hA
  rw [Measure.map_apply (V.measurable_orbitChart S hE hη) hA, Measure.restrict_apply hA,
    V.regularShellMeasure_inter_shellOrbit S hE hη hA (V.measurableSet_shellOrbit S hE hη)]

/-- **The normalized time measure of `C_{E,c}` is the image of the normalized Haar measure.** -/
theorem map_orbitChart_haarAddCircle :
    Measure.map (V.orbitChart S hE hη) AddCircle.haarAddCircle =
      (ENNReal.ofReal (V.cyclePeriod S E η))⁻¹ •
        (V.regularShellMeasure S E).restrict (V.shellOrbit S hE η hη) := by
  have hT : ENNReal.ofReal (V.cyclePeriod S E η) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (V.cyclePeriod_pos S hE hη)).ne'
  have hhaar : (AddCircle.haarAddCircle : Measure (AddCircle (V.cyclePeriod S E η))) =
      (ENNReal.ofReal (V.cyclePeriod S E η))⁻¹ • volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, smul_smul,
      ENNReal.inv_mul_cancel hT ENNReal.ofReal_ne_top, one_smul]
  rw [hhaar, Measure.map_smul, V.map_orbitChart_volume S hE hη]

/-- **`ν_E(C_{E,c}) = T_c(E)`.** -/
theorem regularShellMeasure_shellOrbit :
    V.regularShellMeasure S E (V.shellOrbit S hE η hη) = ENNReal.ofReal (V.cyclePeriod S E η) := by
  have h := V.regularShellMeasure_inter_shellOrbit S hE hη MeasurableSet.univ
    (V.measurableSet_shellOrbit S hE hη)
  rw [univ_inter, preimage_univ, AddCircle.measure_univ] at h
  exact h

/-- **Ergodicity on an orbit.**  A Borel set of regular states that is `ν_E`-almost invariant under
every `Φ_t` either misses `C_{E,c}` or contains it, up to `ν_E`-null sets. -/
theorem orbit_invariant_dichotomy {A : Set (RegularScatteringPhaseSpace (V := V) S)}
    (hA : MeasurableSet A)
    (hinv : ∀ t : ℝ, (fun z => flow V S z t) ⁻¹' A =ᵐ[V.regularShellMeasure S E] A) :
    V.regularShellMeasure S E (A ∩ V.shellOrbit S hE η hη) = 0 ∨
      V.regularShellMeasure S E (V.shellOrbit S hE η hη \ A) = 0 := by
  have hO := V.measurableSet_shellOrbit S hE hη
  have hBm : MeasurableSet (V.orbitChart S hE hη ⁻¹' A) := V.measurable_orbitChart S hE hη hA
  have hchart : ∀ X, MeasurableSet X → V.regularShellMeasure S E X = 0 →
      volume (V.orbitChart S hE hη ⁻¹' X) = 0 := fun X hX h0 => by
    rw [← V.regularShellMeasure_inter_shellOrbit S hE hη hX hO]
    exact measure_mono_null inter_subset_left h0
  have hBinv : ∀ t : ℝ, translate (T := V.cyclePeriod S E η) t ⁻¹' (V.orbitChart S hE hη ⁻¹' A)
      =ᵐ[volume] V.orbitChart S hE hη ⁻¹' A := by
    intro t
    have hpre : translate (T := V.cyclePeriod S E η) t ⁻¹' (V.orbitChart S hE hη ⁻¹' A) =
        V.orbitChart S hE hη ⁻¹' ((fun z => flow V S z t) ⁻¹' A) := by
      ext x
      simp only [mem_preimage, V.orbitChart_translate S hE hη]
    rw [hpre]
    have hFm : MeasurableSet ((fun z => flow V S z t) ⁻¹' A) := V.measurable_flow S t hA
    obtain ⟨h1, h2⟩ := ae_eq_set.mp (hinv t)
    refine ae_eq_set.mpr ⟨?_, ?_⟩
    · rw [← preimage_sdiff]; exact hchart _ (hFm.diff hA) h1
    · rw [← preimage_sdiff]; exact hchart _ (hA.diff hFm) h2
  rcases ae_empty_or_univ_of_translate_invariant hBm.nullMeasurableSet hBinv with h | h
  · left
    rw [V.regularShellMeasure_inter_shellOrbit S hE hη hA hO, measure_congr h, measure_empty]
  · right
    rw [ae_eq_univ] at h
    rw [sdiff_eq, inter_comm, V.regularShellMeasure_inter_shellOrbit S hE hη hA.compl hO,
      preimage_compl]
    exact h

end Measure

end OrbitChart

/-- The orbits of the flow are invariant: `Φ_t⁻¹(C) = C`. -/
theorem flow_preimage_shellOrbit {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (t : ℝ) :
    (fun z => flow V S z t) ⁻¹' V.shellOrbit S hE η hη = V.shellOrbit S hE η hη := by
  ext w
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s + -t, ?_⟩
    simp only at hs ⊢
    rw [← flow_flow, hs, flow_flow_neg_self]
  · rintro ⟨s, rfl⟩
    exact ⟨s + t, (flow_flow V S _ s t).symm⟩

/-! ### The orbits of the cycles of `Π_E` -/

section Cycles

variable {E : ℝ} (hE : V.ShellRegular E)

/-- **The orbit `C_{E,c}` of a cycle `c` of `Π_E`**: the union of the orbits of the departure
states of the ends of `c` (they all coincide, `cycleShellOrbit_germCycle`). -/
def cycleShellOrbit (c : Finset Γ.EdgeEnd) : Set (RegularScatteringPhaseSpace (V := V) S) :=
  {z | ∃ η ∈ c, ∃ hη : η ∈ V.allowedGerms E, z ∈ V.shellOrbit S hE η hη}

theorem cycleShellOrbit_germCycle {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) :
    V.cycleShellOrbit S hE (V.germCycle S E η) = V.shellOrbit S hE η hη := by
  ext z
  constructor
  · rintro ⟨ζ, hζc, hζ, hz⟩
    rwa [V.shellOrbit_eq_of_mem_germCycle S hE hη hζ hζc] at hz
  · intro hz
    exact ⟨η, V.self_mem_germCycle S hE hη, hη, hz⟩

theorem exists_of_mem_germCycles {c : Finset Γ.EdgeEnd} (hc : c ∈ V.germCycles S E) :
    ∃ (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E), V.germCycle S E η = c ∧
      V.cycleShellOrbit S hE c = V.shellOrbit S hE η hη := by
  obtain ⟨η, hη, rfl⟩ := (V.mem_germCycles S).mp hc
  exact ⟨η, hη, rfl, V.cycleShellOrbit_germCycle S hE hη⟩

theorem measurableSet_cycleShellOrbit (c : Finset Γ.EdgeEnd) :
    MeasurableSet (V.cycleShellOrbit S hE c) := by
  have h : V.cycleShellOrbit S hE c =
      ⋃ η ∈ c, ⋃ hη : η ∈ V.allowedGerms E, V.shellOrbit S hE η hη := by
    ext z
    simp [cycleShellOrbit]
  rw [h]
  exact Finset.measurableSet_biUnion _ fun η _ =>
    MeasurableSet.iUnion fun hη => V.measurableSet_shellOrbit S hE hη

/-- The orbits of distinct cycles are disjoint. -/
theorem pairwiseDisjoint_cycleShellOrbit :
    (↑(V.germCycles S E) : Set (Finset Γ.EdgeEnd)).PairwiseDisjoint (V.cycleShellOrbit S hE) := by
  intro c hc d hd hcd
  obtain ⟨η, hη, rfl⟩ := (V.mem_germCycles S).mp hc
  obtain ⟨ζ, hζ, rfl⟩ := (V.mem_germCycles S).mp hd
  change Disjoint (V.cycleShellOrbit S hE (V.germCycle S E η))
    (V.cycleShellOrbit S hE (V.germCycle S E ζ))
  rw [V.cycleShellOrbit_germCycle S hE hη, V.cycleShellOrbit_germCycle S hE hζ]
  exact V.disjoint_shellOrbit S hE hη hζ fun h => hcd (V.germCycle_eq_of_mem S hE hη h).symm

/-- The orbits of the cycles are invariant under the flow. -/
theorem flow_preimage_cycleShellOrbit {c : Finset Γ.EdgeEnd} (hc : c ∈ V.germCycles S E)
    (t : ℝ) : (fun z => flow V S z t) ⁻¹' V.cycleShellOrbit S hE c = V.cycleShellOrbit S hE c := by
  obtain ⟨η, hη, -, hC⟩ := V.exists_of_mem_germCycles S hE hc
  rw [hC, V.flow_preimage_shellOrbit S hE hη t]

/-- **`Σ_E = ⨆_c C_{E,c}`.** -/
theorem shell_eq_biUnion_cycleShellOrbit :
    V.shell S E = ⋃ c ∈ V.germCycles S E, V.cycleShellOrbit S hE c := by
  ext z
  rw [V.mem_shell_iff_exists_mem_shellOrbit S hE]
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨η, hη, hz⟩
    refine ⟨V.germCycle S E η, (V.mem_germCycles S).mpr ⟨η, hη, rfl⟩, ?_⟩
    rw [V.cycleShellOrbit_germCycle S hE hη]
    exact hz
  · rintro ⟨c, -, η, -, hη, hz⟩
    exact ⟨η, hη, hz⟩

/-- **`ν_E = ⊕_c ν_E|_{C_{E,c}}`.**  For every Borel set of regular states, its `ν_E`-measure is
the sum over the cycles of `Π_E` of the measures of its parts on the orbits. -/
theorem regularShellMeasure_eq_sum {A : Set (RegularScatteringPhaseSpace (V := V) S)}
    (hA : MeasurableSet A) :
    V.regularShellMeasure S E A =
      ∑ c ∈ V.germCycles S E, V.regularShellMeasure S E (A ∩ V.cycleShellOrbit S hE c) := by
  rw [← measure_biUnion_finset
    (fun c hc d hd hcd => Disjoint.mono inter_subset_right inter_subset_right
      (V.pairwiseDisjoint_cycleShellOrbit S hE hc hd hcd))
    (fun c _ => hA.inter (V.measurableSet_cycleShellOrbit S hE c)),
    ← inter_iUnion₂, ← V.shell_eq_biUnion_cycleShellOrbit S hE]
  exact (measure_inter_conull (V.regularShellMeasure_compl_shell S hE)).symm

/-- **`ν_E(C_{E,c}) = T_c(E) = ∑_{ζ ∈ c} t_E(ζ)`.** -/
theorem regularShellMeasure_cycleShellOrbit {c : Finset Γ.EdgeEnd} (hc : c ∈ V.germCycles S E) :
    V.regularShellMeasure S E (V.cycleShellOrbit S hE c) =
      ENNReal.ofReal (∑ ζ ∈ c, V.flightTime E ζ) := by
  obtain ⟨η, hη, rfl, hC⟩ := V.exists_of_mem_germCycles S hE hc
  haveI : Fact (0 < V.cyclePeriod S E η) := ⟨V.cyclePeriod_pos S hE hη⟩
  rw [hC, V.regularShellMeasure_shellOrbit S hE hη]
  rfl

include hE in
/-- **`ν_E(Σ_E) = ∑_c T_c(E)`**, finite. -/
theorem regularShellMeasure_univ :
    V.regularShellMeasure S E univ =
      ∑ c ∈ V.germCycles S E, ENNReal.ofReal (∑ ζ ∈ c, V.flightTime E ζ) := by
  rw [V.regularShellMeasure_eq_sum S hE MeasurableSet.univ]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [univ_inter, V.regularShellMeasure_cycleShellOrbit S hE hc]

include hE in
theorem regularShellMeasure_univ_lt_top : V.regularShellMeasure S E univ < ⊤ := by
  rw [V.regularShellMeasure_univ S hE]
  exact ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top

include hE in
/-- **Proposition VII.1 (invariance), on the quotient**: `ν_E` is invariant under every `Φ_t`. -/
theorem measurePreserving_flow_regularShellMeasure (t : ℝ) :
    MeasurePreserving (fun z => flow V S z t) (V.regularShellMeasure S E)
      (V.regularShellMeasure S E) := by
  refine ⟨V.measurable_flow S t, Measure.ext fun A hA => ?_⟩
  have hFm : MeasurableSet ((fun z => flow V S z t) ⁻¹' A) := V.measurable_flow S t hA
  rw [Measure.map_apply (V.measurable_flow S t) hA, V.regularShellMeasure_eq_sum S hE hFm,
    V.regularShellMeasure_eq_sum S hE hA]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨η, hη, -, hC⟩ := V.exists_of_mem_germCycles S hE hc
  haveI : Fact (0 < V.cyclePeriod S E η) := ⟨V.cyclePeriod_pos S hE hη⟩
  have hO := V.measurableSet_shellOrbit S hE hη
  rw [hC, V.regularShellMeasure_inter_shellOrbit S hE hη hFm hO,
    V.regularShellMeasure_inter_shellOrbit S hE hη hA hO]
  have hpre : V.orbitChart S hE hη ⁻¹' ((fun z => flow V S z t) ⁻¹' A) =
      translate (T := V.cyclePeriod S E η) t ⁻¹' (V.orbitChart S hE hη ⁻¹' A) := by
    ext x
    simp only [mem_preimage, V.orbitChart_translate S hE hη]
  rw [hpre]
  exact (measurePreserving_translate_volume t).measure_preimage
    (V.measurable_orbitChart S hE hη hA).nullMeasurableSet

/-- **The ergodic components of `Σ_E` are the orbits of the cycles.**  A Borel set of regular
states that is `ν_E`-almost invariant under every `Φ_t` either misses or contains each orbit
`C_{E,c}` up to null sets, and so coincides `ν_E`-almost everywhere with a union of such orbits. -/
theorem invariant_ae_eq_biUnion {A : Set (RegularScatteringPhaseSpace (V := V) S)}
    (hA : MeasurableSet A)
    (hinv : ∀ t : ℝ, (fun z => flow V S z t) ⁻¹' A =ᵐ[V.regularShellMeasure S E] A) :
    (∀ c ∈ V.germCycles S E,
      V.regularShellMeasure S E (A ∩ V.cycleShellOrbit S hE c) = 0 ∨
        V.regularShellMeasure S E (V.cycleShellOrbit S hE c \ A) = 0) ∧
    ∃ J ⊆ V.germCycles S E, A =ᵐ[V.regularShellMeasure S E] ⋃ c ∈ J, V.cycleShellOrbit S hE c := by
  classical
  have hdich : ∀ c ∈ V.germCycles S E,
      V.regularShellMeasure S E (A ∩ V.cycleShellOrbit S hE c) = 0 ∨
        V.regularShellMeasure S E (V.cycleShellOrbit S hE c \ A) = 0 := by
    intro c hc
    obtain ⟨η, hη, -, hC⟩ := V.exists_of_mem_germCycles S hE hc
    haveI : Fact (0 < V.cyclePeriod S E η) := ⟨V.cyclePeriod_pos S hE hη⟩
    rw [hC]
    exact V.orbit_invariant_dichotomy S hE hη hA hinv
  refine ⟨hdich, (V.germCycles S E).filter
    (fun c => V.regularShellMeasure S E (V.cycleShellOrbit S hE c \ A) = 0),
    Finset.filter_subset _ _, ?_⟩
  set J := (V.germCycles S E).filter
    (fun c => V.regularShellMeasure S E (V.cycleShellOrbit S hE c \ A) = 0) with hJ
  have hU : MeasurableSet (⋃ c ∈ J, V.cycleShellOrbit S hE c) :=
    Finset.measurableSet_biUnion _ fun c _ => V.measurableSet_cycleShellOrbit S hE c
  refine ae_eq_set.mpr ⟨?_, ?_⟩
  · rw [V.regularShellMeasure_eq_sum S hE (hA.diff hU)]
    refine Finset.sum_eq_zero fun c hc => ?_
    by_cases hcJ : c ∈ J
    · refine measure_mono_null ?_ measure_empty
      rintro z ⟨⟨-, hzU⟩, hzc⟩
      exact hzU (mem_biUnion hcJ hzc)
    · have hne : V.regularShellMeasure S E (V.cycleShellOrbit S hE c \ A) ≠ 0 := fun h =>
        hcJ (Finset.mem_filter.mpr ⟨hc, h⟩)
      refine measure_mono_null ?_ ((hdich c hc).resolve_right hne)
      rintro z ⟨⟨hzA, -⟩, hzc⟩
      exact ⟨hzA, hzc⟩
  · refine measure_mono_null (t := ⋃ c ∈ J, (V.cycleShellOrbit S hE c \ A)) ?_ ?_
    · rintro z ⟨hzU, hzA⟩
      obtain ⟨c, hcJ, hzc⟩ := mem_iUnion₂.mp hzU
      exact mem_iUnion₂.mpr ⟨c, hcJ, hzc, hzA⟩
    · refine nonpos_iff_eq_zero.mp ((measure_biUnion_finset_le J _).trans (le_of_eq ?_))
      exact Finset.sum_eq_zero fun c hc => (Finset.mem_filter.mp hc).2

end Cycles

/-! ### Ergodicity of the energy surface -/

/-- **Ergodicity of the flow** for a measure `μ` on the regular quotient phase space: every Borel
set that is `μ`-almost invariant under every `Φ_t`, `t ∈ ℝ`, is `μ`-null or `μ`-conull. -/
def FlowErgodic (μ : Measure (RegularScatteringPhaseSpace (V := V) S)) : Prop :=
  ∀ A : Set (RegularScatteringPhaseSpace (V := V) S), MeasurableSet A →
    (∀ t : ℝ, (fun z => flow V S z t) ⁻¹' A =ᵐ[μ] A) → μ A = 0 ∨ μ Aᶜ = 0

/-- **The normalized time measure** `ν_E / ν_E(Σ_E)` of Proposition VII.1. -/
noncomputable def normalizedShellMeasure (E : ℝ) :
    Measure (RegularScatteringPhaseSpace (V := V) S) :=
  (V.regularShellMeasure S E univ)⁻¹ • V.regularShellMeasure S E

section Ergodic

variable {E : ℝ} (hE : V.ShellRegular E)
include hE

theorem regularShellMeasure_cycleShellOrbit_pos {c : Finset Γ.EdgeEnd}
    (hc : c ∈ V.germCycles S E) : 0 < V.regularShellMeasure S E (V.cycleShellOrbit S hE c) := by
  obtain ⟨η, hη, rfl, -⟩ := V.exists_of_mem_germCycles S hE hc
  rw [V.regularShellMeasure_cycleShellOrbit S hE hc]
  exact ENNReal.ofReal_pos.mpr (V.cyclePeriod_pos S hE hη)

/-- `Σ_E` is nonempty exactly when `Π_E` has a cycle. -/
theorem shell_nonempty_iff : (V.shell S E).Nonempty ↔ (V.germCycles S E).Nonempty := by
  rw [V.shell_eq_biUnion_cycleShellOrbit S hE]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨c, hc, -⟩ := mem_iUnion₂.mp hz
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    obtain ⟨η, hη, -, hC⟩ := V.exists_of_mem_germCycles S hE hc
    refine ⟨V.departureClass S hE η hη, mem_iUnion₂.mpr ⟨c, hc, ?_⟩⟩
    rw [hC]
    exact ⟨0, flow_zero V S _⟩

theorem regularShellMeasure_univ_ne_zero (h : (V.shell S E).Nonempty) :
    V.regularShellMeasure S E univ ≠ 0 := by
  obtain ⟨c, hc⟩ := (V.shell_nonempty_iff S hE).mp h
  exact (lt_of_lt_of_le (V.regularShellMeasure_cycleShellOrbit_pos S hE hc)
    (measure_mono (subset_univ _))).ne'

/-- On a nonempty shell the normalized time measure is a probability measure. -/
theorem isProbabilityMeasure_normalizedShellMeasure (h : (V.shell S E).Nonempty) :
    IsProbabilityMeasure (V.normalizedShellMeasure S E) :=
  ⟨by rw [normalizedShellMeasure, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel (V.regularShellMeasure_univ_ne_zero S hE h)
      (V.regularShellMeasure_univ_lt_top S hE).ne]⟩

/-- Normalizing does not change the null sets. -/
theorem normalizedShellMeasure_eq_zero_iff (X : Set (RegularScatteringPhaseSpace (V := V) S)) :
    V.normalizedShellMeasure S E X = 0 ↔ V.regularShellMeasure S E X = 0 := by
  rw [normalizedShellMeasure, Measure.smul_apply, smul_eq_mul, mul_eq_zero]
  simp only [ENNReal.inv_eq_zero, (V.regularShellMeasure_univ_lt_top S hE).ne, false_or]

theorem ae_normalizedShellMeasure :
    ae (V.normalizedShellMeasure S E) = ae (V.regularShellMeasure S E) :=
  Measure.ae_ennreal_smul_measure_eq
    (ENNReal.inv_ne_zero.mpr (V.regularShellMeasure_univ_lt_top S hE).ne) _

theorem flowErgodic_normalized_iff :
    V.FlowErgodic S (V.normalizedShellMeasure S E) ↔
      V.FlowErgodic S (V.regularShellMeasure S E) := by
  unfold FlowErgodic
  simp only [EventuallyEq, V.ae_normalizedShellMeasure S hE,
    V.normalizedShellMeasure_eq_zero_iff S hE]

/-- **A nonempty shell-regular energy surface is ergodic iff `Π_E` has exactly one cycle**, for
`ν_E` itself. -/
theorem flowErgodic_iff_card_germCycles (h : (V.shell S E).Nonempty) :
    V.FlowErgodic S (V.regularShellMeasure S E) ↔ (V.germCycles S E).card = 1 := by
  constructor
  · intro herg
    by_contra hne
    have hpos : (V.germCycles S E).Nonempty := (V.shell_nonempty_iff S hE).mp h
    have h1 : 1 < (V.germCycles S E).card := by
      have := hpos.card_pos
      omega
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp h1
    have hinv : ∀ t : ℝ, (fun z => flow V S z t) ⁻¹' V.cycleShellOrbit S hE c
        =ᵐ[V.regularShellMeasure S E] V.cycleShellOrbit S hE c := fun t => by
      rw [V.flow_preimage_cycleShellOrbit S hE hc t]
    rcases herg _ (V.measurableSet_cycleShellOrbit S hE c) hinv with h0 | h0
    · exact (V.regularShellMeasure_cycleShellOrbit_pos S hE hc).ne' h0
    · refine (V.regularShellMeasure_cycleShellOrbit_pos S hE hd).ne' (measure_mono_null ?_ h0)
      exact (V.pairwiseDisjoint_cycleShellOrbit S hE hc hd hcd).subset_compl_left
  · intro h1 A hA hinv
    obtain ⟨c, hc1⟩ := Finset.card_eq_one.mp h1
    have hc : c ∈ V.germCycles S E := by rw [hc1]; exact Finset.mem_singleton_self c
    have hsum : ∀ X, MeasurableSet X →
        V.regularShellMeasure S E X =
          V.regularShellMeasure S E (X ∩ V.cycleShellOrbit S hE c) := fun X hX => by
      rw [V.regularShellMeasure_eq_sum S hE hX, hc1, Finset.sum_singleton]
    rcases (V.invariant_ae_eq_biUnion S hE hA hinv).1 c hc with h0 | h0
    · exact Or.inl ((hsum A hA).trans h0)
    · right
      rw [hsum _ hA.compl, inter_comm, ← sdiff_eq]
      exact h0

/-- "`Π_E` has exactly one cycle", in terms of the permutation: all admissible ends lie in one
cycle. -/
theorem card_germCycles_eq_one_iff (h : (V.shell S E).Nonempty) :
    (V.germCycles S E).card = 1 ↔
      ∀ η ζ : V.allowedGerms E, (V.shellGermPerm S hE).SameCycle η ζ := by
  constructor
  · intro h1 η ζ
    obtain ⟨c, hc1⟩ := Finset.card_eq_one.mp h1
    have hη : V.germCycle S E η = c := Finset.mem_singleton.mp
      (hc1 ▸ (V.mem_germCycles S).mpr ⟨η, η.2, rfl⟩)
    have hζ : V.germCycle S E ζ = c := Finset.mem_singleton.mp
      (hc1 ▸ (V.mem_germCycles S).mpr ⟨ζ, ζ.2, rfl⟩)
    rw [← V.mem_germCycle_iff_sameCycle S hE, hη, ← hζ]
    exact V.self_mem_germCycle S hE ζ.2
  · intro hall
    obtain ⟨c₀, hc₀⟩ := (V.shell_nonempty_iff S hE).mp h
    obtain ⟨η₀, hη₀, -, -⟩ := V.exists_of_mem_germCycles S hE hc₀
    refine Finset.card_eq_one.mpr ⟨V.germCycle S E η₀, ?_⟩
    ext c
    rw [Finset.mem_singleton, V.mem_germCycles S]
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      have hmem : ζ ∈ V.germCycle S E η₀ :=
        (V.mem_germCycle_iff_sameCycle S hE ⟨η₀, hη₀⟩ ⟨ζ, hζ⟩).mpr (hall _ _)
      exact V.germCycle_eq_of_mem S hE hη₀ hmem
    · rintro rfl
      exact ⟨η₀, hη₀, rfl⟩

end Ergodic

/-! ### Remark VIII.6, packaged -/

section Packaged

variable {E : ℝ} (hE : V.ShellRegular E)

/-- **Remark VIII.6: the flow on an orbit is ergodic with pure point spectrum.**  Let `E` be
shell-regular, `η` an admissible end, `c` its cycle of `Π_E` and `T = T_c(E)` the period.  Then:

* the circle chart `u mod T ↦ Φ_u(departure state of η)` is a Borel bijection of `ℝ / Tℤ` onto the
  orbit `C_{E,c}` in which the flow is `u ↦ u + t mod T`;
* it carries the time measure `du` to `ν_E` restricted to `C_{E,c}`, and the normalized time
  measure `du / T` (`haarAddCircle`) to the normalized restriction `ν_E|_{C_{E,c}} / T`;
* the flow on `C_{E,c}` is ergodic: a Borel set `ν_E`-almost invariant under every `Φ_t` misses or
  contains `C_{E,c}` up to `ν_E`-null sets; on the circle, a set almost invariant under every
  translation has normalized measure `0` or `1`;
* pure point spectrum with frequencies `ω_n = 2πn/T`, `n ∈ ℤ`: the characters `fourier n` satisfy
  `e_n(u + t) = exp(i ω_n t) e_n(u)`, the Koopman operator of every translation multiplies the
  `n`-th element of the Hilbert basis `fourierBasis` of `L²(du / T)` by `exp(i ω_n t)`, and
  `fourierBasis` consists of the `L²` classes of the characters. -/
theorem orbit_ergodic_pointSpectrum (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E)
    [Fact (0 < V.cyclePeriod S E η)] :
    V.cycleShellOrbit S hE (V.germCycle S E η) = V.shellOrbit S hE η hη ∧
    Function.Injective (V.orbitChart S hE hη) ∧
    range (V.orbitChart S hE hη) = V.shellOrbit S hE η hη ∧
    Measurable (V.orbitChart S hE hη) ∧
    (∀ (t : ℝ) (x : AddCircle (V.cyclePeriod S E η)),
      V.orbitChart S hE hη (CircleFlow.translate t x) = flow V S (V.orbitChart S hE hη x) t) ∧
    Measure.map (V.orbitChart S hE hη) volume =
      (V.regularShellMeasure S E).restrict (V.shellOrbit S hE η hη) ∧
    Measure.map (V.orbitChart S hE hη) AddCircle.haarAddCircle =
      (ENNReal.ofReal (V.cyclePeriod S E η))⁻¹ •
        (V.regularShellMeasure S E).restrict (V.shellOrbit S hE η hη) ∧
    (∀ A : Set (RegularScatteringPhaseSpace (V := V) S), MeasurableSet A →
      (∀ t : ℝ, (fun z => flow V S z t) ⁻¹' A =ᵐ[V.regularShellMeasure S E] A) →
      V.regularShellMeasure S E (A ∩ V.shellOrbit S hE η hη) = 0 ∨
        V.regularShellMeasure S E (V.shellOrbit S hE η hη \ A) = 0) ∧
    (∀ s : Set (AddCircle (V.cyclePeriod S E η)), NullMeasurableSet s AddCircle.haarAddCircle →
      (∀ t : ℝ, CircleFlow.translate t ⁻¹' s =ᵐ[AddCircle.haarAddCircle] s) →
      AddCircle.haarAddCircle s = 0 ∨ AddCircle.haarAddCircle s = 1) ∧
    (∀ (n : ℤ) (t : ℝ) (x : AddCircle (V.cyclePeriod S E η)),
      fourier n (CircleFlow.translate t x) =
        Complex.exp (((frequency (V.cyclePeriod S E η) n * t : ℝ) : ℂ) * Complex.I) *
          fourier n x) ∧
    ⇑(fourierBasis (T := V.cyclePeriod S E η)) = fourierLp 2 ∧
    ∀ (n : ℤ) (t : ℝ),
      Lp.compMeasurePreserving (CircleFlow.translate t)
          (measurePreserving_translate (T := V.cyclePeriod S E η) t) (fourierBasis n) =
        Complex.exp (((frequency (V.cyclePeriod S E η) n * t : ℝ) : ℂ) * Complex.I) •
          fourierBasis n :=
  ⟨V.cycleShellOrbit_germCycle S hE hη, V.orbitChart_injective S hE hη,
    V.range_orbitChart S hE hη, V.measurable_orbitChart S hE hη,
    V.orbitChart_translate S hE hη, V.map_orbitChart_volume S hE hη,
    V.map_orbitChart_haarAddCircle S hE hη,
    fun _ hA hinv => V.orbit_invariant_dichotomy S hE hη hA hinv,
    circle_ergodic_pointSpectrum.2.1, circle_ergodic_pointSpectrum.2.2.1,
    circle_ergodic_pointSpectrum.2.2.2.1, circle_ergodic_pointSpectrum.2.2.2.2⟩

/-- **Remark VIII.6: the ergodic decomposition of a shell-regular energy surface.**  For a
shell-regular energy `E`, with `ν_E` the invariant time measure of Proposition VII.1 on the regular
quotient phase space and `C_{E,c}` the orbit of the cycle `c` of `Π_E`:

* `Σ_E = ⨆_c C_{E,c}`: the orbits of the cycles cover the shell and are pairwise disjoint; each is
  a Borel set, invariant under every `Φ_t`, of `ν_E`-mass `T_c(E) = ∑_{ζ ∈ c} t_E(ζ)`;
* `ν_E = ⊕_c ν_E|_{C_{E,c}}`, and `ν_E` is `Φ_t`-invariant;
* **the ergodic components are indexed by the cycles**: a Borel set `ν_E`-almost invariant under
  every `Φ_t` misses or contains each `C_{E,c}` up to null sets, hence coincides `ν_E`-a.e. with
  the union of the orbits of a set `J` of cycles;
* **a nonempty shell-regular energy surface is ergodic iff `Π_E` has exactly one cycle**: if
  `Σ_E ≠ ∅`, the normalized measure `ν_E / ν_E(Σ_E)` is a probability measure, it is ergodic for
  the flow iff `Π_E` has exactly one cycle, and this holds iff all admissible ends lie in one cycle
  of the permutation `Π_E`. -/
theorem shell_ergodic_iff_one_cycle :
    V.shell S E = ⋃ c ∈ V.germCycles S E, V.cycleShellOrbit S hE c ∧
    (↑(V.germCycles S E) : Set (Finset Γ.EdgeEnd)).PairwiseDisjoint (V.cycleShellOrbit S hE) ∧
    (∀ c ∈ V.germCycles S E, MeasurableSet (V.cycleShellOrbit S hE c) ∧
      (∀ t : ℝ, (fun z => flow V S z t) ⁻¹' V.cycleShellOrbit S hE c =
        V.cycleShellOrbit S hE c) ∧
      V.regularShellMeasure S E (V.cycleShellOrbit S hE c) =
        ENNReal.ofReal (∑ ζ ∈ c, V.flightTime E ζ)) ∧
    (∀ A : Set (RegularScatteringPhaseSpace (V := V) S), MeasurableSet A →
      V.regularShellMeasure S E A =
        ∑ c ∈ V.germCycles S E, V.regularShellMeasure S E (A ∩ V.cycleShellOrbit S hE c)) ∧
    (∀ t : ℝ, MeasurePreserving (fun z => flow V S z t) (V.regularShellMeasure S E)
      (V.regularShellMeasure S E)) ∧
    (∀ A : Set (RegularScatteringPhaseSpace (V := V) S), MeasurableSet A →
      (∀ t : ℝ, (fun z => flow V S z t) ⁻¹' A =ᵐ[V.regularShellMeasure S E] A) →
      (∀ c ∈ V.germCycles S E,
        V.regularShellMeasure S E (A ∩ V.cycleShellOrbit S hE c) = 0 ∨
          V.regularShellMeasure S E (V.cycleShellOrbit S hE c \ A) = 0) ∧
      ∃ J ⊆ V.germCycles S E,
        A =ᵐ[V.regularShellMeasure S E] ⋃ c ∈ J, V.cycleShellOrbit S hE c) ∧
    ((V.shell S E).Nonempty →
      IsProbabilityMeasure (V.normalizedShellMeasure S E) ∧
      (V.FlowErgodic S (V.normalizedShellMeasure S E) ↔ (V.germCycles S E).card = 1) ∧
      ((V.germCycles S E).card = 1 ↔
        ∀ η ζ : V.allowedGerms E, (V.shellGermPerm S hE).SameCycle η ζ)) :=
  ⟨V.shell_eq_biUnion_cycleShellOrbit S hE, V.pairwiseDisjoint_cycleShellOrbit S hE,
    fun _ hc => ⟨V.measurableSet_cycleShellOrbit S hE _,
      V.flow_preimage_cycleShellOrbit S hE hc, V.regularShellMeasure_cycleShellOrbit S hE hc⟩,
    fun _ hA => V.regularShellMeasure_eq_sum S hE hA,
    V.measurePreserving_flow_regularShellMeasure S hE,
    fun _ hA hinv => V.invariant_ae_eq_biUnion S hE hA hinv,
    fun h => ⟨V.isProbabilityMeasure_normalizedShellMeasure S hE h,
      (V.flowErgodic_normalized_iff S hE).trans (V.flowErgodic_iff_card_germCycles S hE h),
      V.card_germCycles_eq_one_iff S hE h⟩⟩

end Packaged

/-! ### The orbit as a measure space, and its spectrum on `L²(C_{E,c}, ν_E / T_c(E))` -/

section OrbitSpace

variable {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E)

/-- **The normalized time measure of the orbit `C_{E,c}`**, as a measure on the orbit itself:
`ν_E` restricted to `C_{E,c}` and divided by `T_c(E)`. -/
noncomputable def orbitMeasure : Measure (V.shellOrbit S hE η hη) :=
  (ENNReal.ofReal (V.cyclePeriod S E η))⁻¹ •
    (V.regularShellMeasure S E).comap (Subtype.val : V.shellOrbit S hE η hη → _)

theorem flow_mem_shellOrbit {z : RegularScatteringPhaseSpace (V := V) S}
    (hz : z ∈ V.shellOrbit S hE η hη) (t : ℝ) : flow V S z t ∈ V.shellOrbit S hE η hη := by
  have h := V.flow_preimage_shellOrbit S hE hη t
  rw [← h] at hz
  exact hz

/-- **The flow `Φ_t` restricted to the orbit `C_{E,c}`.** -/
noncomputable def orbitFlow (t : ℝ) (w : V.shellOrbit S hE η hη) : V.shellOrbit S hE η hη :=
  ⟨flow V S w.1 t, V.flow_mem_shellOrbit S hE hη w.2 t⟩

theorem measurable_orbitFlow (t : ℝ) : Measurable (V.orbitFlow S hE hη t) :=
  ((V.measurable_flow S t).comp measurable_subtype_coe).subtype_mk

variable [Fact (0 < V.cyclePeriod S E η)]

/-- The circle chart with values in the orbit. -/
noncomputable def orbitChartSubtype (x : AddCircle (V.cyclePeriod S E η)) :
    V.shellOrbit S hE η hη :=
  ⟨V.orbitChart S hE hη x, by rw [← V.range_orbitChart S hE hη]; exact mem_range_self x⟩

theorem bijective_orbitChartSubtype : Function.Bijective (V.orbitChartSubtype S hE hη) := by
  refine ⟨fun x y h => V.orbitChart_injective S hE hη (congrArg Subtype.val h), ?_⟩
  rintro ⟨w, hw⟩
  rw [← V.range_orbitChart S hE hη] at hw
  obtain ⟨x, rfl⟩ := hw
  exact ⟨x, rfl⟩

theorem measurableEmbedding_orbitChartSubtype :
    MeasurableEmbedding (V.orbitChartSubtype S hE hη) :=
  ((V.measurable_orbitChart S hE hη).subtype_mk).measurableEmbedding
    (V.bijective_orbitChartSubtype S hE hη).1

/-- **The circle chart as a Borel isomorphism** `ℝ / T_c(E)ℤ ≃ᵐ C_{E,c}`, `u ↦ Φ_u(departure state
of η)`.  The inverse is Borel by Lusin–Souslin. -/
noncomputable def orbitEquiv : AddCircle (V.cyclePeriod S E η) ≃ᵐ V.shellOrbit S hE η hη where
  toEquiv := Equiv.ofBijective _ (V.bijective_orbitChartSubtype S hE hη)
  measurable_toFun := (V.measurable_orbitChart S hE hη).subtype_mk
  measurable_invFun := fun s hs => by
    rw [← Equiv.image_eq_preimage_symm]
    exact (V.measurableEmbedding_orbitChartSubtype S hE hη).measurableSet_image' hs

@[simp] theorem orbitEquiv_apply_val (x : AddCircle (V.cyclePeriod S E η)) :
    (V.orbitEquiv S hE hη x).1 = V.orbitChart S hE hη x := rfl

/-- In the chart, `Φ_t` on the orbit is the translation by `t`. -/
theorem orbitEquiv_translate (t : ℝ) (x : AddCircle (V.cyclePeriod S E η)) :
    V.orbitEquiv S hE hη (CircleFlow.translate t x) =
      V.orbitFlow S hE hη t (V.orbitEquiv S hE hη x) :=
  Subtype.ext (V.orbitChart_translate S hE hη t x)

theorem orbitEquiv_symm_orbitFlow (t : ℝ) (w : V.shellOrbit S hE η hη) :
    (V.orbitEquiv S hE hη).symm (V.orbitFlow S hE hη t w) =
      CircleFlow.translate t ((V.orbitEquiv S hE hη).symm w) := by
  apply (V.orbitEquiv S hE hη).injective
  rw [MeasurableEquiv.apply_symm_apply, V.orbitEquiv_translate S hE hη,
    MeasurableEquiv.apply_symm_apply]

/-- **The chart is measure preserving** from the normalized Haar measure `du / T_c(E)` to the
normalized time measure `ν_E|_{C_{E,c}} / T_c(E)` of the orbit. -/
theorem measurePreserving_orbitEquiv :
    MeasurePreserving (V.orbitEquiv S hE hη) AddCircle.haarAddCircle
      (V.orbitMeasure S hE hη) := by
  have hO := V.measurableSet_shellOrbit S hE hη
  have hemb : MeasurableEmbedding (Subtype.val : V.shellOrbit S hE η hη → _) :=
    MeasurableEmbedding.subtype_coe hO
  refine ⟨(V.orbitEquiv S hE hη).measurable, Measure.ext fun B hB => ?_⟩
  have hB' : MeasurableSet (Subtype.val '' B) := hemb.measurableSet_image.mpr hB
  have h := congrArg (fun μ : Measure _ => μ (Subtype.val '' B))
    (V.map_orbitChart_haarAddCircle S hE hη)
  rw [Measure.map_apply (V.measurable_orbitChart S hE hη) hB', Measure.smul_apply,
    Measure.restrict_apply hB', inter_eq_left.mpr (by rintro _ ⟨w, -, rfl⟩; exact w.2)] at h
  have hpre : V.orbitChart S hE hη ⁻¹' (Subtype.val '' B) = V.orbitEquiv S hE hη ⁻¹' B := by
    ext x
    rw [mem_preimage, mem_preimage, ← V.orbitEquiv_apply_val S hE hη,
      Subtype.val_injective.mem_set_image]
  rw [Measure.map_apply (V.orbitEquiv S hE hη).measurable hB, ← hpre, h, orbitMeasure,
    Measure.smul_apply, hemb.comap_apply]

/-- **`Φ_t` preserves the normalized time measure of the orbit.** -/
theorem measurePreserving_orbitFlow (t : ℝ) :
    MeasurePreserving (V.orbitFlow S hE hη t) (V.orbitMeasure S hE hη)
      (V.orbitMeasure S hE hη) := by
  have heq : V.orbitFlow S hE hη t = V.orbitEquiv S hE hη ∘ CircleFlow.translate t ∘
      (V.orbitEquiv S hE hη).symm := by
    funext w
    simp only [Function.comp_apply]
    rw [V.orbitEquiv_translate S hE hη, MeasurableEquiv.apply_symm_apply]
  rw [heq]
  have hΦ := V.measurePreserving_orbitEquiv S hE hη
  exact hΦ.comp ((measurePreserving_translate t).comp (hΦ.symm _))

/-- **The `L²` isomorphism induced by the chart**: `g ↦ g ∘ (chart)⁻¹`,
`L²(du / T_c(E)) ≃ L²(C_{E,c}, ν_E / T_c(E))`. -/
noncomputable def orbitL2Equiv :
    Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle (V.cyclePeriod S E η))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (V.orbitMeasure S hE hη) :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ (V.orbitEquiv S hE hη).symm
      ((V.measurePreserving_orbitEquiv S hE hη).symm _))
    (fun g => ⟨Lp.compMeasurePreserving (V.orbitEquiv S hE hη)
      (V.measurePreserving_orbitEquiv S hE hη) g, by
      have hΦ := V.measurePreserving_orbitEquiv S hE hη
      have hΦs := hΦ.symm (V.orbitEquiv S hE hη)
      apply Lp.ext
      change ⇑(Lp.compMeasurePreserving _ hΦs (Lp.compMeasurePreserving _ hΦ g)) =ᵐ[_] ⇑g
      filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving _ hΦ g) hΦs,
        hΦs.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving g hΦ)] with w h1 h2
      rw [h1, h2]
      simp⟩)

theorem orbitL2Equiv_apply
    (g : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle (V.cyclePeriod S E η)))) :
    V.orbitL2Equiv S hE hη g = Lp.compMeasurePreserving (V.orbitEquiv S hE hη).symm
      ((V.measurePreserving_orbitEquiv S hE hη).symm _) g := rfl

/-- **The Fourier Hilbert basis of `L²(C_{E,c}, ν_E / T_c(E))`**: `e_n ∘ (chart)⁻¹`, `n ∈ ℤ`. -/
noncomputable def orbitFourierBasis : HilbertBasis ℤ ℂ (Lp ℂ 2 (V.orbitMeasure S hE hη)) :=
  HilbertBasis.ofRepr ((V.orbitL2Equiv S hE hη).symm.trans fourierBasis.repr)

theorem orbitFourierBasis_apply (n : ℤ) :
    V.orbitFourierBasis S hE hη n = V.orbitL2Equiv S hE hη (fourierBasis n) := rfl

/-- `orbitFourierBasis n` is the class of `w ↦ e_n((chart)⁻¹ w)`. -/
theorem coeFn_orbitFourierBasis (n : ℤ) :
    ⇑(V.orbitFourierBasis S hE hη n) =ᵐ[V.orbitMeasure S hE hη]
      fun w => fourier n ((V.orbitEquiv S hE hη).symm w) := by
  have hΦs := (V.measurePreserving_orbitEquiv S hE hη).symm (V.orbitEquiv S hE hη)
  rw [V.orbitFourierBasis_apply S hE hη, V.orbitL2Equiv_apply S hE hη, coe_fourierBasis]
  filter_upwards [Lp.coeFn_compMeasurePreserving (fourierLp (T := V.cyclePeriod S E η) 2 n) hΦs,
    hΦs.quasiMeasurePreserving.ae_eq_comp (coeFn_fourierLp (T := V.cyclePeriod S E η) 2 n)]
    with w h1 h2
  rw [h1]
  exact h2

/-- **Pure point spectrum on the orbit.**  The Koopman operator `f ↦ f ∘ Φ_t` of
`L²(C_{E,c}, ν_E / T_c(E))` multiplies the `n`-th element of `orbitFourierBasis` by
`exp(i ω_n t)`, `ω_n = 2πn / T_c(E)`. -/
theorem koopman_orbitFourierBasis (n : ℤ) (t : ℝ) :
    Lp.compMeasurePreserving (V.orbitFlow S hE hη t) (V.measurePreserving_orbitFlow S hE hη t)
        (V.orbitFourierBasis S hE hη n) =
      Complex.exp (((frequency (V.cyclePeriod S E η) n * t : ℝ) : ℂ) * Complex.I) •
        V.orbitFourierBasis S hE hη n := by
  have hF := V.measurePreserving_orbitFlow S hE hη t
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (V.orbitFourierBasis S hE hη n) hF,
    hF.quasiMeasurePreserving.ae_eq_comp (V.coeFn_orbitFourierBasis S hE hη n),
    Lp.coeFn_smul (Complex.exp (((frequency (V.cyclePeriod S E η) n * t : ℝ) : ℂ) * Complex.I))
      (V.orbitFourierBasis S hE hη n),
    V.coeFn_orbitFourierBasis S hE hη n] with w h1 h2 h3 h4
  simp only [Function.comp_apply] at h1 h2
  rw [h1, h2, h3, Pi.smul_apply, h4, smul_eq_mul, V.orbitEquiv_symm_orbitFlow S hE hη,
    fourier_translate]

end OrbitSpace

/-- **Remark VIII.6: pure point spectrum on `L²(C_{E,c}, ν_E / T_c(E))`.**  For a shell-regular `E`
and an admissible end `η` with cycle `c` and period `T = T_c(E)`:

* the circle chart is a Borel isomorphism `orbitEquiv : ℝ / Tℤ ≃ᵐ C_{E,c}` (inverse Borel by
  Lusin–Souslin), measure preserving from the normalized Haar measure `du / T` to the normalized
  time measure `orbitMeasure = ν_E|_{C_{E,c}} / T`, and conjugating the translation by `t` to
  `Φ_t|_{C_{E,c}}`;
* `Φ_t|_{C_{E,c}}` preserves `orbitMeasure`;
* the Koopman operators `f ↦ f ∘ Φ_t` of `L²(C_{E,c}, ν_E / T)` have the Hilbert basis
  `orbitFourierBasis` of eigenvectors, the classes of `e_n ∘ orbitEquiv⁻¹`,
  `e_n(u) = exp(2πinu/T)`, with eigenvalues `exp(i 2πn t / T)`, `n ∈ ℤ`. -/
theorem orbit_pointSpectrum {E : ℝ} (hE : V.ShellRegular E) (η : Γ.EdgeEnd)
    (hη : η ∈ V.allowedGerms E) [Fact (0 < V.cyclePeriod S E η)] :
    (∀ x, (V.orbitEquiv S hE hη x : RegularScatteringPhaseSpace (V := V) S) =
      V.orbitChart S hE hη x) ∧
    MeasurePreserving (V.orbitEquiv S hE hη) AddCircle.haarAddCircle (V.orbitMeasure S hE hη) ∧
    V.orbitMeasure S hE hη = (ENNReal.ofReal (V.cyclePeriod S E η))⁻¹ •
      (V.regularShellMeasure S E).comap (Subtype.val : V.shellOrbit S hE η hη → _) ∧
    (∀ (t : ℝ) (x : AddCircle (V.cyclePeriod S E η)),
      V.orbitEquiv S hE hη (CircleFlow.translate t x) =
        V.orbitFlow S hE hη t (V.orbitEquiv S hE hη x)) ∧
    (∀ (t : ℝ) (w : V.shellOrbit S hE η hη),
      (V.orbitFlow S hE hη t w : RegularScatteringPhaseSpace (V := V) S) = flow V S w.1 t) ∧
    (∀ t : ℝ, MeasurePreserving (V.orbitFlow S hE hη t) (V.orbitMeasure S hE hη)
      (V.orbitMeasure S hE hη)) ∧
    (∀ n : ℤ, ⇑(V.orbitFourierBasis S hE hη n) =ᵐ[V.orbitMeasure S hE hη]
      fun w => fourier n ((V.orbitEquiv S hE hη).symm w)) ∧
    ∀ (n : ℤ) (t : ℝ),
      Lp.compMeasurePreserving (V.orbitFlow S hE hη t) (V.measurePreserving_orbitFlow S hE hη t)
          (V.orbitFourierBasis S hE hη n) =
        Complex.exp (((frequency (V.cyclePeriod S E η) n * t : ℝ) : ℂ) * Complex.I) •
          V.orbitFourierBasis S hE hη n :=
  ⟨fun _ => rfl, V.measurePreserving_orbitEquiv S hE hη, rfl, V.orbitEquiv_translate S hE hη,
    fun _ _ => rfl, V.measurePreserving_orbitFlow S hE hη, V.coeFn_orbitFourierBasis S hE hη,
    V.koopman_orbitFourierBasis S hE hη⟩

end MechanicalPotential

end HamiltonianMetricGraphs
