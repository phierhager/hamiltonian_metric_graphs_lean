/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Remark VIII.6: the disintegration of the Liouville measure over energy
-/

import HamiltonianMetricGraphs.ShellMeasure
import HamiltonianMetricGraphs.LiouvilleMeasure
import HamiltonianMetricGraphs.FlowMeasurable

/-!
# The quotient Liouville measure disintegrates over energy (Remark VIII.6)

Remark VIII.6 opens with the disintegration `m = ∫_ℝ ν_E dE` of the quotient Liouville measure `m`
(Definition IV.5) into the invariant time measures `ν_E` of Proposition VII.1.  This module proves
it, for every Borel set and every nonnegative Borel function, with the development's `ν_E`.

## Encoding

The development realises `ν_E` on the edge phase planes (`ShellMeasure.lean`): `shellMeasure E e`
is the time density `dq / √(2(E - V_e(q)))` on `[0, ℓ_e]` pushed to the two momentum sheets
`p = ±√(2(E - V_e(q)))`.  The paper's `ν_E` is the pushforward of these branch measures under
`q ↦ π(e, q, ±√(2(E - V_e(q))))`; here `π(e, x)` is `graphClass V S (e, x)`, the class of the graph
phase point in the scattering quotient.  So the measure of Proposition VII.1 on the quotient is

`quotientShellMeasure S E = ∑_e (x ↦ π(e, x))_* (shellMeasure E e)`,

and `lintegral_quotientShellMeasure` checks that integrating against it is literally the formula
defining `ν_E` in Proposition VII.1, with the branch integrals over `U_e(E) = {V_e < E} ∩ (0, ℓ_e)`.
It is defined for every `E`; the remark's "for almost every `E`" is not needed.

## Results

* `lintegral_edgeLiouville_eq`, **the edge form**: for every edge `e` and Borel `F ≥ 0` on the
  phase plane, `∫ F dq dp = ∫_ℝ (∫ F dν_E^e) dE` over the closed edge cylinder.  Fibrewise this is
  `dp = dE / |p|` on each momentum sheet: for fixed `q`, the substitution `E = V_e(q) + p²/2`,
  `dE = p dp`, turns `∫ (F(q, √(2(E-V))) + F(q, -√(2(E-V)))) dE / √(2(E-V))` into
  `∫_{p>0} (F(q, p) + F(q, -p)) dp = ∫_ℝ F(q, p) dp` (`lintegral_timeDensity_fibre`); Tonelli
  swaps the `q`- and `E`-integrals.
* `lintegral_quotientLiouville_eq`, **the quotient form**: `∫ f dm = ∫_ℝ (∫ f dν_E) dE` for every
  Borel `f ≥ 0` on the scattering quotient, and `m(A) = ∫ ν_E(A) dE` for Borel `A`.  The quotient
  measure is the pushforward of the nonzero prequotient Liouville measure, which is the sum of the
  edge Liouville measures off the Liouville-null set of zero-momentum vertex states, so this
  reduces to the edge form.
* `remark_disintegration` packages these.

The local expression `dm = dη r dr du` of the remark, in boundary flow-box coordinates, is
Lemma VI.1 (`TubeForm.lean`, `lintegral_tube_form_speed`); with `E = r²/2 + V(v)` it reads
`dE = r dr`, the boundary counterpart of the fibrewise identity `dE = p dp` used here.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The fibre identity `dp = dE / |p|` -/

/-- **The fibre identity.**  For a fixed potential value `v` and a Borel `G ≥ 0`, integrating
`G(±√(2(E - v)))` against `dE / √(2(E - v))` over all energies is integrating `G(p)` against `dp`:
the substitution `E = v + p²/2` has `dE = p dp`. -/
theorem lintegral_timeDensity_fibre (v : ℝ) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ E, ENNReal.ofReal (1 / Real.sqrt (2 * (E - v))) *
        (G (Real.sqrt (2 * (E - v))) + G (-Real.sqrt (2 * (E - v)))) = ∫⁻ p, G p := by
  set H : ℝ → ℝ≥0∞ := fun E => ENNReal.ofReal (1 / Real.sqrt (2 * (E - v))) *
    (G (Real.sqrt (2 * (E - v))) + G (-Real.sqrt (2 * (E - v)))) with hH
  -- the integrand vanishes below `v`
  have hlow : ∫⁻ E in (Ioi v)ᶜ, H E = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi.compl (g := fun _ => 0) (fun E hE => ?_)]
    · simp
    · have hE : E ≤ v := not_lt.mp hE
      simp only [hH]
      rw [Real.sqrt_eq_zero_of_nonpos (by linarith), div_zero, ENNReal.ofReal_zero, zero_mul]
  rw [← lintegral_add_compl H measurableSet_Ioi, hlow, add_zero]
  -- the substitution `E = v + s²/2` on `s > 0`
  have himg : (fun s : ℝ => v + s ^ 2 / 2) '' Ioi 0 = Ioi v := by
    ext E
    constructor
    · rintro ⟨s, hs, rfl⟩
      have : 0 < s ^ 2 / 2 := by have := pow_pos (mem_Ioi.mp hs) 2; linarith
      exact mem_Ioi.mpr (by linarith)
    · intro hE
      have hE' : 0 < 2 * (E - v) := by have := mem_Ioi.mp hE; linarith
      refine ⟨Real.sqrt (2 * (E - v)), Real.sqrt_pos.mpr hE', ?_⟩
      simp only
      rw [Real.sq_sqrt hE'.le]
      ring
  have hderiv : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun s : ℝ => v + s ^ 2 / 2) s (Ioi 0) s := by
    intro s _
    have h := ((hasDerivAt_pow 2 s).div_const 2).const_add v
    have he : (↑(2 : ℕ) * s ^ (2 - 1) / 2 : ℝ) = s := by norm_num
    rw [he] at h
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => v + s ^ 2 / 2) (Ioi 0) := by
    intro s hs t ht hst
    have h2 : s ^ 2 = t ^ 2 := by simp only at hst; linarith
    exact (pow_left_inj₀ (mem_Ioi.mp hs).le (mem_Ioi.mp ht).le two_ne_zero).mp h2
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj H]
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      ENNReal.ofReal |s| * H (v + s ^ 2 / 2) = G s + G (-s) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hsq : Real.sqrt (2 * (v + s ^ 2 / 2 - v)) = s := by
      rw [show 2 * (v + s ^ 2 / 2 - v) = s ^ 2 by ring, Real.sqrt_sq hs0.le]
    simp only [hH]
    rw [hsq, abs_of_pos hs0, ← mul_assoc, ← ENNReal.ofReal_mul hs0.le, mul_one_div_cancel hs0.ne',
      ENNReal.ofReal_one, one_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt,
    lintegral_add_left hG]
  -- the negative sheet
  have hneg : ∫⁻ s in Ioi (0 : ℝ), G (-s) = ∫⁻ p in Iio (0 : ℝ), G p := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Iio]
    have hcomp : (Ioi (0 : ℝ)).indicator (fun s => G (-s)) =
        fun s => (Iio (0 : ℝ)).indicator G (-s) := by
      funext s
      by_cases hs : s ∈ Ioi (0 : ℝ)
      · have hs' : -s ∈ Iio (0 : ℝ) := by
          simp only [mem_Ioi] at hs; simp only [mem_Iio]; linarith
        rw [indicator_of_mem hs, indicator_of_mem hs']
      · have hs' : -s ∉ Iio (0 : ℝ) := by
          simp only [mem_Ioi, not_lt] at hs; simp only [mem_Iio, not_lt]; linarith
        rw [indicator_of_notMem hs, indicator_of_notMem hs']
    rw [hcomp]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp
      (hG.indicator measurableSet_Iio)
  rw [hneg, add_comm, ← lintegral_union measurableSet_Ioi
    ((Iic_disjoint_Ioi le_rfl).mono_left Iio_subset_Iic_self), Iio_union_Ioi]
  have hnull : ({0}ᶜ : Set ℝ) =ᵐ[volume] univ := by
    rw [ae_eq_univ, compl_compl]
    exact measure_singleton 0
  rw [setLIntegral_congr hnull, Measure.restrict_univ]

/-! ### The edge form -/

/-- The potential of the edge `e` clamped to the closed edge: a continuous function on `ℝ` that
agrees with `V_e` on `[0, ℓ_e]`.  It makes the integrands below jointly Borel in `(E, q)`. -/
noncomputable def clampedPotential (e : Γ.Edge) (q : ℝ) : ℝ :=
  V.extension e (Set.projIcc 0 (Γ.length e) (Γ.length_pos e).le q)

theorem continuous_clampedPotential (e : Γ.Edge) : Continuous (V.clampedPotential e) :=
  (V.extension_continuousOn_closedEdge e).comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun _ => Subtype.mem _)

theorem clampedPotential_of_mem (e : Γ.Edge) {q : ℝ} (hq : q ∈ Icc 0 (Γ.length e)) :
    V.clampedPotential e q = V.extension e q := by
  unfold clampedPotential
  rw [Set.projIcc_of_mem _ hq]

/-- The integrand of `ν_E^e` against `F`, as a jointly Borel function of `(E, q)`. -/
noncomputable def shellIntegrand (e : Γ.Edge) (F : ℝ × ℝ → ℝ≥0∞) (z : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.sqrt (2 * (z.1 - V.clampedPotential e z.2))) *
    (F (z.2, Real.sqrt (2 * (z.1 - V.clampedPotential e z.2))) +
      F (z.2, -Real.sqrt (2 * (z.1 - V.clampedPotential e z.2))))

theorem measurable_shellIntegrand (e : Γ.Edge) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (V.shellIntegrand e F) := by
  have hc : Continuous fun z : ℝ × ℝ => Real.sqrt (2 * (z.1 - V.clampedPotential e z.2)) := by
    have := V.continuous_clampedPotential e
    fun_prop
  unfold shellIntegrand
  refine Measurable.mul ?_ (Measurable.add ?_ ?_)
  · exact ENNReal.measurable_ofReal.comp (hc.measurable.const_div 1)
  · exact hF.comp (measurable_snd.prodMk hc.measurable)
  · exact hF.comp (measurable_snd.prodMk hc.measurable.neg)

/-- Integration against `ν_E^e` as an integral of the jointly Borel integrand over the edge. -/
theorem lintegral_shellMeasure_eq (e : Γ.Edge) (E : ℝ) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(V.shellMeasure E e) =
      ∫⁻ q in Icc 0 (Γ.length e), V.shellIntegrand e F (E, q) := by
  have hA : AEMeasurable (fun q => V.timeDensity e E q * F (q, 1 * V.speedAt e E q))
      (volume.restrict (Icc 0 (Γ.length e))) :=
    (V.aemeasurable_timeDensity e E).mul (hF.comp_aemeasurable (measurable_id.aemeasurable.prodMk
      (((V.continuousOn_speedAt e E).aemeasurable measurableSet_Icc).const_mul 1)))
  rw [shellMeasure, lintegral_add_measure, V.lintegral_sheetMeasure e E 1 hF,
    V.lintegral_sheetMeasure e E (-1) hF, ← lintegral_add_left' hA]
  refine setLIntegral_congr_fun measurableSet_Icc (fun q hq => ?_)
  simp only [shellIntegrand, timeDensity, speedAt, V.clampedPotential_of_mem e hq, one_mul,
    neg_mul]
  rw [mul_add]

/-- `E ↦ ∫ F dν_E^e` is Borel. -/
theorem measurable_lintegral_shellMeasure (e : Γ.Edge) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun E => ∫⁻ x, F x ∂(V.shellMeasure E e) := by
  have h : (fun E => ∫⁻ x, F x ∂(V.shellMeasure E e)) =
      fun E => ∫⁻ q, V.shellIntegrand e F (E, q) ∂(volume.restrict (Icc 0 (Γ.length e))) :=
    funext fun E => V.lintegral_shellMeasure_eq e E hF
  rw [h]
  exact (V.measurable_shellIntegrand e hF).lintegral_prod_right'

/-- Integration against the edge Liouville measure is integration over the closed edge cylinder. -/
theorem lintegral_edgeLiouville (e : Γ.Edge) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x.1 ∂(Γ.edgeLiouville e) = ∫⁻ q in Icc 0 (Γ.length e), ∫⁻ p, F (q, p) := by
  have hEP : MeasurableSet (Γ.EdgePhase e) := measurable_fst measurableSet_Icc
  rw [FiniteMetricGraph.edgeLiouville, ← (MeasurableEmbedding.subtype_coe hEP).lintegral_map,
    map_comap_subtype_coe hEP]
  have hset : Γ.EdgePhase e = Icc 0 (Γ.length e) ×ˢ (univ : Set ℝ) := by
    ext x; simp [FiniteMetricGraph.EdgePhase]
  rw [hset, Measure.volume_eq_prod, setLIntegral_prod F hF.aemeasurable]
  simp only [Measure.restrict_univ]

/-- **Remark VIII.6, the edge form: `dq dp = dE · dq/|p|`.**  On the closed cylinder of the edge
`e`, the Liouville measure disintegrates over energy into the invariant time measures of
Proposition VII.1: for every Borel `F ≥ 0`,

`∫ F dq dp = ∫_ℝ (∫ F dν_E^e) dE`. -/
theorem lintegral_edgeLiouville_eq (e : Γ.Edge) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x.1 ∂(Γ.edgeLiouville e) = ∫⁻ E, ∫⁻ x, F x ∂(V.shellMeasure E e) := by
  simp_rw [V.lintegral_shellMeasure_eq e _ hF]
  have hswap := lintegral_lintegral_swap (μ := (volume : Measure ℝ))
    (ν := volume.restrict (Icc 0 (Γ.length e))) (f := fun E q => V.shellIntegrand e F (E, q))
    (by exact (V.measurable_shellIntegrand e hF).aemeasurable)
  rw [hswap, lintegral_edgeLiouville e hF]
  refine setLIntegral_congr_fun measurableSet_Icc (fun q _ => ?_)
  exact (lintegral_timeDensity_fibre (V.clampedPotential e q)
    (hF.comp measurable_prodMk_left)).symm

/-! ### The quotient form -/

variable (S : BorelEnergyPreservingScattering V)

/-- **The invariant time measure `ν_E` of Proposition VII.1 on the scattering quotient**: the
pushforward of the branch measures `dq / √(2(E - V_e(q)))` on the two momentum sheets under
`x ↦ π(e, x)`, summed over the edges. -/
noncomputable def quotientShellMeasure (E : ℝ) : Measure (ScatteringPhaseSpace (V := V) S) :=
  ∑ e, (V.shellMeasure E e).map (fun x => graphClass V S (e, x))

theorem measurable_graphClass_edge (e : Γ.Edge) :
    Measurable fun x : ℝ × ℝ => graphClass V S (e, x) :=
  (V.measurable_graphClass S).comp measurable_prodMk_left

theorem lintegral_quotientShellMeasure (E : ℝ) {f : ScatteringPhaseSpace (V := V) S → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z, f z ∂(V.quotientShellMeasure S E) =
      ∑ e, ∫⁻ x, f (graphClass V S (e, x)) ∂(V.shellMeasure E e) := by
  rw [quotientShellMeasure, lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [lintegral_map hf (V.measurable_graphClass_edge S e)]

/-- **`quotientShellMeasure` is the measure of Proposition VII.1.**  For every Borel `f ≥ 0` on the
quotient, `∫ f dν_E = ∑_e ∑_{ε = ±1} ∫_{U_e(E)} f(π(e, q, ε√(2(E - V_e(q))))) dq/√(2(E - V_e(q)))`,
with `U_e(E) = {q ∈ (0, ℓ_e) : V_e(q) < E}`. -/
theorem lintegral_quotientShellMeasure_eq_branches (E : ℝ)
    {f : ScatteringPhaseSpace (V := V) S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(V.quotientShellMeasure S E) =
      ∑ e, ((∫⁻ q in V.allowedPositions e E,
          V.timeDensity e E q * f (graphClass V S (e, q, V.speedAt e E q))) +
        ∫⁻ q in V.allowedPositions e E,
          V.timeDensity e E q * f (graphClass V S (e, q, -V.speedAt e E q))) := by
  rw [V.lintegral_quotientShellMeasure S E hf]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hF : Measurable fun x => f (graphClass V S (e, x)) :=
    hf.comp (V.measurable_graphClass_edge S e)
  rw [shellMeasure, lintegral_add_measure, V.lintegral_sheetMeasure e E 1 hF,
    V.lintegral_sheetMeasure e E (-1) hF, V.setLIntegral_Icc_eq_allowedPositions,
    V.setLIntegral_Icc_eq_allowedPositions]
  simp only [one_mul, neg_mul]

/-- The quotient Liouville measure as a sum of edge Liouville measures: the zero-momentum vertex
states removed in the nonzero prequotient are Liouville-null. -/
theorem lintegral_quotientLiouville_eq_sum {f : ScatteringPhaseSpace (V := V) S → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z, f z ∂(quotientLiouville (V := V) S) =
      ∑ e, ∫⁻ x, f (graphClass V S (e, x.1)) ∂(Γ.edgeLiouville e) := by
  set h : Γ.PrequotientPhase → ℝ≥0∞ := fun y => f (graphClass V S (y.1, y.2.1)) with hhdef
  have hh : Measurable h := hf.comp ((V.measurable_graphClass S).comp
    (measurable_prequotientEdge.prodMk
      (measurable_prequotientPosition.prodMk measurable_prequotientMomentum)))
  have hNZ : MeasurableSet {x : Γ.PrequotientPhase |
      x.2.1.1 ∈ Ioo (0 : ℝ) (Γ.length x.1) ∨ x.2.1.2 ≠ 0} :=
    measurableSet_nonzeroPrequotientPhase
  have hemb : MeasurableEmbedding
      (Subtype.val : Γ.NonzeroPrequotientPhase → Γ.PrequotientPhase) :=
    MeasurableEmbedding.subtype_coe hNZ
  have hx : ∀ x : Γ.NonzeroPrequotientPhase, f (quotientMap (V := V) S x) = h x.1 := fun x => by
    simp only [hhdef, graphClass, Γ.graphPoint_of_nonzero x]
  rw [quotientLiouville, lintegral_map hf (measurable_quotientMap (V := V) S)]
  simp_rw [hx]
  rw [FiniteMetricGraph.nonzeroPrequotientLiouville, ← hemb.lintegral_map, hemb.map_comap,
    Subtype.range_coe, Measure.restrict_eq_self_of_ae_mem ?_]
  · rw [FiniteMetricGraph.prequotientLiouville, lintegral_sum_measure, tsum_fintype]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [lintegral_map hh (Γ.measurable_prequotientSigmaMk e)]
  · rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) Γ.prequotientLiouville_boundary_null
    have hy' : ¬ (y.2.1.1 ∈ Ioo (0 : ℝ) (Γ.length y.1) ∨ y.2.1.2 ≠ 0) := hy
    have h1 : y.2.1.1 ∈ Icc (0 : ℝ) (Γ.length y.1) := y.2.2
    rw [not_or] at hy'
    change y.2.1.1 = 0 ∨ y.2.1.1 = Γ.length y.1
    rcases eq_or_lt_of_le h1.1 with h0 | h0
    · exact Or.inl h0.symm
    · right
      by_contra hne
      exact hy'.1 ⟨h0, lt_of_le_of_ne h1.2 hne⟩

/-- **Remark VIII.6, the quotient form: `m = ∫ ν_E dE`.**  For every Borel `f ≥ 0` on the
scattering quotient, `∫ f dm = ∫_ℝ (∫ f dν_E) dE`. -/
theorem lintegral_quotientLiouville_eq {f : ScatteringPhaseSpace (V := V) S → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z, f z ∂(quotientLiouville (V := V) S) = ∫⁻ E, ∫⁻ z, f z ∂(V.quotientShellMeasure S E) := by
  rw [V.lintegral_quotientLiouville_eq_sum S hf]
  simp_rw [V.lintegral_quotientShellMeasure S _ hf]
  have hm : ∀ e : Γ.Edge, Measurable fun x => f (graphClass V S (e, x)) := fun e =>
    hf.comp (V.measurable_graphClass_edge S e)
  rw [lintegral_finsetSum _ (fun e _ => V.measurable_lintegral_shellMeasure e (hm e))]
  exact Finset.sum_congr rfl fun e _ => V.lintegral_edgeLiouville_eq e (hm e)

/-- **Remark VIII.6, `m = ∫ ν_E dE` on sets**: `m(A) = ∫_ℝ ν_E(A) dE` for every Borel `A`. -/
theorem quotientLiouville_apply_eq {A : Set (ScatteringPhaseSpace (V := V) S)}
    (hA : MeasurableSet A) :
    quotientLiouville (V := V) S A = ∫⁻ E, V.quotientShellMeasure S E A := by
  have h := V.lintegral_quotientLiouville_eq S (measurable_one.indicator hA)
  simp only [lintegral_indicator_one hA] at h
  exact h

/-- **Remark VIII.6, the disintegration of the Liouville measure over energy.**

* On every edge cylinder, `∫ F dq dp = ∫_ℝ (∫ F dν_E^e) dE` for Borel `F ≥ 0` (that is,
  `dq dp = dE · dq/|p|` on each momentum sheet).
* `ν_E` on the quotient, `quotientShellMeasure S E`, integrates `f` exactly by the formula of
  Proposition VII.1.
* On the scattering quotient, `∫ f dm = ∫_ℝ (∫ f dν_E) dE` for Borel `f ≥ 0`, and
  `m(A) = ∫_ℝ ν_E(A) dE` for Borel `A`.

The local form `dm = dη r dr du` in boundary flow-box coordinates is Lemma VI.1
(`lintegral_tube_form_speed`). -/
theorem remark_disintegration :
    (∀ (e : Γ.Edge) (F : ℝ × ℝ → ℝ≥0∞), Measurable F →
      ∫⁻ x, F x.1 ∂(Γ.edgeLiouville e) = ∫⁻ E, ∫⁻ x, F x ∂(V.shellMeasure E e)) ∧
    (∀ (E : ℝ) (f : ScatteringPhaseSpace (V := V) S → ℝ≥0∞), Measurable f →
      ∫⁻ z, f z ∂(V.quotientShellMeasure S E) =
        ∑ e, ((∫⁻ q in V.allowedPositions e E,
            V.timeDensity e E q * f (graphClass V S (e, q, V.speedAt e E q))) +
          ∫⁻ q in V.allowedPositions e E,
            V.timeDensity e E q * f (graphClass V S (e, q, -V.speedAt e E q)))) ∧
    (∀ f : ScatteringPhaseSpace (V := V) S → ℝ≥0∞, Measurable f →
      ∫⁻ z, f z ∂(quotientLiouville (V := V) S) =
        ∫⁻ E, ∫⁻ z, f z ∂(V.quotientShellMeasure S E)) ∧
    ∀ A : Set (ScatteringPhaseSpace (V := V) S), MeasurableSet A →
      quotientLiouville (V := V) S A = ∫⁻ E, V.quotientShellMeasure S E A :=
  ⟨fun e _ hF => V.lintegral_edgeLiouville_eq e hF,
    fun E _ hf => V.lintegral_quotientShellMeasure_eq_branches S E hf,
    fun _ hf => V.lintegral_quotientLiouville_eq S hf,
    fun _ hA => V.quotientLiouville_apply_eq S hA⟩

end MechanicalPotential

end HamiltonianMetricGraphs
