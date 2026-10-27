/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Remark VIII.6: the translation flow on a circle of length `T`
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircle

/-!
# The translation flow on `ℝ / Tℤ` (Remark VIII.6)

Remark VIII.6 says that on the periodic orbit `C_{E,c}` of a shell-regular energy surface the flow
is `u ↦ u + t mod T_c(E)`, that this flow is ergodic for the normalized time measure, and that it
has pure point spectrum with frequencies `2πn / T_c(E)`, `n ∈ ℤ`.  This module proves these
statements for the model flow, the translation flow on the additive circle `AddCircle T = ℝ / Tℤ`
with its normalized Haar measure `haarAddCircle` (Lebesgue measure `du / T`).  The transport to the
orbits of the graph flow is `ShellErgodic.lean`.

* `measurePreserving_translate`: every translation `x ↦ x + t` preserves the normalized measure.
* `haarAddCircle_eq_zero_or_one_of_invariant`, **ergodicity of the flow**: a null-measurable set
  which is almost invariant under *every* translation `x ↦ x + t`, `t ∈ ℝ`, has measure `0` or
  `1`.  (Invariance under the whole flow is required: a single rational rotation is not ergodic.)
  The proof applies Mathlib's density-point theorem `ae_empty_or_univ_of_forall_vadd_ae_eq_self`
  to the rotations by `T / (n + 1)`, whose orders `n + 1` tend to infinity.
* `fourier_translate` and `koopman_fourierBasis`, **pure point spectrum**: the characters
  `e_n(u) = exp(2πinu/T)` satisfy `e_n(u + t) = exp(i ω_n t) e_n(u)` with the frequency
  `ω_n = 2πn/T` (`frequency T n`), so each `e_n` is an eigenfunction of the Koopman operator
  `U_t f = f ∘ (· + t)` on `L²` with eigenvalue `exp(i ω_n t)`; and the `e_n` form Mathlib's Hilbert
  basis `fourierBasis` of `L²(haarAddCircle)`.  So `L²` has an orthonormal basis of
  eigenfunctions of the whole Koopman group — pure point spectrum — and the frequencies are exactly
  `2πn/T`, `n ∈ ℤ`.
-/

namespace HamiltonianMetricGraphs

namespace CircleFlow

open Set Filter MeasureTheory AddCircle
open scoped ENNReal Real

variable {T : ℝ}

/-- **The translation flow** on `ℝ / Tℤ`: `u ↦ u + t mod T`. -/
def translate (t : ℝ) (x : AddCircle T) : AddCircle T := x + (t : AddCircle T)

@[simp] theorem translate_coe (t u : ℝ) :
    translate t (u : AddCircle T) = ((u + t : ℝ) : AddCircle T) := by
  simp [translate]

theorem translate_add (s t : ℝ) (x : AddCircle T) :
    translate t (translate s x) = translate (s + t) x := by
  simp only [translate, AddCircle.coe_add, add_assoc]

/-- **The frequency** `ω_n = 2πn / T` of the `n`-th eigenfunction. -/
noncomputable def frequency (T : ℝ) (n : ℤ) : ℝ := 2 * π * n / T

variable [hT : Fact (0 < T)]

omit hT in
theorem measurable_translate (t : ℝ) : Measurable (translate (T := T) t) :=
  measurable_add_const _

/-- The translations preserve the normalized Haar (Lebesgue) measure `du / T`. -/
theorem measurePreserving_translate (t : ℝ) :
    MeasurePreserving (translate (T := T) t) haarAddCircle haarAddCircle :=
  measurePreserving_add_right _ _

/-- The translations preserve the time measure `du` of total mass `T`. -/
theorem measurePreserving_translate_volume (t : ℝ) :
    MeasurePreserving (translate (T := T) t) volume volume :=
  measurePreserving_add_right _ _

/-- The normalized measure and the time measure have the same null sets. -/
theorem ae_haarAddCircle : ae (haarAddCircle : Measure (AddCircle T)) = ae volume := by
  rw [volume_eq_smul_haarAddCircle, Measure.ae_ennreal_smul_measure_eq]
  exact (ENNReal.ofReal_pos.mpr hT.out).ne'

/-- **Ergodicity of the translation flow, for the time measure.**  A null-measurable set that is
almost invariant under every translation is almost empty or almost everything. -/
theorem ae_empty_or_univ_of_translate_invariant {s : Set (AddCircle T)}
    (hs : NullMeasurableSet s volume) (hinv : ∀ t : ℝ, translate t ⁻¹' s =ᵐ[volume] s) :
    s =ᵐ[volume] (∅ : Set (AddCircle T)) ∨ s =ᵐ[volume] univ := by
  refine ae_empty_or_univ_of_forall_vadd_ae_eq_self hs (l := atTop)
    (u := fun n : ℕ => ((T / (n + 1 : ℕ) : ℝ) : AddCircle T)) (fun n => ?_) ?_
  · convert hinv (-(T / (n + 1 : ℕ))) using 1
    refine Set.ext fun x => ?_
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, mem_preimage, translate, vadd_eq_add, add_comm,
      AddCircle.coe_neg]
  · have hord : ∀ n : ℕ, addOrderOf (((T / (n + 1 : ℕ) : ℝ)) : AddCircle T) = n + 1 :=
      fun n => addOrderOf_period_div (Nat.succ_pos n)
    simp only [Function.comp_def, hord]
    exact tendsto_add_atTop_nat 1

/-- **Ergodicity of the translation flow, for the normalized time measure.**  A null-measurable set
almost invariant under every translation `u ↦ u + t` has normalized measure `0` or `1`. -/
theorem haarAddCircle_eq_zero_or_one_of_invariant {s : Set (AddCircle T)}
    (hs : NullMeasurableSet s haarAddCircle)
    (hinv : ∀ t : ℝ, translate t ⁻¹' s =ᵐ[haarAddCircle] s) :
    haarAddCircle s = 0 ∨ haarAddCircle s = 1 := by
  have hs' : NullMeasurableSet s volume := by
    rw [NullMeasurableSet] at hs ⊢
    obtain ⟨t, ht, hst⟩ := hs
    refine ⟨t, ht, ?_⟩
    rw [EventuallyEq, ← ae_haarAddCircle]
    exact hst
  have hinv' : ∀ t : ℝ, translate t ⁻¹' s =ᵐ[volume] s := fun t => by
    rw [EventuallyEq, ← ae_haarAddCircle]; exact hinv t
  rcases ae_empty_or_univ_of_translate_invariant hs' hinv' with h | h
  · left
    rw [EventuallyEq, ← ae_haarAddCircle] at h
    rw [measure_congr h, measure_empty]
  · right
    rw [EventuallyEq, ← ae_haarAddCircle] at h
    rw [measure_congr h, measure_univ]

omit hT in
/-- **The characters are eigenfunctions of the flow**: `e_n(u + t) = exp(i ω_n t) e_n(u)` with
`ω_n = 2πn/T`. -/
theorem fourier_translate (n : ℤ) (t : ℝ) (x : AddCircle T) :
    fourier n (translate t x) =
      Complex.exp (((frequency T n * t : ℝ) : ℂ) * Complex.I) * fourier n x := by
  induction x using QuotientAddGroup.induction_on with
  | H u =>
    rw [translate_coe, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
    congr 1
    unfold frequency
    push_cast
    field_simp
    ring

/-- **Pure point spectrum.**  The Koopman operator `U_t f = f ∘ (· + t)` of the translation flow on
`L²(haarAddCircle)` acts on the `n`-th element of the Fourier Hilbert basis as multiplication by
`exp(i ω_n t)`, `ω_n = 2πn/T`. -/
theorem koopman_fourierBasis (n : ℤ) (t : ℝ) :
    Lp.compMeasurePreserving (translate t) (measurePreserving_translate (T := T) t)
        (fourierBasis n) =
      Complex.exp (((frequency T n * t : ℝ) : ℂ) * Complex.I) • fourierBasis n := by
  apply Lp.ext
  rw [coe_fourierBasis]
  filter_upwards [Lp.coeFn_compMeasurePreserving (fourierLp 2 n)
      (measurePreserving_translate (T := T) t),
    (measurePreserving_translate (T := T) t).quasiMeasurePreserving.ae_eq_comp
      (coeFn_fourierLp (T := T) 2 n),
    Lp.coeFn_smul (Complex.exp (((frequency T n * t : ℝ) : ℂ) * Complex.I)) (fourierLp 2 n),
    coeFn_fourierLp (T := T) 2 n] with x h1 h2 h3 h4
  simp only [Function.comp_apply] at h1 h2 h3
  rw [h1, h2, h3, Pi.smul_apply, h4, smul_eq_mul, fourier_translate]

/-- **Remark VIII.6 for the model flow.**  The translation flow `u ↦ u + t mod T` on `ℝ / Tℤ` with
its normalized time measure:

* preserves the measure;
* is ergodic: a null-measurable set almost invariant under every translation has measure `0` or
  `1`;
* has pure point spectrum with frequencies `ω_n = 2πn/T`, `n ∈ ℤ`: the characters `fourier n` are
  eigenfunctions with eigenvalue `exp(i ω_n t)`, both pointwise and for the Koopman operator on
  `L²`, and their `L²` classes are the Hilbert basis `fourierBasis` of `L²(haarAddCircle)`. -/
theorem circle_ergodic_pointSpectrum :
    (∀ t : ℝ, MeasurePreserving (translate (T := T) t) haarAddCircle haarAddCircle) ∧
    (∀ s : Set (AddCircle T), NullMeasurableSet s haarAddCircle →
      (∀ t : ℝ, translate t ⁻¹' s =ᵐ[haarAddCircle] s) →
      haarAddCircle s = 0 ∨ haarAddCircle s = 1) ∧
    (∀ (n : ℤ) (t : ℝ) (x : AddCircle T), fourier n (translate t x) =
      Complex.exp (((frequency T n * t : ℝ) : ℂ) * Complex.I) * fourier n x) ∧
    ⇑(fourierBasis (T := T)) = fourierLp 2 ∧
    ∀ (n : ℤ) (t : ℝ),
      Lp.compMeasurePreserving (translate t) (measurePreserving_translate (T := T) t)
          (fourierBasis n) =
        Complex.exp (((frequency T n * t : ℝ) : ℂ) * Complex.I) • fourierBasis n :=
  ⟨measurePreserving_translate, fun _ hs hinv => haarAddCircle_eq_zero_or_one_of_invariant hs hinv,
    fourier_translate, coe_fourierBasis, koopman_fourierBasis⟩

end CircleFlow

end HamiltonianMetricGraphs
