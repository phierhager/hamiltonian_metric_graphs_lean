/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import Mathlib

/-!
# Elementary interval estimates for one-sided derivatives

Every flight of a hybrid chain is a curve with a derivative *within* a closed time interval
(one-sided at the two endpoints).  This file collects the mean-value-type estimates used for
such curves: growth bounds from one-sided bounds on the derivative, the distance-travelled bound,
component extraction for `ℝ × ℝ`-valued curves, and the conversion to the right-derivative form
required by Mathlib's Grönwall inequality.

Mathematical proof step: these are the "speed × time" and "force × time" estimates used
throughout the transverse-crossing and no-Zeno arguments.
-/

open Set Filter
open scoped Topology

section Components

variable {α : ℝ → ℝ × ℝ} {w : ℝ × ℝ} {s : Set ℝ} {t : ℝ}

/-- The first component of a derivative of an `ℝ × ℝ`-valued curve. -/
theorem HasDerivWithinAt.fst_comp (h : HasDerivWithinAt α w s t) :
    HasDerivWithinAt (fun u => (α u).1) w.1 s t := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have h' := (hasDerivWithinAt_const t s L).clm_apply h
  simpa [L] using h'

/-- The second component of a derivative of an `ℝ × ℝ`-valued curve. -/
theorem HasDerivWithinAt.snd_comp (h : HasDerivWithinAt α w s t) :
    HasDerivWithinAt (fun u => (α u).2) w.2 s t := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have h' := (hasDerivWithinAt_const t s L).clm_apply h
  simpa [L] using h'

end Components

namespace HamiltonianMetricGraphs

section Growth

variable {f f' : ℝ → ℝ} {a b C : ℝ}

/-- A derivative within `[a, b]` is a right derivative at every point of `[a, b)`.  This is the
form in which Mathlib's Grönwall inequality consumes derivative hypotheses. -/
theorem hasDerivWithinAt_Ici_of_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {g' : E} {t : ℝ} (ht : t ∈ Ico a b)
    (h : HasDerivWithinAt g g' (Icc a b) t) : HasDerivWithinAt g g' (Ici t) t :=
  h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- A derivative within `[a, b]` at an interior point is a genuine derivative. -/
theorem hasDerivAt_of_hasDerivWithinAt_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → E} {g' : E} {t : ℝ} (ht : t ∈ Ioo a b)
    (h : HasDerivWithinAt g g' (Icc a b) t) : HasDerivAt g g' t :=
  h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- Upper growth bound: if `f' ≤ C` on `[a, b]` then `f b - f a ≤ C (b - a)`. -/
theorem image_sub_le_mul_sub_of_hasDerivWithinAt_le (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t)
    (hC : ∀ t ∈ Icc a b, f' t ≤ C) : f b - f a ≤ C * (b - a) := by
  have hcont : ContinuousOn f (Icc a b) := fun t ht => (hf t ht).continuousWithinAt
  have hderiv : ∀ t ∈ interior (Icc a b), HasDerivAt f (f' t) t := by
    intro t ht
    rw [interior_Icc] at ht
    exact hasDerivAt_of_hasDerivWithinAt_Icc ht (hf t (Ioo_subset_Icc_self ht))
  exact (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hcont
    (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hderiv t ht).deriv]; exact hC t (interior_subset ht))
    a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab

/-- Lower growth bound: if `C ≤ f'` on `[a, b]` then `C (b - a) ≤ f b - f a`. -/
theorem mul_sub_le_image_sub_of_le_hasDerivWithinAt (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t)
    (hC : ∀ t ∈ Icc a b, C ≤ f' t) : C * (b - a) ≤ f b - f a := by
  have h : -f b - -f a ≤ -C * (b - a) :=
    image_sub_le_mul_sub_of_hasDerivWithinAt_le (f := fun t => -f t) (f' := fun t => -f' t)
      (C := -C) hab (fun t ht => (hf t ht).neg) (fun t ht => neg_le_neg (hC t ht))
  linarith

/-- The two-sided growth bound on any subinterval `[s, t]` of `[a, b]`. -/
theorem image_sub_le_mul_sub_of_hasDerivWithinAt_le' {s t : ℝ}
    (hf : ∀ u ∈ Icc a b, HasDerivWithinAt f (f' u) (Icc a b) u)
    (hC : ∀ u ∈ Icc a b, f' u ≤ C) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    f t - f s ≤ C * (t - s) := by
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  exact image_sub_le_mul_sub_of_hasDerivWithinAt_le hst
    (fun u hu => (hf u (hsub hu)).mono hsub) (fun u hu => hC u (hsub hu))

theorem mul_sub_le_image_sub_of_le_hasDerivWithinAt' {s t : ℝ}
    (hf : ∀ u ∈ Icc a b, HasDerivWithinAt f (f' u) (Icc a b) u)
    (hC : ∀ u ∈ Icc a b, C ≤ f' u) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    C * (t - s) ≤ f t - f s := by
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  exact mul_sub_le_image_sub_of_le_hasDerivWithinAt hst
    (fun u hu => (hf u (hsub hu)).mono hsub) (fun u hu => hC u (hsub hu))

/-- Distance-travelled bound for a real function: `|f' | ≤ C` on `[a, b]` gives
`|f t - f s| ≤ C (t - s)` for `s ≤ t` in `[a, b]`. -/
theorem abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le {s t : ℝ}
    (hf : ∀ u ∈ Icc a b, HasDerivWithinAt f (f' u) (Icc a b) u)
    (hC : ∀ u ∈ Icc a b, |f' u| ≤ C) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    |f t - f s| ≤ C * (t - s) := by
  have h₁ := image_sub_le_mul_sub_of_hasDerivWithinAt_le' hf
    (fun u hu => (abs_le.mp (hC u hu)).2) hs ht hst
  have h₂ := mul_sub_le_image_sub_of_le_hasDerivWithinAt' (C := -C) hf
    (fun u hu => (abs_le.mp (hC u hu)).1) hs ht hst
  rw [abs_le]
  constructor <;> linarith

end Growth

section Vector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Distance-travelled bound for a vector-valued curve with a derivative within `[a, b]`
bounded in norm by `C`: `dist (g t) (g s) ≤ C (t - s)` for `s ≤ t` in `[a, b]`. -/
theorem dist_le_mul_sub_of_norm_hasDerivWithinAt_le {g : ℝ → E} {g' : ℝ → E} {a b C s t : ℝ}
    (hg : ∀ u ∈ Icc a b, HasDerivWithinAt g (g' u) (Icc a b) u)
    (hC : ∀ u ∈ Icc a b, ‖g' u‖ ≤ C) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    dist (g t) (g s) ≤ C * (t - s) := by
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := s) (b := t) (f := g) (f' := g')
    (fun u hu => (hg u (hsub hu)).mono hsub)
    (fun u hu => hC u (hsub (Ico_subset_Icc_self hu))) t (right_mem_Icc.mpr hst)
  rwa [dist_eq_norm]

end Vector

section Eventually

/-- A property holds eventually as `ε → 0⁺` if it holds on some interval `(0, ε₀)`. -/
theorem eventually_nhdsGT_zero_of_forall_Ioo {P : ℝ → Prop} {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h : ∀ ε ∈ Ioo (0 : ℝ) ε₀, P ε) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P ε :=
  Filter.mem_of_superset (Ioo_mem_nhdsGT hε₀) h

/-- Conversely, an eventual property as `ε → 0⁺` holds on some interval `(0, ε₀)`. -/
theorem exists_Ioo_of_eventually_nhdsGT_zero {P : ℝ → Prop}
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P ε) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, P ε := by
  rcases (nhdsGT_basis (0 : ℝ)).eventually_iff.mp h with ⟨ε₀, hε₀, hP⟩
  exact ⟨ε₀, hε₀, hP⟩

/-- Positive quantities tend to zero as `ε → 0⁺` iff they are eventually below every bound. -/
theorem eventually_lt_of_tendsto_nhds_zero {u : ℝ → ℝ}
    (hu : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), u ε < η := by
  have := hu (Iio_mem_nhds hη)
  exact this

end Eventually

end HamiltonianMetricGraphs
