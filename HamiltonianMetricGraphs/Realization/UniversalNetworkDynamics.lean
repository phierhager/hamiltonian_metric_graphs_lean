/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalNetworkPotential

/-!
# Every trajectory of the uniform network

This file studies **every** solution of Hamilton's equations for
`H_ε(x, p) = ½|p|² + uniPot F ε x` on `[0, ∞)`, not a solution constructed for the purpose:

* the energy `½|p|² + uniPot F ε x` is conserved (`hamEnergy_eq`);
* a trajectory which starts in the tube `|w - uniRow ζ| < 2ε` of the corridor of `ζ` with energy
  below the wall height `4` stays in that tube forever (`uni_confined`).  The argument is energy
  conservation together with the intermediate value theorem: the barrier `uniPot ≥ 4` fills the
  whole gap between two tubes, so the transverse coordinate can neither cross it nor jump it;
* on the tube the force is separable, so the longitudinal pair `(u, p_u)` solves the
  one-dimensional system of the corridor *exactly* (`uni_longitudinal`).  In a circle corridor it
  is free motion for all time (`uni_free_of_not_fold`).

Every initial state in a tube with energy below `4` has a trajectory on `[0, ∞)`
(`exists_uniTrajectory` in `UniversalNetworkExistence.lean`), so the statements are not
vacuous.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph
open scoped Topology

variable {Γ : FiniteMetricGraph} {ε : ℝ}

/-! ### Calculus on `ℝ²` -/

theorem hasDerivWithinAt_pairFst {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f f' s t) : HasDerivWithinAt (fun r => (f r).1) f'.1 s t :=
  (hasFDerivAt_fst (𝕜 := ℝ) (p := f t)).comp_hasDerivWithinAt t h

theorem hasDerivWithinAt_pairSnd {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f f' s t) : HasDerivWithinAt (fun r => (f r).2) f'.2 s t :=
  (hasFDerivAt_snd (𝕜 := ℝ) (p := f t)).comp_hasDerivWithinAt t h

/-- The derivative of a differentiable function on `ℝ²` is given by its two partial
derivatives. -/
theorem fderiv_apply_eq_partialDerivs {W : ℝ × ℝ → ℝ} (hW : Differentiable ℝ W) (y v : ℝ × ℝ) :
    fderiv ℝ W y v = v.1 * deriv (fun s => W (s, y.2)) y.1 +
      v.2 * deriv (fun s => W (y.1, s)) y.2 := by
  have h1 : HasDerivAt (fun s => W (s, y.2)) (fderiv ℝ W y (1, 0)) y.1 := by
    have hc : HasDerivAt (fun s : ℝ => (s, y.2)) ((1 : ℝ), (0 : ℝ)) y.1 :=
      (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2)
    exact (hW y).hasFDerivAt.comp_hasDerivAt y.1 hc
  have h2 : HasDerivAt (fun s => W (y.1, s)) (fderiv ℝ W y (0, 1)) y.2 := by
    have hc : HasDerivAt (fun s : ℝ => (y.1, s)) ((0 : ℝ), (1 : ℝ)) y.2 :=
      (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)
    exact (hW y).hasFDerivAt.comp_hasDerivAt y.2 hc
  rw [h1.deriv, h2.deriv]
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-! ### Conservation of energy -/

/-- **Conservation of energy** along every trajectory of `½|p|² + W(x)`, for a `C¹` potential. -/
theorem hamEnergy_eq {W : ℝ × ℝ → ℝ} (hW : ContDiff ℝ 1 W) {x p : ℝ → ℝ × ℝ}
    (hsol : IsHamiltonianTrajectory W x p) {t : ℝ} (ht : 0 ≤ t) :
    hamEnergy W (x t) (p t) = hamEnergy W (x 0) (p 0) := by
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hderiv : ∀ s, 0 ≤ s →
      HasDerivWithinAt (fun r => hamEnergy W (x r) (p r)) 0 (Ici 0) s := by
    intro s hs
    obtain ⟨hx, hp⟩ := hsol s hs
    have hp1 := hasDerivWithinAt_pairFst hp
    have hp2 := hasDerivWithinAt_pairSnd hp
    have hWx : HasDerivWithinAt (fun r => W (x r)) (fderiv ℝ W (x s) (p s)) (Ici 0) s :=
      (hWd (x s)).hasFDerivAt.comp_hasDerivWithinAt s hx
    refine ((((hp1.pow 2).add (hp2.pow 2)).div_const 2).add hWx).congr_deriv ?_
    rw [fderiv_apply_eq_partialDerivs hWd]
    simp only [gradForce]
    push_cast
    ring
  have hcont : ContinuousOn (fun r => hamEnergy W (x r) (p r)) (Icc 0 t) := fun s hs =>
    (hderiv s hs.1).continuousWithinAt.mono Icc_subset_Ici_self
  have h := constant_of_has_deriv_right_zero hcont
    (fun s hs => (hderiv s hs.1).mono (Ici_subset_Ici.mpr hs.1)) t ⟨ht, le_rfl⟩
  exact h

/-! ### Confinement to the tube of a corridor -/

/-- **Thin-tube confinement for every trajectory.**  A trajectory of the uniform network which
starts in the tube of the corridor of `ζ` with energy below the wall height `4` stays in that
tube for all time. -/
theorem uni_confined (F : RoutingLaw Γ) (hε : 0 < ε) (hεs : ε ≤ 1 / 8) {x p : ℝ → ℝ × ℝ}
    (hsol : IsHamiltonianTrajectory (uniPot F ε) x p) (ζ : Γ.EdgeEnd)
    (h0 : |(x 0).2 - uniRow ζ| < 2 * ε) (hE : hamEnergy (uniPot F ε) (x 0) (p 0) < 4) :
    ∀ t, 0 ≤ t → |(x t).2 - uniRow ζ| < 2 * ε := by
  -- at every time the particle is in some tube, hence either in the tube of `ζ` or far from it
  have hdich : ∀ t, 0 ≤ t → |(x t).2 - uniRow ζ| < 2 * ε ∨ 1 - 2 * ε < |(x t).2 - uniRow ζ| := by
    intro t ht
    have hEt := hamEnergy_eq (contDiff_uniPot F ε) hsol ht
    have hlt : uniPot F ε (x t) < 4 := by
      have hk : 0 ≤ ((p t).1 ^ 2 + (p t).2 ^ 2) / 2 := by positivity
      simp only [hamEnergy] at hEt hE
      linarith
    have hex : ∃ ζ' : Γ.EdgeEnd, |(x t).2 - uniRow ζ'| < 2 * ε := by
      by_contra hcon
      push Not at hcon
      have h4 := uniPot_ge_four_of_far F hε (u := (x t).1) (w := (x t).2) hcon
      exact absurd hlt (not_lt.mpr h4)
    obtain ⟨ζ', hζ'⟩ := hex
    by_cases heq : ζ' = ζ
    · exact Or.inl (heq ▸ hζ')
    · right
      have hsep := one_le_abs_uniRow_sub heq
      have htri := abs_index_sub_le (uniRow ζ') (uniRow ζ) (x t).2
      linarith
  intro t ht
  by_contra hcon
  rw [not_lt] at hcon
  have hcont : ContinuousOn (fun r => |(x r).2 - uniRow ζ|) (Icc 0 t) := by
    have hx : ContinuousOn x (Icc 0 t) := fun s hs =>
      ((hsol s hs.1).1.continuousWithinAt).mono Icc_subset_Ici_self
    exact ((continuous_snd.comp_continuousOn hx).sub continuousOn_const).abs
  have hivt := intermediate_value_Icc ht hcont
  obtain ⟨s, hs, hfs⟩ := hivt ⟨h0.le, hcon⟩
  rcases hdich s hs.1 with h | h
  · simp only at hfs; linarith
  · simp only at hfs; linarith

/-- **Exact projection to the corridor system.**  Along a confined trajectory the longitudinal pair
solves `u' = p_u`, `p_u' = -longPot'(u)` on `[0, ∞)`. -/
theorem uni_longitudinal (F : RoutingLaw Γ) (hε : 0 < ε) (hεs : ε ≤ 1 / 8) {x p : ℝ → ℝ × ℝ}
    (hsol : IsHamiltonianTrajectory (uniPot F ε) x p) (ζ : Γ.EdgeEnd)
    (hconf : ∀ t, 0 ≤ t → |(x t).2 - uniRow ζ| < 2 * ε) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => (x s).1) (p t).1 (Ici 0) t ∧
      HasDerivWithinAt (fun s => (p s).1) (-deriv (longPot F ε ζ) (x t).1) (Ici 0) t := by
  obtain ⟨hx, hp⟩ := hsol t ht
  refine ⟨hasDerivWithinAt_pairFst hx, ?_⟩
  have h := hasDerivWithinAt_pairFst hp
  rwa [gradForce_uniPot_of_tube F hε hεs ζ (hconf t ht)] at h

/-- **In a circle corridor the longitudinal motion is free for all time.** -/
theorem uni_free_of_not_fold (F : RoutingLaw Γ) (hε : 0 < ε) (hεs : ε ≤ 1 / 8)
    {x p : ℝ → ℝ × ℝ} (hsol : IsHamiltonianTrajectory (uniPot F ε) x p) (ζ : Γ.EdgeEnd)
    (hconf : ∀ t, 0 ≤ t → |(x t).2 - uniRow ζ| < 2 * ε) (hnf : ¬ ∃ k, IsFold F ζ k)
    {t : ℝ} (ht : 0 ≤ t) :
    (p t).1 = (p 0).1 ∧ (x t).1 = (x 0).1 + (p 0).1 * t := by
  have hlong := fun s (hs : 0 ≤ s) => uni_longitudinal F hε hεs hsol ζ hconf hs
  have hzero : ∀ s, 0 ≤ s → HasDerivWithinAt (fun r => (p r).1) 0 (Ici 0) s := by
    intro s hs
    have h := (hlong s hs).2
    rwa [longPot_of_not_fold F ε ζ hnf, deriv_const, neg_zero] at h
  have hpconst : ∀ s, 0 ≤ s → (p s).1 = (p 0).1 := by
    intro s hs
    have hcont : ContinuousOn (fun r => (p r).1) (Icc 0 s) := fun r hr =>
      (hzero r hr.1).continuousWithinAt.mono Icc_subset_Ici_self
    exact constant_of_has_deriv_right_zero hcont
      (fun r hr => (hzero r hr.1).mono (Ici_subset_Ici.mpr hr.1)) s ⟨hs, le_rfl⟩
  refine ⟨hpconst t ht, ?_⟩
  have hd : ∀ s, 0 ≤ s →
      HasDerivWithinAt (fun r => (x r).1 - (p 0).1 * r) 0 (Ici 0) s := by
    intro s hs
    have h1 := (hlong s hs).1
    rw [hpconst s hs] at h1
    have h2 := ((hasDerivWithinAt_id s (Ici 0)).const_mul ((p 0).1))
    exact (h1.sub h2).congr_deriv (by ring)
  have hcont : ContinuousOn (fun r => (x r).1 - (p 0).1 * r) (Icc 0 t) := fun r hr =>
    (hd r hr.1).continuousWithinAt.mono Icc_subset_Ici_self
  have h := constant_of_has_deriv_right_zero hcont
    (fun r hr => (hd r hr.1).mono (Ici_subset_Ici.mpr hr.1)) t ⟨ht, le_rfl⟩
  simp only [mul_zero, sub_zero] at h
  linarith

/-- **In an interval corridor the longitudinal motion is an exact corridor solution.** -/
theorem uni_corridorSolution_of_fold (F : RoutingLaw Γ) (hε : 0 < ε) (hεs : ε ≤ 1 / 8)
    {x p : ℝ → ℝ × ℝ} (hsol : IsHamiltonianTrajectory (uniPot F ε) x p) (ζ : Γ.EdgeEnd)
    (hconf : ∀ t, 0 ≤ t → |(x t).2 - uniRow ζ| < 2 * ε) (hf : ∃ k, IsFold F ζ k)
    {c Tmax : ℝ} (hlen : 1000 * ε ≤ corridorLen F ζ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hT : 0 ≤ Tmax) (hp0 : (p 0).1 = c) (hu0 : (x 0).1 ∈ Icc 0 (corridorLen F ζ)) :
    CorridorSolution ε (corridorLen F ζ) c Tmax (fun s => (x s).1) (fun s => (p s).1) := by
  have hlong := fun s (hs : 0 ≤ s) => uni_longitudinal F hε hεs hsol ζ hconf hs
  rw [longPot_of_fold F ε ζ hf] at hlong
  refine corridorSolution_of_net (m := 1) (Λ := fun _ => corridorLen F ζ) (i := 0) hε hlen hc1
    hc2 hT (fun t ht => (hlong t ht.1).1.mono Icc_subset_Ici_self)
    (fun t ht => (hlong t ht.1).2.mono Icc_subset_Ici_self) ?_
  rw [hp0, corridorPot_of_mem hε hu0.1 hu0.2]
  ring

end HamiltonianMetricGraphs
