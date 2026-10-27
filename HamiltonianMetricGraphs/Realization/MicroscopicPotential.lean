/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.BarrierProfile

/-!
# The explicit microscopic potential of the thin three-channel network

The microscopic configuration space is the plane `ℝ²` with coordinates `(u, w)`.  The graph `Γ⋆`
is embedded as three straight segments meeting at the origin `v⋆`:

* edge `0` along the negative `u`-axis, with graph coordinate `q = -u`;
* edge `1` along the positive `u`-axis, with graph coordinate `q = u`;
* edge `2` along the positive `w`-axis, with graph coordinate `q = w`;

the outer vertices sit at `u = -1`, `u = +1` and `w = +1`.

For a scale `ε > 0` the potential is

  `microPot ε (u,w) = (1 - m) · (wellPot ε w + capPot ε u) + m · (wellPot ε u + armPot ε w)`,
  `m = mixW ε w = plateau (3ε) (6ε) w`.

* On the **through-channel region** `w < 3ε` we have `m = 0`, so
  `microPot ε (u,w) = wellPot ε w + capPot ε u` — an exact sum of a function of `w` and a
  function of `u`.  The dynamics there is therefore **exactly separable**: the transverse energy
  `½p_w² + wellPot ε w` and the longitudinal energy `½p_u² + capPot ε u` are conserved
  independently.  In the tube core `|w| ≤ ε`, `|u| ≤ 1` the potential vanishes identically, so the
  longitudinal motion is **exactly free** — exactly the graph dynamics of the zero potential.
* On the **third-arm region** `w > 6ε` we have `m = 1` and the potential is again an exact sum,
  now confining in `u` and with the junction barrier and the cap in `w`.
* On the **interpolation zone** `3ε ≤ w ≤ 6ε` both summands are at least `4`, hence
  `microPot ε ≥ 4` there (`microPot_ge_four_of_mid`).  Since every energy in the window
  `K⋆ = [1/2,2]` is below `4`, a particle can **never enter the interpolation zone**: the two
  separable regions are dynamically disconnected, and no estimate on the glue is ever needed.

This is what makes the model both genuinely branching (three channels meeting at one junction)
and completely analysable.
-/

namespace HamiltonianMetricGraphs

open Set Real

/-! ### The scaled one-dimensional pieces -/

/-- The transverse confining wall at scale `ε`: zero on the core `|z| ≤ ε`, full height outside
`|z| ≥ 2ε`. -/
noncomputable def wellPot (ε z : ℝ) : ℝ := wellProfile (z / ε)

/-- The longitudinal potential of the through-channel: reflecting caps at the outer vertices
`u = ±1`, and nothing in between. -/
noncomputable def capPot (ε u : ℝ) : ℝ :=
  barrierProfile ((u - 1) / ε) + barrierProfile ((-u - 1) / ε)

/-- The longitudinal potential of the third arm: the junction barrier just above `w = 6ε`, which
separates the arm from the junction, and the reflecting cap at the outer vertex `w = 1`. -/
noncomputable def armPot (ε w : ℝ) : ℝ :=
  barrierProfile ((7 * ε - w) / ε) + barrierProfile ((w - 1) / ε)

/-- The interpolation weight between the two separable regions. -/
noncomputable def mixW (ε w : ℝ) : ℝ := plateau (3 * ε) (6 * ε) w

/-! #### Values -/

theorem wellPot_nonneg (ε z : ℝ) : 0 ≤ wellPot ε z := wellProfile_nonneg _

theorem wellPot_le (ε z : ℝ) : wellPot ε z ≤ 4 := wellProfile_le _

/-- The tube core is flat. -/
theorem wellPot_of_abs_le (hε : 0 < ε) {z : ℝ} (h : |z| ≤ ε) : wellPot ε z = 0 := by
  refine wellProfile_of_abs_le_one ?_
  rw [abs_div, abs_of_pos hε, div_le_one hε]
  exact h

/-- Outside the tube the wall is at full height. -/
theorem wellPot_of_two_le_abs (hε : 0 < ε) {z : ℝ} (h : 2 * ε ≤ |z|) : wellPot ε z = 4 := by
  refine wellProfile_of_two_le_abs ?_
  rw [abs_div, abs_of_pos hε, le_div_iff₀ hε]
  linarith

/-- A transverse energy below `4` confines the particle to the tube. -/
theorem abs_lt_two_mul_of_wellPot_lt (hε : 0 < ε) {z : ℝ} (h : wellPot ε z < 4) :
    |z| < 2 * ε := by
  by_contra hcon
  rw [not_lt] at hcon
  rw [wellPot_of_two_le_abs hε hcon] at h
  exact lt_irrefl _ h

theorem capPot_nonneg (ε u : ℝ) : 0 ≤ capPot ε u :=
  add_nonneg (barrierProfile_nonneg _) (barrierProfile_nonneg _)

/-- **The tube is flat**: on the whole closed edge `|u| ≤ 1` the longitudinal potential vanishes,
so the longitudinal motion there is exactly free. -/
theorem capPot_of_abs_le_one (hε : 0 < ε) {u : ℝ} (h : |u| ≤ 1) : capPot ε u = 0 := by
  have h1 : u ≤ 1 := (abs_le.mp h).2
  have h2 : -1 ≤ u := (abs_le.mp h).1
  rw [capPot, barrierProfile_of_nonpos (by
      apply div_nonpos_of_nonpos_of_nonneg _ hε.le
      linarith),
    barrierProfile_of_nonpos (by
      apply div_nonpos_of_nonpos_of_nonneg _ hε.le
      linarith), add_zero]

/-- Beyond the right cap the potential is at the confining height. -/
theorem capPot_ge_of_right (hε : 0 < ε) {u : ℝ} (h : 1 + ε ≤ u) : 4 ≤ capPot ε u := by
  have hb : 4 ≤ barrierProfile ((u - 1) / ε) := by
    refine barrierProfile_ge_of_one_le ?_
    rw [le_div_iff₀ hε]
    linarith
  have := barrierProfile_nonneg ((-u - 1) / ε)
  rw [capPot]
  linarith

/-- Beyond the left cap the potential is at the confining height. -/
theorem capPot_ge_of_left (hε : 0 < ε) {u : ℝ} (h : u ≤ -1 - ε) : 4 ≤ capPot ε u := by
  have hb : 4 ≤ barrierProfile ((-u - 1) / ε) := by
    refine barrierProfile_ge_of_one_le ?_
    rw [le_div_iff₀ hε]
    linarith
  have := barrierProfile_nonneg ((u - 1) / ε)
  rw [capPot]
  linarith

theorem armPot_nonneg (ε w : ℝ) : 0 ≤ armPot ε w :=
  add_nonneg (barrierProfile_nonneg _) (barrierProfile_nonneg _)

/-- The junction barrier is at full height below `6ε`: this is what separates the third arm from
the junction. -/
theorem armPot_ge_of_le_six (hε : 0 < ε) {w : ℝ} (h : w ≤ 6 * ε) : 4 ≤ armPot ε w := by
  have hb : 4 ≤ barrierProfile ((7 * ε - w) / ε) := by
    refine barrierProfile_ge_of_one_le ?_
    rw [le_div_iff₀ hε]
    linarith
  have := barrierProfile_nonneg ((w - 1) / ε)
  rw [armPot]
  linarith

theorem mixW_nonneg (ε w : ℝ) : 0 ≤ mixW ε w := plateau_nonneg _ _ _

theorem mixW_le_one (ε w : ℝ) : mixW ε w ≤ 1 := plateau_le_one _ _ _

theorem mixW_of_le (hε : 0 < ε) {w : ℝ} (h : w ≤ 3 * ε) : mixW ε w = 0 :=
  plateau_of_le (by linarith) h

theorem mixW_of_ge (hε : 0 < ε) {w : ℝ} (h : 6 * ε ≤ w) : mixW ε w = 1 :=
  plateau_of_ge (by linarith) h

/-! ### The microscopic potential -/

/-- **The microscopic potential of the thin three-channel network at scale `ε`.** -/
noncomputable def microPot (ε : ℝ) (x : ℝ × ℝ) : ℝ :=
  (1 - mixW ε x.2) * (wellPot ε x.2 + capPot ε x.1)
    + mixW ε x.2 * (wellPot ε x.1 + armPot ε x.2)

/-- The through-channel form of the potential.  Note that it is an exact **sum** of a function of
`w` and a function of `u`: the dynamics is exactly separable there. -/
noncomputable def throughPot (ε : ℝ) (x : ℝ × ℝ) : ℝ := wellPot ε x.2 + capPot ε x.1

/-- The third-arm form of the potential, again an exact sum. -/
noncomputable def armPot2 (ε : ℝ) (x : ℝ × ℝ) : ℝ := wellPot ε x.1 + armPot ε x.2

/-- **Exact separability in the through-channel region.** -/
theorem microPot_of_through (hε : 0 < ε) {x : ℝ × ℝ} (h : x.2 ≤ 3 * ε) :
    microPot ε x = throughPot ε x := by
  rw [microPot, mixW_of_le hε h, throughPot]
  ring

/-- **Exact separability in the third-arm region.** -/
theorem microPot_of_arm (hε : 0 < ε) {x : ℝ × ℝ} (h : 6 * ε ≤ x.2) :
    microPot ε x = armPot2 ε x := by
  rw [microPot, mixW_of_ge hε h, armPot2]
  ring

/-- **The interpolation zone is inside the barrier.**  Between the two separable regions the
potential is at least `4`, which exceeds every energy in the window `K⋆ = [1/2, 2]`.  Hence no
trajectory of that energy ever enters the zone, and the two regions are dynamically
disconnected. -/
theorem microPot_ge_four_of_mid (hε : 0 < ε) {x : ℝ × ℝ} (h₁ : 3 * ε ≤ x.2)
    (h₂ : x.2 ≤ 6 * ε) : 4 ≤ microPot ε x := by
  have hthrough : 4 ≤ wellPot ε x.2 + capPot ε x.1 := by
    have hw : wellPot ε x.2 = 4 := by
      refine wellPot_of_two_le_abs hε ?_
      rw [abs_of_nonneg (by linarith)]
      linarith
    have := capPot_nonneg ε x.1
    linarith
  have harm : 4 ≤ wellPot ε x.1 + armPot ε x.2 := by
    have := armPot_ge_of_le_six hε h₂
    have := wellPot_nonneg ε x.1
    linarith
  have hm0 := mixW_nonneg ε x.2
  have hm1 := mixW_le_one ε x.2
  rw [microPot]
  nlinarith

/-- The potential is nonnegative. -/
theorem microPot_nonneg (ε : ℝ) (x : ℝ × ℝ) : 0 ≤ microPot ε x := by
  have h1 : 0 ≤ wellPot ε x.2 + capPot ε x.1 :=
    add_nonneg (wellPot_nonneg _ _) (capPot_nonneg _ _)
  have h2 : 0 ≤ wellPot ε x.1 + armPot ε x.2 :=
    add_nonneg (wellPot_nonneg _ _) (armPot_nonneg _ _)
  have hm0 := mixW_nonneg ε x.2
  have hm1 := mixW_le_one ε x.2
  rw [microPot]
  nlinarith

/-! ### Smoothness -/

theorem contDiff_wellPot (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (wellPot ε) :=
  contDiff_wellProfile.comp (contDiff_id.div_const ε)

theorem contDiff_capPot (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (capPot ε) := by
  apply ContDiff.add
  · exact contDiff_barrierProfile.comp ((contDiff_id.sub contDiff_const).div_const ε)
  · exact contDiff_barrierProfile.comp ((contDiff_id.neg.sub contDiff_const).div_const ε)

theorem contDiff_armPot (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (armPot ε) := by
  apply ContDiff.add
  · exact contDiff_barrierProfile.comp ((contDiff_const.sub contDiff_id).div_const ε)
  · exact contDiff_barrierProfile.comp ((contDiff_id.sub contDiff_const).div_const ε)

theorem contDiff_mixW (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (mixW ε) := contDiff_plateau _ _

theorem contDiff_microPot (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (microPot ε) := by
  have hs : ContDiff ℝ n (fun x : ℝ × ℝ => x.2) := contDiff_snd
  have hf : ContDiff ℝ n (fun x : ℝ × ℝ => x.1) := contDiff_fst
  apply ContDiff.add
  · exact (contDiff_const.sub ((contDiff_mixW ε).comp hs)).mul
      (((contDiff_wellPot ε).comp hs).add ((contDiff_capPot ε).comp hf))
  · exact ((contDiff_mixW ε).comp hs).mul
      (((contDiff_wellPot ε).comp hf).add ((contDiff_armPot ε).comp hs))

/-! ### The force field -/

/-- The force of the microscopic Hamiltonian, given componentwise by the two partial
derivatives.  Together with `x' = p` this is Hamilton's equations for
`H_ε(x,p) = ½|p|² + microPot ε x`. -/
noncomputable def microForce (ε : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (-deriv (fun s => microPot ε (s, x.2)) x.1, -deriv (fun s => microPot ε (x.1, s)) x.2)

/-- **The force is separable in the through-channel region.** -/
theorem microForce_of_through (hε : 0 < ε) {x : ℝ × ℝ} (h : x.2 < 3 * ε) :
    microForce ε x = (-deriv (capPot ε) x.1, -deriv (wellPot ε) x.2) := by
  have hfst : (fun s => microPot ε (s, x.2)) = fun s => wellPot ε x.2 + capPot ε s := by
    funext s
    exact microPot_of_through hε (x := (s, x.2)) h.le
  have hsnd : (fun s => microPot ε (x.1, s)) =ᶠ[nhds x.2]
      fun s => wellPot ε s + capPot ε x.1 := by
    filter_upwards [Iio_mem_nhds h] with s hs
    have := microPot_of_through hε (x := (x.1, s)) (le_of_lt hs)
    rw [this, throughPot]
  rw [microForce, hfst, hsnd.deriv_eq]
  congr 1
  · rw [deriv_const_add']
  · rw [deriv_add_const']

/-- In the tube core there is no transverse force. -/
theorem deriv_wellPot_of_abs_lt (hε : 0 < ε) {z : ℝ} (h : |z| < ε) :
    deriv (wellPot ε) z = 0 := by
  have : (wellPot ε) =ᶠ[nhds z] fun _ => (0 : ℝ) := by
    have hopen : Ioo (-ε) ε ∈ nhds z := by
      refine Ioo_mem_nhds ?_ ?_ <;> [linarith [neg_lt_of_abs_lt h]; linarith [lt_of_abs_lt h]]
    filter_upwards [hopen] with y hy
    exact wellPot_of_abs_le hε (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
  rw [this.deriv_eq, deriv_const]

/-- **Inside the tube there is no longitudinal force**: the projected motion is exactly free,
which is exactly the graph dynamics of the zero potential. -/
theorem deriv_capPot_of_abs_lt (hε : 0 < ε) {u : ℝ} (h : |u| < 1) :
    deriv (capPot ε) u = 0 := by
  have : (capPot ε) =ᶠ[nhds u] fun _ => (0 : ℝ) := by
    have hopen : Ioo (-1 : ℝ) 1 ∈ nhds u := by
      refine Ioo_mem_nhds ?_ ?_ <;> [linarith [neg_lt_of_abs_lt h]; linarith [lt_of_abs_lt h]]
    filter_upwards [hopen] with y hy
    exact capPot_of_abs_le_one hε (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
  rw [this.deriv_eq, deriv_const]

/-! ### Global bounds on the forces -/

/-- Composing a profile with a bounded derivative with an affine rescaling keeps the derivative
bounded. -/
theorem exists_bound_deriv_comp_affine {f : ℝ → ℝ} (hf : Differentiable ℝ f) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ y, |deriv f y| ≤ M) (a c : ℝ) :
    ∀ u : ℝ, |deriv (fun s => f (a * s + c)) u| ≤ M * |a| := by
  intro u
  have h1 : HasDerivAt (fun s : ℝ => a * s + c) a u := by
    simpa using ((hasDerivAt_id u).const_mul a).add_const c
  have h2 : HasDerivAt f (deriv f (a * u + c)) (a * u + c) := (hf _).hasDerivAt
  have h3 : HasDerivAt (fun s => f (a * s + c)) (deriv f (a * u + c) * a) u := h2.comp u h1
  rw [h3.deriv, abs_mul]
  exact mul_le_mul (hbound _) le_rfl (abs_nonneg a) hM

theorem wellPot_eq_affine (hε : ε ≠ 0) :
    wellPot ε = fun z => wellProfile (ε⁻¹ * z + 0) := by
  funext z
  rw [wellPot, add_zero]
  congr 1
  field_simp

theorem capPot_eq_affine (hε : ε ≠ 0) :
    capPot ε = fun u => barrierProfile (ε⁻¹ * u + -ε⁻¹) +
      barrierProfile (-ε⁻¹ * u + -ε⁻¹) := by
  funext u
  rw [capPot]
  congr 2 <;> field_simp <;> ring

/-- The transverse force is globally bounded. -/
theorem exists_bound_deriv_wellPot (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z, |deriv (wellPot ε) z| ≤ R := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_wellProfile
  refine ⟨M * |ε⁻¹|, by positivity, fun z => ?_⟩
  rw [wellPot_eq_affine (ne_of_gt hε)]
  exact exists_bound_deriv_comp_affine
    ((contDiff_wellProfile (n := 1)).differentiable (by norm_num)) hM0 hM _ _ z

/-- The longitudinal force of the through-channel is globally bounded. -/
theorem exists_bound_deriv_capPot (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ u, |deriv (capPot ε) u| ≤ R := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_barrierProfile
  refine ⟨M * |ε⁻¹| + M * |(-ε⁻¹)|, by positivity, fun u => ?_⟩
  rw [capPot_eq_affine (ne_of_gt hε)]
  have hd : Differentiable ℝ barrierProfile :=
    (contDiff_barrierProfile (n := 1)).differentiable (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => ε⁻¹ * s + -ε⁻¹) ε⁻¹ u := by
    simpa using ((hasDerivAt_id u).const_mul ε⁻¹).add_const (-ε⁻¹)
  have h2 : HasDerivAt (fun s : ℝ => -ε⁻¹ * s + -ε⁻¹) (-ε⁻¹) u := by
    simpa using ((hasDerivAt_id u).const_mul (-ε⁻¹)).add_const (-ε⁻¹)
  have g1 : HasDerivAt (fun s => barrierProfile (ε⁻¹ * s + -ε⁻¹))
      (deriv barrierProfile (ε⁻¹ * u + -ε⁻¹) * ε⁻¹) u := ((hd _).hasDerivAt).comp u h1
  have g2 : HasDerivAt (fun s => barrierProfile (-ε⁻¹ * s + -ε⁻¹))
      (deriv barrierProfile (-ε⁻¹ * u + -ε⁻¹) * -ε⁻¹) u := ((hd _).hasDerivAt).comp u h2
  have g12 : HasDerivAt (fun s => barrierProfile (ε⁻¹ * s + -ε⁻¹) +
      barrierProfile (-ε⁻¹ * s + -ε⁻¹))
      (deriv barrierProfile (ε⁻¹ * u + -ε⁻¹) * ε⁻¹ +
        deriv barrierProfile (-ε⁻¹ * u + -ε⁻¹) * -ε⁻¹) u := g1.add g2
  rw [g12.deriv]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_) <;> rw [abs_mul] <;>
    exact mul_le_mul (hM _) le_rfl (abs_nonneg _) hM0

end HamiltonianMetricGraphs
