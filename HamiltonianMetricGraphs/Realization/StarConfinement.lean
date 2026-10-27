/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.StarNetwork

/-!
# Confinement and one-dimensional reduction for the explicit three-channel junction

This file proves, **from Hamilton's equations for `H_ε = ½|p|² + microPot ε` alone**, the global
structure of every microscopic trajectory of the star network that is launched at a well-prepared
state of the window `K⋆ = [1/2, 2]`.

The single input is conservation of the microscopic energy
(`ThinHamiltonianNetwork.MicroTrajectory.hamiltonian_eq`) together with the barrier estimate
`microPot_ge_four_of_mid`: on the interpolation zone `3ε ≤ w ≤ 6ε` the potential exceeds `4`,
while a well-prepared state of `K⋆` carries energy at most `2 + ε`.  Since the excluded zone is a
*closed* band separating the through channel from the third arm, the intermediate value theorem
alone forces every trajectory to stay on the side it started on:

* `star_through_confined` — a trajectory launched in the through channel satisfies `w(t) < 3ε`
  for all times;
* `star_arm_confined` — a trajectory launched in the third arm satisfies `w(t) > 6ε` for all
  times.

On each side the potential is an **exact sum**, so the two-dimensional motion splits into two
one-dimensional Newtonian systems; the resulting data are packaged as `StarThrough` and
`StarArm`, whose longitudinal halves are the `CapMotion` and `ArmMotion` of
`StarDynamics.lean` (the systems of `CapDynamics.lean` and `ArmDynamics.lean` at every scale
`0 < ε ≤ 1/100`).  Nothing here is assumed: transverse confinement,
the separability, the exactly free longitudinal motion and the channel selection are all
consequences of the Hamiltonian flow.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {ε S : ℝ}

/-! ### Unpacking a well-prepared state of the star network -/

section Prepared

variable {η : starGraph.EdgeEnd} {x p : ℝ × ℝ}

theorem star_prep_long (hε : 0 < ε)
    (h : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η x p) :
    longComp η.1 x ∈ Icc (8 * ε) (1 - 8 * ε) := by
  have h1 := h.inside
  rw [starNetwork_long, starNetwork_offset_of_pos hε, starGraph_length] at h1
  exact h1

theorem star_prep_trans (hε : 0 < ε)
    (h : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η x p) :
    |transComp η.1 x| ≤ 2 * ε := by
  have h1 := h.transverse
  rw [starNetwork_trans, starNetwork_tubeWidth_of_pos hε] at h1
  exact h1

theorem star_prep_transEnergy (hε : 0 < ε)
    (h : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η x p) :
    transComp η.1 p ^ 2 / 2 + wellPot ε (transComp η.1 x) ≤ ε := by
  have h1 := h.transEnergy_le
  rw [starNetwork_transEnergy, starNetwork_transErr_of_pos hε] at h1
  exact h1

theorem star_prep_towards
    (h : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η x p) :
    0 < EdgeEnd.sign starGraph η * longComp η.1 p := by
  have h1 := h.towards
  rwa [starNetwork_longP] at h1

theorem star_prep_energy
    (h : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η x p) :
    longComp η.1 p ^ 2 / 2 ∈ Icc (1 / 2 : ℝ) 2 := by
  have h1 := h.energy_mem
  rw [starNetwork_long, starNetwork_longP, zeroPotential_hamiltonian] at h1
  exact h1

/-- The nominal speed of a well-prepared state lies in `[1, 2]`. -/
theorem star_prep_speed
    (h : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η x p) :
    |longComp η.1 p| ∈ Icc (1 : ℝ) 2 := by
  have h1 := star_prep_energy h
  have hsq : |longComp η.1 p| ^ 2 = longComp η.1 p ^ 2 := sq_abs _
  have hnn : (0 : ℝ) ≤ |longComp η.1 p| := abs_nonneg _
  exact ⟨by nlinarith [h1.1], by nlinarith [h1.2]⟩

end Prepared

/-! ### The microscopic energy of a well-prepared state -/

/-- **A well-prepared state of `K⋆` carries microscopic energy at most `2 + ε`**, well below the
barrier height `4` of the interpolation zone.  Both cases are exact computations: in the through
channel the potential is `wellPot ε w + capPot ε u` with `capPot ε u = 0` on the closed edge, and
in the third arm it is `wellPot ε u + armPot ε w` with `armPot ε w = 0` between the barriers. -/
theorem star_hamiltonian_le (hε : 0 < ε) {η : starGraph.EdgeEnd} {x p : ℝ × ℝ}
    (h : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η x p) :
    starNetwork.hamiltonian ε x p ≤ 2 + ε := by
  have hlong := star_prep_long hε h
  have htr := star_prep_trans hε h
  have hte := star_prep_transEnergy hε h
  have hen := star_prep_energy h
  by_cases h2 : η.1 = 2
  · rw [h2] at hlong hen htr hte
    simp only [longComp_two] at hlong hen
    simp only [transComp_two] at htr hte
    have hw0 : 8 * ε ≤ x.2 := hlong.1
    have hw1 : x.2 ≤ 1 - 8 * ε := hlong.2
    have harm : microPot ε x = wellPot ε x.1 + armPot ε x.2 := by
      have hx := microPot_of_arm hε (x := x) (by linarith)
      rw [hx, armPot2]
    have harm0 : armPot ε x.2 = 0 := by
      rw [armPot_eq_wall, wallPot_of_nonpos hε (by linarith : 7 * ε - x.2 ≤ 0),
        wallPot_of_nonpos hε (by linarith : x.2 - 1 ≤ 0), add_zero]
    rw [starNetwork_hamiltonian, harm, harm0]
    linarith [hen.2, hte, wellPot_nonneg ε x.1]
  · rw [longComp_of_ne_two h2] at hlong hen
    simp only [transComp_of_ne_two h2] at htr hte
    have hs := embedSign_sq η.1
    have habs : |ThroughRun.embedSign η.1 * x.1| = |x.1| := by
      rw [abs_mul, abs_embedSign, one_mul]
    have hx1 : |x.1| ≤ 1 := by
      rw [← habs, abs_le]
      exact ⟨by linarith [hlong.1], by linarith [hlong.2]⟩
    have hthr : microPot ε x = wellPot ε x.2 + capPot ε x.1 := by
      have hx := microPot_of_through hε (x := x) (by linarith [(abs_le.mp htr).2])
      rw [hx, throughPot]
    have hcap0 : capPot ε x.1 = 0 := capPot_of_abs_le_one hε hx1
    have hpsq : (ThroughRun.embedSign η.1 * p.1) ^ 2 = p.1 ^ 2 := by nlinarith [hs]
    rw [hpsq] at hen
    rw [starNetwork_hamiltonian, hthr, hcap0]
    linarith [hen.2, hte, wellPot_nonneg ε x.2]

/-! ### The trajectory stays on the side it started on -/

variable (Θ : starNetwork.MicroTrajectory ε S)

theorem star_continuousOn_x : ContinuousOn Θ.x (Icc (0 : ℝ) S) :=
  fun t ht => (Θ.ode_pos t ht).continuousWithinAt

/-- **The microscopic energy bounds the potential everywhere along the trajectory.** -/
theorem star_microPot_le (hε : 0 < ε) {η₀ : starGraph.EdgeEnd}
    (h₀ : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η₀ (Θ.x 0) (Θ.p 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : microPot ε (Θ.x t) ≤ 2 + ε := by
  have hd : Differentiable ℝ (starNetwork.pot ε) :=
    (contDiff_microPot ε (n := 1)).differentiable (by norm_num)
  have hcons := Θ.hamiltonian_eq hd ht
  have hle := star_hamiltonian_le hε h₀
  have hk : (0 : ℝ) ≤ ((Θ.p t).1 ^ 2 + (Θ.p t).2 ^ 2) / 2 := by positivity
  rw [starNetwork_hamiltonian, starNetwork_hamiltonian] at hcons
  rw [starNetwork_hamiltonian] at hle
  linarith

/-- **The interpolation zone is never entered.**  Its potential exceeds `4`, the energy is at
most `2 + ε < 4`. -/
theorem star_not_mid (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {η₀ : starGraph.EdgeEnd}
    (h₀ : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η₀ (Θ.x 0) (Θ.p 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : (Θ.x t).2 ∉ Icc (3 * ε) (6 * ε) := by
  intro hmem
  have h4 := microPot_ge_four_of_mid hε hmem.1 hmem.2
  have hle := star_microPot_le Θ hε h₀ ht
  linarith

/-- **The through channel is invariant.**  A trajectory launched at a well-prepared state of a
through germ satisfies `w(t) < 3ε` for all times: the closed band `[3ε, 6ε]` separates it from
the third arm and cannot be crossed. -/
theorem star_through_confined (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {η₀ : starGraph.EdgeEnd}
    (h2 : η₀.1 ≠ 2)
    (h₀ : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η₀ (Θ.x 0) (Θ.p 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : (Θ.x t).2 < 3 * ε := by
  have htr := star_prep_trans hε h₀
  simp only [transComp_of_ne_two h2] at htr
  have h0 : (Θ.x 0).2 < 3 * ε := by
    have := (abs_le.mp htr).2
    linarith
  by_contra hcon
  rw [not_lt] at hcon
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) S := Icc_subset_Icc le_rfl ht.2
  have hcont : ContinuousOn (fun s => (Θ.x s).2) (Icc (0 : ℝ) t) :=
    ((star_continuousOn_x Θ).mono hsub).snd
  obtain ⟨s, hs, hval⟩ :=
    intermediate_value_Icc ht.1 hcont (show 3 * ε ∈ Icc ((Θ.x 0).2) ((Θ.x t).2) from ⟨h0.le, hcon⟩)
  have hval' : (Θ.x s).2 = 3 * ε := hval
  exact star_not_mid Θ hε hεs h₀ (hsub hs) ⟨hval'.ge, by rw [hval']; linarith⟩

/-- **The third arm is invariant.**  A trajectory launched at a well-prepared state of the third
channel satisfies `w(t) > 6ε` for all times: this is the dynamical content of `F⋆(η₃) = η₃`. -/
theorem star_arm_confined (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {η₀ : starGraph.EdgeEnd}
    (h2 : η₀.1 = 2)
    (h₀ : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η₀ (Θ.x 0) (Θ.p 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : 6 * ε < (Θ.x t).2 := by
  have hlong := star_prep_long hε h₀
  rw [h2] at hlong
  simp only [longComp_two] at hlong
  have h0 : 6 * ε < (Θ.x 0).2 := by linarith [hlong.1]
  by_contra hcon
  rw [not_lt] at hcon
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) S := Icc_subset_Icc le_rfl ht.2
  have hcont : ContinuousOn (fun s => (Θ.x s).2) (Icc (0 : ℝ) t) :=
    ((star_continuousOn_x Θ).mono hsub).snd
  obtain ⟨s, hs, hval⟩ :=
    intermediate_value_Icc' ht.1 hcont (show 6 * ε ∈ Icc ((Θ.x t).2) ((Θ.x 0).2) from ⟨hcon, h0.le⟩)
  have hval' : (Θ.x s).2 = 6 * ε := hval
  exact star_not_mid Θ hε hεs h₀ (hsub hs) ⟨by rw [hval']; linarith, hval'.le⟩

/-! ### The one-dimensional reduction -/

/-- **The through-channel reduction of a star trajectory.**  The longitudinal pair solves the
one-dimensional cap system *exactly* (the ODE error of the model is `0`, not merely small), and
the transverse energy stays below the preparation tolerance `ε`. -/
structure StarThrough (ε c S : ℝ) (Θ : starNetwork.MicroTrajectory ε S) : Prop where
  /-- the longitudinal pair is a solution of the one-dimensional cap system -/
  cap : CapMotion ε c S (fun t => (Θ.x t).1) (fun t => (Θ.p t).1)
  /-- the transverse energy is conserved and stays below `ε` -/
  trans_le : ∀ t ∈ Icc (0 : ℝ) S, (Θ.p t).2 ^ 2 / 2 + wellPot ε (Θ.x t).2 ≤ ε

/-- **The third-arm reduction of a star trajectory.** -/
structure StarArm (ε c S : ℝ) (Θ : starNetwork.MicroTrajectory ε S) : Prop where
  /-- the longitudinal pair is a solution of the one-dimensional arm system -/
  arm : ArmMotion ε c S (fun t => (Θ.x t).2) (fun t => (Θ.p t).2)
  /-- the transverse energy is conserved and stays below `ε` -/
  trans_le : ∀ t ∈ Icc (0 : ℝ) S, (Θ.p t).1 ^ 2 / 2 + wellPot ε (Θ.x t).1 ≤ ε

variable {Θ}

/-- **Thin-tube confinement in the through channel**: the transverse displacement is `O(ε)`. -/
theorem StarThrough.abs_trans_lt {c : ℝ} (h : StarThrough ε c S Θ) (hε : 0 < ε)
    (hεs : ε ≤ 1 / 100) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : |(Θ.x t).2| < 2 * ε := by
  have h1 := h.trans_le t ht
  have h2 : (0 : ℝ) ≤ (Θ.p t).2 ^ 2 / 2 := by positivity
  exact abs_lt_two_mul_of_wellPot_lt hε (by linarith)

/-- **Thin-tube confinement in the third arm.** -/
theorem StarArm.abs_trans_lt {c : ℝ} (h : StarArm ε c S Θ) (hε : 0 < ε)
    (hεs : ε ≤ 1 / 100) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : |(Θ.x t).1| < 2 * ε := by
  have h1 := h.trans_le t ht
  have h2 : (0 : ℝ) ≤ (Θ.p t).1 ^ 2 / 2 := by positivity
  exact abs_lt_two_mul_of_wellPot_lt hε (by linarith)

variable (Θ)

/-- **The through-channel structure theorem.**  Every trajectory of `H_ε` launched at a
well-prepared state of a through germ splits exactly into a one-dimensional cap motion and a
one-dimensional transverse oscillation. -/
theorem star_through (hε : 0 < ε) (hεs : ε ≤ 1 / 100) (hS : 0 ≤ S) {η₀ : starGraph.EdgeEnd}
    (h2 : η₀.1 ≠ 2)
    (h₀ : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η₀ (Θ.x 0) (Θ.p 0)) :
    StarThrough ε |(Θ.p 0).1| S Θ := by
  have hconf : ∀ t ∈ Icc (0 : ℝ) S, (Θ.x t).2 < 3 * ε :=
    fun t ht => star_through_confined Θ hε hεs h2 h₀ ht
  have hu : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.x s).1) ((Θ.p t).1) (Icc (0 : ℝ) S) t :=
    fun t ht => (Θ.ode_pos t ht).fst_comp
  have hw : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.x s).2) ((Θ.p t).2) (Icc (0 : ℝ) S) t :=
    fun t ht => (Θ.ode_pos t ht).snd_comp
  have hforce : ∀ t ∈ Icc (0 : ℝ) S,
      starNetwork.force ε (Θ.x t) =
        (-deriv (capPot ε) (Θ.x t).1, -deriv (wellPot ε) (Θ.x t).2) := by
    intro t ht
    rw [starNetwork_force]
    exact microForce_of_through hε (hconf t ht)
  have hpu : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.p s).1) (-deriv (capPot ε) ((Θ.x t).1))
        (Icc (0 : ℝ) S) t := by
    intro t ht
    have h := (Θ.ode_mom t ht).fst_comp
    rw [hforce t ht] at h
    exact h
  have hpw : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.p s).2) (-deriv (wellPot ε) ((Θ.x t).2))
        (Icc (0 : ℝ) S) t := by
    intro t ht
    have h := (Θ.ode_mom t ht).snd_comp
    rw [hforce t ht] at h
    exact h
  -- the initial longitudinal data
  have hlong := star_prep_long hε h₀
  have hen := star_prep_energy h₀
  have hsp := star_prep_speed h₀
  rw [longComp_of_ne_two h2] at hlong hen hsp
  have hs := embedSign_sq η₀.1
  have habsx : |ThroughRun.embedSign η₀.1 * (Θ.x 0).1| = |(Θ.x 0).1| := by
    rw [abs_mul, abs_embedSign, one_mul]
  have habsp : |ThroughRun.embedSign η₀.1 * (Θ.p 0).1| = |(Θ.p 0).1| := by
    rw [abs_mul, abs_embedSign, one_mul]
  rw [habsp] at hsp
  have hx0 : |(Θ.x 0).1| ≤ 1 := by
    rw [← habsx, abs_le]
    exact ⟨by linarith [hlong.1], by linarith [hlong.2]⟩
  have hcap0 : capPot ε ((Θ.x 0).1) = 0 := capPot_of_abs_le_one hε hx0
  refine ⟨⟨hε, hεs, hsp.1, hsp.2, hS, hu, hpu, ?_⟩, ?_⟩
  · intro t ht
    have h := energy1D_eq (contDiff_capPot ε (n := 1)) hu hpu t ht
    simp only [energy1D] at h
    rw [h, hcap0, sq_abs]
    ring
  · intro t ht
    have h := energy1D_eq (contDiff_wellPot ε (n := 1)) hw hpw t ht
    simp only [energy1D] at h
    rw [h]
    have hte := star_prep_transEnergy hε h₀
    simp only [transComp_of_ne_two h2] at hte
    exact hte

/-- **The third-arm structure theorem.**  Every trajectory of `H_ε` launched at a well-prepared
state of the third channel splits exactly into a one-dimensional arm motion and a
one-dimensional transverse oscillation. -/
theorem star_arm (hε : 0 < ε) (hεs : ε ≤ 1 / 100) (hS : 0 ≤ S) {η₀ : starGraph.EdgeEnd}
    (h2 : η₀.1 = 2)
    (h₀ : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η₀ (Θ.x 0) (Θ.p 0)) :
    StarArm ε |(Θ.p 0).2| S Θ := by
  have hconf : ∀ t ∈ Icc (0 : ℝ) S, 6 * ε < (Θ.x t).2 :=
    fun t ht => star_arm_confined Θ hε hεs h2 h₀ ht
  have hu : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.x s).1) ((Θ.p t).1) (Icc (0 : ℝ) S) t :=
    fun t ht => (Θ.ode_pos t ht).fst_comp
  have hw : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.x s).2) ((Θ.p t).2) (Icc (0 : ℝ) S) t :=
    fun t ht => (Θ.ode_pos t ht).snd_comp
  have hforce : ∀ t ∈ Icc (0 : ℝ) S,
      starNetwork.force ε (Θ.x t) =
        (-deriv (wellPot ε) (Θ.x t).1, -deriv (armPot ε) (Θ.x t).2) := by
    intro t ht
    rw [starNetwork_force]
    exact microForce_of_arm hε (hconf t ht)
  have hpu : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.p s).1) (-deriv (wellPot ε) ((Θ.x t).1))
        (Icc (0 : ℝ) S) t := by
    intro t ht
    have h := (Θ.ode_mom t ht).fst_comp
    rw [hforce t ht] at h
    exact h
  have hpw : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.p s).2) (-deriv (armPot ε) ((Θ.x t).2))
        (Icc (0 : ℝ) S) t := by
    intro t ht
    have h := (Θ.ode_mom t ht).snd_comp
    rw [hforce t ht] at h
    exact h
  have hlong := star_prep_long hε h₀
  have hsp := star_prep_speed h₀
  rw [h2] at hlong hsp
  simp only [longComp_two] at hlong hsp
  have harm0 : armPot ε ((Θ.x 0).2) = 0 := by
    rw [armPot_eq_wall, wallPot_of_nonpos hε (by linarith [hlong.1] : 7 * ε - (Θ.x 0).2 ≤ 0),
      wallPot_of_nonpos hε (by linarith [hlong.2] : (Θ.x 0).2 - 1 ≤ 0), add_zero]
  refine ⟨⟨hε, hεs, hsp.1, hsp.2, hS, hw, hpw, ?_⟩, ?_⟩
  · intro t ht
    have h := energy1D_eq (contDiff_armPot ε (n := 1)) hw hpw t ht
    simp only [energy1D] at h
    rw [h, harm0, sq_abs]
    ring
  · intro t ht
    have h := energy1D_eq (contDiff_wellPot ε (n := 1)) hu hpu t ht
    simp only [energy1D] at h
    rw [h]
    have hte := star_prep_transEnergy hε h₀
    rw [h2] at hte
    simp only [transComp_two] at hte
    exact hte

/-! ### The germ of a well-prepared state is determined by the channel -/

/-- In the through channel no state can be prepared towards the third germ: the third channel
starts at `w = 8ε`, while the through tube has width `2ε`. -/
theorem star_through_ne_two {c : ℝ} (h : StarThrough ε c S Θ) (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    {η : starGraph.EdgeEnd} {a : ℝ} (ha : a ∈ Icc (0 : ℝ) S)
    (hp : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η (Θ.x a) (Θ.p a)) :
    η.1 ≠ 2 := by
  intro h2
  have hlong := star_prep_long hε hp
  rw [h2] at hlong
  simp only [longComp_two] at hlong
  have := h.abs_trans_lt hε hεs ha
  have h3 : (Θ.x a).2 ≤ |(Θ.x a).2| := le_abs_self _
  linarith [hlong.1]

/-- In the third arm every prepared state is prepared towards the third germ. -/
theorem star_arm_eq_two {c : ℝ} (h : StarArm ε c S Θ) (hε : 0 < ε)
    {η : starGraph.EdgeEnd} {a : ℝ} (ha : a ∈ Icc (0 : ℝ) S)
    (hp : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η (Θ.x a) (Θ.p a)) :
    η.1 = 2 := by
  by_contra h2
  have htr := star_prep_trans hε hp
  simp only [transComp_of_ne_two h2] at htr
  have hgt := h.arm.gt_six (show a ∈ Icc (0 : ℝ) S from ha)
  have h3 : (Θ.x a).2 ≤ |(Θ.x a).2| := le_abs_self _
  linarith [(abs_le.mp htr).2]

end HamiltonianMetricGraphs
