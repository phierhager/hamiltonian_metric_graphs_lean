/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.GateNetwork

/-!
# Confinement and one-dimensional reduction for the gated three-channel junction

This file repeats, for the gated Hamiltonian `H_ε = ½|p|² + gatePot2 ε`, the structure theorem of
`StarConfinement.lean`.  Everything is again a consequence of conservation of the microscopic
energy alone:

* a well-prepared state of an energy window `K ⊆ [1/2, 2]` carries microscopic energy at most
  `2 + ε`, while the interpolation zone `3ε ≤ w ≤ 6ε` has potential at least `4`
  (`gatePot2_ge_four_of_mid`), so the intermediate value theorem forbids crossing it;
* on each side of that zone the potential is an **exact sum**, so the two-dimensional motion
  splits into two one-dimensional Newtonian systems.

The only difference from the ungated model is that the longitudinal system of the through channel
is now the *gated* one, `u'' = -gatePot ε '(u)`, whose analysis is `GateDynamics.lean`; the third
arm is untouched, because `gatePot2 ε = microPot ε` identically for `w ≥ 6ε`.

The statements are proved for an arbitrary energy window `K ⊆ [1/2, 2]`, so that they can be used
for both `windowLow` and `windowHigh`.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {ε S : ℝ} {K : Set ℝ}

/-! ### Unpacking a well-prepared state of the gated network -/

section Prepared

variable {η : starGraph.EdgeEnd} {x p : ℝ × ℝ}

theorem gate_prep_long (hε : 0 < ε)
    (h : gateNetwork.Prepared (zeroPotential starGraph) K ε η x p) :
    longComp η.1 x ∈ Icc (8 * ε) (1 - 8 * ε) := by
  have h1 := h.inside
  rw [gateNetwork_long, gateNetwork_offset_of_pos hε, starGraph_length] at h1
  exact h1

theorem gate_prep_trans (hε : 0 < ε)
    (h : gateNetwork.Prepared (zeroPotential starGraph) K ε η x p) :
    |transComp η.1 x| ≤ 2 * ε := by
  have h1 := h.transverse
  rw [gateNetwork_trans, gateNetwork_tubeWidth_of_pos hε] at h1
  exact h1

theorem gate_prep_transEnergy (hε : 0 < ε)
    (h : gateNetwork.Prepared (zeroPotential starGraph) K ε η x p) :
    transComp η.1 p ^ 2 / 2 + wellPot ε (transComp η.1 x) ≤ ε := by
  have h1 := h.transEnergy_le
  rw [gateNetwork_transEnergy, gateNetwork_transErr_of_pos hε] at h1
  exact h1

theorem gate_prep_towards
    (h : gateNetwork.Prepared (zeroPotential starGraph) K ε η x p) :
    0 < EdgeEnd.sign starGraph η * longComp η.1 p := by
  have h1 := h.towards
  rwa [gateNetwork_longP] at h1

theorem gate_prep_energy_mem
    (h : gateNetwork.Prepared (zeroPotential starGraph) K ε η x p) :
    longComp η.1 p ^ 2 / 2 ∈ K := by
  have h1 := h.energy_mem
  rw [gateNetwork_long, gateNetwork_longP, zeroPotential_hamiltonian] at h1
  exact h1

theorem gate_prep_energy (hKw : K ⊆ Icc (1 / 2 : ℝ) 2)
    (h : gateNetwork.Prepared (zeroPotential starGraph) K ε η x p) :
    longComp η.1 p ^ 2 / 2 ∈ Icc (1 / 2 : ℝ) 2 :=
  hKw (gate_prep_energy_mem h)

/-- The nominal speed of a well-prepared state lies in `[1, 2]`. -/
theorem gate_prep_speed (hKw : K ⊆ Icc (1 / 2 : ℝ) 2)
    (h : gateNetwork.Prepared (zeroPotential starGraph) K ε η x p) :
    |longComp η.1 p| ∈ Icc (1 : ℝ) 2 := by
  have h1 := gate_prep_energy hKw h
  have hsq : |longComp η.1 p| ^ 2 = longComp η.1 p ^ 2 := sq_abs _
  have hnn : (0 : ℝ) ≤ |longComp η.1 p| := abs_nonneg _
  exact ⟨by nlinarith [h1.1], by nlinarith [h1.2]⟩

end Prepared

/-! ### The microscopic energy of a well-prepared state -/

/-- **A well-prepared state carries microscopic energy at most `2 + ε`**, well below the barrier
height `4` of the interpolation zone.  Both cases are exact computations: in the through channel
the potential is `wellPot ε w + gatePot ε u`, and the gate vanishes at the junction boundary
`|u| = 8ε ≥ 2ε` just as the caps do; in the third arm the gated potential coincides with the
ungated one. -/
theorem gate_hamiltonian_le (hε : 0 < ε) (hKw : K ⊆ Icc (1 / 2 : ℝ) 2)
    {η : starGraph.EdgeEnd} {x p : ℝ × ℝ}
    (h : gateNetwork.Prepared (zeroPotential starGraph) K ε η x p) :
    gateNetwork.hamiltonian ε x p ≤ 2 + ε := by
  have hlong := gate_prep_long hε h
  have htr := gate_prep_trans hε h
  have hte := gate_prep_transEnergy hε h
  have hen := gate_prep_energy hKw h
  by_cases h2 : η.1 = 2
  · rw [h2] at hlong hen htr hte
    simp only [longComp_two] at hlong hen
    simp only [transComp_two] at htr hte
    have hw0 : 8 * ε ≤ x.2 := hlong.1
    have hw1 : x.2 ≤ 1 - 8 * ε := hlong.2
    have harm : gatePot2 ε x = wellPot ε x.1 + armPot ε x.2 := by
      have hx := gatePot2_of_arm hε (x := x) (by linarith)
      rw [hx, armPot2]
    have harm0 : armPot ε x.2 = 0 := by
      rw [armPot_eq_wall, wallPot_of_nonpos hε (by linarith : 7 * ε - x.2 ≤ 0),
        wallPot_of_nonpos hε (by linarith : x.2 - 1 ≤ 0), add_zero]
    rw [gateNetwork_hamiltonian, harm, harm0]
    linarith [hen.2, hte, wellPot_nonneg ε x.1]
  · rw [longComp_of_ne_two h2] at hlong hen
    simp only [transComp_of_ne_two h2] at htr hte
    have hs := embedSign_sq η.1
    have habs : |ThroughRun.embedSign η.1 * x.1| = |x.1| := by
      rw [abs_mul, abs_embedSign, one_mul]
    have hpos : 8 * ε ≤ |x.1| := by
      rw [← habs, abs_of_nonneg (by linarith [hlong.1])]
      exact hlong.1
    have hx1 : |x.1| ≤ 1 := by
      rw [← habs, abs_le]
      exact ⟨by linarith [hlong.1], by linarith [hlong.2]⟩
    have hthr : gatePot2 ε x = wellPot ε x.2 + gatePot ε x.1 :=
      gatePot2_of_through hε (x := x) (by linarith [(abs_le.mp htr).2])
    have hgate0 : gatePot ε x.1 = 0 := gatePot_of_mem hε (by linarith) hx1
    have hpsq : (ThroughRun.embedSign η.1 * p.1) ^ 2 = p.1 ^ 2 := by nlinarith [hs]
    rw [hpsq] at hen
    rw [gateNetwork_hamiltonian, hthr, hgate0]
    linarith [hen.2, hte, wellPot_nonneg ε x.2]

/-! ### The trajectory stays on the side it started on -/

variable (Θ : gateNetwork.MicroTrajectory ε S)

theorem gate_continuousOn_x : ContinuousOn Θ.x (Icc (0 : ℝ) S) :=
  fun t ht => (Θ.ode_pos t ht).continuousWithinAt

/-- **The microscopic energy bounds the potential everywhere along the trajectory.** -/
theorem gate_pot_le (hε : 0 < ε) (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {η₀ : starGraph.EdgeEnd}
    (h₀ : gateNetwork.Prepared (zeroPotential starGraph) K ε η₀ (Θ.x 0) (Θ.p 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : gatePot2 ε (Θ.x t) ≤ 2 + ε := by
  have hd : Differentiable ℝ (gateNetwork.pot ε) :=
    (contDiff_gatePot2 ε (n := 1)).differentiable (by norm_num)
  have hcons := Θ.hamiltonian_eq hd ht
  have hle := gate_hamiltonian_le hε hKw h₀
  have hk : (0 : ℝ) ≤ ((Θ.p t).1 ^ 2 + (Θ.p t).2 ^ 2) / 2 := by positivity
  rw [gateNetwork_hamiltonian, gateNetwork_hamiltonian] at hcons
  rw [gateNetwork_hamiltonian] at hle
  linarith

/-- **The interpolation zone is never entered.** -/
theorem gate_not_mid (hε : 0 < ε) (hεs : ε ≤ 1 / 100) (hKw : K ⊆ Icc (1 / 2 : ℝ) 2)
    {η₀ : starGraph.EdgeEnd}
    (h₀ : gateNetwork.Prepared (zeroPotential starGraph) K ε η₀ (Θ.x 0) (Θ.p 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : (Θ.x t).2 ∉ Icc (3 * ε) (6 * ε) := by
  intro hmem
  have h4 := gatePot2_ge_four_of_mid hε hmem.1 hmem.2
  have hle := gate_pot_le Θ hε hKw h₀ ht
  linarith

/-- **The through channel is invariant.** -/
theorem gate_through_confined (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {η₀ : starGraph.EdgeEnd} (h2 : η₀.1 ≠ 2)
    (h₀ : gateNetwork.Prepared (zeroPotential starGraph) K ε η₀ (Θ.x 0) (Θ.p 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : (Θ.x t).2 < 3 * ε := by
  have htr := gate_prep_trans hε h₀
  simp only [transComp_of_ne_two h2] at htr
  have h0 : (Θ.x 0).2 < 3 * ε := by
    have := (abs_le.mp htr).2
    linarith
  by_contra hcon
  rw [not_lt] at hcon
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) S := Icc_subset_Icc le_rfl ht.2
  have hcont : ContinuousOn (fun s => (Θ.x s).2) (Icc (0 : ℝ) t) :=
    ((gate_continuousOn_x Θ).mono hsub).snd
  obtain ⟨s, hs, hval⟩ :=
    intermediate_value_Icc ht.1 hcont (show 3 * ε ∈ Icc ((Θ.x 0).2) ((Θ.x t).2) from ⟨h0.le, hcon⟩)
  have hval' : (Θ.x s).2 = 3 * ε := hval
  exact gate_not_mid Θ hε hεs hKw h₀ (hsub hs) ⟨hval'.ge, by rw [hval']; linarith⟩

/-- **The third arm is invariant.** -/
theorem gate_arm_confined (hε : 0 < ε) (hεs : ε ≤ 1 / 100) (hKw : K ⊆ Icc (1 / 2 : ℝ) 2)
    {η₀ : starGraph.EdgeEnd} (h2 : η₀.1 = 2)
    (h₀ : gateNetwork.Prepared (zeroPotential starGraph) K ε η₀ (Θ.x 0) (Θ.p 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : 6 * ε < (Θ.x t).2 := by
  have hlong := gate_prep_long hε h₀
  rw [h2] at hlong
  simp only [longComp_two] at hlong
  have h0 : 6 * ε < (Θ.x 0).2 := by linarith [hlong.1]
  by_contra hcon
  rw [not_lt] at hcon
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) S := Icc_subset_Icc le_rfl ht.2
  have hcont : ContinuousOn (fun s => (Θ.x s).2) (Icc (0 : ℝ) t) :=
    ((gate_continuousOn_x Θ).mono hsub).snd
  obtain ⟨s, hs, hval⟩ :=
    intermediate_value_Icc' ht.1 hcont (show 6 * ε ∈ Icc ((Θ.x t).2) ((Θ.x 0).2) from ⟨hcon, h0.le⟩)
  have hval' : (Θ.x s).2 = 6 * ε := hval
  exact gate_not_mid Θ hε hεs hKw h₀ (hsub hs) ⟨by rw [hval']; linarith, hval'.le⟩

/-! ### The one-dimensional reduction -/

/-- **The through-channel reduction of a gated trajectory.**  The longitudinal pair solves the
one-dimensional *gated* system exactly. -/
structure GateThrough (ε c S : ℝ) (Θ : gateNetwork.MicroTrajectory ε S) : Prop where
  /-- the longitudinal pair is a solution of the one-dimensional gated system -/
  gate : GateSolution ε c S (fun t => (Θ.x t).1) (fun t => (Θ.p t).1)
  /-- the transverse energy is conserved and stays below `ε` -/
  trans_le : ∀ t ∈ Icc (0 : ℝ) S, (Θ.p t).2 ^ 2 / 2 + wellPot ε (Θ.x t).2 ≤ ε

/-- **The third-arm reduction of a gated trajectory** — literally the ungated one. -/
structure GateArm (ε c S : ℝ) (Θ : gateNetwork.MicroTrajectory ε S) : Prop where
  /-- the longitudinal pair is a solution of the one-dimensional arm system -/
  arm : ArmMotion ε c S (fun t => (Θ.x t).2) (fun t => (Θ.p t).2)
  /-- the transverse energy is conserved and stays below `ε` -/
  trans_le : ∀ t ∈ Icc (0 : ℝ) S, (Θ.p t).1 ^ 2 / 2 + wellPot ε (Θ.x t).1 ≤ ε

variable {Θ}

/-- **Thin-tube confinement in the through channel**: the transverse displacement is `O(ε)`. -/
theorem GateThrough.abs_trans_lt {c : ℝ} (h : GateThrough ε c S Θ) (hε : 0 < ε)
    (hεs : ε ≤ 1 / 100) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : |(Θ.x t).2| < 2 * ε := by
  have h1 := h.trans_le t ht
  have h2 : (0 : ℝ) ≤ (Θ.p t).2 ^ 2 / 2 := by positivity
  exact abs_lt_two_mul_of_wellPot_lt hε (by linarith)

/-- **Thin-tube confinement in the third arm.** -/
theorem GateArm.abs_trans_lt {c : ℝ} (h : GateArm ε c S Θ) (hε : 0 < ε)
    (hεs : ε ≤ 1 / 100) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : |(Θ.x t).1| < 2 * ε := by
  have h1 := h.trans_le t ht
  have h2 : (0 : ℝ) ≤ (Θ.p t).1 ^ 2 / 2 := by positivity
  exact abs_lt_two_mul_of_wellPot_lt hε (by linarith)

variable (Θ)

/-- **The through-channel structure theorem for the gated model.** -/
theorem gate_through (hε : 0 < ε) (hεs : ε ≤ 1 / 100) (hS : 0 ≤ S)
    (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {η₀ : starGraph.EdgeEnd} (h2 : η₀.1 ≠ 2)
    (h₀ : gateNetwork.Prepared (zeroPotential starGraph) K ε η₀ (Θ.x 0) (Θ.p 0)) :
    GateThrough ε |(Θ.p 0).1| S Θ := by
  have hconf : ∀ t ∈ Icc (0 : ℝ) S, (Θ.x t).2 < 3 * ε :=
    fun t ht => gate_through_confined Θ hε hεs hKw h2 h₀ ht
  have hu : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.x s).1) ((Θ.p t).1) (Icc (0 : ℝ) S) t :=
    fun t ht => (Θ.ode_pos t ht).fst_comp
  have hw : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.x s).2) ((Θ.p t).2) (Icc (0 : ℝ) S) t :=
    fun t ht => (Θ.ode_pos t ht).snd_comp
  have hforce : ∀ t ∈ Icc (0 : ℝ) S,
      gateNetwork.force ε (Θ.x t) =
        (-deriv (gatePot ε) (Θ.x t).1, -deriv (wellPot ε) (Θ.x t).2) := by
    intro t ht
    rw [gateNetwork_force]
    exact gateForce_of_through hε (hconf t ht)
  have hpu : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.p s).1) (-deriv (gatePot ε) ((Θ.x t).1))
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
  have hlong := gate_prep_long hε h₀
  have hsp := gate_prep_speed hKw h₀
  rw [longComp_of_ne_two h2] at hlong hsp
  have habsx : |ThroughRun.embedSign η₀.1 * (Θ.x 0).1| = |(Θ.x 0).1| := by
    rw [abs_mul, abs_embedSign, one_mul]
  have habsp : |ThroughRun.embedSign η₀.1 * (Θ.p 0).1| = |(Θ.p 0).1| := by
    rw [abs_mul, abs_embedSign, one_mul]
  rw [habsp] at hsp
  have hx0 : |(Θ.x 0).1| ≤ 1 := by
    rw [← habsx, abs_le]
    exact ⟨by linarith [hlong.1], by linarith [hlong.2]⟩
  have hx0' : 2 * ε ≤ |(Θ.x 0).1| := by
    rw [← habsx, abs_of_nonneg (by linarith [hlong.1])]
    linarith [hlong.1]
  have hgate0 : gatePot ε ((Θ.x 0).1) = 0 := gatePot_of_mem hε hx0' hx0
  refine ⟨⟨hε, hεs, hsp.1, hsp.2, hS, hu, hpu, ?_⟩, ?_⟩
  · intro t ht
    have h := energy1D_eq (contDiff_gatePot ε (n := 1)) hu hpu t ht
    simp only [energy1D] at h
    rw [h, hgate0, sq_abs]
    ring
  · intro t ht
    have h := energy1D_eq (contDiff_wellPot ε (n := 1)) hw hpw t ht
    simp only [energy1D] at h
    rw [h]
    have hte := gate_prep_transEnergy hε h₀
    simp only [transComp_of_ne_two h2] at hte
    exact hte

/-- **The third-arm structure theorem for the gated model.**  Identical to the ungated one,
because `gatePot2 ε = microPot ε` in the whole third-arm region. -/
theorem gate_arm (hε : 0 < ε) (hεs : ε ≤ 1 / 100) (hS : 0 ≤ S)
    (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {η₀ : starGraph.EdgeEnd} (h2 : η₀.1 = 2)
    (h₀ : gateNetwork.Prepared (zeroPotential starGraph) K ε η₀ (Θ.x 0) (Θ.p 0)) :
    GateArm ε |(Θ.p 0).2| S Θ := by
  have hconf : ∀ t ∈ Icc (0 : ℝ) S, 6 * ε < (Θ.x t).2 :=
    fun t ht => gate_arm_confined Θ hε hεs hKw h2 h₀ ht
  have hu : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.x s).1) ((Θ.p t).1) (Icc (0 : ℝ) S) t :=
    fun t ht => (Θ.ode_pos t ht).fst_comp
  have hw : ∀ t ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => (Θ.x s).2) ((Θ.p t).2) (Icc (0 : ℝ) S) t :=
    fun t ht => (Θ.ode_pos t ht).snd_comp
  have hforce : ∀ t ∈ Icc (0 : ℝ) S,
      gateNetwork.force ε (Θ.x t) =
        (-deriv (wellPot ε) (Θ.x t).1, -deriv (armPot ε) (Θ.x t).2) := by
    intro t ht
    rw [gateNetwork_force]
    exact gateForce_of_arm hε (hconf t ht)
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
  have hlong := gate_prep_long hε h₀
  have hsp := gate_prep_speed hKw h₀
  rw [h2] at hlong hsp
  simp only [longComp_two] at hlong hsp
  have harm0 : armPot ε ((Θ.x 0).2) = 0 := by
    rw [armPot_eq_wall, wallPot_of_nonpos hε (by linarith [hlong.1] : 7 * ε - (Θ.x 0).2 ≤ 0),
      wallPot_of_nonpos hε (by linarith [hlong.2] : (Θ.x 0).2 - 1 ≤ 0), add_zero]
  refine ⟨⟨hε, by linarith, hsp.1, hsp.2, hS, hw, hpw, ?_⟩, ?_⟩
  · intro t ht
    have h := energy1D_eq (contDiff_armPot ε (n := 1)) hw hpw t ht
    simp only [energy1D] at h
    rw [h, harm0, sq_abs]
    ring
  · intro t ht
    have h := energy1D_eq (contDiff_wellPot ε (n := 1)) hu hpu t ht
    simp only [energy1D] at h
    rw [h]
    have hte := gate_prep_transEnergy hε h₀
    rw [h2] at hte
    simp only [transComp_two] at hte
    exact hte

/-! ### The germ of a well-prepared state is determined by the channel -/

/-- In the through channel no state can be prepared towards the third germ. -/
theorem gate_through_ne_two {c : ℝ} (h : GateThrough ε c S Θ) (hε : 0 < ε)
    (hεs : ε ≤ 1 / 100) {η : starGraph.EdgeEnd} {a : ℝ} (ha : a ∈ Icc (0 : ℝ) S)
    (hp : gateNetwork.Prepared (zeroPotential starGraph) K ε η (Θ.x a) (Θ.p a)) :
    η.1 ≠ 2 := by
  intro h2
  have hlong := gate_prep_long hε hp
  rw [h2] at hlong
  simp only [longComp_two] at hlong
  have := h.abs_trans_lt hε hεs ha
  have h3 : (Θ.x a).2 ≤ |(Θ.x a).2| := le_abs_self _
  linarith [hlong.1]

/-- In the third arm every prepared state is prepared towards the third germ. -/
theorem gate_arm_eq_two {c : ℝ} (h : GateArm ε c S Θ) (hε : 0 < ε)
    {η : starGraph.EdgeEnd} {a : ℝ} (ha : a ∈ Icc (0 : ℝ) S)
    (hp : gateNetwork.Prepared (zeroPotential starGraph) K ε η (Θ.x a) (Θ.p a)) :
    η.1 = 2 := by
  by_contra h2
  have htr := gate_prep_trans hε hp
  simp only [transComp_of_ne_two h2] at htr
  have hgt := h.arm.gt_six (show a ∈ Icc (0 : ℝ) S from ha)
  have h3 : (Θ.x a).2 ≤ |(Θ.x a).2| := le_abs_self _
  linarith [(abs_le.mp htr).2]

end HamiltonianMetricGraphs
