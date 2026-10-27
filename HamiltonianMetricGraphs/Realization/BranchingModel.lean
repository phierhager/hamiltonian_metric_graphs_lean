/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.MicroscopicTrajectory
import HamiltonianMetricGraphs.Realization.BranchingGraph
import HamiltonianMetricGraphs.Realization.Reflection

/-!
# The explicit branching microscopic model

This file assembles the microscopic side of the realization into model-level statements: the
Hamiltonian itself, what "well prepared" means, conservation of the microscopic energy,
deterministic channel selection, and the chain parameters of the thin network with their
vanishing as `ε → 0⁺`.

The Hamiltonian is

  `microHamiltonian ε (x, p) = ½(p₁² + p₂²) + microPot ε x`

on `ℝ² × ℝ²`, with `microPot ε` the explicit three-channel potential of
`MicroscopicPotential.lean`.  It is smooth for every `ε > 0`, and the junction it defines has
diameter `O(ε)` while the tubes have width `O(ε)`.

What is proved here, from the Hamiltonian and not by assumption:

* `microHamiltonian_conserved` — the microscopic energy is exactly conserved along the
  trajectories built in `MicroscopicTrajectory.lean`;
* `stays_in_through_channel` — a well-prepared trajectory of the through channel never enters
  the third arm: the interpolation zone is inside a barrier of height `4`, above the whole energy
  window `K⋆ = [1/2, 2]`.  This is the `1 ↔ 2` half of the channel selection;
* `arm_barrier_margin` — the third arm is separated from the junction by a barrier of height `4`,
  with the uniform positive margin `4 - E ≥ 2` on the window.  This is the `3 ↦ 3` half;
* `starParams` and the four limits `offset_tendsto`, `dwell_tendsto`, `odeErr_tendsto`,
  `momErr_tendsto` — the chain parameters of the model vanish as `ε → 0⁺`.  Note that the ODE
  error and the momentum error are not merely small but **exactly zero**: the longitudinal motion
  in the tube is exactly free, and the reflection at a barrier reverses the momentum exactly.
-/

namespace HamiltonianMetricGraphs

open Set Filter
open scoped Topology

/-! ### The Hamiltonian -/

/-- **The microscopic Hamiltonian of the thin three-channel network at scale `ε`.** -/
noncomputable def microHamiltonian (ε : ℝ) (x p : ℝ × ℝ) : ℝ :=
  (p.1 ^ 2 + p.2 ^ 2) / 2 + microPot ε x

/-- The Hamiltonian is smooth in the configuration variable for every scale. -/
theorem contDiff_microHamiltonian (ε : ℝ) (p : ℝ × ℝ) {n : ℕ∞} :
    ContDiff ℝ n (fun x => microHamiltonian ε x p) :=
  contDiff_const.add (contDiff_microPot ε)

variable {ε : ℝ}

/-- The transverse energy of the through channel, which is separately conserved. -/
noncomputable def transverseEnergy (ε w pw : ℝ) : ℝ := pw ^ 2 / 2 + wellPot ε w

/-- The longitudinal energy of the through channel, which is separately conserved. -/
noncomputable def longitudinalEnergy (ε u pu : ℝ) : ℝ := pu ^ 2 / 2 + capPot ε u

/-- In the through channel the microscopic energy is the sum of the longitudinal and the
transverse energy — this is the exact separability of the model. -/
theorem microHamiltonian_split (hε : 0 < ε) {u w pu pw : ℝ} (hw : w ≤ 3 * ε) :
    microHamiltonian ε (u, w) (pu, pw) =
      longitudinalEnergy ε u pu + transverseEnergy ε w pw := by
  rw [microHamiltonian, microPot_of_through hε (x := (u, w)) hw, throughPot,
    longitudinalEnergy, transverseEnergy]
  ring

/-! ### Well-prepared states -/

/-- **A well-prepared microscopic state** of the through channel at scale `ε`: the particle sits
in the tube core, strictly inside the closed edge, with transverse energy below the wall height
and longitudinal energy in the window `K⋆`. -/
structure WellPrepared (ε : ℝ) (u pu w pw : ℝ) : Prop where
  eps_pos : 0 < ε
  core : |w| ≤ ε
  inside : |u| < 1
  transverse : pw ^ 2 / 2 < 4
  energy : longitudinalEnergy ε u pu ∈ windowStar

theorem WellPrepared.transverse_energy_lt {u pu w pw : ℝ} (h : WellPrepared ε u pu w pw) :
    transverseEnergy ε w pw < 4 := by
  rw [transverseEnergy, wellPot_of_abs_le h.eps_pos h.core, add_zero]
  exact h.transverse

/-- A well-prepared longitudinal state has energy at most `2`, comfortably below the barrier
height `4`: this is the uniform exit-basin margin of the model. -/
theorem WellPrepared.energy_le_two {u pu w pw : ℝ} (h : WellPrepared ε u pu w pw) :
    longitudinalEnergy ε u pu ≤ 2 := h.energy.2

theorem WellPrepared.half_le_energy {u pu w pw : ℝ} (h : WellPrepared ε u pu w pw) :
    1 / 2 ≤ longitudinalEnergy ε u pu := h.energy.1

/-! ### Conservation and channel selection -/

/-- **Conservation of the microscopic energy** along a trajectory of the model, in the through
channel.  It follows from the two separate one-dimensional conservation laws, which hold because
the potential is an exact sum there. -/
theorem microHamiltonian_conserved (hε : 0 < ε) {T : ℝ} {u pu w pw : ℝ → ℝ}
    (hu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (pu t) (Icc (0 : ℝ) T) t)
    (hpu : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt pu (-deriv (capPot ε) (u t)) (Icc (0 : ℝ) T) t)
    (hw : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt w (pw t) (Icc (0 : ℝ) T) t)
    (hpw : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt pw (-deriv (wellPot ε) (w t)) (Icc (0 : ℝ) T) t)
    (hconf : ∀ t ∈ Icc (0 : ℝ) T, w t ≤ 3 * ε) :
    ∀ t ∈ Icc (0 : ℝ) T,
      microHamiltonian ε (u t, w t) (pu t, pw t) =
        microHamiltonian ε (u 0, w 0) (pu 0, pw 0) := by
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := left_mem_Icc.mpr (by linarith [ht.1, ht.2])
  have hlong := energy1D_eq (contDiff_capPot ε (n := 1)) hu hpu t ht
  have htrans := energy1D_eq (contDiff_wellPot ε (n := 1)) hw hpw t ht
  rw [microHamiltonian_split hε (hconf t ht), microHamiltonian_split hε (hconf 0 h0)]
  simp only [energy1D] at hlong htrans
  rw [longitudinalEnergy, transverseEnergy, longitudinalEnergy, transverseEnergy]
  linarith

/-- **Deterministic channel selection, the `1 ↔ 2` half.**  A trajectory whose transverse energy
is below the wall height stays in the tube of the through channel, hence never enters the
interpolation zone `3ε ≤ w ≤ 6ε` and a fortiori never enters the third arm.  The particle
entering along channel `1` therefore leaves along channel `2` and cannot leave along channel
`3`. -/
theorem stays_in_through_channel (hε : 0 < ε) {T : ℝ} {w pw : ℝ → ℝ}
    (hw : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt w (pw t) (Icc (0 : ℝ) T) t)
    (hpw : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt pw (-deriv (wellPot ε) (w t)) (Icc (0 : ℝ) T) t)
    (hE : transverseEnergy ε (w 0) (pw 0) < 4) :
    ∀ t ∈ Icc (0 : ℝ) T, |w t| < 2 * ε := by
  intro t ht
  have hS : ∀ z ∈ {z : ℝ | 2 * ε ≤ |z|}, (4 : ℝ) ≤ wellPot ε z := fun z hz =>
    (wellPot_of_two_le_abs hε hz).ge
  have hE' : energy1D (wellPot ε) (w 0) (pw 0) < 4 := hE
  have := not_mem_of_energy_lt (contDiff_wellPot ε (n := 1)) hS hw hpw hE' t ht
  by_contra hcon
  rw [not_lt] at hcon
  exact this hcon

/-- **Deterministic channel selection, the `3 ↦ 3` half.**  The third arm is separated from the
junction by a barrier of height `4`.  Every energy in `K⋆ = [1/2, 2]` is below it with the
uniform margin `4 - E ≥ 2 > 0`, so a particle of the window that is in the third arm can never
reach the junction: it is reflected back into the third arm. -/
theorem arm_barrier_margin (hε : 0 < ε) {E : ℝ} (hE : E ∈ windowStar) :
    ∀ w ≤ 6 * ε, E + 2 ≤ armPot ε w := by
  intro w hw
  have h1 := armPot_ge_of_le_six hε hw
  have h2 : E ≤ 2 := hE.2
  linarith

/-- The exit basins of the three channels are separated by the barrier: a particle of the window
in the third arm stays at `w > 6ε`, while a particle of the through channel stays at
`|w| < 2ε`.  The gap `2ε ≤ w ≤ 6ε` is crossed by neither. -/
theorem channels_disjoint (hε : 0 < ε) {w₁ w₂ : ℝ} (h₁ : |w₁| < 2 * ε) (h₂ : 6 * ε < w₂) :
    w₁ < w₂ := by
  have : w₁ ≤ |w₁| := le_abs_self _
  linarith

/-! ### The chain parameters of the model -/

/-- **The chain parameters of the thin network at scale `ε`.**

* `offset = 8ε` — the routers occupy the longitudinal segment of length `8ε` next to each vertex;
  in particular the junction barrier of the third arm, which sits at `w ≈ 7ε`, is inside it.
* `dwell = 100ε` — an upper bound for the reflection time
  `reflectionTime δ k E d` of the model's barrier, which is `O(ε)` because `d` and `δ` are `O(ε)`
  while the slope `k` is of order `1/ε` (`deriv_barrierProfile_ge`); it also bounds the time
  `2·offset/c` a particle needs to cross a junction.
* `odeErr = 0` — the longitudinal motion inside the tube is **exactly** free, since `capPot`
  vanishes identically on the closed edge (`capPot_of_abs_le_one`).
* `momErr = 0` — the reflection reverses the momentum **exactly**, by conservation of energy
  (`reflect_of_barrier`). -/
noncomputable def starParams (ε : ℝ) : ChainParams where
  offset := 8 * |ε|
  dwell := 100 * |ε|
  odeErr := 0
  momErr := 0
  offset_nonneg := by positivity
  dwell_nonneg := by positivity
  odeErr_nonneg := le_rfl
  momErr_nonneg := le_rfl

@[simp] theorem starParams_offset (ε : ℝ) : (starParams ε).offset = 8 * |ε| := rfl
@[simp] theorem starParams_dwell (ε : ℝ) : (starParams ε).dwell = 100 * |ε| := rfl
@[simp] theorem starParams_odeErr (ε : ℝ) : (starParams ε).odeErr = 0 := rfl
@[simp] theorem starParams_momErr (ε : ℝ) : (starParams ε).momErr = 0 := rfl

theorem starParams_offset_of_pos (hε : 0 < ε) : (starParams ε).offset = 8 * ε := by
  rw [starParams_offset, abs_of_pos hε]

theorem starParams_dwell_of_pos (hε : 0 < ε) : (starParams ε).dwell = 100 * ε := by
  rw [starParams_dwell, abs_of_pos hε]

theorem tendsto_abs_nhdsGT_zero : Tendsto (fun ε : ℝ => |ε|) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun ε : ℝ => |ε|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs (G := ℝ)).tendsto 0
  exact h.mono_left nhdsWithin_le_nhds

/-- The router offset vanishes: the junctions have diameter `O(ε)`. -/
theorem starParams_offset_tendsto :
    Tendsto (fun ε => (starParams ε).offset) (𝓝[>] 0) (𝓝 0) := by
  simpa using tendsto_abs_nhdsGT_zero.const_mul (8 : ℝ)

/-- The junction residence time vanishes: `t_out^ε - t_in^ε = O(ε)`. -/
theorem starParams_dwell_tendsto :
    Tendsto (fun ε => (starParams ε).dwell) (𝓝[>] 0) (𝓝 0) := by
  simpa using tendsto_abs_nhdsGT_zero.const_mul (100 : ℝ)

/-- The error in the graph Hamilton equations vanishes — indeed it is exactly zero, because the
longitudinal motion inside a tube is exactly free. -/
theorem starParams_odeErr_tendsto :
    Tendsto (fun ε => (starParams ε).odeErr) (𝓝[>] 0) (𝓝 0) := by
  simp only [starParams_odeErr]
  exact tendsto_const_nhds

/-- The error in the outgoing longitudinal momentum vanishes — indeed it is exactly zero, because
the reflection reverses the momentum exactly. -/
theorem starParams_momErr_tendsto :
    Tendsto (fun ε => (starParams ε).momErr) (𝓝[>] 0) (𝓝 0) := by
  simp only [starParams_momErr]
  exact tendsto_const_nhds

end HamiltonianMetricGraphs
