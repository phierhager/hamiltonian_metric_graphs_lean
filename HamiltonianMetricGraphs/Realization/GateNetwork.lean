/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.GateDynamics
import HamiltonianMetricGraphs.Realization.StarJunction

/-!
# The energy-gated three-channel network

The gated potential `gatePot2` of `GatePotential.lean` is here presented as a
`ThinHamiltonianNetwork` over the same star `Γ⋆` as `starNetwork`, with the same tube geometry:

  `H_ε(x, p) = ½|p|² + gatePot2 ε x`  on  `ℝ² × ℝ²`.

This is the paper's network `N^g`.  Only two of the network data of `N⋆` change: the potential
(the gate `G_ε` is inserted across the through channel at the branching vertex) and the residence
time, `θ_ε = 32ε` instead of `23ε`, which accommodates the gate reflection (`< 26ε`) and the gate
crossing (`≤ 32ε`).

## The two energy windows

The gate is *energetically selective*: it is at least `g₀ = gateHeight = 7/10` on its core
`[-ε, ε]`, which a longitudinal energy below `g₀` cannot reach, and at most its height
`E_c = max G_ε = gateCritical < 1.365`, which every longitudinal energy above `3/2` passes.  The
two disjoint compact windows

  `K₋ = [1/2, 3/5]`,   `K₊ = [3/2, 2]`,   `max K₋ < g₀ < 1.15 < E_c < 1.365 < min K₊`,

lie on either side of the gate and are both contained in `[1/2, 2]`, so the associated speeds
`c = √(2E)` lie in `[1, 2]` and the one-dimensional machinery of `StarDynamics.lean` and
`GateDynamics.lean` applies on both.  Energies between the windows, where the junction passes
from reflection to transmission, are deliberately **excluded**: no deterministic routing is
claimed there.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

/-! ### The two energy windows -/

/-- The **low** energy window `K₋ = [1/2, 3/5]`, strictly below `g₀ = 7/10`. -/
def windowLow : Set ℝ := Icc (1 / 2 : ℝ) (3 / 5)

/-- The **high** energy window `K₊ = [3/2, 2]`, strictly above the gate height
`E_c = gateCritical < 1.365`. -/
def windowHigh : Set ℝ := Icc (3 / 2 : ℝ) 2

theorem isCompact_windowLow : IsCompact windowLow := isCompact_Icc
theorem isCompact_windowHigh : IsCompact windowHigh := isCompact_Icc

theorem windowLow_subset : windowLow ⊆ Icc (1 / 2 : ℝ) 2 :=
  Icc_subset_Icc le_rfl (by norm_num)

theorem windowHigh_subset : windowHigh ⊆ Icc (1 / 2 : ℝ) 2 :=
  Icc_subset_Icc (by norm_num) le_rfl

/-- Every energy of `K₋` is strictly below `g₀`: such a particle is reflected. -/
theorem windowLow_lt_gateHeight {E : ℝ} (hE : E ∈ windowLow) : E < gateHeight := by
  have h : E ≤ 3 / 5 := hE.2
  rw [gateHeight]; linarith

/-- Every energy of `K₊` is at least `3/2`, hence above the gate height `E_c < 1.365`: such a
particle crosses. -/
theorem windowHigh_ge {E : ℝ} (hE : E ∈ windowHigh) : 3 / 2 ≤ E := hE.1

/-- **The two windows are disjoint**, and separated by the gate: `max K₋ < g₀ < E_c < min K₊`. -/
theorem windowLow_disjoint_windowHigh : Disjoint windowLow windowHigh := by
  rw [Set.disjoint_left]
  intro E hlow hhigh
  have h1 : E ≤ 3 / 5 := hlow.2
  have h2 : 3 / 2 ≤ E := hhigh.1
  linarith

theorem windowLow_regular : ∀ E ∈ windowLow, E ∉ (zeroPotential starGraph).exceptionalEnergies := by
  intro E hE
  refine zeroPotential_not_mem_exceptionalEnergies ?_
  have : (1 / 2 : ℝ) ≤ E := hE.1
  linarith

theorem windowHigh_regular :
    ∀ E ∈ windowHigh, E ∉ (zeroPotential starGraph).exceptionalEnergies := by
  intro E hE
  refine zeroPotential_not_mem_exceptionalEnergies ?_
  have : (3 / 2 : ℝ) ≤ E := hE.1
  linarith

/-! ### The windows lie above the potential -/

/-- **`K₋ = [1/2, 3/5]` lies above the (zero) potential**: the window condition of
Theorem IX.6. -/
theorem windowLow_isWindowAbove : (zeroPotential starGraph).IsWindowAbove windowLow :=
  zeroPotential_isWindowAbove fun E hE => by have : (1 / 2 : ℝ) ≤ E := hE.1; linarith

/-- **`K₊ = [3/2, 2]` lies above the (zero) potential.** -/
theorem windowHigh_isWindowAbove : (zeroPotential starGraph).IsWindowAbove windowHigh :=
  zeroPotential_isWindowAbove fun E hE => by have : (3 / 2 : ℝ) ≤ E := hE.1; linarith

/-! ### The network -/

/-- **The energy-gated three-channel thin Hamiltonian network.**  Same three tubes, same tube
frames, same transverse confinement as `starNetwork`; the potential carries the junction gate and
the residence time is `θ_ε = 32ε` (extended as `32|ε|` to all real `ε`). -/
noncomputable def gateNetwork : ThinHamiltonianNetwork starGraph where
  pot := gatePot2
  contDiff_pot ε := contDiff_gatePot2 ε
  pot_bddBelow ε := ⟨0, by rintro _ ⟨x, rfl⟩; exact gatePot2_nonneg ε x⟩
  base _ := (0, 0)
  tang := starTang
  nrm := starNrm
  tang_sq := starTang_sq
  nrm_sq := starNrm_sq
  tang_nrm := starTang_nrm
  transPot ε _ z := wellPot ε z
  continuous_transPot ε _ := (contDiff_wellPot ε (n := 0)).continuous
  offset ε := 8 * |ε|
  dwell ε := 32 * |ε|
  forceErr _ := 0
  momErr _ := 0
  tubeWidth ε := 2 * |ε|
  transErr ε := |ε|
  offset_nonneg ε := by positivity
  dwell_nonneg ε := by positivity
  forceErr_nonneg _ := le_rfl
  momErr_nonneg _ := le_rfl
  tubeWidth_nonneg ε := by positivity
  transErr_nonneg ε := by positivity
  offset_tendsto := tendsto_const_mul_abs 8
  dwell_tendsto := tendsto_const_mul_abs 32
  forceErr_tendsto := tendsto_const_nhds
  momErr_tendsto := tendsto_const_nhds
  tubeWidth_tendsto := tendsto_const_mul_abs 2
  transErr_tendsto := by simpa using tendsto_abs_nhdsGT_zero

/-! ### The tube coordinates of the gated network

They are literally those of `starNetwork` — the two networks share the tube frames. -/

@[simp] theorem gateNetwork_offset (ε : ℝ) : gateNetwork.offset ε = 8 * |ε| := rfl
@[simp] theorem gateNetwork_dwell (ε : ℝ) : gateNetwork.dwell ε = 32 * |ε| := rfl
@[simp] theorem gateNetwork_forceErr (ε : ℝ) : gateNetwork.forceErr ε = 0 := rfl
@[simp] theorem gateNetwork_momErr (ε : ℝ) : gateNetwork.momErr ε = 0 := rfl
@[simp] theorem gateNetwork_tubeWidth (ε : ℝ) : gateNetwork.tubeWidth ε = 2 * |ε| := rfl
@[simp] theorem gateNetwork_transErr (ε : ℝ) : gateNetwork.transErr ε = |ε| := rfl

theorem gateNetwork_long (e : starGraph.Edge) (x : ℝ × ℝ) :
    gateNetwork.long e x = longComp e x := starNetwork_long e x

theorem gateNetwork_trans (e : starGraph.Edge) (x : ℝ × ℝ) :
    gateNetwork.trans e x = transComp e x := starNetwork_trans e x

theorem gateNetwork_longP (e : starGraph.Edge) (p : ℝ × ℝ) :
    gateNetwork.longP e p = longComp e p := starNetwork_longP e p

theorem gateNetwork_transP (e : starGraph.Edge) (p : ℝ × ℝ) :
    gateNetwork.transP e p = transComp e p := starNetwork_transP e p

theorem gateNetwork_force (ε : ℝ) (x : ℝ × ℝ) : gateNetwork.force ε x = gateForce ε x := rfl

theorem gateNetwork_hamiltonian (ε : ℝ) (x p : ℝ × ℝ) :
    gateNetwork.hamiltonian ε x p = (p.1 ^ 2 + p.2 ^ 2) / 2 + gatePot2 ε x := rfl

theorem gateNetwork_transEnergy (ε : ℝ) (e : starGraph.Edge) (x p : ℝ × ℝ) :
    gateNetwork.transEnergy ε e x p =
      transComp e p ^ 2 / 2 + wellPot ε (transComp e x) := by
  rw [ThinHamiltonianNetwork.transEnergy, gateNetwork_transP, gateNetwork_trans]
  rfl

variable {ε : ℝ}

theorem gateNetwork_offset_of_pos (hε : 0 < ε) : gateNetwork.offset ε = 8 * ε := by
  rw [gateNetwork_offset, abs_of_pos hε]

theorem gateNetwork_dwell_of_pos (hε : 0 < ε) : gateNetwork.dwell ε = 32 * ε := by
  rw [gateNetwork_dwell, abs_of_pos hε]

theorem gateNetwork_tubeWidth_of_pos (hε : 0 < ε) : gateNetwork.tubeWidth ε = 2 * ε := by
  rw [gateNetwork_tubeWidth, abs_of_pos hε]

theorem gateNetwork_transErr_of_pos (hε : 0 < ε) : gateNetwork.transErr ε = ε := by
  rw [gateNetwork_transErr, abs_of_pos hε]

/-- The junction boundary reached by a gated flight is the same as for `starNetwork`: the two
networks have the same junction radius `8ε`. -/
theorem gateNetwork_toGo (hε : 0 < ε) (η : starGraph.EdgeEnd) (q : ℝ) :
    gateNetwork.toGo ε η q = |starTarget ε η - q| := by
  rw [ThinHamiltonianNetwork.toGo, gateNetwork_offset_of_pos hε, starTarget]

end HamiltonianMetricGraphs
