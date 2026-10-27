/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ThinLimit
import HamiltonianMetricGraphs.Realization.MicroscopicChain
import HamiltonianMetricGraphs.Realization.StarDynamics

/-!
# The explicit three-channel thin junction as a thin Hamiltonian network

The valence-3 model of `MicroscopicPotential.lean` is here presented as a
`ThinHamiltonianNetwork` over the star `Γ⋆`: a genuine microscopic mechanical system

  `H_ε(x, p) = ½|p|² + microPot ε x`  on  `ℝ² × ℝ²`,

with three thin physical channels of width `O(ε)` — the two halves of the `u`-axis and the
positive `w`-axis — all emanating from the **single junction region** around the origin, whose
diameter is `O(ε)`.

The geometric data are the three straight tubes:

| edge | centreline | tangent | normal |
|---|---|---|---|
| `0` | `u ∈ [-1, 0]`, graph coordinate `q = -u` | `(-1, 0)` | `(0, 1)` |
| `1` | `u ∈ [0, 1]`, graph coordinate `q = u` | `(1, 0)` | `(0, 1)` |
| `2` | `w ∈ [0, 1]`, graph coordinate `q = w` | `(0, 1)` | `(1, 0)` |

All three tube mouths lie inside the disc of radius `8ε` about the origin, which is the junction
region of the branching vertex `v⋆`; the three outer vertices are at distance `1` from it.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

/-! ### The tube frames -/

/-- The unit tangent of the tube of the edge `e`, in the graph orientation. -/
noncomputable def starTang (e : starGraph.Edge) : ℝ × ℝ :=
  if e = 2 then (0, 1) else (ThroughRun.embedSign e, 0)

/-- The unit normal of the tube of the edge `e`. -/
noncomputable def starNrm (e : starGraph.Edge) : ℝ × ℝ :=
  if e = 2 then (1, 0) else (0, 1)

theorem starTang_two : starTang 2 = (0, 1) := by rw [starTang, if_pos rfl]

theorem starTang_of_ne {e : starGraph.Edge} (h : e ≠ 2) :
    starTang e = (ThroughRun.embedSign e, 0) := by rw [starTang, if_neg h]

theorem starNrm_two : starNrm 2 = (1, 0) := by rw [starNrm, if_pos rfl]

theorem starNrm_of_ne {e : starGraph.Edge} (h : e ≠ 2) : starNrm e = (0, 1) := by
  rw [starNrm, if_neg h]

theorem starTang_sq (e : starGraph.Edge) : (starTang e).1 ^ 2 + (starTang e).2 ^ 2 = 1 := by
  by_cases h : e = 2
  · rw [h, starTang_two]; norm_num
  · rw [starTang_of_ne h]
    have := embedSign_sq e
    simp only []
    nlinarith [this]

theorem starNrm_sq (e : starGraph.Edge) : (starNrm e).1 ^ 2 + (starNrm e).2 ^ 2 = 1 := by
  by_cases h : e = 2
  · rw [h, starNrm_two]; norm_num
  · rw [starNrm_of_ne h]; norm_num

theorem starTang_nrm (e : starGraph.Edge) :
    (starTang e).1 * (starNrm e).1 + (starTang e).2 * (starNrm e).2 = 0 := by
  by_cases h : e = 2
  · rw [h, starTang_two, starNrm_two]; norm_num
  · rw [starTang_of_ne h, starNrm_of_ne h]; norm_num

/-! ### The network -/

theorem tendsto_const_mul_abs (c : ℝ) : Tendsto (fun ε : ℝ => c * |ε|) (𝓝[>] 0) (𝓝 0) := by
  simpa using tendsto_abs_nhdsGT_zero.const_mul c

/-- **The explicit three-channel thin Hamiltonian network** `N⋆` of the paper, with the scales
`δ_ε = 8ε`, `θ_ε = 23ε`, `γ_ε = μ_ε = 0`, `w_ε = 2ε`, `λ_ε = ε` (extended to all real `ε` by
`ε ↦ |ε|`; the hypotheses are verified for `ε ∈ (0, 1/100)`). -/
noncomputable def starNetwork : ThinHamiltonianNetwork starGraph where
  pot := microPot
  contDiff_pot ε := contDiff_microPot ε
  pot_bddBelow ε := ⟨0, by rintro _ ⟨x, rfl⟩; exact microPot_nonneg ε x⟩
  base _ := (0, 0)
  tang := starTang
  nrm := starNrm
  tang_sq := starTang_sq
  nrm_sq := starNrm_sq
  tang_nrm := starTang_nrm
  transPot ε _ z := wellPot ε z
  continuous_transPot ε _ := (contDiff_wellPot ε (n := 0)).continuous
  offset ε := 8 * |ε|
  dwell ε := 23 * |ε|
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
  dwell_tendsto := tendsto_const_mul_abs 23
  forceErr_tendsto := tendsto_const_nhds
  momErr_tendsto := tendsto_const_nhds
  tubeWidth_tendsto := tendsto_const_mul_abs 2
  transErr_tendsto := by simpa using tendsto_abs_nhdsGT_zero

/-! ### The tube coordinates of the star network -/

@[simp] theorem starNetwork_offset (ε : ℝ) : starNetwork.offset ε = 8 * |ε| := rfl
@[simp] theorem starNetwork_dwell (ε : ℝ) : starNetwork.dwell ε = 23 * |ε| := rfl
@[simp] theorem starNetwork_forceErr (ε : ℝ) : starNetwork.forceErr ε = 0 := rfl
@[simp] theorem starNetwork_momErr (ε : ℝ) : starNetwork.momErr ε = 0 := rfl
@[simp] theorem starNetwork_tubeWidth (ε : ℝ) : starNetwork.tubeWidth ε = 2 * |ε| := rfl
@[simp] theorem starNetwork_transErr (ε : ℝ) : starNetwork.transErr ε = |ε| := rfl

theorem starNetwork_long (e : starGraph.Edge) (x : ℝ × ℝ) :
    starNetwork.long e x = longComp e x := by
  by_cases h : e = 2
  · subst h
    rw [ThinHamiltonianNetwork.long, longComp_two]
    change (x.1 - 0) * (starTang 2).1 + (x.2 - 0) * (starTang 2).2 = x.2
    rw [starTang_two]
    norm_num
  · rw [ThinHamiltonianNetwork.long, longComp_of_ne_two h]
    change (x.1 - 0) * (starTang e).1 + (x.2 - 0) * (starTang e).2 = _
    rw [starTang_of_ne h]
    ring

theorem starNetwork_trans (e : starGraph.Edge) (x : ℝ × ℝ) :
    starNetwork.trans e x = transComp e x := by
  by_cases h : e = 2
  · subst h
    rw [ThinHamiltonianNetwork.trans, transComp_two]
    change (x.1 - 0) * (starNrm 2).1 + (x.2 - 0) * (starNrm 2).2 = x.1
    rw [starNrm_two]
    norm_num
  · rw [ThinHamiltonianNetwork.trans, transComp_of_ne_two h]
    change (x.1 - 0) * (starNrm e).1 + (x.2 - 0) * (starNrm e).2 = _
    rw [starNrm_of_ne h]
    ring

theorem starNetwork_longP (e : starGraph.Edge) (p : ℝ × ℝ) :
    starNetwork.longP e p = longComp e p := by
  by_cases h : e = 2
  · subst h
    rw [ThinHamiltonianNetwork.longP, longComp_two]
    change p.1 * (starTang 2).1 + p.2 * (starTang 2).2 = p.2
    rw [starTang_two]; norm_num
  · rw [ThinHamiltonianNetwork.longP, longComp_of_ne_two h]
    change p.1 * (starTang e).1 + p.2 * (starTang e).2 = _
    rw [starTang_of_ne h]; ring

theorem starNetwork_transP (e : starGraph.Edge) (p : ℝ × ℝ) :
    starNetwork.transP e p = transComp e p := by
  by_cases h : e = 2
  · subst h
    rw [ThinHamiltonianNetwork.transP, transComp_two]
    change p.1 * (starNrm 2).1 + p.2 * (starNrm 2).2 = p.1
    rw [starNrm_two]; norm_num
  · rw [ThinHamiltonianNetwork.transP, transComp_of_ne_two h]
    change p.1 * (starNrm e).1 + p.2 * (starNrm e).2 = _
    rw [starNrm_of_ne h]; ring

theorem starNetwork_force (ε : ℝ) (x : ℝ × ℝ) : starNetwork.force ε x = microForce ε x := rfl

theorem starNetwork_hamiltonian (ε : ℝ) (x p : ℝ × ℝ) :
    starNetwork.hamiltonian ε x p = (p.1 ^ 2 + p.2 ^ 2) / 2 + microPot ε x := rfl

theorem starNetwork_transEnergy (ε : ℝ) (e : starGraph.Edge) (x p : ℝ × ℝ) :
    starNetwork.transEnergy ε e x p =
      transComp e p ^ 2 / 2 + wellPot ε (transComp e x) := by
  rw [ThinHamiltonianNetwork.transEnergy, starNetwork_transP, starNetwork_trans]
  rfl

variable {ε : ℝ}

theorem starNetwork_offset_of_pos (hε : 0 < ε) : starNetwork.offset ε = 8 * ε := by
  rw [starNetwork_offset, abs_of_pos hε]

theorem starNetwork_dwell_of_pos (hε : 0 < ε) : starNetwork.dwell ε = 23 * ε := by
  rw [starNetwork_dwell, abs_of_pos hε]

theorem starNetwork_tubeWidth_of_pos (hε : 0 < ε) : starNetwork.tubeWidth ε = 2 * ε := by
  rw [starNetwork_tubeWidth, abs_of_pos hε]

theorem starNetwork_transErr_of_pos (hε : 0 < ε) : starNetwork.transErr ε = ε := by
  rw [starNetwork_transErr, abs_of_pos hε]

theorem starGraph_length (e : starGraph.Edge) : starGraph.length e = 1 := rfl

theorem abs_embedSign (e : starGraph.Edge) : |ThroughRun.embedSign e| = 1 := by
  rw [ThroughRun.embedSign]
  split_ifs <;> norm_num

theorem abs_longComp_of_ne_two {e : starGraph.Edge} (h : e ≠ 2) (z : ℝ × ℝ) :
    |longComp e z| = |z.1| := by
  rw [longComp_of_ne_two h, abs_mul, abs_embedSign, one_mul]

/-- The value of `embedSign` is `±1`. -/
theorem embedSign_eq_or (e : starGraph.Edge) :
    ThroughRun.embedSign e = 1 ∨ ThroughRun.embedSign e = -1 := by
  rw [ThroughRun.embedSign]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The junction region of the branching vertex is a disc of radius `8ε` about the origin, and
all three tube mouths lie inside it: the three channels belong to **one** geometrically connected
microscopic junction region. -/
theorem star_mouths_in_junction {ε : ℝ} (hε : 0 < ε) (e : starGraph.Edge) :
    ∃ x : ℝ × ℝ, starNetwork.long e x = 8 * ε ∧ starNetwork.trans e x = 0 ∧
      x.1 ^ 2 + x.2 ^ 2 = (8 * ε) ^ 2 := by
  by_cases h : e = 2
  · subst h
    refine ⟨(0, 8 * ε), ?_, ?_, ?_⟩
    · rw [starNetwork_long, longComp_two]
    · rw [starNetwork_trans, transComp_two]
    · norm_num
  · refine ⟨(ThroughRun.embedSign e * (8 * ε), 0), ?_, ?_, ?_⟩
    · rw [starNetwork_long, longComp_of_ne_two h]
      change ThroughRun.embedSign e * (ThroughRun.embedSign e * (8 * ε)) = 8 * ε
      have := embedSign_sq e
      nlinarith [this]
    · rw [starNetwork_trans, transComp_of_ne_two h]
    · change (ThroughRun.embedSign e * (8 * ε)) ^ 2 + (0 : ℝ) ^ 2 = (8 * ε) ^ 2
      have := embedSign_sq e
      nlinarith [this]

/-- **The three channels are attached to one connected junction region.**  For every edge the
whole radial segment from the origin to the tube mouth of that edge lies in the disc of radius
`8ε`; the disc therefore contains the origin together with the three mouths and the segments
joining them, so it is a single connected microscopic junction region of diameter `O(ε)`.

(This is a statement about the *geometry* of the network.  Whether the particle can actually pass
from one channel to another inside that region is a dynamical question, answered by
`StarJunction.lean`: the through channels are connected to each other, while the third arm is
separated from them by the junction barrier — which is exactly `F⋆(η₃) = η₃`.) -/
theorem star_junction_segment {ε : ℝ} (hε : 0 < ε) (e : starGraph.Edge) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ x : ℝ × ℝ, starNetwork.long e x = s * (8 * ε) ∧ starNetwork.trans e x = 0 ∧
      x.1 ^ 2 + x.2 ^ 2 ≤ (8 * ε) ^ 2 := by
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  by_cases h : e = 2
  · subst h
    refine ⟨(0, s * (8 * ε)), ?_, ?_, ?_⟩
    · rw [starNetwork_long, longComp_two]
    · rw [starNetwork_trans, transComp_two]
    · have hexp : ((0 : ℝ), s * (8 * ε)).1 ^ 2 + ((0 : ℝ), s * (8 * ε)).2 ^ 2
          = s ^ 2 * (8 * ε) ^ 2 := by
        change (0 : ℝ) ^ 2 + (s * (8 * ε)) ^ 2 = _
        ring
      rw [hexp]
      nlinarith [sq_nonneg (8 * ε)]
  · have hsq := embedSign_sq e
    have hsq2 : ThroughRun.embedSign e ^ 2 = 1 := by rw [sq]; exact hsq
    refine ⟨(ThroughRun.embedSign e * (s * (8 * ε)), 0), ?_, ?_, ?_⟩
    · rw [starNetwork_long, longComp_of_ne_two h]
      change ThroughRun.embedSign e * (ThroughRun.embedSign e * (s * (8 * ε))) = s * (8 * ε)
      rw [← mul_assoc, hsq, one_mul]
    · rw [starNetwork_trans, transComp_of_ne_two h]
    · have hexp : (ThroughRun.embedSign e * (s * (8 * ε)), (0 : ℝ)).1 ^ 2
          + (ThroughRun.embedSign e * (s * (8 * ε)), (0 : ℝ)).2 ^ 2 = s ^ 2 * (8 * ε) ^ 2 := by
        change (ThroughRun.embedSign e * (s * (8 * ε))) ^ 2 + (0 : ℝ) ^ 2 = _
        rw [mul_pow, hsq2, one_mul, mul_pow]
        ring
      rw [hexp]
      nlinarith [sq_nonneg (8 * ε)]

end HamiltonianMetricGraphs
