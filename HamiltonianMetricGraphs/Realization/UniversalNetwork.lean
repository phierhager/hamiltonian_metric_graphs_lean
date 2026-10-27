/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalCorridor
import HamiltonianMetricGraphs.Realization.MicroscopicTrajectory

/-!
# The universal thin network: arbitrarily many parallel corridors

The microscopic configuration space of the universal model is the plane `ℝ²` with coordinates
`(u, w)`.  For a family of `m` corridor lengths `Λ : Fin m → ℝ` the potential is

  `netPot ε m Λ (u,w) = tubeWall ε m w + ∑ i, sel ε i w · corridorPot ε (Λ i) u`,

where corridor `i` is the horizontal strip around `w = i`:

* `tubeWall ε m w = 4 · ∏ i, coreFactor ε i w` vanishes on each core `|w - i| ≤ ε` and equals the
  confining height `4` outside all the tubes `|w - i| < 2ε`.  It is at once the **transverse
  confinement** of every tube and the **barrier separating distinct routing components**: its
  height `4` exceeds every energy of the window `K⋆ = [1/2, 2]`.
* `sel ε i w` is `1` on the whole reachable tube `|w - i| ≤ 2ε` and `0` for `|w - i| ≥ 4ε`, so on
  the reachable part of corridor `i` the potential is the **exact sum**
  `wellPot ε (w - i) + corridorPot ε (Λ i) u` (`netPot_of_corridor`).  Exact separability is what
  makes the longitudinal dynamics *exactly* the one-dimensional corridor system, hence
  `odeErr = 0`.

The number `m` of corridors and their lengths are arbitrary, so the construction accommodates an
arbitrary finite graph with an arbitrary involutive routing law: after resolving every vertex into
its `F_v`-orbits (transpositions and fixed points) the network is a disjoint family of straight
corridors, one per component, and this file is their common microscopic model.
-/

namespace HamiltonianMetricGraphs

open Set Real

variable {ε : ℝ} {m : ℕ}

/-! ### The transverse profile -/

/-- The factor of the tube wall belonging to corridor `i`: `0` on the core `|w - i| ≤ ε`, `1`
outside `|w - i| ≥ 2ε`. -/
noncomputable def coreFactor (ε : ℝ) (i : ℕ) (w : ℝ) : ℝ := wellProfile ((w - i) / ε) / 4

theorem coreFactor_nonneg (ε : ℝ) (i : ℕ) (w : ℝ) : 0 ≤ coreFactor ε i w := by
  have := wellProfile_nonneg ((w - i) / ε)
  rw [coreFactor]; linarith

theorem coreFactor_le_one (ε : ℝ) (i : ℕ) (w : ℝ) : coreFactor ε i w ≤ 1 := by
  have := wellProfile_le ((w - i) / ε)
  rw [coreFactor]; linarith

theorem coreFactor_eq_zero (hε : 0 < ε) {i : ℕ} {w : ℝ} (h : |w - i| ≤ ε) :
    coreFactor ε i w = 0 := by
  rw [coreFactor, wellProfile_of_abs_le_one
    (by rw [abs_div, abs_of_pos hε, div_le_one hε]; exact h)]
  norm_num

theorem coreFactor_eq_one (hε : 0 < ε) {i : ℕ} {w : ℝ} (h : 2 * ε ≤ |w - i|) :
    coreFactor ε i w = 1 := by
  rw [coreFactor, wellProfile_of_two_le_abs
    (by rw [abs_div, abs_of_pos hε, le_div_iff₀ hε]; linarith)]
  norm_num

/-- The tube wall of the network: it vanishes on every corridor core and equals the confining
height `4` everywhere outside the tubes. -/
noncomputable def tubeWall (ε : ℝ) (m : ℕ) (w : ℝ) : ℝ :=
  4 * ∏ i : Fin m, coreFactor ε i w

theorem tubeWall_nonneg (ε : ℝ) (m : ℕ) (w : ℝ) : 0 ≤ tubeWall ε m w := by
  refine mul_nonneg (by norm_num) (Finset.prod_nonneg fun i _ => coreFactor_nonneg ε i w)

theorem tubeWall_le_four (ε : ℝ) (m : ℕ) (w : ℝ) : tubeWall ε m w ≤ 4 := by
  have h : ∏ i : Fin m, coreFactor ε i w ≤ 1 := by
    refine Finset.prod_le_one (fun i _ => coreFactor_nonneg ε i w)
      (fun i _ => coreFactor_le_one ε i w)
  rw [tubeWall]
  linarith

/-- Distinct corridor indices are at distance at least `1`: the corridors sit at the integer
heights `w = 0, 1, …, m-1`. -/
theorem one_le_abs_index_sub {i j : Fin m} (hji : j ≠ i) :
    (1 : ℝ) ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
  have hne : (i : ℕ) ≠ (j : ℕ) := fun hc => hji (Fin.ext hc.symm)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h1 : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The triangle inequality in the form used to separate corridors. -/
theorem abs_index_sub_le (a b w : ℝ) : |a - b| ≤ |w - a| + |w - b| := by
  calc |a - b| = |(a - w) + (w - b)| := by congr 1; ring
    _ ≤ |a - w| + |w - b| := abs_add_le _ _
    _ = |w - a| + |w - b| := by rw [abs_sub_comm]

/-- **The tube wall is the transverse well of the corridor the particle is in.**  Near corridor
`i` all the other factors are `1`, so the wall reduces to the single scaled well of that tube. -/
theorem tubeWall_eq_wellPot (hε : 0 < ε) (hεs : ε ≤ 1 / 8) (i : Fin m) {w : ℝ}
    (h : |w - (i : ℕ)| ≤ 1 / 2) : tubeWall ε m w = wellPot ε (w - (i : ℕ)) := by
  have hone : ∀ j ∈ (Finset.univ : Finset (Fin m)), j ≠ i → coreFactor ε j w = 1 := by
    intro j _ hji
    refine coreFactor_eq_one hε ?_
    have hij := one_le_abs_index_sub hji
    have htri := abs_index_sub_le (((i : ℕ) : ℝ)) (((j : ℕ) : ℝ)) w
    linarith
  have hprod : ∏ j : Fin m, coreFactor ε j w = coreFactor ε i w :=
    Finset.prod_eq_single i hone (fun hi => absurd (Finset.mem_univ i) hi)
  rw [tubeWall, hprod, coreFactor, wellPot, wellProfile]
  ring

/-- Outside all the tubes the wall is at the confining height. -/
theorem tubeWall_eq_four_of_far (hε : 0 < ε) {w : ℝ}
    (h : ∀ j : Fin m, 2 * ε ≤ |w - (j : ℕ)|) : tubeWall ε m w = 4 := by
  have : ∏ j : Fin m, coreFactor ε j w = 1 :=
    Finset.prod_eq_one fun j _ => coreFactor_eq_one hε (h j)
  rw [tubeWall, this, mul_one]

/-! ### The corridor selector -/

/-- The selector of corridor `i`: `1` on the whole reachable tube `|w - i| ≤ 2ε`, `0` outside
`|w - i| ≥ 4ε`. -/
noncomputable def sel (ε : ℝ) (i : ℕ) (w : ℝ) : ℝ := 1 - wellProfile ((w - i) / (2 * ε)) / 4

theorem sel_eq_one (hε : 0 < ε) {i : ℕ} {w : ℝ} (h : |w - i| ≤ 2 * ε) : sel ε i w = 1 := by
  rw [sel, wellProfile_of_abs_le_one
    (by rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * ε), div_le_one (by linarith)]; exact h)]
  norm_num

theorem sel_eq_zero (hε : 0 < ε) {i : ℕ} {w : ℝ} (h : 4 * ε ≤ |w - i|) : sel ε i w = 0 := by
  rw [sel, wellProfile_of_two_le_abs
    (by rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * ε), le_div_iff₀ (by linarith)];
        linarith)]
  norm_num

/-! ### The network potential -/

/-- **The universal microscopic potential of a thin network with `m` parallel corridors.** -/
noncomputable def netPot (ε : ℝ) (m : ℕ) (Λ : Fin m → ℝ) (x : ℝ × ℝ) : ℝ :=
  tubeWall ε m x.2 + ∑ i : Fin m, sel ε i x.2 * corridorPot ε (Λ i) x.1

/-- **Exact separability on the reachable part of a corridor.**  This is what makes the projected
longitudinal dynamics exactly the one-dimensional corridor system. -/
theorem netPot_of_corridor (hε : 0 < ε) (hεs : ε ≤ 1 / 8) (Λ : Fin m → ℝ) (i : Fin m)
    {u w : ℝ} (h : |w - (i : ℕ)| ≤ 2 * ε) :
    netPot ε m Λ (u, w) = wellPot ε (w - (i : ℕ)) + corridorPot ε (Λ i) u := by
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin m)), j ≠ i →
      sel ε j w * corridorPot ε (Λ j) u = 0 := by
    intro j _ hji
    have hij := one_le_abs_index_sub hji
    have htri := abs_index_sub_le (((i : ℕ) : ℝ)) (((j : ℕ) : ℝ)) w
    have hfar : 4 * ε ≤ |w - ((j : ℕ) : ℝ)| := by linarith
    rw [sel_eq_zero hε hfar, zero_mul]
  have hsum : (∑ j : Fin m, sel ε j w * corridorPot ε (Λ j) u) =
      sel ε i w * corridorPot ε (Λ i) u :=
    Finset.sum_eq_single i hzero (fun hi => absurd (Finset.mem_univ i) hi)
  rw [netPot, hsum, sel_eq_one hε h, one_mul,
    tubeWall_eq_wellPot hε hεs i (by linarith [h])]

/-- **The barrier separating the corridors.**  Outside all the tubes the potential is at least the
confining height `4`, which exceeds every energy of the window `K⋆`.  A particle of the window can
therefore never leave the corridor it starts in: it cannot enter any competing routing
component. -/
theorem netPot_ge_four_of_far (hε : 0 < ε) (Λ : Fin m → ℝ) {u w : ℝ}
    (h : ∀ j : Fin m, 2 * ε ≤ |w - (j : ℕ)|) : 4 ≤ netPot ε m Λ (u, w) := by
  have hsum : 0 ≤ ∑ j : Fin m, sel ε j w * corridorPot ε (Λ j) u := by
    refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ (corridorPot_nonneg _ _ _)
    have h1 := wellProfile_le ((w - (j : ℕ)) / (2 * ε))
    rw [sel]
    linarith
  rw [netPot, tubeWall_eq_four_of_far hε h]
  linarith

end HamiltonianMetricGraphs
