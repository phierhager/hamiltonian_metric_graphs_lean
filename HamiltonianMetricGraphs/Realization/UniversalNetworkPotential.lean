/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalRealization

/-!
# The uniform universal network of `(Γ, F)`

This file defines **one** smooth potential `uniPot F ε` on `ℝ²` for a finite metric graph `Γ`
with a routing law `F`.  It depends only on `(Γ, F)` and the scale `ε`.  It does not depend on an
initial state or a time horizon.

The resolved space `R(Γ, F)` is laid out as a family of disjoint straight corridors, one for
every edge-end germ `ζ`, on the horizontal line `w = uniRow ζ ∈ {0, 1, …, m - 1}`.  The corridor
of `ζ` carries the routing component of `ζ`, unrolled forward from `ζ`:

* if the component contains an `F`-fixed germ (a **fold**), it is an interval of `R(Γ, F)`.  The
  corridor is the interval between the two fold positions, closed by two reflecting caps at the
  fixed ends of `F` (`corridorPot`);
* if it contains no fold, it is a circle of `R(Γ, F)`.  The corridor is then its **universal
  cover**: an infinite straight corridor with *no* longitudinal potential at all, in which the graph
  motion lifts to free motion along the corridor.  Nothing has to be closed beyond a horizon.

The potential is

  `uniPot F ε (u, w) = tubeWall ε m w + ∑ k, sel ε k w · longPot F ε (ζ_k) u`,

the transverse wall of height `4` around every corridor core plus, on the tube of each corridor,
its longitudinal potential (`famPot`).  On the reachable tube `|w - uniRow ζ| ≤ 2ε` it is the exact
sum `wellPot ε (w - uniRow ζ) + longPot F ε ζ u` (`uniPot_of_tube`).

The file also fixes the **projection data**, chosen once: the chart `uniChart F ζ j` identifies the
cell of flight `j` in the corridor of `ζ` with the edge of that flight.  It depends only on
`(Γ, F, ζ, j)`.

## Main declarations

* `famPot`, `famPot_of_corridor`, `famPot_ge_four_of_far`, `contDiff_famPot`: corridors with an
  arbitrary family of longitudinal potentials;
* `corridorLow`, `corridorLen`, `longPot`: the fixed layout of the corridor of a germ;
* `uniPot`, `contDiff_uniPot`, `uniPot_of_tube`: the uniform network potential;
* `gradForce`, `IsHamiltonianTrajectory`: Hamilton's equations for `½|p|² + W`;
* `chartAt`, `uniChart`: the fixed projection to the graph.
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph

variable {Γ : FiniteMetricGraph} {ε : ℝ} {m : ℕ}

/-! ### Corridors with an arbitrary family of longitudinal potentials -/

/-- **The potential of `m` parallel corridors with longitudinal potentials `P k`.**  Corridor `k`
is the strip around the line `w = k`; the transverse wall `tubeWall` confines the particle to the
tubes and separates them. -/
noncomputable def famPot (ε : ℝ) (m : ℕ) (P : Fin m → ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  tubeWall ε m x.2 + ∑ i : Fin m, sel ε i x.2 * P i x.1

/-- **Exact separability on the reachable part of a corridor.** -/
theorem famPot_of_corridor (hε : 0 < ε) (hεs : ε ≤ 1 / 8) (P : Fin m → ℝ → ℝ) (i : Fin m)
    {u w : ℝ} (h : |w - (i : ℕ)| ≤ 2 * ε) :
    famPot ε m P (u, w) = wellPot ε (w - (i : ℕ)) + P i u := by
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin m)), j ≠ i → sel ε j w * P j u = 0 := by
    intro j _ hji
    have hij := one_le_abs_index_sub hji
    have htri := abs_index_sub_le (((i : ℕ) : ℝ)) (((j : ℕ) : ℝ)) w
    have hfar : 4 * ε ≤ |w - ((j : ℕ) : ℝ)| := by linarith
    rw [sel_eq_zero hε hfar, zero_mul]
  have hsum : (∑ j : Fin m, sel ε j w * P j u) = sel ε i w * P i u :=
    Finset.sum_eq_single i hzero (fun hi => absurd (Finset.mem_univ i) hi)
  rw [famPot, hsum, sel_eq_one hε h, one_mul, tubeWall_eq_wellPot hε hεs i (by linarith [h])]

/-- **The barrier separating the corridors**: outside all the tubes the potential is at least the
wall height `4`, provided the longitudinal potentials are nonnegative. -/
theorem famPot_ge_four_of_far (hε : 0 < ε) {P : Fin m → ℝ → ℝ} (hP : ∀ i u, 0 ≤ P i u)
    {u w : ℝ} (h : ∀ j : Fin m, 2 * ε ≤ |w - (j : ℕ)|) : 4 ≤ famPot ε m P (u, w) := by
  have hsum : 0 ≤ ∑ j : Fin m, sel ε j w * P j u := by
    refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ (hP _ _)
    have h1 := wellProfile_le ((w - (j : ℕ)) / (2 * ε))
    rw [sel]
    linarith
  rw [famPot, tubeWall_eq_four_of_far hε h]
  linarith

theorem contDiff_tubeWall (ε : ℝ) (m : ℕ) {n : ℕ∞} : ContDiff ℝ n (tubeWall ε m) := by
  unfold tubeWall
  refine contDiff_const.mul (contDiff_prod fun i _ => ?_)
  unfold coreFactor
  exact (contDiff_wellProfile.comp ((contDiff_id.sub contDiff_const).div_const ε)).div_const 4

theorem contDiff_sel (ε : ℝ) (i : ℕ) {n : ℕ∞} : ContDiff ℝ n (sel ε i) := by
  unfold sel
  exact contDiff_const.sub
    ((contDiff_wellProfile.comp ((contDiff_id.sub contDiff_const).div_const (2 * ε))).div_const 4)

/-- The network potential is as smooth as its longitudinal potentials. -/
theorem contDiff_famPot (ε : ℝ) {P : Fin m → ℝ → ℝ} {n : ℕ∞} (hP : ∀ i, ContDiff ℝ n (P i)) :
    ContDiff ℝ n (famPot ε m P) := by
  unfold famPot
  refine ((contDiff_tubeWall ε m).comp contDiff_snd).add (ContDiff.sum fun i _ => ?_)
  exact ((contDiff_sel ε i).comp contDiff_snd).mul ((hP i).comp contDiff_fst)

/-! ### The fixed layout of the corridor of a germ -/

open Classical in
/-- The first fold and the gap between consecutive folds of the itinerary of `ζ`, chosen once
for every germ whose routing component contains a fold. -/
noncomputable def foldPair (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (h : ∃ k, IsFold F ζ k) : ℕ × ℕ :=
  ((exists_foldData h).choose, (exists_foldData h).choose_spec.choose)

theorem foldPair_spec (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (h : ∃ k, IsFold F ζ k) :
    FoldData F ζ (foldPair F ζ h).1 (foldPair F ζ h).2 :=
  (exists_foldData h).choose_spec.choose_spec

open Classical in
/-- The corridor coordinate origin of the germ `ζ`, in the layout coordinate `vpos`: the lower cap
if the routing component of `ζ` has a fold, and one shortest edge length behind the initial edge
otherwise. -/
noncomputable def corridorLow (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) : ℝ :=
  if h : ∃ k, IsFold F ζ k then vpos F ζ ((foldPair F ζ h).1 + (foldPair F ζ h).2 + 1)
  else -minLen Γ ζ.1

open Classical in
/-- The upper cap of the corridor of `ζ` (meaningful only in the presence of a fold). -/
noncomputable def corridorHigh (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) : ℝ :=
  if h : ∃ k, IsFold F ζ k then vpos F ζ ((foldPair F ζ h).1 + 1) else 0

/-- The length of a corridor with two caps. -/
noncomputable def corridorLen (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) : ℝ :=
  corridorHigh F ζ - corridorLow F ζ

theorem corridorLow_of_fold (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (h : ∃ k, IsFold F ζ k) :
    corridorLow F ζ = vpos F ζ ((foldPair F ζ h).1 + (foldPair F ζ h).2 + 1) := by
  rw [corridorLow, dif_pos h]

theorem corridorHigh_of_fold (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (h : ∃ k, IsFold F ζ k) :
    corridorHigh F ζ = vpos F ζ ((foldPair F ζ h).1 + 1) := by
  rw [corridorHigh, dif_pos h]

theorem corridorLow_of_not_fold (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (h : ¬ ∃ k, IsFold F ζ k) :
    corridorLow F ζ = -minLen Γ ζ.1 := by
  rw [corridorLow, dif_neg h]

open Classical in
/-- **The longitudinal potential of the corridor of `ζ`**: two reflecting caps at the fixed ends
of `F` for an interval component, and nothing at all for a circle component. -/
noncomputable def longPot (F : RoutingLaw Γ) (ε : ℝ) (ζ : Γ.EdgeEnd) : ℝ → ℝ :=
  if ∃ k, IsFold F ζ k then corridorPot ε (corridorLen F ζ) else fun _ => 0

theorem longPot_of_fold (F : RoutingLaw Γ) (ε : ℝ) (ζ : Γ.EdgeEnd) (h : ∃ k, IsFold F ζ k) :
    longPot F ε ζ = corridorPot ε (corridorLen F ζ) := by
  rw [longPot, if_pos h]

theorem longPot_of_not_fold (F : RoutingLaw Γ) (ε : ℝ) (ζ : Γ.EdgeEnd)
    (h : ¬ ∃ k, IsFold F ζ k) : longPot F ε ζ = fun _ => 0 := by
  rw [longPot, if_neg h]

theorem longPot_nonneg (F : RoutingLaw Γ) (ε : ℝ) (ζ : Γ.EdgeEnd) (u : ℝ) :
    0 ≤ longPot F ε ζ u := by
  by_cases h : ∃ k, IsFold F ζ k
  · rw [longPot_of_fold F ε ζ h]; exact corridorPot_nonneg _ _ _
  · rw [longPot_of_not_fold F ε ζ h]

theorem contDiff_longPot (F : RoutingLaw Γ) (ε : ℝ) (ζ : Γ.EdgeEnd) {n : ℕ∞} :
    ContDiff ℝ n (longPot F ε ζ) := by
  by_cases h : ∃ k, IsFold F ζ k
  · rw [longPot_of_fold F ε ζ h]; exact contDiff_corridorPot _ _
  · rw [longPot_of_not_fold F ε ζ h]; exact contDiff_const

/-! ### The uniform network potential -/

/-- The height of the corridor of the germ `ζ`. -/
noncomputable def uniRow (ζ : Γ.EdgeEnd) : ℝ := (((netIndex Γ ζ : Fin _) : ℕ) : ℝ)

/-- **The uniform universal potential of `(Γ, F)` at scale `ε`.**  One corridor per edge-end germ,
at the height `uniRow ζ`, carrying the longitudinal potential `longPot F ε ζ`.  It depends on
`(Γ, F)` and `ε` only. -/
noncomputable def uniPot (F : RoutingLaw Γ) (ε : ℝ) : ℝ × ℝ → ℝ :=
  famPot ε (Fintype.card Γ.EdgeEnd) (fun k => longPot F ε ((netIndex Γ).symm k))

/-- **The uniform potential is smooth** (`C^∞`). -/
theorem contDiff_uniPot (F : RoutingLaw Γ) (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (uniPot F ε) :=
  contDiff_famPot ε fun _ => contDiff_longPot _ _ _

theorem uniPot_nonneg (F : RoutingLaw Γ) (ε : ℝ) (x : ℝ × ℝ) : 0 ≤ uniPot F ε x := by
  rw [uniPot, famPot]
  refine add_nonneg (tubeWall_nonneg _ _ _) (Finset.sum_nonneg fun j _ => mul_nonneg ?_
    (longPot_nonneg _ _ _ _))
  have h1 := wellProfile_le ((x.2 - (j : ℕ)) / (2 * ε))
  rw [sel]
  linarith

/-- **Exact separability on the tube of the corridor of `ζ`.** -/
theorem uniPot_of_tube (F : RoutingLaw Γ) (hε : 0 < ε) (hεs : ε ≤ 1 / 8) (ζ : Γ.EdgeEnd)
    {u w : ℝ} (h : |w - uniRow ζ| ≤ 2 * ε) :
    uniPot F ε (u, w) = wellPot ε (w - uniRow ζ) + longPot F ε ζ u := by
  rw [uniPot, famPot_of_corridor hε hεs _ (netIndex Γ ζ) h, Equiv.symm_apply_apply]
  rfl

/-- **The barrier between the corridors**: outside all the tubes the uniform potential is at
least `4`, which exceeds every energy of the window `K⋆ = [1/2, 2]`. -/
theorem uniPot_ge_four_of_far (F : RoutingLaw Γ) (hε : 0 < ε) {u w : ℝ}
    (h : ∀ ζ : Γ.EdgeEnd, 2 * ε ≤ |w - uniRow ζ|) : 4 ≤ uniPot F ε (u, w) := by
  refine famPot_ge_four_of_far hε (fun _ _ => longPot_nonneg _ _ _ _) fun j => ?_
  have := h ((netIndex Γ).symm j)
  rwa [uniRow, Equiv.apply_symm_apply] at this

/-- Distinct corridors are at distance at least `1`. -/
theorem one_le_abs_uniRow_sub {ζ ζ' : Γ.EdgeEnd} (h : ζ ≠ ζ') :
    1 ≤ |uniRow ζ - uniRow ζ'| := by
  have hne : netIndex Γ ζ' ≠ netIndex Γ ζ := fun hc => h ((netIndex Γ).injective hc).symm
  exact one_le_abs_index_sub hne

/-! ### Hamilton's equations -/

/-- The force of the Hamiltonian `½|p|² + W(x)` on `ℝ² × ℝ²`: minus the two partial derivatives
of `W`. -/
noncomputable def gradForce (W : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  (-deriv (fun s => W (s, y.2)) y.1, -deriv (fun s => W (y.1, s)) y.2)

/-- **A trajectory of the Hamiltonian `½|p|² + W(x)` for all nonnegative times**: `x' = p`,
`p' = -∇W(x)` on `[0, ∞)`. -/
def IsHamiltonianTrajectory (W : ℝ × ℝ → ℝ) (x p : ℝ → ℝ × ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivWithinAt x (p t) (Ici 0) t ∧
    HasDerivWithinAt p (gradForce W (x t)) (Ici 0) t

/-- The energy `½|p|² + W(x)` (with the Euclidean norm of the momentum). -/
noncomputable def hamEnergy (W : ℝ × ℝ → ℝ) (y q : ℝ × ℝ) : ℝ := (q.1 ^ 2 + q.2 ^ 2) / 2 + W y

/-- **The force of the uniform network is separable inside the tube of a corridor.** -/
theorem gradForce_uniPot_of_tube (F : RoutingLaw Γ) (hε : 0 < ε) (hεs : ε ≤ 1 / 8)
    (ζ : Γ.EdgeEnd) {y : ℝ × ℝ} (h : |y.2 - uniRow ζ| < 2 * ε) :
    gradForce (uniPot F ε) y =
      (-deriv (longPot F ε ζ) y.1, -deriv (fun s => wellPot ε (s - uniRow ζ)) y.2) := by
  have hfst : (fun s => uniPot F ε (s, y.2)) =
      fun s => wellPot ε (y.2 - uniRow ζ) + longPot F ε ζ s := by
    funext s
    exact uniPot_of_tube F hε hεs ζ h.le
  have hsnd : (fun s => uniPot F ε (y.1, s)) =ᶠ[nhds y.2]
      fun s => wellPot ε (s - uniRow ζ) + longPot F ε ζ y.1 := by
    have hopen : Ioo (uniRow ζ - 2 * ε) (uniRow ζ + 2 * ε) ∈ nhds y.2 := by
      obtain ⟨h1, h2⟩ := abs_lt.mp h
      exact Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hopen] with s hs
    have hs' : |s - uniRow ζ| ≤ 2 * ε := by
      rw [abs_le]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact uniPot_of_tube F hε hεs ζ hs'
  rw [gradForce, hfst, hsnd.deriv_eq]
  congr 1
  · rw [deriv_const_add']
  · rw [deriv_add_const']

/-! ### The fixed projection to the graph -/

/-- The orientation of the identification of flight `j` of the corridor of `ζ` with its edge. -/
noncomputable def chartSign (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (j : ℕ) : ℝ :=
  EdgeEnd.sign Γ (F.itinerary ζ j) * dirSign F ζ j

theorem chartSign_eq_one_or (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (j : ℕ) :
    chartSign F ζ j = 1 ∨ chartSign F ζ j = -1 := by
  rcases dirSign_eq_one_or_neg_one (F := F) (η₀ := ζ) j with hd | hd <;>
    rcases hb : (F.itinerary ζ j).2 with _ | _ <;>
    rw [chartSign, hd] <;>
    [rw [sign_of_false hb]; rw [sign_of_true hb]; rw [sign_of_false hb]; rw [sign_of_true hb]] <;>
    norm_num

/-- **The chart of flight `j`** in a corridor whose coordinate origin is the layout coordinate
`low`: the affine isometry which maps the corridor cell between `vpos j - low` and
`vpos (j + 1) - low` onto the edge `(F.itinerary ζ j).1`, the arrival vertex of the flight to the
germ `F.itinerary ζ j`, and the longitudinal momentum to the graph momentum. -/
noncomputable def chartAt (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (low : ℝ) (j : ℕ) (u v : ℝ) :
    ℝ × ℝ :=
  (EdgeEnd.coordinate Γ (F.itinerary ζ j) + chartSign F ζ j * (u - (vpos F ζ (j + 1) - low)),
    chartSign F ζ j * v)

/-- **The projection data of the uniform network**, chosen once: the chart of flight `j` in the
corridor of `ζ`.  It depends only on `(Γ, F, ζ, j)`. -/
noncomputable def uniChart (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (j : ℕ) (u v : ℝ) : ℝ × ℝ :=
  chartAt F ζ (corridorLow F ζ) j u v

end HamiltonianMetricGraphs
