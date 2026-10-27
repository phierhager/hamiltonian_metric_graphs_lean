/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.WorkedExamplesBasic

/-!
# Plateau potentials and energy filtration (Section XI.D)

## The hypotheses

On a finite metric graph `Γ` fix `0 < δ < ½ min_e ℓ_e` and plateau heights `c_e > max_v V(v)`,
and edgewise `C²` potentials (a `MechanicalPotential`, which carries the prescribed vertex
values at the endpoints) with

  `V_e = c_e` on `[δ, ℓ_e - δ]`,  `V_e' > 0` on `(0, δ)`,  `V_e' < 0` on `(ℓ_e - δ, ℓ_e)`

(`IsPlateau V δ c`).  Fix speed-independent vertex permutations `F_v` (a `PermutationLaw`).

## Results (`example_plateau`)

* for every shell-regular `E ∉ {V(v)} ∪ {c_e}` and every admissible end `η` of `e`,
  `κ_E(η) = η̄` if `E > c_e` and `κ_E(η) = η` if `E < c_e` (`plateau_retraceEnd`): `e` is
  traversed when `E > c_e`, while for `E < c_e` an accessible particle turns on a flank and
  returns — blocked edges remain as reflecting stubs;
* with the traversable subgraph `Γ_E = {e : c_e < E}` (`traversable`, eq. (23)),
  `Π_E(η) = F(κ_E(η))` with `κ_E(η) = η̄` for `η` on `Γ_E` and `η` otherwise
  (`plateau_germStep`); hence `Π_E` is determined by the vertex values (through `G_E`), the
  plateau heights (through `Γ_E`) and the vertex permutations: two such energies with the same
  `G_E` and `Γ_E` have the same `Π_E` and the same cycle type (`plateau_germStep_congr`,
  `plateau_cycleType_congr`) — the cycle type is combinatorial;
* `E ↦ Γ_E` is monotone, and if the `c_e` are distinct, crossing one plateau height `c_{e₀}` adds
  exactly the edge `e₀` (`traversable_mono`, `traversable_eq_insert`).

In addition (not claimed in the paper, which assumes shell-regularity) every
`E ∉ {V(v)} ∪ {c_e}` *is* shell-regular under these hypotheses (`plateau_shellRegular`).
-/

namespace HamiltonianMetricGraphs

namespace WorkedExamples

open Set FiniteMetricGraph MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- **The plateau hypotheses of Sec. XI.D**: `0 < δ < ½ ℓ_e` for every edge, `c_e > V(v)` for every
edge and vertex, `V_e = c_e` on `[δ, ℓ_e - δ]`, `V_e' > 0` on `(0, δ)` and `V_e' < 0` on
`(ℓ_e - δ, ℓ_e)`. -/
structure IsPlateau (δ : ℝ) (c : Γ.Edge → ℝ) : Prop where
  delta_pos : 0 < δ
  delta_lt : ∀ e, δ < Γ.length e / 2
  height_gt : ∀ e v, V.vertexValue v < c e
  plateau : ∀ e, ∀ x ∈ Icc δ (Γ.length e - δ), V.extension e x = c e
  left_flank : ∀ e, ∀ x ∈ Ioo 0 δ, 0 < deriv (V.extension e) x
  right_flank : ∀ e, ∀ x ∈ Ioo (Γ.length e - δ) (Γ.length e), deriv (V.extension e) x < 0

/-- **The traversable subgraph** `Γ_E = {e : c_e < E}` (eq. (23)). -/
def traversable (c : Γ.Edge → ℝ) (E : ℝ) : Set Γ.Edge := {e | c e < E}

variable {V} {δ : ℝ} {c : Γ.Edge → ℝ}

namespace IsPlateau

variable (hP : IsPlateau V δ c)
include hP

theorem delta_le (e : Γ.Edge) : δ ≤ Γ.length e - δ := by
  have := hP.delta_lt e; linarith

/-- `V_e` is strictly increasing on the left flank `[0, δ]`. -/
theorem strictMonoOn_left (e : Γ.Edge) : StrictMonoOn (V.extension e) (Icc 0 δ) := by
  have hδl : δ ≤ Γ.length e := by have := hP.delta_lt e; have := Γ.length_pos e; linarith
  exact strictMonoOn_of_deriv_pos (convex_Icc 0 δ)
    ((V.extension_continuousOn_closedEdge e).mono (Icc_subset_Icc le_rfl hδl))
    (by rw [interior_Icc]; exact hP.left_flank e)

/-- `V_e` is strictly decreasing on the right flank `[ℓ_e - δ, ℓ_e]`. -/
theorem strictAntiOn_right (e : Γ.Edge) :
    StrictAntiOn (V.extension e) (Icc (Γ.length e - δ) (Γ.length e)) := by
  have hδ0 : 0 ≤ Γ.length e - δ := by have := hP.delta_lt e; have := Γ.length_pos e; linarith
  exact strictAntiOn_of_deriv_neg (convex_Icc _ _)
    ((V.extension_continuousOn_closedEdge e).mono (Icc_subset_Icc hδ0 le_rfl))
    (by rw [interior_Icc]; exact hP.right_flank e)

/-- `V_e ≤ c_e` on the whole closed edge. -/
theorem le_height (e : Γ.Edge) {x : ℝ} (hx : x ∈ Icc 0 (Γ.length e)) : V.extension e x ≤ c e := by
  have hδ := hP.delta_pos
  have hle := hP.delta_le e
  by_cases h1 : x ≤ δ
  · rw [← hP.plateau e δ ⟨le_rfl, hle⟩]
    exact (hP.strictMonoOn_left e).monotoneOn ⟨hx.1, h1⟩ ⟨hδ.le, le_rfl⟩ h1
  · by_cases h2 : x ≤ Γ.length e - δ
    · exact (hP.plateau e x ⟨(not_le.mp h1).le, h2⟩).le
    · rw [← hP.plateau e (Γ.length e - δ) ⟨hle, le_rfl⟩]
      exact (hP.strictAntiOn_right e).antitoneOn ⟨le_rfl, by linarith⟩
        ⟨(not_le.mp h2).le, hx.2⟩ (not_le.mp h2).le

end IsPlateau

/-! ### The retrace map -/

/-- **`κ_E` on a plateau potential.**  At a shell-regular energy `E` which is not a plateau
height, an admissible end `η` of `e` satisfies `κ_E(η) = η̄` if `E > c_e` and `κ_E(η) = η` if
`E < c_e`. -/
theorem plateau_retraceEnd (hP : IsPlateau V δ c) {E : ℝ} (hE : V.ShellRegular E)
    (hc : ∀ e, E ≠ c e) {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) :
    V.retraceEnd E η = if c η.1 < E then (η.1, !η.2) else η := by
  split_ifs with hlt
  · exact V.retraceEnd_of_forall_lt hE hη fun x hx => (hP.le_height η.1 hx).trans_lt hlt
  · refine V.retraceEnd_of_exists_gt hE hη ⟨δ, ⟨hP.delta_pos.le, ?_⟩, ?_⟩
    · have := hP.delta_lt η.1; have := Γ.length_pos η.1; linarith
    · rw [hP.plateau η.1 δ ⟨le_rfl, hP.delta_le η.1⟩]
      exact lt_of_le_of_ne (not_lt.mp hlt) (hc η.1)

open Classical in
/-- **`Π_E = F_E ∘ κ_E` on a plateau potential**: an admissible end on a traversable edge is
flipped and then routed, an end on a blocked edge is routed back from its own end. -/
theorem plateau_germStep (hP : IsPlateau V δ c) (F : PermutationLaw Γ) {E : ℝ}
    (hE : V.ShellRegular E) (hc : ∀ e, E ≠ c e) {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) :
    V.germStep (F.toBorelScattering V) E η =
      F.route (if η.1 ∈ traversable c E then (η.1, !η.2) else η) := by
  rw [V.germStep_permutationLaw F hE hη, plateau_retraceEnd hP hE hc hη]
  by_cases hlt : c η.1 < E
  · rw [if_pos hlt, if_pos (show η.1 ∈ traversable c E from hlt)]
  · rw [if_neg hlt, if_neg (show η.1 ∉ traversable c E from hlt)]

/-- **`Π_E` is determined by `G_E`, `Γ_E` and `F`.**  Two shell-regular energies, neither a
plateau height, with the same admissible ends and the same traversable subgraph have the same
end permutation. -/
theorem plateau_germStep_congr (hP : IsPlateau V δ c) (F : PermutationLaw Γ) {E E' : ℝ}
    (hE : V.ShellRegular E) (hE' : V.ShellRegular E') (hc : ∀ e, E ≠ c e) (hc' : ∀ e, E' ≠ c e)
    (hG : V.allowedGerms E = V.allowedGerms E') (hT : traversable c E = traversable c E')
    {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) :
    V.germStep (F.toBorelScattering V) E η = V.germStep (F.toBorelScattering V) E' η := by
  rw [plateau_germStep hP F hE hc hη, plateau_germStep hP F hE' hc' (hG ▸ hη), hT]

open Classical in
/-- **The cycle type of `Π_E` is combinatorial**: it is the same for two shell-regular energies,
neither a plateau height, with the same admissible ends and the same traversable subgraph. -/
theorem plateau_cycleType_congr (hP : IsPlateau V δ c) (F : PermutationLaw Γ) {E E' : ℝ}
    (hE : V.ShellRegular E) (hE' : V.ShellRegular E') (hc : ∀ e, E ≠ c e) (hc' : ∀ e, E' ≠ c e)
    (hG : V.allowedGerms E = V.allowedGerms E') (hT : traversable c E = traversable c E') :
    (V.shellGermPerm (F.toBorelScattering V) hE).cycleType =
      (V.shellGermPerm (F.toBorelScattering V) hE').cycleType := by
  rw [← Equiv.Perm.cycleType_ofSubtype,
    ← Equiv.Perm.cycleType_ofSubtype (g := V.shellGermPerm _ hE')]
  congr 1
  refine Equiv.ext fun η => ?_
  by_cases hη : η ∈ V.allowedGerms E
  · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hη,
      Equiv.Perm.ofSubtype_apply_of_mem _ (show η ∈ V.allowedGerms E' from hG ▸ hη),
      shellGermPerm_apply, shellGermPerm_apply]
    exact plateau_germStep_congr hP F hE hE' hc hc' hG hT hη
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hη,
      Equiv.Perm.ofSubtype_apply_of_not_mem _ (show η ∉ V.allowedGerms E' from hG ▸ hη)]

/-! ### Shell-regularity -/

/-- Under the plateau hypotheses, every energy that is neither a vertex value nor a plateau height
is shell-regular. -/
theorem plateau_shellRegular (hP : IsPlateau V δ c) {E : ℝ} (hexc : E ∉ V.exceptionalEnergies)
    (hc : ∀ e, E ≠ c e) : V.ShellRegular E := by
  refine (V.shellRegular_iff hexc).mpr ⟨?_, ?_⟩
  · intro e x hx hxE hd
    by_cases h1 : x < δ
    · exact (hP.left_flank e x ⟨hx.1, h1⟩).ne' hd
    · by_cases h2 : x ≤ Γ.length e - δ
      · exact hc e (hxE.symm.trans (hP.plateau e x ⟨not_lt.mp h1, h2⟩))
      · exact (hP.right_flank e x ⟨not_le.mp h2, hx.2⟩).ne hd
  · intro e x hx hxE
    have hle := hP.delta_le e
    by_cases hcE : c e < E
    · exact Or.inl fun s hs => (hP.le_height e ⟨hs.1, hs.2.trans hx.2⟩).trans hcE.le
    · have hEc : E < c e := lt_of_le_of_ne (not_lt.mp hcE) (hc e)
      by_cases h1 : x ≤ δ
      · left
        intro s hs
        exact ((hP.strictMonoOn_left e).monotoneOn ⟨hs.1, hs.2.trans h1⟩ ⟨hx.1, h1⟩ hs.2).trans
          hxE
      · by_cases h2 : x < Γ.length e - δ
        · exfalso
          rw [hP.plateau e x ⟨(not_le.mp h1).le, h2.le⟩] at hxE
          linarith
        · right
          intro s hs
          exact ((hP.strictAntiOn_right e).antitoneOn ⟨not_lt.mp h2, hx.2⟩
            ⟨(not_lt.mp h2).trans hs.1, hs.2⟩ hs.1).trans hxE

/-! ### The energy filtration -/

/-- `E ↦ Γ_E` is monotone. -/
theorem traversable_mono {E E' : ℝ} (h : E ≤ E') : traversable c E ⊆ traversable c E' :=
  fun _ he => lt_of_lt_of_le he h

/-- **The filtration grows by one edge at each plateau height**: if the `c_e` are distinct and
`c_{e₀}` is the only plateau height in `[E, E')`, then `Γ_{E'} = Γ_E ∪ {e₀}`. -/
theorem traversable_eq_insert (hinj : Function.Injective c) {E E' : ℝ} {e₀ : Γ.Edge}
    (h₀ : c e₀ ∈ Ico E E') (honly : ∀ e, c e ∈ Ico E E' → c e = c e₀) :
    traversable c E' = insert e₀ (traversable c E) := by
  ext e
  simp only [traversable, mem_setOf_eq, mem_insert_iff]
  constructor
  · intro he
    by_cases hlt : c e < E
    · exact Or.inr hlt
    · exact Or.inl (hinj (honly e ⟨not_lt.mp hlt, he⟩))
  · rintro (rfl | he)
    · exact h₀.2
    · exact he.trans_le (h₀.1.trans h₀.2.le)

/-! ### Section XI.D, packaged -/

open Classical in
/-- **Section XI.D (plateau potentials), packaged.**  Under the plateau hypotheses
`IsPlateau V δ c` and for speed-independent vertex permutations `F`:

* every `E ∉ {V(v)} ∪ {c_e}` is shell-regular;
* for every shell-regular `E ∉ {c_e}` and admissible `η` of `e`: `κ_E(η) = η̄` if `E > c_e`, and
  `κ_E(η) = η` if `E < c_e`;
* with `Γ_E = {e : c_e < E}`, `Π_E(η) = F(η̄)` for `η` on `Γ_E` and `Π_E(η) = F(η)` otherwise;
* `Π_E`, hence its cycle type, depends only on `G_E`, `Γ_E` and `F`;
* `E ↦ Γ_E` is monotone, and for distinct heights, crossing `c_{e₀}` adds exactly `e₀`. -/
theorem example_plateau (hP : IsPlateau V δ c) (F : PermutationLaw Γ) :
    (∀ E, E ∉ V.exceptionalEnergies → (∀ e, E ≠ c e) → V.ShellRegular E) ∧
      (∀ E, V.ShellRegular E → (∀ e, E ≠ c e) → ∀ η ∈ V.allowedGerms E,
        (c η.1 < E → V.retraceEnd E η = (η.1, !η.2)) ∧ (E < c η.1 → V.retraceEnd E η = η)) ∧
      (∀ E, V.ShellRegular E → (∀ e, E ≠ c e) → ∀ η ∈ V.allowedGerms E,
        V.germStep (F.toBorelScattering V) E η =
          F.route (if η.1 ∈ traversable c E then (η.1, !η.2) else η)) ∧
      (∀ E E' (hE : V.ShellRegular E) (hE' : V.ShellRegular E'), (∀ e, E ≠ c e) →
        (∀ e, E' ≠ c e) → V.allowedGerms E = V.allowedGerms E' →
        traversable c E = traversable c E' →
        (∀ η ∈ V.allowedGerms E,
          V.germStep (F.toBorelScattering V) E η = V.germStep (F.toBorelScattering V) E' η) ∧
        (V.shellGermPerm (F.toBorelScattering V) hE).cycleType =
          (V.shellGermPerm (F.toBorelScattering V) hE').cycleType) ∧
      (∀ E E', E ≤ E' → traversable c E ⊆ traversable c E') ∧
      (Function.Injective c → ∀ E E' e₀, c e₀ ∈ Ico E E' → (∀ e, c e ∈ Ico E E' → c e = c e₀) →
        traversable c E' = insert e₀ (traversable c E)) := by
  refine ⟨fun E hexc hc => plateau_shellRegular hP hexc hc, fun E hE hc η hη => ⟨?_, ?_⟩,
    fun E hE hc η hη => plateau_germStep hP F hE hc hη,
    fun E E' hE hE' hc hc' hG hT => ⟨fun η hη => plateau_germStep_congr hP F hE hE' hc hc' hG hT hη,
      plateau_cycleType_congr hP F hE hE' hc hc' hG hT⟩,
    fun E E' h => traversable_mono h,
    fun hinj E E' e₀ h₀ honly => traversable_eq_insert hinj h₀ honly⟩
  · intro hlt
    rw [plateau_retraceEnd hP hE hc hη, if_pos hlt]
  · intro hlt
    rw [plateau_retraceEnd hP hE hc hη, if_neg (not_lt.mpr hlt.le)]

end WorkedExamples

end HamiltonianMetricGraphs
