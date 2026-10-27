/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalComponentResolved
import HamiltonianMetricGraphs.Realization.UniversalNetworkExistence

/-!
# The potential `W^F_ε` of Sec. IX.F

The component `R_i` of the resolved space is placed along the line `w = i` of `ℝ²`
(`i = 1, …, m`; the Lean index `i : Fin m` is placed on `w = i + 1`, `compRow`), and

  `W^F_ε(u, w) = 4 ∏_i χ_{1,4}((w - i)² / ε²) + ∑_i (1 - χ_{1,4}((w - i)² / (4ε²))) P_{ε,i}(u)`

with `P_{ε,i}(u) = B(-u/ε) + B((u - L_i)/ε)` for an interval and `P_{ε,i} = 0` for a circle
(`resolvedPot`, `resolvedCap`).  Here `χ_{a,b} = plateau a b` (built from the fixed smooth step
`Real.smoothTransition`), `B = barrierProfile`, and `A_ε(s) = 4 χ_{1,4}(s²/ε²) = wellPot ε s`
(`wellPot_eq_chi`).

The file proves that `W^F_ε` is smooth and nonnegative, the separation
`W^F_ε = A_ε(w - i) + P_{ε,i}(u)` on `|w - i| ≤ 2ε` (`resolvedPot_of_tube`), the confinement of
every trajectory with energy below `4` to its tube (`resolved_confined`), and the existence of
trajectories of `H_ε = ½|ξ|² + W^F_ε` for all real times (`exists_resolvedFlowLine`).
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph
open scoped Topology

variable {Γ : FiniteMetricGraph} (F : RoutingLaw Γ) {ε : ℝ}

/-! ### The profiles -/

/-- `A_ε(s) = 4 χ_{1,4}(s²/ε²)`, as in the paper. -/
theorem wellPot_eq_chi (ε s : ℝ) : wellPot ε s = 4 * plateau 1 4 (s ^ 2 / ε ^ 2) := by
  rw [wellPot, wellProfile, div_pow]

/-- `B(s) = 4 e^{1 - 1/s}` for `s > 0`. -/
theorem barrierProfile_of_pos {s : ℝ} (hs : 0 < s) :
    barrierProfile s = 4 * Real.exp (1 - 1 / s) := by
  rw [barrierProfile, glue_of_pos hs, mul_assoc, ← Real.exp_add, one_div, sub_eq_add_neg]

/-! ### The potential -/

/-- **The height of the corridor of component `i`**: the line `w = i` of the paper (the Lean index
`i : Fin m` is the paper's `i + 1`). -/
def compRow (i : Fin (RoutingLaw.compCount F)) : ℝ := ((i : ℕ) : ℝ) + 1

open Classical in
/-- **The longitudinal caps `P_{ε,i}`**: `B(-u/ε) + B((u - L_i)/ε)` for an interval component,
`0` for a circle. -/
noncomputable def resolvedCap (ε : ℝ) (i : Fin (RoutingLaw.compCount F)) (u : ℝ) : ℝ :=
  if IsIntervalComp F i then barrierProfile (-u / ε) + barrierProfile ((u - compLen F i) / ε)
  else 0

/-- **The potential `W^F_ε` of Sec. IX.F.** -/
noncomputable def resolvedPot (ε : ℝ) (x : ℝ × ℝ) : ℝ :=
  4 * ∏ i : Fin (RoutingLaw.compCount F), plateau 1 4 ((x.2 - compRow F i) ^ 2 / ε ^ 2) +
    ∑ i : Fin (RoutingLaw.compCount F),
      (1 - plateau 1 4 ((x.2 - compRow F i) ^ 2 / (4 * ε ^ 2))) * resolvedCap F ε i x.1

theorem resolvedCap_of_interval {i : Fin (RoutingLaw.compCount F)} (h : IsIntervalComp F i) :
    resolvedCap F ε i = corridorPot ε (compLen F i) := by
  funext u
  rw [resolvedCap, if_pos h, corridorPot, wallPot, wallPot, neg_div, add_comm]

theorem resolvedCap_of_circle {i : Fin (RoutingLaw.compCount F)} (h : ¬ IsIntervalComp F i) :
    resolvedCap F ε i = fun _ => 0 := by
  funext u
  rw [resolvedCap, if_neg h]

theorem resolvedCap_nonneg (ε : ℝ) (i : Fin (RoutingLaw.compCount F)) (u : ℝ) :
    0 ≤ resolvedCap F ε i u := by
  by_cases h : IsIntervalComp F i
  · rw [resolvedCap_of_interval F h]; exact corridorPot_nonneg _ _ _
  · rw [resolvedCap_of_circle F h]

theorem contDiff_resolvedCap (ε : ℝ) (i : Fin (RoutingLaw.compCount F)) {n : ℕ∞} :
    ContDiff ℝ n (resolvedCap F ε i) := by
  by_cases h : IsIntervalComp F i
  · rw [resolvedCap_of_interval F h]; exact contDiff_corridorPot _ _
  · rw [resolvedCap_of_circle F h]; exact contDiff_const

theorem exists_bound_deriv_resolvedCap (hε : 0 < ε) (i : Fin (RoutingLaw.compCount F)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, |deriv (resolvedCap F ε i) y| ≤ R := by
  by_cases h : IsIntervalComp F i
  · rw [resolvedCap_of_interval F h]; exact exists_bound_deriv_corridorPot hε _
  · rw [resolvedCap_of_circle F h]; exact ⟨0, le_rfl, fun y => by simp⟩

/-- `P_{ε,i} = 0` on `Λ_i`. -/
theorem resolvedCap_eq_zero (hε : 0 < ε) {i : Fin (RoutingLaw.compCount F)} {u : ℝ}
    (hu : u ∈ compDomain F i) : resolvedCap F ε i u = 0 := by
  by_cases h : IsIntervalComp F i
  · rw [compDomain_of_interval F h] at hu
    rw [resolvedCap_of_interval F h]; exact corridorPot_of_mem hε hu.1 hu.2
  · rw [resolvedCap_of_circle F h]

/-- `W^F_ε` is the network potential `famPot` of `UniversalNetworkPotential.lean`, with the
corridors shifted to the heights `w = i + 1`. -/
theorem resolvedPot_eq_famPot (ε : ℝ) (x : ℝ × ℝ) :
    resolvedPot F ε x = famPot ε (RoutingLaw.compCount F) (resolvedCap F ε) (x.1, x.2 - 1) := by
  rw [resolvedPot, famPot, tubeWall]
  simp only
  congr 1
  · congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [coreFactor, wellProfile, compRow, div_pow]
    ring_nf
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [sel, wellProfile, compRow, div_pow, mul_pow]
    ring_nf

/-- **`W^F_ε` is smooth.** -/
theorem contDiff_resolvedPot (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (resolvedPot F ε) := by
  have h : resolvedPot F ε =
      famPot ε (RoutingLaw.compCount F) (resolvedCap F ε) ∘ fun x : ℝ × ℝ => (x.1, x.2 - 1) := by
    funext x; exact resolvedPot_eq_famPot F ε x
  rw [h]
  exact (contDiff_famPot ε fun i => contDiff_resolvedCap F ε i).comp
    (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))

/-- **`W^F_ε` is nonnegative.** -/
theorem resolvedPot_nonneg (ε : ℝ) (x : ℝ × ℝ) : 0 ≤ resolvedPot F ε x := by
  rw [resolvedPot_eq_famPot, famPot]
  refine add_nonneg (tubeWall_nonneg _ _ _) (Finset.sum_nonneg fun j _ => mul_nonneg ?_
    (resolvedCap_nonneg _ _ _ _))
  have h1 := wellProfile_le ((x.2 - 1 - (j : ℕ)) / (2 * ε))
  rw [sel]
  linarith

/-- **Separation on the tube**: on `|w - i| ≤ 2ε`, `W^F_ε = A_ε(w - i) + P_{ε,i}(u)`. -/
theorem resolvedPot_of_tube (hε : 0 < ε) (hεs : ε ≤ 1 / 8) (i : Fin (RoutingLaw.compCount F))
    {u w : ℝ} (h : |w - compRow F i| ≤ 2 * ε) :
    resolvedPot F ε (u, w) = wellPot ε (w - compRow F i) + resolvedCap F ε i u := by
  have h' : |w - 1 - ((i : ℕ) : ℝ)| ≤ 2 * ε := by
    rw [show w - 1 - ((i : ℕ) : ℝ) = w - compRow F i by rw [compRow]; ring]; exact h
  rw [resolvedPot_eq_famPot, famPot_of_corridor hε hεs _ i h', compRow]
  simp only
  ring_nf

/-- **The barrier between the corridors**: away from all tubes `W^F_ε ≥ 4`. -/
theorem resolvedPot_ge_four_of_far (hε : 0 < ε) {u w : ℝ}
    (h : ∀ i : Fin (RoutingLaw.compCount F), 2 * ε ≤ |w - compRow F i|) :
    4 ≤ resolvedPot F ε (u, w) := by
  rw [resolvedPot_eq_famPot]
  refine famPot_ge_four_of_far hε (fun _ _ => resolvedCap_nonneg _ _ _ _) fun j => ?_
  have := h j
  rwa [compRow, show w - (((j : ℕ) : ℝ) + 1) = w - 1 - ((j : ℕ) : ℝ) by ring] at this

theorem one_le_abs_compRow_sub {i j : Fin (RoutingLaw.compCount F)} (hij : i ≠ j) :
    1 ≤ |compRow F i - compRow F j| := by
  have := one_le_abs_index_sub (Ne.symm hij)
  rwa [compRow, compRow, show ((i : ℕ) : ℝ) + 1 - (((j : ℕ) : ℝ) + 1) =
    ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) by ring]

/-- **The force is separable inside a tube.** -/
theorem gradForce_resolvedPot_of_tube (hε : 0 < ε) (hεs : ε ≤ 1 / 8)
    (i : Fin (RoutingLaw.compCount F)) {y : ℝ × ℝ} (h : |y.2 - compRow F i| < 2 * ε) :
    gradForce (resolvedPot F ε) y =
      (-deriv (resolvedCap F ε i) y.1, -deriv (fun s => wellPot ε (s - compRow F i)) y.2) := by
  have hfst : (fun s => resolvedPot F ε (s, y.2)) =
      fun s => wellPot ε (y.2 - compRow F i) + resolvedCap F ε i s := by
    funext s
    exact resolvedPot_of_tube F hε hεs i h.le
  have hsnd : (fun s => resolvedPot F ε (y.1, s)) =ᶠ[𝓝 y.2]
      fun s => wellPot ε (s - compRow F i) + resolvedCap F ε i y.1 := by
    have hopen : Ioo (compRow F i - 2 * ε) (compRow F i + 2 * ε) ∈ 𝓝 y.2 := by
      obtain ⟨h1, h2⟩ := abs_lt.mp h
      exact Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hopen] with s hs
    exact resolvedPot_of_tube F hε hεs i (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  rw [gradForce, hfst, hsnd.deriv_eq]
  congr 1
  · rw [deriv_const_add']
  · rw [deriv_add_const']

/-! ### Confinement -/

/-- **Thin-tube confinement**: a trajectory of `H_ε` on `[0, ∞)` which starts in the tube of
corridor `i` with energy below `4` stays in it. -/
theorem resolved_confined (hε : 0 < ε) (hεs : ε ≤ 1 / 8) {x p : ℝ → ℝ × ℝ}
    (hsol : IsHamiltonianTrajectory (resolvedPot F ε) x p) (i : Fin (RoutingLaw.compCount F))
    (h0 : |(x 0).2 - compRow F i| < 2 * ε) (hE : hamEnergy (resolvedPot F ε) (x 0) (p 0) < 4) :
    ∀ t, 0 ≤ t → |(x t).2 - compRow F i| < 2 * ε := by
  have hdich : ∀ t, 0 ≤ t →
      |(x t).2 - compRow F i| < 2 * ε ∨ 1 - 2 * ε < |(x t).2 - compRow F i| := by
    intro t ht
    have hEt := hamEnergy_eq (contDiff_resolvedPot F ε) hsol ht
    have hlt : resolvedPot F ε (x t) < 4 := by
      have hk : 0 ≤ ((p t).1 ^ 2 + (p t).2 ^ 2) / 2 := by positivity
      simp only [hamEnergy] at hEt hE
      linarith
    have hex : ∃ j : Fin (RoutingLaw.compCount F), |(x t).2 - compRow F j| < 2 * ε := by
      by_contra hcon
      push Not at hcon
      have h4 := resolvedPot_ge_four_of_far F hε (u := (x t).1) (w := (x t).2) hcon
      exact absurd hlt (not_lt.mpr h4)
    obtain ⟨j, hj⟩ := hex
    by_cases heq : j = i
    · exact Or.inl (heq ▸ hj)
    · right
      have hsep := one_le_abs_compRow_sub F heq
      have htri := abs_index_sub_le (compRow F j) (compRow F i) (x t).2
      linarith
  intro t ht
  by_contra hcon
  rw [not_lt] at hcon
  have hcont : ContinuousOn (fun r => |(x r).2 - compRow F i|) (Icc 0 t) := by
    have hx : ContinuousOn x (Icc 0 t) := fun s hs =>
      ((hsol s hs.1).1.continuousWithinAt).mono Icc_subset_Ici_self
    exact ((continuous_snd.comp_continuousOn hx).sub continuousOn_const).abs
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc ht hcont ⟨h0.le, hcon⟩
  rcases hdich s hs.1 with h | h
  · simp only at hfs; linarith
  · simp only at hfs; linarith

/-- Along a confined trajectory the longitudinal pair solves `u' = ξ_u`, `ξ_u' = -P_{ε,i}'(u)`. -/
theorem resolved_longitudinal (hε : 0 < ε) (hεs : ε ≤ 1 / 8) {x p : ℝ → ℝ × ℝ}
    (hsol : IsHamiltonianTrajectory (resolvedPot F ε) x p) (i : Fin (RoutingLaw.compCount F))
    (hconf : ∀ t, 0 ≤ t → |(x t).2 - compRow F i| < 2 * ε) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => (x s).1) (p t).1 (Ici 0) t ∧
      HasDerivWithinAt (fun s => (p s).1) (-deriv (resolvedCap F ε i) (x t).1) (Ici 0) t := by
  obtain ⟨hx, hp⟩ := hsol t ht
  refine ⟨hasDerivWithinAt_pairFst hx, ?_⟩
  have h := hasDerivWithinAt_pairFst hp
  rwa [gradForce_resolvedPot_of_tube F hε hεs i (hconf t ht)] at h

/-! ### Trajectories for all real times -/

/-- **A trajectory of `H_ε = ½|ξ|² + W` for all real times**: `x' = ξ`, `ξ' = -∇W(x)` on `ℝ`. -/
def IsHamiltonianFlowLine (W : ℝ × ℝ → ℝ) (x p : ℝ → ℝ × ℝ) : Prop :=
  ∀ t, HasDerivAt x (p t) t ∧ HasDerivAt p (gradForce W (x t)) t

theorem IsHamiltonianFlowLine.forward {W : ℝ × ℝ → ℝ} {x p : ℝ → ℝ × ℝ}
    (h : IsHamiltonianFlowLine W x p) : IsHamiltonianTrajectory W x p :=
  fun t _ => ⟨(h t).1.hasDerivWithinAt, (h t).2.hasDerivWithinAt⟩

/-- Reversing time in a flow line gives a flow line. -/
theorem IsHamiltonianFlowLine.reverse {W : ℝ × ℝ → ℝ} {x p : ℝ → ℝ × ℝ}
    (h : IsHamiltonianFlowLine W x p) :
    IsHamiltonianFlowLine W (fun t => x (-t)) (fun t => -p (-t)) := by
  intro t
  have hx := (h (-t)).1.scomp t (hasDerivAt_neg t)
  have hp := ((h (-t)).2.scomp t (hasDerivAt_neg t)).neg
  simp only [neg_smul, one_smul, neg_neg] at hx hp
  exact ⟨hx, hp⟩

/-- **One-dimensional Newton systems with a bounded smooth force have solutions for all real
times.** -/
theorem exists_newton1D_real {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ y, |deriv Φ y| ≤ R) (q₀ p₀ : ℝ) :
    ∃ x p : ℝ → ℝ, x 0 = q₀ ∧ p 0 = p₀ ∧
      (∀ t, HasDerivAt x (p t) t ∧ HasDerivAt p (-deriv Φ (x t)) t) ∧
      (∃ x₁ p₁ x₂ p₂ : ℝ → ℝ, x₁ 0 = q₀ ∧ p₁ 0 = p₀ ∧ x₂ 0 = q₀ ∧ p₂ 0 = -p₀ ∧
        (∀ t, 0 ≤ t → HasDerivWithinAt x₁ (p₁ t) (Ici 0) t ∧
          HasDerivWithinAt p₁ (-deriv Φ (x₁ t)) (Ici 0) t) ∧
        (∀ t, 0 ≤ t → HasDerivWithinAt x₂ (p₂ t) (Ici 0) t ∧
          HasDerivWithinAt p₂ (-deriv Φ (x₂ t)) (Ici 0) t) ∧
        (∀ t, 0 ≤ t → x t = x₁ t ∧ p t = p₁ t) ∧
        (∀ t, t ≤ 0 → x t = x₂ (-t) ∧ p t = -p₂ (-t))) := by
  obtain ⟨x₁, p₁, hx₁, hp₁, h₁⟩ := exists_newton1D_Ici hΦ hR0 hR q₀ p₀
  obtain ⟨x₂, p₂, hx₂, hp₂, h₂⟩ := exists_newton1D_Ici hΦ hR0 hR q₀ (-p₀)
  have hcΦ : Continuous (deriv Φ) := hΦ.continuous_deriv (by norm_num)
  set x : ℝ → ℝ := fun t => if 0 ≤ t then x₁ t else x₂ (-t) with hxdef
  set p : ℝ → ℝ := fun t => if 0 ≤ t then p₁ t else -p₂ (-t) with hpdef
  have hxr : ∀ t, 0 ≤ t → x t = x₁ t := fun t ht => by simp [hxdef, ht]
  have hpr : ∀ t, 0 ≤ t → p t = p₁ t := fun t ht => by simp [hpdef, ht]
  have hxl : ∀ t, t ≤ 0 → x t = x₂ (-t) := by
    intro t ht
    rcases lt_or_eq_of_le ht with h | h
    · simp [hxdef, not_le.mpr h]
    · subst h; simp [hxdef, hx₁, hx₂]
  have hpl : ∀ t, t ≤ 0 → p t = -p₂ (-t) := by
    intro t ht
    rcases lt_or_eq_of_le ht with h | h
    · simp [hpdef, not_le.mpr h]
    · subst h; simp [hpdef, hp₁, hp₂]
  -- the backward pieces, as functions of `t ≤ 0`
  have hbx : ∀ t, t ≤ 0 → HasDerivWithinAt (fun s => x₂ (-s)) (-p₂ (-t)) (Iic 0) t := by
    intro t ht
    have h := ((h₂ (-t) (by linarith)).1).scomp t ((hasDerivAt_neg t).hasDerivWithinAt
      (s := Iic 0)) (fun s (hs : s ≤ 0) => by simp only [mem_Ici, Left.nonneg_neg_iff]; exact hs)
    rw [neg_smul, one_smul] at h
    exact h
  have hbp : ∀ t, t ≤ 0 →
      HasDerivWithinAt (fun s => -p₂ (-s)) (-deriv Φ (x₂ (-t))) (Iic 0) t := by
    intro t ht
    have h := (((h₂ (-t) (by linarith)).2).scomp t ((hasDerivAt_neg t).hasDerivWithinAt
      (s := Iic 0)) (fun s (hs : s ≤ 0) => by
        simp only [mem_Ici, Left.nonneg_neg_iff]; exact hs)).neg
    rw [neg_smul, one_smul, neg_neg] at h
    exact h
  have hderiv : ∀ t, HasDerivAt x (p t) t ∧ HasDerivAt p (-deriv Φ (x t)) t := by
    intro t
    have hright : 0 ≤ t → HasDerivWithinAt x (p t) (Ici 0) t ∧
        HasDerivWithinAt p (-deriv Φ (x t)) (Ici 0) t := by
      intro ht
      refine ⟨((h₁ t ht).1.congr (fun s hs => hxr s hs) (hxr t ht)).congr_deriv (hpr t ht).symm,
        ((h₁ t ht).2.congr (fun s hs => hpr s hs) (hpr t ht)).congr_deriv (by rw [hxr t ht])⟩
    have hleft : t ≤ 0 → HasDerivWithinAt x (p t) (Iic 0) t ∧
        HasDerivWithinAt p (-deriv Φ (x t)) (Iic 0) t := by
      intro ht
      refine ⟨((hbx t ht).congr (fun s hs => hxl s hs) (hxl t ht)).congr_deriv (hpl t ht).symm,
        ((hbp t ht).congr (fun s hs => hpl s hs) (hpl t ht)).congr_deriv (by rw [hxl t ht])⟩
    rcases lt_trichotomy t 0 with h | h | h
    · obtain ⟨a, b⟩ := hleft h.le
      exact ⟨a.hasDerivAt (Iic_mem_nhds h), b.hasDerivAt (Iic_mem_nhds h)⟩
    · subst h
      obtain ⟨a, b⟩ := hleft le_rfl
      obtain ⟨c, d⟩ := hright le_rfl
      have e1 := c.union a
      have e2 := d.union b
      rw [Ici_union_Iic, hasDerivWithinAt_univ] at e1 e2
      exact ⟨e1, e2⟩
    · obtain ⟨a, b⟩ := hright h.le
      exact ⟨a.hasDerivAt (Ici_mem_nhds h), b.hasDerivAt (Ici_mem_nhds h)⟩
  refine ⟨x, p, by rw [hxr 0 le_rfl, hx₁], by rw [hpr 0 le_rfl, hp₁], hderiv,
    x₁, p₁, x₂, p₂, hx₁, hp₁, hx₂, hp₂, h₁, h₂, fun t ht => ⟨hxr t ht, hpr t ht⟩,
    fun t ht => ⟨hxl t ht, hpl t ht⟩⟩

/-- The transverse motion with energy below `4` stays in the tube, forward in time. -/
theorem transverse_confined (hε : 0 < ε) {c : ℝ} {w pw : ℝ → ℝ}
    (hw : ∀ t, 0 ≤ t → HasDerivWithinAt w (pw t) (Ici 0) t ∧
      HasDerivWithinAt pw (-deriv (fun s => wellPot ε (s - c)) (w t)) (Ici 0) t)
    (hE : pw 0 ^ 2 / 2 + wellPot ε (w 0 - c) < 4) : ∀ t, 0 ≤ t → |w t - c| < 2 * ε := by
  intro t ht
  have hΦc : ∀ {n : ℕ∞}, ContDiff ℝ n (fun s => wellPot ε (s - c)) :=
    (contDiff_wellPot ε).comp (contDiff_id.sub contDiff_const)
  have hS : ∀ z ∈ {z : ℝ | 2 * ε ≤ |z - c|}, (4 : ℝ) ≤ (fun s => wellPot ε (s - c)) z := by
    intro z hz
    exact (wellPot_of_two_le_abs hε hz).ge
  have hnot := not_mem_of_energy_lt (hΦc (n := 1)) hS
    (fun s hs => (hw s hs.1).1.mono Icc_subset_Ici_self)
    (fun s hs => (hw s hs.1).2.mono Icc_subset_Ici_self) (by rw [energy1D]; exact hE) t
    ⟨ht, le_rfl⟩
  by_contra hcon
  exact hnot (not_lt.mp hcon)

/-- **Existence of trajectories of `H_ε` for all real times** from every state in the tube of a
corridor with energy below the wall height `4`. -/
theorem exists_resolvedFlowLine (hε : 0 < ε) (hεs : ε ≤ 1 / 8) (i : Fin (RoutingLaw.compCount F))
    (y₀ q₀ : ℝ × ℝ) (htube : |y₀.2 - compRow F i| < 2 * ε)
    (hE : hamEnergy (resolvedPot F ε) y₀ q₀ < 4) :
    ∃ x p : ℝ → ℝ × ℝ, x 0 = y₀ ∧ p 0 = q₀ ∧ IsHamiltonianFlowLine (resolvedPot F ε) x p := by
  obtain ⟨Ru, hRu0, hRu⟩ := exists_bound_deriv_resolvedCap F hε i
  obtain ⟨u, pu, hu0, hpu0, hu, -⟩ :=
    exists_newton1D_real (contDiff_resolvedCap F ε i (n := 2)) hRu0 hRu y₀.1 q₀.1
  set Φw : ℝ → ℝ := fun s => wellPot ε (s - compRow F i) with hΦw
  have hΦwc : ∀ {n : ℕ∞}, ContDiff ℝ n Φw :=
    (contDiff_wellPot ε).comp (contDiff_id.sub contDiff_const)
  have hderivΦw : ∀ s, deriv Φw s = deriv (wellPot ε) (s - compRow F i) := fun s =>
    deriv_comp_sub_const (f := wellPot ε) (a := compRow F i) s
  obtain ⟨Rw, hRw0, hRw⟩ := exists_bound_deriv_wellPot hε
  obtain ⟨w, pw, hw0, hpw0, hw, w₁, pw₁, w₂, pw₂, hw₁0, hpw₁0, hw₂0, hpw₂0, hw₁, hw₂, hr, hl⟩ :=
    exists_newton1D_real (hΦwc (n := 2)) hRw0 (fun s => by rw [hderivΦw]; exact hRw _) y₀.2 q₀.2
  have hEw : q₀.2 ^ 2 / 2 + wellPot ε (y₀.2 - compRow F i) < 4 := by
    have hpot := resolvedPot_of_tube F hε hεs i (u := y₀.1) htube.le
    have := resolvedCap_nonneg F ε i y₀.1
    rw [hamEnergy, show y₀ = (y₀.1, y₀.2) from rfl, hpot] at hE
    nlinarith [sq_nonneg q₀.1]
  have hc1 := transverse_confined hε hw₁ (by rw [hw₁0, hpw₁0]; exact hEw)
  have hc2 := transverse_confined hε hw₂ (by rw [hw₂0, hpw₂0, neg_sq]; exact hEw)
  have hconf : ∀ t, |w t - compRow F i| < 2 * ε := by
    intro t
    rcases le_total 0 t with ht | ht
    · rw [(hr t ht).1]; exact hc1 t ht
    · rw [(hl t ht).1]; exact hc2 (-t) (by linarith)
  refine ⟨fun t => (u t, w t), fun t => (pu t, pw t), Prod.ext hu0 hw0, Prod.ext hpu0 hpw0,
    fun t => ⟨(hu t).1.prodMk (hw t).1, ?_⟩⟩
  rw [gradForce_resolvedPot_of_tube F hε hεs i (y := (u t, w t)) (hconf t)]
  exact (hu t).2.prodMk (hw t).2

end HamiltonianMetricGraphs
