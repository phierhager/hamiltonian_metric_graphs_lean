/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.FlightEstimates

/-!
# Edge approximation: Grönwall closeness of approximate flights

The longitudinal dynamics of a well-prepared thin-tube trajectory is an approximate solution of
the edge Hamiltonian system (tolerance `ρ`).  Grönwall's inequality then shows that it stays
close to the exact graph flight started from nearby data, uniformly before the next junction:

  `dist (f t) (g t) ≤ (δ + (ρf + ρg)(b - a)) · exp (K (b - a))`   for `t ∈ [a, b]`,

where `K` is a Lipschitz constant of the edge vector field `(q, p) ↦ (p, -V'(q))` on the strip
`[0, L] × ℝ`.  The Lipschitz constant exists because the potential is `C²` on an open
neighbourhood of the closed edge.

Mathematical proof step: "edge approximation `(q_ε, p_∥,ε) → (q, p)` uniformly before the next
junction" — here a **theorem** derived from the perturbed-ODE description of the tube dynamics.
-/

namespace HamiltonianMetricGraphs

open Set Filter
open scoped NNReal Topology

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- The physical strip of an edge in phase space: coordinate on the closed edge, any momentum. -/
def edgeStrip (e : Γ.Edge) : Set (ℝ × ℝ) := {x | x.1 ∈ Icc (0 : ℝ) (Γ.length e)}

theorem mem_edgeStrip {e : Γ.Edge} {x : ℝ × ℝ} :
    x ∈ Γ.edgeStrip e ↔ x.1 ∈ Icc (0 : ℝ) (Γ.length e) :=
  Iff.rfl

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- The force `-V'` is Lipschitz on the closed edge: it is `C¹` on an open neighbourhood. -/
theorem exists_lipschitzOnWith_force (e : Γ.Edge) :
    ∃ K : ℝ≥0, LipschitzOnWith K (V.force e) (Icc (0 : ℝ) (Γ.length e)) := by
  have h1 : ContDiffOn ℝ 1 (deriv (V.extension e)) (V.domain e) :=
    (V.contDiffOn_extension e).deriv_of_isOpen (V.domain_isOpen e) (by norm_num)
  have h2 : ContDiffOn ℝ 1 (V.force e) (Icc (0 : ℝ) (Γ.length e)) := by
    unfold force
    exact h1.neg.mono (V.closedEdge_subset_domain e)
  exact h2.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc

/-- The edge vector field is Lipschitz on the physical strip (with the sup metric on `ℝ × ℝ`). -/
theorem exists_lipschitzOnWith_edgeVectorField_strip (e : Γ.Edge) :
    ∃ K : ℝ≥0, LipschitzOnWith K (V.edgeVectorField e) (Γ.edgeStrip e) := by
  obtain ⟨Kf, hKf⟩ := V.exists_lipschitzOnWith_force e
  refine ⟨max 1 Kf, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have h1 : dist x.2 y.2 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h2 : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h3 := hKf.dist_le_mul x.1 hx y.1 hy
  have hcoe : ((max 1 Kf : ℝ≥0) : ℝ) = max 1 (Kf : ℝ) := by
    simp [NNReal.coe_max]
  rw [hcoe]
  change max (dist x.2 y.2) (dist (V.force e x.1) (V.force e y.1)) ≤ _
  apply max_le
  · calc dist x.2 y.2 ≤ dist x y := h1
      _ ≤ max 1 (Kf : ℝ) * dist x y :=
          le_mul_of_one_le_left dist_nonneg (le_max_left _ _)
  · calc dist (V.force e x.1) (V.force e y.1) ≤ Kf * dist x.1 y.1 := h3
      _ ≤ Kf * dist x y := mul_le_mul_of_nonneg_left h2 Kf.coe_nonneg
      _ ≤ max 1 (Kf : ℝ) * dist x y :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg

/-- One Lipschitz constant for all edges of the finite graph. -/
theorem exists_uniform_lipschitz_edgeVectorField :
    ∃ K : ℝ≥0, ∀ e : Γ.Edge, LipschitzOnWith K (V.edgeVectorField e) (Γ.edgeStrip e) := by
  classical
  choose K hK using fun e : Γ.Edge => V.exists_lipschitzOnWith_edgeVectorField_strip e
  exact ⟨Finset.univ.sup K, fun e => (hK e).weaken (Finset.le_sup (Finset.mem_univ e))⟩

/-- The explicit Grönwall bound is dominated by `(δ + ε x) · exp (K x)`. -/
theorem gronwallBound_le_exp {δ K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  by_cases hK0 : K = 0
  · subst hK0
    simp only [gronwallBound_K0, zero_mul, Real.exp_zero, mul_one]
    exact le_rfl
  · have hexp := Real.exp_pos (K * x)
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have h := Real.add_one_le_exp (-(K * x))
      rw [Real.exp_neg] at h
      have h2 := mul_le_mul_of_nonneg_right h hexp.le
      rw [inv_mul_cancel₀ hexp.ne'] at h2
      linarith
    have h3 : ε / K * (Real.exp (K * x) - 1) ≤ ε * x * Real.exp (K * x) := by
      calc ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) :=
            mul_le_mul_of_nonneg_left h1 (div_nonneg hε hK)
        _ = ε * x * Real.exp (K * x) := by field_simp
    simp only [gronwallBound_of_K_ne_0 hK0]
    have hexpand : (δ + ε * x) * Real.exp (K * x) =
        δ * Real.exp (K * x) + ε * x * Real.exp (K * x) := by ring
    rw [hexpand]
    linarith

namespace IsFlight

variable {V}

/-- **Edge approximation (Grönwall).**  Two approximate flights on the same edge over the same
time interval, with tolerances `ρf`, `ρg` and initial distance `≤ δ`, stay within the Grönwall
bound of each other. -/
theorem dist_le_gronwallBound {e : Γ.Edge} {K : ℝ≥0}
    (hK : LipschitzOnWith K (V.edgeVectorField e) (Γ.edgeStrip e))
    {of ρf og ρg a b : ℝ} {f wf g wg : ℝ → ℝ × ℝ}
    (hf : V.IsFlight e of ρf a b f wf) (hg : V.IsFlight e og ρg a b g wg)
    (hof : 0 ≤ of) (hog : 0 ≤ og) {δ : ℝ} (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwallBound δ K (ρf + ρg) (t - a) :=
  dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => V.edgeVectorField e)
    (s := fun _ => Γ.edgeStrip e) (fun _ _ => hK) hf.continuousOn
    (fun _ ht => hasDerivWithinAt_Ici_of_Icc ht (hf.hasDerivWithinAt (Ico_subset_Icc_self ht)))
    (fun t ht => (hf.ode t (Ico_subset_Icc_self ht)).1)
    (fun _ ht => hf.physical hof (Ico_subset_Icc_self ht))
    hg.continuousOn
    (fun _ ht => hasDerivWithinAt_Ici_of_Icc ht (hg.hasDerivWithinAt (Ico_subset_Icc_self ht)))
    (fun t ht => (hg.ode t (Ico_subset_Icc_self ht)).1)
    (fun _ ht => hg.physical hog (Ico_subset_Icc_self ht))
    ha

/-- The edge approximation in explicit form: the distance is at most
`(δ + (ρf + ρg)(b - a)) · exp (K (b - a))` on the whole interval. -/
theorem dist_le_closeness {e : Γ.Edge} {K : ℝ≥0}
    (hK : LipschitzOnWith K (V.edgeVectorField e) (Γ.edgeStrip e))
    {of ρf og ρg a b : ℝ} {f wf g wg : ℝ → ℝ × ℝ}
    (hf : V.IsFlight e of ρf a b f wf) (hg : V.IsFlight e og ρg a b g wg)
    (hof : 0 ≤ of) (hog : 0 ≤ og) (hρf : 0 ≤ ρf) (hρg : 0 ≤ ρg) (hab : a ≤ b)
    {δ : ℝ} (hδ : 0 ≤ δ) (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b,
      dist (f t) (g t) ≤ (δ + (ρf + ρg) * (b - a)) * Real.exp (K * (b - a)) := by
  intro t ht
  have h1 := hf.dist_le_gronwallBound hK hg hof hog ha t ht
  have h2 := gronwallBound_le_exp (δ := δ) (K := (K : ℝ)) (ε := ρf + ρg) (x := t - a)
    K.coe_nonneg (by linarith)
  have h3 : (δ + (ρf + ρg) * (t - a)) * Real.exp (K * (t - a)) ≤
      (δ + (ρf + ρg) * (b - a)) * Real.exp (K * (b - a)) := by
    apply mul_le_mul
    · have : (ρf + ρg) * (t - a) ≤ (ρf + ρg) * (b - a) :=
        mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by linarith)
      linarith
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2]) K.coe_nonneg)
    · exact (Real.exp_pos _).le
    · have : 0 ≤ (ρf + ρg) * (b - a) := mul_nonneg (by linarith) (by linarith)
      linarith
  exact h1.trans (h2.trans h3)

end IsFlight

end MechanicalPotential
end HamiltonianMetricGraphs
