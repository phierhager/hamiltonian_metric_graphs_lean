/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma V.1 (Liouville part): the variational equation of the edge flow.
-/

import HamiltonianMetricGraphs.EdgeDynamics

/-!
# The variational equation of the edge flow

Liouville's theorem is not available in Mathlib, and neither is differentiability of the solution
of an ODE with respect to its initial condition.  This module builds the analytic input for both,
for the concrete mechanical edge field

`X(q,p) = (p, -V'(q))`.

Its Fréchet derivative is the linear map

`DX(q) · (u₁, u₂) = (u₂, -V''(q) u₁)`   (`edgeFieldDeriv`),

whose trace vanishes.  The module provides

* `hasFDerivAt_edgeVectorField`: `X` is Fréchet differentiable with derivative `edgeFieldDeriv`;
* `exists_fderiv_estimate`: the *uniform* first-order Taylor estimate on a compact physical
  momentum box, from uniform continuity of `V''` (this is what makes the Grönwall comparison in
  `EdgeLiouville` give a genuine `o(‖h‖)`);
* `exists_varSolution`: for every initial vector, the linearized (variational) equation along a
  curve has a solution on a short interval `[0, Δ]`, by one application of Picard--Lindelöf — the
  bound `Δ ≤ 1/(3M)` is exactly what makes a single application suffice, with no continuation;
* `wronskian_eq_one`: two solutions of the variational equation with the standard initial
  conditions have Wronskian `1` for all time, because `tr DX = 0`.  This is Liouville's theorem
  for the edge flow in its infinitesimal form.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter Metric
open scoped Topology NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The second derivative of the potential -/

/-- The derivative of the force, i.e. `-V''`. -/
noncomputable def forceDeriv (e : Γ.Edge) (q : ℝ) : ℝ := deriv (V.force e) q

theorem contDiffOn_force (e : Γ.Edge) : ContDiffOn ℝ 1 (V.force e) (V.domain e) := by
  have h : ContDiffOn ℝ 1 (deriv (V.extension e)) (V.domain e) :=
    (V.contDiffOn_extension e).deriv_of_isOpen (V.domain_isOpen e) (by norm_num)
  exact h.neg

theorem contDiffAt_force {e : Γ.Edge} {q : ℝ} (hq : q ∈ V.domain e) :
    ContDiffAt ℝ 1 (V.force e) q :=
  (V.contDiffOn_force e).contDiffAt ((V.domain_isOpen e).mem_nhds hq)

theorem hasDerivAt_force {e : Γ.Edge} {q : ℝ} (hq : q ∈ V.domain e) :
    HasDerivAt (V.force e) (V.forceDeriv e q) q :=
  ((V.contDiffAt_force hq).differentiableAt (by norm_num)).hasDerivAt

theorem continuousOn_forceDeriv (e : Γ.Edge) : ContinuousOn (V.forceDeriv e) (V.domain e) := by
  have h : ContinuousOn (deriv (V.force e)) (V.domain e) :=
    (V.contDiffOn_force e).continuousOn_deriv_of_isOpen (V.domain_isOpen e) le_rfl
  exact h

theorem continuousOn_forceDeriv_closedEdge (e : Γ.Edge) :
    ContinuousOn (V.forceDeriv e) (Icc (0 : ℝ) (Γ.length e)) :=
  (V.continuousOn_forceDeriv e).mono (V.closedEdge_subset_domain e)

/-! ### The linearized edge field -/

/-- The Fréchet derivative of the edge vector field: `(u₁, u₂) ↦ (u₂, -V''(q) u₁)`. -/
noncomputable def edgeFieldDeriv (e : Γ.Edge) (q : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((V.forceDeriv e q) • (ContinuousLinearMap.fst ℝ ℝ ℝ))

@[simp] theorem edgeFieldDeriv_apply (e : Γ.Edge) (q : ℝ) (u : ℝ × ℝ) :
    V.edgeFieldDeriv e q u = (u.2, V.forceDeriv e q * u.1) := rfl

/-- **The edge vector field is Fréchet differentiable**, with derivative `edgeFieldDeriv`. -/
theorem hasFDerivAt_edgeVectorField {e : Γ.Edge} {x : ℝ × ℝ} (hx : x.1 ∈ V.domain e) :
    HasFDerivAt (V.edgeVectorField e) (V.edgeFieldDeriv e x.1) x := by
  have h2 : HasFDerivAt (fun y : ℝ × ℝ => y.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    hasFDerivAt_snd
  have hfst : HasFDerivAt (fun y : ℝ × ℝ => y.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    hasFDerivAt_fst
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => V.force e y.1)
      ((V.forceDeriv e x.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) x :=
    (V.hasDerivAt_force hx).comp_hasFDerivAt x hfst
  exact h2.prodMk h1

/-- The operator norm of the linearized field is controlled by `|V''|`. -/
theorem norm_edgeFieldDeriv_le (e : Γ.Edge) (q : ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hq : |V.forceDeriv e q| ≤ C) : ‖V.edgeFieldDeriv e q‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun u => ?_)
  rw [edgeFieldDeriv_apply, norm_prod_le_iff]
  have hu1 : |u.1| ≤ ‖u‖ := by
    rw [Prod.norm_def]; exact le_max_left _ _
  have hu2 : |u.2| ≤ ‖u‖ := by
    rw [Prod.norm_def]; exact le_max_right _ _
  have hn : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  refine ⟨?_, ?_⟩
  · rw [Real.norm_eq_abs]
    calc |u.2| ≤ ‖u‖ := hu2
      _ ≤ C * ‖u‖ := by nlinarith
  · rw [Real.norm_eq_abs, abs_mul]
    calc |V.forceDeriv e q| * |u.1| ≤ C * ‖u‖ := by
          apply mul_le_mul hq hu1 (abs_nonneg _) (by linarith)
      _ = C * ‖u‖ := rfl

/-- The linearized field varies with `q` only through `V''`. -/
theorem norm_edgeFieldDeriv_sub_le (e : Γ.Edge) (q q' : ℝ) :
    ‖V.edgeFieldDeriv e q - V.edgeFieldDeriv e q'‖ ≤ |V.forceDeriv e q - V.forceDeriv e q'| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _) (fun u => ?_)
  have hval : (V.edgeFieldDeriv e q - V.edgeFieldDeriv e q') u =
      (0, (V.forceDeriv e q - V.forceDeriv e q') * u.1) := by
    rw [sub_apply, edgeFieldDeriv_apply, edgeFieldDeriv_apply]
    refine Prod.ext ?_ ?_
    · change u.2 - u.2 = 0
      ring
    · change V.forceDeriv e q * u.1 - V.forceDeriv e q' * u.1 = _
      ring
  rw [hval, norm_prod_le_iff]
  have hu1 : |u.1| ≤ ‖u‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  refine ⟨by simp [mul_nonneg, abs_nonneg, norm_nonneg], ?_⟩
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hu1 (abs_nonneg _)

/-- A uniform bound for `|V''|`, hence for the linearized field, on a physical edge. -/
theorem exists_bound_forceDeriv_closedEdge (e : Γ.Edge) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.forceDeriv e q| ≤ C := by
  have hc : IsCompact ((V.forceDeriv e) '' Icc (0 : ℝ) (Γ.length e)) :=
    isCompact_Icc.image_of_continuousOn (V.continuousOn_forceDeriv_closedEdge e)
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall 0
  refine ⟨max 1 R, le_max_left _ _, fun q hq => ?_⟩
  have := hR ⟨q, hq, rfl⟩
  rw [mem_closedBall, Real.dist_eq, sub_zero] at this
  exact this.trans (le_max_right _ _)

/-- **The uniform first-order Taylor estimate.**  On a compact physical momentum box, the edge
vector field is approximated by its derivative with a *uniform* error: for every `ε > 0` there is
a `δ > 0` such that nearby points of the box satisfy the first-order estimate with constant `ε`.
Uniform continuity of `V''` on the compact closed edge is what makes `δ` independent of the
base point, and hence makes the Grönwall comparison below give a genuine `o(‖h‖)`. -/
theorem exists_fderiv_estimate (e : Γ.Edge) (P : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ x ∈ closedEdgeMomentumBox e P, ∀ y ∈ closedEdgeMomentumBox e P,
      ‖y - x‖ ≤ δ →
        ‖V.edgeVectorField e y - V.edgeVectorField e x -
          V.edgeFieldDeriv e x.1 (y - x)‖ ≤ ε * ‖y - x‖ := by
  -- uniform continuity of `V''` on the compact closed edge
  have huc : UniformContinuousOn (V.forceDeriv e) (Icc (0 : ℝ) (Γ.length e)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (V.continuousOn_forceDeriv_closedEdge e)
  obtain ⟨δ, hδ, hδle⟩ := (Metric.uniformContinuousOn_iff_le.mp huc) ε hε
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  -- work on the convex piece of the box within distance `δ` of `x`
  set s : Set (ℝ × ℝ) := closedEdgeMomentumBox e P ∩ closedBall x δ with hs
  have hconv : Convex ℝ s := by
    refine Convex.inter ?_ (convex_closedBall x δ)
    exact (convex_Icc (0 : ℝ) (Γ.length e)).prod (convex_Icc (-P) P)
  have hxs : x ∈ s := ⟨hx, mem_closedBall_self hδ.le⟩
  have hys : y ∈ s := ⟨hy, by rw [mem_closedBall, dist_eq_norm]; exact hxy⟩
  have hderiv : ∀ z ∈ s, HasFDerivWithinAt (V.edgeVectorField e) (V.edgeFieldDeriv e z.1) s z :=
    fun z hz => (V.hasFDerivAt_edgeVectorField
      (V.closedEdge_subset_domain e hz.1.1)).hasFDerivWithinAt
  have hbound : ∀ z ∈ s, ‖V.edgeFieldDeriv e z.1 - V.edgeFieldDeriv e x.1‖ ≤ ε := by
    intro z hz
    refine (V.norm_edgeFieldDeriv_sub_le e z.1 x.1).trans ?_
    have hdist : dist z.1 x.1 ≤ δ := by
      have h := hz.2
      rw [mem_closedBall, dist_eq_norm, Prod.norm_def] at h
      calc dist z.1 x.1 = |z.1 - x.1| := Real.dist_eq _ _
        _ ≤ max ‖z.1 - x.1‖ ‖z.2 - x.2‖ := le_max_left _ _
        _ ≤ δ := h
    have := hδle z.1 hz.1.1 x.1 hx.1 hdist
    rwa [Real.dist_eq] at this
  have hmvt := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le' hderiv hbound hxs hys
  exact hmvt

/-! ### Solutions of the variational equation -/

/-- The variational (linearized) field along a curve `γ`. -/
noncomputable def varField (e : Γ.Edge) (γ : ℝ → ℝ × ℝ) : ℝ → (ℝ × ℝ) → (ℝ × ℝ) :=
  fun t u => V.edgeFieldDeriv e (γ t).1 u

@[simp] theorem varField_apply (e : Γ.Edge) (γ : ℝ → ℝ × ℝ) (t : ℝ) (u : ℝ × ℝ) :
    V.varField e γ t u = V.edgeFieldDeriv e (γ t).1 u := rfl

/-- **Short-time solvability of the variational equation.**  Along a curve `γ` whose linearized
field is bounded by `M` and continuous in time, the variational equation has a solution on
`[0, Δ]` for every initial vector, provided `Δ ≤ 1/(3M)`.  One application of Picard--Lindelöf
suffices: the required radius grows proportionally with the initial vector, so the admissible time
step is independent of it — this is the standard reason why *linear* ODEs need no continuation
argument. -/
theorem exists_varSolution (e : Γ.Edge) (γ : ℝ → ℝ × ℝ) {Δ : ℝ} (hΔ : 0 ≤ Δ) {M : ℝ≥0}
    (hM1 : (1 : ℝ) ≤ M) (hMbound : ∀ t ∈ Icc (0 : ℝ) Δ, ‖V.edgeFieldDeriv e (γ t).1‖ ≤ M)
    (hcont : ContinuousOn (fun t => V.forceDeriv e (γ t).1) (Icc (0 : ℝ) Δ))
    (hΔM : Δ ≤ 1 / (3 * M)) (u₀ : ℝ × ℝ) :
    ∃ Y : ℝ → ℝ × ℝ, Y 0 = u₀ ∧ ∀ t ∈ Icc (0 : ℝ) Δ,
      HasDerivWithinAt Y (V.edgeFieldDeriv e (γ t).1 (Y t)) (Icc (0 : ℝ) Δ) t := by
  have hMpos : (0 : ℝ) < M := by linarith
  set a : ℝ≥0 := 2 * ‖u₀‖₊ + 2 with ha
  set r : ℝ≥0 := ‖u₀‖₊ + 1 with hr
  set L : ℝ≥0 := M * (3 * ‖u₀‖₊ + 2) with hL
  have hu₀ : (‖u₀‖₊ : ℝ) = ‖u₀‖ := rfl
  have hsub : a - r = r := by
    rw [ha, hr]
    rw [show (2 : ℝ≥0) * ‖u₀‖₊ + 2 = (‖u₀‖₊ + 1) + (‖u₀‖₊ + 1) by ring]
    exact add_tsub_cancel_left _ _
  have ht₀ : (0 : ℝ) ∈ Icc (0 : ℝ) Δ := ⟨le_rfl, hΔ⟩
  have hPL : IsPicardLindelof (V.varField e γ) (⟨0, ht₀⟩ : Icc (0 : ℝ) Δ) u₀ a r L M := by
    refine ⟨fun t ht => ?_, fun u hu => ?_, fun t ht u hu => ?_, ?_⟩
    · -- the linearized field is `M`-Lipschitz, being linear of norm at most `M`
      refine LipschitzOnWith.of_dist_le_mul (fun u _ v _ => ?_)
      rw [dist_eq_norm, dist_eq_norm]
      simp only [varField_apply]
      rw [← map_sub]
      calc ‖V.edgeFieldDeriv e (γ t).1 (u - v)‖
          ≤ ‖V.edgeFieldDeriv e (γ t).1‖ * ‖u - v‖ :=
            (V.edgeFieldDeriv e (γ t).1).le_opNorm (u - v)
        _ ≤ (M : ℝ) * ‖u - v‖ :=
            mul_le_mul_of_nonneg_right (hMbound t ht) (norm_nonneg _)
    · -- continuity in time
      have hmap : (fun t => V.varField e γ t u) =
          fun t => (u.2, V.forceDeriv e (γ t).1 * u.1) := by
        funext t; rfl
      rw [hmap]
      exact continuousOn_const.prodMk (hcont.mul continuousOn_const)
    · -- the norm bound on the ball
      have hnorm : ‖u‖ ≤ ‖u₀‖ + a := by
        have h := hu
        rw [mem_closedBall, dist_eq_norm] at h
        calc ‖u‖ = ‖u₀ + (u - u₀)‖ := by rw [add_sub_cancel]
          _ ≤ ‖u₀‖ + ‖u - u₀‖ := norm_add_le _ _
          _ ≤ ‖u₀‖ + a := by linarith
      have hop := (V.edgeFieldDeriv e (γ t).1).le_opNorm u
      have hM := hMbound t ht
      have hnn : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
      have hLval : (L : ℝ) = M * (3 * ‖u₀‖ + 2) := by
        rw [hL]; push_cast; ring
      have haval : (a : ℝ) = 2 * ‖u₀‖ + 2 := by rw [ha]; push_cast; ring
      rw [varField_apply, hLval]
      calc ‖V.edgeFieldDeriv e (γ t).1 u‖ ≤ ‖V.edgeFieldDeriv e (γ t).1‖ * ‖u‖ := hop
        _ ≤ M * (‖u₀‖ + a) := by
              apply mul_le_mul hM hnorm hnn (le_trans zero_le_one hM1)
        _ = M * (3 * ‖u₀‖ + 2) := by rw [haval]; ring
    · -- the time constraint
      have hmaxval : max (Δ - ((⟨0, ht₀⟩ : Icc (0 : ℝ) Δ) : ℝ))
          (((⟨0, ht₀⟩ : Icc (0 : ℝ) Δ) : ℝ) - 0) = Δ := by
        change max (Δ - 0) ((0 : ℝ) - 0) = Δ
        rw [sub_zero, sub_self, max_eq_left hΔ]
      rw [hmaxval]
      have hLval : (L : ℝ) = M * (3 * ‖u₀‖ + 2) := by rw [hL]; push_cast; ring
      have haval : (a : ℝ) = 2 * ‖u₀‖ + 2 := by rw [ha]; push_cast; ring
      have hrval : (r : ℝ) = ‖u₀‖ + 1 := by rw [hr]; push_cast; ring
      rw [hLval, haval, hrval]
      have hn : (0 : ℝ) ≤ ‖u₀‖ := norm_nonneg u₀
      have h0 : (0 : ℝ) < 3 * M := by linarith
      have h3 : Δ * (3 * (M : ℝ)) ≤ 1 := (le_div_iff₀ h0).mp hΔM
      nlinarith [hΔ, hn, hM1, h3]
  obtain ⟨α, hα0, hαderiv⟩ :=
    hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt (mem_closedBall_self (by positivity))
  exact ⟨α, hα0, hαderiv⟩

/-! ### Component derivatives -/

theorem hasDerivWithinAt_fst_of_prod {f : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f d s t) : HasDerivWithinAt (fun r => (f r).1) d.1 s t :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t h

theorem hasDerivWithinAt_snd_of_prod {f : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f d s t) : HasDerivWithinAt (fun r => (f r).2) d.2 s t :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t h

/-! ### The Wronskian -/

/-- The Wronskian of two curves in the phase plane. -/
def wronskian (Y₁ Y₂ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ := (Y₁ t).1 * (Y₂ t).2 - (Y₂ t).1 * (Y₁ t).2

/-- **Liouville's theorem in infinitesimal form.**  The Wronskian of two solutions of the
variational equation is constant, because the linearized edge field is trace free:
`DX(q) = [[0, 1], [-V''(q), 0]]`. -/
theorem wronskian_hasDerivWithinAt_zero {e : Γ.Edge} {γ Y₁ Y₂ : ℝ → ℝ × ℝ} {Δ t : ℝ}
    (h₁ : HasDerivWithinAt Y₁ (V.edgeFieldDeriv e (γ t).1 (Y₁ t)) (Icc (0 : ℝ) Δ) t)
    (h₂ : HasDerivWithinAt Y₂ (V.edgeFieldDeriv e (γ t).1 (Y₂ t)) (Icc (0 : ℝ) Δ) t) :
    HasDerivWithinAt (wronskian Y₁ Y₂) 0 (Icc (0 : ℝ) Δ) t := by
  set c : ℝ := V.forceDeriv e (γ t).1 with hc
  have h₁₁ : HasDerivWithinAt (fun s => (Y₁ s).1) (Y₁ t).2 (Icc (0 : ℝ) Δ) t := by
    have := hasDerivWithinAt_fst_of_prod h₁
    simpa using this
  have h₁₂ : HasDerivWithinAt (fun s => (Y₁ s).2) (c * (Y₁ t).1) (Icc (0 : ℝ) Δ) t := by
    have := hasDerivWithinAt_snd_of_prod h₁
    simpa using this
  have h₂₁ : HasDerivWithinAt (fun s => (Y₂ s).1) (Y₂ t).2 (Icc (0 : ℝ) Δ) t := by
    have := hasDerivWithinAt_fst_of_prod h₂
    simpa using this
  have h₂₂ : HasDerivWithinAt (fun s => (Y₂ s).2) (c * (Y₂ t).1) (Icc (0 : ℝ) Δ) t := by
    have := hasDerivWithinAt_snd_of_prod h₂
    simpa using this
  have hd := (h₁₁.mul h₂₂).sub (h₂₁.mul h₁₂)
  have hzero : (Y₁ t).2 * (Y₂ t).2 + (Y₁ t).1 * (c * (Y₂ t).1) -
      ((Y₂ t).2 * (Y₁ t).2 + (Y₂ t).1 * (c * (Y₁ t).1)) = 0 := by ring
  rw [hzero] at hd
  exact hd

/-- The Wronskian of two solutions of the variational equation is constant on `[0, Δ]`. -/
theorem wronskian_eq_of_varSolution {e : Γ.Edge} {γ Y₁ Y₂ : ℝ → ℝ × ℝ} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) Δ,
      HasDerivWithinAt Y₁ (V.edgeFieldDeriv e (γ t).1 (Y₁ t)) (Icc (0 : ℝ) Δ) t)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) Δ,
      HasDerivWithinAt Y₂ (V.edgeFieldDeriv e (γ t).1 (Y₂ t)) (Icc (0 : ℝ) Δ) t) :
    ∀ t ∈ Icc (0 : ℝ) Δ, wronskian Y₁ Y₂ t = wronskian Y₁ Y₂ 0 := by
  intro t ht
  rcases eq_or_lt_of_le hΔ with h0 | h0
  · have hteq : t = 0 := by
      have := ht.2; rw [← h0] at this; linarith [ht.1]
    rw [hteq]
  · have hall : ∀ s ∈ Icc (0 : ℝ) Δ,
        HasDerivWithinAt (wronskian Y₁ Y₂) 0 (Icc (0 : ℝ) Δ) s :=
      fun s hs => V.wronskian_hasDerivWithinAt_zero (h₁ s hs) (h₂ s hs)
    have hdiff : DifferentiableOn ℝ (wronskian Y₁ Y₂) (Icc (0 : ℝ) Δ) :=
      fun s hs => (hall s hs).differentiableWithinAt
    have hconst := constant_of_derivWithin_zero hdiff (fun s hs =>
      (hall s (Ico_subset_Icc_self hs)).derivWithin
        (uniqueDiffOn_Icc h0 s (Ico_subset_Icc_self hs)))
    exact hconst t ht

/-- **The Wronskian is `1`**: the two solutions with the standard initial vectors `(1,0)`, `(0,1)`
span a parallelogram of unit area at every time.  This is the determinant identity that makes the
edge flow measure preserving. -/
theorem wronskian_eq_one {e : Γ.Edge} {γ Y₁ Y₂ : ℝ → ℝ × ℝ} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hY₁ : Y₁ 0 = (1, 0)) (hY₂ : Y₂ 0 = (0, 1))
    (h₁ : ∀ t ∈ Icc (0 : ℝ) Δ,
      HasDerivWithinAt Y₁ (V.edgeFieldDeriv e (γ t).1 (Y₁ t)) (Icc (0 : ℝ) Δ) t)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) Δ,
      HasDerivWithinAt Y₂ (V.edgeFieldDeriv e (γ t).1 (Y₂ t)) (Icc (0 : ℝ) Δ) t) :
    ∀ t ∈ Icc (0 : ℝ) Δ, wronskian Y₁ Y₂ t = 1 := by
  intro t ht
  rw [V.wronskian_eq_of_varSolution hΔ h₁ h₂ t ht, wronskian, hY₁, hY₂]
  norm_num

end MechanicalPotential

end HamiltonianMetricGraphs
