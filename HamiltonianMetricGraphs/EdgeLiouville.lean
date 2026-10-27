/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma V.1 (Liouville part): the edge flow preserves `dq dp`.
-/

import HamiltonianMetricGraphs.EdgeVariational

/-!
# Liouville invariance of the edge flow

This module proves the Liouville part of Lemma V.1: **the edge Hamiltonian flow preserves the
measure `dq dp`**.  Mathlib has neither Liouville's theorem nor differentiability of ODE solutions
with respect to their initial condition, so both are established here for the concrete mechanical
edge field.

The argument is the classical one.

* `edgeFlowMap_hasFDerivWithinAt`: the time-`Δ` map is Fréchet differentiable in the initial
  condition, with derivative the solution operator of the variational equation.  The proof is a
  Grönwall comparison of
  `z(t) = φ_t(x) - φ_t(x₀) - Y(t)(x - x₀)`,
  which satisfies `‖z'‖ ≤ M‖z‖ + ε·C‖x - x₀‖` and `z(0) = 0`, where the `ε` comes from the
  *uniform* first-order estimate `exists_fderiv_estimate` and `C` from the Lipschitz dependence
  `dist_le_of_trajectories_ODE_of_mem`.  Letting `ε → 0` gives a genuine `o(‖x - x₀‖)`.
* the determinant of that derivative is the Wronskian of the variational equation, which is `1`
  because the linearized field is trace free (`wronskian_eq_one`).
* `injOn_edgeFlowMap`: the time-`Δ` map is injective, by backward ODE uniqueness.
* `measure_image_edgeFlowMap`: hence, by the change-of-variables formula
  `lintegral_abs_det_fderiv_eq_addHaar_image`, it preserves two-dimensional Lebesgue measure.

The statement is deliberately phrased for an *abstract family of solutions* `F : (ℝ × ℝ) → ℝ →
ℝ × ℝ` confined to a compact physical momentum box: this is exactly what the flight machinery
provides on a no-impact set, and it keeps the analysis independent of the impact bookkeeping.
Only a short time `Δ ≤ 1/(3M)` is needed, which is all the global theory uses (the flow is
composed from finitely many short steps).
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter Metric MeasureTheory Asymptotics
open scoped Topology NNReal ENNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### Germ conversions for one-sided derivatives -/

theorem hasDerivWithinAt_Ici_of_mem_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {d : E} {a b t : ℝ} (ht : t ∈ Ico a b)
    (h : HasDerivWithinAt f d (Icc a b) t) : HasDerivWithinAt f d (Ici t) t := by
  have hmono : HasDerivWithinAt f d (Icc t b) t := h.mono (Icc_subset_Icc ht.1 le_rfl)
  refine hmono.congr_set ?_
  filter_upwards [Iio_mem_nhds ht.2] with y hy
  simp only [mem_Icc, mem_Ici, eq_iff_iff]
  exact ⟨fun hz => hz.1, fun hz => ⟨hz, le_of_lt hy⟩⟩

theorem hasDerivWithinAt_Iic_of_mem_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {d : E} {a b t : ℝ} (ht : t ∈ Ioc a b)
    (h : HasDerivWithinAt f d (Icc a b) t) : HasDerivWithinAt f d (Iic t) t := by
  have hmono : HasDerivWithinAt f d (Icc a t) t := h.mono (Icc_subset_Icc le_rfl ht.2)
  refine hmono.congr_set ?_
  filter_upwards [Ioi_mem_nhds ht.1] with y hy
  simp only [mem_Icc, mem_Iic, eq_iff_iff]
  exact ⟨fun hz => hz.2, fun hz => ⟨le_of_lt hy, hz⟩⟩

/-! ### The pair map and its determinant -/

/-- The linear map determined by the images of the two standard basis vectors of `ℝ × ℝ`. -/
noncomputable def pairMap (a b : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight a + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight b

@[simp] theorem pairMap_apply (a b u : ℝ × ℝ) : pairMap a b u = u.1 • a + u.2 • b := rfl

/-- The determinant of the pair map is the `2 × 2` determinant of its columns. -/
theorem pairMap_det (a b : ℝ × ℝ) : (pairMap a b).det = a.1 * b.2 - b.1 * a.2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, pairMap]

/-! ### The hypotheses: a confined family of edge solutions -/

/-- **A confined family of edge solutions.**  For every initial point `x` of `s`, `F x` is a
solution of the edge Hamiltonian system on `[0, Δ]` starting at `x` and staying in the compact
physical momentum box.  This is exactly the data a no-impact set of the scattered flow provides.
-/
structure EdgeSolutionFamily (V : MechanicalPotential Γ) (e : Γ.Edge) (P Δ : ℝ)
    (s : Set (ℝ × ℝ)) (F : (ℝ × ℝ) → ℝ → ℝ × ℝ) : Prop where
  initial : ∀ x ∈ s, F x 0 = x
  ode : ∀ x ∈ s, ∀ t ∈ Icc (0 : ℝ) Δ,
    HasDerivWithinAt (F x) (V.edgeVectorField e (F x t)) (Icc (0 : ℝ) Δ) t
  confined : ∀ x ∈ s, ∀ t ∈ Icc (0 : ℝ) Δ, F x t ∈ closedEdgeMomentumBox e P

namespace EdgeSolutionFamily

variable {V} {e : Γ.Edge} {P Δ : ℝ} {s : Set (ℝ × ℝ)} {F : (ℝ × ℝ) → ℝ → ℝ × ℝ}
  (hF : EdgeSolutionFamily V e P Δ s F)

include hF

theorem continuousOn (hΔ : 0 ≤ Δ) {x : ℝ × ℝ} (hx : x ∈ s) :
    ContinuousOn (F x) (Icc (0 : ℝ) Δ) :=
  fun t ht => (hF.ode x hx t ht).continuousWithinAt

theorem mem_box (hΔ : 0 ≤ Δ) {x : ℝ × ℝ} (hx : x ∈ s) : x ∈ closedEdgeMomentumBox e P := by
  have := hF.confined x hx 0 ⟨le_rfl, hΔ⟩
  rwa [hF.initial x hx] at this

/-- **Backward uniqueness**: two members of the family that agree at time `Δ` agree throughout, in
particular at time `0`.  Hence the time-`Δ` map is injective. -/
theorem injOn_apply (hΔ : 0 < Δ) : InjOn (fun x => F x Δ) s := by
  intro x hx y hy hxy
  obtain ⟨K, hK⟩ := V.exists_lipschitzOnWith_edgeVectorField_closedMomentumBox e P
  have heq : EqOn (F x) (F y) (Icc (0 : ℝ) Δ) := by
    refine ODE_solution_unique_of_mem_Icc_left (v := fun _ => V.edgeVectorField e)
      (s := fun _ => closedEdgeMomentumBox e P) (K := K) (a := 0) (b := Δ)
      (fun _ _ => hK) (hF.continuousOn hΔ.le hx) ?_ ?_
      (hF.continuousOn hΔ.le hy) ?_ ?_ hxy
    · exact fun t ht => hasDerivWithinAt_Iic_of_mem_Icc ht
        (hF.ode x hx t (Ioc_subset_Icc_self ht))
    · exact fun t ht => hF.confined x hx t (Ioc_subset_Icc_self ht)
    · exact fun t ht => hasDerivWithinAt_Iic_of_mem_Icc ht
        (hF.ode y hy t (Ioc_subset_Icc_self ht))
    · exact fun t ht => hF.confined y hy t (Ioc_subset_Icc_self ht)
  have h0 := heq ⟨le_rfl, hΔ.le⟩
  rwa [hF.initial x hx, hF.initial y hy] at h0

/-- **Lipschitz dependence on the initial condition** (Grönwall).  Two members of the family
separate at most exponentially fast. -/
theorem dist_le (hΔ : 0 ≤ Δ) {K : ℝ≥0}
    (hK : LipschitzOnWith K (V.edgeVectorField e) (closedEdgeMomentumBox e P))
    {x y : ℝ × ℝ} (hx : x ∈ s) (hy : y ∈ s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Δ) :
    dist (F x t) (F y t) ≤ dist x y * Real.exp (K * t) := by
  have h := dist_le_of_trajectories_ODE_of_mem (v := fun _ => V.edgeVectorField e)
    (s := fun _ => closedEdgeMomentumBox e P) (K := K) (a := 0) (b := Δ)
    (f := F x) (g := F y) (δ := dist x y)
    (fun _ _ => hK) (hF.continuousOn hΔ hx)
    (fun u hu => hasDerivWithinAt_Ici_of_mem_Icc hu (hF.ode x hx u (Ico_subset_Icc_self hu)))
    (fun u hu => hF.confined x hx u (Ico_subset_Icc_self hu))
    (hF.continuousOn hΔ hy)
    (fun u hu => hasDerivWithinAt_Ici_of_mem_Icc hu (hF.ode y hy u (Ico_subset_Icc_self hu)))
    (fun u hu => hF.confined y hy u (Ico_subset_Icc_self hu))
    (by rw [hF.initial x hx, hF.initial y hy]) t ht
  rwa [sub_zero] at h

end EdgeSolutionFamily

/-! ### Differentiability of the time-`Δ` map -/

section Deriv

variable {e : Γ.Edge} {P Δ : ℝ} {s : Set (ℝ × ℝ)} {F : (ℝ × ℝ) → ℝ → ℝ × ℝ}

/-- The variational solution operator along the orbit of `x₀`, evaluated at time `Δ`. -/
theorem exists_variational_operator (hF : EdgeSolutionFamily V e P Δ s F) (hΔ : 0 ≤ Δ)
    {M : ℝ≥0} (hM1 : (1 : ℝ) ≤ M)
    (hMbound : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), ‖V.edgeFieldDeriv e q‖ ≤ M)
    (hΔM : Δ ≤ 1 / (3 * M)) {x₀ : ℝ × ℝ} (hx₀ : x₀ ∈ s) :
    ∃ Y : ℝ → (ℝ × ℝ) → (ℝ × ℝ),
      (∀ u : ℝ × ℝ, Y 0 u = u) ∧
      (∀ u : ℝ × ℝ, ∀ t ∈ Icc (0 : ℝ) Δ,
        HasDerivWithinAt (fun r => Y r u)
          (V.edgeFieldDeriv e (F x₀ t).1 (Y t u)) (Icc (0 : ℝ) Δ) t) ∧
      (∃ L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), (∀ u, L u = Y Δ u) ∧ L.det = 1) := by
  have hbox : ∀ t ∈ Icc (0 : ℝ) Δ, (F x₀ t).1 ∈ Icc (0 : ℝ) (Γ.length e) :=
    fun t ht => (hF.confined x₀ hx₀ t ht).1
  have hMγ : ∀ t ∈ Icc (0 : ℝ) Δ, ‖V.edgeFieldDeriv e (F x₀ t).1‖ ≤ M :=
    fun t ht => hMbound _ (hbox t ht)
  have hcont : ContinuousOn (fun t => V.forceDeriv e (F x₀ t).1) (Icc (0 : ℝ) Δ) := by
    refine (V.continuousOn_forceDeriv_closedEdge e).comp ?_ hbox
    exact (continuousOn_fst.comp (hF.continuousOn hΔ hx₀) (fun t _ => mem_univ _))
  obtain ⟨Y₁, hY₁0, hY₁⟩ :=
    V.exists_varSolution e (F x₀) hΔ hM1 hMγ hcont hΔM (1, 0)
  obtain ⟨Y₂, hY₂0, hY₂⟩ :=
    V.exists_varSolution e (F x₀) hΔ hM1 hMγ hcont hΔM (0, 1)
  refine ⟨fun t u => pairMap (Y₁ t) (Y₂ t) u, ?_, ?_, ?_⟩
  · intro u
    show pairMap (Y₁ 0) (Y₂ 0) u = u
    rw [pairMap_apply, hY₁0, hY₂0]
    refine Prod.ext ?_ ?_
    · change u.1 * 1 + u.2 * 0 = u.1; ring
    · change u.1 * 0 + u.2 * 1 = u.2; ring
  · intro u t ht
    show HasDerivWithinAt (fun r => pairMap (Y₁ r) (Y₂ r) u) _ _ _
    have h1 := (hY₁ t ht).const_smul u.1
    have h2 := (hY₂ t ht).const_smul u.2
    have hsum := h1.add h2
    have hlin : u.1 • V.edgeFieldDeriv e (F x₀ t).1 (Y₁ t) +
        u.2 • V.edgeFieldDeriv e (F x₀ t).1 (Y₂ t) =
        V.edgeFieldDeriv e (F x₀ t).1 (pairMap (Y₁ t) (Y₂ t) u) := by
      rw [pairMap_apply, map_add, map_smul, map_smul]
    rw [hlin] at hsum
    exact hsum
  · refine ⟨pairMap (Y₁ Δ) (Y₂ Δ), fun u => rfl, ?_⟩
    rw [pairMap_det]
    have hw := V.wronskian_eq_one hΔ hY₁0 hY₂0 hY₁ hY₂ Δ ⟨hΔ, le_rfl⟩
    rw [wronskian] at hw
    exact hw

/-- **The time-`Δ` map is differentiable in the initial condition.**  Its derivative is the
variational solution operator, whose determinant is the Wronskian, hence `1`. -/
theorem hasFDerivWithinAt_of_edgeSolutionFamily (hF : EdgeSolutionFamily V e P Δ s F)
    (hΔ : 0 < Δ) {M : ℝ≥0} (hM1 : (1 : ℝ) ≤ M)
    (hMbound : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), ‖V.edgeFieldDeriv e q‖ ≤ M)
    (hΔM : Δ ≤ 1 / (3 * M)) {x₀ : ℝ × ℝ} (hx₀ : x₀ ∈ s) :
    ∃ L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), L.det = 1 ∧
      HasFDerivWithinAt (fun x => F x Δ) L s x₀ := by
  classical
  obtain ⟨K, hK⟩ := V.exists_lipschitzOnWith_edgeVectorField_closedMomentumBox e P
  obtain ⟨Y, hY0, hYode, L, hLY, hLdet⟩ :=
    V.exists_variational_operator hF hΔ.le hM1 hMbound hΔM hx₀
  refine ⟨L, hLdet, ?_⟩
  -- constants of the Grönwall comparison
  have hMpos : (0 : ℝ) < M := by linarith
  set C : ℝ := Real.exp (K * Δ) with hC
  have hC1 : 1 ≤ C := by
    rw [hC]
    exact Real.one_le_exp (by positivity)
  set G : ℝ := (Real.exp (M * Δ) - 1) / M with hG
  have hG0 : 0 ≤ G := by
    rw [hG]
    apply div_nonneg _ hMpos.le
    have : (1 : ℝ) ≤ Real.exp (M * Δ) := Real.one_le_exp (by positivity)
    linarith
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  -- choose the first-order accuracy
  set ε : ℝ := c / (C * G + 1) with hε
  have hden : 0 < C * G + 1 := by positivity
  have hεpos : 0 < ε := by rw [hε]; positivity
  obtain ⟨δ, hδ, hδest⟩ := V.exists_fderiv_estimate e P hεpos
  -- points this close have orbits within `δ` of the orbit of `x₀`
  set ρ : ℝ := δ / C with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hmem : ball x₀ ρ ∈ 𝓝 x₀ := ball_mem_nhds x₀ hρpos
  filter_upwards [eventually_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds hmem] with x hxs hxball
  -- the Grönwall comparison for `z t = F x t - F x₀ t - Y t (x - x₀)`
  have hhnorm : ‖x - x₀‖ ≤ ρ := by
    rw [← dist_eq_norm]
    exact le_of_lt (mem_ball.mp hxball)
  set z : ℝ → ℝ × ℝ := fun t => F x t - F x₀ t - Y t (x - x₀) with hzdef
  have hzval : ∀ t, z t = F x t - F x₀ t - Y t (x - x₀) := fun _ => rfl
  set zd : ℝ → ℝ × ℝ := fun t => V.edgeVectorField e (F x t) - V.edgeVectorField e (F x₀ t) -
    V.edgeFieldDeriv e (F x₀ t).1 (Y t (x - x₀)) with hzddef
  have hzdval : ∀ t, zd t = V.edgeVectorField e (F x t) - V.edgeVectorField e (F x₀ t) -
      V.edgeFieldDeriv e (F x₀ t).1 (Y t (x - x₀)) := fun _ => rfl
  have hz0 : z 0 = 0 := by
    rw [hzval, hF.initial x hxs, hF.initial x₀ hx₀, hY0]
    abel
  -- the trajectories stay `δ`-close
  have hclose : ∀ t ∈ Icc (0 : ℝ) Δ, ‖F x t - F x₀ t‖ ≤ C * ‖x - x₀‖ := by
    intro t ht
    have hd := hF.dist_le hΔ.le hK hxs hx₀ ht
    rw [dist_eq_norm, dist_eq_norm] at hd
    refine hd.trans ?_
    rw [mul_comm ‖x - x₀‖ (Real.exp ((K : ℝ) * t))]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [hC]
    refine Real.exp_le_exp.mpr ?_
    have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
    nlinarith [ht.1, ht.2]
  have hδclose : ∀ t ∈ Icc (0 : ℝ) Δ, ‖F x t - F x₀ t‖ ≤ δ := by
    intro t ht
    refine (hclose t ht).trans ?_
    calc C * ‖x - x₀‖ ≤ C * ρ := mul_le_mul_of_nonneg_left hhnorm (by linarith)
      _ = δ := by rw [hρ]; field_simp
  -- the derivative of `z`
  have hzderiv : ∀ t ∈ Icc (0 : ℝ) Δ, HasDerivWithinAt z (zd t) (Icc (0 : ℝ) Δ) t := by
    intro t ht
    have h := ((hF.ode x hxs t ht).sub (hF.ode x₀ hx₀ t ht)).sub (hYode (x - x₀) t ht)
    exact h
  -- the Grönwall bound on `‖zd‖`
  have hzdbound : ∀ t ∈ Ico (0 : ℝ) Δ, ‖zd t‖ ≤ M * ‖z t‖ + ε * (C * ‖x - x₀‖) := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) Δ := Ico_subset_Icc_self ht
    have hx1 : F x t ∈ closedEdgeMomentumBox e P := hF.confined x hxs t htIcc
    have hx2 : F x₀ t ∈ closedEdgeMomentumBox e P := hF.confined x₀ hx₀ t htIcc
    have htaylor := hδest (F x₀ t) hx2 (F x t) hx1 (hδclose t htIcc)
    have hsplit : zd t = (V.edgeVectorField e (F x t) - V.edgeVectorField e (F x₀ t) -
        V.edgeFieldDeriv e (F x₀ t).1 (F x t - F x₀ t)) +
        V.edgeFieldDeriv e (F x₀ t).1 (z t) := by
      have hmap : V.edgeFieldDeriv e (F x₀ t).1 (z t) =
          V.edgeFieldDeriv e (F x₀ t).1 (F x t - F x₀ t) -
          V.edgeFieldDeriv e (F x₀ t).1 (Y t (x - x₀)) := by
        rw [hzval, map_sub]
      rw [hzdval, hmap]
      abel
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have hlin : ‖V.edgeFieldDeriv e (F x₀ t).1 (z t)‖ ≤ M * ‖z t‖ := by
      refine ((V.edgeFieldDeriv e (F x₀ t).1).le_opNorm (z t)).trans ?_
      exact mul_le_mul_of_nonneg_right (hMbound _ hx2.1) (norm_nonneg _)
    have htay : ‖V.edgeVectorField e (F x t) - V.edgeVectorField e (F x₀ t) -
        V.edgeFieldDeriv e (F x₀ t).1 (F x t - F x₀ t)‖ ≤ ε * (C * ‖x - x₀‖) := by
      refine htaylor.trans ?_
      exact mul_le_mul_of_nonneg_left (hclose t htIcc) hεpos.le
    linarith
  -- Grönwall
  have hzcont : ContinuousOn z (Icc (0 : ℝ) Δ) :=
    fun t ht => (hzderiv t ht).continuousWithinAt
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (f := z) (f' := zd)
    (δ := 0) (K := (M : ℝ)) (ε := ε * (C * ‖x - x₀‖)) hzcont
    (fun t ht => hasDerivWithinAt_Ici_of_mem_Icc ht (hzderiv t (Ico_subset_Icc_self ht)))
    (by rw [hz0, norm_zero]) hzdbound Δ ⟨hΔ.le, le_rfl⟩
  rw [sub_zero] at hgron
  -- read off the conclusion
  have hgval : gronwallBound 0 (M : ℝ) (ε * (C * ‖x - x₀‖)) Δ =
      ε * (C * ‖x - x₀‖) * G := by
    simp only [gronwallBound_of_K_ne_0 (ne_of_gt hMpos), hG]
    ring
  rw [hgval] at hgron
  have hzΔ : z Δ = F x Δ - F x₀ Δ - L (x - x₀) := by rw [hzval, hLY (x - x₀)]
  rw [hzΔ] at hgron
  have hεC : ε * (C * G) ≤ c := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [hG0, hC1, hc.le, mul_nonneg (by linarith : (0:ℝ) ≤ C) hG0]
  calc ‖F x Δ - F x₀ Δ - L (x - x₀)‖ ≤ ε * (C * ‖x - x₀‖) * G := hgron
    _ = (ε * (C * G)) * ‖x - x₀‖ := by ring
    _ ≤ c * ‖x - x₀‖ := mul_le_mul_of_nonneg_right hεC (norm_nonneg _)

end Deriv

/-! ### Liouville invariance -/

/-- **Lemma V.1 (Liouville part).**  The time-`Δ` map of the edge Hamiltonian flow preserves
two-dimensional Lebesgue measure `dq dp`: the image of a measurable set of initial conditions has
the same measure.

The proof combines the three ingredients above: the time-`Δ` map is differentiable in the initial
condition, its derivative has determinant `1` (the Wronskian of the trace-free variational
equation — Liouville's theorem), and it is injective by backward ODE uniqueness.  The measure
identity is then the change-of-variables formula. -/
theorem measure_image_edgeFlow {e : Γ.Edge} {P Δ : ℝ} {s : Set (ℝ × ℝ)}
    {F : (ℝ × ℝ) → ℝ → ℝ × ℝ} (hF : EdgeSolutionFamily V e P Δ s F) (hs : MeasurableSet s)
    (hΔ : 0 < Δ) {M : ℝ≥0} (hM1 : (1 : ℝ) ≤ M)
    (hMbound : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), ‖V.edgeFieldDeriv e q‖ ≤ M)
    (hΔM : Δ ≤ 1 / (3 * M)) :
    volume ((fun x => F x Δ) '' s) = volume s := by
  classical
  -- choose the derivative at every point of `s`
  have hderiv : ∀ x ∈ s, ∃ L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), L.det = 1 ∧
      HasFDerivWithinAt (fun y => F y Δ) L s x :=
    fun x hx => V.hasFDerivWithinAt_of_edgeSolutionFamily hF hΔ hM1 hMbound hΔM hx
  choose! L hLdet hLderiv using hderiv
  have hkey := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure (ℝ × ℝ)) hs
    (fun x hx => hLderiv x hx) (hF.injOn_apply hΔ)
  rw [← hkey]
  have hone : ∀ x ∈ s, ENNReal.ofReal |(L x).det| = 1 := by
    intro x hx
    rw [hLdet x hx]
    norm_num
  rw [setLIntegral_congr_fun hs hone, setLIntegral_one]

end MechanicalPotential

end HamiltonianMetricGraphs
