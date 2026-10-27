/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.1 as printed: the flow-box map is a `C¹` diffeomorphism and `Ψ^*(dq ∧ dp) = ξ ds ∧ dξ`.
-/

import HamiltonianMetricGraphs.EdgeLiouville
import HamiltonianMetricGraphs.EnergyTime
import HamiltonianMetricGraphs.BoundaryFlux

/-!
# Lemma VI.1 (local flux form) in the paper's coordinates

Lemma VI.1 of the paper: for an edge-end `η = (e, a)` and `p₀ ≠ 0`, in a small flow box around
`(a, p₀)` the map `Ψ(s, ξ) = φ_s^{(e)}(a, ξ)` is a `C¹` diffeomorphism onto its image, and
`Ψ^*(dq ∧ dp) = ξ ds ∧ dξ`; consequently the positive Liouville measure pulls back to
`|ξ| ds dξ`, and the transverse boundary measure is `|ξ| dξ`, i.e. `r dr` in speed coordinates.

The main result is `local_flux_form`, stated literally in the coordinates `(s, ξ)`: an
`OpenPartialHomeomorph` `Ψ` with source the box `(-δ, δ) × (p₀ - δ, p₀ + δ)`, which is `C¹` with
`C¹` inverse, whose `s`-lines are the solutions of the edge Hamilton equations of the chosen `C²`
extension through `(a, ξ)` (and the only ones staying in the box), with `det DΨ(s, ξ) = ξ`, and
with the change-of-variables identity `∫_{Ψ(B)} f dq dp = ∫_B f ∘ Ψ · |ξ| ds dξ`, and with the
transverse factor `|ξ| dξ` carried by `ξ ↦ r = |ξ|` to `r dr` (`map_abs_transverse`), the boundary
speed measure of Definition III.6 (`map_positiveSpeedOf_speedInterval`).
(The earlier modules `EnergyTime.lean` and `TubeForm.lean` prove the measure part in the
`(r, travel-time)` coordinates instead, without the diffeomorphism statement.)

## Proof

Mathlib has no differentiable dependence of ODE solutions on initial data, so the paper's route
(inverse function theorem applied to `Ψ`, and invariance of `dq ∧ dp` under the edge flow) is
replaced by an explicit inverse.  With `σ = sign p₀`, `c = V_e(a)` and `H(q, p) = p²/2 + V_e(q)`,
the **energy-time chart**

`χ(q, p) = (σ ∫_a^q dx / √(2 (H(q,p) - V_e(x))), σ √(2 (H(q,p) - c)))`

sends a state to the time `s` its trajectory needs from the section `{q = a}` and to the signed
momentum `ξ` it has there.  The travel-time integral is `C¹` jointly in the energy and the
endpoint (differentiation under the integral sign, `hasDerivAt_travel_energy`, and continuity of
the partial derivatives, `hasStrictFDerivAt_uncurry_coprod`); to apply Mathlib's parametric
integral lemmas globally, its integrand is replaced by a clamped, globally continuous function
that agrees with `1/√(2(E - V_e))` on the box.  A direct computation gives

* `Dχ · X_H = (1, 0)` (`chartDeriv_field`): `χ` straightens the Hamiltonian vector field;
* `det Dχ = 1/ξ` (`det_chartDeriv`).

The inverse function theorem (`ContDiffAt.toOpenPartialHomeomorph`) makes `χ` a local `C¹`
diffeomorphism near `(a, p₀)`, and `Ψ` is its inverse on a box.  Then `∂_s Ψ = (Dχ)⁻¹(1, 0) = X_H`,
so `s ↦ Ψ(s, ξ)` solves Hamilton's equations, `Ψ(0, ξ) = (a, ξ)` because the travel time vanishes
only on the section, `det DΨ = ξ`, and Mathlib's change-of-variables formula
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` gives the measure identity.  Uniqueness of the
solution in the box is `ODE_solution_unique_of_mem_Ioo`, the field being Lipschitz near `(a, p₀)`.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory intervalIntegral
open scoped Topology ENNReal NNReal Interval

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

namespace FluxBox

/-! ### A clamped, globally continuous travel-time integrand -/

/-- The clamp of `x` to `[a - r, a + r]`. -/
def clamp (a r x : ℝ) : ℝ := max (a - r) (min x (a + r))

theorem continuous_clamp (a r : ℝ) : Continuous (clamp a r) := by
  unfold clamp; fun_prop

theorem clamp_mem {a r : ℝ} (hr : 0 ≤ r) (x : ℝ) : clamp a r x ∈ Icc (a - r) (a + r) := by
  unfold clamp
  refine ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem clamp_of_mem {a r x : ℝ} (hx : x ∈ Icc (a - r) (a + r)) : clamp a r x = x := by
  unfold clamp
  rw [min_eq_left hx.2, max_eq_right hx.1]

variable (e : Γ.Edge) (a r m : ℝ)

/-- The clamped reciprocal speed `G(E, x) = (max (2 (E - V(clamp x))) m)^{-1/2}`.  On the window
where `2 (E - V(x)) ≥ m` and `x ∈ [a - r, a + r]` it is the reciprocal speed `1/√(2(E - V(x)))`;
elsewhere it is a continuous extension. -/
noncomputable def integrand (E x : ℝ) : ℝ :=
  (Real.sqrt (max (2 * (E - V.extension e (clamp a r x))) m))⁻¹

/-- The clamped travel time `T(E, q) = ∫_a^q G(E, x) dx`. -/
noncomputable def travel (E q : ℝ) : ℝ := ∫ x in a..q, integrand V e a r m E x

/-- Its energy derivative `∂_E T(E, q) = -∫_a^q G(E, x)³ dx`. -/
noncomputable def travelE (E q : ℝ) : ℝ := -∫ x in a..q, integrand V e a r m E x ^ 3

variable {V e a r m}

theorem continuous_integrand (hr : 0 ≤ r) (hm : 0 < m)
    (hdom : Icc (a - r) (a + r) ⊆ V.domain e) :
    Continuous fun y : ℝ × ℝ => integrand V e a r m y.1 y.2 := by
  have hV : Continuous fun x => V.extension e (clamp a r x) :=
    ((V.contDiffOn_extension e).continuousOn.mono hdom).comp_continuous (continuous_clamp a r)
      (fun x => clamp_mem hr x)
  have hmax : Continuous fun y : ℝ × ℝ =>
      max (2 * (y.1 - V.extension e (clamp a r y.2))) m := by
    have h2 : Continuous fun y : ℝ × ℝ => V.extension e (clamp a r y.2) := hV.comp continuous_snd
    exact ((continuous_const.mul (continuous_fst.sub h2))).max continuous_const
  refine (Real.continuous_sqrt.comp hmax).inv₀ ?_
  intro y
  exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le hm (le_max_right _ _)))

theorem integrand_nonneg (E x : ℝ) : 0 ≤ integrand V e a r m E x :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem integrand_le (hm : 0 < m) (E x : ℝ) :
    integrand V e a r m E x ≤ (Real.sqrt m)⁻¹ := by
  unfold integrand
  exact inv_anti₀ (Real.sqrt_pos.mpr hm) (Real.sqrt_le_sqrt (le_max_right _ _))

theorem integrand_eq {Eb E x : ℝ} (hgap : ∀ y ∈ Icc (a - r) (a + r), m ≤ 2 * (Eb - V.extension e y))
    (hE : Eb ≤ E) (hx : x ∈ Icc (a - r) (a + r)) :
    integrand V e a r m E x = (Real.sqrt (2 * (E - V.extension e x)))⁻¹ := by
  unfold integrand
  rw [clamp_of_mem hx, max_eq_left]
  have := hgap x hx
  linarith

/-- The energy derivative of the integrand. -/
theorem hasDerivAt_integrand_energy {Eb E x : ℝ} (hm : 0 < m)
    (hgap : ∀ y ∈ Icc (a - r) (a + r), m ≤ 2 * (Eb - V.extension e y))
    (hE : Eb < E) (hx : x ∈ Icc (a - r) (a + r)) :
    HasDerivAt (fun E' => integrand V e a r m E' x) (-integrand V e a r m E x ^ 3) E := by
  have hw : 0 < 2 * (E - V.extension e x) := by
    have := hgap x hx; linarith
  have hsq : 0 < Real.sqrt (2 * (E - V.extension e x)) := Real.sqrt_pos.mpr hw
  have hinner : HasDerivAt (fun E' : ℝ => 2 * (E' - V.extension e x)) 2 E := by
    simpa using ((hasDerivAt_id E).sub_const (V.extension e x)).const_mul 2
  have hd := (hinner.sqrt (ne_of_gt hw)).inv (ne_of_gt hsq)
  have hev : (fun E' => integrand V e a r m E' x) =ᶠ[𝓝 E]
      fun E' => (Real.sqrt (2 * (E' - V.extension e x)))⁻¹ := by
    filter_upwards [Ioi_mem_nhds hE] with E' hE'
    exact integrand_eq hgap (le_of_lt hE') hx
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [integrand_eq hgap hE.le hx]
  have hne : Real.sqrt (2 * (E - V.extension e x)) ≠ 0 := ne_of_gt hsq
  field_simp

theorem continuous_travel (hr : 0 ≤ r) (hm : 0 < m) (hdom : Icc (a - r) (a + r) ⊆ V.domain e) :
    Continuous fun y : ℝ × ℝ => travel V e a r m y.1 y.2 :=
  continuous_parametric_primitive_of_continuous (f := fun E x => integrand V e a r m E x)
    (continuous_integrand hr hm hdom)

theorem continuous_travelE (hr : 0 ≤ r) (hm : 0 < m) (hdom : Icc (a - r) (a + r) ⊆ V.domain e) :
    Continuous fun y : ℝ × ℝ => travelE V e a r m y.1 y.2 :=
  (continuous_parametric_primitive_of_continuous (f := fun E x => integrand V e a r m E x ^ 3)
    ((continuous_integrand hr hm hdom).pow 3)).neg

/-- `∂_q T(E, q) = G(E, q)`. -/
theorem hasDerivAt_travel_position (hr : 0 ≤ r) (hm : 0 < m)
    (hdom : Icc (a - r) (a + r) ⊆ V.domain e) (E q : ℝ) :
    HasDerivAt (fun q' => travel V e a r m E q') (integrand V e a r m E q) q := by
  have hc : Continuous fun x => integrand V e a r m E x :=
    (continuous_integrand hr hm hdom).comp (continuous_const.prodMk continuous_id)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

/-- `∂_E T(E, q) = -∫_a^q G(E, x)³ dx` on the window `E > E_b`, `q ∈ [a - r, a + r]`. -/
theorem hasDerivAt_travel_energy (hr : 0 ≤ r) (hm : 0 < m)
    (hdom : Icc (a - r) (a + r) ⊆ V.domain e) {Eb E q : ℝ}
    (hgap : ∀ y ∈ Icc (a - r) (a + r), m ≤ 2 * (Eb - V.extension e y))
    (hE : Eb < E) (hq : q ∈ Icc (a - r) (a + r)) :
    HasDerivAt (fun E' => travel V e a r m E' q) (travelE V e a r m E q) E := by
  have hcont := continuous_integrand hr hm hdom
  have hcE : ∀ E' : ℝ, Continuous fun x => integrand V e a r m E' x :=
    fun E' => hcont.comp (continuous_const.prodMk continuous_id)
  have ha : a ∈ Icc (a - r) (a + r) := ⟨by linarith, by linarith⟩
  have hsub : ∀ x ∈ Ι a q, x ∈ Icc (a - r) (a + r) := fun x hx =>
    (Set.ordConnected_Icc.uIcc_subset ha hq) (uIoc_subset_uIcc hx)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := q) (F := fun E' x => integrand V e a r m E' x)
    (F' := fun E' x => -integrand V e a r m E' x ^ 3) (x₀ := E) (s := Ioi Eb)
    (bound := fun _ => (Real.sqrt m)⁻¹ ^ 3) (Ioi_mem_nhds hE)
    (Eventually.of_forall fun E' => (hcE E').aestronglyMeasurable)
    ((hcE E).intervalIntegrable _ _)
    (((hcE E).pow 3).neg.aestronglyMeasurable)
    (Eventually.of_forall fun x _ E' _ => by
      rw [norm_neg, norm_pow, Real.norm_of_nonneg (integrand_nonneg E' x)]
      exact pow_le_pow_left₀ (integrand_nonneg E' x) (integrand_le hm E' x) 3)
    intervalIntegral.intervalIntegrable_const
    (Eventually.of_forall fun x hx E' hE' =>
      hasDerivAt_integrand_energy hm hgap hE' (hsub x hx))
  refine h.2.congr_deriv ?_
  unfold travelE
  rw [intervalIntegral.integral_neg]

/-- The derivative of the clamped travel time. -/
noncomputable def travelDeriv (y : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  travelE V e a r m y.1 y.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    integrand V e a r m y.1 y.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem continuous_travelDeriv (hr : 0 ≤ r) (hm : 0 < m)
    (hdom : Icc (a - r) (a + r) ⊆ V.domain e) :
    Continuous fun y : ℝ × ℝ => travelDeriv (V := V) (e := e) (a := a) (r := r) (m := m) y := by
  unfold travelDeriv
  exact ((continuous_travelE hr hm hdom).smul continuous_const).add
    ((continuous_integrand hr hm hdom).smul continuous_const)

/-- **The clamped travel time is strictly differentiable** on the window `E > E_b`,
`q ∈ (a - r, a + r)`, with the derivative `travelDeriv`. -/
theorem hasStrictFDerivAt_travel (hr : 0 ≤ r) (hm : 0 < m)
    (hdom : Icc (a - r) (a + r) ⊆ V.domain e) {Eb : ℝ}
    (hgap : ∀ y ∈ Icc (a - r) (a + r), m ≤ 2 * (Eb - V.extension e y))
    {y : ℝ × ℝ} (hy : y ∈ Ioi Eb ×ˢ Ioo (a - r) (a + r)) :
    HasStrictFDerivAt (fun y : ℝ × ℝ => travel V e a r m y.1 y.2)
      (travelDeriv (V := V) (e := e) (a := a) (r := r) (m := m) y) y := by
  have hopen : IsOpen (Ioi Eb ×ˢ Ioo (a - r) (a + r)) := isOpen_Ioi.prod isOpen_Ioo
  have h := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := y)
    (f := fun E q => travel V e a r m E q)
    (f₁ := fun E q => travelE V e a r m E q • (1 : ℝ →L[ℝ] ℝ))
    (f₂ := fun E q => integrand V e a r m E q • (1 : ℝ →L[ℝ] ℝ))
    ?_ ?_ ?_ ?_
  · refine h.congr_fderiv ?_
    ext <;> simp [travelDeriv, Function.HasUncurry.uncurry]
  · filter_upwards [hopen.mem_nhds hy] with w hw
    have hd := hasDerivAt_travel_energy hr hm hdom hgap hw.1 (Ioo_subset_Icc_self hw.2)
    refine hd.hasFDerivAt.congr_fderiv ?_
    ext; simp [Function.HasUncurry.uncurry]
  · filter_upwards with w
    have hd := hasDerivAt_travel_position hr hm hdom w.1 w.2
    refine hd.hasFDerivAt.congr_fderiv ?_
    ext; simp [Function.HasUncurry.uncurry]
  · exact (((continuous_travelE hr hm hdom).smul continuous_const)).continuousAt
  · exact (((continuous_integrand hr hm hdom).smul continuous_const)).continuousAt

theorem contDiffAt_travel (hr : 0 ≤ r) (hm : 0 < m)
    (hdom : Icc (a - r) (a + r) ⊆ V.domain e) {Eb : ℝ}
    (hgap : ∀ y ∈ Icc (a - r) (a + r), m ≤ 2 * (Eb - V.extension e y))
    {y : ℝ × ℝ} (hy : y ∈ Ioi Eb ×ˢ Ioo (a - r) (a + r)) :
    ContDiffAt ℝ 1 (fun y : ℝ × ℝ => travel V e a r m y.1 y.2) y := by
  have hopen : IsOpen (Ioi Eb ×ˢ Ioo (a - r) (a + r)) := isOpen_Ioi.prod isOpen_Ioo
  rw [contDiffAt_one_iff]
  exact ⟨fun y => travelDeriv (V := V) (e := e) (a := a) (r := r) (m := m) y, _,
    hopen.mem_nhds hy, (continuous_travelDeriv hr hm hdom).continuousOn,
    fun w hw => (hasStrictFDerivAt_travel hr hm hdom hgap hw).hasFDerivAt⟩

/-! ### The energy-time chart -/

/-- The determinant of a linear map of the plane in terms of the images of the basis vectors:
the value of `dq ∧ dp` on them. -/
theorem det_eq_basis (L : ℝ × ℝ →L[ℝ] ℝ × ℝ) :
    L.det = (L (1, 0)).1 * (L (0, 1)).2 - (L (0, 1)).1 * (L (1, 0)).2 := by
  have hL : L = pairMap (L (1, 0)) (L (0, 1)) := by
    refine ContinuousLinearMap.ext fun u => ?_
    have hu : u = u.1 • ((1 : ℝ), (0 : ℝ)) + u.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hu]
    rw [map_add, map_smul, map_smul, pairMap_apply]
  rw [hL, pairMap_det]
  simp

/-- The derivative of the edge Hamiltonian `H(q, p) = p²/2 + V_e(q)`. -/
noncomputable def hamDeriv (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  deriv (V.extension e) x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem hasFDerivAt_hamiltonian {x : ℝ × ℝ} (hx : x.1 ∈ V.domain e) :
    HasFDerivAt (fun y : ℝ × ℝ => V.hamiltonian e y.1 y.2) (hamDeriv (V := V) (e := e) x) x := by
  have hV : HasDerivAt (V.extension e) (deriv (V.extension e) x.1) x.1 :=
    ((V.extension_contDiffAt_of_mem hx).differentiableAt (by norm_num)).hasDerivAt
  have h2 : HasFDerivAt (fun y : ℝ × ℝ => V.extension e y.1)
      (deriv (V.extension e) x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
    refine (hV.hasFDerivAt.comp x hasFDerivAt_fst).congr_fderiv ?_
    ext <;> simp
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => y.2 ^ 2 / 2)
      (x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    have := ((hasDerivAt_pow 2 x.2).div_const 2).comp_hasFDerivAt x
      (hasFDerivAt_snd (𝕜 := ℝ) (p := x))
    refine this.congr_fderiv ?_
    ext <;> simp
  have h := h1.add h2
  unfold hamiltonian
  refine h.congr_fderiv ?_
  unfold hamDeriv
  ext <;> simp

theorem contDiffAt_hamiltonian {x : ℝ × ℝ} (hx : x.1 ∈ V.domain e) :
    ContDiffAt ℝ 1 (fun y : ℝ × ℝ => V.hamiltonian e y.1 y.2) x := by
  unfold hamiltonian
  have hV : ContDiffAt ℝ 1 (fun y : ℝ × ℝ => V.extension e y.1) x :=
    ((V.extension_contDiffAt_of_mem hx).of_le (by norm_num)).comp x contDiffAt_fst
  exact ((contDiffAt_snd.pow 2).div_const 2).add hV

variable (V e a r m) in
/-- **The energy-time chart** `χ(q, p) = (σ T(H(q,p), q), σ √(2 (H(q,p) - c)))`: the travel
time from the section `{q = a}` and the signed boundary momentum `ξ` of the same energy level.
On the region it is the inverse of the flow-box map `Ψ(s, ξ) = φ_s(a, ξ)`. -/
noncomputable def chart (σ c : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (σ * travel V e a r m (V.hamiltonian e x.1 x.2) x.1,
    σ * Real.sqrt (2 * (V.hamiltonian e x.1 x.2 - c)))

variable (V e a r) in
/-- The region of the chart: positions in `(a - r, a + r)`, energies above `E_b` and `c`, and
momenta of the sign `σ`. -/
def region (σ c Eb : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioo (a - r) (a + r) ∧ Eb < V.hamiltonian e x.1 x.2 ∧
    c < V.hamiltonian e x.1 x.2 ∧ 0 < σ * x.2}

theorem isOpen_region (hdom : Icc (a - r) (a + r) ⊆ V.domain e) (σ c Eb : ℝ) :
    IsOpen (region V e a r σ c Eb) := by
  have hH : ContinuousOn (fun y : ℝ × ℝ => V.hamiltonian e y.1 y.2)
      {x : ℝ × ℝ | x.1 ∈ Ioo (a - r) (a + r)} := by
    intro x hx
    have hV : ContinuousAt (V.extension e) x.1 :=
      V.extension_continuousAt_of_mem (hdom (Ioo_subset_Icc_self hx))
    have : ContinuousAt (fun y : ℝ × ℝ => y.2 ^ 2 / 2 + V.extension e y.1) x :=
      (continuousAt_snd.pow 2 |>.div_const 2).add (hV.comp continuousAt_fst)
    exact this.continuousWithinAt
  have h1 : IsOpen {x : ℝ × ℝ | x.1 ∈ Ioo (a - r) (a + r)} := isOpen_Ioo.preimage continuous_fst
  have h2 := hH.isOpen_inter_preimage h1 (isOpen_Ioi (a := max Eb c))
  have h3 : IsOpen {x : ℝ × ℝ | 0 < σ * x.2} :=
    isOpen_lt continuous_const (continuous_const.mul continuous_snd)
  convert h2.inter h3 using 1
  ext x
  simp only [region, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ioi, max_lt_iff]
  tauto

/-- The derivative of the chart. -/
noncomputable def chartDeriv (σ c : ℝ) (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (σ • (travelDeriv (V := V) (e := e) (a := a) (r := r) (m := m)
      (V.hamiltonian e x.1 x.2, x.1)).comp
      ((hamDeriv (V := V) (e := e) x).prod (ContinuousLinearMap.fst ℝ ℝ ℝ))).prod
    (σ • ((1 / (2 * Real.sqrt (2 * (V.hamiltonian e x.1 x.2 - c)))) •
      ((2 : ℝ) • hamDeriv (V := V) (e := e) x)))

theorem hasFDerivAt_chart (hr : 0 ≤ r) (hm : 0 < m) (hdom : Icc (a - r) (a + r) ⊆ V.domain e)
    {Eb : ℝ} (hgap : ∀ y ∈ Icc (a - r) (a + r), m ≤ 2 * (Eb - V.extension e y))
    {σ c : ℝ} {x : ℝ × ℝ} (hx : x ∈ region V e a r σ c Eb) :
    HasFDerivAt (chart V e a r m σ c) (chartDeriv (V := V) (e := e) (a := a) (r := r) (m := m)
      σ c x) x := by
  have hxd : x.1 ∈ V.domain e := hdom (Ioo_subset_Icc_self hx.1)
  have hH := hasFDerivAt_hamiltonian (V := V) (e := e) hxd
  have hT := (hasStrictFDerivAt_travel hr hm hdom hgap
    (y := (V.hamiltonian e x.1 x.2, x.1)) ⟨hx.2.1, hx.1⟩).hasFDerivAt
  have h1 := (hT.comp x (hH.prodMk hasFDerivAt_fst)).const_mul σ
  have hpos : 2 * (V.hamiltonian e x.1 x.2 - c) ≠ 0 := by
    have := hx.2.2.1; apply ne_of_gt; linarith
  have h2 := (((hH.sub_const c).const_mul 2).sqrt hpos).const_mul σ
  exact h1.prodMk h2

theorem contDiffAt_chart (hr : 0 ≤ r) (hm : 0 < m) (hdom : Icc (a - r) (a + r) ⊆ V.domain e)
    {Eb : ℝ} (hgap : ∀ y ∈ Icc (a - r) (a + r), m ≤ 2 * (Eb - V.extension e y))
    {σ c : ℝ} {x : ℝ × ℝ} (hx : x ∈ region V e a r σ c Eb) :
    ContDiffAt ℝ 1 (chart V e a r m σ c) x := by
  have hxd : x.1 ∈ V.domain e := hdom (Ioo_subset_Icc_self hx.1)
  have hH := contDiffAt_hamiltonian (V := V) (e := e) hxd
  have hT := contDiffAt_travel hr hm hdom hgap
    (y := (V.hamiltonian e x.1 x.2, x.1)) ⟨hx.2.1, hx.1⟩
  have h1 := contDiffAt_const (c := σ) |>.mul (hT.comp x (hH.prodMk contDiffAt_fst))
  have hpos : 2 * (V.hamiltonian e x.1 x.2 - c) ≠ 0 := by
    have := hx.2.2.1; apply ne_of_gt; linarith
  have h2 := contDiffAt_const (c := σ) |>.mul
    (((hH.sub contDiffAt_const).const_smul (2 : ℝ)).sqrt hpos)
  exact h1.prodMk h2

theorem chartDeriv_apply (σ c : ℝ) (x u : ℝ × ℝ) :
    chartDeriv (V := V) (e := e) (a := a) (r := r) (m := m) σ c x u =
      (σ * (travelE V e a r m (V.hamiltonian e x.1 x.2) x.1 *
          (deriv (V.extension e) x.1 * u.1 + x.2 * u.2) +
          integrand V e a r m (V.hamiltonian e x.1 x.2) x.1 * u.1),
        σ * (1 / (2 * Real.sqrt (2 * (V.hamiltonian e x.1 x.2 - c))) *
          (2 * (deriv (V.extension e) x.1 * u.1 + x.2 * u.2)))) := by
  ext <;> simp [chartDeriv, travelDeriv, hamDeriv] <;> ring

/-- On the region the reciprocal speed is `1/|p| = 1/(σ p)`. -/
theorem integrand_eq_inv (hr : 0 ≤ r) {Eb : ℝ}
    (hgap : ∀ y ∈ Icc (a - r) (a + r), m ≤ 2 * (Eb - V.extension e y))
    {σ c : ℝ} (hσ : σ = 1 ∨ σ = -1) {x : ℝ × ℝ} (hx : x ∈ region V e a r σ c Eb) :
    integrand V e a r m (V.hamiltonian e x.1 x.2) x.1 = (σ * x.2)⁻¹ := by
  have _ := hr
  rw [integrand_eq hgap hx.2.1.le (Ioo_subset_Icc_self hx.1)]
  congr 1
  have h2 : 2 * (V.hamiltonian e x.1 x.2 - V.extension e x.1) = (σ * x.2) ^ 2 := by
    unfold hamiltonian
    rcases hσ with rfl | rfl <;> ring
  rw [h2, Real.sqrt_sq hx.2.2.2.le]

/-- **The chart straightens the Hamiltonian vector field**: `Dχ · X_H = (1, 0)`. -/
theorem chartDeriv_field (hr : 0 ≤ r) {Eb : ℝ}
    (hgap : ∀ y ∈ Icc (a - r) (a + r), m ≤ 2 * (Eb - V.extension e y))
    {σ c : ℝ} (hσ : σ = 1 ∨ σ = -1) {x : ℝ × ℝ} (hx : x ∈ region V e a r σ c Eb) :
    chartDeriv (V := V) (e := e) (a := a) (r := r) (m := m) σ c x
      (V.edgeVectorField e x) = (1, 0) := by
  rw [chartDeriv_apply, integrand_eq_inv hr hgap hσ hx]
  have hp : x.2 ≠ 0 := by
    intro h; have := hx.2.2.2; rw [h, mul_zero] at this; exact lt_irrefl _ this
  simp only [edgeVectorField, force]
  ext
  · simp only
    rcases hσ with rfl | rfl <;> field_simp <;> ring
  · simp only
    ring

/-- **The Jacobian of the chart**: `det Dχ = 1/ξ`. -/
theorem det_chartDeriv (hr : 0 ≤ r) {Eb : ℝ}
    (hgap : ∀ y ∈ Icc (a - r) (a + r), m ≤ 2 * (Eb - V.extension e y))
    {σ c : ℝ} (hσ : σ = 1 ∨ σ = -1) {x : ℝ × ℝ} (hx : x ∈ region V e a r σ c Eb) :
    (chartDeriv (V := V) (e := e) (a := a) (r := r) (m := m) σ c x).det =
      (chart V e a r m σ c x).2⁻¹ := by
  rw [det_eq_basis, chartDeriv_apply, chartDeriv_apply, integrand_eq_inv hr hgap hσ hx]
  have hp : x.2 ≠ 0 := by
    intro h; have := hx.2.2.2; rw [h, mul_zero] at this; exact lt_irrefl _ this
  have hR : Real.sqrt (2 * (V.hamiltonian e x.1 x.2 - c)) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr; linarith [hx.2.2.1]
  simp only [chart]
  rcases hσ with rfl | rfl <;> field_simp <;> ring

/-- The travel time vanishes only at the section `q = a`. -/
theorem eq_of_travel_eq_zero (hr : 0 ≤ r) (hm : 0 < m) (hdom : Icc (a - r) (a + r) ⊆ V.domain e)
    {E q : ℝ} (h : travel V e a r m E q = 0) : q = a := by
  have hc : Continuous fun x => integrand V e a r m E x :=
    (continuous_integrand hr hm hdom).comp (continuous_const.prodMk continuous_id)
  have hpos : ∀ x, 0 < integrand V e a r m E x := fun x =>
    inv_pos.mpr (Real.sqrt_pos.mpr (lt_of_lt_of_le hm (le_max_right _ _)))
  rcases lt_trichotomy a q with haq | rfl | hqa
  · exact absurd h (ne_of_gt (intervalIntegral.intervalIntegral_pos_of_pos_on
      (hc.intervalIntegrable _ _) (fun x _ => hpos x) haq))
  · rfl
  · have := intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable q a)
      (fun x _ => hpos x) hqa
    unfold travel at h
    rw [intervalIntegral.integral_symm] at h
    linarith

end FluxBox

/-! ### The transverse measure in speed coordinates -/

/-- **`|ξ| dξ` is `r dr` in speed coordinates.**  On a momentum interval
`(p₀ - δ, p₀ + δ)` of one sign (`δ ≤ |p₀|`), the image of `|ξ| dξ` under the speed `ξ ↦ r = |ξ|`
is `r dr` on the speed interval `(|p₀| - δ, |p₀| + δ)`. -/
theorem map_abs_transverse {p₀ δ : ℝ} (hδ : 0 < δ) (hδp : δ ≤ |p₀|) :
    Measure.map (fun ξ : ℝ => |ξ|)
        ((volume.restrict (Ioo (p₀ - δ) (p₀ + δ))).withDensity fun ξ => ENNReal.ofReal |ξ|) =
      (volume.restrict (Ioo (|p₀| - δ) (|p₀| + δ))).withDensity fun r => ENNReal.ofReal r := by
  ext1 t ht
  have hm : Measurable fun ξ : ℝ => |ξ| := continuous_abs.measurable
  rw [Measure.map_apply hm ht, withDensity_apply _ (hm ht), withDensity_apply _ ht,
    Measure.restrict_restrict (hm ht), Measure.restrict_restrict ht]
  rcases lt_trichotomy p₀ 0 with hp | hp | hp
  · -- negative branch: `r = -ξ`
    rw [abs_of_neg hp] at hδp ⊢
    have hset : Neg.neg ⁻¹' (t ∩ Ioo (-p₀ - δ) (-p₀ + δ)) =
        (fun ξ : ℝ => |ξ|) ⁻¹' t ∩ Ioo (p₀ - δ) (p₀ + δ) := by
      ext ξ
      simp only [mem_preimage, mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rw [abs_of_neg (by linarith)]
        exact ⟨h1, by linarith, by linarith⟩
      · rintro ⟨h1, h2, h3⟩
        rw [abs_of_neg (by linarith)] at h1
        exact ⟨h1, by linarith, by linarith⟩
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.neg ℝ).measurableEmbedding (fun r : ℝ => ENNReal.ofReal r)
      (t ∩ Ioo (-p₀ - δ) (-p₀ + δ))
    rw [← h, hset]
    refine setLIntegral_congr_fun ((hm ht).inter measurableSet_Ioo) (fun ξ hξ => ?_)
    rw [abs_of_neg (by linarith [hξ.2.2])]
  · rw [hp, abs_zero] at hδp; linarith
  · -- positive branch: `r = ξ`
    rw [abs_of_pos hp]
    have hset : (fun ξ : ℝ => |ξ|) ⁻¹' t ∩ Ioo (p₀ - δ) (p₀ + δ) =
        t ∩ Ioo (p₀ - δ) (p₀ + δ) := by
      ext ξ
      simp only [mem_preimage, mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rw [abs_of_pos (by rw [abs_of_pos hp] at hδp; linarith)] at h1
        exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        rw [abs_of_pos (by rw [abs_of_pos hp] at hδp; linarith)]
        exact ⟨h1, h2, h3⟩
    rw [hset]
    refine setLIntegral_congr_fun (ht.inter measurableSet_Ioo) (fun ξ hξ => ?_)
    rw [abs_of_pos (by rw [abs_of_pos hp] at hδp; linarith [hξ.2.1])]

/-- The speed measure `r dr` on a speed interval `J ⊆ (0, ∞)` is the restriction to `J` of the
boundary speed measure `speedFluxMeasure` of Definition III.6. -/
theorem map_positiveSpeedOf_speedInterval {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : J ⊆ Ioi 0) :
    Measure.map FiniteMetricGraph.positiveSpeedOf
        ((volume.restrict J).withDensity fun r => ENNReal.ofReal r) =
      FiniteMetricGraph.speedFluxMeasure.restrict (Subtype.val ⁻¹' J) := by
  have hmeas := FiniteMetricGraph.measurable_positiveSpeedOf
  have hJ' : MeasurableSet (Subtype.val ⁻¹' J : Set FiniteMetricGraph.PositiveSpeed) :=
    measurable_subtype_coe hJ
  ext1 t ht
  rw [Measure.map_apply hmeas ht, withDensity_apply _ (hmeas ht), Measure.restrict_apply ht,
    FiniteMetricGraph.speedFluxMeasure, Measure.map_apply hmeas (ht.inter hJ'),
    withDensity_apply _ (hmeas (ht.inter hJ')), Measure.restrict_restrict (hmeas ht),
    Measure.restrict_restrict (hmeas (ht.inter hJ'))]
  congr 2
  ext r
  simp only [mem_inter_iff, mem_preimage, mem_Ioi]
  constructor
  · rintro ⟨h1, h2⟩
    have hr : 0 < r := hJpos h2
    refine ⟨⟨h1, ?_⟩, hr⟩
    rw [FiniteMetricGraph.positiveSpeedOf_of_pos hr]; exact h2
  · rintro ⟨⟨h1, h2⟩, hr⟩
    refine ⟨h1, ?_⟩
    rw [FiniteMetricGraph.positiveSpeedOf_of_pos hr] at h2; exact h2

open FluxBox

/-- **Lemma VI.1 at an arbitrary base point of the extension domain.**  See `local_flux_form`. -/
theorem local_flux_form_of_mem_domain (e : Γ.Edge) {a p₀ : ℝ} (ha : a ∈ V.domain e)
    (hp₀ : p₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Ψ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      Ψ.source = Ioo (-δ) δ ×ˢ Ioo (p₀ - δ) (p₀ + δ) ∧
      (∀ y ∈ Ψ.source, 0 < p₀ * y.2) ∧
      (∀ x ∈ Ψ.target, x.1 ∈ V.domain e) ∧
      (∀ ξ ∈ Ioo (p₀ - δ) (p₀ + δ), Ψ (0, ξ) = (a, ξ)) ∧
      (∀ y ∈ Ψ.source, HasDerivAt (fun s => Ψ (s, y.2)) (V.edgeVectorField e (Ψ y)) y.1) ∧
      (∀ ξ ∈ Ioo (p₀ - δ) (p₀ + δ), ∀ γ : ℝ → ℝ × ℝ, γ 0 = (a, ξ) →
        (∀ t ∈ Ioo (-δ) δ, HasDerivAt γ (V.edgeVectorField e (γ t)) t ∧ γ t ∈ Ψ.target) →
        ∀ t ∈ Ioo (-δ) δ, γ t = Ψ (t, ξ)) ∧
      ContDiffOn ℝ 1 Ψ Ψ.source ∧ ContDiffOn ℝ 1 Ψ.symm Ψ.target ∧
      (∀ y ∈ Ψ.source, (fderiv ℝ Ψ y).det = y.2) ∧
      (∀ y ∈ Ψ.source,
        (fderiv ℝ Ψ y (1, 0)).1 * (fderiv ℝ Ψ y (0, 1)).2 -
          (fderiv ℝ Ψ y (0, 1)).1 * (fderiv ℝ Ψ y (1, 0)).2 = y.2) ∧
      (∀ g : ℝ × ℝ → ℝ≥0∞,
        ∫⁻ x in Ψ.target, g x = ∫⁻ y in Ψ.source, ENNReal.ofReal |y.2| * g (Ψ y)) ∧
      (∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g →
        ∫⁻ x in Ψ.target, g x =
          ∫⁻ s in Ioo (-δ) δ, ∫⁻ ξ in Ioo (p₀ - δ) (p₀ + δ),
            ENNReal.ofReal |ξ| * g (Ψ (s, ξ))) ∧
      δ ≤ |p₀| ∧
      Measure.map (fun ξ : ℝ => |ξ|)
          ((volume.restrict (Ioo (p₀ - δ) (p₀ + δ))).withDensity fun ξ => ENNReal.ofReal |ξ|) =
        (volume.restrict (Ioo (|p₀| - δ) (|p₀| + δ))).withDensity (fun r => ENNReal.ofReal r) ∧
      Measure.map FiniteMetricGraph.positiveSpeedOf
          ((volume.restrict (Ioo (|p₀| - δ) (|p₀| + δ))).withDensity fun r => ENNReal.ofReal r) =
        FiniteMetricGraph.speedFluxMeasure.restrict
          (Subtype.val ⁻¹' Ioo (|p₀| - δ) (|p₀| + δ)) := by
  classical
  -- the sign of the branch
  set σ : ℝ := if 0 < p₀ then 1 else -1 with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by
    by_cases h : 0 < p₀
    · left; simp [hσdef, h]
    · right; simp [hσdef, h]
  have hσp : σ * p₀ = |p₀| := by
    by_cases h : 0 < p₀
    · simp [hσdef, h, abs_of_pos h]
    · have h' : p₀ < 0 := lt_of_le_of_ne (not_lt.mp h) hp₀
      simp [hσdef, h, abs_of_neg h']
  have hσσ : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have habs : 0 < |p₀| := abs_pos.mpr hp₀
  -- constants of the box
  set c := V.extension e a with hc
  set κ := p₀ ^ 2 / 8 with hκdef
  have hκ : 0 < κ := by have := pow_pos habs 2; rw [sq_abs] at this; positivity
  obtain ⟨r, hr, hdom, hVr⟩ : ∃ r : ℝ, 0 < r ∧ Icc (a - r) (a + r) ⊆ V.domain e ∧
      ∀ y ∈ Icc (a - r) (a + r), V.extension e y ≤ c + κ := by
    obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.mp (V.domain_isOpen e) a ha
    obtain ⟨ε₂, hε₂, hcont⟩ := Metric.continuousAt_iff.mp
      (V.extension_continuousAt_of_mem ha) κ hκ
    refine ⟨min ε₁ ε₂ / 2, by positivity, fun y hy => hball ?_, fun y hy => ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2, min_le_left ε₁ ε₂]
    · have hy' : dist y a < ε₂ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hy.1, hy.2, min_le_right ε₁ ε₂]
      have := hcont hy'
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.2]
  set m := 2 * κ with hmdef
  have hm : 0 < m := by positivity
  set Eb := c + 2 * κ with hEbdef
  have hgap : ∀ y ∈ Icc (a - r) (a + r), m ≤ 2 * (Eb - V.extension e y) := by
    intro y hy; have := hVr y hy; linarith
  have hr0 : 0 ≤ r := hr.le
  set x₀ : ℝ × ℝ := (a, p₀) with hx₀def
  have hHx₀ : V.hamiltonian e x₀.1 x₀.2 = c + 4 * κ := by
    simp only [hx₀def, hamiltonian, hc, hκdef]; ring
  have hx₀ : x₀ ∈ region V e a r σ c Eb := by
    refine ⟨⟨by simp [hx₀def]; linarith, by simp [hx₀def]; linarith⟩, ?_, ?_, ?_⟩
    · rw [hHx₀]; linarith
    · rw [hHx₀]; linarith
    · simp only [hx₀def]; rw [hσp]; exact habs
  -- the Lipschitz neighbourhood (for uniqueness)
  obtain ⟨K, sL, hsL, hLip⟩ := V.exists_lipschitzOnWith_edgeVectorField (e := e) (x := x₀) ha
  set W := region V e a r σ c Eb ∩ interior sL with hWdef
  have hW : IsOpen W := (isOpen_region hdom σ c Eb).inter isOpen_interior
  have hx₀W : x₀ ∈ W := ⟨hx₀, mem_interior_iff_mem_nhds.mpr hsL⟩
  -- the chart and its derivative
  set χ := chart V e a r m σ c with hχdef
  have hχd : ∀ x ∈ region V e a r σ c Eb, HasFDerivAt χ
      (chartDeriv (V := V) (e := e) (a := a) (r := r) (m := m) σ c x) x :=
    fun x hx => hasFDerivAt_chart hr0 hm hdom hgap hx
  have hχ2 : ∀ x ∈ region V e a r σ c Eb, (χ x).2 ≠ 0 := by
    intro x hx
    simp only [hχdef, chart]
    refine mul_ne_zero (by rcases hσ with h | h <;> rw [h] <;> norm_num) ?_
    apply ne_of_gt; apply Real.sqrt_pos.mpr; linarith [hx.2.2.1]
  have hdet : ∀ x ∈ region V e a r σ c Eb,
      (chartDeriv (V := V) (e := e) (a := a) (r := r) (m := m) σ c x).det ≠ 0 := by
    intro x hx
    rw [det_chartDeriv hr0 hgap hσ hx]
    exact inv_ne_zero (hχ2 x hx)
  let Leq : ∀ x ∈ region V e a r σ c Eb, (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := fun x hx =>
    ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero
      (chartDeriv (V := V) (e := e) (a := a) (r := r) (m := m) σ c x) (hdet x hx)
  have hLeq : ∀ x (hx : x ∈ region V e a r σ c Eb),
      ((Leq x hx : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : ℝ × ℝ →L[ℝ] ℝ × ℝ) =
        chartDeriv (V := V) (e := e) (a := a) (r := r) (m := m) σ c x := fun x hx => by
    simp [Leq]
  have hχLeq : ∀ x (hx : x ∈ region V e a r σ c Eb),
      HasFDerivAt χ ((Leq x hx : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : ℝ × ℝ →L[ℝ] ℝ × ℝ) x :=
    fun x hx => by rw [hLeq x hx]; exact hχd x hx
  -- the inverse function theorem
  let Φ₀ := (contDiffAt_chart hr0 hm hdom hgap hx₀).toOpenPartialHomeomorph χ
    (hχLeq x₀ hx₀) one_ne_zero
  let Φ₁ := Φ₀.restrOpen W hW
  have hΦ₁coe : ∀ x, Φ₁ x = χ x := fun x => rfl
  have hΦ₁src : Φ₁.source ⊆ W := fun x hx => hx.2
  have hχx₀ : χ x₀ = (0, p₀) := by
    simp only [hχdef, chart, travel, hx₀def, intervalIntegral.integral_same, mul_zero]
    congr 1
    have : 2 * (V.hamiltonian e a p₀ - c) = p₀ ^ 2 := by
      simp only [hamiltonian, hc]; ring
    rw [this, Real.sqrt_sq_eq_abs, ← hσp, ← mul_assoc, hσσ, one_mul]
  have hx₀src : x₀ ∈ Φ₁.source :=
    ⟨(contDiffAt_chart hr0 hm hdom hgap hx₀).mem_toOpenPartialHomeomorph_source
      (hχLeq x₀ hx₀) one_ne_zero, hx₀W⟩
  have htgt : (0, p₀) ∈ Φ₁.target := by
    rw [← hχx₀, ← hΦ₁coe]; exact Φ₁.map_source hx₀src
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp Φ₁.open_target _ htgt
  set B := Ioo (-δ) δ ×ˢ Ioo (p₀ - δ) (p₀ + δ) with hBdef
  have hBopen : IsOpen B := isOpen_Ioo.prod isOpen_Ioo
  have hBm : MeasurableSet B := hBopen.measurableSet
  have hBsub : B ⊆ Φ₁.target := by
    intro y hy
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  let Ψ := Φ₁.symm.restrOpen B hBopen
  have hΨsrc : Ψ.source = B := by
    change Φ₁.symm.source ∩ B = B
    rw [OpenPartialHomeomorph.symm_source]
    exact inter_eq_right.mpr hBsub
  have hΨcoe : ∀ y, Ψ y = Φ₁.symm y := fun y => rfl
  have hΨsymm : ∀ x, Ψ.symm x = χ x := fun x => rfl
  -- basic facts on the box
  have hΨmem : ∀ y ∈ B, Ψ y ∈ Φ₁.source := fun y hy => Φ₁.map_target (hBsub hy)
  have hΨreg : ∀ y ∈ B, Ψ y ∈ region V e a r σ c Eb := fun y hy => (hΦ₁src (hΨmem y hy)).1
  have hχΨ : ∀ y ∈ B, χ (Ψ y) = y := fun y hy => Φ₁.right_inv (hBsub hy)
  have hΨtgt : ∀ x ∈ Ψ.target, x ∈ W := by
    intro x hx
    have h1 : Ψ.symm x ∈ B := hΨsrc ▸ Ψ.map_target hx
    have h2 : Ψ (Ψ.symm x) = x := Ψ.right_inv hx
    rw [← h2]
    exact hΦ₁src (hΨmem _ h1)
  -- the derivative of `Ψ`
  have hΨd : ∀ y (hy : y ∈ B), HasFDerivAt Ψ
      (((Leq (Ψ y) (hΨreg y hy)).symm : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : ℝ × ℝ →L[ℝ] ℝ × ℝ) y :=
    fun y hy => Φ₁.hasFDerivAt_symm (hBsub hy) (hχLeq _ (hΨreg y hy))
  have hΨfd : ∀ y (hy : y ∈ B), fderiv ℝ Ψ y =
      (((Leq (Ψ y) (hΨreg y hy)).symm : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : ℝ × ℝ →L[ℝ] ℝ × ℝ) :=
    fun y hy => (hΨd y hy).fderiv
  have hdetΨ : ∀ y ∈ B, (fderiv ℝ Ψ y).det = y.2 := by
    intro y hy
    rw [hΨfd y hy, ContinuousLinearEquiv.det_coe_symm, hLeq _ (hΨreg y hy),
      det_chartDeriv hr0 hgap hσ (hΨreg y hy), inv_inv]
    change (χ (Ψ y)).2 = y.2
    rw [hχΨ y hy]
  have hflow : ∀ y ∈ B, HasDerivAt (fun s => Ψ (s, y.2)) (V.edgeVectorField e (Ψ y)) y.1 := by
    intro y hy
    have hline : HasDerivAt (fun s : ℝ => (s, y.2)) ((1 : ℝ), (0 : ℝ)) y.1 :=
      (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2)
    have h := (hΨd y hy).comp_hasDerivAt y.1 hline
    refine h.congr_deriv ?_
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_eq]
    change ((1 : ℝ), (0 : ℝ)) = ((Leq (Ψ y) (hΨreg y hy) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
      ℝ × ℝ →L[ℝ] ℝ × ℝ) (V.edgeVectorField e (Ψ y))
    rw [hLeq _ (hΨreg y hy), chartDeriv_field hr0 hgap hσ (hΨreg y hy)]
  have hinit : ∀ ξ ∈ Ioo (p₀ - δ) (p₀ + δ), Ψ (0, ξ) = (a, ξ) := by
    intro ξ hξ
    have hy : ((0 : ℝ), ξ) ∈ B := ⟨⟨by linarith, hδ⟩, hξ⟩
    have h := hχΨ _ hy
    have hreg := hΨreg _ hy
    set x := Ψ (0, ξ) with hxdef
    have h1 : σ * travel V e a r m (V.hamiltonian e x.1 x.2) x.1 = 0 := congrArg Prod.fst h
    have h2 : σ * Real.sqrt (2 * (V.hamiltonian e x.1 x.2 - c)) = ξ := congrArg Prod.snd h
    have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
    have hxa : x.1 = a := eq_of_travel_eq_zero hr0 hm hdom
      ((mul_eq_zero.mp h1).resolve_left hσ0)
    have hsq : 2 * (V.hamiltonian e x.1 x.2 - c) = (σ * x.2) ^ 2 := by
      simp only [hamiltonian, hc, hxa]
      rcases hσ with h | h <;> rw [h] <;> ring
    rw [hsq, Real.sqrt_sq hreg.2.2.2.le, ← mul_assoc, hσσ, one_mul] at h2
    exact Prod.ext hxa h2
  have hcov : ∀ g : ℝ × ℝ → ℝ≥0∞,
      ∫⁻ x in Ψ.target, g x = ∫⁻ y in Ψ.source, ENNReal.ofReal |y.2| * g (Ψ y) := by
    intro g
    rw [← Ψ.image_source_eq_target, hΨsrc]
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hBm
      (fun y hy => (hΨd y hy).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
      (hΨsrc ▸ Ψ.injOn) g]
    refine setLIntegral_congr_fun hBm (fun y hy => ?_)
    rw [hdetΨ y hy]
  have hsignB : ∀ y ∈ B, 0 < p₀ * y.2 := by
    intro y hy
    have h := hχΨ y hy
    have hR : 0 < Real.sqrt (2 * (V.hamiltonian e (Ψ y).1 (Ψ y).2 - c)) := by
      apply Real.sqrt_pos.mpr; linarith [(hΨreg y hy).2.2.1]
    have hy2 : y.2 = σ * Real.sqrt (2 * (V.hamiltonian e (Ψ y).1 (Ψ y).2 - c)) :=
      calc y.2 = (χ (Ψ y)).2 := by rw [h]
        _ = _ := rfl
    have hp : p₀ = σ * |p₀| := by rw [← hσp, ← mul_assoc, hσσ, one_mul]
    rw [hy2, hp]
    have : σ * |p₀| * (σ * Real.sqrt (2 * (V.hamiltonian e (Ψ y).1 (Ψ y).2 - c))) =
        (σ * σ) * (|p₀| * Real.sqrt (2 * (V.hamiltonian e (Ψ y).1 (Ψ y).2 - c))) := by ring
    rw [this, hσσ, one_mul]
    exact mul_pos habs hR
  have hδp : δ ≤ |p₀| := by
    by_contra hlt
    rw [not_le] at hlt
    have h0 : ((0 : ℝ), (0 : ℝ)) ∈ B := by
      refine ⟨⟨by linarith, hδ⟩, ?_, ?_⟩ <;>
        linarith [neg_abs_le p₀, le_abs_self p₀]
    have := hsignB _ h0
    simp at this
  refine ⟨δ, hδ, Ψ, hΨsrc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hδp,
    map_abs_transverse hδ hδp, map_positiveSpeedOf_speedInterval measurableSet_Ioo
      (fun r hr => lt_of_le_of_lt (by linarith) hr.1)⟩
  · intro y hy; rw [hΨsrc] at hy; exact hsignB y hy
  · intro x hx
    exact hdom (Ioo_subset_Icc_self (hΨtgt x hx).1.1)
  · exact hinit
  · intro y hy; rw [hΨsrc] at hy; exact hflow y hy
  · -- uniqueness of the solution through `(a, ξ)` inside the flow box
    intro ξ hξ γ hγ0 hγ t ht
    have hsub : Ψ.target ⊆ sL := fun x hx => interior_subset (hΨtgt x hx).2
    have hΨcurve : ∀ s ∈ Ioo (-δ) δ, HasDerivAt (fun s => Ψ (s, ξ))
        (V.edgeVectorField e (Ψ (s, ξ))) s ∧ Ψ (s, ξ) ∈ Ψ.target := by
      intro s hs
      have hy : (s, ξ) ∈ B := ⟨hs, hξ⟩
      exact ⟨hflow (s, ξ) hy, Ψ.map_source (hΨsrc ▸ hy)⟩
    have h0 : γ 0 = Ψ (0, ξ) := by rw [hγ0, hinit ξ hξ]
    exact V.edge_integralCurve_unique_on_Ioo (hLip.mono hsub) ⟨by linarith, hδ⟩
      (fun s hs => hγ s hs) hΨcurve h0 ht
  · -- `Ψ` is `C¹`
    intro y hy
    rw [hΨsrc] at hy
    have hcd : ContDiffAt ℝ 1 Φ₁ (Φ₁.symm y) :=
      contDiffAt_chart hr0 hm hdom hgap (hΨreg y hy)
    exact (Φ₁.contDiffAt_symm (hBsub hy) (hχLeq _ (hΨreg y hy)) hcd).contDiffWithinAt
  · -- its inverse is `C¹`
    intro x hx
    exact (contDiffAt_chart hr0 hm hdom hgap (hΨtgt x hx).1).contDiffWithinAt
  · intro y hy; rw [hΨsrc] at hy; exact hdetΨ y hy
  · intro y hy; rw [hΨsrc] at hy; rw [← det_eq_basis]; exact hdetΨ y hy
  · exact hcov
  · intro g hg
    rw [hcov g, hΨsrc, hBdef, Measure.volume_eq_prod, setLIntegral_prod]
    have hcont : ContinuousOn Ψ B := fun y hy => (hΨd y hy).continuousAt.continuousWithinAt
    have hΨm : AEMeasurable Ψ ((volume.prod volume).restrict B) := by
      rw [← Measure.volume_eq_prod]; exact hcont.aemeasurable hBm
    exact ((ENNReal.measurable_ofReal.comp (measurable_snd.abs)).aemeasurable).mul
      (hg.comp_aemeasurable hΨm)

/-- **Lemma VI.1 (local flux form).**  Let `η = (e, a)` be an edge-end, `a` its coordinate, and
let `p₀ ≠ 0`.  There is a flow box `B = (-δ, δ) × (p₀ - δ, p₀ + δ)` around `(0, p₀)` and an open
partial homeomorphism `Ψ` with source `B` such that:

* **`Ψ` is the flow-box map** `Ψ(s, ξ) = φ_s^{(e)}(a, ξ)`: `Ψ(0, ξ) = (a, ξ)`, and `s ↦ Ψ(s, ξ)`
  solves the edge Hamilton equations `q̇ = p`, `ṗ = -Ṽ_e'(q)` of the chosen `C²` extension on
  `(-δ, δ)`; it is the unique solution through `(a, ξ)` that stays in the flow box;
* **`Ψ` is a `C¹` diffeomorphism onto its open image** `Ψ.target = Ψ '' B`: `Ψ` is `C¹` on `B`
  and its inverse `Ψ.symm` is `C¹` on `Ψ.target`;
* **`Ψ^*(dq ∧ dp) = ξ ds ∧ dξ`**: `(dq ∧ dp)(∂_s Ψ, ∂_ξ Ψ) = ξ`, i.e. `det DΨ(s, ξ) = ξ`;
* **the positive Liouville measure pulls back to `|ξ| ds dξ`**:
  `∫_{Ψ(B)} f dq dp = ∫_B f(Ψ(s, ξ)) |ξ| ds dξ` for every `f ≥ 0`, and, for measurable `f`, as
  the iterated integral `∫ ds ∫ |ξ| dξ`, so the transverse boundary measure is `|ξ| dξ`;
* **the transverse boundary measure `|ξ| dξ` is `r dr` in speed coordinates**: `ξ` has the sign
  of `p₀` on the box (so `δ ≤ |p₀|` and `r = |ξ| = sign(p₀) ξ`), and the image of
  `|ξ| dξ` on `(p₀ - δ, p₀ + δ)` under `ξ ↦ |ξ|` is `r dr` on the speed interval
  `(|p₀| - δ, |p₀| + δ)`, which is the restriction to that interval of the boundary speed
  measure `speedFluxMeasure` of Definition III.6.

The box lies over the extension domain of the edge (`x.1 ∈ V.domain e`), where the extension of
the paper's proof lives; for `s` of the outward sign it leaves the physical edge. -/
theorem local_flux_form (η : Γ.EdgeEnd) {p₀ : ℝ} (hp₀ : p₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Ψ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      Ψ.source = Ioo (-δ) δ ×ˢ Ioo (p₀ - δ) (p₀ + δ) ∧
      (∀ y ∈ Ψ.source, 0 < p₀ * y.2) ∧
      (∀ x ∈ Ψ.target, x.1 ∈ V.domain η.1) ∧
      (∀ ξ ∈ Ioo (p₀ - δ) (p₀ + δ), Ψ (0, ξ) = (η.coordinate, ξ)) ∧
      (∀ y ∈ Ψ.source, HasDerivAt (fun s => Ψ (s, y.2)) (V.edgeVectorField η.1 (Ψ y)) y.1) ∧
      (∀ ξ ∈ Ioo (p₀ - δ) (p₀ + δ), ∀ γ : ℝ → ℝ × ℝ, γ 0 = (η.coordinate, ξ) →
        (∀ t ∈ Ioo (-δ) δ, HasDerivAt γ (V.edgeVectorField η.1 (γ t)) t ∧ γ t ∈ Ψ.target) →
        ∀ t ∈ Ioo (-δ) δ, γ t = Ψ (t, ξ)) ∧
      ContDiffOn ℝ 1 Ψ Ψ.source ∧ ContDiffOn ℝ 1 Ψ.symm Ψ.target ∧
      (∀ y ∈ Ψ.source, (fderiv ℝ Ψ y).det = y.2) ∧
      (∀ y ∈ Ψ.source,
        (fderiv ℝ Ψ y (1, 0)).1 * (fderiv ℝ Ψ y (0, 1)).2 -
          (fderiv ℝ Ψ y (0, 1)).1 * (fderiv ℝ Ψ y (1, 0)).2 = y.2) ∧
      (∀ g : ℝ × ℝ → ℝ≥0∞,
        ∫⁻ x in Ψ.target, g x = ∫⁻ y in Ψ.source, ENNReal.ofReal |y.2| * g (Ψ y)) ∧
      (∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g →
        ∫⁻ x in Ψ.target, g x =
          ∫⁻ s in Ioo (-δ) δ, ∫⁻ ξ in Ioo (p₀ - δ) (p₀ + δ),
            ENNReal.ofReal |ξ| * g (Ψ (s, ξ))) ∧
      δ ≤ |p₀| ∧
      Measure.map (fun ξ : ℝ => |ξ|)
          ((volume.restrict (Ioo (p₀ - δ) (p₀ + δ))).withDensity fun ξ => ENNReal.ofReal |ξ|) =
        (volume.restrict (Ioo (|p₀| - δ) (|p₀| + δ))).withDensity (fun r => ENNReal.ofReal r) ∧
      Measure.map FiniteMetricGraph.positiveSpeedOf
          ((volume.restrict (Ioo (|p₀| - δ) (|p₀| + δ))).withDensity fun r => ENNReal.ofReal r) =
        FiniteMetricGraph.speedFluxMeasure.restrict
          (Subtype.val ⁻¹' Ioo (|p₀| - δ) (|p₀| + δ)) :=
  V.local_flux_form_of_mem_domain η.1
    (V.closedEdge_subset_domain η.1 (Γ.edgeEnd_coordinate_mem_closedEdge η)) hp₀

end MechanicalPotential

end HamiltonianMetricGraphs
