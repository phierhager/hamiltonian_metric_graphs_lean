/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.1: the local flux form `dq dp = dq dE / |p| = du dE = du (r dr)`.
-/

import HamiltonianMetricGraphs.EdgeLiouville

/-!
# Energy-time coordinates on an edge

Lemma VI.1 of the paper computes the Liouville measure in a flow box transverse to a boundary
section: `dq ∧ dp` pulls back to `ξ ds ∧ dξ`, so that the transverse boundary measure is `r dr` in
speed coordinates.  This module proves that identity by an explicit change of variables, which
needs no Liouville theorem and no differentiability of the flow — only the fact that the momentum
does not vanish, which on a compact *regular* energy window is exactly the collar estimate of
Lemma V.2.

Everything is phrased through the **speed function**

`speedAt e E q = √(2 (E - V_e(q)))`,

the positive momentum at position `q` on the energy level `E`.  The three identities are

* `lintegral_momentum_eq_energy` — `dp = dE / p` at fixed position: substituting the energy for
  the momentum, whose Jacobian is `dE/dp = p`;
* `lintegral_position_eq_time` — `dq / p = du` at fixed energy, where
  `timeAt e E q₀ q = ∫_{q₀}^q ds / speedAt e E s`
  is the time the trajectory takes from `q₀` to `q` (`hasDerivAt_timeAt`), so that the flow is a
  translation in `u`;
* `lintegral_energy_eq_speed` — `dE = r dr` on a boundary section, where `E = r²/2 + V(v)`.

Together they give `dq dp = du (r dr)`, which is the paper's flux form; combined with Tonelli this
is `lintegral_flux_form` below.  The same `dq / p = du` identity is the density
`dq / √(2(E₀ - V_e(q)))` of the invariant time measure of Proposition VII.1.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set MeasureTheory intervalIntegral
open scoped Topology ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### Images of intervals under monotone maps -/

/-- The image of an open interval under a continuous strictly monotone map. -/
theorem image_Ioo_of_strictMonoOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) (hmono : StrictMonoOn f (Icc a b)) :
    f '' Ioo a b = Ioo (f a) (f b) := by
  refine subset_antisymm ?_ (intermediate_value_Ioo hab hcont)
  rintro y ⟨x, hx, rfl⟩
  exact ⟨hmono (left_mem_Icc.mpr hab) (Ioo_subset_Icc_self hx) hx.1,
    hmono (Ioo_subset_Icc_self hx) (right_mem_Icc.mpr hab) hx.2⟩

theorem strictMonoOn_sq_half_add (c : ℝ) : StrictMonoOn (fun r : ℝ => r ^ 2 / 2 + c) (Ici 0) := by
  intro x hx y hy hxy
  have h0 : (0 : ℝ) ≤ x := hx
  have hsq : x ^ 2 < y ^ 2 := by nlinarith
  simp only
  linarith

theorem image_Ioo_sq_half_add (c : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (fun r : ℝ => r ^ 2 / 2 + c) '' Ioo a b = Ioo (a ^ 2 / 2 + c) (b ^ 2 / 2 + c) := by
  refine image_Ioo_of_strictMonoOn hab ?_ ?_
  · exact (Continuous.continuousOn (by fun_prop))
  · exact (strictMonoOn_sq_half_add c).mono (fun x hx => le_trans ha hx.1)

/-! ### The speed on an energy level -/

/-- The positive momentum at position `q` on the energy level `E`. -/
noncomputable def speedAt (e : Γ.Edge) (E q : ℝ) : ℝ := Real.sqrt (2 * (E - V.extension e q))

theorem speedAt_nonneg (e : Γ.Edge) (E q : ℝ) : 0 ≤ V.speedAt e E q := Real.sqrt_nonneg _

theorem speedAt_pos (e : Γ.Edge) {E q : ℝ} (h : V.extension e q < E) : 0 < V.speedAt e E q :=
  Real.sqrt_pos.mpr (by linarith)

theorem speedAt_sq (e : Γ.Edge) {E q : ℝ} (h : V.extension e q ≤ E) :
    (V.speedAt e E q) ^ 2 = 2 * (E - V.extension e q) :=
  Real.sq_sqrt (by linarith)

/-- On the energy level `E`, the state `(q, ε · speedAt E q)` has energy `E`. -/
theorem hamiltonian_speedAt (e : Γ.Edge) {E q ε : ℝ} (hε : ε ^ 2 = 1)
    (h : V.extension e q ≤ E) : V.hamiltonian e q (ε * V.speedAt e E q) = E := by
  unfold hamiltonian
  rw [mul_pow, hε, one_mul, V.speedAt_sq e h]
  ring

/-- The speed of a state, recovered from its energy. -/
theorem speedAt_hamiltonian (e : Γ.Edge) (q p : ℝ) :
    V.speedAt e (V.hamiltonian e q p) q = |p| := by
  unfold speedAt hamiltonian
  rw [show 2 * (p ^ 2 / 2 + V.extension e q - V.extension e q) = p ^ 2 by ring,
    Real.sqrt_sq_eq_abs]

/-- **The energy derivative of the speed**: `∂p/∂E = 1/p`.  This is the Jacobian of the
momentum-to-energy substitution. -/
theorem hasDerivAt_speedAt_energy (e : Γ.Edge) {E q : ℝ} (h : V.extension e q < E) :
    HasDerivAt (fun F : ℝ => V.speedAt e F q) (1 / V.speedAt e E q) E := by
  have hpos : 0 < 2 * (E - V.extension e q) := by linarith
  have hs : 0 < Real.sqrt (2 * (E - V.extension e q)) := Real.sqrt_pos.mpr hpos
  have hinner : HasDerivAt (fun F : ℝ => 2 * (F - V.extension e q)) 2 E := by
    simpa using ((hasDerivAt_id E).sub_const (V.extension e q)).const_mul 2
  have hd : HasDerivAt (fun F : ℝ => V.speedAt e F q)
      (2 / (2 * Real.sqrt (2 * (E - V.extension e q)))) E := hinner.sqrt (ne_of_gt hpos)
  have harith : 2 / (2 * Real.sqrt (2 * (E - V.extension e q))) = 1 / V.speedAt e E q := by
    have hne : Real.sqrt (2 * (E - V.extension e q)) ≠ 0 := ne_of_gt hs
    unfold speedAt
    field_simp
  rwa [harith] at hd

/-- **The position derivative of the speed**: `∂p/∂q = -V'(q)/p`. -/
theorem hasDerivAt_speedAt_position (e : Γ.Edge) {E q : ℝ} (hq : q ∈ V.domain e)
    (h : V.extension e q < E) :
    HasDerivAt (fun x : ℝ => V.speedAt e E x) (V.force e q / V.speedAt e E q) q := by
  have hpos : 0 < 2 * (E - V.extension e q) := by linarith
  have hs : 0 < Real.sqrt (2 * (E - V.extension e q)) := Real.sqrt_pos.mpr hpos
  have hV : HasDerivAt (V.extension e) (deriv (V.extension e) q) q :=
    ((V.extension_contDiffAt_of_mem hq).differentiableAt (by norm_num)).hasDerivAt
  have hinner : HasDerivAt (fun x : ℝ => 2 * (E - V.extension e x))
      (2 * (-deriv (V.extension e) q)) q := by
    simpa using (hV.const_sub E).const_mul 2
  have hd : HasDerivAt (fun x : ℝ => V.speedAt e E x)
      (2 * (-deriv (V.extension e) q) / (2 * Real.sqrt (2 * (E - V.extension e q)))) q :=
    hinner.sqrt (ne_of_gt hpos)
  have harith : 2 * (-deriv (V.extension e) q) / (2 * Real.sqrt (2 * (E - V.extension e q))) =
      V.force e q / V.speedAt e E q := by
    have hne : Real.sqrt (2 * (E - V.extension e q)) ≠ 0 := ne_of_gt hs
    unfold speedAt force
    field_simp
  rwa [harith] at hd

/-- The speed is continuous in the position where it is positive. -/
theorem continuousAt_speedAt (e : Γ.Edge) {E q : ℝ} (hq : q ∈ V.domain e) :
    ContinuousAt (fun x : ℝ => V.speedAt e E x) q := by
  have hV : ContinuousAt (V.extension e) q := V.extension_continuousAt_of_mem hq
  exact (Real.continuous_sqrt.continuousAt).comp (by fun_prop)

/-! ### Substituting the energy for the momentum -/

/-- The energy of a state at fixed position, as a function of the momentum. -/
noncomputable def energyOfMomentum (e : Γ.Edge) (q p : ℝ) : ℝ := V.hamiltonian e q p

theorem hasDerivAt_energyOfMomentum (e : Γ.Edge) (q p : ℝ) :
    HasDerivAt (fun x : ℝ => V.energyOfMomentum e q x) p p := by
  unfold energyOfMomentum hamiltonian
  simpa using ((hasDerivAt_pow 2 p).div_const 2).add_const (V.extension e q)

theorem strictMonoOn_energyOfMomentum (e : Γ.Edge) (q : ℝ) :
    StrictMonoOn (fun x : ℝ => V.energyOfMomentum e q x) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  unfold energyOfMomentum hamiltonian
  have h0 : (0 : ℝ) ≤ a := ha
  have : a ^ 2 < b ^ 2 := by nlinarith
  simp only
  linarith

/-- **`dp = dE / p`.**  At a fixed position, substituting the energy for a positive momentum:
the Jacobian of `p ↦ p²/2 + V(q)` is `p`, so the Liouville density `dp` becomes `dE / p`.  This is
the transverse half of the paper's flux form. -/
theorem lintegral_momentum_eq_energy (e : Γ.Edge) (q : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (f : ℝ → ℝ≥0∞) :
    ∫⁻ p in Ioo a b, f p =
      ∫⁻ E in Ioo (V.energyOfMomentum e q a) (V.energyOfMomentum e q b),
        ENNReal.ofReal (1 / V.speedAt e E q) * f (V.speedAt e E q) := by
  have hmono : StrictMonoOn (fun x : ℝ => V.energyOfMomentum e q x) (Ici (0 : ℝ)) :=
    V.strictMonoOn_energyOfMomentum e q
  have hsub : Ioo a b ⊆ Ici (0 : ℝ) := fun x hx => le_of_lt (lt_trans ha hx.1)
  have himage : (fun x : ℝ => V.energyOfMomentum e q x) '' Ioo a b =
      Ioo (V.energyOfMomentum e q a) (V.energyOfMomentum e q b) :=
    image_Ioo_sq_half_add (V.extension e q) ha.le hab
  rw [← himage,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun x hx => (V.hasDerivAt_energyOfMomentum e q x).hasDerivWithinAt)
      (hmono.injOn.mono hsub)]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun p hp => ?_)
  have hp0 : 0 < p := lt_trans ha hp.1
  have hspeed : V.speedAt e (V.energyOfMomentum e q p) q = p := by
    unfold energyOfMomentum
    rw [V.speedAt_hamiltonian e q p, abs_of_pos hp0]
  rw [hspeed, abs_of_pos hp0, ← mul_assoc, ← ENNReal.ofReal_mul hp0.le,
    show p * (1 / p) = 1 from by field_simp, ENNReal.ofReal_one, one_mul]

/-! ### Substituting the time for the position -/

/-- **The time coordinate on an energy level.**  `timeAt e E q₀ q` is the time the trajectory of
energy `E` needs to travel from `q₀` to `q`, namely `∫ ds / p`. -/
noncomputable def timeAt (e : Γ.Edge) (E q₀ q : ℝ) : ℝ := ∫ s in q₀..q, 1 / V.speedAt e E s

/-- **`du = dq / p`.**  The time coordinate has derivative `1/p`: this is the Hamilton equation
`dq/dt = p` read backwards. -/
theorem hasDerivAt_timeAt (e : Γ.Edge) {E q₀ q : ℝ} {α β : ℝ}
    (hq : q ∈ Ioo α β) (hq₀ : q₀ ∈ Ioo α β)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hpos : ∀ x ∈ Ioo α β, V.extension e x < E) :
    HasDerivAt (fun x => V.timeAt e E q₀ x) (1 / V.speedAt e E q) q := by
  have hcont : ContinuousOn (fun s => 1 / V.speedAt e E s) (Ioo α β) := by
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div continuousAt_const (V.continuousAt_speedAt e (hdom x hx)) ?_
    exact ne_of_gt (V.speedAt_pos e (hpos x hx))
  have hopen : IsOpen (Ioo α β) := isOpen_Ioo
  refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
  · exact ContinuousOn.intervalIntegrable
      (hcont.mono ((Set.ordConnected_Ioo).uIcc_subset hq₀ hq))
  · exact hcont.stronglyMeasurableAtFilter hopen q hq
  · exact (hcont q hq).continuousAt (hopen.mem_nhds hq)

/-- The time coordinate is strictly increasing along the energy level. -/
theorem strictMonoOn_timeAt (e : Γ.Edge) {E q₀ : ℝ} {α β : ℝ}
    (hq₀ : q₀ ∈ Ioo α β)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hpos : ∀ x ∈ Ioo α β, V.extension e x < E) :
    StrictMonoOn (fun x => V.timeAt e E q₀ x) (Ioo α β) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun x => 1 / V.speedAt e E x)
    (convex_Ioo α β) ?_ ?_ ?_
  · exact fun x hx => (V.hasDerivAt_timeAt e hx hq₀ hdom hpos).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    exact (V.hasDerivAt_timeAt e hx hq₀ hdom hpos).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    exact one_div_pos.mpr (V.speedAt_pos e (hpos x hx))

/-- **`dq / p = du`.**  On an energy level with nonvanishing momentum, the position integral
against the Liouville density `1/p` is the Lebesgue integral in the time coordinate. -/
theorem lintegral_position_eq_time (e : Γ.Edge) {E q₀ : ℝ} {α β : ℝ}
    (hq₀ : q₀ ∈ Ioo α β)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hpos : ∀ x ∈ Ioo α β, V.extension e x < E)
    {a b : ℝ} (hab : Ioo a b ⊆ Ioo α β) (g : ℝ → ℝ≥0∞) :
    ∫⁻ u in (fun x => V.timeAt e E q₀ x) '' Ioo a b, g u =
      ∫⁻ q in Ioo a b, ENNReal.ofReal (1 / V.speedAt e E q) * g (V.timeAt e E q₀ q) := by
  have hmono := V.strictMonoOn_timeAt e hq₀ hdom hpos
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun x hx => (V.hasDerivAt_timeAt e (hab hx) hq₀ hdom hpos).hasDerivWithinAt)
    (hmono.injOn.mono hab)]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun q hq => ?_)
  have hp : 0 < V.speedAt e E q := V.speedAt_pos e (hpos q (hab hq))
  rw [abs_of_pos (one_div_pos.mpr hp)]

/-! ### Substituting the speed for the energy on a boundary section -/

/-- **`dE = r dr`.**  On a boundary section the energy is `r²/2 + V(v)`, so the Liouville
transverse measure `dE` becomes the paper's flux measure `r dr`. -/
theorem lintegral_energy_eq_speed (c : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ E in Ioo (a ^ 2 / 2 + c) (b ^ 2 / 2 + c), g E =
      ∫⁻ r in Ioo a b, ENNReal.ofReal r * g (r ^ 2 / 2 + c) := by
  have hmono : StrictMonoOn (fun r : ℝ => r ^ 2 / 2 + c) (Ici (0 : ℝ)) :=
    strictMonoOn_sq_half_add c
  have hsub : Ioo a b ⊆ Ici (0 : ℝ) := fun x hx => le_of_lt (lt_trans ha hx.1)
  have himage : (fun r : ℝ => r ^ 2 / 2 + c) '' Ioo a b =
      Ioo (a ^ 2 / 2 + c) (b ^ 2 / 2 + c) := image_Ioo_sq_half_add c ha.le hab
  have hderiv : ∀ r : ℝ, HasDerivAt (fun x : ℝ => x ^ 2 / 2 + c) r r := by
    intro r
    simpa using ((hasDerivAt_pow 2 r).div_const 2).add_const c
  rw [← himage,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun x _ => (hderiv x).hasDerivWithinAt) (hmono.injOn.mono hsub)]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
  rw [abs_of_pos (lt_trans ha hr.1)]

/-! ### The flux form -/

/-- **Lemma VI.1 (local flux form).**  On a region of the edge cylinder where the momentum is
positive, the Liouville measure `dq dp` disintegrates over the energy as

`dq dp = dq dE / p`,

the density `1/p` being the Jacobian of the momentum-to-energy substitution.  Together with
`lintegral_position_eq_time` (`dq/p = du`) and `lintegral_energy_eq_speed` (`dE = r dr`) this is
the paper's identity `Ψ*(dq ∧ dp) = ξ ds ∧ dξ`, obtained without any appeal to Liouville's theorem
or to differentiability of the flow. -/
theorem lintegral_flux_form (e : Γ.Edge) {I : Set ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in I ×ˢ Ioo a b, f x ∂(volume : Measure (ℝ × ℝ)) =
      ∫⁻ q in I, ∫⁻ E in Ioo (V.energyOfMomentum e q a) (V.energyOfMomentum e q b),
        ENNReal.ofReal (1 / V.speedAt e E q) * f (q, V.speedAt e E q) := by
  rw [Measure.volume_eq_prod,
    setLIntegral_prod f (hf.aemeasurable.restrict)]
  exact lintegral_congr fun q => V.lintegral_momentum_eq_energy e q ha hab (fun p => f (q, p))

/-- The flux form on a single energy level: the position integral of the Liouville density `1/p`
is the Lebesgue integral in the time coordinate.  This is the density
`dq / √(2(E - V_e(q)))` of the invariant time measure of Proposition VII.1, and it says that in
the time coordinate the edge flow is a translation. -/
theorem lintegral_time_form (e : Γ.Edge) {E q₀ : ℝ} {α β : ℝ} (hq₀ : q₀ ∈ Ioo α β)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hpos : ∀ x ∈ Ioo α β, V.extension e x < E)
    {a b : ℝ} (hab : Ioo a b ⊆ Ioo α β) (h : ℝ → ℝ≥0∞) :
    ∫⁻ q in Ioo a b, ENNReal.ofReal (1 / V.speedAt e E q) * h q =
      ∫⁻ u in (fun x => V.timeAt e E q₀ x) '' Ioo a b,
        h ((fun x => V.timeAt e E q₀ x).invFunOn (Ioo a b) u) := by
  classical
  have hmono := V.strictMonoOn_timeAt e hq₀ hdom hpos
  have hinj : Set.InjOn (fun x => V.timeAt e E q₀ x) (Ioo a b) := hmono.injOn.mono hab
  rw [V.lintegral_position_eq_time e hq₀ hdom hpos hab
    (fun u => h ((fun x => V.timeAt e E q₀ x).invFunOn (Ioo a b) u))]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun q hq => ?_)
  rw [hinj.leftInvOn_invFunOn hq]

/-! ### The flow is a translation in the time coordinate -/

/-- The momentum of a state of energy `E` and positive momentum is the speed on that level. -/
theorem momentum_eq_speedAt (e : Γ.Edge) {q p E : ℝ} (hp : 0 < p)
    (hE : V.hamiltonian e q p = E) : p = V.speedAt e E q := by
  rw [← hE, V.speedAt_hamiltonian e q p, abs_of_pos hp]

/-- **The edge flow is a translation in the time coordinate.**  Along a rightward-moving solution
of the edge Hamiltonian system at energy `E`, the travel time from the initial position is exactly
the elapsed time:

`timeAt e E (γ 0).1 (γ w).1 = w`.

This is the identity that makes the time coordinate of `lintegral_time_form` a linearizing chart
for the flow: in it the dynamics is `u ↦ u + w`.  Its proof is the chain rule together with
`hasDerivAt_timeAt` and Hamilton's equation `q' = p`, the derivative of the difference being
`(1/p) · p - 1 = 0`. -/
theorem timeAt_flow (e : Γ.Edge) {E D : ℝ} (hD : 0 < D) {γ : ℝ → ℝ × ℝ} {α β : ℝ}
    (hderiv : ∀ w ∈ Icc (0 : ℝ) D, HasDerivWithinAt γ (V.edgeVectorField e (γ w)) (Icc 0 D) w)
    (henergy : ∀ w ∈ Icc (0 : ℝ) D, V.hamiltonian e (γ w).1 (γ w).2 = E)
    (hmem : ∀ w ∈ Icc (0 : ℝ) D, (γ w).1 ∈ Ioo α β)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hpos : ∀ x ∈ Ioo α β, V.extension e x < E)
    (hmom : ∀ w ∈ Icc (0 : ℝ) D, 0 < (γ w).2) :
    ∀ w ∈ Icc (0 : ℝ) D, V.timeAt e E (γ 0).1 (γ w).1 = w := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) D := ⟨le_rfl, hD.le⟩
  set q₀ : ℝ := (γ 0).1 with hq₀def
  have hq₀ : q₀ ∈ Ioo α β := hmem 0 h0
  -- the difference `timeAt ∘ γ - id` has vanishing derivative
  set f : ℝ → ℝ := fun w => V.timeAt e E q₀ (γ w).1 - w with hf
  have hfderiv : ∀ w ∈ Icc (0 : ℝ) D, HasDerivWithinAt f 0 (Icc (0 : ℝ) D) w := by
    intro w hw
    have hq : HasDerivWithinAt (fun s => (γ s).1) ((γ w).2) (Icc (0 : ℝ) D) w :=
      V.edgeIntegralCurve_hasDerivWithinAt_fst (hderiv w hw)
    have ht : HasDerivAt (fun x => V.timeAt e E q₀ x) (1 / V.speedAt e E ((γ w).1)) ((γ w).1) :=
      V.hasDerivAt_timeAt e (hmem w hw) hq₀ hdom hpos
    have hcomp : HasDerivWithinAt ((fun x => V.timeAt e E q₀ x) ∘ fun s => (γ s).1)
        (1 / V.speedAt e E ((γ w).1) * (γ w).2) (Icc (0 : ℝ) D) w :=
      ht.comp_hasDerivWithinAt w hq
    have hne : (γ w).2 ≠ 0 := ne_of_gt (hmom w hw)
    have hone : 1 / V.speedAt e E ((γ w).1) * (γ w).2 = 1 := by
      rw [← V.momentum_eq_speedAt e (hmom w hw) (henergy w hw), one_div, inv_mul_cancel₀ hne]
    rw [hone] at hcomp
    have hid : HasDerivWithinAt (fun w : ℝ => w) 1 (Icc (0 : ℝ) D) w :=
      (hasDerivAt_id w).hasDerivWithinAt
    have := hcomp.sub hid
    rwa [sub_self] at this
  -- hence it is constant, and it vanishes at `0`
  have hdiff : DifferentiableOn ℝ f (Icc (0 : ℝ) D) :=
    fun w hw => (hfderiv w hw).differentiableWithinAt
  have hconst := constant_of_derivWithin_zero hdiff (fun w hw =>
    (hfderiv w (Ico_subset_Icc_self hw)).derivWithin
      (uniqueDiffOn_Icc hD w (Ico_subset_Icc_self hw)))
  intro w hw
  have hfw := hconst w hw
  have hf0 : f 0 = 0 := by
    rw [hf]
    simp only
    rw [timeAt, intervalIntegral.integral_same, sub_zero]
  rw [hf0] at hfw
  have : V.timeAt e E q₀ (γ w).1 - w = 0 := hfw
  linarith

/-- The integrand `1/p` of the time coordinate is interval-integrable inside the region where the
momentum does not vanish. -/
theorem intervalIntegrable_one_div_speedAt (e : Γ.Edge) {E : ℝ} {α β : ℝ}
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hpos : ∀ x ∈ Ioo α β, V.extension e x < E)
    {q₀ q : ℝ} (hq₀ : q₀ ∈ Ioo α β) (hq : q ∈ Ioo α β) :
    IntervalIntegrable (fun s => 1 / V.speedAt e E s) MeasureTheory.volume q₀ q := by
  have hcont : ContinuousOn (fun s => 1 / V.speedAt e E s) (Ioo α β) := by
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div continuousAt_const (V.continuousAt_speedAt e (hdom x hx)) ?_
    exact ne_of_gt (V.speedAt_pos e (hpos x hx))
  exact ContinuousOn.intervalIntegrable
    (hcont.mono ((Set.ordConnected_Ioo).uIcc_subset hq₀ hq))

/-- **Additivity of the time coordinate** in its endpoints. -/
theorem timeAt_add (e : Γ.Edge) {E : ℝ} {α β : ℝ}
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hpos : ∀ x ∈ Ioo α β, V.extension e x < E)
    {q₀ q₁ q₂ : ℝ} (hq₀ : q₀ ∈ Ioo α β) (hq₁ : q₁ ∈ Ioo α β) (hq₂ : q₂ ∈ Ioo α β) :
    V.timeAt e E q₀ q₁ + V.timeAt e E q₁ q₂ = V.timeAt e E q₀ q₂ :=
  intervalIntegral.integral_add_adjacent_intervals
    (V.intervalIntegrable_one_div_speedAt e hdom hpos hq₀ hq₁)
    (V.intervalIntegrable_one_div_speedAt e hdom hpos hq₁ hq₂)

/-- **The flow acts by translation in the time coordinate.**  For a rightward-moving solution at
energy `E`, the time coordinate of the state at time `w` is the time coordinate of the initial
state plus `w`:

`u(Φ_w x) = u(x) + w`.

Together with `lintegral_position_eq_time` — which identifies the Liouville density `dq/p` on an
energy branch with Lebesgue measure `du` in the time coordinate — this is the invariance of the
time-parametrization measure of Proposition VII.1 along an edge: the flow is a translation and
`du` is translation invariant. -/
theorem timeAt_flow_add (e : Γ.Edge) {E D : ℝ} (hD : 0 < D) {γ : ℝ → ℝ × ℝ} {α β : ℝ} {q₀ : ℝ}
    (hderiv : ∀ w ∈ Icc (0 : ℝ) D, HasDerivWithinAt γ (V.edgeVectorField e (γ w)) (Icc 0 D) w)
    (henergy : ∀ w ∈ Icc (0 : ℝ) D, V.hamiltonian e (γ w).1 (γ w).2 = E)
    (hmem : ∀ w ∈ Icc (0 : ℝ) D, (γ w).1 ∈ Ioo α β)
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hpos : ∀ x ∈ Ioo α β, V.extension e x < E)
    (hmom : ∀ w ∈ Icc (0 : ℝ) D, 0 < (γ w).2) (hq₀ : q₀ ∈ Ioo α β) :
    ∀ w ∈ Icc (0 : ℝ) D, V.timeAt e E q₀ (γ w).1 = V.timeAt e E q₀ (γ 0).1 + w := by
  intro w hw
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) D := ⟨le_rfl, hD.le⟩
  have hflow := V.timeAt_flow e hD hderiv henergy hmem hdom hpos hmom w hw
  have hadd := V.timeAt_add e hdom hpos hq₀ (hmem 0 h0) (hmem w hw)
  rw [hflow] at hadd
  linarith

end MechanicalPotential

end HamiltonianMetricGraphs
