/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma V.1 (edge flow), as printed: uniqueness, conservation of `H_e`, and invariance of `dq dp`
for the whole time the solution stays on the edge.
-/

import HamiltonianMetricGraphs.EdgeLiouville
import HamiltonianMetricGraphs.FirstHit
import HamiltonianMetricGraphs.EdgeFlight

/-!
# Lemma V.1 (`lem:edge-flow`) as printed

The paper (Sec. V) fixes a `C²` extension `Ṽ_e` of the edge potential to an open interval
`I_e ⊇ [0, ℓ_e]` (here `V.extension e` on `V.domain e`) and lets `φ_t^{(e)}` be the local flow of
`q̇ = p`, `ṗ = -Ṽ_e'(q)`.  Lemma V.1 then reads:

> On each edge cylinder, solutions of the edge equations are unique up to the first time at which
> `q` reaches `0` or `ℓ_e`.  Along such a solution, `H_e` and the measure `dq_e dp` are preserved.

The earlier Liouville statement `measure_image_edgeFlow` (`EdgeLiouville.lean`) is restricted to a
short time step `Δ ≤ 1/(3M)` and to an abstract family of solutions.  This module removes that
restriction.

## Objects

* `IsEdgeCylinderSolution V e T x γ`: `γ` solves the edge equations on `[0, T]` (one-sided
  derivative at the ends), starts at `x`, and stays in the **closed** edge cylinder
  `[0, ℓ_e] × ℝ` throughout `[0, T]`.  Every solution considered "up to the first time at which `q`
  reaches `0` or `ℓ_e`" is of this kind (`isEdgeCylinderSolution_of_edgeFirstHit`).
* `edgeCylinderDomain V e T`: the states admitting such a solution on `[0, T]`.
* `edgeCylinderFlow V e T`: the time-`T` edge flow `φ_T` on that domain (well defined by
  uniqueness, `edgeCylinderFlow_eq`).

## Results

* `eqOn_of_isEdgeCylinderSolution'`: uniqueness up to the boundary hit;
* `hamiltonian_eq_of_isEdgeCylinderSolution`: conservation of `H_e`;
* `edgeCylinderFlow_add`: the semigroup property `φ_b ∘ φ_a = φ_{a+b}`;
* `volume_image_edgeCylinderFlow`: **Liouville for every `t ≥ 0`** — for every measurable set `A`
  of states whose solution stays on the edge during `[0, t]`, `vol(φ_t(A)) = vol(A)`;
* `volume_image_edgeCylinderFlow_neg`: the same for negative times, via momentum reversal;
* `edge_flow_lemma`: the three conclusions of Lemma V.1 packaged together.

## Method

The time-`t` map is the composite of `N` maps of step `Δ = t/N ≤ 1/(3M)`.  Locally near a point
`x₀` the energies are below `H(x₀) + 1`, so all orbits stay in one compact momentum box; there
each step is differentiable with derivative of determinant `1`
(`hasFDerivWithinAt_of_edgeSolutionFamily`, the Wronskian identity).  The chain rule gives the
same for `φ_t`, injectivity comes from backward uniqueness, and the change-of-variables formula
`lintegral_abs_det_fderiv_eq_addHaar_image` concludes.  No measurability of intermediate images
is needed.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter Metric MeasureTheory
open scoped Topology NNReal ENNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### Solutions on the closed edge cylinder -/

/-- **A solution of the edge equations on the edge cylinder.**  `γ` starts at `x`, solves
`q̇ = p`, `ṗ = -Ṽ_e'(q)` on `[0, T]` (with one-sided derivatives at the ends of the interval) and
its position stays in the closed edge `[0, ℓ_e]` throughout `[0, T]`. -/
def IsEdgeCylinderSolution (e : Γ.Edge) (T : ℝ) (x : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) : Prop :=
  γ 0 = x ∧ ∀ s ∈ Icc (0 : ℝ) T, (γ s).1 ∈ Icc (0 : ℝ) (Γ.length e) ∧
    HasDerivWithinAt γ (V.edgeVectorField e (γ s)) (Icc (0 : ℝ) T) s

variable {V}

/-- **Conservation of `H_e`** along a solution on the edge cylinder. -/
theorem hamiltonian_eq_of_isEdgeCylinderSolution {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ}
    {γ : ℝ → ℝ × ℝ} (h : V.IsEdgeCylinderSolution e T x γ) :
    ∀ s ∈ Icc (0 : ℝ) T, V.hamiltonian e (γ s).1 (γ s).2 = V.hamiltonian e x.1 x.2 := by
  have henergy := V.hamiltonian_eq_of_hamiltonEquations_within
    (q := fun s => (γ s).1) (p := fun s => (γ s).2) (a := 0) (b := T)
    (fun s hs => V.closedEdge_subset_domain e (h.2 s hs).1)
    (fun s hs => V.edgeIntegralCurve_hasDerivWithinAt_fst (h.2 s hs).2)
    (fun s hs => by
      simpa [force] using V.edgeIntegralCurve_hasDerivWithinAt_snd (h.2 s hs).2)
  intro s hs
  simpa [h.1] using henergy s hs

/-- An energy bound confines a solution on the edge cylinder to a compact momentum box. -/
theorem mem_box_of_isEdgeCylinderSolution {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ}
    {γ : ℝ → ℝ × ℝ} (h : V.IsEdgeCylinderSolution e T x γ) {C U : ℝ}
    (hC : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), C ≤ V.extension e q)
    (hU : V.hamiltonian e x.1 x.2 ≤ U) :
    ∀ s ∈ Icc (0 : ℝ) T, γ s ∈ closedEdgeMomentumBox e (Real.sqrt (2 * (U - C))) := by
  intro s hs
  have hq := (h.2 s hs).1
  have hbox := V.mem_closedEdgeMomentumBox_of_hamiltonian_le (p := (γ s).2) hq (hC _ hq)
    ((V.hamiltonian_eq_of_isEdgeCylinderSolution h s hs).le.trans hU)
  simpa using hbox

/-- Restricting a solution to a shorter time interval. -/
theorem IsEdgeCylinderSolution.mono {e : Γ.Edge} {T r : ℝ} {x : ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (h : V.IsEdgeCylinderSolution e T x γ) (hr : r ≤ T) : V.IsEdgeCylinderSolution e r x γ :=
  ⟨h.1, fun s hs => ⟨(h.2 s ⟨hs.1, hs.2.trans hr⟩).1,
    (h.2 s ⟨hs.1, hs.2.trans hr⟩).2.mono (Icc_subset_Icc_right hr)⟩⟩

/-- Restarting a solution at a later time `a`. -/
theorem IsEdgeCylinderSolution.shift {e : Γ.Edge} {T a : ℝ} {x : ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (h : V.IsEdgeCylinderSolution e T x γ) (ha : 0 ≤ a) :
    V.IsEdgeCylinderSolution e (T - a) (γ a) (fun r => γ (a + r)) := by
  refine ⟨by simp, fun s hs => ?_⟩
  have hs' : a + s ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨(h.2 _ hs').1, ?_⟩
  have hmaps : MapsTo (fun r => a + r) (Icc (0 : ℝ) (T - a)) (Icc (0 : ℝ) T) :=
    fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hadd : HasDerivWithinAt (fun r : ℝ => a + r) 1 (Icc (0 : ℝ) (T - a)) s :=
    ((hasDerivAt_id s).const_add a).hasDerivWithinAt
  have hcomp := (h.2 _ hs').2.scomp s hadd hmaps
  simpa [Function.comp_def] using hcomp

/-- **Uniqueness** of solutions on the edge cylinder (common time interval). -/
theorem eqOn_of_isEdgeCylinderSolution {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ}
    {γ γ' : ℝ → ℝ × ℝ} (h : V.IsEdgeCylinderSolution e T x γ)
    (h' : V.IsEdgeCylinderSolution e T x γ') : EqOn γ γ' (Icc (0 : ℝ) T) := by
  obtain ⟨C, hC⟩ := V.exists_lowerBound_extension_closedEdge e
  set P := Real.sqrt (2 * (V.hamiltonian e x.1 x.2 - C))
  obtain ⟨K, hK⟩ := V.exists_lipschitzOnWith_edgeVectorField_closedMomentumBox e P
  have hb := V.mem_box_of_isEdgeCylinderSolution h hC le_rfl
  have hb' := V.mem_box_of_isEdgeCylinderSolution h' hC le_rfl
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => V.edgeVectorField e)
    (s := fun _ => closedEdgeMomentumBox e P) (K := K) (fun _ _ => hK)
    (fun s hs => (h.2 s hs).2.continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_mem_Icc hs (h.2 s (Ico_subset_Icc_self hs)).2)
    (fun s hs => hb s (Ico_subset_Icc_self hs))
    (fun s hs => (h'.2 s hs).2.continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_mem_Icc hs (h'.2 s (Ico_subset_Icc_self hs)).2)
    (fun s hs => hb' s (Ico_subset_Icc_self hs))
    (by rw [h.1, h'.1])

/-- **Uniqueness up to the boundary hit.**  Two solutions from the same state, each staying on
the edge for its own time, agree as long as both do. -/
theorem eqOn_of_isEdgeCylinderSolution' {e : Γ.Edge} {T₁ T₂ : ℝ} {x : ℝ × ℝ}
    {γ₁ γ₂ : ℝ → ℝ × ℝ} (h₁ : V.IsEdgeCylinderSolution e T₁ x γ₁)
    (h₂ : V.IsEdgeCylinderSolution e T₂ x γ₂) : EqOn γ₁ γ₂ (Icc (0 : ℝ) (min T₁ T₂)) :=
  eqOn_of_isEdgeCylinderSolution (h₁.mono (min_le_left _ _)) (h₂.mono (min_le_right _ _))

/-- A first-hit witness — a solution followed exactly up to the first time at which `q` reaches
`0` or `ℓ_e` — is a solution on the edge cylinder, for every time up to the hit. -/
theorem isEdgeCylinderSolution_of_edgeFirstHit {e : Γ.Edge} {x : ℝ × ℝ}
    (h : V.EdgeFirstHit e x) {t : ℝ} (ht : t ≤ h.duration) :
    V.IsEdgeCylinderSolution e t x h.curve :=
  IsEdgeCylinderSolution.mono
    ⟨h.initial, fun s hs => ⟨h.physical_at s hs, h.integralCurve s hs⟩⟩ ht

/-- A physical edge segment (a flight up to some time no later than its boundary hit) is a
solution on the edge cylinder. -/
theorem isEdgeCylinderSolution_of_physicalEdgeSegment {e : Γ.Edge} {x : ℝ × ℝ}
    (h : V.PhysicalEdgeSegment e x) {t : ℝ} (ht : t ≤ h.duration) :
    V.IsEdgeCylinderSolution e t x h.curve :=
  IsEdgeCylinderSolution.mono
    ⟨h.initial, fun s hs => ⟨h.physical s hs, (h.integralCurve s hs).hasDerivWithinAt⟩⟩ ht

/-! ### The edge flow on the edge cylinder -/

variable (V)

/-- The states whose solution stays on the closed edge cylinder throughout `[0, T]`: the domain
of the time-`T` edge flow "up to the first time at which `q` reaches `0` or `ℓ_e`". -/
def edgeCylinderDomain (e : Γ.Edge) (T : ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ γ, V.IsEdgeCylinderSolution e T x γ}

/-- A chosen solution on `[0, T]` (unique on `[0, T]` by `eqOn_of_isEdgeCylinderSolution`); a
constant junk value off the domain. -/
noncomputable def edgeCylinderCurve (e : Γ.Edge) (T : ℝ) (x : ℝ × ℝ) : ℝ → ℝ × ℝ := by
  classical
  exact if h : x ∈ V.edgeCylinderDomain e T then h.choose else fun _ => x

/-- **The time-`T` edge flow** `φ_T` on `edgeCylinderDomain V e T`: the value at time `T` of the
(unique) solution on the edge cylinder.  Off the domain it returns `x`, a junk value about which
nothing is claimed. -/
noncomputable def edgeCylinderFlow (e : Γ.Edge) (T : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  V.edgeCylinderCurve e T x T

variable {V}

theorem isEdgeCylinderSolution_edgeCylinderCurve {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ V.edgeCylinderDomain e T) :
    V.IsEdgeCylinderSolution e T x (V.edgeCylinderCurve e T x) := by
  classical
  unfold edgeCylinderCurve
  rw [dif_pos hx]
  exact hx.choose_spec

theorem edgeCylinderDomain_mono {e : Γ.Edge} {T r : ℝ} (hr : r ≤ T) :
    V.edgeCylinderDomain e T ⊆ V.edgeCylinderDomain e r :=
  fun _ ⟨γ, hγ⟩ => ⟨γ, hγ.mono hr⟩

/-- **The flow is the solution**: along any solution on the edge cylinder, `φ_r(x) = γ(r)`. -/
theorem edgeCylinderFlow_eq {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (h : V.IsEdgeCylinderSolution e T x γ) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    V.edgeCylinderFlow e r x = γ r := by
  have hr' := h.mono hr.2
  have hc := isEdgeCylinderSolution_edgeCylinderCurve (V := V) ⟨γ, hr'⟩
  exact eqOn_of_isEdgeCylinderSolution hc hr' ⟨hr.1, le_rfl⟩

theorem edgeCylinderFlow_zero {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ V.edgeCylinderDomain e T) (hT : 0 ≤ T) : V.edgeCylinderFlow e 0 x = x := by
  obtain ⟨γ, hγ⟩ := hx
  rw [edgeCylinderFlow_eq hγ ⟨le_rfl, hT⟩, hγ.1]

/-- **The semigroup property** `φ_b ∘ φ_a = φ_{a+b}` on the edge cylinder. -/
theorem edgeCylinderFlow_add {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ V.edgeCylinderDomain e T) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ T) :
    V.edgeCylinderFlow e a x ∈ V.edgeCylinderDomain e (T - a) ∧
      V.edgeCylinderFlow e b (V.edgeCylinderFlow e a x) = V.edgeCylinderFlow e (a + b) x := by
  obtain ⟨γ, hγ⟩ := hx
  have hfa : V.edgeCylinderFlow e a x = γ a := edgeCylinderFlow_eq hγ ⟨ha, by linarith⟩
  have hsh := hγ.shift ha
  rw [hfa]
  refine ⟨⟨_, hsh⟩, ?_⟩
  rw [edgeCylinderFlow_eq hsh ⟨hb, by linarith⟩, edgeCylinderFlow_eq hγ ⟨by linarith, hab⟩]

/-- The flow conserves `H_e`. -/
theorem hamiltonian_edgeCylinderFlow {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ V.edgeCylinderDomain e T) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    V.hamiltonian e (V.edgeCylinderFlow e r x).1 (V.edgeCylinderFlow e r x).2 =
      V.hamiltonian e x.1 x.2 := by
  obtain ⟨γ, hγ⟩ := hx
  rw [edgeCylinderFlow_eq hγ hr]
  exact hamiltonian_eq_of_isEdgeCylinderSolution hγ r hr

/-- The chosen solutions over an energy-bounded set of initial states form a confined family of
edge solutions in the sense of `EdgeLiouville.lean`. -/
theorem edgeSolutionFamily_edgeCylinderCurve (e : Γ.Edge) {t C U : ℝ}
    (hC : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), C ≤ V.extension e q) {S : Set (ℝ × ℝ)}
    (hS : S ⊆ V.edgeCylinderDomain e t) (hU : ∀ z ∈ S, V.hamiltonian e z.1 z.2 ≤ U) :
    EdgeSolutionFamily V e (Real.sqrt (2 * (U - C))) t S (V.edgeCylinderCurve e t) where
  initial _ hz := (isEdgeCylinderSolution_edgeCylinderCurve (hS hz)).1
  ode _ hz s hs := ((isEdgeCylinderSolution_edgeCylinderCurve (hS hz)).2 s hs).2
  confined z hz s hs :=
    mem_box_of_isEdgeCylinderSolution (isEdgeCylinderSolution_edgeCylinderCurve (hS hz))
      hC (hU z hz) s hs

/-- **Injectivity** of `φ_t` on its domain (backward uniqueness). -/
theorem injOn_edgeCylinderFlow (e : Γ.Edge) {t : ℝ} (ht : 0 < t) :
    InjOn (V.edgeCylinderFlow e t) (V.edgeCylinderDomain e t) := by
  intro x hx y hy hxy
  have hEx := hamiltonian_edgeCylinderFlow hx ⟨ht.le, le_rfl⟩
  have hEy := hamiltonian_edgeCylinderFlow hy ⟨ht.le, le_rfl⟩
  have hE : V.hamiltonian e y.1 y.2 = V.hamiltonian e x.1 x.2 := by
    rw [← hEx, ← hEy, hxy]
  obtain ⟨C, hC⟩ := V.exists_lowerBound_extension_closedEdge e
  have hS : ({x, y} : Set (ℝ × ℝ)) ⊆ V.edgeCylinderDomain e t := by
    rintro _ (rfl | rfl)
    · exact hx
    · exact hy
  have hU : ∀ z ∈ ({x, y} : Set (ℝ × ℝ)),
      V.hamiltonian e z.1 z.2 ≤ V.hamiltonian e x.1 x.2 := by
    rintro _ (rfl | rfl)
    · exact le_rfl
    · exact hE.le
  exact (edgeSolutionFamily_edgeCylinderCurve e hC hS hU).injOn_apply ht
    (by simp) (by simp) hxy

/-! ### Differentiability of `φ_t` for every `t > 0` -/

/-- The energy is continuous at every state over the closed edge. -/
theorem continuousAt_hamiltonian {e : Γ.Edge} {x : ℝ × ℝ} (hx : x.1 ∈ V.domain e) :
    ContinuousAt (fun z : ℝ × ℝ => V.hamiltonian e z.1 z.2) x := by
  unfold hamiltonian
  exact ((continuous_snd.pow 2).div_const 2).continuousAt.add
    ((V.extension_continuousAt_of_mem hx).comp continuous_fst.continuousAt)

/-- **The time-`t` flow is differentiable with Jacobian determinant `1`**, for every `t > 0`, at
every point of every set of states whose solution stays on the edge during `[0, t]`. -/
theorem hasFDerivWithinAt_edgeCylinderFlow (e : Γ.Edge) {t : ℝ} (ht : 0 < t)
    {A : Set (ℝ × ℝ)} (hA : A ⊆ V.edgeCylinderDomain e t) {x₀ : ℝ × ℝ} (hx₀ : x₀ ∈ A) :
    ∃ L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), L.det = 1 ∧
      HasFDerivWithinAt (V.edgeCylinderFlow e t) L A x₀ := by
  obtain ⟨C, hC⟩ := V.exists_lowerBound_extension_closedEdge e
  obtain ⟨B, hB1, hB⟩ := V.exists_bound_forceDeriv_closedEdge e
  set M : ℝ≥0 := ⟨B, by linarith⟩ with hMdef
  have hM1 : (1 : ℝ) ≤ M := hB1
  have hMbound : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), ‖V.edgeFieldDeriv e q‖ ≤ M :=
    fun q hq => V.norm_edgeFieldDeriv_le e q hB1 (hB q hq)
  -- the number of steps
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * (M : ℝ) * t)
  have h3Mt : 0 < 3 * (M : ℝ) * t := by positivity
  have hNpos : (0 : ℝ) < N := h3Mt.trans hN
  set Δ : ℝ := t / N with hΔdef
  have hΔpos : 0 < Δ := div_pos ht hNpos
  have hΔM : Δ ≤ 1 / (3 * M) := by
    rw [hΔdef, div_le_div_iff₀ hNpos (by positivity)]
    linarith
  have hNΔ : (N : ℝ) * Δ = t := by rw [hΔdef]; field_simp
  -- localize to an energy window around `x₀`
  have hx₀D := hA hx₀
  obtain ⟨γ₀, hγ₀⟩ := hx₀D
  have hx₀dom : x₀.1 ∈ V.domain e := by
    have := (hγ₀.2 0 ⟨le_rfl, ht.le⟩).1
    rw [hγ₀.1] at this
    exact V.closedEdge_subset_domain e this
  set U : ℝ := V.hamiltonian e x₀.1 x₀.2 + 1 with hUdef
  set W : Set (ℝ × ℝ) := {z | V.hamiltonian e z.1 z.2 < U} with hWdef
  have hWnhds : W ∈ 𝓝 x₀ :=
    (continuousAt_hamiltonian hx₀dom).preimage_mem_nhds (Iio_mem_nhds (by linarith))
  set S : Set (ℝ × ℝ) := A ∩ W with hSdef
  have hSD : S ⊆ V.edgeCylinderDomain e t := fun z hz => hA hz.1
  have hx₀S : x₀ ∈ S := ⟨hx₀, show _ < U by linarith⟩
  -- induction over the steps
  have key : ∀ k : ℕ, k ≤ N → ∃ L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), L.det = 1 ∧
      HasFDerivWithinAt (V.edgeCylinderFlow e (k * Δ)) L S x₀ := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨ContinuousLinearMap.id ℝ _, ?_, ?_⟩
      · simp [ContinuousLinearMap.det]
      · refine (hasFDerivWithinAt_id x₀ S).congr (fun z hz => ?_) ?_
        · simpa using edgeCylinderFlow_zero (hSD hz) ht.le
        · simpa using edgeCylinderFlow_zero (hSD hx₀S) ht.le
    | succ k ih =>
      intro hk
      obtain ⟨L, hL, hLd⟩ := ih (by omega)
      have hkN : ((k : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ k * Δ := by positivity
      have hkΔ : (k : ℝ) * Δ + Δ ≤ t := by rw [← hNΔ]; nlinarith
      set S' : Set (ℝ × ℝ) := V.edgeCylinderFlow e (k * Δ) '' S with hS'def
      have hS'D : S' ⊆ V.edgeCylinderDomain e Δ := by
        rintro _ ⟨z, hz, rfl⟩
        exact edgeCylinderDomain_mono (by linarith)
          (edgeCylinderFlow_add (hSD hz) hk0 hΔpos.le hkΔ).1
      have hS'U : ∀ z ∈ S', V.hamiltonian e z.1 z.2 ≤ U := by
        rintro _ ⟨z, hz, rfl⟩
        rw [hamiltonian_edgeCylinderFlow (hSD hz) ⟨hk0, by linarith⟩]
        exact hz.2.le
      have hF := edgeSolutionFamily_edgeCylinderCurve e hC hS'D hS'U
      obtain ⟨L', hL', hL'd⟩ := V.hasFDerivWithinAt_of_edgeSolutionFamily hF hΔpos hM1
        hMbound hΔM (mem_image_of_mem _ hx₀S)
      have hcomp := hL'd.comp x₀ hLd (mapsTo_image _ _)
      refine ⟨L'.comp L, ?_, ?_⟩
      · change LinearMap.det ((L' : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)).comp (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))) = 1
        rw [LinearMap.det_comp]
        rw [ContinuousLinearMap.det] at hL hL'
        rw [hL, hL', one_mul]
      · have hstep : ∀ z ∈ S, V.edgeCylinderFlow e (((k + 1 : ℕ) : ℝ) * Δ) z =
            ((fun y => V.edgeCylinderCurve e Δ y Δ) ∘ V.edgeCylinderFlow e (k * Δ)) z := by
          intro z hz
          have h2 := (edgeCylinderFlow_add (hSD hz) hk0 hΔpos.le hkΔ).2
          rw [Function.comp_apply]
          change _ = V.edgeCylinderFlow e Δ (V.edgeCylinderFlow e (k * Δ) z)
          rw [h2]
          push_cast
          ring_nf
        exact hcomp.congr hstep (hstep x₀ hx₀S)
  obtain ⟨L, hL, hLd⟩ := key N le_rfl
  rw [hNΔ] at hLd
  refine ⟨L, hL, ?_⟩
  exact (hasFDerivWithinAt_inter hWnhds).mp hLd

/-! ### Liouville's theorem for the edge flow, for all times -/

/-- **Lemma V.1 (Liouville part), for every time `t ≥ 0`.**  The edge flow preserves `dq dp`: for
every measurable set `A` of states whose solution stays on the edge cylinder during `[0, t]`
(i.e. `t` does not exceed the first time at which `q` reaches `0` or `ℓ_e`, or the solution only
touches the boundary), `vol(φ_t(A)) = vol(A)`.  No smallness condition on `t` is imposed. -/
theorem volume_image_edgeCylinderFlow (e : Γ.Edge) {t : ℝ} (ht : 0 ≤ t) {A : Set (ℝ × ℝ)}
    (hA : MeasurableSet A) (hAD : A ⊆ V.edgeCylinderDomain e t) :
    volume (V.edgeCylinderFlow e t '' A) = volume A := by
  classical
  rcases eq_or_lt_of_le ht with rfl | htpos
  · have hid : EqOn (V.edgeCylinderFlow e 0) id A :=
      fun x hx => edgeCylinderFlow_zero (hAD hx) le_rfl
    rw [hid.image_eq, image_id]
  · have hderiv : ∀ x ∈ A, ∃ L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), L.det = 1 ∧
        HasFDerivWithinAt (V.edgeCylinderFlow e t) L A x :=
      fun x hx => hasFDerivWithinAt_edgeCylinderFlow e htpos hAD hx
    choose! L hLdet hLderiv using hderiv
    have hkey := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure (ℝ × ℝ)) hA
      (fun x hx => hLderiv x hx) ((injOn_edgeCylinderFlow e htpos).mono hAD)
    rw [← hkey]
    have hone : ∀ x ∈ A, ENNReal.ofReal |(L x).det| = 1 := by
      intro x hx
      rw [hLdet x hx]
      norm_num
    rw [setLIntegral_congr_fun hA hone, setLIntegral_one]

/-! ### Negative times, by momentum reversal -/

/-- Momentum reversal `(q, p) ↦ (q, -p)`, as a continuous linear map. -/
noncomputable def momentumReversal : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := pairMap (1, 0) (0, -1)

@[simp] theorem momentumReversal_apply (x : ℝ × ℝ) : momentumReversal x = (x.1, -x.2) := by
  refine Prod.ext ?_ ?_
  · change x.1 * 1 + x.2 * 0 = x.1; ring
  · change x.1 * 0 + x.2 * (-1) = -x.2; ring

theorem momentumReversal_momentumReversal (x : ℝ × ℝ) :
    momentumReversal (momentumReversal x) = x := by
  simp

/-- Momentum reversal preserves `dq dp`. -/
theorem volume_image_momentumReversal (B : Set (ℝ × ℝ)) :
    volume (momentumReversal '' B) = volume B := by
  rw [Measure.addHaar_image_continuousLinearMap]
  have hdet : LinearMap.det (momentumReversal : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) = -1 := by
    have h := pairMap_det (1, 0) (0, -1)
    rw [ContinuousLinearMap.det] at h
    rw [momentumReversal, h]
    norm_num
  rw [hdet]
  norm_num

/-- Momentum reversal composed with time reversal maps solutions of the edge equations to
solutions (one-sided form, on any pair of intervals exchanged by `s ↦ -s`). -/
theorem hasDerivWithinAt_momentumReversal_neg {e : Γ.Edge} {γ : ℝ → ℝ × ℝ} {I J : Set ℝ}
    {s : ℝ} (hγ : HasDerivWithinAt γ (V.edgeVectorField e (γ (-s))) I (-s))
    (hJ : MapsTo (fun u : ℝ => -u) J I) :
    HasDerivWithinAt (fun u => momentumReversal (γ (-u)))
      (V.edgeVectorField e (momentumReversal (γ (-s)))) J s := by
  have hneg : HasDerivWithinAt (fun u : ℝ => -u) (-1) J s := (hasDerivAt_neg s).hasDerivWithinAt
  have h1 := hγ.scomp s hneg hJ
  have h2 := momentumReversal.hasFDerivAt.comp_hasDerivWithinAt s h1
  have hval : momentumReversal ((-1 : ℝ) • V.edgeVectorField e (γ (-s))) =
      V.edgeVectorField e (momentumReversal (γ (-s))) := by
    simp [edgeVectorField]
  rw [hval] at h2
  exact h2

variable (V)

/-- A **backward** solution of the edge equations on the edge cylinder: `β` solves the edge
equations on `[-T, 0]`, ends at `x` at time `0`, and stays on the closed edge throughout. -/
def IsEdgeCylinderSolutionBack (e : Γ.Edge) (T : ℝ) (x : ℝ × ℝ) (β : ℝ → ℝ × ℝ) : Prop :=
  β 0 = x ∧ ∀ s ∈ Icc (-T) 0, (β s).1 ∈ Icc (0 : ℝ) (Γ.length e) ∧
    HasDerivWithinAt β (V.edgeVectorField e (β s)) (Icc (-T) 0) s

/-- The states whose backward solution stays on the edge cylinder throughout `[-T, 0]`. -/
def edgeCylinderDomainBack (e : Γ.Edge) (T : ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ β, V.IsEdgeCylinderSolutionBack e T x β}

/-- **The time-`(-T)` edge flow** `φ_{-T}`, defined through momentum reversal. -/
noncomputable def edgeCylinderFlowBack (e : Γ.Edge) (T : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  momentumReversal (V.edgeCylinderFlow e T (momentumReversal x))

variable {V}

/-- A backward solution, reversed in time and momentum, is a forward solution. -/
theorem isEdgeCylinderSolution_reverse {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ} {β : ℝ → ℝ × ℝ}
    (h : V.IsEdgeCylinderSolutionBack e T x β) :
    V.IsEdgeCylinderSolution e T (momentumReversal x) (fun s => momentumReversal (β (-s))) := by
  refine ⟨by simp [h.1], fun s hs => ?_⟩
  have hs' : -s ∈ Icc (-T) 0 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨by simpa using (h.2 _ hs').1, ?_⟩
  exact hasDerivWithinAt_momentumReversal_neg (h.2 _ hs').2
    (fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩)

/-- A forward solution, reversed in time and momentum, is a backward solution. -/
theorem isEdgeCylinderSolutionBack_reverse {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (h : V.IsEdgeCylinderSolution e T x γ) :
    V.IsEdgeCylinderSolutionBack e T (momentumReversal x)
      (fun s => momentumReversal (γ (-s))) := by
  refine ⟨by simp [h.1], fun s hs => ?_⟩
  have hs' : -s ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨by simpa using (h.2 _ hs').1, ?_⟩
  exact hasDerivWithinAt_momentumReversal_neg (h.2 _ hs').2
    (fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩)

/-- The backward domain is the momentum reversal of the forward one. -/
theorem mem_edgeCylinderDomainBack_iff {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ} :
    x ∈ V.edgeCylinderDomainBack e T ↔ momentumReversal x ∈ V.edgeCylinderDomain e T := by
  constructor
  · rintro ⟨β, hβ⟩
    exact ⟨_, isEdgeCylinderSolution_reverse hβ⟩
  · rintro ⟨γ, hγ⟩
    have := isEdgeCylinderSolutionBack_reverse hγ
    rw [momentumReversal_momentumReversal] at this
    exact ⟨_, this⟩

/-- **The backward flow is the backward solution**: `φ_{-r}(x) = β(-r)`. -/
theorem edgeCylinderFlowBack_eq {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ} {β : ℝ → ℝ × ℝ}
    (h : V.IsEdgeCylinderSolutionBack e T x β) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    V.edgeCylinderFlowBack e r x = β (-r) := by
  rw [edgeCylinderFlowBack, edgeCylinderFlow_eq (isEdgeCylinderSolution_reverse h) hr,
    momentumReversal_momentumReversal]

/-- **Uniqueness of backward solutions** on the edge cylinder. -/
theorem eqOn_of_isEdgeCylinderSolutionBack {e : Γ.Edge} {T : ℝ} {x : ℝ × ℝ}
    {β β' : ℝ → ℝ × ℝ} (h : V.IsEdgeCylinderSolutionBack e T x β)
    (h' : V.IsEdgeCylinderSolutionBack e T x β') : EqOn β β' (Icc (-T) 0) := by
  intro s hs
  have hs' : -s ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have := eqOn_of_isEdgeCylinderSolution (isEdgeCylinderSolution_reverse h)
    (isEdgeCylinderSolution_reverse h') hs'
  simpa using congrArg momentumReversal this

/-- **Lemma V.1 (Liouville part), for every time `-t ≤ 0`.**  For every measurable set `A` of
states whose backward solution stays on the edge cylinder during `[-t, 0]`,
`vol(φ_{-t}(A)) = vol(A)`. -/
theorem volume_image_edgeCylinderFlowBack (e : Γ.Edge) {t : ℝ} (ht : 0 ≤ t)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hAD : A ⊆ V.edgeCylinderDomainBack e t) :
    volume (V.edgeCylinderFlowBack e t '' A) = volume A := by
  have himg : V.edgeCylinderFlowBack e t '' A =
      momentumReversal '' (V.edgeCylinderFlow e t '' (momentumReversal '' A)) := by
    rw [image_image, image_image]
    rfl
  have hpre : momentumReversal '' A = momentumReversal ⁻¹' A :=
    congrFun (image_eq_preimage_of_inverse (f := momentumReversal) (g := momentumReversal)
      momentumReversal_momentumReversal momentumReversal_momentumReversal) A
  have hRA : MeasurableSet (momentumReversal '' A) := by
    rw [hpre]
    exact momentumReversal.continuous.measurable hA
  have hRAD : momentumReversal '' A ⊆ V.edgeCylinderDomain e t := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_edgeCylinderDomainBack_iff.mp (hAD hx)
  rw [himg, volume_image_momentumReversal, volume_image_edgeCylinderFlow e ht hRA hRAD,
    volume_image_momentumReversal]

/-! ### Independence of the chosen extension -/

/-- On the closed edge the force `-Ṽ_e'` does not depend on the chosen `C²` extension: two
potentials whose extensions agree on `[0, ℓ_e]` have the same force there (including at the
endpoints, where the derivative is determined by one-sided difference quotients). -/
theorem force_eq_of_eqOn_closedEdge {V V' : MechanicalPotential Γ} {e : Γ.Edge}
    (hVV' : EqOn (V.extension e) (V'.extension e) (Icc (0 : ℝ) (Γ.length e)))
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (Γ.length e)) : V.force e q = V'.force e q := by
  have hd : HasDerivAt (V.extension e) (deriv (V.extension e) q) q :=
    ((V.extension_contDiffAt_of_mem (V.closedEdge_subset_domain e hq)).differentiableAt
      (by norm_num)).hasDerivAt
  have hd' : HasDerivAt (V'.extension e) (deriv (V'.extension e) q) q :=
    ((V'.extension_contDiffAt_of_mem (V'.closedEdge_subset_domain e hq)).differentiableAt
      (by norm_num)).hasDerivAt
  have hw : HasDerivWithinAt (V'.extension e) (deriv (V.extension e) q)
      (Icc (0 : ℝ) (Γ.length e)) q :=
    hd.hasDerivWithinAt.congr (fun y hy => (hVV' hy).symm) (hVV' hq).symm
  have heq := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc (Γ.length_pos e) q hq) hw
    hd'.hasDerivWithinAt
  unfold force
  rw [heq]

/-- **Solutions on the edge cylinder do not depend on the chosen extension** of `V_e`. -/
theorem isEdgeCylinderSolution_congr {V V' : MechanicalPotential Γ} {e : Γ.Edge}
    (hVV' : EqOn (V.extension e) (V'.extension e) (Icc (0 : ℝ) (Γ.length e)))
    {T : ℝ} {x : ℝ × ℝ} {γ : ℝ → ℝ × ℝ} :
    V.IsEdgeCylinderSolution e T x γ ↔ V'.IsEdgeCylinderSolution e T x γ := by
  have hX : ∀ y : ℝ × ℝ, y.1 ∈ Icc (0 : ℝ) (Γ.length e) →
      V.edgeVectorField e y = V'.edgeVectorField e y := by
    intro y hy
    simp only [edgeVectorField, force_eq_of_eqOn_closedEdge hVV' hy]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun s hs => ⟨(h s hs).1, by rw [← hX _ (h s hs).1]; exact (h s hs).2⟩⟩
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun s hs => ⟨(h s hs).1, by rw [hX _ (h s hs).1]; exact (h s hs).2⟩⟩

/-! ### Lemma V.1 -/

/-- **Lemma V.1 (Edge flow), as printed.**  On each edge cylinder:

1. *uniqueness up to the boundary hit*: two solutions of the edge equations from the same state,
   each followed for as long as it stays on the closed edge, agree on the common time interval
   (forward and backward in time);
2. *conservation of `H_e`* along such a solution;
3. the edge flow `φ_t` (`edgeCylinderFlow`, resp. `edgeCylinderFlowBack` for `-t`) evaluates such
   a solution, `φ_s(x) = γ(s)`;
4. *Liouville*: `φ_t` preserves `dq dp` for **every** `t ≥ 0` — and `φ_{-t}` for every `t ≥ 0` —
   on every measurable set of states whose solution stays on the edge during the time interval.

Independence of the chosen extension is `isEdgeCylinderSolution_congr`. -/
theorem edge_flow_lemma (e : Γ.Edge) :
    (∀ (x : ℝ × ℝ) (T₁ T₂ : ℝ) (γ₁ γ₂ : ℝ → ℝ × ℝ),
      V.IsEdgeCylinderSolution e T₁ x γ₁ → V.IsEdgeCylinderSolution e T₂ x γ₂ →
        EqOn γ₁ γ₂ (Icc (0 : ℝ) (min T₁ T₂))) ∧
    (∀ (x : ℝ × ℝ) (T : ℝ) (β₁ β₂ : ℝ → ℝ × ℝ),
      V.IsEdgeCylinderSolutionBack e T x β₁ → V.IsEdgeCylinderSolutionBack e T x β₂ →
        EqOn β₁ β₂ (Icc (-T) 0)) ∧
    (∀ (x : ℝ × ℝ) (T : ℝ) (γ : ℝ → ℝ × ℝ), V.IsEdgeCylinderSolution e T x γ →
      ∀ s ∈ Icc (0 : ℝ) T, V.hamiltonian e (γ s).1 (γ s).2 = V.hamiltonian e x.1 x.2) ∧
    (∀ (x : ℝ × ℝ) (T : ℝ) (γ : ℝ → ℝ × ℝ), V.IsEdgeCylinderSolution e T x γ →
      ∀ s ∈ Icc (0 : ℝ) T, V.edgeCylinderFlow e s x = γ s) ∧
    (∀ (x : ℝ × ℝ) (T : ℝ) (β : ℝ → ℝ × ℝ), V.IsEdgeCylinderSolutionBack e T x β →
      ∀ s ∈ Icc (0 : ℝ) T, V.edgeCylinderFlowBack e s x = β (-s)) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ A : Set (ℝ × ℝ), MeasurableSet A → A ⊆ V.edgeCylinderDomain e t →
      volume (V.edgeCylinderFlow e t '' A) = volume A) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ A : Set (ℝ × ℝ), MeasurableSet A →
      A ⊆ V.edgeCylinderDomainBack e t →
        volume (V.edgeCylinderFlowBack e t '' A) = volume A) :=
  ⟨fun _ _ _ _ _ h₁ h₂ => eqOn_of_isEdgeCylinderSolution' h₁ h₂,
    fun _ _ _ _ h₁ h₂ => eqOn_of_isEdgeCylinderSolutionBack h₁ h₂,
    fun _ _ _ h => hamiltonian_eq_of_isEdgeCylinderSolution h,
    fun _ _ _ h _ hs => edgeCylinderFlow_eq h hs,
    fun _ _ _ h _ hs => edgeCylinderFlowBack_eq h hs,
    fun _ ht _ hA hAD => volume_image_edgeCylinderFlow e ht hA hAD,
    fun _ ht _ hA hAD => volume_image_edgeCylinderFlowBack e ht hA hAD⟩

end MechanicalPotential

end HamiltonianMetricGraphs
