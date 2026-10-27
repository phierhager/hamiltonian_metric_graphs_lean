/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.WorkedExamplesBasic

/-!
# An interior barrier: an energy-dependent cycle structure (Section XI.B)

## The data

`theta ℓ hℓ` is the theta graph `Θ`: two vertices `a` (`false`) and `b` (`true`) joined by three
edges `e_i` (`i : Fin 3`; the paper's `e₁, e₂, e₃` are `0, 1, 2`) of lengths `ℓ_i`, each with its
coordinate running from `a` to `b`; so `η_i = (i, false)` is the end at `a` and `η_i' = (i, true)`
the end at `b`.

The potential (`thetaPotential`) is `V₁ = V₂ = 0` and `V₃ = B.V₃` for a `BarrierProfile`: a
function, `C²` on an open neighbourhood of `[0, ℓ₃]` (the paper says smooth; `C²` is the
regularity of `MechanicalPotential` and suffices), vanishing at both endpoints.  `IsBarrier B q h`
records the remaining printed hypotheses: `q_* = q` is the unique interior critical point of
`V₃`, and `V₃(q_*) = h > 0`.  The paper also assumes `V₃''(q_*) < 0`; this is never used, so it is
omitted (the results hold without it).  From these hypotheses, `V₃` is strictly increasing on
`[0, q_*]` and strictly decreasing on `[q_*, ℓ₃]` (`IsBarrier.strictMonoOn`,
`IsBarrier.strictAntiOn`), so `q_*` is the maximum.

The vertex laws are `F_a = (η₁ η₂ η₃)` and `F_b = (η₁' η₂' η₃')` at all speeds
(`thetaLaw`).

## Results (`example_theta`)

* `Exc = {0}` (`theta_exceptionalEnergies`);
* every `E > 0` with `E ≠ h` is shell-regular (`theta_shellRegular`), and `E = h` is not
  (`theta_not_shellRegular`);
* **above the barrier**, `E > h`: every edge is crossed, `Π_E = (η₁ η₂' η₃ η₁' η₂ η₃')`, cycle
  type `(6)`, one cycle, of period
  `T(E) = 2(ℓ₁+ℓ₂)/√(2E) + 2 ∫_0^{ℓ₃} dq / √(2(E - V₃(q)))` (`theta_above`);
* **below the barrier**, `0 < E < h`: with `q₋ < q_* < q₊` the solutions of `V₃(q±) = E`
  (which exist and are unique, `theta_exists_turning`), `κ_E(η₃) = η₃`, `κ_E(η₃') = η₃'`,
  `Π_E = (η₁ η₂' η₃)(η₂ η₃' η₁')`, cycle type `(3,3)`, two cycles, of periods
  `T₁(E) = (ℓ₁+ℓ₂)/√(2E) + 2 ∫_0^{q₋} dq / √(2(E - V₃(q)))` and
  `T₂(E) = (ℓ₁+ℓ₂)/√(2E) + 2 ∫_{q₊}^{ℓ₃} dq / √(2(E - V₃(q)))` (`theta_below`).

The divergence of the periods as `E → h` is proved in `WorkedExamplesThetaLimit.lean`.
-/

namespace HamiltonianMetricGraphs

namespace WorkedExamples

open Set FiniteMetricGraph MechanicalPotential

/-! ### The barrier profile -/

/-- A potential profile on `[0, L]`: `C²` on an open neighbourhood of `[0, L]` and vanishing at
both endpoints. -/
structure BarrierProfile (L : ℝ) where
  V₃ : ℝ → ℝ
  domain : Set ℝ
  isOpen_domain : IsOpen domain
  Icc_subset_domain : Icc 0 L ⊆ domain
  contDiffOn : ContDiffOn ℝ 2 V₃ domain
  left_eq_zero : V₃ 0 = 0
  right_eq_zero : V₃ L = 0

namespace BarrierProfile

variable {L : ℝ} (B : BarrierProfile L)

/-- **The barrier hypotheses of Sec. XI.B**: `q` is the unique critical point of `V₃` in the open
interval `(0, L)`, and `V₃(q) = h > 0`. -/
structure IsBarrier (q h : ℝ) : Prop where
  mem : q ∈ Ioo 0 L
  value : B.V₃ q = h
  pos : 0 < h
  critical_iff : ∀ x ∈ Ioo 0 L, deriv B.V₃ x = 0 ↔ x = q

theorem continuousOn_Icc : ContinuousOn B.V₃ (Icc 0 L) :=
  B.contDiffOn.continuousOn.mono B.Icc_subset_domain

theorem continuousOn_deriv : ContinuousOn (deriv B.V₃) (Ioo 0 L) :=
  (B.contDiffOn.continuousOn_deriv_of_isOpen B.isOpen_domain (by norm_num)).mono
    (Ioo_subset_Icc_self.trans B.Icc_subset_domain)

/-- A continuous function without zeros on an open interval has a constant sign there. -/
theorem sign_const {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Ioo a b))
    (h0 : ∀ x ∈ Ioo a b, f x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 < f x) ∨ (∀ x ∈ Ioo a b, f x < 0) := by
  by_contra hcon
  simp only [not_or, not_forall, not_lt] at hcon
  obtain ⟨⟨x, hx, hfx⟩, ⟨y, hy, hfy⟩⟩ := hcon
  obtain ⟨z, hz, hz0⟩ := isPreconnected_Ioo.intermediate_value hx hy hf ⟨hfx, hfy⟩
  exact h0 z hz hz0

variable {B} {q h : ℝ}

/-- `V₃` is strictly increasing on `[0, q_*]`. -/
theorem IsBarrier.strictMonoOn (hB : B.IsBarrier q h) : StrictMonoOn B.V₃ (Icc 0 q) := by
  have hq := hB.mem
  have hcont : ContinuousOn B.V₃ (Icc 0 q) :=
    B.continuousOn_Icc.mono (Icc_subset_Icc le_rfl hq.2.le)
  have hne : ∀ x ∈ Ioo 0 q, deriv B.V₃ x ≠ 0 := fun x hx h0 =>
    hx.2.ne ((hB.critical_iff x ⟨hx.1, hx.2.trans hq.2⟩).mp h0)
  have hdc : ContinuousOn (deriv B.V₃) (Ioo 0 q) :=
    B.continuousOn_deriv.mono (Ioo_subset_Ioo le_rfl hq.2.le)
  rcases sign_const hdc hne with hpos | hneg
  · exact strictMonoOn_of_deriv_pos (convex_Icc 0 q) hcont (by rwa [interior_Icc])
  · exfalso
    have hanti := strictAntiOn_of_deriv_neg (convex_Icc 0 q) hcont (by rwa [interior_Icc])
    have h1 := hanti (left_mem_Icc.2 hq.1.le) (right_mem_Icc.2 hq.1.le) hq.1
    rw [B.left_eq_zero, hB.value] at h1
    linarith [hB.pos]

/-- `V₃` is strictly decreasing on `[q_*, L]`. -/
theorem IsBarrier.strictAntiOn (hB : B.IsBarrier q h) : StrictAntiOn B.V₃ (Icc q L) := by
  have hq := hB.mem
  have hcont : ContinuousOn B.V₃ (Icc q L) :=
    B.continuousOn_Icc.mono (Icc_subset_Icc hq.1.le le_rfl)
  have hne : ∀ x ∈ Ioo q L, deriv B.V₃ x ≠ 0 := fun x hx h0 =>
    hx.1.ne' ((hB.critical_iff x ⟨hq.1.trans hx.1, hx.2⟩).mp h0)
  have hdc : ContinuousOn (deriv B.V₃) (Ioo q L) :=
    B.continuousOn_deriv.mono (Ioo_subset_Ioo hq.1.le le_rfl)
  rcases sign_const hdc hne with hpos | hneg
  · exfalso
    have hmono := strictMonoOn_of_deriv_pos (convex_Icc q L) hcont (by rwa [interior_Icc])
    have h1 := hmono (left_mem_Icc.2 hq.2.le) (right_mem_Icc.2 hq.2.le) hq.2
    rw [B.right_eq_zero, hB.value] at h1
    linarith [hB.pos]
  · exact strictAntiOn_of_deriv_neg (convex_Icc q L) hcont (by rwa [interior_Icc])

/-- `V₃ ≤ h` on `[0, L]`, with equality only at `q_*`: the critical point is the maximum. -/
theorem IsBarrier.lt_of_ne (hB : B.IsBarrier q h) {x : ℝ} (hx : x ∈ Icc 0 L) (hxq : x ≠ q) :
    B.V₃ x < h := by
  have hq := hB.mem
  rw [← hB.value]
  rcases lt_or_gt_of_ne hxq with hlt | hgt
  · exact hB.strictMonoOn ⟨hx.1, hlt.le⟩ (right_mem_Icc.2 hq.1.le) hlt
  · exact hB.strictAntiOn (left_mem_Icc.2 hq.2.le) ⟨hgt.le, hx.2⟩ hgt

theorem IsBarrier.le (hB : B.IsBarrier q h) {x : ℝ} (hx : x ∈ Icc 0 L) : B.V₃ x ≤ h := by
  by_cases hxq : x = q
  · rw [hxq, hB.value]
  · exact (hB.lt_of_ne hx hxq).le

/-- `V₃ < E` on `[0, x)` when `x ≤ q_*` and `V₃(x) = E`. -/
theorem IsBarrier.lt_left (hB : B.IsBarrier q h) {x y : ℝ} (hx : x ∈ Icc 0 q) (hy : y ∈ Icc 0 x)
    (hyx : y < x) : B.V₃ y < B.V₃ x :=
  hB.strictMonoOn ⟨hy.1, hy.2.trans hx.2⟩ hx hyx

/-- `V₃ < E` on `(x, L]` when `q_* ≤ x` and `V₃(x) = E`. -/
theorem IsBarrier.lt_right (hB : B.IsBarrier q h) {x y : ℝ} (hx : x ∈ Icc q L) (hy : y ∈ Icc x L)
    (hxy : x < y) : B.V₃ y < B.V₃ x :=
  hB.strictAntiOn hx ⟨hx.1.trans hy.1, hy.2⟩ hxy

/-- **The turning points `q₋ < q_* < q₊`** with `V₃(q±) = E` exist and are unique for
`0 < E < h`. -/
theorem IsBarrier.exists_turning (hB : B.IsBarrier q h) {E : ℝ} (hE0 : 0 < E) (hEh : E < h) :
    (∃! x, x ∈ Ioo 0 q ∧ B.V₃ x = E) ∧ (∃! x, x ∈ Ioo q L ∧ B.V₃ x = E) := by
  have hq := hB.mem
  constructor
  · obtain ⟨x, hx, hxE⟩ := intermediate_value_Ioo hq.1.le
      (B.continuousOn_Icc.mono (Icc_subset_Icc le_rfl hq.2.le))
      (show E ∈ Ioo (B.V₃ 0) (B.V₃ q) by rw [B.left_eq_zero, hB.value]; exact ⟨hE0, hEh⟩)
    refine ⟨x, ⟨hx, hxE⟩, fun y ⟨hy, hyE⟩ => ?_⟩
    exact hB.strictMonoOn.injOn (Ioo_subset_Icc_self hy) (Ioo_subset_Icc_self hx)
      (hyE.trans hxE.symm)
  · obtain ⟨x, hx, hxE⟩ := intermediate_value_Ioo' hq.2.le
      (B.continuousOn_Icc.mono (Icc_subset_Icc hq.1.le le_rfl))
      (show E ∈ Ioo (B.V₃ L) (B.V₃ q) by rw [B.right_eq_zero, hB.value]; exact ⟨hE0, hEh⟩)
    refine ⟨x, ⟨hx, hxE⟩, fun y ⟨hy, hyE⟩ => ?_⟩
    exact hB.strictAntiOn.injOn (Ioo_subset_Icc_self hy) (Ioo_subset_Icc_self hx)
      (hyE.trans hxE.symm)

end BarrierProfile

/-! ### The theta graph and its potential -/

/-- The endpoints of the theta graph: every edge runs from `a = false` to `b = true`. -/
def thetaEndpoint : Fin 3 → Bool → Bool := fun _ b => b

/-- **The theta graph** `Θ` with edge lengths `ℓ_i`. -/
abbrev theta (ℓ : Fin 3 → ℝ) (hℓ : ∀ i, 0 < ℓ i) : FiniteMetricGraph where
  Vertex := Bool
  Edge := Fin 3
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  endpoint := thetaEndpoint
  length := ℓ
  length_pos := hℓ

variable (ℓ : Fin 3 → ℝ) (hℓ : ∀ i, 0 < ℓ i) (B : BarrierProfile (ℓ 2))

instance theta_nonempty_edge : Nonempty (theta ℓ hℓ).Edge := ⟨(0 : Fin 3)⟩

/-- **The potential of Sec. XI.B**: `V₁ = V₂ = 0` and `V₃ = B.V₃`; all vertex values vanish. -/
def thetaPotential : MechanicalPotential (theta ℓ hℓ) where
  extension e := if e = 2 then B.V₃ else fun _ => 0
  domain e := if e = 2 then B.domain else univ
  domain_isOpen e := by
    by_cases h : e = 2
    · simp only [h, if_true]; exact B.isOpen_domain
    · simp only [h, if_false]; exact isOpen_univ
  closedEdge_subset_domain e := by
    by_cases h : e = 2
    · subst h; simp only [if_true]; exact B.Icc_subset_domain
    · simp only [h, if_false]; exact subset_univ _
  contDiffOn_extension e := by
    by_cases h : e = 2
    · simp only [h, if_true]; exact B.contDiffOn
    · simp only [h, if_false]; exact contDiffOn_const
  vertexValue _ := 0
  endpoint_compatible η := by
    rcases η with ⟨e, b⟩
    by_cases h : e = 2
    · subst h
      cases b
      · simp only [if_true]; exact B.left_eq_zero
      · simp only [if_true]; exact B.right_eq_zero
    · simp [h]

@[simp] theorem thetaPotential_extension_two : (thetaPotential ℓ hℓ B).extension 2 = B.V₃ := by
  simp [thetaPotential]

theorem thetaPotential_extension_of_ne {e : Fin 3} (he : e ≠ 2) (x : ℝ) :
    (thetaPotential ℓ hℓ B).extension e x = 0 := by
  simp [thetaPotential, he]

@[simp] theorem thetaPotential_vertexValue (v : Bool) :
    (thetaPotential ℓ hℓ B).vertexValue v = 0 := rfl

theorem theta_mem_allowedGerms {E : ℝ} (hE0 : 0 < E) (η : (theta ℓ hℓ).EdgeEnd) :
    η ∈ (thetaPotential ℓ hℓ B).allowedGerms E :=
  show (0 : ℝ) < E from hE0

/-- **`Exc = {0}`.** -/
theorem theta_exceptionalEnergies : (thetaPotential ℓ hℓ B).exceptionalEnergies = {0} := by
  ext E
  rw [mem_exceptionalEnergies_iff, Finset.mem_singleton]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨false, h.symm⟩⟩

variable {ℓ hℓ B} {q h : ℝ}

/-- **Every positive energy other than `h` is shell-regular.** -/
theorem theta_shellRegular (hB : B.IsBarrier q h) {E : ℝ} (hE0 : 0 < E) (hEh : E ≠ h) :
    (thetaPotential ℓ hℓ B).ShellRegular E := by
  have hexc : E ∉ (thetaPotential ℓ hℓ B).exceptionalEnergies := by
    rw [theta_exceptionalEnergies, Finset.mem_singleton]; exact hE0.ne'
  refine ((thetaPotential ℓ hℓ B).shellRegular_iff hexc).mpr ⟨?_, ?_⟩
  · intro e x hx hxE hd
    by_cases he : e = 2
    · subst he
      rw [thetaPotential_extension_two] at hxE hd
      have hxq := (hB.critical_iff x hx).mp hd
      rw [hxq, hB.value] at hxE
      exact hEh hxE.symm
    · rw [thetaPotential_extension_of_ne ℓ hℓ B he] at hxE
      exact hE0.ne hxE
  · intro e x hx hxE
    by_cases he : e = 2
    · subst he
      rw [thetaPotential_extension_two] at hxE ⊢
      rcases le_total x q with hxq | hxq
      · left
        intro s hs
        rcases eq_or_lt_of_le hs.2 with hsx | hsx
        · rw [hsx]; exact hxE
        · exact (hB.lt_left ⟨hx.1, hxq⟩ hs hsx).le.trans hxE
      · right
        intro s hs
        rcases eq_or_lt_of_le hs.1 with hsx | hsx
        · rw [← hsx]; exact hxE
        · exact (hB.lt_right ⟨hxq, hx.2⟩ hs hsx).le.trans hxE
    · left
      intro s _
      rw [thetaPotential_extension_of_ne ℓ hℓ B he]
      exact hE0.le

/-- **`E = h` is not shell-regular**: `(q_*, 0)` is an equilibrium on `e₃`. -/
theorem theta_not_shellRegular (hB : B.IsBarrier q h) :
    ¬ (thetaPotential ℓ hℓ B).ShellRegular h := by
  intro hS
  have := hS.noInteriorCriticalValue 2 q hB.mem
    (by rw [thetaPotential_extension_two]; exact hB.value)
  rw [thetaPotential_extension_two] at this
  exact this ((hB.critical_iff q hB.mem).mpr rfl)

/-! ### The retrace map -/

/-- Above the barrier every edge is crossed: `κ_E(η) = η̄`. -/
theorem theta_retrace_above (hB : B.IsBarrier q h) {E : ℝ} (hhE : h < E)
    (η : (theta ℓ hℓ).EdgeEnd) :
    (thetaPotential ℓ hℓ B).retraceEnd E η = (η.1, !η.2) := by
  have hE0 : 0 < E := hB.pos.trans hhE
  refine (thetaPotential ℓ hℓ B).retraceEnd_of_forall_lt
    (theta_shellRegular hB hE0 (ne_of_gt hhE)) (theta_mem_allowedGerms ℓ hℓ B hE0 η) ?_
  intro x hx
  by_cases he : η.1 = 2
  · rw [he, thetaPotential_extension_two]
    rw [he] at hx
    exact (hB.le hx).trans_lt hhE
  · rw [thetaPotential_extension_of_ne ℓ hℓ B he]; exact hE0

/-- Below the barrier the flights on `e₁, e₂` cross, and the flights from `η₃` and `η₃'` return:
`κ_E(η₃) = η₃`, `κ_E(η₃') = η₃'`. -/
theorem theta_retrace_below (hB : B.IsBarrier q h) {E : ℝ} (hE0 : 0 < E) (hEh : E < h)
    (η : (theta ℓ hℓ).EdgeEnd) :
    (thetaPotential ℓ hℓ B).retraceEnd E η = if η.1 = 2 then η else (η.1, !η.2) := by
  have hS := theta_shellRegular (ℓ := ℓ) (hℓ := hℓ) hB hE0 hEh.ne
  have hη := theta_mem_allowedGerms ℓ hℓ B hE0 η
  by_cases he : η.1 = 2
  · rw [if_pos he]
    refine (thetaPotential ℓ hℓ B).retraceEnd_of_exists_gt hS hη ⟨q, ?_, ?_⟩
    · rw [he]; exact Ioo_subset_Icc_self hB.mem
    · rw [he, thetaPotential_extension_two, hB.value]; exact hEh
  · rw [if_neg he]
    refine (thetaPotential ℓ hℓ B).retraceEnd_of_forall_lt hS hη fun x _ => ?_
    rw [thetaPotential_extension_of_ne ℓ hℓ B he]; exact hE0

/-! ### Flight times -/

theorem theta_flightTime_free {E : ℝ} (hS : (thetaPotential ℓ hℓ B).ShellRegular E)
    (hE0 : 0 < E) {η : (theta ℓ hℓ).EdgeEnd} (he : η.1 ≠ 2) :
    (thetaPotential ℓ hℓ B).flightTime E η = ℓ η.1 / Real.sqrt (2 * E) :=
  (thetaPotential ℓ hℓ B).flightTime_of_extension_eq_zero hS hE0
    (theta_mem_allowedGerms ℓ hℓ B hE0 η)
    (fun x _ => thetaPotential_extension_of_ne ℓ hℓ B he x)

/-- Above the barrier, both flights on `e₃` take `∫_0^{ℓ₃} dq / √(2(E - V₃(q)))`. -/
theorem theta_flightTime_above (hB : B.IsBarrier q h) {E : ℝ} (hhE : h < E) (b : Bool) :
    (thetaPotential ℓ hℓ B).flightTime E ((2 : Fin 3), b) =
      ∫ x in (0 : ℝ)..ℓ 2, 1 / Real.sqrt (2 * (E - B.V₃ x)) := by
  have hE0 : 0 < E := hB.pos.trans hhE
  have hS := theta_shellRegular (ℓ := ℓ) (hℓ := hℓ) hB hE0 (ne_of_gt hhE)
  have h := ((thetaPotential ℓ hℓ B).flightTime_eq_integral_of_crossing hS
    (theta_mem_allowedGerms ℓ hℓ B hE0 ((2 : Fin 3), b)) (fun x hx => by
      change (thetaPotential ℓ hℓ B).extension 2 x < E
      rw [thetaPotential_extension_two]
      exact (hB.le (Ioo_subset_Icc_self hx)).trans_lt hhE)).1
  rw [h]
  simp only [speedAt, thetaPotential_extension_two]

/-- Below the barrier, the flight from `η₃` turns at `q₋` and takes
`2 ∫_0^{q₋} dq / √(2(E - V₃(q)))`. -/
theorem theta_flightTime_below_left (hB : B.IsBarrier q h) {E : ℝ} (hE0 : 0 < E) (hEh : E < h)
    {qm : ℝ} (hqm : qm ∈ Ioo 0 q) (hqmE : B.V₃ qm = E) :
    (thetaPotential ℓ hℓ B).flightTime E ((2 : Fin 3), false) =
      2 * ∫ x in (0 : ℝ)..qm, 1 / Real.sqrt (2 * (E - B.V₃ x)) := by
  have hS := theta_shellRegular (ℓ := ℓ) (hℓ := hℓ) hB hE0 hEh.ne
  have hq := hB.mem
  have hqmL : qm ∈ Ioo (0 : ℝ) (ℓ 2) := ⟨hqm.1, hqm.2.trans hq.2⟩
  have h := ((thetaPotential ℓ hℓ B).flightTime_eq_two_mul_integral_of_turning hS
    (theta_mem_allowedGerms ℓ hℓ B hE0 ((2 : Fin 3), false)) (t := qm) hqmL
    (by change (thetaPotential ℓ hℓ B).extension 2 qm = E
        rw [thetaPotential_extension_two]; exact hqmE)
    (fun x hx => by
      change (thetaPotential ℓ hℓ B).extension 2 x < E
      rw [thetaPotential_extension_two, ← hqmE]
      change x ∈ uIoo 0 qm at hx
      rw [uIoo_of_le hqm.1.le] at hx
      exact hB.lt_left ⟨hqm.1.le, hqm.2.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.2)).1
  rw [h]
  change 2 * |∫ x in (0 : ℝ)..qm, 1 / (thetaPotential ℓ hℓ B).speedAt 2 E x| = _
  simp only [speedAt, thetaPotential_extension_two]
  rw [abs_of_nonneg (intervalIntegral.integral_nonneg hqm.1.le
    (fun x _ => one_div_nonneg.mpr (Real.sqrt_nonneg _)))]

/-- Below the barrier, the flight from `η₃'` turns at `q₊` and takes
`2 ∫_{q₊}^{ℓ₃} dq / √(2(E - V₃(q)))`. -/
theorem theta_flightTime_below_right (hB : B.IsBarrier q h) {E : ℝ} (hE0 : 0 < E) (hEh : E < h)
    {qp : ℝ} (hqp : qp ∈ Ioo q (ℓ 2)) (hqpE : B.V₃ qp = E) :
    (thetaPotential ℓ hℓ B).flightTime E ((2 : Fin 3), true) =
      2 * ∫ x in qp..ℓ 2, 1 / Real.sqrt (2 * (E - B.V₃ x)) := by
  have hS := theta_shellRegular (ℓ := ℓ) (hℓ := hℓ) hB hE0 hEh.ne
  have hq := hB.mem
  have hqpL : qp ∈ Ioo (0 : ℝ) (ℓ 2) := ⟨hq.1.trans hqp.1, hqp.2⟩
  have h := ((thetaPotential ℓ hℓ B).flightTime_eq_two_mul_integral_of_turning hS
    (theta_mem_allowedGerms ℓ hℓ B hE0 ((2 : Fin 3), true)) (t := qp) hqpL
    (by change (thetaPotential ℓ hℓ B).extension 2 qp = E
        rw [thetaPotential_extension_two]; exact hqpE)
    (fun x hx => by
      change (thetaPotential ℓ hℓ B).extension 2 x < E
      rw [thetaPotential_extension_two, ← hqpE]
      change x ∈ uIoo (ℓ 2) qp at hx
      rw [uIoo_of_ge hqp.2.le] at hx
      exact hB.lt_right ⟨hqp.1.le, hqp.2.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1)).1
  rw [h]
  change 2 * |∫ x in ℓ 2..qp, 1 / (thetaPotential ℓ hℓ B).speedAt 2 E x| = _
  simp only [speedAt, thetaPotential_extension_two]
  rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg (intervalIntegral.integral_nonneg
    hqp.2.le (fun x _ => one_div_nonneg.mpr (Real.sqrt_nonneg _)))]

/-! ### Length-free combinatorics -/

/-- The vertex laws `F_a = (η₁ η₂ η₃)`, `F_b = (η₁' η₂' η₃')`. -/
def thetaRoute : Fin 3 × Bool → Fin 3 × Bool := fun η => (η.1 + 1, η.2)

/-- The end step above the barrier: `Π_E = F ∘ κ_E` with `κ_E` the flip of every edge. -/
def thetaAboveStep : Fin 3 × Bool → Fin 3 × Bool := fun η => thetaRoute (η.1, !η.2)

/-- The end step below the barrier: `κ_E` fixes the ends of `e₃`. -/
def thetaBelowStep : Fin 3 × Bool → Fin 3 × Bool :=
  fun η => thetaRoute (if η.1 = 2 then η else (η.1, !η.2))

/-- The 6-cycle `(η₁ η₂' η₃ η₁' η₂ η₃')`. -/
def thetaAbovePerm : Equiv.Perm (Fin 3 × Bool) :=
  List.formPerm [(0, false), (1, true), (2, false), (0, true), (1, false), (2, true)]

/-- The product of 3-cycles `(η₁ η₂' η₃)(η₂ η₃' η₁')`. -/
def thetaBelowPerm : Equiv.Perm (Fin 3 × Bool) :=
  List.formPerm [(0, false), (1, true), (2, false)] *
    List.formPerm [(1, false), (2, true), (0, true)]

/-- The cycle `{η₁, η₂', η₃}` below the barrier. -/
def thetaCycleOne : Finset (Fin 3 × Bool) := {(0, false), (1, true), (2, false)}

/-- The cycle `{η₂, η₃', η₁'}` below the barrier. -/
def thetaCycleTwo : Finset (Fin 3 × Bool) := {(1, false), (2, true), (0, true)}

/-- The cycle map below the barrier. -/
def thetaBelowCycle (η : Fin 3 × Bool) : Finset (Fin 3 × Bool) :=
  if η ∈ thetaCycleOne then thetaCycleOne else thetaCycleTwo

theorem thetaRoute_vertex :
    ∀ η : Fin 3 × Bool, thetaEndpoint (thetaRoute η).1 (thetaRoute η).2 =
      thetaEndpoint η.1 η.2 := by decide

theorem thetaRoute_bijective : Function.Bijective thetaRoute := by decide

theorem thetaAboveStep_eq : ∀ η, thetaAboveStep η = thetaAbovePerm η := by decide
theorem thetaBelowStep_eq : ∀ η, thetaBelowStep η = thetaBelowPerm η := by decide
theorem thetaAbovePerm_cycleType : thetaAbovePerm.cycleType = {6} := by decide
theorem thetaBelowPerm_cycleType : thetaBelowPerm.cycleType = {3, 3} := by decide

theorem thetaAbove_reach :
    ∀ ζ ∈ (Finset.univ : Finset (Fin 3 × Bool)), ∃ k < 6, thetaAboveStep^[k] (0, false) = ζ := by
  decide

theorem thetaCycleOne_closed : ∀ ζ ∈ thetaCycleOne, thetaBelowStep ζ ∈ thetaCycleOne := by
  decide

theorem thetaCycleOne_reach :
    ∀ ζ ∈ thetaCycleOne, ∃ k < 3, thetaBelowStep^[k] (0, false) = ζ := by decide

theorem thetaCycleTwo_closed : ∀ ζ ∈ thetaCycleTwo, thetaBelowStep ζ ∈ thetaCycleTwo := by
  decide

theorem thetaCycleTwo_reach :
    ∀ ζ ∈ thetaCycleTwo, ∃ k < 3, thetaBelowStep^[k] (1, false) = ζ := by decide

theorem zero_mem_thetaCycleOne : ((0 : Fin 3), false) ∈ thetaCycleOne := by decide
theorem one_mem_thetaCycleTwo : ((1 : Fin 3), false) ∈ thetaCycleTwo := by decide

theorem mem_thetaBelowCycle (η : Fin 3 × Bool) : η ∈ thetaBelowCycle η := by
  revert η; decide

theorem thetaBelowCycle_of_not_mem {η : Fin 3 × Bool} (hη : η ∉ thetaCycleOne) :
    η ∈ thetaCycleTwo := by
  revert η; decide

theorem theta_image_univ_eq :
    Finset.univ.image (fun _ : Fin 3 × Bool => (Finset.univ : Finset (Fin 3 × Bool))) =
      {Finset.univ} := by decide

theorem theta_image_below_card : (Finset.univ.image thetaBelowCycle).card = 2 := by decide

/-! ### The vertex law and the end step -/

/-- The vertex laws `F_a = (η₁ η₂ η₃)` and `F_b = (η₁' η₂' η₃')`, at all speeds. -/
def thetaLaw : PermutationLaw (theta ℓ hℓ) where
  route := thetaRoute
  route_vertex := thetaRoute_vertex
  route_bijective := thetaRoute_bijective

variable (ℓ hℓ B)

/-- The Borel vertex law of the example. -/
noncomputable abbrev thetaS : BorelEnergyPreservingScattering (thetaPotential ℓ hℓ B) :=
  (thetaLaw (ℓ := ℓ) (hℓ := hℓ)).toBorelScattering (thetaPotential ℓ hℓ B)

variable {ℓ hℓ B}

theorem theta_germStep_above (hB : B.IsBarrier q h) {E : ℝ} (hhE : h < E)
    (η : (theta ℓ hℓ).EdgeEnd) :
    (thetaPotential ℓ hℓ B).germStep (thetaS ℓ hℓ B) E η = thetaAbovePerm η := by
  have hE0 : 0 < E := hB.pos.trans hhE
  rw [(thetaPotential ℓ hℓ B).germStep_permutationLaw _
    (theta_shellRegular hB hE0 (ne_of_gt hhE)) (theta_mem_allowedGerms ℓ hℓ B hE0 η),
    theta_retrace_above hB hhE]
  exact thetaAboveStep_eq η

theorem theta_germStep_below (hB : B.IsBarrier q h) {E : ℝ} (hE0 : 0 < E) (hEh : E < h)
    (η : (theta ℓ hℓ).EdgeEnd) :
    (thetaPotential ℓ hℓ B).germStep (thetaS ℓ hℓ B) E η = thetaBelowPerm η := by
  rw [(thetaPotential ℓ hℓ B).germStep_permutationLaw _
    (theta_shellRegular hB hE0 hEh.ne) (theta_mem_allowedGerms ℓ hℓ B hE0 η),
    theta_retrace_below hB hE0 hEh]
  exact thetaBelowStep_eq η

/-! ### Above the barrier -/

open Classical in
/-- **Above the barrier, `E > h`**: every edge is crossed (`κ_E(η) = η̄`),
`Π_E = (η₁ η₂' η₃ η₁' η₂ η₃')` with cycle type `(6)`, there is one cycle (one periodic orbit),
and its period is `T(E) = 2(ℓ₁+ℓ₂)/√(2E) + 2 ∫_0^{ℓ₃} dq / √(2(E - V₃(q)))`. -/
theorem theta_above (hB : B.IsBarrier q h) {E : ℝ} (hhE : h < E) :
    (∀ η, (thetaPotential ℓ hℓ B).retraceEnd E η = (η.1, !η.2)) ∧
      (∀ η, (thetaPotential ℓ hℓ B).germStep (thetaS ℓ hℓ B) E η = thetaAbovePerm η) ∧
      ((thetaPotential ℓ hℓ B).shellGermPerm (thetaS ℓ hℓ B)
        (theta_shellRegular hB (hB.pos.trans hhE) (ne_of_gt hhE))).cycleType = {6} ∧
      (thetaPotential ℓ hℓ B).germCycles (thetaS ℓ hℓ B) E = {Finset.univ} ∧
      ∀ η, (thetaPotential ℓ hℓ B).cyclePeriod (thetaS ℓ hℓ B) E η =
        2 * (ℓ 0 + ℓ 1) / Real.sqrt (2 * E) +
          2 * ∫ x in (0 : ℝ)..ℓ 2, 1 / Real.sqrt (2 * (E - B.V₃ x)) := by
  have hE0 : 0 < E := hB.pos.trans hhE
  have hS := theta_shellRegular (ℓ := ℓ) (hℓ := hℓ) hB hE0 (ne_of_gt hhE)
  have hall := theta_mem_allowedGerms ℓ hℓ B hE0
  have hstep : ∀ η, (thetaPotential ℓ hℓ B).germStep (thetaS ℓ hℓ B) E η = thetaAboveStep η :=
    fun η => by rw [theta_germStep_above hB hhE]; exact (thetaAboveStep_eq η).symm
  have hcyc : ∀ η : (theta ℓ hℓ).EdgeEnd,
      (thetaPotential ℓ hℓ B).germCycle (thetaS ℓ hℓ B) E η = Finset.univ := fun η =>
    (thetaPotential ℓ hℓ B).germCycle_eq_of_closed_of_mem _ hS hall hstep
      (η := ((0 : Fin 3), false)) Finset.univ 6 (fun _ _ => Finset.mem_univ _)
      (Finset.mem_univ _) thetaAbove_reach (Finset.mem_univ η)
  refine ⟨theta_retrace_above hB hhE, theta_germStep_above hB hhE, ?_, ?_, fun η => ?_⟩
  · rw [(thetaPotential ℓ hℓ B).cycleType_shellGermPerm_eq _ hS hall thetaAbovePerm
      (theta_germStep_above hB hhE)]
    exact thetaAbovePerm_cycleType
  · rw [(thetaPotential ℓ hℓ B).germCycles_eq_image _ hall hcyc]
    exact theta_image_univ_eq
  · rw [(thetaPotential ℓ hℓ B).cyclePeriod_eq_of_germCycle_eq _ (hcyc η)]
    change ∑ ζ : Fin 3 × Bool, (thetaPotential ℓ hℓ B).flightTime E ζ = _
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Fin.sum_univ_three]
    rw [theta_flightTime_above hB hhE true, theta_flightTime_above hB hhE false,
      theta_flightTime_free hS hE0 (η := ((0 : Fin 3), true)) (show (0 : Fin 3) ≠ 2 by decide),
      theta_flightTime_free hS hE0 (η := ((0 : Fin 3), false)) (show (0 : Fin 3) ≠ 2 by decide),
      theta_flightTime_free hS hE0 (η := ((1 : Fin 3), true)) (show (1 : Fin 3) ≠ 2 by decide),
      theta_flightTime_free hS hE0 (η := ((1 : Fin 3), false)) (show (1 : Fin 3) ≠ 2 by decide)]
    ring

/-! ### Below the barrier -/

open Classical in
/-- **Below the barrier, `0 < E < h`**: with `q₋ < q_* < q₊` the solutions of `V₃(q±) = E`,
`κ_E(η₃) = η₃` and `κ_E(η₃') = η₃'`, `Π_E = (η₁ η₂' η₃)(η₂ η₃' η₁')` with cycle type `(3,3)`,
there are two cycles (two periodic orbits), with periods
`T₁(E) = (ℓ₁+ℓ₂)/√(2E) + 2 ∫_0^{q₋} dq / √(2(E - V₃(q)))` (the cycle of `η₁`) and
`T₂(E) = (ℓ₁+ℓ₂)/√(2E) + 2 ∫_{q₊}^{ℓ₃} dq / √(2(E - V₃(q)))` (the cycle of `η₂`). -/
theorem theta_below (hB : B.IsBarrier q h) {E : ℝ} (hE0 : 0 < E) (hEh : E < h) {qm qp : ℝ}
    (hqm : qm ∈ Ioo 0 q) (hqmE : B.V₃ qm = E) (hqp : qp ∈ Ioo q (ℓ 2)) (hqpE : B.V₃ qp = E) :
    (thetaPotential ℓ hℓ B).retraceEnd E ((2 : Fin 3), false) = ((2 : Fin 3), false) ∧
      (thetaPotential ℓ hℓ B).retraceEnd E ((2 : Fin 3), true) = ((2 : Fin 3), true) ∧
      (∀ η, (thetaPotential ℓ hℓ B).germStep (thetaS ℓ hℓ B) E η = thetaBelowPerm η) ∧
      ((thetaPotential ℓ hℓ B).shellGermPerm (thetaS ℓ hℓ B)
        (theta_shellRegular hB hE0 hEh.ne)).cycleType = {3, 3} ∧
      (thetaPotential ℓ hℓ B).germCycle (thetaS ℓ hℓ B) E ((0 : Fin 3), false) = thetaCycleOne ∧
      (thetaPotential ℓ hℓ B).germCycle (thetaS ℓ hℓ B) E ((1 : Fin 3), false) = thetaCycleTwo ∧
      ((thetaPotential ℓ hℓ B).germCycles (thetaS ℓ hℓ B) E).card = 2 ∧
      (thetaPotential ℓ hℓ B).cyclePeriod (thetaS ℓ hℓ B) E ((0 : Fin 3), false) =
        (ℓ 0 + ℓ 1) / Real.sqrt (2 * E) +
          2 * ∫ x in (0 : ℝ)..qm, 1 / Real.sqrt (2 * (E - B.V₃ x)) ∧
      (thetaPotential ℓ hℓ B).cyclePeriod (thetaS ℓ hℓ B) E ((1 : Fin 3), false) =
        (ℓ 0 + ℓ 1) / Real.sqrt (2 * E) +
          2 * ∫ x in qp..ℓ 2, 1 / Real.sqrt (2 * (E - B.V₃ x)) := by
  have hS := theta_shellRegular (ℓ := ℓ) (hℓ := hℓ) hB hE0 hEh.ne
  have hall := theta_mem_allowedGerms ℓ hℓ B hE0
  have hstep : ∀ η, (thetaPotential ℓ hℓ B).germStep (thetaS ℓ hℓ B) E η = thetaBelowStep η :=
    fun η => by rw [theta_germStep_below hB hE0 hEh]; exact (thetaBelowStep_eq η).symm
  have hone : ∀ η ∈ (thetaCycleOne : Finset (theta ℓ hℓ).EdgeEnd),
      (thetaPotential ℓ hℓ B).germCycle (thetaS ℓ hℓ B) E η = thetaCycleOne := fun η hη =>
    (thetaPotential ℓ hℓ B).germCycle_eq_of_closed_of_mem _ hS hall hstep
      (η := ((0 : Fin 3), false)) thetaCycleOne 3 thetaCycleOne_closed zero_mem_thetaCycleOne
      thetaCycleOne_reach hη
  have htwo : ∀ η ∈ (thetaCycleTwo : Finset (theta ℓ hℓ).EdgeEnd),
      (thetaPotential ℓ hℓ B).germCycle (thetaS ℓ hℓ B) E η = thetaCycleTwo := fun η hη =>
    (thetaPotential ℓ hℓ B).germCycle_eq_of_closed_of_mem _ hS hall hstep
      (η := ((1 : Fin 3), false)) thetaCycleTwo 3 thetaCycleTwo_closed one_mem_thetaCycleTwo
      thetaCycleTwo_reach hη
  have hcyc : ∀ η : (theta ℓ hℓ).EdgeEnd,
      (thetaPotential ℓ hℓ B).germCycle (thetaS ℓ hℓ B) E η = thetaBelowCycle η := by
    intro η
    unfold thetaBelowCycle
    split_ifs with h1
    · exact hone η h1
    · exact htwo η (thetaBelowCycle_of_not_mem h1)
  have hret := theta_retrace_below (ℓ := ℓ) (hℓ := hℓ) (B := B) hB hE0 hEh
  have hft0 := theta_flightTime_free hS hE0 (η := ((0 : Fin 3), false))
    (show (0 : Fin 3) ≠ 2 by decide)
  have hft0' := theta_flightTime_free hS hE0 (η := ((0 : Fin 3), true))
    (show (0 : Fin 3) ≠ 2 by decide)
  have hft1 := theta_flightTime_free hS hE0 (η := ((1 : Fin 3), false))
    (show (1 : Fin 3) ≠ 2 by decide)
  have hft1' := theta_flightTime_free hS hE0 (η := ((1 : Fin 3), true))
    (show (1 : Fin 3) ≠ 2 by decide)
  refine ⟨by rw [hret]; rfl, by rw [hret]; rfl, theta_germStep_below hB hE0 hEh, ?_,
    hone _ zero_mem_thetaCycleOne, htwo _ one_mem_thetaCycleTwo, ?_, ?_, ?_⟩
  · rw [(thetaPotential ℓ hℓ B).cycleType_shellGermPerm_eq _ hS hall thetaBelowPerm
      (theta_germStep_below hB hE0 hEh)]
    exact thetaBelowPerm_cycleType
  · rw [(thetaPotential ℓ hℓ B).germCycles_eq_image _ hall hcyc]
    exact theta_image_below_card
  · refine ((thetaPotential ℓ hℓ B).cyclePeriod_eq_of_germCycle_eq _
      (hone _ zero_mem_thetaCycleOne)).trans ?_
    change ∑ ζ ∈ ({(0, false), (1, true), (2, false)} : Finset (Fin 3 × Bool)),
      (thetaPotential ℓ hℓ B).flightTime E ζ = _
    rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide), hft0, hft1',
      theta_flightTime_below_left hB hE0 hEh hqm hqmE]
    ring
  · refine ((thetaPotential ℓ hℓ B).cyclePeriod_eq_of_germCycle_eq _
      (htwo _ one_mem_thetaCycleTwo)).trans ?_
    change ∑ ζ ∈ ({(1, false), (2, true), (0, true)} : Finset (Fin 3 × Bool)),
      (thetaPotential ℓ hℓ B).flightTime E ζ = _
    rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide), hft1, hft0',
      theta_flightTime_below_right hB hE0 hEh hqp hqpE]
    ring

end WorkedExamples

end HamiltonianMetricGraphs
