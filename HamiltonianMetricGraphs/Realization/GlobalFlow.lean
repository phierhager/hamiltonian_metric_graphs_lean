/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import Mathlib

/-!
# Global existence for bounded `C¹` vector fields

The microscopic model needs exactly one input from ODE theory: a time-independent vector
field that is `C¹` and whose norm is bounded by a constant `L` on the whole phase space
has an integral curve on *any* prescribed time interval `[0, T]`, starting from *any*
initial point.

The proof is a single application of the Picard-Lindelöf theorem in the form
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`.  The trick that makes one
application suffice (rather than a continuation argument) is that the global bound `‖f‖ ≤ L`
lets us take the spatial radius `a := L * T` right away: the Picard-Lindelöf side condition
`L * max (tmax - t₀) (t₀ - tmin) ≤ a - r` then reads `L * T ≤ L * T` for `r = 0`.

The Lipschitz constant on the ball `closedBall z₀ (L * T)` is obtained from
`ContDiffOn.exists_lipschitzOnWith`, which needs the ball to be *compact*; for that reason the
ambient space is assumed finite-dimensional.  This is harmless for the intended application,
where `E = (ℝ × ℝ) × (ℝ × ℝ)` is the phase space of a planar mechanical system.

## Main results

* `HamiltonianMetricGraphs.exists_integralCurve_Icc`: existence on `[0, T]` for a bounded `C¹`
  vector field on a finite-dimensional Banach space.
* `HamiltonianMetricGraphs.exists_integralCurve_Icc_plane`: the same statement specialised to
  the concrete phase space `(ℝ × ℝ) × (ℝ × ℝ)`.
-/

namespace HamiltonianMetricGraphs

open Set

open scoped NNReal

/-- A time-independent `C¹` vector field with a global norm bound has an integral curve on
every interval `[0, T]` through every initial point. -/
theorem exists_integralCurve_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] {f : E → E} {L : ℝ} (hf : ContDiff ℝ 1 f)
    (hL : 0 ≤ L) (hbound : ∀ z, ‖f z‖ ≤ L) (z₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ α : ℝ → E, α 0 = z₀ ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt α (f (α t)) (Icc (0 : ℝ) T) t := by
  have hLT : (0 : ℝ) ≤ L * T := mul_nonneg hL hT
  -- The spatial radius on which the Picard-Lindelöf hypotheses are checked.
  set a : ℝ≥0 := (L * T).toNNReal
  have hacoe : (a : ℝ) = L * T := Real.coe_toNNReal _ hLT
  -- A `C¹` function is Lipschitz on the (compact, convex) ball of radius `a`.
  obtain ⟨K, hK⟩ :=
    (hf.contDiffOn (s := Metric.closedBall z₀ (a : ℝ))).exists_lipschitzOnWith
      one_ne_zero (convex_closedBall z₀ (a : ℝ)) (isCompact_closedBall z₀ (a : ℝ))
  -- The Picard-Lindelöf hypotheses on the time interval `[0, T]`.
  have hpl : IsPicardLindelof (fun _ : ℝ ↦ f) (tmin := 0) (tmax := T)
      ⟨0, by simp [hT]⟩ z₀ a 0 L.toNNReal K := by
    refine IsPicardLindelof.of_time_independent (fun x _ ↦ ?_) hK ?_
    · simpa [Real.coe_toNNReal _ hL] using hbound x
    · simp [hacoe, Real.coe_toNNReal _ hL, max_eq_left hT]
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, fun t ht ↦ hα t ht⟩

/-- The same statement for the concrete phase space of a planar mechanical system. -/
theorem exists_integralCurve_Icc_plane {f : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ)} {L : ℝ}
    (hf : ContDiff ℝ 1 f) (hL : 0 ≤ L) (hbound : ∀ z, ‖f z‖ ≤ L)
    (z₀ : (ℝ × ℝ) × (ℝ × ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    ∃ α : ℝ → (ℝ × ℝ) × (ℝ × ℝ), α 0 = z₀ ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt α (f (α t)) (Icc (0 : ℝ) T) t :=
  exists_integralCurve_Icc hf hL hbound z₀ hT

end HamiltonianMetricGraphs
