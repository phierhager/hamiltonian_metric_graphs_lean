/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Corollary VI.6: reversibility of the global scattered evolution.
-/

import HamiltonianMetricGraphs.FlowGroup
import HamiltonianMetricGraphs.QuotientReversal

/-!
# Reversibility of the scattered evolution (Corollary VI.6)

A reversible scattering law is its own time reversal: the paper's condition
`S⁻¹ = ρ̃ ∘ S ∘ ρ̃` says exactly `S (ρ̃⁻¹ β) = ρ̃ (S⁻¹ β)`, which is
`IsTimeReversal S S` (`isTimeReversal_self_of_isReversible`).

The backward flow was *defined* using the canonical time reversal `S* = ρ̃ ∘ S⁻¹ ∘ ρ̃`.
`flow_of_neg_eq` shows that any other time reversal computes the same backward flow — both are
inverses of the forward flow, which is injective — so in the reversible case the backward flow may
be computed with `S` itself.  Corollary VI.6,

`ρ ∘ Φ_t = Φ_{-t} ∘ ρ`,

is then immediate from the definition of the flow and `ρ² = id`: the reversal map conjugates the
forward evolution into the backward one.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-- **A reversible scattering law is its own time reversal.**  This is the paper's Definition
III.4 read as the relation `IsTimeReversal`. -/
theorem isTimeReversal_self_of_isReversible
    (hS : S.toEnergyPreservingScattering.IsReversible) :
    BorelEnergyPreservingScattering.IsTimeReversal V S S := by
  intro v β
  have h := congrArg (fun e : Γ.OutgoingBoundary v ≃ Γ.IncomingBoundary v => e β) (hS v)
  change (S.map v).symm β =
    (Γ.incomingMomentumReversal v).symm ((S.map v) ((Γ.incomingMomentumReversal v).symm β)) at h
  rw [h, (Γ.incomingMomentumReversal v).apply_symm_apply]

section Flow

variable [Nonempty Γ.Edge]

/-- **The backward flow does not depend on the chosen time reversal.**  For any time reversal `T`
of `S`, conjugating the forward flow of `T` by the reversal map computes the flow of `S` at the
negative time.  Both sides are inverses of the injective map `Φ⁺_{-t}`. -/
theorem flow_of_neg_eq {T : BorelEnergyPreservingScattering V}
    (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T)
    (hTS : BorelEnergyPreservingScattering.IsTimeReversal V T S)
    (z : RegularScatteringPhaseSpace (V := V) S) {t : ℝ} (ht : t < 0) :
    flow V S z t =
      reverseRegular hTS (forwardFlow V T (reverseRegular hST z) (-t)) := by
  set u : ℝ := -t with hu
  have hu0 : 0 < u := by rw [hu]; linarith
  set A : RegularScatteringPhaseSpace (V := V) S :=
    reverseRegular hTS (forwardFlow V T (reverseRegular hST z) u) with hA
  -- `A` is a preimage of `z` under `Φ⁺_u`
  have hAz : forwardFlow V S A u = z := by
    rw [hA, forwardFlow_reverseRegular_forwardFlow hTS _ hu0.le hu0.le le_rfl, sub_self,
      forwardFlow_zero, reverseRegular_reverseRegular]
  -- so is `flow z t`
  have hflowz : forwardFlow V S (flow V S z t) u = z := by
    have h := flow_flow_neg_self V S z t
    rwa [flow_of_nonneg V S _ (by linarith : (0 : ℝ) ≤ -t)] at h
  -- and `Φ⁺_u` is injective
  have hinj : Function.Injective (fun w : RegularScatteringPhaseSpace (V := V) S =>
      forwardFlow V S w u) := by
    have hb := flow_bijective V S u
    have heq : (fun w : RegularScatteringPhaseSpace (V := V) S => flow V S w u) =
        fun w => forwardFlow V S w u := by
      funext w; exact flow_of_nonneg V S w hu0.le
    rw [heq] at hb
    exact hb.1
  exact hinj (hflowz.trans hAz.symm)

/-- On the regular sector, the reversal map of the time-reversal relation `IsTimeReversal S S`
coincides with the quotient momentum reversal of Lemma IV.6. -/
theorem reverseRegular_eq_quotientMomentumReversal
    (hS : S.toEnergyPreservingScattering.IsReversible)
    (z : RegularScatteringPhaseSpace (V := V) S) :
    reverseRegular (isTimeReversal_self_of_isReversible V S hS) z =
      regularQuotientMomentumReversal V S hS z := by
  apply Subtype.ext
  refine Quotient.inductionOn' z.1 ?_
  intro x
  rfl

/-- **Corollary VI.6 (reversibility of the global evolution).**  If the scattering structure is
reversible, the quotient momentum reversal `ρ` of Lemma IV.6 conjugates the scattered evolution
into its time reverse:

`ρ ∘ Φ_t = Φ_{-t} ∘ ρ`   for every `t ∈ ℝ`.

The proof is the definition of the flow: for negative times the flow *is* the forward flow of a
time reversal conjugated by `ρ`, and by `flow_of_neg_eq` the time reversal may be taken to be `S`
itself, since `S` is reversible. -/
theorem quotientMomentumReversal_flow (hS : S.toEnergyPreservingScattering.IsReversible)
    (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ) :
    regularQuotientMomentumReversal V S hS (flow V S z t) =
      flow V S (regularQuotientMomentumReversal V S hS z) (-t) := by
  set hSS := isTimeReversal_self_of_isReversible V S hS with hSSdef
  -- abbreviate the reversal map and record its two characterisations
  have hrev : ∀ w : RegularScatteringPhaseSpace (V := V) S,
      reverseRegular hSS w = regularQuotientMomentumReversal V S hS w :=
    fun w => reverseRegular_eq_quotientMomentumReversal V S hS w
  have hinv : ∀ w : RegularScatteringPhaseSpace (V := V) S,
      reverseRegular hSS (reverseRegular hSS w) = w :=
    fun w => reverseRegular_reverseRegular hSS hSS w
  rcases lt_trichotomy t 0 with ht | ht | ht
  · -- negative time: the flow is the conjugated forward flow
    rw [flow_of_neg_eq V S hSS hSS z ht, hrev, hrev,
      regularQuotientMomentumReversal_involutive V S hS,
      flow_of_nonneg V S _ (by linarith : (0 : ℝ) ≤ -t)]
  · rw [ht, neg_zero, flow_zero, flow_zero]
  · -- positive time: apply the negative-time case at `-t` to `ρ z`
    have hneg := flow_of_neg_eq V S hSS hSS (regularQuotientMomentumReversal V S hS z)
      (by linarith : -t < 0)
    rw [neg_neg] at hneg
    rw [hneg, hrev, hrev, regularQuotientMomentumReversal_involutive V S hS,
      flow_of_nonneg V S z ht.le]

end Flow

end MechanicalPotential

end HamiltonianMetricGraphs
