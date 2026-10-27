/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Theorem VI.5: the global deterministic scattered evolution
-/

import HamiltonianMetricGraphs.FlowReversal
import HamiltonianMetricGraphs.ShortTime

/-!
# The global deterministic scattered evolution

This module packages Theorem VI.5: for a finite metric graph, an edgewise `C²` potential and
deterministic energy-preserving Borel scattering laws, the maps `(Φ_t)_{t ∈ ℝ}` form a
**one-parameter group of bijections of the regular quotient phase space** which **preserves the
energy**, is **bimeasurable**, **preserves the quotient Liouville measure**, and is **reversed by
the momentum reversal** when the scattering structure is reversible:

* `Φ_0 = id`, `Φ_{s+t} = Φ_t ∘ Φ_s`, `Φ_t⁻¹ = Φ_{-t}`   (identity (3) of the paper),
* `H ∘ Φ_t = H`                                          (identity (4)),
* `Φ_t` and `Φ_t⁻¹` are Borel                            (Lemma VI.4),
* `m (Φ_t⁻¹ A) = m (A)`                                  (Lemma VI.3),
* `ρ ∘ Φ_t = Φ_{-t} ∘ ρ` for reversible `S`              (Corollary VI.6).

The trajectory itself is characterized by Proposition V.5: between impacts it solves the edge
Hamilton equations (`FlightState.trajectory_hasDerivAt`), at an impact it jumps by the prescribed
scattering law (`FlightState.trajectory_at_impact`), and its impacts are locally finite
(`impactSet_locally_finite`, Lemma V.3).
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V) [Nonempty Γ.Edge]

/-- **Theorem VI.5 (group and energy part).**  The scattered evolution is a one-parameter group of
energy-preserving bijections of the regular quotient phase space. -/
theorem globalDeterministicScatteredEvolution :
    (∀ z : RegularScatteringPhaseSpace (V := V) S, flow V S z 0 = z) ∧
    (∀ (z : RegularScatteringPhaseSpace (V := V) S) (s t : ℝ),
      flow V S (flow V S z s) t = flow V S z (s + t)) ∧
    (∀ (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ),
      flow V S (flow V S z t) (-t) = z) ∧
    (∀ t : ℝ, Function.Bijective
      (fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z t)) ∧
    (∀ (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ),
      quotientHamiltonian (V := V) S (flow V S z t).1 =
        quotientHamiltonian (V := V) S z.1) :=
  ⟨flow_zero V S, flow_flow V S, flow_flow_neg_self V S, flow_bijective V S,
    quotientHamiltonian_flow V S⟩

/-- The scattered evolution as a one-parameter group of permutations: `Φ` is a monoid homomorphism
from the additive reals (written multiplicatively) to the permutation group of the regular
quotient phase space. -/
noncomputable def flowHom :
    Multiplicative ℝ →* Equiv.Perm (RegularScatteringPhaseSpace (V := V) S) where
  toFun t := (flowEquiv V S (Multiplicative.toAdd t)).symm
  map_one' := by
    refine Equiv.ext fun z => ?_
    show flow V S z (-(0 : ℝ)) = z
    rw [neg_zero, flow_zero]
  map_mul' s t := by
    refine Equiv.ext fun z => ?_
    show flow V S z (-(Multiplicative.toAdd s + Multiplicative.toAdd t)) =
      flow V S (flow V S z (-(Multiplicative.toAdd t))) (-(Multiplicative.toAdd s))
    rw [flow_flow]
    congr 1
    ring

@[simp] theorem flowHom_apply (t : ℝ) (z : RegularScatteringPhaseSpace (V := V) S) :
    flowHom V S (Multiplicative.ofAdd t) z = flow V S z (-t) := rfl

/-- **Theorem VI.5 (measure part).**  `Φ_t` is a Borel automorphism of the regular quotient sector
which preserves the quotient Liouville measure: Lemma VI.4 and Lemma VI.3. -/
theorem globalDeterministicScatteredEvolution_measure :
    (∀ t : ℝ, Measurable (fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z t)) ∧
    (∀ (t : ℝ) (B : Set (RegularScatteringPhaseSpace (V := V) S)), MeasurableSet B →
      MeasurableSet ((fun z => flow V S z t) ⁻¹' B) ∧
        MeasurableSet ((fun z => flow V S z t) '' B)) ∧
    (∀ (t : ℝ) (B : Set (RegularScatteringPhaseSpace (V := V) S)), MeasurableSet B →
      regularLiouville V S ((fun z => flow V S z t) ⁻¹' B) = regularLiouville V S B) :=
  ⟨fun t => V.measurable_flow S t,
    fun t _ hB => ⟨(V.measurable_flow S t) hB, V.measurableSet_image_flow S t hB⟩,
    fun t _ hB => V.measure_preimage_flow S t hB⟩

/-- **Theorem VI.5 (measure part), packaged as measure preservation.** -/
theorem globalDeterministicScatteredEvolution_measurePreserving (t : ℝ) :
    MeasureTheory.MeasurePreserving
      (fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z t)
      (regularLiouville V S) (regularLiouville V S) :=
  V.measurePreserving_flow S t

/-- **Reversibility (Corollary VI.6) in the packaged form.** -/
theorem globalDeterministicScatteredEvolution_reversible
    (hS : S.toEnergyPreservingScattering.IsReversible) :
    ∀ (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ),
      regularQuotientMomentumReversal V S hS (flow V S z t) =
        flow V S (regularQuotientMomentumReversal V S hS z) (-t) :=
  quotientMomentumReversal_flow V S hS

end MechanicalPotential

end HamiltonianMetricGraphs
