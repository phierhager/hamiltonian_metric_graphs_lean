/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.PhaseSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Standard Borel structure transport

The scattering-quotient measurability results (Lemma IV.2 saturation, Lemma IV.4 charts as
`MeasurableEquiv`s) rest on the phase spaces being **standard Borel**: for a measurable bijection
between standard Borel spaces the inverse is automatically measurable (Lusin--Souslin), and injective
measurable images are measurable.  Mathlib provides `StandardBorelSpace` for `ℝ`, products, and Borel
subsets, but not for the Sigma type `PrequotientPhase = Σ e, EdgePhase e` with the project's
coproduct σ-algebra.

This file proves the general transport principle — standard Borel structure moves along any
`MeasurableEquiv` — which is the tool that will endow `PrequotientPhase` (via a measurable
equivalence with a Borel subset of `Edge × ℝ²`) and hence `NonzeroPrequotientPhase` and the
incoming/outgoing sections with standard Borel structure.
-/

namespace HamiltonianMetricGraphs

open MeasureTheory

/-- **Standard Borel structure transports along a measurable equivalence.**  If `α ≃ᵐ β` and `β` is
standard Borel, then so is `α`: pull the Polish topology back along the equivalence (making it a
homeomorphism, so `α` is Polish), and the pulled-back Borel σ-algebra is the given one because a
`MeasurableEquiv` reflects measurable sets.  This is the transport tool for giving the scattering
phase spaces standard Borel structure. -/
theorem standardBorelSpace_of_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [StandardBorelSpace β] (e : α ≃ᵐ β) : StandardBorelSpace α := by
  letI := upgradeStandardBorel β
  letI : TopologicalSpace α := TopologicalSpace.induced e inferInstance
  haveI : PolishSpace α := Equiv.polishSpace_induced e.toEquiv
  haveI : BorelSpace α := e.measurableEmbedding.borelSpace ⟨rfl⟩
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩⟩

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- Rebuild a prequotient point from an edge and a raw phase pair, clamping the position into the
physical edge so the result is always a valid `EdgePhase` element.  It is the identity on the
physical region; it only serves to witness measurability of the inverse chart into the Sigma type. -/
noncomputable def rebuildPrequotient (e : Γ.Edge) (y : ℝ × ℝ) : Γ.PrequotientPhase :=
  ⟨e, ⟨(min (max y.1 0) (Γ.length e), y.2),
    ⟨le_min (le_max_right _ _) (Γ.length_pos e).le, min_le_right _ _⟩⟩⟩

theorem measurable_rebuildPrequotient :
    Measurable (fun q : Γ.Edge × (ℝ × ℝ) => Γ.rebuildPrequotient q.1 q.2) := by
  apply measurable_from_prod_countable_right
  intro e
  have hinner : Measurable (fun y : ℝ × ℝ =>
      (⟨(min (max y.1 0) (Γ.length e), y.2),
        ⟨le_min (le_max_right _ _) (Γ.length_pos e).le, min_le_right _ _⟩⟩ : Γ.EdgePhase e)) :=
    Measurable.subtype_mk
      (((measurable_fst.max measurable_const).min measurable_const).prodMk measurable_snd)
  exact (Γ.measurable_prequotientSigmaMk e).comp hinner

/-- The prequotient phase space is measurably equivalent to the Borel subset of `Edge × ℝ²` cut out
by the physical-edge constraint.  The forward map unbundles the dependent subtype; the inverse uses
the clamping rebuild (which is the identity on the physical region). -/
noncomputable def prequotientPhaseEquivSubtype :
    Γ.PrequotientPhase ≃ᵐ
      {p : Γ.Edge × (ℝ × ℝ) // p.2.1 ∈ Set.Icc (0 : ℝ) (Γ.length p.1)} where
  toFun p := ⟨(p.1, p.2.1), p.2.2⟩
  invFun q := Γ.rebuildPrequotient q.1.1 q.1.2
  left_inv := by
    rintro ⟨e, ⟨y, hy0, hy1⟩⟩
    simp only [rebuildPrequotient, max_eq_left hy0, min_eq_left hy1]
  right_inv := by
    rintro ⟨⟨e, y⟩, hy0, hy1⟩
    apply Subtype.ext
    simp only [rebuildPrequotient, max_eq_left hy0, min_eq_left hy1]
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact (MechanicalPotential.measurable_prequotientEdge).prodMk
      ((MechanicalPotential.measurable_prequotientPosition).prodMk
        (MechanicalPotential.measurable_prequotientMomentum))
  measurable_invFun :=
    (Γ.measurable_rebuildPrequotient).comp measurable_subtype_coe

noncomputable instance : StandardBorelSpace Γ.PrequotientPhase := by
  have h1 : MeasurableSet {p : Γ.Edge × (ℝ × ℝ) | 0 ≤ p.2.1} :=
    measurableSet_le measurable_const (measurable_fst.comp measurable_snd)
  have h2 : MeasurableSet {p : Γ.Edge × (ℝ × ℝ) | p.2.1 ≤ Γ.length p.1} :=
    measurableSet_le (measurable_fst.comp measurable_snd)
      ((measurable_from_top (f := fun e : Γ.Edge => Γ.length e)).comp measurable_fst)
  have hR : MeasurableSet {p : Γ.Edge × (ℝ × ℝ) | p.2.1 ∈ Set.Icc (0 : ℝ) (Γ.length p.1)} := by
    have hEq : {p : Γ.Edge × (ℝ × ℝ) | p.2.1 ∈ Set.Icc (0 : ℝ) (Γ.length p.1)}
        = {p : Γ.Edge × (ℝ × ℝ) | 0 ≤ p.2.1} ∩ {p | p.2.1 ≤ Γ.length p.1} := by
      ext p; simp [Set.mem_Icc]
    rw [hEq]; exact h1.inter h2
  haveI : StandardBorelSpace {p : Γ.Edge × (ℝ × ℝ) //
      p.2.1 ∈ Set.Icc (0 : ℝ) (Γ.length p.1)} := hR.standardBorel
  exact standardBorelSpace_of_measurableEquiv Γ.prequotientPhaseEquivSubtype

noncomputable instance : StandardBorelSpace Γ.NonzeroPrequotientPhase :=
  (MechanicalPotential.measurableSet_nonzeroPrequotientPhase (Γ := Γ)).standardBorel

end FiniteMetricGraph

end HamiltonianMetricGraphs
