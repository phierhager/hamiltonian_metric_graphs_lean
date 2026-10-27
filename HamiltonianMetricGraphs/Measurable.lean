/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Scattering

/-!
# Borel structures and boundary speed charts

Finite combinatorial types carry their discrete sigma-algebras.  Boundary covectors carry
the sigma-algebra induced by the measurable injection `(germ, momentum)` into the product of
the finite endpoint-germ space and the real line.  Thus the speed charts below are genuine
measurable equivalences, rather than only set-theoretic parametrizations.
-/

namespace HamiltonianMetricGraphs

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

noncomputable instance : MeasurableSpace Γ.Vertex := ⊤
noncomputable instance : MeasurableSpace Γ.Edge := ⊤
noncomputable instance : MeasurableSpace Bool := ⊤
noncomputable instance : MeasurableSpace Γ.EdgeEnd := ⊤

/-- Boundary covectors have the measurable structure induced by their germ and momentum. -/
noncomputable instance : MeasurableSpace Γ.BoundaryCovector :=
  MeasurableSpace.comap (fun α : Γ.BoundaryCovector => (α.germ, α.momentum)) inferInstance

noncomputable instance (v : Γ.Vertex) : MeasurableSpace (Γ.IncidentEnds v) :=
  MeasurableSpace.comap Subtype.val inferInstance
noncomputable instance (v : Γ.Vertex) : MeasurableSpace (Γ.IncomingBoundary v) :=
  MeasurableSpace.comap Subtype.val inferInstance
noncomputable instance (v : Γ.Vertex) : MeasurableSpace (Γ.OutgoingBoundary v) :=
  MeasurableSpace.comap Subtype.val inferInstance

noncomputable instance (v : Γ.Vertex) : DiscreteMeasurableSpace (Γ.IncidentEnds v) where
  forall_measurableSet s := by
    change ∃ t : Set Γ.EdgeEnd, MeasurableSet t ∧ Subtype.val ⁻¹' t = s
    refine ⟨Subtype.val '' s, MeasurableSet.of_discrete, ?_⟩
    ext η
    simp

theorem measurable_boundary_pair :
    Measurable (fun α : Γ.BoundaryCovector => (α.germ, α.momentum)) :=
  comap_measurable _

theorem measurable_boundary_germ :
    Measurable (fun α : Γ.BoundaryCovector => α.germ) :=
  measurable_fst.comp (measurable_boundary_pair Γ)

theorem measurable_boundary_momentum :
    Measurable (fun α : Γ.BoundaryCovector => α.momentum) :=
  measurable_snd.comp (measurable_boundary_pair Γ)

/-- The boundary speed `|momentum|` is Borel measurable (a flux coordinate, Lemma VI.1). -/
theorem measurable_boundary_speed :
    Measurable (fun α : Γ.BoundaryCovector => |α.momentum|) :=
  (measurable_boundary_momentum Γ).abs

private theorem measurable_incident_sign (v : Γ.Vertex) :
    Measurable (fun η : Γ.IncidentEnds v => η.1.sign) :=
  Measurable.of_discrete

theorem measurable_incomingAtSpeed (v : Γ.Vertex) :
    Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed => Γ.incomingAtSpeed x.1 x.2) := by
  rw [measurable_comap_iff, measurable_comap_iff]
  change Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed =>
    (x.1.1, x.1.1.sign * x.2.1))
  refine Measurable.prodMk ?_ ?_
  · have h₁ : Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed => x.1) := measurable_fst
    have h₂ : Measurable (fun η : Γ.IncidentEnds v => (η.1 : Γ.EdgeEnd)) := measurable_subtype_coe
    exact h₂.comp h₁
  · have h₁ : Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed => x.1.1.sign) :=
      (measurable_incident_sign Γ v).comp measurable_fst
    have h₂ : Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed => x.2.1) :=
      measurable_subtype_coe.comp measurable_snd
    exact h₁.mul h₂

theorem measurable_outgoingAtSpeed (v : Γ.Vertex) :
    Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed => Γ.outgoingAtSpeed x.1 x.2) := by
  rw [measurable_comap_iff, measurable_comap_iff]
  change Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed =>
    (x.1.1, -(x.1.1.sign * x.2.1)))
  refine Measurable.prodMk ?_ ?_
  · have h₁ : Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed => x.1) := measurable_fst
    have h₂ : Measurable (fun η : Γ.IncidentEnds v => (η.1 : Γ.EdgeEnd)) := measurable_subtype_coe
    exact h₂.comp h₁
  · have h₁ : Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed => x.1.1.sign) :=
      (measurable_incident_sign Γ v).comp measurable_fst
    have h₂ : Measurable (fun x : Γ.IncidentEnds v × PositiveSpeed => x.2.1) :=
      measurable_subtype_coe.comp measurable_snd
    exact (h₁.mul h₂).neg

theorem measurable_incoming_speedCoordinates (v : Γ.Vertex) :
    Measurable (fun α : Γ.IncomingBoundary v =>
      ((⟨α.1.germ, α.2.1⟩ : Γ.IncidentEnds v),
        (⟨|α.1.momentum|, abs_pos.mpr α.1.momentum_ne_zero⟩ : PositiveSpeed))) := by
  refine Measurable.prodMk ?_ ?_
  · exact ((measurable_boundary_germ Γ).comp measurable_subtype_coe).subtype_mk
  · exact
      (measurable_abs.comp
        ((measurable_boundary_momentum Γ).comp measurable_subtype_coe)).subtype_mk

theorem measurable_outgoing_speedCoordinates (v : Γ.Vertex) :
    Measurable (fun α : Γ.OutgoingBoundary v =>
      ((⟨α.1.germ, α.2.1⟩ : Γ.IncidentEnds v),
        (⟨|α.1.momentum|, abs_pos.mpr α.1.momentum_ne_zero⟩ : PositiveSpeed))) := by
  refine Measurable.prodMk ?_ ?_
  · exact ((measurable_boundary_germ Γ).comp measurable_subtype_coe).subtype_mk
  · exact
      (measurable_abs.comp
        ((measurable_boundary_momentum Γ).comp measurable_subtype_coe)).subtype_mk

/-- Incoming boundary covectors are measurably equivalent to an incident endpoint germ and a
strictly positive speed. -/
noncomputable def incomingSpeedChart (v : Γ.Vertex) :
    Γ.IncidentEnds v × PositiveSpeed ≃ᵐ Γ.IncomingBoundary v where
  toEquiv :=
    { toFun := fun x => Γ.incomingAtSpeed x.1 x.2
      invFun := fun α =>
        (⟨α.1.germ, α.2.1⟩, ⟨|α.1.momentum|, abs_pos.mpr α.1.momentum_ne_zero⟩)
      left_inv := by
        rintro ⟨η, r⟩
        have hr : 0 < r.1 := r.2
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          rcases η with ⟨⟨e, b⟩, hη⟩
          cases b <;> simp [incomingAtSpeed, EdgeEnd.sign, abs_of_pos hr]
      right_inv := fun α => (Γ.incoming_eq_incomingAtSpeed α).symm }
  measurable_toFun := Γ.measurable_incomingAtSpeed v
  measurable_invFun := measurable_incoming_speedCoordinates Γ v

/-- Outgoing boundary covectors are measurably equivalent to an incident endpoint germ and a
strictly positive speed. -/
noncomputable def outgoingSpeedChart (v : Γ.Vertex) :
    Γ.IncidentEnds v × PositiveSpeed ≃ᵐ Γ.OutgoingBoundary v where
  toEquiv :=
    { toFun := fun x => Γ.outgoingAtSpeed x.1 x.2
      invFun := fun α =>
        (⟨α.1.germ, α.2.1⟩, ⟨|α.1.momentum|, abs_pos.mpr α.1.momentum_ne_zero⟩)
      left_inv := by
        rintro ⟨η, r⟩
        have hr : 0 < r.1 := r.2
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          rcases η with ⟨⟨e, b⟩, hη⟩
          cases b <;> simp [outgoingAtSpeed, EdgeEnd.sign, abs_of_pos hr]
      right_inv := fun α => (Γ.outgoing_eq_outgoingAtSpeed α).symm }
  measurable_toFun := Γ.measurable_outgoingAtSpeed v
  measurable_invFun := measurable_outgoing_speedCoordinates Γ v

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- The boundary (mechanical) energy of a covector is Borel measurable: `p²/2` plus a
germ-determined (hence discrete-measurable) vertex value. -/
theorem measurable_boundaryEnergy : Measurable V.boundaryEnergy := by
  have hmom : Measurable (fun α : Γ.BoundaryCovector => α.momentum) :=
    Γ.measurable_boundary_momentum
  have hvert : Measurable (fun α : Γ.BoundaryCovector => V.vertexValue α.germ.vertex) :=
    (measurable_from_top (f := fun η : Γ.EdgeEnd => V.vertexValue η.vertex)).comp
      Γ.measurable_boundary_germ
  exact ((hmom.pow_const 2).div_const 2).add hvert

end MechanicalPotential
end HamiltonianMetricGraphs
