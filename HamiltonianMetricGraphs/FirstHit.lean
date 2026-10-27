/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.BorelScattering
import HamiltonianMetricGraphs.EdgeDynamics

/-!
# First endpoint-hit witnesses

This file records the exact data supplied by a concrete edge evolution between an initial state
and its first later endpoint contact.  The witness does not assert that every orbit hits an
endpoint: trapped edge trajectories are permitted.  It proves instead the facts needed whenever
an endpoint hit occurs, notably conservation of energy and that a regular arrival is incoming.
-/

namespace HamiltonianMetricGraphs

open Set

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- A positive-time, interior-until-the-end solution segment ending at a specified endpoint
germ of one edge. -/
structure EdgeFirstHit (e : Γ.Edge) (x : ℝ × ℝ) where
  duration : ℝ
  duration_pos : 0 < duration
  curve : ℝ → ℝ × ℝ
  initial : curve 0 = x
  initial_physical : x.1 ∈ Icc (0 : ℝ) (Γ.length e)
  in_domain : ∀ t ∈ Icc (0 : ℝ) duration, (curve t).1 ∈ V.domain e
  integralCurve : ∀ t ∈ Icc (0 : ℝ) duration,
    HasDerivWithinAt curve (V.edgeVectorField e (curve t)) (Icc (0 : ℝ) duration) t
  interior_before : ∀ t ∈ Ioo (0 : ℝ) duration,
    (curve t).1 ∈ Ioo (0 : ℝ) (Γ.length e)
  endpoint : Bool
  hit_endpoint : (curve duration).1 = FiniteMetricGraph.EdgeEnd.coordinate Γ (e, endpoint)

namespace EdgeFirstHit

variable {V} {e : Γ.Edge} {x : ℝ × ℝ} (h : V.EdgeFirstHit e x)

/-- A first-hit witness remains on the closed physical edge throughout its time interval. -/
theorem physical_at (t : ℝ) (ht : t ∈ Icc (0 : ℝ) h.duration) :
    (h.curve t).1 ∈ Icc (0 : ℝ) (Γ.length e) := by
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · simpa [h.initial] using h.initial_physical
  rcases eq_or_lt_of_le ht.2 with rfl | htlt
  · rw [h.hit_endpoint]
    exact FiniteMetricGraph.edgeEnd_coordinate_mem_closedEdge Γ (e, h.endpoint)
  · exact ⟨(h.interior_before t ⟨htpos, htlt⟩).1.le,
      (h.interior_before t ⟨htpos, htlt⟩).2.le⟩

/-- Energy is constant at every time in a first-hit segment. -/
theorem hamiltonian_eq_initial_at (t : ℝ) (ht : t ∈ Icc (0 : ℝ) h.duration) :
    V.hamiltonian e (h.curve t).1 (h.curve t).2 = V.hamiltonian e x.1 x.2 := by
  have henergy := V.hamiltonian_eq_of_hamiltonEquations_within
    (q := fun s => (h.curve s).1) (p := fun s => (h.curve s).2)
    (a := 0) (b := h.duration)
    (fun s hs => h.in_domain s hs)
    (fun s hs => V.edgeIntegralCurve_hasDerivWithinAt_fst (h.integralCurve s hs))
    (fun s hs => by
      simpa [force] using V.edgeIntegralCurve_hasDerivWithinAt_snd (h.integralCurve s hs))
  simpa [h.initial] using henergy t ht

/-- Energy is conserved from the initial state to a first endpoint hit. -/
theorem hamiltonian_eq_initial :
    V.hamiltonian e (h.curve h.duration).1 (h.curve h.duration).2 =
      V.hamiltonian e x.1 x.2 := by
  exact h.hamiltonian_eq_initial_at h.duration ⟨h.duration_pos.le, le_rfl⟩

/-- At a regular energy, the momentum at a first endpoint hit cannot vanish. -/
theorem hit_momentum_ne_zero
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    (h.curve h.duration).2 ≠ 0 := by
  intro hp
  have hE : V.hamiltonian e
      (FiniteMetricGraph.EdgeEnd.coordinate Γ (e, h.endpoint)) 0 =
      V.hamiltonian e x.1 x.2 := by
    rw [← h.hit_endpoint, ← hp]
    exact h.hamiltonian_eq_initial
  have hvertex : V.vertexValue (Γ.endpoint e h.endpoint) = V.hamiltonian e x.1 x.2 := by
    have hend := V.endpoint_hamiltonian (η := (e, h.endpoint)) 0
    rw [hE] at hend
    change V.vertexValue (FiniteMetricGraph.EdgeEnd.vertex Γ (e, h.endpoint)) =
      V.hamiltonian e x.1 x.2
    simpa using hend.symm
  apply hregular
  exact (V.mem_exceptionalEnergies_iff).mpr ⟨Γ.endpoint e h.endpoint, hvertex⟩

/-- The boundary covector at a regular first hit. -/
noncomputable def arrivalCovector
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) : Γ.BoundaryCovector where
  germ := (e, h.endpoint)
  momentum := (h.curve h.duration).2
  momentum_ne_zero := h.hit_momentum_ne_zero hregular

@[simp] theorem arrivalCovector_germ
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    (h.arrivalCovector hregular).germ = (e, h.endpoint) := rfl

@[simp] theorem arrivalCovector_momentum
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    (h.arrivalCovector hregular).momentum = (h.curve h.duration).2 := rfl

/-- The arrival covector belongs to the incoming boundary section. -/
noncomputable def arrivalIncoming
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    Γ.IncomingBoundary (Γ.endpoint e h.endpoint) := by
  refine ⟨h.arrivalCovector hregular, rfl, ?_⟩
  have hqderivIcc := V.edgeIntegralCurve_hasDerivWithinAt_fst
    (h.integralCurve h.duration ⟨h.duration_pos.le, le_rfl⟩)
  have hqderiv : HasDerivWithinAt (fun s => (h.curve s).1) (h.curve h.duration).2
      (Iic h.duration) h.duration :=
    hasDerivWithinAt_Iic_of_Icc h.duration_pos hqderivIcc
  have hpne := h.hit_momentum_ne_zero hregular
  cases hendpoint : h.endpoint
  · have hqzero : (h.curve h.duration).1 = 0 := by
      simpa [hendpoint, FiniteMetricGraph.EdgeEnd.coordinate] using h.hit_endpoint
    have hpnonpos : (h.curve h.duration).2 ≤ 0 :=
      leftEndpoint_derivWithin_nonpos_of_pos_before h.duration_pos
        (fun t ht => (h.interior_before t ht).1) hqderiv hqzero
    have hpneg : (h.curve h.duration).2 < 0 := lt_of_le_of_ne hpnonpos hpne
    simpa [arrivalCovector, hendpoint, FiniteMetricGraph.EdgeEnd.sign] using neg_pos.mpr hpneg
  · have hqright : (h.curve h.duration).1 = Γ.length e := by
      simpa [hendpoint, FiniteMetricGraph.EdgeEnd.coordinate] using h.hit_endpoint
    have hpnonneg : 0 ≤ (h.curve h.duration).2 :=
      rightEndpoint_derivWithin_nonneg_of_lt_before h.duration_pos
        (fun t ht => (h.interior_before t ht).2) hqderiv hqright
    have hppos : 0 < (h.curve h.duration).2 :=
      lt_of_le_of_ne hpnonneg (Ne.symm hpne)
    simpa [arrivalCovector, hendpoint, FiniteMetricGraph.EdgeEnd.sign] using hppos

/-- The energy of the incoming covector at a regular hit equals the energy of the initial edge
state. -/
theorem arrival_boundaryEnergy_eq_initial
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    V.boundaryEnergy (h.arrivalIncoming hregular).1 = V.hamiltonian e x.1 x.2 := by
  rw [V.boundaryEnergy_eq_edgeHamiltonian]
  change V.hamiltonian e (FiniteMetricGraph.EdgeEnd.coordinate Γ (e, h.endpoint))
    (h.curve h.duration).2 = _
  rw [← h.hit_endpoint]
  exact h.hamiltonian_eq_initial

/-- Applying the prescribed scattering law to a regular first arrival preserves its initial
energy. -/
theorem scattered_boundaryEnergy_eq_initial
    (S : BorelEnergyPreservingScattering V)
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    V.boundaryEnergy (S.map (Γ.endpoint e h.endpoint) (h.arrivalIncoming hregular)).1 =
      V.hamiltonian e x.1 x.2 := by
  rw [S.preserves_energy]
  exact h.arrival_boundaryEnergy_eq_initial hregular

/-- Regularity is preserved across a scattering event. -/
theorem scattered_boundaryEnergy_not_exceptional
    (S : BorelEnergyPreservingScattering V)
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    V.boundaryEnergy (S.map (Γ.endpoint e h.endpoint) (h.arrivalIncoming hregular)).1 ∉
      V.exceptionalEnergies := by
  rw [h.scattered_boundaryEnergy_eq_initial S hregular]
  exact hregular

/-- One recursive continuation step is locally available after applying a Borel scattering law
at a regular first hit. -/
theorem exists_local_edge_integralCurve_after_scattering
    (S : BorelEnergyPreservingScattering V)
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    ∃ γ : ℝ → ℝ × ℝ,
      γ 0 =
        (FiniteMetricGraph.EdgeEnd.coordinate Γ
          (S.map (Γ.endpoint e h.endpoint) (h.arrivalIncoming hregular)).1.germ,
          (S.map (Γ.endpoint e h.endpoint) (h.arrivalIncoming hregular)).1.momentum) ∧
      ∃ ε > (0 : ℝ),
        ∀ t ∈ Ioo 0 ε,
          (γ t).1 ∈ Ioo (0 : ℝ)
            (Γ.length (S.map (Γ.endpoint e h.endpoint) (h.arrivalIncoming hregular)).1.germ.1) ∧
          HasDerivAt γ
            (V.edgeVectorField
              (S.map (Γ.endpoint e h.endpoint) (h.arrivalIncoming hregular)).1.germ.1 (γ t)) t := by
  obtain ⟨γ, hγ0, _hγderiv0, ε, hε, hγ⟩ :=
    V.exists_local_edge_integralCurve_from_outgoingBoundary
      (S.map (Γ.endpoint e h.endpoint) (h.arrivalIncoming hregular))
  exact ⟨γ, hγ0, ε, hε, hγ⟩

end EdgeFirstHit
end MechanicalPotential
end HamiltonianMetricGraphs
