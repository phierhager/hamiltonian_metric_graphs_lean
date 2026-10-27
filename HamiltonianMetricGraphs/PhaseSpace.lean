/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.BorelCriterion

/-!
# Edge phase cylinders and the regular energy sector

The prequotient phase space is the finite dependent disjoint union of closed edge cylinders.
Boundary covectors embed into it before the scattering identifications are imposed.
-/

namespace HamiltonianMetricGraphs

open Set

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- The closed phase cylinder over a single metric edge. -/
def EdgePhase (e : Γ.Edge) := {x : ℝ × ℝ | x.1 ∈ Icc (0 : ℝ) (Γ.length e)}

noncomputable instance (e : Γ.Edge) : MeasurableSpace (Γ.EdgePhase e) :=
  MeasurableSpace.comap Subtype.val inferInstance

/-- Momentum reversal on one closed edge phase cylinder. -/
noncomputable def edgePhaseMomentumReversal (e : Γ.Edge) : Γ.EdgePhase e → Γ.EdgePhase e :=
  fun x => ⟨(x.1.1, -x.1.2), by
    change x.1.1 ∈ Icc (0 : ℝ) (Γ.length e)
    exact x.2⟩

/-- The fixed-edge momentum reversal is Borel. -/
theorem measurable_edgePhaseMomentumReversal (e : Γ.Edge) :
    Measurable (Γ.edgePhaseMomentumReversal e) := by
  rw [measurable_comap_iff]
  change Measurable (fun x : Γ.EdgePhase e => (x.1.1, -x.1.2))
  refine Measurable.prodMk ?_ ?_
  · exact measurable_fst.comp measurable_subtype_coe
  · exact (measurable_snd.comp measurable_subtype_coe).neg

/-- The finite disjoint union of edge phase cylinders, before boundary scattering. -/
def PrequotientPhase := Σ e : Γ.Edge, Γ.EdgePhase e

noncomputable instance : MeasurableSpace Γ.PrequotientPhase :=
  @Sigma.instMeasurableSpace Γ.Edge (fun e => Γ.EdgePhase e) (fun _ => inferInstance)

/-- Boundary covectors as points of the corresponding closed edge cylinder. -/
def BoundaryCovector.toPrequotientPhase (α : Γ.BoundaryCovector) : Γ.PrequotientPhase := by
  refine ⟨α.germ.1, ⟨(FiniteMetricGraph.EdgeEnd.coordinate Γ α.germ, α.momentum), ?_⟩⟩
  rcases α.germ with ⟨e, b⟩
  cases b
  · exact ⟨le_rfl, (Γ.length_pos e).le⟩
  · exact ⟨(Γ.length_pos e).le, le_rfl⟩

@[simp] theorem BoundaryCovector.toPrequotientPhase_edge (α : Γ.BoundaryCovector) :
    (α.toPrequotientPhase Γ).1 = α.germ.1 := rfl

@[simp] theorem BoundaryCovector.toPrequotientPhase_momentum (α : Γ.BoundaryCovector) :
    (α.toPrequotientPhase Γ).2.1.2 = α.momentum := rfl

theorem EdgeEnd.ext_of_edge_coordinate_eq {η ζ : Γ.EdgeEnd}
    (hedge : η.1 = ζ.1)
    (hcoordinate : FiniteMetricGraph.EdgeEnd.coordinate Γ η =
      FiniteMetricGraph.EdgeEnd.coordinate Γ ζ) : η = ζ := by
  rcases η with ⟨e, b⟩
  rcases ζ with ⟨f, c⟩
  change e = f at hedge
  subst f
  cases b <;> cases c
  · rfl
  · simp [EdgeEnd.coordinate] at hcoordinate
    linarith [Γ.length_pos e]
  · simp [EdgeEnd.coordinate] at hcoordinate
    linarith [Γ.length_pos e]
  · rfl

theorem BoundaryCovector.toPrequotientPhase_injective :
    Function.Injective (BoundaryCovector.toPrequotientPhase Γ) := by
  intro α β h
  apply BoundaryCovector.ext
  · apply EdgeEnd.ext_of_edge_coordinate_eq Γ
    · exact congrArg Sigma.fst h
    · exact congrArg (fun x : Γ.PrequotientPhase => x.2.1.1) h
  · exact congrArg (fun x : Γ.PrequotientPhase => x.2.1.2) h

/-- The `Sigma.mk e` inclusion into the prequotient coproduct is Borel measurable. -/
theorem measurable_prequotientSigmaMk (e : Γ.Edge) :
    Measurable (fun y : Γ.EdgePhase e => (⟨e, y⟩ : Γ.PrequotientPhase)) := by
  intro A hA
  exact (MeasurableSpace.measurableSet_iInf.mp hA) e

/-- The covector-to-prequotient embedding is Borel measurable: it factors through the measurable
`(germ, momentum)` pair, and for each (finitely many) germ it lands in one edge fibre by a
measurable affine map. -/
theorem measurable_toPrequotientPhase :
    Measurable (BoundaryCovector.toPrequotientPhase Γ) := by
  set h : Γ.EdgeEnd × ℝ → Γ.PrequotientPhase := fun q =>
    ⟨q.1.1, ⟨(FiniteMetricGraph.EdgeEnd.coordinate Γ q.1, q.2), by
      rcases q with ⟨⟨e, b⟩, p⟩
      cases b
      · exact ⟨le_rfl, (Γ.length_pos e).le⟩
      · exact ⟨(Γ.length_pos e).le, le_rfl⟩⟩⟩ with hdef
  have hh : Measurable h := by
    apply measurable_from_prod_countable_right
    intro η
    have hinner : Measurable (fun p : ℝ =>
        (⟨(FiniteMetricGraph.EdgeEnd.coordinate Γ η, p), by
          rcases η with ⟨e, b⟩
          cases b
          · exact ⟨le_rfl, (Γ.length_pos e).le⟩
          · exact ⟨(Γ.length_pos e).le, le_rfl⟩⟩ : Γ.EdgePhase η.1)) :=
      Measurable.subtype_mk (measurable_const.prodMk measurable_id)
    exact (Γ.measurable_prequotientSigmaMk η.1).comp hinner
  have hfact : BoundaryCovector.toPrequotientPhase Γ =
      h ∘ (fun α : Γ.BoundaryCovector => (α.germ, α.momentum)) := by
    funext α; rfl
  rw [hfact]
  exact hh.comp Γ.measurable_boundary_pair

/-- The prequotient phase space with the zero-momentum **boundary** points removed: this is the
paper's `P̃× = ∐ₑ ([0,ℓₑ] × ℝ) \ ({0,ℓₑ} × {0})`.  A point survives when it is in the open edge or
carries nonzero momentum; interior turning points `(q, 0)` with `0 < q < ℓₑ` are genuine phase
points (the flow passes through them), only the zero-momentum vertex states are excluded. -/
def NonzeroPrequotientPhase :=
  {x : Γ.PrequotientPhase | x.2.1.1 ∈ Ioo (0 : ℝ) (Γ.length x.1) ∨ x.2.1.2 ≠ 0}

noncomputable instance : MeasurableSpace Γ.NonzeroPrequotientPhase :=
  MeasurableSpace.comap Subtype.val inferInstance

/-- A point of the nonzero prequotient space sitting at a vertex coordinate carries nonzero
momentum. -/
theorem NonzeroPrequotientPhase.momentum_ne_zero_of_boundary (x : Γ.NonzeroPrequotientPhase)
    (hq : x.1.2.1.1 = 0 ∨ x.1.2.1.1 = Γ.length x.1.1) : x.1.2.1.2 ≠ 0 := by
  rcases x.2 with hint | hne
  · exfalso
    rcases hq with h | h
    · rw [h] at hint; exact lt_irrefl _ hint.1
    · rw [h] at hint; exact lt_irrefl _ hint.2
  · exact hne

def BoundaryCovector.toNonzeroPrequotientPhase (α : Γ.BoundaryCovector) :
    Γ.NonzeroPrequotientPhase :=
  ⟨α.toPrequotientPhase Γ, Or.inr (by
    simpa only [BoundaryCovector.toPrequotientPhase_momentum] using α.momentum_ne_zero)⟩

/-- The covector-to-nonzero-prequotient embedding is Borel measurable. -/
theorem measurable_toNonzeroPrequotientPhase :
    Measurable (BoundaryCovector.toNonzeroPrequotientPhase Γ) :=
  (measurable_toPrequotientPhase Γ).subtype_mk

/-- Componentwise momentum reversal on the nonzero prequotient phase space. -/
noncomputable def prequotientMomentumReversal : Γ.NonzeroPrequotientPhase →
    Γ.NonzeroPrequotientPhase := fun x =>
  ⟨⟨x.1.1, ⟨(x.1.2.1.1, -x.1.2.1.2), x.1.2.2⟩⟩, by
    change x.1.2.1.1 ∈ Ioo (0 : ℝ) (Γ.length x.1.1) ∨ -x.1.2.1.2 ≠ 0
    rcases x.2 with h | h
    · exact Or.inl h
    · exact Or.inr (neg_ne_zero.mpr h)⟩

/-- Componentwise momentum reversal is measurable on the nonzero prequotient phase space. -/
theorem measurable_prequotientMomentumReversal :
    Measurable Γ.prequotientMomentumReversal := by
  rw [measurable_comap_iff]
  unfold prequotientMomentumReversal
  change Measurable (fun x : Γ.NonzeroPrequotientPhase =>
    (⟨x.1.1, Γ.edgePhaseMomentumReversal x.1.1 x.1.2⟩ : Γ.PrequotientPhase))
  have hbase : Measurable (fun x : Γ.PrequotientPhase =>
      (⟨x.1, Γ.edgePhaseMomentumReversal x.1 x.2⟩ : Γ.PrequotientPhase)) := by
    intro t ht
    change @MeasurableSet Γ.PrequotientPhase
      (⨅ e : Γ.Edge, (inferInstance : MeasurableSpace (Γ.EdgePhase e)).map (Sigma.mk e)) t at ht
    change @MeasurableSet Γ.PrequotientPhase
      (⨅ e : Γ.Edge, (inferInstance : MeasurableSpace (Γ.EdgePhase e)).map (Sigma.mk e))
        ((fun x : Γ.PrequotientPhase =>
          (⟨x.1, Γ.edgePhaseMomentumReversal x.1 x.2⟩ : Γ.PrequotientPhase)) ⁻¹' t)
    rw [MeasurableSpace.measurableSet_iInf]
    intro e
    have hte : MeasurableSet
        ((fun y : Γ.EdgePhase e => (⟨e, y⟩ : Γ.PrequotientPhase)) ⁻¹' t) :=
      (MeasurableSpace.measurableSet_iInf.mp ht) e
    change MeasurableSet
      ((Γ.edgePhaseMomentumReversal e) ⁻¹'
        ((fun y : Γ.EdgePhase e => (⟨e, y⟩ : Γ.PrequotientPhase)) ⁻¹' t))
    exact hte.preimage (Γ.measurable_edgePhaseMomentumReversal e)
  exact hbase.comp measurable_subtype_coe

@[simp] theorem prequotientMomentumReversal_edge (x : Γ.NonzeroPrequotientPhase) :
    (Γ.prequotientMomentumReversal x).1.1 = x.1.1 := rfl

@[simp] theorem prequotientMomentumReversal_position (x : Γ.NonzeroPrequotientPhase) :
    (Γ.prequotientMomentumReversal x).1.2.1.1 = x.1.2.1.1 := rfl

@[simp] theorem prequotientMomentumReversal_momentum (x : Γ.NonzeroPrequotientPhase) :
    (Γ.prequotientMomentumReversal x).1.2.1.2 = -x.1.2.1.2 := rfl

@[simp] theorem prequotientMomentumReversal_involutive (x : Γ.NonzeroPrequotientPhase) :
    Γ.prequotientMomentumReversal (Γ.prequotientMomentumReversal x) = x := by
  rcases x with ⟨⟨e, ⟨⟨q, p⟩, hq⟩⟩, hp⟩
  simp [prequotientMomentumReversal]

theorem BoundaryCovector.toNonzeroPrequotientPhase_injective :
    Function.Injective (BoundaryCovector.toNonzeroPrequotientPhase Γ) := by
  intro α β h
  apply BoundaryCovector.toPrequotientPhase_injective Γ
  exact congrArg Subtype.val h

@[simp] theorem prequotientMomentumReversal_boundary (α : Γ.BoundaryCovector) :
    Γ.prequotientMomentumReversal (α.toNonzeroPrequotientPhase Γ) =
      α.momentumReversal.toNonzeroPrequotientPhase Γ := by
  apply Subtype.ext
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl

theorem incoming_outgoing_nonzeroPrequotient_ne {v w : Γ.Vertex}
    (α : Γ.IncomingBoundary v) (β : Γ.OutgoingBoundary w) :
    α.1.toNonzeroPrequotientPhase Γ ≠ β.1.toNonzeroPrequotientPhase Γ := by
  intro h
  have hcov : α.1 = β.1 :=
    BoundaryCovector.toNonzeroPrequotientPhase_injective Γ h
  have hsign : α.1.germ.sign * α.1.momentum = β.1.germ.sign * β.1.momentum := by
    rw [hcov]
  linarith [α.2.2, β.2.2]

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- The mechanical Hamiltonian on the prequotient finite disjoint union of edge cylinders. -/
noncomputable def prequotientHamiltonian (x : Γ.PrequotientPhase) : ℝ :=
  V.hamiltonian x.1 x.2.1.1 x.2.1.2

/-- The prequotient Hamiltonian is Borel measurable: on each edge fibre it is the continuous
`p²/2 + V(q)` on the compact closed edge, and edge is discrete. -/
theorem measurable_prequotientHamiltonian : Measurable V.prequotientHamiltonian := by
  intro A hA
  change @MeasurableSet Γ.PrequotientPhase
    (⨅ e : Γ.Edge, (inferInstance : MeasurableSpace (Γ.EdgePhase e)).map (Sigma.mk e))
    (V.prequotientHamiltonian ⁻¹' A)
  rw [MeasurableSpace.measurableSet_iInf]
  intro e
  change MeasurableSet
    ((fun y : Γ.EdgePhase e => V.prequotientHamiltonian ⟨e, y⟩) ⁻¹' A)
  have hfiber : Measurable (fun y : Γ.EdgePhase e => V.prequotientHamiltonian ⟨e, y⟩) := by
    change Measurable (fun y : Γ.EdgePhase e => V.hamiltonian e y.1.1 y.1.2)
    have hp : Measurable (fun y : Γ.EdgePhase e => y.1.2) :=
      measurable_snd.comp measurable_subtype_coe
    have hq : Measurable (fun y : Γ.EdgePhase e => V.extension e y.1.1) := by
      have hcont := (V.extension_continuousOn_closedEdge e).restrict
      have hmap : Measurable
          (fun y : Γ.EdgePhase e => (⟨y.1.1, y.2⟩ : Icc (0 : ℝ) (Γ.length e))) :=
        (measurable_fst.comp measurable_subtype_coe).subtype_mk
      exact hcont.measurable.comp hmap
    have : Measurable (fun y : Γ.EdgePhase e => (y.1.2) ^ 2 / 2 + V.extension e y.1.1) :=
      ((hp.pow_const 2).div_const 2).add hq
    simpa [hamiltonian] using this
  exact hfiber hA

/-- The prequotient position coordinate is Borel measurable. -/
theorem measurable_prequotientPosition :
    Measurable (fun x : Γ.PrequotientPhase => x.2.1.1) := by
  intro A hA
  change @MeasurableSet Γ.PrequotientPhase
    (⨅ e : Γ.Edge, (inferInstance : MeasurableSpace (Γ.EdgePhase e)).map (Sigma.mk e))
    ((fun x : Γ.PrequotientPhase => x.2.1.1) ⁻¹' A)
  rw [MeasurableSpace.measurableSet_iInf]
  intro e
  change MeasurableSet ((fun y : Γ.EdgePhase e => y.1.1) ⁻¹' A)
  exact (measurable_fst.comp measurable_subtype_coe) hA

/-- The prequotient momentum coordinate is Borel measurable. -/
theorem measurable_prequotientMomentum :
    Measurable (fun x : Γ.PrequotientPhase => x.2.1.2) := by
  intro A hA
  change @MeasurableSet Γ.PrequotientPhase
    (⨅ e : Γ.Edge, (inferInstance : MeasurableSpace (Γ.EdgePhase e)).map (Sigma.mk e))
    ((fun x : Γ.PrequotientPhase => x.2.1.2) ⁻¹' A)
  rw [MeasurableSpace.measurableSet_iInf]
  intro e
  change MeasurableSet ((fun y : Γ.EdgePhase e => y.1.2) ⁻¹' A)
  exact (measurable_snd.comp measurable_subtype_coe) hA

/-- The current edge, as a function of the prequotient point, is Borel measurable (each edge
fibre is measurable in the coproduct). -/
theorem measurable_prequotientEdge :
    Measurable (fun x : Γ.PrequotientPhase => x.1) := by
  intro A _
  change @MeasurableSet Γ.PrequotientPhase
    (⨅ e : Γ.Edge, (inferInstance : MeasurableSpace (Γ.EdgePhase e)).map (Sigma.mk e))
    ((fun x : Γ.PrequotientPhase => x.1) ⁻¹' A)
  rw [MeasurableSpace.measurableSet_iInf]
  intro e
  change MeasurableSet ((fun y : Γ.EdgePhase e => (⟨e, y⟩ : Γ.PrequotientPhase).1) ⁻¹' A)
  by_cases he : e ∈ A
  · have : (fun y : Γ.EdgePhase e => (⟨e, y⟩ : Γ.PrequotientPhase).1) ⁻¹' A = Set.univ := by
      ext y; simp [he]
    rw [this]; exact MeasurableSet.univ
  · have : (fun y : Γ.EdgePhase e => (⟨e, y⟩ : Γ.PrequotientPhase).1) ⁻¹' A = ∅ := by
      ext y; simp [he]
    rw [this]; exact MeasurableSet.empty

/-- The current edge's length, as a function of the prequotient point, is Borel measurable
(constant on each fibre). -/
theorem measurable_prequotientLength :
    Measurable (fun x : Γ.PrequotientPhase => Γ.length x.1) := by
  intro A hA
  change @MeasurableSet Γ.PrequotientPhase
    (⨅ e : Γ.Edge, (inferInstance : MeasurableSpace (Γ.EdgePhase e)).map (Sigma.mk e))
    ((fun x : Γ.PrequotientPhase => Γ.length x.1) ⁻¹' A)
  rw [MeasurableSpace.measurableSet_iInf]
  intro e
  change MeasurableSet ((fun _ : Γ.EdgePhase e => Γ.length e) ⁻¹' A)
  exact measurable_const hA

/-- Reconstruct the boundary covector of a germ-boundary nonzero point (junk off the boundary):
its germ is the current edge with the boundary flag `position = length`, and its momentum is the
current momentum (nonzero at every boundary point; replaced by the junk value `1` at an interior
turning point, where the reconstruction is never used). -/
noncomputable def pointToCovector (x : Γ.NonzeroPrequotientPhase) : Γ.BoundaryCovector := by
  classical
  exact ⟨(x.1.1, if x.1.2.1.1 = Γ.length x.1.1 then true else false),
    if x.1.2.1.2 = 0 then 1 else x.1.2.1.2, by
      split_ifs with h
      · exact one_ne_zero
      · exact h⟩

/-- The point-to-covector reconstruction is Borel measurable. -/
theorem measurable_pointToCovector : Measurable (pointToCovector (Γ := Γ)) := by
  classical
  have hpos : Measurable (fun x : Γ.NonzeroPrequotientPhase => x.1.2.1.1) :=
    measurable_prequotientPosition.comp measurable_subtype_coe
  have hlen : Measurable (fun x : Γ.NonzeroPrequotientPhase => Γ.length x.1.1) :=
    measurable_prequotientLength.comp measurable_subtype_coe
  have hedge : Measurable (fun x : Γ.NonzeroPrequotientPhase => x.1.1) :=
    measurable_prequotientEdge.comp measurable_subtype_coe
  have hmom : Measurable (fun x : Γ.NonzeroPrequotientPhase => x.1.2.1.2) :=
    measurable_prequotientMomentum.comp measurable_subtype_coe
  have hbset : MeasurableSet {x : Γ.NonzeroPrequotientPhase | x.1.2.1.1 = Γ.length x.1.1} := by
    have heq : {x : Γ.NonzeroPrequotientPhase | x.1.2.1.1 = Γ.length x.1.1} =
        (fun x : Γ.NonzeroPrequotientPhase => x.1.2.1.1 - Γ.length x.1.1) ⁻¹' {0} := by
      ext x; simp [sub_eq_zero]
    rw [heq]; exact (hpos.sub hlen) (measurableSet_singleton 0)
  have hbool : Measurable (fun x : Γ.NonzeroPrequotientPhase =>
      if x.1.2.1.1 = Γ.length x.1.1 then true else false) :=
    Measurable.ite hbset measurable_const measurable_const
  have hgerm : Measurable (fun x : Γ.NonzeroPrequotientPhase =>
      ((x.1.1, if x.1.2.1.1 = Γ.length x.1.1 then true else false) : Γ.EdgeEnd)) := by
    apply measurable_to_countable'
    intro η
    have hpre : (fun x : Γ.NonzeroPrequotientPhase =>
        ((x.1.1, if x.1.2.1.1 = Γ.length x.1.1 then true else false) : Γ.EdgeEnd)) ⁻¹' {η} =
        (fun x : Γ.NonzeroPrequotientPhase => x.1.1) ⁻¹' {η.1} ∩
        (fun x : Γ.NonzeroPrequotientPhase =>
          if x.1.2.1.1 = Γ.length x.1.1 then true else false) ⁻¹' {η.2} := by
      ext x
      rcases η with ⟨e, b⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Prod.ext_iff]
    rw [hpre]
    exact (hedge (measurableSet_singleton η.1)).inter (hbool (measurableSet_singleton η.2))
  have hmom' : Measurable (fun x : Γ.NonzeroPrequotientPhase =>
      if x.1.2.1.2 = 0 then (1 : ℝ) else x.1.2.1.2) :=
    Measurable.ite (hmom (measurableSet_singleton 0)) measurable_const hmom
  have hpair : Measurable (fun x : Γ.NonzeroPrequotientPhase =>
      (((x.1.1, if x.1.2.1.1 = Γ.length x.1.1 then true else false) : Γ.EdgeEnd),
        if x.1.2.1.2 = 0 then (1 : ℝ) else x.1.2.1.2)) :=
    hgerm.prodMk hmom'
  intro B hB
  obtain ⟨C, hC, rfl⟩ := hB
  exact hpair hC

/-- Momentum reversal preserves the mechanical Hamiltonian before quotienting. -/
theorem prequotientHamiltonian_momentumReversal (x : Γ.NonzeroPrequotientPhase) :
    V.prequotientHamiltonian (Γ.prequotientMomentumReversal x).1 =
      V.prequotientHamiltonian x.1 := by
  unfold prequotientHamiltonian hamiltonian
  change (-x.1.2.1.2) ^ 2 / 2 + V.extension x.1.1 x.1.2.1.1 =
    x.1.2.1.2 ^ 2 / 2 + V.extension x.1.1 x.1.2.1.1
  ring

theorem prequotientHamiltonian_boundary (α : Γ.BoundaryCovector) :
    V.prequotientHamiltonian (α.toPrequotientPhase Γ) = V.boundaryEnergy α := by
  unfold prequotientHamiltonian
  change V.hamiltonian α.germ.1 (FiniteMetricGraph.EdgeEnd.coordinate Γ α.germ) α.momentum = _
  simpa using (V.boundaryEnergy_eq_edgeHamiltonian α).symm

/-- The finite set of vertex-potential energies excluded by the regular sector. -/
noncomputable def exceptionalEnergies : Finset ℝ :=
  Finset.univ.image V.vertexValue

theorem mem_exceptionalEnergies_iff {E : ℝ} :
    E ∈ V.exceptionalEnergies ↔ ∃ v : Γ.Vertex, V.vertexValue v = E := by
  classical
  simp [exceptionalEnergies, eq_comm]

/-- Regular prequotient states are those whose energy is not a vertex-potential energy. -/
def RegularPrequotientPhase :=
  {x : Γ.NonzeroPrequotientPhase | V.prequotientHamiltonian x.1 ∉ V.exceptionalEnergies}

/-- The regular prequotient sector is Borel: the preimage of the finite exceptional-energy
complement under the measurable prequotient Hamiltonian. -/
theorem measurableSet_regularPrequotientPhase :
    MeasurableSet V.RegularPrequotientPhase := by
  have hE : MeasurableSet ((V.exceptionalEnergies : Set ℝ)) := V.exceptionalEnergies.measurableSet
  exact (V.measurable_prequotientHamiltonian.comp measurable_subtype_coe) hE.compl

/-- The positive-momentum half of the nonzero prequotient phase space is Borel (a flux-coordinate
sign sector, Lemma VI.1). -/
theorem measurableSet_positiveMomentum :
    MeasurableSet {x : Γ.NonzeroPrequotientPhase | 0 < x.1.2.1.2} :=
  (measurable_prequotientMomentum.comp measurable_subtype_coe) measurableSet_Ioi

/-- The negative-momentum half of the nonzero prequotient phase space is Borel. -/
theorem measurableSet_negativeMomentum :
    MeasurableSet {x : Γ.NonzeroPrequotientPhase | x.1.2.1.2 < 0} :=
  (measurable_prequotientMomentum.comp measurable_subtype_coe) measurableSet_Iio

theorem regular_boundary_transverse (α : Γ.BoundaryCovector)
    (_ : V.prequotientHamiltonian (α.toPrequotientPhase Γ) ∉ V.exceptionalEnergies) :
    α.momentum ≠ 0 := α.momentum_ne_zero

/-- The nonzero prequotient phase space is a Borel subset of the prequotient: the open-edge
condition and the nonzero-momentum condition are both Borel. -/
theorem measurableSet_nonzeroPrequotientPhase :
    MeasurableSet {x : Γ.PrequotientPhase |
      x.2.1.1 ∈ Ioo (0 : ℝ) (Γ.length x.1) ∨ x.2.1.2 ≠ 0} := by
  have h1 : MeasurableSet {x : Γ.PrequotientPhase | x.2.1.1 ∈ Ioo (0 : ℝ) (Γ.length x.1)} := by
    have hset : {x : Γ.PrequotientPhase | x.2.1.1 ∈ Ioo (0 : ℝ) (Γ.length x.1)} =
        {x : Γ.PrequotientPhase | 0 < x.2.1.1} ∩ {x | x.2.1.1 < Γ.length x.1} := by
      ext x; simp [Set.mem_Ioo]
    rw [hset]
    exact (measurableSet_lt measurable_const measurable_prequotientPosition).inter
      (measurableSet_lt measurable_prequotientPosition measurable_prequotientLength)
  exact h1.union (measurable_prequotientMomentum (measurableSet_singleton 0)).compl

/-- **Regular states are genuine phase points.**  At a regular energy a physical state is either
strictly inside its edge or carries nonzero momentum: a zero-momentum vertex state has exactly the
exceptional energy `V(v)`.  This is what places every point of a regular trajectory in the
nonzero prequotient phase space. -/
theorem interior_or_momentum_ne_zero_of_regular {e : Γ.Edge} {q p : ℝ}
    (hq : q ∈ Icc (0 : ℝ) (Γ.length e))
    (hreg : V.hamiltonian e q p ∉ V.exceptionalEnergies) :
    q ∈ Ioo (0 : ℝ) (Γ.length e) ∨ p ≠ 0 := by
  by_cases hp : p = 0
  · left
    subst hp
    refine ⟨lt_of_le_of_ne hq.1 ?_, lt_of_le_of_ne hq.2 ?_⟩
    · intro h0
      subst h0
      apply hreg
      rw [V.mem_exceptionalEnergies_iff]
      refine ⟨Γ.endpoint e false, ?_⟩
      have := V.endpoint_hamiltonian (η := (e, false)) 0
      change V.hamiltonian e 0 0 = 0 ^ 2 / 2 + V.vertexValue (Γ.endpoint e false) at this
      rw [this]; ring
    · intro hl
      subst hl
      apply hreg
      rw [V.mem_exceptionalEnergies_iff]
      refine ⟨Γ.endpoint e true, ?_⟩
      have := V.endpoint_hamiltonian (η := (e, true)) 0
      change V.hamiltonian e (Γ.length e) 0 = 0 ^ 2 / 2 + V.vertexValue (Γ.endpoint e true) at this
      rw [this]; ring
  · exact Or.inr hp

end MechanicalPotential
end HamiltonianMetricGraphs
