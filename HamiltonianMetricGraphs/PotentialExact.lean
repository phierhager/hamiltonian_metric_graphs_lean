/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Boundary

/-!
# Edgewise regularity and the boundary energy, as printed

This module states two results of Sec. II of the paper in exactly their printed generality.

* **Definition II.2 (edgewise regularity).**  The paper defines, for every `k`, when a function
  `V : Γ → ℝ` on the metric graph is edgewise `C^k`: it is continuous on `Γ`, and each edge
  restriction `V_e` on `[0, ℓ_e]` admits a `C^k` extension to an open interval containing
  `[0, ℓ_e]`.  The structure `MechanicalPotential` of `Potential.lean` bakes in `k = 2` and
  stores the extension data.  Here the glued graph `Γ` is built as a topological space
  (`FiniteMetricGraph.Point`), `IsEdgewiseContDiff k` is defined for every `k : ℕ∞`, and
  `isEdgewiseContDiff_two_iff` shows that the edgewise `C²` functions on `Γ` are exactly the
  functions on `Γ` presented by a `MechanicalPotential`.
* **Lemma II.4 (`lem:boundary-energy`).**  The printed identity `E_v(η,p) = H_e(a,p)` holds for
  every `p ∈ ℝ`, including `p = 0`; `boundaryEnergyFormula_eq_hamiltonian` is that single
  statement.
-/

namespace HamiltonianMetricGraphs

open Set

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-! ### The glued metric graph as a topological space -/

/-- The vertices of `Γ`, as points of the glued graph.  This type synonym carries the discrete
topology, so that isolated vertices are (isolated) points of `Γ`. -/
def VertexPoint : Type := Γ.Vertex

instance : TopologicalSpace Γ.VertexPoint := ⊥

instance : DiscreteTopology Γ.VertexPoint := ⟨rfl⟩

/-- The disjoint union of the vertex set and the closed edge intervals `[0, ℓ_e]`, before the
endpoints are glued to the vertices (Definition II.1). -/
abbrev PreGraph : Type := Γ.VertexPoint ⊕ Σ e : Γ.Edge, Icc (0 : ℝ) (Γ.length e)

/-- The endpoint `η.coordinate` of an edge interval, as a point of `[0, ℓ_e]`. -/
def EdgeEnd.closedPoint (η : Γ.EdgeEnd) : Icc (0 : ℝ) (Γ.length η.1) :=
  ⟨η.coordinate, Γ.edgeEnd_coordinate_mem_closedEdge η⟩

/-- The gluing relation of Definition II.1: the endpoint `q_e = a` of the edge `e` is glued to
the vertex of the edge-end `(e,a)`.  Both ends of a loop are glued separately. -/
inductive Glue : Γ.PreGraph → Γ.PreGraph → Prop
  | endpoint (η : Γ.EdgeEnd) :
      Glue (Sum.inr ⟨η.1, EdgeEnd.closedPoint Γ η⟩) (Sum.inl η.vertex)

/-- The finite compact metric graph `Γ` of Definition II.1, as the quotient of the vertices and
the closed edge intervals by the endpoint gluing.  It carries the quotient topology. -/
abbrev Point : Type := Quot Γ.Glue

/-- The point of `Γ` represented by the coordinate `q ∈ [0, ℓ_e]` on the edge `e`. -/
def edgePoint (e : Γ.Edge) (q : Icc (0 : ℝ) (Γ.length e)) : Γ.Point :=
  Quot.mk _ (Sum.inr ⟨e, q⟩)

/-- The point of `Γ` given by a vertex. -/
def vertexPoint (v : Γ.Vertex) : Γ.Point := Quot.mk _ (Sum.inl v)

/-- The gluing: the endpoint of an edge interval is the point of its vertex. -/
theorem edgePoint_endpoint (η : Γ.EdgeEnd) :
    Γ.edgePoint η.1 (EdgeEnd.closedPoint Γ η) = Γ.vertexPoint η.vertex :=
  Quot.sound (Glue.endpoint η)

/-- The restriction `V_e` of a function on `Γ` to the closed edge interval `[0, ℓ_e]`. -/
def edgeRestriction (f : Γ.Point → ℝ) (e : Γ.Edge) (q : Icc (0 : ℝ) (Γ.length e)) : ℝ :=
  f (Γ.edgePoint e q)

/-- A function on the glued graph is continuous exactly when each edge restriction is
continuous on `[0, ℓ_e]` (the quotient and the disjoint-union topologies). -/
theorem continuous_iff_edgeRestriction (f : Γ.Point → ℝ) :
    Continuous f ↔ ∀ e : Γ.Edge, Continuous (Γ.edgeRestriction f e) := by
  have hq : Topology.IsQuotientMap (Quot.mk Γ.Glue) := isQuotientMap_quot_mk
  rw [show Continuous f ↔ Continuous (f ∘ Quot.mk Γ.Glue) from hq.continuous_iff]
  rw [continuous_sum_dom]
  constructor
  · rintro ⟨-, h⟩
    rw [continuous_sigma_iff] at h
    exact h
  · intro h
    refine ⟨continuous_of_discreteTopology, ?_⟩
    rw [continuous_sigma_iff]
    exact h

/-- **Definition II.2 (edgewise regularity).**  Let `k ∈ ℕ∞`.  A function `V : Γ → ℝ` is
*edgewise `C^k`* if it is continuous on `Γ` and, for every edge `e`, the restriction `V_e` to
`[0, ℓ_e]` admits a `C^k` extension to an open interval `(a, b) ⊇ [0, ℓ_e]`. -/
def IsEdgewiseContDiff (k : ℕ∞) (f : Γ.Point → ℝ) : Prop :=
  Continuous f ∧ ∀ e : Γ.Edge, ∃ a b : ℝ, a < 0 ∧ Γ.length e < b ∧
    ∃ g : ℝ → ℝ, ContDiffOn ℝ (k : WithTop ℕ∞) g (Ioo a b) ∧
      ∀ q : Icc (0 : ℝ) (Γ.length e), g q = Γ.edgeRestriction f e q

/-- Edgewise `C^k` regularity is monotone in `k`. -/
theorem IsEdgewiseContDiff.mono {k l : ℕ∞} {f : Γ.Point → ℝ} (hf : Γ.IsEdgewiseContDiff k f)
    (hlk : l ≤ k) : Γ.IsEdgewiseContDiff l f := by
  refine ⟨hf.1, fun e => ?_⟩
  obtain ⟨a, b, ha, hb, g, hg, hgf⟩ := hf.2 e
  exact ⟨a, b, ha, hb, g, hg.of_le (by exact_mod_cast hlk), hgf⟩

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- The function on the glued graph `Γ` presented by a mechanical potential: its vertex values
at the vertices and its selected edge extensions on the closed edge intervals.  Endpoint
compatibility makes this well defined on the quotient. -/
def toFunction : Γ.Point → ℝ :=
  Quot.lift (Sum.elim V.vertexValue (fun x => V.extension x.1 x.2)) (by
    rintro _ _ ⟨η⟩
    exact V.endpoint_compatible η)

@[simp] theorem toFunction_edgePoint (e : Γ.Edge) (q : Icc (0 : ℝ) (Γ.length e)) :
    V.toFunction (Γ.edgePoint e q) = V.extension e q := rfl

@[simp] theorem toFunction_vertexPoint (v : Γ.Vertex) :
    V.toFunction (Γ.vertexPoint v) = V.vertexValue v := rfl

/-- An open set containing `[0, ℓ]` contains an open interval containing `[0, ℓ]`. -/
private theorem exists_Ioo_subset_of_isOpen {ℓ : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hsub : Icc (0 : ℝ) ℓ ⊆ U) (hℓ : 0 ≤ ℓ) :
    ∃ a b : ℝ, a < 0 ∧ ℓ < b ∧ Ioo a b ⊆ U := by
  obtain ⟨ε, hε, h0⟩ := Metric.isOpen_iff.mp hU 0 (hsub ⟨le_rfl, hℓ⟩)
  obtain ⟨δ, hδ, h1⟩ := Metric.isOpen_iff.mp hU ℓ (hsub ⟨hℓ, le_rfl⟩)
  refine ⟨-ε, ℓ + δ, by linarith, by linarith, ?_⟩
  rintro x ⟨hx1, hx2⟩
  by_cases hx0 : x < 0
  · apply h0
    rw [Real.ball_eq_Ioo]
    constructor <;> linarith
  by_cases hxl : ℓ < x
  · apply h1
    rw [Real.ball_eq_Ioo]
    constructor <;> linarith
  exact hsub ⟨not_lt.mp hx0, not_lt.mp hxl⟩

/-- Every mechanical potential presents an edgewise `C²` function on `Γ` (Definition II.2 with
`k = 2`). -/
theorem isEdgewiseContDiff_toFunction : Γ.IsEdgewiseContDiff 2 V.toFunction := by
  refine ⟨?_, fun e => ?_⟩
  · rw [FiniteMetricGraph.continuous_iff_edgeRestriction]
    intro e
    exact (V.extension_continuousOn_closedEdge e).restrict
  · obtain ⟨a, b, ha, hb, hab⟩ := exists_Ioo_subset_of_isOpen (V.domain_isOpen e)
      (V.closedEdge_subset_domain e) (le_of_lt (Γ.length_pos e))
    exact ⟨a, b, ha, hb, V.extension e, (V.contDiffOn_extension e).mono hab, fun q => rfl⟩

end MechanicalPotential

namespace FiniteMetricGraph

variable {Γ : FiniteMetricGraph}

/-- Conversely, an edgewise `C²` function on `Γ` is presented by a mechanical potential: choose
the `C²` extensions of Definition II.2 on their open intervals, and the values at the vertices. -/
theorem IsEdgewiseContDiff.exists_mechanicalPotential {f : Γ.Point → ℝ}
    (hf : Γ.IsEdgewiseContDiff 2 f) : ∃ V : MechanicalPotential Γ, V.toFunction = f := by
  choose a b ha hb g hg hgf using hf.2
  let V : MechanicalPotential Γ :=
    { extension := g
      domain := fun e => Ioo (a e) (b e)
      domain_isOpen := fun _ => isOpen_Ioo
      closedEdge_subset_domain := fun e _ hq =>
        ⟨lt_of_lt_of_le (ha e) hq.1, lt_of_le_of_lt hq.2 (hb e)⟩
      contDiffOn_extension := hg
      vertexValue := fun v => f (Γ.vertexPoint v)
      endpoint_compatible := fun η => by
        exact (hgf η.1 (EdgeEnd.closedPoint Γ η)).trans
          (congrArg f (Γ.edgePoint_endpoint η)) }
  refine ⟨V, funext fun z => ?_⟩
  induction z using Quot.ind with
  | mk x =>
    rcases x with v | ⟨e, q⟩
    · rfl
    · exact hgf e q

/-- **Definition II.2 versus `MechanicalPotential`.**  A function on the glued graph `Γ` is
edgewise `C²` (continuous on `Γ`, with `C²` extensions of the edge restrictions to open
intervals around the closed edges) exactly when it is the function presented by some
`MechanicalPotential`.  The structure `MechanicalPotential` additionally *records* a choice of
extension and of open domain; these choices do not change the function on `Γ`. -/
theorem isEdgewiseContDiff_two_iff (f : Γ.Point → ℝ) :
    Γ.IsEdgewiseContDiff 2 f ↔ ∃ V : MechanicalPotential Γ, V.toFunction = f := by
  constructor
  · exact IsEdgewiseContDiff.exists_mechanicalPotential
  · rintro ⟨V, rfl⟩
    exact V.isEdgewiseContDiff_toFunction

/-- Two mechanical potentials present the same function on `Γ` exactly when they have the same
vertex values and their extensions agree on every closed edge. -/
theorem _root_.HamiltonianMetricGraphs.MechanicalPotential.toFunction_eq_iff
    (V W : MechanicalPotential Γ) :
    V.toFunction = W.toFunction ↔
      (∀ v, V.vertexValue v = W.vertexValue v) ∧
        ∀ e, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), V.extension e q = W.extension e q := by
  constructor
  · intro h
    refine ⟨fun v => congrFun h (Γ.vertexPoint v), fun e q hq => ?_⟩
    exact congrFun h (Γ.edgePoint e ⟨q, hq⟩)
  · rintro ⟨hv, he⟩
    funext z
    induction z using Quot.ind with
    | mk x =>
      rcases x with v | ⟨e, q⟩
      · exact hv v
      · exact he e q q.2

end FiniteMetricGraph

/-! ### Lemma II.4 for every `p ∈ ℝ` -/

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- The boundary-energy formula `E_v(η,p) = p²/2 + V(v)` of Definition II.3, as a function of an
edge-end `η` at `v` and an arbitrary real momentum `p` (the zero momentum included). -/
noncomputable def boundaryEnergyFormula (η : Γ.EdgeEnd) (p : ℝ) : ℝ :=
  p ^ 2 / 2 + V.vertexValue η.vertex

/-- On nonzero boundary covectors the formula is the boundary energy `boundaryEnergy`. -/
@[simp] theorem boundaryEnergyFormula_covector (α : Γ.BoundaryCovector) :
    V.boundaryEnergyFormula α.germ α.momentum = V.boundaryEnergy α := rfl

/-- At an edge-end incident to `v`, the formula is `p²/2 + V(v)`. -/
theorem boundaryEnergyFormula_incident {v : Γ.Vertex} (η : Γ.IncidentEnds v) (p : ℝ) :
    V.boundaryEnergyFormula η.1 p = p ^ 2 / 2 + V.vertexValue v := by
  rw [boundaryEnergyFormula, η.2]

/-- **Lemma II.4 (`lem:boundary-energy`), for every `p ∈ ℝ`.**  Let `η = (e,a)` be an edge-end
at `v` and `p ∈ ℝ`.  Then `E_v(η,p) = H_e(a,p)`.  (For `p ≠ 0` this is
`boundaryEnergy_eq_edgeHamiltonian`; for `p = 0` it is `endpoint_hamiltonian`.) -/
theorem boundaryEnergyFormula_eq_hamiltonian {v : Γ.Vertex} (η : Γ.IncidentEnds v) (p : ℝ) :
    V.boundaryEnergyFormula η.1 p =
      V.hamiltonian η.1.1 (FiniteMetricGraph.EdgeEnd.coordinate Γ η.1) p := by
  rw [V.endpoint_hamiltonian, boundaryEnergyFormula]

/-- The consequence stated in Lemma II.4: the edge energy at an endpoint glued to `v` does not
depend on which edge-end at `v` is used to compute it. -/
theorem hamiltonian_endpoint_independent {v : Γ.Vertex} (η ζ : Γ.IncidentEnds v) (p : ℝ) :
    V.hamiltonian η.1.1 (FiniteMetricGraph.EdgeEnd.coordinate Γ η.1) p =
      V.hamiltonian ζ.1.1 (FiniteMetricGraph.EdgeEnd.coordinate Γ ζ.1) p := by
  rw [← V.boundaryEnergyFormula_eq_hamiltonian, ← V.boundaryEnergyFormula_eq_hamiltonian,
    V.boundaryEnergyFormula_incident, V.boundaryEnergyFormula_incident]

end MechanicalPotential
end HamiltonianMetricGraphs
