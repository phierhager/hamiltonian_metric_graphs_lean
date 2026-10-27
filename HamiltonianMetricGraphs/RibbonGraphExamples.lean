/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition XI.1: the examples after the proof (cyclic star and theta graph)
-/

import HamiltonianMetricGraphs.RibbonGraph

/-!
# The ribbon-graph examples of Sec. XI.E

After the proof of Proposition XI.1 the paper computes three examples:

* the **cyclic star** `Γ^⋆` of Sec. XI.A (a centre `c` joined to three leaves, central law the
  cyclic permutation `(η₁ η₂ η₃)`, leaf laws the identity): one face, `4 - 3 + 1 = 2`, `g = 0`
  (`ribbon_cyclicStar`);
* the **theta graph** `Θ` of Sec. XI.B (vertices `a`, `b` joined by three edges) with the same
  cyclic order `(η₁ η₂ η₃)`, `(η₁' η₂' η₃')` at both vertices: one face, `2 - 3 + 1 = 0`, `g = 1`
  (`ribbon_theta_same`);
* the theta graph with the cyclic order at one vertex reversed: three faces, `g = 0`
  (`ribbon_theta_reversed`).

In all three the edges are `Fin 3`, the end `(i, false)` is the end `η_{i+1}` (at the centre `c`,
respectively at `a`) and `(i, true)` is `η'_{i+1}` (at the leaf, respectively at `b`).  The
rotation is the high-energy vertex law (`F_E` above `max V`, where `κ_E = α`), so the face
permutation `φ = σ ∘ α` is `Π_E`.  The numbers of vertices, edges and faces, the Euler
characteristic and the genus are computed by `decide`; connectivity of the ribbon graph is checked
through `connected_of_forall`.
-/

namespace HamiltonianMetricGraphs

open Finset Equiv

namespace RibbonGraph

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A decidable criterion for connectivity: any two darts are joined by a cycle of `σ` or of
`φ`, followed by a cycle of `σ` or of `φ`. -/
theorem connected_of_forall (M : RibbonGraph E)
    (h : ∀ d d' : E × Bool, ∃ d'' : E × Bool,
      (M.rotation.SameCycle d d'' ∨ M.facePerm.SameCycle d d'') ∧
        (M.rotation.SameCycle d'' d' ∨ M.facePerm.SameCycle d'' d')) :
    M.Connected := by
  have hσ : ∀ {a b}, M.rotation.SameCycle a b →
      Relation.EqvGen (fun a b => b = M.rotation a ∨ b = edgeInv a) a b := by
    intro a b hab
    exact eqvGen_of_le (fun a b h => Relation.EqvGen.rel _ _ (Or.inl h))
      ((sameCycle_iff_eqvGen _ a b).mp hab)
  have hφ : ∀ {a b}, M.facePerm.SameCycle a b →
      Relation.EqvGen (fun a b => b = M.rotation a ∨ b = edgeInv a) a b := by
    intro a b hab
    refine eqvGen_of_le (fun a b h => ?_) ((sameCycle_iff_eqvGen _ a b).mp hab)
    subst h
    exact Relation.EqvGen.trans _ (edgeInv a) _ (Relation.EqvGen.rel _ _ (Or.inr rfl))
      (Relation.EqvGen.rel _ _ (Or.inl rfl))
  intro d d'
  obtain ⟨d'', h1, h2⟩ := h d d'
  refine Relation.EqvGen.trans _ d'' _ ?_ ?_
  · rcases h1 with h1 | h1
    · exact hσ h1
    · exact hφ h1
  · rcases h2 with h2 | h2
    · exact hσ h2
    · exact hφ h2

end RibbonGraph

namespace RibbonExamples

/-- The rotation of a dart set `Fin 3 × Bool` given by turning the `false`-ends by `a` and the
`true`-ends by `b` (`a, b ∈ Fin 3`). -/
def turn (a b : Fin 3) : Perm (Fin 3 × Bool) where
  toFun d := if d.2 then (d.1 + b, true) else (d.1 + a, false)
  invFun d := if d.2 then (d.1 - b, true) else (d.1 - a, false)
  left_inv d := by
    rcases d with ⟨i, c⟩
    cases c <;> simp
  right_inv d := by
    rcases d with ⟨i, c⟩
    cases c <;> simp

/-- **The cyclic star** `Γ^⋆` of Sec. XI.A: the central law is the cyclic permutation
`(η₁ η₂ η₃)` of the central ends `(i, false)`, the leaf laws are the identity on the leaf ends
`(i, true)`. -/
def cyclicStar : RibbonGraph (Fin 3) := ⟨turn 1 0⟩

/-- **The theta graph** `Θ` with the same cyclic order `(η₁ η₂ η₃)`, `(η₁' η₂' η₃')` at both
vertices. -/
def thetaSame : RibbonGraph (Fin 3) := ⟨turn 1 1⟩

/-- **The theta graph** `Θ` with the cyclic order at `b` reversed: `(η₁ η₂ η₃)` at `a` and
`(η₃' η₂' η₁')` at `b`. -/
def thetaReversed : RibbonGraph (Fin 3) := ⟨turn 1 2⟩

/-- **The cyclic star (Sec. XI.E).**  The ribbon graph is connected, has `4` vertices, `3` edges
and a single face (all six darts: `Π_E = (η₁ η₁' η₂ η₂' η₃ η₃')`), so `χ = 4 - 3 + 1 = 2` and
`g = 0`. -/
theorem ribbon_cyclicStar :
    cyclicStar.Connected ∧ cyclicStar.numVertices = 4 ∧ cyclicStar.numEdges = 3 ∧
      cyclicStar.faces = {Finset.univ} ∧ cyclicStar.numFaces = 1 ∧
      cyclicStar.eulerChar = 2 ∧ cyclicStar.genus = 0 := by
  refine ⟨RibbonGraph.connected_of_forall _ (by decide), by decide, rfl, by decide, by decide,
    by decide, by decide⟩

/-- **The theta graph with equal cyclic orders (Sec. XI.E).**  The ribbon graph is connected, has
`2` vertices, `3` edges and a single face (`Π_E = (η₁ η₂' η₃ η₁' η₂ η₃')`), so
`χ = 2 - 3 + 1 = 0` and `g = 1`. -/
theorem ribbon_theta_same :
    thetaSame.Connected ∧ thetaSame.numVertices = 2 ∧ thetaSame.numEdges = 3 ∧
      thetaSame.faces = {Finset.univ} ∧ thetaSame.numFaces = 1 ∧
      thetaSame.eulerChar = 0 ∧ thetaSame.genus = 1 := by
  refine ⟨RibbonGraph.connected_of_forall _ (by decide), by decide, rfl, by decide, by decide,
    by decide, by decide⟩

/-- **The theta graph with one cyclic order reversed (Sec. XI.E).**  The ribbon graph is
connected, has `2` vertices, `3` edges and three faces `(η₁ η₃')`, `(η₂ η₁')`, `(η₃ η₂')`, so
`χ = 2 - 3 + 3 = 2` and `g = 0`. -/
theorem ribbon_theta_reversed :
    thetaReversed.Connected ∧ thetaReversed.numVertices = 2 ∧ thetaReversed.numEdges = 3 ∧
      thetaReversed.faces = {{(0, false), (2, true)}, {(1, false), (0, true)},
        {(2, false), (1, true)}} ∧ thetaReversed.numFaces = 3 ∧
      thetaReversed.eulerChar = 2 ∧ thetaReversed.genus = 0 := by
  refine ⟨RibbonGraph.connected_of_forall _ (by decide), by decide, rfl, by decide, by decide,
    by decide, by decide⟩

end RibbonExamples

end HamiltonianMetricGraphs
