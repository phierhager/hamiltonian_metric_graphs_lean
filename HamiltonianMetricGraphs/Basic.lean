/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import Mathlib

/-!
# Finite metric graphs

The combinatorial layer used by the Hamiltonian scattering formalization.
Each endpoint germ carries its endpoint selector, so the two germs of a loop remain
distinct.
-/

namespace HamiltonianMetricGraphs

/-- A finite graph with a positive metric length on every edge. -/
structure FiniteMetricGraph where
  Vertex : Type
  Edge : Type
  vertexFintype : Fintype Vertex
  vertexDecidableEq : DecidableEq Vertex
  edgeFintype : Fintype Edge
  edgeDecidableEq : DecidableEq Edge
  endpoint : Edge → Bool → Vertex
  length : Edge → ℝ
  length_pos : ∀ e, 0 < length e

attribute [instance] FiniteMetricGraph.vertexFintype
attribute [instance] FiniteMetricGraph.vertexDecidableEq
attribute [instance] FiniteMetricGraph.edgeFintype
attribute [instance] FiniteMetricGraph.edgeDecidableEq

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- An endpoint germ; the Boolean distinguishes the two ends even for loops. -/
abbrev EdgeEnd := Γ.Edge × Bool

instance : Fintype Γ.EdgeEnd := inferInstance
instance : DecidableEq Γ.EdgeEnd := inferInstance

/-- The vertex incident to an endpoint germ. -/
def EdgeEnd.vertex (η : Γ.EdgeEnd) : Γ.Vertex := Γ.endpoint η.1 η.2

/-- The coordinate of an endpoint in its edge coordinate interval. -/
def EdgeEnd.coordinate (η : Γ.EdgeEnd) : ℝ := if η.2 then Γ.length η.1 else 0

/-- The outward coordinate sign: `-1` at zero and `+1` at the right endpoint. -/
def EdgeEnd.sign (η : Γ.EdgeEnd) : ℝ := if η.2 then 1 else -1

@[simp] theorem edgeEnd_coordinate_false (e : Γ.Edge) : EdgeEnd.coordinate Γ (e, false) = 0 := rfl
@[simp] theorem edgeEnd_coordinate_true (e : Γ.Edge) :
    EdgeEnd.coordinate Γ (e, true) = Γ.length e := rfl
@[simp] theorem edgeEnd_sign_false (e : Γ.Edge) : EdgeEnd.sign Γ (e, false) = -1 := rfl
@[simp] theorem edgeEnd_sign_true (e : Γ.Edge) : EdgeEnd.sign Γ (e, true) = 1 := rfl

/-- Every endpoint coordinate lies in the closed coordinate interval of its edge. -/
theorem edgeEnd_coordinate_mem_closedEdge (η : Γ.EdgeEnd) :
    η.coordinate ∈ Set.Icc (0 : ℝ) (Γ.length η.1) := by
  rcases η with ⟨e, b⟩
  cases b
  · simp [le_of_lt (Γ.length_pos e)]
  · simp [le_of_lt (Γ.length_pos e)]

/-- The finite type of endpoint germs at a vertex. -/
def IncidentEnds (v : Γ.Vertex) := {η : Γ.EdgeEnd // η.vertex = v}

noncomputable instance (v : Γ.Vertex) : Fintype (Γ.IncidentEnds v) := by
  classical
  refine Fintype.subtype (Finset.univ.filter fun η => η.vertex = v) ?_
  intro η
  simp

instance (v : Γ.Vertex) : DecidableEq (Γ.IncidentEnds v) := by
  unfold IncidentEnds
  infer_instance

theorem edgeEnd_sign_sq (η : Γ.EdgeEnd) : η.sign ^ 2 = 1 := by
  rcases η with ⟨e, b⟩
  cases b <;> norm_num [EdgeEnd.sign]

theorem edgeEnd_sign_ne_zero (η : Γ.EdgeEnd) : η.sign ≠ 0 := by
  rcases η with ⟨e, b⟩
  cases b <;> norm_num [EdgeEnd.sign]

/-- A finite nonempty metric graph has one positive radius smaller than half of every edge
length.  The strict half-length bound keeps the two endpoint-germ collars of a loop disjoint,
as required in the no-Zeno argument. -/
theorem exists_uniform_endpointCollarRadius [Nonempty Γ.Edge] :
    ∃ r : ℝ, 0 < r ∧ ∀ e : Γ.Edge, r < Γ.length e / 2 := by
  classical
  let lengths : Finset ℝ := Finset.univ.image Γ.length
  have hlengths : lengths.Nonempty := by
    rw [Finset.image_nonempty]
    exact Finset.univ_nonempty
  let m : ℝ := lengths.min' hlengths
  have hm_mem : m ∈ lengths := Finset.min'_mem lengths hlengths
  obtain ⟨e₀, -, he₀⟩ := Finset.mem_image.mp hm_mem
  have hm_pos : 0 < m := by
    rw [← he₀]
    exact Γ.length_pos e₀
  refine ⟨m / 4, div_pos hm_pos (by norm_num), ?_⟩
  intro e
  have hm_le : m ≤ Γ.length e := by
    apply Finset.min'_le lengths
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
  nlinarith

/-- Once a coordinate has reached the boundary of an endpoint collar, any later endpoint of the
same edge is at least that collar radius away.  The hypothesis `r < length / 2` is what makes the
statement work for the two distinct germs of a loop as well. -/
theorem endpoint_coordinate_separation_after_collar {e : Γ.Edge} {a b : Bool} {q r : ℝ}
    (hr : 0 < r) (hrlength : r < Γ.length e / 2)
    (hq : q ∈ Set.Icc (0 : ℝ) (Γ.length e))
    (hexit : |q - EdgeEnd.coordinate Γ (e, a)| = r) :
    r ≤ |EdgeEnd.coordinate Γ (e, b) - q| := by
  rcases hq with ⟨hq0, hql⟩
  cases a <;> cases b
  · simpa [abs_sub_comm] using hexit.ge
  · have hqeq : q = r := by
      have hqabs : |q| = r := by
        simpa only [edgeEnd_coordinate_false, sub_zero] using hexit
      simpa [abs_of_nonneg hq0] using hqabs
    -- The point is `r` from the left endpoint and therefore `length - r` from the right one.
    rw [edgeEnd_coordinate_true, hqeq, abs_of_nonneg]
    · nlinarith
    · nlinarith
  · have hqeq : q = Γ.length e - r := by
      simp only [edgeEnd_coordinate_true] at hexit
      rw [abs_of_nonpos (sub_nonpos.mpr hql)] at hexit
      nlinarith
    rw [edgeEnd_coordinate_false, hqeq, abs_of_nonpos]
    · nlinarith
    · nlinarith
  · simpa [abs_sub_comm] using hexit.ge

end FiniteMetricGraph
end HamiltonianMetricGraphs
