/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Basic

/-!
# Edgewise mechanical potentials

The potential is represented by a chosen real-valued extension on every edge together with
the open domain on which it is `C²`.  This is precisely the paper's edgewise extension
assumption: values outside the selected open neighbourhood carry no regularity claim.
-/

namespace HamiltonianMetricGraphs

open Set

variable (Γ : FiniteMetricGraph)

/-- A continuous graph potential with `C²` extensions on open neighbourhoods of its closed
edge intervals.  Endpoint compatibility encodes continuity after gluing the graph. -/
structure MechanicalPotential where
  extension : Γ.Edge → ℝ → ℝ
  domain : Γ.Edge → Set ℝ
  domain_isOpen : ∀ e, IsOpen (domain e)
  closedEdge_subset_domain : ∀ e, Icc (0 : ℝ) (Γ.length e) ⊆ domain e
  contDiffOn_extension : ∀ e, ContDiffOn ℝ 2 (extension e) (domain e)
  vertexValue : Γ.Vertex → ℝ
  endpoint_compatible : ∀ η : Γ.EdgeEnd,
    extension η.1 (FiniteMetricGraph.EdgeEnd.coordinate Γ η) = vertexValue η.vertex

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- The potential restricted to the physical closed interval of an edge. -/
def edgeValue (e : Γ.Edge) (q : Set.Icc (0 : ℝ) (Γ.length e)) : ℝ :=
  V.extension e q.1

/-- The edgewise mechanical Hamiltonian on a point `(q,p)`. -/
noncomputable def hamiltonian (e : Γ.Edge) (q p : ℝ) : ℝ := p ^ 2 / 2 + V.extension e q

/-- The derivative of the selected edgewise extension. -/
noncomputable def force (e : Γ.Edge) (q : ℝ) : ℝ := -deriv (V.extension e) q

theorem extension_contDiffAt_of_mem {e : Γ.Edge} {q : ℝ} (hq : q ∈ V.domain e) :
    ContDiffAt ℝ 2 (V.extension e) q :=
  (V.contDiffOn_extension e).contDiffAt ((V.domain_isOpen e).mem_nhds hq)

theorem extension_continuousAt_of_mem {e : Γ.Edge} {q : ℝ} (hq : q ∈ V.domain e) :
    ContinuousAt (V.extension e) q :=
  (V.extension_contDiffAt_of_mem hq).continuousAt

/-- The selected extension is continuous on the full physical closed edge interval. -/
theorem extension_continuousOn_closedEdge (e : Γ.Edge) :
    ContinuousOn (V.extension e) (Icc (0 : ℝ) (Γ.length e)) := by
  intro q hq
  exact (V.extension_continuousAt_of_mem (V.closedEdge_subset_domain e hq)).continuousWithinAt

/-- The compact physical edge interval has a positive uniform buffer inside the selected open
extension domain.  This is the domain-margin input for uniform local ODE continuation. -/
theorem exists_closedEdge_cthickening_subset_domain (e : Γ.Edge) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ (Icc (0 : ℝ) (Γ.length e)) ⊆ V.domain e :=
  isCompact_Icc.exists_cthickening_subset_open (V.domain_isOpen e)
    (V.closedEdge_subset_domain e)

/-- Finiteness yields one positive extension-domain buffer for all physical edge intervals.
The empty-edge case is vacuous. -/
theorem exists_uniform_closedEdge_cthickening_subset_domain :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e : Γ.Edge,
      Metric.cthickening δ (Icc (0 : ℝ) (Γ.length e)) ⊆ V.domain e := by
  classical
  by_cases h : Nonempty Γ.Edge
  · letI := h
    choose δ hδ hcontain using fun e : Γ.Edge => V.exists_closedEdge_cthickening_subset_domain e
    let d : ℝ := (Finset.univ.image δ).min' (by
      rw [Finset.image_nonempty]
      exact Finset.univ_nonempty)
    have hdmem : d ∈ Finset.univ.image δ := Finset.min'_mem _ _
    obtain ⟨e₀, -, he₀⟩ := Finset.mem_image.mp hdmem
    have hdpos : 0 < d := by rw [← he₀]; exact hδ e₀
    refine ⟨d, hdpos, ?_⟩
    intro e
    exact (Metric.cthickening_mono
      (Finset.min'_le (Finset.univ.image δ) (δ e)
        (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩)) _).trans (hcontain e)
  · have hempty : IsEmpty Γ.Edge := not_nonempty_iff.mp h
    exact ⟨1, by norm_num, fun e => isEmptyElim e⟩

/-- Each edge potential has a lower bound on its compact physical interval.  This is the
edgewise compactness input for the later uniform kinetic-energy estimate. -/
theorem exists_lowerBound_extension_closedEdge (e : Γ.Edge) :
    ∃ C : ℝ, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), C ≤ V.extension e q := by
  have hc : IsCompact ((V.extension e) '' Icc (0 : ℝ) (Γ.length e)) :=
    isCompact_Icc.image_of_continuousOn (V.extension_continuousOn_closedEdge e)
  rcases hc.bddBelow with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro q hq
  exact hC ⟨q, hq, rfl⟩

/-- Each edge potential also has an upper bound on its compact physical interval. -/
theorem exists_upperBound_extension_closedEdge (e : Γ.Edge) :
    ∃ C : ℝ, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), V.extension e q ≤ C := by
  have hc : IsCompact ((V.extension e) '' Icc (0 : ℝ) (Γ.length e)) :=
    isCompact_Icc.image_of_continuousOn (V.extension_continuousOn_closedEdge e)
  rcases hc.bddAbove with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro q hq
  exact hC ⟨q, hq, rfl⟩

/-- Finiteness of the graph upgrades the edgewise compact lower bounds to one lower bound valid
on every physical edge.  The empty-edge case is handled explicitly. -/
theorem exists_uniform_lowerBound_extension_closedEdges :
    ∃ C : ℝ, ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), C ≤ V.extension e q := by
  classical
  by_cases h : Nonempty Γ.Edge
  · letI := h
    choose c hc using fun e : Γ.Edge => V.exists_lowerBound_extension_closedEdge e
    refine ⟨Finset.univ.inf' Finset.univ_nonempty c, ?_⟩
    intro e q hq
    exact (Finset.inf'_le c (Finset.mem_univ e)).trans (hc e q hq)
  · have hempty : IsEmpty Γ.Edge := not_nonempty_iff.mp h
    exact ⟨0, fun e => isEmptyElim e⟩

/-- Finiteness similarly upgrades the edgewise upper bounds to one bound for the entire graph. -/
theorem exists_uniform_upperBound_extension_closedEdges :
    ∃ C : ℝ, ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), V.extension e q ≤ C := by
  classical
  by_cases h : Nonempty Γ.Edge
  · letI := h
    choose c hc using fun e : Γ.Edge => V.exists_upperBound_extension_closedEdge e
    refine ⟨Finset.univ.sup' Finset.univ_nonempty c, ?_⟩
    intro e q hq
    exact (hc e q hq).trans (Finset.le_sup' c (Finset.mem_univ e))
  · have hempty : IsEmpty Γ.Edge := not_nonempty_iff.mp h
    exact ⟨0, fun e => isEmptyElim e⟩

/-- A potential lower bound and an energy upper bound give the elementary uniform kinetic-energy
estimate used to bound speeds on compact energy windows. -/
theorem momentum_sq_le_of_hamiltonian_le {e : Γ.Edge} {q p C U : ℝ}
    (hpotential : C ≤ V.extension e q)
    (henergy : V.hamiltonian e q p ≤ U) :
    p ^ 2 ≤ 2 * (U - C) := by
  unfold hamiltonian at henergy
  nlinarith

/-- The kinetic estimate in explicit speed form.  Its radicand is nonnegative as a consequence
of the same energy identity. -/
theorem abs_momentum_le_sqrt_of_hamiltonian_le {e : Γ.Edge} {q p C U : ℝ}
    (hpotential : C ≤ V.extension e q)
    (henergy : V.hamiltonian e q p ≤ U) :
    |p| ≤ Real.sqrt (2 * (U - C)) := by
  have hkin := V.momentum_sq_le_of_hamiltonian_le hpotential henergy
  have hnonneg : 0 ≤ 2 * (U - C) := le_trans (sq_nonneg p) hkin
  have hsq : p ^ 2 ≤ (Real.sqrt (2 * (U - C))) ^ 2 := by
    rw [Real.sq_sqrt hnonneg]
    exact hkin
  have habs := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (Real.sqrt_nonneg _)] using habs

theorem endpoint_value (η : Γ.EdgeEnd) :
    V.extension η.1 (FiniteMetricGraph.EdgeEnd.coordinate Γ η) = V.vertexValue η.vertex :=
  V.endpoint_compatible η

theorem endpoint_hamiltonian (η : Γ.EdgeEnd) (p : ℝ) :
    V.hamiltonian η.1 (FiniteMetricGraph.EdgeEnd.coordinate Γ η) p =
    p ^ 2 / 2 + V.vertexValue η.vertex := by
  unfold hamiltonian
  rw [V.endpoint_value η]

/-- Continuity of an edge extension at an endpoint supplies a potential collar there. -/
theorem exists_endpoint_potential_collar (η : Γ.EdgeEnd) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ q : ℝ,
      |q - FiniteMetricGraph.EdgeEnd.coordinate Γ η| < r →
        |V.extension η.1 q - V.vertexValue η.vertex| < ε := by
  obtain ⟨r, hr, hcontrol⟩ :=
    (Metric.continuousAt_iff.mp
      (V.extension_continuousAt_of_mem (V.closedEdge_subset_domain η.1
        (FiniteMetricGraph.edgeEnd_coordinate_mem_closedEdge Γ η)))) ε hε
  refine ⟨r, hr, ?_⟩
  intro q hq
  have h := hcontrol (by simpa [Real.dist_eq] using hq)
  simpa [V.endpoint_value η, Real.dist_eq] using h

/-- Finitely many endpoint germs admit one potential-collar radius for a prescribed error.
This deliberately retains both ends of a loop as separate germs. -/
theorem exists_uniform_endpoint_potential_collar [Nonempty Γ.Edge] {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ η : Γ.EdgeEnd, ∀ q : ℝ,
      |q - FiniteMetricGraph.EdgeEnd.coordinate Γ η| < r →
        |V.extension η.1 q - V.vertexValue η.vertex| < ε := by
  classical
  choose r hrpos hr using fun η : Γ.EdgeEnd => V.exists_endpoint_potential_collar η hε
  let radii : Finset ℝ := Finset.univ.image r
  have hradii : radii.Nonempty := by
    rw [Finset.image_nonempty]
    exact Finset.univ_nonempty
  let m : ℝ := radii.min' hradii
  have hm_mem : m ∈ radii := Finset.min'_mem radii hradii
  obtain ⟨η₀, -, hη₀⟩ := Finset.mem_image.mp hm_mem
  have hm_pos : 0 < m := by
    rw [← hη₀]
    exact hrpos η₀
  refine ⟨m, hm_pos, ?_⟩
  intro η q hq
  apply hr η q
  exact lt_of_lt_of_le hq (Finset.min'_le radii (r η)
    (Finset.mem_image.mpr ⟨η, Finset.mem_univ η, rfl⟩))

/-- The uniform potential collar can be chosen short enough that the collars of the two endpoint
germs of every edge are disjoint.  This is the finite-graph input used in the no-Zeno estimate. -/
theorem exists_uniform_disjoint_endpoint_potential_collar [Nonempty Γ.Edge] {ε : ℝ}
    (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ (∀ e : Γ.Edge, r < Γ.length e / 2) ∧
      ∀ η : Γ.EdgeEnd, ∀ q : ℝ,
        |q - FiniteMetricGraph.EdgeEnd.coordinate Γ η| < r →
          |V.extension η.1 q - V.vertexValue η.vertex| < ε := by
  obtain ⟨r₁, hr₁, hpotential⟩ := V.exists_uniform_endpoint_potential_collar hε
  obtain ⟨r₂, hr₂, hlength⟩ := Γ.exists_uniform_endpointCollarRadius
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_, ?_⟩
  · intro e
    exact lt_of_le_of_lt (min_le_right _ _) (hlength e)
  · intro η q hq
    exact hpotential η q (lt_of_lt_of_le hq (min_le_left _ _))

end MechanicalPotential
end HamiltonianMetricGraphs
