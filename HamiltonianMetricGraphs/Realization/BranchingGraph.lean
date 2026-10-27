/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.FreeGraphTrajectory

/-!
# The explicit branching graph `Γ⋆` and its routing law

`Γ⋆` is the star with three unit-length edges: a single valence-3 vertex `v⋆` together with three
outer vertices of valence 1.  Writing `η₁, η₂, η₃` for the three edge-ends incident to `v⋆`, the
routing law is

  `F⋆(η₁) = η₂`,  `F⋆(η₂) = η₁`,  `F⋆(η₃) = η₃`,

which is speed-independent and involutive.  At each outer vertex there is only one incident end,
so the routing law there is forced to be the identity (total reflection).

The compact regular energy window is `K⋆ = [1/2, 2]`: with the zero potential the only exceptional
energy is `0`, which `K⋆` avoids.

Mathematical proof step: the explicit finite metric graph and speed-independent involutive routing
law of the microscopic-realization theorem.
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph

/-! ### Routing laws from germ involutions -/

/-- A routing law built from an involution of endpoint germs that preserves the incident vertex.
This is the convenient way to present a concrete routing law. -/
def RoutingLaw.ofGermMap {Γ : FiniteMetricGraph} (g : Γ.EdgeEnd → Γ.EdgeEnd)
    (hv : ∀ η, EdgeEnd.vertex Γ (g η) = EdgeEnd.vertex Γ η)
    (hg : ∀ η, g (g η) = η) : RoutingLaw Γ where
  route _ η := ⟨g η.1, by rw [hv]; exact η.2⟩
  route_route _ η := Subtype.ext (hg η.1)

@[simp] theorem RoutingLaw.routeGerm_ofGermMap {Γ : FiniteMetricGraph}
    (g : Γ.EdgeEnd → Γ.EdgeEnd) (hv : ∀ η, EdgeEnd.vertex Γ (g η) = EdgeEnd.vertex Γ η)
    (hg : ∀ η, g (g η) = η) (η : Γ.EdgeEnd) :
    (RoutingLaw.ofGermMap g hv hg).routeGerm η = g η := rfl

/-! ### The star graph -/

/-- The three-armed star: one valence-3 vertex `0` and three outer vertices `1, 2, 3`, joined by
three edges of length `1`. -/
abbrev starGraph : FiniteMetricGraph where
  Vertex := Fin 4
  Edge := Fin 3
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  endpoint e b := if b then e.succ else 0
  length _ := 1
  length_pos _ := one_pos

/-- The branching vertex of `Γ⋆`. -/
def vStar : starGraph.Vertex := 0

instance : Nonempty starGraph.Edge := ⟨0⟩

theorem starGraph_length_eq_one : ∀ e : starGraph.Edge, starGraph.length e = 1 := fun _ => rfl

@[simp] theorem starGraph_vertex_false (e : starGraph.Edge) :
    EdgeEnd.vertex starGraph (e, false) = vStar := rfl

@[simp] theorem starGraph_vertex_true (e : starGraph.Edge) :
    EdgeEnd.vertex starGraph (e, true) = e.succ := rfl

/-- The ends incident to the branching vertex are exactly the ends with selector `false`. -/
theorem snd_eq_false_of_vertex_vStar {η : starGraph.EdgeEnd}
    (h : EdgeEnd.vertex starGraph η = vStar) : η.2 = false := by
  rcases η with ⟨e, b⟩
  cases b
  · rfl
  · exact absurd (starGraph_vertex_true e ▸ h) (Fin.succ_ne_zero e)

/-- The three ends at the branching vertex, indexed by the three edges: this exhibits `v⋆` as a
vertex of valence exactly `3`. -/
def starIncidentEquiv : starGraph.IncidentEnds vStar ≃ starGraph.Edge where
  toFun η := η.1.1
  invFun e := ⟨(e, false), rfl⟩
  left_inv η := by
    apply Subtype.ext
    rcases η with ⟨⟨e, b⟩, h⟩
    have hb : b = false := snd_eq_false_of_vertex_vStar h
    simp [hb]
  right_inv _ := rfl

/-- `v⋆` has valence exactly `3`: the model is genuinely branching. -/
theorem card_starIncidentEnds : Nat.card (starGraph.IncidentEnds vStar) = 3 := by
  rw [Nat.card_congr starIncidentEquiv]
  simp

/-! ### The routing law -/

/-- The edge permutation realized at the branching vertex: it exchanges edges `0` and `1` and
fixes edge `2`. -/
def swapEdge : starGraph.Edge → starGraph.Edge
  | 0 => 1
  | 1 => 0
  | 2 => 2

theorem swapEdge_involutive : ∀ e : starGraph.Edge, swapEdge (swapEdge e) = e := by decide

/-- The germ involution of `Γ⋆`: at the branching vertex (selector `false`) the edge is swapped;
at an outer vertex (selector `true`) the single incident end is reflected. -/
def starGermMap (η : starGraph.EdgeEnd) : starGraph.EdgeEnd :=
  cond η.2 η (swapEdge η.1, false)

@[simp] theorem starGermMap_true (e : starGraph.Edge) :
    starGermMap (e, true) = (e, true) := rfl

@[simp] theorem starGermMap_false (e : starGraph.Edge) :
    starGermMap (e, false) = (swapEdge e, false) := rfl

theorem starGermMap_of_true {η : starGraph.EdgeEnd} (h : η.2 = true) : starGermMap η = η := by
  rw [starGermMap, h]
  rfl

theorem starGermMap_of_false {η : starGraph.EdgeEnd} (h : η.2 = false) :
    starGermMap η = (swapEdge η.1, false) := by
  rw [starGermMap, h]
  rfl

theorem starGermMap_vertex (η : starGraph.EdgeEnd) :
    EdgeEnd.vertex starGraph (starGermMap η) = EdgeEnd.vertex starGraph η := by
  rcases hb : η.2 with _ | _
  · rw [starGermMap_of_false hb, starGraph_vertex_false]
    rcases η with ⟨e, b⟩
    cases b
    · rfl
    · exact absurd hb (by simp)
  · rw [starGermMap_of_true hb]

theorem starGermMap_involutive (η : starGraph.EdgeEnd) :
    starGermMap (starGermMap η) = η := by
  rcases hb : η.2 with _ | _
  · rw [starGermMap_of_false hb, starGermMap_false, swapEdge_involutive, ← hb]
  · rw [starGermMap_of_true hb, starGermMap_of_true hb]

/-- The routing law `F⋆`: at the branching vertex it exchanges the ends of edges `0` and `1` and
reflects the end of edge `2`; at each outer vertex the single incident end is reflected. -/
def starRouting : RoutingLaw starGraph :=
  RoutingLaw.ofGermMap starGermMap starGermMap_vertex starGermMap_involutive

@[simp] theorem starRouting_routeGerm (η : starGraph.EdgeEnd) :
    starRouting.routeGerm η = starGermMap η := rfl

/-! #### The three channels at the branching vertex -/

/-- The first channel at `v⋆`. -/
def channel₁ : starGraph.EdgeEnd := (0, false)

/-- The second channel at `v⋆`. -/
def channel₂ : starGraph.EdgeEnd := (1, false)

/-- The third channel at `v⋆`. -/
def channel₃ : starGraph.EdgeEnd := (2, false)

theorem channel_ne₁₂ : channel₁ ≠ channel₂ := by decide
theorem channel_ne₁₃ : channel₁ ≠ channel₃ := by decide
theorem channel_ne₂₃ : channel₂ ≠ channel₃ := by decide

/-- **The routing law is the prescribed one**: `F⋆(η₁) = η₂`. -/
theorem starRouting_channel₁ : starRouting.routeGerm channel₁ = channel₂ := rfl

/-- `F⋆(η₂) = η₁`. -/
theorem starRouting_channel₂ : starRouting.routeGerm channel₂ = channel₁ := rfl

/-- `F⋆(η₃) = η₃`. -/
theorem starRouting_channel₃ : starRouting.routeGerm channel₃ = channel₃ := rfl

/-- `F⋆` is involutive, as required of a reversible routing law. -/
theorem starRouting_involutive (η : starGraph.EdgeEnd) :
    starRouting.routeGerm (starRouting.routeGerm η) = η :=
  starRouting.routeGerm_routeGerm η

/-! ### The compact regular energy window -/

/-- The compact regular energy window `K⋆ = [1/2, 2]`. -/
def windowStar : Set ℝ := Icc (1 / 2 : ℝ) 2

theorem isCompact_windowStar : IsCompact windowStar := isCompact_Icc

/-- `K⋆` avoids the only exceptional energy `0` of the zero potential. -/
theorem windowStar_regular :
    ∀ E ∈ windowStar, E ∉ (zeroPotential starGraph).exceptionalEnergies := by
  intro E hE
  refine zeroPotential_not_mem_exceptionalEnergies ?_
  have : (1 / 2 : ℝ) ≤ E := hE.1
  linarith

/-! ### The graph trajectories of `Γ⋆` -/

open MechanicalPotential

/-- The deterministic graph-scattering trajectory of `Γ⋆` for the routing law `F⋆`, starting at
coordinate `q₀` strictly inside the edge of `η₀`, with speed `c`, and followed through `N`
router passages. -/
noncomputable def starTrajectory (η₀ : starGraph.EdgeEnd) (q₀ c : ℝ)
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (N : ℕ) (hN : 1 ≤ N) :
    GraphTrajectory (zeroPotential starGraph) starRouting :=
  freeGraphTrajectory starRouting starGraph_length_eq_one η₀ q₀ c hq₀ hc N hN

@[simp] theorem starTrajectory_N (η₀ : starGraph.EdgeEnd) (q₀ c : ℝ)
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (N : ℕ) (hN : 1 ≤ N) :
    (starTrajectory η₀ q₀ c hq₀ hc N hN).N = N := rfl

@[simp] theorem starTrajectory_germ (η₀ : starGraph.EdgeEnd) (q₀ c : ℝ)
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (N : ℕ) (hN : 1 ≤ N) (j : ℕ) :
    (starTrajectory η₀ q₀ c hq₀ hc N hN).germ j = starRouting.itinerary η₀ j := rfl

/-- The energy of a star trajectory is `c² / 2`. -/
theorem starTrajectory_energy (η₀ : starGraph.EdgeEnd) (q₀ c : ℝ)
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (N : ℕ) (hN : 1 ≤ N) :
    (starTrajectory η₀ q₀ c hq₀ hc N hN).energy = c ^ 2 / 2 := by
  change (zeroPotential starGraph).hamiltonian _ _
    (FreeTrajectory.momentum starRouting η₀ c 0) = _
  rw [zeroPotential_hamiltonian]
  change (EdgeEnd.sign starGraph η₀ * c) ^ 2 / 2 = _
  rw [mul_pow, starGraph.edgeEnd_sign_sq η₀, one_mul]

/-- A star trajectory whose speed comes from `[1, 2]` has its energy in `K⋆`. -/
theorem starTrajectory_energy_mem (η₀ : starGraph.EdgeEnd) (q₀ : ℝ) {c : ℝ}
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (N : ℕ) (hN : 1 ≤ N)
    (hcw : c ∈ Icc (1 : ℝ) 2) :
    (starTrajectory η₀ q₀ c hq₀ hc N hN).energy ∈ windowStar := by
  rw [starTrajectory_energy]
  obtain ⟨h1, h2⟩ := hcw
  exact ⟨by nlinarith, by nlinarith⟩

/-! ### The two orbit types of `Γ⋆` -/

/-- Starting from channel `3` the itinerary stays on edge `2` forever: the third channel is
reflected back into itself, exactly as `F⋆(η₃) = η₃` prescribes. -/
theorem itinerary_channel₃_edge (j : ℕ) :
    (starRouting.itinerary channel₃ j).1 = (2 : starGraph.Edge) := by
  induction j with
  | zero => rfl
  | succ i ih =>
      rw [RoutingLaw.itinerary_succ, otherEnd_fst, starRouting_routeGerm]
      rcases hb : (starRouting.itinerary channel₃ i).2 with _ | _
      · rw [starGermMap_of_false hb, ih]
        rfl
      · rw [starGermMap_of_true hb, ih]

/-- Starting from channel `1` the itinerary alternates between edges `0` and `1` and never enters
edge `2`: this is the deterministic `1 ↔ 2` routing. -/
theorem itinerary_channel₁_edge (j : ℕ) :
    (starRouting.itinerary channel₁ j).1 = (0 : starGraph.Edge) ∨
      (starRouting.itinerary channel₁ j).1 = (1 : starGraph.Edge) := by
  induction j with
  | zero => exact Or.inl rfl
  | succ i ih =>
      rw [RoutingLaw.itinerary_succ, otherEnd_fst, starRouting_routeGerm]
      rcases hb : (starRouting.itinerary channel₁ i).2 with _ | _
      · rw [starGermMap_of_false hb]
        rcases ih with h | h <;> rw [h] <;> simp [swapEdge]
      · rw [starGermMap_of_true hb]
        exact ih

/-- The `1 ↔ 2` orbit never visits the third channel. -/
theorem itinerary_channel₁_ne_two (j : ℕ) :
    (starRouting.itinerary channel₁ j).1 ≠ (2 : starGraph.Edge) := by
  rcases itinerary_channel₁_edge j with h | h <;> rw [h] <;> decide

end HamiltonianMetricGraphs
