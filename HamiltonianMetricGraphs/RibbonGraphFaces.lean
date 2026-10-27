/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition XI.1: periodic orbits and ribbon faces
-/

import HamiltonianMetricGraphs.RibbonGraph
import HamiltonianMetricGraphs.Bifurcation
import HamiltonianMetricGraphs.ShellCycles

/-!
# Periodic orbits and ribbon faces (Proposition XI.1)

**Proposition XI.1.** *Assume `Γ` is connected and `E > max_Γ V`.  Suppose each
`F_v(·, √(2(E - V(v))))` is a single cyclic permutation of `E_v^∂`.  Then `Π_E` is the face
permutation of the ribbon graph determined by these cyclic orders.  Hence the periodic orbits on
`Σ_E` are in bijection with its faces, and `#cyc(Π_E) = 2 - 2g - #V + #E`, where `g` is the genus
of the associated closed orientable surface.  The period of each orbit is the sum of the flight
times along the corresponding face boundary.*

## The ribbon graph of a rotation system

`FiniteMetricGraph.rotationOf rot` assembles a family of permutations `rot v` of the edge-ends
`E_v^∂` at the vertices `v` into one permutation `σ` of all edge-ends, and
`FiniteMetricGraph.ribbonGraph rot` is the ribbon graph (`RibbonGraph Γ.Edge`, see
`RibbonGraph.lean`) with darts the edge-ends `Γ.EdgeEnd = Γ.Edge × Bool`, vertex rotation `σ` and
edge involution `α(η) = η̄`, the other end of the edge.  If every `rot v` is a single cycle
(`∀ a b, (rot v).SameCycle a b`), the cycles of `σ` are exactly the vertex stars
(`sameCycle_rotationOf_iff`), so the ribbon graph has `#V` vertices if every vertex has an edge
(`numVertices_ribbonGraph`), and it is connected when `Γ` is (`connected_ribbonGraph`).
Connectivity of `Γ` (`FiniteMetricGraph.Connected`) is connectivity of its underlying simple graph
(`SimpleGraph.fromRel` of the incidence relation: loops and multiple edges do not matter).

## The high-energy ribbon graph

`MechanicalPotential.highEnergyRibbon V S hv` is the ribbon graph of the fixed-speed vertex laws
`F_v(·, r_v(E))`, `r_v(E) = √(2(E - V(v)))` (Proposition III.2, `speedPermutation`).

## Main result

`ribbon_faces` — **Proposition XI.1**: under the hypotheses of the proposition (and `Γ` has an
edge, see below),

* `E` is shell-regular and every end is admissible (`G_E` = all edge-ends);
* `Π_E` is the face permutation: `Π_E(η) = φ(η) = σ(η̄)` for every edge-end `η`;
* the cycles of `Π_E` are the faces: `germCycles S E = faces`;
* the periodic orbits on `Σ_E` (the orbits `shellOrbit` of Theorem VIII.5) are in bijection with
  the faces; the orbit of a face `c` is the orbit of the departure state of any of its darts, and
  every point of it is periodic with least period `∑_{ζ ∈ c} t_E(ζ)`, the sum of the flight times
  along the face boundary;
* `#cyc(Π_E) = 2 - 2g - #V + #E`.

## Deviations from the printed statement

* **The genus.**  `g` is the combinatorial genus `RibbonGraph.genus` of the ribbon graph, defined
  by `χ = #V - #E + #F = 2 - 2g`.  `RibbonGraph.lean` proves that this is legitimate — for a
  connected ribbon graph `χ` is even and `χ ≤ 2`, so `g` is a natural number.  That `g` is the
  genus of the closed orientable surface obtained by gluing discs into the faces is the
  classification of surfaces, which is not in Mathlib; it is not formalized.
* **`Γ` has an edge** (`[Nonempty Γ.Edge]`).  The flow of Theorem VI.5 is set up for graphs with an
  edge.  The hypothesis is also needed for the formula: the connected graph with one vertex and no
  edge has `#cyc(Π_E) = 0` and `2 - #V + #E = 1`, which is odd, so no integer `g` satisfies
  `(eq:euler)` there.
* **`E > max_Γ V`** is stated as `V_e < E` on every closed edge and `V(v) < E` at every vertex.
* **"a single cyclic permutation"** is stated as transitivity, `∀ a b, SameCycle a b`, so that a
  vertex of degree one, where `F_v` is the identity (the leaves of the cyclic star), qualifies.
-/

namespace HamiltonianMetricGraphs

open Finset Equiv

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- A metric graph is **connected** when its underlying simple graph (two distinct vertices are
adjacent when an edge joins them) is connected. -/
def Connected : Prop :=
  (SimpleGraph.fromRel fun u v : Γ.Vertex =>
    ∃ e, Γ.endpoint e false = u ∧ Γ.endpoint e true = v).Connected

variable {Γ}

/-- The permutation of all edge-ends assembled from permutations `rot v` of the edge-ends at each
vertex `v`. -/
def rotationOf (rot : ∀ v : Γ.Vertex, Perm (Γ.IncidentEnds v)) : Perm Γ.EdgeEnd :=
  (Equiv.sigmaFiberEquiv fun η : Γ.EdgeEnd => η.vertex).permCongr
    (Equiv.Perm.sigmaCongrRight rot)

/-- **The ribbon graph determined by a rotation system** `rot`: darts the edge-ends, vertex rotation
`rotationOf rot`, and edge involution `η ↦ η̄`. -/
def ribbonGraph (rot : ∀ v : Γ.Vertex, Perm (Γ.IncidentEnds v)) : RibbonGraph Γ.Edge :=
  ⟨rotationOf rot⟩

variable (rot : ∀ v : Γ.Vertex, Perm (Γ.IncidentEnds v))

theorem rotationOf_apply {v : Γ.Vertex} (a : Γ.IncidentEnds v) :
    rotationOf rot a.1 = (rot v a).1 := by
  obtain ⟨η, rfl⟩ := a
  rfl

theorem vertex_rotationOf (η : Γ.EdgeEnd) : (rotationOf rot η).vertex = η.vertex := by
  rw [rotationOf_apply rot (⟨η, rfl⟩ : Γ.IncidentEnds η.vertex)]
  exact (rot _ _).2

theorem rotationOf_pow_apply {v : Γ.Vertex} (a : Γ.IncidentEnds v) (n : ℕ) :
    (rotationOf rot ^ n) a.1 = ((rot v ^ n) a).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Perm.mul_apply, ih, rotationOf_apply, pow_succ', Perm.mul_apply]

/-- If every `rot v` is a single cycle, the cycles of the assembled rotation are the vertex
stars. -/
theorem sameCycle_rotationOf_iff (htrans : ∀ v (a b : Γ.IncidentEnds v), (rot v).SameCycle a b)
    (η ζ : Γ.EdgeEnd) : (rotationOf rot).SameCycle η ζ ↔ ζ.vertex = η.vertex := by
  constructor
  · intro h
    exact sameCycle_of_invariant (fun u : Γ.EdgeEnd => u.vertex = η.vertex)
      (fun u hu => (vertex_rotationOf rot u).trans hu) h rfl
  · intro h
    obtain ⟨n, hn⟩ := sameCycle_iff_exists_nat.mp
      (htrans η.vertex ⟨η, rfl⟩ ⟨ζ, h⟩)
    refine sameCycle_iff_exists_nat.mpr ⟨n, ?_⟩
    rw [rotationOf_pow_apply rot (⟨η, rfl⟩ : Γ.IncidentEnds η.vertex), hn]

/-- With single-cycle vertex rotations, the ribbon graph has one vertex for every vertex of `Γ`
which carries an edge-end. -/
theorem numVertices_ribbonGraph (htrans : ∀ v (a b : Γ.IncidentEnds v), (rot v).SameCycle a b)
    (hinc : ∀ v : Γ.Vertex, ∃ η : Γ.EdgeEnd, η.vertex = v) :
    (ribbonGraph rot).numVertices = Fintype.card Γ.Vertex := by
  unfold RibbonGraph.numVertices numOrbits permOrbits
  set fib : Γ.Vertex → Finset Γ.EdgeEnd := fun v => univ.filter fun ζ => ζ.vertex = v with hfib
  have h1 : (univ.image fun η : Γ.Edge × Bool =>
      univ.filter fun ζ => ((ribbonGraph rot).rotation).SameCycle η ζ) = univ.image fib := by
    ext c
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨η, rfl⟩
      refine ⟨FiniteMetricGraph.EdgeEnd.vertex Γ η, ?_⟩
      ext ζ
      simp only [hfib, mem_filter, mem_univ, true_and]
      exact (sameCycle_rotationOf_iff rot htrans η ζ).symm
    · rintro ⟨v, rfl⟩
      obtain ⟨η, rfl⟩ := hinc v
      refine ⟨η, ?_⟩
      ext ζ
      simp only [hfib, mem_filter, mem_univ, true_and]
      exact sameCycle_rotationOf_iff rot htrans η ζ
  rw [h1, card_image_of_injective _ ?_, card_univ]
  intro v w hvw
  obtain ⟨η, rfl⟩ := hinc v
  have : η ∈ fib η.vertex := by simp [hfib]
  rw [hvw] at this
  simpa [hfib] using this

/-- In a connected graph with an edge, every vertex carries an edge-end. -/
theorem exists_edgeEnd_of_connected [Nonempty Γ.Edge] (hΓ : Γ.Connected) (v : Γ.Vertex) :
    ∃ η : Γ.EdgeEnd, η.vertex = v := by
  obtain ⟨e₀⟩ := (inferInstance : Nonempty Γ.Edge)
  by_cases hv : Γ.endpoint e₀ false = v
  · exact ⟨(e₀, false), hv⟩
  obtain ⟨p⟩ := hΓ.preconnected v (Γ.endpoint e₀ false)
  cases p with
  | nil => exact absurd rfl hv
  | cons h _ =>
      rw [SimpleGraph.fromRel_adj] at h
      rcases h.2 with ⟨e, he, -⟩ | ⟨e, -, he⟩
      · exact ⟨(e, false), he⟩
      · exact ⟨(e, true), he⟩

/-- With single-cycle vertex rotations, the ribbon graph of a connected graph is connected. -/
theorem connected_ribbonGraph (hΓ : Γ.Connected)
    (htrans : ∀ v (a b : Γ.IncidentEnds v), (rot v).SameCycle a b) :
    (ribbonGraph rot).Connected := by
  set R : Γ.EdgeEnd → Γ.EdgeEnd → Prop :=
    fun a b => b = (ribbonGraph rot).rotation a ∨ b = RibbonGraph.edgeInv a with hR
  -- darts at the same vertex are related through the rotation
  have hsame : ∀ η ζ : Γ.EdgeEnd, ζ.vertex = η.vertex → Relation.EqvGen R η ζ := by
    intro η ζ h
    have hs := (sameCycle_rotationOf_iff rot htrans η ζ).mpr h
    exact eqvGen_of_le (fun a b hab => Relation.EqvGen.rel _ _ (Or.inl hab))
      ((sameCycle_iff_eqvGen _ η ζ).mp hs)
  -- the two ends of an edge are related through the edge involution
  have hedge : ∀ e : Γ.Edge, Relation.EqvGen R (e, false) (e, true) :=
    fun e => Relation.EqvGen.rel _ _ (Or.inr rfl)
  -- adjacent vertices carry related darts
  have hadj : ∀ u w : Γ.Vertex, (SimpleGraph.fromRel fun u v : Γ.Vertex =>
      ∃ e, Γ.endpoint e false = u ∧ Γ.endpoint e true = v).Adj u w →
      ∃ ζ : Γ.EdgeEnd, ζ.vertex = w ∧ ∀ η : Γ.EdgeEnd, η.vertex = u → Relation.EqvGen R η ζ := by
    intro u w h
    rw [SimpleGraph.fromRel_adj] at h
    rcases h.2 with ⟨e, he0, he1⟩ | ⟨e, he0, he1⟩
    · refine ⟨(e, true), he1, fun η hη => ?_⟩
      exact Relation.EqvGen.trans _ _ _
        (hsame η (e, false) (he0.trans hη.symm)) (hedge e)
    · refine ⟨(e, false), he0, fun η hη => ?_⟩
      exact Relation.EqvGen.trans _ _ _
        (hsame η (e, true) (he1.trans hη.symm)) (Relation.EqvGen.symm _ _ (hedge e))
  have hwalk : ∀ (u w : Γ.Vertex) (p : (SimpleGraph.fromRel fun u v : Γ.Vertex =>
      ∃ e, Γ.endpoint e false = u ∧ Γ.endpoint e true = v).Walk u w) (η ζ : Γ.EdgeEnd),
      η.vertex = u → ζ.vertex = w → Relation.EqvGen R η ζ := by
    intro u w p
    induction p with
    | nil => intro η ζ hη hζ; exact hsame η ζ (hζ.trans hη.symm)
    | cons h _ ih =>
        intro η ζ hη hζ
        obtain ⟨ξ, hξ, hrel⟩ := hadj _ _ h
        exact Relation.EqvGen.trans _ _ _ (hrel η hη) (ih ξ ζ hξ hζ)
  intro η ζ
  obtain ⟨p⟩ := hΓ.preconnected (EdgeEnd.vertex Γ η) (EdgeEnd.vertex Γ ζ)
  exact hwalk _ _ p η ζ rfl rfl

end FiniteMetricGraph

namespace MechanicalPotential

open Set

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-- The fixed-speed vertex laws `F_v(·, r_v(E))`, `r_v(E) = √(2(E - V(v)))`, at an energy above
every vertex value. -/
noncomputable def highEnergyRotation {E : ℝ} (hv : ∀ v : Γ.Vertex, V.vertexValue v < E)
    (v : Γ.Vertex) : Perm (Γ.IncidentEnds v) :=
  EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v
    ⟨Real.sqrt (2 * (E - V.vertexValue v)), Real.sqrt_pos.mpr (by linarith [hv v])⟩

/-- **The ribbon graph of Proposition XI.1**: the ribbon graph determined by the fixed-speed vertex
laws `F_v(·, √(2(E - V(v))))`. -/
noncomputable def highEnergyRibbon {E : ℝ} (hv : ∀ v : Γ.Vertex, V.vertexValue v < E) :
    RibbonGraph Γ.Edge :=
  FiniteMetricGraph.ribbonGraph (V.highEnergyRotation S hv)

/-- **`Π_E` is the face permutation.**  Above the potential `κ_E(η) = η̄`, and the vertex law at
the far end is the rotation of the ribbon graph. -/
theorem germStep_eq_facePerm {E : ℝ} (hE : V.ShellRegular E)
    (hedge : ∀ e, ∀ q ∈ Icc 0 (Γ.length e), V.extension e q < E)
    (hv : ∀ v : Γ.Vertex, V.vertexValue v < E) (η : Γ.EdgeEnd) :
    V.germStep S E η = (V.highEnergyRibbon S hv).facePerm η := by
  have hη : η ∈ V.allowedGerms E := hv η.vertex
  have hζ := V.retraceStep_fst_of_forall_lt hE hη (hedge η.1)
  set ζ : Γ.EdgeEnd := (η.1, !η.2) with hζdef
  rw [V.germStep_eq_speedPermutation S hE hη hζ
    ⟨Real.sqrt (2 * (E - V.vertexValue ζ.vertex)), Real.sqrt_pos.mpr (by linarith [hv ζ.vertex])⟩
    (V.germSpeed_def ζ E).symm]
  rw [RibbonGraph.facePerm_apply]
  change _ = FiniteMetricGraph.rotationOf (V.highEnergyRotation S hv) ζ
  rw [FiniteMetricGraph.rotationOf_apply (V.highEnergyRotation S hv)
    (⟨ζ, rfl⟩ : Γ.IncidentEnds ζ.vertex)]
  rfl

/-- The cycle of `Π_E` through `η` is the face of `η`. -/
theorem germCycle_eq_face {E : ℝ} (hE : V.ShellRegular E)
    (hedge : ∀ e, ∀ q ∈ Icc 0 (Γ.length e), V.extension e q < E)
    (hv : ∀ v : Γ.Vertex, V.vertexValue v < E) (η : Γ.EdgeEnd) :
    V.germCycle S E η = univ.filter fun ζ => (V.highEnergyRibbon S hv).facePerm.SameCycle η ζ := by
  have hstep : V.germStep S E = (V.highEnergyRibbon S hv).facePerm :=
    funext (V.germStep_eq_facePerm S hE hedge hv)
  ext ζ
  rw [V.mem_germCycle_iff S hE (hv η.vertex), mem_filter, sameCycle_iff_exists_nat, hstep]
  simp only [Finset.mem_univ, true_and, Perm.coe_pow]

/-- The cycles of `Π_E` are the faces. -/
theorem germCycles_eq_faces {E : ℝ} (hE : V.ShellRegular E)
    (hedge : ∀ e, ∀ q ∈ Icc 0 (Γ.length e), V.extension e q < E)
    (hv : ∀ v : Γ.Vertex, V.vertexValue v < E) :
    V.germCycles S E = (V.highEnergyRibbon S hv).faces := by
  classical
  ext c
  rw [V.mem_germCycles S]
  unfold RibbonGraph.faces permOrbits
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨η, -, rfl⟩
    exact ⟨η, (V.germCycle_eq_face S hE hedge hv η).symm⟩
  · rintro ⟨η, rfl⟩
    exact ⟨η, hv (FiniteMetricGraph.EdgeEnd.vertex Γ η), V.germCycle_eq_face S hE hedge hv η⟩

/-- A face is the cycle of `Π_E` through any of its darts. -/
theorem face_eq_germCycle {E : ℝ} (hE : V.ShellRegular E)
    (hedge : ∀ e, ∀ q ∈ Icc 0 (Γ.length e), V.extension e q < E)
    (hv : ∀ v : Γ.Vertex, V.vertexValue v < E) {c : Finset Γ.EdgeEnd}
    (hc : c ∈ (V.highEnergyRibbon S hv).faces) {η : Γ.EdgeEnd} (hη : η ∈ c) :
    c = V.germCycle S E η := by
  rw [V.germCycle_eq_face S hE hedge hv]
  unfold RibbonGraph.faces permOrbits at hc
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hc
  have hdη : (V.highEnergyRibbon S hv).facePerm.SameCycle d η := by simpa using hη
  ext ζ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => hdη.symm.trans h, fun h => hdη.trans h⟩

section Flow

variable [Nonempty Γ.Edge]

/-- **Proposition XI.1 (periodic orbits and ribbon faces).**  Let `Γ` be connected (with an edge),
let `E > max_Γ V` (`V_e < E` on every closed edge and `V(v) < E` at every vertex), and let every
fixed-speed vertex law `F_v(·, √(2(E - V(v))))` be a single cyclic permutation of the edge-ends
`E_v^∂` at `v`.  Let `M` be the ribbon graph determined by these cyclic orders
(`highEnergyRibbon`).  Then:

1. `E` is shell-regular and every edge-end is admissible: `G_E` is the dart set of `M`;
2. `Π_E` **is the face permutation** of `M`: `Π_E(η) = σ(η̄)` for every edge-end `η`;
3. `M` is connected and has `#V` vertices (and `#E` edges);
4. the cycles of `Π_E` are the faces of `M`;
5. **the periodic orbits on `Σ_E` are in bijection with the faces**: the orbit of the face `c`
   is the orbit `shellOrbit` (Theorem VIII.5) of the departure state of any of its darts, every
   point of it is periodic with least period `∑_{ζ ∈ c} t_E(ζ)`, **the sum of the flight times
   along the face boundary**, and `Σ_E` is the union of these orbits;
6. **`#cyc(Π_E) = 2 - 2g - #V + #E`**, `g` the genus of `M`.

The genus `g` is the combinatorial genus `RibbonGraph.genus`, defined by
`#V - #E + #F = 2 - 2g`; that this is a natural number is `RibbonGraph.eulerChar_eq` (for a
connected ribbon graph `#V - #E + #F` is even and at most `2`).  Its identification with the
topological genus of the closed orientable surface of the ribbon graph (classification of surfaces)
is not formalized. -/
theorem ribbon_faces (hΓ : Γ.Connected) {E : ℝ}
    (hedge : ∀ e, ∀ q ∈ Icc 0 (Γ.length e), V.extension e q < E)
    (hv : ∀ v : Γ.Vertex, V.vertexValue v < E)
    (hcyc : ∀ (v : Γ.Vertex) (r : FiniteMetricGraph.PositiveSpeed),
      r.1 = Real.sqrt (2 * (E - V.vertexValue v)) → ∀ a b : Γ.IncidentEnds v,
        (EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r).SameCycle
          a b) :
    ∃ hE : V.ShellRegular E,
      V.allowedGerms E = Set.univ ∧
      (∀ η : Γ.EdgeEnd, V.germStep S E η = (V.highEnergyRibbon S hv).facePerm η) ∧
      ((V.highEnergyRibbon S hv).Connected ∧
        (V.highEnergyRibbon S hv).numVertices = Fintype.card Γ.Vertex ∧
        (V.highEnergyRibbon S hv).numEdges = Fintype.card Γ.Edge) ∧
      V.germCycles S E = (V.highEnergyRibbon S hv).faces ∧
      (∃ f : {c // c ∈ (V.highEnergyRibbon S hv).faces} ≃
          {O : Set (RegularScatteringPhaseSpace (V := V) S) //
            ∃ (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E), O = V.shellOrbit S hE η hη},
        (∀ (c : {c // c ∈ (V.highEnergyRibbon S hv).faces}), ∀ η ∈ c.1,
          (f c).1 = V.shellOrbit S hE η (hv _) ∧
          ∀ z ∈ (f c).1, flow V S z (∑ ζ ∈ c.1, V.flightTime E ζ) = z ∧
            ∀ t ∈ Ioo 0 (∑ ζ ∈ c.1, V.flightTime E ζ), flow V S z t ≠ z) ∧
        ∀ z, z ∈ V.shell S E ↔ ∃ c, z ∈ (f c).1) ∧
      ((V.germCycles S E).card : ℤ) =
        2 - 2 * ((V.highEnergyRibbon S hv).genus : ℤ) - Fintype.card Γ.Vertex +
          Fintype.card Γ.Edge := by
  set M := V.highEnergyRibbon S hv with hM
  have hE : V.ShellRegular E := V.shellRegular_of_forall_lt hedge hv
  have htrans : ∀ v (a b : Γ.IncidentEnds v), (V.highEnergyRotation S hv v).SameCycle a b :=
    fun v a b => hcyc v _ rfl a b
  have hconn : M.Connected := FiniteMetricGraph.connected_ribbonGraph _ hΓ htrans
  have hV : M.numVertices = Fintype.card Γ.Vertex :=
    FiniteMetricGraph.numVertices_ribbonGraph _ htrans
      (FiniteMetricGraph.exists_edgeEnd_of_connected hΓ)
  have hfaces := V.germCycles_eq_faces S hE hedge hv
  have hall : ∀ η : Γ.EdgeEnd, η ∈ V.allowedGerms E := fun η => hv _
  -- a dart of every face
  have hne : ∀ c : {c // c ∈ M.faces}, c.1.Nonempty := by
    rintro ⟨c, hc⟩
    unfold RibbonGraph.faces permOrbits at hc
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨d, by simp [Perm.SameCycle.refl]⟩
  -- the orbit of a face does not depend on the chosen dart
  have horbit : ∀ (c : {c // c ∈ M.faces}) (η ζ : Γ.EdgeEnd), η ∈ c.1 → ζ ∈ c.1 →
      V.shellOrbit S hE η (hall η) = V.shellOrbit S hE ζ (hall ζ) := by
    intro c η ζ hη hζ
    have h1 := V.face_eq_germCycle S hE hedge hv c.2 hη
    rw [h1] at hζ
    exact (V.shellOrbit_eq_of_mem_germCycle S hE (hall η) (hall ζ) hζ).symm
  let g : {c // c ∈ M.faces} →
      {O : Set (RegularScatteringPhaseSpace (V := V) S) //
        ∃ (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E), O = V.shellOrbit S hE η hη} :=
    fun c => ⟨V.shellOrbit S hE (hne c).choose (hall _), (hne c).choose, hall _, rfl⟩
  have hg : ∀ (c : {c // c ∈ M.faces}) (η : Γ.EdgeEnd), η ∈ c.1 →
      (g c).1 = V.shellOrbit S hE η (hall η) :=
    fun c η hη => horbit c _ η (hne c).choose_spec hη
  have hbij : Function.Bijective g := by
    constructor
    · intro c c' hcc'
      obtain ⟨η, hη⟩ := hne c
      obtain ⟨η', hη'⟩ := hne c'
      have h := congrArg Subtype.val hcc'
      rw [hg c η hη, hg c' η' hη'] at h
      have hsc := (V.shellOrbit_eq_iff S hE ⟨η, hall η⟩ ⟨η', hall η'⟩).mp h
      have hmem := (V.mem_germCycle_iff_sameCycle S hE ⟨η, hall η⟩ ⟨η', hall η'⟩).mpr hsc
      apply Subtype.ext
      rw [V.face_eq_germCycle S hE hedge hv c.2 hη, V.face_eq_germCycle S hE hedge hv c'.2 hη',
        V.germCycle_eq_of_mem S hE (hall η) hmem]
    · rintro ⟨O, η, hη, rfl⟩
      have hc : V.germCycle S E η ∈ M.faces := by
        rw [← hfaces, V.mem_germCycles S]
        exact ⟨η, hη, rfl⟩
      refine ⟨⟨_, hc⟩, Subtype.ext ?_⟩
      exact hg ⟨_, hc⟩ η (V.self_mem_germCycle S hE hη)
  refine ⟨hE, Set.eq_univ_of_forall hall, V.germStep_eq_facePerm S hE hedge hv,
    ⟨hconn, hV, rfl⟩, hfaces, ⟨Equiv.ofBijective g hbij, ?_, ?_⟩, ?_⟩
  · intro c η hη
    refine ⟨hg c η hη, ?_⟩
    intro z hz
    rw [Equiv.ofBijective_apply, hg c η hη] at hz
    have hper := V.flow_cyclePeriod_of_mem_shellOrbit S hE (hall η) hz
    have hsum : V.cyclePeriod S E η = ∑ ζ ∈ c.1, V.flightTime E ζ := by
      unfold cyclePeriod
      rw [← V.face_eq_germCycle S hE hedge hv c.2 hη]
    rw [hsum] at hper
    exact hper
  · intro z
    rw [V.mem_shell_iff_exists_mem_shellOrbit S hE z]
    constructor
    · rintro ⟨η, hη, hz⟩
      obtain ⟨c, hc⟩ := hbij.2 ⟨_, η, hη, rfl⟩
      refine ⟨c, ?_⟩
      rw [Equiv.ofBijective_apply, hc]
      exact hz
    · rintro ⟨c, hz⟩
      obtain ⟨η, hη⟩ := hne c
      refine ⟨η, hall η, ?_⟩
      rw [Equiv.ofBijective_apply, hg c η hη] at hz
      exact hz
  · rw [hfaces, ← RibbonGraph.numFaces_eq_card, RibbonGraph.numFaces_eq _ hconn, hV]
    rfl

end Flow

end MechanicalPotential

end HamiltonianMetricGraphs
