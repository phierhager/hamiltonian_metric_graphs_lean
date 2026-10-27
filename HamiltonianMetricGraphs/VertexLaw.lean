/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Liouville-preserving Markov vertex laws are mixtures of deterministic ones
-/

import HamiltonianMetricGraphs.Reversibility
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Markov vertex laws and the deterministic ones

The deterministic vertex laws of this paper are not an alternative to a probabilistic junction
rule: they are its extreme points.

Fix a vertex `v` and a speed `r`.  A **Markov vertex law** assigns to each incoming germ a
probability distribution on the outgoing germs, so it is a row-stochastic matrix `P` on the finite
set `Γ.IncidentEnds v`.  The fixed-speed flux measure of the Liouville measure is the counting
measure on `Γ.IncidentEnds v` (Lemma VI.1), so such a law is **Liouville preserving** exactly when
it also preserves the total flux through the vertex, and that happens exactly when the columns of
`P` sum to one as well (`preservesGermCounting_iff_flux`, `mem_doublyStochastic_iff_vertexLaw`).

Liouville-preserving Markov vertex laws at a fixed speed are therefore exactly the **doubly
stochastic** matrices on the incident germs, and Birkhoff–von Neumann identifies them:

* every deterministic energy-preserving vertex law contributes the permutation matrix of its
  fixed-speed endpoint permutation of Proposition III.2 (`speedMatrix`), which is doubly
  stochastic;
* conversely every permutation of the incident germs is the fixed-speed law of a deterministic
  energy-preserving vertex law (`PermutationLaw.toScattering`, `exists_scattering_speedMatrix_eq`);
* the doubly stochastic matrices are the convex hull of the permutation matrices
  (`doublyStochastic_eq_convexHull_speedMatrix`) and the permutation matrices are precisely their
  extreme points (`extremePoints_eq_speedMatrix`).

Finally, the classical junction rule suggested by the quantum-graph formalism — the squared moduli
`|S_v|²` of a unitary vertex scattering matrix — is doubly stochastic
(`doublyStochastic_normSq_of_unitary`), hence a mixture of the deterministic laws of this paper.
-/

namespace HamiltonianMetricGraphs

open FiniteMetricGraph Matrix

/-! ### Speed-independent deterministic vertex laws -/

/-- A **permutation vertex law**: a bijection of the edge-ends that fixes the vertex of each end.
Unlike `RoutingLaw` no involutivity is assumed, so this covers every deterministic
energy-preserving vertex law that does not depend on the speed. -/
structure PermutationLaw (Γ : FiniteMetricGraph) where
  /-- The end through which a particle arriving along `η` departs. -/
  route : Γ.EdgeEnd → Γ.EdgeEnd
  /-- Routing happens at a vertex, so it does not move the vertex. -/
  route_vertex : ∀ η : Γ.EdgeEnd, (route η).vertex = η.vertex
  /-- The law is deterministic and invertible: a bijection of the ends. -/
  route_bijective : Function.Bijective route

namespace PermutationLaw

variable {Γ : FiniteMetricGraph} (F : PermutationLaw Γ)

theorem edgeEnd_abs_sign (η : Γ.EdgeEnd) : |EdgeEnd.sign Γ η| = 1 := by
  rcases η with ⟨e, b⟩
  cases b <;> simp [EdgeEnd.sign]

/-- The routing law as a permutation of the edge-ends. -/
noncomputable def routeEquiv : Γ.EdgeEnd ≃ Γ.EdgeEnd :=
  Equiv.ofBijective F.route F.route_bijective

@[simp] theorem routeEquiv_apply (η : Γ.EdgeEnd) : F.routeEquiv η = F.route η := rfl

theorem routeEquiv_symm_vertex (η : Γ.EdgeEnd) : (F.routeEquiv.symm η).vertex = η.vertex := by
  have h := F.route_vertex (F.routeEquiv.symm η)
  rw [← F.routeEquiv_apply, F.routeEquiv.apply_symm_apply] at h
  exact h.symm

/-- The routing law at a vertex, as a permutation of the finite set of incident ends. -/
noncomputable def perm (v : Γ.Vertex) : Equiv.Perm (Γ.IncidentEnds v) where
  toFun η := ⟨F.route η.1, by rw [F.route_vertex]; exact η.2⟩
  invFun η := ⟨F.routeEquiv.symm η.1, by rw [F.routeEquiv_symm_vertex]; exact η.2⟩
  left_inv η := Subtype.ext (by
    show F.routeEquiv.symm (F.route η.1) = η.1
    rw [← F.routeEquiv_apply, F.routeEquiv.symm_apply_apply])
  right_inv η := Subtype.ext (by
    show F.route (F.routeEquiv.symm η.1) = η.1
    rw [← F.routeEquiv_apply, F.routeEquiv.apply_symm_apply])

@[simp] theorem perm_apply {v : Γ.Vertex} (η : Γ.IncidentEnds v) :
    (F.perm v η).1 = F.route η.1 := rfl

/-! ### The induced scattering law -/

/-- Incoming covectors at a vertex are sent to outgoing covectors at the same speed along the
routed edge-end. -/
noncomputable def scatter (v : Γ.Vertex) (α : Γ.IncomingBoundary v) : Γ.OutgoingBoundary v :=
  Γ.outgoingAtSpeed (F.perm v ⟨α.1.germ, α.2.1⟩)
    ⟨|α.1.momentum|, abs_pos.mpr α.1.momentum_ne_zero⟩

/-- The inverse: outgoing covectors are sent back along the end that routes into them. -/
noncomputable def unscatter (v : Γ.Vertex) (β : Γ.OutgoingBoundary v) : Γ.IncomingBoundary v :=
  Γ.incomingAtSpeed ((F.perm v).symm ⟨β.1.germ, β.2.1⟩)
    ⟨|β.1.momentum|, abs_pos.mpr β.1.momentum_ne_zero⟩

theorem unscatter_scatter (v : Γ.Vertex) (α : Γ.IncomingBoundary v) :
    F.unscatter v (F.scatter v α) = α := by
  unfold unscatter scatter
  set ξ := F.perm v ⟨α.1.germ, α.2.1⟩ with hξ
  set r : PositiveSpeed := ⟨|α.1.momentum|, abs_pos.mpr α.1.momentum_ne_zero⟩ with hr
  conv_rhs => rw [Γ.incoming_eq_incomingAtSpeed α]
  congr 1
  · have h1 : (⟨(Γ.outgoingAtSpeed ξ r).1.germ, (Γ.outgoingAtSpeed ξ r).2.1⟩ :
        Γ.IncidentEnds v) = ξ := Subtype.ext rfl
    rw [h1, hξ, (F.perm v).symm_apply_apply]
  · apply Subtype.ext
    change |(Γ.outgoingAtSpeed ξ r).1.momentum| = |α.1.momentum|
    rw [outgoingAtSpeed_momentum, abs_neg, abs_mul, edgeEnd_abs_sign, one_mul, hr]
    exact abs_abs _

theorem scatter_unscatter (v : Γ.Vertex) (β : Γ.OutgoingBoundary v) :
    F.scatter v (F.unscatter v β) = β := by
  unfold unscatter scatter
  set ξ := (F.perm v).symm ⟨β.1.germ, β.2.1⟩ with hξ
  set r : PositiveSpeed := ⟨|β.1.momentum|, abs_pos.mpr β.1.momentum_ne_zero⟩ with hr
  conv_rhs => rw [Γ.outgoing_eq_outgoingAtSpeed β]
  congr 1
  · have h1 : (⟨(Γ.incomingAtSpeed ξ r).1.germ, (Γ.incomingAtSpeed ξ r).2.1⟩ :
        Γ.IncidentEnds v) = ξ := Subtype.ext rfl
    rw [h1, hξ, (F.perm v).apply_symm_apply]
  · apply Subtype.ext
    change |(Γ.incomingAtSpeed ξ r).1.momentum| = |β.1.momentum|
    rw [incomingAtSpeed_momentum, abs_mul, edgeEnd_abs_sign, one_mul, hr]
    exact abs_abs _

/-- The permutation law as a bijection between incoming and outgoing covectors at a vertex. -/
noncomputable def scatterEquiv (v : Γ.Vertex) : Γ.IncomingBoundary v ≃ Γ.OutgoingBoundary v where
  toFun := F.scatter v
  invFun := F.unscatter v
  left_inv := F.unscatter_scatter v
  right_inv := F.scatter_unscatter v

/-- **A permutation vertex law is a deterministic energy-preserving vertex law** in the sense of
the paper: the kinetic energy is preserved because the speed is. -/
noncomputable def toScattering (V : MechanicalPotential Γ) :
    MechanicalPotential.EnergyPreservingScattering V where
  map := F.scatterEquiv
  preserves_energy v α := by
    change V.boundaryEnergy (F.scatter v α).1 = V.boundaryEnergy α.1
    unfold scatter
    rw [V.boundaryEnergy_outgoingAtSpeed]
    conv_rhs => rw [Γ.incoming_eq_incomingAtSpeed α]
    rw [V.boundaryEnergy_incomingAtSpeed]

/-- **Proposition III.2 for permutation laws.**  The fixed-speed endpoint permutation of the
induced scattering law is the law itself, at every speed. -/
theorem speedEndpoint_toScattering (V : MechanicalPotential Γ) (v : Γ.Vertex)
    (η : Γ.IncidentEnds v) (r : PositiveSpeed) :
    MechanicalPotential.EnergyPreservingScattering.speedEndpoint V (F.toScattering V) v η r =
      F.perm v η := by
  apply Subtype.ext
  change (F.scatter v (Γ.incomingAtSpeed η r)).1.germ = (F.perm v η).1
  unfold scatter
  rw [outgoingAtSpeed_end]
  have h1 : (⟨(Γ.incomingAtSpeed η r).1.germ, (Γ.incomingAtSpeed η r).2.1⟩ :
      Γ.IncidentEnds v) = η := Subtype.ext rfl
  rw [h1]

/-! ### Realizing a prescribed permutation at one vertex -/

/-- The end through which the law `ofPerm v σ` routes an arriving end: `σ` at the vertex `v`, the
identity everywhere else. -/
noncomputable def ofPermRoute (v : Γ.Vertex) (σ : Equiv.Perm (Γ.IncidentEnds v))
    (η : Γ.EdgeEnd) : Γ.EdgeEnd := by
  classical
  exact if h : η.vertex = v then (σ (⟨η, h⟩ : Γ.IncidentEnds v)).1 else η

theorem ofPermRoute_of_vertex {v : Γ.Vertex} (σ : Equiv.Perm (Γ.IncidentEnds v))
    {η : Γ.EdgeEnd} (h : η.vertex = v) :
    ofPermRoute v σ η = (σ (⟨η, h⟩ : Γ.IncidentEnds v)).1 := by
  classical
  unfold ofPermRoute
  rw [dif_pos h]

theorem ofPermRoute_of_ne {v : Γ.Vertex} (σ : Equiv.Perm (Γ.IncidentEnds v))
    {η : Γ.EdgeEnd} (h : ¬ η.vertex = v) : ofPermRoute v σ η = η := by
  classical
  unfold ofPermRoute
  rw [dif_neg h]

/-- The permutation law that applies `σ` at the vertex `v` and leaves every other end fixed. -/
noncomputable def ofPerm (v : Γ.Vertex) (σ : Equiv.Perm (Γ.IncidentEnds v)) :
    PermutationLaw Γ where
  route := ofPermRoute v σ
  route_vertex := by
    intro η
    by_cases h : η.vertex = v
    · rw [ofPermRoute_of_vertex σ h, (σ (⟨η, h⟩ : Γ.IncidentEnds v)).2, h]
    · rw [ofPermRoute_of_ne σ h]
  route_bijective := by
    refine Finite.injective_iff_bijective.mp ?_
    intro η ζ hηζ
    by_cases hη : η.vertex = v
    · by_cases hζ : ζ.vertex = v
      · rw [ofPermRoute_of_vertex σ hη, ofPermRoute_of_vertex σ hζ] at hηζ
        have h1 : σ (⟨η, hη⟩ : Γ.IncidentEnds v) = σ (⟨ζ, hζ⟩ : Γ.IncidentEnds v) :=
          Subtype.ext hηζ
        exact congrArg (fun x : Γ.IncidentEnds v => x.1) (σ.injective h1)
      · rw [ofPermRoute_of_vertex σ hη, ofPermRoute_of_ne σ hζ] at hηζ
        exact absurd (by rw [← hηζ]; exact (σ (⟨η, hη⟩ : Γ.IncidentEnds v)).2) hζ
    · by_cases hζ : ζ.vertex = v
      · rw [ofPermRoute_of_ne σ hη, ofPermRoute_of_vertex σ hζ] at hηζ
        exact absurd (by rw [hηζ]; exact (σ (⟨ζ, hζ⟩ : Γ.IncidentEnds v)).2) hη
      · rw [ofPermRoute_of_ne σ hη, ofPermRoute_of_ne σ hζ] at hηζ
        exact hηζ

@[simp] theorem ofPerm_perm (v : Γ.Vertex) (σ : Equiv.Perm (Γ.IncidentEnds v))
    (η : Γ.IncidentEnds v) : (ofPerm v σ).perm v η = σ η := by
  apply Subtype.ext
  show ofPermRoute v σ η.1 = (σ η).1
  rw [ofPermRoute_of_vertex σ η.2]
  congr 1

end PermutationLaw

/-! ### Markov vertex laws at a fixed speed -/

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

section VertexLaw

variable {v : Γ.Vertex}

/-- A **Markov vertex law** at the vertex `v`: each incoming germ is assigned a probability
distribution on the outgoing germs. -/
def IsMarkovVertexLaw (P : Matrix (Γ.IncidentEnds v) (Γ.IncidentEnds v) ℝ) : Prop :=
  (∀ η ζ, 0 ≤ P η ζ) ∧ ∀ η, ∑ ζ, P η ζ = 1

/-- A Markov vertex law **preserves the germ counting measure**: the fixed-speed flux measure of
the Liouville measure (Lemma VI.1) is the counting measure on the incident germs, and the law
pushes it forward to itself. -/
def PreservesGermCounting (P : Matrix (Γ.IncidentEnds v) (Γ.IncidentEnds v) ℝ) : Prop :=
  ∀ ζ, ∑ η, P η ζ = 1

/-- **Preserving the germ counting measure is preserving the total flux.**  A Markov vertex law
pushes the counting measure forward to itself exactly when integrating any observable against the
counting measure is unchanged by the law. -/
theorem preservesGermCounting_iff_flux (P : Matrix (Γ.IncidentEnds v) (Γ.IncidentEnds v) ℝ) :
    PreservesGermCounting P ↔
      ∀ f : Γ.IncidentEnds v → ℝ, ∑ η, ∑ ζ, P η ζ * f ζ = ∑ ζ, f ζ := by
  classical
  constructor
  · intro h f
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [← Finset.sum_mul, h ζ, one_mul]
  · intro h ζ
    have hf := h (fun ξ => if ξ = ζ then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq' Finset.univ ζ] at hf
    simpa using hf

/-- **Liouville-preserving Markov vertex laws are the doubly stochastic matrices.** -/
theorem mem_doublyStochastic_iff_vertexLaw
    (P : Matrix (Γ.IncidentEnds v) (Γ.IncidentEnds v) ℝ) :
    P ∈ doublyStochastic ℝ (Γ.IncidentEnds v) ↔
      IsMarkovVertexLaw P ∧ PreservesGermCounting P := by
  rw [mem_doublyStochastic_iff_sum]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-! ### The deterministic laws are the permutation matrices -/

/-- The **transition matrix of a deterministic vertex law** at the vertex `v` and speed `r`: the
permutation matrix of the fixed-speed endpoint permutation of Proposition III.2. -/
noncomputable def speedMatrix (S : V.EnergyPreservingScattering) (v : Γ.Vertex)
    (r : PositiveSpeed) : Matrix (Γ.IncidentEnds v) (Γ.IncidentEnds v) ℝ :=
  (EnergyPreservingScattering.speedPermutation V S v r).permMatrix ℝ

/-- A deterministic vertex law is a Liouville-preserving Markov vertex law. -/
theorem speedMatrix_mem_doublyStochastic (S : V.EnergyPreservingScattering) (v : Γ.Vertex)
    (r : PositiveSpeed) : V.speedMatrix S v r ∈ doublyStochastic ℝ (Γ.IncidentEnds v) :=
  permMatrix_mem_doublyStochastic

/-- **Every permutation matrix on the incident germs is a deterministic vertex law.**  The law can
even be chosen speed independent. -/
theorem exists_scattering_speedMatrix_eq (v : Γ.Vertex)
    (σ : Equiv.Perm (Γ.IncidentEnds v)) :
    ∃ S : V.EnergyPreservingScattering, ∀ r : PositiveSpeed,
      V.speedMatrix S v r = σ.permMatrix ℝ := by
  refine ⟨(PermutationLaw.ofPerm v σ).toScattering V, fun r => ?_⟩
  have hperm : EnergyPreservingScattering.speedPermutation V
      ((PermutationLaw.ofPerm v σ).toScattering V) v r = σ := by
    ext η
    rw [EnergyPreservingScattering.speedPermutation_apply,
      (PermutationLaw.ofPerm v σ).speedEndpoint_toScattering V v η r,
      PermutationLaw.ofPerm_perm]
  rw [speedMatrix, hperm]

/-- **Birkhoff–von Neumann for vertex laws.**  The Liouville-preserving Markov vertex laws at a
fixed speed are exactly the convex combinations of the deterministic laws of this paper. -/
theorem doublyStochastic_eq_convexHull_speedMatrix (v : Γ.Vertex) (r : PositiveSpeed) :
    (doublyStochastic ℝ (Γ.IncidentEnds v) : Set (Matrix (Γ.IncidentEnds v)
        (Γ.IncidentEnds v) ℝ))
      = convexHull ℝ {P | ∃ S : V.EnergyPreservingScattering, V.speedMatrix S v r = P} := by
  rw [doublyStochastic_eq_convexHull_permMatrix]
  congr 1
  ext P
  constructor
  · rintro ⟨σ, rfl⟩
    obtain ⟨S, hS⟩ := V.exists_scattering_speedMatrix_eq v σ
    exact ⟨S, hS r⟩
  · rintro ⟨S, rfl⟩
    exact ⟨EnergyPreservingScattering.speedPermutation V S v r, rfl⟩

/-- **The deterministic laws are exactly the extreme points.**  This is the precise sense in which
the deterministic vertex laws of this paper are the building blocks of every Liouville-preserving
probabilistic junction rule. -/
theorem extremePoints_eq_speedMatrix (v : Γ.Vertex) (r : PositiveSpeed) :
    Set.extremePoints ℝ (doublyStochastic ℝ (Γ.IncidentEnds v) :
        Set (Matrix (Γ.IncidentEnds v) (Γ.IncidentEnds v) ℝ))
      = {P | ∃ S : V.EnergyPreservingScattering, V.speedMatrix S v r = P} := by
  rw [extremePoints_doublyStochastic]
  ext P
  constructor
  · rintro ⟨σ, rfl⟩
    obtain ⟨S, hS⟩ := V.exists_scattering_speedMatrix_eq v σ
    exact ⟨S, hS r⟩
  · rintro ⟨S, rfl⟩
    exact ⟨EnergyPreservingScattering.speedPermutation V S v r, rfl⟩

end VertexLaw

end MechanicalPotential

/-! ### The quantum-graph junction rule -/

/-- **The squared moduli of a unitary vertex scattering matrix are doubly stochastic.**  This is
the classical junction rule suggested by the quantum-graph formalism: the probability of passing
from channel `i` to channel `j` is `|S i j|²`.  Together with Birkhoff–von Neumann it is therefore
a mixture of the deterministic laws of this paper. -/
theorem doublyStochastic_normSq_of_unitary {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    (Matrix.of fun i j => ‖U i j‖ ^ 2) ∈ doublyStochastic ℝ n := by
  classical
  have hz : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hrow : ∀ i, ∑ j, ‖U i j‖ ^ 2 = 1 := by
    intro i
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) i) i
    have hexp : (U * star U) i i = ((∑ j, ‖U i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.mul_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.star_apply, hz (U i j)]
    rw [hexp, Matrix.one_apply_eq] at h
    exact_mod_cast h
  have hcol : ∀ j, ∑ i, ‖U i j‖ ^ 2 = 1 := by
    intro j
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) j) j
    have hexp : (star U * U) j j = ((∑ i, ‖U i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.mul_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.star_apply, mul_comm, hz (U i j)]
    rw [hexp, Matrix.one_apply_eq] at h
    exact_mod_cast h
  rw [mem_doublyStochastic_iff_sum]
  exact ⟨fun i j => by rw [Matrix.of_apply]; positivity, hrow, hcol⟩

end HamiltonianMetricGraphs
