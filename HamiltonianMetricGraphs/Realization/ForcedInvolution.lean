/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ThinHypotheses

/-!
# Reversibility is forced

This file formalizes **Proposition IX.5** of the paper ("Reversibility is forced",
`prop:forced-involution`), as printed: if a thin network satisfies (J) and (D) on `K` for a family
`F` of maps `F_v : E_v^∂ → E_v^∂` (`RoutingMap`, not assumed involutive), then `F(F(η)) = η` for
every end `η` at which, for some `ε`, a state is arriving (`forced_involution`).

The proof is the paper's.  Since `H_ε` is even in `ξ`, `Φ^ε_t ∘ ρ̃ = ρ̃ ∘ Φ^ε_{-t}` for
`ρ̃(x, ξ) = (x, -ξ)`; in the form used, `Φ^ε_b(ρ̃ Φ^ε_b z) = ρ̃ z` (`flow_reversal`,
`MicroscopicCompleteness.lean`).  The conditions (P1), (P2), (P4) are invariant under `ρ̃` and (P3)
changes direction (`prepared_neg_iff`), so `ρ̃` maps the states departing through an end onto the
states arriving at it (`arriving_neg_iff`, `departing_neg_iff`).  If `z` arrives at `η` and `z(b)`
departs through `ζ = F(η)` as in (J), then `ρ̃ z(b)` arrives at `ζ` and `Φ^ε_b(ρ̃ z(b)) = ρ̃ z`
departs through `η` with `0 < b ≤ θ_ε`; (D) gives `η = F(ζ)`.

The flow is complete because `W_ε` is bounded below, which is part of the definition of a thin
network (`ThinHamiltonianNetwork.pot_bddBelow`); no further hypothesis is needed.

As a corollary, `F` is a routing law as soon as every end admits an arriving state
(`forcedRoutingLaw`, `exists_routingLaw_of_forced`).
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph MechanicalPotential

namespace ThinHamiltonianNetwork

variable {Γ : FiniteMetricGraph} (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ)
  (K : Set ℝ)

/-! ### Time reversal of prepared, arriving and departing states -/

variable {N V K}

omit V K in
theorem longP_neg (e : Γ.Edge) (p : ℝ × ℝ) : N.longP e (-p) = -N.longP e p := by
  simp only [longP, Prod.fst_neg, Prod.snd_neg]
  ring

omit V K in
theorem transP_neg (e : Γ.Edge) (p : ℝ × ℝ) : N.transP e (-p) = -N.transP e p := by
  simp only [transP, Prod.fst_neg, Prod.snd_neg]
  ring

omit V K in
/-- The transverse energy is invariant under momentum reversal. -/
theorem transEnergy_neg (ε : ℝ) (e : Γ.Edge) (x p : ℝ × ℝ) :
    N.transEnergy ε e x (-p) = N.transEnergy ε e x p := by
  simp only [transEnergy, transP_neg, neg_sq]

omit N K in
/-- The edge Hamiltonian is even in the momentum. -/
theorem _root_.HamiltonianMetricGraphs.MechanicalPotential.hamiltonian_neg (e : Γ.Edge)
    (q p : ℝ) : V.hamiltonian e q (-p) = V.hamiltonian e q p := by
  simp only [MechanicalPotential.hamiltonian, neg_sq]

/-- Momentum reversal maps a state prepared towards `η` to a state prepared towards the other
end of the same edge: (P1), (P2), (P4) are invariant, (P3) reverses. -/
theorem Prepared.neg {ε : ℝ} {η : Γ.EdgeEnd} {x p : ℝ × ℝ} (h : N.Prepared V K ε η x p) :
    N.Prepared V K ε (otherEnd η) x (-p) where
  inside := h.inside
  transverse := h.transverse
  transEnergy_le := by
    change N.transEnergy ε η.1 x (-p) ≤ N.transErr ε
    rw [transEnergy_neg]
    exact h.transEnergy_le
  towards := by
    change 0 < EdgeEnd.sign Γ (otherEnd η) * N.longP η.1 (-p)
    rw [sign_otherEnd, longP_neg, neg_mul_neg]
    exact h.towards
  energy_mem := by
    change V.hamiltonian η.1 (N.long η.1 x) (N.longP η.1 (-p)) ∈ K
    rw [longP_neg, MechanicalPotential.hamiltonian_neg]
    exact h.energy_mem

/-- **Time reversal and preparedness**: `ρ̃(x, p)` is prepared towards `η` iff `(x, p)` is
prepared towards the other end of the edge of `η`. -/
theorem prepared_neg_iff {ε : ℝ} {η : Γ.EdgeEnd} {x p : ℝ × ℝ} :
    N.Prepared V K ε η x (-p) ↔ N.Prepared V K ε (otherEnd η) x p := by
  constructor
  · intro h
    simpa using h.neg
  · intro h
    simpa using h.neg

/-- **Time reversal maps the states departing through `ζ` onto the states arriving at `ζ`.** -/
theorem arriving_neg_iff {ε : ℝ} {ζ : Γ.EdgeEnd} {x p : ℝ × ℝ} :
    N.Arriving V K ε ζ x (-p) ↔ N.Departing V K ε ζ x p :=
  ⟨fun h => ⟨prepared_neg_iff.mp h.prepared, h.boundary⟩,
    fun h => ⟨prepared_neg_iff.mpr h.prepared, h.boundary⟩⟩

/-- **Time reversal maps the states arriving at `η` onto the states departing through `η`.** -/
theorem departing_neg_iff {ε : ℝ} {η : Γ.EdgeEnd} {x p : ℝ × ℝ} :
    N.Departing V K ε η x (-p) ↔ N.Arriving V K ε η x p := by
  rw [← arriving_neg_iff, neg_neg]

/-! ### Reversibility is forced -/

variable (N V K) in
/-- **A state arriving at `η`, for some `ε`**: some `ε ∈ (0, ε₀)` and some state `(x, ξ)`
arriving at `η` at that scale. -/
def AdmitsArrival (ε₀ : ℝ) (η : Γ.EdgeEnd) : Prop :=
  ∃ ε ∈ Ioo 0 ε₀, ∃ x p : ℝ × ℝ, N.Arriving V K ε η x p

/-- **Proposition IX.5 (Reversibility is forced).**  If a thin network satisfies (J) and (D) on
`K` for a family `F` of maps (not assumed involutive), then `F(F(η)) = η` for every end `η` at
which, for some `ε`, a state is arriving.

Proof: let `z` be arriving at `η`, and let `b` be as in (J), so that `z(b)` departs through
`ζ = F(η)`.  Then `ρ̃ z(b)` is arriving at `ζ`, and `Φ^ε_b(ρ̃ z(b)) = ρ̃ z(0)` is departing through
`η`, with `0 < b ≤ θ_ε`.  By (D) applied to `ρ̃ z(b)`, `η = F(ζ)`. -/
theorem forced_involution {F : RoutingMap Γ} {ε₀ : ℝ}
    (hJ : N.JunctionScatteringMap V K F ε₀) (hD : N.ChannelUniquenessMap V K F ε₀)
    {η : Γ.EdgeEnd} (hη : ∃ ε ∈ Ioo 0 ε₀, ∃ x p : ℝ × ℝ, N.Arriving V K ε η x p) :
    F.routeGerm (F.routeGerm η) = η := by
  obtain ⟨ε, hε, x, p, harr⟩ := hη
  obtain ⟨b, hpass⟩ := hJ ε hε η x p harr
  have hb0 : 0 < b := by simpa using hpass.lt
  have hb1 : b ≤ N.dwell ε := by simpa using hpass.le
  -- `z(b)` departs through `ζ = F(η)`, so `ρ̃ z(b)` arrives at `ζ`
  have hdep : N.Departing V K ε (F.routeGerm η) (N.flow ε b (x, p)).1
      (N.flow ε b (x, p)).2 := hpass.depart
  have harr₂ : N.Arriving V K ε (F.routeGerm η) (reversal (N.flow ε b (x, p))).1
      (reversal (N.flow ε b (x, p))).2 := arriving_neg_iff.mpr hdep
  -- `Φ_b(ρ̃ z(b)) = ρ̃ z` departs through `η`
  have hrev : N.flow ε b (reversal (N.flow ε b (x, p))) = (x, -p) := flow_reversal ε hb0.le (x, p)
  have hdep₂ : N.Departing V K ε η
      (N.flow ε b ((reversal (N.flow ε b (x, p))).1, (reversal (N.flow ε b (x, p))).2)).1
      (N.flow ε b ((reversal (N.flow ε b (x, p))).1, (reversal (N.flow ε b (x, p))).2)).2 := by
    rw [Prod.mk.eta, hrev]
    exact departing_neg_iff.mpr harr
  -- (D), applied to `ρ̃ z(b)`
  exact (hD ε hε (F.routeGerm η) _ _ harr₂ b ⟨hb0, hb1⟩ η hdep₂).symm

/-! ### The routing map is a routing law -/

/-- **The routing map is a routing law.**  If every end admits an arriving state, then (J) and
(D) force `F` to be involutive, and `F` is a `RoutingLaw`. -/
def forcedRoutingLaw {F : RoutingMap Γ} {ε₀ : ℝ}
    (hJ : N.JunctionScatteringMap V K F ε₀) (hD : N.ChannelUniquenessMap V K F ε₀)
    (harr : ∀ η : Γ.EdgeEnd, N.AdmitsArrival V K ε₀ η) : RoutingLaw Γ :=
  F.toRoutingLaw fun η => forced_involution hJ hD (harr η)

@[simp] theorem forcedRoutingLaw_toRoutingMap {F : RoutingMap Γ} {ε₀ : ℝ}
    (hJ : N.JunctionScatteringMap V K F ε₀) (hD : N.ChannelUniquenessMap V K F ε₀)
    (harr : ∀ η : Γ.EdgeEnd, N.AdmitsArrival V K ε₀ η) :
    (forcedRoutingLaw hJ hD harr).toRoutingMap = F := rfl

/-- The forced routing law satisfies (J) in the form `JunctionScatteringConvergesTo`, so the
thin-network limit theorem applies to it. -/
theorem junctionScatteringConvergesTo_forcedRoutingLaw {F : RoutingMap Γ} {ε₀ : ℝ}
    (hJ : N.JunctionScatteringMap V K F ε₀) (hD : N.ChannelUniquenessMap V K F ε₀)
    (harr : ∀ η : Γ.EdgeEnd, N.AdmitsArrival V K ε₀ η) :
    N.JunctionScatteringConvergesTo V K (forcedRoutingLaw hJ hD harr) ε₀ :=
  hJ

/-- The forced routing law satisfies (J) and (D), `HasDeterministicChannelReduction`. -/
theorem hasDeterministicChannelReduction_forcedRoutingLaw {F : RoutingMap Γ} {ε₀ : ℝ}
    (hJ : N.JunctionScatteringMap V K F ε₀) (hD : N.ChannelUniquenessMap V K F ε₀)
    (harr : ∀ η : Γ.EdgeEnd, N.AdmitsArrival V K ε₀ η) :
    N.HasDeterministicChannelReduction V K (forcedRoutingLaw hJ hD harr) ε₀ :=
  ⟨hJ, hD⟩

/-- **Corollary.**  If every end admits an arriving state, a routing map satisfying (J) and (D)
comes from a (unique) routing law. -/
theorem exists_routingLaw_of_forced {F : RoutingMap Γ} {ε₀ : ℝ}
    (hJ : N.JunctionScatteringMap V K F ε₀) (hD : N.ChannelUniquenessMap V K F ε₀)
    (harr : ∀ η : Γ.EdgeEnd, N.AdmitsArrival V K ε₀ η) :
    ∃ L : RoutingLaw Γ, L.toRoutingMap = F :=
  ⟨forcedRoutingLaw hJ hD harr, rfl⟩

end ThinHamiltonianNetwork

end HamiltonianMetricGraphs
