/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.MicroscopicCompleteness
import HamiltonianMetricGraphs.Realization.FreeGraphTrajectory

/-!
# Prepared states and the hypotheses (E), (J), (D)

This file states Definition IX.4 of the paper (`def:prepared`) and the three hypotheses (E), (J),
(D) of Sec. IX.B, exactly as printed.  They are statements about the flow `Φ^ε_t` of
`H_ε = ½|ξ|² + W_ε` alone (`ThinHamiltonianNetwork.flow`, `MicroscopicCompleteness.lean`);
neither the projected `HybridChain` nor the graph trajectory occurs in them.

## Prepared states (Definition IX.4)

A state `(x, ξ)` is **prepared towards the end `η`** of the edge `e` if

* (P1) `δ_ε ≤ q_e(x) ≤ ℓ_e - δ_ε`;
* (P2) `|y_e(x)| ≤ w_ε` and `E^⊥_{ε,e}(x, ξ) ≤ λ_ε`;
* (P3) `σ(η) p_e(ξ) > 0`;
* (P4) `H_e(pr_e(x, ξ)) ∈ K`.

It is **arriving at `η`** if in addition `q_e(x) = q^ε_η = a_η - σ(η) δ_ε`, and **departing
through `η`** if it is prepared towards `η̄` and `q_e(x) = q^ε_η`.

## The hypotheses

For a family `F` of maps `F_v` of the incident ends (`RoutingMap`, not assumed involutive) and
`z(t) = Φ^ε_t(z) = (x(t), ξ(t))`, the network satisfies (E), (J), (D) on `K` if for every
`ε ∈ (0, ε₀)`, every end `η` (`e` its edge, `e'` the edge of `F(η)`) and every state `z`:

* (E) `SatisfiesEdgeReduction` — if `z` is prepared towards `η` and not arriving at `η`, there is
  `b > 0` with (E1) `δ_ε < q_e(x(t)) < ℓ_e - δ_ε` for `0 < t < b` and (P2) for `0 ≤ t ≤ b`,
  (E2) `z(b)` arriving at `η`, (E3) `|⟨∇W_ε(x(t)), τ_e⟩ - V_e'(q_e(x(t)))| ≤ γ_ε` for
  `0 ≤ t ≤ b`;
* (J) `JunctionScatteringMap` — if `z` is arriving at `η`, there is `b ∈ (0, θ_ε]` with `z(b)`
  departing through `F(η)` and `|p_{e'}(ξ(b)) + σ(F(η)) |p_e(ξ(0))|| ≤ μ_ε`;
* (D) `ChannelUniquenessMap` — if `z` is arriving at `η`, then `z(t)` is not departing through any
  end other than `F(η)` for `0 < t ≤ θ_ε`.

For a routing law `F` (involutive), (J) is `JunctionScatteringConvergesTo` and (J) together with
(D) is `HasDeterministicChannelReduction`.

The conclusions of (E) and (J) are packaged as `EdgeFlight` and `JunctionPassage`, stated for an
arbitrary curve `t ↦ (x(t), ξ(t))` on an arbitrary time interval `[a, b]`; the hypotheses use them
for the flow and `a = 0`.  The same structures serve to verify the hypotheses on explicit
trajectories (`StarEdge.lean`, `StarJunction.lean`, …) and to assemble the flights of a run
(`ThinRun.lean`).
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

/-! ### Families of maps of the incident ends -/

/-- **A speed-independent routing map**: at every vertex a map `F_v` of the incident edge-ends.
Unlike `RoutingLaw`, no involution axiom `F_v² = id` is imposed.  This is the "family `F` of maps
`F_v : E_v^∂ → E_v^∂`" for which the paper states (E), (J), (D). -/
structure RoutingMap (Γ : FiniteMetricGraph) where
  /-- the incident end through which a particle arriving along an incident end departs -/
  route : ∀ v : Γ.Vertex, Γ.IncidentEnds v → Γ.IncidentEnds v

namespace RoutingMap

variable {Γ : FiniteMetricGraph} (F : RoutingMap Γ)

/-- The endpoint germ `F(η) = F_{v(η)}(η)`. -/
def routeGerm (η : Γ.EdgeEnd) : Γ.EdgeEnd := (F.route η.vertex ⟨η, rfl⟩).1

/-- The routed germ is incident to the same vertex. -/
theorem routeGerm_vertex (η : Γ.EdgeEnd) : (F.routeGerm η).vertex = η.vertex :=
  (F.route η.vertex ⟨η, rfl⟩).2

/-- Routing an incident end and then forgetting the incidence proof is `routeGerm`. -/
theorem route_fst_eq_routeGerm {v : Γ.Vertex} (ξ : Γ.IncidentEnds v) :
    (F.route v ξ).1 = F.routeGerm ξ.1 := by
  obtain ⟨η, hη⟩ := ξ
  subst hη
  rfl

/-- **A routing map whose germ map is involutive is a routing law.** -/
def toRoutingLaw (h : ∀ η : Γ.EdgeEnd, F.routeGerm (F.routeGerm η) = η) : RoutingLaw Γ where
  route := F.route
  route_route v η := Subtype.ext (by rw [F.route_fst_eq_routeGerm, F.route_fst_eq_routeGerm, h])

@[simp] theorem toRoutingLaw_route (h : ∀ η : Γ.EdgeEnd, F.routeGerm (F.routeGerm η) = η) :
    (F.toRoutingLaw h).route = F.route := rfl

end RoutingMap

/-- A routing law, with its involution axiom forgotten. -/
def RoutingLaw.toRoutingMap {Γ : FiniteMetricGraph} (F : RoutingLaw Γ) : RoutingMap Γ where
  route := F.route

@[simp] theorem RoutingLaw.toRoutingMap_route {Γ : FiniteMetricGraph} (F : RoutingLaw Γ) :
    F.toRoutingMap.route = F.route := rfl

@[simp] theorem RoutingLaw.toRoutingMap_routeGerm {Γ : FiniteMetricGraph} (F : RoutingLaw Γ)
    (η : Γ.EdgeEnd) : F.toRoutingMap.routeGerm η = F.routeGerm η := rfl

@[simp] theorem RoutingMap.toRoutingLaw_toRoutingMap {Γ : FiniteMetricGraph} (F : RoutingMap Γ)
    (h : ∀ η : Γ.EdgeEnd, F.routeGerm (F.routeGerm η) = η) :
    (F.toRoutingLaw h).toRoutingMap = F := rfl

/-! ### The window condition -/

/-- **The window condition `K ⊂ (max_Γ V, ∞)`** (`eq:window-above`): every energy of `K` exceeds
every value of the potential on `Γ`, at the vertices and on the closed edges. -/
def MechanicalPotential.IsWindowAbove {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
    (K : Set ℝ) : Prop :=
  ∀ E ∈ K, (∀ v : Γ.Vertex, V.vertexValue v < E) ∧
    ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), V.extension e q < E

/-- The window condition implies `K ∩ Exc = ∅`. -/
theorem MechanicalPotential.IsWindowAbove.not_mem_exceptionalEnergies {Γ : FiniteMetricGraph}
    {V : MechanicalPotential Γ} {K : Set ℝ} (h : V.IsWindowAbove K) :
    ∀ E ∈ K, E ∉ V.exceptionalEnergies := by
  intro E hE hmem
  obtain ⟨v, hv⟩ := V.mem_exceptionalEnergies_iff.mp hmem
  have := (h E hE).1 v
  linarith

theorem MechanicalPotential.IsWindowAbove.mono {Γ : FiniteMetricGraph}
    {V : MechanicalPotential Γ} {K K' : Set ℝ} (h : V.IsWindowAbove K) (hK : K' ⊆ K) :
    V.IsWindowAbove K' :=
  fun E hE => h E (hK hE)

/-- The zero potential has zero derivative. -/
@[simp] theorem zeroPotential_extension_deriv {Γ : FiniteMetricGraph} (e : Γ.Edge) (q : ℝ) :
    deriv ((zeroPotential Γ).extension e) q = 0 :=
  deriv_const q 0

/-- For the zero potential, the window condition is `K ⊂ (0, ∞)`. -/
theorem zeroPotential_isWindowAbove {Γ : FiniteMetricGraph} {K : Set ℝ}
    (hK : ∀ E ∈ K, 0 < E) : (zeroPotential Γ).IsWindowAbove K :=
  fun E hE => ⟨fun _ => by simpa using hK E hE, fun _ _ _ => by simpa using hK E hE⟩

namespace ThinHamiltonianNetwork

variable {Γ : FiniteMetricGraph} (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ)
  (K : Set ℝ)

/-! ### Prepared, arriving and departing states (Definition IX.4) -/

/-- **A state prepared towards the end `η`** (Definition IX.4, (P1)–(P4)). -/
structure Prepared (ε : ℝ) (η : Γ.EdgeEnd) (x p : ℝ × ℝ) : Prop where
  /-- (P1) `δ_ε ≤ q_e(x) ≤ ℓ_e - δ_ε` -/
  inside : N.long η.1 x ∈ Icc (N.offset ε) (Γ.length η.1 - N.offset ε)
  /-- (P2) `|y_e(x)| ≤ w_ε` -/
  transverse : |N.trans η.1 x| ≤ N.tubeWidth ε
  /-- (P2) `E^⊥_{ε,e}(x, ξ) ≤ λ_ε` -/
  transEnergy_le : N.transEnergy ε η.1 x p ≤ N.transErr ε
  /-- (P3) `σ(η) p_e(ξ) > 0` -/
  towards : 0 < EdgeEnd.sign Γ η * N.longP η.1 p
  /-- (P4) `H_e(pr_e(x, ξ)) ∈ K` -/
  energy_mem : V.hamiltonian η.1 (N.long η.1 x) (N.longP η.1 p) ∈ K

/-- **Arriving at the end `η`**: prepared towards `η`, and `q_e(x) = q^ε_η = a_η - σ(η) δ_ε`. -/
structure Arriving (ε : ℝ) (η : Γ.EdgeEnd) (x p : ℝ × ℝ) : Prop where
  prepared : N.Prepared V K ε η x p
  boundary : N.long η.1 x = EdgeEnd.coordinate Γ η - EdgeEnd.sign Γ η * N.offset ε

/-- **Departing through the end `ζ`**: prepared towards `ζ̄`, and `q_e(x) = q^ε_ζ`. -/
structure Departing (ε : ℝ) (ζ : Γ.EdgeEnd) (x p : ℝ × ℝ) : Prop where
  prepared : N.Prepared V K ε (otherEnd ζ) x p
  boundary : N.long ζ.1 x = EdgeEnd.coordinate Γ ζ - EdgeEnd.sign Γ ζ * N.offset ε

/-- The longitudinal distance `|q^ε_η - q|` still to be travelled before reaching the junction
boundary of `η`. -/
noncomputable def toGo (ε : ℝ) (η : Γ.EdgeEnd) (q : ℝ) : ℝ :=
  |EdgeEnd.coordinate Γ η - EdgeEnd.sign Γ η * N.offset ε - q|

variable {N V K}

/-- A prepared state is not arriving exactly when it has a positive distance to go. -/
theorem toGo_pos_of_not_arriving {ε : ℝ} {η : Γ.EdgeEnd} {x p : ℝ × ℝ}
    (hp : N.Prepared V K ε η x p) (hna : ¬ N.Arriving V K ε η x p) :
    0 < N.toGo ε η (N.long η.1 x) := by
  refine abs_pos.mpr (sub_ne_zero.mpr fun h => hna ⟨hp, h.symm⟩)

theorem not_arriving_of_toGo_pos {ε : ℝ} {η : Γ.EdgeEnd} {x p : ℝ × ℝ}
    (h : 0 < N.toGo ε η (N.long η.1 x)) : ¬ N.Arriving V K ε η x p := by
  intro harr
  rw [toGo, harr.boundary, sub_self, abs_zero] at h
  exact lt_irrefl _ h

variable (N V K)

/-! ### Edge flights and junction passages of a curve -/

/-- **An edge flight on `[a, b]`** of the curve `t ↦ (x(t), ξ(t))` towards the end `η`: the
conclusion (E1)–(E3) of the edge hypothesis, for the time interval `[a, b]` instead of `[0, b]`. -/
structure EdgeFlight (ε : ℝ) (η : Γ.EdgeEnd) (x p : ℝ → ℝ × ℝ) (a b : ℝ) : Prop where
  lt : a < b
  /-- (E1) `δ_ε < q_e(x(t)) < ℓ_e - δ_ε` for `a < t < b` -/
  inside : ∀ t ∈ Ioo a b, N.long η.1 (x t) ∈ Ioo (N.offset ε) (Γ.length η.1 - N.offset ε)
  /-- (E1) (P2) for `a ≤ t ≤ b`: `|y_e(x(t))| ≤ w_ε` -/
  transverse : ∀ t ∈ Icc a b, |N.trans η.1 (x t)| ≤ N.tubeWidth ε
  /-- (E1) (P2) for `a ≤ t ≤ b`: `E^⊥_{ε,e}(x(t), ξ(t)) ≤ λ_ε` -/
  transEnergy : ∀ t ∈ Icc a b, N.transEnergy ε η.1 (x t) (p t) ≤ N.transErr ε
  /-- (E2) `z(b)` is arriving at `η` -/
  arrive : N.Arriving V K ε η (x b) (p b)
  /-- (E3) `|⟨∇W_ε(x(t)), τ_e⟩ - V_e'(q_e(x(t)))| ≤ γ_ε` for `a ≤ t ≤ b` -/
  force : ∀ t ∈ Icc a b,
    |N.longGrad ε η.1 (x t) - deriv (V.extension η.1) (N.long η.1 (x t))| ≤ N.forceErr ε

/-- **A junction passage on `[a, b]`** of the curve `t ↦ (x(t), ξ(t))`, entered at the end `η`,
for the germ map `R` (`R = F.routeGerm`): the conclusion of (J), for the time interval `[a, b]`
instead of `[0, b]`.  The particle departs through `R(η)` at time `b ∈ (a, a + θ_ε]`, with
`|p_{e'}(ξ(b)) + σ(R(η)) |p_e(ξ(a))|| ≤ μ_ε`. -/
structure JunctionPassage (R : Γ.EdgeEnd → Γ.EdgeEnd) (ε : ℝ) (η : Γ.EdgeEnd)
    (x p : ℝ → ℝ × ℝ) (a b : ℝ) : Prop where
  lt : a < b
  /-- the residence time is at most `θ_ε` -/
  le : b ≤ a + N.dwell ε
  /-- `z(b)` is departing through `R(η)` -/
  depart : N.Departing V K ε (R η) (x b) (p b)
  /-- `|p_{e'}(ξ(b)) + σ(R(η)) |p_e(ξ(a))|| ≤ μ_ε` -/
  mom : |N.longP (R η).1 (p b) + EdgeEnd.sign Γ (R η) * (|N.longP η.1 (p a)|)| ≤ N.momErr ε

/-! ### The hypotheses (E), (J), (D) -/

/-- **Hypothesis (E), edge reduction.**  For every `ε ∈ (0, ε₀)`, every end `η` and every state
`z = (x, ξ)` prepared towards `η` and not arriving at `η`, there is `b > 0` such that the flow
`z(t) = Φ^ε_t(z)` satisfies (E1)–(E3) on `[0, b]`. -/
def SatisfiesEdgeReduction (ε₀ : ℝ) : Prop :=
  ∀ ε ∈ Ioo 0 ε₀, ∀ (η : Γ.EdgeEnd) (x p : ℝ × ℝ),
    N.Prepared V K ε η x p → ¬ N.Arriving V K ε η x p →
    ∃ b : ℝ, N.EdgeFlight V K ε η (fun t => (N.flow ε t (x, p)).1)
      (fun t => (N.flow ε t (x, p)).2) 0 b

/-- **Hypothesis (J), junction scattering, for a family `F` of maps.**  For every `ε ∈ (0, ε₀)`,
every end `η` and every state `z` arriving at `η`, there is `b ∈ (0, θ_ε]` such that `Φ^ε_b(z)` is
departing through `F(η)` and `|p_{e'}(ξ(b)) + σ(F(η)) |p_e(ξ(0))|| ≤ μ_ε`. -/
def JunctionScatteringMap (F : RoutingMap Γ) (ε₀ : ℝ) : Prop :=
  ∀ ε ∈ Ioo 0 ε₀, ∀ (η : Γ.EdgeEnd) (x p : ℝ × ℝ), N.Arriving V K ε η x p →
    ∃ b : ℝ, N.JunctionPassage V K F.routeGerm ε η (fun t => (N.flow ε t (x, p)).1)
      (fun t => (N.flow ε t (x, p)).2) 0 b

/-- **Hypothesis (D), deterministic channel, for a family `F` of maps.**  For every
`ε ∈ (0, ε₀)`, every end `η` and every state `z` arriving at `η`, the state `Φ^ε_t(z)` is not
departing through any end other than `F(η)` for `0 < t ≤ θ_ε`. -/
def ChannelUniquenessMap (F : RoutingMap Γ) (ε₀ : ℝ) : Prop :=
  ∀ ε ∈ Ioo 0 ε₀, ∀ (η : Γ.EdgeEnd) (x p : ℝ × ℝ), N.Arriving V K ε η x p →
    ∀ t ∈ Ioc 0 (N.dwell ε), ∀ ζ : Γ.EdgeEnd,
      N.Departing V K ε ζ (N.flow ε t (x, p)).1 (N.flow ε t (x, p)).2 → ζ = F.routeGerm η

/-- **Hypothesis (J) for a routing law `F`.** -/
def JunctionScatteringConvergesTo (F : RoutingLaw Γ) (ε₀ : ℝ) : Prop :=
  N.JunctionScatteringMap V K F.toRoutingMap ε₀

/-- **Hypotheses (J) and (D) for a routing law `F`: deterministic channel reduction.**  Whatever
the unresolved transverse data of the incoming state, the particle leaves the junction through
`F_v(η)` (J) and through no other end (D). -/
def HasDeterministicChannelReduction (F : RoutingLaw Γ) (ε₀ : ℝ) : Prop :=
  N.JunctionScatteringConvergesTo V K F ε₀ ∧ N.ChannelUniquenessMap V K F.toRoutingMap ε₀

/-- **Distinct channels are microscopically separated**: no microscopic state can be departing
through two different germs.  This is a purely geometric property of the network. -/
def ChannelsSeparated (ε₀ : ℝ) : Prop :=
  ∀ ε ∈ Ioo 0 ε₀, ∀ ζ ζ' : Γ.EdgeEnd, ∀ x p : ℝ × ℝ,
    N.Departing V K ε ζ x p → N.Departing V K ε ζ' x p → ζ = ζ'

variable {N V K}

/-- The hypotheses are inherited by every smaller scale threshold. -/
theorem SatisfiesEdgeReduction.mono {ε₀ ε₁ : ℝ} (h : N.SatisfiesEdgeReduction V K ε₀)
    (hle : ε₁ ≤ ε₀) : N.SatisfiesEdgeReduction V K ε₁ :=
  fun ε hε => h ε ⟨hε.1, lt_of_lt_of_le hε.2 hle⟩

theorem JunctionScatteringMap.mono {F : RoutingMap Γ} {ε₀ ε₁ : ℝ}
    (h : N.JunctionScatteringMap V K F ε₀) (hle : ε₁ ≤ ε₀) :
    N.JunctionScatteringMap V K F ε₁ :=
  fun ε hε => h ε ⟨hε.1, lt_of_lt_of_le hε.2 hle⟩

theorem ChannelUniquenessMap.mono {F : RoutingMap Γ} {ε₀ ε₁ : ℝ}
    (h : N.ChannelUniquenessMap V K F ε₀) (hle : ε₁ ≤ ε₀) :
    N.ChannelUniquenessMap V K F ε₁ :=
  fun ε hε => h ε ⟨hε.1, lt_of_lt_of_le hε.2 hle⟩

theorem JunctionScatteringConvergesTo.mono {F : RoutingLaw Γ} {ε₀ ε₁ : ℝ}
    (h : N.JunctionScatteringConvergesTo V K F ε₀) (hle : ε₁ ≤ ε₀) :
    N.JunctionScatteringConvergesTo V K F ε₁ :=
  JunctionScatteringMap.mono h hle

theorem ChannelsSeparated.mono {ε₀ ε₁ : ℝ} (h : N.ChannelsSeparated V K ε₀) (hle : ε₁ ≤ ε₀) :
    N.ChannelsSeparated V K ε₁ :=
  fun ε hε => h ε ⟨hε.1, lt_of_lt_of_le hε.2 hle⟩

theorem HasDeterministicChannelReduction.mono {F : RoutingLaw Γ} {ε₀ ε₁ : ℝ}
    (h : N.HasDeterministicChannelReduction V K F ε₀) (hle : ε₁ ≤ ε₀) :
    N.HasDeterministicChannelReduction V K F ε₁ :=
  ⟨h.1.mono hle, h.2.mono hle⟩

/-- Deterministic channel reduction contains junction scattering. -/
theorem JunctionScatteringConvergesTo.of_deterministic {F : RoutingLaw Γ} {ε₀ : ℝ}
    (h : N.HasDeterministicChannelReduction V K F ε₀) :
    N.JunctionScatteringConvergesTo V K F ε₀ :=
  h.1

/-- Channel separation identifies the outgoing channel: if a microscopic state is departing
through `ζ` and also through the routed germ `F_v(η)`, the two germs coincide. -/
theorem eq_routeGerm_of_separated {F : RoutingLaw Γ} {ε₀ ε : ℝ} (hε : ε ∈ Ioo 0 ε₀)
    (hsep : N.ChannelsSeparated V K ε₀) {ζ η : Γ.EdgeEnd} {x p : ℝ × ℝ}
    (h1 : N.Departing V K ε ζ x p) (h2 : N.Departing V K ε (F.routeGerm η) x p) :
    ζ = F.routeGerm η :=
  hsep ε hε ζ (F.routeGerm η) x p h1 h2

/-! ### Translating flights and passages in time -/

/-- An edge flight on `[0, b]` of a curve is an edge flight on `[a, a + b]` of any curve that
agrees with it after a time shift by `a`. -/
theorem EdgeFlight.translate {ε : ℝ} {η : Γ.EdgeEnd} {x p x' p' : ℝ → ℝ × ℝ} {a b : ℝ}
    (h : N.EdgeFlight V K ε η x p 0 b)
    (hx : ∀ t ∈ Icc (0 : ℝ) b, x' (a + t) = x t) (hp : ∀ t ∈ Icc (0 : ℝ) b, p' (a + t) = p t) :
    N.EdgeFlight V K ε η x' p' a (a + b) := by
  have hmem : ∀ t ∈ Icc a (a + b), t - a ∈ Icc (0 : ℝ) b :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hx' : ∀ t ∈ Icc a (a + b), x' t = x (t - a) := fun t ht => by
    rw [← hx _ (hmem t ht)]; congr 1; ring
  have hp' : ∀ t ∈ Icc a (a + b), p' t = p (t - a) := fun t ht => by
    rw [← hp _ (hmem t ht)]; congr 1; ring
  have hb : 0 < b := h.lt
  have hbmem : a + b ∈ Icc a (a + b) := ⟨by linarith, le_rfl⟩
  refine ⟨by linarith, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, ?_, fun t ht => ?_⟩
  · rw [hx' t (Ioo_subset_Icc_self ht)]
    exact h.inside _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · rw [hx' t ht]
    exact h.transverse _ (hmem t ht)
  · rw [hx' t ht, hp' t ht]
    exact h.transEnergy _ (hmem t ht)
  · rw [hx' _ hbmem, hp' _ hbmem, add_sub_cancel_left]
    exact h.arrive
  · rw [hx' t ht]
    exact h.force _ (hmem t ht)

/-- A junction passage on `[0, b]` of a curve is a junction passage on `[a, a + b]` of any curve
that agrees with it after a time shift by `a`. -/
theorem JunctionPassage.translate {R : Γ.EdgeEnd → Γ.EdgeEnd} {ε : ℝ} {η : Γ.EdgeEnd}
    {x p x' p' : ℝ → ℝ × ℝ} {a b : ℝ} (h : N.JunctionPassage V K R ε η x p 0 b)
    (hx : x' (a + b) = x b) (hp0 : p' a = p 0) (hp : p' (a + b) = p b) :
    N.JunctionPassage V K R ε η x' p' a (a + b) := by
  have hb := h.lt
  have hle := h.le
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [hx, hp]
    exact h.depart
  · rw [hp, hp0]
    exact h.mom

/-! ### The force on a flight with constant longitudinal momentum -/

/-- **A flight with constant longitudinal momentum feels no longitudinal force.**  If the
longitudinal momentum of a trajectory is constant on `[a, b]`, `a < b`, then
`⟨∇W_ε(x(t)), τ_e⟩ = 0` there: by Hamilton's equations its derivative is `-⟨∇W_ε, τ_e⟩`, and the
derivative of a constant on a nontrivial interval is `0`. -/
theorem MicroTrajectory.longGrad_eq_zero_of_const {ε S : ℝ} (Θ : N.MicroTrajectory ε S)
    {e : Γ.Edge} {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbS : b ≤ S)
    (hc : ∀ t ∈ Icc a b, N.longP e (Θ.p t) = c) :
    ∀ t ∈ Icc a b, N.longGrad ε e (Θ.x t) = 0 := by
  intro t ht
  have hsub : Icc a b ⊆ Icc (0 : ℝ) S := Icc_subset_Icc ha hbS
  have h1 : HasDerivWithinAt (fun r => N.longP e (Θ.p r)) (N.longP e (N.force ε (Θ.x t)))
      (Icc a b) t :=
    (hasDerivWithinAt_longP e (Θ.ode_mom t (hsub ht))).mono hsub
  have h2 : HasDerivWithinAt (fun r => N.longP e (Θ.p r)) 0 (Icc a b) t :=
    (hasDerivWithinAt_const t (Icc a b) c).congr (fun s hs => hc s hs) (hc t ht)
  have h3 := (uniqueDiffOn_Icc hab t ht).eq_deriv _ h1 h2
  rw [longP_force] at h3
  linarith

end ThinHamiltonianNetwork

end HamiltonianMetricGraphs
