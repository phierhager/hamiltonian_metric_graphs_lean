/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.GateJunction
import HamiltonianMetricGraphs.Realization.StarLimit

/-!
# An explicit energy-dependent deterministic junction

This file contains the main new theorem of the gated model:

> **`explicit_energy_dependent_junction`** (Theorem IX.10) — the *one* smooth microscopic
> Hamiltonian family `H_ε(x,p) = ½|p|² + gatePot2 ε x` on `ℝ² × ℝ²` of the network `N^g`
> (`θ_ε = 32ε`), describing a particle confined to three thin channels of width `O(ε)` meeting in a
> single junction region of diameter `O(ε)`, realizes, for every `ε ∈ (0, 1/100)`, on the two
> **disjoint compact regular** energy windows `K₋ = [1/2, 3/5]` and `K₊ = [3/2, 2]` **two
> different** deterministic routing laws: total reflection `F₋` on `K₋`, and the transmitting law
> `F₊ = F⋆` on `K₊`.

The physical mechanism is an energy-selective barrier — the smooth gate `G_ε` across the through
channel at the branching vertex, supported in `|u| ≤ 2ε`, at least `g₀ = gateHeight = 7/10` on its
core `[-ε, ε]` and of height `E_c = max G_ε = gateCritical ∈ (1.15, 1.365)`, independent of `ε`.
Below `g₀` the particle does not reach the core and is turned back; above `E_c` it passes.  Both
regimes are consequences of Hamilton's equations for the *same* potential and are proved, not
assumed:

* confinement to a channel and the exact splitting of the two-dimensional motion
  (`GateConfinement.lean`),
* exactly free longitudinal motion along an edge, so (E3) holds with `γ_ε = 0` (`GateEdge.lean`),
* correct outgoing-channel selection, independent of the transverse data, with junction residence
  time `≤ θ_ε = 32ε → 0` and exactly preserved outgoing speed (`GateJunction.lean`).

## Between the windows nothing is claimed

The windows lie on either side of the gate, `max K₋ < g₀ < E_c < min K₊`
(`3/5 < 7/10 < 1.15 < E_c < 1.365 < 3/2`).  **No claim whatever is made for energies between
them**, where the junction passes from reflection to transmission and no deterministic routing law
is asserted.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

/-! ### Realization of a routing law on an energy window -/

/-- **The microscopic family `N` realizes the routing law `F` on the energy window `K`.**  This is
exactly the pair of physical hypotheses of `ThinHypotheses.lean`, and — by
`thin_junction_hamiltonian_limit` — it is what makes the projected microscopic trajectories
converge to the deterministic graph flow with vertex law `F`.

The window is a parameter of the predicate, not of the network: the *same* `N` can realize
different laws on different windows.  That is the whole point of the gated model. -/
def ThinHamiltonianNetwork.RealizesOnEnergyWindow {Γ : FiniteMetricGraph}
    (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (K : Set ℝ) (F : RoutingLaw Γ)
    (ε₀ : ℝ) : Prop :=
  N.SatisfiesEdgeReduction V K ε₀ ∧ N.JunctionScatteringConvergesTo V K F ε₀

namespace ThinHamiltonianNetwork

variable {Γ : FiniteMetricGraph} {N : ThinHamiltonianNetwork Γ} {V : MechanicalPotential Γ}
  {K : Set ℝ} {F : RoutingLaw Γ} {ε₀ ε₁ : ℝ}

theorem RealizesOnEnergyWindow.mono (h : N.RealizesOnEnergyWindow V K F ε₀) (hle : ε₁ ≤ ε₀) :
    N.RealizesOnEnergyWindow V K F ε₁ :=
  ⟨h.1.mono hle, h.2.mono hle⟩

theorem RealizesOnEnergyWindow.edge (h : N.RealizesOnEnergyWindow V K F ε₀) :
    N.SatisfiesEdgeReduction V K ε₀ := h.1

theorem RealizesOnEnergyWindow.junction (h : N.RealizesOnEnergyWindow V K F ε₀) :
    N.JunctionScatteringConvergesTo V K F ε₀ := h.2

end ThinHamiltonianNetwork

/-! ### The two routing laws -/

/-- The **low-energy** routing law of the gated junction: total reflection at every germ.  The
gate blocks the branching vertex, so every channel is closed. -/
def gateRoutingLow : RoutingLaw starGraph := RoutingLaw.reflection starGraph

/-- The **high-energy** routing law of the gated junction: the transmitting law `F⋆` of the
ungated model, `η₁ ↦ η₂`, `η₂ ↦ η₁`, `η₃ ↦ η₃`. -/
def gateRoutingHigh : RoutingLaw starGraph := starRouting

@[simp] theorem gateRoutingLow_routeGerm (η : starGraph.EdgeEnd) :
    gateRoutingLow.routeGerm η = η := rfl

@[simp] theorem gateRoutingHigh_routeGerm (η : starGraph.EdgeEnd) :
    gateRoutingHigh.routeGerm η = starRouting.routeGerm η := rfl

/-- **The two laws differ**, on the very channel the gate controls. -/
theorem gateRouting_ne : gateRoutingLow ≠ gateRoutingHigh := by
  intro h
  have h1 : gateRoutingLow.routeGerm channel₁ = gateRoutingHigh.routeGerm channel₁ := by rw [h]
  rw [gateRoutingLow_routeGerm, gateRoutingHigh_routeGerm, starRouting_channel₁] at h1
  exact channel_ne₁₂ h1

theorem gateRouting_routeGerm_ne :
    gateRoutingLow.routeGerm channel₁ ≠ gateRoutingHigh.routeGerm channel₁ := by
  rw [gateRoutingLow_routeGerm, gateRoutingHigh_routeGerm, starRouting_channel₁]
  exact channel_ne₁₂

/-! ### The two realizations -/

/-- **Below the gate, the gated family realizes total reflection.** -/
theorem gateNetwork_realizes_low :
    gateNetwork.RealizesOnEnergyWindow (zeroPotential starGraph) windowLow gateRoutingLow
      (1 / 100) :=
  ⟨gateNetwork_satisfiesEdgeReduction windowLow_subset, gateNetwork_junctionScattering_low⟩

/-- **Above the gate, the same family realizes the transmitting law `F⋆`.** -/
theorem gateNetwork_realizes_high :
    gateNetwork.RealizesOnEnergyWindow (zeroPotential starGraph) windowHigh gateRoutingHigh
      (1 / 100) :=
  ⟨gateNetwork_satisfiesEdgeReduction windowHigh_subset, gateNetwork_junctionScattering_high⟩

/-! ### The theorem -/

/-- **An explicit energy-dependent deterministic junction (Theorem IX.10).**

The network `N^g = gateNetwork` — the smooth microscopic Hamiltonian family
`H_ε(x, p) = ½|p|² + gatePot2 ε x` on `ℝ² × ℝ²`, a classical particle confined to three thin
channels of width `O(ε)` meeting in one junction region of diameter `O(ε)`, with the scales
`δ_ε = 8ε` and `θ_ε = 32ε` — realizes, for every `ε ∈ (0, ε₀)`, `ε₀ = 1/100`, two **different**
deterministic routing laws on the two **disjoint** compact windows `K₋ = [1/2, 3/5]` and
`K₊ = [3/2, 2]` above the potential: total reflection `F₋` on `K₋` and the transmitting law
`F₊ = F⋆` on `K₊`.  In particular the incoming channel `η₁` is routed to `η₁` at low energy and to
`η₂` at high energy.

The gate `G_ε = gateBump ε` is at least `g₀ = gateHeight = 7/10` on its core `[-ε, ε]`; its height
`E_c = max G_ε = gateCritical` does not depend on `ε` and satisfies `1.15 < E_c < 1.365`; and the
windows lie on either side of the gate, `max K₋ < g₀ < E_c < min K₊`.  Nothing is claimed for
energies between the windows. -/
theorem explicit_energy_dependent_junction :
    -- the network `N^g`: its potential and its scales
    (∀ ε, gateNetwork.pot ε = gatePot2 ε) ∧
    (∀ ε, 0 < ε → gateNetwork.offset ε = 8 * ε ∧ gateNetwork.dwell ε = 32 * ε) ∧
    -- the two windows
    IsCompact windowLow ∧ IsCompact windowHigh ∧
    (zeroPotential starGraph).IsWindowAbove windowLow ∧
    (zeroPotential starGraph).IsWindowAbove windowHigh ∧
    Disjoint windowLow windowHigh ∧
    -- the gate: at least `g₀` on its core, of height `E_c = max G_ε` independent of `ε`
    gateHeight = 7 / 10 ∧
    (∀ ε, 0 < ε → ∀ u, |u| ≤ ε → gateHeight ≤ gateBump ε u) ∧
    (∀ ε, 0 < ε → IsGreatest (Set.range (gateBump ε)) gateCritical) ∧
    (115 / 100 : ℝ) < gateCritical ∧ gateCritical < 1365 / 1000 ∧
    -- the windows lie on either side of the gate: `max K₋ < g₀ < E_c < min K₊`
    sSup windowLow < gateHeight ∧ gateHeight < gateCritical ∧ gateCritical < sInf windowHigh ∧
    -- the two realizations, for every `ε ∈ (0, 1/100)`
    gateNetwork.RealizesOnEnergyWindow (zeroPotential starGraph) windowLow gateRoutingLow
      (1 / 100) ∧
    gateNetwork.RealizesOnEnergyWindow (zeroPotential starGraph) windowHigh gateRoutingHigh
      (1 / 100) ∧
    gateRoutingLow ≠ gateRoutingHigh ∧
    gateRoutingLow.routeGerm channel₁ = channel₁ ∧
    gateRoutingHigh.routeGerm channel₁ = channel₂ := by
  have hlow : sSup windowLow = 3 / 5 := csSup_Icc (by norm_num)
  have hhigh : sInf windowHigh = 3 / 2 := csInf_Icc (by norm_num)
  have hh : gateHeight = 7 / 10 := rfl
  refine ⟨fun ε => rfl, fun ε hε => ⟨gateNetwork_offset_of_pos hε, gateNetwork_dwell_of_pos hε⟩,
    isCompact_windowLow, isCompact_windowHigh, windowLow_isWindowAbove, windowHigh_isWindowAbove,
    windowLow_disjoint_windowHigh, hh, fun ε hε u hu => gateBump_ge hε hu,
    fun ε hε => gateCritical_isGreatest hε, gateCritical_gt, gateCritical_lt, ?_,
    gateHeight_lt_gateCritical, ?_, gateNetwork_realizes_low, gateNetwork_realizes_high,
    gateRouting_ne, rfl, ?_⟩
  · rw [hlow, hh]; norm_num
  · rw [hhigh]; linarith [gateCritical_lt]
  · rw [gateRoutingHigh_routeGerm]; exact starRouting_channel₁

/-- **The two regimes belong to the same microscopic Hamiltonian.**  This is the point of the
theorem above, stated separately: the potential is one and the same function of `(ε, x)`; only the
energy window changes. -/
theorem gateNetwork_pot_eq (ε : ℝ) : gateNetwork.pot ε = gatePot2 ε := rfl

variable {ε : ℝ}

/-- The scale threshold of the gated model for an initial coordinate `q₀`. -/
noncomputable def gateEps (q₀ : ℝ) : ℝ := min (1 / 100) (min q₀ (1 - q₀) / 8)

theorem gateEps_le (q₀ : ℝ) : gateEps q₀ ≤ 1 / 100 := min_le_left _ _

theorem gateEps_pos {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) : 0 < gateEps q₀ :=
  lt_min (by norm_num) (div_pos (lt_min hq₀.1 (by linarith [hq₀.2])) (by norm_num))

theorem gateEps_bounds {q₀ ε : ℝ} (h : ε < gateEps q₀) : 8 * ε < q₀ ∧ 8 * ε < 1 - q₀ := by
  have h1 : ε < min q₀ (1 - q₀) / 8 := lt_of_lt_of_le h (min_le_right _ _)
  have h2 : 8 * ε < min q₀ (1 - q₀) := by linarith
  exact ⟨lt_of_lt_of_le h2 (min_le_left _ _), lt_of_lt_of_le h2 (min_le_right _ _)⟩

variable {η₀ : starGraph.EdgeEnd} {q₀ c : ℝ}

/-! ### The well-prepared initial state of the gated model -/

/-- **The well-prepared initial state of the gated model**: the particle sits on the axis of the
tube of the edge of `η₀`, at graph coordinate `q₀`, with purely longitudinal momentum of speed
`c ∈ [1, 2]` pointing towards `η₀`, whose energy `c²/2` lies in the window `K`. -/
noncomputable def gateWellPrepared (η₀ : starGraph.EdgeEnd) {K : Set ℝ} {q₀ c : ℝ}
    (_hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc1 : 1 ≤ c) (_hc2 : c ≤ 2) (hcK : c ^ 2 / 2 ∈ K) :
    WellPreparedInitialState gateNetwork (zeroPotential starGraph) K (gateEps q₀) where
  germ := η₀
  x₀ := fun _ => starX η₀ q₀
  p₀ := fun _ => starP η₀ c
  q := q₀
  r := EdgeEnd.sign starGraph η₀ * c
  prepared := by
    intro ε hε
    have hε0 : 0 < ε := hε.1
    have hεs : ε ≤ 1 / 100 := le_of_lt (lt_of_lt_of_le hε.2 (gateEps_le q₀))
    obtain ⟨hq8, hq8'⟩ := gateEps_bounds hε.2
    have hsq : EdgeEnd.sign starGraph η₀ ^ 2 = 1 := starGraph.edgeEnd_sign_sq η₀
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [gateNetwork_long, gateNetwork_offset_of_pos hε0, starGraph_length, starX_long]
      exact ⟨le_of_lt hq8, by linarith⟩
    · rw [gateNetwork_trans, gateNetwork_tubeWidth_of_pos hε0, starX_trans, abs_zero]
      linarith
    · rw [gateNetwork_transEnergy, gateNetwork_transErr_of_pos hε0, starX_trans, starP_trans,
        wellPot_of_abs_le hε0 (by rw [abs_zero]; linarith)]
      norm_num
      linarith
    · rw [gateNetwork_longP, starP_long]
      nlinarith
    · rw [gateNetwork_long, gateNetwork_longP, zeroPotential_hamiltonian, starP_long,
        mul_pow, hsq, one_mul]
      exact hcK
  not_arriving := by
    intro ε hε
    have hε0 : 0 < ε := hε.1
    obtain ⟨hq8, hq8'⟩ := gateEps_bounds hε.2
    refine ThinHamiltonianNetwork.not_arriving_of_toGo_pos ?_
    rw [gateNetwork_toGo hε0, gateNetwork_long, starX_long]
    refine abs_pos.mpr (sub_ne_zero.mpr ?_)
    rcases star_sign_coord η₀ with ⟨hs, hc⟩ | ⟨hs, hc⟩
    · rw [starTarget, hs, hc]
      intro h; linarith
    · rw [starTarget, hs, hc]
      intro h; linarith
  converges := by
    have hfun : (fun _ : ℝ => gateNetwork.gState η₀.1 (starX η₀ q₀) (starP η₀ c))
        = fun _ : ℝ => (q₀, EdgeEnd.sign starGraph η₀ * c) := by
      funext _
      rw [ThinHamiltonianNetwork.gState, gateNetwork_long, gateNetwork_longP, starX_long,
        starP_long]
    rw [hfun]
    exact tendsto_const_nhds

/-! ### The graph trajectories of the two regimes -/

/-- The free graph trajectory of `Γ⋆` for an arbitrary routing law. -/
noncomputable def gateTrajectory (F : RoutingLaw starGraph) (η₀ : starGraph.EdgeEnd) (q₀ c : ℝ)
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (M : ℕ) (hM : 1 ≤ M) :
    GraphTrajectory (zeroPotential starGraph) F :=
  freeGraphTrajectory F starGraph_length_eq_one η₀ q₀ c hq₀ hc M hM

theorem gateTrajectory_energy (F : RoutingLaw starGraph) (η₀ : starGraph.EdgeEnd) (q₀ c : ℝ)
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (M : ℕ) (hM : 1 ≤ M) :
    (gateTrajectory F η₀ q₀ c hq₀ hc M hM).energy = c ^ 2 / 2 := by
  change (zeroPotential starGraph).hamiltonian _ _ (FreeTrajectory.momentum F η₀ c 0) = _
  rw [zeroPotential_hamiltonian]
  change (EdgeEnd.sign starGraph η₀ * c) ^ 2 / 2 = _
  rw [mul_pow, starGraph.edgeEnd_sign_sq η₀, one_mul]

theorem gateTrajectory_curve_zero (F : RoutingLaw starGraph) (η₀ : starGraph.EdgeEnd) (q₀ c : ℝ)
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (M : ℕ) (hM : 1 ≤ M) :
    (gateTrajectory F η₀ q₀ c hq₀ hc M hM).curve 0 0 = (q₀, EdgeEnd.sign starGraph η₀ * c) := by
  change FreeTrajectory.curve F η₀ q₀ c 0 0 = _
  rw [FreeTrajectory.curve, FreeTrajectory.startTime_zero]
  refine Prod.ext ?_ rfl
  change FreeTrajectory.startCoord F η₀ q₀ 0 + FreeTrajectory.momentum F η₀ c 0 * (0 - 0) = q₀
  change q₀ + FreeTrajectory.momentum F η₀ c 0 * (0 - 0) = q₀
  ring

/-! ### The two limit theorems -/

set_option maxHeartbeats 1000000 in
-- the final assembly instantiates the general limit theorem at a large concrete structure
/-- **The gated realization theorem, in one regime.**  For an energy window `K ⊆ [1/2, 2]` on
which the gated family realizes the routing law `F`, and an initial speed `c` with `c²/2 ∈ K`,
the projected trajectories of `H_ε = ½|p|² + gatePot2 ε` converge on `[0, T]` to the deterministic
metric-graph flow of `Γ⋆` with vertex law `F`.

This is an instance of the general `thin_junction_hamiltonian_limit`; the two hypotheses come from
`RealizesOnEnergyWindow`. -/
theorem gate_thin_junction_realization {K : Set ℝ} {F : RoutingLaw starGraph}
    (hK : IsCompact K) (hwin : (zeroPotential starGraph).IsWindowAbove K)
    (hreal : gateNetwork.RealizesOnEnergyWindow (zeroPotential starGraph) K F (1 / 100))
    (η₀ : starGraph.EdgeEnd) {q₀ c : ℝ} (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hcK : c ^ 2 / 2 ∈ K) {M : ℕ} (hM : 1 ≤ M) {T : ℝ}
    (hT : T ≤ FreeTrajectory.stopTime η₀ q₀ c M M) :
    ∃ g : GraphTrajectory (zeroPotential starGraph) F,
      g.N = M ∧ (∀ j, g.germ j = F.itinerary η₀ j) ∧
        IsThinGraphLimit (gateWellPrepared η₀ hq₀ hc1 hc2 hcK) g ∧
        ThinTrajectoryConvergesTo gateNetwork (gateWellPrepared η₀ hq₀ hc1 hc2 hcK) g T := by
  have hc0 : (0 : ℝ) < c := by linarith
  set g : GraphTrajectory (zeroPotential starGraph) F :=
    gateTrajectory F η₀ q₀ c hq₀ hc0 M hM with hgdef
  have hcurve : g.curve 0 0 = (q₀, EdgeEnd.sign starGraph η₀ * c) :=
    gateTrajectory_curve_zero F η₀ q₀ c hq₀ hc0 M hM
  have hlimit : IsThinGraphLimit (gateWellPrepared η₀ hq₀ hc1 hc2 hcK) g := ⟨rfl, rfl, hcurve⟩
  have hE : g.energy ∈ K := by
    rw [hgdef, gateTrajectory_energy]
    exact hcK
  have hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (starGraph.length (g.edge 0)) := by
    rw [hcurve, starGraph_length]
    exact hq₀
  refine ⟨g, rfl, fun j => rfl, hlimit, ?_⟩
  exact thin_junction_hamiltonian_limit gateNetwork (zeroPotential starGraph) F K hK hwin
    (gateEps_pos hq₀) (hreal.edge.mono (gateEps_le q₀)) (hreal.junction.mono (gateEps_le q₀))
    (gateWellPrepared η₀ hq₀ hc1 hc2 hcK) g hlimit hE hinit hT

/-- **The low-energy limit: the junction reflects.**  At speed `c = 1` — energy `1/2 ∈ K₋` — the
projected trajectories converge to the graph flow with total reflection at every vertex: a
particle launched into the channel `η₁` bounces back and forth on the edge `0` forever, never
entering the other channels. -/
theorem gate_realization_low (η₀ : starGraph.EdgeEnd) {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1)
    {M : ℕ} (hM : 1 ≤ M) {T : ℝ} (hT : T ≤ FreeTrajectory.stopTime η₀ q₀ 1 M M) :
    ∃ g : GraphTrajectory (zeroPotential starGraph) gateRoutingLow,
      g.N = M ∧ (∀ j, g.germ j = gateRoutingLow.itinerary η₀ j) ∧
        IsThinGraphLimit
          (gateWellPrepared η₀ hq₀ le_rfl one_le_two (show (1 : ℝ) ^ 2 / 2 ∈ windowLow by
            constructor <;> norm_num)) g ∧
        ThinTrajectoryConvergesTo gateNetwork
          (gateWellPrepared η₀ hq₀ le_rfl one_le_two (show (1 : ℝ) ^ 2 / 2 ∈ windowLow by
            constructor <;> norm_num)) g T :=
  gate_thin_junction_realization isCompact_windowLow windowLow_isWindowAbove
    gateNetwork_realizes_low η₀ hq₀ le_rfl one_le_two _ hM hT

/-- **The high-energy limit: the junction transmits.**  At speed `c = 2` — energy `2 ∈ K₊` — the
*same* microscopic family converges to the graph flow with the routing law `F⋆`: a particle
launched into the channel `η₁` crosses the branching vertex and continues along the edge `1`. -/
theorem gate_realization_high (η₀ : starGraph.EdgeEnd) {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1)
    {M : ℕ} (hM : 1 ≤ M) {T : ℝ} (hT : T ≤ FreeTrajectory.stopTime η₀ q₀ 2 M M) :
    ∃ g : GraphTrajectory (zeroPotential starGraph) gateRoutingHigh,
      g.N = M ∧ (∀ j, g.germ j = gateRoutingHigh.itinerary η₀ j) ∧
        IsThinGraphLimit
          (gateWellPrepared η₀ hq₀ one_le_two le_rfl (show (2 : ℝ) ^ 2 / 2 ∈ windowHigh by
            constructor <;> norm_num)) g ∧
        ThinTrajectoryConvergesTo gateNetwork
          (gateWellPrepared η₀ hq₀ one_le_two le_rfl (show (2 : ℝ) ^ 2 / 2 ∈ windowHigh by
            constructor <;> norm_num)) g T :=
  gate_thin_junction_realization isCompact_windowHigh windowHigh_isWindowAbove
    gateNetwork_realizes_high η₀ hq₀ one_le_two le_rfl _ hM hT

/-- **The routing actually observed differs between the two regimes.**  Arriving at the branching
vertex along `η₁`, the particle is routed back to `η₁` at low energy — it stays on the edge `0` —
and to `η₂` at high energy — it continues on the edge `1`.  The limiting itineraries of the *same*
microscopic family therefore separate at the very first junction. -/
theorem gate_itinerary_differs :
    (gateRoutingLow.itinerary channel₁ 1).1 ≠ (gateRoutingHigh.itinerary channel₁ 1).1 := by
  have h1 : gateRoutingLow.itinerary channel₁ 1 = ((0 : starGraph.Edge), true) := rfl
  have h2 : gateRoutingHigh.itinerary channel₁ 1 = ((1 : starGraph.Edge), true) := rfl
  rw [h1, h2]
  decide

end HamiltonianMetricGraphs
