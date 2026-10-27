/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ArmChain
import HamiltonianMetricGraphs.Realization.Realization

/-!
# The explicit branching microscopic realization theorem

This file completes the programme: the abstract hypotheses of `ThinNetworkFamily` are **proved**
for the explicit smooth branching Hamiltonian

  `H_ε(x, p) = ½|p|² + microPot ε x`   on `ℝ² × ℝ²`,

and the repository's global realization theorem is applied to it.

The metric graph is the star `Γ⋆` with a valence-3 vertex `v⋆` and the speed-independent
involutive routing law `F⋆` with `F⋆(η₁) = η₂`, `F⋆(η₂) = η₁`, `F⋆(η₃) = η₃`; the compact regular
energy window is `K⋆ = [1/2, 2]`.  **Both** channels are realized: the through channel `η₁ ↔ η₂`,
where the particle passes straight through the branching vertex, and the third channel `η₃ ↦ η₃`,
where the junction barrier turns it around.

## What is proved from the Hamiltonian

* **Transverse confinement** — `exists_microTrajectory`: the tube has width `O(ε)`.
* **Exactly free longitudinal motion** — `free_motion`: hence `odeErr = 0`.
* **Deterministic channel selection** — `stays_in_through_channel` and `ArmSolution.gt_six`, with
  the uniform exit-basin margin `4 - E ≥ 2` on `K⋆`.
* **Exact reflection with vanishing dwell time** — `CapSolution.reflect`,
  `ArmSolution.reflect_cap`, `ArmSolution.reflect_junction` and `capReflTime_le`: hence
  `momErr = 0` and `dwell ≤ 100 ε`.
* **The router offset is `O(ε)`** — `offset = 8ε` by construction.
* **The chain is the genuine projection** — `ThroughRun.projection`, `ArmRun.projection`,
  packaged as `IsMicroscopicProjection`.

Applying `microscopic_realization` then gives, for every `T < ∞`: agreement of the routed edge
sequence for small `ε`, convergence of the junction entrance times, vanishing junction residence
times, and uniform convergence of the longitudinal position and momentum on compact subintervals
away from the impacts.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

/-! ### The embedding of `Γ⋆` in the plane -/

/-- The longitudinal component of a plane vector along the edge `e`, in the graph orientation:
edge `1` is the positive `u`-axis, edge `0` the negative one, edge `2` the positive `w`-axis. -/
noncomputable def longComp (e : starGraph.Edge) (z : ℝ × ℝ) : ℝ :=
  if e = 2 then z.2 else ThroughRun.embedSign e * z.1

/-- The transverse component, which the tube confines to `O(ε)`. -/
noncomputable def transComp (e : starGraph.Edge) (z : ℝ × ℝ) : ℝ :=
  if e = 2 then z.1 else z.2

theorem longComp_of_ne_two {e : starGraph.Edge} (h : e ≠ 2) (z : ℝ × ℝ) :
    longComp e z = ThroughRun.embedSign e * z.1 := by
  rw [longComp, if_neg h]

theorem transComp_of_ne_two {e : starGraph.Edge} (h : e ≠ 2) (z : ℝ × ℝ) :
    transComp e z = z.2 := by
  rw [transComp, if_neg h]

@[simp] theorem longComp_two (z : ℝ × ℝ) : longComp 2 z = z.2 := by rw [longComp, if_pos rfl]

@[simp] theorem transComp_two (z : ℝ × ℝ) : transComp 2 z = z.1 := by rw [transComp, if_pos rfl]

theorem embedSign_sq (e : starGraph.Edge) :
    ThroughRun.embedSign e * ThroughRun.embedSign e = 1 := by
  rw [ThroughRun.embedSign]
  split_ifs <;> norm_num

/-! ### The microscopic certificate -/

/-- **A hybrid chain is the graph projection of a genuine microscopic trajectory.**  There is a
solution `(x, p)` of Hamilton's equations for `H_ε = ½|p|² + microPot ε` on the whole time window
whose longitudinal components along the current edge are the chain, and whose transverse
component stays in the tube `|·| < 2ε`. -/
def IsMicroscopicProjection (ε : ℝ) {P : ChainParams}
    (ch : HybridChain (zeroPotential starGraph) starRouting P) : Prop :=
  ∃ x p : ℝ → ℝ × ℝ,
    (∀ t ∈ Icc (0 : ℝ) (ch.stop ch.N),
      HasDerivWithinAt x (p t) (Icc (0 : ℝ) (ch.stop ch.N)) t) ∧
    (∀ t ∈ Icc (0 : ℝ) (ch.stop ch.N),
      HasDerivWithinAt p (microForce ε (x t)) (Icc (0 : ℝ) (ch.stop ch.N)) t) ∧
    (∀ j ≤ ch.N, ∀ t ∈ Icc (ch.start j) (ch.stop j),
      longComp (ch.edge j) (x t) = (ch.curve j t).1 ∧
      longComp (ch.edge j) (p t) = (ch.curve j t).2 ∧
      |transComp (ch.edge j) (x t)| < 2 * ε)

/-- The certificate only depends on the scale through its value. -/
theorem IsMicroscopicProjection.congr_scale {a b : ℝ} (hab : a = b) {P : ChainParams}
    {ch : HybridChain (zeroPotential starGraph) starRouting P}
    (h : IsMicroscopicProjection a ch) : IsMicroscopicProjection b ch := by
  subst hab; exact h

/-- What a microscopic run must provide in order to feed the realization theorem. -/
structure RunPackage (η₀ : starGraph.EdgeEnd) (q₀ c : ℝ) (M : ℕ) (ε : ℝ) where
  /-- the projected chain -/
  chain : HybridChain (zeroPotential starGraph) starRouting (starParams ε)
  card : chain.N = M
  edge0 : chain.edge 0 = (starRouting.itinerary η₀ 0).1
  curve0 : chain.curve 0 0 = (q₀, -c)
  window : (M : ℝ) / (2 * c) ≤ chain.stop chain.N
  proj : IsMicroscopicProjection ε chain

/-- **Existence of a microscopic run of the through channel at every admissible scale.** -/
theorem exists_throughPackage {ε c q₀ : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hε : 0 < ε) (hεs : ε ≤ 1 / 1000) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hq1 : 8 * ε < q₀) (hq2 : q₀ < 1 - 8 * ε) :
    Nonempty (RunPackage channel₁ q₀ c M ε) := by
  have hc0 : 0 < c := by linarith
  have hτ : 0 < capReflTime ε c := capReflTime_pos hε hc1
  have hstep : (0 : ℝ) < 2 / c + capReflTime ε c := by positivity
  have hT0 : (0 : ℝ) ≤ ((M : ℝ) + 1) * (2 / c + capReflTime ε c) := by positivity
  have hprep : (0 : ℝ) ^ 2 / 2 + wellPot ε 0 < 4 := by
    rw [wellPot_of_abs_le hε (by rw [abs_zero]; linarith)]
    norm_num
  obtain ⟨u, pu, w, pw, hu0, hpu0, _, _, hconf, hu, hpu, hxeq, hpeq⟩ :=
    exists_microTrajectory hε (-q₀) c 0 0 hT0 hprep
  have hcap0 : capPot ε (u 0) = 0 := by
    rw [hu0]
    refine capPot_of_abs_le_one hε ?_
    rw [abs_neg, abs_of_pos (by linarith)]
    linarith
  have hen : ∀ t ∈ Icc (0 : ℝ) (((M : ℝ) + 1) * (2 / c + capReflTime ε c)),
      pu t ^ 2 / 2 + capPot ε (u t) = c ^ 2 / 2 := by
    intro t ht
    have h := energy1D_eq (contDiff_capPot ε (n := 1)) hu hpu t ht
    simp only [energy1D] at h
    rw [h, hpu0, hcap0]
    ring
  set R : ThroughRun := ⟨ε, c, q₀, M, u, pu, hM, hε, hεs, hc1, hc2, hq1, hq2, hu0, hpu0,
    ⟨hε, hεs, hc1, hc2, hT0, hu, hpu, hen⟩⟩ with hRdef
  refine ⟨⟨ThroughRun.chain R, rfl, rfl, ?_, R.stopT_lower, ?_⟩⟩
  · exact R.crv_zero_zero
  
  have hle : (ThroughRun.chain R).stop (ThroughRun.chain R).N ≤
      ((M : ℝ) + 1) * (2 / c + capReflTime ε c) := R.stopT_le_horizon
  have hsub : Icc (0 : ℝ) ((ThroughRun.chain R).stop (ThroughRun.chain R).N) ⊆
      Icc (0 : ℝ) (((M : ℝ) + 1) * (2 / c + capReflTime ε c)) := Icc_subset_Icc le_rfl hle
  refine ⟨fun t => (u t, w t), fun t => (pu t, pw t), fun t ht => (hxeq t (hsub ht)).mono hsub,
    fun t ht => (hpeq t (hsub ht)).mono hsub, ?_⟩
  intro j hj t ht
  obtain ⟨hp1, hp2⟩ := R.projection hj ht
  have hne : (ThroughRun.chain R).edge j ≠ 2 := itinerary_channel₁_ne_two j
  have hedge : (ThroughRun.chain R).edge j = (starRouting.itinerary channel₁ j).1 := rfl
  have hcrv : (ThroughRun.chain R).curve j t = ThroughRun.crv R j t := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [longComp_of_ne_two hne, hedge, hcrv]
    show ThroughRun.embedSign (starRouting.itinerary channel₁ j).1 * R.u t = _
    rw [hp1, ← mul_assoc, embedSign_sq, one_mul]
  · rw [longComp_of_ne_two hne, hedge, hcrv]
    show ThroughRun.embedSign (starRouting.itinerary channel₁ j).1 * R.pu t = _
    rw [hp2, ← mul_assoc, embedSign_sq, one_mul]
  · rw [transComp_of_ne_two hne]
    exact hconf t (hsub ((ThroughRun.chain R).mem_Icc_zero_stop_N hj ht))

/-- **Existence of a microscopic run of the third arm at every admissible scale.** -/
theorem exists_armPackage {ε c q₀ : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hε : 0 < ε) (hεs : ε ≤ 1 / 1000) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hq1 : 8 * ε < q₀) (hq2 : q₀ < 1 - 8 * ε) :
    Nonempty (RunPackage channel₃ q₀ c M ε) := by
  have hc0 : 0 < c := by linarith
  have hτ : 0 < capReflTime ε c := capReflTime_pos hε hc1
  have hstep : (0 : ℝ) < 2 / c + capReflTime ε c := by positivity
  have hT0 : (0 : ℝ) ≤ ((M : ℝ) + 1) * (2 / c + capReflTime ε c) := by positivity
  obtain ⟨w, pw, hw0, hpw0, hS, hxeq, hpeq⟩ :=
    exists_armTrajectory hε hεs hc1 hc2 q₀ (-c) hT0 (by linarith) (by linarith) (by ring)
  set R : ArmRun := ⟨ε, c, q₀, M, w, pw, hM, hε, hεs, hc1, hc2, hq1, hq2, hw0, hpw0, hS⟩
    with hRdef
  refine ⟨⟨ArmRun.chain R, rfl, rfl, ?_, R.stopT_lower, ?_⟩⟩
  · exact R.crv_zero_zero
  
  have hle : (ArmRun.chain R).stop (ArmRun.chain R).N ≤
      ((M : ℝ) + 1) * (2 / c + capReflTime ε c) := R.stopT_le_horizon
  have hsub : Icc (0 : ℝ) ((ArmRun.chain R).stop (ArmRun.chain R).N) ⊆
      Icc (0 : ℝ) (((M : ℝ) + 1) * (2 / c + capReflTime ε c)) := Icc_subset_Icc le_rfl hle
  refine ⟨fun t => (0, w t), fun t => (0, pw t), fun t ht => (hxeq t (hsub ht)).mono hsub,
    fun t ht => (hpeq t (hsub ht)).mono hsub, ?_⟩
  intro j hj t ht
  obtain ⟨hp1, hp2⟩ := R.projection hj ht
  have hedge : (ArmRun.chain R).edge j = 2 := itinerary_channel₃_edge j
  rw [hedge]
  refine ⟨?_, ?_, ?_⟩
  · exact hp1
  · exact hp2
  · rw [transComp_two, abs_zero]
    positivity


/-! ### The clamped scale -/

/-- A scale function that is the identity on `(0, ε₀)` and lands in `(0, ε₀)` everywhere else, so
that a microscopic run exists at every index of the family. -/
noncomputable def clampEps (ε₀ ε : ℝ) : ℝ := if 0 < ε ∧ ε < ε₀ then ε else ε₀ / 2

theorem clampEps_mem {ε₀ : ℝ} (hε₀ : 0 < ε₀) (ε : ℝ) : clampEps ε₀ ε ∈ Ioo 0 ε₀ := by
  unfold clampEps
  split_ifs with h
  · exact ⟨h.1, h.2⟩
  · constructor <;> linarith

theorem clampEps_eq {ε₀ ε : ℝ} (h : 0 < ε) (h' : ε < ε₀) : clampEps ε₀ ε = ε := by
  unfold clampEps
  rw [if_pos ⟨h, h'⟩]

/-! ### Elementary facts about the star graph trajectory -/

theorem firstDuration_of_false {η₀ : starGraph.EdgeEnd} (h : η₀.2 = false) (q₀ c : ℝ) :
    FreeTrajectory.firstDuration η₀ q₀ c = q₀ / c := by
  unfold FreeTrajectory.firstDuration FreeTrajectory.initialDistance
  rw [h]
  norm_num

theorem starTrajectory_stop_eq {η₀ : starGraph.EdgeEnd} (h : η₀.2 = false) (q₀ c : ℝ)
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (N : ℕ) (hN : 1 ≤ N) :
    (starTrajectory η₀ q₀ c hq₀ hc N hN).stop (starTrajectory η₀ q₀ c hq₀ hc N hN).N =
      q₀ / c + ((N : ℝ) - 1) * (1 / c) + 1 / c / 2 := by
  change FreeTrajectory.stopTime η₀ q₀ c N N = _
  rw [FreeTrajectory.stopTime_self, firstDuration_of_false h]
  rfl

theorem starTrajectory_curve_zero_eq {η₀ : starGraph.EdgeEnd} (h : η₀.2 = false) (q₀ c : ℝ)
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (N : ℕ) (hN : 1 ≤ N) :
    (starTrajectory η₀ q₀ c hq₀ hc N hN).curve 0 0 = (q₀, -c) := by
  change FreeTrajectory.curve starRouting η₀ q₀ c 0 0 = _
  rw [FreeTrajectory.curve]
  have h1 : FreeTrajectory.startCoord starRouting η₀ q₀ 0 = q₀ := rfl
  have h2 : FreeTrajectory.momentum starRouting η₀ c 0 = -c := by
    change EdgeEnd.sign starGraph (starRouting.itinerary η₀ 0) * c = -c
    rw [RoutingLaw.itinerary_zero, sign_of_false h]
    ring
  rw [h1, h2, FreeTrajectory.startTime_zero]
  norm_num


/-! ### The statement -/

/-- The two channels of the model at the branching vertex. -/
inductive Channel where
  /-- the through channel, routed `η₁ ↔ η₂` -/
  | through : Channel
  /-- the third arm, routed `η₃ ↦ η₃` -/
  | arm : Channel

/-- **A well-prepared microscopic initial state**: the particle sits on the axis of the tube of
the edge of its channel, at graph coordinate `q₀` strictly inside the edge, moving towards the
branching vertex `v⋆` with speed `c`, so that its energy `c²/2` lies in `K⋆`. -/
structure MicroInitialState where
  /-- which channel the particle starts in -/
  channel : Channel
  /-- the initial graph coordinate -/
  q₀ : ℝ
  /-- the speed -/
  c : ℝ
  inside : q₀ ∈ Ioo (0 : ℝ) 1
  speed : c ∈ Icc (1 : ℝ) 2

/-- The edge-end towards which the particle moves. -/
def MicroInitialState.germ (x₀ : MicroInitialState) : starGraph.EdgeEnd :=
  match x₀.channel with
  | Channel.through => channel₁
  | Channel.arm => channel₃

theorem MicroInitialState.germ_snd (x₀ : MicroInitialState) : x₀.germ.2 = false := by
  obtain ⟨ch, _, _, _, _⟩ := x₀
  cases ch <;> rfl

/-- The (conserved) energy of a well-prepared microscopic state. -/
noncomputable def MicroInitialState.energy (x₀ : MicroInitialState) : ℝ := x₀.c ^ 2 / 2

theorem MicroInitialState.energy_mem (x₀ : MicroInitialState) : x₀.energy ∈ windowStar := by
  obtain ⟨h1, h2⟩ := x₀.speed
  rw [MicroInitialState.energy]
  exact ⟨by nlinarith, by nlinarith⟩

theorem MicroInitialState.c_pos (x₀ : MicroInitialState) : 0 < x₀.c := by
  linarith [x₀.speed.1]

/-- **`g` is the deterministic graph-scattering trajectory of `x₀`**: it starts on the edge of the
channel of `x₀` at the same coordinate with the same momentum, is routed by `F⋆`, and has energy
in the compact regular window `K⋆`. -/
def IsGraphLimitTrajectory (x₀ : MicroInitialState)
    (g : GraphTrajectory (zeroPotential starGraph) starRouting) : Prop :=
  g.germ 0 = x₀.germ ∧ g.curve 0 0 = (x₀.q₀, -x₀.c) ∧ g.energy = x₀.energy ∧
    g.energy ∈ windowStar

/-- The conclusion of the restricted microscopic-realization theorem, named for readability:
matching of the routed edge sequence, convergence of the junction entrance times together with
agreement of the entry germs, and uniform convergence of the longitudinal state away from the
impacts. -/
def RealizesGraphTrajectory
    (fam : ThinNetworkFamily (zeroPotential starGraph) starRouting)
    (g : GraphTrajectory (zeroPotential starGraph) starRouting) : Prop :=
  (∀ j ≤ g.N, fam.Matches g j) ∧
  (∀ j < g.N, Tendsto (fun ε => (fam.chain ε).stop j) (𝓝[>] 0) (𝓝 (g.stop j)) ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), j < (fam.chain ε).N ∧ (fam.chain ε).germ j = g.germ j) ∧
  (∀ j < g.N, ∀ δ > (0 : ℝ), ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    ∀ t ∈ Icc (g.start j + δ) (g.stop j - δ),
      dist ((fam.chain ε).curve j t) (g.curve j t) < η) ∧
  ((∀ᶠ ε in 𝓝[>] (0 : ℝ), g.N < (fam.chain ε).N →
      g.stop g.N < (fam.chain ε).stop g.N) ∧
    ∀ δ > (0 : ℝ), ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Icc (g.start g.N + δ) (g.stop g.N),
        dist ((fam.chain ε).curve g.N t) (g.curve g.N t) < η)

/-- **The microscopic trajectories of `x₀` converge to the graph trajectory `g` on `[0, T]`.**
There is a thin-network family whose chains are, for small `ε`, the graph projections of genuine
trajectories of the microscopic Hamiltonian `H_ε`, whose parameters (router offset, junction
residence time, ODE tolerance, momentum tolerance) vanish, whose initial data converge to those of
`g`, whose time window covers `[0, T]`, and whose projections converge to `g`. -/
def MicroscopicTrajectoryConvergesTo (_x₀ : MicroInitialState)
    (g : GraphTrajectory (zeroPotential starGraph) starRouting) (T : ℝ) : Prop :=
  ∃ fam : ThinNetworkFamily (zeroPotential starGraph) starRouting,
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsMicroscopicProjection ε (fam.chain ε)) ∧
    fam.ConvergesInitially g ∧ T ≤ g.stop g.N ∧ RealizesGraphTrajectory fam g

/-! ### The core argument, common to both channels -/

set_option maxHeartbeats 1000000 in
/-- **The core of the explicit realization theorem**, for an arbitrary channel at the branching
vertex, given microscopic runs at all small scales. -/
theorem realization_core {η₀ : starGraph.EdgeEnd} (hη : η₀.2 = false) {q₀ c : ℝ}
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) {T : ℝ} (hT : 0 ≤ T)
    (hpkg : ∀ (M : ℕ) (e : ℝ), 1 ≤ M → 0 < e → e ≤ 1 / 1000 → 8 * e < q₀ → q₀ < 1 - 8 * e →
      Nonempty (RunPackage η₀ q₀ c M e)) :
    ∃ g : GraphTrajectory (zeroPotential starGraph) starRouting,
      (g.germ 0 = η₀ ∧ g.curve 0 0 = (q₀, -c) ∧ g.energy = c ^ 2 / 2 ∧
        g.energy ∈ windowStar) ∧
      ∃ fam : ThinNetworkFamily (zeroPotential starGraph) starRouting,
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsMicroscopicProjection ε (fam.chain ε)) ∧
        fam.ConvergesInitially g ∧ T ≤ g.stop g.N ∧ RealizesGraphTrajectory fam g := by
  obtain ⟨hq1, hq2⟩ := hq₀
  have hc0 : (0 : ℝ) < c := by linarith
  set Ng : ℕ := ⌈2 * T⌉₊ + 1 with hNgdef
  have hNg : 1 ≤ Ng := by omega
  set g := starTrajectory η₀ q₀ c ⟨hq1, hq2⟩ hc0 Ng hNg with hgdef
  set M : ℕ := 2 * Ng + 1 with hMdef
  have hM : 1 ≤ M := by omega
  set ε₀ : ℝ := min (1 / 1000) (min (q₀ / 16) ((1 - q₀) / 16)) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hε₀1 : ε₀ ≤ 1 / 1000 := min_le_left _ _
  have hε₀2 : ε₀ ≤ q₀ / 16 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₀3 : ε₀ ≤ (1 - q₀) / 16 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hex : ∀ e : ℝ, Nonempty (RunPackage η₀ q₀ c M (clampEps ε₀ e)) := by
    intro e
    obtain ⟨hlo, hhi⟩ := clampEps_mem hε₀ e
    exact hpkg M (clampEps ε₀ e) hM hlo (le_trans hhi.le hε₀1) (by linarith) (by linarith)
  set pk : ∀ e : ℝ, RunPackage η₀ q₀ c M (clampEps ε₀ e) := fun e => (hex e).some with hpkdef
  have heps : ∀ᶠ e in 𝓝[>] (0 : ℝ), clampEps ε₀ e = e :=
    eventually_nhdsGT_zero_of_forall_Ioo hε₀ (fun e he => clampEps_eq he.1 he.2)
  have habs8 : Tendsto (fun e : ℝ => 8 * |e|) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_abs_nhdsGT_zero.const_mul (8 : ℝ)
  have habs100 : Tendsto (fun e : ℝ => 100 * |e|) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_abs_nhdsGT_zero.const_mul (100 : ℝ)
  set fam : ThinNetworkFamily (zeroPotential starGraph) starRouting :=
    { params := fun e => starParams (clampEps ε₀ e)
      chain := fun e => (pk e).chain
      offset_tendsto := by
        refine Tendsto.congr' ?_ habs8
        filter_upwards [heps] with e he
        rw [starParams_offset, he]
      dwell_tendsto := by
        refine Tendsto.congr' ?_ habs100
        filter_upwards [heps] with e he
        rw [starParams_dwell, he]
      odeErr_tendsto := by
        simp only [starParams_odeErr]
        exact tendsto_const_nhds
      momErr_tendsto := by
        simp only [starParams_momErr]
        exact tendsto_const_nhds } with hfamdef
  have hgcurve : g.curve 0 0 = (q₀, -c) :=
    starTrajectory_curve_zero_eq hη q₀ c ⟨hq1, hq2⟩ hc0 Ng hNg
  have hgstop : g.stop g.N = q₀ / c + ((Ng : ℝ) - 1) * (1 / c) + 1 / c / 2 :=
    starTrajectory_stop_eq hη q₀ c ⟨hq1, hq2⟩ hc0 Ng hNg
  have hTg : T ≤ g.stop g.N := by
    rw [hgstop]
    have hceil : (2 : ℝ) * T ≤ (⌈2 * T⌉₊ : ℝ) := Nat.le_ceil _
    have hNgcast : ((Ng : ℝ) - 1) = (⌈2 * T⌉₊ : ℝ) := by rw [hNgdef]; push_cast; ring
    have hinv : (1 : ℝ) / 2 ≤ 1 / c := by
      rw [div_le_div_iff₀ (by norm_num) hc0]
      linarith
    have h1 : (0 : ℝ) ≤ q₀ / c := by positivity
    have h2 : (0 : ℝ) ≤ 1 / c / 2 := by positivity
    have h3 : (2 : ℝ) * T * (1 / 2) ≤ ((Ng : ℝ) - 1) * (1 / c) := by
      rw [hNgcast]
      have hnn : (0 : ℝ) ≤ (⌈2 * T⌉₊ : ℝ) := Nat.cast_nonneg _
      nlinarith
    linarith
  have hconv : fam.ConvergesInitially g := by
    refine ⟨Filter.Eventually.of_forall (fun e => (pk e).edge0), ?_, ?_⟩
    · have hfun : (fun e : ℝ => (fam.chain e).curve 0 0) = fun _ => ((q₀, -c) : ℝ × ℝ) := by
        funext e; exact (pk e).curve0
      rw [hfun, hgcurve]
      exact tendsto_const_nhds
    · refine Filter.Eventually.of_forall (fun e => ?_)
      have hlow : (M : ℝ) / (2 * c) ≤ (fam.chain e).stop (fam.chain e).N := (pk e).window
      have hMcast : ((M : ℝ)) = 2 * (Ng : ℝ) + 1 := by rw [hMdef]; push_cast; ring
      rw [hMcast] at hlow
      rw [hgstop]
      have hkey : q₀ / c + ((Ng : ℝ) - 1) * (1 / c) + 1 / c / 2 ≤
          (2 * (Ng : ℝ) + 1) / (2 * c) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * c)]
        have hexp : (q₀ / c + ((Ng : ℝ) - 1) * (1 / c) + 1 / c / 2) * (2 * c) =
            2 * q₀ + 2 * ((Ng : ℝ) - 1) + 1 := by field_simp
        rw [hexp]
        linarith
      linarith
  have hcert : ∀ᶠ e in 𝓝[>] (0 : ℝ), IsMicroscopicProjection e (fam.chain e) := by
    refine eventually_nhdsGT_zero_of_forall_Ioo hε₀ (fun e he => ?_)
    exact ((pk e).proj).congr_scale (clampEps_eq he.1 he.2)
  have hen : g.energy = c ^ 2 / 2 := starTrajectory_energy η₀ q₀ c ⟨hq1, hq2⟩ hc0 Ng hNg
  have hEmem : g.energy ∈ windowStar := by
    rw [hen]
    exact ⟨by nlinarith, by nlinarith⟩
  have hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (starGraph.length (g.edge 0)) := by
    rw [hgcurve, starGraph_length_eq_one]
    exact ⟨hq1, hq2⟩
  refine ⟨g, ⟨rfl, hgcurve, hen, hEmem⟩, fam, hcert, hconv, hTg, ?_⟩
  exact microscopic_realization windowStar isCompact_windowStar windowStar_regular g hEmem hinit
    fam hconv

/-! ### The theorem -/

/-- **The explicit branching microscopic realization theorem.**

For every well-prepared microscopic initial state `x₀` — in the through channel or in the third
arm — with energy in the compact regular window `K⋆ = [1/2, 2]`, and every finite horizon `T`,
there is a deterministic graph-scattering trajectory `g` of the valence-3 star `Γ⋆` with the
speed-independent involutive routing law `F⋆` such that

* `g` is the graph trajectory of `x₀` (`IsGraphLimitTrajectory`), and
* the genuine trajectories of the smooth microscopic Hamiltonian `H_ε = ½|p|² + microPot ε`,
  projected to `Γ⋆`, converge to `g` on `[0, T]` as `ε → 0⁺`
  (`MicroscopicTrajectoryConvergesTo`).

Every hypothesis of `ThinNetworkFamily` is discharged from the Hamiltonian: the thin-tube
confinement, the exactly free longitudinal motion (`odeErr = 0`), the deterministic routing at the
branching vertex (`η₁ ↔ η₂` by passing straight through, `η₃ ↦ η₃` by reflection at the junction
barrier), the exact momentum reversal at the barriers (`momErr = 0`), the `O(ε)` router offset and
the `O(ε)` junction residence time. -/
theorem explicit_branching_hamiltonian_realization
    (x₀ : MicroInitialState) {T : ℝ} (hT : 0 ≤ T) :
    ∃ g : GraphTrajectory (zeroPotential starGraph) starRouting,
      IsGraphLimitTrajectory x₀ g ∧ MicroscopicTrajectoryConvergesTo x₀ g T := by
  obtain ⟨ch, q₀, c, hin, hsp⟩ := x₀
  have hc1 : (1 : ℝ) ≤ c := hsp.1
  have hc2 : c ≤ 2 := hsp.2
  have hpkg : ∀ (M : ℕ) (e : ℝ), 1 ≤ M → 0 < e → e ≤ 1 / 1000 → 8 * e < q₀ →
      q₀ < 1 - 8 * e →
      Nonempty (RunPackage (MicroInitialState.germ ⟨ch, q₀, c, hin, hsp⟩) q₀ c M e) := by
    intro M e hM he hes h1 h2
    cases ch with
    | through => exact exists_throughPackage hM he hes hc1 hc2 h1 h2
    | arm => exact exists_armPackage hM he hes hc1 hc2 h1 h2
  obtain ⟨g, hg, fam, hcert, hconv, hTg, hreal⟩ :=
    realization_core (MicroInitialState.germ_snd ⟨ch, q₀, c, hin, hsp⟩) hin hc1 hc2 hT hpkg
  exact ⟨g, hg, fam, hcert, hconv, hTg, hreal⟩

end HamiltonianMetricGraphs
