/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalRun
import HamiltonianMetricGraphs.Realization.Realization
import HamiltonianMetricGraphs.Realization.BranchingRealization

/-!
# The universal reversible microscopic realization theorem

For an **arbitrary** finite metric graph `Γ` and an **arbitrary** speed-independent involutive
routing law `F`, this file assembles the explicit smooth microscopic network of the previous
files into a `ThinNetworkFamily` and proves that the projected trajectories of the microscopic
Hamiltonian converge to the deterministic graph-scattering trajectory.

The network is built functorially from `(Γ, F)`: one straight corridor per edge-end germ, laid
out at the integer heights `w = 0, 1, …`, with

* the **transverse well** confining the particle to the tube of its corridor;
* the **barrier** `tubeWall` of height `4 > sup K⋆` separating distinct routing components — a
  particle of the window can never enter a competing component;
* a **cap** at each end of a corridor, which is the router of an `F`-fixed germ: the particle is
  reflected there with exact momentum reversal in time `O(ε)`;
* the routing of a transposition `F_v(η) = ζ ≠ η` realized by the collinear layout of the two
  edges inside one corridor, so that the particle passes straight through the router.

Every hypothesis of `ThinNetworkFamily` is discharged from the Hamiltonian.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {Γ : FiniteMetricGraph}

/-! ### The network of a graph with a routing law -/

open Classical in
/-- The corridor of the routing component of the germ `ζ`. -/
noncomputable def theCorridor (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (M : ℕ) : Corridor F ζ M :=
  (exists_corridor F ζ M).choose

theorem theCorridor_margin (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (M : ℕ) :
    (theCorridor F ζ M).margin = minLen Γ ζ.1 := (exists_corridor F ζ M).choose_spec

/-- An enumeration of the edge-end germs of `Γ`; the corridor of the germ `ζ` sits at the
height `w = netIndex ζ`. -/
noncomputable def netIndex (Γ : FiniteMetricGraph) :
    Γ.EdgeEnd ≃ Fin (Fintype.card Γ.EdgeEnd) := Fintype.equivFin Γ.EdgeEnd

/-- **The lengths of the corridors of the universal network**: one corridor per edge-end germ,
carrying the whole routing component of that germ. -/
noncomputable def netLengths (F : RoutingLaw Γ) (M : ℕ) :
    Fin (Fintype.card Γ.EdgeEnd) → ℝ :=
  fun k => clen (theCorridor F ((netIndex Γ).symm k) M)

theorem netLengths_apply (F : RoutingLaw Γ) (M : ℕ) (ζ : Γ.EdgeEnd) :
    netLengths F M (netIndex Γ ζ) = clen (theCorridor F ζ M) := by
  rw [netLengths, Equiv.symm_apply_apply]

/-! ### The projection certificate -/

/-- **A hybrid chain is the graph projection of a genuine trajectory of the smooth microscopic
network.**  There is a solution `(x, p)` of Hamilton's equations for
`H_ε = ½ |p|² + netPot ε m Λ` on the whole time window, the transverse coordinate stays in the
tube of the corridor `i`, and along every flight the chain is the image of `(x, p)` under the
affine isometry which identifies the corridor cell of that flight with its edge. -/
def IsNetworkProjection {F : RoutingLaw Γ} {P : ChainParams} (ε : ℝ)
    (ch : HybridChain (zeroPotential Γ) F P) : Prop :=
  ∃ (m : ℕ) (Λ : Fin m → ℝ) (i : Fin m) (x p : ℝ → ℝ × ℝ) (σ base cell : ℕ → ℝ),
    (∀ t ∈ Icc (0 : ℝ) (ch.stop ch.N),
      HasDerivWithinAt x (p t) (Icc (0 : ℝ) (ch.stop ch.N)) t) ∧
    (∀ t ∈ Icc (0 : ℝ) (ch.stop ch.N),
      HasDerivWithinAt p (netForce ε m Λ (x t)) (Icc (0 : ℝ) (ch.stop ch.N)) t) ∧
    (∀ t ∈ Icc (0 : ℝ) (ch.stop ch.N), |(x t).2 - ((i : ℕ) : ℝ)| < 2 * ε) ∧
    (∀ j, σ j = 1 ∨ σ j = -1) ∧
    (∀ j ≤ ch.N, ∀ t ∈ Icc (ch.start j) (ch.stop j),
      (ch.curve j t).1 = base j + σ j * ((x t).1 - cell j) ∧
      (ch.curve j t).2 = σ j * (p t).1)

theorem IsNetworkProjection.congr_scale {F : RoutingLaw Γ} {a b : ℝ} (hab : a = b)
    {P : ChainParams} {ch : HybridChain (zeroPotential Γ) F P}
    (h : IsNetworkProjection a ch) : IsNetworkProjection b ch := by
  subst hab; exact h

/-! ### The microscopic package -/

/-- What a microscopic run must provide in order to feed the realization theorem. -/
structure NetPackage (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (q₀ c : ℝ) (M : ℕ) (ε : ℝ) where
  /-- the projected chain -/
  chain : HybridChain (zeroPotential Γ) F (netParams ε)
  card : chain.N = M
  edge0 : chain.edge 0 = (F.itinerary η₀ 0).1
  curve0 : chain.curve 0 0 = (q₀, EdgeEnd.sign Γ η₀ * c)
  window : GenTrajectory.startTime F η₀ q₀ c M - (M : ℝ) * (16 * ε) ≤ chain.stop chain.N
  proj : IsNetworkProjection ε chain

/-- **Existence of a microscopic run at every admissible scale.**  For every finite horizon `M`
and every small enough `ε` the smooth microscopic network of `(Γ, F)` carries a genuine
trajectory whose graph projection is a hybrid chain with parameters `O(ε)` realizing the first
`M` impacts of the itinerary of `η₀`. -/
theorem exists_netPackage (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) {q₀ c ε : ℝ} (M : ℕ)
    (hε : 0 < ε) (hεs : ε ≤ 1 / 1000) (hεm : 1000 * ε ≤ minLen Γ η₀.1)
    (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hq1 : 8 * ε < q₀) (hq2 : q₀ < Γ.length η₀.1 - 8 * ε) :
    Nonempty (NetPackage F η₀ q₀ c M ε) := by
  classical
  have hc0 : 0 < c := by linarith
  set C := theCorridor F η₀ M with hCdef
  have hmar : C.margin = minLen Γ η₀.1 := theCorridor_margin F η₀ M
  have hCm : 1000 * ε ≤ C.margin := by rw [hmar]; exact hεm
  set Λ := netLengths F M with hΛdef
  set idx := netIndex Γ η₀ with hidxdef
  have hlen : Λ idx = clen C := netLengths_apply F M η₀
  have hclen : 0 < clen C := clen_pos C
  have hmc : C.margin ≤ clen C := margin_le_clen C
  have hΛ : 1000 * ε ≤ Λ idx := by rw [hlen]; linarith
  set Tmax : ℝ := ((M : ℝ) + 1) * (clen C / c + 100 * ε) with hTmaxdef
  have hT0 : 0 ≤ Tmax := by rw [hTmaxdef]; positivity
  set u₀ := spos C q₀ ε 0 with hu₀def
  have hu₀mem : u₀ ∈ Icc (8 * ε) (clen C - 8 * ε) :=
    spos_mem hε hCm hq1 hq2 (Nat.zero_le M)
  have hprep : (0 : ℝ) ^ 2 / 2 + wellShift ε (idx : ℕ) (((idx : ℕ) : ℝ)) < 4 := by
    rw [wellShift_of_abs_le hε (by simp [hε.le])]
    norm_num
  obtain ⟨u, pu, w, pw, hu0, hpu0, hw0, hpw0, hconf, hu, hpu, hxy, hpxy⟩ :=
    exists_netTrajectory hε (by linarith) Λ idx u₀ c (((idx : ℕ) : ℝ)) 0 hT0 hprep
  have hsol : CorridorSolution ε (clen C) c Tmax u pu := by
    have hinit : pu 0 ^ 2 / 2 + corridorPot ε (Λ idx) (u 0) = c ^ 2 / 2 := by
      rw [hu0, hpu0, hlen,
        corridorPot_of_mem hε (by linarith [hu₀mem.1]) (by linarith [hu₀mem.2])]
      ring
    have h := corridorSolution_of_net (i := idx) hε hΛ hc1 hc2 hT0 hu hpu hinit
    rw [hlen] at h
    exact h
  set R : NetRun Γ :=
    { F := F, η₀ := η₀, q₀ := q₀, c := c, ε := ε, M := M, C := C, u := u, pu := pu
      eps_pos := hε
      eps_margin := hCm
      c_ge := hc1
      c_le := hc2
      q_lb := hq1
      q_ub := hq2
      init_pos := hu0
      init_mom := hpu0
      sol := hsol } with hRdef
  have hstopT : R.chain.stop R.chain.N = R.stopT R.M := rfl
  have hstople : R.stopT R.M ≤ Tmax := by
    have h1 := NetRun.stopT_le_arriveT (R := R) le_rfl
    have h2 := ((R.inv R.M le_rfl).arriveT_mem le_rfl).2
    have h3 : R.horizon = Tmax := rfl
    rw [h3] at h2
    linarith
  have hsub : Icc (0 : ℝ) (R.chain.stop R.chain.N) ⊆ Icc (0 : ℝ) Tmax := by
    rw [hstopT]
    exact Icc_subset_Icc le_rfl hstople
  refine ⟨{ chain := R.chain, card := rfl, edge0 := rfl
            curve0 := R.chain_curve_zero_zero
            window := ?_
            proj := ?_ }⟩
  · have h1 := R.startT_ge R.M le_rfl
    have h2 : R.startT R.M ≤ R.stopT R.M := (NetRun.startT_lt_stopT (R := R) le_rfl).le
    rw [hstopT]
    exact le_trans h1 h2
  · refine ⟨Fintype.card Γ.EdgeEnd, Λ, idx, fun t => (u t, w t), fun t => (pu t, pw t),
      R.orient, gstart F η₀ q₀ ε, R.startPos, ?_, ?_, ?_, R.orient_eq_one_or, ?_⟩
    · intro t ht
      exact (hxy t (hsub ht)).mono hsub
    · intro t ht
      exact (hpxy t (hsub ht)).mono hsub
    · intro t ht
      exact hconf t (hsub ht)
    · intro j hj t ht
      have hj' : j ≤ R.M := hj
      exact R.chain_proj hj' ht

/-! ### The graph trajectory covers any finite horizon -/

/-- Every flight after the first traverses a whole edge, so the graph trajectory reaches any
finite horizon after enough impacts. -/
theorem startTime_ge (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) {q₀ c : ℝ}
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) (Γ.length η₀.1)) (hc0 : 0 < c) (hc2 : c ≤ 2) (j : ℕ) :
    ((j : ℝ) - 1) * (minLen Γ η₀.1 / 2) ≤ GenTrajectory.startTime F η₀ q₀ c j := by
  have hml := minLen_pos Γ η₀.1
  induction j with
  | zero =>
      rw [GenTrajectory.startTime_zero]
      push_cast
      linarith
  | succ i ih =>
      rw [GenTrajectory.startTime_succ]
      have htp : 0 < GenTrajectory.travel F η₀ q₀ i := GenTrajectory.travel_pos hq₀ i
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        rw [GenTrajectory.startTime_zero]
        push_cast
        have : 0 < GenTrajectory.travel F η₀ q₀ 0 / c := div_pos htp hc0
        linarith
      · obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
        have hml' : minLen Γ η₀.1 ≤ edgeLen F η₀ (l + 1) := minLen_le_edgeLen η₀.1 (l + 1)
        have hteq : GenTrajectory.travel F η₀ q₀ (l + 1) = edgeLen F η₀ (l + 1) := rfl
        have hstep : minLen Γ η₀.1 / 2 ≤ GenTrajectory.travel F η₀ q₀ (l + 1) / c := by
          rw [hteq, le_div_iff₀ hc0]
          nlinarith
        push_cast
        push_cast at ih
        linarith

/-! ### The statement -/

/-- **A well-prepared microscopic initial state** for `(Γ, F)`: the particle sits on the axis of
the tube of the edge of `germ`, at the graph coordinate `q₀` strictly inside that edge, moving
towards `germ` with speed `c`, so that its energy `c²/2` lies in the compact regular window
`K⋆ = [1/2, 2]`. -/
structure WellPreparedState (Γ : FiniteMetricGraph) where
  /-- the edge-end germ towards which the particle moves -/
  germ : Γ.EdgeEnd
  /-- the initial graph coordinate -/
  q₀ : ℝ
  /-- the speed -/
  c : ℝ
  inside : q₀ ∈ Ioo (0 : ℝ) (Γ.length germ.1)
  speed : c ∈ Icc (1 : ℝ) 2

/-- The compact regular energy window of the model. -/
def window : Set ℝ := Icc (1 / 2 : ℝ) 2

theorem isCompact_window : IsCompact window := isCompact_Icc

theorem window_regular (Γ : FiniteMetricGraph) :
    ∀ E ∈ window, E ∉ (zeroPotential Γ).exceptionalEnergies := by
  intro E hE
  exact zeroPotential_not_mem_exceptionalEnergies (by linarith [hE.1])

/-- The conclusion of the realization theorem: matching of the routed edge sequence, convergence
of the junction entrance times together with agreement of the entry germs, and uniform
convergence of the longitudinal state away from the impacts. -/
def RealizesGraphTrajectory' {F : RoutingLaw Γ}
    (fam : ThinNetworkFamily (zeroPotential Γ) F)
    (g : GraphTrajectory (zeroPotential Γ) F) : Prop :=
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

/-- **The microscopic trajectories converge to the graph trajectory `g` on `[0, T]`.**  There is
a thin-network family whose chains are, for small `ε`, the graph projections of genuine
trajectories of the smooth microscopic Hamiltonian `H_ε = ½|p|² + netPot ε`, whose parameters
(router offset, junction residence time, ODE tolerance, momentum tolerance) vanish, whose initial
data converge to those of `g`, whose time window covers `[0, T]`, and whose projections converge
to `g`. -/
def UniversalMicroscopicConvergence {F : RoutingLaw Γ}
    (g : GraphTrajectory (zeroPotential Γ) F) (T : ℝ) : Prop :=
  ∃ fam : ThinNetworkFamily (zeroPotential Γ) F,
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsNetworkProjection ε (fam.chain ε)) ∧
    fam.ConvergesInitially g ∧ T ≤ g.stop g.N ∧ RealizesGraphTrajectory' fam g

/-! ### Elementary facts about the graph trajectory -/

theorem genTrajectory_curve_zero_zero (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (q₀ c : ℝ)
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) (Γ.length η₀.1)) (hc : 0 < c) (N : ℕ) :
    (genTrajectory F η₀ q₀ c hq₀ hc N).curve 0 0 = (q₀, EdgeEnd.sign Γ η₀ * c) := by
  refine Prod.ext ?_ rfl
  show (GenTrajectory.curve F η₀ q₀ c 0 0).1 = q₀
  rw [GenTrajectory.curve_fst, GenTrajectory.startCoord_zero, GenTrajectory.startTime_zero]
  ring

theorem genTrajectory_stop (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (q₀ c : ℝ)
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) (Γ.length η₀.1)) (hc : 0 < c) (N : ℕ) :
    (genTrajectory F η₀ q₀ c hq₀ hc N).stop (genTrajectory F η₀ q₀ c hq₀ hc N).N =
      GenTrajectory.startTime F η₀ q₀ c N + GenTrajectory.travel F η₀ q₀ N / (2 * c) :=
  GenTrajectory.stopTime_self

theorem genTrajectory_energy (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (q₀ c : ℝ)
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) (Γ.length η₀.1)) (hc : 0 < c) (N : ℕ) :
    (genTrajectory F η₀ q₀ c hq₀ hc N).energy = c ^ 2 / 2 := by
  rw [HybridChain.energy, genTrajectory_curve_zero_zero, zeroPotential_hamiltonian]
  have h := Γ.edgeEnd_sign_sq η₀
  nlinarith [h]

/-! ### The theorem -/

set_option maxHeartbeats 1000000 in
/-- **The universal reversible microscopic realization theorem.**

For *every* finite metric graph `Γ`, *every* speed-independent involutive routing law `F` on it,
the zero graph potential, the compact regular energy window `K⋆ = [1/2, 2]`, *every* well-prepared
initial state `x₀` and *every* finite horizon `T`, there is a deterministic graph-scattering
trajectory `g` of `(Γ, F)` such that

* `g` is the graph trajectory of `x₀`, with energy in `K⋆`, and
* the genuine trajectories of the explicit smooth microscopic Hamiltonian
  `H_ε = ½|p|² + netPot ε`, projected to `Γ`, converge to `g` on `[0, T]` as `ε → 0⁺`.

The microscopic network is constructed functorially from `(Γ, F)`: one straight corridor per
edge-end germ, the transverse well of each tube confining the particle to it, a smooth barrier of
height `4 > sup K⋆` separating distinct routing components, a cap at each end of a corridor acting
as the router of an `F`-fixed germ (exact momentum reversal in time `O(ε)`), and the collinear
layout inside a corridor realizing every transposition of `F`.

Every hypothesis of `ThinNetworkFamily` is discharged from the Hamiltonian: the thin-tube
confinement, the exactly free longitudinal motion (`odeErr = 0`), the deterministic routing at
every vertex, the exact momentum reversal at the caps (`momErr = 0`), the `O(ε)` router offset
and the `O(ε)` junction residence time. -/
theorem universal_reversible_realization (Γ : FiniteMetricGraph) (F : RoutingLaw Γ)
    (x₀ : WellPreparedState Γ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ g : GraphTrajectory (zeroPotential Γ) F,
      (g.germ 0 = x₀.germ ∧ g.curve 0 0 = (x₀.q₀, EdgeEnd.sign Γ x₀.germ * x₀.c) ∧
        g.energy = x₀.c ^ 2 / 2 ∧ g.energy ∈ window) ∧
      UniversalMicroscopicConvergence g T := by
  obtain ⟨η₀, q₀, c, hq₀, hsp⟩ := x₀
  have hc1 : (1 : ℝ) ≤ c := hsp.1
  have hc2 : c ≤ 2 := hsp.2
  have hc0 : (0 : ℝ) < c := by linarith
  haveI : Nonempty Γ.Edge := ⟨η₀.1⟩
  have hml : 0 < minLen Γ η₀.1 := minLen_pos Γ η₀.1
  set Ng : ℕ := ⌈2 * T / minLen Γ η₀.1⌉₊ + 2 with hNgdef
  have hNg : 1 ≤ Ng := by omega
  set g := genTrajectory F η₀ q₀ c hq₀ hc0 Ng with hgdef
  set M : ℕ := Ng + 1 with hMdef
  -- the horizon is covered
  have hgstop : g.stop g.N =
      GenTrajectory.startTime F η₀ q₀ c Ng + GenTrajectory.travel F η₀ q₀ Ng / (2 * c) :=
    genTrajectory_stop F η₀ q₀ c hq₀ hc0 Ng
  have hTg : T ≤ g.stop g.N := by
    have h1 := startTime_ge F η₀ hq₀ hc0 hc2 Ng
    have h2 : (0 : ℝ) ≤ GenTrajectory.travel F η₀ q₀ Ng / (2 * c) :=
      le_of_lt (div_pos (GenTrajectory.travel_pos hq₀ Ng) (by linarith))
    have hceil : 2 * T / minLen Γ η₀.1 ≤ (⌈2 * T / minLen Γ η₀.1⌉₊ : ℝ) := Nat.le_ceil _
    have hNgcast : ((Ng : ℝ) - 1) = (⌈2 * T / minLen Γ η₀.1⌉₊ : ℝ) + 1 := by
      rw [hNgdef]; push_cast; ring
    rw [hgstop]
    have hkey : T ≤ ((Ng : ℝ) - 1) * (minLen Γ η₀.1 / 2) := by
      rw [hNgcast]
      have hd : 2 * T / minLen Γ η₀.1 * minLen Γ η₀.1 = 2 * T := by field_simp
      nlinarith [hceil, hml]
    linarith
  -- the scale threshold
  set ε₀ : ℝ := min (1 / 1000) (min (minLen Γ η₀.1 / (1000 * ((Ng : ℝ) + 1)))
    (min (q₀ / 16) ((Γ.length η₀.1 - q₀) / 16))) with hε₀def
  have hNgpos : (0 : ℝ) ≤ (Ng : ℝ) := Nat.cast_nonneg _
  have hε₀ : 0 < ε₀ := by
    refine lt_min (by norm_num) (lt_min (by positivity) (lt_min ?_ ?_))
    · linarith [hq₀.1]
    · linarith [hq₀.2]
  have hε₀1 : ε₀ ≤ 1 / 1000 := min_le_left _ _
  have hε₀2 : ε₀ ≤ minLen Γ η₀.1 / (1000 * ((Ng : ℝ) + 1)) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₀3 : ε₀ ≤ q₀ / 16 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε₀4 : ε₀ ≤ (Γ.length η₀.1 - q₀) / 16 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the key inequality relating the scale to the horizon
  have hden : (0 : ℝ) < 1000 * ((Ng : ℝ) + 1) := by linarith
  have hkey : ∀ e : ℝ, 0 < e → e ≤ ε₀ →
      1000 * e ≤ minLen Γ η₀.1 ∧ ((Ng : ℝ) + 1) * (16 * e) ≤ minLen Γ η₀.1 / 4 := by
    intro e he0 hele
    have h1 : e ≤ minLen Γ η₀.1 / (1000 * ((Ng : ℝ) + 1)) := le_trans hele hε₀2
    rw [le_div_iff₀ hden] at h1
    constructor
    · nlinarith
    · have hrw : ((Ng : ℝ) + 1) * (16 * e) = (16 / 1000) * (e * (1000 * ((Ng : ℝ) + 1))) := by
        ring
      rw [hrw]
      linarith
  -- the packages
  have hex : ∀ e : ℝ, Nonempty (NetPackage F η₀ q₀ c M (clampEps ε₀ e)) := by
    intro e
    obtain ⟨hlo, hhi⟩ := clampEps_mem hε₀ e
    refine exists_netPackage F η₀ M hlo (le_trans hhi.le hε₀1) (hkey _ hlo hhi.le).1 hc1 hc2 ?_ ?_
    · have : clampEps ε₀ e ≤ q₀ / 16 := le_trans hhi.le hε₀3
      linarith [hq₀.1]
    · have : clampEps ε₀ e ≤ (Γ.length η₀.1 - q₀) / 16 := le_trans hhi.le hε₀4
      linarith [hq₀.2]
  set pk : ∀ e : ℝ, NetPackage F η₀ q₀ c M (clampEps ε₀ e) := fun e => (hex e).some with hpkdef
  have heps : ∀ᶠ e in 𝓝[>] (0 : ℝ), clampEps ε₀ e = e :=
    eventually_nhdsGT_zero_of_forall_Ioo hε₀ (fun e he => clampEps_eq he.1 he.2)
  have habs8 : Tendsto (fun e : ℝ => 8 * |e|) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_abs_nhdsGT_zero.const_mul (8 : ℝ)
  have habs100 : Tendsto (fun e : ℝ => 100 * |e|) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_abs_nhdsGT_zero.const_mul (100 : ℝ)
  set fam : ThinNetworkFamily (zeroPotential Γ) F :=
    { params := fun e => netParams (clampEps ε₀ e)
      chain := fun e => (pk e).chain
      offset_tendsto := by
        refine Tendsto.congr' ?_ habs8
        filter_upwards [heps] with e he
        rw [netParams_offset, he]
      dwell_tendsto := by
        refine Tendsto.congr' ?_ habs100
        filter_upwards [heps] with e he
        rw [netParams_dwell, he]
      odeErr_tendsto := by
        simp only [netParams_odeErr]
        exact tendsto_const_nhds
      momErr_tendsto := by
        simp only [netParams_momErr]
        exact tendsto_const_nhds } with hfamdef
  have hgcurve : g.curve 0 0 = (q₀, EdgeEnd.sign Γ η₀ * c) :=
    genTrajectory_curve_zero_zero F η₀ q₀ c hq₀ hc0 Ng
  have hen : g.energy = c ^ 2 / 2 := genTrajectory_energy F η₀ q₀ c hq₀ hc0 Ng
  have hEmem : g.energy ∈ window := by
    rw [hen, window]
    exact ⟨by nlinarith, by nlinarith⟩
  have hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0)) := by
    rw [hgcurve]
    exact hq₀
  -- convergence of the initial data
  have hconv : fam.ConvergesInitially g := by
    refine ⟨Eventually.of_forall (fun e => (pk e).edge0), ?_, ?_⟩
    · have hfun : (fun e : ℝ => (fam.chain e).curve 0 0) =
          fun _ => ((q₀, EdgeEnd.sign Γ η₀ * c) : ℝ × ℝ) := by
        funext e; exact (pk e).curve0
      rw [hfun, hgcurve]
      exact tendsto_const_nhds
    · refine Eventually.of_forall (fun e => ?_)
      obtain ⟨hlo, hhi⟩ := clampEps_mem hε₀ e
      have hwin := (pk e).window
      have hMstart : GenTrajectory.startTime F η₀ q₀ c M =
          GenTrajectory.startTime F η₀ q₀ c Ng + GenTrajectory.travel F η₀ q₀ Ng / c :=
        GenTrajectory.startTime_succ Ng
      have hMcast : ((M : ℕ) : ℝ) = (Ng : ℝ) + 1 := by rw [hMdef]; push_cast; ring
      have htNg : minLen Γ η₀.1 ≤ GenTrajectory.travel F η₀ q₀ Ng := by
        obtain ⟨l, hl⟩ : ∃ l, Ng = l + 1 := ⟨Ng - 1, by omega⟩
        rw [hl, GenTrajectory.travel_succ]
        exact minLen_le_edgeLen η₀.1 (l + 1)
      have hhalf : minLen Γ η₀.1 / 4 ≤ GenTrajectory.travel F η₀ q₀ Ng / (2 * c) := by
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]
        nlinarith
      have hslack := (hkey _ hlo hhi.le).2
      rw [hMstart, hMcast] at hwin
      have hsplit : GenTrajectory.travel F η₀ q₀ Ng / c =
          GenTrajectory.travel F η₀ q₀ Ng / (2 * c) +
            GenTrajectory.travel F η₀ q₀ Ng / (2 * c) := by
        field_simp
        ring
      rw [hgstop]
      rw [hsplit] at hwin
      linarith
  have hcert : ∀ᶠ e in 𝓝[>] (0 : ℝ), IsNetworkProjection e (fam.chain e) := by
    refine eventually_nhdsGT_zero_of_forall_Ioo hε₀ (fun e he => ?_)
    exact ((pk e).proj).congr_scale (clampEps_eq he.1 he.2)
  refine ⟨g, ⟨rfl, hgcurve, hen, hEmem⟩, fam, hcert, hconv, hTg, ?_⟩
  exact microscopic_realization window isCompact_window (window_regular Γ) g hEmem hinit fam hconv

end HamiltonianMetricGraphs
