/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalNetworkRun

/-!
# Convergence of the projected trajectories of the uniform network

This file states in what sense the projected trajectories of the uniform network converge to the
graph trajectory, and derives the form used in the article from the chain-level statement of the
thin-network theory.

* `IsUniformProjection`: a projected chain is the image of a microscopic trajectory under the
  fixed charts `uniChart F ζ j`;
* `UniformMicroscopicConvergence`: the chain-level convergence (`RealizesGraphTrajectory'`) of a
  thin-network family of such projections;
* `CompactConvergence`: the form of Proposition IX.11.  On every compact set `K ⊆ [0, T]`
  containing no impact time of the graph trajectory, eventually every `t ∈ K` lies in a flight `j`
  of the graph trajectory and the microscopic state read in the fixed chart of that flight is
  uniformly close to the graph state (`compactConvergence_of_realizes`).

The passage from the first to the last uses that the flights of a chain with vanishing ODE error
at zero potential are affine (`HybridChain.curve_eq_affine`), which gives uniform convergence on
the whole first flight `[0, stop 0 - δ]`, and that the flights of a graph trajectory cover its
time window without gaps (`HybridChain.graph_exists_flight`).
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {Γ : FiniteMetricGraph}

/-! ### The notions of convergence -/

/-- **The chain `ch` is the projection of the trajectory `(x, p)` through the fixed charts** of
the corridor of `ζ`: flight `j` runs on the edge `(F.itinerary ζ j).1`, and during it the chain
state is the image of the microscopic state under `uniChart F ζ j`. -/
def IsUniformProjection {P : ChainParams} (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd)
    (x p : ℝ → ℝ × ℝ) (ch : HybridChain (zeroPotential Γ) F P) : Prop :=
  (∀ j ≤ ch.N, ch.edge j = (F.itinerary ζ j).1) ∧
    ∀ j ≤ ch.N, ∀ t ∈ Icc (ch.start j) (ch.stop j),
      ch.curve j t = uniChart F ζ j (x t).1 (p t).1

/-- **Convergence in the sense of the thin-network theory**: the projected trajectories form a
thin-network family (router offset, junction residence time, ODE and momentum tolerances tending to
`0`), the projections are taken through the fixed charts, the initial data converge, and the
projected chains converge to `g` (impact germs, impact times, and uniform convergence of the
longitudinal state away from the impacts). -/
def UniformMicroscopicConvergence (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (x p : ℝ → ℝ → ℝ × ℝ)
    (g : GraphTrajectory (zeroPotential Γ) F) : Prop :=
  ∃ fam : ThinNetworkFamily (zeroPotential Γ) F,
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsUniformProjection F ζ (x ε) (p ε) (fam.chain ε)) ∧
    (∀ ε, (fam.params ε).odeErr = 0) ∧
    fam.ConvergesInitially g ∧ RealizesGraphTrajectory' fam g

/-- **Convergence of the projected microscopic trajectories on compact sets avoiding the
impacts** (the conclusion of Proposition IX.11).  For every compact `K ⊆ [0, T]` which contains no
impact time `g.stop j` (`j < g.N`) of the graph trajectory and every `η > 0`, eventually every
`t ∈ K` lies in a flight `j` of `g`, and the microscopic state at time `t`, read in the fixed chart
of the corridor cell of that flight, is `η`-close to the graph state `g.curve j t`. -/
def CompactConvergence (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (x p : ℝ → ℝ → ℝ × ℝ)
    (g : GraphTrajectory (zeroPotential Γ) F) (T : ℝ) : Prop :=
  ∀ K ⊆ Icc (0 : ℝ) T, IsCompact K → (∀ j < g.N, g.stop j ∉ K) → ∀ η > (0 : ℝ),
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ K, ∃ j ≤ g.N, t ∈ Icc (g.start j) (g.stop j) ∧
      dist (uniChart F ζ j (x ε t).1 (p ε t).1) (g.curve j t) < η

/-! ### Flights at zero potential are affine -/

/-- **A flight of a chain with vanishing ODE error at zero potential is uniform motion.** -/
theorem MechanicalPotential.HybridChain.curve_eq_affine {F : RoutingLaw Γ} {P : ChainParams}
    (hP : P.odeErr = 0) (ch : HybridChain (zeroPotential Γ) F P) {j : ℕ} (hj : j ≤ ch.N) :
    ∀ t ∈ Icc (ch.start j) (ch.stop j), ch.curve j t =
      ((ch.curve j (ch.start j)).1 + (ch.curve j (ch.start j)).2 * (t - ch.start j),
        (ch.curve j (ch.start j)).2) := by
  obtain ⟨w, hw⟩ := ch.flight_ode j hj
  set a := ch.start j with ha
  set b := ch.stop j with hb
  have hder : ∀ t ∈ Icc a b,
      HasDerivWithinAt (ch.curve j) ((ch.curve j t).2, 0) (Icc a b) t := by
    intro t ht
    obtain ⟨h1, h2⟩ := hw t ht
    rw [hP, zeroPotential_edgeVectorField] at h1
    have hwt : w t = ((ch.curve j t).2, 0) := dist_le_zero.mp h1
    rwa [hwt] at h2
  have hcont : ContinuousOn (ch.curve j) (Icc a b) := fun t ht =>
    (hder t ht).continuousWithinAt
  have hpc : ∀ t ∈ Icc a b, (ch.curve j t).2 = (ch.curve j a).2 := by
    refine eq_of_has_deriv_right_eq (f' := fun _ => (0 : ℝ))
      (fun t ht => (hasDerivWithinAt_pairSnd (hder t (mem_Icc_of_Ico ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht))
      (fun t _ => hasDerivWithinAt_const _ _ _)
      (continuous_snd.comp_continuousOn hcont) continuousOn_const rfl
  refine eq_of_has_deriv_right_eq (f' := fun _ => ((ch.curve j a).2, (0 : ℝ))) ?_ ?_ hcont ?_ ?_
  · intro t ht
    have h := (hder t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
    rwa [hpc t (mem_Icc_of_Ico ht)] at h
  · intro t _
    have h1 : HasDerivWithinAt (fun s : ℝ => (ch.curve j a).1 + (ch.curve j a).2 * (s - a))
        (ch.curve j a).2 (Ici t) t := by
      simpa using (((hasDerivWithinAt_id t (Ici t)).sub_const a).const_mul
        (ch.curve j a).2).const_add (ch.curve j a).1
    exact h1.prodMk (hasDerivWithinAt_const _ _ _)
  · exact ((continuous_const.add (continuous_const.mul
      (continuous_id.sub continuous_const))).prodMk continuous_const).continuousOn
  · simp

/-! ### The flights of a graph trajectory cover its window -/

/-- At an impact of a graph trajectory the next flight starts immediately. -/
theorem MechanicalPotential.HybridChain.graph_start_succ_eq {F : RoutingLaw Γ}
    (g : GraphTrajectory (zeroPotential Γ) F) {j : ℕ} (hj : j < g.N) :
    g.start (j + 1) = g.stop j := by
  have h1 := g.stop_le_start_succ j hj
  have h2 := g.start_succ_le j hj
  simp only [ChainParams.zero_dwell, add_zero] at h2
  linarith

/-- **Every time of the window of a graph trajectory lies in one of its flights.** -/
theorem MechanicalPotential.HybridChain.graph_exists_flight {F : RoutingLaw Γ}
    (g : GraphTrajectory (zeroPotential Γ) F) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (g.stop g.N)) :
    ∃ j ≤ g.N, t ∈ Icc (g.start j) (g.stop j) := by
  classical
  have hex : ∃ j, j = g.N ∨ t ≤ g.stop j := ⟨g.N, Or.inl rfl⟩
  set j := Nat.find hex with hjdef
  have hjN : j ≤ g.N := Nat.find_min' hex (Or.inl rfl)
  have hspec := Nat.find_spec hex
  refine ⟨j, hjN, ?_, ?_⟩
  · cases hj : j with
    | zero => rw [g.start_zero]; exact ht.1
    | succ i =>
        have hi : i < j := by omega
        have hmin := Nat.find_min hex hi
        push Not at hmin
        rw [g.graph_start_succ_eq (by omega)]
        exact hmin.2.le
  · rcases hspec with h | h
    · rw [← hjdef] at h; rw [h]; exact ht.2
    · exact h

/-! ### From the chain-level statement to compact sets -/

/-- The chain-level convergence gives uniform convergence of the projected trajectories on every
compact part `[start j + δ, stop j - δ]` of a flight. -/
theorem flightConvergence_of_realizes {F : RoutingLaw Γ} {ζ : Γ.EdgeEnd}
    {x p : ℝ → ℝ → ℝ × ℝ} {g : GraphTrajectory (zeroPotential Γ) F}
    (fam : ThinNetworkFamily (zeroPotential Γ) F)
    (hproj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsUniformProjection F ζ (x ε) (p ε) (fam.chain ε))
    (hconv : fam.ConvergesInitially g) (hR : RealizesGraphTrajectory' fam g)
    {j : ℕ} (hj : j ≤ g.N) {δ : ℝ} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (g.start j + δ) (g.stop j - δ),
      dist (uniChart F ζ j (x ε t).1 (p ε t).1) (g.curve j t) < η := by
  obtain ⟨hmatch, hstop, hcurve, hfinal⟩ := hR
  have hm := hmatch j hj
  have hs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (fam.chain ε).start j < g.start j + δ :=
    hm.start.eventually (gt_mem_nhds (by linarith))
  rcases lt_or_eq_of_le hj with hlt | heq
  · obtain ⟨hst, -⟩ := hstop j hlt
    have hs2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), g.stop j - δ < (fam.chain ε).stop j :=
      hst.eventually (lt_mem_nhds (by linarith))
    filter_upwards [hm.eventually, hs, hs2, hproj, hcurve j hlt δ hδ η hη] with
      ε hN hs1 hs2 hpr hc
    intro t ht
    have ht' : t ∈ Icc ((fam.chain ε).start j) ((fam.chain ε).stop j) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [← hpr.2 j hN.1 t ht']
    exact hc t ht
  · subst heq
    obtain ⟨hf1, hf2⟩ := hfinal
    filter_upwards [hm.eventually, hs, hf1, hconv.finalTime, hproj, hf2 δ hδ η hη] with
      ε hN hs1 hf1' hfin hpr hc
    intro t ht
    have hstopge : g.stop g.N ≤ (fam.chain ε).stop g.N := by
      rcases lt_or_eq_of_le hN.1 with hlt | heq
      · exact (hf1' hlt).le
      · have h' := hfin
        rwa [← heq] at h'
    have ht' : t ∈ Icc ((fam.chain ε).start g.N) ((fam.chain ε).stop g.N) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [← hpr.2 g.N hN.1 t ht']
    exact hc t ⟨ht.1, by linarith [ht.2]⟩

/-- **Uniform convergence on the whole first flight**, from the initial time on: both the
projected chain and the graph trajectory move uniformly during their first flight, and their
initial states converge. -/
theorem initialConvergence_of_realizes {F : RoutingLaw Γ} {ζ : Γ.EdgeEnd}
    {x p : ℝ → ℝ → ℝ × ℝ} {g : GraphTrajectory (zeroPotential Γ) F}
    (fam : ThinNetworkFamily (zeroPotential Γ) F)
    (hproj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsUniformProjection F ζ (x ε) (p ε) (fam.chain ε))
    (hode : ∀ ε, (fam.params ε).odeErr = 0)
    (hconv : fam.ConvergesInitially g) (hR : RealizesGraphTrajectory' fam g)
    {δ : ℝ} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc 0 (g.stop 0 - δ),
      dist (uniChart F ζ 0 (x ε t).1 (p ε t).1) (g.curve 0 t) < η := by
  obtain ⟨hmatch, hstop, -, hfinal⟩ := hR
  have hm := hmatch 0 (Nat.zero_le _)
  -- the window of the first flight
  have hwin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), g.stop 0 - δ < (fam.chain ε).stop 0 := by
    rcases Nat.eq_zero_or_pos g.N with h0 | hpos
    · filter_upwards [hm.eventually, hfinal.1, hconv.finalTime] with ε hN hf1 hfin
      rcases lt_or_eq_of_le hN.1 with hlt | heq
      · have := hf1 (by rw [h0]; exact hlt); rw [h0] at this; linarith
      · rw [← heq, h0] at hfin; linarith
    · exact ((hstop 0 hpos).1).eventually (lt_mem_nhds (by linarith))
  -- the initial states converge
  set S := g.stop 0 with hS
  have hS0 : 0 < S := by
    have := g.start_lt_stop 0 (Nat.zero_le _); rwa [g.start_zero] at this
  set θ := η / (2 * (S + 1)) with hθ
  have hθ0 : 0 < θ := by positivity
  have hclose : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      dist ((fam.chain ε).curve 0 0) (g.curve 0 0) < θ :=
    hconv.state_zero.eventually (Metric.ball_mem_nhds _ hθ0)
  filter_upwards [hwin, hclose, hproj] with ε hw hc hpr
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have htS : t ≤ S := by linarith [ht.2]
  have hmem : t ∈ Icc ((fam.chain ε).start 0) ((fam.chain ε).stop 0) := by
    rw [(fam.chain ε).start_zero]; exact ⟨ht0, by linarith [ht.2]⟩
  have hmemg : t ∈ Icc (g.start 0) (g.stop 0) := by
    rw [g.start_zero]; exact ⟨ht0, htS⟩
  rw [← hpr.2 0 (Nat.zero_le _) t hmem,
    (fam.chain ε).curve_eq_affine (hode ε) (Nat.zero_le _) t hmem,
    g.curve_eq_affine rfl (Nat.zero_le _) t hmemg, (fam.chain ε).start_zero, g.start_zero]
  rw [Prod.dist_eq, max_lt_iff] at hc
  obtain ⟨hc1, hc2⟩ := hc
  rw [Real.dist_eq] at hc1 hc2
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  set a := (fam.chain ε).curve 0 0
  set b := g.curve 0 0
  have hkey : |a.1 + a.2 * (t - 0) - (b.1 + b.2 * (t - 0))| ≤ |a.1 - b.1| + |a.2 - b.2| * S := by
    have h1 : a.1 + a.2 * (t - 0) - (b.1 + b.2 * (t - 0)) = (a.1 - b.1) + (a.2 - b.2) * t := by
      ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg ht0]
    gcongr
  have hθS : θ + θ * S < η := by
    have : θ + θ * S = η / 2 := by rw [hθ]; field_simp; ring
    linarith
  constructor
  · have : |a.2 - b.2| * S ≤ θ * S := mul_le_mul_of_nonneg_right hc2.le hS0.le
    linarith
  · have : θ ≤ θ + θ * S := by nlinarith
    linarith

/-- **The conclusion of Proposition IX.11 from the chain-level statement.** -/
theorem compactConvergence_of_realizes {F : RoutingLaw Γ} {ζ : Γ.EdgeEnd}
    {x p : ℝ → ℝ → ℝ × ℝ} {g : GraphTrajectory (zeroPotential Γ) F} {T : ℝ}
    (hT : T < g.stop g.N) (hU : UniformMicroscopicConvergence F ζ x p g) :
    CompactConvergence F ζ x p g T := by
  obtain ⟨fam, hproj, hode, hconv, hR⟩ := hU
  intro K hKT hK hKimp η hη
  -- a uniform distance of `K` from the impacts and from the end of the window
  have hsep : ∀ j ∈ Finset.range g.N, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ t ∈ K, δ ≤ |t - g.stop j| := by
    intro j hj
    have hjN : j < g.N := Finset.mem_range.mp hj
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl (g.stop j)
      (hKimp j hjN)
    filter_upwards [eventually_nhdsGT_zero_of_forall_Ioo hr fun δ hδ => hδ] with δ hδ t ht
    by_contra hcon
    push Not at hcon
    have hin : t ∈ Metric.ball (g.stop j) r := by
      rw [Metric.mem_ball, Real.dist_eq]; linarith [hδ.2]
    exact hball hin ht
  have hδall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ≤ g.stop g.N - T ∧
      ∀ j ∈ Finset.range g.N, ∀ t ∈ K, δ ≤ |t - g.stop j| := by
    have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ g.stop g.N - T :=
      eventually_nhdsGT_zero_of_forall_Ioo (sub_pos.mpr hT) fun δ hδ => hδ.2.le
    have h3 := (eventually_all_finset (Finset.range g.N)).mpr hsep
    filter_upwards [h1, h2, h3] with δ a b c using ⟨a, b, c⟩
  obtain ⟨δ, hδ0, hδT, hδK⟩ := hδall.exists
  -- convergence on all the flights at once
  have hflights : ∀ j ∈ Finset.range (g.N + 1), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Icc (g.start j + δ) (g.stop j - δ),
        dist (uniChart F ζ j (x ε t).1 (p ε t).1) (g.curve j t) < η := fun j hj =>
    flightConvergence_of_realizes fam hproj hconv hR
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hδ0 hη
  filter_upwards [(eventually_all_finset _).mpr hflights,
    initialConvergence_of_realizes fam hproj hode hconv hR hδ0 hη] with ε hfl hinit
  intro t ht
  have htT := hKT ht
  obtain ⟨j, hjN, hj⟩ := g.graph_exists_flight ⟨htT.1, by linarith [htT.2]⟩
  refine ⟨j, hjN, hj, ?_⟩
  -- `t` keeps the distance `δ` from the end of its flight
  have hupper : t ≤ g.stop j - δ := by
    rcases lt_or_eq_of_le hjN with hlt | heq
    · have := hδK j (Finset.mem_range.mpr hlt) t ht
      rw [abs_of_nonpos (by linarith [hj.2])] at this
      linarith
    · rw [heq]; linarith [htT.2]
  cases j with
  | zero => exact hinit t ⟨htT.1, hupper⟩
  | succ i =>
      have hiN : i < g.N := by omega
      have hstart := g.graph_start_succ_eq hiN
      have := hδK i (Finset.mem_range.mpr hiN) t ht
      rw [abs_of_nonneg (by linarith [hj.1])] at this
      exact hfl (i + 1) (Finset.mem_range.mpr (by omega)) t ⟨by linarith, hupper⟩

end HamiltonianMetricGraphs
