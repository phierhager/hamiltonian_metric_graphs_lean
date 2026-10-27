/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalNetworkConvergence
import HamiltonianMetricGraphs.Realization.UniversalNetworkExistence

/-!
# The uniform universal realization theorem (Proposition IX.11)

For a finite metric graph `Γ` with a routing law `F` and zero graph potential, the potential
`uniPot F ε` of `UniversalNetworkPotential.lean` depends only on `(Γ, F)` and `ε`.  This file
proves that the projected trajectories of `H_ε = ½|p|² + uniPot F ε` converge to the graph
trajectory for **every** well-prepared graph state `x₀` with energy in `K⋆ = [1/2, 2]`, **every**
horizon `T` and **every** family of prepared microscopic initial data converging to `x₀`
(`universal_reversible_realization_uniform`).  The network, the projection charts and the
admissible initial data are fixed before `x₀` and `T` are chosen.

Compared with `universal_reversible_realization`:

* the network does not depend on the initial state or on the horizon.  A circle component of
  `R(Γ, F)` is realized by an infinite corridor without caps, in which the motion is free for all
  time; an interval component by the corridor between its two fixed ends, closed by caps;
* the microscopic initial data are arbitrary prepared data: in the tube of the corridor of the
  initial germ at scale `ε`, with longitudinal energy in `K⋆`, transverse energy tending to `0`,
  and projected longitudinal state converging to the graph state of `x₀`.  They need not lie on the
  tube axis and need not carry the exact graph data;
* the statement concerns *every* trajectory of `H_ε` on `[0, ∞)` from these data, not a
  constructed one.  Such trajectories exist (`IsPreparedFamily.exists_trajectories`, from
  `exists_uniTrajectory` in `UniversalNetworkExistence.lean`);
* the conclusion is also stated in the form of the article: uniform convergence of the projected
  state on every compact subset of `[0, T]` containing no impact time (`CompactConvergence`).

## Layout

There is one corridor per edge-end germ `ζ`, on the line `w = uniRow ζ`; the corridor of `ζ`
carries the routing component of `ζ` unrolled forward from `ζ`.  This is a redundant but faithful
layout of `R(Γ, F)`: a component with `k` germs appears in `k` corridors, and the particle uses the
corridor of the germ it initially moves towards.  The corridors depend on `(Γ, F)` only.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {Γ : FiniteMetricGraph}

/-! ### Prepared microscopic data -/

/-- **A family of prepared microscopic initial data converging to the graph state `x₀`.**  The
state at scale `ε` is `z ε = ((u, w), (ξ_u, ξ_w))`.  It lies in the tube of the corridor of the
initial germ (`|w - uniRow ζ| ≤ 2ε`), its longitudinal energy `ξ_u² / 2` lies in the window
`K⋆ = [1/2, 2]`, its transverse energy `ξ_w² / 2 + wellPot ε (w - uniRow ζ)` tends to `0`, and its
longitudinal state, read in the fixed chart of the first flight, converges to the graph state
`(q₀, σ(ζ) c)` of `x₀`. -/
structure IsPreparedFamily (F : RoutingLaw Γ) (x₀ : WellPreparedState Γ)
    (z : ℝ → (ℝ × ℝ) × (ℝ × ℝ)) : Prop where
  /-- the projected longitudinal state converges to the graph state -/
  long : Tendsto (fun ε => uniChart F x₀.germ 0 (z ε).1.1 (z ε).2.1) (𝓝[>] 0)
    (𝓝 (x₀.q₀, EdgeEnd.sign Γ x₀.germ * x₀.c))
  /-- the longitudinal energy lies in the window `K⋆` -/
  energy : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (z ε).2.1 ^ 2 / 2 ∈ window
  /-- the particle starts in the tube of the corridor of the initial germ -/
  tube : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |(z ε).1.2 - uniRow x₀.germ| ≤ 2 * ε
  /-- the transverse energy tends to `0` -/
  transverse : Tendsto (fun ε => (z ε).2.2 ^ 2 / 2 + wellPot ε ((z ε).1.2 - uniRow x₀.germ))
    (𝓝[>] 0) (𝓝 0)

/-- **The hypotheses can be met**: the data on the tube axis carrying the exact graph state of
`x₀` at every scale form a prepared family. -/
theorem isPreparedFamily_axis (F : RoutingLaw Γ) (x₀ : WellPreparedState Γ) :
    IsPreparedFamily F x₀ fun _ =>
      ((vpos F x₀.germ 1 - corridorLow F x₀.germ - GenTrajectory.travel F x₀.germ x₀.q₀ 0,
        uniRow x₀.germ), (x₀.c, 0)) where
  long := by
    have h := q₀_add_sign_travel (F := F) (η₀ := x₀.germ) (q₀ := x₀.q₀)
    have hval : uniChart F x₀.germ 0
        (vpos F x₀.germ 1 - corridorLow F x₀.germ - GenTrajectory.travel F x₀.germ x₀.q₀ 0)
        x₀.c = (x₀.q₀, EdgeEnd.sign Γ x₀.germ * x₀.c) := by
      refine Prod.ext ?_ (uniChart_zero_snd F x₀.germ _ _)
      change EdgeEnd.coordinate Γ (F.itinerary x₀.germ 0) + chartSign F x₀.germ 0 *
        (vpos F x₀.germ 1 - corridorLow F x₀.germ - GenTrajectory.travel F x₀.germ x₀.q₀ 0 -
          (vpos F x₀.germ (0 + 1) - corridorLow F x₀.germ)) = x₀.q₀
      rw [chartSign, dirSign_zero, mul_one, show F.itinerary x₀.germ 0 = x₀.germ from rfl]
      linarith
    simp only [hval]
    exact tendsto_const_nhds
  energy := by
    refine Eventually.of_forall fun _ => ?_
    have := x₀.speed
    change x₀.c ^ 2 / 2 ∈ Icc (1 / 2 : ℝ) 2
    exact ⟨by nlinarith [this.1], by nlinarith [this.1, this.2]⟩
  tube := by
    filter_upwards [self_mem_nhdsWithin] with e (he : 0 < e)
    simp only [sub_self, abs_zero]
    linarith
  transverse := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e (he : 0 < e)
    simp only [sub_self]
    rw [wellPot_of_abs_le he (by simp [he.le])]
    norm_num

/-! ### Preparations -/

/-- At the initial point of a prepared state the longitudinal potential vanishes. -/
theorem longPot_init (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) {ε : ℝ} (hε : 0 < ε)
    (hεm : 1000 * ε ≤ minLen Γ ζ.1) {u v : ℝ} (hq1 : 8 * ε < (uniChart F ζ 0 u v).1)
    (hq2 : (uniChart F ζ 0 u v).1 < Γ.length ζ.1 - 8 * ε) : longPot F ε ζ u = 0 := by
  by_cases h : ∃ k, IsFold F ζ k
  · set C := foldCorridor F ζ h 0
    have hu : u = spos C (uniChart F ζ 0 u v).1 ε 0 := by
      rw [spos_zero]; exact (uniChart_zero_fst_travel C rfl _ _).symm
    have hmem := spos_mem (C := C) hε hεm hq1 hq2 (le_refl 0)
    rw [← hu] at hmem
    rw [longPot_of_fold F ε ζ h, ← clen_foldCorridor F ζ h 0]
    exact corridorPot_of_mem hε (by linarith [hmem.1]) (by linarith [hmem.2])
  · rw [longPot_of_not_fold F ε ζ h]

/-- **A prepared state lies strictly inside its tube, below the wall height.** -/
theorem prepared_tube_energy (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) {ε : ℝ}
    (hε : 0 < ε) (hεs : ε ≤ 1 / 1000) (hεm : 1000 * ε ≤ minLen Γ ζ.1) {y q : ℝ × ℝ}
    (hc : q.1 ^ 2 / 2 ≤ 2)
    (hq1 : 8 * ε < (uniChart F ζ 0 y.1 q.1).1)
    (hq2 : (uniChart F ζ 0 y.1 q.1).1 < Γ.length ζ.1 - 8 * ε)
    (htube : |y.2 - uniRow ζ| ≤ 2 * ε)
    (htr : q.2 ^ 2 / 2 + wellPot ε (y.2 - uniRow ζ) < 1) :
    |y.2 - uniRow ζ| < 2 * ε ∧ hamEnergy (uniPot F ε) y q < 4 := by
  have hεs' : ε ≤ 1 / 8 := by linarith
  refine ⟨?_, ?_⟩
  · rcases lt_or_eq_of_le htube with h | h
    · exact h
    · exfalso
      have h4 : wellPot ε (y.2 - uniRow ζ) = 4 := wellPot_of_two_le_abs hε h.ge
      nlinarith [sq_nonneg q.2]
  · have hpot : uniPot F ε y = wellPot ε (y.2 - uniRow ζ) + longPot F ε ζ y.1 :=
      uniPot_of_tube F hε hεs' ζ htube
    rw [hamEnergy, hpot, longPot_init F ζ hε hεm hq1 hq2]
    nlinarith

/-- **A trajectory from a prepared state is confined to its tube and yields a package.** -/
theorem exists_uniPackage_of_prepared (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (M : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hεs : ε ≤ 1 / 1000) (hεm : 1000 * ε ≤ minLen Γ ζ.1)
    {x p : ℝ → ℝ × ℝ} (hsol : IsHamiltonianTrajectory (uniPot F ε) x p)
    (hc1 : 1 ≤ (p 0).1) (hc2 : (p 0).1 ≤ 2)
    (hq1 : 8 * ε < (uniChart F ζ 0 (x 0).1 (p 0).1).1)
    (hq2 : (uniChart F ζ 0 (x 0).1 (p 0).1).1 < Γ.length ζ.1 - 8 * ε)
    (htube : |(x 0).2 - uniRow ζ| ≤ 2 * ε)
    (htr : (p 0).2 ^ 2 / 2 + wellPot ε ((x 0).2 - uniRow ζ) < 1) :
    (∀ t, 0 ≤ t → |(x t).2 - uniRow ζ| < 2 * ε) ∧ Nonempty (UniPackage F ζ M ε x p) := by
  obtain ⟨hstrict, hE⟩ := prepared_tube_energy F ζ hε hεs hεm (by nlinarith) hq1 hq2 htube htr
  have hconf := uni_confined F hε (by linarith) hsol ζ hstrict hE
  exact ⟨hconf, exists_uniPackage F ζ M hε hεs hεm hsol hconf hc1 hc2 hq1 hq2⟩

/-- The start times of the graph trajectory depend continuously on the initial coordinate and
the speed. -/
theorem tendsto_startTime (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) {α : Type*} {l : Filter α}
    {qf cf : α → ℝ} {q c : ℝ} (hq : Tendsto qf l (𝓝 q)) (hcf : Tendsto cf l (𝓝 c))
    (hc : c ≠ 0) (j : ℕ) :
    Tendsto (fun a => GenTrajectory.startTime F ζ (qf a) (cf a) j) l
      (𝓝 (GenTrajectory.startTime F ζ q c j)) := by
  induction j with
  | zero => simp only [GenTrajectory.startTime_zero]; exact tendsto_const_nhds
  | succ i ih =>
      simp only [GenTrajectory.startTime_succ]
      refine ih.add (Tendsto.div ?_ hcf hc)
      cases i with
      | zero =>
          rcases hb : ζ.2 with _ | _
          · simp only [GenTrajectory.travel_zero_of_false hb]; exact hq
          · simp only [GenTrajectory.travel_zero_of_true hb]; exact tendsto_const_nhds.sub hq
      | succ k => simp only [GenTrajectory.travel_succ]; exact tendsto_const_nhds

/-! ### Prepared data at small scales -/

/-- The properties of the prepared data `z` at the scale `e` used by the construction. -/
def PreparedAt (F : RoutingLaw Γ) (x₀ : WellPreparedState Γ) (z : ℝ → (ℝ × ℝ) × (ℝ × ℝ))
    (ε₀ e : ℝ) : Prop :=
  0 < e ∧ e < ε₀ ∧ 1 ≤ (z e).2.1 ∧ (z e).2.1 ≤ 2 ∧
    8 * e < (uniChart F x₀.germ 0 (z e).1.1 (z e).2.1).1 ∧
    (uniChart F x₀.germ 0 (z e).1.1 (z e).2.1).1 < Γ.length x₀.germ.1 - 8 * e ∧
    |(z e).1.2 - uniRow x₀.germ| ≤ 2 * e ∧
    (z e).2.2 ^ 2 / 2 + wellPot e ((z e).1.2 - uniRow x₀.germ) < 1

/-- The longitudinal momentum of prepared data converges to the speed of `x₀`. -/
theorem IsPreparedFamily.tendsto_speed {F : RoutingLaw Γ} {x₀ : WellPreparedState Γ}
    {z : ℝ → (ℝ × ℝ) × (ℝ × ℝ)} (hz : IsPreparedFamily F x₀ z) :
    Tendsto (fun e => (z e).2.1) (𝓝[>] 0) (𝓝 x₀.c) := by
  have h2 : Tendsto (fun e => (uniChart F x₀.germ 0 (z e).1.1 (z e).2.1).2) (𝓝[>] 0)
      (𝓝 (EdgeEnd.sign Γ x₀.germ * x₀.c)) := (continuous_snd.tendsto _).comp hz.long
  have hsq : EdgeEnd.sign Γ x₀.germ * EdgeEnd.sign Γ x₀.germ = 1 := by
    have := Γ.edgeEnd_sign_sq x₀.germ; nlinarith [this]
  have h3 := h2.const_mul (EdgeEnd.sign Γ x₀.germ)
  rw [← mul_assoc, hsq, one_mul] at h3
  refine h3.congr fun e => ?_
  rw [uniChart_zero_snd, ← mul_assoc, hsq, one_mul]

/-- **Prepared data have the properties used by the construction at every small scale.** -/
theorem IsPreparedFamily.eventually_preparedAt {F : RoutingLaw Γ} {x₀ : WellPreparedState Γ}
    {z : ℝ → (ℝ × ℝ) × (ℝ × ℝ)} (hz : IsPreparedFamily F x₀ z) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), PreparedAt F x₀ z ε₀ e := by
  have hq₀ := x₀.inside
  have hc0 : (0 : ℝ) < x₀.c := by linarith [x₀.speed.1]
  have hqf : Tendsto (fun e => (uniChart F x₀.germ 0 (z e).1.1 (z e).2.1).1) (𝓝[>] 0)
      (𝓝 x₀.q₀) := (continuous_fst.tendsto _).comp hz.long
  have hpos : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e := self_mem_nhdsWithin
  have hlt : ∀ᶠ e in 𝓝[>] (0 : ℝ), e < ε₀ :=
    eventually_nhdsGT_zero_of_forall_Ioo hε₀ fun e he => he.2
  have hcpos : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < (z e).2.1 :=
    hz.tendsto_speed.eventually (lt_mem_nhds hc0)
  have hid : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlo : ∀ᶠ e in 𝓝[>] (0 : ℝ),
      0 < (uniChart F x₀.germ 0 (z e).1.1 (z e).2.1).1 - 8 * e := by
    have := hqf.sub (hid.const_mul 8)
    rw [mul_zero, sub_zero] at this
    exact this.eventually (lt_mem_nhds hq₀.1)
  have hhi : ∀ᶠ e in 𝓝[>] (0 : ℝ),
      0 < Γ.length x₀.germ.1 - 8 * e - (uniChart F x₀.germ 0 (z e).1.1 (z e).2.1).1 := by
    have := (tendsto_const_nhds (x := Γ.length x₀.germ.1)).sub (hid.const_mul 8) |>.sub hqf
    rw [mul_zero, sub_zero] at this
    exact this.eventually (lt_mem_nhds (by linarith [hq₀.2]))
  have htr : ∀ᶠ e in 𝓝[>] (0 : ℝ),
      (z e).2.2 ^ 2 / 2 + wellPot e ((z e).1.2 - uniRow x₀.germ) < 1 :=
    hz.transverse.eventually (gt_mem_nhds one_pos)
  filter_upwards [hpos, hlt, hcpos, hz.energy, hlo, hhi, hz.tube, htr] with
    e he1 he2 hcp hen hlo hhi htube htr
  rw [window] at hen
  refine ⟨he1, he2, ?_, ?_, by linarith, by linarith, htube, htr⟩
  · nlinarith [hen.1]
  · nlinarith [hen.2]

/-- **Trajectories from prepared data exist** at every small scale: the hypotheses of the
realization theorem can be met for every family of prepared data. -/
theorem IsPreparedFamily.exists_trajectories {F : RoutingLaw Γ} {x₀ : WellPreparedState Γ}
    {z : ℝ → (ℝ × ℝ) × (ℝ × ℝ)} (hz : IsPreparedFamily F x₀ z) :
    ∃ x p : ℝ → ℝ → ℝ × ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IsHamiltonianTrajectory (uniPot F ε) (x ε) (p ε) ∧ x ε 0 = (z ε).1 ∧ p ε 0 = (z ε).2 := by
  set ε₀ := min (1 / 1000) (minLen Γ x₀.germ.1 / 1000) with hε₀def
  have hml := minLen_pos Γ x₀.germ.1
  have hε₀ : 0 < ε₀ := lt_min (by norm_num) (by positivity)
  have hex : ∀ e : ℝ, ∃ xe pe : ℝ → ℝ × ℝ, PreparedAt F x₀ z ε₀ e →
      IsHamiltonianTrajectory (uniPot F e) xe pe ∧ xe 0 = (z e).1 ∧ pe 0 = (z e).2 := by
    intro e
    by_cases hP : PreparedAt F x₀ z ε₀ e
    · obtain ⟨he, heε, hc1, hc2, hq1, hq2, htube, htr⟩ := hP
      have hes : e ≤ 1 / 1000 := le_trans heε.le (min_le_left _ _)
      have hem : 1000 * e ≤ minLen Γ x₀.germ.1 := by
        have := le_trans heε.le (min_le_right _ _); linarith
      obtain ⟨hstrict, hE⟩ := prepared_tube_energy F x₀.germ he hes hem (by nlinarith) hq1 hq2
        htube htr
      obtain ⟨xe, pe, hx0, hp0, hsole⟩ :=
        exists_uniTrajectory F he (by linarith) x₀.germ (z e).1 (z e).2 hstrict hE
      exact ⟨xe, pe, fun _ => ⟨hsole, hx0, hp0⟩⟩
    · exact ⟨fun _ => 0, fun _ => 0, fun h => absurd h hP⟩
  choose x p hxp using hex
  exact ⟨x, p, (hz.eventually_preparedAt hε₀).mono fun e he => hxp e he⟩

/-! ### The theorem -/

/-- **Realization from prepared data in the uniform network.**

Let `Γ` be a finite metric graph with the zero potential and `F` a routing law.  For a
well-prepared graph state `x₀` with energy `c²/2 ∈ K⋆ = [1/2, 2]`, a horizon `T`, a family `z ε`
of prepared microscopic initial data converging to `x₀` (`IsPreparedFamily`), and **any** family
of trajectories `(x ε, p ε)` of `H_ε = ½|p|² + uniPot F ε` on `[0, ∞)` starting at `z ε` (for all
small `ε`), there is the graph trajectory `g` of `x₀`, covering `[0, T]`, such that

* eventually the particle stays in the tube `|w - uniRow ζ| < 2ε` of its corridor for all time;
* the projected microscopic trajectories form a thin-network family converging to `g`
  (`UniformMicroscopicConvergence`);
* on every compact `K ⊆ [0, T]` containing no impact time, the microscopic state read in the
  fixed chart of the current flight converges uniformly to the graph state
  (`CompactConvergence`). -/
theorem uniPot_realization_of_prepared (Γ : FiniteMetricGraph) (F : RoutingLaw Γ)
    (x₀ : WellPreparedState Γ) (T : ℝ)
    {z : ℝ → (ℝ × ℝ) × (ℝ × ℝ)} (hz : IsPreparedFamily F x₀ z)
    {x p : ℝ → ℝ → ℝ × ℝ}
    (hsol : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsHamiltonianTrajectory (uniPot F ε) (x ε) (p ε))
    (hinit : ∀ᶠ ε in 𝓝[>] (0 : ℝ), x ε 0 = (z ε).1 ∧ p ε 0 = (z ε).2) :
    ∃ g : GraphTrajectory (zeroPotential Γ) F,
      (g.germ 0 = x₀.germ ∧ g.curve 0 0 = (x₀.q₀, EdgeEnd.sign Γ x₀.germ * x₀.c) ∧
        g.energy = x₀.c ^ 2 / 2 ∧ g.energy ∈ window) ∧
      T < g.stop g.N ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t, 0 ≤ t → |(x ε t).2 - uniRow x₀.germ| < 2 * ε) ∧
      UniformMicroscopicConvergence F x₀.germ x p g ∧
      CompactConvergence F x₀.germ x p g T := by
  set ζ := x₀.germ with hζ
  set q₀ := x₀.q₀ with hq₀def
  set c := x₀.c with hcdef
  have hq₀ : q₀ ∈ Ioo (0 : ℝ) (Γ.length ζ.1) := x₀.inside
  have hc1 : (1 : ℝ) ≤ c := x₀.speed.1
  have hc2 : c ≤ 2 := x₀.speed.2
  have hc0 : (0 : ℝ) < c := by linarith
  haveI : Nonempty Γ.Edge := ⟨ζ.1⟩
  have hml : 0 < minLen Γ ζ.1 := minLen_pos Γ ζ.1
  set Ng : ℕ := ⌈2 * T / minLen Γ ζ.1⌉₊ + 2 with hNgdef
  set g := genTrajectory F ζ q₀ c hq₀ hc0 Ng with hgdef
  set M : ℕ := Ng + 1 with hMdef
  -- the horizon is covered
  have hgstop : g.stop g.N =
      GenTrajectory.startTime F ζ q₀ c Ng + GenTrajectory.travel F ζ q₀ Ng / (2 * c) :=
    genTrajectory_stop F ζ q₀ c hq₀ hc0 Ng
  have hTg : T < g.stop g.N := by
    have h1 := startTime_ge F ζ hq₀ hc0 hc2 Ng
    have h2 : (0 : ℝ) ≤ GenTrajectory.travel F ζ q₀ Ng / (2 * c) :=
      le_of_lt (div_pos (GenTrajectory.travel_pos hq₀ Ng) (by linarith))
    have hceil : 2 * T / minLen Γ ζ.1 ≤ (⌈2 * T / minLen Γ ζ.1⌉₊ : ℝ) := Nat.le_ceil _
    have hNgcast : ((Ng : ℝ) - 1) = (⌈2 * T / minLen Γ ζ.1⌉₊ : ℝ) + 1 := by
      rw [hNgdef]; push_cast; ring
    rw [hgstop]
    have hkey : T < ((Ng : ℝ) - 1) * (minLen Γ ζ.1 / 2) := by
      rw [hNgcast]
      have hd : 2 * T / minLen Γ ζ.1 * minLen Γ ζ.1 = 2 * T := by field_simp
      nlinarith [hceil, hml]
    linarith
  -- the scale threshold
  set ε₀ : ℝ := min (1 / 1000) (min (minLen Γ ζ.1 / 1000)
    (min (q₀ / 16) ((Γ.length ζ.1 - q₀) / 16))) with hε₀def
  have hε₀ : 0 < ε₀ := by
    refine lt_min (by norm_num) (lt_min (by positivity) (lt_min ?_ ?_))
    · linarith [hq₀.1]
    · linarith [hq₀.2]
  have hε₀1 : ε₀ ≤ 1 / 1000 := min_le_left _ _
  have hε₀2 : ε₀ ≤ minLen Γ ζ.1 / 1000 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₀3 : ε₀ ≤ q₀ / 16 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε₀4 : ε₀ ≤ (Γ.length ζ.1 - q₀) / 16 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the prepared data
  set qf : ℝ → ℝ := fun e => (uniChart F ζ 0 (z e).1.1 (z e).2.1).1 with hqfdef
  set cf : ℝ → ℝ := fun e => (z e).2.1 with hcfdef
  have hqf : Tendsto qf (𝓝[>] 0) (𝓝 q₀) := (continuous_fst.tendsto _).comp hz.long
  have hcf : Tendsto cf (𝓝[>] 0) (𝓝 c) := hz.tendsto_speed
  -- the good scales
  set Good : ℝ → Prop := fun e => PreparedAt F x₀ z ε₀ e ∧
    IsHamiltonianTrajectory (uniPot F e) (x e) (p e) ∧ x e 0 = (z e).1 ∧ p e 0 = (z e).2
    with hGooddef
  have hgood : ∀ᶠ e in 𝓝[>] (0 : ℝ), Good e := by
    filter_upwards [hz.eventually_preparedAt hε₀, hsol, hinit] with e h1 h2 h3 using ⟨h1, h2, h3⟩
  -- the chains, for every scale
  have hex : ∀ e : ℝ, ∃ ch : HybridChain (zeroPotential Γ) F (netParams (clampEps ε₀ e)),
      Good e → (IsUniformProjection F ζ (x e) (p e) ch ∧
        ch.curve 0 0 = uniChart F ζ 0 (x e 0).1 (p e 0).1 ∧
        GenTrajectory.startTime F ζ (uniChart F ζ 0 (x e 0).1 (p e 0).1).1 (p e 0).1 M -
          (M : ℝ) * (16 * e) ≤ ch.stop ch.N ∧
        ∀ t, 0 ≤ t → |(x e t).2 - uniRow ζ| < 2 * e) := by
    intro e
    by_cases hG : Good e
    · obtain ⟨⟨he, heε, hce1, hce2, hqe1, hqe2, htube, htr⟩, hsole, hx0, hp0⟩ := hG
      rw [clampEps_eq he heε]
      have hes : e ≤ 1 / 1000 := by linarith
      have hem : 1000 * e ≤ minLen Γ ζ.1 := by linarith
      have hc1' : 1 ≤ (p e 0).1 := by rw [hp0]; exact hce1
      have hc2' : (p e 0).1 ≤ 2 := by rw [hp0]; exact hce2
      have hq1' : 8 * e < (uniChart F ζ 0 (x e 0).1 (p e 0).1).1 := by rw [hx0, hp0]; exact hqe1
      have hq2' : (uniChart F ζ 0 (x e 0).1 (p e 0).1).1 < Γ.length ζ.1 - 8 * e := by
        rw [hx0, hp0]; exact hqe2
      have htube' : |(x e 0).2 - uniRow ζ| ≤ 2 * e := by rw [hx0]; exact htube
      have htr' : (p e 0).2 ^ 2 / 2 + wellPot e ((x e 0).2 - uniRow ζ) < 1 := by
        rw [hx0, hp0]; exact htr
      obtain ⟨hconf, ⟨pk⟩⟩ := exists_uniPackage_of_prepared F ζ M he hes hem hsole
        hc1' hc2' hq1' hq2' htube' htr'
      refine ⟨pk.chain, fun _ => ⟨⟨fun j _ => pk.edge j, pk.proj⟩, pk.curve0, ?_, hconf⟩⟩
      have := pk.window
      rwa [pk.card] at this ⊢
    · obtain ⟨hlo, hhi⟩ := clampEps_mem hε₀ e
      have hq1 : 8 * clampEps ε₀ e < q₀ := by
        have : clampEps ε₀ e ≤ q₀ / 16 := le_trans hhi.le hε₀3
        linarith [hq₀.1]
      have hq2 : q₀ < Γ.length ζ.1 - 8 * clampEps ε₀ e := by
        have : clampEps ε₀ e ≤ (Γ.length ζ.1 - q₀) / 16 := le_trans hhi.le hε₀4
        linarith [hq₀.2]
      obtain ⟨pk⟩ := exists_netPackage F ζ M hlo (le_trans hhi.le hε₀1)
        (by linarith [le_trans hhi.le hε₀2]) hc1 hc2 hq1 hq2
      exact ⟨pk.chain, fun h => absurd h hG⟩
  choose chF hchF using hex
  have heps : ∀ᶠ e in 𝓝[>] (0 : ℝ), clampEps ε₀ e = e :=
    eventually_nhdsGT_zero_of_forall_Ioo hε₀ (fun e he => clampEps_eq he.1 he.2)
  have habs8 : Tendsto (fun e : ℝ => 8 * |e|) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_abs_nhdsGT_zero.const_mul (8 : ℝ)
  have habs100 : Tendsto (fun e : ℝ => 100 * |e|) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_abs_nhdsGT_zero.const_mul (100 : ℝ)
  set fam : ThinNetworkFamily (zeroPotential Γ) F :=
    { params := fun e => netParams (clampEps ε₀ e)
      chain := chF
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
  have hgcurve : g.curve 0 0 = (q₀, EdgeEnd.sign Γ ζ * c) :=
    genTrajectory_curve_zero_zero F ζ q₀ c hq₀ hc0 Ng
  have hen : g.energy = c ^ 2 / 2 := genTrajectory_energy F ζ q₀ c hq₀ hc0 Ng
  have hEmem : g.energy ∈ window := by
    rw [hen, window]
    exact ⟨by nlinarith, by nlinarith⟩
  have hinit' : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0)) := by
    rw [hgcurve]
    exact hq₀
  have hproj : ∀ᶠ e in 𝓝[>] (0 : ℝ), IsUniformProjection F ζ (x e) (p e) (fam.chain e) := by
    filter_upwards [hgood] with e hG
    exact (hchF e hG).1
  -- convergence of the initial data
  have hconv : fam.ConvergesInitially g := by
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [hgood] with e hG
      exact (hchF e hG).1.1 0 (Nat.zero_le _)
    · have hfun : ∀ᶠ e in 𝓝[>] (0 : ℝ), uniChart F ζ 0 (z e).1.1 (z e).2.1 =
          (fam.chain e).curve 0 0 := by
        filter_upwards [hgood] with e hG
        change _ = (chF e).curve 0 0
        rw [(hchF e hG).2.1, hG.2.2.1, hG.2.2.2]
      rw [hgcurve]
      exact hz.long.congr' hfun
    · -- the microscopic chains run past the end of `g`
      have hMstart : GenTrajectory.startTime F ζ q₀ c M =
          GenTrajectory.startTime F ζ q₀ c Ng + GenTrajectory.travel F ζ q₀ Ng / c :=
        GenTrajectory.startTime_succ Ng
      have hlimit : g.stop g.N < GenTrajectory.startTime F ζ q₀ c M - (M : ℝ) * (16 * 0) := by
        rw [hgstop, hMstart, mul_zero, mul_zero, sub_zero]
        have htp : 0 < GenTrajectory.travel F ζ q₀ Ng := GenTrajectory.travel_pos hq₀ Ng
        have : GenTrajectory.travel F ζ q₀ Ng / (2 * c) < GenTrajectory.travel F ζ q₀ Ng / c :=
          div_lt_div_of_pos_left htp hc0 (by linarith)
        linarith
      have hid : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      have hT' : Tendsto (fun e => GenTrajectory.startTime F ζ (qf e) (cf e) M -
          (M : ℝ) * (16 * e)) (𝓝[>] 0)
          (𝓝 (GenTrajectory.startTime F ζ q₀ c M - (M : ℝ) * (16 * 0))) :=
        (tendsto_startTime F ζ hqf hcf hc0.ne' M).sub ((hid.const_mul 16).const_mul _)
      filter_upwards [hT'.eventually (lt_mem_nhds hlimit), hgood] with e he hG
      have hw := (hchF e hG).2.2.1
      rw [hG.2.2.1, hG.2.2.2] at hw
      exact le_trans he.le hw
  have hR : RealizesGraphTrajectory' fam g :=
    microscopic_realization window isCompact_window (window_regular Γ) g hEmem hinit' fam hconv
  have hconf : ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ t, 0 ≤ t → |(x e t).2 - uniRow ζ| < 2 * e := by
    filter_upwards [hgood] with e hG
    exact (hchF e hG).2.2.2
  have hU : UniformMicroscopicConvergence F ζ x p g :=
    ⟨fam, hproj, fun e => netParams_odeErr _, hconv, hR⟩
  exact ⟨g, ⟨rfl, hgcurve, hen, hEmem⟩, hTg, hconf, hU, compactConvergence_of_realizes hTg hU⟩

/-- **The uniform universal reversible realization theorem** (Proposition IX.11).

For every finite metric graph `Γ` with the zero potential and every routing law `F`, the network
`uniPot F ε` — one smooth potential for each scale `ε`, defined from `(Γ, F)` alone, together with
the fixed corridor heights `uniRow` and charts `uniChart` — has the following properties.

1. `uniPot F ε` is `C^∞`.
2. From every state in the tube of a corridor with energy below the wall height `4` there is a
   trajectory of `H_ε = ½|p|² + uniPot F ε` on `[0, ∞)`.
3. For **every** well-prepared graph state `x₀` with energy in `K⋆ = [1/2, 2]`, **every** horizon
   `T` and **every** family of prepared microscopic initial data converging to `x₀`: trajectories
   from these data exist for all small `ε`, and for **every** family of such trajectories, the
   trajectories stay in the tube of the corridor of the initial germ, and their projections
   converge to the graph trajectory `g` of `x₀` on `[0, T]`, at the level of thin-network chains
   (`UniformMicroscopicConvergence`) and uniformly on every compact subset of `[0, T]` containing
   no impact time (`CompactConvergence`).

The network does not depend on `x₀` or `T`.  A circle component of the resolved space `R(Γ, F)`
is an infinite corridor without longitudinal potential; an interval component is the corridor
between its two fixed ends of `F`, closed by caps. -/
theorem universal_reversible_realization_uniform (Γ : FiniteMetricGraph) (F : RoutingLaw Γ) :
    (∀ ε, ContDiff ℝ (⊤ : ℕ∞) (uniPot F ε)) ∧
    (∀ ε, 0 < ε → ε ≤ 1 / 8 → ∀ (ζ : Γ.EdgeEnd) (y q : ℝ × ℝ),
      |y.2 - uniRow ζ| < 2 * ε → hamEnergy (uniPot F ε) y q < 4 →
      ∃ x' p' : ℝ → ℝ × ℝ, x' 0 = y ∧ p' 0 = q ∧ IsHamiltonianTrajectory (uniPot F ε) x' p') ∧
    ∀ (x₀ : WellPreparedState Γ) (T : ℝ) (z : ℝ → (ℝ × ℝ) × (ℝ × ℝ)),
      IsPreparedFamily F x₀ z →
      (∃ x p : ℝ → ℝ → ℝ × ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        IsHamiltonianTrajectory (uniPot F ε) (x ε) (p ε) ∧ x ε 0 = (z ε).1 ∧
          p ε 0 = (z ε).2) ∧
      ∀ x p : ℝ → ℝ → ℝ × ℝ,
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsHamiltonianTrajectory (uniPot F ε) (x ε) (p ε)) →
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), x ε 0 = (z ε).1 ∧ p ε 0 = (z ε).2) →
        ∃ g : GraphTrajectory (zeroPotential Γ) F,
          (g.germ 0 = x₀.germ ∧ g.curve 0 0 = (x₀.q₀, EdgeEnd.sign Γ x₀.germ * x₀.c) ∧
            g.energy = x₀.c ^ 2 / 2 ∧ g.energy ∈ window) ∧
          T < g.stop g.N ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t, 0 ≤ t → |(x ε t).2 - uniRow x₀.germ| < 2 * ε) ∧
          UniformMicroscopicConvergence F x₀.germ x p g ∧
          CompactConvergence F x₀.germ x p g T :=
  ⟨fun ε => contDiff_uniPot F ε,
    fun _ hε hεs ζ y q htube hE => exists_uniTrajectory F hε hεs ζ y q htube hE,
    fun x₀ T _ hz => ⟨hz.exists_trajectories,
      fun _ _ hsol hinit => uniPot_realization_of_prepared Γ F x₀ T hz hsol hinit⟩⟩

end HamiltonianMetricGraphs
