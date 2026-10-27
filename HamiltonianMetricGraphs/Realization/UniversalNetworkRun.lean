/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalNetworkDynamics

/-!
# Runs of the uniform network

A trajectory of the uniform network `uniPot F ε`, started in the corridor of `ζ`, is turned into a
projected hybrid chain whose flights are the images of the trajectory under the **fixed** charts
`uniChart F ζ j`.  The bookkeeping of the existing run `NetRun` is reused; only the layout changes.

* **Interval components.**  The corridor of `ζ` is the interval between the two fold positions; it
  is the same for every number `M` of flights (`foldCorridor`).  The longitudinal motion of the
  trajectory is an exact corridor solution on every time window, so it *is* the run.
* **Circle components.**  The corridor of `ζ` is infinite and has no caps.  The longitudinal motion
  is free for all time (`uni_free_of_not_fold`).  The chain bookkeeping of a run with `M` flights
  only looks at the flight windows, and there the free motion coincides with the motion of any
  solution of a capped bookkeeping corridor whose caps lie beyond the last flight
  (`circleCorridor`); the chain is therefore the projection of the actual trajectory.  The caps of
  that bookkeeping corridor are not part of the network: they only serve to reuse `NetRun`.

In both cases the identification of flight `j` with its edge is the fixed chart
`chartAt F ζ (corridorLow F ζ) j` (`NetRun.chain_curve_eq_chartAt`).
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph MechanicalPotential

variable {Γ : FiniteMetricGraph}

/-! ### The fixed corridors as run layouts -/

/-- The corridor of an interval component, valid for every number `M` of flights: the interval
between the two fold positions. -/
noncomputable def foldCorridor (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (h : ∃ k, IsFold F ζ k)
    (M : ℕ) : Corridor F ζ M where
  low := corridorLow F ζ
  high := corridorHigh F ζ
  margin := minLen Γ ζ.1
  margin_pos := minLen_pos Γ ζ.1
  margin_le := fun e => minLen_le Γ ζ.1 e
  low_nonpos := by rw [corridorLow_of_fold F ζ h]; exact (foldPair_spec F ζ h).low_nonpos
  mem := fun j _ => by
    rw [corridorLow_of_fold F ζ h, corridorHigh_of_fold F ζ h]
    exact (foldPair_spec F ζ h).vpos_mem j
  cap := by
    intro j _ hj
    have hfd := foldPair_spec F ζ h
    rw [corridorLow_of_fold F ζ h, corridorHigh_of_fold F ζ h]
    obtain ⟨s, rfl⟩ := hfd.isFold_iff.mp hj
    have hd := hfd.dirSign_fold s
    have hv := hfd.vpos_fold s
    by_cases hev : Even s
    · rw [if_pos hev] at hd hv
      exact Or.inl ⟨hd, hv⟩
    · rw [if_neg hev] at hd hv
      exact Or.inr ⟨hd, hv⟩
  interior := fun j _ hj => by
    have hfd := foldPair_spec F ζ h
    rw [corridorLow_of_fold F ζ h, corridorHigh_of_fold F ζ h]
    exact ⟨(hfd.interior_margin hj).1, (hfd.interior_margin hj).2⟩

@[simp] theorem foldCorridor_low (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (h : ∃ k, IsFold F ζ k)
    (M : ℕ) : (foldCorridor F ζ h M).low = corridorLow F ζ := rfl

theorem clen_foldCorridor (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (h : ∃ k, IsFold F ζ k) (M : ℕ) :
    clen (foldCorridor F ζ h M) = corridorLen F ζ := rfl

/-- The bookkeeping corridor of a circle component for `M` flights: its origin is the fixed origin
`corridorLow F ζ` of the infinite corridor, its upper end lies beyond the last flight. -/
noncomputable def circleCorridor (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (h : ¬ ∃ k, IsFold F ζ k)
    (M : ℕ) : Corridor F ζ M :=
  have hf : ∀ k, ¬ IsFold F ζ k := fun k hk => h ⟨k, hk⟩
  have hdir : ∀ i : ℕ, dirSign F ζ i = 1 := fun i => dirSign_eq_one_of_no_fold fun l _ => hf l
  have hmono : ∀ {m n : ℕ}, m ≤ n → vpos F ζ m ≤ vpos F ζ n := fun hmn =>
    vpos_mono (a := 0) (fun i _ _ => hdir i) (by omega) hmn le_rfl
  have hmp := minLen_pos Γ ζ.1
  { low := corridorLow F ζ
    high := vpos F ζ (M + 2) + minLen Γ ζ.1
    margin := minLen Γ ζ.1
    margin_pos := hmp
    margin_le := fun e => minLen_le Γ ζ.1 e
    low_nonpos := by rw [corridorLow_of_not_fold F ζ h]; linarith
    mem := by
      intro j hj
      have h1 : vpos F ζ 0 ≤ vpos F ζ j := hmono (Nat.zero_le j)
      have h2 : vpos F ζ j ≤ vpos F ζ (M + 2) := hmono (by omega)
      rw [vpos_zero] at h1
      rw [corridorLow_of_not_fold F ζ h]
      exact ⟨by linarith, by linarith⟩
    cap := fun j _ hj => absurd hj (hf j)
    interior := by
      intro j hj _
      have h1 : vpos F ζ 0 ≤ vpos F ζ (j + 1) := hmono (Nat.zero_le _)
      have h2 : vpos F ζ (j + 1) ≤ vpos F ζ (M + 2) := hmono (by omega)
      rw [vpos_zero] at h1
      rw [corridorLow_of_not_fold F ζ h]
      exact ⟨by linarith, by linarith⟩ }

@[simp] theorem circleCorridor_low (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (h : ¬ ∃ k, IsFold F ζ k)
    (M : ℕ) : (circleCorridor F ζ h M).low = corridorLow F ζ := rfl

/-! ### The chain of a run is the image of the run under the fixed charts -/

/-- **The two ends of a flight determine the same chart.**  The affine identification used by the
run (from the start of the flight in the corridor to the start of the flight on the edge) is the
fixed chart `chartAt`, which only depends on the layout. -/
theorem gstart_sub_chartSign_mul_spos {F : RoutingLaw Γ} {η₀ : Γ.EdgeEnd} {M : ℕ}
    (C : Corridor F η₀ M) (q₀ ε : ℝ) (j : ℕ) :
    gstart F η₀ q₀ ε j - chartSign F η₀ j * spos C q₀ ε j =
      EdgeEnd.coordinate Γ (F.itinerary η₀ j) - chartSign F η₀ j * (vpos F η₀ (j + 1) - C.low) := by
  cases j with
  | zero =>
      have h1 := q₀_add_sign_travel (F := F) (η₀ := η₀) (q₀ := q₀)
      have hc1 : vpos F η₀ (0 + 1) - C.low = cpos C 1 := rfl
      rw [hc1, gstart_zero, spos_zero, chartSign, dirSign_zero,
        show F.itinerary η₀ 0 = η₀ from rfl]
      linarith
  | succ i =>
      have hd := dirSign_sq (F := F) (η₀ := η₀) (i + 1)
      have hc : vpos F η₀ (i + 1 + 1) - C.low = cpos C (i + 1) +
          dirSign F η₀ (i + 1) * edgeLen F η₀ (i + 1) := by
        rw [← cpos_succ]; rfl
      rw [hc, gstart_succ, spos_succ, chartSign]
      rcases hb : (F.itinerary η₀ (i + 1)).2 with _ | _
      · rw [sign_of_false hb, coordinate_of_false hb]
        linear_combination (8 * ε - edgeLen F η₀ (i + 1)) * hd
      · rw [sign_of_true hb, coordinate_of_true' hb,
          show Γ.length (F.itinerary η₀ (i + 1)).1 = edgeLen F η₀ (i + 1) from rfl]
        linear_combination (edgeLen F η₀ (i + 1) - 8 * ε) * hd

/-- **The projected chain of a run is the image of the run under the fixed charts.** -/
theorem NetRun.chain_curve_eq_chartAt (R : NetRun Γ) {j : ℕ} (hj : j ≤ R.M) {t : ℝ}
    (ht : t ∈ Icc (R.startT j) (R.stopT j)) :
    R.chain.curve j t = chartAt R.F R.η₀ R.C.low j (R.u t) (R.pu t) := by
  obtain ⟨h1, h2⟩ := R.chain_proj hj ht
  have hkey := gstart_sub_chartSign_mul_spos R.C R.q₀ R.ε j
  have horient : EdgeEnd.sign Γ (R.F.itinerary R.η₀ j) * R.sgn j = chartSign R.F R.η₀ j := rfl
  rw [horient] at h1 h2
  refine Prod.ext ?_ ?_
  · rw [R.chain_curve, h1, chartAt]
    have : R.startPos j = spos R.C R.q₀ R.ε j := rfl
    rw [this]
    linarith
  · rw [R.chain_curve, h2, chartAt]

/-! ### The package of a trajectory of the uniform network -/

/-- **What a trajectory of the uniform network provides**: a projected hybrid chain with `M`
flights along the itinerary of `ζ`, whose flights are the images of the trajectory `(x, p)` under
the fixed charts `uniChart F ζ j`, and whose time window is long enough. -/
structure UniPackage (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (M : ℕ) (ε : ℝ)
    (x p : ℝ → ℝ × ℝ) where
  /-- the projected chain -/
  chain : HybridChain (zeroPotential Γ) F (netParams ε)
  card : chain.N = M
  edge : ∀ j, chain.edge j = (F.itinerary ζ j).1
  curve0 : chain.curve 0 0 = uniChart F ζ 0 (x 0).1 (p 0).1
  window : GenTrajectory.startTime F ζ (uniChart F ζ 0 (x 0).1 (p 0).1).1 (p 0).1 M -
    (M : ℝ) * (16 * ε) ≤ chain.stop chain.N
  proj : ∀ j ≤ chain.N, ∀ t ∈ Icc (chain.start j) (chain.stop j),
    chain.curve j t = uniChart F ζ j (x t).1 (p t).1

/-- The first chart in coordinates: the initial corridor coordinate of the graph state. -/
theorem uniChart_zero_fst_travel {F : RoutingLaw Γ} {ζ : Γ.EdgeEnd} {M : ℕ}
    (C : Corridor F ζ M) (hC : C.low = corridorLow F ζ) (u v : ℝ) :
    cpos C 1 - GenTrajectory.travel F ζ (uniChart F ζ 0 u v).1 0 = u := by
  have h1 := q₀_add_sign_travel (F := F) (η₀ := ζ) (q₀ := (uniChart F ζ 0 u v).1)
  have hsq := Γ.edgeEnd_sign_sq ζ
  have hq : (uniChart F ζ 0 u v).1 =
      EdgeEnd.coordinate Γ ζ + EdgeEnd.sign Γ ζ * (u - cpos C 1) := by
    rw [uniChart, chartAt, chartSign, dirSign_zero, mul_one, ← hC]
    rfl
  have h2 : EdgeEnd.sign Γ ζ * (u - cpos C 1 + GenTrajectory.travel F ζ
      (uniChart F ζ 0 u v).1 0) = 0 := by linear_combination h1 - hq
  rcases mul_eq_zero.mp h2 with h | h
  · rw [h] at hsq; norm_num at hsq
  · linarith

/-- The chart of the first flight maps the momentum `c` to the graph momentum towards `ζ`. -/
theorem uniChart_zero_snd (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (u v : ℝ) :
    (uniChart F ζ 0 u v).2 = EdgeEnd.sign Γ ζ * v := by
  rw [uniChart, chartAt, chartSign, dirSign_zero, mul_one]
  rfl

/-- **The package of an interval component.** -/
theorem exists_uniPackage_of_fold (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (h : ∃ k, IsFold F ζ k)
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) (hεs : ε ≤ 1 / 1000) (hεm : 1000 * ε ≤ minLen Γ ζ.1)
    {x p : ℝ → ℝ × ℝ} (hsol : IsHamiltonianTrajectory (uniPot F ε) x p)
    (hconf : ∀ t, 0 ≤ t → |(x t).2 - uniRow ζ| < 2 * ε)
    (hc1 : 1 ≤ (p 0).1) (hc2 : (p 0).1 ≤ 2)
    (hq1 : 8 * ε < (uniChart F ζ 0 (x 0).1 (p 0).1).1)
    (hq2 : (uniChart F ζ 0 (x 0).1 (p 0).1).1 < Γ.length ζ.1 - 8 * ε) :
    Nonempty (UniPackage F ζ M ε x p) := by
  set C := foldCorridor F ζ h M with hCdef
  set q := (uniChart F ζ 0 (x 0).1 (p 0).1).1 with hqdef
  set c := (p 0).1 with hcdef
  have hCm : 1000 * ε ≤ C.margin := hεm
  have hu0 : (x 0).1 = spos C q ε 0 := by
    rw [spos_zero]; exact (uniChart_zero_fst_travel C rfl _ _).symm
  have hu0mem : (x 0).1 ∈ Icc (8 * ε) (clen C - 8 * ε) := by
    rw [hu0]; exact spos_mem hε hCm hq1 hq2 (Nat.zero_le M)
  have hlen : 1000 * ε ≤ corridorLen F ζ := by
    rw [← clen_foldCorridor F ζ h M]; exact le_trans hCm (margin_le_clen C)
  have hT : (0 : ℝ) ≤ ((M : ℝ) + 1) * (clen C / c + 100 * ε) := by
    have := clen_pos C
    have : 0 < c := by linarith
    positivity
  have hsol' := uni_corridorSolution_of_fold F hε (by linarith) hsol ζ hconf h hlen hc1 hc2 hT
    rfl ⟨by linarith [hu0mem.1], by
      have := hu0mem.2; rw [clen_foldCorridor] at this; linarith⟩
  set R : NetRun Γ :=
    { F := F, η₀ := ζ, q₀ := q, c := c, ε := ε, M := M, C := C, u := fun s => (x s).1
      pu := fun s => (p s).1
      eps_pos := hε
      eps_margin := hCm
      c_ge := hc1
      c_le := hc2
      q_lb := hq1
      q_ub := hq2
      init_pos := hu0
      init_mom := rfl
      sol := hsol' } with hRdef
  refine ⟨{ chain := R.chain
            card := rfl
            edge := fun j => rfl
            curve0 := ?_
            window := ?_
            proj := ?_ }⟩
  · rw [R.chain_curve_zero_zero]
    exact Prod.ext rfl (uniChart_zero_snd F ζ _ _).symm
  · have h1 := R.startT_ge R.M le_rfl
    have h2 : R.startT R.M ≤ R.stopT R.M := (NetRun.startT_lt_stopT (R := R) le_rfl).le
    exact le_trans h1 h2
  · intro j hj t ht
    exact R.chain_curve_eq_chartAt hj ht

/-- In a circle corridor the start of every flight is reached by uniform motion. -/
theorem NetRun.startPos_eq_of_no_fold (R : NetRun Γ) (h : ∀ k, ¬ IsFold R.F R.η₀ k) (j : ℕ) :
    R.startPos j = R.startPos 0 + R.c * R.startT j := by
  have hc := NetRun.c_ne (R := R)
  induction j with
  | zero => rw [NetRun.startT_zero]; ring
  | succ i ih =>
      have hd : dirSign R.F R.η₀ i = 1 := dirSign_eq_one_of_no_fold fun l _ => h l
      have h1 : R.startPos (i + 1) = R.endPos i + R.sgn i * (16 * R.ε) :=
        spos_succ_of_not_fold (h i)
      have h2 := NetRun.endPos_sub_startPos (R := R) i
      have h3 := NetRun.startT_succ_of_not_fold (R := R) (h i)
      have hs : R.sgn i = 1 := hd
      rw [h1, h3]
      rw [hs] at h2 ⊢
      rw [ih] at h2
      rw [NetRun.arriveT_eq, mul_add, mul_add, mul_div_cancel₀ _ hc, mul_div_cancel₀ _ hc]
      linarith

/-- **The package of a circle component.** -/
theorem exists_uniPackage_of_not_fold (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd)
    (h : ¬ ∃ k, IsFold F ζ k) (M : ℕ) {ε : ℝ} (hε : 0 < ε) (hεs : ε ≤ 1 / 1000)
    (hεm : 1000 * ε ≤ minLen Γ ζ.1)
    {x p : ℝ → ℝ × ℝ} (hsol : IsHamiltonianTrajectory (uniPot F ε) x p)
    (hconf : ∀ t, 0 ≤ t → |(x t).2 - uniRow ζ| < 2 * ε)
    (hc1 : 1 ≤ (p 0).1) (hc2 : (p 0).1 ≤ 2)
    (hq1 : 8 * ε < (uniChart F ζ 0 (x 0).1 (p 0).1).1)
    (hq2 : (uniChart F ζ 0 (x 0).1 (p 0).1).1 < Γ.length ζ.1 - 8 * ε) :
    Nonempty (UniPackage F ζ M ε x p) := by
  set C := circleCorridor F ζ h M with hCdef
  set q := (uniChart F ζ 0 (x 0).1 (p 0).1).1 with hqdef
  set c := (p 0).1 with hcdef
  have hc0 : 0 < c := by linarith
  have hCm : 1000 * ε ≤ C.margin := hεm
  have hu0 : (x 0).1 = spos C q ε 0 := by
    rw [spos_zero]; exact (uniChart_zero_fst_travel C rfl _ _).symm
  have hu0mem : (x 0).1 ∈ Icc (8 * ε) (clen C - 8 * ε) := by
    rw [hu0]; exact spos_mem hε hCm hq1 hq2 (Nat.zero_le M)
  set Tmax : ℝ := ((M : ℝ) + 1) * (clen C / c + 100 * ε) with hTmax
  have hT : 0 ≤ Tmax := by
    have := clen_pos C
    positivity
  -- an auxiliary solution of the capped bookkeeping corridor with the same initial data
  obtain ⟨Rc, hRc0, hRc⟩ := exists_bound_deriv_corridorPot hε (clen C)
  obtain ⟨ub, pb, hub0, hpb0, hub, hpb⟩ :=
    exists_newton1D (contDiff_corridorPot ε (clen C) (n := 2)) hRc0 hRc (x 0).1 c hT
  have hlen : 1000 * ε ≤ clen C := le_trans hCm (margin_le_clen C)
  have hsolb : CorridorSolution ε (clen C) c Tmax ub pb := by
    refine corridorSolution_of_net (m := 1) (Λ := fun _ => clen C) (i := 0) hε hlen hc1 hc2 hT
      hub hpb ?_
    rw [hpb0, hub0, corridorPot_of_mem hε (by linarith [hu0mem.1]) (by linarith [hu0mem.2])]
    ring
  set R : NetRun Γ :=
    { F := F, η₀ := ζ, q₀ := q, c := c, ε := ε, M := M, C := C, u := ub, pu := pb,
      eps_pos := hε
      eps_margin := hCm
      c_ge := hc1
      c_le := hc2
      q_lb := hq1
      q_ub := hq2
      init_pos := by rw [hub0]; exact hu0
      init_mom := hpb0
      sol := hsolb } with hRdef
  have hnf : ∀ k, ¬ IsFold F ζ k := fun k hk => h ⟨k, hk⟩
  -- on the flight windows the auxiliary solution is the free motion of the actual trajectory
  have hagree : ∀ j ≤ M, ∀ t ∈ Icc (R.startT j) (R.stopT j),
      R.u t = (x t).1 ∧ R.pu t = (p t).1 := by
    intro j hj t ht
    have ht0 : 0 ≤ t := le_trans ((R.inv j hj).nonneg) ht.1
    obtain ⟨hpu, hxu⟩ := uni_free_of_not_fold F hε (by linarith) hsol ζ hconf h ht0
    obtain ⟨h1, h2⟩ := R.chain_flight hj ht
    have hs : R.sgn j = 1 := dirSign_eq_one_of_no_fold fun l _ => hnf l
    have hsp := R.startPos_eq_of_no_fold hnf j
    have hsp0 : R.startPos 0 = (x 0).1 := hu0.symm
    rw [hs] at h1 h2
    refine ⟨?_, ?_⟩
    · rw [h1, hxu, hsp, hsp0]
      change (x 0).1 + c * R.startT j + 1 * c * (t - R.startT j) = (x 0).1 + c * t
      ring
    · rw [h2, hpu]
      change 1 * c = c
      ring
  refine ⟨{ chain := R.chain
            card := rfl
            edge := fun j => rfl
            curve0 := ?_
            window := ?_
            proj := ?_ }⟩
  · rw [R.chain_curve_zero_zero]
    exact Prod.ext rfl (uniChart_zero_snd F ζ _ _).symm
  · have h1 := R.startT_ge R.M le_rfl
    have h2 : R.startT R.M ≤ R.stopT R.M := (NetRun.startT_lt_stopT (R := R) le_rfl).le
    exact le_trans h1 h2
  · intro j hj t ht
    rw [R.chain_curve_eq_chartAt hj ht, (hagree j hj t ht).1, (hagree j hj t ht).2]
    rfl

/-- **The package of a trajectory of the uniform network**, in both cases. -/
theorem exists_uniPackage (F : RoutingLaw Γ) (ζ : Γ.EdgeEnd) (M : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hεs : ε ≤ 1 / 1000) (hεm : 1000 * ε ≤ minLen Γ ζ.1)
    {x p : ℝ → ℝ × ℝ} (hsol : IsHamiltonianTrajectory (uniPot F ε) x p)
    (hconf : ∀ t, 0 ≤ t → |(x t).2 - uniRow ζ| < 2 * ε)
    (hc1 : 1 ≤ (p 0).1) (hc2 : (p 0).1 ≤ 2)
    (hq1 : 8 * ε < (uniChart F ζ 0 (x 0).1 (p 0).1).1)
    (hq2 : (uniChart F ζ 0 (x 0).1 (p 0).1).1 < Γ.length ζ.1 - 8 * ε) :
    Nonempty (UniPackage F ζ M ε x p) := by
  by_cases h : ∃ k, IsFold F ζ k
  · exact exists_uniPackage_of_fold F ζ h M hε hεs hεm hsol hconf hc1 hc2 hq1 hq2
  · exact exists_uniPackage_of_not_fold F ζ h M hε hεs hεm hsol hconf hc1 hc2 hq1 hq2

end HamiltonianMetricGraphs
