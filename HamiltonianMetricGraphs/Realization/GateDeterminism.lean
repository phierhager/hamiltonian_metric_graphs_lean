/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.GateLimit
import HamiltonianMetricGraphs.Realization.StarDeterminism
import HamiltonianMetricGraphs.Realization.ChannelKernel

/-!
# Deterministic channel reduction for the gated junction, in both regimes

`GateJunction.lean` shows that *some* passage through `F(η)` exists.  This file proves the stronger
statement `HasDeterministicChannelReduction`: within the junction window the particle can reach
**no other** junction boundary, whatever the unresolved transverse data of the incoming state.
Since the incoming trajectory in these statements is arbitrary — only its projected graph state is
constrained — the outgoing channel is shown to be independent of the transverse data, which is the
microscopic meaning of the determinism of the two limiting routing laws.

The three ingredients are all consequences of the gated Hamiltonian flow:

* `GateSolution.same_sign` — **below the gate the particle never changes side.**  Its longitudinal
  energy is below the gate height, so `ε < |u(t)|` for *all* times (`abs_gt_of_low`); the
  intermediate value theorem then forbids a sign change.  This is what excludes the opposite
  through channel at low energy.
* `GateSolution.mom_le_of_high` / `mom_ge_of_high` — **above the gate the longitudinal momentum
  never changes sign** inside the closed edge, and its modulus stays `≥ 2/5` (a crude bound,
  from `G_ε ≤ 2g₀`, suffices here).  Hence the
  longitudinal coordinate is strictly monotone across the whole junction window and the particle
  cannot return to the boundary it entered through.
* the travel bound `|Δq| ≤ 2 · dwell = 64ε`, which excludes the far boundary of any edge
  (`1 - 16ε > 64ε` for `ε < 1/100`; the paper's "within `32ε` the longitudinal coordinate changes
  by at most `64ε < 1 - 16ε`").
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {ε S : ℝ} {K : Set ℝ}

/-! ### Two dynamical facts about the gated longitudinal system -/

namespace GateSolution

variable {c Tmax : ℝ} {u pu : ℝ → ℝ}

/-- **Below the gate the particle never changes side.**  The gate is higher than the longitudinal
energy across the whole core `|u| ≤ ε`, so `u` never vanishes; by the intermediate value theorem
its sign is constant. -/
theorem same_sign (G : GateSolution ε c Tmax u pu) (hlow : c ^ 2 / 2 < gateHeight)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) Tmax) (ht : t ∈ Icc (0 : ℝ) Tmax) : 0 < u s * u t := by
  have hε := G.eps_pos
  have hns : ε < |u s| := G.abs_gt_of_low hlow hs
  have hnt : ε < |u t| := G.abs_gt_of_low hlow ht
  have hns0 : u s ≠ 0 := by
    intro h; rw [h, abs_zero] at hns; linarith
  have hnt0 : u t ≠ 0 := by
    intro h; rw [h, abs_zero] at hnt; linarith
  by_contra hcon
  rw [not_lt] at hcon
  -- a sign change forces a zero of `u`, which the gate forbids
  have hsub : uIcc s t ⊆ Icc (0 : ℝ) Tmax := uIcc_subset_Icc hs ht
  have hcont : ContinuousOn u (uIcc s t) := (G.continuousOn_pos).mono hsub
  have hmem : (0 : ℝ) ∈ uIcc (u s) (u t) := by
    rcases lt_or_gt_of_ne hns0 with h1 | h1
    · rcases lt_or_gt_of_ne hnt0 with h2 | h2
      · nlinarith
      · exact mem_uIcc.mpr (Or.inl ⟨h1.le, h2.le⟩)
    · rcases lt_or_gt_of_ne hnt0 with h2 | h2
      · exact mem_uIcc.mpr (Or.inr ⟨h2.le, h1.le⟩)
      · nlinarith
  obtain ⟨r, hr, hval⟩ := intermediate_value_uIcc hcont hmem
  have hzero : u r = 0 := hval
  have := G.abs_gt_of_low hlow (hsub hr)
  rw [hzero, abs_zero] at this
  linarith

/-- **Above the gate the speed never drops below `2/5`** inside the closed edge: the gate is at
most `2 · gateHeight = 7/5` high while the energy is at least `3/2`. -/
theorem sq_mom_ge_of_high (G : GateSolution ε c Tmax u pu) (hhigh : 3 / 2 ≤ c ^ 2 / 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Tmax) (hu : |u t| ≤ 1) : (1 : ℝ) / 5 ≤ pu t ^ 2 := by
  have hε := G.eps_pos
  have hen := G.energy t ht
  have hcap : capPot ε (u t) = 0 := capPot_of_abs_le_one hε hu
  have hg := gateBump_le hε (u t)
  have hh : gateHeight = 7 / 10 := rfl
  rw [gatePot, hcap, zero_add] at hen
  rw [hh] at hg
  linarith

/-- Above the gate an incoming momentum stays negative, with modulus at least `2/5`. -/
theorem mom_le_of_high (G : GateSolution ε c Tmax u pu) (hhigh : 3 / 2 ≤ c ^ 2 / 2) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (_ : a ≤ b)
    (hbound : ∀ t ∈ Icc a b, |u t| ≤ 1) (hpa : pu a < 0) :
    ∀ t ∈ Icc a b, pu t ≤ -(2 / 5) := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha.1 hb.2
  intro t ht
  by_contra hcon
  rw [not_le] at hcon
  have hsq := G.sq_mom_ge_of_high hhigh (hsub ht) (hbound t ht)
  have hpos : (0 : ℝ) < pu t := by nlinarith
  have hcontp : ContinuousOn pu (Icc a t) :=
    (G.continuousOn_mom).mono ((Icc_subset_Icc le_rfl ht.2).trans hsub)
  obtain ⟨s, hs, hval⟩ := intermediate_value_Icc ht.1 hcontp
    (show (0 : ℝ) ∈ Icc (pu a) (pu t) from ⟨hpa.le, hpos.le⟩)
  have hval' : pu s = 0 := hval
  have hsmem : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
  have := G.sq_mom_ge_of_high hhigh (hsub hsmem) (hbound s hsmem)
  rw [hval'] at this
  norm_num at this

/-- Above the gate an outgoing momentum stays positive, with modulus at least `2/5`. -/
theorem mom_ge_of_high (G : GateSolution ε c Tmax u pu) (hhigh : 3 / 2 ≤ c ^ 2 / 2) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Tmax) (hb : b ∈ Icc (0 : ℝ) Tmax) (_ : a ≤ b)
    (hbound : ∀ t ∈ Icc a b, |u t| ≤ 1) (hpa : 0 < pu a) :
    ∀ t ∈ Icc a b, (2 : ℝ) / 5 ≤ pu t := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) Tmax := Icc_subset_Icc ha.1 hb.2
  intro t ht
  by_contra hcon
  rw [not_le] at hcon
  have hsq := G.sq_mom_ge_of_high hhigh (hsub ht) (hbound t ht)
  have hneg : pu t < 0 := by nlinarith
  have hcontp : ContinuousOn pu (Icc a t) :=
    (G.continuousOn_mom).mono ((Icc_subset_Icc le_rfl ht.2).trans hsub)
  obtain ⟨s, hs, hval⟩ := intermediate_value_Icc' ht.1 hcontp
    (show (0 : ℝ) ∈ Icc (pu t) (pu a) from ⟨hneg.le, hpa.le⟩)
  have hval' : pu s = 0 := hval
  have hsmem : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
  have := G.sq_mom_ge_of_high hhigh (hsub hsmem) (hbound s hsmem)
  rw [hval'] at this
  norm_num at this

end GateSolution

/-! ### Extracting a departing state -/

theorem gate_dep_boundary (hε : 0 < ε) {ζ : starGraph.EdgeEnd} {x p : ℝ × ℝ}
    (h : gateNetwork.Departing (zeroPotential starGraph) K ε ζ x p) :
    longComp ζ.1 x = starTarget ε ζ := by
  have h1 := h.boundary
  rw [gateNetwork_long, gateNetwork_offset_of_pos hε] at h1
  exact h1

theorem gate_dep_trans (hε : 0 < ε) {ζ : starGraph.EdgeEnd} {x p : ℝ × ℝ}
    (h : gateNetwork.Departing (zeroPotential starGraph) K ε ζ x p) :
    |transComp ζ.1 x| ≤ 2 * ε := by
  have h1 := gate_prep_trans hε h.prepared
  simpa using h1

/-! ### The channels are geometrically separated -/

/-- **The three channels of the gated network are microscopically separated.**  This is the same
purely geometric statement as for the ungated model: the arm mouth sits at `w = 8ε` while the
through tube has width `2ε`, and the two halves of the through channel lie on opposite sides of the
origin. -/
theorem gateNetwork_channelsSeparated :
    gateNetwork.ChannelsSeparated (zeroPotential starGraph) K (1 / 100) := by
  intro ε hε ζ ζ' x p h1 h2
  have hε0 : 0 < ε := hε.1
  have hεs : ε ≤ 1 / 100 := le_of_lt hε.2
  have hx1 := gate_dep_boundary hε0 h1
  have hx2 := gate_dep_boundary hε0 h2
  have ht1 := gate_dep_trans hε0 h1
  have ht2 := gate_dep_trans hε0 h2
  have hQ1 := starTarget_mem hε0 (by linarith) ζ
  have hQ2 := starTarget_mem hε0 (by linarith) ζ'
  have hedge : ζ.1 = ζ'.1 := by
    by_cases hz : ζ.1 = 2
    · by_cases hz' : ζ'.1 = 2
      · rw [hz, hz']
      · exfalso
        rw [hz, longComp_two] at hx1
        rw [transComp_of_ne_two hz'] at ht2
        have := (abs_le.mp ht2).2
        linarith [hQ1.1, hx1]
    · by_cases hz' : ζ'.1 = 2
      · exfalso
        rw [hz', longComp_two] at hx2
        rw [transComp_of_ne_two hz] at ht1
        have := (abs_le.mp ht1).2
        linarith [hQ2.1, hx2]
      · by_contra hne
        rw [longComp_of_ne_two hz] at hx1
        rw [longComp_of_ne_two hz', embedSign_ne hz hz' (fun h => hne h.symm)] at hx2
        linarith [hQ1.1, hQ2.1]
  refine Prod.ext hedge ?_
  refine starTarget_snd_eq hε0 (by linarith) ?_
  rw [← hx1, ← hx2, hedge]

/-! ### The exit channel is unique -/

variable {Θ : gateNetwork.MicroTrajectory ε S}

/-- The travel bound over the junction window of the gated model. -/
theorem gate_through_travel (hε : 0 < ε) {c : ℝ} (hth : GateThrough ε c S Θ)
    {η : starGraph.EdgeEnd} (hne : η.1 ≠ 2) {a b' : ℝ} (ha : 0 ≤ a) (haS : a + 32 * ε ≤ S)
    (hb'1 : a ≤ b') (hb'2 : b' ≤ a + 32 * ε) :
    |longComp η.1 (Θ.x b') - longComp η.1 (Θ.x a)| ≤ 64 * ε := by
  have hc1 : 1 ≤ c := hth.gate.c_ge
  have hc2 : c ≤ 2 := hth.gate.c_le
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hb'mem : b' ∈ Icc (0 : ℝ) S := ⟨by linarith, by linarith⟩
  have h0 := hth.gate.travel_le hamem hb'mem hb'1
  have h1 : c * (b' - a) ≤ 64 * ε := by nlinarith
  have h2 : longComp η.1 (Θ.x b') - longComp η.1 (Θ.x a)
      = ThroughRun.embedSign η.1 * ((Θ.x b').1 - (Θ.x a).1) := by
    rw [longComp_of_ne_two hne, longComp_of_ne_two hne]; ring
  rw [h2, abs_mul, abs_embedSign, one_mul]
  linarith

/-- **The outer reflection admits no other exit**, in either regime: the far boundary of the edge
is `1 - 16ε` away, further than the window allows, and the opposite through channel is on the other
side of the origin. -/
theorem gate_through_exit_unique_outer (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {c : ℝ}
    (hth : GateThrough ε c S Θ) {η ζ : starGraph.EdgeEnd} (hne : η.1 ≠ 2) (hζne : ζ.1 ≠ 2)
    (hb2 : η.2 = true) {a b' : ℝ} (ha : 0 ≤ a) (haS : a + 32 * ε ≤ S) (hb'1 : a < b')
    (hb'2 : b' ≤ a + 32 * ε)
    (hxa : longComp η.1 (Θ.x a) = starTarget ε η)
    (hxb : longComp ζ.1 (Θ.x b') = starTarget ε ζ) :
    ζ = η := by
  have hsq : ThroughRun.embedSign η.1 * ThroughRun.embedSign η.1 = 1 := embedSign_sq η.1
  have htr := gate_through_travel hε hth hne ha haS hb'1.le hb'2
  rw [hxa, starTarget_of_true hb2] at htr
  obtain ⟨h1, h2⟩ := abs_le.mp htr
  have hUpos : 0 < longComp η.1 (Θ.x b') := by linarith
  by_cases hedge : ζ.1 = η.1
  · have hU : longComp η.1 (Θ.x b') = starTarget ε ζ := by
      rw [longComp_of_ne_two hζne, hedge] at hxb
      rw [longComp_of_ne_two hne]
      exact hxb
    rcases hb : ζ.2 with _ | _
    · exfalso
      rw [starTarget_of_false hb] at hU
      linarith
    · exact Prod.ext hedge (by rw [hb, hb2])
  · exfalso
    have hζs : ThroughRun.embedSign ζ.1 = -ThroughRun.embedSign η.1 :=
      embedSign_ne hne hζne hedge
    have hU : -longComp η.1 (Θ.x b') = starTarget ε ζ := by
      rw [longComp_of_ne_two hζne, hζs] at hxb
      rw [longComp_of_ne_two hne]
      linarith
    have := (starTarget_mem hε (by linarith) ζ).1
    linarith

/-- **Below the gate the through channel admits no other exit.**  The particle never changes side,
so the opposite through channel is unreachable; and the far boundary of its own edge is further
than the window allows. -/
theorem gate_through_exit_unique_low (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {c : ℝ}
    (hth : GateThrough ε c S Θ) (hlow : c ^ 2 / 2 < gateHeight)
    {η ζ : starGraph.EdgeEnd} (hne : η.1 ≠ 2) (hζne : ζ.1 ≠ 2) (hb2 : η.2 = false)
    {a b' : ℝ} (ha : 0 ≤ a) (haS : a + 32 * ε ≤ S) (hb'1 : a < b') (hb'2 : b' ≤ a + 32 * ε)
    (hxa : longComp η.1 (Θ.x a) = starTarget ε η)
    (hxb : longComp ζ.1 (Θ.x b') = starTarget ε ζ) :
    ζ = η := by
  have hsq : ThroughRun.embedSign η.1 * ThroughRun.embedSign η.1 = 1 := embedSign_sq η.1
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hb'mem : b' ∈ Icc (0 : ℝ) S := ⟨by linarith, by linarith⟩
  -- the particle stays on the side it entered from
  have hsame := hth.gate.same_sign hlow hamem hb'mem
  have hUa : longComp η.1 (Θ.x a) = 8 * ε := by rw [hxa, starTarget_of_false hb2]
  have hprod : longComp η.1 (Θ.x a) * longComp η.1 (Θ.x b') = (Θ.x a).1 * (Θ.x b').1 := by
    rw [longComp_of_ne_two hne, longComp_of_ne_two hne]
    nlinarith [hsq]
  have hUpos : 0 < longComp η.1 (Θ.x b') := by
    have h := hsame
    rw [← hprod, hUa] at h
    nlinarith
  have htr := gate_through_travel hε hth hne ha haS hb'1.le hb'2
  rw [hUa] at htr
  obtain ⟨h1, h2⟩ := abs_le.mp htr
  by_cases hedge : ζ.1 = η.1
  · have hU : longComp η.1 (Θ.x b') = starTarget ε ζ := by
      rw [longComp_of_ne_two hζne, hedge] at hxb
      rw [longComp_of_ne_two hne]
      exact hxb
    rcases hb : ζ.2 with _ | _
    · exact Prod.ext hedge (by rw [hb, hb2])
    · exfalso
      rw [starTarget_of_true hb] at hU
      linarith
  · exfalso
    have hζs : ThroughRun.embedSign ζ.1 = -ThroughRun.embedSign η.1 :=
      embedSign_ne hne hζne hedge
    have hU : -longComp η.1 (Θ.x b') = starTarget ε ζ := by
      rw [longComp_of_ne_two hζne, hζs] at hxb
      rw [longComp_of_ne_two hne]
      linarith
    have := (starTarget_mem hε (by linarith) ζ).1
    linarith

set_option maxHeartbeats 1000000 in
-- a four-way case split over the germ types of the opposite through channel
/-- **Above the gate the through channel admits no other exit.**  The longitudinal momentum keeps
its sign throughout the junction window, so the coordinate is strictly monotone and the particle can
neither return to its entrance boundary nor reach the far end of either edge. -/
theorem gate_through_exit_unique_high (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {c : ℝ}
    (hth : GateThrough ε c S Θ) (hhigh : 3 / 2 ≤ c ^ 2 / 2)
    {η ζ : starGraph.EdgeEnd} (hne : η.1 ≠ 2) (hζne : ζ.1 ≠ 2) (hb2 : η.2 = false)
    {a b' : ℝ} (ha : 0 ≤ a) (haS : a + 32 * ε ≤ S) (hb'1 : a < b') (hb'2 : b' ≤ a + 32 * ε)
    (hxa : longComp η.1 (Θ.x a) = starTarget ε η)
    (hpa : longComp η.1 (Θ.p a) = EdgeEnd.sign starGraph η * c)
    (hxb : longComp ζ.1 (Θ.x b') = starTarget ε ζ) :
    ζ = starRouting.routeGerm η := by
  have hc1 : 1 ≤ c := hth.gate.c_ge
  have hc2 : c ≤ 2 := hth.gate.c_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hsq : ThroughRun.embedSign η.1 * ThroughRun.embedSign η.1 = 1 := embedSign_sq η.1
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hbmem : a + 32 * ε ∈ Icc (0 : ℝ) S := ⟨by linarith, haS⟩
  have hb'mem : b' ∈ Icc (0 : ℝ) S := ⟨by linarith, by linarith⟩
  have hUa : longComp η.1 (Θ.x a) = 8 * ε := by rw [hxa, starTarget_of_false hb2]
  have hua : (Θ.x a).1 = ThroughRun.embedSign η.1 * (8 * ε) := by
    rw [fst_eq_of_longComp hne, hUa]
  have hpua : (Θ.p a).1 = -(ThroughRun.embedSign η.1 * c) := by
    rw [fst_eq_of_longComp hne, hpa, sign_of_false hb2]; ring
  -- the whole window stays inside the closed edge
  have hbound : ∀ t ∈ Icc a (a + 32 * ε), |(Θ.x t).1| ≤ 1 := by
    intro t ht
    have hsub : Icc a (a + 32 * ε) ⊆ Icc (0 : ℝ) S := Icc_subset_Icc ha haS
    have h0 := hth.gate.travel_le hamem (hsub ht) ht.1
    have h1 : c * (t - a) ≤ 64 * ε := by nlinarith [ht.1, ht.2]
    have h2 := abs_le.mp h0
    have h3 : |(Θ.x a).1| = 8 * ε := by
      rw [hua, abs_mul, abs_embedSign, one_mul, abs_of_nonneg (by linarith)]
    have h4 := abs_le.mp (le_of_eq h3)
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2, h4.1, h4.2]
  -- the longitudinal coordinate is strictly decreasing in the germ orientation
  have hmono : longComp η.1 (Θ.x b') < longComp η.1 (Θ.x a) := by
    have hbsub : Icc a b' ⊆ Icc a (a + 32 * ε) := Icc_subset_Icc le_rfl hb'2
    have hbound' : ∀ t ∈ Icc a b', |(Θ.x t).1| ≤ 1 := fun t ht => hbound t (hbsub ht)
    have hderiv : ∀ t ∈ Icc a b', HasDerivWithinAt (fun s => longComp η.1 (Θ.x s))
        (longComp η.1 (Θ.p t)) (Icc a b') t := by
      intro t ht
      have hsub : Icc a b' ⊆ Icc (0 : ℝ) S := Icc_subset_Icc ha (by linarith [hb'2])
      have h := (hth.gate.ode_pos t (hsub ht)).mono hsub
      have h2 := h.const_mul (ThroughRun.embedSign η.1)
      rw [longComp_of_ne_two hne (Θ.p t)]
      exact h2.congr (fun s _ => longComp_of_ne_two hne (Θ.x s))
        (longComp_of_ne_two hne (Θ.x t))
    rcases embedSign_eq_or η.1 with hs | hs
    · -- the entering momentum is negative in the plane coordinate
      have hpneg : (Θ.p a).1 < 0 := by rw [hpua, hs]; linarith
      have hmomneg := hth.gate.mom_le_of_high hhigh hamem hb'mem hb'1.le hbound' hpneg
      have hle : ∀ t ∈ Icc a b', longComp η.1 (Θ.p t) ≤ -(2 / 5) := by
        intro t ht
        rw [longComp_of_ne_two hne, hs, one_mul]
        exact hmomneg t ht
      have h := image_sub_le_mul_sub_of_hasDerivWithinAt_le'
        (f := fun s => longComp η.1 (Θ.x s)) (f' := fun s => longComp η.1 (Θ.p s))
        (C := -(2 / 5)) hderiv hle (left_mem_Icc.mpr hb'1.le) (right_mem_Icc.mpr hb'1.le) hb'1.le
      nlinarith [hb'1]
    · have hppos : 0 < (Θ.p a).1 := by rw [hpua, hs]; linarith
      have hmompos := hth.gate.mom_ge_of_high hhigh hamem hb'mem hb'1.le hbound' hppos
      have hle : ∀ t ∈ Icc a b', longComp η.1 (Θ.p t) ≤ -(2 / 5) := by
        intro t ht
        rw [longComp_of_ne_two hne, hs]
        have := hmompos t ht
        linarith
      have h := image_sub_le_mul_sub_of_hasDerivWithinAt_le'
        (f := fun s => longComp η.1 (Θ.x s)) (f' := fun s => longComp η.1 (Θ.p s))
        (C := -(2 / 5)) hderiv hle (left_mem_Icc.mpr hb'1.le) (right_mem_Icc.mpr hb'1.le) hb'1.le
      nlinarith [hb'1]
  have htr := gate_through_travel hε hth hne ha haS hb'1.le hb'2
  rw [hUa] at htr
  obtain ⟨h1, h2⟩ := abs_le.mp htr
  rw [hUa] at hmono
  by_cases hedge : ζ.1 = η.1
  · exfalso
    have hU : longComp η.1 (Θ.x b') = starTarget ε ζ := by
      rw [longComp_of_ne_two hζne, hedge] at hxb
      rw [longComp_of_ne_two hne]
      exact hxb
    rcases hb : ζ.2 with _ | _
    · rw [starTarget_of_false hb] at hU; linarith
    · rw [starTarget_of_true hb] at hU; linarith
  · have hζs : ThroughRun.embedSign ζ.1 = -ThroughRun.embedSign η.1 :=
      embedSign_ne hne hζne hedge
    have hU : -longComp η.1 (Θ.x b') = starTarget ε ζ := by
      rw [longComp_of_ne_two hζne, hζs] at hxb
      rw [longComp_of_ne_two hne]
      linarith
    have hswap : ζ.1 = swapEdge η.1 := eq_swapEdge_of_ne hne hζne hedge
    rcases hb : ζ.2 with _ | _
    · rw [starRouteGerm_of_false hb2]
      exact Prod.ext hswap (by rw [hb])
    · exfalso
      rw [starTarget_of_true hb] at hU
      linarith

/-- **The third arm admits no other exit**, in either regime. -/
theorem gate_arm_exit_unique (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {c : ℝ}
    (harm : GateArm ε c S Θ) {η ζ : starGraph.EdgeEnd} (heq : η.1 = 2) (hζeq : ζ.1 = 2)
    {a b' : ℝ} (ha : 0 ≤ a) (haS : a + 32 * ε ≤ S) (hb'1 : a < b') (hb'2 : b' ≤ a + 32 * ε)
    (hxa : longComp η.1 (Θ.x a) = starTarget ε η)
    (hxb : longComp ζ.1 (Θ.x b') = starTarget ε ζ) :
    ζ = η := by
  have hc1 : 1 ≤ c := harm.arm.c_ge
  have hc2 : c ≤ 2 := harm.arm.c_le
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hb'mem : b' ∈ Icc (0 : ℝ) S := ⟨by linarith, by linarith⟩
  rw [heq, longComp_two] at hxa
  rw [hζeq, longComp_two] at hxb
  have htravel0 : |(Θ.x b').2 - (Θ.x a).2| ≤ c * (b' - a) :=
    harm.arm.travel_le hamem hb'mem hb'1.le
  have htravel : |starTarget ε ζ - starTarget ε η| ≤ 64 * ε := by
    rw [← hxa, ← hxb]
    have h1 : c * (b' - a) ≤ 64 * ε := by nlinarith [hb'1.le, hb'2]
    linarith
  obtain ⟨h1, h2⟩ := abs_le.mp htravel
  have hsnd : ζ.2 = η.2 := by
    rcases hb : η.2 with _ | _ <;> rcases hb2 : ζ.2 with _ | _
    · rfl
    · exfalso
      rw [starTarget_of_false hb, starTarget_of_true hb2] at h1 h2; linarith
    · exfalso
      rw [starTarget_of_true hb, starTarget_of_false hb2] at h1 h2; linarith
    · rfl
  exact Prod.ext (by rw [hζeq, heq]) hsnd

/-! ### Deterministic channel reduction in the two regimes -/

/-- **Below the gate the junction has deterministic channel reduction.**  Whatever the unresolved
transverse data of the incoming state, the particle leaves through the germ it came from and
through no other. -/
theorem gateNetwork_hasDeterministicChannelReduction_low :
    gateNetwork.HasDeterministicChannelReduction (zeroPotential starGraph) windowLow
      gateRoutingLow (1 / 100) := by
  refine ⟨gateNetwork_junctionScattering_low, ?_⟩
  intro ε hε η x p harr₀ b' hb' ζ hdep
  have hε0 : 0 < ε := hε.1
  have hεs : ε ≤ 1 / 100 := le_of_lt hε.2
  have hKw := windowLow_subset
  -- the flow through `(x, p)` on `[0, 1]`, which contains the junction window `[0, 32ε]`
  set Θ := gateNetwork.flowTraj ε (x, p) 1 with hΘ
  have harr : gateNetwork.Arriving (zeroPotential starGraph) windowLow ε η (Θ.x 0) (Θ.p 0) := by
    rw [hΘ, ThinHamiltonianNetwork.flowTraj_x_zero, ThinHamiltonianNetwork.flowTraj_p_zero]
    exact harr₀
  change gateNetwork.Departing (zeroPotential starGraph) windowLow ε ζ (Θ.x b') (Θ.p b') at hdep
  have hS : (0 : ℝ) ≤ 1 := by norm_num
  have haS : (0 : ℝ) + 32 * ε ≤ 1 := by linarith
  have hb'1 : (0 : ℝ) < b' := hb'.1
  have hb'2 : b' ≤ 0 + 32 * ε := by
    have := hb'.2
    rw [gateNetwork_dwell_of_pos hε0] at this
    linarith
  have hxa := gate_arriving_boundary hε0 harr
  have hxb := gate_dep_boundary hε0 hdep
  have hdepprep : gateNetwork.Prepared (zeroPotential starGraph) windowLow ε
      (otherEnd ζ) (Θ.x b') (Θ.p b') := hdep.prepared
  have hb'mem : b' ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hζgoal : ζ = η → ζ = gateRoutingLow.toRoutingMap.routeGerm η := fun h => by rw [h]; rfl
  by_cases h2 : η.1 = 2
  · have harm := gate_arm Θ hε0 hεs hS hKw h2 harr.prepared
    have hζeq : ζ.1 = 2 := by
      have h := gate_arm_eq_two Θ harm hε0 hb'mem (η := otherEnd ζ) hdepprep
      simpa using h
    exact hζgoal (gate_arm_exit_unique hε0 hεs harm h2 hζeq le_rfl haS hb'1 hb'2 hxa hxb)
  · have hth := gate_through Θ hε0 hεs hS hKw h2 harr.prepared
    have hζne : ζ.1 ≠ 2 := by
      have h := gate_through_ne_two Θ hth hε0 hεs hb'mem (η := otherEnd ζ) hdepprep
      simpa using h
    rcases hb2 : η.2 with _ | _
    · -- an inner germ: the low-energy gate keeps the particle on its side
      have hlow : |(Θ.p 0).1| ^ 2 / 2 < gateHeight := by
        have hlongspeed : |longComp η.1 (Θ.p 0)| = |(Θ.p 0).1| := by
          rw [abs_longComp_of_ne_two h2]
        obtain ⟨-, hcK⟩ := gate_arr_mom hKw harr.prepared hlongspeed
        exact windowLow_lt_gateHeight hcK
      exact hζgoal (gate_through_exit_unique_low hε0 hεs hth hlow h2 hζne hb2 le_rfl haS hb'1
        hb'2 hxa hxb)
    · exact hζgoal (gate_through_exit_unique_outer hε0 hεs hth h2 hζne hb2 le_rfl haS hb'1 hb'2
        hxa hxb)

/-- **Above the gate the junction has deterministic channel reduction.**  Whatever the unresolved
transverse data of the incoming state, a particle arriving at the branching vertex along a through
channel leaves through the *opposite* one and through no other germ. -/
theorem gateNetwork_hasDeterministicChannelReduction_high :
    gateNetwork.HasDeterministicChannelReduction (zeroPotential starGraph) windowHigh
      gateRoutingHigh (1 / 100) := by
  refine ⟨gateNetwork_junctionScattering_high, ?_⟩
  intro ε hε η x p harr₀ b' hb' ζ hdep
  have hε0 : 0 < ε := hε.1
  have hεs : ε ≤ 1 / 100 := le_of_lt hε.2
  have hKw := windowHigh_subset
  -- the flow through `(x, p)` on `[0, 1]`, which contains the junction window `[0, 32ε]`
  set Θ := gateNetwork.flowTraj ε (x, p) 1 with hΘ
  have harr : gateNetwork.Arriving (zeroPotential starGraph) windowHigh ε η (Θ.x 0) (Θ.p 0) := by
    rw [hΘ, ThinHamiltonianNetwork.flowTraj_x_zero, ThinHamiltonianNetwork.flowTraj_p_zero]
    exact harr₀
  change gateNetwork.Departing (zeroPotential starGraph) windowHigh ε ζ (Θ.x b') (Θ.p b') at hdep
  have hS : (0 : ℝ) ≤ 1 := by norm_num
  have haS : (0 : ℝ) + 32 * ε ≤ 1 := by linarith
  have hb'1 : (0 : ℝ) < b' := hb'.1
  have hb'2 : b' ≤ 0 + 32 * ε := by
    have := hb'.2
    rw [gateNetwork_dwell_of_pos hε0] at this
    linarith
  have hxa := gate_arriving_boundary hε0 harr
  have hxb := gate_dep_boundary hε0 hdep
  have hdepprep : gateNetwork.Prepared (zeroPotential starGraph) windowHigh ε
      (otherEnd ζ) (Θ.x b') (Θ.p b') := hdep.prepared
  have hb'mem : b' ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  change ζ = starRouting.routeGerm η
  by_cases h2 : η.1 = 2
  · have harm := gate_arm Θ hε0 hεs hS hKw h2 harr.prepared
    have hζeq : ζ.1 = 2 := by
      have h := gate_arm_eq_two Θ harm hε0 hb'mem (η := otherEnd ζ) hdepprep
      simpa using h
    have hζη := gate_arm_exit_unique hε0 hεs harm h2 hζeq le_rfl haS hb'1 hb'2 hxa hxb
    rcases hb2 : η.2 with _ | _
    · rw [hζη]
      exact (starRouteGerm_arm h2 hb2).symm
    · rw [hζη]
      exact (starRouteGerm_of_true hb2).symm
  · have hth := gate_through Θ hε0 hεs hS hKw h2 harr.prepared
    have hζne : ζ.1 ≠ 2 := by
      have h := gate_through_ne_two Θ hth hε0 hεs hb'mem (η := otherEnd ζ) hdepprep
      simpa using h
    rcases hb2 : η.2 with _ | _
    · have hlongspeed : |longComp η.1 (Θ.p 0)| = |(Θ.p 0).1| := by
        rw [abs_longComp_of_ne_two h2]
      obtain ⟨hpa, hcK⟩ := gate_arr_mom hKw harr.prepared hlongspeed
      exact gate_through_exit_unique_high hε0 hεs hth (windowHigh_ge hcK) h2 hζne hb2 le_rfl haS
        hb'1 hb'2 hxa hpa hxb
    · have hζη := gate_through_exit_unique_outer hε0 hεs hth h2 hζne hb2 le_rfl haS hb'1 hb'2
        hxa hxb
      rw [hζη]
      exact (starRouteGerm_of_true hb2).symm

/-! ### The energy-dependent junction is deterministic in both regimes -/

/-- **The energy-dependent junction has a deterministic channel reduction on each window.**  The
same microscopic Hamiltonian family eliminates the transverse variables to two *different*
deterministic graph scattering laws.  Together with `ChannelKernel.channelKernel_of_deterministic`
this says that the observed vertex kernel is the Dirac mass at `F₋(η)` on `K₋` and at `F₊(η)` on
`K₊`, for **every** probability measure on the unresolved transverse data. -/
theorem explicit_energy_dependent_junction_deterministic :
    gateNetwork.HasDeterministicChannelReduction (zeroPotential starGraph) windowLow
        gateRoutingLow (1 / 100) ∧
      gateNetwork.HasDeterministicChannelReduction (zeroPotential starGraph) windowHigh
        gateRoutingHigh (1 / 100) ∧
      gateNetwork.ChannelsSeparated (zeroPotential starGraph) windowLow (1 / 100) ∧
      gateNetwork.ChannelsSeparated (zeroPotential starGraph) windowHigh (1 / 100) :=
  ⟨gateNetwork_hasDeterministicChannelReduction_low,
    gateNetwork_hasDeterministicChannelReduction_high,
    gateNetwork_channelsSeparated, gateNetwork_channelsSeparated⟩

/-! ### The coarse-grained vertex kernel in the two regimes -/

open MeasureTheory in
/-- **The coarse-grained vertex kernel below the gate is the Dirac mass at the incoming germ.**
For *every* probability measure `μ` on the unresolved microscopic data, and every family of
incoming states with the same projected germ `η`, averaging the microscopic outgoing channel over
`μ` produces `δ_η`. -/
theorem gate_channelKernel_low {η : starGraph.EdgeEnd} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (data : Ξ → gateNetwork.Incoming (zeroPotential starGraph) windowLow (1 / 100) η)
    (ζ : starGraph.EdgeEnd) :
    ChannelKernel.channelKernel μ (fun ξ => (data ξ).channel) ζ = if ζ = η then 1 else 0 :=
  ThinHamiltonianNetwork.channelKernel_of_deterministic
    gateNetwork_hasDeterministicChannelReduction_low μ data ζ

open MeasureTheory in
/-- **The coarse-grained vertex kernel above the gate is the Dirac mass at the routed germ.** -/
theorem gate_channelKernel_high {η : starGraph.EdgeEnd} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (data : Ξ → gateNetwork.Incoming (zeroPotential starGraph) windowHigh (1 / 100) η)
    (ζ : starGraph.EdgeEnd) :
    ChannelKernel.channelKernel μ (fun ξ => (data ξ).channel) ζ =
      if ζ = starRouting.routeGerm η then 1 else 0 :=
  ThinHamiltonianNetwork.channelKernel_of_deterministic
    gateNetwork_hasDeterministicChannelReduction_high μ data ζ

open MeasureTheory in
/-- **The two coarse-grained kernels differ.**  On the incoming channel `η₁` the low-energy kernel
is `δ_{η₁}` and the high-energy one is `δ_{η₂}`: eliminating the unresolved transverse data from
the *same* microscopic Hamiltonian family gives two different deterministic vertex laws. -/
theorem gate_channelKernel_differs {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (dataLow : Ξ → gateNetwork.Incoming (zeroPotential starGraph) windowLow (1 / 100) channel₁)
    (dataHigh : Ξ → gateNetwork.Incoming (zeroPotential starGraph) windowHigh (1 / 100)
      channel₁) :
    ChannelKernel.channelKernel μ (fun ξ => (dataLow ξ).channel) channel₁ = 1 ∧
      ChannelKernel.channelKernel μ (fun ξ => (dataHigh ξ).channel) channel₁ = 0 ∧
      ChannelKernel.channelKernel μ (fun ξ => (dataHigh ξ).channel) channel₂ = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gate_channelKernel_low μ dataLow channel₁, if_pos rfl]
  · rw [gate_channelKernel_high μ dataHigh channel₁, starRouting_channel₁,
      if_neg channel_ne₁₂]
  · rw [gate_channelKernel_high μ dataHigh channel₂, starRouting_channel₁, if_pos rfl]

end HamiltonianMetricGraphs
