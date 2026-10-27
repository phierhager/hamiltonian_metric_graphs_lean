/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.StarJunction

/-!
# Deterministic channel reduction for the explicit three-channel junction

The microscopic incoming state of a junction carries, besides the projected graph state `(η, r)`,
**unresolved transverse data** `ξ` — the transverse displacement and momentum inside the tube.
The microscopic scattering map `S_v(η, r, ξ)` is a deterministic map of the full state; the graph
scattering law is deterministic precisely when the *outgoing channel* of `S_v` does not depend on
`ξ` throughout the well-prepared incoming class.  That is the content of
`HasDeterministicChannelReduction`, and this file proves it for the explicit star network.

Two ingredients:

* `starNetwork_channelsSeparated` — a purely geometric fact: the three channels are pairwise
  disjoint at the junction boundary, so no microscopic state is departing through two different
  germs.  The through tube has width `2ε` while the arm mouth sits at `w = 8ε`, and the two
  halves of the through channel lie on opposite sides of the origin.
* `star_exit_unique` — a dynamical fact: within the junction window `[a, a + 23ε]` the particle
  cannot reach any junction boundary other than the one prescribed by `F⋆`.  For the three
  reflecting passages this follows from the travel bound `|Δq| ≤ 2 · 23ε = 46ε < 1 - 16ε`
  alone (the paper's "within `32ε ≥ θ_ε` the longitudinal coordinate changes by at most
  `64ε < 1 - 16ε`"); for the through crossing `η₁ ↦ η₂` it additionally uses that the
  longitudinal motion is exactly free, hence strictly monotone, so the particle cannot return to
  its own entrance boundary.

Since the incoming trajectory in these statements is *arbitrary* — only its projected graph state
is constrained — the outgoing channel is shown to be independent of the transverse data, which is
exactly the microscopic meaning of the determinism of `F⋆`.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {ε S : ℝ}

/-! ### Elementary edge arithmetic of the star -/

theorem embedSign_ne {e e' : starGraph.Edge} (h : e ≠ 2) (h' : e' ≠ 2) (hne : e' ≠ e) :
    ThroughRun.embedSign e' = -ThroughRun.embedSign e := by
  rcases edge_eq_of_ne_two h with rfl | rfl <;> rcases edge_eq_of_ne_two h' with rfl | rfl
  · exact absurd rfl hne
  · rw [ThroughRun.embedSign_one, ThroughRun.embedSign_zero]; norm_num
  · rw [ThroughRun.embedSign_zero, ThroughRun.embedSign_one]
  · exact absurd rfl hne

theorem eq_swapEdge_of_ne {e e' : starGraph.Edge} (h : e ≠ 2) (h' : e' ≠ 2) (hne : e' ≠ e) :
    e' = swapEdge e := by
  rcases edge_eq_of_ne_two h with rfl | rfl <;> rcases edge_eq_of_ne_two h' with rfl | rfl
  · exact absurd rfl hne
  · rfl
  · rfl
  · exact absurd rfl hne

/-- The two junction boundaries of an edge are distinct, so a germ is determined by the boundary
it names. -/
theorem starTarget_snd_eq (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {ζ ζ' : starGraph.EdgeEnd}
    (h : starTarget ε ζ = starTarget ε ζ') : ζ.2 = ζ'.2 := by
  rcases hb : ζ.2 with _ | _ <;> rcases hb' : ζ'.2 with _ | _
  · rfl
  · exfalso; rw [starTarget_of_false hb, starTarget_of_true hb'] at h; linarith
  · exfalso; rw [starTarget_of_true hb, starTarget_of_false hb'] at h; linarith
  · rfl

/-! ### Extracting a departing state -/

theorem star_dep_boundary (hε : 0 < ε) {ζ : starGraph.EdgeEnd} {x p : ℝ × ℝ}
    (h : starNetwork.Departing (zeroPotential starGraph) windowStar ε ζ x p) :
    longComp ζ.1 x = starTarget ε ζ := by
  have h1 := h.boundary
  rw [starNetwork_long, starNetwork_offset_of_pos hε] at h1
  exact h1

theorem star_dep_trans (hε : 0 < ε) {ζ : starGraph.EdgeEnd} {x p : ℝ × ℝ}
    (h : starNetwork.Departing (zeroPotential starGraph) windowStar ε ζ x p) :
    |transComp ζ.1 x| ≤ 2 * ε := by
  have h1 := star_prep_trans hε h.prepared
  simpa using h1

/-! ### The channels are geometrically separated -/

/-- **The three channels are microscopically separated.**  No state of the network can be
departing through two different germs: the arm mouth sits at `w = 8ε` while the through tube has
width `2ε`, and the two halves of the through channel lie on opposite sides of the origin. -/
theorem starNetwork_channelsSeparated :
    starNetwork.ChannelsSeparated (zeroPotential starGraph) windowStar (1 / 100) := by
  intro ε hε ζ ζ' x p h1 h2
  have hε0 : 0 < ε := hε.1
  have hεs : ε ≤ 1 / 100 := le_of_lt hε.2
  have hx1 := star_dep_boundary hε0 h1
  have hx2 := star_dep_boundary hε0 h2
  have ht1 := star_dep_trans hε0 h1
  have ht2 := star_dep_trans hε0 h2
  have hQ1 := starTarget_mem hε0 hεs ζ
  have hQ2 := starTarget_mem hε0 hεs ζ'
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
  refine starTarget_snd_eq hε0 hεs ?_
  rw [← hx1, ← hx2, hedge]

/-! ### The exit channel is unique -/

variable {Θ : starNetwork.MicroTrajectory ε S}

set_option maxHeartbeats 1000000 in
-- an eight-way case split over the germ types of the star
/-- **The through channel admits no other exit.**  Within the junction window the particle can
only reach the junction boundary of `F⋆(η)`. -/
theorem star_through_exit_unique (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {c : ℝ}
    (hth : StarThrough ε c S Θ) {η ζ : starGraph.EdgeEnd} (hne : η.1 ≠ 2) (hζne : ζ.1 ≠ 2)
    {a b' : ℝ} (ha : 0 ≤ a) (haS : a + 23 * ε ≤ S) (hb'1 : a < b') (hb'2 : b' ≤ a + 23 * ε)
    (hxa : longComp η.1 (Θ.x a) = starTarget ε η)
    (hpa : longComp η.1 (Θ.p a) = EdgeEnd.sign starGraph η * c)
    (hxb : longComp ζ.1 (Θ.x b') = starTarget ε ζ) :
    ζ = starRouting.routeGerm η := by
  have hc1 : 1 ≤ c := hth.cap.c_ge
  have hc2 : c ≤ 2 := hth.cap.c_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hssq : ThroughRun.embedSign η.1 * ThroughRun.embedSign η.1 = 1 := embedSign_sq η.1
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hb'mem : b' ∈ Icc (0 : ℝ) S := ⟨by linarith, by linarith⟩
  have hA : ThroughRun.embedSign η.1 * (Θ.x a).1 = starTarget ε η := by
    rw [← longComp_of_ne_two hne]; exact hxa
  -- the travel bound over the junction window
  have htravel0 : |(Θ.x b').1 - (Θ.x a).1| ≤ c * (b' - a) :=
    hth.cap.travel_le hamem hb'mem hb'1.le
  have htravel : |(Θ.x b').1 - (Θ.x a).1| ≤ 46 * ε := by
    have h1 : c * (b' - a) ≤ 46 * ε := by nlinarith [hb'1.le, hb'2]
    linarith
  have hBA : |ThroughRun.embedSign η.1 * (Θ.x b').1 - starTarget ε η| ≤ 46 * ε := by
    rw [← hA, ← mul_sub, abs_mul, abs_embedSign, one_mul]
    exact htravel
  obtain ⟨hBA1, hBA2⟩ := abs_le.mp hBA
  by_cases hedge : ζ.1 = η.1
  · -- the same edge
    have hB : ThroughRun.embedSign η.1 * (Θ.x b').1 = starTarget ε ζ := by
      rw [longComp_of_ne_two hζne, hedge] at hxb; exact hxb
    rcases hb : η.2 with _ | _
    · rcases hb2 : ζ.2 with _ | _
      · -- a return to the entrance boundary is impossible: the motion is strictly monotone
        exfalso
        rw [starTarget_of_false hb] at hA
        rw [starTarget_of_false hb2] at hB
        have hwin : a + 23 * ε ∈ Icc (0 : ℝ) S := ⟨by linarith, haS⟩
        have hua : (Θ.x a).1 = ThroughRun.embedSign η.1 * (8 * ε) := by
          rw [fst_eq_of_longComp hne, hxa, starTarget_of_false hb]
        have hpua : (Θ.p a).1 = -(ThroughRun.embedSign η.1 * c) := by
          rw [fst_eq_of_longComp hne, hpa, sign_of_false hb]; ring
        have habs1 : |(Θ.x a).1| < 1 := by
          rw [hua, abs_mul, abs_embedSign, one_mul, abs_of_nonneg (by linarith)]
          linarith
        have habs2 : |(Θ.x a).1 + (Θ.p a).1 * (a + 23 * ε - a)| < 1 := by
          have hval : (Θ.x a).1 + (Θ.p a).1 * (a + 23 * ε - a)
              = ThroughRun.embedSign η.1 * (8 * ε - 23 * ε * c) := by
            rw [hua, hpua]; ring
          rw [hval, abs_mul, abs_embedSign, one_mul, abs_lt]
          constructor <;> nlinarith
        obtain ⟨hub, -⟩ := hth.cap.free_of_endpoints hamem hwin (by linarith) habs1 habs2 b'
          ⟨hb'1.le, hb'2⟩
        have hub' : (Θ.x b').1 = (Θ.x a).1 + (Θ.p a).1 * (b' - a) := hub
        have hspa : ThroughRun.embedSign η.1 * (Θ.p a).1 = -c := by
          rw [hpua, mul_neg, ← mul_assoc, hssq, one_mul]
        have hkey : ThroughRun.embedSign η.1 * (Θ.x b').1
            = ThroughRun.embedSign η.1 * (Θ.x a).1
              + ThroughRun.embedSign η.1 * (Θ.p a).1 * (b' - a) := by
          rw [hub']; ring
        rw [hA, hB, hspa] at hkey
        have hprod := mul_pos hc0 (show (0 : ℝ) < b' - a by linarith)
        linarith
      · exfalso
        rw [starTarget_of_false hb] at hA hBA1 hBA2
        rw [starTarget_of_true hb2] at hB
        linarith
    · rcases hb2 : ζ.2 with _ | _
      · exfalso
        rw [starTarget_of_true hb] at hA hBA1 hBA2
        rw [starTarget_of_false hb2] at hB
        linarith
      · -- the outer reflection: the exit germ is the entrance germ
        have hζη : ζ = η := Prod.ext hedge (by rw [hb, hb2])
        rw [hζη, starRouteGerm_of_true hb]
  · -- the other edge of the through channel
    have hζs : ThroughRun.embedSign ζ.1 = -ThroughRun.embedSign η.1 :=
      embedSign_ne hne hζne hedge
    have hB : ThroughRun.embedSign η.1 * (Θ.x b').1 = -starTarget ε ζ := by
      rw [longComp_of_ne_two hζne, hζs] at hxb
      linarith
    have hswap : ζ.1 = swapEdge η.1 := eq_swapEdge_of_ne hne hζne hedge
    rcases hb : η.2 with _ | _
    · rcases hb2 : ζ.2 with _ | _
      · -- the through crossing `η₁ ↦ η₂`
        rw [starRouteGerm_of_false hb]
        exact Prod.ext hswap (by rw [hb2])
      · exfalso
        rw [starTarget_of_false hb] at hA hBA1 hBA2
        rw [starTarget_of_true hb2] at hB
        linarith
    · exfalso
      rw [starTarget_of_true hb] at hA hBA1 hBA2
      rcases hb2 : ζ.2 with _ | _
      · rw [starTarget_of_false hb2] at hB; linarith
      · rw [starTarget_of_true hb2] at hB; linarith

/-- **The third arm admits no other exit.** -/
theorem star_arm_exit_unique (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {c : ℝ}
    (harm : StarArm ε c S Θ) {η ζ : starGraph.EdgeEnd} (heq : η.1 = 2) (hζeq : ζ.1 = 2)
    {a b' : ℝ} (ha : 0 ≤ a) (haS : a + 23 * ε ≤ S) (hb'1 : a < b') (hb'2 : b' ≤ a + 23 * ε)
    (hxa : longComp η.1 (Θ.x a) = starTarget ε η)
    (hxb : longComp ζ.1 (Θ.x b') = starTarget ε ζ) :
    ζ = starRouting.routeGerm η := by
  have hc1 : 1 ≤ c := harm.arm.c_ge
  have hc2 : c ≤ 2 := harm.arm.c_le
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hb'mem : b' ∈ Icc (0 : ℝ) S := ⟨by linarith, by linarith⟩
  rw [heq, longComp_two] at hxa
  rw [hζeq, longComp_two] at hxb
  have htravel0 : |(Θ.x b').2 - (Θ.x a).2| ≤ c * (b' - a) :=
    harm.arm.travel_le hamem hb'mem hb'1.le
  have htravel : |starTarget ε ζ - starTarget ε η| ≤ 46 * ε := by
    rw [← hxa, ← hxb]
    have h1 : c * (b' - a) ≤ 46 * ε := by nlinarith [hb'1.le, hb'2]
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
  have hζη : ζ = η := Prod.ext (by rw [hζeq, heq]) hsnd
  rw [hζη]
  rcases hb : η.2 with _ | _
  · rw [starRouteGerm_of_false hb]
    exact Prod.ext (by rw [heq]; rfl) (by rw [hb])
  · rw [starRouteGerm_of_true hb]

/-- The incoming longitudinal momentum of a well-prepared through state is the nominal one. -/
theorem star_through_mom_eq (hε : 0 < ε) {c : ℝ} (hth : StarThrough ε c S Θ)
    {η : starGraph.EdgeEnd} (hne : η.1 ≠ 2) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) S)
    (hp : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η (Θ.x a) (Θ.p a)) :
    longComp η.1 (Θ.p a) = EdgeEnd.sign starGraph η * c := by
  have hq := star_prep_long hε hp
  have hua : |(Θ.x a).1| ≤ 1 := by
    rw [← abs_longComp_of_ne_two hne, abs_of_nonneg (by linarith [hq.1])]
    linarith [hq.2]
  have hspeed : |(Θ.p a).1| = c := hth.speed_eq hε ha hua
  obtain ⟨r, hr, hr1, hr2⟩ := star_prep_mom hp
  have hrc : r = c := by
    have hval : |longComp η.1 (Θ.p a)| = r := by
      rw [hr, abs_mul, star_abs_sign, one_mul, abs_of_nonneg (by linarith)]
    rw [abs_longComp_of_ne_two hne, hspeed] at hval
    exact hval.symm
  rw [hr, hrc]

/-! ### Deterministic channel reduction -/

/-- **The explicit three-channel junction has deterministic channel reduction.**  Whatever the
unresolved transverse data of the incoming state, the particle leaves the junction through
`F⋆(η)` and through no other germ.  Eliminating the transverse variables therefore produces
exactly the deterministic graph scattering law `F⋆`. -/
theorem starNetwork_hasDeterministicChannelReduction :
    starNetwork.HasDeterministicChannelReduction (zeroPotential starGraph) windowStar
      starRouting (1 / 100) := by
  refine ⟨starNetwork_junctionScattering, ?_⟩
  intro ε hε η x p harr₀ b' hb' ζ hdep
  have hε0 : 0 < ε := hε.1
  have hεs : ε ≤ 1 / 100 := le_of_lt hε.2
  -- the flow through `(x, p)` on `[0, 1]`, which contains the junction window `[0, 23ε]`
  set Θ := starNetwork.flowTraj ε (x, p) 1 with hΘ
  have harr : starNetwork.Arriving (zeroPotential starGraph) windowStar ε η (Θ.x 0) (Θ.p 0) := by
    rw [hΘ, ThinHamiltonianNetwork.flowTraj_x_zero, ThinHamiltonianNetwork.flowTraj_p_zero]
    exact harr₀
  change starNetwork.Departing (zeroPotential starGraph) windowStar ε ζ (Θ.x b') (Θ.p b') at hdep
  have hS : (0 : ℝ) ≤ 1 := by norm_num
  have haS : (0 : ℝ) + 23 * ε ≤ 1 := by linarith
  have hb'1 : (0 : ℝ) < b' := hb'.1
  have hb'2 : b' ≤ 0 + 23 * ε := by
    have := hb'.2
    rw [starNetwork_dwell_of_pos hε0] at this
    linarith
  have hamem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, hS⟩
  have hxa := star_arriving_boundary hε0 harr
  have hxb := star_dep_boundary hε0 hdep
  have hdepprep : starNetwork.Prepared (zeroPotential starGraph) windowStar ε
      (otherEnd ζ) (Θ.x b') (Θ.p b') := hdep.prepared
  have hb'mem : b' ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  by_cases h2 : η.1 = 2
  · have harm := star_arm Θ hε0 hεs hS h2 harr.prepared
    have hζeq : ζ.1 = 2 := by
      have h := star_arm_eq_two Θ harm hε0 hb'mem (η := otherEnd ζ) hdepprep
      simpa using h
    exact star_arm_exit_unique hε0 hεs harm h2 hζeq le_rfl haS hb'1 hb'2 hxa hxb
  · have hth := star_through Θ hε0 hεs hS h2 harr.prepared
    have hζne : ζ.1 ≠ 2 := by
      have h := star_through_ne_two Θ hth hε0 hεs hb'mem (η := otherEnd ζ) hdepprep
      simpa using h
    exact star_through_exit_unique hε0 hεs hth h2 hζne le_rfl haS hb'1 hb'2 hxa
      (star_through_mom_eq hε0 hth h2 hamem harr.prepared) hxb

end HamiltonianMetricGraphs
