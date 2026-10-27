/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.StarConfinement

/-!
# The edge-reduction hypothesis for the explicit three-channel junction

This file discharges `SatisfiesEdgeReduction` for the explicit star network: from every
well-prepared microscopic state of `H_ε = ½|p|² + microPot ε` that has not yet reached the
junction boundary, the trajectory performs a genuine edge flight.

The argument is the same in the two channels, because in both the potential is flat along the
tube: `capPot ε` vanishes identically on the closed edge `|u| ≤ 1`, and `armPot ε` vanishes
identically on `[7ε, 1]`.  Hence

* the **longitudinal motion is exactly free** (`CapMotion.free_of_endpoints`,
  `ArmMotion.free_of_endpoints`), so the projected pair `(q, p)` solves `q' = p`, `p' = 0`
  *exactly*: the longitudinal force vanishes, so (E3) holds with `γ_ε = 0`, not merely small;
* the **transverse displacement and energy** stay below `2ε` and `ε` by the exact conservation
  laws of `StarConfinement.lean`;
* the flight ends at the junction boundary of the germ, in a state again well prepared.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {ε S : ℝ}

/-! ### The two germ types of the star -/

/-- Every germ of the star is either an outer germ, with sign `+1` and coordinate `1`, or an
inner germ at the branching vertex, with sign `-1` and coordinate `0`. -/
theorem star_sign_coord (η : starGraph.EdgeEnd) :
    (EdgeEnd.sign starGraph η = 1 ∧ EdgeEnd.coordinate starGraph η = 1) ∨
      (EdgeEnd.sign starGraph η = -1 ∧ EdgeEnd.coordinate starGraph η = 0) := by
  rcases hb : η.2 with _ | _
  · exact Or.inr ⟨sign_of_false hb, coordinate_of_false hb⟩
  · exact Or.inl ⟨sign_of_true hb, coordinate_of_true starGraph_length_eq_one hb⟩

theorem star_abs_sign (η : starGraph.EdgeEnd) : |EdgeEnd.sign starGraph η| = 1 := by
  rcases star_sign_coord η with ⟨hs, _⟩ | ⟨hs, _⟩ <;> rw [hs] <;> norm_num

/-- The junction boundary reached by a flight towards `η`. -/
noncomputable def starTarget (ε : ℝ) (η : starGraph.EdgeEnd) : ℝ :=
  EdgeEnd.coordinate starGraph η - EdgeEnd.sign starGraph η * (8 * ε)

theorem starTarget_mem (hε : 0 < ε) (hεs : ε ≤ 1 / 100) (η : starGraph.EdgeEnd) :
    starTarget ε η ∈ Icc (8 * ε) (1 - 8 * ε) := by
  rw [starTarget]
  rcases star_sign_coord η with ⟨hs, hc⟩ | ⟨hs, hc⟩ <;> rw [hs, hc] <;>
    constructor <;> linarith

theorem starNetwork_toGo (hε : 0 < ε) (η : starGraph.EdgeEnd) (q : ℝ) :
    starNetwork.toGo ε η q = |starTarget ε η - q| := by
  rw [ThinHamiltonianNetwork.toGo, starNetwork_offset_of_pos hε, starTarget]

/-! ### The generic edge flight -/

set_option maxHeartbeats 1000000 in
-- the components of `EdgeFlight` are discharged in one pass
/-- **The generic edge flight of the star network.**  Once the projected longitudinal motion
along the flight is known to be exactly free — which is what the flatness of the tube potential
gives — every one of the nine components of `EdgeFlight` follows by elementary algebra. -/
theorem star_mk_edgeFlight (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    {Θ : starNetwork.MicroTrajectory ε S} {η : starGraph.EdgeEnd} {a b r : ℝ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hab : a < b) (ha0 : 0 ≤ a) (hbS : b ≤ S)
    (hq₀ : longComp η.1 (Θ.x a) ∈ Icc (8 * ε) (1 - 8 * ε))
    (hQ : longComp η.1 (Θ.x a) + EdgeEnd.sign starGraph η * r * (b - a) = starTarget ε η)
    (hfree : ∀ t ∈ Icc a b, longComp η.1 (Θ.x t) =
        longComp η.1 (Θ.x a) + EdgeEnd.sign starGraph η * r * (t - a) ∧
        longComp η.1 (Θ.p t) = EdgeEnd.sign starGraph η * r)
    (htr : ∀ t ∈ Icc a b, |transComp η.1 (Θ.x t)| ≤ 2 * ε)
    (hte : ∀ t ∈ Icc a b, transComp η.1 (Θ.p t) ^ 2 / 2
        + wellPot ε (transComp η.1 (Θ.x t)) ≤ ε) :
    starNetwork.EdgeFlight (zeroPotential starGraph) windowStar ε η Θ.x Θ.p a b := by
  have hQmem := starTarget_mem hε (by linarith) η
  have hr0 : (0 : ℝ) < r := by linarith
  -- the position along the flight interpolates between the two junction boundaries
  have hpos : ∀ t ∈ Icc a b, longComp η.1 (Θ.x t) ∈ Icc (8 * ε) (1 - 8 * ε) := by
    intro t ht
    have hlo : (0 : ℝ) ≤ r * (t - a) := mul_nonneg hr0.le (by linarith [ht.1])
    have hhi : (0 : ℝ) ≤ r * (b - t) := mul_nonneg hr0.le (by linarith [ht.2])
    rw [(hfree t ht).1]
    rcases star_sign_coord η with ⟨hs, _⟩ | ⟨hs, _⟩ <;> rw [hs] at hQ ⊢ <;>
      exact ⟨by nlinarith [hq₀.1, hq₀.2, hQmem.1, hQmem.2],
        by nlinarith [hq₀.1, hq₀.2, hQmem.1, hQmem.2]⟩
  have hstrict : ∀ t ∈ Ioo a b, longComp η.1 (Θ.x t) ∈ Ioo (8 * ε) (1 - 8 * ε) := by
    intro t ht
    have hlo : (0 : ℝ) < r * (t - a) := mul_pos hr0 (by linarith [ht.1])
    have hhi : (0 : ℝ) < r * (b - t) := mul_pos hr0 (by linarith [ht.2])
    rw [(hfree t (Ioo_subset_Icc_self ht)).1]
    rcases star_sign_coord η with ⟨hs, _⟩ | ⟨hs, _⟩ <;> rw [hs] at hQ ⊢ <;>
      exact ⟨by nlinarith [hq₀.1, hq₀.2, hQmem.1, hQmem.2],
        by nlinarith [hq₀.1, hq₀.2, hQmem.1, hQmem.2]⟩
  -- the state at the end of the flight
  have hmemb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hprepb : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η (Θ.x b) (Θ.p b) := by
    have hsq : EdgeEnd.sign starGraph η ^ 2 = 1 := starGraph.edgeEnd_sign_sq η
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [starNetwork_long, starNetwork_offset_of_pos hε, starGraph_length]
      exact hpos b hmemb
    · rw [starNetwork_trans, starNetwork_tubeWidth_of_pos hε]
      exact htr b hmemb
    · rw [starNetwork_transEnergy, starNetwork_transErr_of_pos hε]
      exact hte b hmemb
    · rw [starNetwork_longP, (hfree b hmemb).2]
      nlinarith
    · rw [starNetwork_long, starNetwork_longP, zeroPotential_hamiltonian,
        (hfree b hmemb).2, mul_pow, hsq, one_mul]
      exact ⟨by nlinarith, by nlinarith⟩
  -- the longitudinal force vanishes: the longitudinal momentum is constant
  have hgrad := Θ.longGrad_eq_zero_of_const (e := η.1) ha0 hab hbS
    (c := EdgeEnd.sign starGraph η * r)
    (fun t ht => by rw [starNetwork_longP]; exact (hfree t ht).2)
  refine ⟨hab, ?_, ?_, ?_, ⟨hprepb, ?_⟩, ?_⟩
  · intro t ht
    rw [starNetwork_long, starNetwork_offset_of_pos hε, starGraph_length]
    exact hstrict t ht
  · intro t ht
    rw [starNetwork_trans, starNetwork_tubeWidth_of_pos hε]
    exact htr t ht
  · intro t ht
    rw [starNetwork_transEnergy, starNetwork_transErr_of_pos hε]
    exact hte t ht
  · -- the flight ends exactly at the junction boundary
    rw [starNetwork_long, (hfree b hmemb).1, starNetwork_offset_of_pos hε]
    exact hQ
  · -- (E3) holds exactly: both forces vanish
    intro t ht
    rw [hgrad t ht, starNetwork_forceErr, zeroPotential_extension_deriv, sub_zero, abs_zero]

/-! ### The data of a well-prepared state -/

/-- The longitudinal momentum of a well-prepared state points towards `η` with a nominal speed
in `[1, 2]`. -/
theorem star_prep_mom {η : starGraph.EdgeEnd} {x p : ℝ × ℝ}
    (h : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η x p) :
    ∃ r : ℝ, longComp η.1 p = EdgeEnd.sign starGraph η * r ∧ 1 ≤ r ∧ r ≤ 2 := by
  refine ⟨|longComp η.1 p|, ?_, (star_prep_speed h).1, (star_prep_speed h).2⟩
  have htow := star_prep_towards h
  rcases star_sign_coord η with ⟨hs, _⟩ | ⟨hs, _⟩ <;> rw [hs] at htow ⊢
  · rw [abs_of_pos (by linarith), one_mul]
  · rw [abs_of_neg (by linarith)]; ring

/-- The distance still to be travelled before the junction boundary, signed by the germ. -/
theorem star_prep_toGo (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {η : starGraph.EdgeEnd} {x p : ℝ × ℝ}
    (h : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η x p)
    (hgo : 0 < starNetwork.toGo ε η (starNetwork.long η.1 x)) :
    ∃ d : ℝ, starTarget ε η - longComp η.1 x = EdgeEnd.sign starGraph η * d ∧
      0 < d ∧ d ≤ 1 := by
  have hq := star_prep_long hε h
  have hQ := starTarget_mem hε hεs η
  refine ⟨|starTarget ε η - longComp η.1 x|, ?_, ?_, ?_⟩
  · rcases star_sign_coord η with ⟨hs, hc⟩ | ⟨hs, hc⟩
    · have hQ' : starTarget ε η = 1 - 8 * ε := by rw [starTarget, hs, hc]; ring
      rw [hs, one_mul, abs_of_nonneg (by rw [hQ']; linarith [hq.2])]
    · have hQ' : starTarget ε η = 8 * ε := by rw [starTarget, hs, hc]; ring
      rw [hs, abs_of_nonpos (by rw [hQ']; linarith [hq.1])]; ring
  · rw [starNetwork_toGo hε, starNetwork_long] at hgo; exact hgo
  · rw [abs_le]
    exact ⟨by linarith [hq.2, hQ.1], by linarith [hq.1, hQ.2]⟩

/-! ### The edge flight in the two channels -/

/-- **The edge flight in the through channel.** -/
theorem star_through_edgeFlight (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    {Θ : starNetwork.MicroTrajectory ε S} {c : ℝ} (hth : StarThrough ε c S Θ)
    {η : starGraph.EdgeEnd} (hne : η.1 ≠ 2) {a : ℝ} (ha : 0 ≤ a) (haS : a + 2 ≤ S)
    (hp : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η (Θ.x a) (Θ.p a))
    (hgo : 0 < starNetwork.toGo ε η (starNetwork.long η.1 (Θ.x a))) :
    ∃ b, starNetwork.EdgeFlight (zeroPotential starGraph) windowStar ε η Θ.x Θ.p a b := by
  obtain ⟨r, hpa, hr1, hr2⟩ := star_prep_mom hp
  obtain ⟨d, hdq, hd0, hd1⟩ := star_prep_toGo hε hεs hp hgo
  have hr0 : (0 : ℝ) < r := by linarith
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hq₀mem := star_prep_long hε hp
  have hQmem := starTarget_mem hε hεs η
  have hdr : d / r ≤ 1 := by rw [div_le_one hr0]; linarith
  have hab : a < a + d / r := by have := div_pos hd0 hr0; linarith
  have hble : a + d / r ≤ a + 2 := by linarith
  have hQeq : longComp η.1 (Θ.x a)
      + EdgeEnd.sign starGraph η * r * (a + d / r - a) = starTarget ε η := by
    have h1 : a + d / r - a = d / r := by ring
    have h2 : r * (d / r) = d := by field_simp
    rw [h1, mul_assoc, h2]
    linarith [hdq]
  -- the free longitudinal motion of the through channel
  have hssq : ThroughRun.embedSign η.1 * ThroughRun.embedSign η.1 = 1 := embedSign_sq η.1
  have hLu : ∀ t : ℝ, longComp η.1 (Θ.x t) = ThroughRun.embedSign η.1 * (Θ.x t).1 :=
    fun t => longComp_of_ne_two hne _
  have hLp : ∀ t : ℝ, longComp η.1 (Θ.p t) = ThroughRun.embedSign η.1 * (Θ.p t).1 :=
    fun t => longComp_of_ne_two hne _
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hbmem : a + d / r ∈ Icc (0 : ℝ) S := ⟨by linarith, by linarith⟩
  have habs1 : |(Θ.x a).1| < 1 := by
    rw [← abs_longComp_of_ne_two hne, abs_of_nonneg (by linarith [hq₀mem.1])]
    linarith [hq₀mem.2]
  have hQ' : ThroughRun.embedSign η.1 * ((Θ.x a).1 + (Θ.p a).1 * (a + d / r - a))
      = starTarget ε η := by
    rw [← hQeq, ← hpa]
    simp only [hLu, hLp]
    ring
  have habs2 : |(Θ.x a).1 + (Θ.p a).1 * (a + d / r - a)| < 1 := by
    have h := congrArg abs hQ'
    rw [abs_mul, abs_embedSign, one_mul] at h
    rw [h, abs_of_nonneg (by linarith [hQmem.1])]
    linarith [hQmem.2]
  have hfreeu := hth.cap.free_of_endpoints hamem hbmem hab.le habs1 habs2
  have hsub : Icc a (a + d / r) ⊆ Icc (0 : ℝ) S := Icc_subset_Icc ha (by linarith)
  have hfree : ∀ t ∈ Icc a (a + d / r), longComp η.1 (Θ.x t) =
      longComp η.1 (Θ.x a) + EdgeEnd.sign starGraph η * r * (t - a) ∧
      longComp η.1 (Θ.p t) = EdgeEnd.sign starGraph η * r := by
    intro t ht
    have hu : (Θ.x t).1 = (Θ.x a).1 + (Θ.p a).1 * (t - a) := (hfreeu t ht).1
    have hpu : (Θ.p t).1 = (Θ.p a).1 := (hfreeu t ht).2
    refine ⟨?_, ?_⟩
    · rw [← hpa]
      simp only [hLu, hLp]
      rw [hu]
      ring
    · rw [← hpa]
      simp only [hLp]
      rw [hpu]
  refine ⟨a + d / r, star_mk_edgeFlight hε hεs hr1 hr2 hab ha (by linarith) hq₀mem hQeq hfree
    ?_ ?_⟩
  · intro t ht
    rw [transComp_of_ne_two hne]
    exact (hth.abs_trans_lt hε hεs (hsub ht)).le
  · intro t ht
    simp only [transComp_of_ne_two hne]
    exact hth.trans_le t (hsub ht)

/-- **The edge flight in the third arm.** -/
theorem star_arm_edgeFlight (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    {Θ : starNetwork.MicroTrajectory ε S} {c : ℝ} (harm : StarArm ε c S Θ)
    {η : starGraph.EdgeEnd} (heq : η.1 = 2) {a : ℝ} (ha : 0 ≤ a) (haS : a + 2 ≤ S)
    (hp : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η (Θ.x a) (Θ.p a))
    (hgo : 0 < starNetwork.toGo ε η (starNetwork.long η.1 (Θ.x a))) :
    ∃ b, starNetwork.EdgeFlight (zeroPotential starGraph) windowStar ε η Θ.x Θ.p a b := by
  obtain ⟨r, hpa, hr1, hr2⟩ := star_prep_mom hp
  obtain ⟨d, hdq, hd0, hd1⟩ := star_prep_toGo hε hεs hp hgo
  have hr0 : (0 : ℝ) < r := by linarith
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hq₀mem := star_prep_long hε hp
  have hQmem := starTarget_mem hε hεs η
  have hdr : d / r ≤ 1 := by rw [div_le_one hr0]; linarith
  have hab : a < a + d / r := by have := div_pos hd0 hr0; linarith
  have hble : a + d / r ≤ a + 2 := by linarith
  have hQeq : longComp η.1 (Θ.x a)
      + EdgeEnd.sign starGraph η * r * (a + d / r - a) = starTarget ε η := by
    have h1 : a + d / r - a = d / r := by ring
    have h2 : r * (d / r) = d := by field_simp
    rw [h1, mul_assoc, h2]
    linarith [hdq]
  have hlc : ∀ z : ℝ × ℝ, longComp η.1 z = z.2 := by rw [heq]; exact fun z => longComp_two z
  have htc : ∀ z : ℝ × ℝ, transComp η.1 z = z.1 := by rw [heq]; exact fun z => transComp_two z
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hbmem : a + d / r ∈ Icc (0 : ℝ) S := ⟨by linarith, by linarith⟩
  have hQeq' : (Θ.x a).2 + (Θ.p a).2 * (a + d / r - a) = starTarget ε η := by
    rw [← hQeq, ← hpa]
    simp only [hlc]
  have hwmem : (Θ.x a).2 ∈ Icc (8 * ε) (1 - 8 * ε) := by
    rw [← hlc]; exact hq₀mem
  have hw1 : (Θ.x a).2 ∈ Ioo (7 * ε) 1 := ⟨by linarith [hwmem.1], by linarith [hwmem.2]⟩
  have hw2 : (Θ.x a).2 + (Θ.p a).2 * (a + d / r - a) ∈ Ioo (7 * ε) 1 :=
    ⟨by rw [hQeq']; linarith [hQmem.1], by rw [hQeq']; linarith [hQmem.2]⟩
  have hfreeu := harm.arm.free_of_endpoints hamem hbmem hab.le hw1 hw2
  have hsub : Icc a (a + d / r) ⊆ Icc (0 : ℝ) S := Icc_subset_Icc ha (by linarith)
  have hfree : ∀ t ∈ Icc a (a + d / r), longComp η.1 (Θ.x t) =
      longComp η.1 (Θ.x a) + EdgeEnd.sign starGraph η * r * (t - a) ∧
      longComp η.1 (Θ.p t) = EdgeEnd.sign starGraph η * r := by
    intro t ht
    have hu : (Θ.x t).2 = (Θ.x a).2 + (Θ.p a).2 * (t - a) := (hfreeu t ht).1
    have hpu : (Θ.p t).2 = (Θ.p a).2 := (hfreeu t ht).2
    refine ⟨?_, ?_⟩
    · rw [← hpa]
      simp only [hlc]
      rw [hu]
    · rw [← hpa]
      simp only [hlc]
      rw [hpu]
  refine ⟨a + d / r, star_mk_edgeFlight hε hεs hr1 hr2 hab ha (by linarith) hq₀mem hQeq hfree
    ?_ ?_⟩
  · intro t ht
    rw [htc]
    exact (harm.abs_trans_lt hε hεs (hsub ht)).le
  · intro t ht
    simp only [htc]
    exact harm.trans_le t (hsub ht)

/-! ### The edge-reduction hypothesis -/

/-- **The explicit three-channel junction satisfies the edge-reduction hypothesis (E).**  Both
channels are covered: the through channel `η₁ ↔ η₂` and the third arm `η₃ ↦ η₃`.  The flow from a
prepared state is analysed on `[0, 2]`, which contains the whole flight. -/
theorem starNetwork_satisfiesEdgeReduction :
    starNetwork.SatisfiesEdgeReduction (zeroPotential starGraph) windowStar (1 / 100) := by
  intro ε hε η x p hp hna
  have hε0 : 0 < ε := hε.1
  have hεs : ε ≤ 1 / 100 := le_of_lt hε.2
  -- the flow through `(x, p)` on `[0, 2]`
  set Θ := starNetwork.flowTraj ε (x, p) 2 with hΘ
  have h₀ : starNetwork.Prepared (zeroPotential starGraph) windowStar ε η (Θ.x 0) (Θ.p 0) := by
    rw [hΘ, ThinHamiltonianNetwork.flowTraj_x_zero, ThinHamiltonianNetwork.flowTraj_p_zero]
    exact hp
  have hgo : 0 < starNetwork.toGo ε η (starNetwork.long η.1 (Θ.x 0)) := by
    rw [hΘ, ThinHamiltonianNetwork.flowTraj_x_zero]
    exact ThinHamiltonianNetwork.toGo_pos_of_not_arriving hp hna
  have hS : (0 : ℝ) ≤ 2 := by norm_num
  by_cases h2 : η.1 = 2
  · exact star_arm_edgeFlight hε0 hεs (star_arm Θ hε0 hεs hS h2 h₀) h2 le_rfl (by norm_num) h₀ hgo
  · exact star_through_edgeFlight hε0 hεs (star_through Θ hε0 hεs hS h2 h₀) h2 le_rfl
      (by norm_num) h₀ hgo

end HamiltonianMetricGraphs
