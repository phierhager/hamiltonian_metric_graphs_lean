/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.GateConfinement

/-!
# The edge-reduction hypothesis for the gated three-channel junction

The gate of `GatePotential.lean` sits inside the junction region `|u| ≤ 2ε`, strictly inside the
disc of radius `8ε` that bounds the tube mouths.  Along an **edge flight** it is therefore
completely inactive, exactly as the caps are, and the longitudinal motion is again *exactly free*:

* on the edge `1` the flight lives in `u ∈ [8ε, 1 - 8ε] ⊂ (2ε, 1)`, where `gatePot ε` is flat
  (`GateSolution.free_right_of_endpoints`);
* on the edge `0` it lives in `u ∈ [-(1 - 8ε), -8ε] ⊂ (-1, -2ε)`, where `gatePot ε` is again flat
  (`GateSolution.free_left_of_endpoints`);
* on the edge `2` the potential is literally the ungated one, so `ArmMotion.free_of_endpoints`
  applies verbatim.

Hence the longitudinal force vanishes along every flight, so (E3) holds with `γ_ε = 0` for the
gated network too, and `SatisfiesEdgeReduction` holds on **every** energy window `K ⊆ [1/2, 2]` —
in particular on both `windowLow` and `windowHigh`.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {ε S : ℝ} {K : Set ℝ}

set_option maxHeartbeats 1000000 in
-- the components of `EdgeFlight` are discharged in one pass
/-- **The generic edge flight of the gated network.**  Once the projected longitudinal motion
along the flight is known to be exactly free, every component of `EdgeFlight` follows by
elementary algebra; the longitudinal force (E3) vanishes because the longitudinal momentum is
constant.  This is the gated analogue of `star_mk_edgeFlight`; the only
change is that the energy window is an arbitrary `K` and the energy of the outgoing state is
supplied by the hypothesis `hrK`. -/
theorem gate_mk_edgeFlight (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    {Θ : gateNetwork.MicroTrajectory ε S} {η : starGraph.EdgeEnd} {a b r : ℝ}
    (hr1 : 1 ≤ r) (hrK : r ^ 2 / 2 ∈ K) (hab : a < b) (ha0 : 0 ≤ a)
    (hbS : b ≤ S)
    (hq₀ : longComp η.1 (Θ.x a) ∈ Icc (8 * ε) (1 - 8 * ε))
    (hQ : longComp η.1 (Θ.x a) + EdgeEnd.sign starGraph η * r * (b - a) = starTarget ε η)
    (hfree : ∀ t ∈ Icc a b, longComp η.1 (Θ.x t) =
        longComp η.1 (Θ.x a) + EdgeEnd.sign starGraph η * r * (t - a) ∧
        longComp η.1 (Θ.p t) = EdgeEnd.sign starGraph η * r)
    (htr : ∀ t ∈ Icc a b, |transComp η.1 (Θ.x t)| ≤ 2 * ε)
    (hte : ∀ t ∈ Icc a b, transComp η.1 (Θ.p t) ^ 2 / 2
        + wellPot ε (transComp η.1 (Θ.x t)) ≤ ε) :
    gateNetwork.EdgeFlight (zeroPotential starGraph) K ε η Θ.x Θ.p a b := by
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
  have hprepb : gateNetwork.Prepared (zeroPotential starGraph) K ε η (Θ.x b) (Θ.p b) := by
    have hsq : EdgeEnd.sign starGraph η ^ 2 = 1 := starGraph.edgeEnd_sign_sq η
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [gateNetwork_long, gateNetwork_offset_of_pos hε, starGraph_length]
      exact hpos b hmemb
    · rw [gateNetwork_trans, gateNetwork_tubeWidth_of_pos hε]
      exact htr b hmemb
    · rw [gateNetwork_transEnergy, gateNetwork_transErr_of_pos hε]
      exact hte b hmemb
    · rw [gateNetwork_longP, (hfree b hmemb).2]
      nlinarith
    · rw [gateNetwork_long, gateNetwork_longP, zeroPotential_hamiltonian,
        (hfree b hmemb).2, mul_pow, hsq, one_mul]
      exact hrK
  -- the longitudinal force vanishes: the longitudinal momentum is constant
  have hgrad := Θ.longGrad_eq_zero_of_const (e := η.1) ha0 hab hbS
    (c := EdgeEnd.sign starGraph η * r)
    (fun t ht => by rw [gateNetwork_longP]; exact (hfree t ht).2)
  refine ⟨hab, ?_, ?_, ?_, ⟨hprepb, ?_⟩, ?_⟩
  · intro t ht
    rw [gateNetwork_long, gateNetwork_offset_of_pos hε, starGraph_length]
    exact hstrict t ht
  · intro t ht
    rw [gateNetwork_trans, gateNetwork_tubeWidth_of_pos hε]
    exact htr t ht
  · intro t ht
    rw [gateNetwork_transEnergy, gateNetwork_transErr_of_pos hε]
    exact hte t ht
  · -- the flight ends exactly at the junction boundary
    rw [gateNetwork_long, (hfree b hmemb).1, gateNetwork_offset_of_pos hε]
    exact hQ
  · -- (E3) holds exactly: both forces vanish
    intro t ht
    rw [hgrad t ht, gateNetwork_forceErr, zeroPotential_extension_deriv, sub_zero, abs_zero]

/-! ### The data of a well-prepared state -/

/-- The longitudinal momentum of a well-prepared state points towards `η` with a nominal speed
in `[1, 2]` whose energy lies in the window. -/
theorem gate_prep_mom (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {η : starGraph.EdgeEnd} {x p : ℝ × ℝ}
    (h : gateNetwork.Prepared (zeroPotential starGraph) K ε η x p) :
    ∃ r : ℝ, longComp η.1 p = EdgeEnd.sign starGraph η * r ∧ 1 ≤ r ∧ r ≤ 2 ∧ r ^ 2 / 2 ∈ K := by
  refine ⟨|longComp η.1 p|, ?_, (gate_prep_speed hKw h).1, (gate_prep_speed hKw h).2, ?_⟩
  · have htow := gate_prep_towards h
    rcases star_sign_coord η with ⟨hs, _⟩ | ⟨hs, _⟩ <;> rw [hs] at htow ⊢
    · rw [abs_of_pos (by linarith), one_mul]
    · rw [abs_of_neg (by linarith)]; ring
  · rw [sq_abs]
    exact gate_prep_energy_mem h

/-- The distance still to be travelled before the junction boundary, signed by the germ. -/
theorem gate_prep_toGo (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {η : starGraph.EdgeEnd} {x p : ℝ × ℝ}
    (h : gateNetwork.Prepared (zeroPotential starGraph) K ε η x p)
    (hgo : 0 < gateNetwork.toGo ε η (gateNetwork.long η.1 x)) :
    ∃ d : ℝ, starTarget ε η - longComp η.1 x = EdgeEnd.sign starGraph η * d ∧
      0 < d ∧ d ≤ 1 := by
  have hq := gate_prep_long hε h
  have hQ := starTarget_mem hε (by linarith) η
  refine ⟨|starTarget ε η - longComp η.1 x|, ?_, ?_, ?_⟩
  · rcases star_sign_coord η with ⟨hs, hc⟩ | ⟨hs, hc⟩
    · have hQ' : starTarget ε η = 1 - 8 * ε := by rw [starTarget, hs, hc]; ring
      rw [hs, one_mul, abs_of_nonneg (by rw [hQ']; linarith [hq.2])]
    · have hQ' : starTarget ε η = 8 * ε := by rw [starTarget, hs, hc]; ring
      rw [hs, abs_of_nonpos (by rw [hQ']; linarith [hq.1])]; ring
  · rw [gateNetwork_toGo hε, gateNetwork_long] at hgo; exact hgo
  · rw [abs_le]
    exact ⟨by linarith [hq.2, hQ.1], by linarith [hq.1, hQ.2]⟩

/-! ### Exactly free motion along a through flight -/

variable {Θ : gateNetwork.MicroTrajectory ε S}

/-- **A through flight of the gated model is exactly free.**  The whole flight lives on one side
of the gate — in `(2ε, 1)` on the edge `1` and in `(-1, -2ε)` on the edge `0` — and `gatePot ε`
is flat on both. -/
theorem gate_free_through (hε : 0 < ε) {c : ℝ} (hth : GateThrough ε c S Θ)
    {η : starGraph.EdgeEnd} (hne : η.1 ≠ 2) {a b : ℝ}
    (hamem : a ∈ Icc (0 : ℝ) S) (hbmem : b ∈ Icc (0 : ℝ) S) (hab : a ≤ b)
    (h1 : longComp η.1 (Θ.x a) ∈ Icc (8 * ε) (1 - 8 * ε))
    (h2 : longComp η.1 (Θ.x a) + longComp η.1 (Θ.p a) * (b - a) ∈ Icc (8 * ε) (1 - 8 * ε)) :
    ∀ t ∈ Icc a b, (Θ.x t).1 = (Θ.x a).1 + (Θ.p a).1 * (t - a) ∧ (Θ.p t).1 = (Θ.p a).1 := by
  have hxa : (Θ.x a).1 = ThroughRun.embedSign η.1 * longComp η.1 (Θ.x a) :=
    fst_eq_of_longComp hne _
  have hpa : (Θ.p a).1 = ThroughRun.embedSign η.1 * longComp η.1 (Θ.p a) :=
    fst_eq_of_longComp hne _
  have hV : (Θ.x a).1 + (Θ.p a).1 * (b - a)
      = ThroughRun.embedSign η.1 *
        (longComp η.1 (Θ.x a) + longComp η.1 (Θ.p a) * (b - a)) := by
    rw [hxa, hpa]; ring
  rcases embedSign_eq_or η.1 with hs | hs
  · refine hth.gate.free_right_of_endpoints hamem hbmem hab ?_ ?_
    · rw [hxa, hs, one_mul]
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    · rw [hV, hs, one_mul]
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · refine hth.gate.free_left_of_endpoints hamem hbmem hab ?_ ?_
    · rw [hxa, hs]
      exact ⟨by linarith [h1.2], by linarith [h1.1]⟩
    · rw [hV, hs]
      exact ⟨by linarith [h2.2], by linarith [h2.1]⟩

/-! ### The edge flight in the two channels -/

/-- **The edge flight in the gated through channel.** -/
theorem gate_through_edgeFlight (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {c : ℝ} (hth : GateThrough ε c S Θ)
    {η : starGraph.EdgeEnd} (hne : η.1 ≠ 2) {a : ℝ} (ha : 0 ≤ a) (haS : a + 2 ≤ S)
    (hp : gateNetwork.Prepared (zeroPotential starGraph) K ε η (Θ.x a) (Θ.p a))
    (hgo : 0 < gateNetwork.toGo ε η (gateNetwork.long η.1 (Θ.x a))) :
    ∃ b, gateNetwork.EdgeFlight (zeroPotential starGraph) K ε η Θ.x Θ.p a b := by
  obtain ⟨r, hpa, hr1, hr2, hrK⟩ := gate_prep_mom hKw hp
  obtain ⟨d, hdq, hd0, hd1⟩ := gate_prep_toGo hε hεs hp hgo
  have hr0 : (0 : ℝ) < r := by linarith
  have hq₀mem := gate_prep_long hε hp
  have hQmem := starTarget_mem hε (by linarith) η
  have hdr : d / r ≤ 1 := by rw [div_le_one hr0]; linarith
  have hab : a < a + d / r := by have := div_pos hd0 hr0; linarith
  have hble : a + d / r ≤ a + 2 := by linarith
  have hQeq : longComp η.1 (Θ.x a)
      + EdgeEnd.sign starGraph η * r * (a + d / r - a) = starTarget ε η := by
    have h1 : a + d / r - a = d / r := by ring
    have h2 : r * (d / r) = d := by field_simp
    rw [h1, mul_assoc, h2]
    linarith [hdq]
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hbmem : a + d / r ∈ Icc (0 : ℝ) S := ⟨by linarith, by linarith⟩
  have hQ2 : longComp η.1 (Θ.x a) + longComp η.1 (Θ.p a) * (a + d / r - a)
      ∈ Icc (8 * ε) (1 - 8 * ε) := by
    rw [hpa, hQeq]
    exact hQmem
  have hfreeu := gate_free_through hε hth hne hamem hbmem hab.le hq₀mem hQ2
  have hsub : Icc a (a + d / r) ⊆ Icc (0 : ℝ) S := Icc_subset_Icc ha (by linarith)
  have hLu : ∀ t : ℝ, longComp η.1 (Θ.x t) = ThroughRun.embedSign η.1 * (Θ.x t).1 :=
    fun t => longComp_of_ne_two hne _
  have hLp : ∀ t : ℝ, longComp η.1 (Θ.p t) = ThroughRun.embedSign η.1 * (Θ.p t).1 :=
    fun t => longComp_of_ne_two hne _
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
  refine ⟨a + d / r, gate_mk_edgeFlight hε hεs hr1 hrK hab ha (by linarith) hq₀mem hQeq hfree
    ?_ ?_⟩
  · intro t ht
    rw [transComp_of_ne_two hne]
    exact (hth.abs_trans_lt hε hεs (hsub ht)).le
  · intro t ht
    simp only [transComp_of_ne_two hne]
    exact hth.trans_le t (hsub ht)

/-- **The edge flight in the third arm** — identical to the ungated one. -/
theorem gate_arm_edgeFlight (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {c : ℝ} (harm : GateArm ε c S Θ)
    {η : starGraph.EdgeEnd} (heq : η.1 = 2) {a : ℝ} (ha : 0 ≤ a) (haS : a + 2 ≤ S)
    (hp : gateNetwork.Prepared (zeroPotential starGraph) K ε η (Θ.x a) (Θ.p a))
    (hgo : 0 < gateNetwork.toGo ε η (gateNetwork.long η.1 (Θ.x a))) :
    ∃ b, gateNetwork.EdgeFlight (zeroPotential starGraph) K ε η Θ.x Θ.p a b := by
  obtain ⟨r, hpa, hr1, hr2, hrK⟩ := gate_prep_mom hKw hp
  obtain ⟨d, hdq, hd0, hd1⟩ := gate_prep_toGo hε hεs hp hgo
  have hr0 : (0 : ℝ) < r := by linarith
  have hq₀mem := gate_prep_long hε hp
  have hQmem := starTarget_mem hε (by linarith) η
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
  refine ⟨a + d / r, gate_mk_edgeFlight hε hεs hr1 hrK hab ha (by linarith) hq₀mem hQeq hfree
    ?_ ?_⟩
  · intro t ht
    rw [htc]
    exact (harm.abs_trans_lt hε hεs (hsub ht)).le
  · intro t ht
    simp only [htc]
    exact harm.trans_le t (hsub ht)

/-! ### The edge-reduction hypothesis -/

/-- **The gated three-channel junction satisfies the edge-reduction hypothesis on every energy
window `K ⊆ [1/2, 2]`.**  The gate never acts during a flight, so the longitudinal force
vanishes and (E3) holds with `γ_ε = 0`. -/
theorem gateNetwork_satisfiesEdgeReduction (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) :
    gateNetwork.SatisfiesEdgeReduction (zeroPotential starGraph) K (1 / 100) := by
  intro ε hε η x p hp hna
  have hε0 : 0 < ε := hε.1
  have hεs : ε ≤ 1 / 100 := le_of_lt hε.2
  -- the flow through `(x, p)` on `[0, 2]`
  set Θ := gateNetwork.flowTraj ε (x, p) 2 with hΘ
  have h₀ : gateNetwork.Prepared (zeroPotential starGraph) K ε η (Θ.x 0) (Θ.p 0) := by
    rw [hΘ, ThinHamiltonianNetwork.flowTraj_x_zero, ThinHamiltonianNetwork.flowTraj_p_zero]
    exact hp
  have hgo : 0 < gateNetwork.toGo ε η (gateNetwork.long η.1 (Θ.x 0)) := by
    rw [hΘ, ThinHamiltonianNetwork.flowTraj_x_zero]
    exact ThinHamiltonianNetwork.toGo_pos_of_not_arriving hp hna
  have hS : (0 : ℝ) ≤ 2 := by norm_num
  by_cases h2 : η.1 = 2
  · exact gate_arm_edgeFlight hε0 hεs hKw (gate_arm Θ hε0 hεs hS hKw h2 h₀) h2 le_rfl
      (by norm_num) h₀ hgo
  · exact gate_through_edgeFlight hε0 hεs hKw (gate_through Θ hε0 hεs hS hKw h2 h₀) h2 le_rfl
      (by norm_num) h₀ hgo

end HamiltonianMetricGraphs
