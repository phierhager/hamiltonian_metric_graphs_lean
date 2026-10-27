/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.GateEdge

/-!
# The junction-scattering hypothesis for the gated junction, in the two energy regimes

This is the mathematical heart of the energy-dependent example.  **One and the same** microscopic
Hamiltonian family `H_ε = ½|p|² + gatePot2 ε` produces two *different* deterministic routing laws
on two disjoint compact energy windows:

* on `K₋ = [1/2, 3/5]`, every longitudinal energy is `< g₀ = gateHeight = 7/10`, so a particle
  arriving at the branching vertex along a through channel is turned back by the gate
  (`GateSolution.reflect_gate_left` / `reflect_gate_right`).  Every germ is routed to itself, and
  the limiting law is total reflection `F₋ = RoutingLaw.reflection Γ⋆`;
* on `K₊ = [3/2, 2]`, every longitudinal energy is `≥ 3/2 > 1.365 > E_c = max G_ε`, so the
  particle crosses the junction freely (`GateSolution.cross_gate_right` / `cross_gate_left`) and
  emerges in the opposite through channel.  The limiting law is `F₊ = F⋆`, the transmitting law of
  `BranchingGraph.lean`.

The other three passages — the two outer caps and the third arm — are **identical** in the two
regimes: their barriers have height `4`, above every energy of `[1/2, 2]`.  They are therefore
proved once, for an arbitrary routing law `F` with `F(η) = η` at the germ in question.

In all cases the outgoing longitudinal momentum equals the routed momentum **exactly**
(`momErr = 0`) and the physical residence time is at most `θ_ε = 32ε = dwell ε`: the caps take
`< 23ε`, the arm barrier `< 9ε`, the gate reflection `< 26ε` and the gate crossing `≤ 32ε`, as
in the proof of Theorem IX.10.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {ε S : ℝ} {K : Set ℝ}

/-! ### The speed along a gated trajectory -/

variable {Θ : gateNetwork.MicroTrajectory ε S}

theorem gate_arriving_boundary (hε : 0 < ε) {η : starGraph.EdgeEnd} {x p : ℝ × ℝ}
    (h : gateNetwork.Arriving (zeroPotential starGraph) K ε η x p) :
    longComp η.1 x = starTarget ε η := by
  have h1 := h.boundary
  rw [gateNetwork_long, gateNetwork_offset_of_pos hε] at h1
  exact h1

/-- Outside the gate and inside the closed edge the through-channel speed is exactly the nominal
speed `c`. -/
theorem GateThrough.speed_eq {c : ℝ} (h : GateThrough ε c S Θ) (hε : 0 < ε)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) S) (h1 : 2 * ε ≤ |(Θ.x a).1|) (h2 : |(Θ.x a).1| ≤ 1) :
    |(Θ.p a).1| = c := by
  have hen : (Θ.p a).1 ^ 2 / 2 + gatePot ε ((Θ.x a).1) = c ^ 2 / 2 := h.gate.energy a ha
  have hgate : gatePot ε ((Θ.x a).1) = 0 := gatePot_of_mem hε h1 h2
  have hc0 : (0 : ℝ) < c := h.gate.c_pos
  have hsq : (Θ.p a).1 ^ 2 = c ^ 2 := by
    rw [hgate] at hen
    linarith
  calc |(Θ.p a).1| = Real.sqrt ((Θ.p a).1 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt (c ^ 2) := by rw [hsq]
    _ = c := Real.sqrt_sq hc0.le

/-- Between the two barriers the arm speed is exactly the nominal speed `c`. -/
theorem GateArm.speed_eq {c : ℝ} (h : GateArm ε c S Θ) (hε : 0 < ε)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) S) (h1 : 7 * ε ≤ (Θ.x a).2) (h2 : (Θ.x a).2 ≤ 1) :
    |(Θ.p a).2| = c := by
  have hen : (Θ.p a).2 ^ 2 / 2 + armPot ε ((Θ.x a).2) = c ^ 2 / 2 := h.arm.energy a ha
  have harm : armPot ε ((Θ.x a).2) = 0 := by
    rw [armPot_eq_wall, wallPot_of_nonpos hε (by linarith : 7 * ε - (Θ.x a).2 ≤ 0),
      wallPot_of_nonpos hε (by linarith : (Θ.x a).2 - 1 ≤ 0), add_zero]
  have hc0 : (0 : ℝ) < c := h.arm.c_pos
  have hsq : (Θ.p a).2 ^ 2 = c ^ 2 := by
    rw [harm] at hen
    linarith
  calc |(Θ.p a).2| = Real.sqrt ((Θ.p a).2 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt (c ^ 2) := by rw [hsq]
    _ = c := Real.sqrt_sq hc0.le

/-! ### The generic junction passage -/

/-- **A departing state of the gated network.** -/
theorem gate_mk_departing (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {ζ : starGraph.EdgeEnd}
    {x p : ℝ × ℝ} {r : ℝ} (hr1 : 1 ≤ r) (hrK : r ^ 2 / 2 ∈ K)
    (hx : longComp ζ.1 x = starTarget ε ζ)
    (hpz : longComp ζ.1 p = -EdgeEnd.sign starGraph ζ * r)
    (htr : |transComp ζ.1 x| ≤ 2 * ε)
    (hte : transComp ζ.1 p ^ 2 / 2 + wellPot ε (transComp ζ.1 x) ≤ ε) :
    gateNetwork.Departing (zeroPotential starGraph) K ε ζ x p := by
  have hsq : EdgeEnd.sign starGraph ζ ^ 2 = 1 := starGraph.edgeEnd_sign_sq ζ
  have hQmem := starTarget_mem hε (by linarith) ζ
  have hr0 : (0 : ℝ) < r := by linarith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [gateNetwork_long, gateNetwork_offset_of_pos hε, starGraph_length]
    simp only [otherEnd_fst]
    rw [hx]
    exact hQmem
  · rw [gateNetwork_trans, gateNetwork_tubeWidth_of_pos hε]
    simp only [otherEnd_fst]
    exact htr
  · rw [gateNetwork_transEnergy, gateNetwork_transErr_of_pos hε]
    simp only [otherEnd_fst]
    exact hte
  · rw [gateNetwork_longP, sign_otherEnd]
    simp only [otherEnd_fst]
    rw [hpz]
    nlinarith
  · have hkey : (-EdgeEnd.sign starGraph ζ * r) ^ 2 = r ^ 2 := by
      rw [neg_mul, neg_sq, mul_pow, hsq, one_mul]
    rw [gateNetwork_long, gateNetwork_longP, zeroPotential_hamiltonian]
    simp only [otherEnd_fst]
    rw [hpz, hkey]
    exact hrK
  · rw [gateNetwork_long, gateNetwork_offset_of_pos hε]
    exact hx

/-- **A junction passage of the gated network.**  The graph momentum law is exact: the outgoing
longitudinal momentum equals `F`'s departure momentum with error `0`. -/
theorem gate_mk_junctionPassage (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    {F : RoutingLaw starGraph} {η ζ : starGraph.EdgeEnd} {a b c : ℝ}
    (hc1 : 1 ≤ c) (hcK : c ^ 2 / 2 ∈ K)
    (hab : a < b) (hble : b ≤ a + 32 * ε) (hζ : F.routeGerm η = ζ)
    (hpa : longComp η.1 (Θ.p a) = EdgeEnd.sign starGraph η * c)
    (hx : longComp ζ.1 (Θ.x b) = starTarget ε ζ)
    (hpb : longComp ζ.1 (Θ.p b) = -EdgeEnd.sign starGraph ζ * c)
    (htr : |transComp ζ.1 (Θ.x b)| ≤ 2 * ε)
    (hte : transComp ζ.1 (Θ.p b) ^ 2 / 2 + wellPot ε (transComp ζ.1 (Θ.x b)) ≤ ε) :
    gateNetwork.JunctionPassage (zeroPotential starGraph) K F.routeGerm ε η Θ.x Θ.p a b := by
  subst hζ
  refine ⟨hab, ?_, gate_mk_departing hε hεs hc1 hcK hx hpb htr hte, ?_⟩
  · rw [gateNetwork_dwell_of_pos hε]; exact hble
  · rw [gateNetwork_momErr, gateNetwork_longP, gateNetwork_longP, hpa, hpb, abs_mul,
      star_abs_sign, one_mul, abs_of_pos (by linarith : (0 : ℝ) < c)]
    simp

/-! ### Reading off the arrival data -/

/-- The nominal speed of a trajectory equals the arriving longitudinal speed, and its energy lies
in the window. -/
theorem gate_arr_mom (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {η : starGraph.EdgeEnd} {a c : ℝ}
    (hprep : gateNetwork.Prepared (zeroPotential starGraph) K ε η (Θ.x a) (Θ.p a))
    (hspeed : |longComp η.1 (Θ.p a)| = c) :
    longComp η.1 (Θ.p a) = EdgeEnd.sign starGraph η * c ∧ c ^ 2 / 2 ∈ K := by
  obtain ⟨r, hr, hr1, hr2, hrK⟩ := gate_prep_mom hKw hprep
  have hrc : r = c := by
    have hval : |longComp η.1 (Θ.p a)| = r := by
      rw [hr, abs_mul, star_abs_sign, one_mul, abs_of_nonneg (by linarith)]
    rw [hspeed] at hval
    exact hval.symm
  rw [hrc] at hr hrK
  exact ⟨hr, hrK⟩

/-! ### The passages that do not see the gate -/

/-- **The outer reflection of the through channel.**  The cap at `u = ±1` reverses the momentum
exactly, within `23ε`.  The gate plays no role: this is the forced identity
routing at a valence-1 vertex, and it holds in *both* energy regimes. -/
theorem gate_junction_through_outer (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {c : ℝ} (hth : GateThrough ε c S Θ)
    {F : RoutingLaw starGraph} {η : starGraph.EdgeEnd} (hne : η.1 ≠ 2) (hb2 : η.2 = true)
    (hζ : F.routeGerm η = η) {a : ℝ} (ha : 0 ≤ a) (haS : a + 32 * ε ≤ S)
    (harr : gateNetwork.Arriving (zeroPotential starGraph) K ε η (Θ.x a) (Θ.p a)) :
    ∃ b, gateNetwork.JunctionPassage (zeroPotential starGraph) K F.routeGerm ε η Θ.x Θ.p a b := by
  have hc1 : 1 ≤ c := hth.gate.c_ge
  have hc2 : c ≤ 2 := hth.gate.c_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hssq : ThroughRun.embedSign η.1 * ThroughRun.embedSign η.1 = 1 := embedSign_sq η.1
  have hxa : longComp η.1 (Θ.x a) = 1 - 8 * ε := by
    rw [gate_arriving_boundary hε harr, starTarget_of_true hb2]
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hua : (Θ.x a).1 = ThroughRun.embedSign η.1 * (1 - 8 * ε) := by
    rw [fst_eq_of_longComp hne, hxa]
  have habsu : |(Θ.x a).1| = 1 - 8 * ε := by
    rw [hua, abs_mul, abs_embedSign, one_mul, abs_of_nonneg (by linarith)]
  have hspeed : |(Θ.p a).1| = c :=
    hth.speed_eq hε hamem (by rw [habsu]; linarith) (by rw [habsu]; linarith)
  have hlongspeed : |longComp η.1 (Θ.p a)| = c := by
    rw [abs_longComp_of_ne_two hne]; exact hspeed
  obtain ⟨hpa, hcK⟩ := gate_arr_mom hKw harr.prepared hlongspeed
  have hpua : (Θ.p a).1 = ThroughRun.embedSign η.1 * c := by
    rw [fst_eq_of_longComp hne, hpa, sign_of_true hb2]; ring
  -- the reflection, on whichever side of the gate the edge lies
  have hrefl : ∃ t₁ ∈ Ioo a (a + 23 * ε),
      (Θ.x t₁).1 = ThroughRun.embedSign η.1 * (1 - 8 * ε) ∧
      (Θ.p t₁).1 = -(ThroughRun.embedSign η.1 * c) := by
    rcases embedSign_eq_or η.1 with hs | hs
    · rw [hs] at hua hpua ⊢
      rw [one_mul] at hua hpua
      obtain ⟨t₁, ht₁, hu₁, hp₁⟩ := hth.gate.reflect_cap_right ha (by linarith) hua hpua
      exact ⟨t₁, ht₁, by rw [hu₁]; ring, by rw [hp₁]; ring⟩
    · rw [hs] at hua hpua ⊢
      have hua' : (Θ.x a).1 = -(1 - 8 * ε) := by rw [hua]; ring
      have hpua' : (Θ.p a).1 = -c := by rw [hpua]; ring
      obtain ⟨t₁, ht₁, hu₁, hp₁⟩ := hth.gate.reflect_cap_left ha (by linarith) hua' hpua'
      exact ⟨t₁, ht₁, by rw [hu₁]; ring, by rw [hp₁]; ring⟩
  obtain ⟨t₁, ht₁, hu₁, hp₁⟩ := hrefl
  have ht₁mem : t₁ ∈ Icc (0 : ℝ) S := ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
  refine ⟨t₁, gate_mk_junctionPassage hε hεs hc1 hcK ht₁.1 (by linarith [ht₁.2]) hζ hpa
    ?_ ?_ ?_ ?_⟩
  · rw [longComp_of_ne_two hne, starTarget_of_true hb2, hu₁]
    nlinarith [hssq]
  · rw [longComp_of_ne_two hne, sign_of_true hb2, hp₁]
    nlinarith [hssq]
  · rw [transComp_of_ne_two hne]
    exact (hth.abs_trans_lt hε hεs ht₁mem).le
  · simp only [transComp_of_ne_two hne]
    exact hth.trans_le t₁ ht₁mem

/-- **`η₃ ↦ η₃`: the junction barrier of the third arm.**  Its height `4` exceeds every energy of
`[1/2, 2]`, so this passage too is the same in both regimes. -/
theorem gate_junction_arm_inner (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {c : ℝ} (harm : GateArm ε c S Θ)
    {F : RoutingLaw starGraph} {η : starGraph.EdgeEnd} (heq : η.1 = 2) (hb2 : η.2 = false)
    (hζ : F.routeGerm η = η) {a : ℝ} (ha : 0 ≤ a) (haS : a + 32 * ε ≤ S)
    (harr : gateNetwork.Arriving (zeroPotential starGraph) K ε η (Θ.x a) (Θ.p a)) :
    ∃ b, gateNetwork.JunctionPassage (zeroPotential starGraph) K F.routeGerm ε η Θ.x Θ.p a b := by
  have hc1 : 1 ≤ c := harm.arm.c_ge
  have hc2 : c ≤ 2 := harm.arm.c_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hlc : ∀ z : ℝ × ℝ, longComp η.1 z = z.2 := by rw [heq]; exact fun z => longComp_two z
  have htc : ∀ z : ℝ × ℝ, transComp η.1 z = z.1 := by rw [heq]; exact fun z => transComp_two z
  have hxa : (Θ.x a).2 = 8 * ε := by
    rw [← hlc, gate_arriving_boundary hε harr, starTarget_of_false hb2]
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hspeed : |(Θ.p a).2| = c :=
    harm.speed_eq hε hamem (by rw [hxa]; linarith) (by rw [hxa]; linarith)
  have hlongspeed : |longComp η.1 (Θ.p a)| = c := by rw [hlc]; exact hspeed
  obtain ⟨hpa, hcK⟩ := gate_arr_mom hKw harr.prepared hlongspeed
  have hpwa : (Θ.p a).2 = -c := by
    have h := hpa
    rw [hlc, sign_of_false hb2] at h
    linarith
  obtain ⟨t₁, ht₁, hw₁, hp₁⟩ := harm.arm.reflect_junction ha (by linarith) hxa hpwa
  have ht₁mem : t₁ ∈ Icc (0 : ℝ) S := ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
  refine ⟨t₁, gate_mk_junctionPassage hε hεs hc1 hcK ht₁.1 (by linarith [ht₁.2]) hζ hpa
    ?_ ?_ ?_ ?_⟩
  · rw [hlc, starTarget_of_false hb2]
    exact hw₁
  · rw [hlc, sign_of_false hb2, show (Θ.p t₁).2 = c from hp₁]
    ring
  · rw [htc]
    exact (harm.abs_trans_lt hε hεs ht₁mem).le
  · simp only [htc]
    exact harm.trans_le t₁ ht₁mem

/-- **The outer reflection of the third arm.** -/
theorem gate_junction_arm_outer (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {c : ℝ} (harm : GateArm ε c S Θ)
    {F : RoutingLaw starGraph} {η : starGraph.EdgeEnd} (heq : η.1 = 2) (hb2 : η.2 = true)
    (hζ : F.routeGerm η = η) {a : ℝ} (ha : 0 ≤ a) (haS : a + 32 * ε ≤ S)
    (harr : gateNetwork.Arriving (zeroPotential starGraph) K ε η (Θ.x a) (Θ.p a)) :
    ∃ b, gateNetwork.JunctionPassage (zeroPotential starGraph) K F.routeGerm ε η Θ.x Θ.p a b := by
  have hc1 : 1 ≤ c := harm.arm.c_ge
  have hc2 : c ≤ 2 := harm.arm.c_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hlc : ∀ z : ℝ × ℝ, longComp η.1 z = z.2 := by rw [heq]; exact fun z => longComp_two z
  have htc : ∀ z : ℝ × ℝ, transComp η.1 z = z.1 := by rw [heq]; exact fun z => transComp_two z
  have hxa : (Θ.x a).2 = 1 - 8 * ε := by
    rw [← hlc, gate_arriving_boundary hε harr, starTarget_of_true hb2]
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hspeed : |(Θ.p a).2| = c :=
    harm.speed_eq hε hamem (by rw [hxa]; linarith) (by rw [hxa]; linarith)
  have hlongspeed : |longComp η.1 (Θ.p a)| = c := by rw [hlc]; exact hspeed
  obtain ⟨hpa, hcK⟩ := gate_arr_mom hKw harr.prepared hlongspeed
  have hpwa : (Θ.p a).2 = c := by
    have h := hpa
    rw [hlc, sign_of_true hb2] at h
    linarith
  obtain ⟨t₁, ht₁, hw₁, hp₁⟩ := harm.arm.reflect_cap ha (by linarith) hxa hpwa
  have ht₁mem : t₁ ∈ Icc (0 : ℝ) S := ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
  refine ⟨t₁, gate_mk_junctionPassage hε hεs hc1 hcK ht₁.1 (by linarith [ht₁.2]) hζ hpa
    ?_ ?_ ?_ ?_⟩
  · rw [hlc, starTarget_of_true hb2]
    exact hw₁
  · rw [hlc, sign_of_true hb2, show (Θ.p t₁).2 = -c from hp₁]
    ring
  · rw [htc]
    exact (harm.abs_trans_lt hε hεs ht₁mem).le
  · simp only [htc]
    exact harm.trans_le t₁ ht₁mem

/-! ### The gate: the low-energy regime -/

/-- **`η ↦ η` below the gate.**  A particle arriving at the branching vertex along a through
channel with longitudinal energy below `gateHeight` cannot cross the gate: it is turned around
exactly, at the junction boundary it started from, within `26ε`. -/
theorem gate_junction_through_inner_low (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {c : ℝ} (hth : GateThrough ε c S Θ)
    (hlow : c ^ 2 / 2 < gateHeight)
    {F : RoutingLaw starGraph} {η : starGraph.EdgeEnd} (hne : η.1 ≠ 2) (hb2 : η.2 = false)
    (hζ : F.routeGerm η = η) {a : ℝ} (ha : 0 ≤ a) (haS : a + 32 * ε ≤ S)
    (harr : gateNetwork.Arriving (zeroPotential starGraph) K ε η (Θ.x a) (Θ.p a)) :
    ∃ b, gateNetwork.JunctionPassage (zeroPotential starGraph) K F.routeGerm ε η Θ.x Θ.p a b := by
  have hc1 : 1 ≤ c := hth.gate.c_ge
  have hc2 : c ≤ 2 := hth.gate.c_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hssq : ThroughRun.embedSign η.1 * ThroughRun.embedSign η.1 = 1 := embedSign_sq η.1
  have hxa : longComp η.1 (Θ.x a) = 8 * ε := by
    rw [gate_arriving_boundary hε harr, starTarget_of_false hb2]
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hua : (Θ.x a).1 = ThroughRun.embedSign η.1 * (8 * ε) := by
    rw [fst_eq_of_longComp hne, hxa]
  have habsu : |(Θ.x a).1| = 8 * ε := by
    rw [hua, abs_mul, abs_embedSign, one_mul, abs_of_nonneg (by linarith)]
  have hspeed : |(Θ.p a).1| = c :=
    hth.speed_eq hε hamem (by rw [habsu]; linarith) (by rw [habsu]; linarith)
  have hlongspeed : |longComp η.1 (Θ.p a)| = c := by
    rw [abs_longComp_of_ne_two hne]; exact hspeed
  obtain ⟨hpa, hcK⟩ := gate_arr_mom hKw harr.prepared hlongspeed
  have hpua : (Θ.p a).1 = -(ThroughRun.embedSign η.1 * c) := by
    rw [fst_eq_of_longComp hne, hpa, sign_of_false hb2]; ring
  have hrefl : ∃ t₁ ∈ Ioo a (a + 26 * ε),
      (Θ.x t₁).1 = ThroughRun.embedSign η.1 * (8 * ε) ∧
      (Θ.p t₁).1 = ThroughRun.embedSign η.1 * c := by
    rcases embedSign_eq_or η.1 with hs | hs
    · rw [hs] at hua hpua ⊢
      rw [one_mul] at hua
      have hpua' : (Θ.p a).1 = -c := by rw [hpua]; ring
      obtain ⟨t₁, ht₁, hu₁, hp₁⟩ :=
        hth.gate.reflect_gate_right ha (by linarith) hlow hua hpua'
      exact ⟨t₁, ht₁, by rw [hu₁]; ring, by rw [hp₁]; ring⟩
    · rw [hs] at hua hpua ⊢
      have hua' : (Θ.x a).1 = -(8 * ε) := by rw [hua]; ring
      have hpua' : (Θ.p a).1 = c := by rw [hpua]; ring
      obtain ⟨t₁, ht₁, hu₁, hp₁⟩ :=
        hth.gate.reflect_gate_left ha (by linarith) hlow hua' hpua'
      exact ⟨t₁, ht₁, by rw [hu₁]; ring, by rw [hp₁]; ring⟩
  obtain ⟨t₁, ht₁, hu₁, hp₁⟩ := hrefl
  have ht₁mem : t₁ ∈ Icc (0 : ℝ) S := ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
  refine ⟨t₁, gate_mk_junctionPassage hε hεs hc1 hcK ht₁.1 (by linarith [ht₁.2]) hζ hpa
    ?_ ?_ ?_ ?_⟩
  · rw [longComp_of_ne_two hne, starTarget_of_false hb2, hu₁]
    nlinarith [hssq]
  · rw [longComp_of_ne_two hne, sign_of_false hb2, hp₁]
    nlinarith [hssq]
  · rw [transComp_of_ne_two hne]
    exact (hth.abs_trans_lt hε hεs ht₁mem).le
  · simp only [transComp_of_ne_two hne]
    exact hth.trans_le t₁ ht₁mem

/-! ### The gate: the high-energy regime -/

/-- **`η₁ ↦ η₂`, `η₂ ↦ η₁` above the gate.**  A particle arriving at the branching vertex along a
through channel with longitudinal energy at least `3/2 > 1.365 > E_c` keeps a speed above
`1/2` throughout the junction, crosses it in time at most `32ε`, and emerges at the junction
boundary of the *opposite* through channel with exactly its incoming speed. -/
theorem gate_junction_through_inner_high (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    (hKw : K ⊆ Icc (1 / 2 : ℝ) 2) {c : ℝ} (hth : GateThrough ε c S Θ)
    (hhigh : 3 / 2 ≤ c ^ 2 / 2)
    {η : starGraph.EdgeEnd} (hne : η.1 ≠ 2) (hb2 : η.2 = false)
    {a : ℝ} (ha : 0 ≤ a) (haS : a + 32 * ε ≤ S)
    (harr : gateNetwork.Arriving (zeroPotential starGraph) K ε η (Θ.x a) (Θ.p a)) :
    ∃ b, gateNetwork.JunctionPassage (zeroPotential starGraph) K starRouting.routeGerm ε η
      Θ.x Θ.p a b := by
  have hc1 : 1 ≤ c := hth.gate.c_ge
  have hc2 : c ≤ 2 := hth.gate.c_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hssq : ThroughRun.embedSign η.1 * ThroughRun.embedSign η.1 = 1 := embedSign_sq η.1
  have hxa : longComp η.1 (Θ.x a) = 8 * ε := by
    rw [gate_arriving_boundary hε harr, starTarget_of_false hb2]
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hua : (Θ.x a).1 = ThroughRun.embedSign η.1 * (8 * ε) := by
    rw [fst_eq_of_longComp hne, hxa]
  have habsu : |(Θ.x a).1| = 8 * ε := by
    rw [hua, abs_mul, abs_embedSign, one_mul, abs_of_nonneg (by linarith)]
  have hspeed : |(Θ.p a).1| = c :=
    hth.speed_eq hε hamem (by rw [habsu]; linarith) (by rw [habsu]; linarith)
  have hlongspeed : |longComp η.1 (Θ.p a)| = c := by
    rw [abs_longComp_of_ne_two hne]; exact hspeed
  obtain ⟨hpa, hcK⟩ := gate_arr_mom hKw harr.prepared hlongspeed
  have hpua : (Θ.p a).1 = -(ThroughRun.embedSign η.1 * c) := by
    rw [fst_eq_of_longComp hne, hpa, sign_of_false hb2]; ring
  -- the crossing
  have hcross : ∃ t₁ ∈ Ioo a (a + 32 * ε),
      (Θ.x t₁).1 = -(ThroughRun.embedSign η.1 * (8 * ε)) ∧
      (Θ.p t₁).1 = -(ThroughRun.embedSign η.1 * c) := by
    rcases embedSign_eq_or η.1 with hs | hs
    · rw [hs] at hua hpua ⊢
      rw [one_mul] at hua
      have hpua' : (Θ.p a).1 = -c := by rw [hpua]; ring
      obtain ⟨t₁, ht₁, hu₁, hp₁⟩ :=
        hth.gate.cross_gate_left ha (by linarith) hhigh hua hpua'
      exact ⟨t₁, ht₁, by rw [hu₁]; ring, by rw [hp₁]; ring⟩
    · rw [hs] at hua hpua ⊢
      have hua' : (Θ.x a).1 = -(8 * ε) := by rw [hua]; ring
      have hpua' : (Θ.p a).1 = c := by rw [hpua]; ring
      obtain ⟨t₁, ht₁, hu₁, hp₁⟩ :=
        hth.gate.cross_gate_right ha (by linarith) hhigh hua' hpua'
      exact ⟨t₁, ht₁, by rw [hu₁]; ring, by rw [hp₁]; ring⟩
  obtain ⟨t₁, ht₁, hu₁, hp₁⟩ := hcross
  have ht₁mem : t₁ ∈ Icc (0 : ℝ) S := ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
  -- the outgoing channel
  have hζ : starRouting.routeGerm η = (swapEdge η.1, false) := starRouteGerm_of_false hb2
  have hζne : (starRouting.routeGerm η).1 ≠ 2 := by rw [hζ]; exact swapEdge_ne_two hne
  have hζs : ThroughRun.embedSign (starRouting.routeGerm η).1 = -ThroughRun.embedSign η.1 := by
    rw [hζ]; exact embedSign_swapEdge hne
  have hζ2 : (starRouting.routeGerm η).2 = false := by rw [hζ]
  refine ⟨t₁, gate_mk_junctionPassage hε hεs hc1 hcK ht₁.1 (by linarith [ht₁.2]) rfl hpa
    ?_ ?_ ?_ ?_⟩
  · rw [longComp_of_ne_two hζne, hζs, hu₁, starTarget_of_false hζ2]
    nlinarith [hssq]
  · rw [longComp_of_ne_two hζne, hζs, hp₁, sign_of_false hζ2]
    nlinarith [hssq]
  · rw [transComp_of_ne_two hζne]
    exact (hth.abs_trans_lt hε hεs ht₁mem).le
  · simp only [transComp_of_ne_two hζne]
    exact hth.trans_le t₁ ht₁mem

/-! ### The two junction-scattering hypotheses -/

/-- The routed germ of the arm channel is the arm channel itself, for `F⋆`. -/
theorem starRouteGerm_arm {η : starGraph.EdgeEnd} (heq : η.1 = 2) (hb2 : η.2 = false) :
    starRouting.routeGerm η = η := by
  rw [starRouteGerm_of_false hb2, heq]
  exact Prod.ext (by rw [heq]; rfl) (by rw [hb2])

/-- **Below the gate the junction reflects: the limiting law is total reflection `F₋`.**
Every microscopic state arriving at any junction of `Γ⋆` with longitudinal energy in
`K₋ = [1/2, 3/5]` leaves it through the germ it came from, after a residence time at most
`θ_ε = 32ε`, with exactly reversed speed. -/
theorem gateNetwork_junctionScattering_low :
    gateNetwork.JunctionScatteringConvergesTo (zeroPotential starGraph) windowLow
      (RoutingLaw.reflection starGraph) (1 / 100) := by
  intro ε hε η x p harr₀
  have hε0 : 0 < ε := hε.1
  have hεs : ε ≤ 1 / 100 := le_of_lt hε.2
  have hKw := windowLow_subset
  -- the flow through `(x, p)` on `[0, 1]`, which contains the junction window `[0, 32ε]`
  set Θ := gateNetwork.flowTraj ε (x, p) 1 with hΘ
  have harr : gateNetwork.Arriving (zeroPotential starGraph) windowLow ε η (Θ.x 0) (Θ.p 0) := by
    rw [hΘ, ThinHamiltonianNetwork.flowTraj_x_zero, ThinHamiltonianNetwork.flowTraj_p_zero]
    exact harr₀
  have hS : (0 : ℝ) ≤ 1 := by norm_num
  have haS : (0 : ℝ) + 32 * ε ≤ 1 := by linarith
  have hamem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, hS⟩
  have hζ : ∀ ζ : starGraph.EdgeEnd, (RoutingLaw.reflection starGraph).routeGerm ζ = ζ :=
    fun ζ => rfl
  by_cases h2 : η.1 = 2
  · have harm := gate_arm Θ hε0 hεs hS hKw h2 harr.prepared
    rcases hb2 : η.2 with _ | _
    · exact gate_junction_arm_inner hε0 hεs hKw harm h2 hb2 (hζ η) le_rfl haS harr
    · exact gate_junction_arm_outer hε0 hεs hKw harm h2 hb2 (hζ η) le_rfl haS harr
  · have hth := gate_through Θ hε0 hεs hS hKw h2 harr.prepared
    -- the nominal energy of the trajectory is the arriving energy, hence below the gate
    rcases hb2 : η.2 with _ | _
    · have hlow : |(Θ.p 0).1| ^ 2 / 2 < gateHeight := by
        have hlongspeed : |longComp η.1 (Θ.p 0)| = |(Θ.p 0).1| := by
          rw [abs_longComp_of_ne_two h2]
        obtain ⟨-, hcK⟩ := gate_arr_mom hKw harr.prepared hlongspeed
        exact windowLow_lt_gateHeight hcK
      exact gate_junction_through_inner_low hε0 hεs hKw hth hlow h2 hb2 (hζ η) le_rfl haS harr
    · exact gate_junction_through_outer hε0 hεs hKw hth h2 hb2 (hζ η) le_rfl haS harr

/-- **Above the gate the junction transmits: the limiting law is `F⋆`.**
Every microscopic state arriving at the branching vertex along a through channel with
longitudinal energy in `K₊ = [3/2, 2]` crosses the gate and leaves through the *opposite*
through channel; the third arm and the outer caps still reflect. -/
theorem gateNetwork_junctionScattering_high :
    gateNetwork.JunctionScatteringConvergesTo (zeroPotential starGraph) windowHigh
      starRouting (1 / 100) := by
  intro ε hε η x p harr₀
  have hε0 : 0 < ε := hε.1
  have hεs : ε ≤ 1 / 100 := le_of_lt hε.2
  have hKw := windowHigh_subset
  -- the flow through `(x, p)` on `[0, 1]`, which contains the junction window `[0, 32ε]`
  set Θ := gateNetwork.flowTraj ε (x, p) 1 with hΘ
  have harr : gateNetwork.Arriving (zeroPotential starGraph) windowHigh ε η (Θ.x 0) (Θ.p 0) := by
    rw [hΘ, ThinHamiltonianNetwork.flowTraj_x_zero, ThinHamiltonianNetwork.flowTraj_p_zero]
    exact harr₀
  have hS : (0 : ℝ) ≤ 1 := by norm_num
  have haS : (0 : ℝ) + 32 * ε ≤ 1 := by linarith
  by_cases h2 : η.1 = 2
  · have harm := gate_arm Θ hε0 hεs hS hKw h2 harr.prepared
    rcases hb2 : η.2 with _ | _
    · exact gate_junction_arm_inner hε0 hεs hKw harm h2 hb2
        (starRouteGerm_arm h2 hb2) le_rfl haS harr
    · exact gate_junction_arm_outer hε0 hεs hKw harm h2 hb2
        (starRouteGerm_of_true hb2) le_rfl haS harr
  · have hth := gate_through Θ hε0 hεs hS hKw h2 harr.prepared
    rcases hb2 : η.2 with _ | _
    · have hhigh : 3 / 2 ≤ |(Θ.p 0).1| ^ 2 / 2 := by
        have hlongspeed : |longComp η.1 (Θ.p 0)| = |(Θ.p 0).1| := by
          rw [abs_longComp_of_ne_two h2]
        obtain ⟨-, hcK⟩ := gate_arr_mom hKw harr.prepared hlongspeed
        exact windowHigh_ge hcK
      exact gate_junction_through_inner_high hε0 hεs hKw hth hhigh h2 hb2 le_rfl haS harr
    · exact gate_junction_through_outer hε0 hεs hKw hth h2 hb2
        (starRouteGerm_of_true hb2) le_rfl haS harr

end HamiltonianMetricGraphs
