/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.StarEdge
import HamiltonianMetricGraphs.Realization.ArmDynamics

/-!
# The junction-scattering hypothesis for the explicit three-channel junction

This file discharges `JunctionScatteringConvergesTo starRouting` for the explicit star network:
every microscopic state arriving at a junction boundary leaves it through the channel prescribed
by `F⋆`, after a physical residence time `O(ε)`, with the momentum reversed exactly.

There are four kinds of passage, and each is a theorem about the Hamiltonian flow:

* **`η₁ ↦ η₂` and `η₂ ↦ η₁`** — a particle arriving at the branching vertex along the through
  channel crosses the junction region `|u| ≤ 8ε` *freely*, because `capPot ε` vanishes on the
  whole closed edge; it therefore emerges on the other side, at `|u| = 8ε` with unchanged
  momentum.  The residence time is `16ε / c ≤ 16 ε`.
* **`η₃ ↦ η₃`** — a particle arriving along the third arm meets the junction barrier at
  `w ≈ 7ε`, whose height `4` exceeds every energy of `K⋆`, and is turned around exactly
  (`ArmMotion.reflect_junction`).  The residence time is `< 2ε/c + 7ε ≤ 9ε` (Lemma IX.8 with
  `d = ε`).
* the two **outer reflections**, at the caps of the through channel (`CapMotion.reflect`) and
  of the arm (`ArmMotion.reflect_cap`), which realize the forced identity routing at the
  valence-1 vertices.  The residence time is `< 16ε/c + 7ε ≤ 23ε` (Lemma IX.8 with `d = 8ε`).

All residence times are therefore below `θ_ε = 23ε`, the dwell bound of `starNetwork`, exactly as
in the proof of Theorem IX.9.

In all four cases the outgoing longitudinal momentum equals the routed momentum **exactly**, so
the model's `μ_ε` (`momErr`) is `0`.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {ε S : ℝ}

/-! ### The routed germ of the star -/

theorem edge_eq_of_ne_two {e : starGraph.Edge} (h : e ≠ 2) : e = 0 ∨ e = 1 := by
  fin_cases e
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd rfl h

theorem swapEdge_ne_two {e : starGraph.Edge} (h : e ≠ 2) : swapEdge e ≠ 2 := by
  rcases edge_eq_of_ne_two h with rfl | rfl <;> decide

theorem embedSign_swapEdge {e : starGraph.Edge} (h : e ≠ 2) :
    ThroughRun.embedSign (swapEdge e) = -ThroughRun.embedSign e := by
  rcases edge_eq_of_ne_two h with rfl | rfl
  · rw [show swapEdge 0 = 1 from rfl, ThroughRun.embedSign_one, ThroughRun.embedSign_zero]
    norm_num
  · rw [show swapEdge 1 = 0 from rfl, ThroughRun.embedSign_zero, ThroughRun.embedSign_one]

theorem starRouteGerm_of_false {η : starGraph.EdgeEnd} (h : η.2 = false) :
    starRouting.routeGerm η = (swapEdge η.1, false) := by
  rw [starRouting_routeGerm, starGermMap_of_false h]

theorem starRouteGerm_of_true {η : starGraph.EdgeEnd} (h : η.2 = true) :
    starRouting.routeGerm η = η := by
  rw [starRouting_routeGerm, starGermMap_of_true h]

theorem starTarget_of_false {η : starGraph.EdgeEnd} (h : η.2 = false) :
    starTarget ε η = 8 * ε := by
  rw [starTarget, sign_of_false h, coordinate_of_false h]; ring

theorem starTarget_of_true {η : starGraph.EdgeEnd} (h : η.2 = true) :
    starTarget ε η = 1 - 8 * ε := by
  rw [starTarget, sign_of_true h, coordinate_of_true starGraph_length_eq_one h]; ring

/-- The plane coordinate recovered from the longitudinal coordinate of a through edge. -/
theorem fst_eq_of_longComp {e : starGraph.Edge} (h : e ≠ 2) (z : ℝ × ℝ) :
    z.1 = ThroughRun.embedSign e * longComp e z := by
  rw [longComp_of_ne_two h, ← mul_assoc, embedSign_sq, one_mul]

/-! ### The nominal speed along a trajectory -/

variable {Θ : starNetwork.MicroTrajectory ε S}

/-- Inside the closed edge the through-channel speed is exactly the nominal speed `c`. -/
theorem StarThrough.speed_eq {c : ℝ} (h : StarThrough ε c S Θ) (hε : 0 < ε)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) S) (hu : |(Θ.x a).1| ≤ 1) : |(Θ.p a).1| = c := by
  have hen : (Θ.p a).1 ^ 2 / 2 + capPot ε ((Θ.x a).1) = c ^ 2 / 2 := h.cap.energy a ha
  have hcap : capPot ε ((Θ.x a).1) = 0 := capPot_of_abs_le_one hε hu
  have hc0 : (0 : ℝ) < c := h.cap.c_pos
  have hsq : (Θ.p a).1 ^ 2 = c ^ 2 := by
    rw [hcap] at hen
    linarith
  calc |(Θ.p a).1| = Real.sqrt ((Θ.p a).1 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt (c ^ 2) := by rw [hsq]
    _ = c := Real.sqrt_sq hc0.le

/-- Between the two barriers the arm speed is exactly the nominal speed `c`. -/
theorem StarArm.speed_eq {c : ℝ} (h : StarArm ε c S Θ) (hε : 0 < ε)
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

theorem star_arriving_boundary (hε : 0 < ε) {η : starGraph.EdgeEnd} {x p : ℝ × ℝ}
    (h : starNetwork.Arriving (zeroPotential starGraph) windowStar ε η x p) :
    longComp η.1 x = starTarget ε η := by
  have h1 := h.boundary
  rw [starNetwork_long, starNetwork_offset_of_pos hε] at h1
  exact h1

/-- **A departing state of the star network.** -/
theorem star_mk_departing (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {ζ : starGraph.EdgeEnd}
    {x p : ℝ × ℝ} {r : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hx : longComp ζ.1 x = starTarget ε ζ)
    (hpz : longComp ζ.1 p = -EdgeEnd.sign starGraph ζ * r)
    (htr : |transComp ζ.1 x| ≤ 2 * ε)
    (hte : transComp ζ.1 p ^ 2 / 2 + wellPot ε (transComp ζ.1 x) ≤ ε) :
    starNetwork.Departing (zeroPotential starGraph) windowStar ε ζ x p := by
  have hsq : EdgeEnd.sign starGraph ζ ^ 2 = 1 := starGraph.edgeEnd_sign_sq ζ
  have hQmem := starTarget_mem hε hεs ζ
  have hr0 : (0 : ℝ) < r := by linarith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [starNetwork_long, starNetwork_offset_of_pos hε, starGraph_length]
    simp only [otherEnd_fst]
    rw [hx]
    exact hQmem
  · rw [starNetwork_trans, starNetwork_tubeWidth_of_pos hε]
    simp only [otherEnd_fst]
    exact htr
  · rw [starNetwork_transEnergy, starNetwork_transErr_of_pos hε]
    simp only [otherEnd_fst]
    exact hte
  · rw [starNetwork_longP, sign_otherEnd]
    simp only [otherEnd_fst]
    rw [hpz]
    nlinarith
  · rw [starNetwork_long, starNetwork_longP, zeroPotential_hamiltonian]
    simp only [otherEnd_fst]
    rw [hpz, neg_mul, neg_pow, mul_pow, hsq, one_mul]
    exact ⟨by nlinarith, by nlinarith⟩
  · rw [starNetwork_long, starNetwork_offset_of_pos hε]
    exact hx

/-- **A junction passage of the star network.**  The graph momentum law is exact: the outgoing
longitudinal momentum equals `F⋆`'s departure momentum with error `0`. -/
theorem star_mk_junctionPassage (hε : 0 < ε) (hεs : ε ≤ 1 / 100)
    {η : starGraph.EdgeEnd} {a b c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hab : a < b) (hble : b ≤ a + 23 * ε)
    (hpa : longComp η.1 (Θ.p a) = EdgeEnd.sign starGraph η * c)
    (hx : longComp (starRouting.routeGerm η).1 (Θ.x b) = starTarget ε (starRouting.routeGerm η))
    (hpb : longComp (starRouting.routeGerm η).1 (Θ.p b)
      = -EdgeEnd.sign starGraph (starRouting.routeGerm η) * c)
    (htr : |transComp (starRouting.routeGerm η).1 (Θ.x b)| ≤ 2 * ε)
    (hte : transComp (starRouting.routeGerm η).1 (Θ.p b) ^ 2 / 2
      + wellPot ε (transComp (starRouting.routeGerm η).1 (Θ.x b)) ≤ ε) :
    starNetwork.JunctionPassage (zeroPotential starGraph) windowStar starRouting.routeGerm ε η
      Θ.x Θ.p a b := by
  refine ⟨hab, ?_, star_mk_departing hε hεs hc1 hc2 hx hpb htr hte, ?_⟩
  · rw [starNetwork_dwell_of_pos hε]; exact hble
  · rw [starNetwork_momErr, starNetwork_longP, starNetwork_longP, hpa, hpb, abs_mul,
      star_abs_sign, one_mul, abs_of_pos (by linarith : (0 : ℝ) < c)]
    simp

/-! ### The four passages -/

/-- **`η₁ ↦ η₂`, `η₂ ↦ η₁`: the through junction is crossed freely.**  The longitudinal
potential vanishes on the whole closed edge, so the particle passes straight through the junction
region `|u| ≤ 8ε` and emerges in the opposite channel with unchanged momentum. -/
theorem star_junction_through_inner (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {c : ℝ}
    (hth : StarThrough ε c S Θ) {η : starGraph.EdgeEnd} (hne : η.1 ≠ 2) (hb2 : η.2 = false)
    {a : ℝ} (ha : 0 ≤ a) (haS : a + 23 * ε ≤ S)
    (harr : starNetwork.Arriving (zeroPotential starGraph) windowStar ε η (Θ.x a) (Θ.p a)) :
    ∃ b, starNetwork.JunctionPassage (zeroPotential starGraph) windowStar starRouting.routeGerm ε
      η Θ.x Θ.p a b := by
  have hc1 : 1 ≤ c := hth.cap.c_ge
  have hc2 : c ≤ 2 := hth.cap.c_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hssq : ThroughRun.embedSign η.1 * ThroughRun.embedSign η.1 = 1 := embedSign_sq η.1
  -- the arrival data
  have hxa : longComp η.1 (Θ.x a) = 8 * ε := by
    rw [star_arriving_boundary hε harr, starTarget_of_false hb2]
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hua : (Θ.x a).1 = ThroughRun.embedSign η.1 * (8 * ε) := by
    rw [fst_eq_of_longComp hne, hxa]
  have habsu : |(Θ.x a).1| ≤ 1 := by
    rw [hua, abs_mul, abs_embedSign, one_mul, abs_of_nonneg (by linarith)]
    linarith
  have hspeed : |(Θ.p a).1| = c := hth.speed_eq hε hamem habsu
  have hpa : longComp η.1 (Θ.p a) = EdgeEnd.sign starGraph η * c := by
    obtain ⟨r, hr, hr1, hr2⟩ := star_prep_mom harr.prepared
    have hrc : r = c := by
      have : |longComp η.1 (Θ.p a)| = r := by
        rw [hr, abs_mul, star_abs_sign, one_mul, abs_of_nonneg (by linarith)]
      rw [abs_longComp_of_ne_two hne, hspeed] at this
      exact this.symm
    rw [hr, hrc]
  have hpua : (Θ.p a).1 = -(ThroughRun.embedSign η.1 * c) := by
    rw [fst_eq_of_longComp hne, hpa, sign_of_false hb2]; ring
  -- the free crossing of the junction
  set b : ℝ := a + 16 * ε / c with hbdef
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hba : b - a = 16 * ε / c := by rw [hbdef]; ring
  have hbpos : (0 : ℝ) < 16 * ε / c := by positivity
  have hab : a < b := by rw [hbdef]; linarith
  have hb16 : 16 * ε / c ≤ 16 * ε := by
    rw [div_le_iff₀ hc0]
    nlinarith
  have hble : b ≤ a + 23 * ε := by rw [hbdef]; linarith
  have hbmem : b ∈ Icc (0 : ℝ) S := ⟨by linarith, by linarith⟩
  have hend : (Θ.x a).1 + (Θ.p a).1 * (b - a) = -(ThroughRun.embedSign η.1 * (8 * ε)) := by
    rw [hua, hpua, hba]
    field_simp
    ring
  have habs1 : |(Θ.x a).1| < 1 := by
    rw [hua, abs_mul, abs_embedSign, one_mul, abs_of_nonneg (by linarith)]
    linarith
  have habs2 : |(Θ.x a).1 + (Θ.p a).1 * (b - a)| < 1 := by
    rw [hend, abs_neg, abs_mul, abs_embedSign, one_mul, abs_of_nonneg (by linarith)]
    linarith
  obtain ⟨hub, hpub⟩ := hth.cap.free_of_endpoints hamem hbmem hab.le habs1 habs2 b
    ⟨hab.le, le_rfl⟩
  have hub' : (Θ.x b).1 = -(ThroughRun.embedSign η.1 * (8 * ε)) := by
    have : (Θ.x b).1 = (Θ.x a).1 + (Θ.p a).1 * (b - a) := hub
    rw [this, hend]
  have hpub' : (Θ.p b).1 = -(ThroughRun.embedSign η.1 * c) := by
    have : (Θ.p b).1 = (Θ.p a).1 := hpub
    rw [this, hpua]
  -- the outgoing channel
  have hζ : starRouting.routeGerm η = (swapEdge η.1, false) := starRouteGerm_of_false hb2
  have hζne : (starRouting.routeGerm η).1 ≠ 2 := by rw [hζ]; exact swapEdge_ne_two hne
  have hζs : ThroughRun.embedSign (starRouting.routeGerm η).1 = -ThroughRun.embedSign η.1 := by
    rw [hζ]; exact embedSign_swapEdge hne
  have hζ2 : (starRouting.routeGerm η).2 = false := by rw [hζ]
  refine ⟨b, star_mk_junctionPassage hε hεs hc1 hc2 hab hble hpa ?_ ?_ ?_ ?_⟩
  · rw [longComp_of_ne_two hζne, hζs, hub', starTarget_of_false hζ2]
    nlinarith [hssq]
  · rw [longComp_of_ne_two hζne, hζs, hpub', sign_of_false hζ2]
    nlinarith [hssq]
  · rw [transComp_of_ne_two hζne]
    exact (hth.abs_trans_lt hε hεs hbmem).le
  · simp only [transComp_of_ne_two hζne]
    exact hth.trans_le b hbmem

/-- **The outer reflection of the through channel.**  The cap at `u = ±1` reverses the momentum
exactly, within the time `23ε` (Lemma IX.8 with `d = 8ε`). -/
theorem star_junction_through_outer (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {c : ℝ}
    (hth : StarThrough ε c S Θ) {η : starGraph.EdgeEnd} (hne : η.1 ≠ 2) (hb2 : η.2 = true)
    {a : ℝ} (ha : 0 ≤ a) (haS : a + 23 * ε ≤ S)
    (harr : starNetwork.Arriving (zeroPotential starGraph) windowStar ε η (Θ.x a) (Θ.p a)) :
    ∃ b, starNetwork.JunctionPassage (zeroPotential starGraph) windowStar starRouting.routeGerm ε
      η Θ.x Θ.p a b := by
  have hc1 : 1 ≤ c := hth.cap.c_ge
  have hc2 : c ≤ 2 := hth.cap.c_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hssq : ThroughRun.embedSign η.1 * ThroughRun.embedSign η.1 = 1 := embedSign_sq η.1
  have hxa : longComp η.1 (Θ.x a) = 1 - 8 * ε := by
    rw [star_arriving_boundary hε harr, starTarget_of_true hb2]
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hua : (Θ.x a).1 = ThroughRun.embedSign η.1 * (1 - 8 * ε) := by
    rw [fst_eq_of_longComp hne, hxa]
  have habsu : |(Θ.x a).1| ≤ 1 := by
    rw [hua, abs_mul, abs_embedSign, one_mul, abs_of_nonneg (by linarith)]
    linarith
  have hspeed : |(Θ.p a).1| = c := hth.speed_eq hε hamem habsu
  have hpa : longComp η.1 (Θ.p a) = EdgeEnd.sign starGraph η * c := by
    obtain ⟨r, hr, hr1, hr2⟩ := star_prep_mom harr.prepared
    have hrc : r = c := by
      have hval : |longComp η.1 (Θ.p a)| = r := by
        rw [hr, abs_mul, star_abs_sign, one_mul, abs_of_nonneg (by linarith)]
      rw [abs_longComp_of_ne_two hne, hspeed] at hval
      exact hval.symm
    rw [hr, hrc]
  have hpua : (Θ.p a).1 = ThroughRun.embedSign η.1 * c := by
    rw [fst_eq_of_longComp hne, hpa, sign_of_true hb2]; ring
  -- the reflection
  obtain ⟨t₁, ht₁, hu₁, hp₁⟩ :=
    hth.cap.reflect (embedSign_eq_or η.1) ha (by linarith) hua hpua
  have ht₁mem : t₁ ∈ Icc (0 : ℝ) S := ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
  have hζ : starRouting.routeGerm η = η := starRouteGerm_of_true hb2
  refine ⟨t₁, star_mk_junctionPassage hε hεs hc1 hc2 ht₁.1 (by linarith [ht₁.2]) hpa ?_ ?_ ?_ ?_⟩
  · rw [hζ, longComp_of_ne_two hne, starTarget_of_true hb2]
    have : (Θ.x t₁).1 = ThroughRun.embedSign η.1 * (1 - 8 * ε) := hu₁
    rw [this]
    nlinarith [hssq]
  · rw [hζ, longComp_of_ne_two hne, sign_of_true hb2]
    have : (Θ.p t₁).1 = -(ThroughRun.embedSign η.1 * c) := hp₁
    rw [this]
    nlinarith [hssq]
  · rw [hζ, transComp_of_ne_two hne]
    exact (hth.abs_trans_lt hε hεs ht₁mem).le
  · rw [hζ]
    simp only [transComp_of_ne_two hne]
    exact hth.trans_le t₁ ht₁mem

/-- **`η₃ ↦ η₃`: the junction barrier of the third arm.**  Its height `4` exceeds every energy
of `K⋆`, so a particle arriving along the third channel is turned around exactly and leaves along
the third channel. -/
theorem star_junction_arm_inner (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {c : ℝ}
    (harm : StarArm ε c S Θ) {η : starGraph.EdgeEnd} (heq : η.1 = 2) (hb2 : η.2 = false)
    {a : ℝ} (ha : 0 ≤ a) (haS : a + 23 * ε ≤ S)
    (harr : starNetwork.Arriving (zeroPotential starGraph) windowStar ε η (Θ.x a) (Θ.p a)) :
    ∃ b, starNetwork.JunctionPassage (zeroPotential starGraph) windowStar starRouting.routeGerm ε
      η Θ.x Θ.p a b := by
  have hc1 : 1 ≤ c := harm.arm.c_ge
  have hc2 : c ≤ 2 := harm.arm.c_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hlc : ∀ z : ℝ × ℝ, longComp η.1 z = z.2 := by rw [heq]; exact fun z => longComp_two z
  have htc : ∀ z : ℝ × ℝ, transComp η.1 z = z.1 := by rw [heq]; exact fun z => transComp_two z
  have hxa : (Θ.x a).2 = 8 * ε := by
    rw [← hlc, star_arriving_boundary hε harr, starTarget_of_false hb2]
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hspeed : |(Θ.p a).2| = c :=
    harm.speed_eq hε hamem (by rw [hxa]; linarith) (by rw [hxa]; linarith)
  have hpa : longComp η.1 (Θ.p a) = EdgeEnd.sign starGraph η * c := by
    obtain ⟨r, hr, hr1, hr2⟩ := star_prep_mom harr.prepared
    have hrc : r = c := by
      have hval : |longComp η.1 (Θ.p a)| = r := by
        rw [hr, abs_mul, star_abs_sign, one_mul, abs_of_nonneg (by linarith)]
      rw [hlc, hspeed] at hval
      exact hval.symm
    rw [hr, hrc]
  have hpwa : (Θ.p a).2 = -c := by
    have := hpa
    rw [hlc, sign_of_false hb2] at this
    linarith
  obtain ⟨t₁, ht₁, hw₁, hp₁⟩ := harm.arm.reflect_junction ha (by linarith) hxa hpwa
  have ht₁mem : t₁ ∈ Icc (0 : ℝ) S := ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
  have hζ : starRouting.routeGerm η = η := by
    rw [starRouteGerm_of_false hb2, heq]
    exact Prod.ext (by rw [heq]; rfl) (by rw [hb2])
  refine ⟨t₁, star_mk_junctionPassage hε hεs hc1 hc2 ht₁.1 (by linarith [ht₁.2]) hpa ?_ ?_ ?_ ?_⟩
  · rw [hζ, hlc, starTarget_of_false hb2]
    exact hw₁
  · rw [hζ, hlc, sign_of_false hb2]
    rw [show (Θ.p t₁).2 = c from hp₁]
    ring
  · rw [hζ, htc]
    exact (harm.abs_trans_lt hε hεs ht₁mem).le
  · rw [hζ]
    simp only [htc]
    exact harm.trans_le t₁ ht₁mem

/-- **The outer reflection of the third arm.** -/
theorem star_junction_arm_outer (hε : 0 < ε) (hεs : ε ≤ 1 / 100) {c : ℝ}
    (harm : StarArm ε c S Θ) {η : starGraph.EdgeEnd} (heq : η.1 = 2) (hb2 : η.2 = true)
    {a : ℝ} (ha : 0 ≤ a) (haS : a + 23 * ε ≤ S)
    (harr : starNetwork.Arriving (zeroPotential starGraph) windowStar ε η (Θ.x a) (Θ.p a)) :
    ∃ b, starNetwork.JunctionPassage (zeroPotential starGraph) windowStar starRouting.routeGerm ε
      η Θ.x Θ.p a b := by
  have hc1 : 1 ≤ c := harm.arm.c_ge
  have hc2 : c ≤ 2 := harm.arm.c_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hlc : ∀ z : ℝ × ℝ, longComp η.1 z = z.2 := by rw [heq]; exact fun z => longComp_two z
  have htc : ∀ z : ℝ × ℝ, transComp η.1 z = z.1 := by rw [heq]; exact fun z => transComp_two z
  have hxa : (Θ.x a).2 = 1 - 8 * ε := by
    rw [← hlc, star_arriving_boundary hε harr, starTarget_of_true hb2]
  have hamem : a ∈ Icc (0 : ℝ) S := ⟨ha, by linarith⟩
  have hspeed : |(Θ.p a).2| = c :=
    harm.speed_eq hε hamem (by rw [hxa]; linarith) (by rw [hxa]; linarith)
  have hpa : longComp η.1 (Θ.p a) = EdgeEnd.sign starGraph η * c := by
    obtain ⟨r, hr, hr1, hr2⟩ := star_prep_mom harr.prepared
    have hrc : r = c := by
      have hval : |longComp η.1 (Θ.p a)| = r := by
        rw [hr, abs_mul, star_abs_sign, one_mul, abs_of_nonneg (by linarith)]
      rw [hlc, hspeed] at hval
      exact hval.symm
    rw [hr, hrc]
  have hpwa : (Θ.p a).2 = c := by
    have := hpa
    rw [hlc, sign_of_true hb2] at this
    linarith
  obtain ⟨t₁, ht₁, hw₁, hp₁⟩ := harm.arm.reflect_cap ha (by linarith) hxa hpwa
  have ht₁mem : t₁ ∈ Icc (0 : ℝ) S := ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
  have hζ : starRouting.routeGerm η = η := starRouteGerm_of_true hb2
  refine ⟨t₁, star_mk_junctionPassage hε hεs hc1 hc2 ht₁.1 (by linarith [ht₁.2]) hpa ?_ ?_ ?_ ?_⟩
  · rw [hζ, hlc, starTarget_of_true hb2]
    exact hw₁
  · rw [hζ, hlc, sign_of_true hb2]
    rw [show (Θ.p t₁).2 = -c from hp₁]
    ring
  · rw [hζ, htc]
    exact (harm.abs_trans_lt hε hεs ht₁mem).le
  · rw [hζ]
    simp only [htc]
    exact harm.trans_le t₁ ht₁mem

/-! ### The junction-scattering hypothesis -/

/-- **The explicit three-channel junction satisfies (J) for the routing law `F⋆`.**  Every
microscopic state arriving at a junction of the star leaves it through the channel prescribed by
`F⋆(η₁) = η₂`, `F⋆(η₂) = η₁`, `F⋆(η₃) = η₃` (and by the forced identity at the outer vertices),
after a residence time at most `θ_ε = 23ε`, with exactly reversed speed. -/
theorem starNetwork_junctionScattering :
    starNetwork.JunctionScatteringConvergesTo (zeroPotential starGraph) windowStar
      starRouting (1 / 100) := by
  intro ε hε η x p harr₀
  have hε0 : 0 < ε := hε.1
  have hεs : ε ≤ 1 / 100 := le_of_lt hε.2
  -- the flow through `(x, p)` on `[0, 1]`, which contains the junction window `[0, 23ε]`
  set Θ := starNetwork.flowTraj ε (x, p) 1 with hΘ
  have harr : starNetwork.Arriving (zeroPotential starGraph) windowStar ε η (Θ.x 0) (Θ.p 0) := by
    rw [hΘ, ThinHamiltonianNetwork.flowTraj_x_zero, ThinHamiltonianNetwork.flowTraj_p_zero]
    exact harr₀
  have hS : (0 : ℝ) ≤ 1 := by norm_num
  have haS : (0 : ℝ) + 23 * ε ≤ 1 := by linarith
  by_cases h2 : η.1 = 2
  · have harm := star_arm Θ hε0 hεs hS h2 harr.prepared
    rcases hb2 : η.2 with _ | _
    · exact star_junction_arm_inner hε0 hεs harm h2 hb2 le_rfl haS harr
    · exact star_junction_arm_outer hε0 hεs harm h2 hb2 le_rfl haS harr
  · have hth := star_through Θ hε0 hεs hS h2 harr.prepared
    rcases hb2 : η.2 with _ | _
    · exact star_junction_through_inner hε0 hεs hth h2 hb2 le_rfl haS harr
    · exact star_junction_through_outer hε0 hεs hth h2 hb2 le_rfl haS harr

end HamiltonianMetricGraphs
