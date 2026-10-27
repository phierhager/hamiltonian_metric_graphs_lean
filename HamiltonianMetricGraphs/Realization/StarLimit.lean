/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.StarDeterminism
import HamiltonianMetricGraphs.Realization.ThinLimit

/-!
# The explicit realization theorem as a corollary of the thin-junction limit theorem

This file completes the programme for the explicit valence-3 model.  The hypotheses (E), (J) and
(D) of `ThinHypotheses.lean` have been verified for the smooth microscopic Hamiltonian

  `H_ε(x, p) = ½|p|² + microPot ε x`   on   `ℝ² × ℝ²`

in `StarEdge.lean`, `StarJunction.lean` and `StarDeterminism.lean` (this is Theorem IX.9 of the
paper, `starNetwork_hypotheses`); here we construct the prepared initial data and
apply the **general** theorem `thin_junction_hamiltonian_limit`.  The explicit model is therefore
literally an instance of the general physical limit theorem, not a parallel development.

The limiting graph dynamics is the deterministic metric-graph flow of the star `Γ⋆` with the
routing law

  `F⋆(η₁) = η₂`,  `F⋆(η₂) = η₁`,  `F⋆(η₃) = η₃`,

on the compact energy window `K⋆ = [1/2, 2]`, which lies above the (zero) potential as
Theorem IX.6 requires (`windowStar_isWindowAbove`).
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

/-! ### The admissible range of scales -/

/-- The scale threshold of the explicit model for an initial coordinate `q₀`: below it the two
junction regions of the initial edge do not reach `q₀`. -/
noncomputable def starEps (q₀ : ℝ) : ℝ := min (1 / 100) (min q₀ (1 - q₀) / 8)

theorem starEps_le (q₀ : ℝ) : starEps q₀ ≤ 1 / 100 := min_le_left _ _

theorem starEps_pos {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) : 0 < starEps q₀ :=
  lt_min (by norm_num) (div_pos (lt_min hq₀.1 (by linarith [hq₀.2])) (by norm_num))

theorem starEps_bounds {q₀ ε : ℝ} (h : ε < starEps q₀) : 8 * ε < q₀ ∧ 8 * ε < 1 - q₀ := by
  have h1 : ε < min q₀ (1 - q₀) / 8 := lt_of_lt_of_le h (min_le_right _ _)
  have h2 : 8 * ε < min q₀ (1 - q₀) := by linarith
  exact ⟨lt_of_lt_of_le h2 (min_le_left _ _), lt_of_lt_of_le h2 (min_le_right _ _)⟩

/-! ### The initial microscopic state -/

/-- The initial microscopic configuration: the point of the tube axis of the edge of `η₀` at
graph coordinate `q₀`. -/
noncomputable def starX (η₀ : starGraph.EdgeEnd) (q₀ : ℝ) : ℝ × ℝ :=
  if η₀.1 = 2 then (0, q₀) else (ThroughRun.embedSign η₀.1 * q₀, 0)

/-- The initial microscopic momentum: purely longitudinal, of speed `c`, pointing towards `η₀`. -/
noncomputable def starP (η₀ : starGraph.EdgeEnd) (c : ℝ) : ℝ × ℝ :=
  if η₀.1 = 2 then (0, EdgeEnd.sign starGraph η₀ * c)
  else (ThroughRun.embedSign η₀.1 * (EdgeEnd.sign starGraph η₀ * c), 0)

variable (η₀ : starGraph.EdgeEnd) (q₀ c : ℝ)

@[simp] theorem starX_long : longComp η₀.1 (starX η₀ q₀) = q₀ := by
  by_cases h : η₀.1 = 2
  · rw [starX, if_pos h, h, longComp_two]
  · rw [starX, if_neg h, longComp_of_ne_two h, ← mul_assoc, embedSign_sq, one_mul]

@[simp] theorem starX_trans : transComp η₀.1 (starX η₀ q₀) = 0 := by
  by_cases h : η₀.1 = 2
  · rw [starX, if_pos h, h, transComp_two]
  · rw [starX, if_neg h, transComp_of_ne_two h]

@[simp] theorem starP_long : longComp η₀.1 (starP η₀ c) = EdgeEnd.sign starGraph η₀ * c := by
  by_cases h : η₀.1 = 2
  · rw [starP, if_pos h, h, longComp_two]
  · rw [starP, if_neg h, longComp_of_ne_two h, ← mul_assoc, embedSign_sq, one_mul]

@[simp] theorem starP_trans : transComp η₀.1 (starP η₀ c) = 0 := by
  by_cases h : η₀.1 = 2
  · rw [starP, if_pos h, h, transComp_two]
  · rw [starP, if_neg h, transComp_of_ne_two h]

variable {η₀ q₀ c}

/-! ### The window is above the potential -/

/-- **The window `K⋆ = [1/2, 2]` lies above the (zero) potential**: the window condition
`K ⊂ (max_Γ V, ∞)` of Theorem IX.6. -/
theorem windowStar_isWindowAbove : (zeroPotential starGraph).IsWindowAbove windowStar :=
  zeroPotential_isWindowAbove fun E hE => by have : (1 / 2 : ℝ) ≤ E := hE.1; linarith

/-! ### The well-prepared initial state -/

/-- **The well-prepared initial state of the explicit model**: the particle sits on the axis of
the tube of the edge of `η₀`, at graph coordinate `q₀`, with purely longitudinal momentum of
speed `c ∈ [1, 2]` pointing towards `η₀`. -/
noncomputable def starWellPrepared (η₀ : starGraph.EdgeEnd) {q₀ c : ℝ}
    (_hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    WellPreparedInitialState starNetwork (zeroPotential starGraph) windowStar (starEps q₀) where
  germ := η₀
  x₀ := fun _ => starX η₀ q₀
  p₀ := fun _ => starP η₀ c
  q := q₀
  r := EdgeEnd.sign starGraph η₀ * c
  prepared := by
    intro ε hε
    have hε0 : 0 < ε := hε.1
    obtain ⟨hq8, hq8'⟩ := starEps_bounds hε.2
    have hsq : EdgeEnd.sign starGraph η₀ ^ 2 = 1 := starGraph.edgeEnd_sign_sq η₀
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [starNetwork_long, starNetwork_offset_of_pos hε0, starGraph_length, starX_long]
      exact ⟨le_of_lt hq8, by linarith⟩
    · rw [starNetwork_trans, starNetwork_tubeWidth_of_pos hε0, starX_trans, abs_zero]
      linarith
    · rw [starNetwork_transEnergy, starNetwork_transErr_of_pos hε0, starX_trans, starP_trans,
        wellPot_of_abs_le hε0 (by rw [abs_zero]; linarith)]
      norm_num
      linarith
    · rw [starNetwork_longP, starP_long]
      nlinarith
    · rw [starNetwork_long, starNetwork_longP, zeroPotential_hamiltonian, starP_long,
        mul_pow, hsq, one_mul]
      exact ⟨by nlinarith, by nlinarith⟩
  not_arriving := by
    intro ε hε
    have hε0 : 0 < ε := hε.1
    obtain ⟨hq8, hq8'⟩ := starEps_bounds hε.2
    refine ThinHamiltonianNetwork.not_arriving_of_toGo_pos ?_
    rw [starNetwork_toGo hε0, starNetwork_long, starX_long]
    refine abs_pos.mpr (sub_ne_zero.mpr ?_)
    rcases star_sign_coord η₀ with ⟨hs, hc⟩ | ⟨hs, hc⟩
    · rw [starTarget, hs, hc]
      intro h; linarith
    · rw [starTarget, hs, hc]
      intro h; linarith
  converges := by
    have hfun : (fun _ : ℝ => starNetwork.gState η₀.1 (starX η₀ q₀) (starP η₀ c))
        = fun _ : ℝ => (q₀, EdgeEnd.sign starGraph η₀ * c) := by
      funext _
      rw [ThinHamiltonianNetwork.gState, starNetwork_long, starNetwork_longP, starX_long,
        starP_long]
    rw [hfun]
    exact tendsto_const_nhds

/-! ### The explicit realization theorem -/

/-- **The explicit routing law of the three-channel junction.** -/
theorem explicit_star_routing :
    starRouting.routeGerm channel₁ = channel₂ ∧
      starRouting.routeGerm channel₂ = channel₁ ∧
      starRouting.routeGerm channel₃ = channel₃ :=
  ⟨starRouting_channel₁, starRouting_channel₂, starRouting_channel₃⟩

/-- **The explicit three-channel junction satisfies the hypotheses of the general theorem.** -/
theorem starNetwork_hypotheses (q₀ : ℝ) :
    starNetwork.SatisfiesEdgeReduction (zeroPotential starGraph) windowStar (starEps q₀) ∧
      starNetwork.JunctionScatteringConvergesTo (zeroPotential starGraph) windowStar
        starRouting (starEps q₀) ∧
      starNetwork.HasDeterministicChannelReduction (zeroPotential starGraph) windowStar
        starRouting (starEps q₀) ∧
      starNetwork.ChannelsSeparated (zeroPotential starGraph) windowStar (starEps q₀) :=
  ⟨starNetwork_satisfiesEdgeReduction.mono (starEps_le q₀),
    starNetwork_junctionScattering.mono (starEps_le q₀),
    starNetwork_hasDeterministicChannelReduction.mono (starEps_le q₀),
    starNetwork_channelsSeparated.mono (starEps_le q₀)⟩

/-- **Theorem IX.9 (explicit three-channel junction), the hypotheses.**  The network
`N⋆ = starNetwork` has the potential `W⋆_ε = microPot ε` and the scales `δ_ε = 8ε`,
`θ_ε = 23ε`, `γ_ε = μ_ε = 0`, `w_ε = 2ε`, `λ_ε = ε` of the paper, and for every
`ε ∈ (0, ε₀)`, `ε₀ = 1/100`, it satisfies (E), (J) and (D) on `K⋆ = [1/2, 2]` for `F⋆`; its
channels are separated. -/
theorem explicit_star_junction :
    (∀ ε, starNetwork.pot ε = microPot ε) ∧
    (∀ ε, 0 < ε → starNetwork.offset ε = 8 * ε ∧ starNetwork.dwell ε = 23 * ε ∧
      starNetwork.forceErr ε = 0 ∧ starNetwork.momErr ε = 0 ∧
      starNetwork.tubeWidth ε = 2 * ε ∧ starNetwork.transErr ε = ε) ∧
    windowStar = Icc (1 / 2 : ℝ) 2 ∧
    starNetwork.SatisfiesEdgeReduction (zeroPotential starGraph) windowStar (1 / 100) ∧
    starNetwork.JunctionScatteringConvergesTo (zeroPotential starGraph) windowStar
      starRouting (1 / 100) ∧
    starNetwork.HasDeterministicChannelReduction (zeroPotential starGraph) windowStar
      starRouting (1 / 100) ∧
    starNetwork.ChannelsSeparated (zeroPotential starGraph) windowStar (1 / 100) :=
  ⟨fun _ => rfl, fun _ hε => ⟨starNetwork_offset_of_pos hε, starNetwork_dwell_of_pos hε, rfl, rfl,
    starNetwork_tubeWidth_of_pos hε, starNetwork_transErr_of_pos hε⟩, rfl,
    starNetwork_satisfiesEdgeReduction, starNetwork_junctionScattering,
    starNetwork_hasDeterministicChannelReduction, starNetwork_channelsSeparated⟩

set_option maxHeartbeats 1000000 in
-- the final assembly instantiates the general limit theorem at a large concrete structure
/-- **The explicit realization theorem.**
`H_ε(x,p) = ½|p|² + microPot ε x` is a smooth mechanical Hamiltonian on `ℝ² × ℝ²` describing a
particle confined to three thin channels of width `O(ε)` meeting in a single junction region of
diameter `O(ε)`.  Its projected trajectories converge, on every finite time interval, to the
deterministic metric-graph flow of the star `Γ⋆` with the routing law
`F⋆(η₁) = η₂`, `F⋆(η₂) = η₁`, `F⋆(η₃) = η₃` on the window `K⋆ = [1/2, 2]`.

This is an **instance of the general thin-junction limit theorem**
`thin_junction_hamiltonian_limit`: the hypotheses (E) and (J) are discharged in `StarEdge.lean`
and `StarJunction.lean` from Hamilton's equations, and nothing about the projected chain is
assumed. -/
theorem explicit_thin_junction_realization (η₀ : starGraph.EdgeEnd) {q₀ c : ℝ}
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) {M : ℕ} (hM : 1 ≤ M) {T : ℝ}
    (hT : T ≤ FreeTrajectory.stopTime η₀ q₀ c M M) :
    ∃ g : GraphTrajectory (zeroPotential starGraph) starRouting,
      g.N = M ∧ (∀ j, g.germ j = starRouting.itinerary η₀ j) ∧
        IsThinGraphLimit (starWellPrepared η₀ hq₀ hc1 hc2) g ∧
        ThinTrajectoryConvergesTo starNetwork (starWellPrepared η₀ hq₀ hc1 hc2) g T := by
  have hc0 : (0 : ℝ) < c := by linarith
  set g : GraphTrajectory (zeroPotential starGraph) starRouting :=
    starTrajectory η₀ q₀ c hq₀ hc0 M hM with hgdef
  have hcurve : g.curve 0 0 = (q₀, EdgeEnd.sign starGraph η₀ * c) := by
    change FreeTrajectory.curve starRouting η₀ q₀ c 0 0 = _
    rw [FreeTrajectory.curve, FreeTrajectory.startTime_zero]
    refine Prod.ext ?_ rfl
    change FreeTrajectory.startCoord starRouting η₀ q₀ 0
      + FreeTrajectory.momentum starRouting η₀ c 0 * (0 - 0) = q₀
    change q₀ + FreeTrajectory.momentum starRouting η₀ c 0 * (0 - 0) = q₀
    ring
  have hlimit : IsThinGraphLimit (starWellPrepared η₀ hq₀ hc1 hc2) g := ⟨rfl, rfl, hcurve⟩
  have hE : g.energy ∈ windowStar := starTrajectory_energy_mem η₀ q₀ hq₀ hc0 M hM ⟨hc1, hc2⟩
  have hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (starGraph.length (g.edge 0)) := by
    rw [hcurve, starGraph_length]
    exact hq₀
  refine ⟨g, rfl, fun j => rfl, hlimit, ?_⟩
  refine thin_junction_hamiltonian_limit starNetwork (zeroPotential starGraph) starRouting
    windowStar isCompact_windowStar windowStar_isWindowAbove (starEps_pos hq₀)
    (starNetwork_satisfiesEdgeReduction.mono (starEps_le q₀))
    (starNetwork_junctionScattering.mono (starEps_le q₀))
    (starWellPrepared η₀ hq₀ hc1 hc2) g hlimit hE hinit ?_
  exact hT

end HamiltonianMetricGraphs
