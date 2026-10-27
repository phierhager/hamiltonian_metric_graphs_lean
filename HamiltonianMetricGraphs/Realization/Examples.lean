/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ScaledJunction
import HamiltonianMetricGraphs.Realization.Realization

/-!
# Examples: a trivial thin-network family and an explicit free router

Two sanity checks that the hypotheses of the realization theorem are satisfiable.

* `ThinNetworkFamily.const g`: the graph trajectory itself, viewed as a thin-network family
  with vanishing parameters.  The realization theorem applies to it (and its conclusions are
  then trivial), which shows the structures are consistent.
* `freeJunction`: the explicit smooth (force-free) straight-through router on the real line, at
  a vertex with two distinguished incident edge-ends `η₁ ≠ η₂` exchanged by the routing law.  A
  particle entering along `η₁` at scaled position `-1` with speed `r > 0` crosses the router and
  exits at position `2` along `η₂`.  `freePassage` verifies the four reference-junction
  hypotheses of the theorem for it: exit through `F_v η₁ = η₂` with a positive basin margin
  `min 1 (r/2)`, scaled dwell time `3/r`, and exact conservation of the speed.
-/

namespace HamiltonianMetricGraphs

open Set Filter Metric FiniteMetricGraph
open scoped Topology

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} {V : MechanicalPotential Γ} {F : RoutingLaw Γ}

/-- The constant family: every microscopic chain is the graph trajectory itself. -/
def ThinNetworkFamily.const (g : GraphTrajectory V F) : ThinNetworkFamily V F where
  params _ := ChainParams.zero
  chain _ := g
  offset_tendsto := tendsto_const_nhds
  dwell_tendsto := tendsto_const_nhds
  odeErr_tendsto := tendsto_const_nhds
  momErr_tendsto := tendsto_const_nhds

/-- The constant family converges initially to `g`. -/
theorem ThinNetworkFamily.const_convergesInitially (g : GraphTrajectory V F) :
    (ThinNetworkFamily.const g).ConvergesInitially g where
  edge_zero := Eventually.of_forall fun _ => rfl
  state_zero := tendsto_const_nhds
  finalTime := Eventually.of_forall fun _ => le_rfl

end MechanicalPotential

/-! ### The free straight-through router -/

variable (Γ : FiniteMetricGraph) (v : Γ.Vertex) (η₁ η₂ : Γ.IncidentEnds v)

/-- The exit basin on the far side of the free router: past `y = 1`, moving right. -/
def freeExitBasin : Set (ℝ × ℝ) := {z | 1 ≤ z.1 ∧ 0 < z.2}

/-- The exit basin on the near side: past `y = -1`, moving left. -/
def freeReturnBasin : Set (ℝ × ℝ) := {z | z.1 ≤ -1 ∧ z.2 < 0}

theorem freeExitBasin_disjoint_freeReturnBasin : Disjoint (freeExitBasin) (freeReturnBasin) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact absurd (hz.1.trans hz'.1) (by norm_num)

/-- The free straight-through router on the line: no force, exit basins for the two
distinguished ends `η₁` (return) and `η₂` (transmission), empty basins elsewhere, and the
longitudinal momentum read off as the momentum itself. -/
noncomputable def freeJunction : ReferenceJunction Γ v ℝ where
  force _ := 0
  region := univ
  K := 0
  lipschitz := (LipschitzWith.const (0 : ℝ)).lipschitzOnWith
  basin ζ := if ζ = η₂ then freeExitBasin else if ζ = η₁ then freeReturnBasin else ∅
  basin_disjoint := by
    intro ζ ζ' hne
    show Disjoint (if ζ = η₂ then freeExitBasin else if ζ = η₁ then freeReturnBasin else ∅)
      (if ζ' = η₂ then freeExitBasin else if ζ' = η₁ then freeReturnBasin else ∅)
    by_cases h1 : ζ = η₂
    · subst h1
      rw [if_pos rfl]
      by_cases h2 : ζ' = ζ
      · exact absurd h2.symm hne
      · rw [if_neg h2]
        by_cases h3 : ζ' = η₁
        · rw [if_pos h3]; exact freeExitBasin_disjoint_freeReturnBasin
        · rw [if_neg h3]; exact Set.disjoint_empty _
    · rw [if_neg h1]
      by_cases h3 : ζ = η₁
      · subst h3
        rw [if_pos rfl]
        by_cases h2 : ζ' = η₂
        · rw [if_pos h2]; exact freeExitBasin_disjoint_freeReturnBasin.symm
        · rw [if_neg h2]
          by_cases h4 : ζ' = ζ
          · exact absurd h4.symm hne
          · rw [if_neg h4]; exact Set.disjoint_empty _
      · rw [if_neg h3]; exact Set.empty_disjoint _
  channelMomentum _ z := z.2
  Λ := 1
  channelMomentum_lipschitz _ := LipschitzWith.prod_snd

/-- The reference passage through the free router: entering along `η₁` at `y = -1` with speed
`r`, the particle moves freely and is at `y = 2` at the scaled time `3/r`, inside the exit
basin of `η₂ = F_v η₁` with margin `min 1 (r/2)`, at the same speed.  This verifies the four
junction hypotheses of the realization theorem for an explicit smooth router. -/
noncomputable def freePassage (F : RoutingLaw Γ) (hF : F.route v η₁ = η₂) {r : ℝ} (hr : 0 < r) :
    ReferencePassage (freeJunction Γ v η₁ η₂) F η₁ r (3 / r) (min 1 (r / 2)) 0 where
  τ_out := 3 / r
  τ_out_nonneg := by positivity
  τ_out_le := le_rfl
  z τ := (-1 + r * τ, r)
  continuousOn := by
    apply Continuous.continuousOn
    fun_prop
  hasDerivWithinAt τ _ := by
    have h1 : HasDerivAt (fun τ : ℝ => -1 + r * τ) r τ := by
      simpa using ((hasDerivAt_id τ).const_mul r).const_add (-1)
    have h2 : HasDerivAt (fun _ : ℝ => r) 0 τ := hasDerivAt_const τ r
    exact (h1.prodMk h2).hasDerivWithinAt
  region _ _ := trivial
  exit_margin := by
    rw [hF]
    change ball (-1 + r * (3 / r), r) (min 1 (r / 2)) ⊆
      (if η₂ = η₂ then freeExitBasin else if η₂ = η₁ then freeReturnBasin else ∅)
    rw [if_pos rfl]
    intro z hz
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hz
    have h3 : r * (3 / r) = 3 := by field_simp
    rw [h3] at hz
    have hm1 : min 1 (r / 2) ≤ 1 := min_le_left _ _
    have hm2 : min 1 (r / 2) ≤ r / 2 := min_le_right _ _
    have hz1 := abs_lt.mp hz.1
    have hz2 := abs_lt.mp hz.2
    exact ⟨by linarith [hz1.1], by linarith [hz2.1]⟩
  exit_speed := by
    change |(|r| - r)| ≤ 0
    rw [abs_of_pos hr, sub_self, abs_zero]

end HamiltonianMetricGraphs
