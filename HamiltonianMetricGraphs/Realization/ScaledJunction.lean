/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.Routing
import HamiltonianMetricGraphs.Realization.IntervalEstimates

/-!
# Scaled Hamiltonian junctions

This file treats the microscopic router `J_{v,ε} = ε J_v` in isolation.  The reference junction
`J_v` is a Hamiltonian system on a configuration space `E` (a normed space) with force field
`G = -∇W_v`; the router of the thin network is its rescaling by `ε`.  We prove:

* **Rescaling** (`scaledRouter_hasDerivAt`): in the scaled variables `y = Y/ε`, `τ = t/ε` the
  router dynamics `Y' = P`, `P' = ε⁻¹ G(Y/ε) + F_slow(Y)` becomes
  `y' = p`, `p' = G(y) + ε F_slow(εy)`, i.e. the reference dynamics with an `O(ε)` perturbation
  (`ε ‖F_slow‖ ≤ ε R`, where the slowly varying part is the force of the edge potentials).
* **Scaled-junction perturbation lemma** (`dist_le_of_perturbed_junction`): an `O(ε)`-perturbed
  solution started `δ`-close to a reference solution stays within
  `(δ + ρ τ) exp (K τ)` of it (Grönwall), on any region where `G` is Lipschitz.
* **Channel stability** (`channel_stability`): if the reference trajectory exits inside the
  basin of `F_v(η)` with a positive margin `m` and the perturbed trajectory is within `m` of it,
  the perturbed trajectory exits through the same channel and through no competing basin.
* **Vanishing physical junction time** (`physical_dwell_le`): a scaled dwell time `≤ T` is a
  physical dwell time `≤ ε T`.
* **`ReferenceJunction` / `ReferencePassage`**: the four uniform properties of the reference
  junction assumed in the theorem (exit through `F_v(η)`, transverse separated exit basin,
  bounded scaled dwell time, exit speed close to the incoming speed), and the theorem
  `ReferencePassage.scaled_exit` deriving from them the router properties used by the hybrid
  chains (`HybridChain.edge_succ`, `start_succ_le`, `depart_mom`) for the `ε`-router.

Mathematical proof steps: "scaled-junction perturbation lemma", "channel-stability lemma from a
positive exit-basin margin", "vanishing physical junction time".
-/

namespace HamiltonianMetricGraphs

open Set Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Rescaling -/

/-- The scaled configuration `y(τ) = Y(ετ)/ε` of a physical router trajectory. -/
noncomputable def scaledPosition (ε : ℝ) (Y : ℝ → E) : ℝ → E := fun τ => ε⁻¹ • Y (ε * τ)

/-- The scaled momentum `p(τ) = P(ετ)` of a physical router trajectory. -/
def scaledMomentum (ε : ℝ) (P : ℝ → E) : ℝ → E := fun τ => P (ε * τ)

/-- **Rescaling of the router dynamics.**  If `(Y, P)` solves the physical router equations
`Y' = P`, `P' = ε⁻¹ G(Y/ε) + F_slow(Y)` (router force of the `ε`-scaled potential `W_v(·/ε)`
plus the slowly varying edge force), then the scaled variables solve
`y' = p`, `p' = G(y) + ε F_slow(Y(ετ))`. -/
theorem scaledRouter_hasDerivAt {ε : ℝ} (hε : ε ≠ 0) {Y P : ℝ → E} (G Fs : E → E) {τ : ℝ}
    (hY : HasDerivAt Y (P (ε * τ)) (ε * τ))
    (hP : HasDerivAt P (ε⁻¹ • G (ε⁻¹ • Y (ε * τ)) + Fs (Y (ε * τ))) (ε * τ)) :
    HasDerivAt (scaledPosition ε Y) (scaledMomentum ε P τ) τ ∧
    HasDerivAt (scaledMomentum ε P)
      (G (scaledPosition ε Y τ) + ε • Fs (Y (ε * τ))) τ := by
  have hlin : HasDerivAt (fun s : ℝ => ε * s) ε τ := by
    simpa using (hasDerivAt_id τ).const_mul ε
  constructor
  · have h := (hY.scomp τ hlin).const_smul ε⁻¹
    have h' : HasDerivAt (scaledPosition ε Y) (ε⁻¹ • ε • P (ε * τ)) τ := h
    rw [smul_smul, inv_mul_cancel₀ hε, one_smul] at h'
    exact h'
  · have h := hP.scomp τ hlin
    have h' : HasDerivAt (scaledMomentum ε P)
        (ε • (ε⁻¹ • G (ε⁻¹ • Y (ε * τ)) + Fs (Y (ε * τ)))) τ := h
    rw [smul_add, smul_smul, mul_inv_cancel₀ hε, one_smul] at h'
    exact h'

/-- The perturbation produced by the rescaling is `O(ε)`: bounded by `ε R` when the slowly
varying force is bounded by `R`. -/
theorem norm_scaled_perturbation_le {ε R : ℝ} (hε : 0 ≤ ε) {Fs : E → E} {y : E}
    (hFs : ‖Fs y‖ ≤ R) : ‖ε • Fs y‖ ≤ ε * R := by
  rw [norm_smul, Real.norm_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left hFs hε

/-! ### The scaled-junction perturbation lemma -/

/-- The phase-space vector field `(y, p) ↦ (p, G y)` of a junction with force field `G`. -/
def junctionField (G : E → E) : E × E → E × E := fun z => (z.2, G z.1)

omit [NormedSpace ℝ E] in
/-- A Lipschitz force field on a region `S` gives a Lipschitz phase-space field on `S × E`. -/
theorem lipschitzOnWith_junctionField {G : E → E} {S : Set E} {K : ℝ≥0}
    (hG : LipschitzOnWith K G S) :
    LipschitzOnWith (max 1 K) (junctionField G) (S ×ˢ (univ : Set E)) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have h1 : dist x.2 y.2 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h2 : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h3 := hG.dist_le_mul x.1 hx.1 y.1 hy.1
  have hcoe : ((max 1 K : ℝ≥0) : ℝ) = max 1 (K : ℝ) := by simp [NNReal.coe_max]
  rw [hcoe]
  change max (dist x.2 y.2) (dist (G x.1) (G y.1)) ≤ _
  apply max_le
  · calc dist x.2 y.2 ≤ dist x y := h1
      _ ≤ max 1 (K : ℝ) * dist x y := le_mul_of_one_le_left dist_nonneg (le_max_left _ _)
  · calc dist (G x.1) (G y.1) ≤ K * dist x.1 y.1 := h3
      _ ≤ K * dist x y := mul_le_mul_of_nonneg_left h2 K.coe_nonneg
      _ ≤ max 1 (K : ℝ) * dist x y :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg

/-- **Scaled-junction perturbation lemma.**  Let `z` be an exact solution of `y' = p`,
`p' = G(y)` and `zε` an approximate solution with error `ρ` (e.g. `ρ = εR` after rescaling),
both on `[a, b]`, with configurations in a region `S` on which `G` is `K`-Lipschitz.  If
`dist (zε a) (z a) ≤ δ` then `dist (zε τ) (z τ) ≤ (δ + ρ (b - a)) exp (max 1 K · (b - a))`
for every `τ ∈ [a, b]`. -/
theorem dist_le_of_perturbed_junction {G : E → E} {S : Set E} {K : ℝ≥0}
    (hG : LipschitzOnWith K G S) {a b ρ δ : ℝ} (hab : a ≤ b) (hρ : 0 ≤ ρ)
    {z zε z' zε' : ℝ → E × E}
    (hz : ContinuousOn z (Icc a b))
    (hz' : ∀ τ ∈ Ico a b, HasDerivWithinAt z (z' τ) (Ici τ) τ)
    (hz_ode : ∀ τ ∈ Ico a b, z' τ = junctionField G (z τ))
    (hzS : ∀ τ ∈ Ico a b, (z τ).1 ∈ S)
    (hzε : ContinuousOn zε (Icc a b))
    (hzε' : ∀ τ ∈ Ico a b, HasDerivWithinAt zε (zε' τ) (Ici τ) τ)
    (hzε_ode : ∀ τ ∈ Ico a b, dist (zε' τ) (junctionField G (zε τ)) ≤ ρ)
    (hzεS : ∀ τ ∈ Ico a b, (zε τ).1 ∈ S)
    (ha : dist (zε a) (z a) ≤ δ) :
    ∀ τ ∈ Icc a b,
      dist (zε τ) (z τ) ≤ (δ + ρ * (b - a)) * Real.exp ((max 1 (K : ℝ)) * (b - a)) := by
  have hK := lipschitzOnWith_junctionField hG
  have hgron := dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => junctionField G)
    (s := fun _ => S ×ˢ (univ : Set E)) (K := max 1 K) (εf := ρ) (εg := 0)
    (fun _ _ => hK) hzε hzε' hzε_ode (fun τ hτ => ⟨hzεS τ hτ, trivial⟩) hz hz'
    (fun τ hτ => by rw [hz_ode τ hτ, dist_self]) (fun τ hτ => ⟨hzS τ hτ, trivial⟩) ha
  intro τ hτ
  have hδ0 : 0 ≤ δ := dist_nonneg.trans ha
  have hcoe : ((max 1 K : ℝ≥0) : ℝ) = max 1 (K : ℝ) := by simp [NNReal.coe_max]
  have hKnn : (0 : ℝ) ≤ max 1 (K : ℝ) := le_trans zero_le_one (le_max_left _ _)
  have h1 := hgron τ hτ
  rw [hcoe, add_zero] at h1
  refine h1.trans ?_
  have h2 : gronwallBound δ (max 1 (K : ℝ)) ρ (τ - a) ≤
      (δ + ρ * (τ - a)) * Real.exp (max 1 (K : ℝ) * (τ - a)) := by
    by_cases hK0 : max 1 (K : ℝ) = 0
    · exact absurd hK0 (by positivity)
    · have hexp := Real.exp_pos (max 1 (K : ℝ) * (τ - a))
      have h1' : Real.exp (max 1 (K : ℝ) * (τ - a)) - 1 ≤
          max 1 (K : ℝ) * (τ - a) * Real.exp (max 1 (K : ℝ) * (τ - a)) := by
        have h := Real.add_one_le_exp (-(max 1 (K : ℝ) * (τ - a)))
        rw [Real.exp_neg] at h
        have h2 := mul_le_mul_of_nonneg_right h hexp.le
        rw [inv_mul_cancel₀ hexp.ne'] at h2
        linarith
      have h3 : ρ / max 1 (K : ℝ) * (Real.exp (max 1 (K : ℝ) * (τ - a)) - 1) ≤
          ρ * (τ - a) * Real.exp (max 1 (K : ℝ) * (τ - a)) := by
        calc ρ / max 1 (K : ℝ) * (Real.exp (max 1 (K : ℝ) * (τ - a)) - 1)
            ≤ ρ / max 1 (K : ℝ) *
                (max 1 (K : ℝ) * (τ - a) * Real.exp (max 1 (K : ℝ) * (τ - a))) :=
              mul_le_mul_of_nonneg_left h1' (div_nonneg hρ hKnn)
          _ = ρ * (τ - a) * Real.exp (max 1 (K : ℝ) * (τ - a)) := by
              field_simp
      simp only [gronwallBound_of_K_ne_0 hK0]
      have hexpand : (δ + ρ * (τ - a)) * Real.exp (max 1 (K : ℝ) * (τ - a)) =
          δ * Real.exp (max 1 (K : ℝ) * (τ - a)) +
            ρ * (τ - a) * Real.exp (max 1 (K : ℝ) * (τ - a)) := by ring
      rw [hexpand]
      linarith
  refine h2.trans ?_
  apply mul_le_mul
  · have : ρ * (τ - a) ≤ ρ * (b - a) := mul_le_mul_of_nonneg_left (by linarith [hτ.2]) hρ
    linarith
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hτ.2]) hKnn)
  · exact (Real.exp_pos _).le
  · have : 0 ≤ ρ * (b - a) := mul_nonneg hρ (by linarith)
    linarith

/-! ### Channel stability and dwell time -/

/-- **Channel stability.**  If the reference exit state `z` lies in the exit basin of the
channel `i` with margin `m` (the ball of radius `m` around `z` is contained in the basin) and the
basins of distinct channels are disjoint, then every state within `m` of `z` exits through the
channel `i` and through no competing channel. -/
theorem channel_stability {X : Type*} [PseudoMetricSpace X] {ι : Type*} (B : ι → Set X)
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j)) {i : ι} {z : X} {m : ℝ}
    (hmargin : ball z m ⊆ B i) {z' : X} (hz' : dist z' z < m) :
    z' ∈ B i ∧ ∀ i', i' ≠ i → z' ∉ B i' := by
  have hmem : z' ∈ B i := hmargin (mem_ball.mpr hz')
  refine ⟨hmem, fun i' hi' hmem' => ?_⟩
  exact Set.disjoint_left.mp (hdisj hi') hmem' hmem

/-- **Vanishing physical junction time.**  If the scaled dwell time is at most `T`, the
physical dwell time `t_out - t_in = ε (τ_out - τ_in)` is at most `ε T`: it vanishes as
`ε → 0⁺`. -/
theorem physical_dwell_le {ε T τ_in τ_out t_in t_out : ℝ} (hε : 0 ≤ ε)
    (hdwell : τ_out - τ_in ≤ T) (hin : t_in = ε * τ_in) (hout : t_out = ε * τ_out) :
    t_out - t_in ≤ ε * T := by
  rw [hin, hout, ← mul_sub]
  exact mul_le_mul_of_nonneg_left hdwell hε

/-! ### Reference junctions -/

/-- A reference Hamiltonian junction `J_v` at the vertex `v`: a force field `G = -∇W_v` on the
configuration space `E`, Lipschitz on the region `region` visited by well-prepared trajectories,
pairwise disjoint exit basins in phase space for the incident edge-ends, and the longitudinal
momentum read off in each channel (Lipschitz in the phase-space state). -/
structure ReferenceJunction (Γ : FiniteMetricGraph) (v : Γ.Vertex) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  force : E → E
  region : Set E
  K : ℝ≥0
  lipschitz : LipschitzOnWith K force region
  basin : Γ.IncidentEnds v → Set (E × E)
  basin_disjoint : Pairwise fun ζ ζ' => Disjoint (basin ζ) (basin ζ')
  channelMomentum : Γ.IncidentEnds v → E × E → ℝ
  Λ : ℝ≥0
  channelMomentum_lipschitz : ∀ ζ, LipschitzWith Λ (channelMomentum ζ)

/-- **The four uniform junction properties of the theorem**, for a well-prepared incoming state
in channel `η` with speed `r`: a reference passage is a solution `z` of the reference dynamics
on `[0, τ_out]` (configurations in the region) such that

1. it exits through the basin of `F_v η` — the unique routed channel;
2. the exit is separated from competing basins by a positive margin `m` (transverse, uniformly
   separated exit);
3. the scaled dwell time `τ_out` is at most `T`;
4. the exit longitudinal speed is within `κ` of the incoming speed `r`.

The constants `T`, `m`, `κ` are the uniform constants over the energy window. -/
structure ReferencePassage {Γ : FiniteMetricGraph} {v : Γ.Vertex}
    (J : ReferenceJunction Γ v E) (F : RoutingLaw Γ) (η : Γ.IncidentEnds v)
    (r T m κ : ℝ) where
  τ_out : ℝ
  τ_out_nonneg : 0 ≤ τ_out
  τ_out_le : τ_out ≤ T
  z : ℝ → E × E
  continuousOn : ContinuousOn z (Icc 0 τ_out)
  hasDerivWithinAt : ∀ τ ∈ Ico 0 τ_out, HasDerivWithinAt z (junctionField J.force (z τ)) (Ici τ) τ
  region : ∀ τ ∈ Ico 0 τ_out, (z τ).1 ∈ J.region
  exit_margin : ball (z τ_out) m ⊆ J.basin (F.route v η)
  exit_speed : |(|J.channelMomentum (F.route v η) (z τ_out)| - r)| ≤ κ

namespace ReferencePassage

variable {Γ : FiniteMetricGraph} {v : Γ.Vertex} {J : ReferenceJunction Γ v E} {F : RoutingLaw Γ}
  {η : Γ.IncidentEnds v} {r T m κ : ℝ}

/-- **Scaled exit.**  Let `zε` be the scaled trajectory of the `ε`-router: an approximate
solution of the reference dynamics with error `ρ` (`ρ = εR` by the rescaling lemma), started
within `δ` of the reference passage.  If `(δ + ρ T) exp (max 1 K · T) < m` (true for `ε`, `δ`
small), then at the reference exit time the scaled trajectory

* lies in the exit basin of `F_v η` and in no competing basin (channel stability), and
* has longitudinal speed within `κ + Λ (δ + ρ T) exp (max 1 K · T)` of the incoming speed.

Together with `physical_dwell_le` these are exactly the router properties
`edge_succ`, `depart_mom` and `start_succ_le` of a hybrid chain with
`dwell = εT` and `momErr = κ + Λ (δ + ρ T) exp (max 1 K · T)`. -/
theorem scaled_exit (ref : ReferencePassage J F η r T m κ) {ρ δ : ℝ} (hρ : 0 ≤ ρ)
    {zε zε' : ℝ → E × E}
    (hcont : ContinuousOn zε (Icc 0 ref.τ_out))
    (hderiv : ∀ τ ∈ Ico 0 ref.τ_out, HasDerivWithinAt zε (zε' τ) (Ici τ) τ)
    (hode : ∀ τ ∈ Ico 0 ref.τ_out, dist (zε' τ) (junctionField J.force (zε τ)) ≤ ρ)
    (hregion : ∀ τ ∈ Ico 0 ref.τ_out, (zε τ).1 ∈ J.region)
    (hinit : dist (zε 0) (ref.z 0) ≤ δ)
    (hsmall : (δ + ρ * T) * Real.exp (max 1 (J.K : ℝ) * T) < m) :
    zε ref.τ_out ∈ J.basin (F.route v η) ∧
    (∀ ζ, ζ ≠ F.route v η → zε ref.τ_out ∉ J.basin ζ) ∧
    |(|J.channelMomentum (F.route v η) (zε ref.τ_out)| - r)| ≤
      κ + J.Λ * ((δ + ρ * T) * Real.exp (max 1 (J.K : ℝ) * T)) := by
  have hclose := dist_le_of_perturbed_junction J.lipschitz ref.τ_out_nonneg hρ ref.continuousOn
    ref.hasDerivWithinAt (fun _ _ => rfl) ref.region hcont hderiv hode hregion hinit ref.τ_out
    (right_mem_Icc.mpr ref.τ_out_nonneg)
  have hδ0 : 0 ≤ δ := dist_nonneg.trans hinit
  have hKnn : (0 : ℝ) ≤ max 1 (J.K : ℝ) := le_trans zero_le_one (le_max_left _ _)
  have hmono : (δ + ρ * (ref.τ_out - 0)) * Real.exp (max 1 (J.K : ℝ) * (ref.τ_out - 0)) ≤
      (δ + ρ * T) * Real.exp (max 1 (J.K : ℝ) * T) := by
    apply mul_le_mul
    · have := mul_le_mul_of_nonneg_left ref.τ_out_le hρ
      linarith
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ref.τ_out_le]) hKnn)
    · exact (Real.exp_pos _).le
    · have : 0 ≤ ρ * T := mul_nonneg hρ (ref.τ_out_nonneg.trans ref.τ_out_le)
      linarith
  have hdist : dist (zε ref.τ_out) (ref.z ref.τ_out) ≤
      (δ + ρ * T) * Real.exp (max 1 (J.K : ℝ) * T) := hclose.trans hmono
  obtain ⟨h1, h2⟩ := channel_stability J.basin J.basin_disjoint ref.exit_margin
    (lt_of_le_of_lt hdist hsmall)
  refine ⟨h1, h2, ?_⟩
  have hlip := (J.channelMomentum_lipschitz (F.route v η)).dist_le_mul (zε ref.τ_out)
    (ref.z ref.τ_out)
  have habs : |(|J.channelMomentum (F.route v η) (zε ref.τ_out)| -
      |J.channelMomentum (F.route v η) (ref.z ref.τ_out)|)| ≤
      J.Λ * ((δ + ρ * T) * Real.exp (max 1 (J.K : ℝ) * T)) := by
    calc |(|J.channelMomentum (F.route v η) (zε ref.τ_out)| -
          |J.channelMomentum (F.route v η) (ref.z ref.τ_out)|)|
        ≤ |J.channelMomentum (F.route v η) (zε ref.τ_out) -
            J.channelMomentum (F.route v η) (ref.z ref.τ_out)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = dist (J.channelMomentum (F.route v η) (zε ref.τ_out))
            (J.channelMomentum (F.route v η) (ref.z ref.τ_out)) := (Real.dist_eq _ _).symm
      _ ≤ J.Λ * dist (zε ref.τ_out) (ref.z ref.τ_out) := hlip
      _ ≤ J.Λ * ((δ + ρ * T) * Real.exp (max 1 (J.K : ℝ) * T)) :=
          mul_le_mul_of_nonneg_left hdist J.Λ.coe_nonneg
  have hexit := ref.exit_speed
  calc |(|J.channelMomentum (F.route v η) (zε ref.τ_out)| - r)|
      = |(|J.channelMomentum (F.route v η) (zε ref.τ_out)| -
          |J.channelMomentum (F.route v η) (ref.z ref.τ_out)|) +
          (|J.channelMomentum (F.route v η) (ref.z ref.τ_out)| - r)| := by ring_nf
    _ ≤ |(|J.channelMomentum (F.route v η) (zε ref.τ_out)| -
          |J.channelMomentum (F.route v η) (ref.z ref.τ_out)|)| +
          |(|J.channelMomentum (F.route v η) (ref.z ref.τ_out)| - r)| := abs_add_le _ _
    _ ≤ J.Λ * ((δ + ρ * T) * Real.exp (max 1 (J.K : ℝ) * T)) + κ := add_le_add habs hexit
    _ = κ + J.Λ * ((δ + ρ * T) * Real.exp (max 1 (J.K : ℝ) * T)) := by ring

end ReferencePassage

end HamiltonianMetricGraphs
