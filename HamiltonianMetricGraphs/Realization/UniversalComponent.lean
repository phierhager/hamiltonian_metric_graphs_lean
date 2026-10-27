/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalComponentFlow
import HamiltonianMetricGraphs.Realization.UniversalComponentPotential
import HamiltonianMetricGraphs.Realization.UniversalComponentBilliard

/-!
# Realization at zero potential (Proposition IX.11), as printed

This file proves Proposition IX.11 of the paper in its printed form
(`universal_reversible_realization_paper`): the components `R_1, …, R_m` of the resolved space
`R(Γ, F)` are laid out along the lines `w = i` of `ℝ²`, one corridor per component, the potential
is `W^F_ε` of Sec. IX.F, and the microscopic trajectories are read through the maps `ι_i` with the
orientations `o_i`.  The limit is the paper's graph flow `Φ_t` (`graphFlow`, i.e.
`FlightState.trajectory` with the vertex law `S^F = F.toBorelScattering 0`).

## The proof

* **Confinement** (`prepared_confined`): `H_ε(z_ε) ≤ 2 + ε < 4 ≤ W^F_ε` on `|w - i| = 2ε`, so the
  trajectory stays in the tube of corridor `i`, for all real times;
* **separation**: in the tube `u_ε` solves `ü = -P_{ε,i}'(u)` at energy `½ ξ_{u,ε}²`.  For a circle
  this is free motion (`circle_free`); for an interval it is the billiard up to excursions of
  length `O(ε)` (`billiard_good`, `UniversalComponentBilliard.lean`);
* **the lifted flow** (`lift_flow`, `UniversalComponentFlow.lean`): `Φ_t(z)` is the unrolled orbit
  at `s(t) = u₀ + v₀ t`, and its vertex impacts are the times at which `s(t)` is a glued point;
* **comparison** (`component_realization_core`): on a compact `I` without impacts, `s(I)` keeps a
  positive distance from the glued points; for small `ε` the lifted microscopic position
  `ρ u_ε(t) + 2 L n` is in the same segment as `s(t)`, which places `ι_i(u_ε(t))` on the edge of
  `Φ_t(z)` and gives the uniform convergence.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {Γ : FiniteMetricGraph} {F : RoutingLaw Γ}

/-! ### A prepared state at one scale -/

section Scale

variable {i : Fin (RoutingLaw.compCount F)} {ε : ℝ}

/-- The prepared states of Proposition IX.11 at the scale `ε`: `u_ε ∈ Λ_i`, `½ ξ_u² ∈ K⋆`,
`|w_ε - i| ≤ 2ε` and `½ ξ_w² + A_ε(w_ε - i) ≤ ε`. -/
def IsPreparedState (F : RoutingLaw Γ) (i : Fin (RoutingLaw.compCount F)) (ε : ℝ)
    (y q : ℝ × ℝ) : Prop :=
  y.1 ∈ compDomain F i ∧ q.1 ^ 2 / 2 ∈ Icc (1 / 2 : ℝ) 2 ∧ |y.2 - compRow F i| ≤ 2 * ε ∧
    q.2 ^ 2 / 2 + wellPot ε (y.2 - compRow F i) ≤ ε

/-- A prepared state is strictly inside its tube, below the wall height `4`. -/
theorem IsPreparedState.energy {y q : ℝ × ℝ} (h : IsPreparedState F i ε y q) (hε : 0 < ε)
    (hεs : ε < 1 / 8) :
    |y.2 - compRow F i| < 2 * ε ∧ hamEnergy (resolvedPot F ε) y q < 4 := by
  obtain ⟨hdom, hK, htube, htr⟩ := h
  refine ⟨?_, ?_⟩
  · rcases lt_or_eq_of_le htube with h | h
    · exact h
    · exfalso
      have h4 : wellPot ε (y.2 - compRow F i) = 4 := wellPot_of_two_le_abs hε h.ge
      nlinarith [sq_nonneg q.2]
  · have hpot := resolvedPot_of_tube F hε hεs.le i (u := y.1) htube
    rw [resolvedCap_eq_zero F hε hdom, add_zero] at hpot
    rw [hamEnergy, show y = (y.1, y.2) from rfl, hpot]
    nlinarith [hK.2, sq_nonneg q.2]

/-- **Confinement for all real times.** -/
theorem prepared_confined {x p : ℝ → ℝ × ℝ} (hε : 0 < ε) (hεs : ε < 1 / 8)
    (hsol : IsHamiltonianFlowLine (resolvedPot F ε) x p)
    (h0 : IsPreparedState F i ε (x 0) (p 0)) : ∀ t, |(x t).2 - compRow F i| < 2 * ε := by
  obtain ⟨hstrict, hE⟩ := h0.energy hε hεs
  have hfwd := resolved_confined F hε hεs.le hsol.forward i hstrict hE
  have hbwd := resolved_confined F hε hεs.le hsol.reverse.forward i
    (by simpa using hstrict) (by simpa [hamEnergy] using hE)
  intro t
  rcases le_total 0 t with ht | ht
  · exact hfwd t ht
  · simpa using hbwd (-t) (by linarith)

/-- **In a circle corridor the motion is free.** -/
theorem circle_free {x p : ℝ → ℝ × ℝ} (hε : 0 < ε) (hεs : ε < 1 / 8)
    (hsol : IsHamiltonianTrajectory (resolvedPot F ε) x p)
    (hconf : ∀ t, 0 ≤ t → |(x t).2 - compRow F i| < 2 * ε) (hc : ¬ IsIntervalComp F i)
    {t : ℝ} (ht : 0 ≤ t) : (p t).1 = (p 0).1 ∧ (x t).1 = (x 0).1 + (p 0).1 * t := by
  have hlong := fun s (hs : 0 ≤ s) => resolved_longitudinal F hε hεs.le hsol i hconf hs
  have hzero : ∀ s, 0 ≤ s → HasDerivWithinAt (fun r => (p r).1) 0 (Ici 0) s := by
    intro s hs
    have h := (hlong s hs).2
    rwa [resolvedCap_of_circle F hc, deriv_const, neg_zero] at h
  have hpconst : ∀ s, 0 ≤ s → (p s).1 = (p 0).1 := by
    intro s hs
    have hcont : ContinuousOn (fun r => (p r).1) (Icc 0 s) := fun r hr =>
      (hzero r hr.1).continuousWithinAt.mono Icc_subset_Ici_self
    exact constant_of_has_deriv_right_zero hcont
      (fun r hr => (hzero r hr.1).mono (Ici_subset_Ici.mpr hr.1)) s ⟨hs, le_rfl⟩
  refine ⟨hpconst t ht, ?_⟩
  have hd : ∀ s, 0 ≤ s → HasDerivWithinAt (fun r => (x r).1 - (p 0).1 * r) 0 (Ici 0) s := by
    intro s hs
    have h1 := (hlong s hs).1
    rw [hpconst s hs] at h1
    exact (h1.sub ((hasDerivWithinAt_id s (Ici 0)).const_mul ((p 0).1))).congr_deriv (by ring)
  have hcont : ContinuousOn (fun r => (x r).1 - (p 0).1 * r) (Icc 0 t) := fun r hr =>
    (hd r hr.1).continuousWithinAt.mono Icc_subset_Ici_self
  have h := constant_of_has_deriv_right_zero hcont
    (fun r hr => (hd r hr.1).mono (Ici_subset_Ici.mpr hr.1)) t ⟨ht, le_rfl⟩
  simp only [mul_zero, sub_zero] at h
  linarith

/-- **In an interval corridor the longitudinal motion is a corridor solution.** -/
theorem interval_corridorSolution {x p : ℝ → ℝ × ℝ} (hε : 0 < ε) (hεs : ε < 1 / 8)
    (hsol : IsHamiltonianTrajectory (resolvedPot F ε) x p)
    (hconf : ∀ t, 0 ≤ t → |(x t).2 - compRow F i| < 2 * ε) (hc : IsIntervalComp F i)
    (hlen : 1000 * ε ≤ compLen F i) (hdom : (x 0).1 ∈ compDomain F i)
    (hK : (p 0).1 ^ 2 / 2 ∈ Icc (1 / 2 : ℝ) 2) {Tmax : ℝ} (hT : 0 ≤ Tmax) :
    CorridorSolution ε (compLen F i) |(p 0).1| Tmax (fun s => (x s).1) (fun s => (p s).1) := by
  have hlong := fun s (hs : 0 ≤ s) => resolved_longitudinal F hε hεs.le hsol i hconf hs
  rw [resolvedCap_of_interval F hc] at hlong
  have hu : ∀ t ∈ Icc (0 : ℝ) Tmax, HasDerivWithinAt (fun s => (x s).1) (p t).1 (Icc 0 Tmax) t :=
    fun t ht => (hlong t ht.1).1.mono Icc_subset_Ici_self
  have hpu : ∀ t ∈ Icc (0 : ℝ) Tmax, HasDerivWithinAt (fun s => (p s).1)
      (-deriv (corridorPot ε (compLen F i)) (x t).1) (Icc 0 Tmax) t :=
    fun t ht => (hlong t ht.1).2.mono Icc_subset_Ici_self
  have hsq : (1 : ℝ) ≤ (p 0).1 ^ 2 ∧ (p 0).1 ^ 2 ≤ 4 := ⟨by linarith [hK.1], by linarith [hK.2]⟩
  rw [compDomain_of_interval F hc] at hdom
  exact
    { eps_pos := hε
      len := hlen
      c_ge := by
        rw [← Real.sqrt_sq_eq_abs]
        calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
          _ ≤ Real.sqrt ((p 0).1 ^ 2) := Real.sqrt_le_sqrt hsq.1
      c_le := by
        rw [← Real.sqrt_sq_eq_abs]
        calc Real.sqrt ((p 0).1 ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hsq.2
          _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      time_nonneg := hT
      ode_pos := hu
      ode_mom := hpu
      energy := by
        intro t ht
        have h := energy1D_eq (contDiff_corridorPot ε (compLen F i) (n := 1)) hu hpu t ht
        rw [energy1D, energy1D] at h
        rw [h, corridorPot_of_mem hε hdom.1 hdom.2, sq_abs]
        ring }

end Scale

/-! ### Compactness margin -/

theorem exists_margin {I : Set ℝ} (hI : IsCompact I) {s : ℝ → ℝ} (hs : Continuous s)
    {G : Set ℝ} (hG : IsClosed G) (hGne : G.Nonempty) (hIG : ∀ t ∈ I, s t ∉ G) :
    ∃ η > 0, ∀ t ∈ I, η ≤ Metric.infDist (s t) G := by
  rcases I.eq_empty_or_nonempty with hI0 | hIne
  · exact ⟨1, one_pos, fun t ht => by rw [hI0] at ht; exact absurd ht (notMem_empty t)⟩
  · have hcont : ContinuousOn (fun t => Metric.infDist (s t) G) I :=
      ((Metric.continuous_infDist_pt G).comp hs).continuousOn
    obtain ⟨t₀, ht₀, hmin⟩ := hI.exists_isMinOn hIne hcont
    refine ⟨Metric.infDist (s t₀) G, (hG.notMem_iff_infDist_pos hGne).mp (hIG t₀ ht₀),
      fun t ht => hmin ht⟩

/-! ### The core convergence -/

/-- **The comparison at small scales.**  For every `r > 0`, at all small `ε` and all `t ∈ I`, the
microscopic position `u_ε(t)` lies in `Λ_i` and has a lift `y'` within `r` of `s(t) = u₀ + v₀ t`,
through which `ι_i`, `Z_i` and `o_i u̇_ε` are read. -/
theorem component_realization_key (i : Fin (RoutingLaw.compCount F)) {u₀ v₀ : ℝ}
    (hu₀ : u₀ ∈ compDomain F i) (hu₀g : u₀ ∉ gluedSet F (compBase F i))
    (hv₀ : v₀ ^ 2 / 2 ∈ Icc (1 / 2 : ℝ) 2) {x p : ℝ → ℝ → ℝ × ℝ}
    (hprep : ∀ ε, 0 < ε → ε < 1 / 8 → IsPreparedState F i ε (x ε 0) (p ε 0))
    (hsol : ∀ ε, 0 < ε → ε < 1 / 8 → IsHamiltonianTrajectory (resolvedPot F ε) (x ε) (p ε))
    (hlim : Tendsto (fun ε => ((x ε 0).1, (p ε 0).1)) (𝓝[>] 0) (𝓝 (u₀, v₀)))
    {I : Set ℝ} {T η : ℝ} (hT : 0 ≤ T) (hIT : ∀ t ∈ I, t ∈ Icc 0 T) (hη : 0 < η)
    (hmargin : ∀ t ∈ I, η ≤ Metric.infDist (u₀ + v₀ * t) (gluedSet F (compBase F i)))
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), |(p ε 0).1 - v₀| < r ∧ ∀ t ∈ I, ∃ y' : ℝ,
      |y' - (u₀ + v₀ * t)| < r ∧ (x ε t).1 ∈ compDomain F i ∧
      compMap F i (x ε t).1 = unroll F (compBase F i) y' ∧
      ((x ε t).1 ∈ gluedSet F (compBase F i) ↔ y' ∈ gluedSet F (compBase F i)) ∧
      (y' ∉ gluedSet F (compBase F i) →
        compSign F i (x ε t).1 * (p ε t).1 = unrollSign F (compBase F i) y' * (p ε 0).1) := by
  set β := compBase F i
  set U : ℝ → ℝ := fun ε => (x ε 0).1
  set Ξ : ℝ → ℝ := fun ε => (p ε 0).1
  have hU : Tendsto U (𝓝[>] 0) (𝓝 u₀) := (continuous_fst.tendsto _).comp hlim
  have hΞ : Tendsto Ξ (𝓝[>] 0) (𝓝 v₀) := (continuous_snd.tendsto _).comp hlim
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hv1 : 1 ≤ |v₀| := by
    have : (1 : ℝ) ≤ v₀ ^ 2 := by linarith [hv₀.1]
    nlinarith [sq_abs v₀, abs_nonneg v₀]
  -- the number of excursions on `[0, T]` and the error
  obtain ⟨K, hK⟩ : ∃ K : ℕ, T < ((K : ℝ) - 1) * (compLen F i / 4) := by
    have hL := compLen_pos F i
    obtain ⟨K, hK⟩ := exists_nat_gt (4 * T / compLen F i + 1)
    refine ⟨K, ?_⟩
    have : 4 * T / compLen F i < (K : ℝ) - 1 := by linarith
    rw [div_lt_iff₀ hL] at this
    linarith
  have herr : Tendsto (fun ε => ((K : ℝ) + 1) * (216 * ε) + |U ε - u₀| + (T + 1) * |Ξ ε - v₀|)
      (𝓝[>] 0) (𝓝 0) := by
    have := (((hid.const_mul 216).const_mul ((K : ℝ) + 1)).add ((hU.sub_const u₀).abs)).add
      (((hΞ.sub_const v₀).abs).const_mul (T + 1))
    simpa using this
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ((K : ℝ) + 1) * (216 * ε) + |U ε - u₀| + (T + 1) * |Ξ ε - v₀| < min (min r η) 1 :=
    herr.eventually (gt_mem_nhds (lt_min (lt_min hr hη) one_pos))
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 / 8 ∧ 100 * ε ≤ 1 :=
    eventually_nhdsGT_zero_of_forall_Ioo (by norm_num : (0 : ℝ) < 1 / 1000)
      fun ε hε => ⟨hε.1, by linarith [hε.2], by linarith [hε.2]⟩
  -- the deviation of the free lift
  have hdev : ∀ ε t, t ∈ Icc 0 T → |(U ε + Ξ ε * t) - (u₀ + v₀ * t)| ≤
      |U ε - u₀| + (T + 1) * |Ξ ε - v₀| := by
    intro ε t ht
    have : (U ε + Ξ ε * t) - (u₀ + v₀ * t) = (U ε - u₀) + (Ξ ε - v₀) * t := by ring
    rw [this]
    calc |(U ε - u₀) + (Ξ ε - v₀) * t| ≤ |U ε - u₀| + |(Ξ ε - v₀) * t| := abs_add_le _ _
      _ = |U ε - u₀| + |Ξ ε - v₀| * t := by rw [abs_mul, abs_of_nonneg ht.1]
      _ ≤ |U ε - u₀| + (T + 1) * |Ξ ε - v₀| := by
          nlinarith [abs_nonneg (Ξ ε - v₀), ht.2]
  by_cases hint : IsIntervalComp F i
  · -- an interval component
    have hL := compLen_pos F i
    have hu₀' : u₀ ∈ Ioo 0 (compLen F i) := by
      rw [compDomain_of_interval F hint] at hu₀
      obtain ⟨h0, hLg⟩ := endpoints_mem_compVertexSet F hint
      rw [mem_compVertexSet_iff] at h0 hLg
      exact ⟨lt_of_le_of_ne hu₀.1 (fun h => hu₀g (h ▸ h0.2)),
        lt_of_le_of_ne hu₀.2 (fun h => hu₀g (h.symm ▸ hLg.2))⟩
    have hlen : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 1000 * ε ≤ compLen F i :=
      eventually_nhdsGT_zero_of_forall_Ioo (by positivity : 0 < compLen F i / 1000)
        fun ε hε => by linarith [hε.2]
    have hlo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 8 * ε < U ε := by
      have := hU.sub (hid.const_mul 8)
      rw [mul_zero, sub_zero] at this
      filter_upwards [this.eventually (lt_mem_nhds hu₀'.1)] with ε hε using by linarith
    have hhi : ∀ᶠ ε in 𝓝[>] (0 : ℝ), U ε < compLen F i - 8 * ε := by
      have := (tendsto_const_nhds (x := compLen F i)).sub (hid.const_mul 8) |>.sub hU
      rw [mul_zero, sub_zero] at this
      filter_upwards [this.eventually (lt_mem_nhds (by linarith [hu₀'.2] :
        (0 : ℝ) < compLen F i - u₀))] with ε hε using by linarith
    filter_upwards [hsmall, hpos, hlen, hlo, hhi] with ε hsm hpos' hlenε hloε hhiε
    obtain ⟨hε, hεs, hε100⟩ := hpos'
    have hsm1 : ((K : ℝ) + 1) * (216 * ε) + |U ε - u₀| + (T + 1) * |Ξ ε - v₀| < r :=
      lt_of_lt_of_le hsm (le_trans (min_le_left _ _) (min_le_left _ _))
    have hsm2 : ((K : ℝ) + 1) * (216 * ε) + |U ε - u₀| + (T + 1) * |Ξ ε - v₀| < η :=
      lt_of_lt_of_le hsm (le_trans (min_le_left _ _) (min_le_right _ _))
    have hsm3 : ((K : ℝ) + 1) * (216 * ε) + |U ε - u₀| + (T + 1) * |Ξ ε - v₀| < 1 :=
      lt_of_lt_of_le hsm (min_le_right _ _)
    have hKε : 0 ≤ ((K : ℝ) + 1) * (216 * ε) := by positivity
    have hTε : 0 ≤ (T + 1) * |Ξ ε - v₀| := by positivity
    have hΞv : |Ξ ε - v₀| < r := by
      have : |Ξ ε - v₀| ≤ (T + 1) * |Ξ ε - v₀| := by nlinarith [abs_nonneg (Ξ ε - v₀)]
      linarith [abs_nonneg (U ε - u₀)]
    refine ⟨hΞv, ?_⟩
    obtain ⟨hdomε, hKε', -, -⟩ := hprep ε hε hεs
    have hconf : ∀ t, 0 ≤ t → |(x ε t).2 - compRow F i| < 2 * ε := by
      obtain ⟨hstrict, hE⟩ := (hprep ε hε hεs).energy hε hεs
      exact resolved_confined F hε hεs.le (hsol ε hε hεs) i hstrict hE
    have hS := interval_corridorSolution (Tmax := T + 1) hε hεs (hsol ε hε hεs) hconf hint hlenε
      hdomε hKε' (by linarith)
    -- the sign of the speed
    have hΞ0 : Ξ ε ≠ 0 := by
      intro h0
      have : |Ξ ε - v₀| < 1 := by
        have : |Ξ ε - v₀| ≤ (T + 1) * |Ξ ε - v₀| := by nlinarith [abs_nonneg (Ξ ε - v₀)]
        linarith [abs_nonneg (U ε - u₀)]
      rw [h0, zero_sub, abs_neg] at this
      linarith
    set σ : ℤ := if 0 < Ξ ε then 1 else -1 with hσdef
    have hσ : σ = 1 ∨ σ = -1 := by rw [hσdef]; split_ifs <;> simp
    have hσΞ : Ξ ε = σ * |Ξ ε| := by
      rw [hσdef]
      split_ifs with h
      · push_cast; rw [abs_of_pos h, one_mul]
      · push_cast; rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hΞ0)]; ring
    have hgood := billiard_good hS hσ (by rw [← hσΞ]) ⟨hloε.le, hhiε.le⟩ hT (by linarith) hK
    intro t ht
    have htT := hIT t ht
    have hdevt := hdev ε t htT
    rcases hgood t htT with ⟨M, hM⟩ | ⟨n, ρ, hρ, hut, hlift, hpt⟩
    · exfalso
      have hML : (M : ℝ) * compLen F i ∈ gluedSet F β := by
        rw [mul_comm]; exact mul_len_mem_gluedSet hint M
      have hd := Metric.infDist_le_dist_of_mem (x := u₀ + v₀ * t) hML
      rw [Real.dist_eq] at hd
      have hm := hmargin t ht
      have hσc : (U ε) + σ * |Ξ ε| * t = U ε + Ξ ε * t := by rw [← hσΞ]
      change |(x ε 0).1 + σ * |Ξ ε| * t - M * compLen F i| ≤ _ at hM
      rw [show (x ε 0).1 = U ε from rfl, hσc] at hM
      have : |u₀ + v₀ * t - M * compLen F i| ≤
          |(U ε + Ξ ε * t) - (u₀ + v₀ * t)| + |U ε + Ξ ε * t - M * compLen F i| := by
        rw [abs_sub_comm (U ε + Ξ ε * t) (u₀ + v₀ * t)]
        exact abs_sub_le _ _ _
      linarith
    · refine ⟨ρ * (x ε t).1 + 2 * compLen F i * n, ?_, ?_, ?_, ?_, ?_⟩
      · have hσc : (U ε) + σ * |Ξ ε| * t = U ε + Ξ ε * t := by rw [← hσΞ]
        change |ρ * (x ε t).1 + 2 * compLen F i * n - ((x ε 0).1 + σ * |Ξ ε| * t)| ≤ _ at hlift
        rw [show (x ε 0).1 = U ε from rfl, hσc] at hlift
        have : |ρ * (x ε t).1 + 2 * compLen F i * n - (u₀ + v₀ * t)| ≤
            |ρ * (x ε t).1 + 2 * compLen F i * n - (U ε + Ξ ε * t)| +
              |(U ε + Ξ ε * t) - (u₀ + v₀ * t)| := abs_sub_le _ _ _
        have hKle : (K : ℝ) * (216 * ε) ≤ ((K : ℝ) + 1) * (216 * ε) := by nlinarith
        linarith
      · rw [compDomain_of_interval F hint]; exact hut
      · rw [compMap]
        exact ((unroll_symm hint (by rcases hρ with h | h <;> rw [h] <;> norm_num) n _).1).symm
      · exact ((unroll_symm hint (by rcases hρ with h | h <;> rw [h] <;> norm_num) n _).2.1).symm
      · intro hng
        have hρ' : (ρ : ℝ) = 1 ∨ (ρ : ℝ) = -1 := by rcases hρ with h | h <;> rw [h] <;> norm_num
        have hsym := unroll_symm hint hρ' n (x ε t).1
        have hng' : (x ε t).1 ∉ gluedSet F β := fun h => hng (hsym.2.1.mpr h)
        rw [hsym.2.2 hng', compSign]
        have hpt' : (p ε t).1 = ρ * σ * |Ξ ε| := hpt
        have hp0 : (p ε 0).1 = σ * |Ξ ε| := hσΞ
        rw [hpt', hp0]
        ring
  · -- a circle component
    filter_upwards [hsmall, hpos] with ε hsm hpos'
    obtain ⟨hε, hεs, -⟩ := hpos'
    have hsm1 : ((K : ℝ) + 1) * (216 * ε) + |U ε - u₀| + (T + 1) * |Ξ ε - v₀| < r :=
      lt_of_lt_of_le hsm (le_trans (min_le_left _ _) (min_le_left _ _))
    have hKε : 0 ≤ ((K : ℝ) + 1) * (216 * ε) := by positivity
    have hΞv : |Ξ ε - v₀| < r := by
      have : |Ξ ε - v₀| ≤ (T + 1) * |Ξ ε - v₀| := by nlinarith [abs_nonneg (Ξ ε - v₀)]
      linarith [abs_nonneg (U ε - u₀)]
    refine ⟨hΞv, ?_⟩
    have hconf : ∀ t, 0 ≤ t → |(x ε t).2 - compRow F i| < 2 * ε := by
      obtain ⟨hstrict, hE⟩ := (hprep ε hε hεs).energy hε hεs
      exact resolved_confined F hε hεs.le (hsol ε hε hεs) i hstrict hE
    intro t ht
    have htT := hIT t ht
    obtain ⟨hpt, hxt⟩ := circle_free hε hεs (hsol ε hε hεs) hconf hint htT.1
    refine ⟨(x ε t).1, ?_, by rw [compDomain_of_circle F hint]; trivial, rfl, Iff.rfl, ?_⟩
    · rw [hxt]
      have := hdev ε t htT
      linarith
    · intro _
      rw [hpt, compSign]

/-- **The core convergence** (forward trajectories on `[0, ∞)`). -/
theorem component_realization_core (i : Fin (RoutingLaw.compCount F)) {u₀ v₀ : ℝ}
    (hu₀ : u₀ ∈ compDomain F i) (hu₀Z : u₀ ∉ compVertexSet F i)
    (hv₀ : v₀ ^ 2 / 2 ∈ Icc (1 / 2 : ℝ) 2) (a : (zeroPotential Γ).FlightState)
    (ha : compMap F i u₀ = GraphPoint.interior a.edge a.state.1)
    (hap : a.state.2 = compSign F i u₀ * v₀) {x p : ℝ → ℝ → ℝ × ℝ}
    (hprep : ∀ ε, 0 < ε → ε < 1 / 8 → IsPreparedState F i ε (x ε 0) (p ε 0))
    (hsol : ∀ ε, 0 < ε → ε < 1 / 8 → IsHamiltonianTrajectory (resolvedPot F ε) (x ε) (p ε))
    (hlim : Tendsto (fun ε => ((x ε 0).1, (p ε 0).1)) (𝓝[>] 0) (𝓝 (u₀, v₀)))
    {I : Set ℝ} (hI : IsCompact I) (hI0 : I ⊆ Ici 0)
    (himp : ∀ t ∈ I, ¬ IsVertexImpact (F.toBorelScattering (zeroPotential Γ)) a t) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ I,
      (x ε t).1 ∈ compDomain F i ∧ (x ε t).1 ∉ compVertexSet F i ∧
      compMap F i (x ε t).1 = GraphPoint.interior
        (graphFlow (F.toBorelScattering (zeroPotential Γ)) a t).1
        (compMap F i (x ε t).1).coord) ∧
    TendstoUniformlyOn
      (fun ε t => ((compMap F i (x ε t).1).coord, compSign F i (x ε t).1 * (p ε t).1))
      (fun t => (graphFlow (F.toBorelScattering (zeroPotential Γ)) a t).2) (𝓝[>] 0) I := by
  set β := compBase F i
  set S := F.toBorelScattering (zeroPotential Γ)
  have hu₀g : u₀ ∉ gluedSet F β := fun h => hu₀Z ((mem_compVertexSet_iff F).mpr ⟨hu₀, h⟩)
  have hseg₀ := seg_mem_Ioo_of_not_mem F β hu₀g
  set k₀ := segIdx F β u₀
  have hv0 : v₀ ≠ 0 := by
    intro h; rw [h] at hv₀; norm_num at hv₀
  -- the graph state `z` is the lifted state at `u₀`
  have hint := unroll_of_mem_Ioo F β hseg₀
  rw [compMap, hint] at ha
  injection ha with he hq
  have hs : a.state = segState F β k₀ u₀ v₀ := by
    refine Prod.ext hq.symm ?_
    rw [hap, segState, compSign, unrollSign_of_mem_Ico F β ⟨hseg₀.1.le, hseg₀.2⟩]
  have hlift := fun t (ht : 0 ≤ t) => lift_flow (β := β) a hseg₀ hv0 he.symm hs ht
  -- the margin of `s(I)` from the glued points
  have hnot : ∀ t ∈ I, u₀ + v₀ * t ∉ gluedSet F β := by
    intro t ht hg
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ t from hI0 ht) with h0 | hpos
    · rw [← h0, mul_zero, add_zero] at hg; exact hu₀g hg
    · exact himp t ht ((hlift t hpos.le).2 hpos hg)
  obtain ⟨η, hη, hmargin⟩ := exists_margin hI (continuous_const.add (continuous_const.mul
    continuous_id)) (isClosed_gluedSet F β) ⟨0, 0, posSeq_zero F β⟩ hnot
  obtain ⟨T₀, hT₀⟩ := hI.bddAbove
  set T := max T₀ 0
  have hT : 0 ≤ T := le_max_right _ _
  have hIT : ∀ t ∈ I, t ∈ Icc 0 T := fun t ht => ⟨hI0 ht, le_trans (hT₀ ht) (le_max_left _ _)⟩
  -- the flow on `I`
  have hflow : ∀ t ∈ I, graphFlow S a t =
      ((germSeq F β (segIdx F β (u₀ + v₀ * t))).1,
        segState F β (segIdx F β (u₀ + v₀ * t)) (u₀ + v₀ * t) v₀) :=
    fun t ht => (hlift t (hI0 ht)).1 (hnot t ht)
  -- reading a lift close to `s(t)`
  have hread : ∀ t ∈ I, ∀ y', |y' - (u₀ + v₀ * t)| < η →
      y' ∉ gluedSet F β ∧ unroll F β y' = GraphPoint.interior (graphFlow S a t).1
        (EdgeEnd.coordinate Γ (germSeq F β (segIdx F β (u₀ + v₀ * t))) -
          EdgeEnd.sign Γ (germSeq F β (segIdx F β (u₀ + v₀ * t))) *
            (posSeq F β (segIdx F β (u₀ + v₀ * t) + 1) - y')) ∧
      unrollSign F β y' = EdgeEnd.sign Γ (germSeq F β (segIdx F β (u₀ + v₀ * t))) := by
    intro t ht y' hy'
    have hseg := seg_mem_Ioo_of_not_mem F β (hnot t ht)
    have hy'seg := mem_seg_of_lt_infDist F β hseg (lt_of_lt_of_le hy' (hmargin t ht))
    refine ⟨?_, ?_, unrollSign_of_mem_Ico F β ⟨hy'seg.1.le, hy'seg.2⟩⟩
    · rintro ⟨k, rfl⟩
      have h1 := (posSeq_lt_iff F β).mp hy'seg.1
      have h2 := (posSeq_lt_iff F β).mp hy'seg.2
      omega
    · rw [unroll_of_mem_Ioo F β hy'seg, hflow t ht]
  refine ⟨?_, ?_⟩
  · filter_upwards [component_realization_key i hu₀ hu₀g hv₀ hprep hsol hlim hT hIT hη hmargin
      hη] with ε hε' t ht
    obtain ⟨-, hε⟩ := hε'
    obtain ⟨y', hy', hdom, hmap, hglue, -⟩ := hε t ht
    obtain ⟨hng, hun, -⟩ := hread t ht y' hy'
    refine ⟨hdom, fun h => hng (hglue.mp ((mem_compVertexSet_iff F).mp h).2), ?_⟩
    rw [hmap, hun]
    rfl
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [component_realization_key i hu₀ hu₀g hv₀ hprep hsol hlim hT hIT hη hmargin
      (lt_min hη hδ)] with ε hε' t ht
    obtain ⟨hΞ, hε⟩ := hε'
    obtain ⟨y', hy', hdom, hmap, hglue, hsign⟩ := hε t ht
    obtain ⟨hng, hun, hsg⟩ := hread t ht y' (lt_of_lt_of_le hy' (min_le_left _ _))
    rw [hmap, hun, GraphPoint.coord_interior, hsign hng, hsg, hflow t ht, segState]
    simp only
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    set g := germSeq F β (segIdx F β (u₀ + v₀ * t))
    have hsg1 : |EdgeEnd.sign Γ g| = 1 := by
      rcases sign_eq_one_or_neg_one g with h | h <;> rw [h] <;> norm_num
    constructor
    · rw [show EdgeEnd.coordinate Γ g - EdgeEnd.sign Γ g *
          (posSeq F β (segIdx F β (u₀ + v₀ * t) + 1) - (u₀ + v₀ * t)) -
          (EdgeEnd.coordinate Γ g - EdgeEnd.sign Γ g *
            (posSeq F β (segIdx F β (u₀ + v₀ * t) + 1) - y')) =
          EdgeEnd.sign Γ g * ((u₀ + v₀ * t) - y') by ring, abs_mul, hsg1, one_mul, abs_sub_comm]
      exact lt_of_lt_of_le hy' (min_le_right _ _)
    · rw [show EdgeEnd.sign Γ g * v₀ - EdgeEnd.sign Γ g * (p ε 0).1 =
          EdgeEnd.sign Γ g * (v₀ - (p ε 0).1) by ring, abs_mul, hsg1, one_mul, abs_sub_comm]
      exact lt_of_lt_of_le hΞ (min_le_right _ _)

/-! ### Proposition IX.11 -/

/-- **The graph state `z = (ι_i(u₀), o_i(u₀) v₀)` exists** as a flight state of the zero potential
whenever `u₀ ∈ Λ_i \ Z_i` and `v₀ ≠ 0`. -/
theorem exists_flightState_compMap (i : Fin (RoutingLaw.compCount F)) {u₀ v₀ : ℝ}
    (hu₀ : u₀ ∈ compDomain F i \ compVertexSet F i) (hv₀ : v₀ ≠ 0) :
    ∃ z : (zeroPotential Γ).FlightState,
      compMap F i u₀ = GraphPoint.interior z.edge z.state.1 ∧
        z.state.2 = compSign F i u₀ * v₀ := by
  have hg : u₀ ∉ gluedSet F (compBase F i) :=
    fun h => hu₀.2 ((mem_compVertexSet_iff F).mpr ⟨hu₀.1, h⟩)
  have hseg := seg_mem_Ioo_of_not_mem F (compBase F i) hg
  have hmem := unroll_coord_mem F (compBase F i) hseg
  have hreg : (zeroPotential Γ).hamiltonian
      (germSeq F (compBase F i) (segIdx F (compBase F i) u₀)).1
      (EdgeEnd.coordinate Γ (germSeq F (compBase F i) (segIdx F (compBase F i) u₀)) -
        EdgeEnd.sign Γ (germSeq F (compBase F i) (segIdx F (compBase F i) u₀)) *
          (posSeq F (compBase F i) (segIdx F (compBase F i) u₀ + 1) - u₀))
      (compSign F i u₀ * v₀) ∉ (zeroPotential Γ).exceptionalEnergies := by
    refine zeroPotential_not_mem_exceptionalEnergies ?_
    rw [zeroPotential_hamiltonian]
    have : compSign F i u₀ * v₀ ≠ 0 := mul_ne_zero (by
      rcases sign_eq_one_or_neg_one (germSeq F (compBase F i) (segIdx F (compBase F i) u₀))
        with h | h <;> rw [compSign, unrollSign, h] <;> norm_num) hv₀
    positivity
  refine ⟨MechanicalPotential.FlightState.ofInterior (V := zeroPotential Γ)
    (x := (_, compSign F i u₀ * v₀)) hmem hreg, ?_, rfl⟩
  rw [compMap, unroll_of_mem_Ioo F _ hseg]
  rfl

/-- **Proposition IX.11 (Realization at zero potential), as printed.**

Let `V ≡ 0`, let `F` be a routing law, and let `H_ε = ½|ξ|² + W^F_ε` (`resolvedPot F ε`), whose
corridors are the components `R_1, …, R_m` of the resolved space `R(Γ, F)` placed along the lines
`w = i` (`compRow F i`).  Let `z = (ι_i(u₀), o_i(u₀) v₀)` with `u₀ ∈ Λ_i \ Z_i` and
`½ v₀² ∈ K⋆ = [1/2, 2]`; here `z` is any flight state of the zero potential at that graph state
(one exists by `exists_flightState_compMap`), and `Φ_t(z)` is the paper's graph flow
`graphFlow (F.toBorelScattering 0) z t = FlightState.trajectory …` of Theorem VI.5 with the vertex
law `S^F`.  Let `z_ε = (u_ε, w_ε; ξ_{u,ε}, ξ_{w,ε})`, `0 < ε < 1/8`, be states with
`u_ε ∈ Λ_i`, `½ ξ_{u,ε}² ∈ K⋆`, `|w_ε - i| ≤ 2ε`, `½ ξ_{w,ε}² + A_ε(w_ε - i) ≤ ε` and
`(u_ε, ξ_{u,ε}) → (u₀, v₀)`.  Then:

* trajectories `Φ^ε_t(z_ε)` of `H_ε` through `z_ε`, defined for all `t ∈ ℝ`, exist;
* for **every** family of such trajectories `Φ^ε_t(z_ε) = (u_ε(t), w_ε(t); …)`:
  `|w_ε(t) - i| < 2ε` for all `t ∈ ℝ` and all `0 < ε < 1/8`; and for every compact
  `I ⊆ [0, ∞)` containing no vertex impact of `Φ_t(z) = (e(t), q(t), p(t))`, eventually
  `ι_i(u_ε(t)) = (e(t), q_ε(t))` for all `t ∈ I` (with `u_ε(t) ∈ Λ_i \ Z_i`), and
  `sup_{t ∈ I} |(q_ε(t), o_i(u_ε(t)) u̇_ε(t)) - (q(t), p(t))| → 0` (uniform convergence on `I`).

The coordinate `q_ε(t)` is the edge coordinate of `ι_i(u_ε(t))`. -/
theorem universal_reversible_realization_paper (F : RoutingLaw Γ)
    (i : Fin (RoutingLaw.compCount F)) {u₀ v₀ : ℝ}
    (hu₀ : u₀ ∈ compDomain F i \ compVertexSet F i) (hv₀ : v₀ ^ 2 / 2 ∈ Icc (1 / 2 : ℝ) 2)
    (z : (zeroPotential Γ).FlightState)
    (hz : compMap F i u₀ = GraphPoint.interior z.edge z.state.1 ∧
      z.state.2 = compSign F i u₀ * v₀)
    (zε : ℝ → (ℝ × ℝ) × (ℝ × ℝ))
    (hzε : ∀ ε, 0 < ε → ε < 1 / 8 →
      (zε ε).1.1 ∈ compDomain F i ∧ (zε ε).2.1 ^ 2 / 2 ∈ Icc (1 / 2 : ℝ) 2 ∧
      |(zε ε).1.2 - compRow F i| ≤ 2 * ε ∧
      (zε ε).2.2 ^ 2 / 2 + wellPot ε ((zε ε).1.2 - compRow F i) ≤ ε)
    (hlim : Tendsto (fun ε => ((zε ε).1.1, (zε ε).2.1)) (𝓝[>] 0) (𝓝 (u₀, v₀))) :
    (∀ ε, 0 < ε → ε < 1 / 8 → ∃ x p : ℝ → ℝ × ℝ,
      IsHamiltonianFlowLine (resolvedPot F ε) x p ∧ x 0 = (zε ε).1 ∧ p 0 = (zε ε).2) ∧
    ∀ x p : ℝ → ℝ → ℝ × ℝ,
      (∀ ε, 0 < ε → ε < 1 / 8 →
        IsHamiltonianFlowLine (resolvedPot F ε) (x ε) (p ε) ∧ x ε 0 = (zε ε).1 ∧
          p ε 0 = (zε ε).2) →
      (∀ ε, 0 < ε → ε < 1 / 8 → ∀ t, |(x ε t).2 - compRow F i| < 2 * ε) ∧
      ∀ I : Set ℝ, IsCompact I → I ⊆ Ici 0 →
        (∀ t ∈ I, ¬ IsVertexImpact (F.toBorelScattering (zeroPotential Γ)) z t) →
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ I,
          (x ε t).1 ∈ compDomain F i \ compVertexSet F i ∧
          compMap F i (x ε t).1 = GraphPoint.interior
            (graphFlow (F.toBorelScattering (zeroPotential Γ)) z t).1
            (compMap F i (x ε t).1).coord) ∧
        TendstoUniformlyOn
          (fun ε t => ((compMap F i (x ε t).1).coord,
            compSign F i (x ε t).1 * deriv (fun s => (x ε s).1) t))
          (fun t => ((graphFlow (F.toBorelScattering (zeroPotential Γ)) z t).2.1,
            (graphFlow (F.toBorelScattering (zeroPotential Γ)) z t).2.2)) (𝓝[>] 0) I := by
  have hprep' : ∀ ε, 0 < ε → ε < 1 / 8 → IsPreparedState F i ε (zε ε).1 (zε ε).2 :=
    fun ε hε hεs => hzε ε hε hεs
  refine ⟨fun ε hε hεs => ?_, fun x p hsol => ?_⟩
  · obtain ⟨hstrict, hE⟩ := (hprep' ε hε hεs).energy hε hεs
    obtain ⟨x, p, hx0, hp0, hfl⟩ :=
      exists_resolvedFlowLine F hε hεs.le i (zε ε).1 (zε ε).2 hstrict hE
    exact ⟨x, p, hfl, hx0, hp0⟩
  have hprep : ∀ ε, 0 < ε → ε < 1 / 8 → IsPreparedState F i ε (x ε 0) (p ε 0) := by
    intro ε hε hεs
    rw [(hsol ε hε hεs).2.1, (hsol ε hε hεs).2.2]
    exact hprep' ε hε hεs
  have hfwd : ∀ ε, 0 < ε → ε < 1 / 8 →
      IsHamiltonianTrajectory (resolvedPot F ε) (x ε) (p ε) :=
    fun ε hε hεs => (hsol ε hε hεs).1.forward
  have hlim' : Tendsto (fun ε => ((x ε 0).1, (p ε 0).1)) (𝓝[>] 0) (𝓝 (u₀, v₀)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_nhdsGT_zero_of_forall_Ioo (by norm_num : (0 : ℝ) < 1 / 8)
      fun ε hε => hε] with ε hε
    rw [(hsol ε hε.1 hε.2).2.1, (hsol ε hε.1 hε.2).2.2]
  refine ⟨fun ε hε hεs => prepared_confined hε hεs (hsol ε hε hεs).1 (hprep ε hε hεs),
    fun I hI hI0 himp => ?_⟩
  obtain ⟨hev, hunif⟩ := component_realization_core i hu₀.1 hu₀.2 hv₀ z hz.1 hz.2 hprep hfwd
    hlim' hI hI0 himp
  refine ⟨hev.mono fun ε h t ht => ⟨⟨(h t ht).1, (h t ht).2.1⟩, (h t ht).2.2⟩, ?_⟩
  refine hunif.congr ?_
  filter_upwards [eventually_nhdsGT_zero_of_forall_Ioo (by norm_num : (0 : ℝ) < 1 / 8)
    fun ε hε => hε] with ε hε t _
  have hd : HasDerivAt (fun s => (x ε s).1) (p ε t).1 t :=
    (hasDerivWithinAt_pairFst ((hsol ε hε.1 hε.2).1 t).1.hasDerivWithinAt).hasDerivAt
      (Filter.univ_mem)
  simp only [hd.deriv]

end HamiltonianMetricGraphs
