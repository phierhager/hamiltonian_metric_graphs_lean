/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ThinHypotheses

/-!
# Speed and travel along an edge flight, under the window condition

The hypotheses (E) and (J) say nothing about the longitudinal speed along a flight.  Under the
window condition `K ⊂ (max_Γ V, ∞)` (`eq:window-above`, `MechanicalPotential.IsWindowAbove`) of
Sec. IX.A, the speed is controlled by the edge energy up to the error `γ_ε`, exactly as for the
graph flight (`|p| ∈ [r_K, R_K]`, Lemma IX.2).  This file derives the bounds used in the proof of
the thin-network limit (`ThinRun.lean`).

## The estimate

Let `t ↦ (x(t), ξ(t))` be a trajectory of `H_ε` performing an edge flight (E1)–(E3) towards `η`
on `[a, c]`, starting at a state prepared towards `η`.  Write `q = q_e(x)`, `p = p_e(ξ)`,
`E(t) = H_e(q, p) = p²/2 + V_e(q)` and `σ = σ(η)`.  By Hamilton's equations,
`q' = p`, `p' = -⟨∇W_ε, τ_e⟩`, so `E' = p (V_e'(q) - ⟨∇W_ε, τ_e⟩)` and, by (E3),
`|E'| ≤ γ_ε |p|`.  Hence, as long as `σ p > 0`,

  `(E + γ_ε σ q)' ≥ 0`  and  `(E - γ_ε σ q)' ≤ 0`,

so `|E(t) - E(a)| ≤ γ_ε ℓ_e`, because `q` stays in `[0, ℓ_e]` by (P1), (E1), (E2).  If
`V_e + g ≤ E` on `K` and `γ_ε ℓ_e < g`, this keeps `p² = 2(E - V_e(q)) ≥ 2(g - γ_ε ℓ_e) > 0`, so
`p` never vanishes and `σ p > 0` on the whole flight (`EdgeFlight.sign_pos_and_energy`, by a
first-zero argument).  Consequences: the longitudinal speed is bounded by a constant depending only
on `K` and `V` (`EdgeFlight.abs_longP_le`), and so is the distance travelled per unit time
(`EdgeFlight.toGo_le`).

`exists_window_constants` supplies, from the window condition and the compactness of `K`, the gap
`g > 0` and the bounds `max K ≤ Kmax`, `Vmin ≤ min_Γ V`.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

/-! ### The constants of the window -/

/-- **The constants of a window above the potential.**  If `K` is compact and `K ⊂ (max_Γ V, ∞)`,
there are a gap `g > 0` with `V_e(q) + g ≤ E` for all `E ∈ K` and all `q` on the closed edges,
an upper bound `Kmax` of `K` and a lower bound `Vmin` of `V`. -/
theorem MechanicalPotential.exists_window_constants {Γ : FiniteMetricGraph}
    (V : MechanicalPotential Γ) {K : Set ℝ} (hK : IsCompact K) (hwin : V.IsWindowAbove K) :
    ∃ g Kmax Vmin : ℝ, 0 < g ∧ (∀ E ∈ K, E ≤ Kmax) ∧
      ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e),
        Vmin ≤ V.extension e q ∧ ∀ E ∈ K, V.extension e q + g ≤ E := by
  set A : Set ℝ := ⋃ e : Γ.Edge, V.extension e '' Icc (0 : ℝ) (Γ.length e) with hAdef
  have hcont : ∀ e : Γ.Edge, ContinuousOn (V.extension e) (Icc (0 : ℝ) (Γ.length e)) :=
    fun e => (V.contDiffOn_extension e).continuousOn.mono (V.closedEdge_subset_domain e)
  have hA : IsCompact A := isCompact_iUnion fun e => isCompact_Icc.image_of_continuousOn (hcont e)
  have hmemA : ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), V.extension e q ∈ A :=
    fun e q hq => mem_iUnion.mpr ⟨e, q, hq, rfl⟩
  obtain ⟨Kmax, hKmax⟩ := hK.bddAbove
  obtain ⟨Vmin, hVmin⟩ := hA.bddBelow
  by_cases hne : (K ×ˢ A).Nonempty
  · obtain ⟨⟨E₀, v₀⟩, hmem, hmin⟩ := (hK.prod hA).exists_isMinOn hne
      (continuous_fst.sub continuous_snd).continuousOn
    obtain ⟨e₀, q₀, hq₀, hv₀⟩ := mem_iUnion.mp hmem.2
    have hlt : v₀ < E₀ := by
      have hv : V.extension e₀ q₀ = v₀ := hv₀
      rw [← hv]
      exact (hwin E₀ hmem.1).2 e₀ q₀ hq₀
    refine ⟨E₀ - v₀, Kmax, Vmin, by linarith, fun E hE => hKmax hE, fun e q hq =>
      ⟨hVmin (hmemA e q hq), fun E hE => ?_⟩⟩
    have h := isMinOn_iff.mp hmin (E, V.extension e q) ⟨hE, hmemA e q hq⟩
    simp only at h
    linarith
  · refine ⟨1, Kmax, Vmin, one_pos, fun E hE => hKmax hE, fun e q hq =>
      ⟨hVmin (hmemA e q hq), fun E hE => ?_⟩⟩
    exact absurd ⟨(E, V.extension e q), hE, hmemA e q hq⟩ hne

namespace ThinHamiltonianNetwork

variable {Γ : FiniteMetricGraph} {N : ThinHamiltonianNetwork Γ} {V : MechanicalPotential Γ}
  {K : Set ℝ}

/-! ### The edge energy along a flight -/

set_option maxHeartbeats 1000000 in
-- one long first-zero argument
/-- **Along an edge flight above the potential, the particle keeps moving towards `η` and its edge
energy changes by at most `γ_ε ℓ_e`.**  This is the microscopic counterpart of
`|p| = √(2(E - V_e(q))) ≥ r_K` along a graph flight (Lemma IX.2). -/
theorem EdgeFlight.sign_pos_and_energy {ε S : ℝ} {Θ : N.MicroTrajectory ε S} {η : Γ.EdgeEnd}
    {a c g : ℝ} (ha : 0 ≤ a) (hcS : c ≤ S) (hfl : N.EdgeFlight V K ε η Θ.x Θ.p a c)
    (hprep : N.Prepared V K ε η (Θ.x a) (Θ.p a))
    (hgap : ∀ E ∈ K, ∀ q ∈ Icc (0 : ℝ) (Γ.length η.1), V.extension η.1 q + g ≤ E)
    (hγ : N.forceErr ε * Γ.length η.1 < g) :
    ∀ t ∈ Icc a c, 0 < EdgeEnd.sign Γ η * N.longP η.1 (Θ.p t) ∧
      |V.hamiltonian η.1 (N.long η.1 (Θ.x t)) (N.longP η.1 (Θ.p t)) -
        V.hamiltonian η.1 (N.long η.1 (Θ.x a)) (N.longP η.1 (Θ.p a))| ≤
        N.forceErr ε * Γ.length η.1 := by
  set e := η.1 with he
  set σ := EdgeEnd.sign Γ η with hσdef
  set ℓ := Γ.length e with hℓ
  set γ := N.forceErr ε with hγdef
  set Q : ℝ → ℝ := fun t => N.long e (Θ.x t) with hQdef
  set P : ℝ → ℝ := fun t => N.longP e (Θ.p t) with hPdef
  set G : ℝ → ℝ := fun t => N.longGrad ε e (Θ.x t) with hGdef
  set D : ℝ → ℝ := fun t => deriv (V.extension e) (Q t) with hDdef
  set H : ℝ → ℝ := fun t => V.hamiltonian e (Q t) (P t) with hHdef
  have hac : a < c := hfl.lt
  have hsub : Icc a c ⊆ Icc (0 : ℝ) S := Icc_subset_Icc ha hcS
  have hσabs : |σ| = 1 := RoutingLaw.edgeEnd_abs_sign η
  have hγ0 : 0 ≤ γ := N.forceErr_nonneg ε
  have hδ0 : 0 ≤ N.offset ε := N.offset_nonneg ε
  -- the position stays on the closed edge
  have hQmem : ∀ t ∈ Icc a c, Q t ∈ Icc (0 : ℝ) ℓ := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      have h1 := hprep.inside
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · subst h'
      have h1 := hfl.arrive.prepared.inside
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    · have h1 := hfl.inside t ⟨h, h'⟩
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  -- Hamilton's equations for the projected state
  have hQd : ∀ t ∈ Icc a c, HasDerivWithinAt Q (P t) (Icc a c) t := fun t ht =>
    (hasDerivWithinAt_long e (Θ.ode_pos t (hsub ht))).mono hsub
  have hPd : ∀ t ∈ Icc a c, HasDerivWithinAt P (-G t) (Icc a c) t := by
    intro t ht
    have h := (hasDerivWithinAt_longP (N := N) e (Θ.ode_mom t (hsub ht))).mono hsub
    rwa [longP_force] at h
  have hVd : ∀ t ∈ Icc a c,
      HasDerivWithinAt (fun r => V.extension e (Q r)) (D t * P t) (Icc a c) t := by
    intro t ht
    have hdiff : DifferentiableAt ℝ (V.extension e) (Q t) :=
      ((V.contDiffOn_extension e).differentiableOn (by norm_num)).differentiableAt
        ((V.domain_isOpen e).mem_nhds (V.closedEdge_subset_domain e (hQmem t ht)))
    exact hdiff.hasDerivAt.comp_hasDerivWithinAt t (hQd t ht)
  have hHd : ∀ t ∈ Icc a c, HasDerivWithinAt H (P t * (D t - G t)) (Icc a c) t := by
    intro t ht
    have h := (((hPd t ht).pow 2).div_const 2).add (hVd t ht)
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  -- the force error (E3)
  have hF : ∀ t ∈ Icc a c, |G t - D t| ≤ γ := hfl.force
  -- the two comparison functions
  set Hp : ℝ → ℝ := fun t => H t + γ * σ * Q t with hHpdef
  set Hm : ℝ → ℝ := fun t => H t - γ * σ * Q t with hHmdef
  have hHpd : ∀ t ∈ Icc a c,
      HasDerivWithinAt Hp (P t * (D t - G t) + γ * σ * P t) (Icc a c) t :=
    fun t ht => (hHd t ht).add ((hQd t ht).const_mul (γ * σ))
  have hHmd : ∀ t ∈ Icc a c,
      HasDerivWithinAt Hm (P t * (D t - G t) - γ * σ * P t) (Icc a c) t :=
    fun t ht => (hHd t ht).sub ((hQd t ht).const_mul (γ * σ))
  have hkey : ∀ t ∈ Icc a c, 0 < σ * P t →
      0 ≤ P t * (D t - G t) + γ * σ * P t ∧ P t * (D t - G t) - γ * σ * P t ≤ 0 := by
    intro t ht hpos
    have habsP : |P t| = σ * P t := by
      rw [← abs_of_pos hpos, abs_mul, hσabs, one_mul]
    have hb : |P t * (D t - G t)| ≤ γ * (σ * P t) := by
      rw [abs_mul, abs_sub_comm, habsP, mul_comm]
      exact mul_le_mul_of_nonneg_right (hF t ht) hpos.le
    have := abs_le.mp hb
    constructor <;> nlinarith [this.1, this.2]
  have hPc : ContinuousOn P (Icc a c) := fun t ht => (hPd t ht).continuousWithinAt
  have hσPc : ContinuousOn (fun t => σ * P t) (Icc a c) := hPc.const_smul σ
  have hHpc : ContinuousOn Hp (Icc a c) := fun t ht => (hHpd t ht).continuousWithinAt
  have hHmc : ContinuousOn Hm (Icc a c) := fun t ht => (hHmd t ht).continuousWithinAt
  -- `|σ (q(t) - q(s))| ≤ ℓ`
  have hσQ : ∀ s ∈ Icc a c, ∀ t ∈ Icc a c, |σ * (Q t - Q s)| ≤ ℓ := by
    intro s hs t ht
    rw [abs_mul, hσabs, one_mul, abs_le]
    have h1 := hQmem s hs
    have h2 := hQmem t ht
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hγσQ : ∀ s ∈ Icc a c, ∀ t ∈ Icc a c,
      -(γ * ℓ) ≤ γ * (σ * (Q t - Q s)) ∧ γ * (σ * (Q t - Q s)) ≤ γ * ℓ := by
    intro s hs t ht
    have h := abs_le.mp (hσQ s hs t ht)
    constructor <;> nlinarith [h.1, h.2]
  -- the edge energy at the start lies in `K`
  have hEa : H a ∈ K := hprep.energy_mem
  have hamem : a ∈ Icc a c := ⟨le_rfl, hac.le⟩
  -- **the particle keeps moving towards `η`**: first-zero argument
  have hsign : ∀ t ∈ Icc a c, 0 < σ * P t := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₀, ht₀, hneg⟩ := hcon
    set A : Set ℝ := Icc a c ∩ (fun t => σ * P t) ⁻¹' Iic 0 with hAdef
    have hAc : IsClosed A := hσPc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hAne : A.Nonempty := ⟨t₀, ht₀, hneg⟩
    have hAbdd : BddBelow A := ⟨a, fun t ht => ht.1.1⟩
    set τ := sInf A with hτdef
    have hτA : τ ∈ A := hAc.csInf_mem hAne hAbdd
    have hτmem : τ ∈ Icc a c := hτA.1
    have hτ0 : σ * P τ ≤ 0 := hτA.2
    have hpa : 0 < σ * P a := hprep.towards
    have hτa : a < τ := by
      rcases eq_or_lt_of_le hτmem.1 with h | h
      · rw [← h] at hτ0; linarith
      · exact h
    have hbefore : ∀ s ∈ Ico a τ, 0 < σ * P s := by
      intro s hs
      by_contra hn
      push Not at hn
      have := csInf_le hAbdd ⟨⟨hs.1, hs.2.le.trans hτmem.2⟩, hn⟩
      linarith [hs.2]
    -- `σ p` vanishes at `τ`
    have hzero : σ * P τ = 0 := by
      by_contra hne
      have hlt : σ * P τ < 0 := lt_of_le_of_ne hτ0 hne
      obtain ⟨s, hs, hval⟩ := intermediate_value_Icc' hτa.le
        (hσPc.mono (Icc_subset_Icc le_rfl hτmem.2)) ⟨hlt.le, hpa.le⟩
      have hval' : σ * P s = 0 := hval
      have hsA : s ∈ A := ⟨⟨hs.1, hs.2.trans hτmem.2⟩, show σ * P s ≤ 0 by rw [hval']⟩
      have hle := csInf_le hAbdd hsA
      have hsτ : s = τ := le_antisymm hs.2 hle
      rw [hsτ] at hval'
      exact hne hval'
    have hσne : σ ≠ 0 := by intro h; rw [h, abs_zero] at hσabs; norm_num at hσabs
    have hP0 : P τ = 0 := (mul_eq_zero.mp hzero).resolve_left hσne
    -- the comparison function `E + γ σ q` does not decrease before `τ`
    have hmono : MonotoneOn Hp (Icc a τ) := by
      have hsubτ : Icc a τ ⊆ Icc a c := Icc_subset_Icc le_rfl hτmem.2
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a τ)
        (f' := fun t => P t * (D t - G t) + γ * σ * P t) (hHpc.mono hsubτ)
        (fun t ht => ?_) (fun t ht => ?_)
      · rw [interior_Icc] at ht ⊢
        exact (hHpd t (hsubτ (Ioo_subset_Icc_self ht))).mono
          (Ioo_subset_Icc_self.trans hsubτ)
      · rw [interior_Icc] at ht
        exact (hkey t (hsubτ (Ioo_subset_Icc_self ht)) (hbefore t ⟨ht.1.le, ht.2⟩)).1
    have hHpτ : Hp a ≤ Hp τ := hmono ⟨le_rfl, hτa.le⟩ ⟨hτa.le, le_rfl⟩ hτa.le
    have hHτ : H τ = V.extension e (Q τ) := by
      simp only [hHdef, MechanicalPotential.hamiltonian, hP0]
      ring
    have hgapτ := hgap (H a) hEa (Q τ) (hQmem τ hτmem)
    have hb := (hγσQ a hamem τ hτmem).2
    simp only [hHpdef] at hHpτ
    nlinarith
  -- with `σ p > 0` throughout, the energy changes by at most `γ ℓ`
  have hmono : MonotoneOn Hp (Icc a c) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a c)
      (f' := fun t => P t * (D t - G t) + γ * σ * P t) hHpc (fun t ht => ?_)
      (fun t ht => ?_)
    · rw [interior_Icc] at ht ⊢
      exact (hHpd t (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self
    · rw [interior_Icc] at ht
      exact (hkey t (Ioo_subset_Icc_self ht) (hsign t (Ioo_subset_Icc_self ht))).1
  have hanti : AntitoneOn Hm (Icc a c) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a c)
      (f' := fun t => P t * (D t - G t) - γ * σ * P t) hHmc (fun t ht => ?_)
      (fun t ht => ?_)
    · rw [interior_Icc] at ht ⊢
      exact (hHmd t (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self
    · rw [interior_Icc] at ht
      exact (hkey t (Ioo_subset_Icc_self ht) (hsign t (Ioo_subset_Icc_self ht))).2
  intro t ht
  refine ⟨hsign t ht, ?_⟩
  have h1 : Hp a ≤ Hp t := hmono hamem ht ht.1
  have h2 : Hm t ≤ Hm a := hanti hamem ht ht.1
  have h3 := hγσQ a hamem t ht
  simp only [hHpdef, hHmdef] at h1 h2
  change |H t - H a| ≤ γ * ℓ
  rw [abs_le]
  constructor <;> nlinarith [h3.1, h3.2]

/-- **The longitudinal speed along an edge flight above the potential is bounded** by a constant
that depends only on the window and the potential: `|p| ≤ 1 + 2 |Kmax + g - Vmin|`. -/
theorem EdgeFlight.abs_longP_le {ε S : ℝ} {Θ : N.MicroTrajectory ε S} {η : Γ.EdgeEnd}
    {a c g Kmax Vmin : ℝ} (ha : 0 ≤ a) (hcS : c ≤ S) (hfl : N.EdgeFlight V K ε η Θ.x Θ.p a c)
    (hprep : N.Prepared V K ε η (Θ.x a) (Θ.p a))
    (hgap : ∀ E ∈ K, ∀ q ∈ Icc (0 : ℝ) (Γ.length η.1), V.extension η.1 q + g ≤ E)
    (hγ : N.forceErr ε * Γ.length η.1 < g) (hKmax : ∀ E ∈ K, E ≤ Kmax)
    (hVmin : ∀ q ∈ Icc (0 : ℝ) (Γ.length η.1), Vmin ≤ V.extension η.1 q) :
    ∀ t ∈ Icc a c, |N.longP η.1 (Θ.p t)| ≤ 1 + 2 * |Kmax + g - Vmin| := by
  intro t ht
  have hE := (hfl.sign_pos_and_energy ha hcS hprep hgap hγ t ht).2
  have hEa : V.hamiltonian η.1 (N.long η.1 (Θ.x a)) (N.longP η.1 (Θ.p a)) ∈ K :=
    hprep.energy_mem
  have hK := hKmax _ hEa
  have hδ0 := N.offset_nonneg ε
  -- the position is on the closed edge
  have hQ : N.long η.1 (Θ.x t) ∈ Icc (0 : ℝ) (Γ.length η.1) := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      have h1 := hprep.inside
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · subst h'
      have h1 := hfl.arrive.prepared.inside
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    · have h1 := hfl.inside t ⟨h, h'⟩
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hV := hVmin _ hQ
  have hupper := (abs_le.mp hE).2
  have hHt : V.hamiltonian η.1 (N.long η.1 (Θ.x t)) (N.longP η.1 (Θ.p t)) =
      N.longP η.1 (Θ.p t) ^ 2 / 2 + V.extension η.1 (N.long η.1 (Θ.x t)) := rfl
  have hγ' : N.forceErr ε * Γ.length η.1 < g := hγ
  set p := N.longP η.1 (Θ.p t)
  have hsq : p ^ 2 ≤ 2 * |Kmax + g - Vmin| := by
    have := le_abs_self (Kmax + g - Vmin)
    linarith
  have hp : |p| ≤ 1 + p ^ 2 := by
    rcases le_or_gt |p| 1 with h | h
    · nlinarith [sq_nonneg p]
    · nlinarith [sq_abs p, abs_nonneg p]
  linarith

/-- **The distance travelled on an edge flight is at most the speed bound times its duration.** -/
theorem EdgeFlight.toGo_le {ε S : ℝ} {Θ : N.MicroTrajectory ε S} {η : Γ.EdgeEnd}
    {a c g Kmax Vmin : ℝ} (ha : 0 ≤ a) (hcS : c ≤ S) (hfl : N.EdgeFlight V K ε η Θ.x Θ.p a c)
    (hprep : N.Prepared V K ε η (Θ.x a) (Θ.p a))
    (hgap : ∀ E ∈ K, ∀ q ∈ Icc (0 : ℝ) (Γ.length η.1), V.extension η.1 q + g ≤ E)
    (hγ : N.forceErr ε * Γ.length η.1 < g) (hKmax : ∀ E ∈ K, E ≤ Kmax)
    (hVmin : ∀ q ∈ Icc (0 : ℝ) (Γ.length η.1), Vmin ≤ V.extension η.1 q) :
    N.toGo ε η (N.long η.1 (Θ.x a)) ≤ (1 + 2 * |Kmax + g - Vmin|) * (c - a) := by
  have hsub : Icc a c ⊆ Icc (0 : ℝ) S := Icc_subset_Icc ha hcS
  have hac := hfl.lt
  have h := abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le
    (f := fun t => N.long η.1 (Θ.x t)) (f' := fun t => N.longP η.1 (Θ.p t))
    (fun t ht => (hasDerivWithinAt_long η.1 (Θ.ode_pos t (hsub ht))).mono hsub)
    (hfl.abs_longP_le ha hcS hprep hgap hγ hKmax hVmin) ⟨le_rfl, hac.le⟩ ⟨hac.le, le_rfl⟩
    hac.le
  rw [toGo, ← hfl.arrive.boundary]
  exact h

end ThinHamiltonianNetwork

end HamiltonianMetricGraphs
