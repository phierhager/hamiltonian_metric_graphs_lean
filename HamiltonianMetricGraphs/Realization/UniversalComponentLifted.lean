/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalComponentFlow
import HamiltonianMetricGraphs.Realization.UniversalComponentResolved

/-!
# The lifted flow `(IX.lifted-flow)`

For `V ≡ 0` the graph flow lifts to `Λ_i`: with the folding map `f` (`compFold`; the identity for
a circle, the `2L_i`-periodic `|s|` for an interval) and `U(t) = f(u₀ + v₀ t)`,

  `Φ_t(ι_i(u₀), o_i(u₀) v₀) = (ι_i(U(t)), o_i(U(t)) U̇(t))` whenever `U(t) ∉ Z_i`,

and every positive time with `U(t) ∈ Z_i` is a vertex impact (`lifted_flow`).  This is the
displayed equation of Sec. IX.F; the proof of Proposition IX.11 in `UniversalComponent.lean` uses
the equivalent form `lift_flow` on the unrolled line.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {Γ : FiniteMetricGraph} (F : RoutingLaw Γ)

/-- The value of the folding map is determined by any representation `s = ρ x + 2 L n` with
`x ∈ [0, L]`. -/
theorem compFold_eq_of_repr {i : Fin F.compCount} (h : IsIntervalComp F i) {s x ρ : ℝ} {n : ℤ}
    (hρ : ρ = 1 ∨ ρ = -1) (hx : x ∈ Icc 0 (compLen F i)) (hs : s = ρ * x + 2 * compLen F i * n) :
    compFold F i s = x := by
  have hL := compLen_pos F i
  have hp : (0 : ℝ) < 2 * compLen F i := by linarith
  rw [compFold, if_pos h]
  by_cases hm : ρ * x = -compLen F i
  · -- the representative in `(-L, L]` is `L`
    have hx' : x = compLen F i := by
      rcases hρ with rfl | rfl
      · linarith [hx.1]
      · linarith
    have : toIocMod hp (-compLen F i) s = compLen F i := by
      rw [toIocMod_eq_iff]
      refine ⟨⟨by linarith, by linarith⟩, n - 1, ?_⟩
      rw [hs, hm, zsmul_eq_mul]; push_cast; ring
    rw [this, abs_of_pos hL, hx']
  · have : toIocMod hp (-compLen F i) s = ρ * x := by
      rw [toIocMod_eq_iff]
      refine ⟨⟨?_, ?_⟩, n, by rw [hs, zsmul_eq_mul]; ring⟩
      · rcases hρ with rfl | rfl
        · linarith [hx.1]
        · rcases lt_or_eq_of_le hx.2 with h' | h'
          · linarith
          · exfalso; apply hm; rw [h']; ring
      · rcases hρ with rfl | rfl <;> linarith [hx.1, hx.2]
    rw [this, abs_mul]
    rcases hρ with rfl | rfl <;> simp [abs_of_nonneg hx.1]

/-- **The folding map is affine with slope `±1` near a non-glued point.** -/
theorem hasDerivAt_compFold {i : Fin F.compCount} (h : IsIntervalComp F i) {s : ℝ}
    (hs : s ∉ gluedSet F (compBase F i)) :
    ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ ∃ n : ℤ, s = ρ * compFold F i s + 2 * compLen F i * n ∧
      HasDerivAt (compFold F i) ρ s := by
  obtain ⟨hmem, ρ, hρ, n, hn⟩ := compFold_spec F h s
  have hρρ : ρ * ρ = 1 := by rcases hρ with rfl | rfl <;> norm_num
  refine ⟨ρ, hρ, n, hn, ?_⟩
  -- the value is strictly inside `(0, L)`
  have hin : compFold F i s ∈ Ioo 0 (compLen F i) := by
    refine ⟨lt_of_le_of_ne hmem.1 fun h0 => hs ?_, lt_of_le_of_ne hmem.2 fun hL => hs ?_⟩
    · rw [hn, ← h0]; exact (unroll_symm h hρ n 0).2.1.mpr ⟨0, posSeq_zero F _⟩
    · rw [hn, hL]
      exact (unroll_symm h hρ n _).2.1.mpr ⟨_, (compLen_eq_posSeq h).symm⟩
  have heq : compFold F i =ᶠ[𝓝 s] fun s' => ρ * (s' - 2 * compLen F i * n) := by
    have hopen : Ioo (s - min (compFold F i s) (compLen F i - compFold F i s))
        (s + min (compFold F i s) (compLen F i - compFold F i s)) ∈ 𝓝 s := by
      have : 0 < min (compFold F i s) (compLen F i - compFold F i s) :=
        lt_min hin.1 (by linarith [hin.2])
      exact Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hopen] with s' hs'
    have hm1 := min_le_left (compFold F i s) (compLen F i - compFold F i s)
    have hm2 := min_le_right (compFold F i s) (compLen F i - compFold F i s)
    refine compFold_eq_of_repr F h (n := n) hρ ⟨?_, ?_⟩ ?_
    · rcases hρ with rfl | rfl <;> nlinarith [hs'.1, hs'.2]
    · rcases hρ with rfl | rfl <;> nlinarith [hs'.1, hs'.2]
    · linear_combination (2 * compLen F i * n - s') * hρρ
  have hd : HasDerivAt (fun s' => ρ * (s' - 2 * compLen F i * n)) ρ s := by
    simpa using ((hasDerivAt_id s).sub_const (2 * compLen F i * n)).const_mul ρ
  exact hd.congr_of_eventuallyEq heq

/-- The folding map sends a parameter to `Z_i` exactly when the parameter is a glued point. -/
theorem compFold_mem_compVertexSet_iff (i : Fin F.compCount) (s : ℝ) :
    compFold F i s ∈ compVertexSet F i ↔ s ∈ gluedSet F (compBase F i) := by
  rw [mem_compVertexSet_iff]
  by_cases h : IsIntervalComp F i
  · obtain ⟨hmem, ρ, hρ, n, hn⟩ := compFold_spec F h s
    have hsym := (unroll_symm h hρ n (compFold F i s)).2.1
    rw [← hn] at hsym
    rw [compDomain_of_interval F h, hsym]
    exact ⟨fun h' => h'.2, fun h' => ⟨hmem, h'⟩⟩
  · rw [compFold_of_circle F h, compDomain_of_circle F h]
    exact ⟨fun h' => h'.2, fun h' => ⟨trivial, h'⟩⟩

/-- **The lifted flow, equation (IX.lifted-flow) of the paper.**  For `u₀ ∈ Λ_i \ Z_i`, `v₀ ≠ 0`
and `U(t) = f(u₀ + v₀ t)`:
`Φ_t(ι_i(u₀), o_i(u₀) v₀) = (ι_i(U(t)), o_i(U(t)) U̇(t))` whenever `U(t) ∉ Z_i`, and every positive
time with `U(t) ∈ Z_i` is a vertex impact. -/
theorem lifted_flow (i : Fin F.compCount) {u₀ v₀ : ℝ}
    (hu₀ : u₀ ∈ compDomain F i \ compVertexSet F i) (hv₀ : v₀ ≠ 0)
    (z : (zeroPotential Γ).FlightState)
    (hz : compMap F i u₀ = GraphPoint.interior z.edge z.state.1 ∧
      z.state.2 = compSign F i u₀ * v₀) {t : ℝ} (ht : 0 ≤ t) :
    (compFold F i (u₀ + v₀ * t) ∉ compVertexSet F i →
      GraphPoint.interior (graphFlow (F.toBorelScattering (zeroPotential Γ)) z t).1
          (graphFlow (F.toBorelScattering (zeroPotential Γ)) z t).2.1 =
        compMap F i (compFold F i (u₀ + v₀ * t)) ∧
      (graphFlow (F.toBorelScattering (zeroPotential Γ)) z t).2.2 =
        compSign F i (compFold F i (u₀ + v₀ * t)) *
          deriv (fun τ => compFold F i (u₀ + v₀ * τ)) t) ∧
    (0 < t → compFold F i (u₀ + v₀ * t) ∈ compVertexSet F i →
      IsVertexImpact (F.toBorelScattering (zeroPotential Γ)) z t) := by
  set β := compBase F i
  have hu₀g : u₀ ∉ gluedSet F β := fun h => hu₀.2 ((mem_compVertexSet_iff F).mpr ⟨hu₀.1, h⟩)
  have hseg₀ := seg_mem_Ioo_of_not_mem F β hu₀g
  set k₀ := segIdx F β u₀
  have ha := hz.1
  rw [compMap, unroll_of_mem_Ioo F β hseg₀] at ha
  injection ha with he hq
  have hs : z.state = segState F β k₀ u₀ v₀ := by
    refine Prod.ext hq.symm ?_
    rw [hz.2, segState, compSign, unrollSign_of_mem_Ico F β ⟨hseg₀.1.le, hseg₀.2⟩]
  have hlift := lift_flow (β := β) z hseg₀ hv₀ he.symm hs ht
  refine ⟨fun hU => ?_, fun hpos hU => hlift.2 hpos ((compFold_mem_compVertexSet_iff F i _).mp hU)⟩
  set s := u₀ + v₀ * t
  have hsg : s ∉ gluedSet F β := fun h => hU ((compFold_mem_compVertexSet_iff F i s).mpr h)
  have hsseg := seg_mem_Ioo_of_not_mem F β hsg
  rw [hlift.1 hsg, segState]
  simp only
  -- the value and the orientation at `s`, transported to `f(s)`
  have hlin : HasDerivAt (fun τ : ℝ => u₀ + v₀ * τ) v₀ t := by
    simpa using ((hasDerivAt_id t).const_mul v₀).const_add u₀
  by_cases hint : IsIntervalComp F i
  · obtain ⟨ρ, hρ, n, hn, hd⟩ := hasDerivAt_compFold F hint hsg
    have hsym := unroll_symm hint hρ n (compFold F i s)
    rw [← hn] at hsym
    have hfg : compFold F i s ∉ gluedSet F β := fun h => hsg (hsym.2.1.mpr h)
    have hU' : HasDerivAt (fun τ => compFold F i (u₀ + v₀ * τ)) (ρ * v₀) t := by
      exact hd.comp t hlin
    refine ⟨?_, ?_⟩
    · rw [compMap, ← hsym.1, unroll_of_mem_Ioo F β hsseg]
    · rw [hU'.deriv, compSign, ← unrollSign_of_mem_Ico F β ⟨hsseg.1.le, hsseg.2⟩,
        hsym.2.2 hfg]
      ring
  · rw [compFold_of_circle F hint]
    have hU' : HasDerivAt (fun τ => compFold F i (u₀ + v₀ * τ)) v₀ t := by
      have : (fun τ => compFold F i (u₀ + v₀ * τ)) = fun τ => u₀ + v₀ * τ := by
        funext τ; rw [compFold_of_circle F hint]
      rw [this]; exact hlin
    refine ⟨by rw [compMap, unroll_of_mem_Ioo F β hsseg], ?_⟩
    rw [hU'.deriv, compSign, unrollSign_of_mem_Ico F β ⟨hsseg.1.le, hsseg.2⟩]

end HamiltonianMetricGraphs
