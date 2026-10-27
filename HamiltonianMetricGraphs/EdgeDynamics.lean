/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.LiouvilleMeasure

/-!
# Local mechanical edge dynamics

This exposes the concrete Hamiltonian vector field used by the later ODE construction.  Its
continuity on the chosen open extension domain follows directly from the paper's `C²`
assumption; no abstract edge-flow preservation hypothesis is introduced here.
-/

namespace HamiltonianMetricGraphs

open Set Filter
open scoped NNReal Topology

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- Hamilton's vector field `(q', p') = (p, -V'(q))` on an edge extension domain. -/
noncomputable def edgeVectorField (e : Γ.Edge) : ℝ × ℝ → ℝ × ℝ := fun x =>
  (x.2, V.force e x.1)

theorem continuousOn_force (e : Γ.Edge) :
    ContinuousOn (V.force e) (V.domain e) := by
  unfold force
  exact ((V.contDiffOn_extension e).continuousOn_deriv_of_isOpen
    (V.domain_isOpen e) (by norm_num)).neg

/-- The force is bounded on every compact physical edge interval. -/
theorem exists_absBound_force_closedEdge (e : Γ.Edge) :
    ∃ R : ℝ, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.force e q| ≤ R := by
  have hcont : ContinuousOn (V.force e) (Icc (0 : ℝ) (Γ.length e)) :=
    (V.continuousOn_force e).mono (V.closedEdge_subset_domain e)
  have hc : IsCompact ((V.force e) '' Icc (0 : ℝ) (Γ.length e)) :=
    isCompact_Icc.image_of_continuousOn hcont
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall 0
  refine ⟨R, ?_⟩
  intro q hq
  have := hR ⟨q, hq, rfl⟩
  simpa [Metric.mem_closedBall, Real.dist_eq] using this

/-- Finiteness upgrades the compact force bounds to a single bound over the whole graph. -/
theorem exists_uniform_absBound_force_closedEdges :
    ∃ R : ℝ, ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.force e q| ≤ R := by
  classical
  by_cases h : Nonempty Γ.Edge
  · letI := h
    choose r hr using fun e : Γ.Edge => V.exists_absBound_force_closedEdge e
    refine ⟨Finset.univ.sup' Finset.univ_nonempty r, ?_⟩
    intro e q hq
    exact (hr e q hq).trans (Finset.le_sup' r (Finset.mem_univ e))
  · have hempty : IsEmpty Γ.Edge := not_nonempty_iff.mp h
    exact ⟨0, fun e => isEmptyElim e⟩

theorem continuousOn_edgeVectorField (e : Γ.Edge) :
    ContinuousOn (V.edgeVectorField e) (V.domain e ×ˢ (univ : Set ℝ)) := by
  unfold edgeVectorField
  refine continuousOn_snd.prodMk ?_
  exact (V.continuousOn_force e).comp continuousOn_fst (fun x hx => hx.1)

/-- The concrete edge vector field is `C¹` at every point of the selected open extension
domain.  This is the hypothesis needed for Picard--Lindelöf. -/
theorem contDiffAt_edgeVectorField {e : Γ.Edge} {x : ℝ × ℝ} (hx : x.1 ∈ V.domain e) :
    ContDiffAt ℝ 1 (V.edgeVectorField e) x := by
  unfold edgeVectorField force
  refine contDiffAt_snd.prodMk ?_
  exact ((V.extension_contDiffAt_of_mem hx).derivWithin (m := 1) (by norm_num)).fst''.neg

/-- A `C¹` edge vector field is Lipschitz on a neighbourhood of every point in its extension
domain. -/
theorem exists_lipschitzOnWith_edgeVectorField {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x.1 ∈ V.domain e) :
    ∃ (K : ℝ≥0) (s : Set (ℝ × ℝ)), s ∈ 𝓝 x ∧ LipschitzOnWith K (V.edgeVectorField e) s :=
  (V.contDiffAt_edgeVectorField hx).exists_lipschitzOnWith

/-- The position component of an integral curve of the vector field satisfies `q' = p`. -/
theorem edgeIntegralCurve_hasDerivAt_fst {e : Γ.Edge} {α : ℝ → ℝ × ℝ} {t : ℝ}
    (hα : HasDerivAt α (V.edgeVectorField e (α t)) t) :
    HasDerivAt (fun s => (α s).1) (α t).2 t := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have h := (hasDerivAt_const t L).clm_apply hα
  simpa [L, edgeVectorField] using h

/-- A uniform momentum bound on an edge integral curve bounds its coordinate travel distance.
This is the rigorous `distance ≤ speed × time` estimate used by the no-Zeno argument. -/
theorem edgeIntegralCurve_coordinate_travel_bound {e : Γ.Edge} {α : ℝ → ℝ × ℝ}
    {a b P : ℝ} (hab : a ≤ b)
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (V.edgeVectorField e (α t)) t)
    (hP : ∀ t ∈ Icc a b, |(α t).2| ≤ P) :
    |(α b).1 - (α a).1| ≤ P * (b - a) := by
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := a) (b := b) (f := fun t => (α t).1) (f' := fun t => (α t).2)
    (fun t ht => (V.edgeIntegralCurve_hasDerivAt_fst (hα t ht)).hasDerivWithinAt)
    (fun t ht => by
      simpa [Real.norm_eq_abs] using hP t (Ico_subset_Icc_self ht))
    b (right_mem_Icc.mpr hab)
  simpa [Real.norm_eq_abs] using hbound

/-- Rewriting a speed-times-time estimate as a positive lower bound on elapsed time. -/
theorem time_lower_bound_of_coordinate_separation {r P Δ : ℝ}
    (htravel : r ≤ P * Δ) (hP : 0 < P) : r / P ≤ Δ := by
  rw [div_le_iff₀ hP]
  simpa [mul_comm] using htravel

/-- The momentum component of an integral curve satisfies `p' = -V'(q)`. -/
theorem edgeIntegralCurve_hasDerivAt_snd {e : Γ.Edge} {α : ℝ → ℝ × ℝ} {t : ℝ}
    (hα : HasDerivAt α (V.edgeVectorField e (α t)) t) :
    HasDerivAt (fun s => (α s).2) (V.force e (α t).1) t := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have h := (hasDerivAt_const t L).clm_apply hα
  simpa [L, edgeVectorField] using h

/-- One-sided (within-a-set) version: the position component of a within-integral curve
satisfies `q' = p`.  This is the form needed at a maximal-flight endpoint, where only a
one-sided derivative is available. -/
theorem edgeIntegralCurve_hasDerivWithinAt_fst {e : Γ.Edge} {α : ℝ → ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (hα : HasDerivWithinAt α (V.edgeVectorField e (α t)) s t) :
    HasDerivWithinAt (fun u => (α u).1) (α t).2 s t := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have h := (hasDerivWithinAt_const t s L).clm_apply hα
  simpa [L, edgeVectorField] using h

/-- One-sided (within-a-set) version: the momentum component of a within-integral curve
satisfies `p' = -V'(q)`. -/
theorem edgeIntegralCurve_hasDerivWithinAt_snd {e : Γ.Edge} {α : ℝ → ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (hα : HasDerivWithinAt α (V.edgeVectorField e (α t)) s t) :
    HasDerivWithinAt (fun u => (α u).2) (V.force e (α t).1) s t := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have h := (hasDerivWithinAt_const t s L).clm_apply hα
  simpa [L, edgeVectorField] using h

/-- A uniform momentum bound on a one-sided (within-`Icc`) edge integral curve bounds its
coordinate travel distance.  This is the `distance ≤ speed × time` estimate applicable to a
maximal edge flight, whose terminal derivative is only one-sided. -/
theorem edgeIntegralCurve_coordinate_travel_bound_within {e : Γ.Edge} {α : ℝ → ℝ × ℝ}
    {a b P : ℝ} (hab : a ≤ b)
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (V.edgeVectorField e (α t)) (Icc a b) t)
    (hP : ∀ t ∈ Icc a b, |(α t).2| ≤ P) :
    |(α b).1 - (α a).1| ≤ P * (b - a) := by
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := a) (b := b) (f := fun t => (α t).1) (f' := fun t => (α t).2)
    (fun t ht => V.edgeIntegralCurve_hasDerivWithinAt_fst (hα t ht))
    (fun t ht => by
      simpa [Real.norm_eq_abs] using hP t (Ico_subset_Icc_self ht))
    b (right_mem_Icc.mpr hab)
  simpa [Real.norm_eq_abs] using hbound

/-- Time reversal together with momentum reversal sends an edge integral curve to another
integral curve of the same mechanical Hamiltonian system. -/
theorem edgeIntegralCurve_timeReversal {e : Γ.Edge} {α : ℝ → ℝ × ℝ} {t : ℝ}
    (hα : HasDerivAt α (V.edgeVectorField e (α (-t))) (-t)) :
    HasDerivAt (fun s => ((α (-s)).1, -(α (-s)).2))
      (V.edgeVectorField e ((α (-t)).1, -(α (-t)).2)) t := by
  have hq := V.edgeIntegralCurve_hasDerivAt_fst hα
  have hp := V.edgeIntegralCurve_hasDerivAt_snd hα
  have hqrev := hq.comp t (hasDerivAt_neg t)
  have hprev := (hp.comp t (hasDerivAt_neg t)).neg
  simpa [edgeVectorField] using hqrev.prodMk hprev

/-- Momentum reversal preserves the mechanical energy: the energy invariance underlying the
time-reversed (backward) edge flight. -/
theorem hamiltonian_neg_momentum (e : Γ.Edge) (q p : ℝ) :
    V.hamiltonian e q (-p) = V.hamiltonian e q p := by
  unfold hamiltonian; ring

/-- The momentum-and-time reversal of an edge integral curve on `[a,b]` is an edge integral curve
on `[-b,-a]`.  This is the interval-level backward-flight symmetry (edge ODE only; scattering
reversibility is not assumed). -/
theorem edgeIntegralCurve_timeReversal_on {e : Γ.Edge} {α : ℝ → ℝ × ℝ} {a b : ℝ}
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (V.edgeVectorField e (α t)) t) :
    ∀ s ∈ Icc (-b) (-a),
      HasDerivAt (fun u => ((α (-u)).1, -(α (-u)).2))
        (V.edgeVectorField e ((α (-s)).1, -(α (-s)).2)) s := by
  intro s hs
  refine V.edgeIntegralCurve_timeReversal (hα (-s) ⟨?_, ?_⟩)
  · linarith [hs.2]
  · linarith [hs.1]

/-- A continuous nonvanishing real curve that starts positive remains positive on an interval. -/
theorem positive_on_Icc_of_continuousOn_ne_zero {p : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn p (Icc a b)) (hne : ∀ t ∈ Icc a b, p t ≠ 0)
    (hpa : 0 < p a) : ∀ t ∈ Icc a b, 0 < p t := by
  intro t ht
  by_contra hpt
  have hneg : p t < 0 := lt_of_le_of_ne (le_of_not_gt hpt) (hne t ht)
  have hcont' : ContinuousOn p (Icc a t) :=
    hcont.mono (fun s hs => ⟨hs.1, le_trans hs.2 ht.2⟩)
  obtain ⟨s, hs, hzero⟩ := intermediate_value_Icc' ht.1 hcont'
    ⟨le_of_lt hneg, le_of_lt hpa⟩
  exact hne s ⟨hs.1, le_trans hs.2 ht.2⟩ hzero

/-- A continuous nonvanishing real curve that starts negative remains negative on an interval. -/
theorem negative_on_Icc_of_continuousOn_ne_zero {p : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn p (Icc a b)) (hne : ∀ t ∈ Icc a b, p t ≠ 0)
    (hpa : p a < 0) : ∀ t ∈ Icc a b, p t < 0 := by
  have hpos := positive_on_Icc_of_continuousOn_ne_zero (p := fun t => -p t)
    (hcont.neg) (fun t ht => neg_ne_zero.mpr (hne t ht)) (by linarith)
  intro t ht
  linarith [hpos t ht]

/-- A scalar curve through zero with positive derivative is positive immediately to the right. -/
theorem eventually_pos_right_of_hasDerivAt_pos {f : ℝ → ℝ} {t d : ℝ}
    (h : HasDerivAt f d t) (hd : 0 < d) (hf : f t = 0) :
    ∀ᶠ s in 𝓝[>] t, 0 < f s := by
  apply eventually_nhdsWithin_iff.mpr
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos
    (f := f) (x₀ := t) (by rw [h.deriv]; exact hd) hf
  filter_upwards [hsign] with s hs hst
  apply sign_eq_one_iff.mp
  rw [hs, sign_pos (sub_pos.mpr hst)]

/-- A scalar curve through zero with negative derivative is negative immediately to the right. -/
theorem eventually_neg_right_of_hasDerivAt_neg {f : ℝ → ℝ} {t d : ℝ}
    (h : HasDerivAt f d t) (hd : d < 0) (hf : f t = 0) :
    ∀ᶠ s in 𝓝[>] t, f s < 0 := by
  apply eventually_nhdsWithin_iff.mpr
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg
    (f := f) (x₀ := t) (by rw [h.deriv]; exact hd) hf
  filter_upwards [hsign] with s hs hst
  apply sign_eq_neg_one_iff.mp
  rw [hs, sign_neg (sub_neg.mpr hst)]

/-- A scalar curve through zero with positive derivative is negative immediately to the left. -/
theorem eventually_neg_left_of_hasDerivAt_pos {f : ℝ → ℝ} {t d : ℝ}
    (h : HasDerivAt f d t) (hd : 0 < d) (hf : f t = 0) :
    ∀ᶠ s in 𝓝[<] t, f s < 0 := by
  apply eventually_nhdsWithin_iff.mpr
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos
    (f := f) (x₀ := t) (by rw [h.deriv]; exact hd) hf
  filter_upwards [hsign] with s hs hst
  apply sign_eq_neg_one_iff.mp
  rw [hs, sign_neg (sub_neg.mpr hst)]

/-- A scalar curve through zero with negative derivative is positive immediately to the left. -/
theorem eventually_pos_left_of_hasDerivAt_neg {f : ℝ → ℝ} {t d : ℝ}
    (h : HasDerivAt f d t) (hd : d < 0) (hf : f t = 0) :
    ∀ᶠ s in 𝓝[<] t, 0 < f s := by
  apply eventually_nhdsWithin_iff.mpr
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg
    (f := f) (x₀ := t) (by rw [h.deriv]; exact hd) hf
  filter_upwards [hsign] with s hs hst
  apply sign_eq_one_iff.mp
  rw [hs, sign_pos (sub_pos.mpr hst)]

/-- The left-sided derivative version of the preceding sign test.  This is the form needed at a
maximal physical flight endpoint, where only times before the hit are part of the physical
curve. -/
theorem eventually_neg_left_of_hasDerivWithinAt_pos {f : ℝ → ℝ} {t d : ℝ}
    (h : HasDerivWithinAt f d (Iic t) t) (hd : 0 < d) (hf : f t = 0) :
    ∀ᶠ s in 𝓝[<] t, f s < 0 := by
  have hslopeIic := (hasDerivWithinAt_iff_tendsto_slope.mp h)
  have hslope : Tendsto (slope f t) (𝓝[<] t) (𝓝 d) :=
    hslopeIic.mono_left (nhdsWithin_mono _ (by
      intro s hs
      change s < t at hs
      exact ⟨hs.le, ne_of_lt hs⟩))
  have hball : ∀ᶠ s in 𝓝[<] t, slope f t s ∈ Metric.ball d (d / 2) :=
    hslope (Metric.ball_mem_nhds _ (by linarith))
  filter_upwards [hball, self_mem_nhdsWithin] with s hs hst
  change s < t at hst
  rw [Metric.mem_ball, Real.dist_eq] at hs
  have hslope_pos : 0 < slope f t s := by
    rw [abs_lt] at hs
    linarith
  rw [slope_def_field] at hslope_pos
  have hden : s - t < 0 := sub_neg.mpr hst
  rcases (div_pos_iff.mp hslope_pos) with hpos | hneg
  · exact (not_lt_of_ge hden.le hpos.2).elim
  · rw [hf] at hneg
    linarith

/-- If a curve is positive before a left endpoint, its left derivative there cannot point
outward. This is the one-sided counterpart used by maximal first-hit flights. -/
theorem leftEndpoint_derivWithin_nonpos_of_pos_before {q : ℝ → ℝ} {a b p : ℝ}
    (hab : a < b) (hpos : ∀ t ∈ Ioo a b, 0 < q t)
    (hderiv : HasDerivWithinAt q p (Iic b) b) (hzero : q b = 0) : p ≤ 0 := by
  by_contra hp
  have hppos : 0 < p := lt_of_not_ge hp
  have hneg := eventually_neg_left_of_hasDerivWithinAt_pos hderiv hppos hzero
  have hneg' := eventually_nhdsWithin_iff.mp hneg
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hneg'
  let r := min (δ / 2) ((b - a) / 2)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrδ : r ≤ δ / 2 := min_le_left _ _
  have hrab : r ≤ (b - a) / 2 := min_le_right _ _
  have hsIoo : b - r ∈ Ioo a b := by constructor <;> linarith
  have hdist : dist (b - r) b < δ := by
    rw [Real.dist_eq, show b - r - b = -r by ring, abs_neg, abs_of_pos hr]
    linarith
  have hnegat := hnear hdist hsIoo.2
  exact (not_lt_of_ge (le_of_lt (hpos _ hsIoo))) hnegat

/-- If a curve is positive before reaching the left endpoint, its derivative at that endpoint
cannot point outward. -/
theorem leftEndpoint_deriv_nonpos_of_pos_before {q : ℝ → ℝ} {a b p : ℝ}
    (hab : a < b) (hpos : ∀ t ∈ Ioo a b, 0 < q t)
    (hderiv : HasDerivAt q p b) (hzero : q b = 0) : p ≤ 0 := by
  by_contra hp
  have hppos : 0 < p := lt_of_not_ge hp
  have hleft := eventually_neg_left_of_hasDerivAt_pos hderiv hppos hzero
  have hleft' := eventually_nhdsWithin_iff.mp hleft
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hleft'
  let r := min (δ / 2) ((b - a) / 2)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrδ : r ≤ δ / 2 := min_le_left _ _
  have hrab : r ≤ (b - a) / 2 := min_le_right _ _
  have hsIoo : b - r ∈ Ioo a b := by constructor <;> linarith
  have hdist : dist (b - r) b < δ := by
    rw [Real.dist_eq, show b - r - b = -r by ring, abs_neg, abs_of_pos hr]
    linarith
  have hneg := hnear hdist hsIoo.2
  exact (not_lt_of_ge (le_of_lt (hpos _ hsIoo))) hneg

/-- A derivative taken within `Icc a b` at the right endpoint `b` is the same as the left
derivative taken within `Iic b`, because the two sets have the same germ at `b`. -/
theorem hasDerivWithinAt_Iic_of_Icc {f : ℝ → ℝ} {d a b : ℝ} (hab : a < b)
    (h : HasDerivWithinAt f d (Icc a b) b) : HasDerivWithinAt f d (Iic b) b := by
  apply h.congr_set
  filter_upwards [Ioi_mem_nhds hab] with x hx
  simp only [mem_Icc, mem_Iic, eq_iff_iff]
  exact ⟨fun hy => hy.2, fun hy => ⟨le_of_lt hx, hy⟩⟩

/-- One-sided counterpart of `rightEndpoint_deriv_nonneg_of_lt_before`: if a curve stays below
the right endpoint before reaching it, its left derivative there cannot point outward. -/
theorem rightEndpoint_derivWithin_nonneg_of_lt_before {q : ℝ → ℝ} {a b p L : ℝ}
    (hab : a < b) (hlt : ∀ t ∈ Ioo a b, q t < L)
    (hderiv : HasDerivWithinAt q p (Iic b) b) (hL : q b = L) : 0 ≤ p := by
  have hderiv' : HasDerivWithinAt (fun t => -q t + L) (-p) (Iic b) b := by
    simpa using (hderiv.neg.add_const L)
  have hpos : ∀ t ∈ Ioo a b, 0 < (fun t => -q t + L) t := fun t ht => by
    have := hlt t ht; simp only; linarith
  have hnonpos : -p ≤ 0 :=
    leftEndpoint_derivWithin_nonpos_of_pos_before hab hpos hderiv' (by simp [hL])
  linarith

/-- If a curve is below the right endpoint before reaching it, its derivative at that endpoint
cannot point outward. -/
theorem rightEndpoint_deriv_nonneg_of_lt_before {q : ℝ → ℝ} {a b p L : ℝ}
    (hab : a < b) (hlt : ∀ t ∈ Ioo a b, q t < L)
    (hderiv : HasDerivAt q p b) (hL : q b = L) : 0 ≤ p := by
  by_contra hp
  have hpneg : p < 0 := lt_of_not_ge hp
  have hderiv' : HasDerivAt (fun t => q t - L) p b := by
    simpa using hderiv.sub_const L
  have hleft := eventually_pos_left_of_hasDerivAt_neg hderiv' hpneg (by simp [hL])
  have hleft' := eventually_nhdsWithin_iff.mp hleft
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hleft'
  let r := min (δ / 2) ((b - a) / 2)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrδ : r ≤ δ / 2 := min_le_left _ _
  have hrab : r ≤ (b - a) / 2 := min_le_right _ _
  have hsIoo : b - r ∈ Ioo a b := by constructor <;> linarith
  have hdist : dist (b - r) b < δ := by
    rw [Real.dist_eq, show b - r - b = -r by ring, abs_neg, abs_of_pos hr]
    linarith
  have hgt := hnear hdist hsIoo.2
  exact (not_lt_of_ge (le_of_lt (hlt _ hsIoo))) (by linarith)

/-- Local existence of a concrete Hamiltonian edge trajectory through every state lying in the
open extension domain. -/
theorem exists_local_edge_integralCurve {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x.1 ∈ V.domain e) (t₀ : ℝ) :
    ∃ α : ℝ → ℝ × ℝ, α t₀ = x ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (V.edgeVectorField e (α t)) t :=
  ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    (V.contDiffAt_edgeVectorField hx) t₀

/-- Picard--Lindelöf local existence is uniform over every compact set of initial states lying
in one edge's extension domain.  This is obtained from a finite subcover of the local flow balls,
not by assuming a global edge flow. -/
theorem exists_uniform_local_edge_integralCurve_on_compact {e : Γ.Edge} (K : Set (ℝ × ℝ))
    (hKcompact : IsCompact K) (hKdomain : ∀ x ∈ K, x.1 ∈ V.domain e) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∃ α : ℝ → ℝ × ℝ, α 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt α (V.edgeVectorField e (α t)) t := by
  classical
  by_cases hK : K.Nonempty
  · let X := {x : ℝ × ℝ // x ∈ K}
    choose r hr ε hε hflow using fun x : X =>
      ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt
        (V.contDiffAt_edgeVectorField (hKdomain x.1 x.2)) 0
    obtain ⟨u, hcover⟩ := hKcompact.elim_finite_subcover
      (fun x : X => Metric.ball x.1 (r x))
      (fun x => Metric.isOpen_ball) (by
        intro x hx
        refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
        exact Metric.mem_ball_self (hr ⟨x, hx⟩))
    have hu_nonempty : u.Nonempty := by
      rcases hK with ⟨x, hx⟩
      rcases Set.mem_iUnion₂.mp (hcover hx) with ⟨c, hc, hxc⟩
      exact ⟨c, hc⟩
    let values : Finset ℝ := u.image ε
    have hvalues_nonempty : values.Nonempty := by
      rw [Finset.image_nonempty]
      exact hu_nonempty
    let δ : ℝ := values.min' hvalues_nonempty
    have hδpos : 0 < δ := by
      have hmem : δ ∈ values := Finset.min'_mem values hvalues_nonempty
      obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hmem
      rw [← heq]
      exact hε c
    refine ⟨δ, hδpos, ?_⟩
    intro x hx
    rcases Set.mem_iUnion₂.mp (hcover hx) with ⟨c, hc, hxc⟩
    obtain ⟨α, hα0, hα⟩ := hflow c x
      (Metric.ball_subset_closedBall hxc)
    refine ⟨α, hα0, ?_⟩
    intro t ht
    apply hα t
    have hδε : δ ≤ ε c := Finset.min'_le values (ε c)
      (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
    constructor <;> linarith [ht.1, ht.2, hδε, hδpos]
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact (hK ⟨x, hx⟩).elim

/-- The closed physical edge with a bounded momentum interval is compact.  These boxes are the
compact state sets on which Picard--Lindelöf can be made uniform without extending the potential
outside the open neighbourhood required in the paper. -/
def closedEdgeMomentumBox (e : Γ.Edge) (P : ℝ) : Set (ℝ × ℝ) :=
  Icc (0 : ℝ) (Γ.length e) ×ˢ Icc (-P) P

theorem isCompact_closedEdgeMomentumBox (e : Γ.Edge) (P : ℝ) :
    IsCompact (closedEdgeMomentumBox e P) := by
  exact isCompact_Icc.prod isCompact_Icc

/-- Every physical momentum box lies in the selected extension domain in its position
coordinate. -/
theorem closedEdgeMomentumBox_subset_domain {e : Γ.Edge} {P : ℝ} :
    ∀ x ∈ closedEdgeMomentumBox e P, x.1 ∈ V.domain e := by
  intro x hx
  exact V.closedEdge_subset_domain e hx.1

/-- Uniform local existence on a physical edge and any fixed momentum bound. -/
theorem exists_uniform_local_edge_integralCurve_on_closedEdgeMomentumBox
    (e : Γ.Edge) (P : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ closedEdgeMomentumBox e P, ∃ α : ℝ → ℝ × ℝ,
      α 0 = x ∧ ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt α (V.edgeVectorField e (α t)) t :=
  V.exists_uniform_local_edge_integralCurve_on_compact
    (closedEdgeMomentumBox e P) (isCompact_closedEdgeMomentumBox e P)
    (closedEdgeMomentumBox_subset_domain V)

/-- An upper energy bound and a lower potential bound place a physical state in the compact
momentum box dictated by the elementary kinetic-energy estimate. -/
theorem mem_closedEdgeMomentumBox_of_hamiltonian_le {e : Γ.Edge} {q p C U : ℝ}
    (hq : q ∈ Icc (0 : ℝ) (Γ.length e)) (hpotential : C ≤ V.extension e q)
    (henergy : V.hamiltonian e q p ≤ U) :
    (q, p) ∈ closedEdgeMomentumBox e (Real.sqrt (2 * (U - C))) := by
  constructor
  · exact hq
  · have hp := V.abs_momentum_le_sqrt_of_hamiltonian_le hpotential henergy
    exact abs_le.mp hp

/-- The concrete vector field is `C¹` on every closed physical momentum box. -/
theorem contDiffOn_edgeVectorField_closedMomentumBox (e : Γ.Edge) (P : ℝ) :
    ContDiffOn ℝ 1 (V.edgeVectorField e) (closedEdgeMomentumBox e P) := by
  intro x hx
  exact (V.contDiffAt_edgeVectorField (V.closedEdge_subset_domain e hx.1)).contDiffWithinAt

/-- Compact convex physical momentum boxes turn the local `C¹` estimate into one global
Lipschitz constant. This supplies interval-wide uniqueness for energy-bounded edge segments. -/
theorem exists_lipschitzOnWith_edgeVectorField_closedMomentumBox (e : Γ.Edge) (P : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (V.edgeVectorField e) (closedEdgeMomentumBox e P) :=
  (V.contDiffOn_edgeVectorField_closedMomentumBox e P).exists_lipschitzOnWith
    one_ne_zero ((convex_Icc (0 : ℝ) (Γ.length e)).prod (convex_Icc (-P) P))
    (isCompact_closedEdgeMomentumBox e P)

/-- The mechanical vector field is uniformly bounded on every finite-graph family of closed
physical momentum boxes.  This is the bounded-derivative input for the maximal-continuation
argument; its proof uses the concrete force bound, not a global-flow assumption. -/
theorem exists_uniform_normBound_edgeVectorField_closedMomentumBoxes (P : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ e : Γ.Edge, ∀ x ∈ closedEdgeMomentumBox e P,
      ‖V.edgeVectorField e x‖ ≤ B := by
  obtain ⟨R, hR⟩ := V.exists_uniform_absBound_force_closedEdges
  refine ⟨|P| + |R|, add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  intro e x hx
  rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs, edgeVectorField]
  constructor
  · have hleft : -|P| ≤ -P := neg_le_neg (le_abs_self P)
    have hright : P ≤ |P| := le_abs_self P
    have hxp : -P ≤ x.2 ∧ x.2 ≤ P := hx.2
    have habs : |x.2| ≤ |P| := abs_le.mpr ⟨le_trans hleft hxp.1, le_trans hxp.2 hright⟩
    exact habs.trans (le_add_of_nonneg_right (abs_nonneg R))
  · have hforce : |V.force e x.1| ≤ R := hR e x.1 hx.1
    exact hforce.trans (le_trans (le_abs_self R) (le_add_of_nonneg_left (abs_nonneg P)))

/-- The local Picard--Lindelöf trajectory can be restricted to an interval on which its position
remains in the chosen open extension domain.  This prevents later energy arguments from making
an implicit claim about the potential outside the regularity neighbourhood. -/
theorem exists_local_edge_integralCurve_in_domain {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x.1 ∈ V.domain e) (t₀ : ℝ) :
    ∃ α : ℝ → ℝ × ℝ, α t₀ = x ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        (α t).1 ∈ V.domain e ∧ HasDerivAt α (V.edgeVectorField e (α t)) t := by
  obtain ⟨α, hα₀, ε₀, hε₀, hα⟩ := V.exists_local_edge_integralCurve hx t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε₀) (t₀ + ε₀) := by constructor <;> linarith
  have hcont : ContinuousAt (fun t => (α t).1) t₀ :=
    (V.edgeIntegralCurve_hasDerivAt_fst (hα t₀ ht₀)).continuousAt
  have hpre : (fun t => (α t).1) ⁻¹' V.domain e ∈ 𝓝 t₀ :=
    hcont.preimage_mem_nhds ((V.domain_isOpen e).mem_nhds (by simpa [hα₀] using hx))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨α, hα₀, min (ε₀ / 2) δ, lt_min (by linarith) hδ, ?_⟩
  intro t ht
  have heps : min (ε₀ / 2) δ ≤ ε₀ / 2 := min_le_left _ _
  have hdel : min (ε₀ / 2) δ ≤ δ := min_le_right _ _
  have hdist : dist t t₀ < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, hdel]
  constructor
  · exact hball (by simpa only [Metric.mem_ball] using hdist)
  · apply hα t
    constructor <;> linarith [ht.1, ht.2, heps]

/-- An interior initial state has a nontrivial local trajectory that stays in the physical open
edge cylinder.  This is the starting point for the eventual first-endpoint-hit construction. -/
theorem exists_local_edge_integralCurve_in_openCylinder {e : Γ.Edge} {x : ℝ × ℝ}
    (hxdom : x.1 ∈ V.domain e) (hx : x.1 ∈ Ioo (0 : ℝ) (Γ.length e)) (t₀ : ℝ) :
    ∃ α : ℝ → ℝ × ℝ, α t₀ = x ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        (α t).1 ∈ Ioo (0 : ℝ) (Γ.length e) ∧
          HasDerivAt α (V.edgeVectorField e (α t)) t := by
  obtain ⟨α, hα₀, ε₀, hε₀, hα⟩ := V.exists_local_edge_integralCurve_in_domain hxdom t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε₀) (t₀ + ε₀) := by constructor <;> linarith
  have hcont : ContinuousAt (fun t => (α t).1) t₀ :=
    (V.edgeIntegralCurve_hasDerivAt_fst (hα t₀ ht₀).2).continuousAt
  have hpre : (fun t => (α t).1) ⁻¹' Ioo (0 : ℝ) (Γ.length e) ∈ 𝓝 t₀ :=
    hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by simpa [hα₀] using hx))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨α, hα₀, min (ε₀ / 2) δ, lt_min (by linarith) hδ, ?_⟩
  intro t ht
  have heps : min (ε₀ / 2) δ ≤ ε₀ / 2 := min_le_left _ _
  have hdel : min (ε₀ / 2) δ ≤ δ := min_le_right _ _
  have hdist : dist t t₀ < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, hdel]
  constructor
  · exact hball (by simpa only [Metric.mem_ball] using hdist)
  · exact (hα t (by constructor <;> linarith [ht.1, ht.2, heps])).2

/-- A state at the left endpoint with inward (positive) momentum immediately enters the open
edge cylinder. -/
theorem exists_local_edge_integralCurve_from_leftEndpoint {e : Γ.Edge} {p : ℝ} (hp : 0 < p) :
    ∃ γ : ℝ → ℝ × ℝ, γ 0 = (0, p) ∧
      HasDerivAt γ (V.edgeVectorField e (γ 0)) 0 ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo 0 ε, (γ t).1 ∈ Ioo (0 : ℝ) (Γ.length e) ∧
        HasDerivAt γ (V.edgeVectorField e (γ t)) t := by
  have hdom : (0 : ℝ) ∈ V.domain e :=
    V.closedEdge_subset_domain e ⟨le_rfl, (Γ.length_pos e).le⟩
  obtain ⟨γ, hγ0, ε₀, hε₀, hγ⟩ :=
    V.exists_local_edge_integralCurve_in_domain (x := (0, p)) hdom 0
  have h0 : (0 : ℝ) ∈ Ioo (0 - ε₀) (0 + ε₀) := by constructor <;> linarith
  have hqderiv : HasDerivAt (fun t => (γ t).1) p 0 := by
    simpa [hγ0] using V.edgeIntegralCurve_hasDerivAt_fst (hγ 0 h0).2
  have hγderiv0 : HasDerivAt γ (V.edgeVectorField e (γ 0)) 0 := (hγ 0 h0).2
  have hpos : ∀ᶠ t in 𝓝[>] 0, 0 < (γ t).1 :=
    eventually_pos_right_of_hasDerivAt_pos hqderiv hp (by simp [hγ0])
  have hpos' := eventually_nhdsWithin_iff.mp hpos
  obtain ⟨δp, hδp, hnearpos⟩ := Metric.eventually_nhds_iff.mp hpos'
  have hcont : ContinuousAt (fun t => (γ t).1) 0 := hqderiv.continuousAt
  have hupper : (fun t => (γ t).1) ⁻¹' Iio (Γ.length e) ∈ 𝓝 0 :=
    hcont.preimage_mem_nhds
      (isOpen_Iio.mem_nhds (by simpa [hγ0] using Γ.length_pos e))
  obtain ⟨δu, hδu, hnearupper⟩ := Metric.mem_nhds_iff.mp hupper
  refine ⟨γ, hγ0, hγderiv0, min (ε₀ / 2) (min δp δu),
    lt_min (by linarith) (lt_min hδp hδu), ?_⟩
  intro t ht
  have heps : min (ε₀ / 2) (min δp δu) ≤ ε₀ / 2 := min_le_left _ _
  have hdp : min (ε₀ / 2) (min δp δu) ≤ δp :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hdu : min (ε₀ / 2) (min δp δu) ≤ δu :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hdistp : dist t 0 < δp := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, hdp]
  have hdistu : dist t 0 < δu := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, hdu]
  constructor
  · constructor
    · exact hnearpos (by simpa only [Metric.mem_ball] using hdistp) ht.1
    · exact hnearupper (by simpa only [Metric.mem_ball] using hdistu)
  · exact (hγ t (by constructor <;> linarith [ht.1, ht.2, heps])).2

/-- A state at the right endpoint with inward (negative) momentum immediately enters the open
edge cylinder. -/
theorem exists_local_edge_integralCurve_from_rightEndpoint {e : Γ.Edge} {p : ℝ} (hp : p < 0) :
    ∃ γ : ℝ → ℝ × ℝ, γ 0 = (Γ.length e, p) ∧
      HasDerivAt γ (V.edgeVectorField e (γ 0)) 0 ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo 0 ε, (γ t).1 ∈ Ioo (0 : ℝ) (Γ.length e) ∧
        HasDerivAt γ (V.edgeVectorField e (γ t)) t := by
  have hdom : Γ.length e ∈ V.domain e :=
    V.closedEdge_subset_domain e ⟨(Γ.length_pos e).le, le_rfl⟩
  obtain ⟨γ, hγ0, ε₀, hε₀, hγ⟩ :=
    V.exists_local_edge_integralCurve_in_domain (x := (Γ.length e, p)) hdom 0
  have h0 : (0 : ℝ) ∈ Ioo (0 - ε₀) (0 + ε₀) := by constructor <;> linarith
  have hqderiv : HasDerivAt (fun t => (γ t).1 - Γ.length e) p 0 := by
    simpa [hγ0] using
      (V.edgeIntegralCurve_hasDerivAt_fst (hγ 0 h0).2).sub_const (Γ.length e)
  have hγderiv0 : HasDerivAt γ (V.edgeVectorField e (γ 0)) 0 := (hγ 0 h0).2
  have hneg : ∀ᶠ t in 𝓝[>] 0, (γ t).1 - Γ.length e < 0 :=
    eventually_neg_right_of_hasDerivAt_neg hqderiv hp (by simp [hγ0])
  have hneg' := eventually_nhdsWithin_iff.mp hneg
  obtain ⟨δp, hδp, hnearneg⟩ := Metric.eventually_nhds_iff.mp hneg'
  have hcont : ContinuousAt (fun t => (γ t).1) 0 :=
    (V.edgeIntegralCurve_hasDerivAt_fst (hγ 0 h0).2).continuousAt
  have hlower : (fun t => (γ t).1) ⁻¹' Ioi (0 : ℝ) ∈ 𝓝 0 :=
    hcont.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (by simpa [hγ0] using Γ.length_pos e))
  obtain ⟨δu, hδu, hnearlower⟩ := Metric.mem_nhds_iff.mp hlower
  refine ⟨γ, hγ0, hγderiv0, min (ε₀ / 2) (min δp δu),
    lt_min (by linarith) (lt_min hδp hδu), ?_⟩
  intro t ht
  have heps : min (ε₀ / 2) (min δp δu) ≤ ε₀ / 2 := min_le_left _ _
  have hdp : min (ε₀ / 2) (min δp δu) ≤ δp :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hdu : min (ε₀ / 2) (min δp δu) ≤ δu :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hdistp : dist t 0 < δp := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, hdp]
  have hdistu : dist t 0 < δu := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, hdu]
  constructor
  · constructor
    · exact hnearlower (by simpa only [Metric.mem_ball] using hdistu)
    · linarith [hnearneg (by simpa only [Metric.mem_ball] using hdistp) ht.1]
  · exact (hγ t (by constructor <;> linarith [ht.1, ht.2, heps])).2

/-- The outgoing sign convention at either endpoint produces a positive-time solution in the
open cylinder of the selected edge.  Thus scattering does not leave a trajectory stranded at a
vertex. -/
theorem exists_local_edge_integralCurve_from_outgoingBoundary {v : Γ.Vertex}
    (α : Γ.OutgoingBoundary v) :
    ∃ γ : ℝ → ℝ × ℝ,
      γ 0 = (FiniteMetricGraph.EdgeEnd.coordinate Γ α.1.germ, α.1.momentum) ∧
        HasDerivAt γ (V.edgeVectorField α.1.germ.1 (γ 0)) 0 ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo 0 ε, (γ t).1 ∈ Ioo (0 : ℝ) (Γ.length α.1.germ.1) ∧
        HasDerivAt γ (V.edgeVectorField α.1.germ.1 (γ t)) t := by
  rcases α with ⟨⟨⟨e, b⟩, p, hp⟩, hv, hout⟩
  cases b
  · have hppos : 0 < p := by simpa [FiniteMetricGraph.EdgeEnd.sign] using hout
    simpa [FiniteMetricGraph.EdgeEnd.coordinate] using
      V.exists_local_edge_integralCurve_from_leftEndpoint (e := e) hppos
  · have hpneg : p < 0 := by simpa [FiniteMetricGraph.EdgeEnd.sign] using hout
    simpa [FiniteMetricGraph.EdgeEnd.coordinate] using
      V.exists_local_edge_integralCurve_from_rightEndpoint (e := e) hpneg

/-- Uniqueness of concrete edge trajectories on any interval where they remain in a common
Lipschitz neighbourhood of the mechanical vector field. -/
theorem edge_integralCurve_unique_on_Ioo {e : Γ.Edge} {K : ℝ≥0} {s : Set (ℝ × ℝ)}
    {a b t₀ : ℝ} {f g : ℝ → ℝ × ℝ}
    (hLip : LipschitzOnWith K (V.edgeVectorField e) s) (ht₀ : t₀ ∈ Ioo a b)
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (V.edgeVectorField e (f t)) t ∧ f t ∈ s)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (V.edgeVectorField e (g t)) t ∧ g t ∈ s)
    (hfg : f t₀ = g t₀) : EqOn f g (Ioo a b) := by
  exact ODE_solution_unique_of_mem_Ioo (v := fun _ => V.edgeVectorField e)
    (s := fun _ => s) (fun _ _ => hLip) ht₀ hf hg hfg

/-- Along a coordinate solution of Hamilton's equations, the mechanical Hamiltonian has
zero derivative.  This is the concrete energy calculation used by the collision construction;
the potential extension is only used at points certified to lie in its chosen open domain. -/
theorem hamiltonian_hasDerivAt_zero_of_hamiltonEquations {e : Γ.Edge} {q p : ℝ → ℝ} {t : ℝ}
    (ht : q t ∈ V.domain e)
    (hq : HasDerivAt q (p t) t)
    (hp : HasDerivAt p (-deriv (V.extension e) (q t)) t) :
    HasDerivAt (fun s => V.hamiltonian e (q s) (p s)) 0 t := by
  have hV₀ : HasDerivAt (V.extension e) (deriv (V.extension e) (q t)) (q t) :=
    ((V.extension_contDiffAt_of_mem ht).differentiableAt (by norm_num)).hasDerivAt
  have hV : HasDerivAt (V.extension e ∘ q)
      (deriv (V.extension e) (q t) * p t) t := by
    simpa only [Function.comp_apply] using hV₀.comp t hq
  have hsum := (hp.pow 2).div_const 2 |>.add hV
  refine (hsum.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [] with s
    simp [hamiltonian, Function.comp_def]
  · dsimp at hsum ⊢
    ring

/-- One-sided version of the energy calculation: along a within-solution of Hamilton's
equations, the mechanical Hamiltonian has zero within-derivative. -/
theorem hamiltonian_hasDerivWithinAt_zero_of_hamiltonEquations {e : Γ.Edge} {q p : ℝ → ℝ}
    {s : Set ℝ} {t : ℝ}
    (ht : q t ∈ V.domain e)
    (hq : HasDerivWithinAt q (p t) s t)
    (hp : HasDerivWithinAt p (-deriv (V.extension e) (q t)) s t) :
    HasDerivWithinAt (fun u => V.hamiltonian e (q u) (p u)) 0 s t := by
  have hV₀ : HasDerivAt (V.extension e) (deriv (V.extension e) (q t)) (q t) :=
    ((V.extension_contDiffAt_of_mem ht).differentiableAt (by norm_num)).hasDerivAt
  have hV : HasDerivWithinAt (V.extension e ∘ q)
      (deriv (V.extension e) (q t) * p t) s t := by
    simpa only [Function.comp_apply] using hV₀.comp_hasDerivWithinAt t hq
  have hsum := ((hp.pow 2).div_const 2).add hV
  refine (hsum.congr_of_eventuallyEq ?_ ?_).congr_deriv ?_
  · filter_upwards [] with u
    simp [hamiltonian, Function.comp_def]
  · simp [hamiltonian, Function.comp_def]
  · push_cast; ring

/-- Energy is constant on every closed time interval on which a coordinate solution remains in
the extension domain and satisfies Hamilton's equations in the one-sided (within-`Icc`) sense.
This is the form applicable to a maximal edge flight, whose terminal derivative is one-sided. -/
theorem hamiltonian_eq_of_hamiltonEquations_within {e : Γ.Edge} {q p : ℝ → ℝ} {a b : ℝ}
    (hdom : ∀ t ∈ Icc a b, q t ∈ V.domain e)
    (hq : ∀ t ∈ Icc a b, HasDerivWithinAt q (p t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (-deriv (V.extension e) (q t)) (Icc a b) t) :
    ∀ t ∈ Icc a b, V.hamiltonian e (q t) (p t) = V.hamiltonian e (q a) (p a) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · apply constant_of_derivWithin_zero
    · intro t ht
      exact (V.hamiltonian_hasDerivWithinAt_zero_of_hamiltonEquations
        (hdom t ht) (hq t ht) (hp t ht)).differentiableWithinAt
    · intro t ht
      exact (V.hamiltonian_hasDerivWithinAt_zero_of_hamiltonEquations
        (hdom t (mem_Icc_of_Ico ht)) (hq t (mem_Icc_of_Ico ht))
        (hp t (mem_Icc_of_Ico ht))).derivWithin
          ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt (mem_Icc_of_Ico ht))
  · intro t ht
    have hta : t = a := le_antisymm ht.2 ht.1
    subst t
    rfl
  · intro t ht
    exact (not_lt_of_ge (le_trans ht.1 ht.2) hba).elim

/-- The mechanical Hamiltonian has zero derivative along a vector-valued integral curve. -/
theorem hamiltonian_hasDerivAt_zero_of_edgeIntegralCurve {e : Γ.Edge} {α : ℝ → ℝ × ℝ} {t : ℝ}
    (ht : (α t).1 ∈ V.domain e)
    (hα : HasDerivAt α (V.edgeVectorField e (α t)) t) :
    HasDerivAt (fun s => V.hamiltonian e (α s).1 (α s).2) 0 t := by
  exact V.hamiltonian_hasDerivAt_zero_of_hamiltonEquations ht
    (V.edgeIntegralCurve_hasDerivAt_fst hα) (by
      simpa [force] using V.edgeIntegralCurve_hasDerivAt_snd hα)

/-- Energy is constant on every closed time interval on which a coordinate solution remains in
the extension domain and satisfies Hamilton's equations. -/
theorem hamiltonian_eq_of_hamiltonEquations {e : Γ.Edge} {q p : ℝ → ℝ} {a b : ℝ}
    (hdom : ∀ t ∈ Icc a b, q t ∈ V.domain e)
    (hq : ∀ t ∈ Icc a b, HasDerivAt q (p t) t)
    (hp : ∀ t ∈ Icc a b, HasDerivAt p (-deriv (V.extension e) (q t)) t) :
    ∀ t ∈ Icc a b, V.hamiltonian e (q t) (p t) = V.hamiltonian e (q a) (p a) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · apply constant_of_derivWithin_zero
    · intro t ht
      exact (V.hamiltonian_hasDerivAt_zero_of_hamiltonEquations (hdom t ht) (hq t ht)
        (hp t ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have h := V.hamiltonian_hasDerivAt_zero_of_hamiltonEquations
        (hdom t (mem_Icc_of_Ico ht)) (hq t (mem_Icc_of_Ico ht)) (hp t (mem_Icc_of_Ico ht))
      exact h.hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt (mem_Icc_of_Ico ht))
  · intro t ht
    have hta : t = a := le_antisymm ht.2 ht.1
    subst t
    rfl
  · intro t ht
    exact (not_lt_of_ge (le_trans ht.1 ht.2) hba).elim

end MechanicalPotential
end HamiltonianMetricGraphs
