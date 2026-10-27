/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition VII.1: the passage of a flight along one momentum branch
-/

import HamiltonianMetricGraphs.ShellMeasure

/-!
# A flight traverses one momentum branch in the time `∫ dq / |p|` (Proposition VII.1)

The proof of Proposition VII.1 parametrizes each open branch
`{(q, ε √(2(E - V_e(q)))) : q ∈ J}` of the energy level by the time coordinate
`dt = dq / p`.  This module proves the corresponding statement about an actual solution of the
edge equations, under the hypotheses of the proposition and **without** shell-regularity.

A solution `c(u) = (q(u), p(u))` of Hamilton's equations at energy `E` starts at a *branch start*
`(α, ε √(2(E - V_e(α))))`: either a simple interior turning point (`V_e(α) = E`, with the force
pushing in the direction `ε`), or a point of the allowed region `V_e(α) < E` (a vertex departure).
Then (`exists_sheetTraverse`) there are a far end `β` and a time `τ > 0` such that

* for `0 < u < τ` the solution is on the open branch: `q(u)` lies strictly between `α` and `β`,
  `V_e(q(u)) < E`, `p(u) = ε √(2(E - V_e(q(u))))`, and the oriented travel time
  `sheetTime α ε (q(u)) = ε ∫_α^{q(u)} dr / √(2(E - V_e(r)))` equals `u`;
* every position strictly between `α` and `β` is reached at some `u ∈ (0, τ)`;
* at `u = τ` the solution is at `(β, ε √(2(E - V_e(β))))`, where either `β` is an interior turning
  point (`V_e(β) = E`, and the solution continues past `τ`), or `β` is an endpoint of the edge
  reached at the end `D` of the solution's interval.

The proof is elementary: the momentum keeps the sign `ε` up to a maximal time `u*`, during which
`d/du sheetTime(q(u)) = (ε / |p|) p = 1`; the travel time is bounded by the finite total time
`∫ dq / |p|` of the edge, so `u*` is finite, and at `u*` either the momentum vanishes (a turning
point) or the solution has reached a vertex.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory intervalIntegral
open scoped Topology ENNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- The oriented travel time from `α` in the direction `ε` along the energy level `E` of `e`:
`ε ∫_α^q dr / √(2(E - V_e(r)))`. -/
noncomputable def sheetTime (e : Γ.Edge) (E α ε q : ℝ) : ℝ :=
  ε * ∫ r in α..q, 1 / V.speedAt e E r

@[simp] theorem sheetTime_self (e : Γ.Edge) (E α ε : ℝ) : V.sheetTime e E α ε α = 0 := by
  simp [sheetTime]

theorem continuousOn_sheetTime (e : Γ.Edge) {E α ε : ℝ}
    (hint : IntervalIntegrable (fun r => 1 / V.speedAt e E r) volume 0 (Γ.length e))
    (hα : α ∈ Icc 0 (Γ.length e)) :
    ContinuousOn (V.sheetTime e E α ε) (Icc 0 (Γ.length e)) := by
  have hle : (0 : ℝ) ≤ Γ.length e := (Γ.length_pos e).le
  have h := intervalIntegral.continuousOn_primitive_interval' hint
    (by rw [uIcc_of_le hle]; exact hα)
  rw [uIcc_of_le hle] at h
  exact continuousOn_const.mul h

theorem isOpen_allowedDomain (e : Γ.Edge) (E : ℝ) :
    IsOpen (V.domain e ∩ V.extension e ⁻¹' Iio E) :=
  ((V.contDiffOn_extension e).continuousOn).isOpen_inter_preimage (V.domain_isOpen e) isOpen_Iio

theorem continuousOn_one_div_speedAt (e : Γ.Edge) (E : ℝ) :
    ContinuousOn (fun r => 1 / V.speedAt e E r) (V.domain e ∩ V.extension e ⁻¹' Iio E) := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  exact ContinuousAt.div continuousAt_const (V.continuousAt_speedAt e hx.1)
    (ne_of_gt (V.speedAt_pos e hx.2))

/-- The oriented travel time has derivative `ε / √(2(E - V_e(q)))` in the allowed region. -/
theorem hasDerivAt_sheetTime (e : Γ.Edge) {E α ε q : ℝ}
    (hint : IntervalIntegrable (fun r => 1 / V.speedAt e E r) volume 0 (Γ.length e))
    (hα : α ∈ Icc 0 (Γ.length e)) (hq : q ∈ Icc 0 (Γ.length e)) (hqE : V.extension e q < E) :
    HasDerivAt (V.sheetTime e E α ε) (ε * (1 / V.speedAt e E q)) q := by
  have hle : (0 : ℝ) ≤ Γ.length e := (Γ.length_pos e).le
  have hO : q ∈ V.domain e ∩ V.extension e ⁻¹' Iio E :=
    ⟨V.closedEdge_subset_domain e hq, hqE⟩
  have hint' : IntervalIntegrable (fun r => 1 / V.speedAt e E r) volume α q := by
    refine hint.mono_set ?_
    rw [uIcc_of_le hle]
    exact uIcc_subset_Icc hα hq
  have h := intervalIntegral.integral_hasDerivAt_right hint'
    ((V.continuousOn_one_div_speedAt e E).stronglyMeasurableAtFilter
      (V.isOpen_allowedDomain e E) q hO)
    ((V.continuousOn_one_div_speedAt e E q hO).continuousAt
      ((V.isOpen_allowedDomain e E).mem_nhds hO))
  exact h.const_mul ε

theorem eps_mul_self {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  rcases hε with rfl | rfl <;> norm_num

/-- With `ε p > 0`, the momentum is `ε |p|`. -/
theorem eq_eps_mul_abs {ε p : ℝ} (hε : ε = 1 ∨ ε = -1) (hp : 0 ≤ ε * p) : p = ε * |p| := by
  rcases hε with rfl | rfl
  · rw [one_mul] at hp ⊢; rw [abs_of_nonneg hp]
  · have : p ≤ 0 := by linarith
    rw [abs_of_nonpos this]; ring

/-- Membership in `uIoo a b` from a strict inequality in the direction `ε`. -/
theorem mem_uIoo_of_eps {ε a b x : ℝ} (hε : ε = 1 ∨ ε = -1) (h1 : ε * a < ε * x)
    (h2 : ε * x < ε * b) : x ∈ uIoo a b := by
  rw [uIoo, mem_Ioo]
  rcases hε with rfl | rfl
  · simp only [one_mul] at h1 h2
    exact ⟨lt_of_le_of_lt (min_le_left _ _) h1, lt_of_lt_of_le h2 (le_max_right _ _)⟩
  · have h1' : x < a := by linarith
    have h2' : b < x := by linarith
    exact ⟨lt_of_le_of_lt (min_le_right _ _) h2', lt_of_lt_of_le h1' (le_max_left _ _)⟩

theorem ne_of_mem_uIoo {a b x : ℝ} (hx : x ∈ uIoo a b) : x ≠ a ∧ x ≠ b := by
  rw [uIoo, mem_Ioo] at hx
  constructor <;> rintro rfl
  · rcases le_total x b with h | h
    · rw [min_eq_left h] at hx; exact lt_irrefl _ hx.1
    · rw [max_eq_left h] at hx; exact lt_irrefl _ hx.2
  · rcases le_total a x with h | h
    · rw [max_eq_right h] at hx; exact lt_irrefl _ hx.2
    · rw [min_eq_right h] at hx; exact lt_irrefl _ hx.1

/-- **A solution traverses one open momentum branch.**  See the module docstring. -/
theorem exists_sheetTraverse (e : Γ.Edge) {E α ε D : ℝ} (hε : ε = 1 ∨ ε = -1)
    {c : ℝ → ℝ × ℝ} (hα : α ∈ Icc 0 (Γ.length e))
    (hstart : (V.extension e α = E ∧ 0 < ε * V.force e α) ∨ V.extension e α < E)
    (hc0 : c 0 = (α, ε * V.speedAt e E α)) (hD : 0 < D)
    (hcont : ContinuousOn c (Icc 0 D))
    (hder0 : HasDerivWithinAt c (V.edgeVectorField e (c 0)) (Ici 0) 0)
    (hder : ∀ u ∈ Ioo 0 D, HasDerivAt c (V.edgeVectorField e (c u)) u)
    (henergy : ∀ u ∈ Icc 0 D, V.hamiltonian e (c u).1 (c u).2 = E)
    (hphys : ∀ u ∈ Icc 0 D, (c u).1 ∈ Icc 0 (Γ.length e))
    (hinter : ∀ u ∈ Ioo 0 D, (c u).1 ∈ Ioo 0 (Γ.length e))
    (hint : IntervalIntegrable (fun r => 1 / V.speedAt e E r) volume 0 (Γ.length e))
    (hend : (c D).1 ∉ Ioo 0 (Γ.length e) ∨
      ∀ q ∈ Icc 0 (Γ.length e), V.sheetTime e E α ε q < D) :
    ∃ β τ : ℝ, 0 < τ ∧ τ ≤ D ∧ β ∈ Icc 0 (Γ.length e) ∧ 0 < ε * (β - α) ∧
      V.sheetTime e E α ε β = τ ∧ c τ = (β, ε * V.speedAt e E β) ∧
      ((β ∈ Ioo 0 (Γ.length e) ∧ V.extension e β = E ∧ τ < D) ∨
        (β ∉ Ioo 0 (Γ.length e) ∧ τ = D)) ∧
      (∀ u ∈ Ioo 0 τ, (c u).1 ∈ uIoo α β ∧ V.extension e (c u).1 < E ∧
        (c u).2 = ε * V.speedAt e E (c u).1 ∧ V.sheetTime e E α ε (c u).1 = u) ∧
      (∀ r ∈ uIoo α β, ∃ u ∈ Ioo 0 τ, (c u).1 = r) := by
  set ℓ := Γ.length e with hℓ
  have hε2 : ε * ε = 1 := eps_mul_self hε
  have hqcont : ContinuousOn (fun u => (c u).1) (Icc 0 D) := continuous_fst.comp_continuousOn hcont
  have hpcont : ContinuousOn (fun u => (c u).2) (Icc 0 D) := continuous_snd.comp_continuousOn hcont
  have hqder : ∀ u ∈ Ioo 0 D, HasDerivAt (fun w => (c w).1) (c u).2 u :=
    fun u hu => (hder u hu).fst
  have hpder : ∀ u ∈ Ioo 0 D, HasDerivAt (fun w => (c w).2) (V.force e (c u).1) u :=
    fun u hu => (hder u hu).snd
  have hsp : ∀ u ∈ Icc 0 D, V.speedAt e E (c u).1 = |(c u).2| :=
    fun u hu => V.speedAt_eq_abs_of_hamiltonian (henergy u hu)
  have hq0 : (c 0).1 = α := by rw [hc0]
  have hp0 : (c 0).2 = ε * V.speedAt e E α := by rw [hc0]
  have hD0 : (0 : ℝ) ∈ Icc 0 D := ⟨le_rfl, hD.le⟩
  -- Step 1: the momentum has the sign `ε` just after the start
  have hev : ∀ᶠ w in 𝓝[>] (0 : ℝ), 0 < ε * (c w).2 := by
    rcases hstart with ⟨hVα, hF⟩ | hVα
    · have hs0 : V.speedAt e E α = 0 := by
        unfold speedAt; rw [hVα, sub_self, mul_zero, Real.sqrt_zero]
      have hd : HasDerivWithinAt (fun w => ε * (c w).2) (ε * V.force e α) (Ici 0) 0 := by
        have h1 := (hasFDerivAt_snd (𝕜 := ℝ) (p := c 0)).comp_hasDerivWithinAt (0 : ℝ) hder0
        have h2 : HasDerivWithinAt (fun w => (c w).2) (V.force e α) (Ici 0) 0 := by
          have h3 : HasDerivWithinAt (Prod.snd ∘ c) (V.force e α) (Ici 0) 0 := by
            simpa [edgeVectorField, hq0] using h1
          exact h3
        exact h2.const_mul ε
      have hsl := hasDerivWithinAt_iff_tendsto_slope.mp hd
      rw [Ici_sdiff_left] at hsl
      filter_upwards [hsl.eventually (lt_mem_nhds hF), self_mem_nhdsWithin] with w hw hw0
      rw [slope_def_field, hp0, hs0, mul_zero, mul_zero, sub_zero, sub_zero] at hw
      exact (div_pos_iff_of_pos_right (show (0 : ℝ) < w from hw0)).mp hw
    · have hpos0 : 0 < ε * (c 0).2 := by
        rw [hp0, ← mul_assoc, hε2, one_mul]
        exact V.speedAt_pos e hVα
      have hcw : ContinuousWithinAt (fun w => ε * (c w).2) (Ioo 0 D) 0 :=
        ((continuous_const.mul continuous_snd).comp_continuousOn hcont 0 hD0).mono
          Ioo_subset_Icc_self
      rw [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT hD] at hcw
      exact hcw.eventually (lt_mem_nhds hpos0)
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  set δ := min δ₀ D with hδdef
  have hδpos : 0 < δ := lt_min hδ₀ hD
  have hδD : δ ≤ D := min_le_right _ _
  -- Step 2: the maximal time `u*` with the sign `ε`
  set K : Set ℝ := {u | u ∈ Icc 0 D ∧ ∀ w ∈ Ioo 0 u, 0 < ε * (c w).2} with hK
  have hδK : δ ∈ K := ⟨⟨hδpos.le, hδD⟩, fun w hw =>
    hδ₀sub ⟨hw.1, lt_of_lt_of_le hw.2 (min_le_left _ _)⟩⟩
  have hKbdd : BddAbove K := ⟨D, fun u hu => hu.1.2⟩
  set us := sSup K with hus
  have hδus : δ ≤ us := le_csSup hKbdd hδK
  have husD : us ≤ D := csSup_le ⟨δ, hδK⟩ fun u hu => hu.1.2
  have hus0 : 0 < us := lt_of_lt_of_le hδpos hδus
  have hpos : ∀ w ∈ Ioo 0 us, 0 < ε * (c w).2 := by
    intro w hw
    obtain ⟨u, huK, hwu⟩ := exists_lt_of_lt_csSup ⟨δ, hδK⟩ hw.2
    exact huK.2 w ⟨hw.1, hwu⟩
  have hIoo : ∀ w ∈ Ioo 0 us, w ∈ Ioo 0 D := fun w hw => ⟨hw.1, lt_of_lt_of_le hw.2 husD⟩
  have hIcc : ∀ w ∈ Icc 0 us, w ∈ Icc 0 D := fun w hw => ⟨hw.1, le_trans hw.2 husD⟩
  -- Step 3: on `(0, u*)` the solution is on the open branch
  have hpeq : ∀ w ∈ Ioo 0 us, (c w).2 = ε * V.speedAt e E (c w).1 := by
    intro w hw
    rw [hsp w (Ioo_subset_Icc_self (hIoo w hw))]
    exact eq_eps_mul_abs hε (hpos w hw).le
  have hVlt : ∀ w ∈ Ioo 0 us, V.extension e (c w).1 < E := by
    intro w hw
    have hE := henergy w (Ioo_subset_Icc_self (hIoo w hw))
    have hne : (c w).2 ≠ 0 := by
      intro h0; have := hpos w hw; rw [h0, mul_zero] at this; exact lt_irrefl _ this
    have : 0 < (c w).2 ^ 2 := by positivity
    unfold hamiltonian at hE
    linarith
  have hspos : ∀ w ∈ Ioo 0 us, 0 < V.speedAt e E (c w).1 :=
    fun w hw => V.speedAt_pos e (hVlt w hw)
  -- Step 4: the travel time equals the elapsed time
  set g : ℝ → ℝ := fun w => V.sheetTime e E α ε (c w).1 - w with hg
  have hgcont : ContinuousOn g (Icc 0 us) := by
    refine ContinuousOn.sub ?_ continuousOn_id
    exact (V.continuousOn_sheetTime e hint hα).comp (hqcont.mono (fun w hw => hIcc w hw))
      (fun w hw => hphys w (hIcc w hw))
  have hgder : ∀ w ∈ Ioo 0 us, HasDerivAt g 0 w := by
    intro w hw
    have hT := V.hasDerivAt_sheetTime e (ε := ε) hint hα (hphys w (Ioo_subset_Icc_self (hIoo w hw)))
      (hVlt w hw)
    have h := (hT.comp w (hqder w (hIoo w hw))).sub (hasDerivAt_id w)
    refine h.congr_deriv ?_
    rw [hpeq w hw]
    field_simp [(hspos w hw).ne']
    linear_combination hε2
  have hg0 : g 0 = 0 := by simp [hg, hq0]
  have hgzero : ∀ w ∈ Ico 0 us, g w = 0 := by
    intro w hw
    rcases eq_or_lt_of_le hw.1 with h | h
    · rw [← h, hg0]
    obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope g (fun _ => 0) h
      (hgcont.mono (Icc_subset_Icc le_rfl hw.2.le))
      (fun x hx => hgder x ⟨hx.1, lt_trans hx.2 hw.2⟩)
    rw [hg0, sub_zero] at hξ
    have hw0 : w - 0 ≠ 0 := by rw [sub_zero]; exact h.ne'
    rw [eq_div_iff hw0, zero_mul] at hξ
    exact hξ.symm
  have hTq : ∀ w ∈ Ico 0 us, V.sheetTime e E α ε (c w).1 = w := by
    intro w hw
    have := hgzero w hw
    simp only [hg] at this
    linarith
  have hgus : g us = 0 := by
    have h1 : Tendsto g (𝓝[<] us) (𝓝 (g us)) := by
      have := (hgcont us ⟨hus0.le, le_rfl⟩).mono (Ico_subset_Icc_self : Ico (0 : ℝ) us ⊆ Icc 0 us)
      rw [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsLT hus0] at this
      exact this
    have h2 : Tendsto g (𝓝[<] us) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hus0] with w hw
      exact (hgzero w ⟨hw.1.le, hw.2⟩).symm
    exact tendsto_nhds_unique h1 h2
  have hTus : V.sheetTime e E α ε (c us).1 = us := by
    simp only [hg] at hgus; linarith
  -- strict monotonicity of the oriented position
  have hmono : StrictMonoOn (fun w => ε * (c w).1) (Icc 0 us) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun w => ε * (c w).2) (convex_Icc 0 us)
      ((continuousOn_const.mul hqcont).mono (fun w hw => hIcc w hw)) ?_ ?_
    · intro w hw
      rw [interior_Icc] at hw
      exact ((hqder w (hIoo w hw)).const_mul ε).hasDerivWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      exact hpos w hw
  -- the sign at `u*`
  have hpus : 0 ≤ ε * (c us).2 := by
    have hcw : ContinuousWithinAt (fun w => ε * (c w).2) (Ico 0 us) us :=
      ((continuous_const.mul continuous_snd).comp_continuousOn hcont us ⟨hus0.le, husD⟩).mono
        (fun w hw => ⟨hw.1, le_trans hw.2.le husD⟩)
    rw [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsLT hus0] at hcw
    refine ge_of_tendsto hcw ?_
    filter_upwards [Ioo_mem_nhdsLT hus0] with w hw
    exact (hpos w hw).le
  have hpus_eq : (c us).2 = ε * V.speedAt e E (c us).1 := by
    rw [hsp us ⟨hus0.le, husD⟩]
    exact eq_eps_mul_abs hε hpus
  -- Step 5: the end of the branch
  refine ⟨(c us).1, us, hus0, husD, hphys us ⟨hus0.le, husD⟩, ?_, hTus, ?_, ?_, ?_, ?_⟩
  · have := hmono ⟨le_rfl, hus0.le⟩ ⟨hus0.le, le_rfl⟩ hus0
    simp only [hq0] at this
    linarith
  · exact Prod.ext rfl hpus_eq
  · rcases lt_or_eq_of_le husD with hlt | heq
    · -- the momentum vanishes at `u*`
      left
      have hp0' : (c us).2 = 0 := by
        by_contra hne
        have hposus : 0 < ε * (c us).2 := by
          rcases lt_or_eq_of_le hpus with h | h
          · exact h
          · exfalso
            rcases hε with rfl | rfl
            · exact hne (by linarith)
            · exact hne (by linarith)
        have hcont' : ContinuousAt (fun w => ε * (c w).2) us :=
          ((hpder us ⟨hus0, hlt⟩).continuousAt).const_mul ε
        obtain ⟨η, hη, hηsub⟩ := Metric.eventually_nhds_iff.mp
          (hcont'.eventually (lt_mem_nhds hposus))
        set u' := min (us + η / 2) D with hu'
        have hu'K : u' ∈ K := by
          refine ⟨⟨by positivity, min_le_right _ _⟩, fun w hw => ?_⟩
          rcases lt_or_ge w us with hwu | hwu
          · exact hpos w ⟨hw.1, hwu⟩
          · refine hηsub ?_
            rw [Real.dist_eq, abs_lt]
            have : w < us + η / 2 := lt_of_lt_of_le hw.2 (min_le_left _ _)
            constructor <;> linarith
        have hle := le_csSup hKbdd hu'K
        have hgt : us < u' := lt_min (by linarith) hlt
        linarith
      have hint' := hinter us ⟨hus0, hlt⟩
      refine ⟨hint', ?_, hlt⟩
      have hE := henergy us ⟨hus0.le, husD⟩
      rw [hamiltonian, hp0'] at hE
      linarith
    · right
      refine ⟨?_, heq⟩
      rcases hend with h | h
      · rw [heq]; exact h
      · exfalso
        have := h _ (hphys us ⟨hus0.le, husD⟩)
        rw [hTus, heq] at this
        exact lt_irrefl _ this
  · intro u hu
    refine ⟨?_, hVlt u hu, hpeq u hu, hTq u ⟨hu.1.le, hu.2⟩⟩
    have h1 := hmono ⟨le_rfl, hus0.le⟩ ⟨hu.1.le, hu.2.le⟩ hu.1
    have h2 := hmono ⟨hu.1.le, hu.2.le⟩ ⟨hus0.le, le_rfl⟩ hu.2
    simp only [hq0] at h1
    exact mem_uIoo_of_eps hε h1 h2
  · intro r hr
    have hr' : r ∈ uIcc ((c 0).1) ((c us).1) := by
      rw [hq0]; exact uIoo_subset_uIcc_self hr
    have hivt := intermediate_value_uIcc (a := (0 : ℝ)) (b := us) (f := fun w => (c w).1)
      (by rw [uIcc_of_le hus0.le]; exact hqcont.mono (fun w hw => hIcc w hw)) hr'
    obtain ⟨u, hu, hur⟩ := hivt
    rw [uIcc_of_le hus0.le] at hu
    obtain ⟨hrα, hrβ⟩ := ne_of_mem_uIoo hr
    refine ⟨u, ⟨lt_of_le_of_ne hu.1 ?_, lt_of_le_of_ne hu.2 ?_⟩, hur⟩
    · rintro rfl; exact hrα (hur.symm.trans hq0)
    · rintro rfl; exact hrβ hur.symm

end MechanicalPotential

end HamiltonianMetricGraphs
