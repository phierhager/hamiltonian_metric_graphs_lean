/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition VII.1: the time parametrization of `ν_E` and its flow invariance
-/

import HamiltonianMetricGraphs.EnergySurfaceExactSection

/-!
# The time parametrization of `ν_E` and its invariance (Proposition VII.1)

`ν_E = regularShellMeasure S E` is the measure of Proposition VII.1: the pushforward of the branch
measures `dq / √(2(E - V_e(q)))` on `U_e(E)` under `q ↦ π(e, q, ±√(2(E - V_e(q))))`
(`lintegral_quotientShellMeasure_eq_branches`).  At an energy `E` as in Proposition VII.1 (not a
vertex value, a regular value of every `V_e` on the open edge; **no shell-regularity**) we prove:

* `regularShellMeasure_eq_sum_branchSection` — **the time parametrization**: for every Borel set
  `B` of regular states,
  `ν_E(B) = ∑_{z ∈ branchSection E} Leb {u ∈ [0, τ_z) : Φ_u z ∈ B}`,
  `τ_z` the time the flow from `z` needs to traverse its open branch.  This is the paper's
  `|dt| = dq / |p|`: on each branch the substitution `u = ε ∫_α^q dr / |p|` turns the branch
  measure into Lebesgue measure in the time `u` (`volume_piece_eq`), and the open branches from
  the finitely many points of the section tile the open branches of every edge
  (`iUnion_pieces_eq_allowedPositions`, `disjoint_pieces`).
* `regularShellMeasure_preimage_flow` — **invariance**: `ν_E(Φ_t⁻¹ A) = ν_E(A)` for every Borel
  `A` and every `t ∈ ℝ`, by the suspension criterion `measure_preimage_eq_of_suspension`.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-! ### The branch maps -/

/-- The branch map `q ↦ π(e, q, ε √(2(E - V_e(q))))`, `ε = boolSign b`, written with the clamped
potential so that it is Borel on all of `ℝ`; it is the paper's branch map on the closed edge
(`branchClass_of_mem`). -/
noncomputable def branchClass (e : Γ.Edge) (E : ℝ) (b : Bool) (q : ℝ) :
    ScatteringPhaseSpace (V := V) S :=
  graphClass V S (e, q, boolSign b * Real.sqrt (2 * (E - V.clampedPotential e q)))

theorem measurable_branchClass (e : Γ.Edge) (E : ℝ) (b : Bool) :
    Measurable (V.branchClass S e E b) := by
  refine (V.measurable_graphClass S).comp ?_
  have hc := V.continuous_clampedPotential e
  exact (measurable_const.prodMk (measurable_id.prodMk
    (measurable_const.mul (by fun_prop))))

theorem branchClass_of_mem (e : Γ.Edge) (E : ℝ) (b : Bool) {q : ℝ}
    (hq : q ∈ Icc 0 (Γ.length e)) :
    V.branchClass S e E b q = graphClass V S (e, q, boolSign b * V.speedAt e E q) := by
  rw [branchClass, V.clampedPotential_of_mem e hq]
  rfl

theorem allowedPositions_subset (e : Γ.Edge) (E : ℝ) :
    V.allowedPositions e E ⊆ Icc 0 (Γ.length e) := fun _ hq => Ioo_subset_Icc_self hq.1

/-- **The branch formula for sets.**  `ν_E(B)` is the sum over edges and momentum signs of the
branch measure `dq / √(2(E - V_e(q)))` of the positions in `U_e(E)` whose branch point is in `B`. -/
theorem regularShellMeasure_apply_branches (E : ℝ)
    {B : Set (RegularScatteringPhaseSpace (V := V) S)} (hB : MeasurableSet B) :
    V.regularShellMeasure S E B = ∑ e, ∑ b : Bool,
      (volume.withDensity (V.timeDensity e E))
        (V.allowedPositions e E ∩ V.branchClass S e E b ⁻¹' (Subtype.val '' B)) := by
  have hW : MeasurableSet (Subtype.val '' B) :=
    (V.measurableEmbedding_regular S).measurableSet_image.mpr hB
  rw [regularShellMeasure, (V.measurableEmbedding_regular S).comap_apply,
    ← lintegral_indicator_one hW,
    V.lintegral_quotientShellMeasure_eq_branches S E (measurable_one.indicator hW)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_bool]
  have hU := V.measurableSet_allowedPositions e E
  have key : ∀ b : Bool, ∫⁻ q in V.allowedPositions e E,
      V.timeDensity e E q * (Subtype.val '' B).indicator 1
        (graphClass V S (e, q, boolSign b * V.speedAt e E q)) =
      (volume.withDensity (V.timeDensity e E))
        (V.allowedPositions e E ∩ V.branchClass S e E b ⁻¹' (Subtype.val '' B)) := by
    intro b
    have hpre : MeasurableSet (V.branchClass S e E b ⁻¹' (Subtype.val '' B)) :=
      V.measurable_branchClass S e E b hW
    rw [withDensity_apply _ (hU.inter hpre), inter_comm, ← Measure.restrict_restrict hpre,
      ← lintegral_indicator hpre]
    refine setLIntegral_congr_fun hU fun q hq => ?_
    rw [← V.branchClass_of_mem S e E b (V.allowedPositions_subset e E hq)]
    by_cases h : V.branchClass S e E b q ∈ Subtype.val '' B
    · rw [indicator_of_mem h, indicator_of_mem (show q ∈ V.branchClass S e E b ⁻¹'
        (Subtype.val '' B) from h)]
      simp
    · rw [indicator_of_notMem h, indicator_of_notMem (show q ∉ V.branchClass S e E b ⁻¹'
        (Subtype.val '' B) from h)]
      simp
  rw [← key true, ← key false]
  simp

/-! ### One branch piece -/

section Pieces

variable [Nonempty Γ.Edge]

/-- The data of the branch traversed by the flow from a point `z` of the section, with far end
`β` and traversal time `τ` (the conclusion of `exists_isBranchPiece`). -/
def IsBranchPiece (E : ℝ) (z : RegularScatteringPhaseSpace (V := V) S) (β τ : ℝ) : Prop :=
  0 < τ ∧ flow V S z τ ∈ V.branchSection S E ∧
    β ∈ Icc 0 (Γ.length (V.repEdge S z)) ∧
    0 < boolSign (V.sectionDir S z) * (β - V.repPos S z) ∧
    (β ∉ Ioo 0 (Γ.length (V.repEdge S z)) ∨ V.extension (V.repEdge S z) β = E) ∧
    uIoo (V.repPos S z) β ⊆ Ioo 0 (Γ.length (V.repEdge S z)) ∧
    (∀ u ∈ Ioo 0 τ, ∃ q ∈ uIoo (V.repPos S z) β,
      V.sheetTime (V.repEdge S z) E (V.repPos S z) (boolSign (V.sectionDir S z)) q = u) ∧
    (∀ q ∈ uIoo (V.repPos S z) β,
      V.sheetTime (V.repEdge S z) E (V.repPos S z) (boolSign (V.sectionDir S z)) q ∈
        Ioo 0 τ ∧ q ∈ V.allowedPositions (V.repEdge S z) E ∧
      (flow V S z
        (V.sheetTime (V.repEdge S z) E (V.repPos S z) (boolSign (V.sectionDir S z)) q)).1 =
        graphClass V S (V.repEdge S z, q,
          boolSign (V.sectionDir S z) * V.speedAt (V.repEdge S z) E q))

theorem exists_isBranchPiece' {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) {z : RegularScatteringPhaseSpace (V := V) S}
    (hz : z ∈ V.branchSection S E) : ∃ β τ, V.IsBranchPiece S E z β τ :=
  V.exists_isBranchPiece S hE hreg hz

/-- Strictly inside its traversal time the flow from a point of the section is off the section. -/
theorem flow_notMem_branchSection {E : ℝ} {z : RegularScatteringPhaseSpace (V := V) S}
    {β τ : ℝ} (h : V.IsBranchPiece S E z β τ) {u : ℝ} (hu : u ∈ Ioo 0 τ) :
    flow V S z u ∉ V.branchSection S E := by
  obtain ⟨-, -, -, -, -, hsub, hsurj, hmap⟩ := h
  obtain ⟨q, hq, rfl⟩ := hsurj u hu
  obtain ⟨-, hqU, hcl⟩ := hmap q hq
  refine V.not_mem_branchSection_of_interior S (hsub hq) ?_ hcl.symm
  have hs := V.speedAt_pos (V.repEdge S z) hqU.2
  rcases boolSign_cases (V.sectionDir S z) with h | h <;> rw [h] <;> linarith

/-- **`|dt| = dq / |p|` on one branch.**  The Lebesgue measure of the times in `[0, τ)` at which
the flow from `z` is in `B` is the branch measure of the corresponding positions. -/
theorem volume_piece_eq {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) {z : RegularScatteringPhaseSpace (V := V) S}
    {β τ : ℝ} (h : V.IsBranchPiece S E z β τ)
    {B : Set (RegularScatteringPhaseSpace (V := V) S)} (hB : MeasurableSet B) :
    volume (Ico 0 τ ∩ (fun u => flow V S z u) ⁻¹' B) =
      (volume.withDensity (V.timeDensity (V.repEdge S z) E))
        (uIoo (V.repPos S z) β ∩
          V.branchClass S (V.repEdge S z) E (V.sectionDir S z) ⁻¹' (Subtype.val '' B)) := by
  obtain ⟨-, -, -, -, -, hsub, hsurj, hmap⟩ := h
  set e := V.repEdge S z with he
  set α := V.repPos S z with hα
  set b := V.sectionDir S z with hb
  set ε := boolSign b with hε
  set T := V.sheetTime e E α ε with hT
  have hW : MeasurableSet (Subtype.val '' B) :=
    (V.measurableEmbedding_regular S).measurableSet_image.mpr hB
  set s := uIoo α β ∩ V.branchClass S e E b ⁻¹' (Subtype.val '' B) with hs
  have hsm : MeasurableSet s := measurableSet_Ioo.inter (V.measurable_branchClass S e E b hW)
  have hIcc : ∀ q ∈ uIoo α β, q ∈ Icc 0 (Γ.length e) := fun q hq => Ioo_subset_Icc_self (hsub hq)
  -- the set of times is the image of the set of positions under the time coordinate
  have himage : Ioo 0 τ ∩ (fun u => flow V S z u) ⁻¹' B = T '' s := by
    ext u
    constructor
    · rintro ⟨hu, huB⟩
      obtain ⟨q, hq, rfl⟩ := hsurj u hu
      refine ⟨q, ⟨hq, ?_⟩, rfl⟩
      refine ⟨_, huB, ?_⟩
      rw [(hmap q hq).2.2, V.branchClass_of_mem S e E b (hIcc q hq)]
    · rintro ⟨q, ⟨hq, w, hwB, hw⟩, rfl⟩
      refine ⟨(hmap q hq).1, ?_⟩
      have : flow V S z (T q) = w := by
        apply Subtype.ext
        rw [(hmap q hq).2.2, hw, V.branchClass_of_mem S e E b (hIcc q hq)]
      change flow V S z (T q) ∈ B
      rw [this]; exact hwB
  have hinj : InjOn T s := by
    intro q₁ hq₁ q₂ hq₂ hTq
    have h1 := (hmap q₁ hq₁.1).2.2
    have h2 := (hmap q₂ hq₂.1).2.2
    rw [hTq] at h1
    have r1 := (V.rep_graphClass_interior S (hsub hq₁.1) h1.symm).2.1
    have r2 := (V.rep_graphClass_interior S (hsub hq₂.1) h2.symm).2.1
    exact r1.symm.trans r2
  have hint := V.intervalIntegrable_one_div_speedAt_edge hE hreg e
  have hαI : α ∈ Icc 0 (Γ.length e) := V.repPos_mem S z
  have hderiv : ∀ q ∈ s, HasDerivWithinAt T (ε * (1 / V.speedAt e E q)) s q := fun q hq =>
    (V.hasDerivAt_sheetTime e hint hαI (hIcc q hq.1) (hmap q hq.1).2.1.2).hasDerivWithinAt
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul hsm hderiv hinj (fun _ => (1 : ℝ≥0∞))
  rw [measure_congr ((Ioo_ae_eq_Ico (a := (0 : ℝ)) (b := τ)).symm.inter (EventuallyEq.refl _ _)),
    himage, ← setLIntegral_one, hcv, withDensity_apply _ hsm]
  refine setLIntegral_congr_fun hsm fun q _ => ?_
  rw [mul_one, abs_mul, abs_of_nonneg (one_div_nonneg.mpr (V.speedAt_nonneg e E q))]
  have : |ε| = 1 := by rcases boolSign_cases b with h | h <;> rw [hε, h] <;> norm_num
  rw [this, one_mul]
  rfl

end Pieces

/-! ### The start of the branch through an allowed position -/

/-- Going left from an allowed position `q`, either the whole segment `[0, q]` is allowed, or there
is a last point `α ∈ (0, q)` of the level `g = E`, after which `g < E`. -/
theorem exists_left_start {g : ℝ → ℝ} {L E q : ℝ} (hg : ContinuousOn g (Icc 0 L))
    (hq : q ∈ Ioo 0 L) (hgq : g q < E) (hg0 : g 0 ≠ E) :
    (∀ r ∈ Icc 0 q, g r < E) ∨ ∃ α ∈ Ioo 0 q, g α = E ∧ ∀ r ∈ Ioc α q, g r < E := by
  by_cases h : ∀ r ∈ Icc 0 q, g r < E
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨r₀, hr₀, hr₀E⟩ := h
  set A : Set ℝ := Icc 0 q ∩ g ⁻¹' Ici E with hA
  have hgq' : ContinuousOn g (Icc 0 q) := hg.mono (Icc_subset_Icc le_rfl hq.2.le)
  have hAcl : IsClosed A := hgq'.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hAne : A.Nonempty := ⟨r₀, hr₀, hr₀E⟩
  have hAbdd : BddAbove A := ⟨q, fun r hr => hr.1.2⟩
  set α := sSup A with hαdef
  have hαA : α ∈ A := hAcl.csSup_mem hAne hAbdd
  have hafter : ∀ r ∈ Ioc α q, g r < E := by
    intro r hr
    by_contra hge
    have hrA : r ∈ A := ⟨⟨le_trans hαA.1.1 hr.1.le, hr.2⟩, not_lt.mp hge⟩
    exact absurd (le_csSup hAbdd hrA) (not_le.mpr hr.1)
  have hαq : α < q := by
    rcases eq_or_lt_of_le hαA.1.2 with h | h
    · exfalso; have := hαA.2; rw [h] at this; exact absurd this (not_le.mpr hgq)
    · exact h
  have hαle : g α ≤ E := by
    have hcw : ContinuousWithinAt g (Ioo α q) α :=
      (hgq' α hαA.1).mono (fun r hr => ⟨le_trans hαA.1.1 hr.1.le, hr.2.le⟩)
    rw [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT hαq] at hcw
    refine le_of_tendsto hcw ?_
    filter_upwards [Ioo_mem_nhdsGT hαq] with r hr
    exact (hafter r ⟨hr.1, hr.2.le⟩).le
  have hαE : g α = E := le_antisymm hαle hαA.2
  have hα0 : 0 < α := by
    rcases eq_or_lt_of_le hαA.1.1 with h | h
    · exfalso; rw [← h] at hαE; exact hg0 hαE
    · exact h
  exact ⟨α, ⟨hα0, hαq⟩, hαE, hafter⟩

/-- Going right from an allowed position `q`: the mirror image of `exists_left_start`. -/
theorem exists_right_start {g : ℝ → ℝ} {L E q : ℝ} (hg : ContinuousOn g (Icc 0 L))
    (hq : q ∈ Ioo 0 L) (hgq : g q < E) (hgL : g L ≠ E) :
    (∀ r ∈ Icc q L, g r < E) ∨ ∃ α ∈ Ioo q L, g α = E ∧ ∀ r ∈ Ico q α, g r < E := by
  have hmaps : MapsTo (fun r => L - r) (Icc 0 L) (Icc 0 L) := by
    intro r hr
    simp only [mem_Icc] at hr ⊢
    constructor <;> linarith [hr.1, hr.2]
  have hg' : ContinuousOn (fun r => g (L - r)) (Icc 0 L) :=
    hg.comp (continuous_const.sub continuous_id).continuousOn hmaps
  have hq' : L - q ∈ Ioo 0 L := by
    simp only [mem_Ioo]; constructor <;> linarith [hq.1, hq.2]
  have hgq' : g (L - (L - q)) < E := by rw [sub_sub_cancel]; exact hgq
  have hg0' : g (L - 0) ≠ E := by rw [sub_zero]; exact hgL
  rcases exists_left_start (g := fun r => g (L - r)) hg' hq' hgq' hg0' with
    h | ⟨α', hα', hE, hafter⟩
  · left
    intro r hr
    have hr' : L - r ∈ Icc 0 (L - q) := by
      simp only [mem_Icc]; constructor <;> linarith [hr.1, hr.2]
    have := h (L - r) hr'
    simpa only [sub_sub_cancel] using this
  · right
    refine ⟨L - α', ?_, hE, ?_⟩
    · simp only [mem_Ioo]; constructor <;> linarith [hα'.1, hα'.2]
    · intro r hr
      have hr' : L - r ∈ Ioc α' (L - q) := by
        simp only [mem_Ioc]; constructor <;> linarith [hr.1, hr.2]
      have := hafter (L - r) hr'
      simpa only [sub_sub_cancel] using this

/-- A level point which is approached from the right by `f < E` has nonpositive slope. -/
theorem deriv_neg_of_right {f : ℝ → ℝ} {α E d : ℝ} (hd : HasDerivAt f d α) (hfα : f α = E)
    (hright : ∀ᶠ r in 𝓝[>] α, f r < E) (hd0 : d ≠ 0) : d < 0 := by
  by_contra hpos
  have hpos' : 0 < d := lt_of_le_of_ne (not_lt.mp hpos) (Ne.symm hd0)
  have hsl := hasDerivAt_iff_tendsto_slope.mp hd
  have hsl' := hsl.mono_left (nhdsWithin_mono α (fun r (hr : r ∈ Ioi α) => ne_of_gt hr))
  have hev := hsl'.eventually (lt_mem_nhds hpos')
  obtain ⟨r, hr1, hr2, hr3⟩ := (hev.and (hright.and self_mem_nhdsWithin)).exists
  rw [slope_def_field, hfα] at hr1
  have : 0 < r - α := sub_pos.mpr hr3
  have := (div_pos_iff_of_pos_right this).mp hr1
  linarith

/-- A level point which is approached from the left by `f < E` has nonnegative slope. -/
theorem deriv_pos_of_left {f : ℝ → ℝ} {α E d : ℝ} (hd : HasDerivAt f d α) (hfα : f α = E)
    (hleft : ∀ᶠ r in 𝓝[<] α, f r < E) (hd0 : d ≠ 0) : 0 < d := by
  by_contra hneg
  have hneg' : d < 0 := lt_of_le_of_ne (not_lt.mp hneg) hd0
  have hsl := hasDerivAt_iff_tendsto_slope.mp hd
  have hsl' := hsl.mono_left (nhdsWithin_mono α (fun r (hr : r ∈ Iio α) => ne_of_lt hr))
  have hev := hsl'.eventually (gt_mem_nhds hneg')
  obtain ⟨r, hr1, hr2, hr3⟩ := (hev.and (hleft.and self_mem_nhdsWithin)).exists
  rw [slope_def_field, hfα] at hr1
  have h1 : r - α < 0 := sub_neg.mpr hr3
  have h2 : 0 < f r - E := by
    by_contra h
    push Not at h
    have : 0 ≤ (f r - E) / (r - α) := div_nonneg_of_nonpos h h1.le
    linarith
  linarith

/-- The class of a branch start `(e, α, ε √(2(E - V_e(α))))` and its outgoing representative. -/
theorem exists_regular_start {E : ℝ} (hE : E ∉ V.exceptionalEnergies) (e : Γ.Edge) (b : Bool)
    {α : ℝ} (hα : α ∈ Icc 0 (Γ.length e)) (hVα : V.extension e α ≤ E)
    (hadm : α ∈ Ioo 0 (Γ.length e) ∨ boolSign b * V.speedAt e E α ≠ 0)
    (hnin : ¬ ((α = 0 ∧ boolSign b * V.speedAt e E α < 0) ∨
      (α = Γ.length e ∧ 0 < boolSign b * V.speedAt e E α))) :
    ∃ z : RegularScatteringPhaseSpace (V := V) S, quotientHamiltonian (V := V) S z.1 = E ∧
      V.repEdge S z = e ∧ V.repPos S z = α ∧ V.repMom S z = boolSign b * V.speedAt e E α := by
  have hy : Γ.AdmissiblePoint (e, α, boolSign b * V.speedAt e E α) := ⟨hα, hadm⟩
  have hH : V.hamiltonian e α (boolSign b * V.speedAt e E α) = E :=
    V.hamiltonian_speedAt e (by rcases boolSign_cases b with h | h <;> rw [h] <;> norm_num) hVα
  have hq : quotientHamiltonian (V := V) S (graphClass V S (e, α, boolSign b * V.speedAt e E α))
      = E := by
    rw [quotientHamiltonian_graphClass V S hy]; exact hH
  refine ⟨⟨graphClass V S (e, α, boolSign b * V.speedAt e E α), by
    change quotientHamiltonian (V := V) S _ ∉ V.exceptionalEnergies
    rw [hq]; exact hE⟩, hq, ?_⟩
  have hnin' :
      ¬ IsIncomingPoint (V := V) S (Γ.graphPoint (e, α, boolSign b * V.speedAt e E α)) := by
    rw [isIncomingPoint_graphPoint_iff V S hy]; exact hnin
  exact V.repEdge_eq_of_graphClass S hy hnin' rfl

/-- **Every allowed position lies on the branch from a point of the section.**  For an allowed
position `q` of `e` and a direction `b`, there is a point `z` of the section on `e`, with
direction `b`, behind `q`, such that every position from `z` up to `q` is allowed. -/
theorem exists_start {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) (e : Γ.Edge) (b : Bool) {q : ℝ}
    (hq : q ∈ V.allowedPositions e E) :
    ∃ z ∈ V.branchSection S E, V.repEdge S z = e ∧ V.sectionDir S z = b ∧
      0 < boolSign b * (q - V.repPos S z) ∧
      ∀ r, 0 < boolSign b * (r - V.repPos S z) → 0 ≤ boolSign b * (q - r) →
        V.extension e r < E := by
  have hℓ := Γ.length_pos e
  have hcont := V.extension_continuousOn_closedEdge e
  have hderiv : ∀ α ∈ Ioo 0 (Γ.length e), V.extension e α = E →
      HasDerivAt (V.extension e) (deriv (V.extension e) α) α ∧ deriv (V.extension e) α ≠ 0 :=
    fun α hα hαE => ⟨((V.extension_contDiffAt_of_mem
      (V.closedEdge_subset_domain e (Ioo_subset_Icc_self hα))).differentiableAt
      (by norm_num)).hasDerivAt, hreg e α hα hαE⟩
  cases b with
  | true =>
    rcases exists_left_start hcont hq.1 hq.2 (V.extension_zero_ne hE e) with
      hall | ⟨α, hα, hαE, haft⟩
    · -- departure from the left vertex
      have h0 : V.extension e 0 < E := hall 0 ⟨le_rfl, hq.1.1.le⟩
      have hs0 := V.speedAt_pos e h0
      obtain ⟨z, hzE, hze, hzα, hzp⟩ := V.exists_regular_start S hE e true
        ⟨le_rfl, hℓ.le⟩ h0.le (Or.inr (by simp; exact hs0.ne'))
        (by simp only [boolSign_true, one_mul]; rintro (⟨-, h⟩ | ⟨h, -⟩) <;> linarith)
      refine ⟨z, ⟨hzE, Or.inl (by rw [hzα, hze]; exact fun h => lt_irrefl _ h.1)⟩, hze, ?_, ?_, ?_⟩
      · rw [sectionDir, hzp, if_pos (by simp; exact hs0.ne')]; simp [hs0]
      · simp [hzα, hq.1.1]
      · intro r hr1 hr2
        simp only [boolSign_true, one_mul, hzα, sub_zero] at hr1 hr2
        exact hall r ⟨hr1.le, by linarith⟩
    · -- departure from a turning point on the left
      obtain ⟨hd, hd0⟩ := hderiv α ⟨hα.1, lt_trans hα.2 hq.1.2⟩ hαE
      have hneg : deriv (V.extension e) α < 0 := by
        refine deriv_neg_of_right hd hαE ?_ hd0
        filter_upwards [Ioo_mem_nhdsGT hα.2] with r hr
        exact haft r ⟨hr.1, hr.2.le⟩
      have hs : V.speedAt e E α = 0 := by
        unfold speedAt; rw [hαE, sub_self, mul_zero, Real.sqrt_zero]
      obtain ⟨z, hzE, hze, hzα, hzp⟩ := V.exists_regular_start S hE e true
        (Ioo_subset_Icc_self ⟨hα.1, lt_trans hα.2 hq.1.2⟩) hαE.le
        (Or.inl ⟨hα.1, lt_trans hα.2 hq.1.2⟩) (by rw [hs, mul_zero]; simp)
      rw [hs, mul_zero] at hzp
      refine ⟨z, ⟨hzE, Or.inr hzp⟩, hze, ?_, ?_, ?_⟩
      · rw [sectionDir, hzp, if_neg (not_not.mpr rfl), hze, hzα, force]
        simp [hneg]
      · simp [hzα, hα.2]
      · intro r hr1 hr2
        simp only [boolSign_true, one_mul, hzα] at hr1 hr2
        exact haft r ⟨by linarith, by linarith⟩
  | false =>
    rcases exists_right_start hcont hq.1 hq.2 (V.extension_length_ne hE e) with
      hall | ⟨α, hα, hαE, haft⟩
    · -- departure from the right vertex
      have hL : V.extension e (Γ.length e) < E := hall _ ⟨hq.1.2.le, le_rfl⟩
      have hsL := V.speedAt_pos e hL
      obtain ⟨z, hzE, hze, hzα, hzp⟩ := V.exists_regular_start S hE e false
        ⟨hℓ.le, le_rfl⟩ hL.le (Or.inr (by simp; exact hsL.ne'))
        (by simp only [boolSign_false, neg_one_mul]; rintro (⟨h, -⟩ | ⟨-, h⟩) <;> linarith)
      refine ⟨z, ⟨hzE, Or.inl (by rw [hzα, hze]; exact fun h => lt_irrefl _ h.2)⟩, hze, ?_, ?_, ?_⟩
      · rw [sectionDir, hzp, if_pos (by simp; exact hsL.ne')]; simp [hsL.le]
      · simp [hzα, hq.1.2]
      · intro r hr1 hr2
        simp only [boolSign_false, neg_one_mul, hzα] at hr1 hr2
        exact hall r ⟨by linarith, by linarith⟩
    · -- departure from a turning point on the right
      obtain ⟨hd, hd0⟩ := hderiv α ⟨lt_trans hq.1.1 hα.1, hα.2⟩ hαE
      have hpos : 0 < deriv (V.extension e) α := by
        refine deriv_pos_of_left hd hαE ?_ hd0
        filter_upwards [Ioo_mem_nhdsLT hα.1] with r hr
        exact haft r ⟨hr.1.le, hr.2⟩
      have hs : V.speedAt e E α = 0 := by
        unfold speedAt; rw [hαE, sub_self, mul_zero, Real.sqrt_zero]
      obtain ⟨z, hzE, hze, hzα, hzp⟩ := V.exists_regular_start S hE e false
        (Ioo_subset_Icc_self ⟨lt_trans hq.1.1 hα.1, hα.2⟩) hαE.le
        (Or.inl ⟨lt_trans hq.1.1 hα.1, hα.2⟩) (by rw [hs, mul_zero]; simp)
      rw [hs, mul_zero] at hzp
      refine ⟨z, ⟨hzE, Or.inr hzp⟩, hze, ?_, ?_, ?_⟩
      · rw [sectionDir, hzp, if_neg (not_not.mpr rfl), hze, hzα, force]
        simp [hpos.le]
      · simp [hzα, hα.1]
      · intro r hr1 hr2
        simp only [boolSign_false, neg_one_mul, hzα] at hr1 hr2
        exact haft r ⟨by linarith, by linarith⟩

/-! ### The tiling of the open branches -/

section Tiling

variable [Nonempty Γ.Edge]

/-- An allowed position reached from the start of a branch without leaving the allowed region is
on that branch. -/
theorem mem_piece_of_start {E : ℝ} {z : RegularScatteringPhaseSpace (V := V) S} {β τ : ℝ}
    (h : V.IsBranchPiece S E z β τ) {q : ℝ} (hq : q ∈ Ioo 0 (Γ.length (V.repEdge S z)))
    (hdir : 0 < boolSign (V.sectionDir S z) * (q - V.repPos S z))
    (hallowed : ∀ r, 0 < boolSign (V.sectionDir S z) * (r - V.repPos S z) →
      0 ≤ boolSign (V.sectionDir S z) * (q - r) → V.extension (V.repEdge S z) r < E) :
    q ∈ uIoo (V.repPos S z) β := by
  obtain ⟨-, -, hβI, hβdir, hβend, -⟩ := h
  have hα := V.repPos_mem S z
  have hε := boolSign_cases (V.sectionDir S z)
  have hqβ : 0 < boolSign (V.sectionDir S z) * (β - q) := by
    by_contra hle
    have hle' : 0 ≤ boolSign (V.sectionDir S z) * (q - β) := by
      have : boolSign (V.sectionDir S z) * (q - β) = -(boolSign (V.sectionDir S z) * (β - q)) := by
        ring
      rw [this]; linarith [not_lt.mp hle]
    have hVβ := hallowed β hβdir hle'
    have hβint : β ∈ Ioo 0 (Γ.length (V.repEdge S z)) := by
      rcases hε with h | h
      · rw [h] at hβdir hle'
        constructor <;> linarith [hα.1, hα.2, hq.1, hq.2, hβI.1, hβI.2]
      · rw [h] at hβdir hle'
        constructor <;> linarith [hα.1, hα.2, hq.1, hq.2, hβI.1, hβI.2]
    rcases hβend with h | h
    · exact h hβint
    · rw [h] at hVβ; exact lt_irrefl _ hVβ
  exact mem_uIoo_of_eps hε (by linarith) (by linarith)

/-- Two points of the section whose flows meet within their traversal times coincide. -/
theorem eq_of_flow_eq {E : ℝ} {z z' : RegularScatteringPhaseSpace (V := V) S} {β τ β' τ' : ℝ}
    (hz : z ∈ V.branchSection S E) (hz' : z' ∈ V.branchSection S E)
    (h : V.IsBranchPiece S E z β τ) (h' : V.IsBranchPiece S E z' β' τ')
    {u u' : ℝ} (hu : u ∈ Ico 0 τ) (hu' : u' ∈ Ico 0 τ') (heq : flow V S z u = flow V S z' u') :
    z = z' := by
  have key : ∀ {z z' : RegularScatteringPhaseSpace (V := V) S} {β τ β' τ' u u' : ℝ},
      z ∈ V.branchSection S E → V.IsBranchPiece S E z' β' τ' → u ∈ Ico 0 τ → u' ∈ Ico 0 τ' →
      flow V S z u = flow V S z' u' → u ≤ u' → z = z' := by
    intro z z' β τ β' τ' u u' hz h' hu hu' heq hle
    have hzeq : z = flow V S z' (u' - u) := by
      have h1 : flow V S (flow V S z u) (-u) = z := flow_flow_neg_self V S z u
      rw [heq, flow_flow] at h1
      rw [← h1, sub_eq_add_neg]
    rcases eq_or_lt_of_le hle with h0 | hlt
    · rw [hzeq, h0, sub_self, flow_zero]
    · exact absurd (hzeq ▸ hz) (V.flow_notMem_branchSection S h'
        ⟨by linarith, by linarith [hu.1, hu'.2]⟩)
  rcases le_total u u' with hle | hle
  · exact key (β := β) hz h' hu hu' heq hle
  · exact (key (β := β') hz' h hu' hu heq.symm hle).symm

end Tiling

/-! ### Measurability of points -/

theorem measurableSet_singleton_regular (z : RegularScatteringPhaseSpace (V := V) S) :
    MeasurableSet ({z} : Set (RegularScatteringPhaseSpace (V := V) S)) := by
  have hm : Measurable fun w : RegularScatteringPhaseSpace (V := V) S =>
      (((rep V S w.1).1.1, (rep V S w.1).1.2.1) : Γ.Edge × ℝ × ℝ) :=
    (V.measurable_repPair S).comp measurable_subtype_coe
  have hpt : MeasurableSet ({(((rep V S z.1).1.1, (rep V S z.1).1.2.1) : Γ.Edge × ℝ × ℝ)} :
      Set (Γ.Edge × ℝ × ℝ)) := by
    rw [show ({(((rep V S z.1).1.1, (rep V S z.1).1.2.1) : Γ.Edge × ℝ × ℝ)} :
        Set (Γ.Edge × ℝ × ℝ)) = {(rep V S z.1).1.1} ×ˢ ({(rep V S z.1).1.2.1.1} ×ˢ
          {(rep V S z.1).1.2.1.2}) by simp]
    exact (MeasurableSpace.measurableSet_top).prod
      ((measurableSet_singleton _).prod (measurableSet_singleton _))
  convert hm hpt using 1
  ext w
  simp only [mem_singleton_iff, mem_preimage]
  constructor
  · rintro rfl; rfl
  · intro h
    rw [Prod.ext_iff] at h
    have hrep : rep V S w.1 = rep V S z.1 := Subtype.ext (Γ.prequotient_ext h.1 h.2)
    apply Subtype.ext
    rw [← quotientMap_rep V S w.1, ← quotientMap_rep V S z.1, hrep]

theorem measurableSet_of_finite {A : Set (RegularScatteringPhaseSpace (V := V) S)}
    (hA : A.Finite) : MeasurableSet A := by
  haveI : MeasurableSingletonClass (RegularScatteringPhaseSpace (V := V) S) :=
    ⟨V.measurableSet_singleton_regular S⟩
  exact hA.measurableSet

/-! ### The time parametrization and the invariance of `ν_E` -/

section Main

variable [Nonempty Γ.Edge]

/-- For one edge and one momentum sign, the branches departing the points of the section tile the
open branch over `U_e(E)`, so their branch measures add up. -/
theorem sum_pieces_eq {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) {β τ : RegularScatteringPhaseSpace (V := V) S → ℝ}
    (hp : ∀ z ∈ V.branchSection S E, V.IsBranchPiece S E z (β z) (τ z))
    (Cf : Finset (RegularScatteringPhaseSpace (V := V) S))
    (hCf : ∀ z, z ∈ Cf ↔ z ∈ V.branchSection S E)
    (e : Γ.Edge) (b : Bool) {X : Set ℝ} (hX : MeasurableSet X) :
    ∑ z ∈ Cf.filter (fun z => V.repEdge S z = e ∧ V.sectionDir S z = b),
      (volume.withDensity (V.timeDensity e E)) (uIoo (V.repPos S z) (β z) ∩ X) =
      (volume.withDensity (V.timeDensity e E)) (V.allowedPositions e E ∩ X) := by
  classical
  set Cfe := Cf.filter (fun z => V.repEdge S z = e ∧ V.sectionDir S z = b) with hCfe
  have hdisj : (↑Cfe : Set (RegularScatteringPhaseSpace (V := V) S)).PairwiseDisjoint
      (fun z => uIoo (V.repPos S z) (β z) ∩ X) := by
    intro z hz z' hz' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro q ⟨hq, -⟩ ⟨hq', -⟩
    have hzC := (hCf z).mp (Finset.mem_filter.mp hz).1
    have hzC' := (hCf z').mp (Finset.mem_filter.mp hz').1
    obtain ⟨he, hb⟩ := (Finset.mem_filter.mp hz).2
    obtain ⟨he', hb'⟩ := (Finset.mem_filter.mp hz').2
    have hm := ((hp z hzC).2.2.2.2.2.2.2 q hq)
    have hm' := ((hp z' hzC').2.2.2.2.2.2.2 q hq')
    have heq : flow V S z (V.sheetTime (V.repEdge S z) E (V.repPos S z)
        (boolSign (V.sectionDir S z)) q) = flow V S z' (V.sheetTime (V.repEdge S z') E
        (V.repPos S z') (boolSign (V.sectionDir S z')) q) := by
      apply Subtype.ext
      rw [hm.2.2, hm'.2.2, he, hb, he', hb']
    exact hne (V.eq_of_flow_eq S hzC hzC' (hp z hzC) (hp z' hzC')
      ⟨hm.1.1.le, hm.1.2⟩ ⟨hm'.1.1.le, hm'.1.2⟩ heq)
  rw [← measure_biUnion_finset hdisj (fun z _ => measurableSet_Ioo.inter hX)]
  congr 1
  rw [← iUnion₂_inter]
  congr 1
  ext q
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨z, hz, hq⟩
    obtain ⟨he, -⟩ := (Finset.mem_filter.mp hz).2
    have hm := (hp z ((hCf z).mp (Finset.mem_filter.mp hz).1)).2.2.2.2.2.2.2 q hq
    rw [← he]; exact hm.2.1
  · intro hq
    obtain ⟨z, hzC, he, hb, hdir, hall⟩ := V.exists_start S hE hreg e b hq
    refine ⟨z, Finset.mem_filter.mpr ⟨(hCf z).mpr hzC, he, hb⟩, ?_⟩
    rw [← he] at hq hall
    rw [← hb] at hdir hall
    exact V.mem_piece_of_start S (hp z hzC) hq.1 hdir hall

/-- **The time parametrization of `ν_E`** (Proposition VII.1, `|dt| = dq / |p|`).  There are
traversal times `τ_z > 0` for the points `z` of the finite branch section, with `Φ_{τ_z} z` back
in the section and `Φ_u z` off the section for `0 < u < τ_z`, such that for every Borel set `B`
`ν_E(B) = ∑_z Leb {u ∈ [0, τ_z) : Φ_u z ∈ B}`. -/
theorem exists_branchSection_parametrization {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) :
    ∃ τ : RegularScatteringPhaseSpace (V := V) S → ℝ,
      (∀ z ∈ V.branchSection S E, 0 < τ z) ∧
      (∀ z ∈ V.branchSection S E, flow V S z (τ z) ∈ V.branchSection S E) ∧
      (∀ z ∈ V.branchSection S E, ∀ u ∈ Ioo 0 (τ z), flow V S z u ∉ V.branchSection S E) ∧
      ∀ B, MeasurableSet B → V.regularShellMeasure S E B =
        ∑ z ∈ (V.finite_branchSection S hE hreg).toFinset,
          volume (Ico 0 (τ z) ∩ (fun u => flow V S z u) ⁻¹' B) := by
  classical
  choose! β τ hp using fun z (hz : z ∈ V.branchSection S E) => V.exists_isBranchPiece' S hE hreg hz
  refine ⟨τ, fun z hz => (hp z hz).1, fun z hz => (hp z hz).2.1,
    fun z hz u hu => V.flow_notMem_branchSection S (hp z hz) hu, ?_⟩
  intro B hB
  set Cf := (V.finite_branchSection S hE hreg).toFinset with hCfdef
  have hCf : ∀ z, z ∈ Cf ↔ z ∈ V.branchSection S E := fun z => Set.Finite.mem_toFinset _
  have hW : MeasurableSet (Subtype.val '' B) :=
    (V.measurableEmbedding_regular S).measurableSet_image.mpr hB
  rw [V.regularShellMeasure_apply_branches S E hB,
    Finset.sum_congr rfl fun z hz => V.volume_piece_eq S hE hreg (hp z ((hCf z).mp hz)) hB]
  set F : RegularScatteringPhaseSpace (V := V) S → Γ.Edge → Bool → ℝ≥0∞ := fun z e b =>
    (volume.withDensity (V.timeDensity e E))
      (uIoo (V.repPos S z) (β z) ∩ V.branchClass S e E b ⁻¹' (Subtype.val '' B)) with hF
  have hsplit : ∀ z, F z (V.repEdge S z) (V.sectionDir S z) =
      ∑ e, ∑ b, if V.repEdge S z = e ∧ V.sectionDir S z = b then F z e b else 0 := by
    intro z
    rw [Finset.sum_eq_single (V.repEdge S z), Finset.sum_eq_single (V.sectionDir S z)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro e _ he; simp [Ne.symm he]
    · simp
  change ∑ e, ∑ b, _ = ∑ z ∈ Cf, F z (V.repEdge S z) (V.sectionDir S z)
  simp_rw [hsplit]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun (e : Γ.Edge) _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun (b : Bool) _ => ?_
  rw [← Finset.sum_filter]
  exact (V.sum_pieces_eq S hE hreg hp Cf hCf e b
    (V.measurable_branchClass S e E b hW)).symm

/-- **Proposition VII.1 (invariance).**  At an energy `E` which is not a vertex value and is a
regular value of every `V_e` on the open edge, `ν_E` is invariant under the scattered evolution:
`ν_E(Φ_t⁻¹ A) = ν_E(A)` for every Borel `A` and every `t ∈ ℝ`. -/
theorem regularShellMeasure_preimage_flow {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) (t : ℝ)
    {A : Set (RegularScatteringPhaseSpace (V := V) S)} (hA : MeasurableSet A) :
    V.regularShellMeasure S E ((fun z => flow V S z t) ⁻¹' A) = V.regularShellMeasure S E A := by
  classical
  obtain ⟨τ, hτ, hret, hfirst, hν⟩ := V.exists_branchSection_parametrization S hE hreg
  set Cf := (V.finite_branchSection S hE hreg).toFinset with hCfdef
  have hCf : ∀ z, z ∈ Cf ↔ z ∈ V.branchSection S E := fun z => Set.Finite.mem_toFinset _
  exact measure_preimage_eq_of_suspension (fun z t => flow V S z t) (flow_zero V S)
    (flow_flow V S) (V.measurable_flow S) (ι := {z // z ∈ Cf}) (fun i => i.1)
    (fun i => τ i.1) (fun i => hτ _ ((hCf _).mp i.2)) Subtype.val_injective
    (fun i => ⟨⟨_, (hCf _).mpr (hret _ ((hCf _).mp i.2))⟩, rfl⟩)
    (fun i j u hu h => hfirst i.1 ((hCf _).mp i.2) u hu (h ▸ (hCf _).mp j.2))
    _ (fun B hB => by rw [hν B hB]; exact (Finset.sum_coe_sort Cf _).symm) t hA

/-- **Proposition VII.1 (invariance), as measure preservation.** -/
theorem measurePreserving_flow_regularShellMeasure_of_regular {E : ℝ}
    (hE : E ∉ V.exceptionalEnergies) (hreg : V.NoInteriorCriticalValue E) (t : ℝ) :
    MeasurePreserving (fun z => flow V S z t) (V.regularShellMeasure S E)
      (V.regularShellMeasure S E) :=
  ⟨V.measurable_flow S t, Measure.ext fun A hA => by
    rw [Measure.map_apply (V.measurable_flow S t) hA]
    exact V.regularShellMeasure_preimage_flow S hE hreg t hA⟩

end Main

end MechanicalPotential

end HamiltonianMetricGraphs
