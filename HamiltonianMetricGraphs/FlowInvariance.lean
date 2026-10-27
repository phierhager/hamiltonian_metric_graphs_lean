/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3: reduction of the Liouville invariance to the short-time one-impact case
-/

import HamiltonianMetricGraphs.LiouvilleChart

/-!
# Reducing the Liouville invariance to short times on one energy window

`LiouvilleChart.lean` reduces the invariance `m (Φ_t⁻¹ B) = m B` of Lemma VI.3 to a statement about
edgewise planar Lebesgue measure.  This module performs the *structural* half of the remaining
argument, leaving a single short-time statement.

The two ingredients are already available:

* **Energy conservation** (`quotientHamiltonian_flow`).  The energy sectors `{H ∈ C}` are invariant,
  so the invariance may be proved one sector at a time, and the regular sector is the disjoint union
  of countably many Borel sectors each contained in a *compact* regular energy window
  (`energyWindow`, `energySlab`).
* **The group law** (`flow_flow_of_nonneg`) together with the **uniform no-Zeno bound** of
  Lemma V.2 (`exists_uniform_impactDuration_lower_bound`).  On a compact regular window every
  outgoing flight lasts at least `τ > 0`, so for `0 < s < τ` every trajectory has *at most one*
  impact in `[0, s]`; and every `t > 0` is an integer multiple of such an `s`, so
  `Φ_t = Φ_s ∘ ⋯ ∘ Φ_s` reduces the general time to the short time (`preservesOn_of_lt`).

What is left is therefore exactly `ShortTimeInvariance`: on every compact regular energy window,
the invariance for all sufficiently short times (how short is left to the proof).  From it,
`measure_preimage_flow_of_shortTime` derives the full Lemma VI.3: all real times, all Borel sets.
-/

namespace HamiltonianMetricGraphs

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace MechanicalPotential

open PhysicalEdgeSegment

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-! ### Energy sectors -/

/-- The part of the regular quotient sector with energy in `C`. -/
def energySector (C : Set ℝ) : Set (RegularScatteringPhaseSpace (V := V) S) :=
  {z | quotientHamiltonian (V := V) S z.1 ∈ C}

theorem measurableSet_energySector {C : Set ℝ} (hC : MeasurableSet C) :
    MeasurableSet (V.energySector S C) :=
  ((measurable_quotientHamiltonian (V := V) S).comp measurable_subtype_coe) hC

theorem energySector_mono {C D : Set ℝ} (h : C ⊆ D) : V.energySector S C ⊆ V.energySector S D :=
  fun _ hz => h hz

/-- Every point of the regular sector has energy off the exceptional set. -/
theorem energySector_compl_exceptional :
    V.energySector S ((V.exceptionalEnergies : Set ℝ)ᶜ) = univ :=
  eq_univ_of_forall fun z => z.2

section Flow

variable [Nonempty Γ.Edge]

theorem flow_mem_energySector {C : Set ℝ} {z : RegularScatteringPhaseSpace (V := V) S}
    (hz : z ∈ V.energySector S C) (t : ℝ) : flow V S z t ∈ V.energySector S C := by
  change quotientHamiltonian (V := V) S (flow V S z t).1 ∈ C
  rw [quotientHamiltonian_flow]
  exact hz

/-! ### The invariance property on one energy sector -/

/-- `Φ_t` preserves the quotient Liouville measure of every Borel set of the energy sector `C`. -/
def PreservesOn (C : Set ℝ) (t : ℝ) : Prop :=
  ∀ B : Set (RegularScatteringPhaseSpace (V := V) S), MeasurableSet B → B ⊆ V.energySector S C →
    regularLiouville V S ((fun z => flow V S z t) ⁻¹' B) = regularLiouville V S B

theorem PreservesOn.mono {C D : Set ℝ} {t : ℝ} (h : C ⊆ D) (H : V.PreservesOn S D t) :
    V.PreservesOn S C t :=
  fun B hB hBC => H B hB (le_trans hBC (V.energySector_mono S h))

theorem preservesOn_zero (C : Set ℝ) : V.PreservesOn S C 0 := by
  intro B _ _
  have heq : (fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z 0) ⁻¹' B = B := by
    ext z
    simp only [mem_preimage, flow_zero]
  rw [heq]

/-- The preimage of an energy-sector set under the flow is again an energy-sector set. -/
theorem preimage_flow_subset_energySector {C : Set ℝ}
    {B : Set (RegularScatteringPhaseSpace (V := V) S)} (hBC : B ⊆ V.energySector S C) (t : ℝ) :
    (fun z => flow V S z t) ⁻¹' B ⊆ V.energySector S C := by
  intro z hz
  have h := hBC hz
  change quotientHamiltonian (V := V) S (flow V S z t).1 ∈ C at h
  rw [quotientHamiltonian_flow] at h
  exact h

/-- Invariance is additive in the time, on nonnegative times. -/
theorem PreservesOn.add {C : Set ℝ} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (Hs : V.PreservesOn S C s) (Ht : V.PreservesOn S C t) : V.PreservesOn S C (s + t) := by
  intro B hB hBC
  have heq : (fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z (s + t)) ⁻¹' B =
      (fun z => flow V S z s) ⁻¹' ((fun z => flow V S z t) ⁻¹' B) := by
    ext z
    simp only [mem_preimage]
    rw [← flow_flow_of_nonneg V S z hs ht]
  rw [heq, Hs _ ((V.measurable_flow S t) hB) (V.preimage_flow_subset_energySector S hBC t),
    Ht B hB hBC]

theorem preservesOn_natMul {C : Set ℝ} {s : ℝ} (hs : 0 ≤ s) (H : V.PreservesOn S C s) (n : ℕ) :
    V.PreservesOn S C ((n : ℝ) * s) := by
  induction n with
  | zero => simpa using V.preservesOn_zero S C
  | succ k ih =>
      have h := PreservesOn.add V S (s := (k : ℝ) * s) (t := s) (by positivity) hs ih H
      have hcast : ((k : ℝ) * s + s) = ((k + 1 : ℕ) : ℝ) * s := by push_cast; ring
      rwa [hcast] at h

/-- **Short times suffice.**  If the flow preserves the measure of the sector `C` for every time
below some positive `ε`, it preserves it for every nonnegative time: write `t = n · (t/n)` with
`t/n < ε` and compose. -/
theorem preservesOn_of_lt {C : Set ℝ} {ε : ℝ} (hε : 0 < ε)
    (H : ∀ s : ℝ, 0 < s → s < ε → V.PreservesOn S C s) :
    ∀ t : ℝ, 0 ≤ t → V.PreservesOn S C t := by
  intro t ht
  rcases eq_or_lt_of_le ht with h0 | hpos
  · rw [← h0]; exact V.preservesOn_zero S C
  obtain ⟨n, hn⟩ := exists_nat_gt (t / ε)
  have hn0 : 0 < (n : ℝ) := lt_of_le_of_lt (by positivity) hn
  have hslt : t / n < ε := by
    rw [div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hε] at hn
    linarith
  have hspos : 0 < t / n := by positivity
  have h := V.preservesOn_natMul S hspos.le (H (t / n) hspos hslt) n
  have hcast : ((n : ℝ) * (t / n)) = t := by field_simp
  rwa [hcast] at h

/-! ### A partition with piecewise invariance suffices -/

/-- **A partition on which the flow preserves measure gives the invariance.**  `Φ_t` is a Borel
*automorphism* of the regular sector (`flowMeasurableEquiv`), so the images of a countable
measurable partition form again a countable measurable partition.  If `Φ_t` preserves the measure
of every Borel subset of every piece, countable additivity on the two sides gives
`m (Φ_t⁻¹ B) = m B`.

This is what removes the need to identify the *image* strata: only a partition of the source and
the piecewise preservation are needed. -/
theorem measure_preimage_flow_of_partition (t : ℝ)
    {P : ℕ → Set (RegularScatteringPhaseSpace (V := V) S)}
    (hPmeas : ∀ n, MeasurableSet (P n))
    (hPdisj : Pairwise (Function.onFun Disjoint P))
    (hPcover : (⋃ n, P n) = univ)
    (hPpres : ∀ n, ∀ W, W ⊆ P n → MeasurableSet W →
      regularLiouville V S ((fun z => flow V S z t) '' W) = regularLiouville V S W)
    {B : Set (RegularScatteringPhaseSpace (V := V) S)} (hB : MeasurableSet B) :
    regularLiouville V S ((fun z => flow V S z t) ⁻¹' B) = regularLiouville V S B := by
  classical
  have hinj : Function.Injective (fun z => flow V S z t) :=
    (V.flowMeasurableEquiv S t).injective
  have hsurj : Function.Surjective (fun z => flow V S z t) :=
    (V.flowMeasurableEquiv S t).surjective
  have hBpre : MeasurableSet ((fun z => flow V S z t) ⁻¹' B) := (V.measurable_flow S t) hB
  -- the source decomposition
  have hsrc : (fun z => flow V S z t) ⁻¹' B = ⋃ n, (P n ∩ (fun z => flow V S z t) ⁻¹' B) := by
    rw [← iUnion_inter, hPcover, univ_inter]
  have hsrcmeas : ∀ n, MeasurableSet (P n ∩ (fun z => flow V S z t) ⁻¹' B) :=
    fun n => (hPmeas n).inter hBpre
  have hsrcdisj : Pairwise (Function.onFun Disjoint
      fun n => P n ∩ (fun z => flow V S z t) ⁻¹' B) :=
    fun m n hmn => Disjoint.mono inter_subset_left inter_subset_left (hPdisj hmn)
  -- the target decomposition
  have himgmeas : ∀ n, MeasurableSet ((fun z => flow V S z t) '' (P n) ∩ B) :=
    fun n => (V.measurableSet_image_flow S t (hPmeas n)).inter hB
  have himgdisj : Pairwise (Function.onFun Disjoint
      fun n => (fun z => flow V S z t) '' (P n) ∩ B) :=
    fun m n hmn => Disjoint.mono inter_subset_left inter_subset_left
      (Set.disjoint_image_of_injective hinj (hPdisj hmn))
  have himgcover : (⋃ n, ((fun z => flow V S z t) '' (P n) ∩ B)) = B := by
    rw [← iUnion_inter, ← image_iUnion, hPcover, image_univ,
      Function.Surjective.range_eq hsurj, univ_inter]
  -- the pieces have equal measure
  have hkey : ∀ n, regularLiouville V S (P n ∩ (fun z => flow V S z t) ⁻¹' B) =
      regularLiouville V S ((fun z => flow V S z t) '' (P n) ∩ B) := by
    intro n
    have himg : (fun z => flow V S z t) '' (P n ∩ (fun z => flow V S z t) ⁻¹' B) =
        (fun z => flow V S z t) '' (P n) ∩ B := by
      ext y
      constructor
      · rintro ⟨z, ⟨hzP, hzB⟩, rfl⟩
        exact ⟨⟨z, hzP, rfl⟩, hzB⟩
      · rintro ⟨⟨z, hzP, rfl⟩, hyB⟩
        exact ⟨z, ⟨hzP, hyB⟩, rfl⟩
    rw [← hPpres n _ inter_subset_left (hsrcmeas n), himg]
  rw [hsrc, measure_iUnion hsrcdisj hsrcmeas, tsum_congr hkey,
    ← measure_iUnion himgdisj himgmeas, himgcover]

/-- **A partition of one energy sector with piecewise invariance suffices.**  The argument of
`measure_preimage_flow_of_partition`, run inside the invariant energy sector `C`: only the sector
needs to be covered by the partition, and only Borel subsets of the sector are concerned. -/
theorem preservesOn_of_partition {C : Set ℝ} (t : ℝ)
    {P : ℕ → Set (RegularScatteringPhaseSpace (V := V) S)}
    (hPmeas : ∀ n, MeasurableSet (P n))
    (hPdisj : Pairwise (Function.onFun Disjoint P))
    (hPcover : V.energySector S C ⊆ ⋃ n, P n)
    (hPpres : ∀ n, ∀ W, W ⊆ P n → MeasurableSet W →
      regularLiouville V S ((fun z => flow V S z t) '' W) = regularLiouville V S W) :
    V.PreservesOn S C t := by
  classical
  intro B hB hBC
  have hinj : Function.Injective (fun z => flow V S z t) :=
    (V.flowMeasurableEquiv S t).injective
  have hBpre : MeasurableSet ((fun z => flow V S z t) ⁻¹' B) := (V.measurable_flow S t) hB
  have hpresub : (fun z => flow V S z t) ⁻¹' B ⊆ ⋃ n, P n :=
    le_trans (V.preimage_flow_subset_energySector S hBC t) hPcover
  -- the source decomposition
  have hsrc : (fun z => flow V S z t) ⁻¹' B = ⋃ n, (P n ∩ (fun z => flow V S z t) ⁻¹' B) := by
    rw [← iUnion_inter]
    exact (inter_eq_self_of_subset_right hpresub).symm
  have hsrcmeas : ∀ n, MeasurableSet (P n ∩ (fun z => flow V S z t) ⁻¹' B) :=
    fun n => (hPmeas n).inter hBpre
  have hsrcdisj : Pairwise (Function.onFun Disjoint
      fun n => P n ∩ (fun z => flow V S z t) ⁻¹' B) :=
    fun m n hmn => Disjoint.mono inter_subset_left inter_subset_left (hPdisj hmn)
  -- the target decomposition
  have himgmeas : ∀ n, MeasurableSet ((fun z => flow V S z t) '' (P n) ∩ B) :=
    fun n => (V.measurableSet_image_flow S t (hPmeas n)).inter hB
  have himgdisj : Pairwise (Function.onFun Disjoint
      fun n => (fun z => flow V S z t) '' (P n) ∩ B) :=
    fun m n hmn => Disjoint.mono inter_subset_left inter_subset_left
      (Set.disjoint_image_of_injective hinj (hPdisj hmn))
  have hsurj : Function.Surjective
      (fun z : RegularScatteringPhaseSpace (V := V) S => flow V S z t) :=
    (V.flowMeasurableEquiv S t).surjective
  have hBimg : B ⊆ (fun z => flow V S z t) '' (⋃ n, P n) := by
    intro y hy
    obtain ⟨z, hz⟩ := hsurj y
    have hzy : flow V S z t = y := hz
    have hzpre : z ∈ (fun z => flow V S z t) ⁻¹' B := by
      change flow V S z t ∈ B
      rw [hzy]
      exact hy
    exact ⟨z, hpresub hzpre, hz⟩
  have himgcover : (⋃ n, ((fun z => flow V S z t) '' (P n) ∩ B)) = B := by
    rw [← iUnion_inter, ← image_iUnion]
    exact inter_eq_self_of_subset_right hBimg
  -- the pieces have equal measure
  have hkey : ∀ n, regularLiouville V S (P n ∩ (fun z => flow V S z t) ⁻¹' B) =
      regularLiouville V S ((fun z => flow V S z t) '' (P n) ∩ B) := by
    intro n
    have himg : (fun z => flow V S z t) '' (P n ∩ (fun z => flow V S z t) ⁻¹' B) =
        (fun z => flow V S z t) '' (P n) ∩ B := by
      ext y
      constructor
      · rintro ⟨z, ⟨hzP, hzB⟩, rfl⟩
        exact ⟨⟨z, hzP, rfl⟩, hzB⟩
      · rintro ⟨⟨z, hzP, rfl⟩, hyB⟩
        exact ⟨z, ⟨hzP, hyB⟩, rfl⟩
    rw [← hPpres n _ inter_subset_left (hsrcmeas n), himg]
  rw [hsrc, measure_iUnion hsrcdisj hsrcmeas, tsum_congr hkey,
    ← measure_iUnion himgdisj himgmeas, himgcover]

/-! ### A countable exhaustion by compact regular energy windows -/

/-- The `n`-th compact energy window: the bounded energies at distance at least `1 / (n + 1)` from
every exceptional energy. -/
def energyWindow (n : ℕ) : Set ℝ :=
  Icc (-(n : ℝ)) (n : ℝ) \
    ⋃ c ∈ V.exceptionalEnergies, Ioo (c - 1 / (n + 1)) (c + 1 / (n + 1))

omit [Nonempty Γ.Edge] in
theorem isCompact_energyWindow (n : ℕ) : IsCompact (V.energyWindow n) := by
  refine isCompact_Icc.diff ?_
  exact isOpen_biUnion fun c _ => isOpen_Ioo

omit [Nonempty Γ.Edge] in
theorem regular_energyWindow (n : ℕ) : ∀ E ∈ V.energyWindow n, E ∉ V.exceptionalEnergies := by
  intro E hE hEex
  refine hE.2 (mem_biUnion hEex ?_)
  have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
  exact ⟨by linarith, by linarith⟩

omit [Nonempty Γ.Edge] in
theorem measurableSet_energyWindow (n : ℕ) : MeasurableSet (V.energyWindow n) :=
  (V.isCompact_energyWindow n).measurableSet

omit [Nonempty Γ.Edge] in
theorem iUnion_energyWindow :
    (⋃ n : ℕ, V.energyWindow n) = ((V.exceptionalEnergies : Set ℝ)ᶜ) := by
  refine subset_antisymm (fun E hE => ?_) (fun E hE => ?_)
  · obtain ⟨n, hn⟩ := mem_iUnion.mp hE
    exact V.regular_energyWindow n E hn
  · classical
    -- a positive distance to the (finite) exceptional set
    obtain ⟨d, hd0, hd⟩ : ∃ d : ℝ, 0 < d ∧ ∀ c ∈ V.exceptionalEnergies, d ≤ |E - c| := by
      rcases V.exceptionalEnergies.eq_empty_or_nonempty with hF | hF
      · exact ⟨1, one_pos, by simp [hF]⟩
      · refine ⟨V.exceptionalEnergies.inf' hF (fun c => |E - c|), ?_,
          fun c hc => Finset.inf'_le _ hc⟩
        rw [Finset.lt_inf'_iff]
        intro c hc
        refine abs_pos.mpr (sub_ne_zero.mpr ?_)
        intro heq
        exact hE (heq ▸ hc)
    obtain ⟨n, hn⟩ := exists_nat_gt (max |E| (1 / d))
    have hnE : |E| < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    have hnd : 1 / d < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (abs_nonneg E) hnE
    have hsmall : 1 / ((n : ℝ) + 1) < d := by
      rw [div_lt_iff₀ (by linarith)]
      rw [div_lt_iff₀ hd0] at hnd
      linarith
    refine mem_iUnion.mpr ⟨n, ⟨?_, ?_⟩, ?_⟩
    · exact (abs_le.mp hnE.le).1
    · exact (abs_le.mp hnE.le).2
    · intro hmem
      simp only [mem_iUnion, exists_prop] at hmem
      obtain ⟨c, hc, hcmem⟩ := hmem
      have h1 : |E - c| < 1 / ((n : ℝ) + 1) := by
        rw [abs_lt]
        exact ⟨by linarith [hcmem.1], by linarith [hcmem.2]⟩
      exact absurd (hd c hc) (not_le.mpr (lt_trans h1 hsmall))

/-- The disjointified windows: a countable Borel partition of the regular energies, each piece
inside a compact regular window. -/
def energySlab (n : ℕ) : Set ℝ := disjointed V.energyWindow n

omit [Nonempty Γ.Edge] in
theorem energySlab_subset (n : ℕ) : V.energySlab n ⊆ V.energyWindow n := disjointed_le _ n

omit [Nonempty Γ.Edge] in
theorem measurableSet_energySlab (n : ℕ) : MeasurableSet (V.energySlab n) :=
  MeasurableSet.disjointed V.measurableSet_energyWindow n

omit [Nonempty Γ.Edge] in
theorem pairwise_disjoint_energySlab :
    Pairwise (Function.onFun Disjoint V.energySlab) :=
  disjoint_disjointed _

omit [Nonempty Γ.Edge] in
theorem iUnion_energySlab :
    (⋃ n : ℕ, V.energySlab n) = ((V.exceptionalEnergies : Set ℝ)ᶜ) := by
  have h : (⋃ n : ℕ, V.energySlab n) = ⋃ n : ℕ, V.energyWindow n := iUnion_disjointed
  rw [h, V.iUnion_energyWindow]

/-! ### The reduction -/

/-- **The short-time invariance statement.**  On every compact regular energy window `K` there is a
positive time below which the flow preserves the quotient Liouville measure of the Borel sets of
the sector `{H ∈ K}`.  The threshold is left to the proof: it will be taken smaller than every
outgoing flight over `K` (so that every trajectory has at most one impact) and small enough that
the impact stratum fits inside the vertex tubes of `VertexTube.lean`. -/
def ShortTimeInvariance : Prop :=
  ∀ K : Set ℝ, IsCompact K → (∀ E ∈ K, E ∉ V.exceptionalEnergies) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → V.PreservesOn S K s

/-- On a compact regular energy window, `ShortTimeInvariance` gives the invariance for every
nonnegative time, by `preservesOn_of_lt`. -/
theorem preservesOn_window_of_shortTime (H : V.ShortTimeInvariance S) (K : Set ℝ)
    (hK : IsCompact K) (hKreg : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∀ t : ℝ, 0 ≤ t → V.PreservesOn S K t := by
  obtain ⟨ε, hε, H'⟩ := H K hK hKreg
  exact V.preservesOn_of_lt S hε H'

/-- **Lemma VI.3 from the short-time case.**  The energy sectors are invariant and the regular
sector is the disjoint union of countably many Borel sectors inside compact regular windows, so the
short-time invariance propagates to every Borel set and every real time (negative times by
`Φ_t⁻¹ = Φ_{-t}`). -/
theorem measure_preimage_flow_of_shortTime (H : V.ShortTimeInvariance S) (t : ℝ)
    {B : Set (RegularScatteringPhaseSpace (V := V) S)} (hB : MeasurableSet B) :
    regularLiouville V S ((fun z => flow V S z t) ⁻¹' B) = regularLiouville V S B := by
  classical
  -- first the nonnegative times
  have hnonneg : ∀ u : ℝ, 0 ≤ u → ∀ A : Set (RegularScatteringPhaseSpace (V := V) S),
      MeasurableSet A →
      regularLiouville V S ((fun z => flow V S z u) ⁻¹' A) = regularLiouville V S A := by
    intro u hu A hA
    set piece : ℕ → Set (RegularScatteringPhaseSpace (V := V) S) :=
      fun n => A ∩ V.energySector S (V.energySlab n) with hpiece
    have hpiecemeas : ∀ n, MeasurableSet (piece n) := fun n =>
      hA.inter (V.measurableSet_energySector S (V.measurableSet_energySlab n))
    have hpiecedisj : Pairwise (Function.onFun Disjoint piece) := by
      intro m n hmn
      refine Set.disjoint_left.mpr ?_
      rintro z ⟨-, hzm⟩ ⟨-, hzn⟩
      exact Set.disjoint_left.mp (V.pairwise_disjoint_energySlab hmn) hzm hzn
    have hcover : (⋃ n, piece n) = A := by
      refine subset_antisymm (iUnion_subset fun n => inter_subset_left) (fun z hz => ?_)
      have hEz : quotientHamiltonian (V := V) S z.1 ∈ ((V.exceptionalEnergies : Set ℝ)ᶜ) := z.2
      rw [← V.iUnion_energySlab] at hEz
      obtain ⟨n, hn⟩ := mem_iUnion.mp hEz
      exact mem_iUnion.mpr ⟨n, hz, hn⟩
    -- the preimage decomposes the same way
    have hprepiece : (fun z => flow V S z u) ⁻¹' A =
        ⋃ n, (fun z => flow V S z u) ⁻¹' piece n := by
      rw [← preimage_iUnion, hcover]
    have hpredisj : Pairwise (Function.onFun Disjoint
        fun n => (fun z => flow V S z u) ⁻¹' piece n) := by
      intro m n hmn
      exact Disjoint.preimage _ (hpiecedisj hmn)
    rw [hprepiece, measure_iUnion hpredisj
        (fun n => (V.measurable_flow S u) (hpiecemeas n)),
      ← hcover, measure_iUnion hpiecedisj hpiecemeas]
    refine tsum_congr fun n => ?_
    refine V.preservesOn_window_of_shortTime S H (V.energyWindow n)
      (V.isCompact_energyWindow n) (V.regular_energyWindow n) u hu (piece n) (hpiecemeas n) ?_
    intro z hz
    exact V.energySector_mono S (V.energySlab_subset n) hz.2
  rcases le_or_gt 0 t with ht | ht
  · exact hnonneg t ht B hB
  -- negative times: `Φ_t⁻¹ B = Φ_{-t} '' B` and `Φ_{-t}` preserves the measure
  have hneg : 0 ≤ -t := by linarith
  have himg : MeasurableSet ((fun z => flow V S z (-t)) '' B) :=
    V.measurableSet_image_flow S (-t) hB
  have hset : (fun z => flow V S z t) ⁻¹' B = (fun z => flow V S z (-t)) '' B := by
    ext z
    constructor
    · intro hz
      exact ⟨flow V S z t, hz, flow_flow_neg_self V S z t⟩
    · rintro ⟨w, hw, rfl⟩
      have h := flow_flow_neg_self V S w (-t)
      rw [neg_neg] at h
      rw [mem_preimage, h]
      exact hw
  rw [hset]
  have hinj : Function.Injective (fun z => flow V S z (-t)) :=
    (V.flowMeasurableEquiv S (-t)).injective
  have hpre : (fun z => flow V S z (-t)) ⁻¹' ((fun z => flow V S z (-t)) '' B) = B :=
    hinj.preimage_image B
  have h := hnonneg (-t) hneg _ himg
  rw [hpre] at h
  exact h.symm

end Flow

end MechanicalPotential

end HamiltonianMetricGraphs
