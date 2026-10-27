/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.NoZenoExact
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Scattered trajectories on open intervals

The interval version of Definition V.2 uses the actual vertex-impact set from
Definition IV.4. The local edge lifts and the one-sided scattering limits imply
agreement with the global flow, without assuming a global extension of the curve.
This gives Lemmas V.3--V.5 on arbitrary open intervals. The global specialization
recovers Proposition V.6.
-/

namespace HamiltonianMetricGraphs

open Set Filter Topology

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-- Definition IV.4 on a time domain `J`: the preimage of the vertex section. -/
def vertexImpactSetOn (γ : ℝ → RegularScatteringPhaseSpace (V := V) S) (J : Set ℝ) : Set ℝ :=
  J ∩ vertexImpactSet V S γ

/-- The one-sided edge lifts in Definition V.2 at an impact inside `J`. -/
def IsScatteringImpactOn (γ : ℝ → RegularScatteringPhaseSpace (V := V) S)
    (J : Set ℝ) (t : ℝ) : Prop :=
  ∃ (v : Γ.Vertex) (α : Γ.IncomingBoundary v) (ε : ℝ), 0 < ε ∧
    Ioo (t - ε) (t + ε) ⊆ J ∧
    (γ t).1 = quotientMap (V := V) S (α.1.toNonzeroPrequotientPhase Γ) ∧
    (γ t).1 = quotientMap (V := V) S ((S.map v α).1.toNonzeroPrequotientPhase Γ) ∧
    ∃ cLeft cRight : ℝ → ℝ × ℝ,
      IsEdgeLift V S γ (Ioo (t - ε) t) α.1.germ.1 cLeft ∧
      IsEdgeLift V S γ (Ioo t (t + ε)) (S.map v α).1.germ.1 cRight ∧
      Tendsto cLeft (𝓝[<] t)
        (𝓝 (FiniteMetricGraph.EdgeEnd.coordinate Γ α.1.germ, α.1.momentum)) ∧
      Tendsto cRight (𝓝[>] t)
        (𝓝 (FiniteMetricGraph.EdgeEnd.coordinate Γ (S.map v α).1.germ,
          (S.map v α).1.momentum))

/-- Definition V.2. Values of the total function outside the open interval `J` are unused.
Local finiteness is required only on compact subsets of `J`. -/
structure IsScatteredTrajectoryOn (γ : ℝ → RegularScatteringPhaseSpace (V := V) S)
    (J : Set ℝ) : Prop where
  isOpen : IsOpen J
  isPreconnected : IsPreconnected J
  locallyFinite : ∀ K : Set ℝ, IsCompact K → K ⊆ J →
    (vertexImpactSetOn V S γ J ∩ K).Finite
  lift : ∀ t ∈ J \ vertexImpactSet V S γ, ∃ (e : Γ.Edge) (c : ℝ → ℝ × ℝ),
    IsEdgeLift V S γ (connectedComponentIn (J \ vertexImpactSet V S γ) t) e c
  impact : ∀ t ∈ vertexImpactSetOn V S γ J, IsScatteringImpactOn V S γ J t

/-- The complement of the impact set is relatively open in the time interval. -/
theorem IsScatteredTrajectoryOn.isOpen_without_impacts
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} {J : Set ℝ}
    (hγ : IsScatteredTrajectoryOn V S γ J) : IsOpen (J \ vertexImpactSet V S γ) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hγ.isOpen t ht.1
  have hKJ : Icc (t - δ / 2) (t + δ / 2) ⊆ J := by
    intro u hu
    apply hball
    rw [Real.ball_eq_Ioo]
    constructor <;> linarith [hu.1, hu.2]
  have hfin := hγ.locallyFinite _ isCompact_Icc hKJ
  have htF : t ∉ vertexImpactSetOn V S γ J ∩ Icc (t - δ / 2) (t + δ / 2) :=
    fun h => ht.2 h.1.2
  have hmem := hfin.isClosed.isOpen_compl.mem_nhds htF
  filter_upwards [hmem, Ioo_mem_nhds (show t - δ / 2 < t by linarith)
    (show t < t + δ / 2 by linarith)] with u hu huδ
  have huJ := hKJ (Ioo_subset_Icc_self huδ)
  exact ⟨huJ, fun huI => hu ⟨⟨huJ, huI⟩, Ioo_subset_Icc_self huδ⟩⟩

variable [Nonempty Γ.Edge]

/-- A trajectory on an interval follows the flow for a short time to the right. -/
theorem IsScatteredTrajectoryOn.right_flow
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} {J : Set ℝ}
    (hγ : IsScatteredTrajectoryOn V S γ J) {t : ℝ} (ht : t ∈ J) :
    ∃ ε > 0, ∀ h ∈ Ioo 0 ε, γ (t + h) = flow V S (γ t) h := by
  by_cases htI : t ∈ vertexImpactSet V S γ
  · obtain ⟨v, α, ε, hε, -, -, hαS, cLeft, cRight, -, hc, -, hlim⟩ := hγ.impact t ⟨ht, htI⟩
    refine ⟨ε, hε, fun h hh => Subtype.ext ?_⟩
    have hht : t + h ∈ Ioo t (t + ε) := ⟨by linarith [hh.1], by linarith [hh.2]⟩
    rw [(hc (t + h) hht).2.1]
    refine (flow_val_of_lift V S (γ t) (admissiblePoint_covector (S.map v α).1) ?_ ?_
      (hc.solution) hlim (by simpa using hh)).symm
    · rw [Γ.graphPoint_covector]
      exact scatteringStep_target_notIncoming (V := V) S ⟨v, α, rfl, rfl⟩
    · rw [hαS, graphClass_covector]
  · obtain ⟨e, c, hc⟩ := hγ.lift t ⟨ht, htI⟩
    have hUo := (hγ.isOpen_without_impacts V S).connectedComponentIn (x := t)
    have htU : t ∈ connectedComponentIn (J \ vertexImpactSet V S γ) t :=
      mem_connectedComponentIn ⟨ht, htI⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo t htU
    have hsub : Ioo (t - ε) (t + ε) ⊆ connectedComponentIn (J \ vertexImpactSet V S γ) t := by
      rw [← Real.ball_eq_Ioo]
      exact hball
    obtain ⟨hadm, hγt, hder⟩ := hc t htU
    have hint := hc.interior hUo htU
    have hsol : ∀ u ∈ Ioo t (t + ε), HasDerivAt c (V.edgeVectorField e (c u)) u ∧
        (c u).1 ∈ Ioo (0 : ℝ) (Γ.length e) := by
      intro u hu
      have huU := hsub ⟨by linarith [hu.1], hu.2⟩
      exact ⟨(hc u huU).2.2, hc.interior hUo huU⟩
    refine ⟨ε, hε, fun h hh => Subtype.ext ?_⟩
    have hht := hsub (show t + h ∈ Ioo (t - ε) (t + ε) by
      constructor <;> linarith [hh.1, hh.2])
    rw [(hc (t + h) hht).2.1]
    exact (flow_val_of_lift V S (γ t) hadm
      (not_isIncomingPoint_graphPoint_of_interior' V S hint) hγt hsol
      (hder.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (by simpa using hh)).symm

/-- A trajectory on an interval follows the flow for a short time to the left. -/
theorem IsScatteredTrajectoryOn.left_flow
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} {J : Set ℝ}
    (hγ : IsScatteredTrajectoryOn V S γ J) {t : ℝ} (ht : t ∈ J) :
    ∃ ε > 0, ∀ h ∈ Ioo 0 ε, γ t = flow V S (γ (t - h)) h := by
  by_cases htI : t ∈ vertexImpactSet V S γ
  · obtain ⟨v, α, ε, hε, -, hα, -, cLeft, cRight, hc, -, hlim, -⟩ := hγ.impact t ⟨ht, htI⟩
    refine ⟨ε, hε, fun h hh => Subtype.ext ?_⟩
    have hht : t - h ∈ Ioo (t - ε) t := ⟨by linarith [hh.2], by linarith [hh.1]⟩
    obtain ⟨hadm, hγth, hder⟩ := hc (t - h) hht
    have hint := hc.interior isOpen_Ioo hht
    have hsol : ∀ u ∈ Ioo (t - h) t, HasDerivAt cLeft (V.edgeVectorField α.1.germ.1 (cLeft u)) u ∧
        (cLeft u).1 ∈ Ioo (0 : ℝ) (Γ.length α.1.germ.1) := by
      intro u hu
      exact hc.solution u ⟨by linarith [hu.1, hh.2], hu.2⟩
    have hland := flow_val_of_lift_landing V S (γ (t - h)) hadm
      (not_isIncomingPoint_graphPoint_of_interior' V S hint) hγth
      (show t - h < t by linarith [hh.1]) hsol
      (hder.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (coordinate_not_mem_Ioo α.1.germ) hlim
    rw [show t - (t - h) = h by ring] at hland
    rw [hland, hα, graphClass_covector]
  · obtain ⟨e, c, hc⟩ := hγ.lift t ⟨ht, htI⟩
    have hUo := (hγ.isOpen_without_impacts V S).connectedComponentIn (x := t)
    have htU : t ∈ connectedComponentIn (J \ vertexImpactSet V S γ) t :=
      mem_connectedComponentIn ⟨ht, htI⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo t htU
    have hsub : Ioo (t - ε) (t + ε) ⊆ connectedComponentIn (J \ vertexImpactSet V S γ) t := by
      rw [← Real.ball_eq_Ioo]
      exact hball
    refine ⟨ε, hε, fun h hh => Subtype.ext ?_⟩
    have hht := hsub (show t - h ∈ Ioo (t - ε) (t + ε) by
      constructor <;> linarith [hh.1, hh.2])
    obtain ⟨hadm, hγth, hder⟩ := hc (t - h) hht
    have hint := hc.interior hUo hht
    have hsol : ∀ u ∈ Ioo (t - h) (t + ε), HasDerivAt c (V.edgeVectorField e (c u)) u ∧
        (c u).1 ∈ Ioo (0 : ℝ) (Γ.length e) := by
      intro u hu
      have huU := hsub ⟨by linarith [hu.1, hh.2], hu.2⟩
      exact ⟨(hc u huU).2.2, hc.interior hUo huU⟩
    have hval := flow_val_of_lift V S (γ (t - h)) hadm
      (not_isIncomingPoint_graphPoint_of_interior' V S hint) hγth hsol
      (hder.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (h := h) (by constructor <;> linarith [hh.1])
    rw [show t - h + h = t by ring] at hval
    rw [hval, (hc t htU).2.1]

/-- Local uniqueness on an interval, without assuming the curve extends globally. -/
theorem IsScatteredTrajectoryOn.eq_flow
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} {J : Set ℝ}
    (hγ : IsScatteredTrajectoryOn V S γ J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    γ t = flow V S (γ s) (t - s) := by
  let f : J → RegularScatteringPhaseSpace (V := V) S := fun u => flow V S (γ u) (-u)
  have hconst : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro u
    obtain ⟨ε₁, hε₁, hR⟩ := hγ.right_flow V S u.2
    obtain ⟨ε₂, hε₂, hL⟩ := hγ.left_flow V S u.2
    have hmem : ∀ᶠ v : J in 𝓝 u, (v : ℝ) ∈ Ioo (u - ε₂) (u + ε₁) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [hmem] with v hv
    dsimp [f]
    rcases lt_trichotomy (v : ℝ) (u : ℝ) with h | h | h
    · have h1 := hL (u - v) ⟨by linarith, by linarith [hv.1]⟩
      rw [show (u : ℝ) - (u - v) = v by ring] at h1
      rw [h1, flow_flow, show (u : ℝ) - v + -u = -v by ring]
    · rw [h]
    · have h1 := hR (v - u) ⟨by linarith, by linarith [hv.2]⟩
      rw [show (u : ℝ) + (v - u) = v by ring] at h1
      rw [h1, flow_flow, show (v : ℝ) - u + -v = -u by ring]
  letI : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp hγ.isPreconnected
  have h := congrArg (fun z => flow V S z t)
    (hconst.apply_eq_of_preconnectedSpace ⟨t, ht⟩ ⟨s, hs⟩)
  simpa [f, flow_flow, sub_eq_add_neg, add_comm] using h

/-- Lemma V.3 on an arbitrary open interval. -/
theorem quotientHamiltonian_isScatteredTrajectoryOn
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} {J : Set ℝ}
    (hγ : IsScatteredTrajectoryOn V S γ J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    quotientHamiltonian (V := V) S (γ t).1 = quotientHamiltonian (V := V) S (γ s).1 := by
  rw [hγ.eq_flow V S hs ht, quotientHamiltonian_flow]

/-- A uniform positive impact-separation constant for interval trajectories of energies in `K`. -/
def IsNoZenoConstantOn (K : Set ℝ) (τ : ℝ) : Prop :=
  0 < τ ∧ ∀ (γ : ℝ → RegularScatteringPhaseSpace (V := V) S) (J : Set ℝ),
    IsScatteredTrajectoryOn V S γ J →
    (∀ t ∈ J, quotientHamiltonian (V := V) S (γ t).1 ∈ K) →
    ∀ s ∈ vertexImpactSetOn V S γ J, ∀ t ∈ vertexImpactSetOn V S γ J,
      s ≠ t → τ ≤ |t - s|

/-- Lemma V.4 on arbitrary open intervals, with one constant for the entire energy window. -/
theorem no_zeno_on {K : Set ℝ} (hK : IsCompact K)
    (hKV : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ τ, IsNoZenoConstantOn V S K τ := by
  obtain ⟨τ, hτ⟩ := no_zeno V S hK hKV
  refine ⟨τ, hτ.1, fun γ J hγ henergy s hs t ht hne => ?_⟩
  have hs0 : (0 : ℝ) ∈ vertexImpactSet V S (flow V S (γ s)) := by
    simpa [vertexImpactSet, flow_zero] using hs.2
  have hts : t - s ∈ vertexImpactSet V S (flow V S (γ s)) := by
    change IsVertexImpactClass V S (flow V S (γ s) (t - s)).1
    rw [← hγ.eq_flow V S hs.1 ht.1]
    exact ht.2
  simpa using hτ.2 (γ s) (flow V S (γ s)) (flow_isScatteredTrajectory V S (γ s))
    (henergy s hs.1) 0 hs0 (t - s) hts (by intro h; apply hne; linarith)

omit [Nonempty Γ.Edge] in
/-- Lemma V.5 with the specified no-Zeno constant for the singleton energy window. -/
theorem impact_local_finiteness_on
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} {J : Set ℝ}
    (hγ : IsScatteredTrajectoryOn V S γ J) {E τ : ℝ}
    (henergy : ∀ t ∈ J, quotientHamiltonian (V := V) S (γ t).1 = E)
    (hτ : IsNoZenoConstantOn V S {E} τ) :
    (∀ u ∈ vertexImpactSetOn V S γ J, ∀ t ∈ vertexImpactSetOn V S γ J,
      u ≠ t → τ ≤ |t - u|) ∧
    ∀ a b : ℝ, a ≤ b → (vertexImpactSetOn V S γ J ∩ Icc a b).Finite ∧
      ((vertexImpactSetOn V S γ J ∩ Icc a b).ncard : ℝ) ≤ 1 + (b - a) / τ := by
  have hbound := hτ.2 γ J hγ (fun t ht => mem_singleton_iff.mpr (henergy t ht))
  refine ⟨hbound, fun a b hab => ncard_inter_Icc_le_of_separated hτ.1 ?_ hab⟩
  intro u hu t ht hut
  have h := hbound u hu t ht hut.ne
  rw [abs_of_pos (sub_pos.mpr hut)] at h
  linarith

/-- Lemma V.5 with a constant supplied by Lemma V.4 at any value of the trajectory. -/
theorem exists_impact_local_finiteness_on
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} {J : Set ℝ}
    (hγ : IsScatteredTrajectoryOn V S γ J) {s : ℝ} (hs : s ∈ J) :
    ∃ τ > 0,
      (∀ u ∈ vertexImpactSetOn V S γ J, ∀ t ∈ vertexImpactSetOn V S γ J,
        u ≠ t → τ ≤ |t - u|) ∧
      ∀ a b : ℝ, a ≤ b → (vertexImpactSetOn V S γ J ∩ Icc a b).Finite ∧
        ((vertexImpactSetOn V S γ J ∩ Icc a b).ncard : ℝ) ≤ 1 + (b - a) / τ := by
  obtain ⟨τ, hτ⟩ := no_zeno_on V S
    (K := {quotientHamiltonian (V := V) S (γ s).1}) isCompact_singleton
    (fun E hE => by rw [mem_singleton_iff.mp hE]; exact (γ s).2)
  exact ⟨τ, hτ.1, impact_local_finiteness_on V S hγ
    (fun t ht => quotientHamiltonian_isScatteredTrajectoryOn V S hγ hs ht) hτ⟩

omit [Nonempty Γ.Edge] in
/-- The auxiliary impact set in the original global definition is the actual vertex-impact set. -/
theorem IsScatteredTrajectoryWith.impactSet_eq
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S} {I : Set ℝ}
    (hγ : IsScatteredTrajectoryWith V S γ I) : I = vertexImpactSet V S γ := by
  apply Set.Subset.antisymm (subset_vertexImpactSet V S hγ)
  intro t ht
  by_contra htI
  obtain ⟨e, c, hc⟩ := hγ.lift t htI
  have hUo : IsOpen (connectedComponentIn Iᶜ t) :=
    (isClosed_of_finite_inter_isCompact hγ.locallyFinite).isOpen_compl.connectedComponentIn
  have htU : t ∈ connectedComponentIn Iᶜ t := mem_connectedComponentIn htI
  change IsVertexImpactClass V S (γ t).1 at ht
  rw [(hc t htU).2.1] at ht
  exact not_isVertexImpactClass_graphClass V S (hc.interior hUo htU) ht

omit [Nonempty Γ.Edge] in
/-- The existing global trajectory definition satisfies the interval definition on all of `ℝ`. -/
theorem IsScatteredTrajectory.on_univ {z : RegularScatteringPhaseSpace (V := V) S}
    {γ : ℝ → RegularScatteringPhaseSpace (V := V) S}
    (hγ : IsScatteredTrajectory V S z γ) : IsScatteredTrajectoryOn V S γ univ := by
  obtain ⟨-, I, hI⟩ := hγ
  have hEq := hI.impactSet_eq V S
  refine ⟨isOpen_univ, isPreconnected_univ, ?_, ?_, ?_⟩
  · intro K hK _
    simpa [vertexImpactSetOn, ← hEq] using hI.locallyFinite K hK
  · intro t ht
    have htI : t ∉ I := by simpa [hEq] using ht.2
    obtain ⟨e, c, hc⟩ := hI.lift t htI
    exact ⟨e, c, by simpa only [hEq, ← compl_eq_univ_sdiff] using hc⟩
  · intro t ht
    have htI : t ∈ I := by simpa [vertexImpactSetOn, ← hEq] using ht
    obtain ⟨ε, hε, hfree⟩ := exists_punctured_nhd_disjoint hI.locallyFinite t
    have hLdisj : Disjoint (Ioo (t - ε) t) I := Set.disjoint_left.mpr fun u hu =>
      hfree u ⟨hu.1, by linarith [hu.2]⟩ (ne_of_lt hu.2)
    have hRdisj : Disjoint (Ioo t (t + ε)) I := Set.disjoint_left.mpr fun u hu =>
      hfree u ⟨by linarith [hu.1], hu.2⟩ (ne_of_gt hu.1)
    obtain ⟨eL, cL, hcL⟩ := hI.exists_lift isPreconnected_Ioo hLdisj
      (show t - ε / 2 ∈ Ioo (t - ε) t from ⟨by linarith, by linarith⟩)
    obtain ⟨eR, cR, hcR⟩ := hI.exists_lift isPreconnected_Ioo hRdisj
      (show t + ε / 2 ∈ Ioo t (t + ε) from ⟨by linarith, by linarith⟩)
    obtain ⟨v, α, hα, hαS, hleft, hright⟩ := hI.impact t htI
    obtain ⟨heL, hlimL⟩ := hleft (t - ε) (by linarith) hLdisj eL cL hcL
    obtain ⟨heR, hlimR⟩ := hright (t + ε) (by linarith) hRdisj eR cR hcR
    subst eL
    subst eR
    exact ⟨v, α, ε, hε, subset_univ _, hα, hαS, cL, cR, hcL, hcR, hlimL, hlimR⟩

/-- Proposition V.6 for the interval definition specialized to the whole time axis. -/
theorem existsUnique_scatteredTrajectoryOn (z : RegularScatteringPhaseSpace (V := V) S) :
    ∃! γ : ℝ → RegularScatteringPhaseSpace (V := V) S,
      γ 0 = z ∧ IsScatteredTrajectoryOn V S γ univ := by
  refine ⟨flow V S z, ⟨flow_zero V S z, (flow_isScatteredTrajectory V S z).on_univ V S⟩, ?_⟩
  intro γ hγ
  funext t
  simpa [hγ.1] using hγ.2.eq_flow V S (show (0 : ℝ) ∈ univ from trivial)
    (show t ∈ univ from trivial)

end MechanicalPotential
end HamiltonianMetricGraphs
