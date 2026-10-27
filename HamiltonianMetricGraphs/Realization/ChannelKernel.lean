/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ThinHypotheses

/-!
# Coarse-graining a deterministic microscopic junction

A full microscopic incoming state of a junction is a triple `(η, r, ξ)`: the projected graph
state `(η, r)` together with **unresolved data** `ξ` — everything the graph coordinates do not
see, namely the transverse displacement and momentum inside the tube (the arriving microscopic
state `(x, ξ)` determines its whole future through the flow `Φ^ε_t`).  The microscopic scattering
process is *deterministic*: it assigns to each such triple a definite outgoing channel

  `C_v(η, r, ξ) ∈ Γ.EdgeEnd`.

An observer who only measures the graph state must average over `ξ`.  Given a probability
measure `μ` on the unresolved data, the observed vertex law is the **channel kernel**

  `P_v(ζ ∣ η, r) = μ {ξ : C_v(η, r, ξ) = ζ}`.

This file contains the elementary but conceptually central statement of that coarse-graining:

* `channelKernel_of_ae_eq` / `channelKernel_dirac` — **one outgoing microscopic basin gives a
  deterministic graph law**: if `C_v(η,r,·) = F_v(η,r)` for `μ`-almost every `ξ`, then
  `P_v(· ∣ η, r) = δ_{F_v(η,r)}`;
* `channelKernel_ne_dirac` — **several outgoing basins give a genuinely stochastic law**: if two
  distinct germs are each attained on a set of positive measure, no Dirac mass can be the kernel;
* `exitGerms_eq_singleton` and `channel_eq_routeGerm` — the link to the microscopic hypothesis
  `HasDeterministicChannelReduction` of `ThinHypotheses.lean`: it says exactly that the exit set
  of every arriving state is the **singleton** `{F_v(η)}`, so the microscopic
  channel map is constant on the whole preparation class and the induced kernel is Dirac for
  *every* probability measure on the unresolved data.

Only the deterministic implication is developed; building the general stochastic vertex law into
a Markov-process theory on metric graphs is deliberately out of scope.  What is made precise here
is the dichotomy

  one outgoing basin  ⟹  deterministic graph law,
  several outgoing basins + unresolved data  ⟹  nontrivial stochastic channel kernel.
-/

namespace HamiltonianMetricGraphs

open Set MeasureTheory
open scoped ENNReal

/-! ### The channel kernel induced by a deterministic microscopic channel map -/

namespace ChannelKernel

variable {Γ : FiniteMetricGraph} {Ξ : Type*} [MeasurableSpace Ξ]

/-- **The channel kernel of a deterministic microscopic channel map.**  `C ξ` is the outgoing
channel selected by the microscopic scattering process on the unresolved datum `ξ`; the kernel
is the `μ`-probability that the observed outgoing channel is `ζ`. -/
noncomputable def channelKernel (μ : Measure Ξ) (C : Ξ → Γ.EdgeEnd) (ζ : Γ.EdgeEnd) : ℝ≥0∞ :=
  μ {ξ | C ξ = ζ}

theorem channelKernel_le_one (μ : Measure Ξ) [IsProbabilityMeasure μ] (C : Ξ → Γ.EdgeEnd)
    (ζ : Γ.EdgeEnd) : channelKernel μ C ζ ≤ 1 := by
  have h : μ {ξ | C ξ = ζ} ≤ μ univ := measure_mono (subset_univ _)
  rwa [measure_univ] at h

/-- The germ actually selected almost everywhere carries full kernel mass.  No measurability of
the fibres is needed: subadditivity suffices. -/
theorem channelKernel_self_eq_one (μ : Measure Ξ) [IsProbabilityMeasure μ] {C : Ξ → Γ.EdgeEnd}
    {ζ₀ : Γ.EdgeEnd} (h : ∀ᵐ ξ ∂μ, C ξ = ζ₀) : channelKernel μ C ζ₀ = 1 := by
  refine le_antisymm (channelKernel_le_one μ C ζ₀) ?_
  have hnull : μ {ξ | C ξ = ζ₀}ᶜ = 0 := by
    rw [ae_iff] at h
    exact h
  have hcover : (univ : Set Ξ) ⊆ {ξ | C ξ = ζ₀} ∪ {ξ | C ξ = ζ₀}ᶜ := by
    intro ξ _
    by_cases hξ : C ξ = ζ₀
    · exact Or.inl hξ
    · exact Or.inr hξ
  have hsub : (1 : ℝ≥0∞) ≤ μ {ξ | C ξ = ζ₀} + μ {ξ | C ξ = ζ₀}ᶜ := by
    calc (1 : ℝ≥0∞) = μ univ := (measure_univ (μ := μ)).symm
      _ ≤ μ ({ξ | C ξ = ζ₀} ∪ {ξ | C ξ = ζ₀}ᶜ) := measure_mono hcover
      _ ≤ μ {ξ | C ξ = ζ₀} + μ {ξ | C ξ = ζ₀}ᶜ := measure_union_le _ _
  rw [hnull, add_zero] at hsub
  exact hsub

/-- Every other germ has kernel mass zero. -/
theorem channelKernel_other_eq_zero (μ : Measure Ξ) {C : Ξ → Γ.EdgeEnd} {ζ₀ ζ : Γ.EdgeEnd}
    (h : ∀ᵐ ξ ∂μ, C ξ = ζ₀) (hne : ζ ≠ ζ₀) : channelKernel μ C ζ = 0 := by
  have hnull : μ {ξ | C ξ = ζ₀}ᶜ = 0 := by rw [ae_iff] at h; exact h
  refine measure_mono_null ?_ hnull
  intro ξ hξ
  simp only [mem_setOf_eq] at hξ
  intro hcon
  exact hne (hξ ▸ hcon)

/-- **Deterministic coarse-graining.**  If the deterministic microscopic channel map takes the
single value `ζ₀` for almost every unresolved datum, the induced vertex kernel is the degenerate
(Dirac) kernel at `ζ₀`: eliminating the unresolved variables produces a *deterministic* graph
scattering law. -/
theorem channelKernel_of_ae_eq (μ : Measure Ξ) [IsProbabilityMeasure μ] {C : Ξ → Γ.EdgeEnd}
    {ζ₀ : Γ.EdgeEnd} (h : ∀ᵐ ξ ∂μ, C ξ = ζ₀) (ζ : Γ.EdgeEnd) :
    channelKernel μ C ζ = if ζ = ζ₀ then 1 else 0 := by
  by_cases hζ : ζ = ζ₀
  · rw [if_pos hζ, hζ]
    exact channelKernel_self_eq_one μ h
  · rw [if_neg hζ]
    exact channelKernel_other_eq_zero μ h hζ

/-- The same statement written with Mathlib's Dirac measure: `P_v(· ∣ η,r) = δ_{ζ₀}`. -/
theorem channelKernel_dirac [MeasurableSpace Γ.EdgeEnd] [MeasurableSingletonClass Γ.EdgeEnd]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] {C : Ξ → Γ.EdgeEnd} {ζ₀ : Γ.EdgeEnd}
    (h : ∀ᵐ ξ ∂μ, C ξ = ζ₀) (ζ : Γ.EdgeEnd) :
    channelKernel μ C ζ = Measure.dirac ζ₀ {ζ} := by
  rw [channelKernel_of_ae_eq μ h ζ, Measure.dirac_apply, Set.indicator_apply]
  by_cases hζ : ζ = ζ₀
  · rw [if_pos hζ, if_pos (by rw [hζ]; exact rfl)]
    rfl
  · rw [if_neg hζ, if_neg]
    intro hcon
    exact hζ (by simpa [eq_comm] using hcon)

/-- A constant channel map is in particular almost everywhere constant. -/
theorem channelKernel_of_const (μ : Measure Ξ) [IsProbabilityMeasure μ] {C : Ξ → Γ.EdgeEnd}
    {ζ₀ : Γ.EdgeEnd} (h : ∀ ξ, C ξ = ζ₀) (ζ : Γ.EdgeEnd) :
    channelKernel μ C ζ = if ζ = ζ₀ then 1 else 0 :=
  channelKernel_of_ae_eq μ (Filter.Eventually.of_forall h) ζ

/-! ### Several basins: a genuinely stochastic kernel -/

/-- **Several outgoing basins give a nondegenerate kernel.**  If two *distinct* germs are each
attained on a set of positive `μ`-measure — i.e. the microscopic scattering process really does
send different unresolved data to different channels — then the induced vertex kernel is not a
Dirac mass at any germ: the coarse-grained graph law is genuinely stochastic. -/
theorem channelKernel_ne_dirac (μ : Measure Ξ) {C : Ξ → Γ.EdgeEnd} {ζ₁ ζ₂ : Γ.EdgeEnd}
    (hne : ζ₁ ≠ ζ₂) (h₁ : 0 < channelKernel μ C ζ₁) (h₂ : 0 < channelKernel μ C ζ₂)
    (ζ₀ : Γ.EdgeEnd) :
    ¬ ∀ ζ, channelKernel μ C ζ = if ζ = ζ₀ then 1 else 0 := by
  intro hdirac
  by_cases h : ζ₁ = ζ₀
  · have hz : ζ₂ ≠ ζ₀ := by rw [← h]; exact fun hc => hne hc.symm
    rw [hdirac ζ₂, if_neg hz] at h₂
    exact lt_irrefl 0 h₂
  · rw [hdirac ζ₁, if_neg h] at h₁
    exact lt_irrefl 0 h₁

/-- **The kernel is a probability kernel.**  With measurable fibres the masses of the finitely
many germs sum to one, so `P_v(· ∣ η, r)` really is a vertex scattering *distribution*. -/
theorem sum_channelKernel (μ : Measure Ξ) [IsProbabilityMeasure μ] (C : Ξ → Γ.EdgeEnd)
    (hmeas : ∀ ζ : Γ.EdgeEnd, MeasurableSet {ξ | C ξ = ζ}) :
    ∑ ζ : Γ.EdgeEnd, channelKernel μ C ζ = 1 := by
  classical
  have hdisj : Pairwise (Function.onFun Disjoint fun ζ : Γ.EdgeEnd => {ξ | C ξ = ζ}) := by
    intro ζ ζ' hζ
    refine Set.disjoint_left.mpr ?_
    intro ξ h1 h2
    exact hζ (by rw [← h1, ← h2] : ζ = ζ')
  have hcover : (univ : Set Ξ) = ⋃ ζ : Γ.EdgeEnd, {ξ | C ξ = ζ} := by
    ext ξ
    simp only [mem_univ, mem_iUnion, mem_setOf_eq, true_iff]
    exact ⟨C ξ, rfl⟩
  have h := measure_iUnion (μ := μ) hdisj hmeas
  rw [← hcover, measure_univ] at h
  have hfin : ∑' ζ : Γ.EdgeEnd, μ {ξ | C ξ = ζ} = ∑ ζ : Γ.EdgeEnd, μ {ξ | C ξ = ζ} :=
    tsum_fintype _
  rw [hfin] at h
  exact h.symm

end ChannelKernel

/-! ### The link with the microscopic hypothesis -/

namespace ThinHamiltonianNetwork

open ChannelKernel

variable {Γ : FiniteMetricGraph} (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ)
  (K : Set ℝ)

/-- **The exit set of a microscopic junction passage**: the germs through which the flow from the
state `(x, ξ)` is departing at some time of the junction window `(0, θ_ε]`.  This is the
microscopic scattering basin structure seen from the graph: the outgoing channel is deterministic
exactly when this set is a singleton. -/
def ExitGerms (ε : ℝ) (x p : ℝ × ℝ) : Set Γ.EdgeEnd :=
  {ζ | ∃ t ∈ Ioc 0 (N.dwell ε), N.Departing V K ε ζ (N.flow ε t (x, p)).1 (N.flow ε t (x, p)).2}

variable {N V K}

/-- **One outgoing basin.**  Deterministic channel reduction ((J) and (D)) says exactly that the
exit set of every state arriving at `η` is the singleton `{F_v(η)}`. -/
theorem exitGerms_eq_singleton {F : RoutingLaw Γ} {ε₀ : ℝ}
    (hdet : N.HasDeterministicChannelReduction V K F ε₀) {ε : ℝ} (hε : ε ∈ Set.Ioo 0 ε₀)
    {η : Γ.EdgeEnd} {x p : ℝ × ℝ} (harr : N.Arriving V K ε η x p) :
    N.ExitGerms V K ε x p = {F.routeGerm η} := by
  obtain ⟨b, hb⟩ := hdet.1 ε hε η x p harr
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · exact ⟨b, ⟨by simpa using hb.lt, by simpa using hb.le⟩, hb.depart⟩
  · rintro ζ ⟨t, ht, hdep⟩
    exact hdet.2 ε hε η x p harr t ht ζ hdep

open Classical in
/-- **The outgoing channel of the deterministic microscopic scattering process.**  It is defined
by choice from the exit set; the content of `HasDeterministicChannelReduction` is precisely that
the choice is forced, whatever the unresolved data. -/
noncomputable def channel (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (K : Set ℝ)
    (ε : ℝ) (x p : ℝ × ℝ) (dflt : Γ.EdgeEnd) : Γ.EdgeEnd :=
  if h : (N.ExitGerms V K ε x p).Nonempty then h.choose else dflt

/-- **The microscopic channel map is constant on the whole class of arriving states.**  Whatever
the unresolved data — the transverse displacement and momentum of the arriving state — the
microscopic scattering process selects `F_v(η)`. -/
theorem channel_eq_routeGerm {F : RoutingLaw Γ} {ε₀ : ℝ}
    (hdet : N.HasDeterministicChannelReduction V K F ε₀) {ε : ℝ} (hε : ε ∈ Set.Ioo 0 ε₀)
    {η : Γ.EdgeEnd} {x p : ℝ × ℝ} (harr : N.Arriving V K ε η x p) (dflt : Γ.EdgeEnd) :
    channel N V K ε x p dflt = F.routeGerm η := by
  classical
  have hset := exitGerms_eq_singleton hdet hε harr
  have hne : (N.ExitGerms V K ε x p).Nonempty := by
    rw [hset]; exact ⟨F.routeGerm η, rfl⟩
  rw [channel, dif_pos hne]
  exact (Set.eq_singleton_iff_unique_mem.mp hset).2 _ hne.choose_spec

/-! ### The induced vertex kernel of a deterministic junction -/

/-- **A microscopic incoming state at the junction of `η`.**  Besides the projected graph state
`(η, r)` — which is pinned down by `arriving` — it carries the *unresolved data*: the microscopic
state itself, hence its transverse displacement and momentum. -/
structure Incoming (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (K : Set ℝ)
    (ε₀ : ℝ) (η : Γ.EdgeEnd) where
  /-- the microscopic scale -/
  eps : ℝ
  eps_mem : eps ∈ Set.Ioo 0 ε₀
  /-- the microscopic configuration -/
  x : ℝ × ℝ
  /-- the microscopic momentum -/
  p : ℝ × ℝ
  arriving : N.Arriving V K eps η x p

/-- The outgoing channel as a function of the microscopic incoming state, i.e. of the
unresolved data. -/
noncomputable def Incoming.channel {ε₀ : ℝ} {η : Γ.EdgeEnd}
    (d : N.Incoming V K ε₀ η) : Γ.EdgeEnd :=
  ThinHamiltonianNetwork.channel N V K d.eps d.x d.p η

theorem Incoming.channel_eq {F : RoutingLaw Γ} {ε₀ : ℝ}
    (hdet : N.HasDeterministicChannelReduction V K F ε₀) {η : Γ.EdgeEnd}
    (d : N.Incoming V K ε₀ η) : d.channel = F.routeGerm η :=
  channel_eq_routeGerm hdet d.eps_mem d.arriving η

/-- **The vertex kernel of a deterministic microscopic junction is the Dirac kernel.**

For *every* probability measure `μ` on the unresolved microscopic data — no independence,
smoothness or equidistribution assumption is needed — eliminating that data from the
deterministic microscopic scattering process yields the degenerate kernel
`P_v(· ∣ η, r) = δ_{F_v(η)}`.  This is the precise sense in which a microscopic scattering basin
with a *unique* outgoing channel coarse-grains to a deterministic graph scattering law. -/
theorem channelKernel_of_deterministic {F : RoutingLaw Γ} {ε₀ : ℝ}
    (hdet : N.HasDeterministicChannelReduction V K F ε₀) {η : Γ.EdgeEnd}
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (data : Ξ → N.Incoming V K ε₀ η) (ζ : Γ.EdgeEnd) :
    ChannelKernel.channelKernel μ (fun ξ => (data ξ).channel) ζ =
      if ζ = F.routeGerm η then 1 else 0 :=
  ChannelKernel.channelKernel_of_const μ (fun ξ => (data ξ).channel_eq hdet) ζ

end ThinHamiltonianNetwork

end HamiltonianMetricGraphs
