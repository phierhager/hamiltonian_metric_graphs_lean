/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.BorelScattering
import HamiltonianMetricGraphs.EdgeDynamics

/-!
# Physical edge segments

This is the finite-time object ordered in the maximal-continuation construction.  Unlike an
`EdgeFirstHit`, it does not assert that its terminal point is an endpoint.  It records only a
concrete solution which remains in one physical edge, with an open-edge condition away from its
initial instant.  The next module will order compatible such segments by duration.
-/

namespace HamiltonianMetricGraphs

open Set Filter
open scoped Topology

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- A positive-time concrete Hamiltonian segment on one closed edge.  It starts either in the
open cylinder or at an outward-scattered boundary state, and is in the open cylinder immediately
after time zero. -/
structure PhysicalEdgeSegment (e : Γ.Edge) (x : ℝ × ℝ) where
  duration : ℝ
  duration_pos : 0 < duration
  curve : ℝ → ℝ × ℝ
  initial : curve 0 = x
  initial_physical : x.1 ∈ Icc (0 : ℝ) (Γ.length e)
  physical : ∀ t ∈ Icc (0 : ℝ) duration,
    (curve t).1 ∈ Icc (0 : ℝ) (Γ.length e)
  in_domain : ∀ t ∈ Icc (0 : ℝ) duration, (curve t).1 ∈ V.domain e
  integralCurve : ∀ t ∈ Icc (0 : ℝ) duration,
    HasDerivAt curve (V.edgeVectorField e (curve t)) t
  interior_after_initial : ∀ t ∈ Ioo (0 : ℝ) duration,
    (curve t).1 ∈ Ioo (0 : ℝ) (Γ.length e)

namespace PhysicalEdgeSegment

variable {V} {e : Γ.Edge} {x : ℝ × ℝ} (h : V.PhysicalEdgeSegment e x)

/-- Every point of a physical edge segment lies in the closed physical edge. -/
theorem physical_at (t : ℝ) (ht : t ∈ Icc (0 : ℝ) h.duration) :
    (h.curve t).1 ∈ Icc (0 : ℝ) (Γ.length e) := by
  exact h.physical t ht

/-- Energy is constant along a physical edge segment. -/
theorem hamiltonian_eq_initial_at (t : ℝ) (ht : t ∈ Icc (0 : ℝ) h.duration) :
    V.hamiltonian e (h.curve t).1 (h.curve t).2 = V.hamiltonian e x.1 x.2 := by
  have henergy := V.hamiltonian_eq_of_hamiltonEquations
    (q := fun s => (h.curve s).1) (p := fun s => (h.curve s).2)
    (a := 0) (b := h.duration)
    (fun s hs => h.in_domain s hs)
    (fun s hs => V.edgeIntegralCurve_hasDerivAt_fst (h.integralCurve s hs))
    (fun s hs => by
      simpa [force] using V.edgeIntegralCurve_hasDerivAt_snd (h.integralCurve s hs))
  simpa [h.initial] using henergy t ht

/-- A physical segment is continuous on its full certified time interval. -/
theorem continuousOn_curve : ContinuousOn h.curve (Icc (0 : ℝ) h.duration) :=
  fun t ht => (h.integralCurve t ht).continuousAt.continuousWithinAt

/-- The image of a finite physical segment is compact. This compactness is used to turn the
pointwise local Lipschitz estimates of the vector field into a finite continuation cover. -/
theorem isCompact_curve_image : IsCompact (h.curve '' Icc (0 : ℝ) h.duration) :=
  isCompact_Icc.image_of_continuousOn h.continuousOn_curve

/-- Two physical segments with the same initial state agree for their common duration.  The
proof first bounds both momenta by their common conserved energy, then applies the global
Lipschitz estimate on the resulting compact physical box. -/
theorem eqOn_common_duration (k : V.PhysicalEdgeSegment e x) :
    EqOn h.curve k.curve (Icc (0 : ℝ) (min h.duration k.duration)) := by
  obtain ⟨C, hC⟩ := V.exists_lowerBound_extension_closedEdge e
  let E : ℝ := V.hamiltonian e x.1 x.2
  let P : ℝ := Real.sqrt (2 * (E - C))
  obtain ⟨K, hK⟩ := V.exists_lipschitzOnWith_edgeVectorField_closedMomentumBox e P
  apply ODE_solution_unique_of_mem_Icc_right (v := fun _ => V.edgeVectorField e)
    (s := fun _ => closedEdgeMomentumBox e P) (K := K)
  · intro _ _
    exact hK
  · exact h.continuousOn_curve.mono (Icc_subset_Icc le_rfl (min_le_left _ _))
  · intro t ht
    exact (h.integralCurve t ⟨ht.1, le_trans ht.2.le (min_le_left _ _)⟩).hasDerivWithinAt
  · intro t ht
    apply V.mem_closedEdgeMomentumBox_of_hamiltonian_le
    · exact h.physical_at t ⟨ht.1, le_trans ht.2.le (min_le_left _ _)⟩
    · exact hC _ (h.physical_at t ⟨ht.1, le_trans ht.2.le (min_le_left _ _)⟩)
    · change V.hamiltonian e (h.curve t).1 (h.curve t).2 ≤ E
      exact (h.hamiltonian_eq_initial_at t
        ⟨ht.1, le_trans ht.2.le (min_le_left _ _)⟩).le
  · exact k.continuousOn_curve.mono (Icc_subset_Icc le_rfl (min_le_right _ _))
  · intro t ht
    exact (k.integralCurve t ⟨ht.1, le_trans ht.2.le (min_le_right _ _)⟩).hasDerivWithinAt
  · intro t ht
    apply V.mem_closedEdgeMomentumBox_of_hamiltonian_le
    · exact k.physical_at t ⟨ht.1, le_trans ht.2.le (min_le_right _ _)⟩
    · exact hC _ (k.physical_at t ⟨ht.1, le_trans ht.2.le (min_le_right _ _)⟩)
    · change V.hamiltonian e (k.curve t).1 (k.curve t).2 ≤ E
      exact (k.hamiltonian_eq_initial_at t
        ⟨ht.1, le_trans ht.2.le (min_le_right _ _)⟩).le
  · exact h.initial.trans k.initial.symm

/-- Restricting a physical segment to a shorter positive duration preserves all physical and ODE
invariants. This is the restriction operation used by the duration order in the maximal-flight
construction. -/
def restrict {T : ℝ} (hTpos : 0 < T) (hTle : T ≤ h.duration) :
    V.PhysicalEdgeSegment e x where
  duration := T
  duration_pos := hTpos
  curve := h.curve
  initial := h.initial
  initial_physical := h.initial_physical
  physical := fun t ht => h.physical t ⟨ht.1, le_trans ht.2 hTle⟩
  in_domain := fun t ht => h.in_domain t ⟨ht.1, le_trans ht.2 hTle⟩
  integralCurve := fun t ht => h.integralCurve t ⟨ht.1, le_trans ht.2 hTle⟩
  interior_after_initial := fun t ht =>
    h.interior_after_initial t ⟨ht.1, lt_of_lt_of_le ht.2 hTle⟩

@[simp] theorem restrict_duration {T : ℝ} (hTpos : 0 < T) (hTle : T ≤ h.duration) :
    (h.restrict hTpos hTle).duration = T := rfl

@[simp] theorem restrict_curve {T : ℝ} (hTpos : 0 < T) (hTle : T ≤ h.duration) :
    (h.restrict hTpos hTle).curve = h.curve := rfl

/-- Restart a physical segment at a strictly-earlier-than-terminal interior time `s`: the tail
`t ↦ curve (s + t)` is again a physical segment, now based at `curve s`.  This is the time-shift
building block for the flow semigroup. -/
def shiftFrom {s : ℝ} (hs0 : 0 ≤ s) (hs : s < h.duration) :
    V.PhysicalEdgeSegment e (h.curve s) where
  duration := h.duration - s
  duration_pos := by linarith
  curve := fun t => h.curve (s + t)
  initial := by simp
  initial_physical := h.physical_at s ⟨hs0, hs.le⟩
  physical := fun t ht => h.physical_at (s + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  in_domain := fun t ht => h.in_domain (s + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  integralCurve := fun t ht =>
    HasDerivAt.comp_const_add s t
      (h.integralCurve (s + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  interior_after_initial := fun t ht =>
    h.interior_after_initial (s + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩

@[simp] theorem shiftFrom_duration {s : ℝ} (hs0 : 0 ≤ s) (hs : s < h.duration) :
    (h.shiftFrom hs0 hs).duration = h.duration - s := rfl

@[simp] theorem shiftFrom_curve {s : ℝ} (hs0 : 0 ≤ s) (hs : s < h.duration) (t : ℝ) :
    (h.shiftFrom hs0 hs).curve t = h.curve (s + t) := rfl

/-- The time-shifted restart carries exactly the original conserved energy. -/
theorem shiftFrom_hamiltonian_eq {s : ℝ} (hs0 : 0 ≤ s) (hs : s < h.duration) :
    V.hamiltonian e (h.curve s).1 (h.curve s).2 = V.hamiltonian e x.1 x.2 :=
  h.hamiltonian_eq_initial_at s ⟨hs0, hs.le⟩

/-- `h` is an initial restriction of `k`: its duration is no later and both curves agree over
the whole closed time interval on which `h` is defined.  This intentionally forms a preorder,
not an equality of bundled segments, since their arbitrary values outside their certified
intervals are irrelevant. -/
def Extends (h k : V.PhysicalEdgeSegment e x) : Prop :=
  h.duration ≤ k.duration ∧ ∀ t ∈ Icc (0 : ℝ) h.duration, h.curve t = k.curve t

theorem extends_refl (h : V.PhysicalEdgeSegment e x) : h.Extends h :=
  ⟨le_rfl, fun _ _ => rfl⟩

theorem extends_trans {h k l : V.PhysicalEdgeSegment e x}
    (hk : h.Extends k) (kl : k.Extends l) : h.Extends l := by
  refine ⟨le_trans hk.1 kl.1, ?_⟩
  intro t ht
  exact (hk.2 t ht).trans (kl.2 t ⟨ht.1, le_trans ht.2 hk.1⟩)

/-- Deterministic Hamiltonian uniqueness makes the duration preorder total: any two physical
segments from the same state are restrictions of one another according to their durations. -/
theorem extends_or_extends (h k : V.PhysicalEdgeSegment e x) : h.Extends k ∨ k.Extends h := by
  rcases le_total h.duration k.duration with hle | hle
  · left
    refine ⟨hle, ?_⟩
    intro t ht
    have htm : t ∈ Icc (0 : ℝ) (min h.duration k.duration) := by
      simpa [min_eq_left hle] using ht
    exact h.eqOn_common_duration k htm
  · right
    refine ⟨hle, ?_⟩
    intro t ht
    have htm : t ∈ Icc (0 : ℝ) (min h.duration k.duration) := by
      simpa [min_eq_right hle] using ht
    exact (h.eqOn_common_duration k htm).symm

theorem restrict_extends (h : V.PhysicalEdgeSegment e x) {T : ℝ}
    (hTpos : 0 < T) (hTle : T ≤ h.duration) : (h.restrict hTpos hTle).Extends h :=
  ⟨hTle, fun _ _ => rfl⟩

/-- The set of all certified positive durations from a fixed edge state. -/
def durationSet (V : MechanicalPotential Γ) (e : Γ.Edge) (x : ℝ × ℝ) : Set ℝ :=
  {T | ∃ h : V.PhysicalEdgeSegment e x, h.duration = T}

theorem mem_durationSet (h : V.PhysicalEdgeSegment e x) : h.duration ∈ durationSet V e x :=
  ⟨h, rfl⟩

theorem durationSet_nonempty (h : V.PhysicalEdgeSegment e x) : (durationSet V e x).Nonempty :=
  ⟨h.duration, h.mem_durationSet⟩

/-- Every certified duration `d > s` from the initial state yields the certified duration `d - s`
from the time-`s` state.  This is the "shift" half of the duration-set correspondence used to
relate the flight past a time `s` to the flight of the restarted state. -/
theorem sub_mem_durationSet_of_mem (h : V.PhysicalEdgeSegment e x) {s : ℝ} (hs0 : 0 ≤ s)
    {d : ℝ} (hd : d ∈ durationSet V e x) (hsd : s < d) (hs : s < h.duration) :
    d - s ∈ durationSet V e (h.curve s) := by
  obtain ⟨k, hk⟩ := hd
  subst hk
  have hks : k.curve s = h.curve s :=
    k.eqOn_common_duration h ⟨hs0, le_of_lt (lt_min hsd hs)⟩
  rw [← hks]
  exact ⟨k.shiftFrom hs0 hsd, rfl⟩

/-- Prepend the initial `[0,s]` portion of `h` to a flight `k` starting at `h.curve s`.  The
result is a physical segment from `x` of duration `s + k.duration`; the two pieces glue with a
genuine two-sided derivative at `s` because both one-sided velocities equal the vector field at
`h.curve s = k.curve 0`.  This is the "prepend" half of the duration-set correspondence. -/
noncomputable def prependSegment (h : V.PhysicalEdgeSegment e x) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < h.duration) (k : V.PhysicalEdgeSegment e (h.curve s)) :
    V.PhysicalEdgeSegment e x where
  duration := s + k.duration
  duration_pos := by have := k.duration_pos; linarith
  curve := fun t => if t ≤ s then h.curve t else k.curve (t - s)
  initial := by simp only [if_pos hs0]; exact h.initial
  initial_physical := h.initial_physical
  physical := fun t ht => by
    by_cases htc : t ≤ s
    · simp only [if_pos htc]; exact h.physical_at t ⟨ht.1, le_trans htc hs.le⟩
    · push_neg at htc
      simp only [if_neg (not_le_of_gt htc)]
      exact k.physical_at (t - s) ⟨by linarith, by linarith [ht.2]⟩
  in_domain := fun t ht => by
    by_cases htc : t ≤ s
    · simp only [if_pos htc]; exact h.in_domain t ⟨ht.1, le_trans htc hs.le⟩
    · push_neg at htc
      simp only [if_neg (not_le_of_gt htc)]
      exact k.in_domain (t - s) ⟨by linarith, by linarith [ht.2]⟩
  integralCurve := fun t ht => by
    rcases lt_trichotomy t s with htlt | rfl | htgt
    · have hct : (if t ≤ s then h.curve t else k.curve (t - s)) = h.curve t := if_pos htlt.le
      rw [hct]
      have heq : (fun t => if t ≤ s then h.curve t else k.curve (t - s)) =ᶠ[𝓝 t] h.curve := by
        filter_upwards [Iio_mem_nhds htlt] with y hy
        exact if_pos (le_of_lt hy)
      exact (h.integralCurve t ⟨ht.1, le_trans htlt.le hs.le⟩).congr_of_eventuallyEq heq
    · have hks : k.curve 0 = h.curve t := k.initial
      have hcs : (if t ≤ t then h.curve t else k.curve (t - t)) = h.curve t := if_pos le_rfl
      rw [hcs]
      have hleft : HasDerivWithinAt (fun u => if u ≤ t then h.curve u else k.curve (u - t))
          (V.edgeVectorField e (h.curve t)) (Iic t) t := by
        apply (h.integralCurve t ⟨hs0, hs.le⟩).hasDerivWithinAt.congr_of_eventuallyEq
        · filter_upwards [self_mem_nhdsWithin] with y hy
          exact if_pos hy
        · exact if_pos le_rfl
      have hkderiv : HasDerivAt (fun u => k.curve (u - t))
          (V.edgeVectorField e (h.curve t)) t := by
        have h0 := k.integralCurve 0 ⟨le_rfl, k.duration_pos.le⟩
        rw [hks] at h0
        simpa using HasDerivAt.comp_sub_const t t (by simpa using h0)
      have hright : HasDerivWithinAt (fun u => if u ≤ t then h.curve u else k.curve (u - t))
          (V.edgeVectorField e (h.curve t)) (Ici t) t := by
        apply hkderiv.hasDerivWithinAt.congr_of_eventuallyEq
        · filter_upwards [self_mem_nhdsWithin] with y hy
          rcases eq_or_lt_of_le (Set.mem_Ici.mp hy) with rfl | hylt
          · simp [hks]
          · exact if_neg (not_le_of_gt hylt)
        · simp [hks]
      rw [← hasDerivWithinAt_univ, ← Iic_union_Ici]
      exact hleft.union hright
    · have hct : (if t ≤ s then h.curve t else k.curve (t - s)) = k.curve (t - s) :=
        if_neg (not_le_of_gt htgt)
      rw [hct]
      have hkderiv : HasDerivAt (fun t => k.curve (t - s))
          (V.edgeVectorField e (k.curve (t - s))) t := by
        have hk := k.integralCurve (t - s) ⟨by linarith, by linarith [ht.2]⟩
        simpa using HasDerivAt.comp_sub_const t s (by simpa using hk)
      have heq : (fun t => if t ≤ s then h.curve t else k.curve (t - s)) =ᶠ[𝓝 t]
          (fun t => k.curve (t - s)) := by
        filter_upwards [Ioi_mem_nhds htgt] with y hy
        exact if_neg (not_le_of_gt hy)
      exact hkderiv.congr_of_eventuallyEq heq
  interior_after_initial := fun t ht => by
    by_cases htc : t ≤ s
    · simp only [if_pos htc]
      exact h.interior_after_initial t ⟨ht.1, lt_of_le_of_lt htc hs⟩
    · push_neg at htc
      simp only [if_neg (not_le_of_gt htc)]
      exact k.interior_after_initial (t - s) ⟨by linarith, by linarith [ht.2]⟩

@[simp] theorem prependSegment_duration (h : V.PhysicalEdgeSegment e x) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < h.duration) (k : V.PhysicalEdgeSegment e (h.curve s)) :
    (h.prependSegment hs0 hs k).duration = s + k.duration := rfl

/-- The flight time from the initial state is at most `s` plus the flight time from the
time-`s` state.  This is the inequality obtained from the shift correspondence alone. -/
theorem sSup_durationSet_le_shift (h : V.PhysicalEdgeSegment e x) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < h.duration) (hmid : BddAbove (durationSet V e (h.curve s))) :
    sSup (durationSet V e x) ≤ s + sSup (durationSet V e (h.curve s)) := by
  have hmid0 : 0 ≤ sSup (durationSet V e (h.curve s)) :=
    le_trans (h.shiftFrom hs0 hs).duration_pos.le
      (le_csSup hmid (h.shiftFrom hs0 hs).mem_durationSet)
  apply csSup_le h.durationSet_nonempty
  intro d hd
  by_cases hsd : s < d
  · have hmem := h.sub_mem_durationSet_of_mem hs0 hd hsd hs
    have hle := le_csSup hmid hmem
    linarith
  · push_neg at hsd
    linarith

/-- The flight from the time-`s` state terminates exactly when the original flight does.  This is
what makes the restarted flight state have the same forward chain as the original. -/
theorem bddAbove_durationSet_curve_iff (h : V.PhysicalEdgeSegment e x) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < h.duration) :
    BddAbove (durationSet V e (h.curve s)) ↔ BddAbove (durationSet V e x) := by
  constructor
  · intro hmid
    have hmid0 : 0 ≤ sSup (durationSet V e (h.curve s)) :=
      le_trans (h.shiftFrom hs0 hs).duration_pos.le
        (le_csSup hmid (h.shiftFrom hs0 hs).mem_durationSet)
    refine ⟨s + sSup (durationSet V e (h.curve s)), ?_⟩
    rintro d ⟨seg, rfl⟩
    by_cases hsd : s < seg.duration
    · have hmem := h.sub_mem_durationSet_of_mem hs0 ⟨seg, rfl⟩ hsd hs
      have hle := le_csSup hmid hmem
      linarith
    · push_neg at hsd; linarith
  · intro hbdd
    refine ⟨sSup (durationSet V e x), ?_⟩
    rintro d ⟨k, rfl⟩
    have hmem : s + k.duration ∈ durationSet V e x := ⟨h.prependSegment hs0 hs k, rfl⟩
    have := le_csSup hbdd hmem
    have := k.duration_pos
    linarith

/-- The flight time from the time-`s` state is exactly the remaining flight time.  This exact
identity is the analytic heart of the flow semigroup: the restarted flight lasts precisely until
the same impact. -/
theorem sSup_durationSet_shift_eq (h : V.PhysicalEdgeSegment e x) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < h.duration) (hbdd : BddAbove (durationSet V e x)) :
    sSup (durationSet V e (h.curve s)) = sSup (durationSet V e x) - s := by
  have hmid : BddAbove (durationSet V e (h.curve s)) :=
    (h.bddAbove_durationSet_curve_iff hs0 hs).mpr hbdd
  have hmid_ne : (durationSet V e (h.curve s)).Nonempty :=
    ⟨_, (h.shiftFrom hs0 hs).mem_durationSet⟩
  have hle := h.sSup_durationSet_le_shift hs0 hs hmid
  have hge : sSup (durationSet V e (h.curve s)) ≤ sSup (durationSet V e x) - s := by
    apply csSup_le hmid_ne
    rintro d ⟨k, rfl⟩
    have hmem : s + k.duration ∈ durationSet V e x := ⟨h.prependSegment hs0 hs k, rfl⟩
    have := le_csSup hbdd hmem
    linarith
  linarith

/-- Transporting a segment along an equality of its base point leaves the duration unchanged. -/
theorem duration_cast {y y' : ℝ × ℝ} (hy : y = y') (seg : V.PhysicalEdgeSegment e y) :
    (hy ▸ seg).duration = seg.duration := by subst hy; rfl

/-- Transporting a segment along an equality of its base point leaves the curve unchanged. -/
theorem curve_cast {y y' : ℝ × ℝ} (hy : y = y') (seg : V.PhysicalEdgeSegment e y) (t : ℝ) :
    (hy ▸ seg).curve t = seg.curve t := by subst hy; rfl

/-- An unbounded duration set supplies a segment extending beyond every prescribed finite time. -/
theorem exists_segment_duration_gt_of_not_bddAbove (h : V.PhysicalEdgeSegment e x)
    (hub : ¬ BddAbove (durationSet V e x)) (t : ℝ) :
    ∃ k : V.PhysicalEdgeSegment e x, t < k.duration := by
  obtain ⟨T, hT, htT⟩ := (not_bddAbove_iff.mp hub) t
  rcases hT with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  simpa [hk] using htT

/-- Any time strictly below a finite upper supremum is covered by a strictly longer physical
segment. This is the selection principle for the canonical maximal curve. -/
theorem exists_segment_duration_gt_of_lt_sSup (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht : t < sSup (durationSet V e x)) :
    ∃ k : V.PhysicalEdgeSegment e x, t < k.duration := by
  obtain ⟨T, hT, htT⟩ := (lt_csSup_iff hbdd h.durationSet_nonempty).mp ht
  rcases hT with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  simpa [hk] using htT

/-- A chosen certified segment extending beyond a time below the finite duration supremum.  The
choice is harmless because `eqOn_common_duration` proves all such choices have the same value at
every already-covered nonnegative time. -/
noncomputable def segmentAt (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) (t : ℝ)
    (ht : t < sSup (durationSet V e x)) : V.PhysicalEdgeSegment e x :=
  Classical.choose (h.exists_segment_duration_gt_of_lt_sSup hbdd ht)

theorem lt_duration_segmentAt (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) (t : ℝ)
    (ht : t < sSup (durationSet V e x)) : t < (h.segmentAt hbdd t ht).duration :=
  Classical.choose_spec (h.exists_segment_duration_gt_of_lt_sSup hbdd ht)

/-- The chosen segment has the same value as every other segment which covers the time. -/
theorem segmentAt_curve_eq (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t < sSup (durationSet V e x))
    (k : V.PhysicalEdgeSegment e x) (hkt : t < k.duration) :
    (h.segmentAt hbdd t ht).curve t = k.curve t := by
  have htm : t ∈ Icc (0 : ℝ)
      (min (h.segmentAt hbdd t ht).duration k.duration) :=
    ⟨ht0, le_min (h.lt_duration_segmentAt hbdd t ht).le hkt.le⟩
  exact (h.segmentAt hbdd t ht).eqOn_common_duration k htm

/-- The canonical curve on the interval below the duration supremum. Values at and beyond the
supremum are deliberately left as the initial state; all later trajectory theorems use it only
on the certified interval. -/
noncomputable def maximalCurve (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) : ℝ → ℝ × ℝ := fun t =>
  if ht : t < sSup (durationSet V e x) then (h.segmentAt hbdd t ht).curve t else x

theorem maximalCurve_eq_segment_curve (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t < sSup (durationSet V e x))
    (k : V.PhysicalEdgeSegment e x) (hkt : t < k.duration) :
    h.maximalCurve hbdd t = k.curve t := by
  simp only [maximalCurve, dif_pos ht]
  exact h.segmentAt_curve_eq hbdd ht0 ht k hkt

/-- The canonical maximal curve of the restarted flight equals the time-shifted canonical maximal
curve of the original flight, throughout the (shifted) flight interval.  This is the curve half of
the semigroup correspondence, proved from segment uniqueness — no re-solved ODE is introduced. -/
theorem maximalCurve_shift_eq (h : V.PhysicalEdgeSegment e x) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < h.duration) (hbdd : BddAbove (durationSet V e x))
    (g : V.PhysicalEdgeSegment e (h.curve s)) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u < sSup (durationSet V e x) - s) :
    g.maximalCurve ((h.bddAbove_durationSet_curve_iff hs0 hs).mpr hbdd) u =
      h.maximalCurve hbdd (s + u) := by
  have hmid := (h.bddAbove_durationSet_curve_iff hs0 hs).mpr hbdd
  have hsupmid : sSup (durationSet V e (h.curve s)) = sSup (durationSet V e x) - s :=
    h.sSup_durationSet_shift_eq hs0 hs hbdd
  have hsu : s + u < sSup (durationSet V e x) := by linarith
  have hsu0 : 0 ≤ s + u := by linarith
  obtain ⟨K, hK⟩ := h.exists_segment_duration_gt_of_lt_sSup hbdd hsu
  rw [h.maximalCurve_eq_segment_curve hbdd hsu0 hsu K hK]
  have hsK : s < K.duration := by linarith [hK]
  have hKs : K.curve s = h.curve s := K.eqOn_common_duration h ⟨hs0, le_of_lt (lt_min hsK hs)⟩
  have hu' : u < sSup (durationSet V e (h.curve s)) := by rw [hsupmid]; exact hu
  have hk'u : u < (hKs ▸ (K.shiftFrom hs0 hsK)).duration := by
    rw [duration_cast]; show u < K.duration - s; linarith [hK]
  rw [g.maximalCurve_eq_segment_curve hmid hu0 hu' (hKs ▸ (K.shiftFrom hs0 hsK)) hk'u,
    curve_cast]
  show K.curve (s + u) = K.curve (s + u)
  rfl

/-- The canonical maximal curve depends only on the edge and initial state, not on the chosen
witnessing segment.  (Both `bddAbove` proofs are propositionally equal.) -/
theorem maximalCurve_indep (h h' : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < sSup (durationSet V e x)) :
    h.maximalCurve hbdd t = h'.maximalCurve hbdd t := by
  obtain ⟨k, hk⟩ := h.exists_segment_duration_gt_of_lt_sSup hbdd ht
  rw [h.maximalCurve_eq_segment_curve hbdd ht0 ht k hk,
    h'.maximalCurve_eq_segment_curve hbdd ht0 ht k hk]

/-- Transporting a segment along an equality of its base point leaves the maximal curve
unchanged. -/
theorem maximalCurve_cast {y y' : ℝ × ℝ} (hy : y = y') (seg : V.PhysicalEdgeSegment e y)
    (hb : BddAbove (durationSet V e y)) (hb' : BddAbove (durationSet V e y')) (t : ℝ) :
    (hy ▸ seg).maximalCurve hb' t = seg.maximalCurve hb t := by
  subst hy; rfl

/-- The canonical maximal curve of a flight restarted at the canonical point `maximalCurve h s`
(reached at time `s < sSup`, possibly beyond the initial segment's own duration) equals the
time-shifted canonical maximal curve.  This is the flow-friendly form of `maximalCurve_shift_eq`,
based at a genuine maximal-flight point rather than a fixed segment's curve. -/
theorem maximalCurve_restart_eq (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < sSup (durationSet V e x))
    (g : V.PhysicalEdgeSegment e (h.maximalCurve hbdd s))
    (hg_bdd : BddAbove (durationSet V e (h.maximalCurve hbdd s)))
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < sSup (durationSet V e x) - s) :
    g.maximalCurve hg_bdd t = h.maximalCurve hbdd (s + t) := by
  obtain ⟨K, hK⟩ := h.exists_segment_duration_gt_of_lt_sSup hbdd hs
  have hKs : h.maximalCurve hbdd s = K.curve s := h.maximalCurve_eq_segment_curve hbdd hs0 hs K hK
  have hsK : s < K.duration := hK
  have hb'' : BddAbove (durationSet V e (K.curve s)) := by rw [← hKs]; exact hg_bdd
  have hsu : s + t < sSup (durationSet V e x) := by linarith
  have hshift := K.maximalCurve_shift_eq hs0 hsK hbdd (hKs ▸ g) ht0 ht
  rw [← maximalCurve_cast hKs g hg_bdd hb'' t,
    Subsingleton.elim hb'' ((K.bddAbove_durationSet_curve_iff hs0 hsK).mpr hbdd), hshift]
  exact K.maximalCurve_indep h hbdd (by linarith) hsu

/-- The flight restarted at `maximalCurve h s` terminates iff the original does. -/
theorem bddAbove_durationSet_maximalCurve_iff (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < sSup (durationSet V e x)) :
    BddAbove (durationSet V e (h.maximalCurve hbdd s)) ↔ BddAbove (durationSet V e x) := by
  obtain ⟨K, hK⟩ := h.exists_segment_duration_gt_of_lt_sSup hbdd hs
  have hKs : h.maximalCurve hbdd s = K.curve s := h.maximalCurve_eq_segment_curve hbdd hs0 hs K hK
  rw [hKs]
  exact K.bddAbove_durationSet_curve_iff hs0 hK

/-- The flight restarted at `maximalCurve h s` lasts exactly the remaining time. -/
theorem sSup_durationSet_maximalCurve_eq (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < sSup (durationSet V e x)) :
    sSup (durationSet V e (h.maximalCurve hbdd s)) = sSup (durationSet V e x) - s := by
  obtain ⟨K, hK⟩ := h.exists_segment_duration_gt_of_lt_sSup hbdd hs
  have hKs : h.maximalCurve hbdd s = K.curve s := h.maximalCurve_eq_segment_curve hbdd hs0 hs K hK
  rw [hKs]
  exact K.sSup_durationSet_shift_eq hs0 hK hbdd

/-- The canonical curve in the unbounded-duration case.  It is defined at every nonnegative
time by a segment extending farther than that time; uniqueness on common intervals makes the
choice independent. -/
noncomputable def unboundedCurve (h : V.PhysicalEdgeSegment e x)
    (hub : ¬ BddAbove (durationSet V e x)) : ℝ → ℝ × ℝ := fun t =>
  if ht : 0 ≤ t then (Classical.choose (h.exists_segment_duration_gt_of_not_bddAbove hub t)).curve t
  else x

theorem unboundedCurve_eq_segment_curve (h : V.PhysicalEdgeSegment e x)
    (hub : ¬ BddAbove (durationSet V e x)) {t : ℝ} (ht0 : 0 ≤ t)
    (k : V.PhysicalEdgeSegment e x) (hkt : t < k.duration) :
    h.unboundedCurve hub t = k.curve t := by
  simp only [unboundedCurve, dif_pos ht0]
  let j : V.PhysicalEdgeSegment e x :=
    Classical.choose (h.exists_segment_duration_gt_of_not_bddAbove hub t)
  have hjt : t < j.duration :=
    Classical.choose_spec (h.exists_segment_duration_gt_of_not_bddAbove hub t)
  have htm : t ∈ Icc (0 : ℝ) (min j.duration k.duration) :=
    ⟨ht0, le_min hjt.le hkt.le⟩
  exact j.eqOn_common_duration k htm

/-- The unbounded no-hit curve depends only on the edge and initial state. -/
theorem unboundedCurve_indep (h h' : V.PhysicalEdgeSegment e x)
    (hub : ¬ BddAbove (durationSet V e x)) {t : ℝ} (ht0 : 0 ≤ t) :
    h.unboundedCurve hub t = h'.unboundedCurve hub t := by
  obtain ⟨k, hk⟩ := h.exists_segment_duration_gt_of_not_bddAbove hub t
  rw [h.unboundedCurve_eq_segment_curve hub ht0 k hk,
    h'.unboundedCurve_eq_segment_curve hub ht0 k hk]

theorem unboundedCurve_physical_at (h : V.PhysicalEdgeSegment e x)
    (hub : ¬ BddAbove (durationSet V e x)) {t : ℝ} (ht0 : 0 ≤ t) :
    (h.unboundedCurve hub t).1 ∈ Icc (0 : ℝ) (Γ.length e) := by
  obtain ⟨k, hkt⟩ := h.exists_segment_duration_gt_of_not_bddAbove hub t
  rw [h.unboundedCurve_eq_segment_curve hub ht0 k hkt]
  exact k.physical_at t ⟨ht0, hkt.le⟩

theorem unboundedCurve_initial (h : V.PhysicalEdgeSegment e x)
    (hub : ¬ BddAbove (durationSet V e x)) : h.unboundedCurve hub 0 = x := by
  obtain ⟨k, hk⟩ := h.exists_segment_duration_gt_of_not_bddAbove hub 0
  rw [h.unboundedCurve_eq_segment_curve hub le_rfl k hk]
  exact k.initial

theorem unboundedCurve_interior_at (h : V.PhysicalEdgeSegment e x)
    (hub : ¬ BddAbove (durationSet V e x)) {t : ℝ} (ht : 0 < t) :
    (h.unboundedCurve hub t).1 ∈ Ioo (0 : ℝ) (Γ.length e) := by
  obtain ⟨k, hkt⟩ := h.exists_segment_duration_gt_of_not_bddAbove hub t
  rw [h.unboundedCurve_eq_segment_curve hub ht.le k hkt]
  exact k.interior_after_initial t ⟨ht, hkt⟩

theorem unboundedCurve_hamiltonian_eq_initial (h : V.PhysicalEdgeSegment e x)
    (hub : ¬ BddAbove (durationSet V e x)) {t : ℝ} (ht0 : 0 ≤ t) :
    V.hamiltonian e (h.unboundedCurve hub t).1 (h.unboundedCurve hub t).2 =
      V.hamiltonian e x.1 x.2 := by
  obtain ⟨k, hkt⟩ := h.exists_segment_duration_gt_of_not_bddAbove hub t
  rw [h.unboundedCurve_eq_segment_curve hub ht0 k hkt]
  exact k.hamiltonian_eq_initial_at t ⟨ht0, hkt.le⟩

theorem unboundedCurve_hasDerivAt (h : V.PhysicalEdgeSegment e x)
    (hub : ¬ BddAbove (durationSet V e x)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (h.unboundedCurve hub)
      (V.edgeVectorField e (h.unboundedCurve hub t)) t := by
  obtain ⟨k, hkt⟩ := h.exists_segment_duration_gt_of_not_bddAbove hub (t + 1)
  have hkt' : t < k.duration := lt_trans (by linarith) hkt
  let r : ℝ := min (t / 2) ((k.duration - t) / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith) (by linarith)
  have heq : h.unboundedCurve hub =ᶠ[𝓝 t] k.curve := by
    filter_upwards [Metric.ball_mem_nhds t hr] with y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    have hy0 : 0 ≤ y := by
      dsimp [r] at hy
      linarith [min_le_left (t / 2) ((k.duration - t) / 2)]
    have hyk : y < k.duration := by
      dsimp [r] at hy
      linarith [min_le_right (t / 2) ((k.duration - t) / 2)]
    exact h.unboundedCurve_eq_segment_curve hub hy0 k hyk
  have hvalue := h.unboundedCurve_eq_segment_curve hub ht.le k hkt'
  rw [hvalue]
  exact (k.integralCurve t ⟨ht.le, hkt'.le⟩).congr_of_eventuallyEq heq

/-- Transporting a segment along an equality of its base point leaves the unbounded no-hit curve
unchanged.  The escape-flight analogue of `maximalCurve_cast`. -/
theorem unboundedCurve_cast {y y' : ℝ × ℝ} (hy : y = y') (seg : V.PhysicalEdgeSegment e y)
    (hb : ¬ BddAbove (durationSet V e y)) (hb' : ¬ BddAbove (durationSet V e y')) (t : ℝ) :
    (hy ▸ seg).unboundedCurve hb' t = seg.unboundedCurve hb t := by
  subst hy; rfl

/-- **An escape flight restarted along itself still escapes.**  Restarting a global no-hit flight
at any of its points gives a flight that again never reaches an endpoint, so the escape branch is
preserved by the flow.  This is the unbounded-duration counterpart of
`bddAbove_durationSet_maximalCurve_iff`. -/
theorem not_bddAbove_durationSet_unboundedCurve (h : V.PhysicalEdgeSegment e x)
    (hub : ¬ BddAbove (durationSet V e x)) {s : ℝ} (hs0 : 0 ≤ s) :
    ¬ BddAbove (durationSet V e (h.unboundedCurve hub s)) := by
  obtain ⟨K, hK⟩ := h.exists_segment_duration_gt_of_not_bddAbove hub s
  have hKs : h.unboundedCurve hub s = K.curve s := h.unboundedCurve_eq_segment_curve hub hs0 K hK
  rw [hKs]
  intro hbdd
  exact hub ((K.bddAbove_durationSet_curve_iff hs0 hK).mp hbdd)

/-- **The escape-flight restart identity.**  The global no-hit curve of a flight restarted at time
`s` is the original no-hit curve shifted by `s`.  This is the unbounded-duration counterpart of
`maximalCurve_restart_eq`, and it is what lets the flow semigroup pass through the escape flight of
a terminating chain.  No ODE is re-solved: a segment `K` outlasting `s + t` is shifted by
`shiftFrom`, and both sides are read off that one segment. -/
theorem unboundedCurve_restart_eq (h : V.PhysicalEdgeSegment e x)
    (hub : ¬ BddAbove (durationSet V e x)) {s : ℝ} (hs0 : 0 ≤ s)
    (g : V.PhysicalEdgeSegment e (h.unboundedCurve hub s))
    (hg_ub : ¬ BddAbove (durationSet V e (h.unboundedCurve hub s)))
    {t : ℝ} (ht0 : 0 ≤ t) :
    g.unboundedCurve hg_ub t = h.unboundedCurve hub (s + t) := by
  obtain ⟨K, hK⟩ := h.exists_segment_duration_gt_of_not_bddAbove hub (s + t)
  have hsK : s < K.duration := lt_of_le_of_lt (by linarith) hK
  have hKs : h.unboundedCurve hub s = K.curve s := h.unboundedCurve_eq_segment_curve hub hs0 K hsK
  have hb'' : ¬ BddAbove (durationSet V e (K.curve s)) := by rw [← hKs]; exact hg_ub
  rw [← unboundedCurve_cast hKs g hg_ub hb'' t]
  -- The shifted segment `K.shiftFrom` is based at `K.curve s` and outlasts `t`.
  have hshift : t < (K.shiftFrom hs0 hsK).duration := by
    show t < K.duration - s
    linarith
  have hLHS : (hKs ▸ g).unboundedCurve hb'' t = (K.shiftFrom hs0 hsK).curve t :=
    (hKs ▸ g).unboundedCurve_eq_segment_curve hb'' ht0 (K.shiftFrom hs0 hsK) hshift
  have hRHS : h.unboundedCurve hub (s + t) = K.curve (s + t) :=
    h.unboundedCurve_eq_segment_curve hub (by linarith) K hK
  rw [hLHS, hRHS]
  rfl

/-- The canonical curve remains on the closed physical edge before the duration supremum. -/
theorem maximalCurve_physical_at (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t < sSup (durationSet V e x)) :
    (h.maximalCurve hbdd t).1 ∈ Icc (0 : ℝ) (Γ.length e) := by
  let k := h.segmentAt hbdd t ht
  have hkt : t < k.duration := h.lt_duration_segmentAt hbdd t ht
  rw [h.maximalCurve_eq_segment_curve hbdd ht0 ht k hkt]
  exact k.physical_at t ⟨ht0, hkt.le⟩

/-- The canonical curve has the initial mechanical energy at every nonnegative time before the
duration supremum. -/
theorem maximalCurve_hamiltonian_eq_initial (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t < sSup (durationSet V e x)) :
    V.hamiltonian e (h.maximalCurve hbdd t).1 (h.maximalCurve hbdd t).2 =
      V.hamiltonian e x.1 x.2 := by
  let k := h.segmentAt hbdd t ht
  have hkt : t < k.duration := h.lt_duration_segmentAt hbdd t ht
  rw [h.maximalCurve_eq_segment_curve hbdd ht0 ht k hkt]
  exact k.hamiltonian_eq_initial_at t ⟨ht0, hkt.le⟩

/-- Before the duration supremum, every positive-time point of the canonical curve is in the
open cylinder: a longer chosen segment certifies this directly. -/
theorem maximalCurve_interior_at (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (sSup (durationSet V e x))) :
    (h.maximalCurve hbdd t).1 ∈ Ioo (0 : ℝ) (Γ.length e) := by
  let k := h.segmentAt hbdd t ht.2
  have hkt : t < k.duration := h.lt_duration_segmentAt hbdd t ht.2
  rw [h.maximalCurve_eq_segment_curve hbdd ht.1.le ht.2 k hkt]
  exact k.interior_after_initial t ⟨ht.1, hkt⟩

/-- Before a finite duration supremum, the canonical curve satisfies the concrete Hamiltonian
ODE. At a positive time it agrees on a full neighbourhood with one longer certified segment. -/
theorem maximalCurve_hasDerivAt (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (sSup (durationSet V e x))) :
    HasDerivAt (h.maximalCurve hbdd)
      (V.edgeVectorField e (h.maximalCurve hbdd t)) t := by
  let k := h.segmentAt hbdd t ht.2
  have hkt : t < k.duration := h.lt_duration_segmentAt hbdd t ht.2
  have hk_sup : k.duration ≤ sSup (durationSet V e x) :=
    le_csSup hbdd k.mem_durationSet
  let r : ℝ := min (t / 2) ((k.duration - t) / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith [ht.1]) (by linarith [hkt])
  have heq : h.maximalCurve hbdd =ᶠ[𝓝 t] k.curve := by
    filter_upwards [Metric.ball_mem_nhds t hr] with y hy
    rw [Metric.mem_ball] at hy
    have hy0 : 0 ≤ y := by
      rw [Real.dist_eq, abs_lt] at hy
      dsimp [r] at hy
      have : t / 2 ≤ t / 2 := le_rfl
      linarith [min_le_left (t / 2) ((k.duration - t) / 2)]
    have hyk : y < k.duration := by
      rw [Real.dist_eq, abs_lt] at hy
      dsimp [r] at hy
      linarith [min_le_right (t / 2) ((k.duration - t) / 2)]
    have hysup : y < sSup (durationSet V e x) := lt_of_lt_of_le hyk hk_sup
    exact h.maximalCurve_eq_segment_curve hbdd hy0 hysup k hyk
  have htk_mem : t ∈ Icc (0 : ℝ) k.duration := ⟨ht.1.le, hkt.le⟩
  have hvalue : h.maximalCurve hbdd t = k.curve t :=
    h.maximalCurve_eq_segment_curve hbdd ht.1.le ht.2 k hkt
  rw [hvalue]
  exact (k.integralCurve t htk_mem).congr_of_eventuallyEq heq

/-- A finite duration supremum gives one Lipschitz travel bound for the canonical curve on every
closed subinterval strictly inside its domain. -/
theorem exists_maximalCurve_travel_bound (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℝ,
      0 < a → a ≤ b → b < sSup (durationSet V e x) →
        dist (h.maximalCurve hbdd b) (h.maximalCurve hbdd a) ≤ B * (b - a) := by
  obtain ⟨C, hC⟩ := V.exists_lowerBound_extension_closedEdge e
  let E : ℝ := V.hamiltonian e x.1 x.2
  let P : ℝ := Real.sqrt (2 * (E - C))
  obtain ⟨B, hBnonneg, hB⟩ := V.exists_uniform_normBound_edgeVectorField_closedMomentumBoxes P
  refine ⟨B, hBnonneg, ?_⟩
  intro a b ha hab hb
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivAt (h.maximalCurve hbdd)
        (V.edgeVectorField e (h.maximalCurve hbdd t)) t := by
    intro t ht
    apply h.maximalCurve_hasDerivAt hbdd
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hmem : ∀ t ∈ Icc a b,
      h.maximalCurve hbdd t ∈ closedEdgeMomentumBox e P := by
    intro t ht
    apply V.mem_closedEdgeMomentumBox_of_hamiltonian_le
    · exact h.maximalCurve_physical_at hbdd (le_trans ha.le ht.1)
        (lt_of_le_of_lt ht.2 hb)
    · exact hC _ (h.maximalCurve_physical_at hbdd (le_trans ha.le ht.1)
        (lt_of_le_of_lt ht.2 hb))
    · change V.hamiltonian e (h.maximalCurve hbdd t).1 (h.maximalCurve hbdd t).2 ≤ E
      exact (h.maximalCurve_hamiltonian_eq_initial hbdd (le_trans ha.le ht.1)
        (lt_of_le_of_lt ht.2 hb)).le
  have htravel := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := a) (b := b) (f := h.maximalCurve hbdd)
    (f' := fun t => V.edgeVectorField e (h.maximalCurve hbdd t))
    (fun t ht => (hderiv t ht).hasDerivWithinAt)
    (fun t ht => hB e (h.maximalCurve hbdd t)
      (hmem t (Ico_subset_Icc_self ht)))
    b (right_mem_Icc.mpr hab)
  simpa only [dist_eq_norm_sub] using htravel

/-- If the duration set is bounded above, the canonical curve is Cauchy as time approaches its
finite supremum from the left. Completeness of `ℝ × ℝ` will therefore provide its endpoint. -/
theorem cauchy_map_maximalCurve_nhdsLT (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) :
    Cauchy (Filter.map (h.maximalCurve hbdd) (𝓝[<] sSup (durationSet V e x))) := by
  obtain ⟨B, hBnonneg, htravel⟩ := h.exists_maximalCurve_travel_bound hbdd
  let T : ℝ := sSup (durationSet V e x)
  have hTpos : 0 < T :=
    lt_of_lt_of_le h.duration_pos (le_csSup hbdd h.mem_durationSet)
  refine Metric.cauchy_iff.mpr ⟨(nhdsLT_neBot T).map _, ?_⟩
  intro ε hε
  let δ : ℝ := min (T / 2) (ε / (B + 1))
  have hB1 : 0 < B + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (div_pos hε hB1)
  have hδT : δ ≤ T / 2 := min_le_left _ _
  have hδε : δ ≤ ε / (B + 1) := min_le_right _ _
  let U : Set ℝ := Ioo (T - δ) T
  have hU : U ∈ 𝓝[<] T := by
    dsimp [U]
    simpa only [← Iio_inter_Ioi] using
      inter_mem_nhdsWithin (Iio T) (Ioi_mem_nhds (by linarith : T - δ < T))
  let W : Set (ℝ × ℝ) := h.maximalCurve hbdd '' U
  refine ⟨W, ?_, ?_⟩
  · rw [Filter.mem_map]
    apply Filter.mem_of_superset hU
    intro t ht
    exact ⟨t, ht, rfl⟩
  · rintro y ⟨u, hu, rfl⟩ z ⟨v, hv, rfl⟩
    rcases le_total u v with huv | hvu
    · have hu0 : 0 < u := by
        dsimp [U] at hu
        have hbase : 0 < T - δ := by linarith [hδT, hTpos]
        exact lt_trans hbase hu.1
      have hvT : v < T := by simpa [U] using hv.2
      have huvδ : v - u < δ := by
        dsimp [U] at hu hv
        linarith [hu.1, hv.2]
      have hbound := htravel u v hu0 huv (by simpa [T] using hvT)
      calc
        dist (h.maximalCurve hbdd u) (h.maximalCurve hbdd v) =
            dist (h.maximalCurve hbdd v) (h.maximalCurve hbdd u) := dist_comm _ _
        _ ≤ B * (v - u) := hbound
        _ ≤ B * δ := mul_le_mul_of_nonneg_left huvδ.le hBnonneg
        _ < (B + 1) * δ := by nlinarith [hδ]
        _ ≤ ε := by
          rw [mul_comm]
          exact (le_div_iff₀ hB1).mp hδε
    · have hv0 : 0 < v := by
        dsimp [U] at hu hv
        have hbase : 0 < T - δ := by linarith [hδT, hTpos]
        exact lt_trans hbase hv.1
      have huT : u < T := by simpa [U] using hu.2
      have hvuδ : u - v < δ := by
        dsimp [U] at hu hv
        linarith [hv.1, hu.2]
      have hbound := htravel v u hv0 hvu (by simpa [T] using huT)
      calc
        dist (h.maximalCurve hbdd u) (h.maximalCurve hbdd v) ≤ B * (u - v) := hbound
        _ ≤ B * δ := mul_le_mul_of_nonneg_left hvuδ.le hBnonneg
        _ < (B + 1) * δ := by nlinarith [hδ]
        _ ≤ ε := by
          rw [mul_comm]
          exact (le_div_iff₀ hB1).mp hδε

/-- The endpoint of the canonical curve at a finite duration supremum, obtained from the
left-Cauchy property and completeness of the Euclidean phase plane. -/
noncomputable def maximalEndpoint (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) : ℝ × ℝ := by
  letI : (𝓝[<] sSup (durationSet V e x)).NeBot := nhdsLT_neBot _
  exact Classical.choose ((cauchy_map_iff_exists_tendsto.mp
    (h.cauchy_map_maximalCurve_nhdsLT hbdd)))

theorem tendsto_maximalCurve_maximalEndpoint (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) :
    Tendsto (h.maximalCurve hbdd) (𝓝[<] sSup (durationSet V e x))
      (𝓝 (h.maximalEndpoint hbdd)) := by
  letI : (𝓝[<] sSup (durationSet V e x)).NeBot := nhdsLT_neBot _
  exact Classical.choose_spec ((cauchy_map_iff_exists_tendsto.mp
    (h.cauchy_map_maximalCurve_nhdsLT hbdd)))

/-- The restarted flight reaches the same maximal endpoint (position and momentum) as the
original.  This is the endpoint half of the semigroup correspondence, obtained by uniqueness of
limits from the curve correspondence. -/
theorem maximalEndpoint_shift_eq (h : V.PhysicalEdgeSegment e x) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < h.duration) (hbdd : BddAbove (durationSet V e x))
    (g : V.PhysicalEdgeSegment e (h.curve s)) :
    g.maximalEndpoint ((h.bddAbove_durationSet_curve_iff hs0 hs).mpr hbdd) =
      h.maximalEndpoint hbdd := by
  have hmid := (h.bddAbove_durationSet_curve_iff hs0 hs).mpr hbdd
  set T := sSup (durationSet V e x) with hT
  have hsupmid : sSup (durationSet V e (h.curve s)) = T - s :=
    h.sSup_durationSet_shift_eq hs0 hs hbdd
  have hdurT : h.duration ≤ T := le_csSup hbdd h.mem_durationSet
  have hTspos : 0 < T - s := by linarith
  letI : (𝓝[<] (T - s)).NeBot := nhdsLT_neBot _
  have hshift : Tendsto (fun u => s + u) (𝓝[<] (T - s)) (𝓝[<] T) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont := (continuous_id.const_add s).tendsto (T - s)
      simp only [id_eq, add_sub_cancel] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      have : u < T - s := hu
      show s + u < T
      linarith
  have h1 : Tendsto (fun u => h.maximalCurve hbdd (s + u)) (𝓝[<] (T - s))
      (𝓝 (h.maximalEndpoint hbdd)) :=
    (h.tendsto_maximalCurve_maximalEndpoint hbdd).comp hshift
  have hgtend : Tendsto (g.maximalCurve hmid) (𝓝[<] (T - s)) (𝓝 (g.maximalEndpoint hmid)) := by
    rw [← hsupmid]
    exact g.tendsto_maximalCurve_maximalEndpoint hmid
  have heq : g.maximalCurve hmid =ᶠ[𝓝[<] (T - s)] (fun u => h.maximalCurve hbdd (s + u)) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hTspos)]
      with u hu hupos
    have hult : u < T - s := hu
    exact h.maximalCurve_shift_eq hs0 hs hbdd g (Set.mem_Ioi.mp hupos).le hult
  exact tendsto_nhds_unique hgtend (h1.congr' heq.symm)

/-- The maximal endpoint depends only on the edge and initial state, not on the witnessing
segment. -/
theorem maximalEndpoint_indep (h h' : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) :
    h.maximalEndpoint hbdd = h'.maximalEndpoint hbdd := by
  have hTpos : 0 < sSup (durationSet V e x) :=
    lt_of_lt_of_le h.duration_pos (le_csSup hbdd h.mem_durationSet)
  letI : (𝓝[<] sSup (durationSet V e x)).NeBot := nhdsLT_neBot _
  have h1 := h.tendsto_maximalCurve_maximalEndpoint hbdd
  have h2 := h'.tendsto_maximalCurve_maximalEndpoint hbdd
  have heq : h.maximalCurve hbdd =ᶠ[𝓝[<] sSup (durationSet V e x)] h'.maximalCurve hbdd := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hTpos)]
      with u hu hupos
    have hult : u < sSup (durationSet V e x) := hu
    exact h.maximalCurve_indep h' hbdd (Set.mem_Ioi.mp hupos).le hult
  exact tendsto_nhds_unique h1 (h2.congr' heq.symm)

/-- The finite-time endpoint remains on the closed physical edge. -/
theorem maximalEndpoint_physical (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) :
    (h.maximalEndpoint hbdd).1 ∈ Icc (0 : ℝ) (Γ.length e) := by
  let T : ℝ := sSup (durationSet V e x)
  have hTpos : 0 < T :=
    lt_of_lt_of_le h.duration_pos (le_csSup hbdd h.mem_durationSet)
  letI : (𝓝[<] T).NeBot := nhdsLT_neBot _
  have htend : Tendsto (h.maximalCurve hbdd) (𝓝[<] T)
      (𝓝 (h.maximalEndpoint hbdd)) := by
    simpa [T] using h.tendsto_maximalCurve_maximalEndpoint hbdd
  have hevent : ∀ᶠ t in 𝓝[<] T,
      h.maximalCurve hbdd t ∈ {z : ℝ × ℝ | z.1 ∈ Icc (0 : ℝ) (Γ.length e)} := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hTpos)] with t htT ht0
    exact h.maximalCurve_physical_at hbdd ht0.le htT
  exact (isClosed_Icc.preimage continuous_fst).mem_of_tendsto htend hevent

/-- The limiting endpoint is still in the open domain on which the chosen potential extension
is `C²`. -/
theorem maximalEndpoint_mem_domain (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) :
    (h.maximalEndpoint hbdd).1 ∈ V.domain e :=
  V.closedEdge_subset_domain e (h.maximalEndpoint_physical hbdd)

/-- The vector field along the canonical curve converges to its value at the finite endpoint.
This is the analytic input needed to extend the curve differentiably to that endpoint from the
left. -/
theorem tendsto_edgeVectorField_maximalCurve_maximalEndpoint
    (h : V.PhysicalEdgeSegment e x) (hbdd : BddAbove (durationSet V e x)) :
    Tendsto (fun t => V.edgeVectorField e (h.maximalCurve hbdd t))
      (𝓝[<] sSup (durationSet V e x))
      (𝓝 (V.edgeVectorField e (h.maximalEndpoint hbdd))) := by
  exact (V.contDiffAt_edgeVectorField (h.maximalEndpoint_mem_domain hbdd)).continuousAt.tendsto.comp
    (h.tendsto_maximalCurve_maximalEndpoint hbdd)

/-- The canonical curve completed by its limiting endpoint.  This auxiliary curve is used only
to obtain a one-sided derivative at the limiting time; before that time it is definitionally the
canonical curve. -/
noncomputable def maximalCurveClosed (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) : ℝ → ℝ × ℝ := fun t =>
  if t < sSup (durationSet V e x) then h.maximalCurve hbdd t else h.maximalEndpoint hbdd

theorem maximalCurveClosed_eq_maximalCurve (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht : t < sSup (durationSet V e x)) :
    h.maximalCurveClosed hbdd t = h.maximalCurve hbdd t := by
  simp [maximalCurveClosed, ht]

theorem maximalCurveClosed_eq_endpoint (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) :
    h.maximalCurveClosed hbdd (sSup (durationSet V e x)) = h.maximalEndpoint hbdd := by
  simp [maximalCurveClosed]

/-- The completed maximal curve depends only on the edge and initial state (at nonnegative
times). -/
theorem maximalCurveClosed_indep (h h' : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ} (ht0 : 0 ≤ t) :
    h.maximalCurveClosed hbdd t = h'.maximalCurveClosed hbdd t := by
  by_cases ht : t < sSup (durationSet V e x)
  · rw [h.maximalCurveClosed_eq_maximalCurve hbdd ht,
      h'.maximalCurveClosed_eq_maximalCurve hbdd ht]
    exact h.maximalCurve_indep h' hbdd ht0 ht
  · simp only [maximalCurveClosed, if_neg ht]
    exact h.maximalEndpoint_indep h' hbdd

theorem maximalCurveClosed_hasDerivAt (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (sSup (durationSet V e x))) :
    HasDerivAt (h.maximalCurveClosed hbdd)
      (V.edgeVectorField e (h.maximalCurveClosed hbdd t)) t := by
  have heq : h.maximalCurveClosed hbdd =ᶠ[𝓝 t] h.maximalCurve hbdd := by
    filter_upwards [Iio_mem_nhds ht.2] with y hy
    exact h.maximalCurveClosed_eq_maximalCurve hbdd hy
  rw [h.maximalCurveClosed_eq_maximalCurve hbdd ht.2]
  exact (h.maximalCurve_hasDerivAt hbdd ht).congr_of_eventuallyEq heq

theorem continuousWithinAt_maximalCurveClosed_left (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) :
    ContinuousWithinAt (h.maximalCurveClosed hbdd)
      (Ioo (0 : ℝ) (sSup (durationSet V e x))) (sSup (durationSet V e x)) := by
  let T : ℝ := sSup (durationSet V e x)
  have hTpos : 0 < T :=
    lt_of_lt_of_le h.duration_pos (le_csSup hbdd h.mem_durationSet)
  have hlim : Tendsto (h.maximalCurve hbdd) (𝓝[Ioo (0 : ℝ) T] T)
      (𝓝 (h.maximalEndpoint hbdd)) := by
    exact (h.tendsto_maximalCurve_maximalEndpoint hbdd).mono_left
      (nhdsWithin_mono _ Ioo_subset_Iio_self)
  have heq : h.maximalCurveClosed hbdd =ᶠ[𝓝[Ioo (0 : ℝ) T] T] h.maximalCurve hbdd := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact h.maximalCurveClosed_eq_maximalCurve hbdd ht.2
  change Tendsto (h.maximalCurveClosed hbdd) (𝓝[Ioo (0 : ℝ) T] T)
    (𝓝 (h.maximalCurveClosed hbdd T))
  rw [show T = sSup (durationSet V e x) by rfl,
    h.maximalCurveClosed_eq_endpoint hbdd]
  exact hlim.congr' heq.symm

/-- The completed maximal curve has the expected left derivative at its finite endpoint. -/
theorem maximalCurveClosed_hasDerivWithinAt_leftEndpoint
    (h : V.PhysicalEdgeSegment e x) (hbdd : BddAbove (durationSet V e x)) :
    HasDerivWithinAt (h.maximalCurveClosed hbdd)
      (V.edgeVectorField e (h.maximalEndpoint hbdd))
      (Iic (sSup (durationSet V e x))) (sSup (durationSet V e x)) := by
  let T : ℝ := sSup (durationSet V e x)
  have hTpos : 0 < T :=
    lt_of_lt_of_le h.duration_pos (le_csSup hbdd h.mem_durationSet)
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (s := Ioo (0 : ℝ) T)
  · intro t ht
    exact (h.maximalCurveClosed_hasDerivAt hbdd ht).differentiableAt.differentiableWithinAt
  · simpa [T] using h.continuousWithinAt_maximalCurveClosed_left hbdd
  · simpa only [← Iio_inter_Ioi] using
      inter_mem_nhdsWithin (Iio T) (Ioi_mem_nhds hTpos)
  · have hfield : Tendsto (fun t => V.edgeVectorField e (h.maximalCurve hbdd t))
        (𝓝[<] T) (𝓝 (V.edgeVectorField e (h.maximalEndpoint hbdd))) := by
      simpa [T] using h.tendsto_edgeVectorField_maximalCurve_maximalEndpoint hbdd
    apply hfield.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hTpos)] with t htT ht0
    simpa [h.maximalCurveClosed_eq_maximalCurve hbdd htT] using
      (h.maximalCurveClosed_hasDerivAt hbdd ⟨ht0, htT⟩).deriv.symm

/-- The candidate used to continue a finite maximal curve through an interior limiting point.
The first branch retains the original segment around time zero, the middle branch is the
canonical maximal curve, and the final branch is a local ODE solution started at the endpoint. -/
noncomputable def continuationCurve (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) (c : ℝ) (β : ℝ → ℝ × ℝ) : ℝ → ℝ × ℝ := fun t =>
  if t ≤ c then h.curve t else
    if t < sSup (durationSet V e x) then h.maximalCurve hbdd t else β t

/-- If a finite maximal endpoint were in the open edge, a locally defined ODE solution there
could be spliced to the canonical curve and would yield a longer physical segment. -/
theorem exists_segment_duration_gt_sSup_of_maximalEndpoint_interior
    (h : V.PhysicalEdgeSegment e x) (hbdd : BddAbove (durationSet V e x))
    (hinterior : (h.maximalEndpoint hbdd).1 ∈ Ioo (0 : ℝ) (Γ.length e)) :
    ∃ k : V.PhysicalEdgeSegment e x, sSup (durationSet V e x) < k.duration := by
  let T : ℝ := sSup (durationSet V e x)
  have hTpos : 0 < T :=
    lt_of_lt_of_le h.duration_pos (le_csSup hbdd h.mem_durationSet)
  obtain ⟨β, hβT, ε, hεpos, hβ⟩ :=
    V.exists_local_edge_integralCurve_in_openCylinder
      (h.maximalEndpoint_mem_domain hbdd) hinterior T
  let c : ℝ := h.duration / 2
  have hcpos : 0 < c := by dsimp [c]; linarith [h.duration_pos]
  have hchdur : c < h.duration := by dsimp [c]; linarith [h.duration_pos]
  have hcT : c < T :=
    lt_of_lt_of_le hchdur (le_csSup hbdd h.mem_durationSet)
  let δ : ℝ := ε / 2
  have hδpos : 0 < δ := by dsimp [δ]; linarith
  have hδeps : δ < ε := by dsimp [δ]; linarith
  let γ : ℝ → ℝ × ℝ := h.continuationCurve hbdd c β
  have hγ0 : γ 0 = x := by
    simp [γ, continuationCurve, hcpos.le, h.initial]
  have hγphysical : ∀ t ∈ Icc (0 : ℝ) (T + δ),
      (γ t).1 ∈ Icc (0 : ℝ) (Γ.length e) := by
    intro t ht
    by_cases htc : t ≤ c
    · simp only [γ, continuationCurve, if_pos htc]
      exact h.physical_at t ⟨ht.1, le_trans htc hchdur.le⟩
    · by_cases htT : t < T
      · simpa [γ, continuationCurve, T, htc, htT] using
          h.maximalCurve_physical_at hbdd ht.1 (by simpa [T] using htT)
      · have htTle : T ≤ t := le_of_not_gt htT
        have htupper : t < T + ε := by linarith [ht.2, hδeps]
        simpa [γ, continuationCurve, T, htc, htT] using
          ⟨(hβ t ⟨by linarith, htupper⟩).1.1.le,
            (hβ t ⟨by linarith, htupper⟩).1.2.le⟩
  have hγdomain : ∀ t ∈ Icc (0 : ℝ) (T + δ), (γ t).1 ∈ V.domain e := by
    intro t ht
    exact V.closedEdge_subset_domain e (hγphysical t ht)
  have hγinterior : ∀ t ∈ Ioo (0 : ℝ) (T + δ),
      (γ t).1 ∈ Ioo (0 : ℝ) (Γ.length e) := by
    intro t ht
    by_cases htc : t ≤ c
    · simp only [γ, continuationCurve, if_pos htc]
      exact h.interior_after_initial t ⟨ht.1, lt_of_le_of_lt htc hchdur⟩
    · by_cases htT : t < T
      · simpa [γ, continuationCurve, T, htc, htT] using
          h.maximalCurve_interior_at hbdd ⟨ht.1, by simpa [T] using htT⟩
      · have htTle : T ≤ t := le_of_not_gt htT
        have htupper : t < T + ε := by linarith [ht.2, hδeps]
        simpa [γ, continuationCurve, T, htc, htT] using
          (hβ t ⟨by linarith, htupper⟩).1
  have hγderiv : ∀ t ∈ Icc (0 : ℝ) (T + δ),
      HasDerivAt γ (V.edgeVectorField e (γ t)) t := by
    intro t ht
    rcases lt_trichotomy t c with htc | rfl | hct
    · have heq : γ =ᶠ[𝓝 t] h.curve := by
        filter_upwards [Iio_mem_nhds htc] with y hy
        change y < c at hy
        simp [γ, continuationCurve, hy.le]
      simp only [γ, continuationCurve, if_pos htc.le]
      exact (h.integralCurve t ⟨ht.1, (lt_of_lt_of_le htc hchdur.le).le⟩).congr_of_eventuallyEq heq
    · let r : ℝ := min (c / 2) ((h.duration - c) / 2)
      have hrpos : 0 < r := by
        dsimp [r]
        exact lt_min (by linarith [hcpos]) (by linarith [hchdur])
      have heq : γ =ᶠ[𝓝 c] h.curve := by
        filter_upwards [Metric.ball_mem_nhds c hrpos] with y hy
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
        by_cases hyc : y ≤ c
        · simp [γ, continuationCurve, hyc]
        · have hy0 : 0 ≤ y := by
            simp only [r] at hy
            linarith [min_le_left (c / 2) ((h.duration - c) / 2)]
          have hyhdur : y < h.duration := by
            simp only [r] at hy
            linarith [min_le_right (c / 2) ((h.duration - c) / 2)]
          have hyT : y < T := lt_of_lt_of_le hyhdur (le_csSup hbdd h.mem_durationSet)
          simpa [γ, continuationCurve, T, hyc, hyT] using
            h.maximalCurve_eq_segment_curve hbdd hy0 (by simpa [T] using hyT) h hyhdur
      simp only [γ, continuationCurve, if_pos le_rfl]
      exact (h.integralCurve c ⟨hcpos.le, hchdur.le⟩).congr_of_eventuallyEq heq
    · rcases lt_trichotomy t T with htT | rfl | hTt
      · have heq : γ =ᶠ[𝓝 t] h.maximalCurve hbdd := by
          filter_upwards [Ioi_mem_nhds hct, Iio_mem_nhds htT] with y hyc hyT
          change c < y at hyc
          change y < T at hyT
          simp [γ, continuationCurve, T, not_le_of_gt hyc, hyT]
        simpa [γ, continuationCurve, T, not_le_of_gt hct, htT] using
          (h.maximalCurve_hasDerivAt hbdd
            ⟨by linarith [hcpos], by simpa [T] using htT⟩).congr_of_eventuallyEq heq
      · have hleftEq : γ =ᶠ[𝓝[Iic T] T] h.maximalCurveClosed hbdd := by
          filter_upwards [self_mem_nhdsWithin,
            nhdsWithin_le_nhds (Ioi_mem_nhds hcT)] with y hyT hyc
          change y ≤ T at hyT
          change c < y at hyc
          by_cases hylt : y < T
          · simp [γ, continuationCurve, T, not_le_of_gt hyc, hylt,
              maximalCurveClosed]
          · have hyTle : T ≤ y := le_of_not_gt hylt
            have hyEq : y = T := le_antisymm hyT hyTle
            subst y
            simp [γ, continuationCurve, T, not_le_of_gt hcT, hβT,
              maximalCurveClosed]
        have hrightEq : γ =ᶠ[𝓝[Ici T] T] β := by
          filter_upwards [self_mem_nhdsWithin] with y hyT
          change T ≤ y at hyT
          have hyc : ¬ y ≤ c := not_le_of_gt (lt_of_lt_of_le hcT hyT)
          have hylt : ¬ y < T := not_lt_of_ge hyT
          simp [γ, continuationCurve, T, hyc, hylt]
        have hleft :=
          (h.maximalCurveClosed_hasDerivWithinAt_leftEndpoint hbdd).congr_of_eventuallyEq
          hleftEq (by simp [γ, continuationCurve, T, not_le_of_gt hcT, hβT,
            maximalCurveClosed])
        have hβderiv := (hβ T ⟨by linarith, by linarith⟩).2
        have hright : HasDerivWithinAt γ (V.edgeVectorField e (h.maximalEndpoint hbdd))
            (Ici T) T := by
          simpa [hβT] using hβderiv.hasDerivWithinAt.congr_of_eventuallyEq hrightEq
            (by simp [γ, continuationCurve, T, not_le_of_gt hcT, hβT])
        have hγT : γ T = h.maximalEndpoint hbdd := by
          simp [γ, continuationCurve, T, not_le_of_gt hcT, hβT]
        simpa [T, hγT] using hleft.union hright
      · have heq : γ =ᶠ[𝓝 t] β := by
          filter_upwards [Ioi_mem_nhds hTt] with y hyT
          have hyc : ¬ y ≤ c := not_le_of_gt (lt_trans hcT hyT)
          have hylt : ¬ y < T := not_lt_of_ge hyT.le
          simp [γ, continuationCurve, T, hyc, hylt]
        have htupper : t < T + ε := by linarith [ht.2, hδeps]
        simpa [γ, continuationCurve, T, not_le_of_gt (lt_trans hcT hTt),
          not_lt_of_ge hTt.le] using
          (hβ t ⟨by linarith, htupper⟩).2.congr_of_eventuallyEq heq
  refine ⟨{
    duration := T + δ
    duration_pos := by linarith
    curve := γ
    initial := hγ0
    initial_physical := h.initial_physical
    physical := hγphysical
    in_domain := hγdomain
    integralCurve := hγderiv
    interior_after_initial := hγinterior
  }, ?_⟩
  dsimp [T]
  linarith

/-- A bounded duration set cannot have its maximal endpoint in the open cylinder: the preceding
splicing theorem would contradict the least-upper-bound property. -/
theorem maximalEndpoint_not_interior (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) :
    ¬ (h.maximalEndpoint hbdd).1 ∈ Ioo (0 : ℝ) (Γ.length e) := by
  intro hinterior
  obtain ⟨k, hk⟩ := h.exists_segment_duration_gt_sSup_of_maximalEndpoint_interior hbdd hinterior
  exact (not_lt_of_ge (le_csSup hbdd k.mem_durationSet)) hk

/-- The position coordinate of a finite maximal endpoint is one of the two endpoint coordinates.
This is the analytic first-hit alternative, derived rather than built into the maximal-flow
construction. -/
theorem maximalEndpoint_coordinate_eq_zero_or_length (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) :
    (h.maximalEndpoint hbdd).1 = 0 ∨ (h.maximalEndpoint hbdd).1 = Γ.length e := by
  have hclosed := h.maximalEndpoint_physical hbdd
  by_cases hzero : (h.maximalEndpoint hbdd).1 = 0
  · exact Or.inl hzero
  · right
    apply le_antisymm hclosed.2
    apply le_of_not_gt
    intro hlt
    exact h.maximalEndpoint_not_interior hbdd ⟨lt_of_le_of_ne hclosed.1 (Ne.symm hzero), hlt⟩

/-- The mechanical energy of the finite maximal endpoint is the initial energy. -/
theorem maximalEndpoint_hamiltonian_eq_initial (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) :
    V.hamiltonian e (h.maximalEndpoint hbdd).1 (h.maximalEndpoint hbdd).2 =
      V.hamiltonian e x.1 x.2 := by
  let T : ℝ := sSup (durationSet V e x)
  let E : ℝ := V.hamiltonian e x.1 x.2
  letI : (𝓝[<] T).NeBot := nhdsLT_neBot _
  have hTpos : 0 < T :=
    lt_of_lt_of_le h.duration_pos (le_csSup hbdd h.mem_durationSet)
  have hcurve : Tendsto (h.maximalCurve hbdd) (𝓝[<] T)
      (𝓝 (h.maximalEndpoint hbdd)) := by
    simpa [T] using h.tendsto_maximalCurve_maximalEndpoint hbdd
  have hHcont : ContinuousAt (fun z : ℝ × ℝ => V.hamiltonian e z.1 z.2)
      (h.maximalEndpoint hbdd) := by
    unfold hamiltonian
    exact ((continuousAt_snd.pow 2).div_const 2).add
      ((V.extension_contDiffAt_of_mem (h.maximalEndpoint_mem_domain hbdd)).continuousAt.comp
        continuousAt_fst)
  have hlim : Tendsto (fun t => V.hamiltonian e (h.maximalCurve hbdd t).1
      (h.maximalCurve hbdd t).2) (𝓝[<] T)
      (𝓝 (V.hamiltonian e (h.maximalEndpoint hbdd).1 (h.maximalEndpoint hbdd).2)) :=
    hHcont.tendsto.comp hcurve
  have hevent : (fun t => V.hamiltonian e (h.maximalCurve hbdd t).1
      (h.maximalCurve hbdd t).2) =ᶠ[𝓝[<] T] fun _ => E := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hTpos)] with t htT ht0
    exact h.maximalCurve_hamiltonian_eq_initial hbdd ht0.le htT
  have hconst : Tendsto (fun _ : ℝ => E) (𝓝[<] T) (𝓝 E) := tendsto_const_nhds
  rw [show E = V.hamiltonian e x.1 x.2 by rfl] at hconst
  exact tendsto_nhds_unique (hlim.congr' hevent) hconst

/-- At a regular energy, a finite maximal endpoint has nonzero momentum. -/
theorem maximalEndpoint_momentum_ne_zero (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    (h.maximalEndpoint hbdd).2 ≠ 0 := by
  intro hp
  rcases h.maximalEndpoint_coordinate_eq_zero_or_length hbdd with hq | hq
  · apply hregular
    apply (V.mem_exceptionalEnergies_iff).mpr
    refine ⟨Γ.endpoint e false, ?_⟩
    have hE := h.maximalEndpoint_hamiltonian_eq_initial hbdd
    rw [hq, hp] at hE
    have hend := V.endpoint_hamiltonian (η := (e, false)) 0
    have hend' : V.hamiltonian e 0 0 = V.vertexValue (Γ.endpoint e false) := by
      simpa [FiniteMetricGraph.EdgeEnd.coordinate, FiniteMetricGraph.EdgeEnd.vertex] using hend
    rw [hE] at hend'
    simpa using hend'.symm
  · apply hregular
    apply (V.mem_exceptionalEnergies_iff).mpr
    refine ⟨Γ.endpoint e true, ?_⟩
    have hE := h.maximalEndpoint_hamiltonian_eq_initial hbdd
    rw [hq, hp] at hE
    have hend := V.endpoint_hamiltonian (η := (e, true)) 0
    have hend' : V.hamiltonian e (Γ.length e) 0 = V.vertexValue (Γ.endpoint e true) := by
      simpa [FiniteMetricGraph.EdgeEnd.coordinate, FiniteMetricGraph.EdgeEnd.vertex] using hend
    rw [hE] at hend'
    simpa using hend'.symm

/-- A maximal physical flight arriving at the left endpoint has nonpositive terminal momentum.
Together with regular nonvanishing this is the incoming sign at that endpoint. -/
theorem maximalEndpoint_left_momentum_nonpos (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x))
    (hq : (h.maximalEndpoint hbdd).1 = 0) :
    (h.maximalEndpoint hbdd).2 ≤ 0 := by
  let T : ℝ := sSup (durationSet V e x)
  have hTpos : 0 < T :=
    lt_of_lt_of_le h.duration_pos (le_csSup hbdd h.mem_durationSet)
  have hderivPair := h.maximalCurveClosed_hasDerivWithinAt_leftEndpoint hbdd
  have hderiv : HasDerivWithinAt (fun t => (h.maximalCurveClosed hbdd t).1)
      (h.maximalEndpoint hbdd).2 (Iic T) T := by
    have hmap : ContinuousLinearMap.toSpanSingleton ℝ (h.maximalEndpoint hbdd).2 =
        ContinuousLinearMap.fst ℝ ℝ ℝ ∘SL
          ContinuousLinearMap.toSpanSingleton ℝ
            (V.edgeVectorField e (h.maximalEndpoint hbdd)) := by
      ext
      simp [edgeVectorField]
    change HasFDerivAtFilter (fun t => (h.maximalCurveClosed hbdd t).1)
      (ContinuousLinearMap.toSpanSingleton ℝ (h.maximalEndpoint hbdd).2)
      (𝓝[Iic T] T ×ˢ pure T)
    simpa [T, hmap] using hderivPair.fst
  apply leftEndpoint_derivWithin_nonpos_of_pos_before hTpos
  · intro t ht
    change 0 < (h.maximalCurveClosed hbdd t).1
    rw [h.maximalCurveClosed_eq_maximalCurve hbdd (by simpa [T] using ht.2)]
    exact (h.maximalCurve_interior_at hbdd ⟨ht.1, by simpa [T] using ht.2⟩).1
  · exact hderiv
  · simpa [T, maximalCurveClosed, hq] using h.maximalCurveClosed_eq_endpoint hbdd

/-- At a regular left-endpoint hit the maximal-flight momentum has the strict incoming sign. -/
theorem maximalEndpoint_left_momentum_neg (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies)
    (hq : (h.maximalEndpoint hbdd).1 = 0) :
    (h.maximalEndpoint hbdd).2 < 0 :=
  lt_of_le_of_ne (h.maximalEndpoint_left_momentum_nonpos hbdd hq)
    (h.maximalEndpoint_momentum_ne_zero hbdd hregular)

/-- A maximal physical flight arriving at the right endpoint has nonnegative terminal momentum. -/
theorem maximalEndpoint_right_momentum_nonneg (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x))
    (hq : (h.maximalEndpoint hbdd).1 = Γ.length e) :
    0 ≤ (h.maximalEndpoint hbdd).2 := by
  let T : ℝ := sSup (durationSet V e x)
  have hTpos : 0 < T :=
    lt_of_lt_of_le h.duration_pos (le_csSup hbdd h.mem_durationSet)
  have hderivPair := h.maximalCurveClosed_hasDerivWithinAt_leftEndpoint hbdd
  have hderiv : HasDerivWithinAt (fun t => (h.maximalCurveClosed hbdd t).1)
      (h.maximalEndpoint hbdd).2 (Iic T) T := by
    have hmap : ContinuousLinearMap.toSpanSingleton ℝ (h.maximalEndpoint hbdd).2 =
        ContinuousLinearMap.fst ℝ ℝ ℝ ∘SL
          ContinuousLinearMap.toSpanSingleton ℝ
            (V.edgeVectorField e (h.maximalEndpoint hbdd)) := by
      ext
      simp [edgeVectorField]
    change HasFDerivAtFilter (fun t => (h.maximalCurveClosed hbdd t).1)
      (ContinuousLinearMap.toSpanSingleton ℝ (h.maximalEndpoint hbdd).2)
      (𝓝[Iic T] T ×ˢ pure T)
    simpa [T, hmap] using hderivPair.fst
  have hderiv' : HasDerivWithinAt
      (fun t => -(h.maximalCurveClosed hbdd t).1 + Γ.length e)
      (-(h.maximalEndpoint hbdd).2) (Iic T) T := by
    simpa using hderiv.neg.const_add (Γ.length e)
  have hnonpos : -(h.maximalEndpoint hbdd).2 ≤ 0 :=
    leftEndpoint_derivWithin_nonpos_of_pos_before hTpos
      (fun t ht => by
        rw [h.maximalCurveClosed_eq_maximalCurve hbdd (by simpa [T] using ht.2)]
        linarith [(h.maximalCurve_interior_at hbdd
          ⟨ht.1, by simpa [T] using ht.2⟩).2])
      hderiv' (by simpa [T, maximalCurveClosed, hq] using
        h.maximalCurveClosed_eq_endpoint hbdd)
  linarith

/-- At a regular right-endpoint hit the maximal-flight momentum has the strict incoming sign. -/
theorem maximalEndpoint_right_momentum_pos (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies)
    (hq : (h.maximalEndpoint hbdd).1 = Γ.length e) :
    0 < (h.maximalEndpoint hbdd).2 :=
  lt_of_le_of_ne (h.maximalEndpoint_right_momentum_nonneg hbdd hq)
    (Ne.symm (h.maximalEndpoint_momentum_ne_zero hbdd hregular))

/-- The completed maximal curve starts at the original state. -/
theorem maximalCurveClosed_initial (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) : h.maximalCurveClosed hbdd 0 = x := by
  have hTpos : 0 < sSup (durationSet V e x) :=
    lt_of_lt_of_le h.duration_pos (le_csSup hbdd h.mem_durationSet)
  rw [h.maximalCurveClosed_eq_maximalCurve hbdd hTpos]
  rw [h.maximalCurve_eq_segment_curve hbdd le_rfl hTpos h h.duration_pos]
  exact h.initial

/-- The completed maximal curve stays on the closed physical edge at every time up to and
including the endpoint. -/
theorem maximalCurveClosed_physical (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (sSup (durationSet V e x))) :
    (h.maximalCurveClosed hbdd t).1 ∈ Icc (0 : ℝ) (Γ.length e) := by
  rcases eq_or_lt_of_le ht.2 with hteq | htlt
  · rw [hteq, h.maximalCurveClosed_eq_endpoint hbdd]
    exact h.maximalEndpoint_physical hbdd
  · rw [h.maximalCurveClosed_eq_maximalCurve hbdd htlt]
    exact h.maximalCurve_physical_at hbdd ht.1 htlt

/-- Energy is conserved along the completed maximal curve throughout its closed interval. -/
theorem maximalCurveClosed_hamiltonian_eq_initial (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (sSup (durationSet V e x))) :
    V.hamiltonian e (h.maximalCurveClosed hbdd t).1 (h.maximalCurveClosed hbdd t).2 =
      V.hamiltonian e x.1 x.2 := by
  rcases eq_or_lt_of_le ht.2 with hteq | htlt
  · rw [hteq, h.maximalCurveClosed_eq_endpoint hbdd]
    exact h.maximalEndpoint_hamiltonian_eq_initial hbdd
  · rw [h.maximalCurveClosed_eq_maximalCurve hbdd htlt]
    exact h.maximalCurve_hamiltonian_eq_initial hbdd ht.1 htlt

/-- The completed maximal curve remains in the extension domain throughout its closed interval. -/
theorem maximalCurveClosed_mem_domain (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (sSup (durationSet V e x))) :
    (h.maximalCurveClosed hbdd t).1 ∈ V.domain e :=
  V.closedEdge_subset_domain e (h.maximalCurveClosed_physical hbdd ht)

/-- Strictly before the endpoint, every positive-time point of the completed maximal curve is in
the open edge. -/
theorem maximalCurveClosed_interior (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (sSup (durationSet V e x))) :
    (h.maximalCurveClosed hbdd t).1 ∈ Ioo (0 : ℝ) (Γ.length e) := by
  rw [h.maximalCurveClosed_eq_maximalCurve hbdd ht.2]
  exact h.maximalCurve_interior_at hbdd ht

/-- The completed maximal curve has a one-sided (right) within-derivative at its initial time,
inherited from the original segment. -/
theorem maximalCurveClosed_hasDerivWithinAt_zero (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) :
    HasDerivWithinAt (h.maximalCurveClosed hbdd) (V.edgeVectorField e x)
      (Icc (0 : ℝ) (sSup (durationSet V e x))) 0 := by
  let T : ℝ := sSup (durationSet V e x)
  have hTpos : 0 < T :=
    lt_of_lt_of_le h.duration_pos (le_csSup hbdd h.mem_durationSet)
  have hmin : 0 < min h.duration T := lt_min h.duration_pos hTpos
  have hderiv0 : HasDerivAt h.curve (V.edgeVectorField e x) 0 := by
    have hd := h.integralCurve 0 ⟨le_rfl, h.duration_pos.le⟩
    rwa [h.initial] at hd
  refine (hderiv0.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_)
  · have hset : Ico (0 : ℝ) (min h.duration T) ∈ 𝓝[Icc (0 : ℝ) T] (0 : ℝ) := by
      rw [mem_nhdsWithin]
      refine ⟨Iio (min h.duration T), isOpen_Iio, hmin, ?_⟩
      rintro t ⟨htU, htIcc⟩
      exact ⟨htIcc.1, htU⟩
    filter_upwards [hset] with t ht
    have htT : t < T := lt_of_lt_of_le ht.2 (min_le_right _ _)
    have hth : t < h.duration := lt_of_lt_of_le ht.2 (min_le_left _ _)
    rw [h.maximalCurveClosed_eq_maximalCurve hbdd htT]
    exact h.maximalCurve_eq_segment_curve hbdd ht.1 htT h hth
  · rw [h.maximalCurveClosed_initial hbdd, h.initial]

/-- The completed maximal curve satisfies the concrete Hamiltonian ODE in the one-sided
within-`Icc` sense at every time of its closed interval: two-sided in the interior, one-sided at
both endpoints. -/
theorem maximalCurveClosed_hasDerivWithinAt_Icc (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (sSup (durationSet V e x))) :
    HasDerivWithinAt (h.maximalCurveClosed hbdd)
      (V.edgeVectorField e (h.maximalCurveClosed hbdd t))
      (Icc (0 : ℝ) (sSup (durationSet V e x))) t := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0pos
  · subst h0
    rw [h.maximalCurveClosed_initial hbdd]
    exact h.maximalCurveClosed_hasDerivWithinAt_zero hbdd
  rcases eq_or_lt_of_le ht.2 with hT | hTlt
  · subst hT
    rw [h.maximalCurveClosed_eq_endpoint hbdd]
    exact (h.maximalCurveClosed_hasDerivWithinAt_leftEndpoint hbdd).mono Icc_subset_Iic_self
  · exact (h.maximalCurveClosed_hasDerivAt hbdd ⟨h0pos, hTlt⟩).hasDerivWithinAt

/-- The terminal nonzero boundary covector of a finite regular maximal physical flight. -/
noncomputable def maximalArrivalCovector (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) : Γ.BoundaryCovector := by
  by_cases hleft : (h.maximalEndpoint hbdd).1 = 0
  · exact ⟨(e, false), (h.maximalEndpoint hbdd).2,
      h.maximalEndpoint_momentum_ne_zero hbdd hregular⟩
  · exact ⟨(e, true), (h.maximalEndpoint hbdd).2,
      h.maximalEndpoint_momentum_ne_zero hbdd hregular⟩

@[simp] theorem maximalArrivalCovector_momentum (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    (h.maximalArrivalCovector hbdd hregular).momentum = (h.maximalEndpoint hbdd).2 := by
  by_cases hleft : (h.maximalEndpoint hbdd).1 = 0 <;>
    simp [maximalArrivalCovector, hleft]

/-- The arrival germ of a maximal flight sits on the flight's own edge. -/
@[simp] theorem maximalArrivalCovector_germ_fst (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    (h.maximalArrivalCovector hbdd hregular).germ.1 = e := by
  by_cases hleft : (h.maximalEndpoint hbdd).1 = 0 <;>
    simp [maximalArrivalCovector, hleft]

/-- The coordinate of the arrival germ is the position the maximal flight actually lands at.  This
is the compatibility between the germ selected by `maximalArrivalCovector` and the analytic
endpoint, and it uses that a finite maximal flight lands at `0` or at `length e`. -/
theorem maximalArrivalCovector_coordinate (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    FiniteMetricGraph.EdgeEnd.coordinate Γ (h.maximalArrivalCovector hbdd hregular).germ =
      (h.maximalEndpoint hbdd).1 := by
  by_cases hleft : (h.maximalEndpoint hbdd).1 = 0
  · rw [show (h.maximalArrivalCovector hbdd hregular).germ = (e, false) from by
      simp [maximalArrivalCovector, hleft], Γ.edgeEnd_coordinate_false, hleft]
  · have hright : (h.maximalEndpoint hbdd).1 = Γ.length e :=
      (h.maximalEndpoint_coordinate_eq_zero_or_length hbdd).resolve_left hleft
    rw [show (h.maximalArrivalCovector hbdd hregular).germ = (e, true) from by
      simp [maximalArrivalCovector, hleft], Γ.edgeEnd_coordinate_true, hright]

/-- A finite maximal flight at regular energy arrives in the incoming boundary section. -/
noncomputable def maximalArrivalIncoming (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    Γ.IncomingBoundary (h.maximalArrivalCovector hbdd hregular).germ.vertex := by
  refine ⟨h.maximalArrivalCovector hbdd hregular, rfl, ?_⟩
  by_cases hleft : (h.maximalEndpoint hbdd).1 = 0
  · have hp : (h.maximalEndpoint hbdd).2 < 0 :=
      h.maximalEndpoint_left_momentum_neg hbdd hregular hleft
    simp [maximalArrivalCovector, hleft, FiniteMetricGraph.EdgeEnd.sign, hp]
  · have hright : (h.maximalEndpoint hbdd).1 = Γ.length e :=
      (h.maximalEndpoint_coordinate_eq_zero_or_length hbdd).resolve_left hleft
    have hp : 0 < (h.maximalEndpoint hbdd).2 :=
      h.maximalEndpoint_right_momentum_pos hbdd hregular hright
    simp [maximalArrivalCovector, hleft, FiniteMetricGraph.EdgeEnd.sign, hp]

/-- The restarted flight has the same maximal arrival covector as the original.  This lifts the
endpoint correspondence to the boundary-scattering interface. -/
theorem maximalArrivalCovector_shift_eq (h : V.PhysicalEdgeSegment e x) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < h.duration) (hbdd : BddAbove (durationSet V e x))
    (g : V.PhysicalEdgeSegment e (h.curve s))
    (hreg_g : V.hamiltonian e (h.curve s).1 (h.curve s).2 ∉ V.exceptionalEnergies)
    (hreg_h : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    g.maximalArrivalCovector ((h.bddAbove_durationSet_curve_iff hs0 hs).mpr hbdd) hreg_g =
      h.maximalArrivalCovector hbdd hreg_h := by
  have hend := h.maximalEndpoint_shift_eq hs0 hs hbdd g
  apply FiniteMetricGraph.BoundaryCovector.ext
  · by_cases hleft : (h.maximalEndpoint hbdd).1 = 0
    · have hgl : (g.maximalEndpoint ((h.bddAbove_durationSet_curve_iff hs0 hs).mpr hbdd)).1 = 0 := by
        rw [hend]; exact hleft
      simp only [maximalArrivalCovector, dif_pos hleft, dif_pos hgl]
    · have hgl : ¬ (g.maximalEndpoint ((h.bddAbove_durationSet_curve_iff hs0 hs).mpr hbdd)).1 = 0 := by
        rw [hend]; exact hleft
      simp only [maximalArrivalCovector, dif_neg hleft, dif_neg hgl]
  · rw [maximalArrivalCovector_momentum, maximalArrivalCovector_momentum, hend]

/-- The maximal arrival covector depends only on the edge and initial state. -/
theorem maximalArrivalCovector_indep (h h' : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x))
    (hreg : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies)
    (hreg' : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    h.maximalArrivalCovector hbdd hreg = h'.maximalArrivalCovector hbdd hreg' := by
  have hend := h.maximalEndpoint_indep h' hbdd
  apply FiniteMetricGraph.BoundaryCovector.ext
  · by_cases hleft : (h.maximalEndpoint hbdd).1 = 0
    · have hgl : (h'.maximalEndpoint hbdd).1 = 0 := by rw [← hend]; exact hleft
      simp only [maximalArrivalCovector, dif_pos hleft, dif_pos hgl]
    · have hgl : ¬ (h'.maximalEndpoint hbdd).1 = 0 := by rw [← hend]; exact hleft
      simp only [maximalArrivalCovector, dif_neg hleft, dif_neg hgl]
  · rw [maximalArrivalCovector_momentum, maximalArrivalCovector_momentum, hend]

/-- Transporting a segment along an equality of its base point leaves the maximal arrival covector
unchanged. -/
theorem maximalArrivalCovector_cast {y y' : ℝ × ℝ} (hy : y = y')
    (seg : V.PhysicalEdgeSegment e y) (hb : BddAbove (durationSet V e y))
    (hb' : BddAbove (durationSet V e y'))
    (hr : V.hamiltonian e y.1 y.2 ∉ V.exceptionalEnergies)
    (hr' : V.hamiltonian e y'.1 y'.2 ∉ V.exceptionalEnergies) :
    (hy ▸ seg).maximalArrivalCovector hb' hr' = seg.maximalArrivalCovector hb hr := by
  subst hy; rfl

/-- The flight restarted at the maximal-flight point `maximalCurve h s` has the same maximal
arrival covector as the original.  Flow-friendly form of `maximalArrivalCovector_shift_eq`. -/
theorem maximalArrivalCovector_restart_eq (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x)) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < sSup (durationSet V e x))
    (g : V.PhysicalEdgeSegment e (h.maximalCurve hbdd s))
    (hg_bdd : BddAbove (durationSet V e (h.maximalCurve hbdd s)))
    (hreg_g : V.hamiltonian e (h.maximalCurve hbdd s).1 (h.maximalCurve hbdd s).2 ∉
      V.exceptionalEnergies)
    (hreg_h : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    g.maximalArrivalCovector hg_bdd hreg_g = h.maximalArrivalCovector hbdd hreg_h := by
  obtain ⟨K, hK⟩ := h.exists_segment_duration_gt_of_lt_sSup hbdd hs
  have hKs : h.maximalCurve hbdd s = K.curve s := h.maximalCurve_eq_segment_curve hbdd hs0 hs K hK
  have hsK : s < K.duration := hK
  have hb'' : BddAbove (durationSet V e (K.curve s)) := by rw [← hKs]; exact hg_bdd
  have hreg_Kcurve : V.hamiltonian e (K.curve s).1 (K.curve s).2 ∉ V.exceptionalEnergies := by
    rw [← hKs]; exact hreg_g
  have hshift := K.maximalArrivalCovector_shift_eq hs0 hsK hbdd (hKs ▸ g) hreg_Kcurve hreg_h
  rw [← maximalArrivalCovector_cast hKs g hg_bdd hb'' hreg_g hreg_Kcurve,
    Subsingleton.elim hb'' ((K.bddAbove_durationSet_curve_iff hs0 hsK).mpr hbdd), hshift]
  exact K.maximalArrivalCovector_indep h hbdd hreg_h hreg_h

/-- Boundary energy at a regular maximal arrival is the original mechanical energy. -/
theorem maximalArrival_boundaryEnergy_eq_initial (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (durationSet V e x))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies) :
    V.boundaryEnergy (h.maximalArrivalCovector hbdd hregular) = V.hamiltonian e x.1 x.2 := by
  by_cases hleft : (h.maximalEndpoint hbdd).1 = 0
  · have hend := V.endpoint_hamiltonian (η := (e, false)) (h.maximalEndpoint hbdd).2
    have hend' : V.hamiltonian e 0 (h.maximalEndpoint hbdd).2 =
        (h.maximalEndpoint hbdd).2 ^ 2 / 2 + V.vertexValue (Γ.endpoint e false) := by
      simpa [FiniteMetricGraph.EdgeEnd.coordinate, FiniteMetricGraph.EdgeEnd.vertex] using hend
    have henergy := h.maximalEndpoint_hamiltonian_eq_initial hbdd
    rw [hleft] at henergy
    simpa [boundaryEnergy, maximalArrivalCovector, hleft,
      FiniteMetricGraph.EdgeEnd.coordinate, FiniteMetricGraph.EdgeEnd.vertex] using hend'.symm.trans henergy
  · have hright : (h.maximalEndpoint hbdd).1 = Γ.length e :=
      (h.maximalEndpoint_coordinate_eq_zero_or_length hbdd).resolve_left hleft
    have hLne : Γ.length e ≠ 0 := ne_of_gt (Γ.length_pos e)
    have hend := V.endpoint_hamiltonian (η := (e, true)) (h.maximalEndpoint hbdd).2
    have henergy := h.maximalEndpoint_hamiltonian_eq_initial hbdd
    rw [hright] at henergy
    simpa [boundaryEnergy, maximalArrivalCovector, hleft, hright, hLne,
      FiniteMetricGraph.EdgeEnd.coordinate, FiniteMetricGraph.EdgeEnd.vertex] using hend.symm.trans henergy

end PhysicalEdgeSegment

/-- Every interior state starts a nontrivial physical edge segment. -/
theorem exists_physicalEdgeSegment_from_interior {e : Γ.Edge} {x : ℝ × ℝ}
    (hx : x.1 ∈ Ioo (0 : ℝ) (Γ.length e)) :
    ∃ _ : V.PhysicalEdgeSegment e x, True := by
  have hxdom : x.1 ∈ V.domain e := V.closedEdge_subset_domain e ⟨hx.1.le, hx.2.le⟩
  obtain ⟨γ, hγ0, ε, hε, hγ⟩ :=
    V.exists_local_edge_integralCurve_in_openCylinder hxdom hx 0
  refine ⟨{
    duration := ε / 2
    duration_pos := by linarith
    curve := γ
    initial := hγ0
    initial_physical := ⟨hx.1.le, hx.2.le⟩
    physical := ?_
    in_domain := ?_
    integralCurve := ?_
    interior_after_initial := ?_ }, trivial⟩
  · intro t ht
    exact ⟨(hγ t (by constructor <;> linarith [ht.1, ht.2])).1.1.le,
      (hγ t (by constructor <;> linarith [ht.1, ht.2])).1.2.le⟩
  · intro t ht
    exact V.closedEdge_subset_domain e
      ⟨(hγ t (by constructor <;> linarith [ht.1, ht.2])).1.1.le,
        (hγ t (by constructor <;> linarith [ht.1, ht.2])).1.2.le⟩
  · intro t ht
    exact (hγ t (by constructor <;> linarith [ht.1, ht.2])).2
  · intro t ht
    exact (hγ t (by constructor <;> linarith [ht.1, ht.2])).1

/-- Every outgoing boundary covector starts a physical edge segment with a certified ODE
derivative at the impact instant. -/
theorem exists_physicalEdgeSegment_from_outgoingBoundary {v : Γ.Vertex}
    (α : Γ.OutgoingBoundary v) :
    ∃ _ : V.PhysicalEdgeSegment α.1.germ.1
      (FiniteMetricGraph.EdgeEnd.coordinate Γ α.1.germ, α.1.momentum), True := by
  obtain ⟨γ, hγ0, hγderiv0, ε, hε, hγ⟩ :=
    V.exists_local_edge_integralCurve_from_outgoingBoundary α
  refine ⟨{
    duration := ε / 2
    duration_pos := by linarith
    curve := γ
    initial := hγ0
    initial_physical := FiniteMetricGraph.edgeEnd_coordinate_mem_closedEdge Γ α.1.germ
    physical := ?_
    in_domain := ?_
    integralCurve := ?_
    interior_after_initial := ?_ }, trivial⟩
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | htpos
    · simpa [hγ0] using
        (FiniteMetricGraph.edgeEnd_coordinate_mem_closedEdge Γ α.1.germ)
    · exact ⟨(hγ t (by constructor <;> linarith [ht.2])).1.1.le,
        (hγ t (by constructor <;> linarith [ht.2])).1.2.le⟩
  · intro t ht
    apply V.closedEdge_subset_domain α.1.germ.1
    rcases eq_or_lt_of_le ht.1 with rfl | htpos
    · simpa [hγ0] using
        (FiniteMetricGraph.edgeEnd_coordinate_mem_closedEdge Γ α.1.germ)
    · exact ⟨(hγ t (by constructor <;> linarith [ht.2])).1.1.le,
        (hγ t (by constructor <;> linarith [ht.2])).1.2.le⟩
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | htpos
    · exact hγderiv0
    · exact (hγ t (by constructor <;> linarith [ht.2])).2
  · intro t ht
    exact (hγ t (by constructor <;> linarith [ht.1, ht.2])).1

/-- One deterministic scattering step after a finite regular maximal flight starts a new
physical segment on the selected outgoing edge. -/
theorem exists_physicalEdgeSegment_after_maximalArrival {e : Γ.Edge} {x : ℝ × ℝ}
    (h : V.PhysicalEdgeSegment e x) (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V e x))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies)
    (S : BorelEnergyPreservingScattering V) :
    ∃ k : V.PhysicalEdgeSegment
        (S.map (h.maximalArrivalIncoming hbdd hregular).1.germ.vertex
          (h.maximalArrivalIncoming hbdd hregular)).1.germ.1
        (FiniteMetricGraph.EdgeEnd.coordinate Γ
          (S.map (h.maximalArrivalIncoming hbdd hregular).1.germ.vertex
            (h.maximalArrivalIncoming hbdd hregular)).1.germ,
          (S.map (h.maximalArrivalIncoming hbdd hregular).1.germ.vertex
            (h.maximalArrivalIncoming hbdd hregular)).1.momentum), True := by
  exact V.exists_physicalEdgeSegment_from_outgoingBoundary
    (S.map (h.maximalArrivalIncoming hbdd hregular).1.germ.vertex
      (h.maximalArrivalIncoming hbdd hregular))

/-- Scattering after a finite regular maximal flight preserves its initial mechanical energy. -/
theorem scattered_maximalArrival_energy_eq_initial {e : Γ.Edge} {x : ℝ × ℝ}
    (h : V.PhysicalEdgeSegment e x) (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V e x))
    (hregular : V.hamiltonian e x.1 x.2 ∉ V.exceptionalEnergies)
    (S : BorelEnergyPreservingScattering V) :
    V.boundaryEnergy
      (S.map (h.maximalArrivalIncoming hbdd hregular).1.germ.vertex
        (h.maximalArrivalIncoming hbdd hregular)).1 =
      V.hamiltonian e x.1 x.2 := by
  rw [S.preserves_energy]
  exact h.maximalArrival_boundaryEnergy_eq_initial hbdd hregular

end MechanicalPotential
end HamiltonianMetricGraphs
