/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalComponentResolved

/-!
# Each component of `R(Γ, F)` is an interval or a circle

The paper asserts that each component `R_i` of the resolved space is, in its length metric,
isometric to an interval `[0, L_i]` or a circle `ℝ / L_i ℤ`, and that `ι_i` is that isometry
followed by the natural map `R → Γ`.  This file proves the corresponding statements about the
parametrization `ι_i = compMap F i` of `UniversalComponentResolved.lean`:

* **interval** (`compMap_injOn_interval`): `ι_i` is injective on `Λ_i \ Z_i = [0, L_i] \ Z_i`;
* **circle** (`compMap_add_compLen`, `compMap_injOn_circle`): `ι_i` and `o_i` are `L_i`-periodic,
  and `ι_i` is injective on `[0, L_i) \ Z_i`;
* **onto the component** (`compMap_mem_comp`, `exists_compMap_eq_of_comp`): the points
  `ι_i(u)`, `u ∈ Λ_i \ Z_i`, are exactly the edge-interior points of the edges of `R_i`;
* on each segment `ι_i` is an isometry onto an open edge (`compMap_of_mem_segment`).

Together: `ι_i` identifies `Λ_i \ Z_i` (respectively `(ℝ \ Z_i) / L_i ℤ`) with the edge-interior
points of `R_i`, piecewise isometrically, the pieces being glued at the points of `Z_i` exactly as
the ends are glued in `R(Γ, F)` (`otherEnd_germSeq_vertex`, `routeGerm_germSeq`).

The combinatorial input is that the routing orbit of the base germ meets each edge of the component
once per period (`germSeq_edge_ne_interval`, `germSeq_edge_ne_circle`): if an orbit met an edge in
both directions it would contain a fold (`exists_fold_of_otherEnd`).
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph RoutingLaw

variable {Γ : FiniteMetricGraph} (F : RoutingLaw Γ)

/-! ### Orbits meeting an edge twice -/

section Orbit

variable (β : Γ.EdgeEnd)

theorem otherEnd_germSeq_shift {a b : ℤ} (h : otherEnd (germSeq F β a) = germSeq F β b) (n : ℤ) :
    otherEnd (germSeq F β (a + n)) = germSeq F β (b - n) := by
  rw [germSeq_add, F.otherEnd_zpow, h, ← germSeq_add, sub_eq_add_neg]

/-- **An orbit which meets an edge in both directions contains a fold** half-way. -/
theorem exists_fold_of_otherEnd {a b : ℤ} (h : otherEnd (germSeq F β a) = germSeq F β b) :
    ∃ m : ℤ, b - a = 2 * m + 1 ∧ F.routeGerm (germSeq F β (a + m)) = germSeq F β (a + m) := by
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (b - a)
  · exfalso
    have := otherEnd_germSeq_shift F β h m
    rw [show b - m = a + m by omega] at this
    have h2 : (otherEnd (germSeq F β (a + m))).2 = (germSeq F β (a + m)).2 := by rw [this]
    simp [otherEnd] at h2
  · refine ⟨m, hm, ?_⟩
    have := otherEnd_germSeq_shift F β h m
    rw [show b - m = a + m + 1 by omega] at this
    rw [routeGerm_germSeq, ← this, otherEnd_otherEnd]

/-- A repetition in the orbit is a period of the whole orbit. -/
theorem germSeq_period_of_eq {a b : ℤ} (h : germSeq F β b = germSeq F β a) (k : ℤ) :
    germSeq F β (k + (b - a)) = germSeq F β k := by
  have h1 : germSeq F β (k + (b - a)) = (F.stepPerm ^ (k - a)) (germSeq F β b) := by
    rw [show k + (b - a) = b + (k - a) by ring, germSeq_add]
  rw [h1, h, ← germSeq_add, show a + (k - a) = k by ring]

end Orbit

/-- A fold anywhere in the orbit of the base germ makes the component an interval. -/
theorem isIntervalComp_of_fold {i : Fin F.compCount} {k : ℤ}
    (hk : F.routeGerm (germSeq F (compBase F i) k) = germSeq F (compBase F i) k) :
    IsIntervalComp F i :=
  ⟨germSeq F (compBase F i) k, by rw [germSeq, F.compOf_stepPerm_zpow, compOf_compBase], hk⟩

/-! ### Each edge is met once -/

/-- **In an interval component the edges of the segments `0, …, K - 1` are distinct.** -/
theorem germSeq_edge_ne_interval {i : Fin F.compCount} (h : IsIntervalComp F i) {a b : ℤ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ compFoldIdx F i h) :
    (germSeq F (compBase F i) a).1 ≠ (germSeq F (compBase F i) b).1 := by
  intro he
  rcases edgeEnd_eq_or_eq_otherEnd he.symm with hg | hg
  · -- a period shorter than the interval would bring the first fold inside it
    have hp := germSeq_period_of_eq F (compBase F i) hg (-1)
    have hf := fold_neg_one F h
    rw [← hp] at hf
    have hidx : (-1 + (b - a)).toNat < compFoldIdx F i h := by omega
    have := not_fold_lt_compFoldIdx F h hidx
    rw [show (((-1 + (b - a)).toNat : ℕ) : ℤ) = -1 + (b - a) by omega] at this
    exact this hf
  · obtain ⟨m, hm, hf⟩ := exists_fold_of_otherEnd F _ hg.symm
    have hidx : (a + m).toNat < compFoldIdx F i h := by omega
    have := not_fold_lt_compFoldIdx F h hidx
    rw [show (((a + m).toNat : ℕ) : ℤ) = a + m by omega] at this
    exact this hf

/-- **In a circle component the edges of one period are distinct.** -/
theorem germSeq_edge_ne_circle {i : Fin F.compCount} (h : ¬ IsIntervalComp F i) {a b : ℤ}
    (ha : 0 ≤ a) (hab : a < b)
    (hb : b < Function.minimalPeriod F.stepPerm (compBase F i)) :
    (germSeq F (compBase F i) a).1 ≠ (germSeq F (compBase F i) b).1 := by
  intro he
  rcases edgeEnd_eq_or_eq_otherEnd he.symm with hg | hg
  · have hp := germSeq_period_of_eq F (compBase F i) hg 0
    rw [zero_add, germSeq_zero, germSeq] at hp
    have hper : Function.IsPeriodicPt F.stepPerm (b - a).toNat (compBase F i) := by
      change (⇑F.stepPerm)^[(b - a).toNat] (compBase F i) = compBase F i
      rw [← Equiv.Perm.coe_pow, ← zpow_natCast, show (((b - a).toNat : ℕ) : ℤ) = b - a by omega]
      exact hp
    have := hper.minimalPeriod_le (by omega)
    omega
  · obtain ⟨m, -, hf⟩ := exists_fold_of_otherEnd F _ hg.symm
    exact h (isIntervalComp_of_fold F hf)

/-! ### Periodicity of a circle -/

theorem germSeq_add_period (β : Γ.EdgeEnd) (k : ℤ) :
    germSeq F β (k + Function.minimalPeriod F.stepPerm β) = germSeq F β k := by
  have hβ : germSeq F β (Function.minimalPeriod F.stepPerm β) = germSeq F β 0 := by
    rw [germSeq, germSeq_zero, zpow_natCast, Equiv.Perm.coe_pow]
    exact Function.iterate_minimalPeriod
  have := germSeq_period_of_eq F β hβ k
  rwa [sub_zero] at this

section Circle

variable {F} {i : Fin F.compCount} (h : ¬ IsIntervalComp F i)
include h

theorem compLen_of_circle : compLen F i =
    posSeq F (compBase F i) (Function.minimalPeriod F.stepPerm (compBase F i)) := by
  rw [compLen, dif_neg h]

theorem posSeq_add_period (k : ℤ) :
    posSeq F (compBase F i) (k + Function.minimalPeriod F.stepPerm (compBase F i)) =
      posSeq F (compBase F i) k + compLen F i := by
  have hc := int_const_of_succ (f := fun n => posSeq F (compBase F i)
      (n + Function.minimalPeriod F.stepPerm (compBase F i)) - posSeq F (compBase F i) n)
    (fun n => by
      rw [show n + 1 + (Function.minimalPeriod F.stepPerm (compBase F i) : ℤ) =
        n + Function.minimalPeriod F.stepPerm (compBase F i) + 1 by ring, posSeq_succ,
        posSeq_succ, segLen, segLen, germSeq_add_period F _]
      ring) k 0
  simp only [zero_add, posSeq_zero, sub_zero] at hc
  rw [compLen_of_circle h]
  linarith

theorem segIdx_add_compLen (y : ℝ) :
    segIdx F (compBase F i) (y + compLen F i) =
      segIdx F (compBase F i) y + Function.minimalPeriod F.stepPerm (compBase F i) := by
  have hs := segIdx_spec F (compBase F i) y
  apply segIdx_eq
  rw [posSeq_add_period h, show segIdx F (compBase F i) y +
    (Function.minimalPeriod F.stepPerm (compBase F i) : ℤ) + 1 =
      segIdx F (compBase F i) y + 1 + Function.minimalPeriod F.stepPerm (compBase F i) by ring,
    posSeq_add_period h]
  constructor <;> linarith [hs.1, hs.2]

/-- **A circle component is `L_i`-periodic**: `ι_i` and `o_i` factor through `ℝ / L_i ℤ`. -/
theorem compMap_add_compLen (u : ℝ) :
    compMap F i (u + compLen F i) = compMap F i u ∧
      compSign F i (u + compLen F i) = compSign F i u := by
  refine ⟨?_, ?_⟩
  · rw [compMap, unroll, unroll, segIdx_add_compLen h, germSeq_add_period F _,
      show segIdx F (compBase F i) u + (Function.minimalPeriod F.stepPerm (compBase F i) : ℤ) + 1
        = segIdx F (compBase F i) u + 1 + Function.minimalPeriod F.stepPerm (compBase F i) by ring,
      posSeq_add_period h, posSeq_add_period h]
    by_cases hu : u = posSeq F (compBase F i) (segIdx F (compBase F i) u)
    · rw [if_pos (by rw [← hu]), if_pos hu]
    · rw [if_neg (fun h' => hu (by linarith)), if_neg hu]
      congr 1
      ring
  · change unrollSign F (compBase F i) (u + compLen F i) = unrollSign F (compBase F i) u
    rw [unrollSign, unrollSign, segIdx_add_compLen h, germSeq_add_period F _]

end Circle

/-! ### Injectivity -/

/-- `ι_i` on an open segment, as an injective function of the segment index and the parameter. -/
theorem compMap_eq_compMap_of_segments {i : Fin F.compCount} {k k' : ℤ} {u u' : ℝ}
    (hu : u ∈ Ioo (posSeq F (compBase F i) k) (posSeq F (compBase F i) (k + 1)))
    (hu' : u' ∈ Ioo (posSeq F (compBase F i) k') (posSeq F (compBase F i) (k' + 1)))
    (heq : compMap F i u = compMap F i u') (hk : k = k') : u = u' := by
  subst hk
  rw [compMap, unroll_of_mem_Ioo F _ hu, unroll_of_mem_Ioo F _ hu'] at heq
  injection heq with _ hq
  have hs := Γ.edgeEnd_sign_ne_zero (germSeq F (compBase F i) k)
  have : EdgeEnd.sign Γ (germSeq F (compBase F i) k) * (u - u') = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hs
  · linarith

theorem edge_compMap_of_mem {i : Fin F.compCount} {k : ℤ} {u : ℝ}
    (hu : u ∈ Ioo (posSeq F (compBase F i) k) (posSeq F (compBase F i) (k + 1))) :
    ∃ q, compMap F i u = GraphPoint.interior (germSeq F (compBase F i) k).1 q :=
  ⟨_, by rw [compMap, unroll_of_mem_Ioo F _ hu]⟩

theorem segIdx_mem_of_not_glued {β : Γ.EdgeEnd} {u : ℝ} (hu : u ∉ gluedSet F β) :
    u ∈ Ioo (posSeq F β (segIdx F β u)) (posSeq F β (segIdx F β u + 1)) :=
  seg_mem_Ioo_of_not_mem F β hu

/-- **For an interval component, `ι_i` is injective on `Λ_i \ Z_i`.** -/
theorem compMap_injOn_interval {i : Fin F.compCount} (h : IsIntervalComp F i) :
    InjOn (compMap F i) (compDomain F i \ compVertexSet F i) := by
  intro u hu u' hu' heq
  have hg : ∀ {v}, v ∈ compDomain F i \ compVertexSet F i → v ∉ gluedSet F (compBase F i) :=
    fun hv hg => hv.2 ((mem_compVertexSet_iff F).mpr ⟨hv.1, hg⟩)
  have hrange : ∀ {v}, v ∈ compDomain F i \ compVertexSet F i →
      0 ≤ segIdx F (compBase F i) v ∧ segIdx F (compBase F i) v ≤ compFoldIdx F i h := by
    intro v hv
    have hs := segIdx_mem_of_not_glued F (hg hv)
    have hd := hv.1
    rw [compDomain_of_interval F h] at hd
    have hvL : v < compLen F i := lt_of_le_of_ne hd.2 (fun he => hg hv
      ⟨_, by rw [he, compLen_eq_posSeq h]⟩)
    rw [compLen_eq_posSeq h] at hvL
    have h1 : (0 : ℤ) < segIdx F (compBase F i) v + 1 := by
      have := lt_of_le_of_lt hd.1 hs.2
      rw [← posSeq_zero F (compBase F i)] at this
      exact (posSeq_lt_iff F _).mp this
    have h2 : segIdx F (compBase F i) v < (compFoldIdx F i h : ℤ) + 1 :=
      (posSeq_lt_iff F _).mp (lt_trans hs.1 hvL)
    omega
  have hs := segIdx_mem_of_not_glued F (hg hu)
  have hs' := segIdx_mem_of_not_glued F (hg hu')
  refine compMap_eq_compMap_of_segments F hs hs' heq ?_
  obtain ⟨q, hq⟩ := edge_compMap_of_mem F hs
  obtain ⟨q', hq'⟩ := edge_compMap_of_mem F hs'
  rw [hq, hq'] at heq
  injection heq with he _
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact germSeq_edge_ne_interval F h (hrange hu).1 hlt (hrange hu').2 he
  · exact germSeq_edge_ne_interval F h (hrange hu').1 hlt (hrange hu).2 he.symm

/-- **For a circle component, `ι_i` is injective on `[0, L_i) \ Z_i`.** -/
theorem compMap_injOn_circle {i : Fin F.compCount} (h : ¬ IsIntervalComp F i) :
    InjOn (compMap F i) (Ico 0 (compLen F i) \ compVertexSet F i) := by
  intro u hu u' hu' heq
  have hg : ∀ {v}, v ∈ Ico 0 (compLen F i) \ compVertexSet F i →
      v ∉ gluedSet F (compBase F i) := fun hv hg => hv.2 ((mem_compVertexSet_iff F).mpr
        ⟨by rw [compDomain_of_circle F h]; trivial, hg⟩)
  have hrange : ∀ {v}, v ∈ Ico 0 (compLen F i) \ compVertexSet F i →
      0 ≤ segIdx F (compBase F i) v ∧
        segIdx F (compBase F i) v < Function.minimalPeriod F.stepPerm (compBase F i) := by
    intro v hv
    have hs := segIdx_mem_of_not_glued F (hg hv)
    have hd := hv.1
    rw [compLen_of_circle h] at hd
    have h1 : (0 : ℤ) < segIdx F (compBase F i) v + 1 := by
      have := lt_of_le_of_lt hd.1 hs.2
      rw [← posSeq_zero F (compBase F i)] at this
      exact (posSeq_lt_iff F _).mp this
    have h2 := (posSeq_lt_iff F _).mp (lt_of_lt_of_le hs.1 hd.2.le |>.trans_le le_rfl)
    omega
  have hs := segIdx_mem_of_not_glued F (hg hu)
  have hs' := segIdx_mem_of_not_glued F (hg hu')
  refine compMap_eq_compMap_of_segments F hs hs' heq ?_
  obtain ⟨q, hq⟩ := edge_compMap_of_mem F hs
  obtain ⟨q', hq'⟩ := edge_compMap_of_mem F hs'
  rw [hq, hq'] at heq
  injection heq with he _
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact germSeq_edge_ne_circle F h (hrange hu).1 hlt (hrange hu').2 he
  · exact germSeq_edge_ne_circle F h (hrange hu').1 hlt (hrange hu).2 he.symm

/-! ### The image is the component -/

/-- **`ι_i` lands in the component `R_i`**: an edge-interior point `ι_i(u)` lies on an edge of
`R_i`. -/
theorem compMap_mem_comp {i : Fin F.compCount} {u : ℝ} {e : Γ.Edge} {q : ℝ}
    (hu : compMap F i u = GraphPoint.interior e q) : F.compOf (e, true) = F.compEnum i := by
  by_cases hg : u ∈ gluedSet F (compBase F i)
  · obtain ⟨k, rfl⟩ := hg
    rw [compMap, unroll_posSeq] at hu
    cases hu
  · rw [compMap, unroll_of_mem_Ioo F _ (seg_mem_Ioo_of_not_mem F _ hg)] at hu
    injection hu with he _
    rw [← compOf_compBase F i, ← he]
    have h1 := F.compOf_stepPerm_zpow (segIdx F (compBase F i) u) (compBase F i)
    change F.compOf (germSeq F (compBase F i) (segIdx F (compBase F i) u)) = _ at h1
    generalize germSeq F (compBase F i) (segIdx F (compBase F i) u) = g at h1 ⊢
    obtain ⟨e', b⟩ := g
    cases b
    · rw [← h1]; exact F.compOf_otherEnd (e', false)
    · exact h1

/-- An edge-interior point `ι_i(u)` lies in the open edge. -/
theorem compMap_coord_mem {i : Fin F.compCount} {u : ℝ} {e : Γ.Edge} {q : ℝ}
    (hu : compMap F i u = GraphPoint.interior e q) : q ∈ Ioo (0 : ℝ) (Γ.length e) := by
  by_cases hg : u ∈ gluedSet F (compBase F i)
  · obtain ⟨k, rfl⟩ := hg
    rw [compMap, unroll_posSeq] at hu
    cases hu
  · have hs := seg_mem_Ioo_of_not_mem F _ hg
    rw [compMap, unroll_of_mem_Ioo F _ hs] at hu
    injection hu with he hq
    rw [← he, ← hq]
    exact unroll_coord_mem F _ hs

/-- **Each component `R_i` of `R(Γ, F)` is an interval or a circle.**  `L_i > 0`; the points
`ι_i(u)`, `u ∈ Λ_i \ Z_i`, are exactly the edge-interior points of the edges of `R_i`; `ι_i` is an
isometry onto an open edge on each component of `Λ_i \ Z_i` (`compMap_of_mem_segment`); and either

* `R_i` is an interval: `Λ_i = [0, L_i]`, the endpoints `0, L_i` are in `Z_i`, and `ι_i` is
  injective on `Λ_i \ Z_i`; or
* `R_i` is a circle: `Λ_i = ℝ`, `ι_i` and `o_i` are `L_i`-periodic, and `ι_i` is injective on
  `[0, L_i) \ Z_i`. -/
theorem component_interval_or_circle (i : Fin F.compCount) :
    0 < compLen F i ∧
    (∀ (e : Γ.Edge) (q : ℝ), F.compOf (e, true) = F.compEnum i → q ∈ Ioo (0 : ℝ) (Γ.length e) →
      ∃ u ∈ compDomain F i \ compVertexSet F i, compMap F i u = GraphPoint.interior e q) ∧
    (∀ (u : ℝ) (e : Γ.Edge) (q : ℝ), compMap F i u = GraphPoint.interior e q →
      F.compOf (e, true) = F.compEnum i ∧ q ∈ Ioo (0 : ℝ) (Γ.length e)) ∧
    ((IsIntervalComp F i ∧ compDomain F i = Icc 0 (compLen F i) ∧
        0 ∈ compVertexSet F i ∧ compLen F i ∈ compVertexSet F i ∧
        InjOn (compMap F i) (compDomain F i \ compVertexSet F i)) ∨
      (¬ IsIntervalComp F i ∧ compDomain F i = univ ∧
        (∀ u, compMap F i (u + compLen F i) = compMap F i u ∧
          compSign F i (u + compLen F i) = compSign F i u) ∧
        InjOn (compMap F i) (Ico 0 (compLen F i) \ compVertexSet F i))) := by
  refine ⟨compLen_pos F i, fun e q he hq => ?_, fun u e q hu =>
    ⟨compMap_mem_comp F hu, compMap_coord_mem F hu⟩, ?_⟩
  · obtain ⟨u, hu, hZ, hval⟩ := exists_compMap_eq_of_comp F i he hq
    exact ⟨u, ⟨hu, hZ⟩, hval⟩
  · by_cases h : IsIntervalComp F i
    · exact Or.inl ⟨h, compDomain_of_interval F h, (endpoints_mem_compVertexSet F h).1,
        (endpoints_mem_compVertexSet F h).2, compMap_injOn_interval F h⟩
    · exact Or.inr ⟨h, compDomain_of_circle F h, compMap_add_compLen h,
        compMap_injOn_circle F h⟩

end HamiltonianMetricGraphs
