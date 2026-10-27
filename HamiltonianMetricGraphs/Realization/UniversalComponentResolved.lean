/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalComponentOrbit

/-!
# The components of the resolved space `R(Γ, F)` and the maps `ι_i`

The resolved space `R = R(Γ, F)` of Sec. IX.F is obtained from `⊔_e [0, ℓ_e]` by identifying the
endpoint of `η` with that of `F(η)` whenever `F(η) ≠ η`.  This file describes its components
combinatorially and constructs the data of the paper for each of them.

## Components

A particle in `R` moving towards the end `η` continues, through the glued point, along the edge of
`F(η)` towards the opposite end `stepPerm η = otherEnd (F η)`; moving the other way it follows the
orbit of `otherEnd η`.  The **component** of an edge-end is therefore its class for the relation
`SameComp`: `η'` lies in the step orbit of `η` or of `otherEnd η`.  The components are the
elements of the finite quotient `RoutingLaw.Comp F`, enumerated as `R_1, …, R_m` by
`compEnum : Fin m ≃ Comp F` (`m = compCount F`; the Lean index `i : Fin m` is the paper's `i + 1`).

A component is an **interval** (`IsIntervalComp`) if it contains an end fixed by `F` — the
reflecting endpoints — and a **circle** otherwise.

## The data of the paper

For each component `i` we fix a base germ (`compBase`) and unroll its orbit along the line
(`unroll`, `UniversalComponentOrbit.lean`):

* interval: the base germ is `stepPerm φ` for an `F`-fixed end `φ`, so the unrolling starts at the
  endpoint of `φ` (`u = 0`) and the next `F`-fixed end is reached at `u = L_i` (`compLen`); the
  unrolling is symmetric about both (`compMap_reflect_zero`, `compMap_reflect_len`);
* circle: the base germ is any germ of the component and `L_i` is the length of one period of its
  orbit.

Then `Λ_i = [0, L_i]` resp. `ℝ` (`compDomain`), `ι_i = unroll` (`compMap`), `o_i = unrollSign`
(`compSign`), `Z_i = ι_i⁻¹(𝒱) ∩ Λ_i` (`compVertexSet`).  The paper's statements about these data
are proved here: `Z_i` is discrete and contains the endpoints of an interval
(`compVertexSet_discrete`, `zero_mem_compVertexSet`, `len_mem_compVertexSet`), on each component of
`Λ_i \ Z_i` the map `ι_i` is an isometry onto an open edge with `q = const + o_i(u) u` and locally
constant `o_i = ±1` (`compMap_of_mem_segment`), and every edge-interior point is `ι_i(u)` for some
`i` and `u ∈ Λ_i \ Z_i` (`exists_compMap_eq_interior`).
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph

variable {Γ : FiniteMetricGraph}

namespace RoutingLaw

variable (F : RoutingLaw Γ)

/-! ### The components -/

/-- Two edge-ends lie in the same component of `R(Γ, F)`: the second is in the step orbit of the
first or of its opposite end. -/
def SameComp (η η' : Γ.EdgeEnd) : Prop :=
  (∃ k : ℤ, (F.stepPerm ^ k) η = η') ∨ ∃ k : ℤ, (F.stepPerm ^ k) (otherEnd η) = η'

theorem sameComp_equivalence : Equivalence F.SameComp where
  refl η := Or.inl ⟨0, by simp⟩
  symm := by
    rintro η η' (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact Or.inl ⟨-k, by rw [← Equiv.Perm.mul_apply, ← zpow_add]; simp⟩
    · refine Or.inr ⟨k, ?_⟩
      rw [F.otherEnd_zpow, otherEnd_otherEnd, ← Equiv.Perm.mul_apply, ← zpow_add]
      simp
  trans := by
    rintro η η' η'' (⟨a, rfl⟩ | ⟨a, rfl⟩) (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact Or.inl ⟨b + a, by rw [zpow_add, Equiv.Perm.mul_apply]⟩
    · refine Or.inr ⟨b + -a, ?_⟩
      rw [F.otherEnd_zpow, zpow_add, Equiv.Perm.mul_apply]
    · exact Or.inr ⟨b + a, by rw [zpow_add, Equiv.Perm.mul_apply]⟩
    · refine Or.inl ⟨b + -a, ?_⟩
      rw [F.otherEnd_zpow, otherEnd_otherEnd, zpow_add, Equiv.Perm.mul_apply]

/-- The setoid of the components of `R(Γ, F)` on the edge-ends. -/
def compSetoid : Setoid Γ.EdgeEnd := ⟨F.SameComp, F.sameComp_equivalence⟩

/-- **The components of the resolved space `R(Γ, F)`.** -/
def Comp : Type := Quotient F.compSetoid

noncomputable instance : Fintype F.Comp := by
  classical
  exact Quotient.fintype _

/-- The number `m` of components of `R(Γ, F)`. -/
noncomputable def compCount : ℕ := Fintype.card F.Comp

/-- **The enumeration `R_1, …, R_m` of the components** (the Lean index `i` is the paper's
`i + 1`). -/
noncomputable def compEnum : Fin F.compCount ≃ F.Comp := (Fintype.equivFin F.Comp).symm

/-- The component of an edge-end. -/
def compOf (η : Γ.EdgeEnd) : F.Comp := Quotient.mk F.compSetoid η

theorem compOf_eq_iff {η η' : Γ.EdgeEnd} : F.compOf η = F.compOf η' ↔ F.SameComp η η' :=
  Quotient.eq (r := F.compSetoid)

theorem compOf_otherEnd (η : Γ.EdgeEnd) : F.compOf (otherEnd η) = F.compOf η :=
  (F.compOf_eq_iff).mpr (F.sameComp_equivalence.symm (Or.inr ⟨0, by simp⟩))

theorem compOf_stepPerm_zpow (k : ℤ) (η : Γ.EdgeEnd) :
    F.compOf ((F.stepPerm ^ k) η) = F.compOf η :=
  (F.compOf_eq_iff).mpr (F.sameComp_equivalence.symm (Or.inl ⟨k, rfl⟩))

end RoutingLaw

open RoutingLaw

variable (F : RoutingLaw Γ)

/-! ### Interval and circle components -/

/-- **The component `i` is an interval**: it contains an end fixed by `F`. -/
def IsIntervalComp (i : Fin F.compCount) : Prop :=
  ∃ φ : Γ.EdgeEnd, F.compOf φ = F.compEnum i ∧ F.routeGerm φ = φ

open Classical in
/-- **The base germ of component `i`**: for an interval, the step of a chosen `F`-fixed end `φ`,
so that the unrolled orbit starts at the endpoint of `φ`; for a circle, a chosen germ of the
component. -/
noncomputable def compBase (i : Fin F.compCount) : Γ.EdgeEnd :=
  if h : IsIntervalComp F i then F.stepPerm h.choose else (F.compEnum i).out

theorem compOf_compBase (i : Fin F.compCount) : F.compOf (compBase F i) = F.compEnum i := by
  unfold compBase
  split_ifs with h
  · have h1 := F.compOf_stepPerm_zpow 1 h.choose
    rw [zpow_one] at h1
    rw [h1]
    exact h.choose_spec.1
  · exact Quotient.out_eq _

/-- For an interval, the germ before the base germ is the chosen `F`-fixed end. -/
theorem germSeq_compBase_neg_one {i : Fin F.compCount} (h : IsIntervalComp F i) :
    germSeq F (compBase F i) (-1) = h.choose := by
  rw [compBase, dif_pos h, germSeq, zpow_neg_one]
  exact Equiv.symm_apply_apply _ _

theorem fold_neg_one {i : Fin F.compCount} (h : IsIntervalComp F i) :
    F.routeGerm (germSeq F (compBase F i) (-1)) = germSeq F (compBase F i) (-1) := by
  rw [germSeq_compBase_neg_one F h]
  exact h.choose_spec.2

/-- The step orbit is periodic with the order of the step permutation. -/
theorem germSeq_add_orderOf (β : Γ.EdgeEnd) (k : ℤ) :
    germSeq F β (k + orderOf F.stepPerm) = germSeq F β k := by
  rw [germSeq_add, zpow_natCast, pow_orderOf_eq_one]
  rfl

theorem exists_second_fold {i : Fin F.compCount} (h : IsIntervalComp F i) :
    ∃ k : ℕ, F.routeGerm (germSeq F (compBase F i) k) = germSeq F (compBase F i) k := by
  have hpos : 0 < orderOf F.stepPerm := orderOf_pos _
  refine ⟨orderOf F.stepPerm - 1, ?_⟩
  have hk : (((orderOf F.stepPerm - 1 : ℕ)) : ℤ) = -1 + (orderOf F.stepPerm : ℤ) := by
    rw [Nat.cast_sub hpos]; push_cast; ring
  rw [hk, germSeq_add_orderOf]
  exact fold_neg_one F h

open Classical in
/-- For an interval, the index of the second `F`-fixed end: the first fold of the orbit at a
nonnegative index. -/
noncomputable def compFoldIdx (i : Fin F.compCount) (h : IsIntervalComp F i) : ℕ :=
  Nat.find (exists_second_fold F h)

theorem fold_compFoldIdx {i : Fin F.compCount} (h : IsIntervalComp F i) :
    F.routeGerm (germSeq F (compBase F i) (compFoldIdx F i h)) =
      germSeq F (compBase F i) (compFoldIdx F i h) := by
  classical
  exact Nat.find_spec (exists_second_fold F h)

theorem not_fold_lt_compFoldIdx {i : Fin F.compCount} (h : IsIntervalComp F i) {k : ℕ}
    (hk : k < compFoldIdx F i h) :
    F.routeGerm (germSeq F (compBase F i) k) ≠ germSeq F (compBase F i) k := by
  classical
  exact Nat.find_min (exists_second_fold F h) hk

/-- The step map has every germ as a periodic point. -/
theorem minimalPeriod_stepPerm_pos (β : Γ.EdgeEnd) :
    0 < Function.minimalPeriod F.stepPerm β := by
  refine Function.minimalPeriod_pos_of_mem_periodicPts
    ⟨orderOf F.stepPerm, orderOf_pos _, ?_⟩
  change (⇑F.stepPerm)^[orderOf F.stepPerm] β = β
  rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
  rfl

open Classical in
/-- **The length `L_i` of the component `i`**: for an interval, the position of the second fixed
end; for a circle, the length of one period of the orbit. -/
noncomputable def compLen (i : Fin F.compCount) : ℝ :=
  if h : IsIntervalComp F i then posSeq F (compBase F i) (compFoldIdx F i h + 1)
  else posSeq F (compBase F i) (Function.minimalPeriod F.stepPerm (compBase F i))

theorem compLen_of_interval {i : Fin F.compCount} (h : IsIntervalComp F i) :
    compLen F i = posSeq F (compBase F i) (compFoldIdx F i h + 1) := by
  rw [compLen, dif_pos h]

theorem compLen_pos (i : Fin F.compCount) : 0 < compLen F i := by
  unfold compLen
  split_ifs with h
  · have := (posSeq_lt_iff F (compBase F i)).mpr
      (show (0 : ℤ) < (compFoldIdx F i h : ℤ) + 1 by positivity)
    rwa [posSeq_zero] at this
  · have := (posSeq_lt_iff F (compBase F i)).mpr
      (show (0 : ℤ) < (Function.minimalPeriod F.stepPerm (compBase F i) : ℤ) by
        exact_mod_cast minimalPeriod_stepPerm_pos F _)
    rwa [posSeq_zero] at this

open Classical in
/-- **The parameter domain `Λ_i`**: `[0, L_i]` for an interval, `ℝ` for a circle. -/
def compDomain (i : Fin F.compCount) : Set ℝ :=
  if IsIntervalComp F i then Icc 0 (compLen F i) else univ

/-- **The map `ι_i : Λ_i → Γ`**: the unrolled orbit of the base germ.  (It is defined on all of
`ℝ`; only its values on `Λ_i` are used.) -/
noncomputable def compMap (i : Fin F.compCount) : ℝ → GraphPoint Γ := unroll F (compBase F i)

/-- **The orientation `o_i = ±1`** of `ι_i`. -/
noncomputable def compSign (i : Fin F.compCount) : ℝ → ℝ := unrollSign F (compBase F i)

/-- **The discrete set `Z_i = ι_i⁻¹(𝒱)`** of parameters mapped to vertices. -/
def compVertexSet (i : Fin F.compCount) : Set ℝ :=
  {u | u ∈ compDomain F i ∧ (compMap F i u).IsVertex}

theorem compDomain_of_interval {i : Fin F.compCount} (h : IsIntervalComp F i) :
    compDomain F i = Icc 0 (compLen F i) := by
  rw [compDomain, if_pos h]

theorem compDomain_of_circle {i : Fin F.compCount} (h : ¬ IsIntervalComp F i) :
    compDomain F i = univ := by
  rw [compDomain, if_neg h]

theorem mem_compVertexSet_iff {i : Fin F.compCount} {u : ℝ} :
    u ∈ compVertexSet F i ↔ u ∈ compDomain F i ∧ u ∈ gluedSet F (compBase F i) := by
  rw [compVertexSet, mem_setOf_eq, compMap, unroll_isVertex_iff]

/-! ### Properties of the data -/

/-- **On each component of `Λ_i \ Z_i` the map `ι_i` is an isometry onto an open edge**: on the
segment `(posSeq k, posSeq (k + 1))` it maps `u` to the point `const + o_i(u) u` of the edge of
`germSeq k`, with the constant orientation `o_i(u) = σ(germSeq k) = ±1`, and the segment onto the
whole open edge. -/
theorem compMap_of_mem_segment (i : Fin F.compCount) {k : ℤ} {u : ℝ}
    (hu : u ∈ Ioo (posSeq F (compBase F i) k) (posSeq F (compBase F i) (k + 1))) :
    compMap F i u = GraphPoint.interior (germSeq F (compBase F i) k).1
        ((EdgeEnd.coordinate Γ (germSeq F (compBase F i) k) -
          EdgeEnd.sign Γ (germSeq F (compBase F i) k) * posSeq F (compBase F i) (k + 1)) +
          compSign F i u * u) ∧
      compSign F i u = EdgeEnd.sign Γ (germSeq F (compBase F i) k) ∧
      (compSign F i u = 1 ∨ compSign F i u = -1) := by
  have hs : compSign F i u = EdgeEnd.sign Γ (germSeq F (compBase F i) k) :=
    unrollSign_of_mem_Ico F _ ⟨hu.1.le, hu.2⟩
  refine ⟨?_, hs, hs ▸ sign_eq_one_or_neg_one _⟩
  rw [compMap, unroll_of_mem_Ioo F _ hu, hs]
  congr 1
  ring

/-- The image of a segment is the whole open edge. -/
theorem compMap_segment_surj (i : Fin F.compCount) (k : ℤ) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) (Γ.length (germSeq F (compBase F i) k).1)) :
    ∃ u ∈ Ioo (posSeq F (compBase F i) k) (posSeq F (compBase F i) (k + 1)),
      compMap F i u = GraphPoint.interior (germSeq F (compBase F i) k).1 q := by
  set g := germSeq F (compBase F i) k
  set d := EdgeEnd.sign Γ g * (EdgeEnd.coordinate Γ g - q)
  have hd : d ∈ Ioo (0 : ℝ) (Γ.length g.1) := by
    rw [← chart_mem_Ioo_iff g]
    have : EdgeEnd.coordinate Γ g - EdgeEnd.sign Γ g * d = q := by
      simp only [d]; rw [← mul_assoc, sign_mul_self, one_mul]; ring
    rwa [this]
  have hlen := segLen_eq_posSeq (F := F) (β := compBase F i) k
  refine ⟨posSeq F (compBase F i) (k + 1) - d, ⟨by linarith [hd.2], by linarith [hd.1]⟩, ?_⟩
  rw [compMap, unroll_of_mem_Ioo F _ ⟨by linarith [hd.2], by linarith [hd.1]⟩]
  congr 1
  simp only [d]
  rw [show posSeq F (compBase F i) (k + 1) - (posSeq F (compBase F i) (k + 1) -
    EdgeEnd.sign Γ g * (EdgeEnd.coordinate Γ g - q)) =
      EdgeEnd.sign Γ g * (EdgeEnd.coordinate Γ g - q) by ring, ← mul_assoc, sign_mul_self]
  ring

/-! ### The symmetries of an interval component -/

section Interval

variable {F} {i : Fin F.compCount} (h : IsIntervalComp F i)
include h

theorem compLen_eq_posSeq : compLen F i =
    posSeq F (compBase F i) ((compFoldIdx F i h : ℤ) + 1) := compLen_of_interval F h

/-- The unrolled interval is even about its first endpoint. -/
theorem unroll_neg (y : ℝ) : unroll F (compBase F i) (-y) = unroll F (compBase F i) y := by
  have := unroll_reflect F (compBase F i) (fold_neg_one F h) y
  rwa [show (-1 : ℤ) + 1 = 0 by ring, posSeq_zero, mul_zero, zero_sub] at this

theorem unrollSign_neg {y : ℝ} (hy : y ∉ gluedSet F (compBase F i)) :
    unrollSign F (compBase F i) (-y) = -unrollSign F (compBase F i) y := by
  have := unrollSign_reflect F (compBase F i) (fold_neg_one F h) hy
  rwa [show (-1 : ℤ) + 1 = 0 by ring, posSeq_zero, mul_zero, zero_sub] at this

theorem neg_mem_gluedSet {y : ℝ} :
    -y ∈ gluedSet F (compBase F i) ↔ y ∈ gluedSet F (compBase F i) := by
  have := mem_gluedSet_reflect F (compBase F i) (fold_neg_one F h) (y := y)
  rwa [show (-1 : ℤ) + 1 = 0 by ring, posSeq_zero, mul_zero, zero_sub] at this

/-- The unrolled interval is even about its second endpoint. -/
theorem unroll_two_len_sub (y : ℝ) :
    unroll F (compBase F i) (2 * compLen F i - y) = unroll F (compBase F i) y := by
  rw [compLen_eq_posSeq h]
  exact unroll_reflect F (compBase F i) (fold_compFoldIdx F h) y

theorem unrollSign_two_len_sub {y : ℝ} (hy : y ∉ gluedSet F (compBase F i)) :
    unrollSign F (compBase F i) (2 * compLen F i - y) = -unrollSign F (compBase F i) y := by
  rw [compLen_eq_posSeq h]
  exact unrollSign_reflect F (compBase F i) (fold_compFoldIdx F h) hy

theorem two_len_sub_mem_gluedSet {y : ℝ} :
    2 * compLen F i - y ∈ gluedSet F (compBase F i) ↔ y ∈ gluedSet F (compBase F i) := by
  rw [compLen_eq_posSeq h]
  exact mem_gluedSet_reflect F (compBase F i) (fold_compFoldIdx F h)

/-- The unrolled interval is `2L`-periodic. -/
theorem unroll_add_two_len (y : ℝ) :
    unroll F (compBase F i) (y + 2 * compLen F i) = unroll F (compBase F i) y := by
  rw [show y + 2 * compLen F i = 2 * compLen F i - -y by ring, unroll_two_len_sub h, unroll_neg h]

theorem germSeq_add_two_period (k : ℤ) :
    germSeq F (compBase F i) (k + 2 * ((compFoldIdx F i h : ℤ) + 1)) =
      germSeq F (compBase F i) k := by
  have h1 := germSeq_reflect F (compBase F i) (fold_compFoldIdx F h) (-1 - k)
  have h2 := germSeq_reflect F (compBase F i) (fold_neg_one F h) k
  rw [show 2 * (compFoldIdx F i h : ℤ) + 1 - (-1 - k) = k + 2 * ((compFoldIdx F i h : ℤ) + 1) by
    ring] at h1
  rw [show 2 * (-1 : ℤ) + 1 - k = -1 - k by ring] at h2
  rw [h1, h2, otherEnd_otherEnd]

theorem posSeq_add_two_period (k : ℤ) :
    posSeq F (compBase F i) (k + 2 * ((compFoldIdx F i h : ℤ) + 1)) =
      posSeq F (compBase F i) k + 2 * compLen F i := by
  have h1 := posSeq_reflect F (compBase F i) (fold_compFoldIdx F h) (-k)
  have h2 := posSeq_reflect F (compBase F i) (fold_neg_one F h) k
  rw [show 2 * (compFoldIdx F i h : ℤ) + 2 - -k = k + 2 * ((compFoldIdx F i h : ℤ) + 1) by
    ring] at h1
  rw [show 2 * (-1 : ℤ) + 2 - k = -k by ring, show (-1 : ℤ) + 1 = 0 by ring, posSeq_zero] at h2
  rw [h1, h2, compLen_eq_posSeq h]
  ring

theorem segIdx_add_two_len (y : ℝ) :
    segIdx F (compBase F i) (y + 2 * compLen F i) =
      segIdx F (compBase F i) y + 2 * ((compFoldIdx F i h : ℤ) + 1) := by
  have hs := segIdx_spec F (compBase F i) y
  apply segIdx_eq
  rw [posSeq_add_two_period h, show segIdx F (compBase F i) y + 2 * ((compFoldIdx F i h : ℤ) + 1)
    + 1 = (segIdx F (compBase F i) y + 1) + 2 * ((compFoldIdx F i h : ℤ) + 1) by ring,
    posSeq_add_two_period h]
  constructor <;> linarith [hs.1, hs.2]

theorem unrollSign_add_two_len (y : ℝ) :
    unrollSign F (compBase F i) (y + 2 * compLen F i) = unrollSign F (compBase F i) y := by
  rw [unrollSign, unrollSign, segIdx_add_two_len h, germSeq_add_two_period h]

theorem add_two_len_mem_gluedSet {y : ℝ} :
    y + 2 * compLen F i ∈ gluedSet F (compBase F i) ↔ y ∈ gluedSet F (compBase F i) := by
  rw [show y + 2 * compLen F i = 2 * compLen F i - -y by ring, two_len_sub_mem_gluedSet h,
    neg_mem_gluedSet h]

theorem add_two_len_zsmul (n : ℤ) (y : ℝ) :
    unroll F (compBase F i) (y + 2 * compLen F i * n) = unroll F (compBase F i) y ∧
      (y + 2 * compLen F i * n ∈ gluedSet F (compBase F i) ↔ y ∈ gluedSet F (compBase F i)) ∧
      unrollSign F (compBase F i) (y + 2 * compLen F i * n) = unrollSign F (compBase F i) y := by
  have p1 : Function.Periodic (unroll F (compBase F i)) (2 * compLen F i) :=
    unroll_add_two_len h
  have p2 : Function.Periodic (fun y => y ∈ gluedSet F (compBase F i)) (2 * compLen F i) :=
    fun y => propext (add_two_len_mem_gluedSet h)
  have p3 : Function.Periodic (unrollSign F (compBase F i)) (2 * compLen F i) :=
    unrollSign_add_two_len h
  rw [mul_comm (2 * compLen F i)]
  exact ⟨p1.int_mul n y, by rw [show (y + n * (2 * compLen F i) ∈ gluedSet F (compBase F i)) =
    (y ∈ gluedSet F (compBase F i)) from p2.int_mul n y], p3.int_mul n y⟩

/-- **The symmetries of an interval component**: `y ↦ ρ y + 2 L n` (`ρ = ±1`, `n ∈ ℤ`) preserves
the unrolled map and the glued points, and multiplies the orientation by `ρ`. -/
theorem unroll_symm {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) (n : ℤ) (y : ℝ) :
    unroll F (compBase F i) (ρ * y + 2 * compLen F i * n) = unroll F (compBase F i) y ∧
      (ρ * y + 2 * compLen F i * n ∈ gluedSet F (compBase F i) ↔
        y ∈ gluedSet F (compBase F i)) ∧
      (y ∉ gluedSet F (compBase F i) →
        unrollSign F (compBase F i) (ρ * y + 2 * compLen F i * n) =
          ρ * unrollSign F (compBase F i) y) := by
  obtain ⟨h1, h2, h3⟩ := add_two_len_zsmul h n (ρ * y)
  rcases hρ with rfl | rfl
  · simp only [one_mul] at h1 h2 h3 ⊢
    exact ⟨h1, h2, fun _ => h3⟩
  · simp only [neg_one_mul] at h1 h2 h3 ⊢
    refine ⟨h1.trans (unroll_neg h y), h2.trans (neg_mem_gluedSet h), fun hy => ?_⟩
    rw [h3, unrollSign_neg h hy]

/-- The multiples of `L_i` are glued points of an interval. -/
theorem mul_len_mem_gluedSet (n : ℤ) : compLen F i * n ∈ gluedSet F (compBase F i) := by
  have h0 : (0 : ℝ) ∈ gluedSet F (compBase F i) := ⟨0, posSeq_zero F _⟩
  have hL : compLen F i ∈ gluedSet F (compBase F i) := ⟨_, (compLen_eq_posSeq h).symm⟩
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · have := ((unroll_symm h (Or.inl rfl) m 0).2.1).mpr h0
    convert this using 1
    push_cast; ring
  · have := ((unroll_symm h (Or.inl rfl) m (compLen F i)).2.1).mpr hL
    convert this using 1
    push_cast; ring

end Interval

/-! ### The folding map `f` -/

open Classical in
/-- **The folding map `f`** of the paper: the identity for a circle, and for an interval the
`2L_i`-periodic function with `f(s) = |s|` on `[-L_i, L_i]`. -/
noncomputable def compFold (i : Fin F.compCount) (s : ℝ) : ℝ :=
  if IsIntervalComp F i then
    |toIocMod (show (0 : ℝ) < 2 * compLen F i by linarith [compLen_pos F i])
      (-compLen F i) s|
  else s

theorem compFold_spec {i : Fin F.compCount} (h : IsIntervalComp F i) (s : ℝ) :
    compFold F i s ∈ Icc 0 (compLen F i) ∧ ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ ∃ n : ℤ,
      s = ρ * compFold F i s + 2 * compLen F i * n := by
  have hL := compLen_pos F i
  have hp : (0 : ℝ) < 2 * compLen F i := by linarith
  set m := toIocMod hp (-compLen F i) s
  have hm := toIocMod_mem_Ioc hp (-compLen F i) s
  have hfold : compFold F i s = |m| := by rw [compFold, if_pos h]
  obtain ⟨-, z, hz⟩ := (toIocMod_eq_iff hp).mp (rfl : m = m)
  refine ⟨?_, ?_⟩
  · rw [hfold]
    refine ⟨abs_nonneg _, abs_le.mpr ⟨by linarith [hm.1], by linarith [hm.2]⟩⟩
  · rcases le_or_gt 0 m with hm0 | hm0
    · refine ⟨1, Or.inl rfl, z, ?_⟩
      rw [hfold, abs_of_nonneg hm0, hz, zsmul_eq_mul]; ring
    · refine ⟨-1, Or.inr rfl, z, ?_⟩
      rw [hfold, abs_of_neg hm0, hz, zsmul_eq_mul]; ring

theorem compFold_of_circle {i : Fin F.compCount} (h : ¬ IsIntervalComp F i) (s : ℝ) :
    compFold F i s = s := by
  rw [compFold, if_neg h]

/-! ### Discreteness of `Z_i`, endpoints, and surjectivity -/

/-- The glued points form a closed set. -/
theorem isClosed_gluedSet (β : Γ.EdgeEnd) : IsClosed (gluedSet F β) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  have hk := seg_mem_Ioo_of_not_mem F β hy
  refine Filter.mem_of_superset (Ioo_mem_nhds hk.1 hk.2) ?_
  rintro z hz ⟨k, rfl⟩
  have h1 := (posSeq_lt_iff F β).mp hz.1
  have h2 := (posSeq_lt_iff F β).mp hz.2
  omega

/-- A point close to a non-glued point lies in the same open segment. -/
theorem mem_seg_of_lt_infDist (β : Γ.EdgeEnd) {y₀ y : ℝ} {k : ℤ}
    (hy₀ : y₀ ∈ Ioo (posSeq F β k) (posSeq F β (k + 1)))
    (hy : |y - y₀| < Metric.infDist y₀ (gluedSet F β)) :
    y ∈ Ioo (posSeq F β k) (posSeq F β (k + 1)) := by
  have hd1 := Metric.infDist_le_dist_of_mem (x := y₀)
    (show posSeq F β k ∈ gluedSet F β from ⟨k, rfl⟩)
  have hd2 := Metric.infDist_le_dist_of_mem (x := y₀)
    (show posSeq F β (k + 1) ∈ gluedSet F β from ⟨k + 1, rfl⟩)
  rw [Real.dist_eq] at hd1 hd2
  rw [abs_of_pos (by linarith [hy₀.1])] at hd1
  rw [abs_of_neg (by linarith [hy₀.2])] at hd2
  have := abs_lt.mp hy
  constructor <;> linarith

/-- A non-glued point has positive distance from the glued points. -/
theorem infDist_gluedSet_pos (β : Γ.EdgeEnd) {y : ℝ} (hy : y ∉ gluedSet F β) :
    0 < Metric.infDist y (gluedSet F β) := by
  rcases (isClosed_gluedSet F β).notMem_iff_infDist_pos ⟨0, 0, posSeq_zero F β⟩ |>.mp hy with h
  exact h

/-- **`Z_i` is discrete.** -/
theorem compVertexSet_discrete (i : Fin F.compCount) :
    ∃ δ > 0, ∀ u ∈ compVertexSet F i, ∀ u' ∈ compVertexSet F i, |u' - u| < δ → u' = u := by
  obtain ⟨ℓ, hℓ, hle⟩ := exists_length_lower_bound F (compBase F i)
  refine ⟨ℓ, hℓ, fun u hu u' hu' hlt => ?_⟩
  obtain ⟨-, k, rfl⟩ := (mem_compVertexSet_iff F).mp hu
  obtain ⟨-, k', rfl⟩ := (mem_compVertexSet_iff F).mp hu'
  by_contra hne
  have hkk : k ≠ k' := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hkk with h | h
  · have := posSeq_sub_ge F (compBase F i) hle h.le
    have h1 : (1 : ℝ) ≤ ((k' - k : ℤ) : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ k' - k)
    rw [abs_of_nonneg (by nlinarith)] at hlt
    nlinarith
  · have := posSeq_sub_ge F (compBase F i) hle h.le
    have h1 : (1 : ℝ) ≤ ((k - k' : ℤ) : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ k - k')
    rw [abs_sub_comm, abs_of_nonneg (by nlinarith)] at hlt
    nlinarith

/-- **`Z_i` contains the endpoints `0, L_i` of an interval.** -/
theorem endpoints_mem_compVertexSet {i : Fin F.compCount} (h : IsIntervalComp F i) :
    0 ∈ compVertexSet F i ∧ compLen F i ∈ compVertexSet F i := by
  have hL := compLen_pos F i
  rw [mem_compVertexSet_iff, mem_compVertexSet_iff, compDomain_of_interval F h]
  exact ⟨⟨⟨le_rfl, hL.le⟩, 0, posSeq_zero F _⟩,
    ⟨⟨hL.le, le_rfl⟩, _, (compLen_eq_posSeq h).symm⟩⟩

/-- The orbit of the base germ meets every edge of its component. -/
theorem exists_germSeq_edge (i : Fin F.compCount) {e : Γ.Edge}
    (he : F.compOf (e, true) = F.compEnum i) : ∃ k : ℤ, (germSeq F (compBase F i) k).1 = e := by
  have he' : F.SameComp (compBase F i) (e, true) :=
    (F.compOf_eq_iff).mp (by rw [compOf_compBase, he])
  rcases he' with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k, by rw [germSeq, hk]⟩
  · refine ⟨-k, ?_⟩
    have := F.otherEnd_zpow (-k) (compBase F i)
    rw [neg_neg, hk] at this
    rw [germSeq, ← otherEnd_fst, this]

/-- **Every edge-interior point of an edge of `R_i` is `ι_i(u)` for some `u ∈ Λ_i \ Z_i`.** -/
theorem exists_compMap_eq_of_comp (i : Fin F.compCount) {e : Γ.Edge}
    (hi : F.compOf (e, true) = F.compEnum i) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) (Γ.length e)) :
    ∃ u ∈ compDomain F i, u ∉ compVertexSet F i ∧ compMap F i u = GraphPoint.interior e q := by
  obtain ⟨k, hk⟩ := exists_germSeq_edge F i hi
  obtain ⟨y, hy, hyval⟩ := compMap_segment_surj F i k (q := q) (by rw [hk]; exact hq)
  rw [hk] at hyval
  have hyg : y ∉ gluedSet F (compBase F i) := by
    rintro ⟨k', rfl⟩
    have h1 := (posSeq_lt_iff F _).mp hy.1
    have h2 := (posSeq_lt_iff F _).mp hy.2
    omega
  by_cases hint : IsIntervalComp F i
  · obtain ⟨hmem, ρ, hρ, n, hn⟩ := compFold_spec F hint y
    have hsym := unroll_symm hint hρ n (compFold F i y)
    rw [← hn] at hsym
    refine ⟨compFold F i y, by rw [compDomain_of_interval F hint]; exact hmem, ?_, ?_⟩
    · rw [mem_compVertexSet_iff, ← hsym.2.1]
      exact fun h => hyg h.2
    · rw [compMap, ← hsym.1]
      exact hyval
  · refine ⟨y, by rw [compDomain_of_circle F hint]; trivial, ?_, hyval⟩
    rw [mem_compVertexSet_iff]
    exact fun h => hyg h.2

/-- **Every edge-interior point is `ι_i(u)` for some `i` and `u ∈ Λ_i \ Z_i`.** -/
theorem exists_compMap_eq_interior (e : Γ.Edge) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) (Γ.length e)) :
    ∃ i : Fin F.compCount, ∃ u ∈ compDomain F i, u ∉ compVertexSet F i ∧
      compMap F i u = GraphPoint.interior e q :=
  ⟨F.compEnum.symm (F.compOf (e, true)), exists_compMap_eq_of_comp F _ (by simp) hq⟩

end HamiltonianMetricGraphs
