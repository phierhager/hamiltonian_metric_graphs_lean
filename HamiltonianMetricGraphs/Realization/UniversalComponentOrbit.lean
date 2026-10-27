/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalFolds

/-!
# Unrolling a routing orbit along a line

This file contains the combinatorics behind the resolved space `R(Γ, F)` of Sec. IX.F.

A particle that arrives at the vertex of the edge-end `η` along `η` leaves along `F(η)` and next
arrives at the opposite end of `F(η)`.  The resulting **step map** `η ↦ otherEnd (F η)` is a
permutation of the edge-ends (`RoutingLaw.stepPerm`), with inverse `η ↦ F (otherEnd η)`.

For a germ `β`, the two-sided sequence `germSeq F β k = stepPerm^k β` (`k ∈ ℤ`) lists the
edge-ends met by a particle moving through the routing component of `β`.  Laying the edges of
these germs end to end along the real line — segment `k` is `[posSeq k, posSeq (k + 1)]`, of length
`ℓ(germSeq k)` — gives the map `unroll F β : ℝ → Γ`.  On the open segment `k` it is the isometry
onto the open edge of `germSeq k` which runs *towards* the end `germSeq k`; the points `posSeq k`
go to vertices.

Two facts make this the parametrization of the components of `R(Γ, F)`:

* **gluing**: the end of segment `k` is the end `germSeq k`, the start of segment `k + 1` is the
  end `F (germSeq k)`.  So consecutive segments are glued exactly as in `R(Γ, F)`; at a fixed end
  of `F` (a *fold*) segment `k + 1` retraces segment `k`;
* **reflection** (`germSeq_reflect`, `posSeq_reflect`, `unroll_reflect`): if `germSeq j` is a
  fold, the unrolling is symmetric about the point `posSeq (j + 1)`.  For an interval component,
  which has two folds, the unrolling is therefore even about one end and `2L`-periodic.

## Main declarations

* `GraphPoint`: the points of the metric graph — vertices and edge-interior points `(e, q)`;
* `RoutingLaw.stepPerm`, `germSeq`, `posSeq`, `segIdx`;
* `unroll`, `unrollSign`: the unrolled map and its orientation;
* `unroll_of_mem_Ioo`, `unroll_posSeq`: the map on a segment and at a glued point;
* `unroll_reflect`, `unrollSign_reflect`: the reflection at a fold.
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph

variable {Γ : FiniteMetricGraph}

/-! ### Points of the metric graph -/

/-- **A point of the metric graph `Γ`**: a vertex, or an edge-interior point `(e, q)`, written in
the coordinate `q ∈ (0, ℓ_e)` of the edge `e`. -/
inductive GraphPoint (Γ : FiniteMetricGraph) where
  /-- a vertex of `Γ` -/
  | vertex : Γ.Vertex → GraphPoint Γ
  /-- the point at coordinate `q` of the edge `e` -/
  | interior : Γ.Edge → ℝ → GraphPoint Γ

namespace GraphPoint

/-- A point of `Γ` is a vertex (it lies in the vertex set `𝒱`). -/
def IsVertex : GraphPoint Γ → Prop
  | vertex _ => True
  | interior _ _ => False

@[simp] theorem isVertex_vertex (v : Γ.Vertex) : (vertex v : GraphPoint Γ).IsVertex := trivial

@[simp] theorem not_isVertex_interior (e : Γ.Edge) (q : ℝ) :
    ¬ (interior e q : GraphPoint Γ).IsVertex := id

/-- The edge coordinate of a point (`0` at a vertex). -/
def coord : GraphPoint Γ → ℝ
  | vertex _ => 0
  | interior _ q => q

@[simp] theorem coord_interior (e : Γ.Edge) (q : ℝ) : (interior e q : GraphPoint Γ).coord = q :=
  rfl

end GraphPoint

/-! ### Endpoint arithmetic -/

/-- The coordinate of the opposite end, in terms of the outward sign. -/
theorem coordinate_otherEnd_eq (η : Γ.EdgeEnd) :
    EdgeEnd.coordinate Γ (otherEnd η) =
      EdgeEnd.coordinate Γ η - EdgeEnd.sign Γ η * Γ.length η.1 := by
  rcases hb : η.2 with _ | _
  · rw [coordinate_of_true' (show (otherEnd η).2 = true by simp [hb]), coordinate_of_false hb,
      sign_of_false hb]
    simp
  · rw [coordinate_of_false (show (otherEnd η).2 = false by simp [hb]), coordinate_of_true' hb,
      sign_of_true hb]
    ring

theorem sign_eq_one_or_neg_one (η : Γ.EdgeEnd) :
    EdgeEnd.sign Γ η = 1 ∨ EdgeEnd.sign Γ η = -1 := by
  rcases hb : η.2 with _ | _
  · exact Or.inr (sign_of_false hb)
  · exact Or.inl (sign_of_true hb)

theorem sign_mul_self (η : Γ.EdgeEnd) : EdgeEnd.sign Γ η * EdgeEnd.sign Γ η = 1 := by
  rcases sign_eq_one_or_neg_one η with h | h <;> rw [h] <;> norm_num

/-- **The edge chart towards an end.**  The point at distance `d` before the end `η` has the
coordinate `coord η - σ(η) d`; it is inside the edge exactly for `0 < d < ℓ`. -/
theorem chart_mem_Ioo_iff (η : Γ.EdgeEnd) (d : ℝ) :
    EdgeEnd.coordinate Γ η - EdgeEnd.sign Γ η * d ∈ Ioo (0 : ℝ) (Γ.length η.1) ↔
      d ∈ Ioo (0 : ℝ) (Γ.length η.1) := by
  rcases hb : η.2 with _ | _
  · rw [coordinate_of_false hb, sign_of_false hb]
    simp
  · rw [coordinate_of_true' hb, sign_of_true hb]
    simp only [mem_Ioo, one_mul]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem chart_mem_Icc_iff (η : Γ.EdgeEnd) (d : ℝ) :
    EdgeEnd.coordinate Γ η - EdgeEnd.sign Γ η * d ∈ Icc (0 : ℝ) (Γ.length η.1) ↔
      d ∈ Icc (0 : ℝ) (Γ.length η.1) := by
  rcases hb : η.2 with _ | _
  · rw [coordinate_of_false hb, sign_of_false hb]
    simp
  · rw [coordinate_of_true' hb, sign_of_true hb]
    simp only [mem_Icc, one_mul]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- An edge-end is determined by its edge and its coordinate. -/
theorem edgeEnd_eq_of_coordinate {η ζ : Γ.EdgeEnd} (h1 : η.1 = ζ.1)
    (h2 : EdgeEnd.coordinate Γ η = EdgeEnd.coordinate Γ ζ) : η = ζ := by
  obtain ⟨e, b⟩ := η
  obtain ⟨e', b'⟩ := ζ
  simp only at h1
  subst h1
  have hl := Γ.length_pos e
  cases b <;> cases b' <;> simp_all [EdgeEnd.coordinate]

/-- An edge-end on the edge of `ζ` is `ζ` or its opposite end. -/
theorem edgeEnd_eq_or_eq_otherEnd {η ζ : Γ.EdgeEnd} (h : η.1 = ζ.1) : η = ζ ∨ η = otherEnd ζ := by
  obtain ⟨e, b⟩ := η
  obtain ⟨e', b'⟩ := ζ
  simp only at h
  subst h
  cases b <;> cases b' <;> simp [otherEnd]

/-! ### Two-sided orbits -/

/-- A two-sided sequence which follows a permutation is an orbit of it. -/
theorem eq_zpow_of_succ {α : Type*} {s : Equiv.Perm α} {x : ℤ → α}
    (h : ∀ k, x (k + 1) = s (x k)) (k₀ n : ℤ) : x (k₀ + n) = (s ^ n) (x k₀) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [← add_assoc, h, ih, show (n : ℤ) + 1 = 1 + n by ring, zpow_add, zpow_one,
        Equiv.Perm.mul_apply]
  | pred n ih =>
      have h' := h (k₀ + (-(n : ℤ) - 1))
      rw [show k₀ + (-(n : ℤ) - 1) + 1 = k₀ + -(n : ℤ) by ring, ih] at h'
      have h'' : x (k₀ + (-(n : ℤ) - 1)) = s⁻¹ ((s ^ (-(n : ℤ))) (x k₀)) := by rw [h']; simp
      rw [h'', show -(n : ℤ) - 1 = -1 + -n by ring, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]

/-! ### The step permutation -/

namespace RoutingLaw

variable (F : RoutingLaw Γ)

/-- **The step map as a permutation**: `η ↦ otherEnd (F η)`, with inverse `η ↦ F (otherEnd η)`. -/
def stepPerm : Equiv.Perm Γ.EdgeEnd where
  toFun := F.step
  invFun η := F.routeGerm (otherEnd η)
  left_inv η := by simp [step, F.routeGerm_routeGerm]
  right_inv η := by simp [step, F.routeGerm_routeGerm]

@[simp] theorem stepPerm_apply (η : Γ.EdgeEnd) : F.stepPerm η = otherEnd (F.routeGerm η) := rfl

@[simp] theorem stepPerm_symm_apply (η : Γ.EdgeEnd) :
    F.stepPerm.symm η = F.routeGerm (otherEnd η) := rfl

theorem stepPerm_inv_apply (η : Γ.EdgeEnd) :
    (F.stepPerm⁻¹ : Equiv.Perm Γ.EdgeEnd) η = F.routeGerm (otherEnd η) := rfl

/-- `otherEnd` conjugates the step map to its inverse: a reversed orbit is an orbit. -/
theorem otherEnd_stepPerm (η : Γ.EdgeEnd) :
    otherEnd (F.stepPerm η) = (F.stepPerm⁻¹ : Equiv.Perm Γ.EdgeEnd) (otherEnd η) := by
  simp [stepPerm_inv_apply]

theorem otherEnd_stepPerm_inv (η : Γ.EdgeEnd) :
    otherEnd ((F.stepPerm⁻¹ : Equiv.Perm Γ.EdgeEnd) η) = F.stepPerm (otherEnd η) := rfl

theorem otherEnd_zpow (k : ℤ) (η : Γ.EdgeEnd) :
    otherEnd ((F.stepPerm ^ k) η) = (F.stepPerm ^ (-k)) (otherEnd η) := by
  have h := eq_zpow_of_succ (s := F.stepPerm) (x := fun n : ℤ => otherEnd ((F.stepPerm ^ (-n)) η))
    (fun n => by
      rw [show -(n + 1) = -1 + -n by ring, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply,
        F.otherEnd_stepPerm_inv]) 0 (-k)
  simpa using h

end RoutingLaw

/-! ### The two-sided germ sequence of an orbit -/

section Unroll

variable (F : RoutingLaw Γ) (β : Γ.EdgeEnd)

/-- **The germ sequence of the routing orbit of `β`**: `germSeq F β k = stepPerm^k β`, `k ∈ ℤ`.
Segment `k` of the unrolled orbit runs along the edge of `germSeq k` towards that end. -/
def germSeq (k : ℤ) : Γ.EdgeEnd := (F.stepPerm ^ k) β

@[simp] theorem germSeq_zero : germSeq F β 0 = β := by simp [germSeq]

theorem germSeq_succ (k : ℤ) : germSeq F β (k + 1) = F.stepPerm (germSeq F β k) := by
  rw [germSeq, germSeq, add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]

/-- The end through which segment `k + 1` starts is `F` of the end of segment `k`. -/
theorem routeGerm_germSeq (k : ℤ) :
    F.routeGerm (germSeq F β k) = otherEnd (germSeq F β (k + 1)) := by
  rw [germSeq_succ, RoutingLaw.stepPerm_apply, otherEnd_otherEnd]

theorem germSeq_pred (k : ℤ) :
    germSeq F β (k - 1) = F.routeGerm (otherEnd (germSeq F β k)) := by
  have h := routeGerm_germSeq F β (k - 1)
  rw [sub_add_cancel] at h
  rw [← h, F.routeGerm_routeGerm]

theorem germSeq_add (k n : ℤ) : germSeq F β (k + n) = (F.stepPerm ^ n) (germSeq F β k) :=
  eq_zpow_of_succ (germSeq_succ F β) k n

/-- The length of segment `k`. -/
noncomputable def segLen (k : ℤ) : ℝ := Γ.length (germSeq F β k).1

theorem segLen_pos (k : ℤ) : 0 < segLen F β k := Γ.length_pos _

/-- **The positions of the glued points** of the unrolled orbit: `posSeq 0 = 0` and
`posSeq (k + 1) = posSeq k + ℓ(germSeq k)`. -/
noncomputable def posSeq : ℤ → ℝ
  | Int.ofNat n => ∑ j ∈ Finset.range n, segLen F β j
  | Int.negSucc n => -∑ j ∈ Finset.range (n + 1), segLen F β (-((j : ℤ) + 1))

@[simp] theorem posSeq_zero : posSeq F β 0 = 0 := by
  change ∑ j ∈ Finset.range 0, segLen F β j = 0
  simp

theorem posSeq_succ (k : ℤ) : posSeq F β (k + 1) = posSeq F β k + segLen F β k := by
  rcases k with n | n
  · change ∑ j ∈ Finset.range (n + 1), segLen F β j = ∑ j ∈ Finset.range n, segLen F β j + _
    rw [Finset.sum_range_succ]
    rfl
  · rcases n with _ | m
    · change posSeq F β 0 = -∑ j ∈ Finset.range 1, segLen F β (-((j : ℤ) + 1)) + _
      simp
    · have hk : Int.negSucc (m + 1) + 1 = Int.negSucc m := by
        simp [Int.negSucc_eq]
      rw [hk]
      change -∑ j ∈ Finset.range (m + 1), segLen F β (-((j : ℤ) + 1)) =
        -∑ j ∈ Finset.range (m + 1 + 1), segLen F β (-((j : ℤ) + 1)) + _
      rw [Finset.sum_range_succ _ (m + 1)]
      have : Int.negSucc (m + 1) = -(((m + 1 : ℕ) : ℤ) + 1) := by simp [Int.negSucc_eq]
      rw [this]
      ring

theorem segLen_eq_posSeq {F : RoutingLaw Γ} {β : Γ.EdgeEnd} (k : ℤ) :
    Γ.length (germSeq F β k).1 = posSeq F β (k + 1) - posSeq F β k := by
  rw [posSeq_succ]; simp [segLen]

theorem posSeq_strictMono : StrictMono (posSeq F β) := by
  refine strictMono_int_of_lt_succ fun k => ?_
  rw [posSeq_succ]
  linarith [segLen_pos F β k]

theorem posSeq_lt_iff {k k' : ℤ} : posSeq F β k < posSeq F β k' ↔ k < k' :=
  (posSeq_strictMono F β).lt_iff_lt

theorem posSeq_le_iff {k k' : ℤ} : posSeq F β k ≤ posSeq F β k' ↔ k ≤ k' :=
  (posSeq_strictMono F β).le_iff_le

theorem posSeq_injective : Function.Injective (posSeq F β) := (posSeq_strictMono F β).injective

/-- A positive lower bound for all edge lengths. -/
theorem exists_length_lower_bound : ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ k, ℓ ≤ segLen F β k :=
  ⟨minLen Γ β.1, minLen_pos Γ β.1, fun _ => minLen_le Γ β.1 _⟩

theorem posSeq_sub_ge {ℓ : ℝ} (hℓ : ∀ k, ℓ ≤ segLen F β k) {k k' : ℤ} (hkk : k ≤ k') :
    ((k' - k : ℤ) : ℝ) * ℓ ≤ posSeq F β k' - posSeq F β k := by
  induction k', hkk using Int.leInduction with
  | base => simp
  | succ n hn ih =>
      rw [posSeq_succ]
      push_cast at ih ⊢
      linarith [hℓ n]

/-- **Every point of the line lies in a segment.** -/
theorem exists_seg (y : ℝ) : ∃ k : ℤ, posSeq F β k ≤ y ∧ y < posSeq F β (k + 1) := by
  obtain ⟨ℓ, hℓ, hle⟩ := exists_length_lower_bound F β
  have hlow : ∃ k : ℤ, posSeq F β k ≤ y := by
    refine ⟨-(⌈|y| / ℓ⌉ : ℤ), ?_⟩
    have h0 : (0 : ℤ) ≤ ⌈|y| / ℓ⌉ := Int.ceil_nonneg (by positivity)
    have h := posSeq_sub_ge F β hle (k := -(⌈|y| / ℓ⌉ : ℤ)) (k' := 0) (by omega)
    rw [posSeq_zero] at h
    have hc : |y| / ℓ ≤ (⌈|y| / ℓ⌉ : ℝ) := Int.le_ceil _
    have hc' : |y| ≤ (⌈|y| / ℓ⌉ : ℝ) * ℓ := by
      rwa [div_le_iff₀ hℓ] at hc
    push_cast at h
    linarith [neg_abs_le y]
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, posSeq F β k ≤ y → k ≤ b := by
    refine ⟨⌈|y| / ℓ⌉, fun k hk => ?_⟩
    by_contra hcon
    push Not at hcon
    have h := posSeq_sub_ge F β hle (k := 0) (k' := k) (by
      have : (0 : ℤ) ≤ ⌈|y| / ℓ⌉ := Int.ceil_nonneg (by positivity)
      omega)
    rw [posSeq_zero, sub_zero, sub_zero] at h
    have hc : (⌈|y| / ℓ⌉ : ℝ) < k := by exact_mod_cast hcon
    have hc' : |y| / ℓ ≤ (⌈|y| / ℓ⌉ : ℝ) := Int.le_ceil _
    have : |y| < (k : ℝ) * ℓ := by
      have := (div_lt_iff₀ hℓ).mp (lt_of_le_of_lt hc' hc)
      linarith
    linarith [le_abs_self y]
  obtain ⟨k, hk, hmax⟩ := Int.exists_greatest_of_bdd hbdd hlow
  refine ⟨k, hk, ?_⟩
  by_contra hcon
  push Not at hcon
  have := hmax (k + 1) hcon
  omega

/-- The segment containing a point is unique. -/
theorem seg_unique {y : ℝ} {k k' : ℤ} (h : posSeq F β k ≤ y ∧ y < posSeq F β (k + 1))
    (h' : posSeq F β k' ≤ y ∧ y < posSeq F β (k' + 1)) : k = k' := by
  have h1 : k < k' + 1 := (posSeq_lt_iff F β).mp (lt_of_le_of_lt h.1 h'.2)
  have h2 : k' < k + 1 := (posSeq_lt_iff F β).mp (lt_of_le_of_lt h'.1 h.2)
  omega

/-- The index of the segment `[posSeq k, posSeq (k + 1))` containing `y`. -/
noncomputable def segIdx (y : ℝ) : ℤ := (exists_seg F β y).choose

theorem segIdx_spec (y : ℝ) :
    posSeq F β (segIdx F β y) ≤ y ∧ y < posSeq F β (segIdx F β y + 1) :=
  (exists_seg F β y).choose_spec

theorem segIdx_eq {y : ℝ} {k : ℤ} (h : posSeq F β k ≤ y ∧ y < posSeq F β (k + 1)) :
    segIdx F β y = k :=
  seg_unique F β (segIdx_spec F β y) h

/-! ### The unrolled map -/

/-- **The unrolled orbit of `β`.**  The glued point `posSeq k` goes to the vertex where segment
`k` starts; a point `y` of the open segment `k` goes to the point of the edge of `germSeq k` at
distance `posSeq (k + 1) - y` before the end `germSeq k`. -/
noncomputable def unroll (y : ℝ) : GraphPoint Γ :=
  if y = posSeq F β (segIdx F β y) then
    GraphPoint.vertex (otherEnd (germSeq F β (segIdx F β y))).vertex
  else
    GraphPoint.interior (germSeq F β (segIdx F β y)).1
      (EdgeEnd.coordinate Γ (germSeq F β (segIdx F β y)) -
        EdgeEnd.sign Γ (germSeq F β (segIdx F β y)) * (posSeq F β (segIdx F β y + 1) - y))

/-- **The orientation of the unrolled map**: `dq/dy = σ(germSeq k)` on segment `k`. -/
noncomputable def unrollSign (y : ℝ) : ℝ := EdgeEnd.sign Γ (germSeq F β (segIdx F β y))

/-- The glued points: the preimage of the vertex set. -/
def gluedSet : Set ℝ := range (posSeq F β)

theorem unroll_of_mem_Ioo {k : ℤ} {y : ℝ} (h : y ∈ Ioo (posSeq F β k) (posSeq F β (k + 1))) :
    unroll F β y = GraphPoint.interior (germSeq F β k).1
      (EdgeEnd.coordinate Γ (germSeq F β k) -
        EdgeEnd.sign Γ (germSeq F β k) * (posSeq F β (k + 1) - y)) := by
  have hk : segIdx F β y = k := segIdx_eq F β ⟨h.1.le, h.2⟩
  rw [unroll, hk, if_neg (ne_of_gt h.1)]

theorem unrollSign_of_mem_Ico {k : ℤ} {y : ℝ} (h : y ∈ Ico (posSeq F β k) (posSeq F β (k + 1))) :
    unrollSign F β y = EdgeEnd.sign Γ (germSeq F β k) := by
  rw [unrollSign, segIdx_eq F β h]

theorem unroll_posSeq (k : ℤ) :
    unroll F β (posSeq F β k) = GraphPoint.vertex (otherEnd (germSeq F β k)).vertex := by
  have hk : segIdx F β (posSeq F β k) = k :=
    segIdx_eq F β ⟨le_rfl, (posSeq_lt_iff F β).mpr (lt_add_one k)⟩
  rw [unroll, hk, if_pos rfl]

/-- The point where segment `k` starts is also the vertex where segment `k - 1` ends. -/
theorem otherEnd_germSeq_vertex (k : ℤ) :
    (otherEnd (germSeq F β (k + 1))).vertex = (germSeq F β k).vertex := by
  rw [← routeGerm_germSeq, F.routeGerm_vertex]

theorem seg_mem_Ioo_of_not_mem {y : ℝ} (hy : y ∉ gluedSet F β) :
    y ∈ Ioo (posSeq F β (segIdx F β y)) (posSeq F β (segIdx F β y + 1)) :=
  ⟨lt_of_le_of_ne (segIdx_spec F β y).1 (fun h => hy ⟨_, h⟩), (segIdx_spec F β y).2⟩

/-- **The vertex points of the unrolled map are exactly the glued points.** -/
theorem unroll_isVertex_iff (y : ℝ) : (unroll F β y).IsVertex ↔ y ∈ gluedSet F β := by
  constructor
  · intro h
    by_contra hy
    rw [unroll_of_mem_Ioo F β (seg_mem_Ioo_of_not_mem F β hy)] at h
    exact h
  · rintro ⟨k, rfl⟩
    rw [unroll_posSeq]
    trivial

/-- On an open segment the unrolled map lands in the open edge. -/
theorem unroll_coord_mem {k : ℤ} {y : ℝ} (h : y ∈ Ioo (posSeq F β k) (posSeq F β (k + 1))) :
    EdgeEnd.coordinate Γ (germSeq F β k) -
        EdgeEnd.sign Γ (germSeq F β k) * (posSeq F β (k + 1) - y) ∈
      Ioo (0 : ℝ) (Γ.length (germSeq F β k).1) := by
  rw [chart_mem_Ioo_iff]
  have hs := posSeq_succ F β k
  have hl : segLen F β k = Γ.length (germSeq F β k).1 := rfl
  constructor <;> linarith [h.1, h.2]

/-! ### Reflection at a fold -/

/-- **The orbit retraces itself after a fold.** -/
theorem germSeq_reflect {j : ℤ} (hj : F.routeGerm (germSeq F β j) = germSeq F β j) (k : ℤ) :
    germSeq F β (2 * j + 1 - k) = otherEnd (germSeq F β k) := by
  set x : ℤ → Γ.EdgeEnd := fun n => otherEnd (germSeq F β (2 * j + 1 - n)) with hx
  have hsucc : ∀ n, x (n + 1) = F.stepPerm (x n) := by
    intro n
    simp only [hx]
    rw [show 2 * j + 1 - (n + 1) = 2 * j + 1 - n - 1 by ring, germSeq_pred,
      RoutingLaw.stepPerm_apply]
  have hbase : x (j + 1) = germSeq F β (j + 1) := by
    simp only [hx]
    rw [show 2 * j + 1 - (j + 1) = j by ring, germSeq_succ, RoutingLaw.stepPerm_apply, hj]
  have h := eq_zpow_of_succ hsucc (j + 1) (k - (j + 1))
  rw [hbase, ← germSeq_add, show j + 1 + (k - (j + 1)) = k by ring] at h
  simp only [hx] at h
  rw [← h, otherEnd_otherEnd]

theorem segLen_reflect {j : ℤ} (hj : F.routeGerm (germSeq F β j) = germSeq F β j) (k : ℤ) :
    segLen F β (2 * j + 1 - k) = segLen F β k := by
  rw [segLen, segLen, germSeq_reflect F β hj, otherEnd_fst]

/-- A two-sided sequence with vanishing increments is constant. -/
theorem int_const_of_succ {f : ℤ → ℝ} (h : ∀ k, f (k + 1) = f k) (k k' : ℤ) : f k = f k' := by
  have key : ∀ n : ℤ, f (k' + n) = f k' := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [← add_assoc, h, ih]
    | pred n ih =>
        have := h (k' + (-(n : ℤ) - 1))
        rw [show k' + (-(n : ℤ) - 1) + 1 = k' + -(n : ℤ) by ring, ih] at this
        exact this.symm
  have := key (k - k')
  rwa [add_sub_cancel] at this

/-- **The glued points are symmetric about the fold.** -/
theorem posSeq_reflect {j : ℤ} (hj : F.routeGerm (germSeq F β j) = germSeq F β j) (k : ℤ) :
    posSeq F β (2 * j + 2 - k) = 2 * posSeq F β (j + 1) - posSeq F β k := by
  have hc := int_const_of_succ (f := fun n => posSeq F β (2 * j + 2 - n) + posSeq F β n)
    (fun n => by
      have h1 := posSeq_succ F β (2 * j + 2 - (n + 1))
      rw [show 2 * j + 2 - (n + 1) + 1 = 2 * j + 2 - n by ring] at h1
      have h2 := segLen_reflect F β hj n
      rw [show 2 * j + 1 - n = 2 * j + 2 - (n + 1) by ring] at h2
      rw [posSeq_succ]
      linarith) k (j + 1)
  rw [show 2 * j + 2 - (j + 1) = j + 1 by ring] at hc
  linarith

theorem mem_gluedSet_reflect {j : ℤ} (hj : F.routeGerm (germSeq F β j) = germSeq F β j)
    {y : ℝ} : 2 * posSeq F β (j + 1) - y ∈ gluedSet F β ↔ y ∈ gluedSet F β := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨2 * j + 2 - k, ?_⟩
    rw [posSeq_reflect F β hj, hk]
    ring
  · rintro ⟨k, rfl⟩
    exact ⟨2 * j + 2 - k, posSeq_reflect F β hj k⟩

/-- **The unrolled map is symmetric about a fold.** -/
theorem unroll_reflect {j : ℤ} (hj : F.routeGerm (germSeq F β j) = germSeq F β j) (y : ℝ) :
    unroll F β (2 * posSeq F β (j + 1) - y) = unroll F β y := by
  by_cases hy : y ∈ gluedSet F β
  · obtain ⟨k, rfl⟩ := hy
    rw [← posSeq_reflect F β hj, unroll_posSeq, unroll_posSeq,
      show 2 * j + 2 - k = 2 * j + 1 - (k - 1) by ring, germSeq_reflect F β hj, otherEnd_otherEnd,
      ← otherEnd_germSeq_vertex F β (k - 1), sub_add_cancel]
  · have hk := seg_mem_Ioo_of_not_mem F β hy
    generalize segIdx F β y = k at hk
    have hk' : 2 * posSeq F β (j + 1) - y ∈
        Ioo (posSeq F β (2 * j + 1 - k)) (posSeq F β (2 * j + 1 - k + 1)) := by
      rw [show 2 * j + 1 - k = 2 * j + 2 - (k + 1) by ring, posSeq_reflect F β hj,
        show 2 * j + 2 - (k + 1) + 1 = 2 * j + 2 - k by ring, posSeq_reflect F β hj]
      constructor <;> linarith [hk.1, hk.2]
    rw [unroll_of_mem_Ioo F β hk', unroll_of_mem_Ioo F β hk, germSeq_reflect F β hj,
      otherEnd_fst, coordinate_otherEnd_eq, sign_otherEnd,
      show 2 * j + 1 - k + 1 = 2 * j + 2 - k by ring, posSeq_reflect F β hj]
    congr 1
    have hs := posSeq_succ F β k
    have hl : segLen F β k = Γ.length (germSeq F β k).1 := rfl
    rw [← hl, hs]
    ring

/-- **The orientation reverses at a fold.** -/
theorem unrollSign_reflect {j : ℤ} (hj : F.routeGerm (germSeq F β j) = germSeq F β j) {y : ℝ}
    (hy : y ∉ gluedSet F β) :
    unrollSign F β (2 * posSeq F β (j + 1) - y) = -unrollSign F β y := by
  have hk := seg_mem_Ioo_of_not_mem F β hy
  have hy' : unrollSign F β y = EdgeEnd.sign Γ (germSeq F β (segIdx F β y)) := rfl
  rw [hy']
  generalize segIdx F β y = k at hk ⊢
  have hk' : 2 * posSeq F β (j + 1) - y ∈
      Ico (posSeq F β (2 * j + 1 - k)) (posSeq F β (2 * j + 1 - k + 1)) := by
    rw [show 2 * j + 1 - k = 2 * j + 2 - (k + 1) by ring, posSeq_reflect F β hj,
      show 2 * j + 2 - (k + 1) + 1 = 2 * j + 2 - k by ring, posSeq_reflect F β hj]
    constructor <;> linarith [hk.1, hk.2]
  rw [unrollSign_of_mem_Ico F β hk', germSeq_reflect F β hj, sign_otherEnd]

end Unroll

end HamiltonianMetricGraphs
