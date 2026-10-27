/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalLayout

/-!
# The two caps of a routing component

This file proves the structure theorem behind the universal microscopic model: **the corridor of
a routing component is a finite interval whose two endpoints are the fold positions**, and the
particle bounces between them forever.

Precisely, if the itinerary of `η₀` contains a fold at all, then

* the folds are exactly the terms of an arithmetic progression `k₁, k₁ + d, k₁ + 2d, …`
  (`isFold_iff`);
* the fold positions alternate between two values `B = vpos (k₁ + 1)` and `A = vpos (k₁ + d + 1)`
  (`vpos_fold_alternates`);
* every vertex position lies in `[A, B]` (`vpos_mem_Icc`), the direction is constant between
  consecutive folds, and a vertex which is not a fold keeps a distance of at least one edge
  length from both caps (`cap_margin`).

If the itinerary contains no fold — the case of a *circle* component of the resolved
`1`-manifold — then the direction is constantly `+1` and the positions increase strictly
(`dirSign_eq_one_of_no_fold`, `vpos_strictMono_of_no_fold`); such a component is realized on a
corridor whose caps lie beyond the finite horizon.
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph

variable {Γ : FiniteMetricGraph} {F : RoutingLaw Γ} {η₀ : Γ.EdgeEnd}

/-! ### Monotonicity between folds -/

/-- On a stretch on which the direction is constantly `s` the position advances by a nonnegative
multiple of `s`. -/
theorem vpos_diff {a b : ℕ} (hab : a ≤ b) (s : ℝ)
    (hs : ∀ i, a ≤ i → i < b → dirSign F η₀ i = s) :
    ∃ d : ℝ, 0 ≤ d ∧ (a < b → 0 < d) ∧ vpos F η₀ b = vpos F η₀ a + s * d := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨0, le_rfl, fun h => absurd h (lt_irrefl a), by ring⟩
  | succ m ham ih =>
      obtain ⟨d, hd0, -, hdv⟩ := ih fun i hi him => hs i hi (by omega)
      refine ⟨d + edgeLen F η₀ m, by linarith [edgeLen_pos F η₀ m], fun _ => by
        linarith [edgeLen_pos F η₀ m], ?_⟩
      rw [vpos_succ, hdv, hs m ham (by omega)]
      ring

/-- On a stretch on which the direction is constantly `+1` the position is monotone. -/
theorem vpos_mono {a b : ℕ} (hs : ∀ i, a ≤ i → i < b → dirSign F η₀ i = 1)
    {m n : ℕ} (ham : a ≤ m) (hmn : m ≤ n) (hnb : n ≤ b) :
    vpos F η₀ m ≤ vpos F η₀ n := by
  obtain ⟨d, hd0, -, hdv⟩ := vpos_diff (F := F) (η₀ := η₀) hmn 1
    fun i hi hin => hs i (by omega) (by omega)
  rw [hdv]; linarith

/-- Strict version of `vpos_mono`. -/
theorem vpos_lt {a b : ℕ} (hs : ∀ i, a ≤ i → i < b → dirSign F η₀ i = 1)
    {m n : ℕ} (ham : a ≤ m) (hmn : m < n) (hnb : n ≤ b) :
    vpos F η₀ m < vpos F η₀ n := by
  obtain ⟨d, -, hdp, hdv⟩ := vpos_diff (F := F) (η₀ := η₀) hmn.le 1
    fun i hi hin => hs i (by omega) (by omega)
  rw [hdv]; linarith [hdp hmn]

/-- On a stretch on which the direction is constantly `-1` the position is antitone. -/
theorem vpos_anti {a b : ℕ} (hs : ∀ i, a ≤ i → i < b → dirSign F η₀ i = -1)
    {m n : ℕ} (ham : a ≤ m) (hmn : m ≤ n) (hnb : n ≤ b) :
    vpos F η₀ n ≤ vpos F η₀ m := by
  obtain ⟨d, hd0, -, hdv⟩ := vpos_diff (F := F) (η₀ := η₀) hmn (-1)
    fun i hi hin => hs i (by omega) (by omega)
  rw [hdv]; linarith

/-- Strict version of `vpos_anti`. -/
theorem vpos_gt {a b : ℕ} (hs : ∀ i, a ≤ i → i < b → dirSign F η₀ i = -1)
    {m n : ℕ} (ham : a ≤ m) (hmn : m < n) (hnb : n ≤ b) :
    vpos F η₀ n < vpos F η₀ m := by
  obtain ⟨d, -, hdp, hdv⟩ := vpos_diff (F := F) (η₀ := η₀) hmn.le (-1)
    fun i hi hin => hs i (by omega) (by omega)
  rw [hdv]; linarith [hdp hmn]

/-- The direction is constant on a fold-free stretch. -/
theorem dirSign_const {a b : ℕ} (hab : a ≤ b) (h : ∀ i, a ≤ i → i < b → ¬ IsFold F η₀ i) :
    dirSign F η₀ b = dirSign F η₀ a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ m ham ih =>
      rw [dirSign_succ_of_not_fold (h m ham (by omega)), ih fun i hi him => h i hi (by omega)]

/-! ### The fold-free case -/

/-- Without folds the particle never turns around. -/
theorem dirSign_eq_one_of_no_fold {j : ℕ} (h : ∀ i, i < j → ¬ IsFold F η₀ i) :
    dirSign F η₀ j = 1 :=
  dirSign_const (Nat.zero_le j) fun i _ hij => h i hij

/-- Without folds the vertex positions increase strictly. -/
theorem vpos_strictMono_of_no_fold {b : ℕ} (h : ∀ i, i < b → ¬ IsFold F η₀ i)
    {m n : ℕ} (hmn : m < n) (hnb : n ≤ b) : vpos F η₀ m < vpos F η₀ n :=
  vpos_lt (a := 0) (b := b)
    (fun i _ hib => dirSign_eq_one_of_no_fold fun l hl => h l (by omega))
    (Nat.zero_le m) hmn hnb

/-! ### Consecutive folds -/

/-- `a` and `a + d` are **consecutive folds** of the itinerary. -/
structure Consec (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (a d : ℕ) : Prop where
  /-- the gap is positive -/
  gap_pos : 0 < d
  /-- `a` is a fold -/
  fold_left : IsFold F η₀ a
  /-- `a + d` is a fold -/
  fold_right : IsFold F η₀ (a + d)
  /-- nothing in between is a fold -/
  between : ∀ i, a < i → i < a + d → ¬ IsFold F η₀ i

/-- **The fold recursion.**  After two consecutive folds `a` and `a + d` the next fold is at
`a + 2d`, the fold position there is the one of `a`, and the direction repeats. -/
theorem Consec.next {a d : ℕ} (h : Consec F η₀ a d) : Consec F η₀ (a + d) d := by
  have hd := h.gap_pos
  refine ⟨hd, h.fold_right, ?_, ?_⟩
  · have hidx : a + d + 1 + (d - 1) = a + d + d := by omega
    have := (isFold_retrace h.fold_right (i := a) (j := d - 1) (by omega)).mpr h.fold_left
    rw [hidx] at this
    exact this
  · intro m hm1 hm2
    have hj : m = a + d + 1 + (m - (a + d) - 1) := by omega
    set j := m - (a + d) - 1 with hjdef
    have hjlt : j < d - 1 := by omega
    have hi : (a + d - 1 - j) + 1 + j = a + d := by omega
    have hiff := isFold_retrace h.fold_right (i := a + d - 1 - j) (j := j) hi
    intro hf
    rw [hj] at hf
    exact h.between (a + d - 1 - j) (by omega) (by omega) (hiff.mp hf)

theorem Consec.vpos_next {a d : ℕ} (h : Consec F η₀ a d) :
    vpos F η₀ (a + d + d + 1) = vpos F η₀ (a + 1) := by
  have hd := h.gap_pos
  have hidx : a + d + 2 + (d - 1) = a + d + d + 1 := by omega
  have := vpos_retrace h.fold_right (i := a + 1) (j := d - 1) (by omega)
  rw [hidx] at this
  exact this

theorem Consec.dirSign_next {a d : ℕ} (h : Consec F η₀ a d) :
    dirSign F η₀ (a + d + d) = dirSign F η₀ a := by
  have hd := h.gap_pos
  have hidx : a + d + 1 + (d - 1) = a + d + d := by omega
  have h1 := dirSign_retrace h.fold_right (i := a + 1) (j := d - 1) (by omega)
  rw [hidx] at h1
  rw [h1, dirSign_succ_of_fold h.fold_left]
  ring

/-- Every fold is a term of the arithmetic progression started by two consecutive folds. -/
theorem Consec.iterate {a d : ℕ} (h : Consec F η₀ a d) (s : ℕ) : Consec F η₀ (a + s * d) d := by
  induction s with
  | zero => simpa using h
  | succ m ih =>
      have := ih.next
      have hidx : a + m * d + d = a + (m + 1) * d := by ring
      rwa [hidx] at this

/-- The fold positions alternate between two values. -/
theorem Consec.vpos_iterate {a d : ℕ} (h : Consec F η₀ a d) (s : ℕ) :
    vpos F η₀ (a + s * d + 1) =
      if Even s then vpos F η₀ (a + 1) else vpos F η₀ (a + d + 1) := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
      match s with
      | 0 => simp
      | 1 => simp
      | (m + 2) =>
          have hkey := (h.iterate m).vpos_next
          have hidx : a + m * d + d + d + 1 = a + (m + 2) * d + 1 := by ring
          rw [hidx] at hkey
          rw [hkey, ih m (by omega)]
          have : Even (m + 2) ↔ Even m := by simp [Nat.even_add]
          simp only [this]

/-! ### The structure theorem in the presence of a fold -/

variable (F η₀)

/-- The index of the first fold of the itinerary. -/
noncomputable def firstFold (h : ∃ k, IsFold F η₀ k) : ℕ := Nat.find h

variable {F η₀}

theorem isFold_firstFold (h : ∃ k, IsFold F η₀ k) : IsFold F η₀ (firstFold F η₀ h) :=
  Nat.find_spec h

theorem not_isFold_of_lt_firstFold (h : ∃ k, IsFold F η₀ k) {i : ℕ}
    (hi : i < firstFold F η₀ h) : ¬ IsFold F η₀ i :=
  Nat.find_min h hi

theorem firstFold_le (h : ∃ k, IsFold F η₀ k) {k : ℕ} (hk : IsFold F η₀ k) :
    firstFold F η₀ h ≤ k :=
  Nat.find_le hk

/-- A fold recurs after one period of the itinerary, so every fold has a next one. -/
theorem exists_next_fold {k : ℕ} (hk : IsFold F η₀ k) : ∃ m, IsFold F η₀ (k + 1 + m) := by
  obtain ⟨n, hn0, hn⟩ := F.exists_period η₀
  refine ⟨n - 1, ?_⟩
  have hidx : k + 1 + (n - 1) = k + n := by omega
  rw [hidx]
  show F.routeGerm (F.itinerary η₀ (k + n)) = F.itinerary η₀ (k + n)
  rw [hn k]
  exact hk

/-- The gap to the next fold. -/
noncomputable def foldGap {k : ℕ} (hk : IsFold F η₀ k) : ℕ :=
  Nat.find (exists_next_fold hk) + 1

theorem foldGap_pos {k : ℕ} (hk : IsFold F η₀ k) : 0 < foldGap hk := Nat.succ_pos _

theorem isFold_add_foldGap {k : ℕ} (hk : IsFold F η₀ k) : IsFold F η₀ (k + foldGap hk) := by
  have := Nat.find_spec (exists_next_fold hk)
  have hidx : k + 1 + Nat.find (exists_next_fold hk) = k + foldGap hk := by
    rw [foldGap]; omega
  rwa [hidx] at this

theorem consec_foldGap {k : ℕ} (hk : IsFold F η₀ k) : Consec F η₀ k (foldGap hk) := by
  refine ⟨foldGap_pos hk, hk, isFold_add_foldGap hk, ?_⟩
  intro m hm1 hm2
  have hlt : m - k - 1 < Nat.find (exists_next_fold hk) := by
    rw [foldGap] at hm2; omega
  have := Nat.find_min (exists_next_fold hk) hlt
  have hidx : k + 1 + (m - k - 1) = m := by omega
  rwa [hidx] at this

/-! ### The shortest edge -/

/-- The length of a shortest edge of `Γ`. -/
noncomputable def minLen (Γ : FiniteMetricGraph) (e₀ : Γ.Edge) : ℝ :=
  Finset.univ.inf' ⟨e₀, Finset.mem_univ e₀⟩ Γ.length

theorem minLen_le (Γ : FiniteMetricGraph) (e₀ e : Γ.Edge) : minLen Γ e₀ ≤ Γ.length e :=
  Finset.inf'_le _ (Finset.mem_univ e)

theorem minLen_pos (Γ : FiniteMetricGraph) (e₀ : Γ.Edge) : 0 < minLen Γ e₀ := by
  rw [minLen, Finset.lt_inf'_iff]
  exact fun e _ => Γ.length_pos e

theorem minLen_le_edgeLen (e₀ : Γ.Edge) (j : ℕ) : minLen Γ e₀ ≤ edgeLen F η₀ j :=
  minLen_le Γ e₀ _

/-! ### Quantitative monotonicity -/

/-- One step of an increasing stretch advances by a whole edge. -/
theorem vpos_add_edgeLen_le {a b : ℕ} (hs : ∀ i, a ≤ i → i < b → dirSign F η₀ i = 1)
    {m n : ℕ} (ham : a ≤ m) (hmn : m < n) (hnb : n ≤ b) :
    vpos F η₀ m + edgeLen F η₀ m ≤ vpos F η₀ n := by
  have h1 : vpos F η₀ (m + 1) = vpos F η₀ m + edgeLen F η₀ m := by
    rw [vpos_succ, hs m ham (by omega)]; ring
  have h2 : vpos F η₀ (m + 1) ≤ vpos F η₀ n := vpos_mono hs (by omega) (by omega) hnb
  linarith

/-- One step of a decreasing stretch retreats by a whole edge. -/
theorem vpos_le_sub_edgeLen {a b : ℕ} (hs : ∀ i, a ≤ i → i < b → dirSign F η₀ i = -1)
    {m n : ℕ} (ham : a ≤ m) (hmn : m < n) (hnb : n ≤ b) :
    vpos F η₀ n ≤ vpos F η₀ m - edgeLen F η₀ m := by
  have h1 : vpos F η₀ (m + 1) = vpos F η₀ m - edgeLen F η₀ m := by
    rw [vpos_succ, hs m ham (by omega)]; ring
  have h2 : vpos F η₀ n ≤ vpos F η₀ (m + 1) := vpos_anti hs (by omega) (by omega) hnb
  linarith


/-! ### The structure theorem in the presence of a fold -/

/-- The layout data of a routing component containing a fold: `a` is the first fold and `d` the
gap to the next one. -/
structure FoldData (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (a d : ℕ) : Prop where
  /-- `a` and `a + d` are consecutive folds -/
  consec : Consec F η₀ a d
  /-- `a` is the first fold -/
  first : ∀ i, i < a → ¬ IsFold F η₀ i

theorem exists_foldData (h : ∃ k, IsFold F η₀ k) : ∃ a d, FoldData F η₀ a d :=
  ⟨firstFold F η₀ h, foldGap (isFold_firstFold h),
    consec_foldGap _, fun i hi => not_isFold_of_lt_firstFold h hi⟩

namespace FoldData

variable {a d : ℕ}

/-- Before the first fold the particle moves in the positive direction. -/
theorem dirSign_before (hfd : FoldData F η₀ a d) {j : ℕ} (hj : j ≤ a) : dirSign F η₀ j = 1 :=
  dirSign_eq_one_of_no_fold fun i hi => hfd.first i (by omega)

/-- **The first sweep is at least as long as the initial one.**  The retrace lemma forbids a fold
in `(a, 2a + 1)`, so the gap to the second fold is at least `a + 1`. -/
theorem gap_ge (hfd : FoldData F η₀ a d) : a + 1 ≤ d := by
  by_contra hc
  have hd := hfd.consec.gap_pos
  have hda : d ≤ a := by omega
  have hi : (a - d) + 1 + (d - 1) = a := by omega
  have hiff := isFold_retrace hfd.consec.fold_left (i := a - d) (j := d - 1) hi
  have hj : a + 1 + (d - 1) = a + d := by omega
  have hf : IsFold F η₀ (a + 1 + (d - 1)) := by rw [hj]; exact hfd.consec.fold_right
  exact hfd.first (a - d) (by omega) (hiff.mp hf)

/-- The particle returns to its starting vertex after the first fold. -/
theorem vpos_return (hfd : FoldData F η₀ a d) : vpos F η₀ (2 * a + 2) = 0 := by
  have h := vpos_retrace hfd.consec.fold_left (i := 0) (j := a) (by omega)
  rw [show a + 2 + a = 2 * a + 2 by omega] at h
  simpa using h

/-- The direction on the sweep following the fold `a + s d`. -/
theorem sweep_dir (hfd : FoldData F η₀ a d) (s : ℕ) {m : ℕ}
    (h1 : a + s * d + 1 ≤ m) (h2 : m ≤ a + s * d + d) :
    dirSign F η₀ m = -dirSign F η₀ (a + s * d) := by
  have hc : dirSign F η₀ m = dirSign F η₀ (a + s * d + 1) :=
    dirSign_const h1 fun i hi him =>
      (hfd.consec.iterate s).between i (by omega) (by omega)
  rw [hc, dirSign_succ_of_fold (hfd.consec.iterate s).fold_left]

/-- The direction on the first descending sweep is `-1`. -/
theorem dirSign_desc (hfd : FoldData F η₀ a d) {m : ℕ} (h1 : a + 1 ≤ m) (h2 : m ≤ a + d) :
    dirSign F η₀ m = -1 := by
  have h := hfd.sweep_dir 0 (m := m) (by simpa using h1) (by simpa using h2)
  rw [h]
  simp [hfd.dirSign_before (j := a) le_rfl]

/-- **The lower cap is at most the origin.** -/
theorem low_nonpos (hfd : FoldData F η₀ a d) : vpos F η₀ (a + d + 1) ≤ 0 := by
  have hg := hfd.gap_ge
  have h1 : vpos F η₀ (a + d + 1) ≤ vpos F η₀ (2 * a + 2) :=
    vpos_anti (a := a + 1) (b := a + d + 1)
      (fun i hi hib => hfd.dirSign_desc hi (by omega)) (by omega) (by omega) le_rfl
  rw [hfd.vpos_return] at h1
  exact h1

/-- **The upper cap is at least one edge to the right of the origin.** -/
theorem high_ge (hfd : FoldData F η₀ a d) : edgeLen F η₀ 0 ≤ vpos F η₀ (a + 1) := by
  have h1 : vpos F η₀ 1 ≤ vpos F η₀ (a + 1) :=
    vpos_mono (a := 0) (b := a + 1) (fun i _ hi => hfd.dirSign_before (by omega))
      (by omega) (by omega) le_rfl
  have h2 : vpos F η₀ 1 = edgeLen F η₀ 0 := by rw [vpos_succ]; simp
  linarith

/-- **The folds are exactly the arithmetic progression `a, a + d, a + 2d, …`.** -/
theorem isFold_iff (hfd : FoldData F η₀ a d) {k : ℕ} : IsFold F η₀ k ↔ ∃ s, k = a + s * d := by
  have hd := hfd.consec.gap_pos
  constructor
  · intro hk
    have hka : a ≤ k := by
      by_contra hc
      exact hfd.first k (by omega) hk
    have hmod := Nat.div_add_mod (k - a) d
    have hrd : (k - a) % d < d := Nat.mod_lt _ hd
    obtain ⟨P, hP⟩ : ∃ P, d * ((k - a) / d) = P := ⟨_, rfl⟩
    rw [hP] at hmod
    rcases Nat.eq_zero_or_pos ((k - a) % d) with h0 | h0
    · refine ⟨(k - a) / d, ?_⟩
      rw [Nat.mul_comm, hP]
      omega
    · exfalso
      refine (hfd.consec.iterate ((k - a) / d)).between k ?_ ?_ hk
      · rw [Nat.mul_comm, hP]; omega
      · rw [Nat.mul_comm, hP]; omega
  · rintro ⟨s, rfl⟩
    exact (hfd.consec.iterate s).fold_left

/-- **The direction at the folds alternates.** -/
theorem dirSign_fold (hfd : FoldData F η₀ a d) (s : ℕ) :
    dirSign F η₀ (a + s * d) = if Even s then 1 else -1 := by
  have hd := hfd.consec.gap_pos
  induction s using Nat.strong_induction_on with
  | _ s ih =>
      match s with
      | 0 => simpa using hfd.dirSign_before (j := a) le_rfl
      | 1 =>
          have h := hfd.dirSign_desc (m := a + d) (by omega) le_rfl
          simpa using h
      | (m + 2) =>
          have hkey := (hfd.consec.iterate m).dirSign_next
          have hidx : a + m * d + d + d = a + (m + 2) * d := by ring
          rw [hidx] at hkey
          rw [hkey, ih m (by omega)]
          have hev : Even (m + 2) ↔ Even m := by simp [Nat.even_add]
          simp only [hev]

/-- **The fold positions alternate between the two caps.** -/
theorem vpos_fold (hfd : FoldData F η₀ a d) (s : ℕ) :
    vpos F η₀ (a + s * d + 1) =
      if Even s then vpos F η₀ (a + 1) else vpos F η₀ (a + d + 1) :=
  hfd.consec.vpos_iterate s

/-- **Confinement**: every vertex position lies between the two caps. -/
theorem vpos_mem (hfd : FoldData F η₀ a d) (j : ℕ) :
    vpos F η₀ j ∈ Icc (vpos F η₀ (a + d + 1)) (vpos F η₀ (a + 1)) := by
  have hd := hfd.consec.gap_pos
  have hlow := hfd.low_nonpos
  rcases le_or_gt j (a + 1) with hj | hj
  · have h1 : vpos F η₀ 0 ≤ vpos F η₀ j :=
      vpos_mono (a := 0) (b := a + 1) (fun i _ hi => hfd.dirSign_before (by omega))
        (by omega) (by omega) hj
    have h2 : vpos F η₀ j ≤ vpos F η₀ (a + 1) :=
      vpos_mono (a := 0) (b := a + 1) (fun i _ hi => hfd.dirSign_before (by omega))
        (by omega) hj le_rfl
    rw [vpos_zero] at h1
    exact ⟨by linarith, h2⟩
  · -- `j` lies in the sweep number `s`
    have hmod := Nat.div_add_mod (j - a - 1) d
    have hrd : (j - a - 1) % d < d := Nat.mod_lt _ hd
    obtain ⟨P, hP⟩ : ∃ P, d * ((j - a - 1) / d) = P := ⟨_, rfl⟩
    rw [hP] at hmod
    set s := (j - a - 1) / d with hs
    have hsd : s * d = P := by rw [Nat.mul_comm]; exact hP
    have h1 : a + s * d + 1 ≤ j := by rw [hsd]; omega
    have h2 : j ≤ a + s * d + d := by rw [hsd]; omega
    have hstep : ∀ i, a + s * d + 1 ≤ i → i < a + s * d + d + 1 →
        dirSign F η₀ i = -dirSign F η₀ (a + s * d) :=
      fun i hi hib => hfd.sweep_dir s hi (by omega)
    have hnext : a + (s + 1) * d + 1 = a + s * d + d + 1 := by ring_nf
    have hvs := hfd.vpos_fold s
    have hvs1 := hfd.vpos_fold (s + 1)
    have hds := hfd.dirSign_fold s
    rw [hnext] at hvs1
    by_cases hev : Even s
    · -- descending sweep from the high cap to the low cap
      rw [if_pos hev] at hvs hds
      have hdir : ∀ i, a + s * d + 1 ≤ i → i < a + s * d + d + 1 → dirSign F η₀ i = -1 := by
        intro i hi hib; rw [hstep i hi hib, hds]
      have hnotev : ¬ Even (s + 1) := by simp [Nat.even_add_one, hev]
      rw [if_neg hnotev] at hvs1
      refine ⟨?_, ?_⟩
      · have := vpos_anti (a := a + s * d + 1) (b := a + s * d + d + 1)
          (fun i hi hib => hdir i hi hib) h1 (by omega) le_rfl
        linarith [hvs1 ▸ this]
      · have := vpos_anti (a := a + s * d + 1) (b := a + s * d + d + 1)
          (fun i hi hib => hdir i hi hib) le_rfl h1 (by omega)
        linarith [hvs ▸ this]
    · -- ascending sweep from the low cap to the high cap
      rw [if_neg hev] at hvs hds
      have hev1 : Even (s + 1) := by simp [Nat.even_add_one, hev]
      rw [if_pos hev1] at hvs1
      have hdir : ∀ i, a + s * d + 1 ≤ i → i < a + s * d + d + 1 → dirSign F η₀ i = 1 := by
        intro i hi hib; rw [hstep i hi hib, hds]; ring
      refine ⟨?_, ?_⟩
      · have := vpos_mono (a := a + s * d + 1) (b := a + s * d + d + 1)
          (fun i hi hib => hdir i hi hib) le_rfl h1 (by omega)
        linarith [hvs ▸ this]
      · have := vpos_mono (a := a + s * d + 1) (b := a + s * d + d + 1)
          (fun i hi hib => hdir i hi hib) h1 (by omega) le_rfl
        linarith [hvs1 ▸ this]

/-- **The margin at a non-fold vertex**: a vertex which is not a cap is at least one edge length
away from both caps. -/
theorem interior_margin (hfd : FoldData F η₀ a d) {j : ℕ} (hj : ¬ IsFold F η₀ j) :
    vpos F η₀ (a + d + 1) + minLen Γ η₀.1 ≤ vpos F η₀ (j + 1) ∧
      vpos F η₀ (j + 1) ≤ vpos F η₀ (a + 1) - minLen Γ η₀.1 := by
  have hd := hfd.consec.gap_pos
  have hlow := hfd.low_nonpos
  have hml : ∀ i : ℕ, minLen Γ η₀.1 ≤ edgeLen F η₀ i := fun i => minLen_le_edgeLen η₀.1 i
  rcases lt_or_ge j a with hja | hja
  · -- on the initial ascending sweep
    have hmono : ∀ i, (0 : ℕ) ≤ i → i < a + 1 → dirSign F η₀ i = 1 :=
      fun i _ hi => hfd.dirSign_before (by omega)
    have hup : vpos F η₀ (j + 1) ≤ vpos F η₀ a :=
      vpos_mono hmono (by omega) (by omega) (by omega)
    have hstep : vpos F η₀ (a + 1) = vpos F η₀ a + edgeLen F η₀ a := by
      rw [vpos_succ, hfd.dirSign_before (j := a) le_rfl]; ring
    have hlo : vpos F η₀ 1 ≤ vpos F η₀ (j + 1) :=
      vpos_mono hmono (by omega) (by omega) (by omega)
    have hv1 : vpos F η₀ 1 = edgeLen F η₀ 0 := by rw [vpos_succ]; simp
    exact ⟨by linarith [hml 0], by linarith [hml a]⟩
  · -- inside the sweep number `s`
    have hmod := Nat.div_add_mod (j - a) d
    have hrd : (j - a) % d < d := Nat.mod_lt _ hd
    obtain ⟨P, hP⟩ : ∃ P, d * ((j - a) / d) = P := ⟨_, rfl⟩
    rw [hP] at hmod
    set s := (j - a) / d with hs
    have hsd : s * d = P := by rw [Nat.mul_comm]; exact hP
    have hr0 : (j - a) % d ≠ 0 := by
      intro h0
      exact hj (hfd.isFold_iff.mpr ⟨s, by rw [hsd]; omega⟩)
    have h1 : a + s * d + 1 ≤ j := by rw [hsd]; omega
    have h2 : j + 1 ≤ a + s * d + d := by rw [hsd]; omega
    have hstep : ∀ i, a + s * d + 1 ≤ i → i < a + s * d + d + 1 →
        dirSign F η₀ i = -dirSign F η₀ (a + s * d) :=
      fun i hi hib => hfd.sweep_dir s hi (by omega)
    have hnext : a + (s + 1) * d + 1 = a + s * d + d + 1 := by ring_nf
    have hvs := hfd.vpos_fold s
    have hvs1 := hfd.vpos_fold (s + 1)
    have hds := hfd.dirSign_fold s
    rw [hnext] at hvs1
    by_cases hev : Even s
    · rw [if_pos hev] at hvs hds
      have hnotev : ¬ Even (s + 1) := by simp [Nat.even_add_one, hev]
      rw [if_neg hnotev] at hvs1
      have hdir : ∀ i, a + s * d + 1 ≤ i → i < a + s * d + d + 1 → dirSign F η₀ i = -1 := by
        intro i hi hib; rw [hstep i hi hib, hds]
      have hA := vpos_le_sub_edgeLen (a := a + s * d + 1) (b := a + s * d + d + 1)
        (fun i hi hib => hdir i hi hib) (m := j + 1) (n := a + s * d + d + 1)
        (by omega) (by omega) le_rfl
      have hB := vpos_le_sub_edgeLen (a := a + s * d + 1) (b := a + s * d + d + 1)
        (fun i hi hib => hdir i hi hib) (m := a + s * d + 1) (n := j + 1)
        le_rfl (by omega) (by omega)
      rw [hvs1] at hA
      rw [hvs] at hB
      exact ⟨by linarith [hml (j + 1)], by linarith [hml (a + s * d + 1)]⟩
    · rw [if_neg hev] at hvs hds
      have hev1 : Even (s + 1) := by simp [Nat.even_add_one, hev]
      rw [if_pos hev1] at hvs1
      have hdir : ∀ i, a + s * d + 1 ≤ i → i < a + s * d + d + 1 → dirSign F η₀ i = 1 := by
        intro i hi hib; rw [hstep i hi hib, hds]; ring
      have hA := vpos_add_edgeLen_le (a := a + s * d + 1) (b := a + s * d + d + 1)
        (fun i hi hib => hdir i hi hib) (m := a + s * d + 1) (n := j + 1)
        le_rfl (by omega) (by omega)
      have hB := vpos_add_edgeLen_le (a := a + s * d + 1) (b := a + s * d + d + 1)
        (fun i hi hib => hdir i hi hib) (m := j + 1) (n := a + s * d + d + 1)
        (by omega) (by omega) le_rfl
      rw [hvs] at hA
      rw [hvs1] at hB
      exact ⟨by linarith [hml (a + s * d + 1)], by linarith [hml (j + 1)]⟩

end FoldData

/-! ### The corridor -/

/-- **The corridor of the itinerary of `η₀`**: the straight microscopic tube in which the whole
routing component is laid out, together with everything the microscopic run needs.  The two caps
are `low` and `high`; every fold of the routing law happens exactly at a cap, and every other
vertex keeps a distance of at least `margin` from both. -/
structure Corridor (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (M : ℕ) where
  /-- the coordinate of the lower cap -/
  low : ℝ
  /-- the coordinate of the upper cap -/
  high : ℝ
  /-- the margin kept by every vertex which is not a cap -/
  margin : ℝ
  margin_pos : 0 < margin
  margin_le : ∀ e : Γ.Edge, margin ≤ Γ.length e
  low_nonpos : low ≤ 0
  /-- every vertex of the run lies in the corridor -/
  mem : ∀ j ≤ M + 1, vpos F η₀ j ∈ Icc low high
  /-- a fold happens exactly at a cap, on the side the particle is moving towards -/
  cap : ∀ j ≤ M, IsFold F η₀ j →
    (dirSign F η₀ j = 1 ∧ vpos F η₀ (j + 1) = high) ∨
      (dirSign F η₀ j = -1 ∧ vpos F η₀ (j + 1) = low)
  /-- a vertex which is not a fold keeps the margin from both caps -/
  interior : ∀ j ≤ M, ¬ IsFold F η₀ j →
    vpos F η₀ (j + 1) ∈ Icc (low + margin) (high - margin)

namespace Corridor

variable {M : ℕ} (C : Corridor F η₀ M)

theorem margin_le_high : C.margin ≤ C.high := by
  have h1 : vpos F η₀ 1 ∈ Icc C.low C.high := C.mem 1 (by omega)
  have h2 : vpos F η₀ 1 = Γ.length η₀.1 := by
    rw [vpos_succ]; simp [edgeLen_def]
  have := C.margin_le η₀.1
  rw [h2] at h1
  linarith [h1.2]

theorem low_lt_high : C.low < C.high := by
  have := C.margin_le_high
  have := C.margin_pos
  have := C.low_nonpos
  linarith

end Corridor

/-- **Every routing component has a corridor.**  If the itinerary folds, the corridor is the
interval between the two fold positions; if it does not — a circle component of the resolved
`1`-manifold — the caps are placed beyond the finite horizon of the run. -/
theorem exists_corridor (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (M : ℕ) :
    ∃ C : Corridor F η₀ M, C.margin = minLen Γ η₀.1 := by
  have hmp := minLen_pos Γ η₀.1
  by_cases hf : ∃ k, IsFold F η₀ k
  · obtain ⟨a, d, hfd⟩ := exists_foldData hf
    refine ⟨{ low := vpos F η₀ (a + d + 1)
              high := vpos F η₀ (a + 1)
              margin := minLen Γ η₀.1
              margin_pos := hmp
              margin_le := fun e => minLen_le Γ η₀.1 e
              low_nonpos := hfd.low_nonpos
              mem := fun j _ => hfd.vpos_mem j
              cap := ?_
              interior := fun j _ hj => ⟨(hfd.interior_margin hj).1,
                (hfd.interior_margin hj).2⟩ }, rfl⟩
    intro j _ hj
    obtain ⟨s, rfl⟩ := hfd.isFold_iff.mp hj
    have hd := hfd.dirSign_fold s
    have hv := hfd.vpos_fold s
    by_cases hev : Even s
    · rw [if_pos hev] at hd hv
      exact Or.inl ⟨hd, hv⟩
    · rw [if_neg hev] at hd hv
      exact Or.inr ⟨hd, hv⟩
  · push_neg at hf
    have hdir : ∀ i : ℕ, dirSign F η₀ i = 1 :=
      fun i => dirSign_eq_one_of_no_fold fun l _ => hf l
    have hmono : ∀ {m n : ℕ}, m ≤ n → vpos F η₀ m ≤ vpos F η₀ n := by
      intro m n hmn
      exact vpos_mono (a := 0) (b := n) (fun i _ _ => hdir i) (by omega) hmn le_rfl
    refine ⟨{ low := -minLen Γ η₀.1
              high := vpos F η₀ (M + 2) + minLen Γ η₀.1
              margin := minLen Γ η₀.1
              margin_pos := hmp
              margin_le := fun e => minLen_le Γ η₀.1 e
              low_nonpos := by linarith
              mem := ?_
              cap := fun j _ hj => absurd hj (hf j)
              interior := ?_ }, rfl⟩
    · intro j hj
      have h1 : vpos F η₀ 0 ≤ vpos F η₀ j := hmono (Nat.zero_le j)
      have h2 : vpos F η₀ j ≤ vpos F η₀ (M + 2) := hmono (by omega)
      rw [vpos_zero] at h1
      exact ⟨by linarith, by linarith⟩
    · intro j hj _
      have h1 : vpos F η₀ 0 ≤ vpos F η₀ (j + 1) := hmono (Nat.zero_le _)
      have h2 : vpos F η₀ (j + 1) ≤ vpos F η₀ (M + 2) := hmono (by omega)
      rw [vpos_zero] at h1
      exact ⟨by linarith, by linarith⟩

end HamiltonianMetricGraphs
