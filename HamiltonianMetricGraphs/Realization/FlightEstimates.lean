/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.HybridChain

/-!
# Quantitative estimates for a single flight

A *flight* is one piece of a hybrid chain: a curve on a time interval `[a, b]` that solves
Hamilton's equations on an edge up to a tolerance `ρ` and stays in the tube (longitudinal
coordinate in `[o, L - o]`).  This file proves the elementary estimates used by the
transverse-crossing and no-Zeno arguments:

* momentum drift `|p t - p s| ≤ (R + ρ)(t - s)` from the force bound `R`;
* coordinate travel `|q t - q s| ≤ (B + ρ)(t - s)` from a momentum bound `B`;
* directed motion: a momentum bounded away from `0` in one direction moves the coordinate
  monotonically;
* **no early end**: a flight departing a vertex with outgoing speed `≥ c`, or starting at
  distance `≥ μ` from both tube boundaries, lasts at least a fixed positive time;
* **transverse crossing**: a flight heading towards a vertex with speed `≥ m` from distance
  `≤ d` enters the router next to that vertex within time `4d/m`, and its momentum changes by at
  most `(R + ρ) · 4d/m` meanwhile.

Mathematical proof steps: "no-Zeno lower bound between impacts" and "convergence of impact
times using transverse crossing".
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- One flight of a hybrid chain, isolated: on `[a, b]` the curve solves the edge Hamiltonian
system up to tolerance `ρ` (with derivative candidate `w`) and stays in the tube of offset `o`. -/
structure IsFlight (e : Γ.Edge) (o ρ a b : ℝ) (curve w : ℝ → ℝ × ℝ) : Prop where
  ode : ∀ t ∈ Icc a b, dist (w t) (V.edgeVectorField e (curve t)) ≤ ρ ∧
    HasDerivWithinAt curve (w t) (Icc a b) t
  tube : ∀ t ∈ Icc a b, (curve t).1 ∈ Icc o (Γ.length e - o)

namespace HybridChain

variable {V} {F : RoutingLaw Γ} {P : ChainParams} (c : HybridChain V F P)

/-- Every flight of a hybrid chain is a flight in the sense of `IsFlight`. -/
theorem isFlight {j : ℕ} (hj : j ≤ c.N) :
    ∃ w : ℝ → ℝ × ℝ,
      V.IsFlight (c.edge j) P.offset P.odeErr (c.start j) (c.stop j) (c.curve j) w := by
  obtain ⟨w, hw⟩ := c.flight_ode j hj
  exact ⟨w, ⟨hw, c.flight_tube j hj⟩⟩

end HybridChain

namespace IsFlight

variable {V} {e : Γ.Edge} {o ρ a b : ℝ} {curve w : ℝ → ℝ × ℝ}

theorem mono (h : V.IsFlight e o ρ a b curve w) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    V.IsFlight e o ρ a' b' curve w := by
  have hsub : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha hb
  exact ⟨fun t ht => ⟨(h.ode t (hsub ht)).1, ((h.ode t (hsub ht)).2).mono hsub⟩,
    fun t ht => h.tube t (hsub ht)⟩

theorem physical (h : V.IsFlight e o ρ a b curve w) (ho : 0 ≤ o) {t : ℝ} (ht : t ∈ Icc a b) :
    (curve t).1 ∈ Icc (0 : ℝ) (Γ.length e) :=
  ⟨ho.trans (h.tube t ht).1, (h.tube t ht).2.trans (by linarith)⟩

theorem hasDerivWithinAt (h : V.IsFlight e o ρ a b curve w) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt curve (w t) (Icc a b) t :=
  (h.ode t ht).2

theorem continuousOn (h : V.IsFlight e o ρ a b curve w) : ContinuousOn curve (Icc a b) :=
  fun _ ht => (h.hasDerivWithinAt ht).continuousWithinAt

theorem deriv_fst (h : V.IsFlight e o ρ a b curve w) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => (curve s).1) (w t).1 (Icc a b) t :=
  (h.hasDerivWithinAt ht).fst_comp

theorem deriv_snd (h : V.IsFlight e o ρ a b curve w) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => (curve s).2) (w t).2 (Icc a b) t :=
  (h.hasDerivWithinAt ht).snd_comp

/-- The position equation `q' = p` holds up to the tolerance. -/
theorem abs_fst_sub_le (h : V.IsFlight e o ρ a b curve w) {t : ℝ} (ht : t ∈ Icc a b) :
    |(w t).1 - (curve t).2| ≤ ρ := by
  have := (h.ode t ht).1
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at this
  exact this.1

/-- The momentum equation `p' = -V'(q)` holds up to the tolerance. -/
theorem abs_snd_sub_le (h : V.IsFlight e o ρ a b curve w) {t : ℝ} (ht : t ∈ Icc a b) :
    |(w t).2 - V.force e (curve t).1| ≤ ρ := by
  have := (h.ode t ht).1
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at this
  exact this.2

/-- Momentum drift from the force bound: `|p t - p s| ≤ (R + ρ)(t - s)`. -/
theorem momentum_drift (h : V.IsFlight e o ρ a b curve w) (ho : 0 ≤ o) {R : ℝ}
    (hR : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.force e q| ≤ R) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    |(curve t).2 - (curve s).2| ≤ (R + ρ) * (t - s) := by
  refine abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le (f' := fun u => (w u).2)
    (fun u hu => h.deriv_snd hu) (fun u hu => ?_) hs ht hst
  have h1 := h.abs_snd_sub_le hu
  have h2 := hR _ (h.physical ho hu)
  calc |(w u).2| = |((w u).2 - V.force e (curve u).1) + V.force e (curve u).1| := by ring_nf
    _ ≤ |(w u).2 - V.force e (curve u).1| + |V.force e (curve u).1| := abs_add_le _ _
    _ ≤ ρ + R := add_le_add h1 h2
    _ = R + ρ := by ring

/-- A momentum bound at the start propagates along the flight. -/
theorem abs_momentum_le (h : V.IsFlight e o ρ a b curve w) (ho : 0 ≤ o) {R : ℝ}
    (hR : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.force e q| ≤ R) {B : ℝ}
    (hB : |(curve a).2| ≤ B) (hab : a ≤ b) {t : ℝ} (ht : t ∈ Icc a b) :
    |(curve t).2| ≤ B + (R + ρ) * (t - a) := by
  have hd := h.momentum_drift ho hR (left_mem_Icc.mpr hab) ht ht.1
  calc |(curve t).2| = |((curve t).2 - (curve a).2) + (curve a).2| := by ring_nf
    _ ≤ |(curve t).2 - (curve a).2| + |(curve a).2| := abs_add_le _ _
    _ ≤ (R + ρ) * (t - a) + B := add_le_add hd hB
    _ = B + (R + ρ) * (t - a) := by ring

/-- Coordinate travel from a momentum bound: `|q t - q s| ≤ (B + ρ)(t - s)`. -/
theorem coordinate_travel (h : V.IsFlight e o ρ a b curve w) {B : ℝ}
    (hB : ∀ u ∈ Icc a b, |(curve u).2| ≤ B) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    |(curve t).1 - (curve s).1| ≤ (B + ρ) * (t - s) := by
  refine abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le (f' := fun u => (w u).1)
    (fun u hu => h.deriv_fst hu) (fun u hu => ?_) hs ht hst
  have h1 := h.abs_fst_sub_le hu
  have h2 := hB u hu
  calc |(w u).1| = |((w u).1 - (curve u).2) + (curve u).2| := by ring_nf
    _ ≤ |(w u).1 - (curve u).2| + |(curve u).2| := abs_add_le _ _
    _ ≤ ρ + B := add_le_add h1 h2
    _ = B + ρ := by ring

/-- Directed motion: if `m ≤ σ p` on the flight (with `|σ| = 1`) and `ρ ≤ m / 2`, then
`σ q` increases at rate at least `m / 2`. -/
theorem directed (h : V.IsFlight e o ρ a b curve w) {σ m : ℝ} (hσ : |σ| = 1)
    (hm : ∀ u ∈ Icc a b, m ≤ σ * (curve u).2) (hρ : ρ ≤ m / 2) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    m / 2 * (t - s) ≤ σ * ((curve t).1 - (curve s).1) := by
  have key := mul_sub_le_image_sub_of_le_hasDerivWithinAt' (f := fun u => σ * (curve u).1)
    (f' := fun u => σ * (w u).1) (C := m / 2)
    (fun u hu => (h.deriv_fst hu).const_mul σ) (fun u hu => ?_) hs ht hst
  · linarith [key]
  · have h1 := h.abs_fst_sub_le hu
    have h2 := hm u hu
    have h3 : |σ * ((w u).1 - (curve u).2)| ≤ ρ := by
      rw [abs_mul, hσ, one_mul]; exact h1
    have h4 := (abs_le.mp h3).1
    have : σ * (w u).1 = σ * (curve u).2 + σ * ((w u).1 - (curve u).2) := by ring
    linarith

/-- Distance travelled in phase space: `dist (curve t) (curve s) ≤ C (t - s)` when the
derivative candidate is bounded by `C` in norm. -/
theorem dist_le (h : V.IsFlight e o ρ a b curve w) {C : ℝ}
    (hC : ∀ u ∈ Icc a b, ‖w u‖ ≤ C) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    dist (curve t) (curve s) ≤ C * (t - s) :=
  dist_le_mul_sub_of_norm_hasDerivWithinAt_le (fun _ hu => h.hasDerivWithinAt hu) hC hs ht hst

/-- The derivative candidate is bounded by `max (B + ρ) (R + ρ)` in norm when the momentum is
bounded by `B`. -/
theorem norm_w_le (h : V.IsFlight e o ρ a b curve w) (ho : 0 ≤ o) {R : ℝ}
    (hR : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.force e q| ≤ R) {B : ℝ}
    (hB : ∀ u ∈ Icc a b, |(curve u).2| ≤ B) {u : ℝ} (hu : u ∈ Icc a b) :
    ‖w u‖ ≤ max (B + ρ) (R + ρ) := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := h.abs_fst_sub_le hu
  have h2 := h.abs_snd_sub_le hu
  have h3 := hB u hu
  have h4 := hR _ (h.physical ho hu)
  apply max_le
  · calc |(w u).1| = |((w u).1 - (curve u).2) + (curve u).2| := by ring_nf
      _ ≤ |(w u).1 - (curve u).2| + |(curve u).2| := abs_add_le _ _
      _ ≤ ρ + B := add_le_add h1 h3
      _ ≤ max (B + ρ) (R + ρ) := by rw [add_comm]; exact le_max_left _ _
  · calc |(w u).2| = |((w u).2 - V.force e (curve u).1) + V.force e (curve u).1| := by ring_nf
      _ ≤ |(w u).2 - V.force e (curve u).1| + |V.force e (curve u).1| := abs_add_le _ _
      _ ≤ ρ + R := add_le_add h2 h4
      _ ≤ max (B + ρ) (R + ρ) := by rw [add_comm]; exact le_max_right _ _

/-! ### Geometry of the two tube boundaries -/

/-- In the tube, the signed distance to the vertex of a germ `ζ` on the edge is at most `-o`. -/
theorem sign_mul_sub_coordinate_le (h : V.IsFlight e o ρ a b curve w) {ζ : Γ.EdgeEnd}
    (hζ : ζ.1 = e) {t : ℝ} (ht : t ∈ Icc a b) :
    EdgeEnd.sign Γ ζ * ((curve t).1 - EdgeEnd.coordinate Γ ζ) ≤ -o := by
  have htube := h.tube t ht
  rcases ζ with ⟨e', s⟩
  change e' = e at hζ
  subst hζ
  cases s
  · simp only [edgeEnd_sign_false, edgeEnd_coordinate_false, sub_zero]
    linarith [htube.1]
  · simp only [edgeEnd_sign_true, edgeEnd_coordinate_true, one_mul]
    linarith [htube.2]

/-- The tube boundary next to a germ `ζ'` on the edge, expressed relative to another germ `ζ`
of the same edge: it is the near boundary if `ζ' = ζ`, and the far boundary otherwise. -/
theorem boundary_cases {ζ ζ' : Γ.EdgeEnd} (hζ : ζ.1 = e) (hζ' : ζ'.1 = e) (q : ℝ)
    (hq : q = EdgeEnd.coordinate Γ ζ' - EdgeEnd.sign Γ ζ' * o) :
    (ζ' = ζ ∧ EdgeEnd.sign Γ ζ * (q - EdgeEnd.coordinate Γ ζ) = -o) ∨
    (ζ' ≠ ζ ∧ EdgeEnd.sign Γ ζ * (q - EdgeEnd.coordinate Γ ζ) = -(Γ.length e - o)) := by
  rcases ζ with ⟨e₁, s₁⟩
  rcases ζ' with ⟨e₂, s₂⟩
  change e₁ = e at hζ
  change e₂ = e at hζ'
  subst hζ hζ'
  cases s₁ <;> cases s₂
  · left; refine ⟨rfl, ?_⟩
    simp only [edgeEnd_sign_false, edgeEnd_coordinate_false] at hq ⊢
    rw [hq]; ring
  · right; refine ⟨by simp, ?_⟩
    simp only [edgeEnd_sign_false, edgeEnd_coordinate_false, edgeEnd_sign_true,
      edgeEnd_coordinate_true] at hq ⊢
    rw [hq]; ring
  · right; refine ⟨by simp, ?_⟩
    simp only [edgeEnd_sign_false, edgeEnd_coordinate_false, edgeEnd_sign_true,
      edgeEnd_coordinate_true] at hq ⊢
    rw [hq]; ring
  · left; refine ⟨rfl, ?_⟩
    simp only [edgeEnd_sign_true, edgeEnd_coordinate_true] at hq ⊢
    rw [hq]; ring

/-! ### No early end -/

/-- **No early end, departure form.**  A flight that starts within `L/4` of the vertex of the
germ `ζ`, moving away from it with speed at least `c`, and ends at a tube boundary, lasts at
least `min (c / (2(R+2))) (L / (2(B+c+2)))`.  This is the quantitative core of the no-Zeno
estimate: inside the collar the outgoing momentum cannot reverse (force bound), so the flight
cannot return to `ζ`, and it cannot reach the far end of the edge in a short time (speed bound).
-/
theorem duration_lower_bound_departure (h : V.IsFlight e o ρ a b curve w) (hab : a < b)
    {R : ℝ} (hR : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.force e q| ≤ R) (hR0 : 0 ≤ R)
    (hρ1 : ρ ≤ 1) (ho0 : 0 ≤ o) (ho : o ≤ Γ.length e / 4)
    {ζ : Γ.EdgeEnd} (hζ : ζ.1 = e)
    (hstart : |(curve a).1 - EdgeEnd.coordinate Γ ζ| ≤ Γ.length e / 4)
    {c B : ℝ} (hc : 0 < c) (hρc : ρ ≤ c / 4)
    (hout : EdgeEnd.sign Γ ζ * (curve a).2 ≤ -c) (hB : |(curve a).2| ≤ B)
    {ζ' : Γ.EdgeEnd} (hζ' : ζ'.1 = e)
    (hend : (curve b).1 = EdgeEnd.coordinate Γ ζ' - EdgeEnd.sign Γ ζ' * o) :
    min (c / (2 * (R + 2))) (Γ.length e / (2 * (B + c + 2))) ≤ b - a := by
  have hL := Γ.length_pos e
  have hσ : |EdgeEnd.sign Γ ζ| = 1 := RoutingLaw.edgeEnd_abs_sign ζ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  by_contra hcon
  rw [not_le] at hcon
  have h1 : b - a < c / (2 * (R + 2)) := lt_of_lt_of_le hcon (min_le_left _ _)
  have h2 : b - a < Γ.length e / (2 * (B + c + 2)) := lt_of_lt_of_le hcon (min_le_right _ _)
  -- Momentum stays outgoing with speed `≥ c/2` on the whole (short) flight.
  have hdrift : ∀ t ∈ Icc a b, |(curve t).2 - (curve a).2| ≤ c / 2 := by
    intro t ht
    have := h.momentum_drift ho0 hR (left_mem_Icc.mpr hab.le) ht ht.1
    have hRρ : (R + ρ) * (t - a) ≤ (R + 1) * (b - a) := by
      apply mul_le_mul (by linarith) (by linarith [ht.2]) (by linarith [ht.1]) (by linarith)
    have hb : (R + 1) * (b - a) ≤ c / 2 := by
      rw [lt_div_iff₀ (by linarith)] at h1
      nlinarith
    linarith
  have hmom : ∀ t ∈ Icc a b, c / 2 ≤ -EdgeEnd.sign Γ ζ * (curve t).2 := by
    intro t ht
    have hd := (abs_le.mp (hdrift t ht))
    have h3 : |EdgeEnd.sign Γ ζ * ((curve t).2 - (curve a).2)| ≤ c / 2 := by
      rw [abs_mul, hσ, one_mul]; exact hdrift t ht
    have h4 := (abs_le.mp h3).2
    have : EdgeEnd.sign Γ ζ * (curve t).2 =
        EdgeEnd.sign Γ ζ * (curve a).2 + EdgeEnd.sign Γ ζ * ((curve t).2 - (curve a).2) := by ring
    linarith
  -- Hence the coordinate moves away from `ζ`.
  have hσ' : |-EdgeEnd.sign Γ ζ| = 1 := by rw [abs_neg]; exact hσ
  have hmove := h.directed hσ' hmom (by linarith) (left_mem_Icc.mpr hab.le)
    (right_mem_Icc.mpr hab.le) hab.le
  -- Speed bound along the flight.
  have hspeed : ∀ t ∈ Icc a b, |(curve t).2| ≤ B + c / 2 := by
    intro t ht
    have := hdrift t ht
    calc |(curve t).2| = |((curve t).2 - (curve a).2) + (curve a).2| := by ring_nf
      _ ≤ |(curve t).2 - (curve a).2| + |(curve a).2| := abs_add_le _ _
      _ ≤ c / 2 + B := add_le_add this hB
      _ = B + c / 2 := by ring
  have htravel := h.coordinate_travel hspeed (left_mem_Icc.mpr hab.le)
    (right_mem_Icc.mpr hab.le) hab.le
  have hsa := h.sign_mul_sub_coordinate_le hζ (left_mem_Icc.mpr hab.le)
  rcases boundary_cases (o := o) hζ hζ' _ hend with ⟨_, hnear⟩ | ⟨_, hfar⟩
  · -- returning to the departure germ is impossible: the signed distance strictly decreased
    have : EdgeEnd.sign Γ ζ * ((curve b).1 - EdgeEnd.coordinate Γ ζ) =
        EdgeEnd.sign Γ ζ * ((curve a).1 - EdgeEnd.coordinate Γ ζ) +
          EdgeEnd.sign Γ ζ * ((curve b).1 - (curve a).1) := by ring
    have hpos : 0 < c / 2 / 2 * (b - a) := by
      apply mul_pos (by linarith) (by linarith)
    nlinarith
  · -- reaching the far end needs to travel at least `L - 2o ≥ L/2`
    have hfar' : (curve b).1 - (curve a).1 =
        EdgeEnd.sign Γ ζ * (EdgeEnd.sign Γ ζ * ((curve b).1 - EdgeEnd.coordinate Γ ζ) -
          EdgeEnd.sign Γ ζ * ((curve a).1 - EdgeEnd.coordinate Γ ζ)) := by
      have hsq := Γ.edgeEnd_sign_sq ζ
      have : EdgeEnd.sign Γ ζ * EdgeEnd.sign Γ ζ = 1 := by nlinarith
      calc (curve b).1 - (curve a).1
          = (EdgeEnd.sign Γ ζ * EdgeEnd.sign Γ ζ) * ((curve b).1 - (curve a).1) := by
            rw [this, one_mul]
        _ = _ := by ring
    have hdist : Γ.length e / 2 ≤ |(curve b).1 - (curve a).1| := by
      rw [hfar', abs_mul, hσ, one_mul, hfar]
      have hsa' : |EdgeEnd.sign Γ ζ * ((curve a).1 - EdgeEnd.coordinate Γ ζ)| ≤
          Γ.length e / 4 := by rw [abs_mul, hσ, one_mul]; exact hstart
      have := (abs_le.mp hsa').1
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hbd : (B + c / 2 + ρ) * (b - a) < Γ.length e / 2 := by
      rw [lt_div_iff₀ (by linarith)] at h2
      nlinarith
    linarith

/-- **No early end, interior form.**  A flight starting at distance at least `μ` from both tube
boundaries and ending at a tube boundary lasts at least `min 1 (μ / (B + R + 2))`. -/
theorem duration_lower_bound_interior (h : V.IsFlight e o ρ a b curve w) (hab : a < b)
    {R : ℝ} (hR : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.force e q| ≤ R) (hR0 : 0 ≤ R)
    (hρ1 : ρ ≤ 1) (ho0 : 0 ≤ o)
    {μ B : ℝ} (hB : |(curve a).2| ≤ B)
    (hstart : (curve a).1 ∈ Icc (o + μ) (Γ.length e - o - μ))
    (hend : (curve b).1 = o ∨ (curve b).1 = Γ.length e - o) :
    min 1 (μ / (B + R + 2)) ≤ b - a := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  by_contra hcon
  rw [not_le] at hcon
  have h1 : b - a < 1 := lt_of_lt_of_le hcon (min_le_left _ _)
  have h2 : b - a < μ / (B + R + 2) := lt_of_lt_of_le hcon (min_le_right _ _)
  have hspeed : ∀ t ∈ Icc a b, |(curve t).2| ≤ B + R + 1 := by
    intro t ht
    have := h.abs_momentum_le ho0 hR hB hab.le ht
    have : (R + ρ) * (t - a) ≤ R + 1 := by
      calc (R + ρ) * (t - a) ≤ (R + 1) * 1 := by
            apply mul_le_mul (by linarith) (by linarith [ht.1, ht.2]) (by linarith [ht.1])
              (by linarith)
        _ = R + 1 := by ring
    linarith
  have htravel := h.coordinate_travel hspeed (left_mem_Icc.mpr hab.le)
    (right_mem_Icc.mpr hab.le) hab.le
  have hbd : (B + R + 1 + ρ) * (b - a) < μ := by
    rw [lt_div_iff₀ (by linarith)] at h2
    nlinarith
  rcases hend with hend | hend <;> rw [hend] at htravel <;>
    · have := abs_le.mp htravel
      linarith [hstart.1, hstart.2]

/-! ### Transverse crossing -/

/-- **Transverse crossing.**  Suppose that at time `t₀` the flight is within distance `d` of the
vertex of the germ `η` and heading towards it with speed at least `m` (`m ≤ σ(η) p`), and that
`d` is small compared with `m` (`4d/m < m / (2(R+ρ+1))`, so the momentum cannot reverse before
the router is reached).  Then the flight ends by time `t₀ + 4d/m` (it must enter the router),
the end point is the tube boundary next to `η`, and the momentum changes by at most
`(R+ρ) · 4d/m`. -/
theorem crossing (h : V.IsFlight e o ρ a b curve w) (hab : a ≤ b)
    {R : ℝ} (hR : ∀ q ∈ Icc (0 : ℝ) (Γ.length e), |V.force e q| ≤ R) (hR0 : 0 ≤ R)
    (hρ0 : 0 ≤ ρ) (ho0 : 0 ≤ o) (ho : o ≤ Γ.length e / 4)
    {η : Γ.EdgeEnd} (hη : η.1 = e) {t₀ m d : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hm : 0 < m) (hρm : ρ ≤ m / 4)
    (hin : m ≤ EdgeEnd.sign Γ η * (curve t₀).2)
    (hdist : -d ≤ EdgeEnd.sign Γ η * ((curve t₀).1 - EdgeEnd.coordinate Γ η))
    (hdL : d ≤ Γ.length e / 4)
    (hhorizon : 4 * d / m < m / (2 * (R + ρ + 1))) :
    b - t₀ ≤ 4 * d / m ∧
    |(curve b).2 - (curve t₀).2| ≤ (R + ρ) * (4 * d / m) ∧
    ∀ η' : Γ.EdgeEnd, η'.1 = e →
      (curve b).1 = EdgeEnd.coordinate Γ η' - EdgeEnd.sign Γ η' * o → η' = η := by
  have hL := Γ.length_pos e
  have hσ : |EdgeEnd.sign Γ η| = 1 := RoutingLaw.edgeEnd_abs_sign η
  set T₁ := m / (2 * (R + ρ + 1)) with hT₁
  have hT₁pos : 0 < T₁ := by positivity
  -- On `[t₀, t₀ + T₁]` the momentum keeps heading towards `η` with speed `≥ m/2`.
  have hmom : ∀ t ∈ Icc t₀ (min b (t₀ + T₁)), m / 2 ≤ EdgeEnd.sign Γ η * (curve t).2 := by
    intro t ht
    have htb : t ∈ Icc a b := ⟨ht₀.1.trans ht.1, ht.2.trans (min_le_left _ _)⟩
    have hdr := h.momentum_drift ho0 hR ht₀ htb ht.1
    have hle : (R + ρ) * (t - t₀) ≤ m / 2 := by
      have : t - t₀ ≤ T₁ := by linarith [ht.2, min_le_right b (t₀ + T₁)]
      calc (R + ρ) * (t - t₀) ≤ (R + ρ + 1) * T₁ := by
            apply mul_le_mul (by linarith) this (by linarith [ht.1]) (by linarith)
        _ = m / 2 := by rw [hT₁]; field_simp; try ring
    have h3 : |EdgeEnd.sign Γ η * ((curve t).2 - (curve t₀).2)| ≤ m / 2 := by
      rw [abs_mul, hσ, one_mul]; exact hdr.trans hle
    have h4 := (abs_le.mp h3).1
    have : EdgeEnd.sign Γ η * (curve t).2 =
        EdgeEnd.sign Γ η * (curve t₀).2 + EdgeEnd.sign Γ η * ((curve t).2 - (curve t₀).2) := by
      ring
    linarith
  have hsub : V.IsFlight e o ρ t₀ (min b (t₀ + T₁)) curve w :=
    h.mono ht₀.1 (min_le_left _ _)
  have hmin_mem : min b (t₀ + T₁) ∈ Icc t₀ (min b (t₀ + T₁)) :=
    right_mem_Icc.mpr (le_min ht₀.2 (by linarith))
  -- Directed motion towards `η` on that interval.
  have hmove := hsub.directed hσ hmom (by linarith) (left_mem_Icc.mpr (le_min ht₀.2 (by linarith)))
    hmin_mem (le_min ht₀.2 (by linarith))
  -- The coordinate cannot pass the vertex: signed distance is at most `-o ≤ 0`.
  have hbound := h.sign_mul_sub_coordinate_le hη
    (show min b (t₀ + T₁) ∈ Icc a b from ⟨ht₀.1.trans hmin_mem.1, min_le_left _ _⟩)
  have hkey : m / 2 / 2 * (min b (t₀ + T₁) - t₀) ≤ d := by
    have : EdgeEnd.sign Γ η * ((curve (min b (t₀ + T₁))).1 - EdgeEnd.coordinate Γ η) =
        EdgeEnd.sign Γ η * ((curve (min b (t₀ + T₁))).1 - (curve t₀).1) +
          EdgeEnd.sign Γ η * ((curve t₀).1 - EdgeEnd.coordinate Γ η) := by ring
    linarith
  have hmin_le : min b (t₀ + T₁) - t₀ ≤ 4 * d / m := by
    rw [le_div_iff₀ hm]
    nlinarith
  -- Since `4d/m < T₁`, the minimum is `b`.
  have hbt : b - t₀ ≤ 4 * d / m := by
    by_contra hcon
    rw [not_le] at hcon
    have : min b (t₀ + T₁) - t₀ > 4 * d / m := by
      rcases min_choice b (t₀ + T₁) with hmin | hmin <;> rw [hmin]
      · exact hcon
      · linarith
    linarith
  refine ⟨hbt, ?_, ?_⟩
  · have hdr := h.momentum_drift ho0 hR ht₀ (right_mem_Icc.mpr hab) ht₀.2
    calc |(curve b).2 - (curve t₀).2| ≤ (R + ρ) * (b - t₀) := hdr
      _ ≤ (R + ρ) * (4 * d / m) := by
          apply mul_le_mul_of_nonneg_left hbt (by linarith)
  · intro η' hη' hend
    -- `b` lies in the directed interval, so the signed distance to `η` is `≥ -d`.
    have hbmem : b ∈ Icc t₀ (min b (t₀ + T₁)) := by
      refine ⟨ht₀.2, le_min le_rfl ?_⟩
      linarith
    have hmoveb := hsub.directed hσ hmom (by linarith)
      (left_mem_Icc.mpr (le_min ht₀.2 (by linarith))) hbmem ht₀.2
    have hge : -d ≤ EdgeEnd.sign Γ η * ((curve b).1 - EdgeEnd.coordinate Γ η) := by
      have : EdgeEnd.sign Γ η * ((curve b).1 - EdgeEnd.coordinate Γ η) =
          EdgeEnd.sign Γ η * ((curve b).1 - (curve t₀).1) +
            EdgeEnd.sign Γ η * ((curve t₀).1 - EdgeEnd.coordinate Γ η) := by ring
      have hnn : 0 ≤ m / 2 / 2 * (b - t₀) := by
        apply mul_nonneg (by linarith) (by linarith [ht₀.2])
      linarith
    rcases boundary_cases (o := o) hη hη' _ hend with ⟨heq, _⟩ | ⟨_, hfar⟩
    · exact heq
    · exfalso
      linarith

end IsFlight

/-- Two germs of the same edge with the same tube-boundary coordinate coincide (the two
boundaries are `o` and `L - o`, distinct when `o < L / 2`). -/
theorem germ_eq_of_boundary_eq {e : Γ.Edge} {o : ℝ} (ho : o < Γ.length e / 2)
    {ζ ζ' : Γ.EdgeEnd} (hζ : ζ.1 = e) (hζ' : ζ'.1 = e)
    (h : EdgeEnd.coordinate Γ ζ - EdgeEnd.sign Γ ζ * o =
      EdgeEnd.coordinate Γ ζ' - EdgeEnd.sign Γ ζ' * o) : ζ = ζ' := by
  rcases ζ with ⟨e₁, s₁⟩
  rcases ζ' with ⟨e₂, s₂⟩
  change e₁ = e at hζ
  change e₂ = e at hζ'
  subst hζ hζ'
  cases s₁ <;> cases s₂
  · rfl
  · exfalso
    simp only [edgeEnd_sign_false, edgeEnd_coordinate_false, edgeEnd_sign_true,
      edgeEnd_coordinate_true] at h
    linarith
  · exfalso
    simp only [edgeEnd_sign_false, edgeEnd_coordinate_false, edgeEnd_sign_true,
      edgeEnd_coordinate_true] at h
    linarith
  · rfl

end MechanicalPotential
end HamiltonianMetricGraphs
