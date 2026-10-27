/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ArmDynamics
import HamiltonianMetricGraphs.Realization.MicroscopicChain

/-!
# The projected chain of a microscopic trajectory of the third arm

The same recursion as in `MicroscopicChain.lean`, for the third channel `η₃` of the star.  Here
the graph coordinate on edge `2` *is* the microscopic coordinate `w`, the routers occupy
`w ≤ 8ε` (around `v⋆`) and `w ≥ 1 - 8ε` (around the outer vertex), and **every** flight ends at a
barrier: the junction barrier just below `7ε` realizes `F⋆(η₃) = η₃`, the cap at `w = 1` realizes
the reflection at the outer vertex.  The recursion is therefore over single flights, with the two
barrier types alternating.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

/-! ### The itinerary of a channel at the branching vertex -/

/-- Along an itinerary starting at the branching vertex the endpoint selector alternates. -/
theorem itinerary_snd_alt {η₀ : starGraph.EdgeEnd} (h : η₀.2 = false) (k : ℕ) :
    (starRouting.itinerary η₀ (2 * k)).2 = false ∧
      (starRouting.itinerary η₀ (2 * k + 1)).2 = true := by
  induction k with
  | zero =>
      refine ⟨h, ?_⟩
      rw [show 2 * 0 + 1 = 0 + 1 by ring, itinerary_snd_succ, RoutingLaw.itinerary_zero, h]
      rfl
  | succ m ih =>
      refine ⟨?_, ?_⟩
      · rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, itinerary_snd_succ, ih.2]
        rfl
      · rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, itinerary_snd_succ,
          itinerary_snd_succ, ih.2]
        rfl

theorem itinerary_snd_even₃ (k : ℕ) : (starRouting.itinerary channel₃ (2 * k)).2 = false :=
  (itinerary_snd_alt rfl k).1

theorem itinerary_snd_odd₃ (k : ℕ) : (starRouting.itinerary channel₃ (2 * k + 1)).2 = true :=
  (itinerary_snd_alt rfl k).2

theorem routed₃_snd (j : ℕ) :
    (starRouting.routeGerm (starRouting.itinerary channel₃ j)).2 =
      (starRouting.itinerary channel₃ j).2 := by
  rw [starRouting_routeGerm, starGermMap_snd]

theorem coord₃_even (k : ℕ) :
    EdgeEnd.coordinate starGraph (starRouting.itinerary channel₃ (2 * k)) = 0 :=
  coordinate_of_false (itinerary_snd_even₃ k)

theorem sign₃_even (k : ℕ) :
    EdgeEnd.sign starGraph (starRouting.itinerary channel₃ (2 * k)) = -1 :=
  sign_of_false (itinerary_snd_even₃ k)

theorem coord₃_odd (k : ℕ) :
    EdgeEnd.coordinate starGraph (starRouting.itinerary channel₃ (2 * k + 1)) = 1 :=
  coordinate_of_true starGraph_length_eq_one (itinerary_snd_odd₃ k)

theorem sign₃_odd (k : ℕ) :
    EdgeEnd.sign starGraph (starRouting.itinerary channel₃ (2 * k + 1)) = 1 :=
  sign_of_true (itinerary_snd_odd₃ k)

theorem routed₃_coord_even (k : ℕ) :
    EdgeEnd.coordinate starGraph
      (starRouting.routeGerm (starRouting.itinerary channel₃ (2 * k))) = 0 :=
  coordinate_of_false (by rw [routed₃_snd]; exact itinerary_snd_even₃ k)

theorem routed₃_sign_even (k : ℕ) :
    EdgeEnd.sign starGraph
      (starRouting.routeGerm (starRouting.itinerary channel₃ (2 * k))) = -1 :=
  sign_of_false (by rw [routed₃_snd]; exact itinerary_snd_even₃ k)

theorem routed₃_coord_odd (k : ℕ) :
    EdgeEnd.coordinate starGraph
      (starRouting.routeGerm (starRouting.itinerary channel₃ (2 * k + 1))) = 1 :=
  coordinate_of_true starGraph_length_eq_one (by rw [routed₃_snd]; exact itinerary_snd_odd₃ k)

theorem routed₃_sign_odd (k : ℕ) :
    EdgeEnd.sign starGraph
      (starRouting.routeGerm (starRouting.itinerary channel₃ (2 * k + 1))) = 1 :=
  sign_of_true (by rw [routed₃_snd]; exact itinerary_snd_odd₃ k)

/-! ### A microscopic run of the third arm -/

/-- **The data of an explicit microscopic run along the third arm.**  A genuine trajectory of the
microscopic Hamiltonian at scale `ε`, launched on edge `2` at graph coordinate `q₀` towards the
branching vertex with speed `c`. -/
structure ArmRun where
  /-- the thinness scale -/
  ε : ℝ
  /-- the speed -/
  c : ℝ
  /-- the initial graph coordinate on edge `2` -/
  q₀ : ℝ
  /-- the number of chain flights -/
  N : ℕ
  /-- the microscopic transverse coordinate, which is the graph coordinate of edge `2` -/
  w : ℝ → ℝ
  /-- its momentum -/
  pw : ℝ → ℝ
  N_pos : 1 ≤ N
  eps_pos : 0 < ε
  eps_small : ε ≤ 1 / 1000
  c_ge : 1 ≤ c
  c_le : c ≤ 2
  q_lb : 8 * ε < q₀
  q_ub : q₀ < 1 - 8 * ε
  init_pos : w 0 = q₀
  init_mom : pw 0 = -c
  sol : ArmSolution ε c (((N : ℝ) + 1) * (2 / c + capReflTime ε c)) w pw

namespace ArmRun

/-- The time horizon of the run. -/
noncomputable def horizon (R : ArmRun) : ℝ :=
  ((R.N : ℝ) + 1) * (2 / R.c + capReflTime R.ε R.c)

theorem sol' (R : ArmRun) : ArmSolution R.ε R.c R.horizon R.w R.pw := R.sol

theorem c_pos (R : ArmRun) : 0 < R.c := by linarith [R.c_ge]

theorem c_ne (R : ArmRun) : R.c ≠ 0 := ne_of_gt R.c_pos

theorem tau_pos (R : ArmRun) : 0 < capReflTime R.ε R.c := capReflTime_pos R.eps_pos R.c_ge

theorem tau_le (R : ArmRun) : capReflTime R.ε R.c ≤ 100 * R.ε :=
  capReflTime_le R.eps_pos R.c_ge R.c_le

theorem step_pos (R : ArmRun) : 0 < 2 / R.c + capReflTime R.ε R.c := by
  have := R.tau_pos
  have := R.c_pos
  positivity

/-- The initial distance to `v⋆` of the flight `2k`. -/
noncomputable def radArm (R : ArmRun) : ℕ → ℝ
  | 0 => R.q₀
  | _ + 1 => 1 - 8 * R.ε

@[simp] theorem radArm_zero (R : ArmRun) : radArm R 0 = R.q₀ := rfl
@[simp] theorem radArm_succ (R : ArmRun) (k : ℕ) : radArm R (k + 1) = 1 - 8 * R.ε := rfl

theorem off_lt_radArm (R : ArmRun) (k : ℕ) : 8 * R.ε < radArm R k := by
  cases k with
  | zero => exact R.q_lb
  | succ m => rw [radArm_succ]; linarith [R.eps_pos, R.eps_small]

theorem radArm_le (R : ArmRun) (k : ℕ) : radArm R k ≤ 1 - 8 * R.ε := by
  cases k with
  | zero => exact R.q_ub.le
  | succ m => rw [radArm_succ]

/-- The graph coordinate at which flight `j` starts. -/
noncomputable def startPos (R : ArmRun) (j : ℕ) : ℝ :=
  if j % 2 = 0 then radArm R (j / 2) else 8 * R.ε

/-- The graph coordinate at which flight `j` ends. -/
noncomputable def endPos (R : ArmRun) (j : ℕ) : ℝ :=
  if j % 2 = 0 then 8 * R.ε else 1 - 8 * R.ε

/-- The (constant) graph momentum during flight `j`. -/
noncomputable def momArm (R : ArmRun) (j : ℕ) : ℝ := if j % 2 = 0 then -R.c else R.c

/-- The duration of flight `j`. -/
noncomputable def durArm (R : ArmRun) (j : ℕ) : ℝ :=
  (endPos R j - startPos R j) / momArm R j

theorem startPos_even (R : ArmRun) (k : ℕ) : startPos R (2 * k) = radArm R k := by
  have h1 : 2 * k % 2 = 0 := by omega
  have h2 : 2 * k / 2 = k := by omega
  unfold startPos
  rw [if_pos h1, h2]

theorem startPos_odd (R : ArmRun) (k : ℕ) : startPos R (2 * k + 1) = 8 * R.ε := by
  unfold startPos
  rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]

theorem endPos_even (R : ArmRun) (k : ℕ) : endPos R (2 * k) = 8 * R.ε := by
  unfold endPos
  rw [if_pos (by omega : 2 * k % 2 = 0)]

theorem endPos_odd (R : ArmRun) (k : ℕ) : endPos R (2 * k + 1) = 1 - 8 * R.ε := by
  unfold endPos
  rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]

theorem momArm_even (R : ArmRun) (k : ℕ) : momArm R (2 * k) = -R.c := by
  unfold momArm
  rw [if_pos (by omega : 2 * k % 2 = 0)]

theorem momArm_odd (R : ArmRun) (k : ℕ) : momArm R (2 * k + 1) = R.c := by
  unfold momArm
  rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]

theorem startPos_mem (R : ArmRun) (j : ℕ) : startPos R j ∈ Icc (8 * R.ε) (1 - 8 * R.ε) := by
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    rw [startPos_even]
    exact ⟨(R.off_lt_radArm k).le, R.radArm_le k⟩
  · subst hk
    rw [startPos_odd]
    exact ⟨le_rfl, by linarith [R.eps_pos, R.eps_small]⟩

theorem endPos_mem (R : ArmRun) (j : ℕ) : endPos R j ∈ Icc (8 * R.ε) (1 - 8 * R.ε) := by
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    rw [endPos_even]
    exact ⟨le_rfl, by linarith [R.eps_pos, R.eps_small]⟩
  · subst hk; rw [endPos_odd]; exact ⟨by linarith [R.eps_pos, R.eps_small], le_rfl⟩

theorem momArm_ne (R : ArmRun) (j : ℕ) : momArm R j ≠ 0 := by
  unfold momArm
  split_ifs
  · exact neg_ne_zero.mpr R.c_ne
  · exact R.c_ne

theorem mom_mul_dur (R : ArmRun) (j : ℕ) :
    momArm R j * durArm R j = endPos R j - startPos R j := by
  rw [durArm, mul_div_cancel₀ _ (R.momArm_ne j)]

theorem durArm_even_eq (R : ArmRun) (k : ℕ) :
    durArm R (2 * k) = (radArm R k - 8 * R.ε) / R.c := by
  have hc := R.c_ne
  rw [durArm, endPos_even, startPos_even, momArm_even]
  field_simp
  ring

theorem durArm_odd_eq (R : ArmRun) (k : ℕ) :
    durArm R (2 * k + 1) = (1 - 16 * R.ε) / R.c := by
  have hc := R.c_ne
  rw [durArm, endPos_odd, startPos_odd, momArm_odd]
  ring_nf

theorem durArm_pos (R : ArmRun) (j : ℕ) : 0 < durArm R j := by
  have hc := R.c_pos
  have hε := R.eps_pos
  have hεs := R.eps_small
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    rw [durArm_even_eq]
    exact div_pos (by linarith [R.off_lt_radArm k]) hc
  · subst hk
    rw [durArm_odd_eq]
    exact div_pos (by linarith) hc

theorem durArm_le (R : ArmRun) (j : ℕ) : durArm R j ≤ 2 / R.c := by
  have hc := R.c_pos
  have hε := R.eps_pos
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    rw [durArm_even_eq, div_le_div_iff₀ hc hc]
    nlinarith [R.radArm_le k]
  · subst hk
    rw [durArm_odd_eq, div_le_div_iff₀ hc hc]
    nlinarith

/-- Every flight but possibly the first covers at least half an edge. -/
theorem half_le_durArm (R : ArmRun) {j : ℕ} (hj : 1 ≤ j) :
    1 / (2 * R.c) ≤ durArm R j := by
  have hc := R.c_pos
  have hε := R.eps_pos
  have hεs := R.eps_small
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    rw [durArm_even_eq, radArm_succ, div_le_div_iff₀ (by positivity) hc]
    nlinarith
  · subst hk
    rw [durArm_odd_eq, div_le_div_iff₀ (by positivity) hc]
    nlinarith

/-- The entry time of flight `j`. -/
noncomputable def bt (R : ArmRun) : ℕ → ℝ
  | 0 => 0
  | j + 1 => exitAfter R.ε R.c R.w R.pw (bt R j + durArm R j)

@[simp] theorem bt_zero (R : ArmRun) : bt R 0 = 0 := rfl

/-- The time at which flight `j` reaches the router. -/
noncomputable def atm (R : ArmRun) (j : ℕ) : ℝ := bt R j + durArm R j

theorem bt_succ (R : ArmRun) (j : ℕ) :
    bt R (j + 1) = exitAfter R.ε R.c R.w R.pw (atm R j) := by
  simp only [bt, atm]

theorem bt_lt_atm (R : ArmRun) (j : ℕ) : bt R j < atm R j := by
  rw [atm]; linarith [R.durArm_pos j]

/-! #### The recursion invariant -/

/-- The state of the run at the beginning of flight `j`. -/
structure Inv (R : ArmRun) (j : ℕ) : Prop where
  nonneg : 0 ≤ bt R j
  le : bt R j ≤ (j : ℝ) * (2 / R.c + capReflTime R.ε R.c)
  pos : R.w (bt R j) = startPos R j
  mom : R.pw (bt R j) = momArm R j

section Invariant

variable {R : ArmRun}

theorem Inv.atm_nonneg {j : ℕ} (h : Inv R j) : 0 ≤ atm R j :=
  le_trans h.nonneg (R.bt_lt_atm j).le

theorem Inv.bt_mem {j : ℕ} (h : Inv R j) (hj : j ≤ R.N) :
    bt R j ∈ Icc (0 : ℝ) R.horizon := by
  refine ⟨h.nonneg, h.le.trans ?_⟩
  rw [horizon]
  refine mul_le_mul_of_nonneg_right ?_ R.step_pos.le
  have : (j : ℝ) ≤ (R.N : ℝ) := Nat.cast_le.mpr hj
  linarith

theorem Inv.atm_le {j : ℕ} (h : Inv R j) :
    atm R j + capReflTime R.ε R.c ≤ ((j : ℝ) + 1) * (2 / R.c + capReflTime R.ε R.c) := by
  have hexp : ((j : ℝ) + 1) * (2 / R.c + capReflTime R.ε R.c) =
      (j : ℝ) * (2 / R.c + capReflTime R.ε R.c) + (2 / R.c + capReflTime R.ε R.c) := by ring
  rw [atm, hexp]
  linarith [h.le, R.durArm_le j]

theorem Inv.atm_horizon {j : ℕ} (h : Inv R j) (hj : j ≤ R.N) :
    atm R j + capReflTime R.ε R.c ≤ R.horizon := by
  refine h.atm_le.trans ?_
  rw [horizon]
  refine mul_le_mul_of_nonneg_right ?_ R.step_pos.le
  have : (j : ℝ) ≤ (R.N : ℝ) := Nat.cast_le.mpr hj
  linarith

theorem Inv.atm_mem {j : ℕ} (h : Inv R j) (hj : j ≤ R.N) :
    atm R j ∈ Icc (0 : ℝ) R.horizon :=
  ⟨h.atm_nonneg, le_trans (by linarith [R.tau_pos]) (h.atm_horizon hj)⟩

/-- **The flight.**  On `[bt j, atm j]` the microscopic motion along the arm is exactly free. -/
theorem Inv.flight {j : ℕ} (h : Inv R j) (hj : j ≤ R.N) :
    ∀ t ∈ Icc (bt R j) (atm R j),
      R.w t = startPos R j + momArm R j * (t - bt R j) ∧ R.pw t = momArm R j := by
  have hε := R.eps_pos
  have hεs := R.eps_small
  have hab : bt R j ≤ atm R j := (R.bt_lt_atm j).le
  have hmemI : ∀ y ∈ Icc (8 * R.ε) (1 - 8 * R.ε), y ∈ Ioo (7 * R.ε) 1 := by
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h1 : R.w (bt R j) ∈ Ioo (7 * R.ε) 1 := by
    rw [h.pos]; exact hmemI _ (R.startPos_mem j)
  have hend : R.w (bt R j) + R.pw (bt R j) * (atm R j - bt R j) = endPos R j := by
    rw [h.pos, h.mom, atm]
    have := R.mom_mul_dur j
    have hsimp : bt R j + durArm R j - bt R j = durArm R j := by ring
    rw [hsimp]
    linarith
  have h2 : R.w (bt R j) + R.pw (bt R j) * (atm R j - bt R j) ∈ Ioo (7 * R.ε) 1 := by
    rw [hend]; exact hmemI _ (R.endPos_mem j)
  intro t ht
  obtain ⟨hw, hp⟩ := R.sol'.free_of_endpoints (h.bt_mem hj) (h.atm_mem hj) hab h1 h2 t ht
  exact ⟨by rw [hw, h.pos, h.mom], by rw [hp, h.mom]⟩

theorem Inv.w_atm {j : ℕ} (h : Inv R j) (hj : j ≤ R.N) : R.w (atm R j) = endPos R j := by
  have := (h.flight hj (atm R j) (right_mem_Icc.mpr (R.bt_lt_atm j).le)).1
  rw [this, atm]
  have hmd := R.mom_mul_dur j
  have hsimp : bt R j + durArm R j - bt R j = durArm R j := by ring
  rw [hsimp]
  linarith

theorem Inv.pw_atm {j : ℕ} (h : Inv R j) (hj : j ≤ R.N) : R.pw (atm R j) = momArm R j :=
  (h.flight hj (atm R j) (right_mem_Icc.mpr (R.bt_lt_atm j).le)).2

/-- **The barrier passage.**  Whichever of the two barriers the flight ends at, the momentum is
reversed exactly and the position is unchanged. -/
theorem Inv.exit {j : ℕ} (h : Inv R j) (hj : j ≤ R.N) :
    bt R (j + 1) ∈ Ioc (atm R j) (atm R j + capReflTime R.ε R.c) ∧
      R.w (bt R (j + 1)) = R.w (atm R j) ∧
      R.pw (bt R (j + 1)) = -R.pw (atm R j) := by
  have hw := h.w_atm hj
  have hp := h.pw_atm hj
  have hex : ∃ t, t ∈ Ioc (atm R j) (atm R j + capReflTime R.ε R.c) ∧
      R.w t = R.w (atm R j) ∧ R.pw t = -R.pw (atm R j) := by
    obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · subst hk
      rw [endPos_even] at hw
      rw [momArm_even] at hp
      obtain ⟨t₁, ht₁, h1, h2⟩ :=
        R.sol'.reflect_junction h.atm_nonneg (h.atm_horizon hj) hw hp
      exact ⟨t₁, ht₁, by rw [h1, hw], by rw [h2, hp]; ring⟩
    · subst hk
      rw [endPos_odd] at hw
      rw [momArm_odd] at hp
      obtain ⟨t₁, ht₁, h1, h2⟩ :=
        R.sol'.reflect_cap h.atm_nonneg (h.atm_horizon hj) hw hp
      exact ⟨t₁, ht₁, by rw [h1, hw], by rw [h2, hp]⟩
  obtain ⟨hmem, hpos, hmom⟩ := exitAfter_spec hex
  rw [← R.bt_succ j] at hmem hpos hmom
  exact ⟨hmem, hpos, hmom⟩

theorem Inv.atm_lt_bt_succ {j : ℕ} (h : Inv R j) (hj : j ≤ R.N) :
    atm R j < bt R (j + 1) := (h.exit hj).1.1

theorem Inv.bt_succ_le {j : ℕ} (h : Inv R j) (hj : j ≤ R.N) :
    bt R (j + 1) ≤ atm R j + capReflTime R.ε R.c := (h.exit hj).1.2

theorem Inv.succ {j : ℕ} (h : Inv R j) (hj : j ≤ R.N) : Inv R (j + 1) := by
  obtain ⟨hmem, hpos, hmom⟩ := h.exit hj
  refine ⟨le_trans h.atm_nonneg hmem.1.le, ?_, ?_, ?_⟩
  · refine le_trans hmem.2 (le_trans h.atm_le (le_of_eq ?_))
    push_cast
    ring
  · rw [hpos, h.w_atm hj]
    obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · subst hk
      rw [endPos_even, show 2 * k + 1 = 2 * k + 1 from rfl, startPos_odd]
    · subst hk
      rw [endPos_odd, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, startPos_even, radArm_succ]
  · rw [hmom, h.pw_atm hj]
    obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · subst hk
      rw [momArm_even, momArm_odd]
      ring
    · subst hk
      rw [momArm_odd, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, momArm_even]

end Invariant

/-- **The invariant holds along the whole run.** -/
theorem inv (R : ArmRun) : ∀ j ≤ R.N + 1, Inv R j := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨le_rfl, by simp, ?_, ?_⟩
      · rw [bt_zero, R.init_pos, show (0 : ℕ) = 2 * 0 by norm_num, startPos_even, radArm_zero]
      · rw [bt_zero, R.init_mom, show (0 : ℕ) = 2 * 0 by norm_num, momArm_even]
  | succ m ih => intro hm; exact (ih (by omega)).succ (by omega)


/-! ### The projected chain -/

/-- The end time of flight `j`; the last flight of the window is stopped strictly inside. -/
noncomputable def stopT (R : ArmRun) (j : ℕ) : ℝ :=
  if j = R.N then bt R j + 1 / (2 * R.c) else atm R j

/-- The projected graph state during flight `j`: on edge `2` the graph coordinate *is* `w`. -/
noncomputable def crv (R : ArmRun) (j : ℕ) (t : ℝ) : ℝ × ℝ :=
  (startPos R j + momArm R j * (t - bt R j), momArm R j)

theorem crv_fun (R : ArmRun) (j : ℕ) :
    crv R j = fun t => (startPos R j + momArm R j * (t - bt R j), momArm R j) := rfl

@[simp] theorem crv_fst (R : ArmRun) (j : ℕ) (t : ℝ) :
    (crv R j t).1 = startPos R j + momArm R j * (t - bt R j) := rfl

@[simp] theorem crv_snd (R : ArmRun) (j : ℕ) (t : ℝ) : (crv R j t).2 = momArm R j := rfl

/-- The chain starts at the initial state of the run. -/
theorem crv_zero_zero (R : ArmRun) : crv R 0 0 = (R.q₀, -R.c) := by
  have h1 : startPos R 0 = R.q₀ := by simpa using startPos_even R 0
  have h2 : momArm R 0 = -R.c := by simpa using momArm_even R 0
  rw [crv, h1, h2, bt_zero]
  norm_num

theorem stopT_last (R : ArmRun) : stopT R R.N = bt R R.N + 1 / (2 * R.c) := by
  unfold stopT; rw [if_pos rfl]

theorem stopT_of_ne (R : ArmRun) {j : ℕ} (h : j ≠ R.N) : stopT R j = atm R j := by
  unfold stopT; rw [if_neg h]

theorem bt_lt_stopT (R : ArmRun) (j : ℕ) : bt R j < stopT R j := by
  rcases eq_or_ne j R.N with rfl | h
  · rw [stopT_last]
    have : 0 < 1 / (2 * R.c) := by have := R.c_pos; positivity
    linarith
  · rw [stopT_of_ne R h]; exact R.bt_lt_atm j

theorem stopT_le_atm (R : ArmRun) (j : ℕ) : stopT R j ≤ atm R j := by
  rcases eq_or_ne j R.N with rfl | h
  · rw [stopT_last, atm]
    linarith [R.half_le_durArm R.N_pos]
  · rw [stopT_of_ne R h]

/-! #### The travelled distance -/

theorem c_dur_even (R : ArmRun) {k : ℕ} (h : 2 * k ≠ R.N) :
    R.c * (stopT R (2 * k) - bt R (2 * k)) = radArm R k - 8 * R.ε := by
  have hc := R.c_ne
  rw [stopT_of_ne R h, atm, durArm_even_eq]
  field_simp
  ring

theorem c_dur_odd (R : ArmRun) {k : ℕ} (h : 2 * k + 1 ≠ R.N) :
    R.c * (stopT R (2 * k + 1) - bt R (2 * k + 1)) = 1 - 16 * R.ε := by
  have hc := R.c_ne
  rw [stopT_of_ne R h, atm, durArm_odd_eq]
  field_simp
  ring

theorem c_dur_last (R : ArmRun) : R.c * (stopT R R.N - bt R R.N) = 1 / 2 := by
  have hc := R.c_ne
  rw [stopT_last]
  field_simp
  ring

/-- **The chain flights stay in the tube.** -/
theorem crv_fst_mem_Icc (R : ArmRun) {j : ℕ} (hj : j ≤ R.N) {t : ℝ}
    (ht : t ∈ Icc (bt R j) (stopT R j)) :
    (crv R j t).1 ∈ Icc (8 * R.ε) (1 - 8 * R.ε) := by
  have hc := R.c_pos
  have hε := R.eps_pos
  have hεs := R.eps_small
  have h0 : 0 ≤ R.c * (t - bt R j) := by nlinarith [ht.1]
  have hd : R.c * (t - bt R j) ≤ R.c * (stopT R j - bt R j) := by nlinarith [ht.2]
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    rw [crv_fst, startPos_even, momArm_even]
    rcases eq_or_ne (2 * k) R.N with heq | hne
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by have := R.N_pos; omega⟩
      have hlast : R.c * (stopT R (2 * (i + 1)) - bt R (2 * (i + 1))) = 1 / 2 := by
        rw [heq]; exact R.c_dur_last
      rw [hlast] at hd
      rw [radArm_succ]
      constructor <;> nlinarith
    · rw [c_dur_even R hne] at hd
      have := R.radArm_le k
      constructor <;> nlinarith
  · subst hk
    rw [crv_fst, startPos_odd, momArm_odd]
    rcases eq_or_ne (2 * k + 1) R.N with heq | hne
    · have hlast : R.c * (stopT R (2 * k + 1) - bt R (2 * k + 1)) = 1 / 2 := by
        rw [heq]; exact R.c_dur_last
      rw [hlast] at hd
      constructor <;> nlinarith
    · rw [c_dur_odd R hne] at hd
      constructor <;> nlinarith

/-- The strict version. -/
theorem crv_fst_mem_Ioo (R : ArmRun) {j : ℕ} (hj : j ≤ R.N) {t : ℝ}
    (ht : t ∈ Ioo (bt R j) (stopT R j)) :
    (crv R j t).1 ∈ Ioo (8 * R.ε) (1 - 8 * R.ε) := by
  have hc := R.c_pos
  have hε := R.eps_pos
  have hεs := R.eps_small
  have h0 : 0 < R.c * (t - bt R j) := by nlinarith [ht.1]
  have hd : R.c * (t - bt R j) < R.c * (stopT R j - bt R j) := by nlinarith [ht.2]
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    rw [crv_fst, startPos_even, momArm_even]
    rcases eq_or_ne (2 * k) R.N with heq | hne
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by have := R.N_pos; omega⟩
      have hlast : R.c * (stopT R (2 * (i + 1)) - bt R (2 * (i + 1))) = 1 / 2 := by
        rw [heq]; exact R.c_dur_last
      rw [hlast] at hd
      rw [radArm_succ]
      constructor <;> nlinarith
    · rw [c_dur_even R hne] at hd
      have := R.radArm_le k
      constructor <;> nlinarith
  · subst hk
    rw [crv_fst, startPos_odd, momArm_odd]
    rcases eq_or_ne (2 * k + 1) R.N with heq | hne
    · have hlast : R.c * (stopT R (2 * k + 1) - bt R (2 * k + 1)) = 1 / 2 := by
        rw [heq]; exact R.c_dur_last
      rw [hlast] at hd
      constructor <;> nlinarith
    · rw [c_dur_odd R hne] at hd
      constructor <;> nlinarith

theorem crv_final (R : ArmRun) :
    (crv R R.N (stopT R R.N)).1 ∈ Ioo (8 * R.ε) (1 - 8 * R.ε) := by
  have hc := R.c_pos
  have hε := R.eps_pos
  have hεs := R.eps_small
  have hd := R.c_dur_last
  obtain ⟨k, hk | hk⟩ : ∃ k, R.N = 2 * k ∨ R.N = 2 * k + 1 := ⟨R.N / 2, by omega⟩
  · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by have := R.N_pos; omega⟩
    have hd' : R.c * (stopT R (2 * (i + 1)) - bt R (2 * (i + 1))) = 1 / 2 := by
      rw [← hk]; exact hd
    rw [hk, crv_fst, startPos_even, momArm_even, radArm_succ]
    constructor <;> nlinarith
  · have hd' : R.c * (stopT R (2 * k + 1) - bt R (2 * k + 1)) = 1 / 2 := by
      rw [← hk]; exact hd
    rw [hk, crv_fst, startPos_odd, momArm_odd]
    constructor <;> nlinarith

theorem crv_arrive (R : ArmRun) {j : ℕ} (h : j ≠ R.N) :
    (crv R j (stopT R j)).1 = endPos R j := by
  rw [crv_fst, stopT_of_ne R h, atm]
  have hmd := R.mom_mul_dur j
  have hs : bt R j + durArm R j - bt R j = durArm R j := by ring
  rw [hs]
  linarith

theorem hasDerivAt_crv (R : ArmRun) (j : ℕ) (s : ℝ) :
    HasDerivAt (crv R j) (momArm R j, 0) s := by
  rw [crv_fun]
  have h1 : HasDerivAt (fun t : ℝ => startPos R j + momArm R j * (t - bt R j))
      (momArm R j) s := by
    simpa using
      (((hasDerivAt_id s).sub_const (bt R j)).const_mul (momArm R j)).const_add (startPos R j)
  exact h1.prodMk (hasDerivAt_const s (momArm R j))

/-- **The projected chain of a microscopic run along the third arm.** -/
noncomputable def chain (R : ArmRun) :
    HybridChain (zeroPotential starGraph) starRouting (starParams R.ε) where
  N := R.N
  start := bt R
  stop := stopT R
  edge j := (starRouting.itinerary channel₃ j).1
  curve := crv R
  germ := starRouting.itinerary channel₃
  start_zero := rfl
  start_lt_stop := fun j _ => R.bt_lt_stopT j
  stop_le_start_succ := by
    intro j hj
    rw [stopT_of_ne R (by omega)]
    exact ((R.inv j (by omega)).atm_lt_bt_succ (by omega)).le
  start_succ_le := by
    intro j hj
    rw [starParams_dwell_of_pos R.eps_pos, stopT_of_ne R (by omega)]
    have h1 := (R.inv j (by omega)).bt_succ_le (by omega)
    have h2 := R.tau_le
    linarith
  flight_ode := by
    intro j _
    refine ⟨fun s => ((crv R j s).2, 0), fun t _ => ⟨?_, ?_⟩⟩
    · rw [zeroPotential_edgeVectorField]
      simp
    · show HasDerivWithinAt (crv R j) ((crv R j t).2, 0) _ t
      rw [crv_snd]
      exact (R.hasDerivAt_crv j t).hasDerivWithinAt
  flight_tube := by
    intro j hj t ht
    rw [starGraph_length_eq_one, starParams_offset_of_pos R.eps_pos]
    exact R.crv_fst_mem_Icc hj ht
  flight_inside := by
    intro j hj t ht
    rw [starGraph_length_eq_one, starParams_offset_of_pos R.eps_pos]
    exact R.crv_fst_mem_Ioo hj ht
  final_inside := by
    rw [starGraph_length_eq_one, starParams_offset_of_pos R.eps_pos]
    exact R.crv_final
  germ_edge := fun _ _ => rfl
  edge_succ := by
    intro j _
    rw [RoutingLaw.itinerary_succ, otherEnd_fst]
  arrive := by
    intro j hj
    rw [starParams_offset_of_pos R.eps_pos, R.crv_arrive (by omega)]
    obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · subst hk
      rw [endPos_even, coord₃_even, sign₃_even]
      ring
    · subst hk
      rw [endPos_odd, coord₃_odd, sign₃_odd]
      ring
  depart_coord := by
    intro j hj
    rw [starParams_offset_of_pos R.eps_pos, crv_fst, sub_self, mul_zero, add_zero]
    obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · subst hk
      rw [routed₃_coord_even, routed₃_sign_even, startPos_odd]
      ring
    · subst hk
      rw [routed₃_coord_odd, routed₃_sign_odd,
        show 2 * k + 1 + 1 = 2 * (k + 1) by ring, startPos_even, radArm_succ]
      ring
  depart_mom := by
    intro j hj
    have hc := R.c_pos
    rw [crv_snd, crv_snd, RoutingLaw.departureMomentum]
    obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · subst hk
      rw [momArm_even, momArm_odd, routed₃_sign_even, abs_neg, abs_of_pos hc]
      simp
    · subst hk
      rw [momArm_odd, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, momArm_even, routed₃_sign_odd,
        abs_of_pos hc]
      simp

@[simp] theorem chain_N (R : ArmRun) : (chain R).N = R.N := rfl

/-- **The chain is the graph projection of the microscopic trajectory.**  On edge `2` the graph
coordinate is the microscopic coordinate `w` itself. -/
theorem projection (R : ArmRun) {j : ℕ} (hj : j ≤ R.N) {t : ℝ}
    (ht : t ∈ Icc (bt R j) (stopT R j)) :
    R.w t = (crv R j t).1 ∧ R.pw t = (crv R j t).2 := by
  have hsub : Icc (bt R j) (stopT R j) ⊆ Icc (bt R j) (atm R j) :=
    Icc_subset_Icc le_rfl (R.stopT_le_atm j)
  obtain ⟨hw, hp⟩ := (R.inv j (by omega)).flight hj t (hsub ht)
  exact ⟨by rw [hw, crv_fst], by rw [hp, crv_snd]⟩

/-! #### Time bounds -/

theorem bt_lower (R : ArmRun) : ∀ j ≤ R.N, ((j : ℝ) - 1) * (1 / (2 * R.c)) ≤ bt R j := by
  have hc := R.c_pos
  have hunit : (0 : ℝ) < 1 / (2 * R.c) := by positivity
  have hmono : ∀ m, m < R.N → stopT R m ≤ bt R (m + 1) := fun m hm =>
    (chain R).stop_le_start_succ m (show m < R.N by omega)
  have hdur : ∀ m, 1 ≤ m → m ≤ R.N → 1 / (2 * R.c) ≤ stopT R m - bt R m := by
    intro m hm1 hmN
    rcases eq_or_ne m R.N with rfl | h
    · rw [stopT_last]; linarith
    · rw [stopT_of_ne R h, atm]
      linarith [R.half_le_durArm hm1]
  intro j
  induction j with
  | zero => intro _; rw [bt_zero]; push_cast; linarith
  | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hstop := hmono m (by omega)
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · have hlt := R.bt_lt_stopT 0
        rw [bt_zero] at hlt
        push_cast
        linarith
      · have hd := hdur m hmpos (by omega)
        push_cast
        push_cast at hprev
        linarith

theorem stopT_lower (R : ArmRun) : (R.N : ℝ) / (2 * R.c) ≤ stopT R R.N := by
  have hc := R.c_pos
  have h := R.bt_lower R.N le_rfl
  rw [stopT_last]
  have hex : ((R.N : ℝ) - 1) * (1 / (2 * R.c)) + 1 / (2 * R.c) = (R.N : ℝ) / (2 * R.c) := by
    field_simp
    ring
  linarith

theorem stopT_le_horizon (R : ArmRun) : stopT R R.N ≤ R.horizon := by
  have hc := R.c_pos
  have hτ := R.tau_pos
  have hstep := R.step_pos
  have hhalf : 1 / (2 * R.c) ≤ 2 / R.c + capReflTime R.ε R.c := by
    have h : 1 / (2 * R.c) ≤ 2 / R.c := by
      rw [div_le_div_iff₀ (by positivity) hc]
      linarith
    linarith
  have hI := R.inv R.N (by omega)
  have h2 := hI.le
  have hcast : (R.N : ℝ) + 1 ≤ (R.N : ℝ) + 1 := le_rfl
  have hexp : ((R.N : ℝ) + 1) * (2 / R.c + capReflTime R.ε R.c) =
      (R.N : ℝ) * (2 / R.c + capReflTime R.ε R.c) + (2 / R.c + capReflTime R.ε R.c) := by ring
  rw [stopT_last, horizon, hexp]
  linarith

end ArmRun

end HamiltonianMetricGraphs
