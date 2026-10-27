/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalTrajectory
import HamiltonianMetricGraphs.Realization.UniversalFolds
import HamiltonianMetricGraphs.Realization.MicroscopicChain

/-!
# The geometry of a microscopic run in the universal corridor

This file fixes the corridor coordinates of a run: the position of every vertex, the two ends of
every flight and the distance it travels.  The two facts proved here are the ones the dynamics
needs:

* at a fold the flight ends exactly at a cap of the corridor (`epos_of_fold`), so the reflection
  lemma `CorridorSolution.reflect` applies;
* at any other vertex the flight ends at distance at least `margin - 8ε` from both caps
  (`epos_of_not_fold`), so the passage through the router is exactly free motion.

The `8ε` offset is the router radius: a flight of the projected chain runs from the tube boundary
next to its departure vertex to the tube boundary next to its arrival vertex.
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph MechanicalPotential

variable {Γ : FiniteMetricGraph} {F : RoutingLaw Γ} {η₀ : Γ.EdgeEnd} {M : ℕ}

/-! ### Corridor coordinates -/

/-- The length of the corridor. -/
noncomputable def clen (C : Corridor F η₀ M) : ℝ := C.high - C.low

/-- The corridor coordinate of the vertex reached by flight `j`. -/
noncomputable def cpos (C : Corridor F η₀ M) (j : ℕ) : ℝ := vpos F η₀ j - C.low

theorem clen_pos (C : Corridor F η₀ M) : 0 < clen C := sub_pos.mpr C.low_lt_high

theorem margin_le_clen (C : Corridor F η₀ M) : C.margin ≤ clen C := by
  have h1 := C.margin_le_high
  have h2 := C.low_nonpos
  rw [clen]; linarith

@[simp] theorem cpos_zero (C : Corridor F η₀ M) : cpos C 0 = -C.low := by
  rw [cpos, vpos_zero]; ring

theorem cpos_one (C : Corridor F η₀ M) : cpos C 1 = Γ.length η₀.1 - C.low := by
  rw [cpos, vpos_succ]
  simp [edgeLen_def]

theorem cpos_mem (C : Corridor F η₀ M) {j : ℕ} (hj : j ≤ M + 1) :
    cpos C j ∈ Icc 0 (clen C) := by
  have h := C.mem j hj
  rw [cpos, clen]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem cpos_succ (C : Corridor F η₀ M) (j : ℕ) :
    cpos C (j + 1) = cpos C j + dirSign F η₀ j * edgeLen F η₀ j := by
  rw [cpos, cpos, vpos_succ]; ring

theorem edgeLen_le_clen (C : Corridor F η₀ M) {j : ℕ} (hj : j ≤ M) :
    edgeLen F η₀ j ≤ clen C := by
  have h1 := cpos_mem C (j := j) (by omega)
  have h2 := cpos_mem C (j := j + 1) (by omega)
  have h3 := cpos_succ C j
  rcases dirSign_eq_one_or_neg_one (F := F) (η₀ := η₀) j with hd | hd
  · rw [hd] at h3; linarith [h1.1, h2.2]
  · rw [hd] at h3; linarith [h1.2, h2.1]

theorem margin_le_edgeLen (C : Corridor F η₀ M) (j : ℕ) : C.margin ≤ edgeLen F η₀ j :=
  C.margin_le _

/-- **The vertex reached by flight `j` is a cap exactly when the impact is a fold.** -/
theorem cpos_succ_cases (C : Corridor F η₀ M) {j : ℕ} (hj : j ≤ M) :
    (IsFold F η₀ j ∧ ((dirSign F η₀ j = 1 ∧ cpos C (j + 1) = clen C) ∨
        (dirSign F η₀ j = -1 ∧ cpos C (j + 1) = 0))) ∨
      (¬ IsFold F η₀ j ∧ cpos C (j + 1) ∈ Icc C.margin (clen C - C.margin)) := by
  by_cases hf : IsFold F η₀ j
  · refine Or.inl ⟨hf, ?_⟩
    rcases C.cap j hj hf with ⟨hd, hv⟩ | ⟨hd, hv⟩
    · exact Or.inl ⟨hd, by rw [cpos, hv, clen]⟩
    · exact Or.inr ⟨hd, by rw [cpos, hv]; ring⟩
  · refine Or.inr ⟨hf, ?_⟩
    have h := C.interior j hj hf
    exact ⟨by rw [cpos]; linarith [h.1], by rw [cpos, clen]; linarith [h.2]⟩

/-! ### The ends of a flight -/

variable (C : Corridor F η₀ M) (q₀ ε : ℝ)

/-- The corridor coordinate at which flight `j` starts: the initial point for `j = 0`, and the
tube boundary at distance `8ε` past the departure vertex afterwards. -/
noncomputable def spos (j : ℕ) : ℝ :=
  if j = 0 then cpos C 1 - GenTrajectory.travel F η₀ q₀ 0
  else cpos C j + dirSign F η₀ j * (8 * ε)

/-- The corridor coordinate at which flight `j` ends: the tube boundary at distance `8ε` before
the arrival vertex. -/
noncomputable def epos (j : ℕ) : ℝ := cpos C (j + 1) - dirSign F η₀ j * (8 * ε)

variable {C q₀ ε}

/-- The distance travelled by flight `j` in the corridor. -/
noncomputable def rdist (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (q₀ ε : ℝ) (j : ℕ) : ℝ :=
  GenTrajectory.travel F η₀ q₀ j - (if j = 0 then 8 * ε else 16 * ε)

@[simp] theorem spos_zero :
    spos C q₀ ε 0 = cpos C 1 - GenTrajectory.travel F η₀ q₀ 0 := by rw [spos, if_pos rfl]

theorem spos_succ (j : ℕ) :
    spos C q₀ ε (j + 1) = cpos C (j + 1) + dirSign F η₀ (j + 1) * (8 * ε) := by
  rw [spos, if_neg (Nat.succ_ne_zero j)]

@[simp] theorem rdist_zero :
    rdist F η₀ q₀ ε 0 = GenTrajectory.travel F η₀ q₀ 0 - 8 * ε := by
  rw [rdist, if_pos rfl]

theorem rdist_succ (j : ℕ) :
    rdist F η₀ q₀ ε (j + 1) = edgeLen F η₀ (j + 1) - 16 * ε := by
  rw [rdist, if_neg (Nat.succ_ne_zero j)]
  rfl

/-- **The travelled distance is the signed displacement of the flight.** -/
theorem epos_sub_spos (j : ℕ) :
    epos C ε j - spos C q₀ ε j = dirSign F η₀ j * rdist F η₀ q₀ ε j := by
  cases j with
  | zero =>
      rw [spos_zero, epos, rdist_zero, dirSign_zero, one_mul, one_mul]
      ring
  | succ i =>
      rw [spos_succ, epos, rdist_succ, cpos_succ]
      have hlen : edgeLen F η₀ (i + 1) = edgeLen F η₀ (i + 1) := rfl
      have hsq := dirSign_sq (F := F) (η₀ := η₀) (i + 1)
      nlinarith [hsq]

/-! ### Position bounds -/

theorem travel_zero_lb (hq1 : 8 * ε < q₀) (hq2 : q₀ < Γ.length η₀.1 - 8 * ε) :
    8 * ε < GenTrajectory.travel F η₀ q₀ 0 := by
  rcases hb : η₀.2 with _ | _
  · rw [GenTrajectory.travel_zero_of_false hb]; exact hq1
  · rw [GenTrajectory.travel_zero_of_true hb]; linarith

theorem travel_zero_ub (hq1 : 8 * ε < q₀) (hq2 : q₀ < Γ.length η₀.1 - 8 * ε) :
    8 * ε < Γ.length η₀.1 - GenTrajectory.travel F η₀ q₀ 0 := by
  rcases hb : η₀.2 with _ | _
  · rw [GenTrajectory.travel_zero_of_false hb]; linarith
  · rw [GenTrajectory.travel_zero_of_true hb]; linarith

/-- **At a fold the flight ends exactly at a cap.** -/
theorem epos_of_fold {j : ℕ} (hj : j ≤ M) (hf : IsFold F η₀ j) :
    epos C ε j = clen C / 2 + dirSign F η₀ j * (clen C / 2 - 8 * ε) := by
  rcases cpos_succ_cases C hj with ⟨-, ⟨hd, hv⟩ | ⟨hd, hv⟩⟩ | ⟨hnf, -⟩
  · rw [epos, hd, hv]; ring
  · rw [epos, hd, hv]; ring
  · exact absurd hf hnf

/-- After a fold the next flight starts where the previous one ended. -/
theorem spos_succ_of_fold {j : ℕ} (hf : IsFold F η₀ j) :
    spos C q₀ ε (j + 1) = epos C ε j := by
  rw [spos_succ, epos, dirSign_succ_of_fold hf]
  ring

/-- Through a pass the particle travels the two router radii freely. -/
theorem spos_succ_of_not_fold {j : ℕ} (hf : ¬ IsFold F η₀ j) :
    spos C q₀ ε (j + 1) = epos C ε j + dirSign F η₀ j * (16 * ε) := by
  rw [spos_succ, epos, dirSign_succ_of_not_fold hf]
  ring

/-- **The end of a flight lies in the corridor, at distance at least `8ε` from both caps.** -/
theorem epos_mem (hε : 0 < ε) (hεm : 1000 * ε ≤ C.margin) {j : ℕ} (hj : j ≤ M) :
    epos C ε j ∈ Icc (8 * ε) (clen C - 8 * ε) := by
  have hmc := margin_le_clen C
  rcases cpos_succ_cases C hj with ⟨-, ⟨hd, hv⟩ | ⟨hd, hv⟩⟩ | ⟨-, hv⟩
  · rw [epos, hd, hv]
    constructor <;> linarith
  · rw [epos, hd, hv]
    constructor <;> linarith
  · rw [epos]
    rcases dirSign_eq_one_or_neg_one (F := F) (η₀ := η₀) j with hd | hd <;> rw [hd] <;>
      exact ⟨by linarith [hv.1, hv.2], by linarith [hv.1, hv.2]⟩

/-- **The start of a flight lies in the corridor, at distance at least `8ε` from both caps.** -/
theorem spos_mem (hε : 0 < ε) (hεm : 1000 * ε ≤ C.margin)
    (hq1 : 8 * ε < q₀) (hq2 : q₀ < Γ.length η₀.1 - 8 * ε) {j : ℕ} (hj : j ≤ M) :
    spos C q₀ ε j ∈ Icc (8 * ε) (clen C - 8 * ε) := by
  have hmc := margin_le_clen C
  cases j with
  | zero =>
      have hlb := travel_zero_lb (F := F) (η₀ := η₀) hq1 hq2
      have hub := travel_zero_ub (F := F) (η₀ := η₀) hq1 hq2
      have hlow := C.low_nonpos
      have h1 : cpos C 1 ≤ clen C := (cpos_mem C (by omega)).2
      rw [spos_zero, cpos_one]
      constructor
      · linarith
      · have : Γ.length η₀.1 - C.low ≤ clen C := by rw [← cpos_one C]; exact h1
        linarith
  | succ i =>
      by_cases hf : IsFold F η₀ i
      · rw [spos_succ_of_fold hf]
        exact epos_mem hε hεm (by omega)
      · rw [spos_succ_of_not_fold hf]
        have h := epos_mem (C := C) (ε := ε) hε hεm (j := i) (by omega)
        rcases cpos_succ_cases C (j := i) (by omega) with ⟨hfc, -⟩ | ⟨-, hv⟩
        · exact absurd hfc hf
        · rw [epos] at h ⊢
          rcases dirSign_eq_one_or_neg_one (F := F) (η₀ := η₀) i with hd | hd <;> rw [hd] <;>
            exact ⟨by linarith [hv.1, hv.2], by linarith [hv.1, hv.2]⟩

/-- **The travelled distance of a flight is positive.** -/
theorem rdist_pos (hε : 0 < ε) (hεm : 1000 * ε ≤ C.margin)
    (hq1 : 8 * ε < q₀) (hq2 : q₀ < Γ.length η₀.1 - 8 * ε) (j : ℕ) :
    0 < rdist F η₀ q₀ ε j := by
  cases j with
  | zero =>
      rw [rdist_zero]
      linarith [travel_zero_lb (F := F) (η₀ := η₀) hq1 hq2]
  | succ i =>
      rw [rdist_succ]
      have := margin_le_edgeLen C (i + 1)
      linarith

/-- The travelled distance of a flight is at most the length of the corridor. -/
theorem rdist_le (hε : 0 < ε) (hq₀ : q₀ ∈ Ioo (0 : ℝ) (Γ.length η₀.1)) {j : ℕ} (hj : j ≤ M) :
    rdist F η₀ q₀ ε j ≤ clen C := by
  have h1 : GenTrajectory.travel F η₀ q₀ j ≤ edgeLen F η₀ j :=
    GenTrajectory.travel_le_edgeLen hq₀ j
  have h2 : edgeLen F η₀ j ≤ clen C := edgeLen_le_clen C hj
  rw [rdist]
  have : (0 : ℝ) ≤ if j = 0 then 8 * ε else 16 * ε := by
    split <;> linarith
  linarith

/-! ### The times of the run -/

/-- The time at which flight `j` starts: after a fold the particle leaves the router at the exit
time of the cap reflection, after a pass it leaves it after crossing the two router radii. -/
noncomputable def rstart (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (q₀ c ε : ℝ) (u pu : ℝ → ℝ) :
    ℕ → ℝ
  | 0 => 0
  | j + 1 =>
      if IsFold F η₀ j then
        exitAfter ε c u pu (rstart F η₀ q₀ c ε u pu j + rdist F η₀ q₀ ε j / c)
      else rstart F η₀ q₀ c ε u pu j + rdist F η₀ q₀ ε j / c + 16 * ε / c

/-- The time at which flight `j` reaches the router of its arrival vertex. -/
noncomputable def rarrive (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (q₀ c ε : ℝ) (u pu : ℝ → ℝ)
    (j : ℕ) : ℝ := rstart F η₀ q₀ c ε u pu j + rdist F η₀ q₀ ε j / c

/-! ### The run -/

/-- **The data of an explicit microscopic run of the universal corridor.**  A genuine solution
`(u, p_u)` of the one-dimensional corridor system at scale `ε`, launched at the graph coordinate
`q₀` of the edge of `η₀` towards `η₀` with speed `c`, on a time window long enough to carry `M`
chain flights. -/
structure NetRun (Γ : FiniteMetricGraph) where
  /-- the routing law -/
  F : RoutingLaw Γ
  /-- the first impact germ -/
  η₀ : Γ.EdgeEnd
  /-- the initial graph coordinate -/
  q₀ : ℝ
  /-- the speed, equivalently the energy `c²/2` -/
  c : ℝ
  /-- the thinness scale -/
  ε : ℝ
  /-- the number of chain flights -/
  M : ℕ
  /-- the corridor layout of the routing component -/
  C : Corridor F η₀ M
  /-- the microscopic longitudinal coordinate -/
  u : ℝ → ℝ
  /-- the microscopic longitudinal momentum -/
  pu : ℝ → ℝ
  eps_pos : 0 < ε
  eps_margin : 1000 * ε ≤ C.margin
  c_ge : 1 ≤ c
  c_le : c ≤ 2
  q_lb : 8 * ε < q₀
  q_ub : q₀ < Γ.length η₀.1 - 8 * ε
  init_pos : u 0 = spos C q₀ ε 0
  init_mom : pu 0 = c
  sol : CorridorSolution ε (clen C) c (((M : ℝ) + 1) * (clen C / c + 100 * ε)) u pu

namespace NetRun

variable (R : NetRun Γ)

/-- The time budget of one flight together with its router passage. -/
noncomputable def step : ℝ := clen R.C / R.c + 100 * R.ε

/-- The time horizon of the run. -/
noncomputable def horizon : ℝ := ((R.M : ℝ) + 1) * R.step

/-- The start time of flight `j`. -/
noncomputable def startT (j : ℕ) : ℝ := rstart R.F R.η₀ R.q₀ R.c R.ε R.u R.pu j

/-- The time at which flight `j` reaches the router. -/
noncomputable def arriveT (j : ℕ) : ℝ := rarrive R.F R.η₀ R.q₀ R.c R.ε R.u R.pu j

/-- The corridor distance travelled by flight `j`. -/
noncomputable def dist' (j : ℕ) : ℝ := rdist R.F R.η₀ R.q₀ R.ε j

/-- The corridor coordinate at which flight `j` starts. -/
noncomputable def startPos (j : ℕ) : ℝ := spos R.C R.q₀ R.ε j

/-- The corridor coordinate at which flight `j` ends. -/
noncomputable def endPos (j : ℕ) : ℝ := epos R.C R.ε j

/-- The direction of flight `j`. -/
noncomputable def sgn (j : ℕ) : ℝ := dirSign R.F R.η₀ j

variable {R}

theorem c_pos : 0 < R.c := by linarith [R.c_ge]

theorem c_ne : R.c ≠ 0 := ne_of_gt c_pos

theorem clen_pos' : 0 < clen R.C := clen_pos R.C

theorem step_pos : 0 < R.step := by
  have := clen_pos' (R := R)
  have := c_pos (R := R)
  have := R.eps_pos
  rw [step]
  positivity

theorem horizon_eq : R.horizon = ((R.M : ℝ) + 1) * (clen R.C / R.c + 100 * R.ε) := rfl

theorem tau_pos : 0 < capReflTime R.ε R.c := capReflTime_pos R.eps_pos R.c_ge

theorem tau_le : capReflTime R.ε R.c ≤ 100 * R.ε := capReflTime_le R.eps_pos R.c_ge R.c_le

@[simp] theorem startT_zero : R.startT 0 = 0 := rfl

theorem arriveT_eq (j : ℕ) : R.arriveT j = R.startT j + R.dist' j / R.c := rfl

theorem startT_succ_of_fold {j : ℕ} (h : IsFold R.F R.η₀ j) :
    R.startT (j + 1) = exitAfter R.ε R.c R.u R.pu (R.arriveT j) := by
  show rstart _ _ _ _ _ _ _ (j + 1) = _
  rw [rstart, if_pos h]
  rfl

theorem startT_succ_of_not_fold {j : ℕ} (h : ¬ IsFold R.F R.η₀ j) :
    R.startT (j + 1) = R.arriveT j + 16 * R.ε / R.c := by
  show rstart _ _ _ _ _ _ _ (j + 1) = _
  rw [rstart, if_neg h]
  rfl

theorem dist_at_zero : R.dist' 0 = GenTrajectory.travel R.F R.η₀ R.q₀ 0 - 8 * R.ε := rdist_zero

theorem dist_at_succ (j : ℕ) : R.dist' (j + 1) = edgeLen R.F R.η₀ (j + 1) - 16 * R.ε :=
  rdist_succ j

theorem dist_pos (j : ℕ) : 0 < R.dist' j :=
  rdist_pos (C := R.C) R.eps_pos R.eps_margin R.q_lb R.q_ub j

theorem startT_lt_arriveT (j : ℕ) : R.startT j < R.arriveT j := by
  rw [arriveT_eq]
  have := div_pos (dist_pos (R := R) j) (c_pos (R := R))
  linarith

theorem q₀_mem : R.q₀ ∈ Ioo (0 : ℝ) (Γ.length R.η₀.1) := by
  have := R.eps_pos
  exact ⟨by linarith [R.q_lb], by linarith [R.q_ub]⟩

theorem dist_le {j : ℕ} (hj : j ≤ R.M) : R.dist' j ≤ clen R.C :=
  rdist_le (C := R.C) R.eps_pos q₀_mem hj

theorem startPos_mem {j : ℕ} (hj : j ≤ R.M) :
    R.startPos j ∈ Icc (8 * R.ε) (clen R.C - 8 * R.ε) :=
  spos_mem R.eps_pos R.eps_margin R.q_lb R.q_ub hj

theorem endPos_mem {j : ℕ} (hj : j ≤ R.M) :
    R.endPos j ∈ Icc (8 * R.ε) (clen R.C - 8 * R.ε) :=
  epos_mem R.eps_pos R.eps_margin hj

theorem startPos_mem_Ioo {j : ℕ} (hj : j ≤ R.M) : R.startPos j ∈ Ioo 0 (clen R.C) := by
  have h := startPos_mem (R := R) hj
  have := R.eps_pos
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem endPos_mem_Ioo {j : ℕ} (hj : j ≤ R.M) : R.endPos j ∈ Ioo 0 (clen R.C) := by
  have h := endPos_mem (R := R) hj
  have := R.eps_pos
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem endPos_sub_startPos (j : ℕ) : R.endPos j - R.startPos j = R.sgn j * R.dist' j :=
  epos_sub_spos j

/-! #### The recursion invariant -/

/-- The state of the run at the beginning of flight `j`. -/
structure Inv (R : NetRun Γ) (j : ℕ) : Prop where
  /-- the start time is nonnegative -/
  nonneg : 0 ≤ R.startT j
  /-- the start time is within the time budget -/
  le : R.startT j ≤ (j : ℝ) * R.step
  /-- the particle is at the start of flight `j` -/
  pos : R.u (R.startT j) = R.startPos j
  /-- moving in the direction of flight `j` at the nominal speed -/
  mom : R.pu (R.startT j) = R.sgn j * R.c

theorem inv_zero : Inv R 0 where
  nonneg := le_rfl
  le := by rw [startT_zero]; simp
  pos := by rw [startT_zero]; exact R.init_pos
  mom := by
    rw [startT_zero, R.init_mom, sgn, dirSign_zero, one_mul]

theorem Inv.startT_mem {j : ℕ} (h : Inv R j) (hj : j ≤ R.M) :
    R.startT j ∈ Icc (0 : ℝ) R.horizon := by
  refine ⟨h.nonneg, h.le.trans ?_⟩
  rw [horizon]
  refine mul_le_mul_of_nonneg_right ?_ (step_pos (R := R)).le
  have : (j : ℝ) ≤ (R.M : ℝ) := Nat.cast_le.mpr hj
  linarith

theorem pass_le : 16 * R.ε / R.c ≤ 100 * R.ε := by
  have hc := c_pos (R := R)
  have hc1 := R.c_ge
  have hε := R.eps_pos
  rw [div_le_iff₀ hc]
  nlinarith

theorem pass_nonneg : 0 ≤ 16 * R.ε / R.c := by
  have hc := c_pos (R := R)
  have hε := R.eps_pos
  positivity

theorem Inv.arriveT_le {j : ℕ} (h : Inv R j) (hj : j ≤ R.M) :
    R.arriveT j + 100 * R.ε ≤ ((j : ℝ) + 1) * R.step := by
  have hd : R.dist' j / R.c ≤ clen R.C / R.c :=
    div_le_div_of_nonneg_right (dist_le (R := R) hj) (c_pos (R := R)).le
  have hexp : ((j : ℝ) + 1) * R.step = (j : ℝ) * R.step + R.step := by ring
  rw [arriveT_eq, hexp, step]
  have := h.le
  rw [step] at this
  linarith

theorem Inv.arriveT_horizon' {j : ℕ} (h : Inv R j) (hj : j ≤ R.M) :
    R.arriveT j + 100 * R.ε ≤ R.horizon := by
  refine (h.arriveT_le hj).trans ?_
  rw [horizon]
  refine mul_le_mul_of_nonneg_right ?_ (step_pos (R := R)).le
  have : (j : ℝ) ≤ (R.M : ℝ) := Nat.cast_le.mpr hj
  linarith

theorem Inv.arriveT_horizon {j : ℕ} (h : Inv R j) (hj : j ≤ R.M) :
    R.arriveT j + capReflTime R.ε R.c ≤ R.horizon := by
  have := h.arriveT_horizon' hj
  linarith [tau_le (R := R)]

theorem Inv.arriveT_nonneg {j : ℕ} (h : Inv R j) : 0 ≤ R.arriveT j :=
  h.nonneg.trans (startT_lt_arriveT (R := R) j).le

theorem Inv.arriveT_mem {j : ℕ} (h : Inv R j) (hj : j ≤ R.M) :
    R.arriveT j ∈ Icc (0 : ℝ) R.horizon :=
  ⟨h.arriveT_nonneg, le_trans (by linarith [tau_pos (R := R)]) (h.arriveT_horizon hj)⟩

/-- **The flight is exactly free motion.** -/
theorem Inv.flight {j : ℕ} (h : Inv R j) (hj : j ≤ R.M) :
    ∀ t ∈ Icc (R.startT j) (R.arriveT j),
      R.u t = R.startPos j + R.sgn j * R.c * (t - R.startT j) ∧
        R.pu t = R.sgn j * R.c := by
  have hend : R.u (R.startT j) + R.pu (R.startT j) * (R.arriveT j - R.startT j) =
      R.endPos j := by
    rw [h.pos, h.mom, arriveT_eq]
    have hc := c_ne (R := R)
    have hs : R.sgn j * R.c * (R.dist' j / R.c) = R.sgn j * R.dist' j := by
      field_simp
    have := endPos_sub_startPos (R := R) j
    rw [show R.startT j + R.dist' j / R.c - R.startT j = R.dist' j / R.c by ring, hs]
    linarith
  intro t ht
  obtain ⟨hu, hp⟩ := R.sol.free_of_endpoints (h.startT_mem hj) (h.arriveT_mem hj)
    (startT_lt_arriveT (R := R) j).le (by rw [h.pos]; exact startPos_mem_Ioo (R := R) hj)
    (by rw [hend]; exact endPos_mem_Ioo (R := R) hj) t ht
  exact ⟨by rw [hu, h.pos, h.mom], by rw [hp, h.mom]⟩

theorem Inv.u_arriveT {j : ℕ} (h : Inv R j) (hj : j ≤ R.M) :
    R.u (R.arriveT j) = R.endPos j := by
  have := (h.flight hj (R.arriveT j) ⟨(startT_lt_arriveT (R := R) j).le, le_rfl⟩).1
  rw [this, arriveT_eq]
  have hc := c_ne (R := R)
  have hs : R.sgn j * R.c * (R.startT j + R.dist' j / R.c - R.startT j) =
      R.sgn j * R.dist' j := by field_simp; ring
  rw [hs]
  linarith [endPos_sub_startPos (R := R) j]

theorem Inv.pu_arriveT {j : ℕ} (h : Inv R j) (hj : j ≤ R.M) :
    R.pu (R.arriveT j) = R.sgn j * R.c :=
  (h.flight hj (R.arriveT j) ⟨(startT_lt_arriveT (R := R) j).le, le_rfl⟩).2

/-! #### The step of the recursion -/

/-- **The router passage.**  At a fold the particle is reflected at the cap with exact momentum
reversal; at any other vertex it crosses the router freely.  In both cases it leaves the router
exactly at the tube boundary of the next edge, moving at the nominal speed in the direction the
routing law prescribes, after a residence time of at most `100 ε`. -/
theorem Inv.router {j : ℕ} (h : Inv R j) (hj : j < R.M) :
    R.arriveT j ≤ R.startT (j + 1) ∧ R.startT (j + 1) ≤ R.arriveT j + 100 * R.ε ∧
      Inv R (j + 1) := by
  have hjM : j ≤ R.M := by omega
  have hε := R.eps_pos
  by_cases hf : IsFold R.F R.η₀ j
  · -- reflection at a cap
    have hcap : R.endPos j = clen R.C / 2 + R.sgn j * (clen R.C / 2 - 8 * R.ε) :=
      epos_of_fold hjM hf
    have hs : R.sgn j = 1 ∨ R.sgn j = -1 := dirSign_eq_one_or_neg_one j
    have hua : R.u (R.arriveT j) = clen R.C / 2 + R.sgn j * (clen R.C / 2 - 8 * R.ε) := by
      rw [h.u_arriveT hjM, hcap]
    have hpa : R.pu (R.arriveT j) = R.sgn j * R.c := h.pu_arriveT hjM
    have hex : ∃ t, t ∈ Ioc (R.arriveT j) (R.arriveT j + capReflTime R.ε R.c) ∧
        R.u t = R.u (R.arriveT j) ∧ R.pu t = -R.pu (R.arriveT j) := by
      obtain ⟨t₁, ht₁, h1, h2⟩ :=
        R.sol.reflect hs h.arriveT_nonneg (h.arriveT_horizon hjM) hua hpa
      exact ⟨t₁, ht₁, by rw [h1, hua], by rw [h2, hpa]⟩
    obtain ⟨hmem, hu, hpu⟩ := exitAfter_spec hex
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [startT_succ_of_fold hf]; linarith [hmem.1]
    · rw [startT_succ_of_fold hf]; linarith [hmem.2, tau_le (R := R)]
    · rw [startT_succ_of_fold hf]
      linarith [hmem.1, h.arriveT_nonneg]
    · rw [startT_succ_of_fold hf]
      have h1 := h.arriveT_le hjM
      have h2 := tau_le (R := R)
      push_cast
      linarith [hmem.2]
    · rw [startT_succ_of_fold hf, hu, h.u_arriveT hjM]
      exact (spos_succ_of_fold hf).symm
    · rw [startT_succ_of_fold hf, hpu, hpa, sgn, sgn, dirSign_succ_of_fold hf]
      ring
  · -- free passage through the router
    have hnext : R.startPos (j + 1) = R.endPos j + R.sgn j * (16 * R.ε) :=
      spos_succ_of_not_fold hf
    have hb : R.arriveT j + 16 * R.ε / R.c ∈ Icc (0 : ℝ) R.horizon := by
      refine ⟨by linarith [h.arriveT_nonneg, pass_nonneg (R := R)], ?_⟩
      have := h.arriveT_horizon' hjM
      linarith [pass_le (R := R)]
    have hend : R.u (R.arriveT j) +
        R.pu (R.arriveT j) * (R.arriveT j + 16 * R.ε / R.c - R.arriveT j) =
          R.startPos (j + 1) := by
      rw [h.u_arriveT hjM, h.pu_arriveT hjM, hnext]
      have hc := c_ne (R := R)
      field_simp
      ring
    have hfree := R.sol.free_of_endpoints (h.arriveT_mem hjM) hb
      (by linarith [pass_nonneg (R := R)])
      (by rw [h.u_arriveT hjM]; exact endPos_mem_Ioo (R := R) hjM)
      (by rw [hend]; exact startPos_mem_Ioo (R := R) (by omega))
      (R.arriveT j + 16 * R.ε / R.c) ⟨by linarith [pass_nonneg (R := R)], le_rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [startT_succ_of_not_fold hf]; linarith [pass_nonneg (R := R)]
    · rw [startT_succ_of_not_fold hf]; linarith [pass_le (R := R)]
    · rw [startT_succ_of_not_fold hf]
      linarith [h.arriveT_nonneg, pass_nonneg (R := R)]
    · rw [startT_succ_of_not_fold hf]
      have h1 := h.arriveT_le hjM
      push_cast
      linarith [pass_le (R := R)]
    · rw [startT_succ_of_not_fold hf, hfree.1, hend]
    · rw [startT_succ_of_not_fold hf, hfree.2, h.pu_arriveT hjM, sgn, sgn,
        dirSign_succ_of_not_fold hf]

theorem Inv.succ {j : ℕ} (h : Inv R j) (hj : j < R.M) : Inv R (j + 1) := (h.router hj).2.2

/-- **The invariant holds along the whole run.** -/
theorem inv (R : NetRun Γ) : ∀ j ≤ R.M, Inv R j := by
  intro j
  induction j with
  | zero => intro _; exact inv_zero
  | succ i ih => intro hi; exact (ih (by omega)).succ (by omega)

end NetRun

/-! ### The projected graph flight -/

/-- The parameters of the projected chain: router offset `8ε`, junction residence time `100ε`,
and **no** ODE or momentum error at all. -/
noncomputable def netParams (ε : ℝ) : ChainParams where
  offset := 8 * |ε|
  dwell := 100 * |ε|
  odeErr := 0
  momErr := 0
  offset_nonneg := by positivity
  dwell_nonneg := by positivity
  odeErr_nonneg := le_rfl
  momErr_nonneg := le_rfl

@[simp] theorem netParams_offset (ε : ℝ) : (netParams ε).offset = 8 * |ε| := rfl
@[simp] theorem netParams_dwell (ε : ℝ) : (netParams ε).dwell = 100 * |ε| := rfl
@[simp] theorem netParams_odeErr (ε : ℝ) : (netParams ε).odeErr = 0 := rfl
@[simp] theorem netParams_momErr (ε : ℝ) : (netParams ε).momErr = 0 := rfl

/-- The graph coordinate at which chain flight `j` starts: the initial coordinate for `j = 0`,
and the tube boundary next to the routed germ afterwards. -/
noncomputable def gstart (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (q₀ ε : ℝ) : ℕ → ℝ
  | 0 => q₀
  | j + 1 => EdgeEnd.coordinate Γ (F.routeGerm (F.itinerary η₀ j)) -
      EdgeEnd.sign Γ (F.routeGerm (F.itinerary η₀ j)) * (8 * ε)

/-- The (constant) graph momentum during chain flight `j`. -/
noncomputable def gmom (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (c : ℝ) (j : ℕ) : ℝ :=
  EdgeEnd.sign Γ (F.itinerary η₀ j) * c

@[simp] theorem gstart_zero (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (q₀ ε : ℝ) :
    gstart F η₀ q₀ ε 0 = q₀ := rfl

theorem gstart_succ (F : RoutingLaw Γ) (η₀ : Γ.EdgeEnd) (q₀ ε : ℝ) (j : ℕ) :
    gstart F η₀ q₀ ε (j + 1) = edgeLen F η₀ (j + 1) -
      EdgeEnd.coordinate Γ (F.itinerary η₀ (j + 1)) +
      EdgeEnd.sign Γ (F.itinerary η₀ (j + 1)) * (8 * ε) := by
  show EdgeEnd.coordinate Γ (F.routeGerm (F.itinerary η₀ j)) -
    EdgeEnd.sign Γ (F.routeGerm (F.itinerary η₀ j)) * (8 * ε) = _
  rw [F.routeGerm_itinerary, coordinate_otherEnd, sign_otherEnd]
  rw [show Γ.length (F.itinerary η₀ (j + 1)).1 = edgeLen F η₀ (j + 1) from rfl]
  ring

/-- The initial flight reaches its impact germ after travelling `travel 0`. -/
theorem q₀_add_sign_travel {q₀ : ℝ} :
    q₀ + EdgeEnd.sign Γ η₀ * GenTrajectory.travel F η₀ q₀ 0 = EdgeEnd.coordinate Γ η₀ := by
  rcases hb : η₀.2 with _ | _
  · rw [sign_of_false hb, coordinate_of_false hb, GenTrajectory.travel_zero_of_false hb]
    ring
  · rw [sign_of_true hb, coordinate_of_true' hb, GenTrajectory.travel_zero_of_true hb]
    ring

namespace NetRun

variable {R : NetRun Γ}

/-- The projected graph state during chain flight `j`. -/
noncomputable def gcurve (R : NetRun Γ) (j : ℕ) (t : ℝ) : ℝ × ℝ :=
  (gstart R.F R.η₀ R.q₀ R.ε j + gmom R.F R.η₀ R.c j * (t - R.startT j), gmom R.F R.η₀ R.c j)

/-- The end time of chain flight `j`: the arrival at the router for `j < M`, and the middle of
the last flight for `j = M`. -/
noncomputable def stopT (R : NetRun Γ) (j : ℕ) : ℝ :=
  if j < R.M then R.arriveT j else R.startT R.M + R.dist' R.M / (2 * R.c)

@[simp] theorem gcurve_snd (j : ℕ) (t : ℝ) :
    (R.gcurve j t).2 = gmom R.F R.η₀ R.c j := rfl

theorem gcurve_fst (j : ℕ) (t : ℝ) :
    (R.gcurve j t).1 = gstart R.F R.η₀ R.q₀ R.ε j +
      EdgeEnd.sign Γ (R.F.itinerary R.η₀ j) * (R.c * (t - R.startT j)) := by
  show gstart R.F R.η₀ R.q₀ R.ε j + gmom R.F R.η₀ R.c j * (t - R.startT j) = _
  rw [gmom]; ring

theorem stopT_of_lt {j : ℕ} (h : j < R.M) : R.stopT j = R.arriveT j := if_pos h

theorem stopT_self : R.stopT R.M = R.startT R.M + R.dist' R.M / (2 * R.c) :=
  if_neg (lt_irrefl _)

theorem stopT_le_arriveT {j : ℕ} (hj : j ≤ R.M) : R.stopT j ≤ R.arriveT j := by
  rcases lt_or_eq_of_le hj with h | h
  · rw [stopT_of_lt h]
  · subst h
    rw [stopT_self, arriveT_eq]
    have hc := c_pos (R := R)
    have hd := dist_pos (R := R) R.M
    have : R.dist' R.M / (2 * R.c) ≤ R.dist' R.M / R.c := by
      apply div_le_div_of_nonneg_left hd.le hc
      linarith
    linarith

theorem startT_lt_stopT {j : ℕ} (hj : j ≤ R.M) : R.startT j < R.stopT j := by
  rcases lt_or_eq_of_le hj with h | h
  · rw [stopT_of_lt h, arriveT_eq]
    have := div_pos (dist_pos (R := R) j) (c_pos (R := R))
    linarith
  · subst h
    rw [stopT_self]
    have hc := c_pos (R := R)
    have := div_pos (dist_pos (R := R) R.M) (by linarith : (0 : ℝ) < 2 * R.c)
    linarith

/-- The distance travelled inside a chain flight. -/
theorem travelled {j : ℕ} (hj : j ≤ R.M) {t : ℝ} (ht : t ∈ Icc (R.startT j) (R.stopT j)) :
    0 ≤ R.c * (t - R.startT j) ∧ R.c * (t - R.startT j) ≤ R.dist' j := by
  have hc := c_pos (R := R)
  refine ⟨mul_nonneg hc.le (by linarith [ht.1]), ?_⟩
  have h1 : t ≤ R.arriveT j := le_trans ht.2 (stopT_le_arriveT hj)
  rw [arriveT_eq] at h1
  have : R.c * (t - R.startT j) ≤ R.c * (R.dist' j / R.c) := by
    apply mul_le_mul_of_nonneg_left (by linarith) hc.le
  have h2 : R.c * (R.dist' j / R.c) = R.dist' j := by field_simp
  linarith [h2 ▸ this]

theorem travelled_strict {j : ℕ} (hj : j ≤ R.M) {t : ℝ} (ht : t ∈ Ioo (R.startT j) (R.stopT j)) :
    0 < R.c * (t - R.startT j) ∧ R.c * (t - R.startT j) < R.dist' j := by
  have hc := c_pos (R := R)
  refine ⟨mul_pos hc (by linarith [ht.1]), ?_⟩
  have h1 : t < R.arriveT j := lt_of_lt_of_le ht.2 (stopT_le_arriveT hj)
  rw [arriveT_eq] at h1
  have : R.c * (t - R.startT j) < R.c * (R.dist' j / R.c) := by
    apply mul_lt_mul_of_pos_left (by linarith) hc
  have h2 : R.c * (R.dist' j / R.c) = R.dist' j := by field_simp
  linarith [h2 ▸ this]

theorem travelled_final : R.c * (R.stopT R.M - R.startT R.M) = R.dist' R.M / 2 := by
  have hc := c_ne (R := R)
  rw [stopT_self]
  field_simp
  ring

/-- **The projected flight stays in the tube of its edge.** -/
theorem gcurve_mem {j : ℕ} (hj : j ≤ R.M) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ R.dist' j) :
    gstart R.F R.η₀ R.q₀ R.ε j + EdgeEnd.sign Γ (R.F.itinerary R.η₀ j) * v ∈
      Icc (8 * R.ε) (edgeLen R.F R.η₀ j - 8 * R.ε) := by
  have hε := R.eps_pos
  cases j with
  | zero =>
      rw [gstart_zero, show R.F.itinerary R.η₀ 0 = R.η₀ from rfl]
      rw [dist_at_zero] at h1
      have hlen : edgeLen R.F R.η₀ 0 = Γ.length R.η₀.1 := rfl
      rw [hlen]
      rcases hb : R.η₀.2 with _ | _
      · rw [sign_of_false hb]
        rw [GenTrajectory.travel_zero_of_false hb] at h1
        exact ⟨by linarith, by linarith [R.q_ub]⟩
      · rw [sign_of_true hb]
        rw [GenTrajectory.travel_zero_of_true hb] at h1
        exact ⟨by linarith [R.q_lb], by linarith⟩
  | succ i =>
      rw [gstart_succ]
      rw [dist_at_succ] at h1
      have hml : R.C.margin ≤ edgeLen R.F R.η₀ (i + 1) := margin_le_edgeLen R.C (i + 1)
      have hem := R.eps_margin
      rcases hb : (R.F.itinerary R.η₀ (i + 1)).2 with _ | _
      · rw [sign_of_false hb, coordinate_of_false hb]
        exact ⟨by linarith, by linarith⟩
      · rw [sign_of_true hb, coordinate_of_true' hb]
        have hcl : EdgeEnd.coordinate Γ (R.F.itinerary R.η₀ (i + 1)) =
            edgeLen R.F R.η₀ (i + 1) := coordinate_of_true' hb
        rw [show Γ.length (R.F.itinerary R.η₀ (i + 1)).1 = edgeLen R.F R.η₀ (i + 1) from rfl]
        exact ⟨by linarith, by linarith⟩

/-- The strict version of `gcurve_mem`. -/
theorem gcurve_mem_Ioo {j : ℕ} (hj : j ≤ R.M) {v : ℝ} (h0 : 0 < v) (h1 : v < R.dist' j) :
    gstart R.F R.η₀ R.q₀ R.ε j + EdgeEnd.sign Γ (R.F.itinerary R.η₀ j) * v ∈
      Ioo (8 * R.ε) (edgeLen R.F R.η₀ j - 8 * R.ε) := by
  have hε := R.eps_pos
  cases j with
  | zero =>
      rw [gstart_zero, show R.F.itinerary R.η₀ 0 = R.η₀ from rfl]
      rw [dist_at_zero] at h1
      have hlen : edgeLen R.F R.η₀ 0 = Γ.length R.η₀.1 := rfl
      rw [hlen]
      rcases hb : R.η₀.2 with _ | _
      · rw [sign_of_false hb]
        rw [GenTrajectory.travel_zero_of_false hb] at h1
        exact ⟨by linarith, by linarith [R.q_ub]⟩
      · rw [sign_of_true hb]
        rw [GenTrajectory.travel_zero_of_true hb] at h1
        exact ⟨by linarith [R.q_lb], by linarith⟩
  | succ i =>
      rw [gstart_succ]
      rw [dist_at_succ] at h1
      have hml : R.C.margin ≤ edgeLen R.F R.η₀ (i + 1) := margin_le_edgeLen R.C (i + 1)
      have hem := R.eps_margin
      rcases hb : (R.F.itinerary R.η₀ (i + 1)).2 with _ | _
      · rw [sign_of_false hb, coordinate_of_false hb]
        exact ⟨by linarith, by linarith⟩
      · rw [sign_of_true hb, coordinate_of_true' hb]
        rw [show Γ.length (R.F.itinerary R.η₀ (i + 1)).1 = edgeLen R.F R.η₀ (i + 1) from rfl]
        exact ⟨by linarith, by linarith⟩

/-- **A flight arrives exactly at the tube boundary next to its impact germ.** -/
theorem gcurve_arrive {j : ℕ} (hj : j < R.M) :
    (R.gcurve j (R.stopT j)).1 =
      EdgeEnd.coordinate Γ (R.F.itinerary R.η₀ j) -
        EdgeEnd.sign Γ (R.F.itinerary R.η₀ j) * (8 * R.ε) := by
  have hc := c_ne (R := R)
  have hv : R.c * (R.stopT j - R.startT j) = R.dist' j := by
    rw [stopT_of_lt hj, arriveT_eq]
    field_simp
    ring
  rw [gcurve_fst, hv]
  cases j with
  | zero =>
      rw [gstart_zero, show R.F.itinerary R.η₀ 0 = R.η₀ from rfl, dist_at_zero]
      have := q₀_add_sign_travel (F := R.F) (η₀ := R.η₀) (q₀ := R.q₀)
      have hsq := Γ.edgeEnd_sign_sq R.η₀
      nlinarith [this, hsq]
  | succ i =>
      rw [gstart_succ, dist_at_succ]
      rcases hb : (R.F.itinerary R.η₀ (i + 1)).2 with _ | _
      · rw [sign_of_false hb, coordinate_of_false hb]; ring
      · rw [sign_of_true hb, coordinate_of_true' hb,
          show Γ.length (R.F.itinerary R.η₀ (i + 1)).1 = edgeLen R.F R.η₀ (i + 1) from rfl]
        ring

/-! ### The projected chain -/

theorem abs_eps (R : NetRun Γ) : |R.ε| = R.ε := abs_of_pos R.eps_pos

/-- **The projected chain of a microscopic run.**  Every field of `HybridChain` is discharged from
the microscopic dynamics: the flights are exactly free (`odeErr = 0`), they stay in the tubes, the
routing law prescribes the next edge, the departure coordinate is the tube boundary next to the
routed germ, and the departure momentum is exactly the routed momentum (`momErr = 0`).  The router
offset is `8 ε` and the junction residence time at most `100 ε`. -/
noncomputable def chain (R : NetRun Γ) :
    HybridChain (zeroPotential Γ) R.F (netParams R.ε) where
  N := R.M
  start := R.startT
  stop := R.stopT
  edge j := (R.F.itinerary R.η₀ j).1
  curve := R.gcurve
  germ := R.F.itinerary R.η₀
  start_zero := startT_zero
  start_lt_stop := fun _ hj => startT_lt_stopT hj
  stop_le_start_succ := by
    intro j hj
    rw [stopT_of_lt hj]
    exact ((R.inv j hj.le).router hj).1
  start_succ_le := by
    intro j hj
    rw [stopT_of_lt hj, netParams_dwell, R.abs_eps]
    exact ((R.inv j hj.le).router hj).2.1
  flight_ode := by
    intro j _
    refine ⟨fun _ => (gmom R.F R.η₀ R.c j, 0), fun t _ => ⟨?_, ?_⟩⟩
    · simp
    · have h1 : HasDerivAt
          (fun s : ℝ => gstart R.F R.η₀ R.q₀ R.ε j + gmom R.F R.η₀ R.c j * (s - R.startT j))
          (gmom R.F R.η₀ R.c j) t := by
        simpa using
          (((hasDerivAt_id t).sub_const (R.startT j)).const_mul
            (gmom R.F R.η₀ R.c j)).const_add (gstart R.F R.η₀ R.q₀ R.ε j)
      have h2 : HasDerivAt (fun _ : ℝ => gmom R.F R.η₀ R.c j) 0 t :=
        hasDerivAt_const t (gmom R.F R.η₀ R.c j)
      exact (h1.prodMk h2).hasDerivWithinAt
  flight_tube := by
    intro j hj t ht
    rw [netParams_offset, R.abs_eps, gcurve_fst]
    exact gcurve_mem hj (travelled hj ht).1 (travelled hj ht).2
  flight_inside := by
    intro j hj t ht
    rw [netParams_offset, R.abs_eps, gcurve_fst]
    exact gcurve_mem_Ioo hj (travelled_strict hj ht).1 (travelled_strict hj ht).2
  final_inside := by
    rw [netParams_offset, R.abs_eps, gcurve_fst, travelled_final]
    refine gcurve_mem_Ioo le_rfl ?_ ?_
    · linarith [dist_pos (R := R) R.M]
    · linarith [dist_pos (R := R) R.M]
  germ_edge := fun _ _ => rfl
  arrive := by
    intro j hj
    rw [netParams_offset, R.abs_eps]
    exact gcurve_arrive hj
  edge_succ := by
    intro j _
    rw [RoutingLaw.itinerary_succ, otherEnd_fst]
  depart_coord := by
    intro j _
    rw [netParams_offset, R.abs_eps, gcurve_fst, sub_self, mul_zero, mul_zero, add_zero]
    rfl
  depart_mom := by
    intro j _
    rw [netParams_momErr, gcurve_snd, gcurve_snd]
    have h : gmom R.F R.η₀ R.c (j + 1) =
        R.F.departureMomentum (R.F.itinerary R.η₀ j) (gmom R.F R.η₀ R.c j) := by
      show EdgeEnd.sign Γ (R.F.itinerary R.η₀ (j + 1)) * R.c =
        -(EdgeEnd.sign Γ (R.F.routeGerm (R.F.itinerary R.η₀ j))) *
          |EdgeEnd.sign Γ (R.F.itinerary R.η₀ j) * R.c|
      rw [RoutingLaw.itinerary_succ, sign_otherEnd, abs_mul, RoutingLaw.edgeEnd_abs_sign,
        one_mul, abs_of_pos (c_pos (R := R))]
    rw [h]
    simp

@[simp] theorem chain_N (R : NetRun Γ) : R.chain.N = R.M := rfl
@[simp] theorem chain_start (R : NetRun Γ) (j : ℕ) : R.chain.start j = R.startT j := rfl
@[simp] theorem chain_stop (R : NetRun Γ) (j : ℕ) : R.chain.stop j = R.stopT j := rfl
@[simp] theorem chain_edge (R : NetRun Γ) (j : ℕ) :
    R.chain.edge j = (R.F.itinerary R.η₀ j).1 := rfl
@[simp] theorem chain_curve (R : NetRun Γ) (j : ℕ) (t : ℝ) : R.chain.curve j t = R.gcurve j t :=
  rfl
@[simp] theorem chain_germ (R : NetRun Γ) (j : ℕ) : R.chain.germ j = R.F.itinerary R.η₀ j := rfl

/-- The chain starts at the initial state of the run. -/
theorem chain_curve_zero_zero (R : NetRun Γ) :
    R.chain.curve 0 0 = (R.q₀, EdgeEnd.sign Γ R.η₀ * R.c) := by
  have h : (R.gcurve 0 0).1 = R.q₀ := by
    rw [gcurve_fst, gstart_zero, startT_zero, sub_zero, mul_zero, mul_zero, add_zero]
  exact Prod.ext h rfl

/-! ### The time window and the projection -/

theorem dist_ge (R : NetRun Γ) (j : ℕ) :
    GenTrajectory.travel R.F R.η₀ R.q₀ j - 16 * R.ε ≤ R.dist' j := by
  cases j with
  | zero => rw [dist_at_zero]; linarith [R.eps_pos]
  | succ i => rw [dist_at_succ]; exact le_of_eq (by rw [GenTrajectory.travel_succ])

/-- **The microscopic run is not slower than the graph trajectory, up to `O(Mε)`.** -/
theorem startT_ge (R : NetRun Γ) : ∀ j ≤ R.M,
    GenTrajectory.startTime R.F R.η₀ R.q₀ R.c j - (j : ℝ) * (16 * R.ε) ≤ R.startT j := by
  have hc := c_pos (R := R)
  have hc1 := R.c_ge
  have hε := R.eps_pos
  intro j
  induction j with
  | zero => intro _; simp [GenTrajectory.startTime_zero]
  | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hstep : R.arriveT i ≤ R.startT (i + 1) := ((R.inv i (by omega)).router (by omega)).1
      have hd : GenTrajectory.travel R.F R.η₀ R.q₀ i - 16 * R.ε ≤ R.dist' i := R.dist_ge i
      have hdiv : (GenTrajectory.travel R.F R.η₀ R.q₀ i - 16 * R.ε) / R.c ≤ R.dist' i / R.c :=
        div_le_div_of_nonneg_right hd hc.le
      have hsplit : (GenTrajectory.travel R.F R.η₀ R.q₀ i - 16 * R.ε) / R.c =
          GenTrajectory.travel R.F R.η₀ R.q₀ i / R.c - 16 * R.ε / R.c := by ring
      have hpass : 16 * R.ε / R.c ≤ 16 * R.ε := by
        rw [div_le_iff₀ hc]; nlinarith
      have harr : R.arriveT i = R.startT i + R.dist' i / R.c := arriveT_eq i
      have hstart : GenTrajectory.startTime R.F R.η₀ R.q₀ R.c (i + 1) =
          GenTrajectory.startTime R.F R.η₀ R.q₀ R.c i +
            GenTrajectory.travel R.F R.η₀ R.q₀ i / R.c := GenTrajectory.startTime_succ i
      rw [hstart]
      push_cast
      rw [hsplit] at hdiv
      linarith

/-- **The projected chain is the image of the microscopic trajectory** under the affine isometry
which identifies the corridor cell of flight `j` with the edge of that flight. -/
theorem chain_flight (R : NetRun Γ) {j : ℕ} (hj : j ≤ R.M) {t : ℝ}
    (ht : t ∈ Icc (R.startT j) (R.stopT j)) :
    R.u t = R.startPos j + R.sgn j * R.c * (t - R.startT j) ∧ R.pu t = R.sgn j * R.c :=
  (R.inv j hj).flight hj t ⟨ht.1, le_trans ht.2 (stopT_le_arriveT hj)⟩

theorem chain_proj (R : NetRun Γ) {j : ℕ} (hj : j ≤ R.M) {t : ℝ}
    (ht : t ∈ Icc (R.startT j) (R.stopT j)) :
    (R.gcurve j t).1 = gstart R.F R.η₀ R.q₀ R.ε j +
        (EdgeEnd.sign Γ (R.F.itinerary R.η₀ j) * R.sgn j) * (R.u t - R.startPos j) ∧
      (R.gcurve j t).2 = (EdgeEnd.sign Γ (R.F.itinerary R.η₀ j) * R.sgn j) * R.pu t := by
  obtain ⟨hu, hp⟩ := R.chain_flight hj ht
  rw [gcurve_fst, gcurve_snd, gmom, hu, hp]
  rcases dirSign_eq_one_or_neg_one (F := R.F) (η₀ := R.η₀) j with hd | hd
  · rw [show R.sgn j = dirSign R.F R.η₀ j from rfl, hd]
    constructor <;> ring
  · rw [show R.sgn j = dirSign R.F R.η₀ j from rfl, hd]
    constructor <;> ring

/-- The orientation of the affine identification of flight `j`. -/
noncomputable def orient (R : NetRun Γ) (j : ℕ) : ℝ :=
  EdgeEnd.sign Γ (R.F.itinerary R.η₀ j) * R.sgn j

theorem orient_eq_one_or (R : NetRun Γ) (j : ℕ) : R.orient j = 1 ∨ R.orient j = -1 := by
  rcases dirSign_eq_one_or_neg_one (F := R.F) (η₀ := R.η₀) j with hd | hd <;>
    rcases hb : (R.F.itinerary R.η₀ j).2 with _ | _ <;>
    rw [orient, show R.sgn j = dirSign R.F R.η₀ j from rfl, hd] <;>
    [rw [sign_of_false hb]; rw [sign_of_true hb]; rw [sign_of_false hb]; rw [sign_of_true hb]] <;>
    norm_num

end NetRun

end HamiltonianMetricGraphs
