/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ThinFlightBounds
import HamiltonianMetricGraphs.Realization.UniversalGraphTrajectory

/-!
# From the microscopic hypotheses to the projected chain

This file carries out the **bridge** from the hypotheses (E) and (J) of `ThinHypotheses.lean` to
the abstract realization machinery: along the flow `Φ^ε_t(z)` of a prepared state `z`, (E) and (J)
are applied alternately by finite induction — each time to the current state `Φ^ε_a(z)`, which is
legitimate because (E) and (J) are statements about *every* state — and the resulting sequence of
edge flights and junction passages is assembled into a `HybridChain` with parameters
`(δ_ε, θ_ε, γ_ε, μ_ε)` (`offset`, `dwell`, `forceErr`, `momErr`).

Nothing about the chain is assumed.  The impact germs are produced by the routing law itself
(`RoutingLaw.itinerary`), the flight times are the arrival times supplied by (E), the departure
times those supplied by (J), and every one of the eighteen fields of `HybridChain` is discharged
from the two hypotheses.  The chain's ODE tolerance is the force error `γ_ε` of (E3): the
projected curve `(q, p)` has derivative `(p, -⟨∇W_ε, τ_e⟩)`, at distance
`|⟨∇W_ε, τ_e⟩ - V_e'(q)| ≤ γ_ε` from the edge vector field `(p, -V_e'(q))`.

The only further input is a lower bound on the duration of a full flight, which makes the run
cover any given time window.  It comes from the speed bound of `ThinFlightBounds.lean`, which
holds under the window condition `K ⊂ (max_Γ V, ∞)` once `γ_ε ℓ_e` is below the gap of the
window; the run carries these window constants.
-/

namespace HamiltonianMetricGraphs

open Set FiniteMetricGraph MechanicalPotential ThinHamiltonianNetwork

variable {Γ : FiniteMetricGraph}

/-- The length of a shortest edge of `Γ`. -/
noncomputable def minEdgeLen (Γ : FiniteMetricGraph) (e₀ : Γ.Edge) : ℝ :=
  Finset.univ.inf' ⟨e₀, Finset.mem_univ e₀⟩ Γ.length

theorem minEdgeLen_le (Γ : FiniteMetricGraph) (e₀ e : Γ.Edge) : minEdgeLen Γ e₀ ≤ Γ.length e :=
  Finset.inf'_le _ (Finset.mem_univ e)

theorem minEdgeLen_pos (Γ : FiniteMetricGraph) (e₀ : Γ.Edge) : 0 < minEdgeLen Γ e₀ := by
  rw [minEdgeLen, Finset.lt_inf'_iff]
  exact fun e _ => Γ.length_pos e

/-! ### The parameters of a run -/

/-- The chain parameters of a run: the scales `δ_ε, θ_ε, γ_ε, μ_ε` of the network. -/
noncomputable def thinParams (N : ThinHamiltonianNetwork Γ) (ε : ℝ) : ChainParams where
  offset := N.offset ε
  dwell := N.dwell ε
  odeErr := N.forceErr ε
  momErr := N.momErr ε
  offset_nonneg := N.offset_nonneg ε
  dwell_nonneg := N.dwell_nonneg ε
  odeErr_nonneg := N.forceErr_nonneg ε
  momErr_nonneg := N.momErr_nonneg ε

@[simp] theorem thinParams_offset (N : ThinHamiltonianNetwork Γ) (ε : ℝ) :
    (thinParams N ε).offset = N.offset ε := rfl
@[simp] theorem thinParams_dwell (N : ThinHamiltonianNetwork Γ) (ε : ℝ) :
    (thinParams N ε).dwell = N.dwell ε := rfl
@[simp] theorem thinParams_odeErr (N : ThinHamiltonianNetwork Γ) (ε : ℝ) :
    (thinParams N ε).odeErr = N.forceErr ε := rfl
@[simp] theorem thinParams_momErr (N : ThinHamiltonianNetwork Γ) (ε : ℝ) :
    (thinParams N ε).momErr = N.momErr ε := rfl

/-! ### The data of a microscopic run -/

/-- **A microscopic run of a thin Hamiltonian network.**  A state prepared towards `germ₀` and not
arriving there, the hypotheses (E) and (J) at the scale `ε`, and the constants of the window
`K ⊂ (max_Γ V, ∞)` (`exists_window_constants`) with `γ_ε ℓ_e` below its gap.  The trajectory is
the flow `Φ^ε_t(x₀, p₀)`; the run has `n` junction passages. -/
structure ThinRun (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (K : Set ℝ)
    (F : RoutingLaw Γ) (ε : ℝ) (n : ℕ) where
  /-- the first impact germ -/
  germ₀ : Γ.EdgeEnd
  /-- the initial configuration -/
  x₀ : ℝ × ℝ
  /-- the initial momentum -/
  p₀ : ℝ × ℝ
  eps_pos : 0 < ε
  /-- the junction regions are small compared with the edges -/
  offset_lt : 2 * N.offset ε < minEdgeLen Γ germ₀.1
  /-- the initial state is prepared towards `germ₀` -/
  init : N.Prepared V K ε germ₀ x₀ p₀
  /-- the initial state is not arriving at `germ₀` -/
  init_toGo : 0 < N.toGo ε germ₀ (N.long germ₀.1 x₀)
  /-- hypothesis (E) at the scale `ε` -/
  edgeRed : ∀ (η : Γ.EdgeEnd) (x p : ℝ × ℝ), N.Prepared V K ε η x p →
    ¬ N.Arriving V K ε η x p →
    ∃ b, N.EdgeFlight V K ε η (fun t => (N.flow ε t (x, p)).1) (fun t => (N.flow ε t (x, p)).2)
      0 b
  /-- hypothesis (J) at the scale `ε` -/
  jct : ∀ (η : Γ.EdgeEnd) (x p : ℝ × ℝ), N.Arriving V K ε η x p →
    ∃ b, N.JunctionPassage V K F.routeGerm ε η (fun t => (N.flow ε t (x, p)).1)
      (fun t => (N.flow ε t (x, p)).2) 0 b
  /-- the gap of the window above the potential -/
  gap : ℝ
  /-- an upper bound of the window -/
  Kmax : ℝ
  /-- a lower bound of the potential -/
  Vmin : ℝ
  gap_le : ∀ E ∈ K, ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), V.extension e q + gap ≤ E
  le_Kmax : ∀ E ∈ K, E ≤ Kmax
  Vmin_le : ∀ e : Γ.Edge, ∀ q ∈ Icc (0 : ℝ) (Γ.length e), Vmin ≤ V.extension e q
  /-- the force error is small compared with the gap -/
  forceErr_lt : ∀ e : Γ.Edge, N.forceErr ε * Γ.length e < gap

namespace ThinRun

variable {N : ThinHamiltonianNetwork Γ} {V : MechanicalPotential Γ} {K : Set ℝ}
  {F : RoutingLaw Γ} {ε : ℝ} {n : ℕ}

/-- The microscopic configuration `x(t)` of the run: the flow through `(x₀, p₀)`. -/
noncomputable def xt (R : ThinRun N V K F ε n) (t : ℝ) : ℝ × ℝ := (N.flow ε t (R.x₀, R.p₀)).1

/-- The microscopic momentum `ξ(t)` of the run. -/
noncomputable def pt (R : ThinRun N V K F ε n) (t : ℝ) : ℝ × ℝ := (N.flow ε t (R.x₀, R.p₀)).2

/-- The run on `[0, S]`, as a trajectory of `H_ε`. -/
noncomputable def traj (R : ThinRun N V K F ε n) (S : ℝ) : N.MicroTrajectory ε S :=
  N.flowTraj ε (R.x₀, R.p₀) S

@[simp] theorem traj_x (R : ThinRun N V K F ε n) (S : ℝ) : (R.traj S).x = R.xt := rfl
@[simp] theorem traj_p (R : ThinRun N V K F ε n) (S : ℝ) : (R.traj S).p = R.pt := rfl

theorem xt_zero (R : ThinRun N V K F ε n) : R.xt 0 = R.x₀ := by simp [xt]
theorem pt_zero (R : ThinRun N V K F ε n) : R.pt 0 = R.p₀ := by simp [pt]

/-- The flow restarted at the state of the run at time `a ≥ 0` is the run shifted by `a`. -/
theorem flow_restart (R : ThinRun N V K F ε n) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    N.flow ε t (R.xt a, R.pt a) = (R.xt (a + t), R.pt (a + t)) := by
  simp only [xt, pt, Prod.mk.eta]
  rw [flow_add ε ha ht]

/-- The speed bound of the window. -/
noncomputable def speedMax (R : ThinRun N V K F ε n) : ℝ := 1 + 2 * |R.Kmax + R.gap - R.Vmin|

theorem speedMax_pos (R : ThinRun N V K F ε n) : 0 < R.speedMax := by
  rw [speedMax]; positivity

/-- **(E), along the run**: from a prepared, not arriving state of the run at time `a ≥ 0`, the run
performs an edge flight on `[a, c]` for some `c`. -/
theorem exists_flight (R : ThinRun N V K F ε n) {η : Γ.EdgeEnd} {a : ℝ} (ha : 0 ≤ a)
    (hp : N.Prepared V K ε η (R.xt a) (R.pt a))
    (hgo : 0 < N.toGo ε η (N.long η.1 (R.xt a))) :
    ∃ c, N.EdgeFlight V K ε η R.xt R.pt a c := by
  obtain ⟨b, hb⟩ := R.edgeRed η (R.xt a) (R.pt a) hp (not_arriving_of_toGo_pos hgo)
  refine ⟨a + b, hb.translate (fun t ht => ?_) (fun t ht => ?_)⟩
  · rw [R.flow_restart ha ht.1]
  · rw [R.flow_restart ha ht.1]

/-- **(J), along the run**: from a state of the run arriving at `η` at time `a ≥ 0`, the run
performs a junction passage on `[a, c]` for some `c`. -/
theorem exists_passage (R : ThinRun N V K F ε n) {η : Γ.EdgeEnd} {a : ℝ} (ha : 0 ≤ a)
    (harr : N.Arriving V K ε η (R.xt a) (R.pt a)) :
    ∃ c, N.JunctionPassage V K F.routeGerm ε η R.xt R.pt a c := by
  obtain ⟨b, hb⟩ := R.jct η (R.xt a) (R.pt a) harr
  have hb0 : 0 ≤ b := hb.lt.le
  refine ⟨a + b, hb.translate ?_ ?_ ?_⟩
  · rw [R.flow_restart ha hb0]
  · rw [R.flow_restart ha le_rfl, add_zero]
  · rw [R.flow_restart ha hb0]

/-- **The travel bound** along a flight of the run, from the window condition. -/
theorem toGo_le (R : ThinRun N V K F ε n) {η : Γ.EdgeEnd} {a c : ℝ} (ha : 0 ≤ a)
    (hfl : N.EdgeFlight V K ε η R.xt R.pt a c) (hp : N.Prepared V K ε η (R.xt a) (R.pt a)) :
    N.toGo ε η (N.long η.1 (R.xt a)) ≤ R.speedMax * (c - a) :=
  EdgeFlight.toGo_le (Θ := R.traj c) ha le_rfl hfl hp (fun E hE => R.gap_le E hE η.1)
    (R.forceErr_lt η.1) R.le_Kmax (R.Vmin_le η.1)

/-- The germ at which flight `j` arrives. -/
noncomputable def germ (R : ThinRun N V K F ε n) (j : ℕ) : Γ.EdgeEnd :=
  F.itinerary R.germ₀ j

open Classical in
/-- The time at which the edge flight starting at `a` towards `η` ends. -/
noncomputable def flightEnd (R : ThinRun N V K F ε n) (η : Γ.EdgeEnd) (a : ℝ) : ℝ :=
  if h : ∃ c, N.EdgeFlight V K ε η R.xt R.pt a c then h.choose else a + 1

open Classical in
/-- The time at which the junction passage entered at `a` through `η` ends. -/
noncomputable def passEnd (R : ThinRun N V K F ε n) (η : Γ.EdgeEnd) (a : ℝ) : ℝ :=
  if h : ∃ c, N.JunctionPassage V K F.routeGerm ε η R.xt R.pt a c then h.choose else a + 1

theorem flightEnd_spec (R : ThinRun N V K F ε n) {η : Γ.EdgeEnd} {a : ℝ}
    (h : ∃ c, N.EdgeFlight V K ε η R.xt R.pt a c) :
    N.EdgeFlight V K ε η R.xt R.pt a (R.flightEnd η a) := by
  classical
  rw [flightEnd, dif_pos h]
  exact h.choose_spec

theorem passEnd_spec (R : ThinRun N V K F ε n) {η : Γ.EdgeEnd} {a : ℝ}
    (h : ∃ c, N.JunctionPassage V K F.routeGerm ε η R.xt R.pt a c) :
    N.JunctionPassage V K F.routeGerm ε η R.xt R.pt a (R.passEnd η a) := by
  classical
  rw [passEnd, dif_pos h]
  exact h.choose_spec

/-- The time at which flight `j` starts. -/
noncomputable def startT (R : ThinRun N V K F ε n) : ℕ → ℝ
  | 0 => 0
  | j + 1 => passEnd R (germ R j) (flightEnd R (germ R j) (startT R j))

/-- The time at which flight `j` reaches the junction boundary. -/
noncomputable def arriveT (R : ThinRun N V K F ε n) (j : ℕ) : ℝ :=
  R.flightEnd (R.germ j) (R.startT j)

@[simp] theorem startT_zero (R : ThinRun N V K F ε n) : R.startT 0 = 0 := rfl

theorem startT_succ (R : ThinRun N V K F ε n) (j : ℕ) :
    R.startT (j + 1) = R.passEnd (R.germ j) (R.arriveT j) := by
  simp only [startT, arriveT]

/-! ### The recursion invariant -/

/-- The state of the run at the beginning of flight `j`. -/
structure Inv (R : ThinRun N V K F ε n) (j : ℕ) : Prop where
  nonneg : 0 ≤ R.startT j
  prep : N.Prepared V K ε (R.germ j) (R.xt (R.startT j)) (R.pt (R.startT j))
  toGo_pos : 0 < N.toGo ε (R.germ j) (N.long (R.germ j).1 (R.xt (R.startT j)))

variable {R : ThinRun N V K F ε n}

theorem inv_zero : Inv R 0 where
  nonneg := le_rfl
  prep := by rw [startT_zero, R.xt_zero, R.pt_zero]; exact R.init
  toGo_pos := by rw [startT_zero, R.xt_zero]; exact R.init_toGo

/-- The edge flight of step `j`. -/
theorem Inv.flight {j : ℕ} (h : Inv R j) :
    N.EdgeFlight V K ε (R.germ j) R.xt R.pt (R.startT j) (R.arriveT j) :=
  R.flightEnd_spec (R.exists_flight h.nonneg h.prep h.toGo_pos)

theorem Inv.startT_lt_arriveT {j : ℕ} (h : Inv R j) : R.startT j < R.arriveT j := h.flight.lt

theorem Inv.arriveT_nonneg {j : ℕ} (h : Inv R j) : 0 ≤ R.arriveT j :=
  h.nonneg.trans h.startT_lt_arriveT.le

/-- The junction passage of step `j`. -/
theorem Inv.passage {j : ℕ} (h : Inv R j) :
    N.JunctionPassage V K F.routeGerm ε (R.germ j) R.xt R.pt (R.arriveT j) (R.startT (j + 1)) := by
  rw [startT_succ]
  exact R.passEnd_spec (R.exists_passage h.arriveT_nonneg h.flight.arrive)

/-- The edge of the germ reached by flight `j + 1` is the edge of the routed germ. -/
theorem germ_succ_fst' (R : ThinRun N V K F ε n) (j : ℕ) :
    (R.germ (j + 1)).1 = (F.routeGerm (R.germ j)).1 := by
  rw [germ, germ, RoutingLaw.itinerary_succ, otherEnd_fst]

/-- **A full flight travels a whole edge**: after the first junction passage the particle starts
at one junction boundary of its edge and ends at the other. -/
theorem toGo_succ {j : ℕ} (h : Inv R j) :
    N.toGo ε (R.germ (j + 1)) (N.long (R.germ (j + 1)).1 (R.xt (R.startT (j + 1))))
      = Γ.length (R.germ (j + 1)).1 - 2 * N.offset ε := by
  have hoff : 2 * N.offset ε < Γ.length (R.germ (j + 1)).1 := by
    have := minEdgeLen_le Γ R.germ₀.1 (R.germ (j + 1)).1
    linarith [R.offset_lt]
  have hd := h.passage.depart.boundary
  have hother : F.routeGerm (R.germ j) = otherEnd (R.germ (j + 1)) := by
    rw [germ, germ, RoutingLaw.itinerary_succ, otherEnd_otherEnd]
  rw [hother] at hd
  have hfst : (otherEnd (R.germ (j + 1))).1 = (R.germ (j + 1)).1 := rfl
  rw [hfst] at hd
  rw [ThinHamiltonianNetwork.toGo, hd, coordinate_otherEnd, sign_otherEnd]
  rcases hb : (R.germ (j + 1)).2 with _ | _
  · rw [sign_of_false hb, coordinate_of_false hb]
    rw [abs_of_nonpos (by linarith)]
    ring
  · rw [sign_of_true hb, coordinate_of_true' hb]
    rw [abs_of_nonneg (by linarith)]
    ring

theorem Inv.succ {j : ℕ} (h : Inv R j) : Inv R (j + 1) := by
  have hp := h.passage
  refine ⟨?_, ?_, ?_⟩
  · exact h.arriveT_nonneg.trans hp.lt.le
  · have hd := hp.depart.prepared
    have hg : otherEnd (F.routeGerm (R.germ j)) = R.germ (j + 1) := by
      rw [germ, germ, RoutingLaw.itinerary_succ]
    rwa [hg] at hd
  · rw [toGo_succ h]
    have := minEdgeLen_le Γ R.germ₀.1 (R.germ (j + 1)).1
    linarith [R.offset_lt]

/-- **The invariant holds along the whole run.** -/
theorem inv (R : ThinRun N V K F ε n) : ∀ j, Inv R j := by
  intro j
  induction j with
  | zero => exact inv_zero
  | succ i ih => exact ih.succ

/-! ### The projected chain -/

/-- The end time of chain flight `j`: the arrival at the junction boundary for `j < n`, and the
middle of the last flight for `j = n`. -/
noncomputable def stopT (R : ThinRun N V K F ε n) (j : ℕ) : ℝ :=
  if j < n then R.arriveT j else (R.startT n + R.arriveT n) / 2

/-- The projected graph state during chain flight `j`: the image of the microscopic trajectory
under the projection `π_ε`. -/
noncomputable def gcurve (R : ThinRun N V K F ε n) (j : ℕ) (t : ℝ) : ℝ × ℝ :=
  N.gState (R.germ j).1 (R.xt t) (R.pt t)

theorem stopT_of_lt (R : ThinRun N V K F ε n) {j : ℕ} (h : j < n) : R.stopT j = R.arriveT j :=
  if_pos h

theorem stopT_self (R : ThinRun N V K F ε n) :
    R.stopT n = (R.startT n + R.arriveT n) / 2 := if_neg (lt_irrefl _)

theorem startT_lt_stopT {j : ℕ} (h : Inv R j) (hj : j ≤ n) : R.startT j < R.stopT j := by
  rcases lt_or_eq_of_le hj with hlt | heq
  · rw [R.stopT_of_lt hlt]; exact h.startT_lt_arriveT
  · subst heq
    rw [R.stopT_self]
    linarith [h.startT_lt_arriveT]

theorem stopT_le_arriveT {j : ℕ} (h : Inv R j) (hj : j ≤ n) : R.stopT j ≤ R.arriveT j := by
  rcases lt_or_eq_of_le hj with hlt | heq
  · rw [R.stopT_of_lt hlt]
  · subst heq
    rw [R.stopT_self]
    linarith [h.startT_lt_arriveT]

theorem Icc_subset' {j : ℕ} (h : Inv R j) (hj : j ≤ n) :
    Icc (R.startT j) (R.stopT j) ⊆ Icc (R.startT j) (R.arriveT j) :=
  Icc_subset_Icc le_rfl (stopT_le_arriveT h hj)

theorem Ioo_subset' {j : ℕ} (h : Inv R j) (hj : j ≤ n) :
    Ioo (R.startT j) (R.stopT j) ⊆ Ioo (R.startT j) (R.arriveT j) :=
  Ioo_subset_Ioo le_rfl (stopT_le_arriveT h hj)

/-- The edge of the germ reached by flight `j + 1` is the edge of the routed germ. -/
theorem germ_succ_fst (R : ThinRun N V K F ε n) (j : ℕ) :
    (R.germ (j + 1)).1 = (F.routeGerm (R.germ j)).1 := R.germ_succ_fst' j

/-- **The projected flight solves the edge equations up to `γ_ε`.**  Along an edge flight the
projected curve `(q, p)` has derivative `(p, -⟨∇W_ε, τ_e⟩)`, at distance
`|⟨∇W_ε, τ_e⟩ - V_e'(q)| ≤ γ_ε` (E3) from the edge vector field `(p, -V_e'(q))`. -/
theorem flight_ode (R : ThinRun N V K F ε n) {η : Γ.EdgeEnd} {a c : ℝ} (ha : 0 ≤ a)
    (hfl : N.EdgeFlight V K ε η R.xt R.pt a c) :
    ∀ t ∈ Icc a c,
      dist (N.longP η.1 (R.pt t), N.longP η.1 (N.force ε (R.xt t)))
        (V.edgeVectorField η.1 (N.gState η.1 (R.xt t) (R.pt t))) ≤ N.forceErr ε ∧
      HasDerivWithinAt (fun r => N.gState η.1 (R.xt r) (R.pt r))
        (N.longP η.1 (R.pt t), N.longP η.1 (N.force ε (R.xt t))) (Icc a c) t := by
  intro t ht
  have hsub : Icc a c ⊆ Icc (0 : ℝ) c := Icc_subset_Icc ha le_rfl
  refine ⟨?_, ?_⟩
  · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, MechanicalPotential.edgeVectorField,
      gState_fst, gState_snd, sub_self, abs_zero, longP_force, MechanicalPotential.force,
      max_le_iff]
    refine ⟨N.forceErr_nonneg ε, ?_⟩
    rw [show -N.longGrad ε η.1 (R.xt t) - -deriv (V.extension η.1) (N.long η.1 (R.xt t))
      = -(N.longGrad ε η.1 (R.xt t) - deriv (V.extension η.1) (N.long η.1 (R.xt t))) by ring,
      abs_neg]
    exact hfl.force t ht
  · exact (hasDerivWithinAt_gState η.1 ((R.traj c).ode_pos t (hsub ht))
      ((R.traj c).ode_mom t (hsub ht))).mono hsub

/-- **The projected chain of a microscopic run.**  Every field of `HybridChain` is discharged from
(E) and (J): the flights are the edge flights of (E), the impacts are the junction passages of
(J), and the parameters are the scales `δ_ε, θ_ε, γ_ε, μ_ε` of the network. -/
noncomputable def chain (R : ThinRun N V K F ε n) : HybridChain V F (thinParams N ε) where
  N := n
  start := R.startT
  stop := R.stopT
  edge j := (R.germ j).1
  curve := R.gcurve
  germ := R.germ
  start_zero := R.startT_zero
  start_lt_stop := fun j hj => startT_lt_stopT (R.inv j) hj
  stop_le_start_succ := by
    intro j hj
    rw [R.stopT_of_lt hj]
    exact (R.inv j).passage.lt.le
  start_succ_le := by
    intro j hj
    rw [R.stopT_of_lt hj, thinParams_dwell]
    exact (R.inv j).passage.le
  flight_ode := by
    intro j hj
    have hode := R.flight_ode (R.inv j).nonneg (R.inv j).flight
    refine ⟨fun t => (N.longP (R.germ j).1 (R.pt t), N.longP (R.germ j).1 (N.force ε (R.xt t))),
      fun t ht => ⟨(hode t (Icc_subset' (R.inv j) hj ht)).1, ?_⟩⟩
    exact (hode t (Icc_subset' (R.inv j) hj ht)).2.mono (Icc_subset' (R.inv j) hj)
  flight_tube := by
    intro j hj t ht
    have hfl := (R.inv j).flight
    have ht' := Icc_subset' (R.inv j) hj ht
    change N.long (R.germ j).1 (R.xt t) ∈ Icc (N.offset ε) (Γ.length (R.germ j).1 - N.offset ε)
    rcases eq_or_lt_of_le ht'.1 with h | h
    · rw [← h]; exact (R.inv j).prep.inside
    rcases eq_or_lt_of_le ht'.2 with h' | h'
    · rw [h']; exact hfl.arrive.prepared.inside
    · exact Ioo_subset_Icc_self (hfl.inside t ⟨h, h'⟩)
  flight_inside := by
    intro j hj t ht
    exact (R.inv j).flight.inside t (Ioo_subset' (R.inv j) hj ht)
  final_inside := by
    have hn := R.inv n
    have hmid : (R.startT n + R.arriveT n) / 2 ∈ Ioo (R.startT n) (R.arriveT n) := by
      have := hn.startT_lt_arriveT
      constructor <;> linarith
    have hstrict := hn.flight.inside _ hmid
    rw [R.stopT_self]
    exact hstrict
  germ_edge := fun _ _ => rfl
  arrive := by
    intro j hj
    rw [R.stopT_of_lt hj, thinParams_offset]
    exact (R.inv j).flight.arrive.boundary
  edge_succ := fun j _ => R.germ_succ_fst j
  depart_coord := by
    intro j hj
    have hd := (R.inv j).passage.depart.boundary
    have he := R.germ_succ_fst j
    change N.long (R.germ (j + 1)).1 (R.xt (R.startT (j + 1))) = _
    rw [he, thinParams_offset]
    exact hd
  depart_mom := by
    intro j hj
    have hm := (R.inv j).passage.mom
    have he := R.germ_succ_fst j
    rw [R.stopT_of_lt hj, thinParams_momErr]
    change |N.longP (R.germ (j + 1)).1 (R.pt (R.startT (j + 1))) -
      F.departureMomentum (R.germ j) (N.longP (R.germ j).1 (R.pt (R.arriveT j)))| ≤ _
    rw [he, RoutingLaw.departureMomentum, neg_mul, sub_neg_eq_add]
    exact hm

@[simp] theorem chain_N (R : ThinRun N V K F ε n) : R.chain.N = n := rfl
@[simp] theorem chain_start (R : ThinRun N V K F ε n) (j : ℕ) :
    R.chain.start j = R.startT j := rfl
@[simp] theorem chain_stop (R : ThinRun N V K F ε n) (j : ℕ) : R.chain.stop j = R.stopT j := rfl
@[simp] theorem chain_edge (R : ThinRun N V K F ε n) (j : ℕ) :
    R.chain.edge j = (R.germ j).1 := rfl
@[simp] theorem chain_curve (R : ThinRun N V K F ε n) (j : ℕ) (t : ℝ) :
    R.chain.curve j t = R.gcurve j t := rfl
@[simp] theorem chain_germ (R : ThinRun N V K F ε n) (j : ℕ) : R.chain.germ j = R.germ j := rfl

/-- The chain starts at the projected initial state of the microscopic trajectory. -/
theorem chain_curve_zero_zero (R : ThinRun N V K F ε n) :
    R.chain.curve 0 0 = N.gState R.germ₀.1 R.x₀ R.p₀ := by
  change N.gState R.germ₀.1 (R.xt 0) (R.pt 0) = _
  rw [R.xt_zero, R.pt_zero]

/-! ### The time window of the run -/

/-- The minimal duration of a full edge flight. -/
noncomputable def minDur (R : ThinRun N V K F ε n) : ℝ :=
  (minEdgeLen Γ R.germ₀.1 - 2 * N.offset ε) / R.speedMax

theorem minDur_pos (R : ThinRun N V K F ε n) : 0 < R.minDur := by
  refine div_pos ?_ R.speedMax_pos
  linarith [R.offset_lt]

/-- **The microscopic run is not faster than the speed bound of the window**: each full flight
lasts at least `minDur`. -/
theorem startT_lower (R : ThinRun N V K F ε n) :
    ∀ j : ℕ, ((j : ℝ) - 1) * R.minDur ≤ R.startT j := by
  have hsp := R.speedMax_pos
  intro j
  induction j with
  | zero => simp only [startT_zero, Nat.cast_zero]; linarith [R.minDur_pos]
  | succ i ih =>
      have hinv := R.inv i
      have hpass := hinv.passage.lt.le
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        have hz : 0 ≤ R.startT 1 := (R.inv 1).nonneg
        push_cast
        simpa using hz
      · obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
        have hfl := R.toGo_le hinv.nonneg hinv.flight hinv.prep
        have hto := toGo_succ (R.inv l)
        rw [hto] at hfl
        have hmin : minEdgeLen Γ R.germ₀.1 ≤ Γ.length (R.germ (l + 1)).1 :=
          minEdgeLen_le Γ R.germ₀.1 _
        have hdur : R.minDur ≤ R.arriveT (l + 1) - R.startT (l + 1) := by
          rw [minDur, div_le_iff₀ hsp]
          linarith
        push_cast at ih ⊢
        linarith

theorem stopT_lower (R : ThinRun N V K F ε n) : ((n : ℝ) - 1) * R.minDur ≤ R.stopT n := by
  have h1 := R.startT_lower n
  have h2 := startT_lt_stopT (R.inv n) le_rfl
  linarith

/-! ### The chain is the projection of the microscopic trajectory -/

/-- **The projected chain is the image of the microscopic trajectory under `π_ε`**, and the
transverse displacement stays inside the tube along every flight. -/
theorem chain_is_projection (R : ThinRun N V K F ε n) :
    ∀ j ≤ n, ∀ t ∈ Icc (R.startT j) (R.stopT j),
      R.chain.curve j t = N.gState (R.chain.edge j) (R.xt t) (R.pt t) ∧
        |N.trans (R.chain.edge j) (R.xt t)| ≤ N.tubeWidth ε := by
  intro j hj t ht
  refine ⟨rfl, ?_⟩
  exact (R.inv j).flight.transverse t (Icc_subset' (R.inv j) hj ht)

end ThinRun

end HamiltonianMetricGraphs
