/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.UniversalComponentOrbit
import HamiltonianMetricGraphs.Realization.GraphFlow

/-!
# The graph flow at zero potential lifts to the unrolled orbits

For `V ≡ 0` the paper's graph flow `Φ_t` (Theorem VI.5, `FlightState.trajectory` with the vertex
law `F.toBorelScattering V` of the routing law) is free motion on the edges, and at a vertex the
law `S^F` continues the motion from the end `F(η)` at the same speed.  In the unrolled orbit of
`UniversalComponentOrbit.lean` this is uniform motion along the line, through the glued points:

  `Φ_t(unroll y₀, σ(y₀) v₀) = (unroll (y₀ + v₀ t), σ(y₀ + v₀ t) v₀)` whenever `y₀ + v₀ t` is not
  a glued point,

and the vertex impacts are the times at which `y₀ + v₀ t` is a glued point (`lift_flow`).  This is
the identity `(IX.lifted-flow)` of the paper before it is composed with the folding map `f`.

The proof follows the chain of flights of a finite window of the flow (`FlowRun.chain`): by
induction over the flights, flight `j` runs along segment `k₀ ± j` of the unrolled orbit.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

variable {Γ : FiniteMetricGraph} {F : RoutingLaw Γ}

/-! ### Vertex impacts and the flow from a state -/

/-- **The vertex impacts of the flow from `a`**: the positive times `impactReal n`, `n ≥ 1`, of
the scattering events of the chain of `a`. -/
def IsVertexImpact {V : MechanicalPotential Γ} (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (t : ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ (FlightState.iterate V S a n).isSome ∧ FlightState.impactReal V S a n = t

/-- **The graph flow `Φ_t` from the flight state `a`**: `FlightState.trajectory`, Theorem VI.5 of
the paper (the nonemptiness of the edge set is supplied by the edge of `a`). -/
noncomputable def graphFlow {V : MechanicalPotential Γ} (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (t : ℝ) : Γ.Edge × ℝ × ℝ :=
  haveI : Nonempty Γ.Edge := ⟨a.edge⟩
  FlightState.trajectory V S a t

theorem graphFlow_eq {V : MechanicalPotential Γ} [Nonempty Γ.Edge]
    (S : BorelEnergyPreservingScattering V) (a : V.FlightState) (t : ℝ) :
    graphFlow S a t = FlightState.trajectory V S a t := rfl

/-! ### Free flights -/

/-- **A flight of a graph trajectory at zero potential is free motion.** -/
theorem free_flight (g : GraphTrajectory (zeroPotential Γ) F) {j : ℕ} (hj : j ≤ g.N) :
    ∀ t ∈ Icc (g.start j) (g.stop j),
      g.curve j t = ((g.curve j (g.start j)).1 + (g.curve j (g.start j)).2 * (t - g.start j),
        (g.curve j (g.start j)).2) := by
  have hode := g.flight_ode_exact hj
  have hlt := g.start_lt_stop j hj
  set a := g.start j
  set b := g.stop j
  have hd : ∀ t ∈ Icc a b, HasDerivWithinAt (g.curve j) ((g.curve j t).2, 0) (Icc a b) t := by
    intro t ht
    have := hode t ht
    rwa [zeroPotential_edgeVectorField] at this
  have hp : ∀ t ∈ Icc a b, (g.curve j t).2 = (g.curve j a).2 := by
    have hcont : ContinuousOn (fun s => (g.curve j s).2) (Icc a b) := fun s hs =>
      (hd s hs).snd_comp.continuousWithinAt
    exact constant_of_has_deriv_right_zero hcont
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hd s (Ico_subset_Icc_self hs)).snd_comp)
  have hq : ∀ t ∈ Icc a b,
      (g.curve j t).1 - (g.curve j a).2 * (t - a) =
        (g.curve j a).1 - (g.curve j a).2 * (a - a) := by
    have hd' : ∀ t ∈ Icc a b,
        HasDerivWithinAt (fun s => (g.curve j s).1 - (g.curve j a).2 * (s - a)) 0 (Icc a b) t := by
      intro t ht
      have h1 := (hd t ht).fst_comp
      have h2 := ((hasDerivWithinAt_id t (Icc a b)).sub_const a).const_mul (g.curve j a).2
      refine (h1.sub h2).congr_deriv ?_
      simp only
      rw [hp t ht]
      ring
    have hcont : ContinuousOn (fun s => (g.curve j s).1 - (g.curve j a).2 * (s - a)) (Icc a b) :=
      fun s hs => (hd' s hs).continuousWithinAt
    exact constant_of_has_deriv_right_zero hcont
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hd' s (Ico_subset_Icc_self hs)))
  intro t ht
  refine Prod.ext ?_ (hp t ht)
  have := hq t ht
  simp only [sub_self, mul_zero, sub_zero] at this
  simp only
  linarith

/-! ### The lifted state -/

section Lift

variable (F) (β : Γ.EdgeEnd)

/-- The graph state at the point `y` of segment `k` of the unrolled orbit of `β`, moving with
velocity `v` along the line. -/
noncomputable def segState (k : ℤ) (y v : ℝ) : ℝ × ℝ :=
  (EdgeEnd.coordinate Γ (germSeq F β k) -
      EdgeEnd.sign Γ (germSeq F β k) * (posSeq F β (k + 1) - y),
    EdgeEnd.sign Γ (germSeq F β k) * v)

/-- The segment visited by flight `j` from segment `k₀` in the direction of `v₀`. -/
noncomputable def liftIdx (k₀ : ℤ) (v₀ : ℝ) (j : ℕ) : ℤ := if 0 < v₀ then k₀ + j else k₀ - j

theorem liftIdx_succ_pos {k₀ : ℤ} {v₀ : ℝ} (hv : 0 < v₀) (j : ℕ) :
    liftIdx k₀ v₀ (j + 1) = liftIdx k₀ v₀ j + 1 := by
  simp only [liftIdx, if_pos hv]; push_cast; ring

theorem liftIdx_succ_neg {k₀ : ℤ} {v₀ : ℝ} (hv : v₀ < 0) (j : ℕ) :
    liftIdx k₀ v₀ (j + 1) = liftIdx k₀ v₀ j - 1 := by
  simp only [liftIdx, if_neg (not_lt.mpr hv.le)]; push_cast; ring

@[simp] theorem liftIdx_zero (k₀ : ℤ) (v₀ : ℝ) : liftIdx k₀ v₀ 0 = k₀ := by
  simp [liftIdx]

/-- **The invariant of the lift**: flight `j` starts on segment `liftIdx j` at the lifted
coordinate `y₀ + v₀ · start j`, which is at the entry end of the segment (or inside it). -/
structure LiftInv (g : GraphTrajectory (zeroPotential Γ) F) (k₀ : ℤ) (y₀ v₀ : ℝ) (j : ℕ) :
    Prop where
  edge : g.edge j = (germSeq F β (liftIdx k₀ v₀ j)).1
  curve : g.curve j (g.start j) = segState F β (liftIdx k₀ v₀ j) (y₀ + v₀ * g.start j) v₀
  pos : 0 < v₀ → posSeq F β (liftIdx k₀ v₀ j) ≤ y₀ + v₀ * g.start j ∧
    y₀ + v₀ * g.start j < posSeq F β (liftIdx k₀ v₀ j + 1)
  neg : v₀ < 0 → posSeq F β (liftIdx k₀ v₀ j) < y₀ + v₀ * g.start j ∧
    y₀ + v₀ * g.start j ≤ posSeq F β (liftIdx k₀ v₀ j + 1)

variable {F β}

namespace LiftInv

variable {g : GraphTrajectory (zeroPotential Γ) F} {k₀ : ℤ} {y₀ v₀ : ℝ} {j : ℕ}

theorem curve_eq (I : LiftInv F β g k₀ y₀ v₀ j) (hj : j ≤ g.N) {t : ℝ}
    (ht : t ∈ Icc (g.start j) (g.stop j)) :
    g.curve j t = segState F β (liftIdx k₀ v₀ j) (y₀ + v₀ * t) v₀ := by
  rw [free_flight g hj t ht, I.curve, segState, segState]
  simp only [Prod.mk.injEq, and_true]
  ring

theorem mem_Icc (I : LiftInv F β g k₀ y₀ v₀ j) (hj : j ≤ g.N) {t : ℝ}
    (ht : t ∈ Icc (g.start j) (g.stop j)) :
    y₀ + v₀ * t ∈ Icc (posSeq F β (liftIdx k₀ v₀ j)) (posSeq F β (liftIdx k₀ v₀ j + 1)) := by
  have h := g.physical hj ht
  rw [I.curve_eq hj ht, I.edge, segState, chart_mem_Icc_iff, segLen_eq_posSeq] at h
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

theorem mem_Ioo (I : LiftInv F β g k₀ y₀ v₀ j) (hj : j ≤ g.N) {t : ℝ}
    (ht : t ∈ Ioo (g.start j) (g.stop j)) :
    y₀ + v₀ * t ∈ Ioo (posSeq F β (liftIdx k₀ v₀ j)) (posSeq F β (liftIdx k₀ v₀ j + 1)) := by
  have h := g.interior hj ht
  rw [I.curve_eq hj (Ioo_subset_Icc_self ht), I.edge, segState, chart_mem_Ioo_iff,
    segLen_eq_posSeq] at h
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- An edge-end on the edge of `ζ` is `ζ` or its opposite end. -/
theorem eq_or_eq_otherEnd {η ζ : Γ.EdgeEnd} (h : η.1 = ζ.1) : η = ζ ∨ η = otherEnd ζ := by
  obtain ⟨e, b⟩ := η
  obtain ⟨e', b'⟩ := ζ
  simp only at h
  subst h
  cases b <;> cases b' <;> simp [otherEnd]

/-- The lifted coordinate at the end of a non-final flight. -/
theorem stop_pos (I : LiftInv F β g k₀ y₀ v₀ j) (hj : j < g.N) (hv : 0 < v₀) :
    y₀ + v₀ * g.stop j = posSeq F β (liftIdx k₀ v₀ j + 1) ∧
      g.germ j = germSeq F β (liftIdx k₀ v₀ j) := by
  set κ := liftIdx k₀ v₀ j
  have hlt := g.start_lt_stop j hj.le
  have hmem := I.mem_Icc hj.le ⟨hlt.le, le_rfl⟩
  have hstart := (I.pos hv).1
  have harr := g.arrive_eq hj
  rw [I.curve_eq hj.le ⟨hlt.le, le_rfl⟩, segState] at harr
  rcases eq_or_eq_otherEnd (show (g.germ j).1 = (germSeq F β κ).1 by
      rw [g.germ_edge j hj, I.edge]) with hg | hg
  · rw [hg] at harr
    have : EdgeEnd.sign Γ (germSeq F β κ) * (posSeq F β (κ + 1) - (y₀ + v₀ * g.stop j)) = 0 := by
      linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (Γ.edgeEnd_sign_ne_zero _)
    · exact ⟨by linarith, hg⟩
  · exfalso
    rw [hg, coordinate_otherEnd_eq, segLen_eq_posSeq] at harr
    have h2 : EdgeEnd.sign Γ (germSeq F β κ) *
        (posSeq F β κ - (y₀ + v₀ * g.stop j)) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact Γ.edgeEnd_sign_ne_zero _ h
    · have : v₀ * g.start j < v₀ * g.stop j := mul_lt_mul_of_pos_left hlt hv
      linarith

theorem stop_neg (I : LiftInv F β g k₀ y₀ v₀ j) (hj : j < g.N) (hv : v₀ < 0) :
    y₀ + v₀ * g.stop j = posSeq F β (liftIdx k₀ v₀ j) ∧
      g.germ j = otherEnd (germSeq F β (liftIdx k₀ v₀ j)) := by
  set κ := liftIdx k₀ v₀ j
  have hlt := g.start_lt_stop j hj.le
  have hstart := (I.neg hv).2
  have harr := g.arrive_eq hj
  rw [I.curve_eq hj.le ⟨hlt.le, le_rfl⟩, segState] at harr
  rcases eq_or_eq_otherEnd (show (g.germ j).1 = (germSeq F β κ).1 by
      rw [g.germ_edge j hj, I.edge]) with hg | hg
  · exfalso
    rw [hg] at harr
    have : EdgeEnd.sign Γ (germSeq F β κ) * (posSeq F β (κ + 1) - (y₀ + v₀ * g.stop j)) = 0 := by
      linarith
    rcases mul_eq_zero.mp this with h | h
    · exact Γ.edgeEnd_sign_ne_zero _ h
    · have : v₀ * g.stop j < v₀ * g.start j := mul_lt_mul_of_neg_left hlt hv
      linarith
  · rw [hg, coordinate_otherEnd_eq, segLen_eq_posSeq] at harr
    have h2 : EdgeEnd.sign Γ (germSeq F β κ) *
        (posSeq F β κ - (y₀ + v₀ * g.stop j)) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (Γ.edgeEnd_sign_ne_zero _)
    · exact ⟨by linarith, hg⟩

/-- **The inductive step**: through a vertex the motion continues on the next segment. -/
theorem succ (I : LiftInv F β g k₀ y₀ v₀ j) (hj : j < g.N) (hv : v₀ ≠ 0) :
    LiftInv F β g k₀ y₀ v₀ (j + 1) := by
  have hstart : g.start (j + 1) = g.stop j := g.start_succ_eq_stop hj
  have hedge := g.edge_succ j hj
  have hcoord := g.depart_coord_eq hj
  have hmom := g.depart_mom_eq hj
  have hlt := g.start_lt_stop j hj.le
  rw [I.curve_eq hj.le ⟨hlt.le, le_rfl⟩, segState] at hmom
  rw [hstart] at hcoord hmom
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · obtain ⟨hy, hg⟩ := I.stop_neg hj hneg
    set κ := liftIdx k₀ v₀ j
    have hκ : liftIdx k₀ v₀ (j + 1) = κ - 1 := liftIdx_succ_neg hneg j
    have hF : F.routeGerm (g.germ j) = germSeq F β (κ - 1) := by
      rw [hg, germSeq_pred]
    refine ⟨?_, ?_, fun h => absurd h (not_lt.mpr hneg.le), fun _ => ?_⟩
    · rw [hedge, hF, hκ]
    · rw [hκ, segState, hstart, hy, show κ - 1 + 1 = κ by ring, sub_self, mul_zero, sub_zero]
      refine Prod.ext ?_ ?_
      · rw [hcoord, hF]
      · rw [hmom, RoutingLaw.departureMomentum, hF]
        simp only
        rw [abs_mul, abs_of_neg hneg]
        rcases sign_eq_one_or_neg_one (germSeq F β κ) with h | h <;> rw [h] <;> ring
    · rw [hκ, hstart, hy, show κ - 1 + 1 = κ by ring]
      exact ⟨(posSeq_lt_iff F β).mpr (by omega), le_rfl⟩
  · obtain ⟨hy, hg⟩ := I.stop_pos hj hpos
    set κ := liftIdx k₀ v₀ j
    have hκ : liftIdx k₀ v₀ (j + 1) = κ + 1 := liftIdx_succ_pos hpos j
    have hF : F.routeGerm (g.germ j) = otherEnd (germSeq F β (κ + 1)) := by
      rw [hg, routeGerm_germSeq]
    refine ⟨?_, ?_, fun _ => ?_, fun h => absurd h (not_lt.mpr hpos.le)⟩
    · rw [hedge, hF, hκ, otherEnd_fst]
    · rw [hκ, segState, hstart, hy]
      refine Prod.ext ?_ ?_
      · rw [hcoord, hF, coordinate_otherEnd_eq, segLen_eq_posSeq]
      · rw [hmom, RoutingLaw.departureMomentum, hF, sign_otherEnd]
        simp only
        rw [abs_mul, abs_of_pos hpos]
        rcases sign_eq_one_or_neg_one (germSeq F β κ) with h | h <;> rw [h] <;> ring
    · rw [hκ, hstart, hy]
      exact ⟨le_rfl, (posSeq_lt_iff F β).mpr (by omega)⟩

end LiftInv

/-- **The invariant holds along every graph trajectory starting on the unrolled orbit.** -/
theorem liftInv_all (g : GraphTrajectory (zeroPotential Γ) F) {k₀ : ℤ} {y₀ v₀ : ℝ}
    (hy : y₀ ∈ Ioo (posSeq F β k₀) (posSeq F β (k₀ + 1))) (hv : v₀ ≠ 0)
    (he : g.edge 0 = (germSeq F β k₀).1) (hs : g.curve 0 0 = segState F β k₀ y₀ v₀) :
    ∀ j ≤ g.N, LiftInv F β g k₀ y₀ v₀ j := by
  intro j hj
  induction j with
  | zero =>
      refine ⟨by rw [he, liftIdx_zero], ?_, fun _ => ?_, fun _ => ?_⟩
      · rw [g.start_zero, liftIdx_zero, mul_zero, add_zero, hs]
      · rw [g.start_zero, liftIdx_zero, mul_zero, add_zero]; exact ⟨hy.1.le, hy.2⟩
      · rw [g.start_zero, liftIdx_zero, mul_zero, add_zero]; exact ⟨hy.1, hy.2.le⟩
  | succ i ih => exact (ih (Nat.le_of_succ_le hj)).succ (Nat.lt_of_succ_le hj) hv

/-! ### The lift of the flow -/

/-- **The graph flow at zero potential lifts to the unrolled orbit.**  Let the flight state `a`
sit at the point `unroll y₀` of segment `k₀`, with momentum `σ(y₀) v₀`.  Then for every `t ≥ 0`
at which `y₀ + v₀ t` is not a glued point, the flow is at the point `unroll (y₀ + v₀ t)` with
momentum `σ(y₀ + v₀ t) v₀`; and every positive time at which `y₀ + v₀ t` is a glued point is a
vertex impact of the flow. -/
theorem lift_flow (a : (zeroPotential Γ).FlightState) {k₀ : ℤ} {y₀ v₀ : ℝ}
    (hy : y₀ ∈ Ioo (posSeq F β k₀) (posSeq F β (k₀ + 1))) (hv : v₀ ≠ 0)
    (he : a.edge = (germSeq F β k₀).1) (hs : a.state = segState F β k₀ y₀ v₀)
    {t : ℝ} (ht : 0 ≤ t) :
    (y₀ + v₀ * t ∉ gluedSet F β →
      graphFlow (F.toBorelScattering (zeroPotential Γ)) a t =
        ((germSeq F β (segIdx F β (y₀ + v₀ * t))).1,
          segState F β (segIdx F β (y₀ + v₀ * t)) (y₀ + v₀ * t) v₀)) ∧
    (0 < t → y₀ + v₀ * t ∈ gluedSet F β →
      IsVertexImpact (F.toBorelScattering (zeroPotential Γ)) a t) := by
  haveI : Nonempty Γ.Edge := ⟨a.edge⟩
  set S := F.toBorelScattering (zeroPotential Γ)
  obtain ⟨M, TM, hTM, R⟩ := FlightState.exists_flowRun S a (T := t + 1) (by linarith)
  set g : GraphTrajectory (zeroPotential Γ) F := R.chain (F := F) with hgdef
  have hinv := liftInv_all g hy hv (by rw [R.chain_edge_zero, he])
    (by rw [R.chain_curve_zero, hs])
  have hstopN : g.stop g.N = TM := R.chain_stop_N
  set j := g.flightIndex t with hjdef
  have hjN : j ≤ g.N := g.flightIndex_le t
  have hstart : g.start j ≤ t := g.start_flightIndex_le ht
  have hstop : t ≤ g.stop j := by
    rcases lt_or_eq_of_le hjN with h | h
    · rw [← g.start_succ_eq_stop h]; exact (g.lt_start_succ_flightIndex h).le
    · rw [h, hstopN]; linarith
  have I := hinv j hjN
  have hmem := I.mem_Icc hjN ⟨hstart, hstop⟩
  refine ⟨fun hng => ?_, fun htpos hgl => ?_⟩
  · have hIoo : y₀ + v₀ * t ∈
        Ioo (posSeq F β (liftIdx k₀ v₀ j)) (posSeq F β (liftIdx k₀ v₀ j + 1)) :=
      ⟨lt_of_le_of_ne hmem.1 (fun h => hng ⟨_, h⟩),
        lt_of_le_of_ne hmem.2 (fun h => hng ⟨_, h.symm⟩)⟩
    have hseg : segIdx F β (y₀ + v₀ * t) = liftIdx k₀ v₀ j := segIdx_eq F β ⟨hIoo.1.le, hIoo.2⟩
    rw [graphFlow_eq, ← R.chain_state_eq ⟨ht, by linarith⟩, g.state_eq_of_flightIndex_eq hjdef.symm,
      hseg, ← I.edge, ← I.curve_eq hjN ⟨hstart, hstop⟩]
  · obtain ⟨k, hk⟩ := hgl
    set κ := liftIdx k₀ v₀ j
    -- the glued point is an end of the current segment
    have hend : y₀ + v₀ * t = posSeq F β κ ∨ y₀ + v₀ * t = posSeq F β (κ + 1) := by
      rw [← hk] at hmem ⊢
      have h1 : κ ≤ k := (posSeq_le_iff F β).mp hmem.1
      have h2 : k ≤ κ + 1 := (posSeq_le_iff F β).mp hmem.2
      rcases (show k = κ ∨ k = κ + 1 by omega) with h | h <;> rw [h] <;> simp
    have himpact_start : t = g.start j → IsVertexImpact S a t := by
      intro hts
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · exfalso
        rw [h0, g.start_zero] at hts
        linarith
      · exact ⟨j, hpos, R.isSome_of_le hjN, hts.symm⟩
    have himpact_stop : t = g.stop j → IsVertexImpact S a t := by
      intro hts
      rcases lt_or_eq_of_le hjN with h | h
      · refine ⟨j + 1, Nat.succ_pos j, R.isSome_of_le (Nat.succ_le_of_lt h), ?_⟩
        rw [hts]
        exact (FlightState.flowStop_of_lt h).symm
      · exfalso
        rw [h, hstopN] at hts
        linarith
    rcases lt_or_gt_of_ne hv with hneg | hpos
    · obtain ⟨hs1, hs2⟩ := I.neg hneg
      rcases hend with h | h
      · -- reached the far end: the end of the flight
        apply himpact_stop
        by_contra hne
        have hlt : t < g.stop j := lt_of_le_of_ne hstop hne
        have hin := I.mem_Ioo hjN ⟨?_, hlt⟩
        · linarith [hin.1]
        · rcases lt_or_eq_of_le hstart with h' | h'
          · exact h'
          · exfalso; rw [h'] at hs1; linarith
      · apply himpact_start
        by_contra hne
        have hlt : g.start j < t := lt_of_le_of_ne hstart (Ne.symm hne)
        have : v₀ * t < v₀ * g.start j := mul_lt_mul_of_neg_left hlt hneg
        linarith
    · obtain ⟨hs1, hs2⟩ := I.pos hpos
      rcases hend with h | h
      · apply himpact_start
        by_contra hne
        have hlt : g.start j < t := lt_of_le_of_ne hstart (Ne.symm hne)
        have : v₀ * g.start j < v₀ * t := mul_lt_mul_of_pos_left hlt hpos
        linarith
      · apply himpact_stop
        by_contra hne
        have hlt : t < g.stop j := lt_of_le_of_ne hstop hne
        have hin := I.mem_Ioo hjN ⟨?_, hlt⟩
        · linarith [hin.2]
        · rcases lt_or_eq_of_le hstart with h' | h'
          · exact h'
          · exfalso; rw [h'] at hs2; linarith

end Lift

end HamiltonianMetricGraphs
