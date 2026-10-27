/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.FirstHit
import HamiltonianMetricGraphs.EdgeFlight

/-!
# Compact regular energy windows and no-Zeno estimates

This module begins the quantitative part of Lemma V.2.  Its first result extracts a strictly
positive uniform gap between a compact energy window and the finite set of vertex energies.
The edge and vertex types are assumed nonempty here: if there is an edge, this is automatic for
the concrete graph and is exactly the case in which an impact estimate has content.
-/

namespace HamiltonianMetricGraphs

open Set

/-- A forward sequence of impact times with a uniform positive separation.  This lightweight
object is the discrete target supplied by the eventual recursive scattering construction. -/
structure ForwardImpactSchedule where
  time : ℕ → ℝ
  separation : ℝ
  separation_pos : 0 < separation
  next_separated : ∀ n : ℕ, separation ≤ time (n + 1) - time n

namespace ForwardImpactSchedule

/-- Iterating the one-step separation estimate gives a linear lower bound on every impact time. -/
theorem lower_bound (I : ForwardImpactSchedule) (n : ℕ) :
    I.time 0 + n * I.separation ≤ I.time n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnext := I.next_separated n
      rw [Nat.cast_succ]
      change I.time 0 + ((n : ℝ) + 1) * I.separation ≤ I.time (n + 1)
      calc
        I.time 0 + ((n : ℝ) + 1) * I.separation =
            (I.time 0 + n * I.separation) + I.separation := by
              ring
        _ ≤ I.time n + I.separation := by linarith
        _ ≤ I.time (n + 1) - I.time n + I.time n := by linarith
        _ = I.time (n + 1) := by ring

/-- Forward impact times eventually exceed every fixed finite time.  This is the no-Zeno
conclusion needed to justify an infinite recursive concatenation on all positive times. -/
theorem eventually_gt (I : ForwardImpactSchedule) (B : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B < I.time n := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((B - I.time 0) / I.separation)
  refine ⟨N, ?_⟩
  intro n hn
  have hcast : ((B - I.time 0) / I.separation) < (n : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hlinear : B < I.time 0 + n * I.separation := by
    have hmul : B - I.time 0 < (n : ℝ) * I.separation :=
      (div_lt_iff₀ I.separation_pos).mp hcast
    linarith
  exact lt_of_lt_of_le hlinear (I.lower_bound n)

end ForwardImpactSchedule

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

namespace PhysicalEdgeSegment

variable {V}

/-- A finite (bounded-duration) maximal physical edge flight is a genuine first endpoint hit:
its completed maximal curve is a first-hit witness ending at the maximal endpoint germ.  This is
the concrete bridge from the maximal-continuation construction to the first-hit API, and it makes
every `EdgeFirstHit` no-Zeno estimate applicable to the recursive scattered flight chain. -/
noncomputable def toEdgeFirstHit {e : Γ.Edge} {x : ℝ × ℝ} (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V e x)) : V.EdgeFirstHit e x := by
  classical
  refine
    { duration := sSup (PhysicalEdgeSegment.durationSet V e x)
      duration_pos := lt_of_lt_of_le h.duration_pos (le_csSup hbdd h.mem_durationSet)
      curve := h.maximalCurveClosed hbdd
      initial := h.maximalCurveClosed_initial hbdd
      initial_physical := h.initial_physical
      in_domain := fun t ht => h.maximalCurveClosed_mem_domain hbdd ht
      integralCurve := fun t ht => h.maximalCurveClosed_hasDerivWithinAt_Icc hbdd ht
      interior_before := fun t ht => h.maximalCurveClosed_interior hbdd ht
      endpoint := if (h.maximalEndpoint hbdd).1 = 0 then false else true
      hit_endpoint := ?_ }
  rw [h.maximalCurveClosed_eq_endpoint hbdd]
  by_cases hzero : (h.maximalEndpoint hbdd).1 = 0
  · simp [hzero, FiniteMetricGraph.EdgeEnd.coordinate]
  · have hlen : (h.maximalEndpoint hbdd).1 = Γ.length e :=
      (h.maximalEndpoint_coordinate_eq_zero_or_length hbdd).resolve_left hzero
    simp [hzero, hlen, FiniteMetricGraph.EdgeEnd.coordinate]

@[simp] theorem toEdgeFirstHit_duration {e : Γ.Edge} {x : ℝ × ℝ}
    (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V e x)) :
    (h.toEdgeFirstHit hbdd).duration = sSup (PhysicalEdgeSegment.durationSet V e x) := rfl

@[simp] theorem toEdgeFirstHit_curve {e : Γ.Edge} {x : ℝ × ℝ}
    (h : V.PhysicalEdgeSegment e x)
    (hbdd : BddAbove (PhysicalEdgeSegment.durationSet V e x)) :
    (h.toEdgeFirstHit hbdd).curve = h.maximalCurveClosed hbdd := rfl

end PhysicalEdgeSegment

/-- A compact energy window avoiding the finite exceptional-energy set has a uniform positive
gap from every vertex potential. -/
theorem exists_compact_regular_energy_gap [Nonempty Γ.Edge] (K : Set ℝ) (hKcompact : IsCompact K)
    (hregular : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ E ∈ K, ∀ v : Γ.Vertex, δ ≤ |E - V.vertexValue v| := by
  classical
  by_cases hK : K.Nonempty
  · let e : Γ.Edge := Classical.choice (inferInstance : Nonempty Γ.Edge)
    letI : Nonempty Γ.Vertex := ⟨Γ.endpoint e false⟩
    have hvertex : (Finset.univ : Finset Γ.Vertex).Nonempty := Finset.univ_nonempty
    choose x hx hxmin using fun v : Γ.Vertex =>
      hKcompact.exists_isMinOn hK
        (((continuous_id.sub continuous_const).abs).continuousOn :
          ContinuousOn (fun E : ℝ => |E - V.vertexValue v|) K)
    let gaps : Finset ℝ := Finset.univ.image (fun v : Γ.Vertex => |x v - V.vertexValue v|)
    have hgaps : gaps.Nonempty := by
      rw [Finset.image_nonempty]
      exact hvertex
    let δ : ℝ := gaps.min' hgaps
    have hδ_mem : δ ∈ gaps := Finset.min'_mem gaps hgaps
    obtain ⟨v₀, -, hv₀⟩ := Finset.mem_image.mp hδ_mem
    have hδ_pos : 0 < δ := by
      rw [← hv₀]
      apply abs_pos.mpr
      intro heq
      apply hregular (x v₀) (hx v₀)
      exact (V.mem_exceptionalEnergies_iff).mpr ⟨v₀, (sub_eq_zero.mp heq).symm⟩
    refine ⟨δ, hδ_pos, ?_⟩
    intro E hE v
    exact le_trans
      (Finset.min'_le gaps _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩))
      (hxmin v hE)
  · refine ⟨1, by norm_num, ?_⟩
    intro E hE
    exact (hK ⟨E, hE⟩).elim

/-- The compact regular-energy gap survives a quarter-gap variation of the potential near an
endpoint.  No monotonicity assumption on the potential is used. -/
theorem endpoint_collar_energy_gap {q E δ : ℝ} {η : Γ.EdgeEnd}
    (hgap : δ ≤ |E - V.vertexValue η.vertex|)
    (hclose : |V.extension η.1 q - V.vertexValue η.vertex| < δ / 4) :
    3 * δ / 4 < |E - V.extension η.1 q| := by
  have htriangle : |E - V.vertexValue η.vertex| ≤
      |E - V.extension η.1 q| + |V.extension η.1 q - V.vertexValue η.vertex| :=
    abs_sub_le E (V.extension η.1 q) (V.vertexValue η.vertex)
  nlinarith

/-- For a mechanical state, the endpoint collar gap gives a strictly positive kinetic-energy
lower bound. -/
theorem endpoint_collar_kinetic_lower_bound {e : Γ.Edge} {q p E δ : ℝ} {η : Γ.EdgeEnd}
    (hη : η.1 = e)
    (hgap : δ ≤ |E - V.vertexValue η.vertex|)
    (hclose : |V.extension e q - V.vertexValue η.vertex| < δ / 4)
    (henergy : V.hamiltonian e q p = E) :
    3 * δ / 4 ≤ E - V.extension e q := by
  subst e
  have habs_lower := V.endpoint_collar_energy_gap hgap hclose
  have hnonneg : 0 ≤ E - V.extension η.1 q := by
    unfold hamiltonian at henergy
    nlinarith [sq_nonneg p]
  exact le_of_lt (by simpa [abs_of_nonneg hnonneg] using habs_lower)

/-- In a regular endpoint collar, the momentum of a state with the window energy is nonzero. -/
theorem endpoint_collar_momentum_ne_zero {e : Γ.Edge} {q p E δ : ℝ} {η : Γ.EdgeEnd}
    (hη : η.1 = e) (hδ : 0 < δ)
    (hgap : δ ≤ |E - V.vertexValue η.vertex|)
    (hclose : |V.extension e q - V.vertexValue η.vertex| < δ / 4)
    (henergy : V.hamiltonian e q p = E) : p ≠ 0 := by
  subst e
  intro hp
  have hkin := V.endpoint_collar_kinetic_lower_bound rfl hgap hclose henergy
  unfold hamiltonian at henergy
  rw [hp] at henergy
  norm_num at henergy
  nlinarith

/-- A compact regular energy window has a single potential collar in which it stays uniformly
away from the local potential energy at every endpoint germ. -/
theorem exists_compact_regular_endpoint_collar [Nonempty Γ.Edge] (K : Set ℝ)
    (hKcompact : IsCompact K) (hregular : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ δ r : ℝ, 0 < δ ∧ 0 < r ∧ (∀ e : Γ.Edge, r < Γ.length e / 2) ∧
      ∀ E ∈ K, ∀ η : Γ.EdgeEnd, ∀ q : ℝ,
        |q - FiniteMetricGraph.EdgeEnd.coordinate Γ η| < r →
          3 * δ / 4 < |E - V.extension η.1 q| := by
  obtain ⟨δ, hδ, hgap⟩ := V.exists_compact_regular_energy_gap K hKcompact hregular
  obtain ⟨r, hr, hlength, hclose⟩ :=
    V.exists_uniform_disjoint_endpoint_potential_collar (show 0 < δ / 4 by positivity)
  refine ⟨δ, r, hδ, hr, hlength, ?_⟩
  intro E hE η q hq
  exact V.endpoint_collar_energy_gap (hgap E hE η.vertex) (hclose η q hq)

/-- Compactness of an energy window and the finite lower potential bound give one finite speed
bound for every mechanical state in that window.  We add one to the square-root expression so
the displayed bound is strictly positive even in degenerate empty-window cases. -/
theorem exists_compact_energy_speed_bound (K : Set ℝ) (hKcompact : IsCompact K) :
    ∃ P : ℝ, 0 < P ∧ ∀ e : Γ.Edge, ∀ q p E : ℝ,
      q ∈ Icc (0 : ℝ) (Γ.length e) → E ∈ K → V.hamiltonian e q p = E → |p| ≤ P := by
  obtain ⟨C, hC⟩ := V.exists_uniform_lowerBound_extension_closedEdges
  obtain ⟨U, hU⟩ := hKcompact.bddAbove
  let P : ℝ := Real.sqrt (2 * (U - C)) + 1
  refine ⟨P, by dsimp [P]; positivity, ?_⟩
  intro e q p E hq hE henergy
  have hpotential : C ≤ V.extension e q := hC e q hq
  have henergy_le : V.hamiltonian e q p ≤ U := by
    rw [henergy]
    exact hU hE
  have hspeed := V.abs_momentum_le_sqrt_of_hamiltonian_le hpotential henergy_le
  dsimp [P]
  linarith [Real.sqrt_nonneg (2 * (U - C))]

namespace EdgeFirstHit

/-- The compact-energy speed estimate applies uniformly along every rigorously supplied
first-hit segment.  This is the bridge from conservation of energy to the travel-time estimate. -/
theorem exists_absMomentum_bound_of_compact_energy {e : Γ.Edge} {x : ℝ × ℝ}
    (h : V.EdgeFirstHit e x) (K : Set ℝ) (hKcompact : IsCompact K)
    (henergy : V.hamiltonian e x.1 x.2 ∈ K) :
    ∃ P : ℝ, 0 < P ∧ ∀ t ∈ Icc (0 : ℝ) h.duration, |(h.curve t).2| ≤ P := by
  obtain ⟨P, hPpos, hP⟩ := V.exists_compact_energy_speed_bound K hKcompact
  refine ⟨P, hPpos, ?_⟩
  intro t ht
  apply hP e (h.curve t).1 (h.curve t).2 (V.hamiltonian e x.1 x.2)
  · exact h.physical_at t ht
  · exact henergy
  · exact h.hamiltonian_eq_initial_at t ht

end EdgeFirstHit

/-- An edge flight from the boundary of an endpoint collar to any endpoint takes at least
`r / P`, provided its momentum is bounded by `P`.  This is the geometric-and-ODE core of the
uniform no-Zeno estimate; the scattered-trajectory construction will supply its hypotheses for
successive impacts. -/
theorem edge_flight_time_lower_bound {e : Γ.Edge} {η : Γ.EdgeEnd} {b : Bool}
    {α : ℝ → ℝ × ℝ} {a t r P : ℝ} (hη : η.1 = e)
    (hat : a ≤ t) (hr : 0 < r) (hrlength : r < Γ.length e / 2) (hP : 0 < P)
    (hα : ∀ s ∈ Icc a t, HasDerivWithinAt α (V.edgeVectorField e (α s)) (Icc a t) s)
    (hspeed : ∀ s ∈ Icc a t, |(α s).2| ≤ P)
    (hphysical : ∀ s ∈ Icc a t, (α s).1 ∈ Icc (0 : ℝ) (Γ.length e))
    (hexit : |(α a).1 - FiniteMetricGraph.EdgeEnd.coordinate Γ η| = r)
    (hend : (α t).1 = FiniteMetricGraph.EdgeEnd.coordinate Γ (e, b)) :
    r / P ≤ t - a := by
  subst e
  have hsep : r ≤ |FiniteMetricGraph.EdgeEnd.coordinate Γ (η.1, b) - (α a).1| :=
    Γ.endpoint_coordinate_separation_after_collar hr hrlength
      (hphysical a (left_mem_Icc.mpr hat)) hexit
  have htravel := V.edgeIntegralCurve_coordinate_travel_bound_within hat hα hspeed
  apply time_lower_bound_of_coordinate_separation (P := P) ?_ hP
  calc
    r ≤ |FiniteMetricGraph.EdgeEnd.coordinate Γ (η.1, b) - (α a).1| := hsep
    _ = |(α t).1 - (α a).1| := by rw [hend]
    _ ≤ P * (t - a) := htravel

namespace EdgeFirstHit

/-- A first-hit flight that departs a vertex germ with outgoing momentum, at an energy that
stays uniformly away from the local potential inside a collar of that germ, must physically
leave the collar: at some time its distance from the departure germ equals the collar radius.
This is the geometric no-Zeno core — it rules out an accumulation of impacts inside a collar,
including a spurious immediate reflection back to the same germ, using only conservation of
energy and the collar kinetic-energy gap (no monotonicity of the potential is assumed). -/
theorem exists_collar_radius_time {e : Γ.Edge} {x : ℝ × ℝ} (h : V.EdgeFirstHit e x)
    {η₀ : Γ.EdgeEnd} {r δ : ℝ} (hη₀ : η₀.1 = e) (hr : 0 < r) (hrlen : r < Γ.length e / 2)
    (hstart : x.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ η₀)
    (hout : η₀.sign * x.2 < 0) (hδ : 0 < δ)
    (hcollar : ∀ q : ℝ, |q - FiniteMetricGraph.EdgeEnd.coordinate Γ η₀| < r →
        3 * δ / 4 < |V.hamiltonian e x.1 x.2 - V.extension e q|) :
    ∃ a ∈ Icc (0 : ℝ) h.duration,
      |(h.curve a).1 - FiniteMetricGraph.EdgeEnd.coordinate Γ η₀| = r := by
  classical
  set T := h.duration with hT
  set c₀ := FiniteMetricGraph.EdgeEnd.coordinate Γ η₀ with hc₀
  set E := V.hamiltonian e x.1 x.2 with hEdef
  by_contra hcon
  push_neg at hcon
  -- The flight never reaches collar radius, hence stays strictly inside the collar.
  have hq0 : (h.curve 0).1 = c₀ := by rw [h.initial, hstart]
  have hdcont : ContinuousOn (fun s => |(h.curve s).1 - c₀|) (Icc (0 : ℝ) T) := by
    apply ContinuousOn.abs
    apply ContinuousOn.sub _ continuousOn_const
    exact fun t ht =>
      (V.edgeIntegralCurve_hasDerivWithinAt_fst (h.integralCurve t ht)).continuousWithinAt
  have hlt : ∀ t ∈ Icc (0 : ℝ) T, |(h.curve t).1 - c₀| < r := by
    intro t ht
    rcases lt_trichotomy (|(h.curve t).1 - c₀|) r with hlt | heq | hgt
    · exact hlt
    · exact absurd heq (hcon t ht)
    · exfalso
      have hd0 : |(h.curve 0).1 - c₀| = 0 := by rw [hq0]; simp
      have hmem : r ∈ Icc (|(h.curve 0).1 - c₀|) (|(h.curve t).1 - c₀|) := by
        rw [hd0]; exact ⟨hr.le, hgt.le⟩
      obtain ⟨a, ha, haval⟩ :=
        intermediate_value_Icc ht.1 (hdcont.mono (Icc_subset_Icc le_rfl ht.2)) hmem
      exact hcon a ⟨ha.1, le_trans ha.2 ht.2⟩ haval
  -- Inside the collar, the momentum never vanishes.
  have hpne : ∀ t ∈ Icc (0 : ℝ) T, (h.curve t).2 ≠ 0 := by
    intro t ht hpt
    have hen := h.hamiltonian_eq_initial_at t ht
    have hcol := hcollar (h.curve t).1 (hlt t ht)
    have hval : V.extension e (h.curve t).1 = E := by
      rw [hEdef, ← hen, hpt]; simp [hamiltonian]
    rw [hval] at hcol
    simp at hcol
    linarith
  have hpcont : ContinuousOn (fun s => (h.curve s).2) (Icc (0 : ℝ) T) :=
    fun t ht => (V.edgeIntegralCurve_hasDerivWithinAt_snd (h.integralCurve t ht)).continuousWithinAt
  have hqderiv : ∀ s ∈ interior (Icc (0 : ℝ) T),
      HasDerivWithinAt (fun u => (h.curve u).1) ((h.curve s).2) (interior (Icc (0 : ℝ) T)) s := by
    intro s hs
    rw [interior_Icc] at hs ⊢
    exact ((V.edgeIntegralCurve_hasDerivWithinAt_fst
      (h.integralCurve s (mem_Icc_of_Ioo hs))).hasDerivAt
        (Icc_mem_nhds hs.1 hs.2)).hasDerivWithinAt
  have hqcont : ContinuousOn (fun s => (h.curve s).1) (Icc (0 : ℝ) T) :=
    fun t ht => (V.edgeIntegralCurve_hasDerivWithinAt_fst (h.integralCurve t ht)).continuousWithinAt
  have hTpos : 0 < T := h.duration_pos
  have hp0 : (h.curve 0).2 = x.2 := by rw [h.initial]
  -- Case split on the departure germ, deriving a strict monotonicity contradiction.
  cases hb2 : η₀.2 with
  | false =>
    have hc₀zero : c₀ = 0 := by rw [hc₀]; simp [FiniteMetricGraph.EdgeEnd.coordinate, hb2]
    have hx2pos : 0 < x.2 := by
      have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η₀ = -1 := by
        simp [FiniteMetricGraph.EdgeEnd.sign, hb2]
      rw [hsgn] at hout; linarith
    have hppos : ∀ t ∈ Icc (0 : ℝ) T, 0 < (h.curve t).2 :=
      positive_on_Icc_of_continuousOn_ne_zero hpcont hpne (by rw [hp0]; exact hx2pos)
    have hmono : StrictMonoOn (fun u => (h.curve u).1) (Icc (0 : ℝ) T) :=
      strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hqcont hqderiv
        (fun s hs => by rw [interior_Icc] at hs; exact hppos s (mem_Icc_of_Ioo hs))
    have hqT : (h.curve 0).1 < (h.curve T).1 :=
      hmono (left_mem_Icc.mpr hTpos.le) (right_mem_Icc.mpr hTpos.le) hTpos
    have hqTlt : (h.curve T).1 < r := by
      have := hlt T (right_mem_Icc.mpr hTpos.le)
      rw [hc₀zero] at this
      have hnn : (0 : ℝ) ≤ (h.curve T).1 := (h.physical_at T (right_mem_Icc.mpr hTpos.le)).1
      rw [abs_of_nonneg (by linarith)] at this; linarith
    have hqTend : (h.curve T).1 = FiniteMetricGraph.EdgeEnd.coordinate Γ (e, h.endpoint) :=
      h.hit_endpoint
    -- endpoint coordinate is 0 or length e; both contradict 0 < q(T) < r < length
    cases hb : h.endpoint with
    | false =>
      rw [hb] at hqTend; simp [FiniteMetricGraph.EdgeEnd.coordinate] at hqTend
      rw [hq0, hc₀zero] at hqT; rw [hqTend] at hqT; linarith
    | true =>
      rw [hb] at hqTend; simp [FiniteMetricGraph.EdgeEnd.coordinate] at hqTend
      rw [hqTend] at hqTlt; linarith [hrlen]
  | true =>
    have hc₀len : c₀ = Γ.length e := by
      rw [hc₀]; simp [FiniteMetricGraph.EdgeEnd.coordinate, hb2, hη₀]
    have hx2neg : x.2 < 0 := by
      have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η₀ = 1 := by
        simp [FiniteMetricGraph.EdgeEnd.sign, hb2]
      rw [hsgn] at hout; linarith
    have hpneg : ∀ t ∈ Icc (0 : ℝ) T, (h.curve t).2 < 0 :=
      negative_on_Icc_of_continuousOn_ne_zero hpcont hpne (by rw [hp0]; exact hx2neg)
    have hmono : StrictMonoOn (fun u => -(h.curve u).1) (Icc (0 : ℝ) T) :=
      strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hqcont.neg
        (fun s hs => (hqderiv s hs).neg)
        (fun s hs => by rw [interior_Icc] at hs
                        have := hpneg s (mem_Icc_of_Ioo hs); simpa using by linarith)
    have hqT : -(h.curve 0).1 < -(h.curve T).1 :=
      hmono (left_mem_Icc.mpr hTpos.le) (right_mem_Icc.mpr hTpos.le) hTpos
    have hqTlt : Γ.length e - r < (h.curve T).1 := by
      have := hlt T (right_mem_Icc.mpr hTpos.le)
      rw [hc₀len] at this
      have hle : (h.curve T).1 ≤ Γ.length e := (h.physical_at T (right_mem_Icc.mpr hTpos.le)).2
      rw [abs_of_nonpos (by linarith)] at this; linarith
    have hqTend : (h.curve T).1 = FiniteMetricGraph.EdgeEnd.coordinate Γ (e, h.endpoint) :=
      h.hit_endpoint
    cases hb : h.endpoint with
    | false =>
      rw [hb] at hqTend; simp [FiniteMetricGraph.EdgeEnd.coordinate] at hqTend
      rw [hqTend] at hqTlt; linarith [hrlen]
    | true =>
      rw [hb] at hqTend; simp [FiniteMetricGraph.EdgeEnd.coordinate] at hqTend
      rw [hq0, hc₀len] at hqT; rw [hqTend] at hqT; linarith

/-- The uniform no-Zeno separation constant for outgoing vertex-departing flights.  Over a
compact regular energy window `K`, every first-hit flight that leaves a vertex germ with
outgoing momentum lasts at least a fixed positive time `τ`, uniformly over all edges, all such
flights, and all energies in `K`.  This packages the collar-exit geometry and the compact-window
speed bound into the exact positive gap later assigned to consecutive scattered impact times. -/
theorem exists_uniform_duration_lower_bound_outgoing [Nonempty Γ.Edge] (K : Set ℝ)
    (hKcompact : IsCompact K) (hregular : ∀ E ∈ K, E ∉ V.exceptionalEnergies) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ {e : Γ.Edge} {x : ℝ × ℝ} (h : V.EdgeFirstHit e x),
      V.hamiltonian e x.1 x.2 ∈ K →
      ∀ {η₀ : Γ.EdgeEnd}, η₀.1 = e →
        x.1 = FiniteMetricGraph.EdgeEnd.coordinate Γ η₀ →
        FiniteMetricGraph.EdgeEnd.sign Γ η₀ * x.2 < 0 → τ ≤ h.duration := by
  obtain ⟨δ, r, hδ, hr, hrlen, hcollarK⟩ :=
    V.exists_compact_regular_endpoint_collar K hKcompact hregular
  obtain ⟨P, hP, hspeedK⟩ := V.exists_compact_energy_speed_bound K hKcompact
  refine ⟨r / P, div_pos hr hP, ?_⟩
  intro e x h hEK η₀ hη₀ hstart hout
  have hcollar : ∀ q : ℝ, |q - FiniteMetricGraph.EdgeEnd.coordinate Γ η₀| < r →
      3 * δ / 4 < |V.hamiltonian e x.1 x.2 - V.extension e q| := by
    intro q hq
    have := hcollarK (V.hamiltonian e x.1 x.2) hEK η₀ q hq
    rwa [hη₀] at this
  obtain ⟨a, ha, haval⟩ :=
    exists_collar_radius_time V h hη₀ hr (hrlen e) hstart hout hδ hcollar
  have hspeed : ∀ t ∈ Icc (0 : ℝ) h.duration, |(h.curve t).2| ≤ P := fun t ht =>
    hspeedK e (h.curve t).1 (h.curve t).2 (V.hamiltonian e x.1 x.2)
      (h.physical_at t ht) hEK (h.hamiltonian_eq_initial_at t ht)
  have htravel := V.edgeIntegralCurve_coordinate_travel_bound_within (α := h.curve)
    (a := 0) (b := a) ha.1
    (fun s hs => (h.integralCurve s ⟨hs.1, le_trans hs.2 ha.2⟩).mono
      (Icc_subset_Icc le_rfl ha.2))
    (fun s hs => hspeed s ⟨hs.1, le_trans hs.2 ha.2⟩)
  rw [h.initial, hstart, haval] at htravel
  have hle : r / P ≤ a := time_lower_bound_of_coordinate_separation (by linarith) hP
  exact le_trans hle ha.2

/-- Once an edge segment has left the collar of the vertex from which it departed, a compact
energy window forces a positive lower bound on the time to its next endpoint.  This is the
trajectory-level form of the quantitative core of Lemma V.2; the later concatenation supplies
the collar-exit witness after each scattering event. -/
theorem exists_duration_lower_bound_after_collar_exit {e : Γ.Edge} {x : ℝ × ℝ}
    (h : V.EdgeFirstHit e x) (K : Set ℝ) (hKcompact : IsCompact K)
    (henergy : V.hamiltonian e x.1 x.2 ∈ K) {η : Γ.EdgeEnd}
    {r : ℝ} (hη : η.1 = e) (hr : 0 < r) (hrlength : r < Γ.length e / 2)
    (hexit : |(h.curve 0).1 - FiniteMetricGraph.EdgeEnd.coordinate Γ η| = r) :
    ∃ P : ℝ, 0 < P ∧ r / P ≤ h.duration := by
  obtain ⟨P, hPpos, hspeed⟩ :=
    exists_absMomentum_bound_of_compact_energy V h K hKcompact henergy
  refine ⟨P, hPpos, ?_⟩
  simpa using V.edge_flight_time_lower_bound hη h.duration_pos.le hr hrlength hPpos
    h.integralCurve hspeed h.physical_at hexit h.hit_endpoint

/-- The collar-exit bound can be chosen once for every compact energy window, uniformly over
all edges and all first-hit segments in that window.  This is the exact positive separation
constant later assigned to consecutive impact times. -/
theorem exists_uniform_duration_lower_bound_after_collar_exit (K : Set ℝ)
    (hKcompact : IsCompact K) {r : ℝ} (hr : 0 < r)
    (hrlength : ∀ e : Γ.Edge, r < Γ.length e / 2) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ {e : Γ.Edge} {x : ℝ × ℝ}
      (h : V.EdgeFirstHit e x), V.hamiltonian e x.1 x.2 ∈ K →
      ∀ {η : Γ.EdgeEnd}, η.1 = e →
      |(h.curve 0).1 - FiniteMetricGraph.EdgeEnd.coordinate Γ η| = r → τ ≤ h.duration := by
  obtain ⟨P, hPpos, hP⟩ := V.exists_compact_energy_speed_bound K hKcompact
  refine ⟨r / P, div_pos hr hPpos, ?_⟩
  intro e x h henergy η hη hexit
  have hspeed : ∀ t ∈ Icc (0 : ℝ) h.duration, |(h.curve t).2| ≤ P := by
    intro t ht
    apply hP e (h.curve t).1 (h.curve t).2 (V.hamiltonian e x.1 x.2)
    · exact h.physical_at t ht
    · exact henergy
    · exact h.hamiltonian_eq_initial_at t ht
  simpa using V.edge_flight_time_lower_bound hη h.duration_pos.le hr (hrlength e) hPpos
    h.integralCurve hspeed h.physical_at hexit h.hit_endpoint

end EdgeFirstHit

end MechanicalPotential
end HamiltonianMetricGraphs
