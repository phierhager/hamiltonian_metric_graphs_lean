/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition VII.1: the branch section of a regular energy surface
-/

import HamiltonianMetricGraphs.ShellErgodic
import HamiltonianMetricGraphs.ShellRegularity
import HamiltonianMetricGraphs.EnergySurfaceExactCurve
import HamiltonianMetricGraphs.EnergySurfaceExactSuspension

/-!
# The branch section of a regular energy surface (Proposition VII.1)

Fix an energy `E` as in Proposition VII.1: `E` is not a vertex value and is a regular value of
`V_e : (0, ℓ_e) → ℝ` on every edge (`NoInteriorCriticalValue`).  No shell-regularity is assumed:
a flight may be trapped in a potential well inside an edge.

The **branch section** `branchSection E ⊆ Σ_E` consists of the states of energy `E` whose
outgoing representative is not on an open branch: the interior turning points `(q, 0)` and the
boundary classes.  It is exactly the complement in `Σ_E` of the parametrized open branches of
Proposition VII.1.  We prove:

* `finite_branchSection`: the section is finite (at a regular value the turning points of an edge
  are isolated, hence finitely many, and there are finitely many boundary covectors of energy `E`);
* `exists_isBranchPiece`: from each point `z` of the section the flow runs along one open
  branch `{(q, ε √(2(E - V_e(q)))) : q ∈ J}` of an edge, `J` the open interval between the
  position `α` of `z` and a far end `β`, reaching `q ∈ J` at the time
  `sheetTime α ε q = ε ∫_α^q dr / √(2(E - V_e(r)))`, and it is back in the section after the
  finite time `τ = sheetTime α ε β`.  This is `exists_sheetTraverse` applied to the flight
  of the representative of `z`.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### Integrability of the time density -/

theorem extension_endpoint_ne {E : ℝ} (hE : E ∉ V.exceptionalEnergies) (e : Γ.Edge) (b : Bool) :
    V.extension e (FiniteMetricGraph.EdgeEnd.coordinate Γ (e, b)) ≠ E := by
  intro h
  apply hE
  rw [V.mem_exceptionalEnergies_iff]
  exact ⟨FiniteMetricGraph.EdgeEnd.vertex Γ (e, b), by rw [← V.endpoint_compatible (e, b), h]⟩

theorem extension_zero_ne {E : ℝ} (hE : E ∉ V.exceptionalEnergies) (e : Γ.Edge) :
    V.extension e 0 ≠ E := by
  simpa using V.extension_endpoint_ne hE e false

theorem extension_length_ne {E : ℝ} (hE : E ∉ V.exceptionalEnergies) (e : Γ.Edge) :
    V.extension e (Γ.length e) ≠ E := by
  simpa using V.extension_endpoint_ne hE e true

/-- At a regular energy every turning point of a closed edge is simple. -/
theorem simple_of_noInteriorCriticalValue {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) (e : Γ.Edge) :
    ∀ q ∈ Icc (0 : ℝ) (Γ.length e), V.extension e q = E → deriv (V.extension e) q ≠ 0 := by
  intro q hq hqE
  rcases eq_or_lt_of_le hq.1 with h0 | h0
  · exact absurd (h0 ▸ hqE) (V.extension_zero_ne hE e)
  rcases eq_or_lt_of_le hq.2 with hl | hl
  · exact absurd (hl ▸ hqE) (V.extension_length_ne hE e)
  exact hreg e q ⟨h0, hl⟩ hqE

/-- At a regular energy the reciprocal speed is integrable over each closed edge. -/
theorem intervalIntegrable_one_div_speedAt_edge {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) (e : Γ.Edge) :
    IntervalIntegrable (fun r => 1 / V.speedAt e E r) volume 0 (Γ.length e) := by
  have hle : (0 : ℝ) ≤ Γ.length e := (Γ.length_pos e).le
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
  have hfin := V.lintegral_timeDensity_edge_lt_top e (V.simple_of_noInteriorCriticalValue hE hreg e)
  have hmeas : AEMeasurable (fun r => 1 / V.speedAt e E r)
      (volume.restrict (Icc 0 (Γ.length e))) :=
    ((V.continuousOn_speedAt e E).aemeasurable measurableSet_Icc).const_div 1
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun r => by
    simp only [Pi.zero_apply]; exact one_div_nonneg.mpr (V.speedAt_nonneg e E r))]
  exact hfin

/-! ### The branch section -/

variable (S : BorelEnergyPreservingScattering V)

/-- The sign `±1` attached to a Boolean. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem boolSign_true : boolSign true = 1 := rfl
@[simp] theorem boolSign_false : boolSign false = -1 := rfl

theorem boolSign_cases (b : Bool) : boolSign b = 1 ∨ boolSign b = -1 := by
  cases b <;> simp

/-- The edge of the outgoing representative. -/
noncomputable def repEdge (z : RegularScatteringPhaseSpace (V := V) S) : Γ.Edge :=
  (rep V S z.1).1.1

/-- The position of the outgoing representative. -/
noncomputable def repPos (z : RegularScatteringPhaseSpace (V := V) S) : ℝ :=
  (rep V S z.1).1.2.1.1

/-- The momentum of the outgoing representative. -/
noncomputable def repMom (z : RegularScatteringPhaseSpace (V := V) S) : ℝ :=
  (rep V S z.1).1.2.1.2

/-- **The branch section**: states of energy `E` whose outgoing representative is a boundary
covector or an interior turning point, i.e. which are not on an open branch. -/
def branchSection (E : ℝ) : Set (RegularScatteringPhaseSpace (V := V) S) :=
  {z | quotientHamiltonian (V := V) S z.1 = E ∧
    (V.repPos S z ∉ Ioo 0 (Γ.length (V.repEdge S z)) ∨ V.repMom S z = 0)}

/-- The direction of the branch departing a point of the section: the sign of the momentum at a
boundary covector, the sign of the force at a turning point. -/
noncomputable def sectionDir (z : RegularScatteringPhaseSpace (V := V) S) : Bool :=
  if V.repMom S z ≠ 0 then decide (0 < V.repMom S z)
  else decide (0 < V.force (V.repEdge S z) (V.repPos S z))

theorem repPos_mem (z : RegularScatteringPhaseSpace (V := V) S) :
    V.repPos S z ∈ Icc 0 (Γ.length (V.repEdge S z)) := (rep V S z.1).1.2.2

theorem hamiltonian_rep (z : RegularScatteringPhaseSpace (V := V) S) :
    V.hamiltonian (V.repEdge S z) (V.repPos S z) (V.repMom S z) =
      quotientHamiltonian (V := V) S z.1 := by
  rw [← quotientMap_rep V S z.1, quotientHamiltonian_mk]
  rfl

theorem graphClass_rep (z : RegularScatteringPhaseSpace (V := V) S) :
    graphClass V S (V.repEdge S z, V.repPos S z, V.repMom S z) = z.1 := by
  have := graphClass_repFlight V S z
  exact this

theorem repEdge_eq_of_graphClass {z : RegularScatteringPhaseSpace (V := V) S}
    {y : Γ.Edge × ℝ × ℝ} (hy : Γ.AdmissiblePoint y)
    (hnin : ¬ IsIncomingPoint (V := V) S (Γ.graphPoint y)) (hz : graphClass V S y = z.1) :
    V.repEdge S z = y.1 ∧ V.repPos S z = y.2.1 ∧ V.repMom S z = y.2.2 := by
  have hrep : rep V S z.1 = Γ.graphPoint y := by
    rw [← hz, graphClass, rep_quotientMap_of_not_incoming V S _ hnin]
  refine ⟨?_, ?_, ?_⟩
  · rw [repEdge, hrep, Γ.graphPoint_edge hy]
  · rw [repPos, hrep, Γ.graphPoint_state hy]
  · rw [repMom, hrep, Γ.graphPoint_state hy]

/-- The representative of the class of an interior point is that point. -/
theorem rep_graphClass_interior {z : RegularScatteringPhaseSpace (V := V) S} {e : Γ.Edge}
    {q p : ℝ} (hq : q ∈ Ioo 0 (Γ.length e)) (hz : graphClass V S (e, q, p) = z.1) :
    V.repEdge S z = e ∧ V.repPos S z = q ∧ V.repMom S z = p := by
  have hy : Γ.AdmissiblePoint (e, q, p) := ⟨Ioo_subset_Icc_self hq, Or.inl hq⟩
  refine V.repEdge_eq_of_graphClass S hy ?_ hz
  rw [isIncomingPoint_graphPoint_iff V S hy]
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · have h' : q = 0 := h
    rw [h'] at hq; exact lt_irrefl _ hq.1
  · have h' : q = Γ.length e := h
    rw [h'] at hq; exact lt_irrefl _ hq.2

/-- A class on an open branch (interior position, nonzero momentum) is not in the section. -/
theorem not_mem_branchSection_of_interior {E : ℝ} {z : RegularScatteringPhaseSpace (V := V) S}
    {e : Γ.Edge} {q p : ℝ} (hq : q ∈ Ioo 0 (Γ.length e)) (hp : p ≠ 0)
    (hz : graphClass V S (e, q, p) = z.1) : z ∉ V.branchSection S E := by
  obtain ⟨he, hpos, hmom⟩ := V.rep_graphClass_interior S hq hz
  rintro ⟨-, h | h⟩
  · rw [hpos, he] at h; exact h hq
  · rw [hmom] at h; exact hp h

/-! ### Finiteness of the section -/

/-- At a regular energy the turning points of a closed edge are isolated, hence finitely many. -/
theorem finite_turningPoints {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) (e : Γ.Edge) :
    {q | q ∈ Icc (0 : ℝ) (Γ.length e) ∧ V.extension e q = E}.Finite := by
  have hcl : IsClosed (Icc (0 : ℝ) (Γ.length e) ∩ V.extension e ⁻¹' {E}) :=
    (V.extension_continuousOn_closedEdge e).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_singleton
  have hcomp : IsCompact {q | q ∈ Icc (0 : ℝ) (Γ.length e) ∧ V.extension e q = E} :=
    isCompact_Icc.of_isClosed_subset hcl inter_subset_left
  refine hcomp.finite (isDiscrete_iff_nhdsNE.mpr fun q hq => ?_)
  rw [inf_principal_eq_bot]
  have hd : HasDerivAt (V.extension e) (deriv (V.extension e) q) q :=
    ((V.extension_contDiffAt_of_mem (V.closedEdge_subset_domain e hq.1)).differentiableAt
      (by norm_num)).hasDerivAt
  filter_upwards [hd.eventually_ne (c := E)
    (V.simple_of_noInteriorCriticalValue hE hreg e q hq.1 hq.2)] with r hr hmem
  exact hr hmem.2

/-- **The branch section is finite.** -/
theorem finite_branchSection {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) : (V.branchSection S E).Finite := by
  classical
  set P : Γ.Edge → Set ℝ := fun e =>
    ({0, Γ.length e} : Set ℝ) ∪ {q | q ∈ Icc (0 : ℝ) (Γ.length e) ∧ V.extension e q = E} with hP
  have hPfin : ∀ e, (P e).Finite := fun e =>
    ((Set.finite_singleton _).insert _).union (V.finite_turningPoints hE hreg e)
  set F : Set (Γ.Edge × ℝ × ℝ) := ⋃ e, ({e} : Set Γ.Edge) ×ˢ (P e ×ˢ
    ((fun q => V.speedAt e E q) '' P e ∪ (fun q => -V.speedAt e E q) '' P e)) with hF
  have hFfin : F.Finite := Set.finite_iUnion fun e =>
    (Set.finite_singleton e).prod ((hPfin e).prod (((hPfin e).image _).union ((hPfin e).image _)))
  set f : RegularScatteringPhaseSpace (V := V) S → Γ.Edge × ℝ × ℝ :=
    fun z => (V.repEdge S z, V.repPos S z, V.repMom S z) with hf
  have hinj : Function.Injective f := by
    intro z z' h
    apply Subtype.ext
    rw [← V.graphClass_rep S z, ← V.graphClass_rep S z']
    exact congrArg (graphClass V S) h
  refine (hFfin.preimage hinj.injOn).subset ?_
  intro z hz
  obtain ⟨hzE, hzs⟩ := hz
  have hH := (V.hamiltonian_rep S z).trans hzE
  have hq := V.repPos_mem S z
  have hpos : V.repPos S z ∈ P (V.repEdge S z) := by
    rcases hzs with h | h
    · left
      rcases eq_or_lt_of_le hq.1 with h0 | h0
      · exact Or.inl h0.symm
      rcases eq_or_lt_of_le hq.2 with hl | hl
      · exact Or.inr hl
      · exact absurd ⟨h0, hl⟩ h
    · right
      refine ⟨hq, ?_⟩
      rw [hamiltonian, h] at hH
      linarith
  have hsp := V.speedAt_eq_abs_of_hamiltonian hH
  refine mem_iUnion.mpr ⟨V.repEdge S z, rfl, hpos, ?_⟩
  rcases le_total 0 (V.repMom S z) with h | h
  · left; exact ⟨V.repPos S z, hpos, by simp only [hf]; rw [hsp, abs_of_nonneg h]⟩
  · right; exact ⟨V.repPos S z, hpos, by simp only [hf]; rw [hsp, abs_of_nonpos h, neg_neg]⟩

/-! ### The flight of a point of the section -/

section Flight

variable [Nonempty Γ.Edge]

/-- Before its first impact the trajectory of a flight state is its flight curve. -/
theorem trajectory_eq_flightCurve_of_lt (a : V.FlightState) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : ∀ _ : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      u < sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    FlightState.trajectory V S a u = (a.edge, FlightState.flightCurve V a u) := by
  have hact : FlightState.ActiveAt V S a 0 u := by
    refine ⟨by rw [FlightState.iterate_zero]; rfl, by rw [FlightState.impactReal_zero]; exact hu0,
      fun hsucc => ?_⟩
    rw [FlightState.impactReal_succ_eq_of_isSome (V := V) (FlightState.iterate_zero V S _) hsucc,
      FlightState.impactReal_zero, zero_add]
    have hb : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state) := by
      by_contra hnb
      have hnone := (FlightState.next_eq_none_iff (V := V) S a).mpr hnb
      rw [FlightState.iterate_succ, FlightState.iterate_zero] at hsucc
      simp [hnone] at hsucc
    exact hu hb
  rw [FlightState.trajectory_eq V S a hu0 hact (FlightState.iterate_zero V S _),
    FlightState.impactReal_zero, sub_zero]

omit [Nonempty Γ.Edge] in
/-- The analytic properties of a flight curve on `[0, D]`, `D` its impact time if it has one. -/
theorem flightCurve_facts (a : V.FlightState) {D : ℝ}
    (hDb : ∀ _ : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      D = sSup (PhysicalEdgeSegment.durationSet V a.edge a.state)) :
    ContinuousOn (FlightState.flightCurve V a) (Icc 0 D) ∧
    HasDerivWithinAt (FlightState.flightCurve V a)
      (V.edgeVectorField a.edge (FlightState.flightCurve V a 0)) (Ici 0) 0 ∧
    (∀ u ∈ Ioo 0 D, HasDerivAt (FlightState.flightCurve V a)
      (V.edgeVectorField a.edge (FlightState.flightCurve V a u)) u) ∧
    (∀ u ∈ Icc 0 D, V.hamiltonian a.edge (FlightState.flightCurve V a u).1
      (FlightState.flightCurve V a u).2 = a.energy) ∧
    (∀ u ∈ Icc 0 D, (FlightState.flightCurve V a u).1 ∈ Icc 0 (Γ.length a.edge)) ∧
    (∀ u ∈ Ioo 0 D, (FlightState.flightCurve V a u).1 ∈ Ioo 0 (Γ.length a.edge)) := by
  classical
  set c := FlightState.flightCurve V a with hc
  have hder0 : HasDerivWithinAt c (V.edgeVectorField a.edge (c 0)) (Ici 0) 0 := by
    have hseg := a.segment.integralCurve 0 ⟨le_rfl, a.segment.duration_pos.le⟩
    have h0 : c 0 = a.segment.curve 0 := by
      rw [hc, FlightState.flightCurve_zero, a.segment.initial]
    rw [h0]
    refine hseg.hasDerivWithinAt.congr_of_eventuallyEq ?_ h0
    filter_upwards [Ico_mem_nhdsGE a.segment.duration_pos] with t ht
    exact FlightState.flightCurve_eq_segment_curve V a ht.1 ht.2
  have hder : ∀ u ∈ Ioo 0 D, HasDerivAt c (V.edgeVectorField a.edge (c u)) u := fun u hu =>
    FlightState.flightCurve_hasDerivAt V a hu.1 (fun hb => by rw [← hDb hb]; exact hu.2)
  refine ⟨?_, hder0, hder, ?_, ?_, ?_⟩
  · by_cases hb : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)
    · have heq : c = a.segment.maximalCurveClosed hb := by
        rw [hc]; unfold FlightState.flightCurve; rw [dif_pos hb]
      intro t ht
      rw [heq]
      rw [hDb hb] at ht ⊢
      exact (a.segment.maximalCurveClosed_hasDerivWithinAt_Icc hb ht).continuousWithinAt
    · intro t ht
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · rw [← h0]
        exact hder0.continuousWithinAt.mono Icc_subset_Ici_self
      · exact (FlightState.flightCurve_hasDerivAt V a h0
          (fun hb' => absurd hb' hb)).continuousAt.continuousWithinAt
  · exact fun u hu => FlightState.flightCurve_hamiltonian_eq V a hu.1
      (fun hb => by rw [← hDb hb]; exact hu.2)
  · exact fun u hu => FlightState.flightCurve_physical V a hu.1
      (fun hb => by rw [← hDb hb]; exact hu.2)
  · exact fun u hu => FlightState.flightCurve_interior V a hu.1
      (fun hb => by rw [← hDb hb]; exact hu.2)

/-- **From a point of the section the flow runs along one open branch.**  For `z` in the branch
section, with `α`, `ε` its position and branch direction, there are a far end `β` and a time
`τ > 0` such that the flow reaches each `q` strictly between `α` and `β` at the time
`sheetTime α ε q ∈ (0, τ)`, at the point `π(e, q, ε √(2(E - V_e(q))))` of the open branch over the
allowed region, every time in `(0, τ)` is such a time, and `Φ_τ z` is again in the section. -/
theorem exists_isBranchPiece {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) {z : RegularScatteringPhaseSpace (V := V) S}
    (hz : z ∈ V.branchSection S E) :
    ∃ β τ : ℝ, 0 < τ ∧ flow V S z τ ∈ V.branchSection S E ∧
      β ∈ Icc 0 (Γ.length (V.repEdge S z)) ∧
      0 < boolSign (V.sectionDir S z) * (β - V.repPos S z) ∧
      (β ∉ Ioo 0 (Γ.length (V.repEdge S z)) ∨ V.extension (V.repEdge S z) β = E) ∧
      uIoo (V.repPos S z) β ⊆ Ioo 0 (Γ.length (V.repEdge S z)) ∧
      (∀ u ∈ Ioo 0 τ, ∃ q ∈ uIoo (V.repPos S z) β,
        V.sheetTime (V.repEdge S z) E (V.repPos S z) (boolSign (V.sectionDir S z)) q = u) ∧
      (∀ q ∈ uIoo (V.repPos S z) β,
        V.sheetTime (V.repEdge S z) E (V.repPos S z) (boolSign (V.sectionDir S z)) q ∈
          Ioo 0 τ ∧ q ∈ V.allowedPositions (V.repEdge S z) E ∧
        (flow V S z
          (V.sheetTime (V.repEdge S z) E (V.repPos S z) (boolSign (V.sectionDir S z)) q)).1 =
          graphClass V S (V.repEdge S z, q,
            boolSign (V.sectionDir S z) * V.speedAt (V.repEdge S z) E q)) := by
  classical
  set e := V.repEdge S z with he
  set α := V.repPos S z with hα
  set p := V.repMom S z with hp
  set ε := boolSign (V.sectionDir S z) with hεdef
  set a := repFlight V S z with ha
  set c := FlightState.flightCurve V a with hc
  have hzE : quotientHamiltonian (V := V) S z.1 = E := hz.1
  have hH : V.hamiltonian e α p = E := (V.hamiltonian_rep S z).trans hzE
  have hε : ε = 1 ∨ ε = -1 := boolSign_cases _
  have haE : a.energy = E := by rw [ha, repFlight_energy]; exact hzE
  have hαI : α ∈ Icc 0 (Γ.length e) := V.repPos_mem S z
  have hsα : V.speedAt e E α = |p| := V.speedAt_eq_abs_of_hamiltonian hH
  -- the start of the branch
  have hp_eq : p = ε * V.speedAt e E α := by
    rw [hsα, hεdef, sectionDir]
    by_cases hp0 : p = 0
    · rw [hp0]; simp
    · rw [if_pos (show V.repMom S z ≠ 0 from hp0)]
      rcases lt_or_gt_of_ne hp0 with hneg | hpos
      · have : ¬ (0 < V.repMom S z) := not_lt.mpr hneg.le
        simp only [this, decide_false, boolSign_false]
        rw [abs_of_neg hneg]; ring
      · have : 0 < V.repMom S z := hpos
        simp only [this, decide_true, boolSign_true]
        rw [abs_of_pos hpos]; ring
  have hstart : (V.extension e α = E ∧ 0 < ε * V.force e α) ∨ V.extension e α < E := by
    by_cases hp0 : p = 0
    · left
      have hVα : V.extension e α = E := by
        rw [hamiltonian, hp0] at hH; linarith
      refine ⟨hVα, ?_⟩
      have hαint : α ∈ Ioo 0 (Γ.length e) := by
        rcases (rep V S z.1).2 with h | h
        · exact h
        · exact absurd hp0 h
      have hF : V.force e α ≠ 0 := by
        rw [force, neg_ne_zero]; exact hreg e α hαint hVα
      rw [hεdef, sectionDir, if_neg (show ¬ V.repMom S z ≠ 0 from not_not.mpr hp0)]
      rcases lt_or_gt_of_ne hF with hneg | hpos
      · have : ¬ (0 < V.force (V.repEdge S z) (V.repPos S z)) := not_lt.mpr hneg.le
        simp only [this, decide_false, boolSign_false]
        linarith
      · have : 0 < V.force (V.repEdge S z) (V.repPos S z) := hpos
        simp only [this, decide_true, boolSign_true]
        linarith
    · right
      have : 0 < p ^ 2 := by positivity
      rw [hamiltonian] at hH; linarith
  have hint := V.intervalIntegrable_one_div_speedAt_edge hE hreg e
  -- the time interval of the flight curve
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    (V.continuousOn_sheetTime e (ε := ε) hint hαI)
  set D : ℝ := if hb : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state) then
    sSup (PhysicalEdgeSegment.durationSet V a.edge a.state) else max (M + 1) 1 with hDdef
  have hDb : ∀ hb : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state),
      D = sSup (PhysicalEdgeSegment.durationSet V a.edge a.state) := fun hb => by
    rw [hDdef, dif_pos hb]
  have hD : 0 < D := by
    by_cases hb : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)
    · rw [hDb hb]; exact FlightState.impactDuration_pos_of_bddAbove (V := V) a hb
    · rw [hDdef, dif_neg hb]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨hcont, hder0, hder, henergy, hphys, hinter⟩ := V.flightCurve_facts a hDb
  have hae : a.edge = e := rfl
  have has : a.state = (α, p) := rfl
  have hc0 : c 0 = (α, ε * V.speedAt e E α) := by
    rw [hc, FlightState.flightCurve_zero, has, ← hp_eq]
  have hend : (c D).1 ∉ Ioo 0 (Γ.length e) ∨
      ∀ q ∈ Icc 0 (Γ.length e), V.sheetTime e E α ε q < D := by
    by_cases hb : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state)
    · left
      rw [hDb hb, hc, FlightState.flightCurve_sSup]
      exact a.segment.maximalEndpoint_not_interior hb
    · right
      intro q hq
      have h1 : V.sheetTime e E α ε q ≤ M := hM ⟨q, hq, rfl⟩
      rw [hDdef, dif_neg hb]
      exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  obtain ⟨β, τ, hτ, hτD, hβI, hdir, hTβ, hcτ, hcases, hbranch, hsurj⟩ :=
    V.exists_sheetTraverse e hε hαI hstart hc0 hD hcont hder0 hder
      (fun u hu => (henergy u hu).trans haE) hphys hinter hint hend
  -- the flow along the trajectory
  have ha_ni : a.NotIncoming := repFlight_notIncoming V S z
  have hz0 : V.trajClass S a 0 = z := by
    apply Subtype.ext
    rw [trajClass_val, FlightState.trajectory_zero]
    exact graphClass_repFlight V S z
  have hflow : ∀ u, 0 ≤ u → flow V S z u = V.trajClass S a u := fun u hu => by
    rw [← V.flow_trajClass_zero S ha_ni hu, hz0]
  have htraj : ∀ u, 0 ≤ u → u < D → FlightState.trajectory V S a u = (e, c u) := fun u hu0 hu =>
    V.trajectory_eq_flightCurve_of_lt S a hu0 (fun hb => by rw [← hDb hb]; exact hu)
  have hsub : uIoo α β ⊆ Ioo 0 (Γ.length e) := uIoo_subset_Ioo hαI hβI
  refine ⟨β, τ, hτ, ?_, hβI, hdir, ?_, hsub, ?_, ?_⟩
  · -- `Φ_τ z` is back in the section
    refine ⟨by rw [quotientHamiltonian_flow]; exact hzE, ?_⟩
    have hrep := V.rep_trajClass S ha_ni τ
    have hadm := FlightState.trajectory_admissible S a τ
    have hpos' : V.repPos S (flow V S z τ) = (FlightState.trajectory V S a τ).2.1 := by
      rw [repPos, hflow τ hτ.le, hrep, Γ.graphPoint_state hadm]
    have hmom' : V.repMom S (flow V S z τ) = (FlightState.trajectory V S a τ).2.2 := by
      rw [repMom, hflow τ hτ.le, hrep, Γ.graphPoint_state hadm]
    have hedge' : V.repEdge S (flow V S z τ) = (FlightState.trajectory V S a τ).1 := by
      rw [repEdge, hflow τ hτ.le, hrep, Γ.graphPoint_edge hadm]
    rw [hpos', hmom', hedge']
    rcases hcases with ⟨hβint, hVβ, hτlt⟩ | ⟨hβnot, hτeq⟩
    · right
      rw [htraj τ hτ.le hτlt, hcτ]
      have : V.speedAt e E β = 0 := by
        unfold speedAt; rw [hVβ, sub_self, mul_zero, Real.sqrt_zero]
      simp [this]
    · left
      have hb : BddAbove (PhysicalEdgeSegment.durationSet V a.edge a.state) := by
        by_contra hnb
        have h1 : V.sheetTime e E α ε β ≤ M := hM ⟨β, hβI, rfl⟩
        have h2 : D = max (M + 1) 1 := by rw [hDdef, dif_neg hnb]
        have h3 : M + 1 ≤ D := h2 ▸ le_max_left _ _
        linarith
      obtain ⟨b, hnext⟩ := Option.ne_none_iff_exists'.mp
        (fun h => ((FlightState.next_eq_none_iff (V := V) S a).mp h) hb)
      have hiter : FlightState.iterate V S a (0 + 1) = some b := by
        rw [FlightState.iterate_succ, FlightState.iterate_zero]; exact hnext
      have himp : FlightState.impactReal V S a (0 + 1) = τ := by
        rw [FlightState.impactReal_succ_eq_of_isSome (V := V) (FlightState.iterate_zero V S _)
          (by rw [hiter]; rfl), FlightState.impactReal_zero, zero_add, ← hDb hb, hτeq]
      have hat := FlightState.trajectory_at_impact V S a 0 hiter
      rw [himp] at hat
      rw [hat]
      obtain ⟨η₀, hη₀, hstate, -⟩ := FlightState.next_isOutgoing (V := V) S hnext
      simp only
      rw [hstate, ← hη₀]
      exact edgeEnd_coordinate_notMem_Ioo η₀
  · rcases hcases with ⟨-, hVβ, -⟩ | ⟨hβnot, -⟩
    · exact Or.inr hVβ
    · exact Or.inl hβnot
  · intro u hu
    obtain ⟨hq, -, -, hT⟩ := hbranch u hu
    exact ⟨(c u).1, hq, hT⟩
  · intro q hq
    obtain ⟨u, hu, hcu⟩ := hsurj q hq
    obtain ⟨-, hVq, hpq, hT⟩ := hbranch u hu
    rw [hcu] at hVq hpq hT
    have huD : u < D := lt_of_lt_of_le hu.2 hτD
    refine ⟨by rw [hT]; exact hu, ⟨hsub hq, hVq⟩, ?_⟩
    rw [hT, hflow u hu.1.le, trajClass_val, htraj u hu.1.le huD]
    congr 1
    refine Prod.ext rfl (Prod.ext hcu ?_)
    exact hpq

end Flight

end MechanicalPotential

end HamiltonianMetricGraphs
