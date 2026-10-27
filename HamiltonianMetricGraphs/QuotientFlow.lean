/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition V.5 (existence): the scattered evolution `Φₜ` on the regular quotient phase space.
-/

import HamiltonianMetricGraphs.FlightRetrace
import HamiltonianMetricGraphs.ScatterMap

/-!
# The scattered evolution on the regular quotient phase space

This module builds the paper's global flow `Φₜ : P^Reg_S → P^Reg_S` for every real time `t`
(Proposition V.5, existence part), and proves that it starts at the identity, conserves the
quotient Hamiltonian, and satisfies the forward semigroup law.  The inverse identities and the
full group law are in `FlowGroup`.

**Forward time.**  A regular quotient point `z` has an *outgoing representative*
`rep S z ∈ P̃⁺` (Lemma IV.4, `outgoingChart`): an interior point or an outgoing boundary covector,
with regular energy.  Such a point starts a `FlightState` (`repFlight`), and the unified forward
trajectory `FlightState.trajectory` of that flight state, read in the quotient, is `Φₜ z` for
`t ≥ 0`.  The value never sits at an incoming boundary point (`trajectory_notIncoming`), so the
quotient point at time `s` has the trajectory's own point as outgoing representative; this is what
turns the flight-state semigroup `trajectory_semigroup` into the quotient semigroup
`Φ_{s+t} = Φ_t ∘ Φ_s`.

**Backward time.**  For `t < 0` the paper uses the incoming representative and the inverse laws
`S⁻¹`.  Here this is packaged as conjugation by the reversal map `ρ : Q(S) → Q(T)`, `[x] ↦ [R x]`,
which is well defined for every *time reversal* `T` of `S` (`IsTimeReversal`): a scattering step
`α ↦ S α` of `S` becomes the step `R (S α) ↦ R α = T (R (S α))` of `T`.  Then
`Φₜ z := ρ⁻¹ (Φ⁺_{-t, T} (ρ z))` with `T = timeReversed S`.  Since `ρ` sends the class of an
outgoing point to the class of an incoming one, the outgoing representative of `ρ z` is the
`T`-scattered image of the reversed point — exactly the paper's "incoming chart with `S⁻¹`".
-/

namespace HamiltonianMetricGraphs

open Set Filter Topology

/-! ### Graph phase points -/

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-- A graph phase point `(e, q, p)` is *admissible* when it is physical (`0 ≤ q ≤ ℓₑ`) and is not
a zero-momentum vertex state: exactly the points of the paper's `P̃×`. -/
def AdmissiblePoint (y : Γ.Edge × ℝ × ℝ) : Prop :=
  y.2.1 ∈ Icc (0 : ℝ) (Γ.length y.1) ∧ (y.2.1 ∈ Ioo (0 : ℝ) (Γ.length y.1) ∨ y.2.2 ≠ 0)

/-- Momentum reversal of a graph phase point. -/
def reversePoint (y : Γ.Edge × ℝ × ℝ) : Γ.Edge × ℝ × ℝ := (y.1, y.2.1, -y.2.2)

@[simp] theorem reversePoint_reversePoint (y : Γ.Edge × ℝ × ℝ) :
    Γ.reversePoint (Γ.reversePoint y) = y := by
  rcases y with ⟨e, q, p⟩
  simp [reversePoint]

theorem admissiblePoint_reversePoint_iff (y : Γ.Edge × ℝ × ℝ) :
    Γ.AdmissiblePoint (Γ.reversePoint y) ↔ Γ.AdmissiblePoint y := by
  rcases y with ⟨e, q, p⟩
  simp [AdmissiblePoint, reversePoint]

/-- Extensionality for prequotient points: same edge and same phase pair. -/
theorem prequotient_ext {x y : Γ.PrequotientPhase} (h1 : x.1 = y.1) (h2 : x.2.1 = y.2.1) :
    x = y := by
  rcases x with ⟨e, ⟨p, hp⟩⟩
  rcases y with ⟨e', ⟨p', hp'⟩⟩
  change e = e' at h1
  change p = p' at h2
  subst h1
  subst h2
  rfl

/-- A graph phase point as a point of the nonzero prequotient space.  An inadmissible point is sent
to the junk value "midpoint of its edge at rest", which is never used. -/
noncomputable def graphPoint (y : Γ.Edge × ℝ × ℝ) : Γ.NonzeroPrequotientPhase := by
  classical
  exact if h : Γ.AdmissiblePoint y then ⟨⟨y.1, ⟨y.2, h.1⟩⟩, h.2⟩
  else ⟨⟨y.1, ⟨(Γ.length y.1 / 2, 0),
      ⟨(half_pos (Γ.length_pos y.1)).le, half_le_self (Γ.length_pos y.1).le⟩⟩⟩,
    Or.inl ⟨half_pos (Γ.length_pos y.1), half_lt_self (Γ.length_pos y.1)⟩⟩

theorem graphPoint_val {y : Γ.Edge × ℝ × ℝ} (h : Γ.AdmissiblePoint y) :
    (Γ.graphPoint y).1 = ⟨y.1, ⟨y.2, h.1⟩⟩ := by
  unfold graphPoint
  rw [dif_pos h]

theorem graphPoint_edge {y : Γ.Edge × ℝ × ℝ} (h : Γ.AdmissiblePoint y) :
    (Γ.graphPoint y).1.1 = y.1 := by
  rw [graphPoint_val Γ h]

theorem graphPoint_state {y : Γ.Edge × ℝ × ℝ} (h : Γ.AdmissiblePoint y) :
    (Γ.graphPoint y).1.2.1 = y.2 := by
  rw [graphPoint_val Γ h]

/-- Every point of the nonzero prequotient space is the graph point of its own coordinates. -/
theorem graphPoint_of_nonzero (x : Γ.NonzeroPrequotientPhase) :
    Γ.graphPoint (x.1.1, x.1.2.1) = x := by
  have h : Γ.AdmissiblePoint (x.1.1, x.1.2.1) := ⟨x.1.2.2, x.2⟩
  apply Subtype.ext
  exact prequotient_ext Γ (graphPoint_edge Γ h) (graphPoint_state Γ h)

/-- The graph point of a boundary covector is the covector's prequotient point. -/
theorem graphPoint_covector (δ : Γ.BoundaryCovector) :
    Γ.graphPoint (δ.germ.1, FiniteMetricGraph.EdgeEnd.coordinate Γ δ.germ, δ.momentum) =
      δ.toNonzeroPrequotientPhase Γ := by
  have h : Γ.AdmissiblePoint (δ.germ.1, FiniteMetricGraph.EdgeEnd.coordinate Γ δ.germ,
      δ.momentum) := ⟨Γ.edgeEnd_coordinate_mem_closedEdge δ.germ, Or.inr δ.momentum_ne_zero⟩
  apply Subtype.ext
  exact prequotient_ext Γ (graphPoint_edge Γ h) (graphPoint_state Γ h)

/-- Graph points intertwine momentum reversal. -/
theorem graphPoint_reversePoint (y : Γ.Edge × ℝ × ℝ) :
    Γ.graphPoint (Γ.reversePoint y) = Γ.prequotientMomentumReversal (Γ.graphPoint y) := by
  classical
  by_cases h : Γ.AdmissiblePoint y
  · have hR : Γ.AdmissiblePoint (Γ.reversePoint y) := (Γ.admissiblePoint_reversePoint_iff y).mpr h
    apply Subtype.ext
    refine prequotient_ext Γ ?_ ?_
    · rw [graphPoint_edge Γ hR]
      change y.1 = (Γ.graphPoint y).1.1
      rw [graphPoint_edge Γ h]
    · rw [graphPoint_state Γ hR]
      change (y.2.1, -y.2.2) = ((Γ.graphPoint y).1.2.1.1, -(Γ.graphPoint y).1.2.1.2)
      rw [graphPoint_state Γ h]
  · have hR : ¬ Γ.AdmissiblePoint (Γ.reversePoint y) := by
      rwa [Γ.admissiblePoint_reversePoint_iff]
    apply Subtype.ext
    unfold graphPoint
    rw [dif_neg hR, dif_neg h]
    refine prequotient_ext Γ rfl ?_
    change (Γ.length y.1 / 2, (0 : ℝ)) = (Γ.length y.1 / 2, -(0 : ℝ))
    rw [neg_zero]

end FiniteMetricGraph

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-! ### Classes of graph points -/

/-- The class of a graph phase point in the scattering quotient. -/
noncomputable def graphClass (y : Γ.Edge × ℝ × ℝ) : ScatteringPhaseSpace (V := V) S :=
  quotientMap (V := V) S (Γ.graphPoint y)

theorem quotientHamiltonian_graphClass {y : Γ.Edge × ℝ × ℝ} (h : Γ.AdmissiblePoint y) :
    quotientHamiltonian (V := V) S (graphClass V S y) = V.hamiltonian y.1 y.2.1 y.2.2 := by
  unfold graphClass
  rw [quotientHamiltonian_mk]
  unfold prequotientHamiltonian
  rw [Γ.graphPoint_val h]

/-- A graph point is an incoming boundary point exactly when it sits at a vertex with inward
momentum. -/
theorem isIncomingPoint_graphPoint_iff {y : Γ.Edge × ℝ × ℝ} (h : Γ.AdmissiblePoint y) :
    IsIncomingPoint (V := V) S (Γ.graphPoint y) ↔
      (y.2.1 = 0 ∧ y.2.2 < 0) ∨ (y.2.1 = Γ.length y.1 ∧ 0 < y.2.2) := by
  rw [isIncomingPoint_iff, Γ.graphPoint_val h]

/-! ### Outgoing representatives as flight states -/

/-- A point of the outgoing representative section starts a physical edge segment: it is either
strictly inside its edge or an outgoing boundary covector. -/
theorem exists_physicalEdgeSegment_of_not_incoming (x : Γ.NonzeroPrequotientPhase)
    (hx : ¬ IsIncomingPoint (V := V) S x) :
    ∃ _ : V.PhysicalEdgeSegment x.1.1 x.1.2.1, True := by
  by_cases hint : x.1.2.1.1 ∈ Ioo (0 : ℝ) (Γ.length x.1.1)
  · exact V.exists_physicalEdgeSegment_from_interior hint
  · have hne : x.1.2.1.2 ≠ 0 := x.2.resolve_left hint
    have hq : x.1.2.1.1 ∈ Icc (0 : ℝ) (Γ.length x.1.1) := x.1.2.2
    rw [isIncomingPoint_iff] at hx
    have hx' := not_or.mp hx
    have hx1 : x.1.2.1.1 = 0 → 0 ≤ x.1.2.1.2 :=
      fun h0 => not_lt.mp (not_and.mp hx'.1 h0)
    have hx2 : x.1.2.1.1 = Γ.length x.1.1 → x.1.2.1.2 ≤ 0 :=
      fun hl => not_lt.mp (not_and.mp hx'.2 hl)
    by_cases h0 : x.1.2.1.1 = 0
    · have hp : 0 < x.1.2.1.2 := lt_of_le_of_ne (hx1 h0) (Ne.symm hne)
      let α : Γ.OutgoingBoundary (Γ.endpoint x.1.1 false) :=
        ⟨⟨(x.1.1, false), x.1.2.1.2, hne⟩, rfl, by
          change FiniteMetricGraph.EdgeEnd.sign Γ (x.1.1, false) * x.1.2.1.2 < 0
          rw [Γ.edgeEnd_sign_false]; linarith⟩
      obtain ⟨seg, -⟩ := V.exists_physicalEdgeSegment_from_outgoingBoundary α
      have hpt : (FiniteMetricGraph.EdgeEnd.coordinate Γ (x.1.1, false), x.1.2.1.2) = x.1.2.1 := by
        refine Prod.ext ?_ rfl
        change (0 : ℝ) = x.1.2.1.1
        exact h0.symm
      exact ⟨hpt ▸ seg, trivial⟩
    · have hl : x.1.2.1.1 = Γ.length x.1.1 := by
        by_contra hne'
        exact hint ⟨lt_of_le_of_ne hq.1 (Ne.symm h0), lt_of_le_of_ne hq.2 hne'⟩
      have hp : x.1.2.1.2 < 0 := lt_of_le_of_ne (hx2 hl) hne
      let α : Γ.OutgoingBoundary (Γ.endpoint x.1.1 true) :=
        ⟨⟨(x.1.1, true), x.1.2.1.2, hne⟩, rfl, by
          change FiniteMetricGraph.EdgeEnd.sign Γ (x.1.1, true) * x.1.2.1.2 < 0
          rw [Γ.edgeEnd_sign_true]; linarith⟩
      obtain ⟨seg, -⟩ := V.exists_physicalEdgeSegment_from_outgoingBoundary α
      have hpt : (FiniteMetricGraph.EdgeEnd.coordinate Γ (x.1.1, true), x.1.2.1.2) = x.1.2.1 := by
        refine Prod.ext ?_ rfl
        change Γ.length x.1.1 = x.1.2.1.1
        exact hl.symm
      exact ⟨hpt ▸ seg, trivial⟩

namespace FlightState

/-- The flight state started at a regular point of the outgoing representative section. -/
noncomputable def ofRep (x : Γ.NonzeroPrequotientPhase) (hx : ¬ IsIncomingPoint (V := V) S x)
    (hreg : V.prequotientHamiltonian x.1 ∉ V.exceptionalEnergies) : V.FlightState where
  edge := x.1.1
  state := x.1.2.1
  segment := Classical.choose (exists_physicalEdgeSegment_of_not_incoming V S x hx)
  regular := hreg

@[simp] theorem ofRep_edge (x : Γ.NonzeroPrequotientPhase) (hx : ¬ IsIncomingPoint (V := V) S x)
    (hreg : V.prequotientHamiltonian x.1 ∉ V.exceptionalEnergies) :
    (ofRep V S x hx hreg).edge = x.1.1 := rfl

@[simp] theorem ofRep_state (x : Γ.NonzeroPrequotientPhase) (hx : ¬ IsIncomingPoint (V := V) S x)
    (hreg : V.prequotientHamiltonian x.1 ∉ V.exceptionalEnergies) :
    (ofRep V S x hx hreg).state = x.1.2.1 := rfl

/-- A flight state does not start at an incoming boundary point. -/
def NotIncoming (a : V.FlightState) : Prop :=
  ¬ ((a.state.1 = 0 ∧ a.state.2 < 0) ∨ (a.state.1 = Γ.length a.edge ∧ 0 < a.state.2))

theorem notIncoming_ofRep (x : Γ.NonzeroPrequotientPhase) (hx : ¬ IsIncomingPoint (V := V) S x)
    (hreg : V.prequotientHamiltonian x.1 ∉ V.exceptionalEnergies) :
    (ofRep V S x hx hreg).NotIncoming := by
  rw [isIncomingPoint_iff] at hx
  exact hx

variable {V S}

/-- An outgoing flight state does not start at an incoming point. -/
theorem IsOutgoing.notIncoming {b : V.FlightState} (hout : b.IsOutgoing) : b.NotIncoming := by
  obtain ⟨η₀, hη₀, hstate, hsign⟩ := hout
  rcases η₀ with ⟨e, bo⟩
  change e = b.edge at hη₀
  subst hη₀
  cases bo
  · rw [Γ.edgeEnd_coordinate_false] at hstate
    rw [Γ.edgeEnd_sign_false] at hsign
    rintro (⟨-, hneg⟩ | ⟨hl, -⟩)
    · linarith
    · rw [hstate] at hl
      exact absurd hl.symm (ne_of_gt (Γ.length_pos b.edge))
  · rw [Γ.edgeEnd_coordinate_true] at hstate
    rw [Γ.edgeEnd_sign_true] at hsign
    rintro (⟨h0, -⟩ | ⟨-, hpos⟩)
    · rw [hstate] at h0
      exact absurd h0 (ne_of_gt (Γ.length_pos b.edge))
    · linarith

/-- An interior point is not an incoming point. -/
theorem notIncoming_of_interior {a : V.FlightState}
    (hint : a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge)) : a.NotIncoming := by
  rintro (⟨h0, -⟩ | ⟨hl, -⟩)
  · rw [h0] at hint; exact lt_irrefl _ hint.1
  · rw [hl] at hint; exact lt_irrefl _ hint.2

/-- Every flight state starts either strictly inside its edge or at a vertex with outgoing
momentum: an inward-pointing vertex state leaves the edge immediately, and a zero-momentum
vertex state has exceptional energy. -/
theorem interior_or_isOutgoing (a : V.FlightState) :
    a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge) ∨ a.IsOutgoing := by
  by_cases hint : a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge)
  · exact Or.inl hint
  · right
    have hq : a.state.1 ∈ Icc (0 : ℝ) (Γ.length a.edge) := a.segment.initial_physical
    have hne : a.state.2 ≠ 0 :=
      (V.interior_or_momentum_ne_zero_of_regular hq a.regular).resolve_left hint
    -- the position solves `q' = p` at time `0`
    have hderiv : HasDerivAt (fun s => (a.segment.curve s).1) a.state.2 0 := by
      have h := V.edgeIntegralCurve_hasDerivAt_fst
        (a.segment.integralCurve 0 ⟨le_rfl, a.segment.duration_pos.le⟩)
      rwa [a.segment.initial] at h
    have hq0 : (a.segment.curve 0).1 = a.state.1 := by rw [a.segment.initial]
    by_cases h0 : a.state.1 = 0
    · refine ⟨(a.edge, false), rfl, by rw [Γ.edgeEnd_coordinate_false, h0], ?_⟩
      rw [Γ.edgeEnd_sign_false]
      -- the momentum must be positive: otherwise the position becomes negative
      have hpos : 0 < a.state.2 := by
        rcases lt_or_gt_of_ne hne with hneg | hpos
        · exfalso
          have hev := eventually_neg_right_of_hasDerivAt_neg hderiv hneg (by rw [hq0, h0])
          obtain ⟨s, hsneg, hs⟩ := (hev.and (Ioo_mem_nhdsGT a.segment.duration_pos)).exists
          have := (a.segment.interior_after_initial s hs).1
          change (a.segment.curve s).1 < 0 at hsneg
          linarith
        · exact hpos
      linarith
    · have hl : a.state.1 = Γ.length a.edge := by
        by_contra hne'
        exact hint ⟨lt_of_le_of_ne hq.1 (Ne.symm h0), lt_of_le_of_ne hq.2 hne'⟩
      refine ⟨(a.edge, true), rfl, by rw [Γ.edgeEnd_coordinate_true, hl], ?_⟩
      rw [Γ.edgeEnd_sign_true]
      have hneg : a.state.2 < 0 := by
        rcases lt_or_gt_of_ne hne with hneg | hpos
        · exact hneg
        · exfalso
          have hderiv' : HasDerivAt (fun s => (a.segment.curve s).1 - Γ.length a.edge)
              a.state.2 0 := hderiv.sub_const _
          have hev := eventually_pos_right_of_hasDerivAt_pos hderiv' hpos (by rw [hq0, hl, sub_self])
          obtain ⟨s, hspos, hs⟩ := (hev.and (Ioo_mem_nhdsGT a.segment.duration_pos)).exists
          have := (a.segment.interior_after_initial s hs).2
          change 0 < (a.segment.curve s).1 - Γ.length a.edge at hspos
          linarith
      linarith

/-- The states reached along the chain after at least one scattering event are outgoing. -/
theorem isOutgoing_of_iterate_succ (S : BorelEnergyPreservingScattering V) {a b : V.FlightState}
    {n : ℕ} (hb : iterate V S a (n + 1) = some b) : b.IsOutgoing := by
  rw [iterate_succ] at hb
  rcases Option.bind_eq_some_iff.mp hb with ⟨c, -, hcb⟩
  exact next_isOutgoing (V := V) S hcb

/-- Before time zero the unified trajectory is pinned at the initial state. -/
theorem trajectory_of_neg [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) {t : ℝ} (ht : t < 0) : trajectory V S a t = (a.edge, a.state) := by
  unfold trajectory
  rw [dif_neg (not_le.mpr ht)]

/-- At the onset of any defined flight the trajectory sits at that flight's initial state. -/
theorem trajectory_impactReal [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) {n : ℕ} {b : V.FlightState} (hb : iterate V S a n = some b) :
    trajectory V S a (impactReal V S a n) = (b.edge, b.state) := by
  cases n with
  | zero =>
      rw [impactReal_zero, trajectory_zero]
      rw [iterate_zero] at hb
      rw [Option.some.inj hb]
  | succ m => exact trajectory_at_impact V S a m hb

/-- Every point of a trajectory is admissible: physical, and never a zero-momentum vertex
state (the energy is regular). -/
theorem trajectory_admissible [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (t : ℝ) : Γ.AdmissiblePoint (trajectory V S a t) := by
  by_cases ht : 0 ≤ t
  · refine ⟨trajectory_physical V S a ht, ?_⟩
    exact V.interior_or_momentum_ne_zero_of_regular (trajectory_physical V S a ht)
      (trajectory_regular V S a ht)
  · rw [trajectory_of_neg S a (not_le.mp ht)]
    exact ⟨a.segment.initial_physical,
      V.interior_or_momentum_ne_zero_of_regular a.segment.initial_physical a.regular⟩

/-- Energy conservation along the whole trajectory, including the pinned negative times. -/
theorem trajectory_hamiltonian_eq' [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    (a : V.FlightState) (t : ℝ) :
    V.hamiltonian (trajectory V S a t).1 (trajectory V S a t).2.1 (trajectory V S a t).2.2 =
      a.energy := by
  by_cases ht : 0 ≤ t
  · exact trajectory_hamiltonian_eq V S a ht
  · rw [trajectory_of_neg S a (not_le.mp ht)]
    rfl

/-- **The trajectory never sits at an incoming boundary point.**  At the onset of a flight it is
at the (outgoing) initial state of that flight; strictly inside a flight it is interior. -/
theorem trajectory_notIncoming [Nonempty Γ.Edge] (S : BorelEnergyPreservingScattering V)
    {a : V.FlightState} (ha : a.NotIncoming) (t : ℝ) :
    ¬ IsIncomingPoint (V := V) S (Γ.graphPoint (trajectory V S a t)) := by
  rw [isIncomingPoint_graphPoint_iff V S (trajectory_admissible S a t)]
  by_cases ht : 0 ≤ t
  · obtain ⟨n, hact⟩ := exists_activeAt V S a ht
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hact.1
    rw [trajectory_eq V S a ht hact hb]
    rcases eq_or_lt_of_le hact.2.1 with heq | hlt
    · -- the onset of flight `n`
      rw [← heq, sub_self, flightCurve_zero]
      cases n with
      | zero =>
          rw [iterate_zero] at hb
          rw [← Option.some.inj hb]
          exact ha
      | succ m => exact (isOutgoing_of_iterate_succ S hb).notIncoming
    · -- strictly inside flight `n`
      have hint := flightCurve_interior V b (by linarith) (hact.elapsed_lt (V := V) hb hlt).2
      rintro (⟨h0, -⟩ | ⟨hl, -⟩)
      · change (flightCurve V b (t - impactReal V S a n)).1 = 0 at h0
        rw [h0] at hint; exact lt_irrefl _ hint.1
      · change (flightCurve V b (t - impactReal V S a n)).1 = Γ.length b.edge at hl
        rw [hl] at hint; exact lt_irrefl _ hint.2
  · rw [trajectory_of_neg S a (not_le.mp ht)]
    exact ha

end FlightState

/-! ### The representative flight of a regular quotient point -/

/-- The outgoing representative of a quotient point (Lemma IV.4). -/
noncomputable def rep (z : ScatteringPhaseSpace (V := V) S) : Γ.NonzeroPrequotientPhase :=
  (outgoingChart (V := V) S z).1

theorem rep_not_incoming (z : ScatteringPhaseSpace (V := V) S) :
    ¬ IsIncomingPoint (V := V) S (rep V S z) :=
  (outgoingChart (V := V) S z).2

theorem quotientMap_rep (z : ScatteringPhaseSpace (V := V) S) :
    quotientMap (V := V) S (rep V S z) = z := by
  change outgoingRepresentativeMap (V := V) S (outgoingChart (V := V) S z) = z
  exact (Equiv.ofBijective (outgoingRepresentativeMap (V := V) S)
    (outgoingRepresentativeMap_bijective (V := V) S)).apply_symm_apply z

theorem rep_quotientMap (x : Γ.NonzeroPrequotientPhase) :
    rep V S (quotientMap (V := V) S x) = repOf (V := V) S x :=
  congrArg Subtype.val (outgoingChart_quotientMap (V := V) S x)

theorem rep_quotientMap_of_not_incoming (x : Γ.NonzeroPrequotientPhase)
    (hx : ¬ IsIncomingPoint (V := V) S x) : rep V S (quotientMap (V := V) S x) = x := by
  rw [rep_quotientMap, repOf_of_not_incoming (V := V) S hx]

theorem regular_rep (z : RegularScatteringPhaseSpace (V := V) S) :
    V.prequotientHamiltonian (rep V S z.1).1 ∉ V.exceptionalEnergies := by
  have h := z.2
  change quotientHamiltonian (V := V) S z.1 ∉ V.exceptionalEnergies at h
  rwa [← quotientMap_rep V S z.1, quotientHamiltonian_mk] at h

/-- The flight state started at the outgoing representative of a regular quotient point. -/
noncomputable def repFlight (z : RegularScatteringPhaseSpace (V := V) S) : V.FlightState :=
  FlightState.ofRep V S (rep V S z.1) (rep_not_incoming V S z.1) (regular_rep V S z)

@[simp] theorem repFlight_edge (z : RegularScatteringPhaseSpace (V := V) S) :
    (repFlight V S z).edge = (rep V S z.1).1.1 := rfl

@[simp] theorem repFlight_state (z : RegularScatteringPhaseSpace (V := V) S) :
    (repFlight V S z).state = (rep V S z.1).1.2.1 := rfl

theorem repFlight_notIncoming (z : RegularScatteringPhaseSpace (V := V) S) :
    (repFlight V S z).NotIncoming :=
  FlightState.notIncoming_ofRep V S _ _ _

theorem repFlight_energy (z : RegularScatteringPhaseSpace (V := V) S) :
    (repFlight V S z).energy = quotientHamiltonian (V := V) S z.1 := by
  rw [← quotientMap_rep V S z.1, quotientHamiltonian_mk]
  rfl

/-- The class of the representative flight's initial point is the point itself. -/
theorem graphClass_repFlight (z : RegularScatteringPhaseSpace (V := V) S) :
    graphClass V S ((repFlight V S z).edge, (repFlight V S z).state) = z.1 := by
  unfold graphClass
  rw [repFlight_edge, repFlight_state, Γ.graphPoint_of_nonzero, quotientMap_rep]

/-! ### The reversal map between the quotients of time-reversed laws -/

section Reversal

variable {V}
variable {S} {T : BorelEnergyPreservingScattering V}

/-- A scattering step of `S` is reversed into a scattering step of any time reversal `T`. -/
theorem scatteringStep_reverse (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T)
    {x y : Γ.NonzeroPrequotientPhase} (hxy : scatteringStep (V := V) S x y) :
    scatteringStep (V := V) T (Γ.prequotientMomentumReversal y)
      (Γ.prequotientMomentumReversal x) := by
  rcases hxy with ⟨v, α, rfl, rfl⟩
  set β : Γ.OutgoingBoundary v := S.map v α with hβ
  refine ⟨v, (Γ.incomingMomentumReversal v).symm β, ?_, ?_⟩
  · rw [Γ.prequotientMomentumReversal_boundary]
    apply congrArg (fun δ : Γ.BoundaryCovector => δ.toNonzeroPrequotientPhase Γ)
    exact FiniteMetricGraph.BoundaryCovector.ext Γ rfl rfl
  · rw [Γ.prequotientMomentumReversal_boundary, hST v β]
    apply congrArg (fun δ : Γ.BoundaryCovector => δ.toNonzeroPrequotientPhase Γ)
    rw [hβ, (S.map v).symm_apply_apply α]
    exact FiniteMetricGraph.BoundaryCovector.ext Γ rfl rfl

/-- Momentum reversal sends the scattering equivalence of `S` to that of a time reversal `T`. -/
theorem scatteringSetoid_reverse (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T)
    {x y : Γ.NonzeroPrequotientPhase} (hxy : (scatteringSetoid (V := V) S) x y) :
    (scatteringSetoid (V := V) T) (Γ.prequotientMomentumReversal x)
      (Γ.prequotientMomentumReversal y) := by
  induction hxy with
  | rel x y hxy =>
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (scatteringStep_reverse hST hxy))
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- **The reversal map** `ρ : Q(S) → Q(T)`, `[x] ↦ [R x]`, for a time reversal `T` of `S`. -/
noncomputable def reverseQuotient (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T) :
    ScatteringPhaseSpace (V := V) S → ScatteringPhaseSpace (V := V) T :=
  Quotient.lift (fun x => quotientMap (V := V) T (Γ.prequotientMomentumReversal x))
    (fun _ _ hxy => Quotient.sound (scatteringSetoid_reverse hST hxy))

@[simp] theorem reverseQuotient_mk (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T)
    (x : Γ.NonzeroPrequotientPhase) :
    reverseQuotient hST (quotientMap (V := V) S x) =
      quotientMap (V := V) T (Γ.prequotientMomentumReversal x) := rfl

theorem reverseQuotient_reverseQuotient
    (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T)
    (hTS : BorelEnergyPreservingScattering.IsTimeReversal V T S)
    (z : ScatteringPhaseSpace (V := V) S) :
    reverseQuotient hTS (reverseQuotient hST z) = z := by
  refine Quotient.inductionOn' z ?_
  intro x
  change quotientMap (V := V) S
    (Γ.prequotientMomentumReversal (Γ.prequotientMomentumReversal x)) = quotientMap (V := V) S x
  rw [Γ.prequotientMomentumReversal_involutive]

theorem measurable_reverseQuotient (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T) :
    Measurable (reverseQuotient hST) := by
  intro A hA
  rw [measurableSet_quotient_iff] at hA ⊢
  have hpre : quotientMap (V := V) S ⁻¹' (reverseQuotient hST ⁻¹' A) =
      Γ.prequotientMomentumReversal ⁻¹' (quotientMap (V := V) T ⁻¹' A) := by
    ext x; rfl
  rw [hpre]
  exact hA.preimage Γ.measurable_prequotientMomentumReversal

theorem quotientHamiltonian_reverseQuotient
    (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T)
    (z : ScatteringPhaseSpace (V := V) S) :
    quotientHamiltonian (V := V) T (reverseQuotient hST z) = quotientHamiltonian (V := V) S z := by
  refine Quotient.inductionOn' z ?_
  intro x
  change quotientHamiltonian (V := V) T (quotientMap (V := V) T (Γ.prequotientMomentumReversal x))
    = quotientHamiltonian (V := V) S (quotientMap (V := V) S x)
  rw [quotientHamiltonian_mk, quotientHamiltonian_mk]
  exact V.prequotientHamiltonian_momentumReversal x

theorem reverseQuotient_graphClass (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T)
    (y : Γ.Edge × ℝ × ℝ) :
    reverseQuotient hST (graphClass V S y) = graphClass V T (Γ.reversePoint y) := by
  unfold graphClass
  rw [reverseQuotient_mk, Γ.graphPoint_reversePoint]

/-- The reversal map restricted to the regular sectors. -/
noncomputable def reverseRegular (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T) :
    RegularScatteringPhaseSpace (V := V) S → RegularScatteringPhaseSpace (V := V) T :=
  fun z => ⟨reverseQuotient hST z.1, by
    change quotientHamiltonian (V := V) T (reverseQuotient hST z.1) ∉ V.exceptionalEnergies
    rw [quotientHamiltonian_reverseQuotient]
    exact z.2⟩

theorem reverseRegular_val (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T)
    (z : RegularScatteringPhaseSpace (V := V) S) :
    (reverseRegular hST z).1 = reverseQuotient hST z.1 := rfl

theorem reverseRegular_reverseRegular
    (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T)
    (hTS : BorelEnergyPreservingScattering.IsTimeReversal V T S)
    (z : RegularScatteringPhaseSpace (V := V) S) :
    reverseRegular hTS (reverseRegular hST z) = z := by
  apply Subtype.ext
  rw [reverseRegular_val, reverseRegular_val, reverseQuotient_reverseQuotient]

theorem measurable_reverseRegular (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T) :
    Measurable (reverseRegular hST) := by
  rw [measurable_comap_iff]
  change Measurable (fun z : RegularScatteringPhaseSpace (V := V) S => reverseQuotient hST z.1)
  exact (measurable_reverseQuotient hST).comp measurable_subtype_coe

theorem quotientHamiltonian_reverseRegular
    (hST : BorelEnergyPreservingScattering.IsTimeReversal V S T)
    (z : RegularScatteringPhaseSpace (V := V) S) :
    quotientHamiltonian (V := V) T (reverseRegular hST z).1 = quotientHamiltonian (V := V) S z.1 :=
  quotientHamiltonian_reverseQuotient hST z.1

end Reversal

/-- The time-reversed law used for negative times, with its two time-reversal relations. -/
theorem isTimeReversal_symm_timeReversed :
    BorelEnergyPreservingScattering.IsTimeReversal V
      (BorelEnergyPreservingScattering.timeReversed V S) S :=
  (BorelEnergyPreservingScattering.isTimeReversal_timeReversed V S).symm

/-! ### The forward flow -/

variable [Nonempty Γ.Edge]

/-- **The forward scattered evolution** on the regular quotient sector: the class of the unified
forward trajectory of the representative flight (pinned at `z` for negative times). -/
noncomputable def forwardFlow (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ) :
    RegularScatteringPhaseSpace (V := V) S :=
  ⟨graphClass V S (FlightState.trajectory V S (repFlight V S z) t), by
    change quotientHamiltonian (V := V) S
      (graphClass V S (FlightState.trajectory V S (repFlight V S z) t)) ∉ V.exceptionalEnergies
    rw [quotientHamiltonian_graphClass V S (FlightState.trajectory_admissible S _ t),
      FlightState.trajectory_hamiltonian_eq']
    exact (repFlight V S z).regular⟩

theorem forwardFlow_val (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ) :
    (forwardFlow V S z t).1 = graphClass V S (FlightState.trajectory V S (repFlight V S z) t) :=
  rfl

@[simp] theorem forwardFlow_zero (z : RegularScatteringPhaseSpace (V := V) S) :
    forwardFlow V S z 0 = z := by
  apply Subtype.ext
  rw [forwardFlow_val, FlightState.trajectory_zero, graphClass_repFlight]

theorem forwardFlow_of_neg (z : RegularScatteringPhaseSpace (V := V) S) {t : ℝ} (ht : t < 0) :
    forwardFlow V S z t = z := by
  apply Subtype.ext
  rw [forwardFlow_val, FlightState.trajectory_of_neg S _ ht, graphClass_repFlight]

/-- Energy conservation along the forward flow. -/
theorem quotientHamiltonian_forwardFlow (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ) :
    quotientHamiltonian (V := V) S (forwardFlow V S z t).1 =
      quotientHamiltonian (V := V) S z.1 := by
  rw [forwardFlow_val, quotientHamiltonian_graphClass V S (FlightState.trajectory_admissible S _ t),
    FlightState.trajectory_hamiltonian_eq', repFlight_energy]

/-- The outgoing representative of the flow at a nonnegative time is the trajectory's point. -/
theorem rep_forwardFlow (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ) :
    rep V S (forwardFlow V S z t).1 =
      Γ.graphPoint (FlightState.trajectory V S (repFlight V S z) t) := by
  rw [forwardFlow_val, graphClass]
  exact rep_quotientMap_of_not_incoming V S _
    (FlightState.trajectory_notIncoming S (repFlight_notIncoming V S z) t)

theorem repFlight_forwardFlow_edge (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ) :
    (repFlight V S (forwardFlow V S z t)).edge =
      (FlightState.trajectory V S (repFlight V S z) t).1 := by
  rw [repFlight_edge, rep_forwardFlow]
  exact Γ.graphPoint_edge (FlightState.trajectory_admissible S _ t)

theorem repFlight_forwardFlow_state (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ) :
    (repFlight V S (forwardFlow V S z t)).state =
      (FlightState.trajectory V S (repFlight V S z) t).2 := by
  rw [repFlight_state, rep_forwardFlow]
  exact Γ.graphPoint_state (FlightState.trajectory_admissible S _ t)

/-- **The forward semigroup law on the quotient**: `Φ⁺_t (Φ⁺_s z) = Φ⁺_{s+t} z` for `s, t ≥ 0`. -/
theorem forwardFlow_forwardFlow (z : RegularScatteringPhaseSpace (V := V) S) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    forwardFlow V S (forwardFlow V S z s) t = forwardFlow V S z (s + t) := by
  apply Subtype.ext
  rw [forwardFlow_val, forwardFlow_val,
    FlightState.trajectory_semigroup V S (repFlight V S z) hs ht (repFlight V S (forwardFlow V S z s))
      (repFlight_forwardFlow_edge V S z s) (repFlight_forwardFlow_state V S z s)]


/-! ### The two-sided flow -/


/-- **The scattered evolution `Φₜ`** on the regular quotient phase space, for every real `t`:
the forward flow for `t ≥ 0`, and for `t < 0` the forward flow of the time-reversed law
conjugated by the reversal map (the paper's incoming chart with the inverse laws). -/
noncomputable def flow (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ) :
    RegularScatteringPhaseSpace (V := V) S :=
  if 0 ≤ t then forwardFlow V S z t
  else reverseRegular (isTimeReversal_symm_timeReversed V S)
    (forwardFlow V (BorelEnergyPreservingScattering.timeReversed V S)
      (reverseRegular (BorelEnergyPreservingScattering.isTimeReversal_timeReversed V S) z) (-t))

theorem flow_of_nonneg (z : RegularScatteringPhaseSpace (V := V) S) {t : ℝ} (ht : 0 ≤ t) :
    flow V S z t = forwardFlow V S z t := by
  unfold flow; rw [if_pos ht]

theorem flow_of_neg (z : RegularScatteringPhaseSpace (V := V) S) {t : ℝ} (ht : t < 0) :
    flow V S z t = reverseRegular (isTimeReversal_symm_timeReversed V S)
      (forwardFlow V (BorelEnergyPreservingScattering.timeReversed V S)
        (reverseRegular (BorelEnergyPreservingScattering.isTimeReversal_timeReversed V S) z)
        (-t)) := by
  unfold flow; rw [if_neg (not_le.mpr ht)]

/-- `Φ₀ = id`. -/
@[simp] theorem flow_zero (z : RegularScatteringPhaseSpace (V := V) S) : flow V S z 0 = z := by
  rw [flow_of_nonneg V S z le_rfl, forwardFlow_zero]

/-- **Energy conservation**: `H ∘ Φₜ = H` for every real `t` (the identity (4) of the paper). -/
theorem quotientHamiltonian_flow (z : RegularScatteringPhaseSpace (V := V) S) (t : ℝ) :
    quotientHamiltonian (V := V) S (flow V S z t).1 = quotientHamiltonian (V := V) S z.1 := by
  by_cases ht : 0 ≤ t
  · rw [flow_of_nonneg V S z ht, quotientHamiltonian_forwardFlow]
  · rw [flow_of_neg V S z (not_le.mp ht), quotientHamiltonian_reverseRegular,
      quotientHamiltonian_forwardFlow, quotientHamiltonian_reverseRegular]

/-- The forward semigroup law for the two-sided flow, on nonnegative times. -/
theorem flow_flow_of_nonneg (z : RegularScatteringPhaseSpace (V := V) S) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) : flow V S (flow V S z s) t = flow V S z (s + t) := by
  rw [flow_of_nonneg V S z hs, flow_of_nonneg V S _ ht, flow_of_nonneg V S z (by linarith),
    forwardFlow_forwardFlow V S z hs ht]

/-- The backward semigroup law for the two-sided flow, on nonpositive times. -/
theorem flow_flow_of_nonpos (z : RegularScatteringPhaseSpace (V := V) S) {s t : ℝ}
    (hs : s ≤ 0) (ht : t ≤ 0) : flow V S (flow V S z s) t = flow V S z (s + t) := by
  rcases eq_or_lt_of_le hs with rfl | hs'
  · rw [flow_zero, zero_add]
  rcases eq_or_lt_of_le ht with rfl | ht'
  · rw [flow_zero, add_zero]
  rw [flow_of_neg V S z hs', flow_of_neg V S _ ht', flow_of_neg V S z (by linarith),
    reverseRegular_reverseRegular, forwardFlow_forwardFlow _ _ _ (by linarith) (by linarith)]
  congr 2
  ring

end MechanicalPotential

end HamiltonianMetricGraphs
