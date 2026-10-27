/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3 (no-impact part): a uniform time for the Liouville invariance of the edge flow
-/

import HamiltonianMetricGraphs.EdgeFlightMap
import HamiltonianMetricGraphs.NoZeno

/-!
# A uniform time for the no-impact Liouville invariance

`measure_image_flightCurve` (Lemma V.1 read through the flight machinery) says that the time-`Δ`
flight map preserves `dq dp` on a measurable set of initial conditions, *provided* the flights stay
in one physical momentum box and `Δ ≤ 1 / (3M)` where `M` bounds the linearized field on the closed
edge.  Both provisos are uniform once an energy window is fixed:

* `exists_compact_energy_speed_bound` bounds the momentum on a compact energy window, and
  `flightCurve_mem_closedEdgeMomentumBox` confines the flight to the corresponding box;
* `exists_bound_forceDeriv_closedEdge` bounds `V''` on each closed edge, and there are finitely
  many edges, so one `M` works for all of them.

`exists_uniform_measure_image_flightCurve` packages this: on a compact energy window there is one
positive time `ε` below which the time-`Δ` flight map preserves `dq dp` on *every* measurable set
of surviving initial states.  This is the no-impact half of Lemma VI.3, with every hypothesis
discharged, in the form the covering argument consumes.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set MeasureTheory PhysicalEdgeSegment
open scoped NNReal ENNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- A single bound for the linearized edge field over all the (finitely many) closed edges. -/
theorem exists_uniform_bound_edgeFieldDeriv :
    ∃ M : ℝ≥0, (1 : ℝ) ≤ (M : ℝ) ∧
      ∀ (e : Γ.Edge), ∀ q ∈ Icc (0 : ℝ) (Γ.length e), ‖V.edgeFieldDeriv e q‖ ≤ (M : ℝ) := by
  classical
  choose C hC1 hCbound using fun e : Γ.Edge => V.exists_bound_forceDeriv_closedEdge e
  set N : ℝ≥0 := Finset.univ.sup (fun e : Γ.Edge => Real.toNNReal (C e)) with hN
  refine ⟨N + 1, ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ (N : ℝ) := N.coe_nonneg
    push_cast
    linarith
  · intro e q hq
    have hCe : (0 : ℝ) ≤ C e := by linarith [hC1 e]
    have h1 : Real.toNNReal (C e) ≤ N :=
      hN ▸ Finset.le_sup (f := fun e : Γ.Edge => Real.toNNReal (C e)) (Finset.mem_univ e)
    have h2 : C e ≤ (N : ℝ) := by
      have h := NNReal.coe_le_coe.mpr h1
      rwa [Real.coe_toNNReal (C e) hCe] at h
    have hle : C e ≤ ((N + 1 : ℝ≥0) : ℝ) := by push_cast; linarith
    exact V.norm_edgeFieldDeriv_le e q (le_trans (hC1 e) hle) (le_trans (hCbound e q hq) hle)

/-- **Lemma VI.3, no-impact part, with the hypotheses discharged.**  On a compact energy window
there is a uniform positive time `ε` such that for every `0 < Δ ≤ ε` the time-`Δ` flight map
preserves `dq dp` on every measurable set of initial states whose flights carry energy in the
window and survive past `Δ`.  Together with the openness of the no-impact condition
(`noImpact_persists`) this is the invariance on the no-impact stratum. -/
theorem exists_uniform_measure_image_flightCurve (K : Set ℝ) (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (e : Γ.Edge) (Δ : ℝ), 0 < Δ → Δ ≤ ε →
      ∀ (W : Set (ℝ × ℝ)) (b : ℝ × ℝ → V.FlightState),
        MeasurableSet W →
        (∀ x ∈ W, (b x).edge = e) → (∀ x ∈ W, (b x).state = x) →
        (∀ x ∈ W, (b x).energy ∈ K) →
        (∀ x ∈ W, ∀ _ : BddAbove (durationSet V (b x).edge (b x).state),
          Δ ≤ sSup (durationSet V (b x).edge (b x).state)) →
        volume ((fun x => FlightState.flightCurve V (b x) Δ) '' W) = volume W := by
  classical
  obtain ⟨P, -, hPbound⟩ := V.exists_compact_energy_speed_bound K hK
  obtain ⟨M, hM1, hMbound⟩ := V.exists_uniform_bound_edgeFieldDeriv
  refine ⟨1 / (3 * (M : ℝ)), by positivity, ?_⟩
  intro e Δ hΔ hΔε W b hW hbe hbs hbE hsurv
  refine V.measure_image_flightCurve b hbe hbs hsurv (P := P) ?_ hW hΔ hM1 (hMbound e) hΔε
  intro x hx t ht
  have h := FlightState.flightCurve_mem_closedEdgeMomentumBox V (b x) hPbound (hbE x hx) ht.1
    (fun hbdd => le_trans ht.2 (hsurv x hx hbdd))
  rwa [hbe x hx] at h

end MechanicalPotential

end HamiltonianMetricGraphs
