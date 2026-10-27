/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.ThinNetwork
import HamiltonianMetricGraphs.Realization.GlobalFlow
import HamiltonianMetricGraphs.Realization.SmoothPlateau

/-!
# Completeness of the microscopic flow, and the flow `Φ^ε_t`

Definition IX.3(i) of the paper takes the potential `W_ε ∈ C²(ℝ²)` of a thin network bounded
below and notes that the flow `Φ^ε_t` of `H_ε(x, ξ) = ½|ξ|² + W_ε(x)` is then complete, since
`|ξ|² ≤ 2(H_ε - inf W_ε)` bounds the velocity.  The formal `ThinHamiltonianNetwork` carries both
assumptions (`contDiff_pot`, `pot_bddBelow`).  This file proves completeness and uniqueness and
then defines the flow once and for all; the hypotheses (E), (J), (D) of `ThinHypotheses.lean` are
statements about it.

## Main results

* `exists_microTrajectory_of_bddBelow`: if `W_ε` is bounded below, through every state there is a
  trajectory of `H_ε` on `[0, A]` for every `A ≥ 0`.
* `MicroTrajectory.eq_of_initial`: two trajectories with the same initial state agree (the vector
  field is `C¹`).
* `flow`: **the flow `Φ^ε_t` of `H_ε`**, defined for all `t ∈ ℝ` (for `t < 0` through the time
  reversal `ρ̃(x, ξ) = (x, -ξ)`), with `flow_zero`, `flow_add` (`Φ_{s+t} = Φ_t ∘ Φ_s` for
  `s, t ≥ 0`), `flow_neg` (`Φ_{-t} = ρ̃ ∘ Φ_t ∘ ρ̃`) and `flow_reversal`
  (`Φ_b(ρ̃ Φ_b z) = ρ̃ z`, the identity `Φ^ε_t ∘ ρ̃ = ρ̃ ∘ Φ^ε_{-t}` used in Proposition IX.5).
* `flowTraj`: the flow through `z`, restricted to `[0, S]`, is a trajectory of `H_ε`;
  `MicroTrajectory.eq_flow`: every trajectory is the flow through its initial state;
  `hasDerivAt_flow`: `t ↦ Φ^ε_t(z)` solves Hamilton's equations at every `t ∈ ℝ`;
  `hamiltonian_flow`: `H_ε` is conserved along the flow.

## Proof of global existence

No continuation argument is needed.  Fix the initial state `(x₀, p₀)` with energy `E`, a lower
bound `m` of `W_ε`, and `P² = 2(E - m)`.  The vector field of `H_ε` is cut off smoothly in the
momentum (outside `|p|² ≤ P² + 1`) and in the position (outside `|x - x₀|² ≤ 2P²A² + 1`); the
result is `C¹` and globally bounded, so `exists_integralCurve_Icc` (Picard–Lindelöf) solves it on
`[0, A]`.  At the first time `τ` at which a cutoff would become active, the curve has solved
Hamilton's equations on `[0, τ)`, so the energy is conserved up to `τ`
(`constant_of_has_deriv_right_zero`), `|p(τ)|² ≤ P²` and `|x(τ) - x₀| ≤ Pτ ≤ PA` by the mean
value inequality — so no cutoff is active at `τ` either, a contradiction.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph
open scoped Topology

namespace ThinHamiltonianNetwork

variable {Γ : FiniteMetricGraph} {N : ThinHamiltonianNetwork Γ}

/-- squared Euclidean norm -/
private def sq2 (v : ℝ × ℝ) : ℝ := v.1 ^ 2 + v.2 ^ 2

private theorem sq2_nonneg (v : ℝ × ℝ) : 0 ≤ sq2 v := by
  unfold sq2; positivity

private theorem norm_sq_le_sq2 (v : ℝ × ℝ) : ‖v‖ ^ 2 ≤ sq2 v := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  unfold sq2
  rcases max_cases |v.1| |v.2| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h, sq_abs] <;>
    nlinarith [sq_nonneg v.1, sq_nonneg v.2]

private theorem sq2_le_two_norm_sq (v : ℝ × ℝ) : sq2 v ≤ 2 * ‖v‖ ^ 2 := by
  have h1 : |v.1| ≤ ‖v‖ := by simpa using norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by simpa using norm_snd_le v
  unfold sq2
  have e1 : v.1 ^ 2 ≤ ‖v‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e2 : v.2 ^ 2 ≤ ‖v‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  linarith

private theorem contDiff_sq2 {n : WithTop ℕ∞} : ContDiff ℝ n sq2 :=
  (contDiff_fst.pow 2).add (contDiff_snd.pow 2)

private theorem continuous_sq2 : Continuous sq2 :=
  (continuous_fst.pow 2).add (continuous_snd.pow 2)

/-- The energy of a curve solving Hamilton's equations at a time `t` has derivative `0` there. -/
theorem hasDerivWithinAt_hamiltonian_zero {ε : ℝ} {x p : ℝ → ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x (p t) s t) (hp : HasDerivWithinAt p (N.force ε (x t)) s t) :
    HasDerivWithinAt (fun r => N.hamiltonian ε (x r) (p r)) 0 s t := by
  have hpot : Differentiable ℝ (N.pot ε) := (N.contDiff_pot ε).differentiable (by norm_num)
  have hkin : HasDerivWithinAt (fun r => ((p r).1 ^ 2 + (p r).2 ^ 2) / 2)
      ((p t).1 * (N.force ε (x t)).1 + (p t).2 * (N.force ε (x t)).2) s t := by
    have h1 := hp.fst_comp
    have h2 := hp.snd_comp
    have key : HasDerivWithinAt (fun r => ((p r).1 ^ 2 + (p r).2 ^ 2) / 2)
        ((2 * (p t).1 ^ (2 - 1) * (N.force ε (x t)).1 +
          2 * (p t).2 ^ (2 - 1) * (N.force ε (x t)).2) / 2) s t :=
      ((h1.pow 2).add (h2.pow 2)).div_const 2
    convert key using 1
    ring
  have hpot' : HasDerivWithinAt (fun r => N.pot ε (x r))
      (fderiv ℝ (N.pot ε) (x t) (p t)) s t :=
    ((hpot (x t)).hasFDerivAt).comp_hasDerivWithinAt t hx
  rw [fderiv_apply_eq hpot] at hpot'
  have hsum := hkin.add hpot'
  have hz : (p t).1 * (N.force ε (x t)).1 + (p t).2 * (N.force ε (x t)).2 +
      (deriv (fun s => N.pot ε (s, (x t).2)) (x t).1 * (p t).1 +
        deriv (fun s => N.pot ε ((x t).1, s)) (x t).2 * (p t).2) = 0 := by
    rw [ThinHamiltonianNetwork.force]
    ring
  rw [hz] at hsum
  exact hsum

/-- The force of a `C²` potential is `C¹`. -/
theorem contDiff_force (ε : ℝ) : ContDiff ℝ 1 (N.force ε) := by
  have hW := N.contDiff_pot ε
  have hd : Differentiable ℝ (N.pot ε) := hW.differentiable (by norm_num)
  have heq : N.force ε = fun z => (-(fderiv ℝ (N.pot ε) z (1, 0)),
      -(fderiv ℝ (N.pot ε) z (0, 1))) := by
    funext z
    simp only [ThinHamiltonianNetwork.force, (hasDerivAt_partial_fst hd z).deriv,
      (hasDerivAt_partial_snd hd z).deriv]
  rw [heq]
  have hf : ContDiff ℝ 1 (fderiv ℝ (N.pot ε)) := hW.fderiv_right (by norm_num)
  exact ((hf.clm_apply contDiff_const).neg).prodMk ((hf.clm_apply contDiff_const).neg)

/-- The position component of a phase-space curve. -/
private theorem hasDerivWithinAt_phase_fst {α : ℝ → (ℝ × ℝ) × (ℝ × ℝ)}
    {w : (ℝ × ℝ) × (ℝ × ℝ)} {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt α w s t) :
    HasDerivWithinAt (fun u => (α u).1) w.1 s t :=
  (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)).hasFDerivAt.comp_hasDerivWithinAt t h

/-- The momentum component of a phase-space curve. -/
private theorem hasDerivWithinAt_phase_snd {α : ℝ → (ℝ × ℝ) × (ℝ × ℝ)}
    {w : (ℝ × ℝ) × (ℝ × ℝ)} {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt α w s t) :
    HasDerivWithinAt (fun u => (α u).2) w.2 s t :=
  (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)).hasFDerivAt.comp_hasDerivWithinAt t h

/-! ### Cut-off vector field -/

/-- A smooth cutoff equal to `1` where `sq2 v ≤ a` and to `0` where `sq2 v ≥ 4a`. -/
private noncomputable def cut (a : ℝ) (v : ℝ × ℝ) : ℝ := 1 - plateau a (4 * a) (sq2 v)

private theorem cut_of_le {a : ℝ} (ha : 0 < a) {v : ℝ × ℝ} (h : sq2 v ≤ a) : cut a v = 1 := by
  rw [cut, plateau_of_le (by linarith) h, sub_zero]

private theorem cut_of_ge {a : ℝ} (ha : 0 < a) {v : ℝ × ℝ} (h : 4 * a ≤ sq2 v) :
    cut a v = 0 := by
  rw [cut, plateau_of_ge (by linarith) h, sub_self]

private theorem abs_cut_le (a : ℝ) (v : ℝ × ℝ) : |cut a v| ≤ 1 := by
  have h0 := plateau_nonneg a (4 * a) (sq2 v)
  have h1 := plateau_le_one a (4 * a) (sq2 v)
  rw [abs_le, cut]
  constructor <;> linarith

private theorem contDiff_cut (a : ℝ) : ContDiff ℝ 1 (cut a) :=
  contDiff_const.sub ((contDiff_plateau a (4 * a)).comp contDiff_sq2)

/-- The vector field of `H_ε` with the velocity cut off where `sq2 p ≥ 4a` and the force cut off
where `sq2 (x - x₀) ≥ 4R`.  It is `C¹` and globally bounded. -/
private noncomputable def cutField (N : ThinHamiltonianNetwork Γ) (ε : ℝ) (x₀ : ℝ × ℝ)
    (a R : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ) :=
  (cut a w.2 • w.2, cut R (w.1 - x₀) • N.force ε w.1)

private theorem contDiff_cutField (ε : ℝ) (x₀ : ℝ × ℝ) (a R : ℝ) :
    ContDiff ℝ 1 (cutField N ε x₀ a R) :=
  (((contDiff_cut a).comp contDiff_snd).smul contDiff_snd).prodMk
    (((contDiff_cut R).comp (contDiff_fst.sub contDiff_const)).smul
      ((contDiff_force ε).comp contDiff_fst))

private theorem norm_le_one_add_sq (r : ℝ) : r ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg (r - 1)]

private theorem exists_bound_cutField (ε : ℝ) (x₀ : ℝ × ℝ) {a R : ℝ} (ha : 0 < a)
    (hR : 0 < R) : ∃ L, 0 ≤ L ∧ ∀ w, ‖cutField N ε x₀ a R w‖ ≤ L := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ (1 + 4 * R)).exists_bound_of_continuousOn
    (contDiff_force (N := N) ε).continuous.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ (Metric.mem_closedBall_self (by linarith)))
  refine ⟨max (1 + 4 * a) M, le_max_of_le_right hM0, fun w => ?_⟩
  rw [cutField, Prod.norm_def]
  refine max_le ?_ ?_
  · rcases le_or_gt (4 * a) (sq2 w.2) with h | h
    · rw [cut_of_ge ha h, zero_smul, norm_zero]
      exact le_max_of_le_right hM0
    · rw [norm_smul, Real.norm_eq_abs]
      have h1 := abs_cut_le a w.2
      have h2 := norm_sq_le_sq2 w.2
      have h3 := norm_le_one_add_sq ‖w.2‖
      calc |cut a w.2| * ‖w.2‖ ≤ 1 * ‖w.2‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ 1 + 4 * a := by linarith
        _ ≤ _ := le_max_left _ _
  · rcases le_or_gt (4 * R) (sq2 (w.1 - x₀)) with h | h
    · rw [cut_of_ge hR h, zero_smul, norm_zero]
      exact le_max_of_le_right hM0
    · rw [norm_smul, Real.norm_eq_abs]
      have h1 := abs_cut_le R (w.1 - x₀)
      have h2 := norm_sq_le_sq2 (w.1 - x₀)
      have h3 := norm_le_one_add_sq ‖w.1 - x₀‖
      have hmem : w.1 ∈ Metric.closedBall x₀ (1 + 4 * R) := by
        rw [Metric.mem_closedBall, dist_eq_norm]; linarith
      calc |cut R (w.1 - x₀)| * ‖N.force ε w.1‖ ≤ 1 * M :=
            mul_le_mul h1 (hM _ hmem) (norm_nonneg _) zero_le_one
        _ ≤ _ := by rw [one_mul]; exact le_max_right _ _

/-! ### Global forward existence -/

/-- **Global forward existence for a potential bounded below.**  If `W_ε` is bounded below, then
through every state `(x₀, p₀)` there is a trajectory of `H_ε` on `[0, A]`, for every `A ≥ 0`.

Proof: solve the cut-off system, which is `C¹` and bounded, on `[0, A]`.  Along it, as long as
the cutoffs are inactive, the energy `E` is conserved, hence `|p|² ≤ 2(E - inf W)` and
`|x(t) - x₀| ≤ t √(2(E - inf W))`; these bounds keep the cutoffs inactive.  A first-exit-time
argument shows that the cutoffs are never active, so the solution solves Hamilton's equations. -/
theorem exists_microTrajectory_of_bddBelow {ε : ℝ} (hbdd : BddBelow (range (N.pot ε)))
    (x₀ p₀ : ℝ × ℝ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ Θ : N.MicroTrajectory ε A, Θ.x 0 = x₀ ∧ Θ.p 0 = p₀ := by
  obtain ⟨m, hm⟩ := hbdd
  have hm' : ∀ x, m ≤ N.pot ε x := fun x => hm ⟨x, rfl⟩
  set E := N.hamiltonian ε x₀ p₀ with hE
  set P2 := 2 * (E - m) with hP2
  have hP2nn : 0 ≤ P2 := by
    have := hm' x₀
    simp only [hP2, hE, hamiltonian]
    nlinarith [sq_nonneg p₀.1, sq_nonneg p₀.2]
  set a := P2 + 1 with ha_def
  set R := 2 * P2 * A ^ 2 + 1 with hR_def
  have ha : 0 < a := by positivity
  have hR : 0 < R := by positivity
  obtain ⟨L, hL0, hL⟩ := exists_bound_cutField (N := N) ε x₀ ha hR
  obtain ⟨α, hα0, hα⟩ :=
    exists_integralCurve_Icc_plane (contDiff_cutField ε x₀ a R) hL0 hL (x₀, p₀) hA
  have hαc : ContinuousOn α (Icc 0 A) := fun t ht => (hα t ht).continuousWithinAt
  -- the region where the cutoffs are inactive
  set G : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {w | sq2 w.2 < a ∧ sq2 (w.1 - x₀) < R} with hG
  have hGo : IsOpen G :=
    (isOpen_lt (continuous_sq2.comp continuous_snd) continuous_const).inter
      (isOpen_lt (continuous_sq2.comp (continuous_fst.sub continuous_const))
        continuous_const)
  have hfield : ∀ w ∈ G, cutField N ε x₀ a R w = (w.2, N.force ε w.1) := by
    intro w hw
    rw [cutField, cut_of_le ha hw.1.le, cut_of_le hR hw.2.le, one_smul, one_smul]
  have hham : Continuous fun w : (ℝ × ℝ) × (ℝ × ℝ) => N.hamiltonian ε w.1 w.2 :=
    (((continuous_snd.fst.pow 2).add (continuous_snd.snd.pow 2)).div_const 2).add
      ((N.contDiff_pot ε).continuous.comp continuous_fst)
  -- the cutoffs are never active
  have hgood : ∀ t ∈ Icc 0 A, α t ∈ G := by
    by_contra hcon
    push Not at hcon
    set B := Icc 0 A ∩ α ⁻¹' Gᶜ with hB
    have hBc : IsClosed B := hαc.preimage_isClosed_of_isClosed isClosed_Icc hGo.isClosed_compl
    have hBne : B.Nonempty := by
      obtain ⟨t, ht, hn⟩ := hcon
      exact ⟨t, ht, hn⟩
    have hBbdd : BddBelow B := ⟨0, fun t ht => ht.1.1⟩
    set τ := sInf B with hτ
    have hτB : τ ∈ B := hBc.csInf_mem hBne hBbdd
    have hτ0 : 0 ≤ τ := hτB.1.1
    have hτA : τ ≤ A := hτB.1.2
    have hbefore : ∀ s ∈ Ico 0 τ, α s ∈ G := by
      intro s hs
      by_contra hn
      have : τ ≤ s := csInf_le hBbdd ⟨⟨hs.1, hs.2.le.trans hτA⟩, hn⟩
      linarith [hs.2]
    have hder : ∀ s ∈ Ico 0 τ,
        HasDerivWithinAt (fun r => (α r).1) (α s).2 (Ici s) s ∧
          HasDerivWithinAt (fun r => (α r).2) (N.force ε (α s).1) (Ici s) s := by
      intro s hs
      have hsA : s < A := lt_of_lt_of_le hs.2 hτA
      have hnhds : Icc 0 A ∈ 𝓝[Ici s] s :=
        mem_of_superset (Icc_mem_nhdsGE hsA) (Icc_subset_Icc_left hs.1)
      have h := (hα s ⟨hs.1, hsA.le⟩).mono_of_mem_nhdsWithin hnhds
      rw [hfield _ (hbefore s hs)] at h
      exact ⟨hasDerivWithinAt_phase_fst h, hasDerivWithinAt_phase_snd h⟩
    have hαcτ : ContinuousOn α (Icc 0 τ) := hαc.mono (Icc_subset_Icc_right hτA)
    -- energy conservation up to the first exit time
    have hconst := constant_of_has_deriv_right_zero
      (f := fun r => N.hamiltonian ε (α r).1 (α r).2) (hham.comp_continuousOn hαcτ)
      (fun s hs => hasDerivWithinAt_hamiltonian_zero (hder s hs).1 (hder s hs).2)
    have hkin : ∀ r ∈ Icc 0 τ, sq2 (α r).2 ≤ P2 := by
      intro r hr
      have h := hconst r hr
      simp only [hα0] at h
      have := hm' (α r).1
      simp only [hamiltonian] at h
      simp only [sq2, hP2, hE, hamiltonian]
      linarith
    have hnorm : ∀ r ∈ Icc 0 τ, ‖(α r).2‖ ≤ √P2 := by
      intro r hr
      have h := Real.abs_le_sqrt ((norm_sq_le_sq2 _).trans (hkin r hr))
      rwa [abs_norm] at h
    have hpos := norm_image_sub_le_of_norm_deriv_right_le_segment
      (f := fun r => (α r).1) (f' := fun r => (α r).2) (C := √P2)
      (continuous_fst.comp_continuousOn hαcτ) (fun s hs => (hder s hs).1)
      (fun s hs => hnorm s ⟨hs.1, hs.2.le⟩) τ ⟨hτ0, le_rfl⟩
    simp only [hα0, sub_zero] at hpos
    have hsq : ‖(α τ).1 - x₀‖ ^ 2 ≤ P2 * A ^ 2 := by
      calc ‖(α τ).1 - x₀‖ ^ 2 ≤ (√P2 * τ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpos 2
        _ = P2 * τ ^ 2 := by rw [mul_pow, Real.sq_sqrt hP2nn]
        _ ≤ P2 * A ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ0 hτA 2) hP2nn
    have hin : α τ ∈ G := by
      refine ⟨?_, ?_⟩
      · have := hkin τ ⟨hτ0, le_rfl⟩
        linarith
      · have := sq2_le_two_norm_sq ((α τ).1 - x₀)
        nlinarith
    exact hτB.2 hin
  refine ⟨⟨fun t => (α t).1, fun t => (α t).2, fun t ht => ?_, fun t ht => ?_⟩, ?_, ?_⟩
  · have h := hα t ht
    rw [hfield _ (hgood t ht)] at h
    exact hasDerivWithinAt_phase_fst h
  · have h := hα t ht
    rw [hfield _ (hgood t ht)] at h
    exact hasDerivWithinAt_phase_snd h
  · simp [hα0]
  · simp [hα0]

/-! ### Uniqueness of the microscopic trajectory -/

/-- The microscopic force is the negative gradient, written through the total derivative. -/
theorem force_eq_fderiv (ε : ℝ) (x : ℝ × ℝ) :
    N.force ε x = (-(fderiv ℝ (N.pot ε) x (1, 0)), -(fderiv ℝ (N.pot ε) x (0, 1))) := by
  have hW : Differentiable ℝ (N.pot ε) := (N.contDiff_pot ε).differentiable (by norm_num)
  rw [force, (hasDerivAt_partial_fst hW x).deriv, (hasDerivAt_partial_snd hW x).deriv]

/-- **Uniqueness of the microscopic Hamiltonian trajectory.**  Two trajectories of `H_ε` with the
same initial state agree wherever both are defined.  (The vector field `(x, p) ↦ (p, -∇W_ε(x))`
is `C¹`, hence Lipschitz on bounded sets.) -/
theorem MicroTrajectory.eq_of_initial {ε S₁ S₂ : ℝ} (Θ₁ : N.MicroTrajectory ε S₁)
    (Θ₂ : N.MicroTrajectory ε S₂) (hx : Θ₁.x 0 = Θ₂.x 0) (hp : Θ₁.p 0 = Θ₂.p 0) :
    ∀ t ∈ Icc (0 : ℝ) (min S₁ S₂), Θ₁.x t = Θ₂.x t ∧ Θ₁.p t = Θ₂.p t := by
  set b := min S₁ S₂ with hbdef
  have hb₁ : b ≤ S₁ := min_le_left _ _
  have hb₂ : b ≤ S₂ := min_le_right _ _
  set v : ℝ → (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ) := fun _ z => (z.2, N.force ε z.1)
  have hv : ContDiff ℝ 1 (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (z.2, N.force ε z.1)) :=
    contDiff_snd.prodMk ((contDiff_force ε).comp contDiff_fst)
  set f₁ : ℝ → (ℝ × ℝ) × (ℝ × ℝ) := fun t => (Θ₁.x t, Θ₁.p t) with hf₁
  set f₂ : ℝ → (ℝ × ℝ) × (ℝ × ℝ) := fun t => (Θ₂.x t, Θ₂.p t) with hf₂
  have hd₁ : ∀ t ∈ Icc (0 : ℝ) S₁, HasDerivWithinAt f₁ (v t (f₁ t)) (Icc (0 : ℝ) S₁) t :=
    fun t ht => (Θ₁.ode_pos t ht).prodMk (Θ₁.ode_mom t ht)
  have hd₂ : ∀ t ∈ Icc (0 : ℝ) S₂, HasDerivWithinAt f₂ (v t (f₂ t)) (Icc (0 : ℝ) S₂) t :=
    fun t ht => (Θ₂.ode_pos t ht).prodMk (Θ₂.ode_mom t ht)
  have hc₁ : ContinuousOn f₁ (Icc (0 : ℝ) b) :=
    fun t ht => ((hd₁ t ⟨ht.1, ht.2.trans hb₁⟩).continuousWithinAt).mono
      (Icc_subset_Icc le_rfl hb₁)
  have hc₂ : ContinuousOn f₂ (Icc (0 : ℝ) b) :=
    fun t ht => ((hd₂ t ⟨ht.1, ht.2.trans hb₂⟩).continuousWithinAt).mono
      (Icc_subset_Icc le_rfl hb₂)
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₁
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₂
  set M := max C₁ C₂ with hMdef
  obtain ⟨KL, hKL⟩ := (hv.locallyLipschitz.locallyLipschitzOn (s := Metric.closedBall 0 M))
    |>.exists_lipschitzOnWith_of_compact (isCompact_closedBall 0 M)
  have hIci : ∀ {S : ℝ} {t : ℝ}, t ∈ Ico (0 : ℝ) b → b ≤ S →
      Icc (0 : ℝ) S ∈ 𝓝[Ici t] t := by
    intro S t ht hbS
    exact mem_of_superset (Icc_mem_nhdsGE (lt_of_lt_of_le ht.2 hbS))
      (Icc_subset_Icc ht.1 le_rfl)
  have heq := ODE_solution_unique_of_mem_Icc_right (v := v) (s := fun _ => Metric.closedBall 0 M)
    (K := KL) (fun _ _ => hKL) hc₁
    (fun t ht => (hd₁ t ⟨ht.1, ht.2.le.trans hb₁⟩).mono_of_mem_nhdsWithin (hIci ht hb₁))
    (fun t ht => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hC₁ t (Ico_subset_Icc_self ht)).trans (le_max_left _ _)) hc₂
    (fun t ht => (hd₂ t ⟨ht.1, ht.2.le.trans hb₂⟩).mono_of_mem_nhdsWithin (hIci ht hb₂))
    (fun t ht => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hC₂ t (Ico_subset_Icc_self ht)).trans (le_max_right _ _))
    (show f₁ 0 = f₂ 0 by simp only [hf₁, hf₂, hx, hp])
  intro t ht
  have := heq ht
  simp only [hf₁, hf₂, Prod.mk.injEq] at this
  exact this

/-! ### Restarting and reversing a trajectory -/

/-- **A trajectory restarted at time `a`**: `t ↦ (x(a + t), p(a + t))` on `[0, S']`, for
`[a, a + S'] ⊆ [0, S]`. -/
def MicroTrajectory.shift {ε S : ℝ} (Θ : N.MicroTrajectory ε S) (a S' : ℝ) (ha : 0 ≤ a)
    (hS : a + S' ≤ S) : N.MicroTrajectory ε S' where
  x t := Θ.x (a + t)
  p t := Θ.p (a + t)
  ode_pos t ht := by
    have hmem : a + t ∈ Icc (0 : ℝ) S := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmaps : MapsTo (fun r : ℝ => a + r) (Icc (0 : ℝ) S') (Icc (0 : ℝ) S) :=
      fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have h := (Θ.ode_pos (a + t) hmem).scomp t ((hasDerivAt_id t).const_add a).hasDerivWithinAt
      hmaps
    simp only [one_smul] at h
    exact h
  ode_mom t ht := by
    have hmem : a + t ∈ Icc (0 : ℝ) S := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmaps : MapsTo (fun r : ℝ => a + r) (Icc (0 : ℝ) S') (Icc (0 : ℝ) S) :=
      fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have h := (Θ.ode_mom (a + t) hmem).scomp t ((hasDerivAt_id t).const_add a).hasDerivWithinAt
      hmaps
    simp only [one_smul] at h
    exact h

@[simp] theorem MicroTrajectory.shift_x {ε S : ℝ} (Θ : N.MicroTrajectory ε S) (a S' : ℝ)
    (ha : 0 ≤ a) (hS : a + S' ≤ S) (t : ℝ) : (Θ.shift a S' ha hS).x t = Θ.x (a + t) := rfl

@[simp] theorem MicroTrajectory.shift_p {ε S : ℝ} (Θ : N.MicroTrajectory ε S) (a S' : ℝ)
    (ha : 0 ≤ a) (hS : a + S' ≤ S) (t : ℝ) : (Θ.shift a S' ha hS).p t = Θ.p (a + t) := rfl

/-- **Time reversal of a microscopic trajectory.**  Since `H_ε` is even in the momentum, the
reversed curve `t ↦ (x(c - t), -p(c - t))` solves Hamilton's equations again; it is a trajectory
on `[0, S']` whenever `[c - S', c] ⊆ [0, S]`.  This is `Φ^ε_t ∘ ρ̃ = ρ̃ ∘ Φ^ε_{-t}`. -/
def MicroTrajectory.reverse {ε S : ℝ} (Θ : N.MicroTrajectory ε S) (c S' : ℝ) (hc : S' ≤ c)
    (hcS : c ≤ S) : N.MicroTrajectory ε S' where
  x t := Θ.x (c - t)
  p t := -Θ.p (c - t)
  ode_pos t ht := by
    have hmem : c - t ∈ Icc (0 : ℝ) S := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hmaps : MapsTo (fun r : ℝ => c - r) (Icc (0 : ℝ) S') (Icc (0 : ℝ) S) :=
      fun r hr => ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have h := (Θ.ode_pos (c - t) hmem).scomp t ((hasDerivAt_id t).const_sub c).hasDerivWithinAt
      hmaps
    simp only [neg_smul, one_smul] at h
    exact h
  ode_mom t ht := by
    have hmem : c - t ∈ Icc (0 : ℝ) S := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hmaps : MapsTo (fun r : ℝ => c - r) (Icc (0 : ℝ) S') (Icc (0 : ℝ) S) :=
      fun r hr => ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have h := ((Θ.ode_mom (c - t) hmem).scomp t
      ((hasDerivAt_id t).const_sub c).hasDerivWithinAt hmaps).neg
    simp only [neg_smul, one_smul, neg_neg] at h
    exact h

@[simp] theorem MicroTrajectory.reverse_x {ε S : ℝ} (Θ : N.MicroTrajectory ε S) (c S' : ℝ)
    (hc : S' ≤ c) (hcS : c ≤ S) (t : ℝ) : (Θ.reverse c S' hc hcS).x t = Θ.x (c - t) := rfl

@[simp] theorem MicroTrajectory.reverse_p {ε S : ℝ} (Θ : N.MicroTrajectory ε S) (c S' : ℝ)
    (hc : S' ≤ c) (hcS : c ≤ S) (t : ℝ) : (Θ.reverse c S' hc hcS).p t = -Θ.p (c - t) := rfl

/-! ### The flow `Φ^ε_t` -/

variable (N)

/-- The momentum reversal `ρ̃(x, ξ) = (x, -ξ)` of the phase space `ℝ² × ℝ²`. -/
def reversal (z : (ℝ × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ) := (z.1, -z.2)

@[simp] theorem reversal_fst (z : (ℝ × ℝ) × (ℝ × ℝ)) : (reversal z).1 = z.1 := rfl
@[simp] theorem reversal_snd (z : (ℝ × ℝ) × (ℝ × ℝ)) : (reversal z).2 = -z.2 := rfl
@[simp] theorem reversal_reversal (z : (ℝ × ℝ) × (ℝ × ℝ)) : reversal (reversal z) = z := by
  simp [reversal]

/-- The forward flow: the state at time `t ≥ 0` of the trajectory through `z` on `[0, t]`
supplied by `exists_microTrajectory_of_bddBelow`. -/
noncomputable def fwdFlow (ε t : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((exists_microTrajectory_of_bddBelow (N := N) (N.pot_bddBelow ε) z.1 z.2
      (le_max_right t 0)).choose.x t,
    (exists_microTrajectory_of_bddBelow (N := N) (N.pot_bddBelow ε) z.1 z.2
      (le_max_right t 0)).choose.p t)

/-- **The flow `Φ^ε_t` of `H_ε(x, ξ) = ½|ξ|² + W_ε(x)` on `ℝ² × ℝ²`** (Definition IX.3(i)).
It is complete because `W_ε` is bounded below (`exists_microTrajectory_of_bddBelow`) and unique
because `W_ε` is `C²` (`MicroTrajectory.eq_of_initial`).  For `t < 0` it is defined through the
time reversal, `Φ_{-t} = ρ̃ ∘ Φ_t ∘ ρ̃`. -/
noncomputable def flow (ε t : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ) :=
  if 0 ≤ t then N.fwdFlow ε t z else reversal (N.fwdFlow ε (-t) (reversal z))

variable {N}

theorem flow_of_nonneg {ε t : ℝ} (ht : 0 ≤ t) (z : (ℝ × ℝ) × (ℝ × ℝ)) :
    N.flow ε t z = N.fwdFlow ε t z := if_pos ht

/-- **Every trajectory is the flow through its initial state.** -/
theorem flow_eq_of_traj {ε S : ℝ} (Θ : N.MicroTrajectory ε S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    N.flow ε t (Θ.x 0, Θ.p 0) = (Θ.x t, Θ.p t) := by
  rw [flow_of_nonneg ht.1, fwdFlow]
  have hspec := (exists_microTrajectory_of_bddBelow (N := N) (N.pot_bddBelow ε) (Θ.x 0) (Θ.p 0)
      (le_max_right t 0)).choose_spec
  have h := MicroTrajectory.eq_of_initial _ Θ hspec.1 hspec.2 t
    ⟨ht.1, le_min (le_max_left _ _) ht.2⟩
  rw [h.1, h.2]

/-- The flow at time `0` is the identity. -/
@[simp] theorem flow_zero (ε : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) : N.flow ε 0 z = z := by
  obtain ⟨Θ, hx, hp⟩ := exists_microTrajectory_of_bddBelow (N := N) (N.pot_bddBelow ε) z.1 z.2
    le_rfl
  have h := flow_eq_of_traj Θ (t := 0) ⟨le_rfl, le_rfl⟩
  rw [hx, hp] at h
  simpa using h

variable (N) in
/-- **The flow through `z`, restricted to `[0, S]`, is a trajectory of `H_ε`.** -/
noncomputable def flowTraj (ε : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) (S : ℝ) : N.MicroTrajectory ε S where
  x t := (N.flow ε t z).1
  p t := (N.flow ε t z).2
  ode_pos t ht := by
    obtain ⟨Θ, hx, hp⟩ := exists_microTrajectory_of_bddBelow (N := N) (N.pot_bddBelow ε) z.1 z.2
      (ht.1.trans ht.2)
    have heq : ∀ s ∈ Icc (0 : ℝ) S, N.flow ε s z = (Θ.x s, Θ.p s) := by
      intro s hs
      have h := flow_eq_of_traj Θ hs
      rwa [hx, hp] at h
    have h := Θ.ode_pos t ht
    rw [show Θ.p t = (N.flow ε t z).2 by rw [heq t ht]] at h
    exact h.congr (fun s hs => by rw [heq s hs]) (by rw [heq t ht])
  ode_mom t ht := by
    obtain ⟨Θ, hx, hp⟩ := exists_microTrajectory_of_bddBelow (N := N) (N.pot_bddBelow ε) z.1 z.2
      (ht.1.trans ht.2)
    have heq : ∀ s ∈ Icc (0 : ℝ) S, N.flow ε s z = (Θ.x s, Θ.p s) := by
      intro s hs
      have h := flow_eq_of_traj Θ hs
      rwa [hx, hp] at h
    have h := Θ.ode_mom t ht
    rw [show Θ.x t = (N.flow ε t z).1 by rw [heq t ht]] at h
    exact h.congr (fun s hs => by rw [heq s hs]) (by rw [heq t ht])

@[simp] theorem flowTraj_x (ε : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) (S t : ℝ) :
    (N.flowTraj ε z S).x t = (N.flow ε t z).1 := rfl

@[simp] theorem flowTraj_p (ε : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) (S t : ℝ) :
    (N.flowTraj ε z S).p t = (N.flow ε t z).2 := rfl

theorem flowTraj_x_zero (ε : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) (S : ℝ) :
    (N.flowTraj ε z S).x 0 = z.1 := by simp

theorem flowTraj_p_zero (ε : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) (S : ℝ) :
    (N.flowTraj ε z S).p 0 = z.2 := by simp

/-- **Every trajectory of `H_ε` is the flow through its initial state**, componentwise. -/
theorem MicroTrajectory.eq_flow {ε S : ℝ} (Θ : N.MicroTrajectory ε S) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) S) :
    Θ.x t = (N.flow ε t (Θ.x 0, Θ.p 0)).1 ∧ Θ.p t = (N.flow ε t (Θ.x 0, Θ.p 0)).2 := by
  rw [flow_eq_of_traj Θ ht]
  exact ⟨rfl, rfl⟩

/-- **The flow property** `Φ_{s+t} = Φ_t ∘ Φ_s` for `s, t ≥ 0`. -/
theorem flow_add (ε : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (z : (ℝ × ℝ) × (ℝ × ℝ)) :
    N.flow ε (s + t) z = N.flow ε t (N.flow ε s z) := by
  have h := flow_eq_of_traj ((N.flowTraj ε z (s + t)).shift s t hs le_rfl) (t := t)
    ⟨ht, le_rfl⟩
  simp only [MicroTrajectory.shift_x, MicroTrajectory.shift_p, flowTraj_x, flowTraj_p,
    add_zero, Prod.mk.eta] at h
  exact h.symm

/-- **Time reversal**: `Φ_{-t} = ρ̃ ∘ Φ_t ∘ ρ̃` for `t ≥ 0`. -/
theorem flow_neg (ε : ℝ) {t : ℝ} (ht : 0 ≤ t) (z : (ℝ × ℝ) × (ℝ × ℝ)) :
    N.flow ε (-t) z = reversal (N.flow ε t (reversal z)) := by
  rcases ht.lt_or_eq with ht | ht
  · rw [flow, if_neg (by linarith), neg_neg, flow_of_nonneg ht.le]
  · subst ht
    simp

/-- **Reversibility of the flow**: running the reversed final state for the same time `b` returns
the reversed initial state, `Φ_b(ρ̃ Φ_b z) = ρ̃ z`.  This is `Φ^ε_t ∘ ρ̃ = ρ̃ ∘ Φ^ε_{-t}`, since
`H_ε` is even in the momentum. -/
theorem flow_reversal (ε : ℝ) {b : ℝ} (hb : 0 ≤ b) (z : (ℝ × ℝ) × (ℝ × ℝ)) :
    N.flow ε b (reversal (N.flow ε b z)) = reversal z := by
  have h := flow_eq_of_traj ((N.flowTraj ε z b).reverse b b le_rfl le_rfl) (t := b)
    ⟨hb, le_rfl⟩
  simp only [MicroTrajectory.reverse_x, MicroTrajectory.reverse_p, flowTraj_x, flowTraj_p,
    sub_zero, sub_self, flow_zero] at h
  exact h

/-- The flow through `z` has derivative `(ξ, -∇W_ε(x))` within `[0, S]` at every `t ∈ [0, S]`. -/
theorem hasDerivWithinAt_flow_Icc (ε : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) {S t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) S) :
    HasDerivWithinAt (fun s => N.flow ε s z) ((N.flow ε t z).2, N.force ε (N.flow ε t z).1)
      (Icc (0 : ℝ) S) t := by
  have h := ((N.flowTraj ε z S).ode_pos t ht).prodMk ((N.flowTraj ε z S).ode_mom t ht)
  simpa only [flowTraj_x, flowTraj_p, Prod.mk.eta] using h

/-- **The flow solves Hamilton's equations at every time `t ∈ ℝ`**:
`d/dt Φ^ε_t(z) = (ξ(t), -∇W_ε(x(t)))`.  For `t < 0` this is the time reversal of the forward
flow, and at `t = 0` the two one-sided derivatives agree. -/
theorem hasDerivAt_flow (ε : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) (t : ℝ) :
    HasDerivAt (fun s => N.flow ε s z) ((N.flow ε t z).2, N.force ε (N.flow ε t z).1) t := by
  -- the reversal `ρ̃` as a continuous linear map
  set ρ : ((ℝ × ℝ) × (ℝ × ℝ)) →L[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) :=
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)).prod
      (-(ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))) with hρ
  have hρapp : ∀ w, ρ w = reversal w := fun w => rfl
  set w := reversal z with hw
  -- forward derivatives
  have hfwd : ∀ (y : (ℝ × ℝ) × (ℝ × ℝ)) {u : ℝ}, 0 ≤ u →
      HasDerivWithinAt (fun s => N.flow ε s y) ((N.flow ε u y).2, N.force ε (N.flow ε u y).1)
        (Ici u) u := by
    intro y u hu
    exact (hasDerivWithinAt_flow_Icc ε y (S := u + 1) ⟨hu, by linarith⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE (by linarith : u < u + 1)) (Icc_subset_Icc hu le_rfl))
  have hfwd' : ∀ (y : (ℝ × ℝ) × (ℝ × ℝ)) {u : ℝ}, 0 < u →
      HasDerivAt (fun s => N.flow ε s y) ((N.flow ε u y).2, N.force ε (N.flow ε u y).1) u := by
    intro y u hu
    exact (hasDerivWithinAt_flow_Icc ε y (S := u + 1) ⟨hu.le, by linarith⟩).hasDerivAt
      (Icc_mem_nhds hu (by linarith))
  -- the flow at nonpositive times is the reversed forward flow
  have hneg : ∀ s ≤ 0, N.flow ε s z = ρ (N.flow ε (-s) w) := by
    intro s hs
    have h := flow_neg (N := N) ε (t := -s) (by linarith) z
    rw [neg_neg] at h
    rw [h, hρapp]
  -- the value of the derivative of the reversed forward flow
  have hval : ∀ s ≤ 0, ρ ((-1 : ℝ) • ((N.flow ε (-s) w).2, N.force ε (N.flow ε (-s) w).1)) =
      ((N.flow ε s z).2, N.force ε (N.flow ε s z).1) := by
    intro s hs
    rw [hneg s hs, hρapp, hρapp]
    simp [reversal]
  rcases lt_trichotomy t 0 with ht | ht | ht
  · -- negative times
    have h := ρ.hasFDerivAt.comp_hasDerivAt t ((hfwd' w (u := -t) (by linarith)).scomp t
      (hasDerivAt_neg t))
    rw [hval t ht.le] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact hneg s (le_of_lt hs)
  · -- `t = 0`: the one-sided derivatives agree
    subst ht
    have hr := hfwd z (u := 0) le_rfl
    have hl0 := hfwd w (u := -0) (by simp)
    have hl := ρ.hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ)
      (hl0.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt
        (s := Iic (0 : ℝ)) (fun r hr => by simpa using hr))
    rw [hval 0 le_rfl] at hl
    have hl' : HasDerivWithinAt (fun s => N.flow ε s z)
        ((N.flow ε 0 z).2, N.force ε (N.flow ε 0 z).1) (Iic 0) 0 :=
      hl.congr (fun s hs => hneg s hs) (hneg 0 le_rfl)
    have hu := hl'.union hr
    rw [Iic_union_Ici] at hu
    exact hu.hasDerivAt univ_mem
  · exact hfwd' z ht

/-- **Energy conservation along the flow.** -/
theorem hamiltonian_flow (ε : ℝ) {t : ℝ} (ht : 0 ≤ t) (z : (ℝ × ℝ) × (ℝ × ℝ)) :
    N.hamiltonian ε (N.flow ε t z).1 (N.flow ε t z).2 = N.hamiltonian ε z.1 z.2 := by
  have h := (N.flowTraj ε z t).hamiltonian_eq
    ((N.contDiff_pot ε).differentiable (by norm_num)) ⟨ht, le_rfl⟩
  simpa using h

end ThinHamiltonianNetwork

end HamiltonianMetricGraphs
