/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.ShellCycles
import HamiltonianMetricGraphs.Bifurcation

/-!
# The retrace involution (Lemma VIII.3)

Fix a shell-regular energy `E`.  The flight departing an admissible end `η ∈ G_E` at the speed
`r_η(E)` lands, after the flight time `t_E(η) > 0`, at an end `κ_E(η)` of the same edge, with
nonzero momentum pointing out of the edge, so `κ_E(η) ∈ G_E` and the landing speed is
`r_{κ_E(η)}(E)`.  Lemma VIII.3 of the paper (`lem:retrace`) states:

  for every shell-regular `E`, the edge-flight map `κ_E : G_E → G_E` satisfies `κ_E² = id` and
  `t_E(κ_E(η)) = t_E(η)` for all `η ∈ G_E`.  Moreover `κ_E` maps each end to an end of the same
  edge.  Hence, on the admissible ends of each edge, it is either the identity or a
  transposition.

`Structure.lean` proves the phase-space form of the retrace involution for the *germ-and-speed*
map `retraceStep` (`retraceStep_exact`, `retraceStep_involutive`).  This file states the lemma in
its printed, end-level form.

## Main definitions

* `retraceEnd E η = κ_E(η)`: the end at which the flight departing `η` at speed `r_η(E)` lands
  (`(retraceStep η (germSpeed η E)).1`);
* `retraceMap hE : G_E → G_E`, the edge-flight map as a self-map of the admissible ends;
* `retracePerm hE`: the same map as an involutive permutation of `G_E`.

## Main results

* `retraceStep_snd_eq_germSpeed`: the landing speed is `r_{κ_E(η)}(E)`;
* `retraceEnd_mem_allowedGerms`: `κ_E(η) ∈ G_E`;
* `retraceEnd_retraceEnd`: `κ_E(κ_E(η)) = η`;
* `flightTime_retraceEnd`: `t_E(κ_E(η)) = t_E(η)`;
* `retraceEnd_edge`: `κ_E(η)` lies on the edge of `η`;
* `retraceEnd_eq_self_or_flip`: `κ_E(η)` is `η` or the other end `(e, !b)` of its edge;
* `retrace_edge_id_or_swap`: on the admissible ends of each edge `e`, `κ_E` is the identity, or
  both ends of `e` are admissible and `κ_E` is their transposition;
* `retrace_lemma`: **Lemma VIII.3**, all of the above in one statement.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- **The edge-flight map** `κ_E` of Lemma VIII.3, on ends: the end at which the flight departing
`η` at the speed `r_η(E) = germSpeed η E` lands. -/
noncomputable def retraceEnd (E : ℝ) (η : Γ.EdgeEnd) : Γ.EdgeEnd :=
  (V.retraceStep η (V.germSpeed η E)).1

theorem retraceEnd_def (E : ℝ) (η : Γ.EdgeEnd) :
    V.retraceEnd E η = (V.retraceStep η (V.germSpeed η E)).1 := rfl

/-- `κ_E(η)` lies on the edge of `η`. -/
@[simp] theorem retraceEnd_edge (E : ℝ) (η : Γ.EdgeEnd) : (V.retraceEnd E η).1 = η.1 := rfl

/-- `κ_E(η) ∈ G_E`. -/
theorem retraceEnd_mem_allowedGerms {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) : V.retraceEnd E η ∈ V.allowedGerms E :=
  V.retraceStep_fst_mem_allowedGerms hE hη

/-- **The landing speed is `r_{κ_E(η)}(E)`.** -/
theorem retraceStep_snd_eq_germSpeed {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) :
    (V.retraceStep η (V.germSpeed η E)).2 = V.germSpeed (V.retraceEnd E η) E := by
  have hr := V.germSpeed_mem_regularSpeeds hE hη
  have hbdd := V.bddAbove_departurePoint_germSpeed hE hη
  have h2 := V.departureEnergy_retraceStep hr hbdd
  rw [V.departureEnergy_germSpeed hη] at h2
  have h3 := V.germSpeed_departureEnergy (V.retraceStep η (V.germSpeed η E)).1
    (V.retraceStep_pos η (V.germSpeed η E)).le
  rw [h2] at h3
  exact h3.symm

/-- **`κ_E² = id`** on `G_E`. -/
theorem retraceEnd_retraceEnd {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) : V.retraceEnd E (V.retraceEnd E η) = η := by
  have hr := V.germSpeed_mem_regularSpeeds hE hη
  have hbdd := V.bddAbove_departurePoint_germSpeed hE hη
  have h := V.retraceStep_involutive hr hbdd
  rw [retraceEnd_def, ← V.retraceStep_snd_eq_germSpeed hE hη]
  exact congrArg Prod.fst h

/-- **`t_E(κ_E(η)) = t_E(η)`.** -/
theorem flightTime_retraceEnd {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) : V.flightTime E (V.retraceEnd E η) = V.flightTime E η := by
  have hr := V.germSpeed_mem_regularSpeeds hE hη
  have hbdd := V.bddAbove_departurePoint_germSpeed hE hη
  have hq := V.retraceStep_mem_regularSpeeds hr hbdd
  obtain ⟨-, hsup, -⟩ := V.retraceStep_exact hr hbdd
  rw [flightTime, ← V.retraceStep_snd_eq_germSpeed hE hη, retraceEnd_def,
    V.departureDurationTotal_of_mem hq, hsup, V.flightTime_eq_sSup hE hη]

/-- `κ_E(η)` is `η` itself or the other end of its edge. -/
theorem retraceEnd_eq_self_or_flip (E : ℝ) (η : Γ.EdgeEnd) :
    V.retraceEnd E η = η ∨ V.retraceEnd E η = (η.1, !η.2) := by
  have he : (V.retraceEnd E η).1 = η.1 := rfl
  generalize V.retraceEnd E η = ζ at he ⊢
  rcases η with ⟨e, b⟩
  rcases ζ with ⟨e', b'⟩
  simp only at he
  subst he
  cases b <;> cases b' <;> simp

/-- The edge-flight map as a self-map of the admissible ends. -/
noncomputable def retraceMap {E : ℝ} (hE : V.ShellRegular E) :
    V.allowedGerms E → V.allowedGerms E :=
  fun η => ⟨V.retraceEnd E η, V.retraceEnd_mem_allowedGerms hE η.2⟩

@[simp] theorem retraceMap_coe {E : ℝ} (hE : V.ShellRegular E) (η : V.allowedGerms E) :
    ((V.retraceMap hE η : V.allowedGerms E) : Γ.EdgeEnd) = V.retraceEnd E η := rfl

theorem retraceMap_involutive {E : ℝ} (hE : V.ShellRegular E) :
    Function.Involutive (V.retraceMap hE) :=
  fun η => Subtype.ext (V.retraceEnd_retraceEnd hE η.2)

/-- The edge-flight map as an (involutive) permutation of `G_E`. -/
noncomputable def retracePerm {E : ℝ} (hE : V.ShellRegular E) : Equiv.Perm (V.allowedGerms E) :=
  (V.retraceMap_involutive hE).toPerm

@[simp] theorem retracePerm_coe {E : ℝ} (hE : V.ShellRegular E) (η : V.allowedGerms E) :
    ((V.retracePerm hE η : V.allowedGerms E) : Γ.EdgeEnd) = V.retraceEnd E η := rfl

/-- **On the admissible ends of each edge, `κ_E` is the identity or a transposition.**  Either
`κ_E` fixes every admissible end of `e`, or both ends `(e, false)` and `(e, true)` of `e` are
admissible, they are distinct, and `κ_E` acts on the admissible ends of `e` as their
transposition. -/
theorem retrace_edge_id_or_swap {E : ℝ} (hE : V.ShellRegular E) (e : Γ.Edge) :
    (∀ η : V.allowedGerms E, (η : Γ.EdgeEnd).1 = e → V.retracePerm hE η = η) ∨
      ∃ (η₀ η₁ : V.allowedGerms E), (η₀ : Γ.EdgeEnd) = (e, false) ∧
        (η₁ : Γ.EdgeEnd) = (e, true) ∧ η₀ ≠ η₁ ∧
        ∀ η : V.allowedGerms E, (η : Γ.EdgeEnd).1 = e →
          V.retracePerm hE η = Equiv.swap η₀ η₁ η := by
  by_cases hfix : ∀ η : V.allowedGerms E, (η : Γ.EdgeEnd).1 = e → V.retracePerm hE η = η
  · exact Or.inl hfix
  right
  simp only [not_forall] at hfix
  obtain ⟨ξ, hξe, hξ⟩ := hfix
  -- `κ_E` moves `ξ`, so it sends it to the other end of `e`
  have hflip : V.retraceEnd E ξ = ((ξ : Γ.EdgeEnd).1, !(ξ : Γ.EdgeEnd).2) := by
    rcases V.retraceEnd_eq_self_or_flip E ξ with h | h
    · exact absurd (Subtype.ext h) hξ
    · exact h
  have hξ' : V.retraceEnd E ξ ∈ V.allowedGerms E := V.retraceEnd_mem_allowedGerms hE ξ.2
  -- name the two ends of `e`, both admissible
  have hmem : ∀ b : Bool, ((e, b) : Γ.EdgeEnd) ∈ V.allowedGerms E := by
    intro b
    obtain ⟨⟨e', b'⟩, hξa⟩ := ξ
    simp only at hξe hflip hξ'
    subst hξe
    rcases Bool.eq_or_eq_not b b' with h | h
    · rw [h]; exact hξa
    · rw [h, ← hflip]; exact hξ'
  -- `κ_E` flips every admissible end of `e`
  have hflipAll : ∀ b : Bool, V.retraceEnd E (e, b) = (e, !b) := by
    have hξb : (ξ : Γ.EdgeEnd) = (e, (ξ : Γ.EdgeEnd).2) := Prod.ext hξe rfl
    intro b
    rcases Bool.eq_or_eq_not b (ξ : Γ.EdgeEnd).2 with h | h
    · rw [h, ← hξb, hflip, hξe]
    · have hinv := V.retraceEnd_retraceEnd hE ξ.2
      rw [hflip] at hinv
      rw [h, Bool.not_not, ← hξe, hinv]
  refine ⟨⟨(e, false), hmem false⟩, ⟨(e, true), hmem true⟩, rfl, rfl, ?_, ?_⟩
  · intro h
    have := congrArg (fun x : V.allowedGerms E => (x : Γ.EdgeEnd).2) h
    simp at this
  · rintro ⟨⟨e', b⟩, hη⟩ he
    simp only at he
    subst he
    apply Subtype.ext
    rw [retracePerm_coe, hflipAll b]
    cases b
    · rw [Equiv.swap_apply_left]; rfl
    · rw [Equiv.swap_apply_right]; rfl

/-- **Lemma VIII.3 (retrace involution).**  For every shell-regular energy `E`, the edge-flight
map `κ_E : G_E → G_E` (`retraceMap hE`, on ends `retraceEnd E`) satisfies

* `κ_E(η) ∈ G_E`, and the landing speed of the flight departing `η` is `r_{κ_E(η)}(E)`;
* `κ_E² = id`;
* `t_E(κ_E(η)) = t_E(η)` for all `η ∈ G_E`;
* `κ_E` maps each end to an end of the same edge;
* hence, on the admissible ends of each edge, `κ_E` is either the identity or the transposition
  of the two ends of that edge. -/
theorem retrace_lemma {E : ℝ} (hE : V.ShellRegular E) :
    (∀ η ∈ V.allowedGerms E, V.retraceEnd E η ∈ V.allowedGerms E ∧
        (V.retraceStep η (V.germSpeed η E)).2 = V.germSpeed (V.retraceEnd E η) E) ∧
      Function.Involutive (V.retraceMap hE) ∧
      (∀ η ∈ V.allowedGerms E, V.retraceEnd E (V.retraceEnd E η) = η) ∧
      (∀ η ∈ V.allowedGerms E, V.flightTime E (V.retraceEnd E η) = V.flightTime E η) ∧
      (∀ η : Γ.EdgeEnd, (V.retraceEnd E η).1 = η.1) ∧
      ∀ e : Γ.Edge,
        (∀ η : V.allowedGerms E, (η : Γ.EdgeEnd).1 = e → V.retracePerm hE η = η) ∨
          ∃ (η₀ η₁ : V.allowedGerms E), (η₀ : Γ.EdgeEnd) = (e, false) ∧
            (η₁ : Γ.EdgeEnd) = (e, true) ∧ η₀ ≠ η₁ ∧
            ∀ η : V.allowedGerms E, (η : Γ.EdgeEnd).1 = e →
              V.retracePerm hE η = Equiv.swap η₀ η₁ η :=
  ⟨fun _ hη => ⟨V.retraceEnd_mem_allowedGerms hE hη, V.retraceStep_snd_eq_germSpeed hE hη⟩,
    V.retraceMap_involutive hE,
    fun _ hη => V.retraceEnd_retraceEnd hE hη,
    fun _ hη => V.flightTime_retraceEnd hE hη,
    V.retraceEnd_edge E,
    V.retrace_edge_id_or_swap hE⟩

end MechanicalPotential

end HamiltonianMetricGraphs
