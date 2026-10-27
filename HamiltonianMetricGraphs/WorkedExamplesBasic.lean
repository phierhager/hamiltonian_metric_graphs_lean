/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.RetraceExact
import HamiltonianMetricGraphs.ShellMeasure
import HamiltonianMetricGraphs.VertexLawExact
import HamiltonianMetricGraphs.Realization.FreeGraphTrajectory

/-!
# Tools for the worked examples of Section XI

The examples of Section XI of the paper compute, for explicit graphs, potentials and vertex laws,
the end permutation `Π_E = F_E ∘ κ_E` of a shell-regular energy `E` (Definition VIII.4,
`germStep`, `shellGermPerm`), its cycles (`germCycle`, `germCycles`), their periods
`T_c(E) = ∑_{η ∈ c} t_E(η)` (`cyclePeriod`) and the shell mass (14).  This file collects the
general facts the examples share.

* `PermutationLaw.toBorelScattering` (of `VertexLawExact.lean`) makes a speed-independent
  permutation vertex law — *not* necessarily involutive; the cyclic laws of Sec. XI are not — a
  Borel vertex datum of the paper; `speedEndpoint_toBorelScattering` and
  `isReversible_toBorelScattering_iff` compute its fixed-speed law and its reversibility.
* `card_shellOrbits_eq_card_germCycles`: the number of periodic orbits on `Σ_E` (the distinct
  `shellOrbit`s of Theorem VIII.5) is the number of cycles of `Π_E`.
* `germStep_eq_speedEndpoint`, `germStep_permutationLaw`: `Π_E(η) = F_{v}(κ_E(η), r)` with the
  fixed-speed vertex permutation at the landing speed `r = r_{κ_E(η)}(E)`; for a permutation law
  simply `Π_E(η) = F(κ_E(η))`.
* `retraceEnd_of_forall_lt`, `retraceEnd_of_exists_gt`: `κ_E(η)` is the opposite end when the
  potential stays below `E` on the edge, and `η` itself when it exceeds `E` somewhere.
* `flightTime_of_extension_eq_zero`: on an edge where the potential vanishes,
  `t_E(η) = ℓ_e / √(2E)`.
* `zeroPotential_*`: for `V ≡ 0`, every `E > 0` is shell-regular, every end is admissible,
  `κ_E(η) = η̄` and `t_E(η) = ℓ_e / √(2E)`.
* `germCycle_eq_of_closed`, `germCycles_eq_image`, `cycleType_shellGermPerm_eq`: when every end is
  admissible and `Π_E` agrees with an explicit map, the cycles, the set of cycles and the cycle
  type of `Π_E` are those of the explicit map, which are then computed by `decide`.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

/-! ### Permutation laws are Borel vertex data -/

namespace PermutationLaw

variable {Γ : FiniteMetricGraph} (F : PermutationLaw Γ)

/-- **Proposition III.2 for the Borel form**: the fixed-speed endpoint permutation of the law is
`F_v`, at every speed (the law is speed-independent). -/
theorem speedEndpoint_toBorelScattering (V : MechanicalPotential Γ) (v : Γ.Vertex)
    (η : Γ.IncidentEnds v) (r : PositiveSpeed) :
    EnergyPreservingScattering.speedEndpoint V
        (F.toBorelScattering V).toEnergyPreservingScattering v η r = F.perm v η := by
  rw [F.toBorelScattering_toEnergyPreservingScattering V]
  exact F.speedEndpoint_toScattering V v η r

/-- A permutation law is reversible (Lemma III.5) exactly when it is an involution. -/
theorem isReversible_toBorelScattering_iff (V : MechanicalPotential Γ) :
    (F.toBorelScattering V).toEnergyPreservingScattering.IsReversible ↔
      ∀ η : Γ.EdgeEnd, F.route (F.route η) = η := by
  rw [EnergyPreservingScattering.reversible_iff_speedEndpoint_involutive]
  simp only [speedEndpoint_toBorelScattering]
  constructor
  · intro h η
    have h1 := h η.vertex ⟨η, rfl⟩ ⟨1, Set.mem_Ioi.mpr one_pos⟩
    exact congrArg Subtype.val h1
  · intro h v η _
    exact Subtype.ext (h η.1)

end PermutationLaw

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The end step through the retrace map -/

/-- `Π_E(η) = F_v(κ_E(η), r)`: the end step of `η` is the image of `ζ = κ_E(η)` under the
fixed-speed vertex permutation at the vertex of `ζ`, at the landing speed `r = r_ζ(E)`. -/
theorem germStep_eq_speedEndpoint (S : BorelEnergyPreservingScattering V) {E : ℝ}
    (hE : V.ShellRegular E) {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) :
    V.germStep S E η =
      (EnergyPreservingScattering.speedEndpoint V S.toEnergyPreservingScattering
        (V.retraceEnd E η).vertex ⟨V.retraceEnd E η, rfl⟩
        ⟨V.germSpeed (V.retraceEnd E η) E,
          V.germSpeed_pos_iff.mpr (V.retraceEnd_mem_allowedGerms hE hη)⟩).1 :=
  V.germStep_eq_speedPermutation S hE hη rfl _ rfl

/-- **For a speed-independent permutation law, `Π_E = F ∘ κ_E`.** -/
theorem germStep_permutationLaw (F : PermutationLaw Γ) {E : ℝ} (hE : V.ShellRegular E)
    {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E) :
    V.germStep (F.toBorelScattering V) E η = F.route (V.retraceEnd E η) := by
  rw [V.germStep_eq_speedEndpoint _ hE hη, PermutationLaw.speedEndpoint_toBorelScattering]
  rfl

/-! ### The retrace map from the shape of the potential -/

/-- If the potential stays below `E` on the closed edge of `η`, then `κ_E(η) = η̄`, the opposite
end. -/
theorem retraceEnd_of_forall_lt {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (hlt : ∀ q ∈ Icc 0 (Γ.length η.1), V.extension η.1 q < E) :
    V.retraceEnd E η = (η.1, !η.2) :=
  V.retraceStep_fst_of_forall_lt hE hη hlt

/-- If the potential exceeds `E` somewhere on the closed edge of `η`, then `κ_E(η) = η`. -/
theorem retraceEnd_of_exists_gt {E : ℝ} (hE : V.ShellRegular E) {η : Γ.EdgeEnd}
    (hη : η ∈ V.allowedGerms E) (hgt : ∃ q ∈ Icc 0 (Γ.length η.1), E < V.extension η.1 q) :
    V.retraceEnd E η = η :=
  V.retraceStep_fst_of_exists_gt hE hη hgt

/-- **The flight time on an edge without potential**: `t_E(η) = ℓ_e / √(2E)`. -/
theorem flightTime_of_extension_eq_zero {E : ℝ} (hE : V.ShellRegular E) (hE0 : 0 < E)
    {η : Γ.EdgeEnd} (hη : η ∈ V.allowedGerms E)
    (hzero : ∀ q ∈ Icc 0 (Γ.length η.1), V.extension η.1 q = 0) :
    V.flightTime E η = Γ.length η.1 / Real.sqrt (2 * E) := by
  have hcross : ∀ x ∈ Ioo (0 : ℝ) (Γ.length η.1), V.extension η.1 x < E := fun x hx => by
    rw [hzero x (Ioo_subset_Icc_self hx)]; exact hE0
  rw [(V.flightTime_eq_integral_of_crossing hE hη hcross).1]
  have hl := (Γ.length_pos η.1).le
  rw [intervalIntegral.integral_congr (g := fun _ => 1 / Real.sqrt (2 * E)) (fun x hx => by
    rw [uIcc_of_le hl] at hx
    simp only [speedAt, hzero x hx, sub_zero])]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one_div]

/-! ### The zero potential -/

theorem zeroPotential_mem_allowedGerms {E : ℝ} (hE0 : 0 < E) (η : Γ.EdgeEnd) :
    η ∈ (zeroPotential Γ).allowedGerms E :=
  show (0 : ℝ) < E from hE0

/-- For `V ≡ 0` every positive energy is shell-regular. -/
theorem zeroPotential_shellRegular {E : ℝ} (hE0 : 0 < E) : (zeroPotential Γ).ShellRegular E :=
  (zeroPotential Γ).shellRegular_of_forall_lt (fun _ _ _ => hE0) (fun _ => hE0)

/-- For `V ≡ 0` and `E > 0`, `κ_E(η) = η̄`: every flight crosses its edge. -/
theorem zeroPotential_retraceEnd {E : ℝ} (hE0 : 0 < E) (η : Γ.EdgeEnd) :
    (zeroPotential Γ).retraceEnd E η = (η.1, !η.2) :=
  (zeroPotential Γ).retraceEnd_of_forall_lt (zeroPotential_shellRegular hE0)
    (zeroPotential_mem_allowedGerms hE0 η) (fun _ _ => hE0)

/-- For `V ≡ 0` and `E > 0`, `t_E(η) = ℓ_e / √(2E)`. -/
theorem zeroPotential_flightTime {E : ℝ} (hE0 : 0 < E) (η : Γ.EdgeEnd) :
    (zeroPotential Γ).flightTime E η = Γ.length η.1 / Real.sqrt (2 * E) :=
  (zeroPotential Γ).flightTime_of_extension_eq_zero (zeroPotential_shellRegular hE0) hE0
    (zeroPotential_mem_allowedGerms hE0 η) (fun _ _ => rfl)

/-! ### Cycles of an explicitly known end step -/

section Cycles

variable (S : BorelEnergyPreservingScattering V)

/-- If every end is admissible and `Π_E` agrees with `f`, then the iterates agree. -/
theorem germStep_iterate_eq {E : ℝ} {f : Γ.EdgeEnd → Γ.EdgeEnd}
    (hf : ∀ ζ, V.germStep S E ζ = f ζ) (k : ℕ) (η : Γ.EdgeEnd) :
    (V.germStep S E)^[k] η = f^[k] η := by
  rw [show V.germStep S E = f from funext hf]

/-- **The cycle of `Π_E` through `η` is an explicit finite set `s`** if every end is admissible,
`Π_E` agrees with an explicit map `f`, `s` is closed under `f`, contains `η`, and each of its
members is reached from `η`. -/
theorem germCycle_eq_of_closed {E : ℝ} (hE : V.ShellRegular E)
    (hall : ∀ ζ, ζ ∈ V.allowedGerms E) {f : Γ.EdgeEnd → Γ.EdgeEnd}
    (hf : ∀ ζ, V.germStep S E ζ = f ζ) {η : Γ.EdgeEnd} (s : Finset Γ.EdgeEnd) (n : ℕ)
    (hs : ∀ ζ ∈ s, f ζ ∈ s) (hηs : η ∈ s) (hreach : ∀ ζ ∈ s, ∃ k < n, f^[k] η = ζ) :
    V.germCycle S E η = s := by
  ext ζ
  rw [V.mem_germCycle_iff S hE (hall η)]
  constructor
  · rintro ⟨k, rfl⟩
    rw [V.germStep_iterate_eq S hf]
    induction k with
    | zero => exact hηs
    | succ k ih => rw [Function.iterate_succ_apply']; exact hs _ ih
  · intro hζ
    obtain ⟨k, -, hk⟩ := hreach ζ hζ
    exact ⟨k, by rw [V.germStep_iterate_eq S hf, hk]⟩

/-- The same cycle, seen from any of its members. -/
theorem germCycle_eq_of_closed_of_mem {E : ℝ} (hE : V.ShellRegular E)
    (hall : ∀ ζ, ζ ∈ V.allowedGerms E) {f : Γ.EdgeEnd → Γ.EdgeEnd}
    (hf : ∀ ζ, V.germStep S E ζ = f ζ) {η : Γ.EdgeEnd} (s : Finset Γ.EdgeEnd) (n : ℕ)
    (hs : ∀ ζ ∈ s, f ζ ∈ s) (hηs : η ∈ s) (hreach : ∀ ζ ∈ s, ∃ k < n, f^[k] η = ζ)
    {ξ : Γ.EdgeEnd} (hξ : ξ ∈ s) : V.germCycle S E ξ = s := by
  have h := V.germCycle_eq_of_closed S hE hall hf s n hs hηs hreach
  rw [← h] at hξ ⊢
  exact V.germCycle_eq_of_mem S hE (hall η) hξ

/-- **The set of cycles of `Π_E`** is the image of the explicit cycle map `g`. -/
theorem germCycles_eq_image {E : ℝ} (hall : ∀ ζ, ζ ∈ V.allowedGerms E)
    {g : Γ.EdgeEnd → Finset Γ.EdgeEnd} (hg : ∀ ζ, V.germCycle S E ζ = g ζ) :
    V.germCycles S E = Finset.univ.image g := by
  ext c
  rw [V.mem_germCycles S, Finset.mem_image]
  simp only [Finset.mem_univ, true_and, hg]
  exact ⟨fun ⟨η, _, h⟩ => ⟨η, h⟩, fun ⟨η, h⟩ => ⟨η, hall η, h⟩⟩

/-- The period of the cycle through `η`, when the cycle is the explicit set `s`. -/
theorem cyclePeriod_eq_of_germCycle_eq {E : ℝ} {η : Γ.EdgeEnd} {s : Finset Γ.EdgeEnd}
    (h : V.germCycle S E η = s) : V.cyclePeriod S E η = ∑ ζ ∈ s, V.flightTime E ζ := by
  rw [cyclePeriod, h]

open Classical in
/-- **The cycle type of `Π_E` is that of an explicit permutation** `π` of all ends, when every end
is admissible and `Π_E` agrees with `π`. -/
theorem cycleType_shellGermPerm_eq {E : ℝ} (hE : V.ShellRegular E)
    (hall : ∀ ζ, ζ ∈ V.allowedGerms E) (π : Equiv.Perm Γ.EdgeEnd)
    (hπ : ∀ ζ, V.germStep S E ζ = π ζ) :
    (V.shellGermPerm S hE).cycleType = π.cycleType := by
  rw [← Equiv.Perm.cycleType_ofSubtype]
  congr 1
  refine Equiv.ext fun ζ => ?_
  rw [Equiv.Perm.ofSubtype_apply_of_mem _ (hall ζ), shellGermPerm_apply, hπ]

end Cycles

/-! ### Periodic orbits and cycles -/

section Orbits

variable (S : BorelEnergyPreservingScattering V) [Nonempty Γ.Edge]

/-- **The number of periodic orbits on `Σ_E` is the number of cycles of `Π_E`.**  The periodic
orbits of the shell are the orbits `shellOrbit` of the departure states (Theorem VIII.5 (c),
`regularShell_decomposition`); two of them coincide exactly when the ends lie in the same cycle. -/
theorem card_shellOrbits_eq_card_germCycles {E : ℝ} (hE : V.ShellRegular E) :
    Nat.card {O : Set (RegularScatteringPhaseSpace (V := V) S) //
        ∃ (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E), O = V.shellOrbit S hE η hη} =
      (V.germCycles S E).card := by
  classical
  have hdec := V.regularShell_decomposition S hE
  -- same orbit iff same cycle
  have hiff : ∀ (η ζ : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E) (hζ : ζ ∈ V.allowedGerms E),
      V.shellOrbit S hE η hη = V.shellOrbit S hE ζ hζ ↔
        V.germCycle S E η = V.germCycle S E ζ := by
    intro η ζ hη hζ
    rw [hdec.2.1 ⟨η, hη⟩ ⟨ζ, hζ⟩, ← V.mem_germCycle_iff_sameCycle S hE ⟨η, hη⟩ ⟨ζ, hζ⟩]
    constructor
    · intro h
      exact (V.germCycle_eq_of_mem S hE hη h).symm
    · intro h
      rw [h]
      exact V.self_mem_germCycle S hE hζ
  have hrep : ∀ c : {c // c ∈ V.germCycles S E},
      ∃ η, ∃ hη : η ∈ V.allowedGerms E, V.germCycle S E η = c.1 := fun c => by
    obtain ⟨η, hη, h⟩ := (V.mem_germCycles S).mp c.2
    exact ⟨η, hη, h⟩
  choose rep hrepmem hrepeq using hrep
  let f : {c // c ∈ V.germCycles S E} → {O : Set (RegularScatteringPhaseSpace (V := V) S) //
      ∃ (η : Γ.EdgeEnd) (hη : η ∈ V.allowedGerms E), O = V.shellOrbit S hE η hη} :=
    fun c => ⟨V.shellOrbit S hE (rep c) (hrepmem c), rep c, hrepmem c, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c d hcd
      have h := congrArg Subtype.val hcd
      apply Subtype.ext
      rw [← hrepeq c, ← hrepeq d]
      exact (hiff _ _ _ _).mp h
    · rintro ⟨O, η, hη, rfl⟩
      have hc : V.germCycle S E η ∈ V.germCycles S E :=
        (V.mem_germCycles S).mpr ⟨η, hη, rfl⟩
      refine ⟨⟨_, hc⟩, Subtype.ext ?_⟩
      exact (hiff _ _ _ _).mpr (hrepeq ⟨_, hc⟩)
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_finsetCard]

end Orbits

end MechanicalPotential

end HamiltonianMetricGraphs
