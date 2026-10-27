/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition VII.1 and Example VII.2: the invariant time measure of a regular energy surface
-/

import HamiltonianMetricGraphs.EnergySurfaceExactInvariance
import HamiltonianMetricGraphs.Examples
import HamiltonianMetricGraphs.ScatteredTrajectory

/-!
# Proposition VII.1 and Example VII.2, as printed

**Proposition VII.1** (`prop:energy-surface-measure`).  Let `E₀` not be a vertex value and be a
regular value of `V_e : (0, ℓ_e) → ℝ` for every edge `e`.  Put
`U_e(E₀) = {q ∈ (0, ℓ_e) : E₀ > V_e(q)}` and `Σ_{E₀} = H⁻¹(E₀) ∩ P^Reg_S`, and let `ν_{E₀}` be the
pushforward of the branch measures `dq / √(2(E₀ - V_e(q)))` on `U_e(E₀)` under
`q ↦ π(e, q, ε √(2(E₀ - V_e(q))))`, `ε = ±1`.  Then `ν_{E₀}` is a measure on `Σ_{E₀}`; the
complement of the open branches consists of interior turning points and boundary classes and is
`ν_{E₀}`-null; `ν_{E₀}` is invariant under `Φ_t`; and if `Σ_{E₀} ≠ ∅` it has finite mass and its
normalization is an invariant probability measure.

`energy_surface_measure` proves all of this for `ν_{E₀} = regularShellMeasure S E₀`, the single
formal `ν_E` of the development (defined in `ShellErgodic.lean` as the restriction to the regular
sector of `quotientShellMeasure S E`, the pushforward of the edgewise branch measures
`shellMeasure E e` under the class map `x ↦ π(e, x)`), under exactly the printed hypotheses:
`E₀ ∉ exceptionalEnergies` and `NoInteriorCriticalValue E₀`.  **No shell-regularity is assumed**:
flights trapped in a potential well inside an edge are allowed, and the proof does not use the
periodic-orbit structure of Theorem VIII.5.

The proof follows the paper's: on each open branch the flow is the translation `t ↦ t + s` in the
time coordinate `dt = dq/p`, so `ν_{E₀}` is Lebesgue measure in time; the finitely many interior
turning points and boundary classes — the branch section — are null, and the flow passes from one
branch to the next through them.  Formally: `exists_branchSection_parametrization` writes
`ν_{E₀}(B) = ∑_z Leb{u ∈ [0, τ_z) : Φ_u z ∈ B}` over the finite section, and the suspension
criterion `measure_preimage_eq_of_suspension` gives invariance.

**Example VII.2** (reflecting interval).  `reflecting_interval_example`: on `Γ = [0, L]` with the
reflecting law at both endpoints, the quotient identifies each endpoint state `(q, p)` with its
elastic reflection `(q, -p)`, the regular energies are those different from `V(0)` and `V(L)`, and
at a regular energy level `ν_E` is the density `dq / √(2(E - V(q)))` on each of the two momentum
branches, a finite flow-invariant measure.  `reflecting_interval_elastic` adds the impact rule:
at every vertex impact of an orbit, the edge lift arriving from the left tends to `(wall, p)` and
the edge lift leaving to the right starts from `(wall, -p)`, `p ≠ 0`.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-! ### `ν_E` lives on the regular energy surface -/

/-- Every branch point over `U_e(E)` has energy `E`. -/
theorem quotientHamiltonian_branch {E : ℝ} {e : Γ.Edge} {q : ℝ}
    (hq : q ∈ V.allowedPositions e E) (b : Bool) :
    quotientHamiltonian (V := V) S (graphClass V S (e, q, boolSign b * V.speedAt e E q)) = E := by
  have hy : Γ.AdmissiblePoint (e, q, boolSign b * V.speedAt e E q) :=
    ⟨Ioo_subset_Icc_self hq.1, Or.inl hq.1⟩
  rw [quotientHamiltonian_graphClass V S hy]
  exact V.hamiltonian_speedAt e (by rcases boolSign_cases b with h | h <;> rw [h] <;> norm_num)
    hq.2.le

/-- At a non-exceptional energy the quotient `ν_E` is carried by the regular sector. -/
theorem quotientShellMeasure_compl_regular {E : ℝ} (hE : E ∉ V.exceptionalEnergies) :
    V.quotientShellMeasure S E (range (Subtype.val :
      RegularScatteringPhaseSpace (V := V) S → ScatteringPhaseSpace (V := V) S))ᶜ = 0 := by
  have hR : MeasurableSet (range (Subtype.val :
      RegularScatteringPhaseSpace (V := V) S → ScatteringPhaseSpace (V := V) S)) := by
    rw [Subtype.range_coe]; exact measurableSet_regularScatteringPhaseSpace V S
  rw [← lintegral_indicator_one hR.compl,
    V.lintegral_quotientShellMeasure_eq_branches S E (measurable_one.indicator hR.compl)]
  refine Finset.sum_eq_zero fun e _ => ?_
  have hU := V.measurableSet_allowedPositions e E
  have key : ∀ b : Bool, ∫⁻ q in V.allowedPositions e E, V.timeDensity e E q *
      (range (Subtype.val : RegularScatteringPhaseSpace (V := V) S →
        ScatteringPhaseSpace (V := V) S))ᶜ.indicator 1
        (graphClass V S (e, q, boolSign b * V.speedAt e E q)) = 0 := by
    intro b
    rw [setLIntegral_congr_fun hU (g := fun _ => 0) fun q hq => ?_]
    · simp
    have hmem : graphClass V S (e, q, boolSign b * V.speedAt e E q) ∈ range (Subtype.val :
        RegularScatteringPhaseSpace (V := V) S → ScatteringPhaseSpace (V := V) S) := by
      have hH := V.quotientHamiltonian_branch S hq b
      refine ⟨⟨_, ?_⟩, rfl⟩
      show quotientHamiltonian (V := V) S
        (graphClass V S (e, q, boolSign b * V.speedAt e E q)) ∉ V.exceptionalEnergies
      rw [hH]; exact hE
    rw [indicator_of_notMem (not_not.mpr hmem), mul_zero]
  have k1 := key true
  have k2 := key false
  simp only [boolSign_true, boolSign_false, one_mul, neg_one_mul] at k1 k2
  rw [k1, k2, add_zero]

/-- `ν_E` on the regular sector pushes forward to the quotient `ν_E`. -/
theorem map_val_regularShellMeasure {E : ℝ} (hE : E ∉ V.exceptionalEnergies) :
    (V.regularShellMeasure S E).map Subtype.val = V.quotientShellMeasure S E := by
  rw [regularShellMeasure, (V.measurableEmbedding_regular S).map_comap]
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (V.quotientShellMeasure_compl_regular S hE))

/-- **The defining formula of `ν_E` on the regular sector.** -/
theorem lintegral_regularShellMeasure_eq_branches {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    {f : ScatteringPhaseSpace (V := V) S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z.1 ∂(V.regularShellMeasure S E) =
      ∑ e, ((∫⁻ q in V.allowedPositions e E,
          V.timeDensity e E q * f (graphClass V S (e, q, V.speedAt e E q))) +
        ∫⁻ q in V.allowedPositions e E,
          V.timeDensity e E q * f (graphClass V S (e, q, -V.speedAt e E q))) := by
  rw [← V.lintegral_quotientShellMeasure_eq_branches S E hf,
    ← V.map_val_regularShellMeasure S hE, lintegral_map hf measurable_subtype_coe]

/-! ### The open branches -/

/-- **The parametrized open branches** of Proposition VII.1: the points
`π(e, q, ε √(2(E - V_e(q))))`, `q ∈ U_e(E)`, `ε = ±1`. -/
def openBranches (E : ℝ) : Set (RegularScatteringPhaseSpace (V := V) S) :=
  {z | ∃ (e : Γ.Edge) (b : Bool), ∃ q ∈ V.allowedPositions e E,
    z.1 = graphClass V S (e, q, boolSign b * V.speedAt e E q)}

theorem openBranches_subset_shell (E : ℝ) : V.openBranches S E ⊆ V.shell S E := by
  rintro z ⟨e, b, q, hq, hz⟩
  change quotientHamiltonian (V := V) S z.1 = E
  rw [hz, V.quotientHamiltonian_branch S hq b]

/-- Off the open branches, a point of `Σ_E` is in the branch section. -/
theorem shell_diff_openBranches_subset (E : ℝ) :
    V.shell S E \ V.openBranches S E ⊆ V.branchSection S E := by
  rintro z ⟨hzE, hzB⟩
  refine ⟨hzE, ?_⟩
  by_contra hnot
  push Not at hnot
  obtain ⟨hint, hp⟩ := hnot
  apply hzB
  have hH := (V.hamiltonian_rep S z).trans hzE
  have hV : V.extension (V.repEdge S z) (V.repPos S z) < E := by
    have : 0 < V.repMom S z ^ 2 := by positivity
    rw [hamiltonian] at hH; linarith
  refine ⟨V.repEdge S z, decide (0 < V.repMom S z), V.repPos S z, ⟨hint, hV⟩, ?_⟩
  rw [← V.graphClass_rep S z, V.speedAt_eq_abs_of_hamiltonian hH]
  congr 2
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · simp [not_lt.mpr hneg.le, abs_of_neg hneg]
  · simp [hpos, abs_of_pos hpos]

section Main

variable [Nonempty Γ.Edge]

/-- The section is `ν_E`-null. -/
theorem regularShellMeasure_branchSection {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) :
    V.regularShellMeasure S E (V.branchSection S E) = 0 := by
  obtain ⟨τ, -, -, hfirst, hν⟩ := V.exists_branchSection_parametrization S hE hreg
  rw [hν _ (V.measurableSet_of_finite S (V.finite_branchSection S hE hreg))]
  refine Finset.sum_eq_zero fun z hz => measure_mono_null ?_ (Real.volume_singleton (a := 0))
  rintro u ⟨hu, hzu⟩
  rcases eq_or_lt_of_le hu.1 with h | h
  · exact h.symm
  · exact absurd hzu (hfirst z ((Set.Finite.mem_toFinset _).mp hz) u ⟨h, hu.2⟩)

/-- `ν_E` is carried by `Σ_E`. -/
theorem regularShellMeasure_compl_shell_of_regular {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) :
    V.regularShellMeasure S E (V.shell S E)ᶜ = 0 := by
  obtain ⟨τ, -, -, -, hν⟩ := V.exists_branchSection_parametrization S hE hreg
  rw [hν _ (V.measurableSet_shell S E).compl]
  refine Finset.sum_eq_zero fun z hz => ?_
  have hzE : z ∈ V.shell S E := ((Set.Finite.mem_toFinset _).mp hz).1
  convert measure_empty (μ := (volume : Measure ℝ))
  ext u
  simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
    not_not]
  intro _
  change quotientHamiltonian (V := V) S _ = E
  rw [quotientHamiltonian_flow]; exact hzE

/-- The complement of the open branches is `ν_E`-null. -/
theorem regularShellMeasure_compl_openBranches {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) :
    V.regularShellMeasure S E (V.openBranches S E)ᶜ = 0 := by
  refine measure_mono_null (t := (V.shell S E)ᶜ ∪ V.branchSection S E) ?_
    (measure_union_null (V.regularShellMeasure_compl_shell_of_regular S hE hreg)
      (V.regularShellMeasure_branchSection S hE hreg))
  intro z hz
  by_cases hzE : z ∈ V.shell S E
  · exact Or.inr (V.shell_diff_openBranches_subset S E ⟨hzE, hz⟩)
  · exact Or.inl hzE

/-- The total mass of `ν_E` is finite. -/
theorem regularShellMeasure_univ_lt_top_of_regular {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) : V.regularShellMeasure S E univ < ⊤ := by
  obtain ⟨τ, -, -, -, hν⟩ := V.exists_branchSection_parametrization S hE hreg
  rw [hν _ MeasurableSet.univ]
  refine ENNReal.sum_lt_top.mpr fun z _ => lt_of_le_of_lt (measure_mono inter_subset_left) ?_
  rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top

/-- On a nonempty energy surface `ν_E` is nonzero. -/
theorem regularShellMeasure_univ_ne_zero_of_regular {E : ℝ} (hE : E ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E) (hne : (V.shell S E).Nonempty) :
    V.regularShellMeasure S E univ ≠ 0 := by
  classical
  obtain ⟨τ, hτ, -, -, hν⟩ := V.exists_branchSection_parametrization S hE hreg
  -- a point of the section
  obtain ⟨z, hz⟩ : (V.branchSection S E).Nonempty := by
    obtain ⟨w, hw⟩ := hne
    by_cases hwC : w ∈ V.branchSection S E
    · exact ⟨w, hwC⟩
    · have hwB : w ∈ V.openBranches S E := by
        by_contra h
        exact hwC (V.shell_diff_openBranches_subset S E ⟨hw, h⟩)
      obtain ⟨e, b, q, hq, -⟩ := hwB
      obtain ⟨z, hz, -⟩ := V.exists_start S hE hreg e b hq
      exact ⟨z, hz⟩
  rw [hν _ MeasurableSet.univ]
  refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun z =>
    volume (Ico 0 (τ z) ∩ (fun u => flow V S z u) ⁻¹' univ)) (fun _ _ => zero_le)
    ((Set.Finite.mem_toFinset _).mpr hz)))
  simp only [preimage_univ, inter_univ, Real.volume_Ico, sub_zero]
  exact ENNReal.ofReal_pos.mpr (hτ z hz)

/-- **Proposition VII.1** (`prop:energy-surface-measure`), as printed.  Let `E₀` not be a vertex
value and be a regular value of `V_e : (0, ℓ_e) → ℝ` on every edge.  Then, for
`ν_{E₀} = regularShellMeasure S E₀` and `Σ_{E₀} = shell S E₀`:

1. `ν_{E₀}` is the pushforward of the branch measures `dq / √(2(E₀ - V_e(q)))` on
   `U_e(E₀) = allowedPositions e E₀` under `q ↦ π(e, q, ±√(2(E₀ - V_e(q))))`: the defining
   formula holds for every nonnegative Borel `f`;
2. `ν_{E₀}` is a measure on `Σ_{E₀}`: `ν_{E₀}(Σ_{E₀}ᶜ) = 0`;
3. the parametrized open branches lie in `Σ_{E₀}`, and a point of `Σ_{E₀}` off them is an interior
   turning point (`0 < q < ℓ_e`, `p = 0`, `V_e(q) = E₀`) or a boundary class (its outgoing
   representative sits at a vertex); the complement of the open branches is `ν_{E₀}`-null;
4. `ν_{E₀}` is invariant under `Φ_t` for every `t ∈ ℝ`: `ν_{E₀}(Φ_t⁻¹ A) = ν_{E₀}(A)` for every
   Borel `A` (in particular for every Borel `A ⊆ Σ_{E₀}`);
5. if `Σ_{E₀} ≠ ∅`, then `0 < ν_{E₀}(Σ_{E₀}) < ∞`, and the normalization
   `normalizedShellMeasure S E₀ = ν_{E₀} / ν_{E₀}(Σ_{E₀})` is a `Φ_t`-invariant probability
   measure. -/
theorem energy_surface_measure {E₀ : ℝ} (hE : E₀ ∉ V.exceptionalEnergies)
    (hreg : V.NoInteriorCriticalValue E₀) :
    (∀ f : ScatteringPhaseSpace (V := V) S → ℝ≥0∞, Measurable f →
      ∫⁻ z, f z.1 ∂(V.regularShellMeasure S E₀) =
        ∑ e, ((∫⁻ q in V.allowedPositions e E₀, ENNReal.ofReal (1 / V.speedAt e E₀ q) *
            f (graphClass V S (e, q, V.speedAt e E₀ q))) +
          ∫⁻ q in V.allowedPositions e E₀, ENNReal.ofReal (1 / V.speedAt e E₀ q) *
            f (graphClass V S (e, q, -V.speedAt e E₀ q)))) ∧
    V.regularShellMeasure S E₀ (V.shell S E₀)ᶜ = 0 ∧
    V.openBranches S E₀ ⊆ V.shell S E₀ ∧
    (∀ z ∈ V.shell S E₀, z ∉ V.openBranches S E₀ →
      (V.repPos S z ∈ Ioo 0 (Γ.length (V.repEdge S z)) ∧ V.repMom S z = 0 ∧
        V.extension (V.repEdge S z) (V.repPos S z) = E₀) ∨
      V.repPos S z ∉ Ioo 0 (Γ.length (V.repEdge S z))) ∧
    V.regularShellMeasure S E₀ (V.openBranches S E₀)ᶜ = 0 ∧
    (∀ (t : ℝ) (A : Set (RegularScatteringPhaseSpace (V := V) S)), MeasurableSet A →
      V.regularShellMeasure S E₀ ((fun z => flow V S z t) ⁻¹' A) =
        V.regularShellMeasure S E₀ A) ∧
    (∀ t : ℝ, MeasurePreserving (fun z => flow V S z t) (V.regularShellMeasure S E₀)
      (V.regularShellMeasure S E₀)) ∧
    ((V.shell S E₀).Nonempty →
      0 < V.regularShellMeasure S E₀ (V.shell S E₀) ∧
      V.regularShellMeasure S E₀ (V.shell S E₀) < ⊤ ∧
      IsProbabilityMeasure (V.normalizedShellMeasure S E₀) ∧
      ∀ t : ℝ, MeasurePreserving (fun z => flow V S z t) (V.normalizedShellMeasure S E₀)
        (V.normalizedShellMeasure S E₀)) := by
  have hshell : V.regularShellMeasure S E₀ (V.shell S E₀) = V.regularShellMeasure S E₀ univ := by
    rw [← measure_inter_add_sdiff univ (V.measurableSet_shell S E₀), univ_inter,
      ← compl_eq_univ_sdiff, V.regularShellMeasure_compl_shell_of_regular S hE hreg, add_zero]
  refine ⟨fun f hf => ?_, V.regularShellMeasure_compl_shell_of_regular S hE hreg,
    V.openBranches_subset_shell S E₀, fun z hz hzB => ?_,
    V.regularShellMeasure_compl_openBranches S hE hreg,
    fun t A hA => V.regularShellMeasure_preimage_flow S hE hreg t hA,
    V.measurePreserving_flow_regularShellMeasure_of_regular S hE hreg, fun hne => ?_⟩
  · exact V.lintegral_regularShellMeasure_eq_branches S hE hf
  · obtain ⟨-, h | h⟩ := V.shell_diff_openBranches_subset S E₀ ⟨hz, hzB⟩
    · exact Or.inr h
    · left
      have hint : V.repPos S z ∈ Ioo 0 (Γ.length (V.repEdge S z)) := by
        rcases (rep V S z.1).2 with h' | h'
        · exact h'
        · exact absurd h h'
      refine ⟨hint, h, ?_⟩
      have hH := (V.hamiltonian_rep S z).trans hz
      rw [hamiltonian, h] at hH; linarith
  · have hpos := V.regularShellMeasure_univ_ne_zero_of_regular S hE hreg hne
    have hfin := V.regularShellMeasure_univ_lt_top_of_regular S hE hreg
    refine ⟨by rw [hshell]; exact pos_iff_ne_zero.mpr hpos, by rw [hshell]; exact hfin,
      ⟨by rw [normalizedShellMeasure, Measure.smul_apply, smul_eq_mul,
        ENNReal.inv_mul_cancel hpos hfin.ne]⟩, fun t => ?_⟩
    refine ⟨V.measurable_flow S t, ?_⟩
    rw [normalizedShellMeasure, Measure.map_smul,
      (V.measurePreserving_flow_regularShellMeasure_of_regular S hE hreg t).map_eq]

end Main

/-! ### Reflection at an endpoint -/

/-- Under the reflecting law an endpoint state is identified with its elastic reflection: the
classes of `(η, p)` and `(η, -p)` coincide. -/
theorem graphClass_reflection_endpoint (η : Γ.EdgeEnd) {p : ℝ} (hp : p ≠ 0) :
    graphClass V (reflectionScattering V) (η.1, FiniteMetricGraph.EdgeEnd.coordinate Γ η, p) =
      graphClass V (reflectionScattering V)
        (η.1, FiniteMetricGraph.EdgeEnd.coordinate Γ η, -p) := by
  have key : ∀ p : ℝ, (hp : p ≠ 0) → 0 < FiniteMetricGraph.EdgeEnd.sign Γ η * p →
      graphClass V (reflectionScattering V) (η.1, FiniteMetricGraph.EdgeEnd.coordinate Γ η, p) =
      graphClass V (reflectionScattering V)
        (η.1, FiniteMetricGraph.EdgeEnd.coordinate Γ η, -p) := by
    intro p hp hin
    let α : Γ.IncomingBoundary (FiniteMetricGraph.EdgeEnd.vertex Γ η) := ⟨⟨η, p, hp⟩, rfl, hin⟩
    have h1 : graphClass V (reflectionScattering V)
        (η.1, FiniteMetricGraph.EdgeEnd.coordinate Γ η, p) =
        quotientMap (V := V) (reflectionScattering V) (α.1.toNonzeroPrequotientPhase Γ) := by
      unfold graphClass
      exact congrArg _ (Γ.graphPoint_covector α.1)
    have h2 : graphClass V (reflectionScattering V)
        (η.1, FiniteMetricGraph.EdgeEnd.coordinate Γ η, -p) =
        quotientMap (V := V) (reflectionScattering V)
          (((reflectionScattering V).map _ α).1.toNonzeroPrequotientPhase Γ) := by
      unfold graphClass
      exact congrArg _ (Γ.graphPoint_covector ((reflectionScattering V).map _ α).1)
    rw [h1, h2]
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨_, α, rfl, rfl⟩)
  have hs := Γ.edgeEnd_sign_ne_zero η
  rcases lt_or_gt_of_ne (mul_ne_zero hs hp) with hneg | hpos
  · have := key (-p) (neg_ne_zero.mpr hp) (by rw [mul_neg]; linarith)
    rw [neg_neg] at this
    exact this.symm
  · exact key p hp hpos

end MechanicalPotential

/-! ### Example VII.2: the reflecting interval -/

/-- **The interval `Γ = [0, L]`**: one edge of length `L`, whose two ends are the two vertices
(`false` at `q = 0`, `true` at `q = L`). -/
def reflectingIntervalGraph (L : ℝ) (hL : 0 < L) : FiniteMetricGraph where
  Vertex := Bool
  Edge := Unit
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  endpoint := fun _ b => b
  length := fun _ => L
  length_pos := fun _ => hL

instance (L : ℝ) (hL : 0 < L) : Nonempty (reflectingIntervalGraph L hL).Edge := ⟨()⟩

instance (L : ℝ) (hL : 0 < L) : Unique (reflectingIntervalGraph L hL).Edge :=
  inferInstanceAs (Unique Unit)

namespace MechanicalPotential

open Set MeasureTheory Filter
open scoped ENNReal Topology

/-- **Example VII.2 (reflecting interval).**  Let `Γ = [0, L]` carry the reflecting law at both
endpoints (`reflectionScattering`).  Then:

1. the quotient identifies each endpoint state `(q, p)`, `q ∈ {0, L}`, with its elastic
   reflection `(q, -p)`;
2. the regular energies are exactly those different from the endpoint values `V(0)`, `V(L)`;
3. the scattered evolution of Theorem VI.5 is an energy-preserving one-parameter group there
   (the usual one-dimensional motion with elastic reflection);
4. at a regular energy level `E` (`E ≠ V(0), V(L)`, and `E` a regular value of `V` on `(0, L)`),
   Proposition VII.1 gives the invariant measure `ν_E` with the standard density
   `dq / √(2(E - V(q)))` on each of the two momentum branches over
   `U(E) = {q ∈ (0, L) : V(q) < E}`; it is finite and invariant under every `Φ_t`. -/
theorem reflecting_interval_example {L : ℝ} (hL : 0 < L)
    (V : MechanicalPotential (reflectingIntervalGraph L hL)) :
    (∀ (b : Bool) (p : ℝ), p ≠ 0 →
      graphClass V (reflectionScattering V) ((), (if b then L else 0), p) =
        graphClass V (reflectionScattering V) ((), (if b then L else 0), -p)) ∧
    (∀ E : ℝ, E ∈ V.exceptionalEnergies ↔ E = V.extension () 0 ∨ E = V.extension () L) ∧
    (∀ (z : RegularScatteringPhaseSpace (V := V) (reflectionScattering V)) (s t : ℝ),
      flow V (reflectionScattering V) (flow V (reflectionScattering V) z s) t =
        flow V (reflectionScattering V) z (s + t)) ∧
    (∀ (z : RegularScatteringPhaseSpace (V := V) (reflectionScattering V)) (t : ℝ),
      quotientHamiltonian (V := V) (reflectionScattering V)
        (flow V (reflectionScattering V) z t).1 =
        quotientHamiltonian (V := V) (reflectionScattering V) z.1) ∧
    (∀ E : ℝ, E ≠ V.extension () 0 → E ≠ V.extension () L →
      (∀ q ∈ Ioo 0 L, V.extension () q = E → deriv (V.extension ()) q ≠ 0) →
      (∀ f : ScatteringPhaseSpace (V := V) (reflectionScattering V) → ℝ≥0∞, Measurable f →
        ∫⁻ z, f z.1 ∂(V.regularShellMeasure (reflectionScattering V) E) =
          (∫⁻ q in V.allowedPositions () E, ENNReal.ofReal (1 / V.speedAt () E q) *
              f (graphClass V (reflectionScattering V) ((), q, V.speedAt () E q))) +
            ∫⁻ q in V.allowedPositions () E, ENNReal.ofReal (1 / V.speedAt () E q) *
              f (graphClass V (reflectionScattering V) ((), q, -V.speedAt () E q))) ∧
      (∀ t : ℝ, MeasurePreserving (fun z => flow V (reflectionScattering V) z t)
        (V.regularShellMeasure (reflectionScattering V) E)
        (V.regularShellMeasure (reflectionScattering V) E)) ∧
      V.regularShellMeasure (reflectionScattering V) E univ < ⊤) := by
  have hexc : ∀ E : ℝ, E ∈ V.exceptionalEnergies ↔
      E = V.extension () 0 ∨ E = V.extension () L := by
    intro E
    rw [V.mem_exceptionalEnergies_iff]
    have h0 : V.vertexValue false = V.extension () 0 :=
      (V.endpoint_compatible ((), false)).symm
    have h1 : V.vertexValue true = V.extension () L :=
      (V.endpoint_compatible ((), true)).symm
    constructor
    · rintro ⟨v, hv⟩
      cases v
      · left; rw [← hv, h0]
      · right; rw [← hv, h1]
    · rintro (h | h)
      · exact ⟨false, by rw [h0, h]⟩
      · exact ⟨true, by rw [h1, h]⟩
  refine ⟨fun b p hp => V.graphClass_reflection_endpoint ((), b) hp, hexc,
    fun z s t => flow_flow V _ z s t, fun z t => quotientHamiltonian_flow V _ z t,
    fun E h0 hL' hcrit => ?_⟩
  have hE : E ∉ V.exceptionalEnergies := by
    rw [hexc]; rintro (h | h)
    · exact h0 h
    · exact hL' h
  have hreg : V.NoInteriorCriticalValue E := fun e q hq hqE => hcrit q hq hqE
  obtain ⟨hform, -, -, -, -, -, hmp, -⟩ := V.energy_surface_measure (reflectionScattering V) hE hreg
  refine ⟨fun f hf => ?_, hmp, V.regularShellMeasure_univ_lt_top_of_regular _ hE hreg⟩
  rw [hform f hf, Fintype.sum_unique]
  rfl

/-- **Example VII.2: elastic reflection at the walls.**  On the reflecting interval, at every
vertex impact `t₀` of an orbit `t ↦ Φ_t z` (Definition V.4, `flowImpactSet`) there are a wall
`q_w ∈ {0, L}` and a momentum `p ≠ 0` such that `Φ_{t₀} z = π(q_w, p) = π(q_w, -p)`, every edge lift
of the orbit just before `t₀` arrives at `(q_w, p)`, and every edge lift just after `t₀` leaves
from `(q_w, -p)`: the trajectory reaching the wall with momentum `p` continues with momentum `-p`.
This is the impact condition `flow_isScatteringImpact` of Proposition V.5 with the reflecting law
`S_v α = (momentum reversal of α)`. -/
theorem reflecting_interval_elastic {L : ℝ} (hL : 0 < L)
    (V : MechanicalPotential (reflectingIntervalGraph L hL))
    (z : RegularScatteringPhaseSpace (V := V) (reflectionScattering V)) {t₀ : ℝ}
    (ht₀ : t₀ ∈ flowImpactSet V (reflectionScattering V) z) :
    ∃ (b : Bool) (p : ℝ), p ≠ 0 ∧
      (flow V (reflectionScattering V) z t₀).1 =
        graphClass V (reflectionScattering V) ((), (if b then L else 0), p) ∧
      (flow V (reflectionScattering V) z t₀).1 =
        graphClass V (reflectionScattering V) ((), (if b then L else 0), -p) ∧
      (∀ t < t₀, Disjoint (Ioo t t₀) (flowImpactSet V (reflectionScattering V) z) →
        ∀ c : ℝ → ℝ × ℝ,
          IsEdgeLift V (reflectionScattering V) (flow V (reflectionScattering V) z) (Ioo t t₀)
            () c →
          Tendsto c (𝓝[<] t₀) (𝓝 ((if b then L else 0), p))) ∧
      (∀ t > t₀, Disjoint (Ioo t₀ t) (flowImpactSet V (reflectionScattering V) z) →
        ∀ c : ℝ → ℝ × ℝ,
          IsEdgeLift V (reflectionScattering V) (flow V (reflectionScattering V) z) (Ioo t₀ t)
            () c →
          Tendsto c (𝓝[>] t₀) (𝓝 ((if b then L else 0), -p))) := by
  obtain ⟨v, α, h1, h2, hl, hr⟩ := flow_isScatteringImpact V (reflectionScattering V) z ht₀
  have hS : ((reflectionScattering V).map v α).1 = α.1.momentumReversal := rfl
  rw [hS] at h2 hr
  refine ⟨α.1.germ.2, α.1.momentum, α.1.momentum_ne_zero, ?_, ?_, ?_, ?_⟩
  · rw [h1, ← graphClass_covector]; rfl
  · rw [h2, ← graphClass_covector]; rfl
  · intro t ht hdisj c hc
    exact (hl t ht hdisj () c hc).2
  · intro t ht hdisj c hc
    exact (hr t ht hdisj () c hc).2

end MechanicalPotential

end HamiltonianMetricGraphs
