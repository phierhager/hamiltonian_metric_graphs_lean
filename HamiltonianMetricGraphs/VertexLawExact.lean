/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.VertexLaw
import HamiltonianMetricGraphs.BorelScattering

/-!
# Section X as printed: Theorem X.4 over Borel laws, Lemma X.3, Remarks X.5 and X.6

This file makes the fixed-speed statements of Sec. X of the paper match their printed form.

* **Theorem X.4 (Birkhoff–von Neumann for vertex laws).**  The paper defines `D_{v,r}` as the set
  of matrices `P^S_{v,r}` of the *deterministic scattering structures of Definition III.1*, i.e.
  of Borel isomorphisms `D^in_v → D^out_v` preserving boundary energy
  (`BorelEnergyPreservingScattering`).  `borelSpeedMatrices V v r` is that set, and
  `birkhoff_vertexLaws` proves (a) `D_{v,r}` is the set of permutation matrices, (b) the doubly
  stochastic matrices are its convex hull, and every one is an explicit finite convex combination
  of its elements, (c) `D_{v,r}` is the set of extreme points of the doubly stochastic matrices.
  The realization of a prescribed permutation (the converse half of (a)) is the
  speed-independent law `PermutationLaw.toBorelScattering`, whose measurability is read off the
  speed charts.  `speedMatrix_apply` is equation (X.4): `P^S_{v,r}(η,ζ) = 1` iff
  `ζ = F_v(η,r)`.
* **After Lemma X.3.**  "For `d ≥ 3`, not every doubly stochastic matrix has this form"
  (`|U(η,ζ)|²` with `U` unitary): `halfSwapMatrix` is the printed example
  `½[[1,1,0],[1,0,1],[0,1,1]]` (`halfSwapMatrix_fin_three`), placed on any three distinct
  indices, and `exists_doublyStochastic_not_unistochastic` gives the statement for every
  `d ≥ 3`; `vertexLaw_not_unistochastic` specializes it to the incident ends of a vertex.
* **Remark X.6.**  Detailed balance with respect to counting measure,
  `P(η,ζ) = P(ζ,η)`, forces a row-stochastic matrix to be doubly stochastic
  (`mem_doublyStochastic_of_detailedBalance`), and it is strictly stronger as soon as `d ≥ 3`
  (`exists_doublyStochastic_not_detailedBalance`, a 3-cycle).  For `d ≤ 2` the two notions
  coincide (`detailedBalance_of_mem_doublyStochastic_of_card_le_two`), so "strictly stronger"
  is a statement about `d ≥ 3`.
* **Remark X.5.**  A flux-preserving matrix is a transport plan with counting marginals
  (`mem_transportPlans_one_iff`), and after normalization a coupling of the uniform probability
  vector with itself (`smul_mem_transportPlans_uniform_iff`); permutation laws are exactly the
  map-induced plans (`isMapInduced_iff_permMatrix`), so the map-induced plans are the extreme
  points (`extremePoints_transportPlans_one`).  For general transport problems extreme plans
  need not be induced by maps: source `δ₀`, target `½(δ₀ + δ₁)` on a two-point space
  (`extreme_plan_not_mapInduced`).

Transport plans are written as mass matrices: on a finite space a measure is its vector of point
masses, and a plan is the matrix of its point masses on the product.
-/

namespace HamiltonianMetricGraphs

open FiniteMetricGraph Matrix

/-! ### Theorem X.4 over Borel scattering laws -/

namespace PermutationLaw

variable {Γ : FiniteMetricGraph} (F : PermutationLaw Γ)

/-- In the speed charts a permutation law is `(η, r) ↦ (π η, r)`. -/
theorem scatter_eq_chart (v : Γ.Vertex) :
    F.scatter v = (fun x : Γ.IncidentEnds v × PositiveSpeed =>
      Γ.outgoingAtSpeed (F.perm v x.1) x.2) ∘ (Γ.incomingSpeedChart v).symm := rfl

theorem unscatter_eq_chart (v : Γ.Vertex) :
    F.unscatter v = (fun x : Γ.IncidentEnds v × PositiveSpeed =>
      Γ.incomingAtSpeed ((F.perm v).symm x.1) x.2) ∘ (Γ.outgoingSpeedChart v).symm := rfl

theorem measurable_scatter (v : Γ.Vertex) : Measurable (F.scatter v) := by
  rw [scatter_eq_chart]
  refine Measurable.comp ?_ (Γ.incomingSpeedChart v).symm.measurable
  exact (Γ.measurable_outgoingAtSpeed v).comp
    ((Measurable.of_discrete.comp measurable_fst).prodMk measurable_snd)

theorem measurable_unscatter (v : Γ.Vertex) : Measurable (F.unscatter v) := by
  rw [unscatter_eq_chart]
  refine Measurable.comp ?_ (Γ.outgoingSpeedChart v).symm.measurable
  exact (Γ.measurable_incomingAtSpeed v).comp
    ((Measurable.of_discrete.comp measurable_fst).prodMk measurable_snd)

/-- The permutation law at a vertex as a **Borel isomorphism** `D^in_v → D^out_v`. -/
noncomputable def scatterMeasurableEquiv (v : Γ.Vertex) :
    Γ.IncomingBoundary v ≃ᵐ Γ.OutgoingBoundary v where
  toEquiv := F.scatterEquiv v
  measurable_toFun := F.measurable_scatter v
  measurable_invFun := F.measurable_unscatter v

/-- **A permutation law is a deterministic scattering structure of Definition III.1**: a Borel
isomorphism at every vertex that preserves boundary energy. -/
noncomputable def toBorelScattering (V : MechanicalPotential Γ) :
    MechanicalPotential.BorelEnergyPreservingScattering V where
  map := F.scatterMeasurableEquiv
  preserves_energy := (F.toScattering V).preserves_energy

theorem toBorelScattering_toEnergyPreservingScattering (V : MechanicalPotential Γ) :
    (F.toBorelScattering V).toEnergyPreservingScattering = F.toScattering V := rfl

end PermutationLaw

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-- **Equation (X.4).**  The matrix of a deterministic law at `(v, r)` has entry `1` at
`(η, F_v(η, r))` and `0` elsewhere. -/
theorem speedMatrix_apply (S : V.EnergyPreservingScattering) (v : Γ.Vertex) (r : PositiveSpeed)
    (η ζ : Γ.IncidentEnds v) :
    V.speedMatrix S v r η ζ =
      if ζ = EnergyPreservingScattering.speedEndpoint V S v η r then 1 else 0 := by
  classical
  simp only [speedMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    EnergyPreservingScattering.speedPermutation_apply]
  by_cases h : ζ = EnergyPreservingScattering.speedEndpoint V S v η r
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

/-- **The set `D_{v,r}` of Theorem X.4**: the matrices `P^S_{v,r}` of the deterministic scattering
structures `S` of Definition III.1 (Borel, energy preserving). -/
def borelSpeedMatrices (v : Γ.Vertex) (r : PositiveSpeed) :
    Set (Matrix (Γ.IncidentEnds v) (Γ.IncidentEnds v) ℝ) :=
  {P | ∃ S : V.BorelEnergyPreservingScattering,
    V.speedMatrix S.toEnergyPreservingScattering v r = P}

/-- **Every permutation of the incident ends is realized by a Borel deterministic law**, which
can be taken speed independent and the identity at the other vertices. -/
theorem exists_borelScattering_speedPermutation_eq (v : Γ.Vertex)
    (σ : Equiv.Perm (Γ.IncidentEnds v)) :
    ∃ S : V.BorelEnergyPreservingScattering, ∀ r : PositiveSpeed,
      EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r = σ := by
  refine ⟨(PermutationLaw.ofPerm v σ).toBorelScattering V, fun r => ?_⟩
  ext η
  rw [EnergyPreservingScattering.speedPermutation_apply,
    PermutationLaw.toBorelScattering_toEnergyPreservingScattering,
    (PermutationLaw.ofPerm v σ).speedEndpoint_toScattering V v η r,
    PermutationLaw.ofPerm_perm]

/-- **Theorem X.4 (a).**  `D_{v,r}` is the set of permutation matrices on `E_v^∂`. -/
theorem borelSpeedMatrices_eq (v : Γ.Vertex) (r : PositiveSpeed) :
    V.borelSpeedMatrices v r = {P | ∃ σ : Equiv.Perm (Γ.IncidentEnds v), σ.permMatrix ℝ = P} := by
  ext P
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨EnergyPreservingScattering.speedPermutation V S.toEnergyPreservingScattering v r, rfl⟩
  · rintro ⟨σ, rfl⟩
    obtain ⟨S, hS⟩ := V.exists_borelScattering_speedPermutation_eq v σ
    exact ⟨S, by rw [speedMatrix, hS r]⟩

/-- **Theorem X.4.**  Fix `v` and `r > 0` and let `D_{v,r}` be the matrices of the deterministic
scattering structures of Definition III.1.  Then
(a) `D_{v,r}` is the set of permutation matrices on `E_v^∂`;
(b) every doubly stochastic matrix is a finite convex combination of elements of `D_{v,r}`
    (explicitly, and equivalently: the doubly stochastic matrices are the convex hull of
    `D_{v,r}`);
(c) `D_{v,r}` is the set of extreme points of the doubly stochastic matrices. -/
theorem birkhoff_vertexLaws (v : Γ.Vertex) (r : PositiveSpeed) :
    V.borelSpeedMatrices v r = {P | ∃ σ : Equiv.Perm (Γ.IncidentEnds v), σ.permMatrix ℝ = P} ∧
    (∀ P ∈ doublyStochastic ℝ (Γ.IncidentEnds v),
      ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (Q : ι → Matrix (Γ.IncidentEnds v)
          (Γ.IncidentEnds v) ℝ),
        (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, Q i ∈ V.borelSpeedMatrices v r) ∧
          P = ∑ i, w i • Q i) ∧
    (doublyStochastic ℝ (Γ.IncidentEnds v) : Set (Matrix (Γ.IncidentEnds v)
        (Γ.IncidentEnds v) ℝ)) = convexHull ℝ (V.borelSpeedMatrices v r) ∧
    Set.extremePoints ℝ (doublyStochastic ℝ (Γ.IncidentEnds v) :
        Set (Matrix (Γ.IncidentEnds v) (Γ.IncidentEnds v) ℝ)) = V.borelSpeedMatrices v r := by
  classical
  have ha := V.borelSpeedMatrices_eq v r
  have hrange : V.borelSpeedMatrices v r =
      Set.range (fun σ : Equiv.Perm (Γ.IncidentEnds v) => σ.permMatrix ℝ) := by
    rw [ha]; rfl
  refine ⟨ha, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨w, hw0, hw1, hPw⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
    refine ⟨Equiv.Perm (Γ.IncidentEnds v), inferInstance, w,
      fun σ => σ.permMatrix ℝ, hw0, hw1, fun σ => ?_, hPw.symm⟩
    rw [ha]
    exact ⟨σ, rfl⟩
  · rw [hrange, doublyStochastic_eq_convexHull_permMatrix]; rfl
  · rw [hrange, extremePoints_doublyStochastic]; rfl

end MechanicalPotential

/-! ### After Lemma X.3: a doubly stochastic matrix that is not unistochastic -/

section Unistochastic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix `½ (P_{(b c)} + P_{(a b)})`.  On `a, b, c = 0, 1, 2` it is the printed example
`½[[1,1,0],[1,0,1],[0,1,1]]` (`halfSwapMatrix_fin_three`). -/
noncomputable def halfSwapMatrix (a b c : n) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (Equiv.swap b c).permMatrix ℝ + (1 / 2 : ℝ) • (Equiv.swap a b).permMatrix ℝ

omit [Fintype n] in
theorem permMatrix_apply' (σ : Equiv.Perm n) (i j : n) :
    σ.permMatrix ℝ i j = if σ i = j then 1 else 0 := by
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq]

omit [Fintype n] in
theorem halfSwapMatrix_apply (a b c i j : n) :
    halfSwapMatrix a b c i j =
      (1 / 2 : ℝ) * (if Equiv.swap b c i = j then 1 else 0) +
        (1 / 2 : ℝ) * (if Equiv.swap a b i = j then 1 else 0) := by
  simp only [halfSwapMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, permMatrix_apply']

theorem halfSwapMatrix_mem_doublyStochastic (a b c : n) :
    halfSwapMatrix a b c ∈ doublyStochastic ℝ n :=
  (convex_doublyStochastic (R := ℝ) (n := n)) permMatrix_mem_doublyStochastic
    permMatrix_mem_doublyStochastic (by norm_num) (by norm_num) (by norm_num)

/-- The printed example after Lemma X.3. -/
theorem halfSwapMatrix_fin_three :
    halfSwapMatrix (0 : Fin 3) 1 2 = !![1 / 2, 1 / 2, 0; 1 / 2, 0, 1 / 2; 0, 1 / 2, 1 / 2] := by
  ext i j
  rw [halfSwapMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [Equiv.swap_apply_def]

/-- **The example is not unistochastic.**  If `a, b, c` are distinct, no unitary `U` satisfies
`|U(i,j)|² = halfSwapMatrix a b c i j`: rows `a` and `b` of `U` would be orthogonal, but their
supports meet only in the column `a`, where both entries have modulus `1/√2`. -/
theorem halfSwapMatrix_not_unistochastic {a b c : n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    (Matrix.of fun i j => ‖U i j‖ ^ 2) ≠ halfSwapMatrix a b c := by
  intro hM
  have hent : ∀ i j, ‖U i j‖ ^ 2 = halfSwapMatrix a b c i j := fun i j => by
    rw [← hM, Matrix.of_apply]
  have hzero : ∀ i j, halfSwapMatrix a b c i j = 0 → U i j = 0 := fun i j h => by
    have := hent i j
    rw [h] at this
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  -- the `(a, b)` entry of `U Uᴴ = 1`
  have horth := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) a) b
  rw [Matrix.mul_apply, Matrix.one_apply_ne hab] at horth
  have hsingle : ∑ k, U a k * (star U) k b = U a a * (star U) a b := by
    refine Finset.sum_eq_single a (fun k _ hk => ?_) (by simp)
    by_cases hka : halfSwapMatrix a b c a k = 0
    · rw [hzero a k hka, zero_mul]
    · have hkb : halfSwapMatrix a b c b k = 0 := by
        rw [halfSwapMatrix_apply] at hka ⊢
        rw [Equiv.swap_apply_of_ne_of_ne hab hac] at hka
        rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
        rw [Equiv.swap_apply_left] at hka
        by_cases hkb' : b = k
        · subst hkb'
          simp [hab, Ne.symm hbc]
        · simp_all
      rw [Matrix.star_apply, hzero b k hkb, star_zero, mul_zero]
  rw [hsingle] at horth
  have haa : ‖U a a‖ ^ 2 = 1 / 2 := by
    rw [hent, halfSwapMatrix_apply, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
    simp [Ne.symm hab]
  have hba : ‖U b a‖ ^ 2 = 1 / 2 := by
    rw [hent, halfSwapMatrix_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    simp [hac.symm]
  rcases mul_eq_zero.mp horth with h | h
  · rw [h, norm_zero] at haa; norm_num at haa
  · rw [Matrix.star_apply, star_eq_zero] at h
    rw [h, norm_zero] at hba; norm_num at hba

/-- **After Lemma X.3: for `d ≥ 3`, not every doubly stochastic matrix has the form
`(|U(η,ζ)|²)` with `U` unitary.** -/
theorem exists_doublyStochastic_not_unistochastic (hd : 3 ≤ Fintype.card n) :
    ∃ P ∈ doublyStochastic ℝ n, ∀ U ∈ Matrix.unitaryGroup n ℂ,
      (Matrix.of fun i j => ‖U i j‖ ^ 2) ≠ P := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := (Fintype.two_lt_card_iff (α := n)).mp (by omega)
  exact ⟨halfSwapMatrix a b c, halfSwapMatrix_mem_doublyStochastic a b c,
    fun U hU => halfSwapMatrix_not_unistochastic hab hac hbc hU⟩

/-- The printed `3 × 3` example `½[[1,1,0],[1,0,1],[0,1,1]]` is doubly stochastic and is not
`(|U(η,ζ)|²)` for any unitary `U`. -/
theorem fin_three_example_not_unistochastic :
    !![1 / 2, 1 / 2, 0; 1 / 2, 0, 1 / 2; 0, 1 / 2, 1 / 2] ∈ doublyStochastic ℝ (Fin 3) ∧
      ∀ U ∈ Matrix.unitaryGroup (Fin 3) ℂ,
        (Matrix.of fun i j => ‖U i j‖ ^ 2) ≠
          !![(1 / 2 : ℝ), 1 / 2, 0; 1 / 2, 0, 1 / 2; 0, 1 / 2, 1 / 2] := by
  rw [← halfSwapMatrix_fin_three]
  exact ⟨halfSwapMatrix_mem_doublyStochastic _ _ _,
    fun U hU => halfSwapMatrix_not_unistochastic (by decide) (by decide) (by decide) hU⟩

/-- The statement after Lemma X.3 at a vertex with `d = #E_v^∂ ≥ 3` incident ends. -/
theorem vertexLaw_not_unistochastic {Γ : FiniteMetricGraph} (v : Γ.Vertex)
    (hd : 3 ≤ Fintype.card (Γ.IncidentEnds v)) :
    ∃ P ∈ doublyStochastic ℝ (Γ.IncidentEnds v), ∀ U ∈ Matrix.unitaryGroup (Γ.IncidentEnds v) ℂ,
      (Matrix.of fun i j => ‖U i j‖ ^ 2) ≠ P := by
  classical
  exact exists_doublyStochastic_not_unistochastic hd

end Unistochastic

/-! ### Remark X.6: detailed balance -/

section DetailedBalance

variable {n : Type*}

/-- **Detailed balance** of a transition matrix `P` with respect to the weights `m`:
`m(η) P(η,ζ) = m(ζ) P(ζ,η)`, i.e. reversibility of the boundary Markov chain with respect to the
measure `m`.  For the counting measure `m ≡ 1` this is `P(η,ζ) = P(ζ,η)`
(`detailedBalance_one_iff`). -/
def DetailedBalance (m : n → ℝ) (P : Matrix n n ℝ) : Prop :=
  ∀ i j, m i * P i j = m j * P j i

/-- Reversibility with respect to counting measure is `P(η,ζ) = P(ζ,η)`. -/
theorem detailedBalance_one_iff (P : Matrix n n ℝ) :
    DetailedBalance (fun _ => 1) P ↔ ∀ i j, P i j = P j i := by
  simp [DetailedBalance]

/-- **Remark X.6.**  A row-stochastic matrix in detailed balance with respect to counting measure
is doubly stochastic. -/
theorem mem_doublyStochastic_of_detailedBalance [Fintype n] [DecidableEq n] {P : Matrix n n ℝ}
    (hnn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (hdb : DetailedBalance (fun _ => 1) P) : P ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨hnn, hrow, fun j => ?_⟩
  rw [← hrow j]
  exact Finset.sum_congr rfl fun i _ => (detailedBalance_one_iff P).mp hdb i j

/-- **Remark X.6, strictness.**  For `d ≥ 3` detailed balance is strictly stronger than double
stochasticity: the permutation matrix of a 3-cycle is doubly stochastic but not symmetric. -/
theorem exists_doublyStochastic_not_detailedBalance [Fintype n] [DecidableEq n]
    (hd : 3 ≤ Fintype.card n) :
    ∃ P ∈ doublyStochastic ℝ n, ¬ DetailedBalance (fun _ => 1) P := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := (Fintype.two_lt_card_iff (α := n)).mp (by omega)
  refine ⟨(Equiv.swap a b * Equiv.swap b c).permMatrix ℝ, permMatrix_mem_doublyStochastic, ?_⟩
  intro hdb
  have h := (detailedBalance_one_iff _).mp hdb a b
  rw [permMatrix_apply', permMatrix_apply'] at h
  simp [Equiv.swap_apply_of_ne_of_ne hab hac,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc), Ne.symm hac] at h

/-- For `d ≤ 2` the two notions coincide: every doubly stochastic matrix is symmetric.  So the
strictness in Remark X.6 is a statement about vertices with at least three incident ends. -/
theorem detailedBalance_of_mem_doublyStochastic_of_card_le_two [Fintype n] [DecidableEq n]
    (hd : Fintype.card n ≤ 2)
    {P : Matrix n n ℝ} (hP : P ∈ doublyStochastic ℝ n) : DetailedBalance (fun _ => 1) P := by
  classical
  rw [detailedBalance_one_iff]
  intro i j
  by_cases hij : i = j
  · rw [hij]
  have huniv : ({i, j} : Finset n) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_pair hij]
    have : 2 ≤ Fintype.card n := by
      have := Finset.card_le_univ ({i, j} : Finset n)
      rwa [Finset.card_pair hij] at this
    omega
  rw [mem_doublyStochastic_iff_sum] at hP
  have hrow := hP.2.1 i
  have hcol := hP.2.2 i
  rw [← huniv, Finset.sum_pair hij] at hrow hcol
  linarith

/-- **Remark X.6 at a vertex.**  A Markov vertex law in detailed balance with respect to counting
measure preserves the end flux. -/
theorem MechanicalPotential.preservesGermCounting_of_detailedBalance {Γ : FiniteMetricGraph}
    {v : Γ.Vertex} {P : Matrix (Γ.IncidentEnds v) (Γ.IncidentEnds v) ℝ}
    (hP : MechanicalPotential.IsMarkovVertexLaw P) (hdb : DetailedBalance (fun _ => 1) P) :
    MechanicalPotential.PreservesGermCounting P := by
  classical
  exact ((MechanicalPotential.mem_doublyStochastic_iff_vertexLaw P).mp
    (mem_doublyStochastic_of_detailedBalance hP.1 hP.2 hdb)).2

end DetailedBalance

/-! ### Remark X.5: the transport interpretation -/

section Transport

/-- A counting fact: the `0/1` matrix of a map `T` has all column sums `1`
exactly when `T` is a bijection. -/
theorem sum_ite_eq_one_iff_bijective {n : Type*} [Fintype n] [DecidableEq n] (T : n → n) :
    (∀ j, ∑ i, (if T i = j then (1 : ℝ) else 0) = 1) ↔ Function.Bijective T := by
  constructor
  · intro h
    refine (Finite.injective_iff_bijective.mp ?_)
    refine Finite.injective_iff_surjective.mpr ?_
    intro j
    have hj := h j
    rw [Finset.sum_boole, Nat.cast_eq_one, Finset.card_eq_one] at hj
    obtain ⟨i, hi⟩ := hj
    have : i ∈ Finset.univ.filter (fun i => T i = j) := by
      rw [hi]; exact Finset.mem_singleton_self i
    exact ⟨i, (Finset.mem_filter.mp this).2⟩
  · intro hT j
    rw [Finset.sum_boole, Nat.cast_eq_one, Finset.card_eq_one]
    obtain ⟨i, hi⟩ := hT.2 j
    refine ⟨i, ?_⟩
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hk => hT.1 (hk.trans hi.symm), fun hk => hk ▸ hi⟩

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Transport plans on finite spaces** between the mass vectors `a` on `α` and `b` on `β`: the
nonnegative mass matrices on `α × β` with marginals `a` and `b`. -/
def TransportPlans (a : α → ℝ) (b : β → ℝ) : Set (Matrix α β ℝ) :=
  {π | (∀ i j, 0 ≤ π i j) ∧ (∀ i, ∑ j, π i j = a i) ∧ ∀ j, ∑ i, π i j = b j}

/-- A plan is **induced by a transport map** `T : α → β` from the source `a` when it is the image
`(id, T)_# a`: all the mass `a i` at `i` is sent to `T i`. -/
def IsMapInduced [DecidableEq β] (a : α → ℝ) (π : Matrix α β ℝ) : Prop :=
  ∃ T : α → β, ∀ i j, π i j = if T i = j then a i else 0

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Remark X.5.**  The flux-preserving matrices are exactly the transport plans with counting
measure as both marginals. -/
theorem mem_transportPlans_one_iff (P : Matrix n n ℝ) :
    P ∈ TransportPlans (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) ↔ P ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  rfl

/-- **Remark X.5, normalization.**  `P / d` couples the uniform probability vector on the ends with
itself exactly when `P` is doubly stochastic. -/
theorem smul_mem_transportPlans_uniform_iff [Nonempty n] (P : Matrix n n ℝ) :
    ((Fintype.card n : ℝ)⁻¹ • P) ∈
        TransportPlans (fun _ => (Fintype.card n : ℝ)⁻¹) (fun _ => (Fintype.card n : ℝ)⁻¹) ↔
      P ∈ doublyStochastic ℝ n := by
  have hd : (0 : ℝ) < (Fintype.card n : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  rw [mem_doublyStochastic_iff_sum]
  simp only [TransportPlans, Set.mem_setOf_eq, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact forall₂_congr fun i j => (mul_nonneg_iff_of_pos_left hd)
  · exact forall_congr' fun i => ⟨fun h => mul_left_cancel₀ hd.ne' (h.trans (mul_one _).symm),
      fun h => by rw [h, mul_one]⟩
  · exact forall_congr' fun i => ⟨fun h => mul_left_cancel₀ hd.ne' (h.trans (mul_one _).symm),
      fun h => by rw [h, mul_one]⟩

/-- **Remark X.5: permutation laws are exactly the map-induced plans.**  A flux-preserving matrix
is induced by a transport map exactly when it is a permutation matrix. -/
theorem isMapInduced_iff_permMatrix {P : Matrix n n ℝ} (hP : P ∈ doublyStochastic ℝ n) :
    IsMapInduced (fun _ => (1 : ℝ)) P ↔ ∃ σ : Equiv.Perm n, σ.permMatrix ℝ = P := by
  constructor
  · rintro ⟨T, hT⟩
    have hcol : ∀ j, ∑ i, (if T i = j then (1 : ℝ) else 0) = 1 := fun j =>
      (Finset.sum_congr rfl fun i _ => (hT i j).symm).trans
        ((mem_doublyStochastic_iff_sum.mp hP).2.2 j)
    refine ⟨Equiv.ofBijective T ((sum_ite_eq_one_iff_bijective T).mp hcol), ?_⟩
    ext i j
    rw [permMatrix_apply', hT i j]
    rfl
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, fun i j => permMatrix_apply' σ i j⟩

/-- **Remark X.5.**  In the finite uniform-marginal setting the extreme plans are exactly the
map-induced ones (by Theorem X.4 these are the deterministic vertex laws). -/
theorem extremePoints_transportPlans_one :
    Set.extremePoints ℝ (TransportPlans (fun _ : n => (1 : ℝ)) (fun _ : n => (1 : ℝ))) =
      {P ∈ TransportPlans (fun _ : n => (1 : ℝ)) (fun _ : n => (1 : ℝ)) |
        IsMapInduced (fun _ => (1 : ℝ)) P} := by
  have hset : TransportPlans (fun _ : n => (1 : ℝ)) (fun _ : n => (1 : ℝ)) =
      (doublyStochastic ℝ n : Set (Matrix n n ℝ)) := by
    ext P; exact mem_transportPlans_one_iff P
  rw [hset, extremePoints_doublyStochastic]
  ext P
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨permMatrix_mem_doublyStochastic,
      (isMapInduced_iff_permMatrix permMatrix_mem_doublyStochastic).mpr ⟨σ, rfl⟩⟩
  · rintro ⟨hP, hmap⟩
    exact (isMapInduced_iff_permMatrix hP).mp hmap

/-- The source `δ₀` on the two-point space. -/
def diracZero : Fin 2 → ℝ := ![1, 0]

/-- The target `½(δ₀ + δ₁)` on the two-point space. -/
noncomputable def halfHalf : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- The product plan `δ₀ ⊗ ½(δ₀ + δ₁)`. -/
noncomputable def splitPlan : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 0, 0]

/-- The transport problem from `δ₀` to `½(δ₀ + δ₁)` has exactly one plan, the product plan. -/
theorem transportPlans_diracZero_halfHalf :
    TransportPlans diracZero halfHalf = {splitPlan} := by
  ext π
  simp only [TransportPlans, Set.mem_setOf_eq, Set.mem_singleton_iff, diracZero, halfHalf,
    Fin.sum_univ_two, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨⟨⟨h00, h01⟩, h10, h11⟩, ⟨_, hr1⟩, hc0, hc1⟩
    have e10 : π 1 0 = 0 := by linarith
    have e11 : π 1 1 = 0 := by linarith
    ext i j
    fin_cases i <;> fin_cases j <;> simp [splitPlan] <;> linarith
  · rintro rfl
    simp [splitPlan]
    norm_num

/-- **Remark X.5: for general transport problems, extreme plans need not be induced by maps.**
From `δ₀` to `½(δ₀ + δ₁)` on a two-point space the only plan — hence an extreme plan — splits the
mass at `0`, so it is not of the form `(id, T)_# δ₀`. -/
theorem extreme_plan_not_mapInduced :
    splitPlan ∈ Set.extremePoints ℝ (TransportPlans diracZero halfHalf) ∧
      ¬ IsMapInduced diracZero splitPlan := by
  refine ⟨by rw [transportPlans_diracZero_halfHalf, extremePoints_singleton]; rfl, ?_⟩
  rintro ⟨T, hT⟩
  have h0 := hT 0 0
  have h1 := hT 0 1
  simp only [splitPlan, diracZero, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h0 h1
  split_ifs at h0 <;> norm_num at h0

end Transport

end HamiltonianMetricGraphs
