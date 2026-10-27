/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Proposition VII.1: the suspension criterion for flow invariance
-/

import Mathlib

/-!
# Invariance of a time measure built from a finite suspension (Proposition VII.1)

The proof of Proposition VII.1 in the paper reads: on every bounded time interval the flow on a
regular energy surface is a concatenation of finitely many measure-preserving edge translations and
vertex permutations.  This module isolates the measure-theoretic content of that sentence as an
abstract criterion.

Let `Φ` be a one-parameter group of measurable maps of a measurable space `X`, and let `z i`
(`i` in a finite type) be finitely many distinct points with positive *first return times* `τ i`
to the finite set `{z j}`: `Φ_{τ i} (z i)` is again some `z j`, and `Φ_u (z i)` is none of the
`z j` for `0 < u < τ i`.  If a measure `ν` is the sum of the images of Lebesgue measure on
`[0, τ i)` under the orbit maps `u ↦ Φ_u (z i)`, then `ν` is `Φ`-invariant
(`measure_preimage_eq_of_suspension`).

The proof: the return map `i ↦ j` is injective (two orbits arriving at the same `z j` coincide
just before, by the first-return property), hence a permutation of the finite index set.  For
`0 ≤ t ≤ min τ`, shifting `[0, τ i)` by `t` moves the piece `[τ i, τ i + t)` onto `[0, t)` of the
successor orbit, and summing over the permutation gives back `ν`.  Larger times follow from the
group law.
-/

namespace HamiltonianMetricGraphs

open MeasureTheory Set
open scoped ENNReal

section Suspension

variable {X : Type*} [MeasurableSpace X] (Φ : X → ℝ → X)

/-- Splitting a half-open interval of a (not necessarily measurable) set. -/
theorem volume_Ico_inter_split (A : Set ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    volume (Ico a c ∩ A) = volume (Ico a b ∩ A) + volume (Ico b c ∩ A) := by
  rw [← measure_inter_add_sdiff (Ico a c ∩ A) (measurableSet_Ico : MeasurableSet (Ico a b))]
  congr 2
  · ext x
    simp only [mem_inter_iff, mem_Ico]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, h3⟩, -, h5⟩
      exact ⟨⟨h1, h5⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨h1, lt_of_lt_of_le h2 hbc⟩, h3⟩, h1, h2⟩
  · ext x
    simp only [mem_inter_iff, mem_sdiff, mem_Ico, not_and, not_lt]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨h4 h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨le_trans hab h1, h2⟩, h3⟩, fun _ => h1⟩

/-- Translation invariance of Lebesgue measure on an interval piece of a set. -/
theorem volume_Ico_inter_shift (A : Set ℝ) (a b t : ℝ) :
    volume (Ico a b ∩ (fun u => u + t) ⁻¹' A) = volume (Ico (a + t) (b + t) ∩ A) := by
  have h : Ico a b ∩ (fun u => u + t) ⁻¹' A =
      (fun u => u + t) ⁻¹' (Ico (a + t) (b + t) ∩ A) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
  rw [h, measure_preimage_add_right]

/-- **The suspension criterion for invariance.**  A measure which is the sum of the images of
Lebesgue measure on `[0, τ i)` under the orbit maps `u ↦ Φ_u (z i)` of finitely many distinct
points with first return times `τ i` to the set `{z j}` is invariant under the flow. -/
theorem measure_preimage_eq_of_suspension
    (hΦ0 : ∀ x, Φ x 0 = x) (hΦadd : ∀ x s t, Φ (Φ x s) t = Φ x (s + t))
    (hΦmeas : ∀ t, Measurable fun x => Φ x t)
    {ι : Type*} [Fintype ι] (z : ι → X) (τ : ι → ℝ) (hτ : ∀ i, 0 < τ i)
    (hz : Function.Injective z) (hret : ∀ i, ∃ j, Φ (z i) (τ i) = z j)
    (hfirst : ∀ i j, ∀ u ∈ Ioo 0 (τ i), Φ (z i) u ≠ z j)
    (ν : Measure X)
    (hν : ∀ B, MeasurableSet B →
      ν B = ∑ i, volume (Ico 0 (τ i) ∩ (fun u => Φ (z i) u) ⁻¹' B))
    (t : ℝ) {A : Set X} (hA : MeasurableSet A) :
    ν ((fun x => Φ x t) ⁻¹' A) = ν A := by
  classical
  -- the return permutation
  choose σ hσ using hret
  have hσinj : Function.Injective σ := by
    -- if two orbits arrive at the same point, they coincide just before
    have key : ∀ i j, τ i ≤ τ j → σ i = σ j → i = j := by
      intro i j hij hs
      have h : Φ (z i) (τ i) = Φ (z j) (τ j) := by rw [hσ i, hσ j, hs]
      have hzi : z i = Φ (z j) (τ j - τ i) := by
        have h1 := congrArg (fun x => Φ x (-τ i)) h
        simp only [hΦadd, add_neg_cancel, hΦ0] at h1
        rw [h1, sub_eq_add_neg]
      rcases eq_or_lt_of_le hij with heq | hlt
      · rw [heq, sub_self, hΦ0] at hzi
        exact hz hzi
      · exact absurd hzi.symm
          (hfirst j i (τ j - τ i) ⟨by linarith, by linarith [hτ i]⟩)
    intro i j hs
    rcases le_total (τ i) (τ j) with h | h
    · exact key i j h hs
    · exact (key j i h hs.symm).symm
  have hσbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hσinj
  let eσ : ι ≃ ι := Equiv.ofBijective σ hσbij
  -- notation for the orbit preimages
  set Sp : ι → Set X → Set ℝ := fun i B => (fun u => Φ (z i) u) ⁻¹' B with hSp
  -- invariance for small nonnegative times
  have hsmall : ∀ s, 0 ≤ s → (∀ i, s ≤ τ i) → ∀ B, MeasurableSet B →
      ν ((fun x => Φ x s) ⁻¹' B) = ν B := by
    intro s hs0 hsτ B hB
    rw [hν _ ((hΦmeas s) hB), hν B hB]
    have hterm : ∀ i, volume (Ico 0 (τ i) ∩ (fun u => Φ (z i) u) ⁻¹'
        ((fun x => Φ x s) ⁻¹' B)) =
        volume (Ico s (τ i) ∩ Sp i B) + volume (Ico 0 s ∩ Sp (σ i) B) := by
      intro i
      have h1 : Ico 0 (τ i) ∩ (fun u => Φ (z i) u) ⁻¹' ((fun x => Φ x s) ⁻¹' B) =
          Ico 0 (τ i) ∩ (fun u => u + s) ⁻¹' Sp i B := by
        ext u
        simp only [hSp, mem_inter_iff, mem_preimage, hΦadd]
      rw [h1, volume_Ico_inter_shift, zero_add,
        volume_Ico_inter_split (Sp i B) (hsτ i) (by linarith [hsτ i] : τ i ≤ τ i + s)]
      congr 1
      have h2 : (fun u => u + τ i) ⁻¹' Sp i B = Sp (σ i) B := by
        ext u
        simp only [hSp, mem_preimage, ← hσ i, hΦadd, add_comm u (τ i)]
      have h3 := volume_Ico_inter_shift (Sp i B) 0 s (τ i)
      rw [h2, zero_add, add_comm s (τ i)] at h3
      exact h3.symm
    simp_rw [hterm, Finset.sum_add_distrib]
    rw [show (∑ i, volume (Ico 0 s ∩ Sp (σ i) B)) = ∑ i, volume (Ico 0 s ∩ Sp i B) from
      Equiv.sum_comp eσ (fun i => volume (Ico 0 s ∩ Sp i B)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_comm, ← volume_Ico_inter_split (Sp i B) hs0 (hsτ i)]
  -- a uniform small time
  by_cases hι : Nonempty ι
  swap
  · have hzero : ∀ B, MeasurableSet B → ν B = 0 := by
      intro B hB
      rw [hν B hB]
      haveI : IsEmpty ι := not_nonempty_iff.mp hι
      simp
    rw [hzero A hA, hzero _ ((hΦmeas t) hA)]
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min τ
  set δ := τ i₀ with hδ
  have hδpos : 0 < δ := hτ i₀
  -- invariance for nonnegative times
  have hnonneg : ∀ s, 0 ≤ s → ∀ B, MeasurableSet B → ν ((fun x => Φ x s) ⁻¹' B) = ν B := by
    intro s hs B hB
    obtain ⟨n, hn⟩ := Archimedean.arch s hδpos
    set r := s / (n + 1 : ℝ) with hr
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hr0 : 0 ≤ r := div_nonneg hs hn1.le
    have hrδ : r ≤ δ := by
      rw [hr, div_le_iff₀ hn1]
      have : s ≤ n • δ := hn
      rw [nsmul_eq_mul] at this
      nlinarith
    have hiter : ∀ k : ℕ, ∀ B, MeasurableSet B →
        ν ((fun x => Φ x (k * r)) ⁻¹' B) = ν B := by
      intro k
      induction k with
      | zero =>
        intro B hB
        simp only [Nat.cast_zero, zero_mul, hΦ0, preimage_id']
      | succ k ih =>
        intro B hB
        have hpre : (fun x => Φ x (((k + 1 : ℕ) : ℝ) * r)) ⁻¹' B =
            (fun x => Φ x r) ⁻¹' ((fun x => Φ x (k * r)) ⁻¹' B) := by
          ext x
          simp only [mem_preimage, hΦadd]
          congr! 2
          push_cast
          ring
        rw [hpre, hsmall r hr0 (fun i => le_trans hrδ (hi₀ i)) _ ((hΦmeas _) hB), ih B hB]
    have hs' : s = ((n + 1 : ℕ) : ℝ) * r := by
      rw [hr]
      push_cast
      field_simp
    rw [hs']
    exact hiter (n + 1) B hB
  rcases le_or_gt 0 t with ht | ht
  · exact hnonneg t ht A hA
  · have h := hnonneg (-t) (by linarith) _ ((hΦmeas t) hA)
    have hpre : (fun x => Φ x (-t)) ⁻¹' ((fun x => Φ x t) ⁻¹' A) = A := by
      ext x
      simp only [mem_preimage, hΦadd, neg_add_cancel, hΦ0]
    rw [hpre] at h
    exact h.symm

end Suspension

end HamiltonianMetricGraphs
