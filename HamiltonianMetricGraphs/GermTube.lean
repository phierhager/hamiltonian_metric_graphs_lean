/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager

Lemma VI.3: the germ tube in flux coordinates
-/

import HamiltonianMetricGraphs.VertexTube

/-!
# The outgoing tube of a germ in flux coordinates

The flow box of `exists_germFlowBox` makes the departure flight of a germ `η` the inverse of the
time coordinate `timeAt` on a collar of the germ.  Feeding that into the tube chart of Lemma VI.1
(`lintegral_tube_chart_speed`, and `lintegral_tube_chart_speed_neg` for a germ at the right endpoint
of its edge) identifies the planar Lebesgue measure of the *outgoing tube*

`{departure flight of η at speed r ∈ A, for a time u ∈ (0, s)}`

with the flux measure `r dr ⊗ du`:

`∫⁻_T g dq dp = ∫⁻_A r ∫⁻_{(0,s)} (1_T · g) (departure flight of η at speed r, time u) du dr`

for every Borel subset `T` of the tube (`lintegral_germTube`).  This is the coordinate half of
Lemma VI.3: the other half is that scattering permutes the germs at a fixed speed and reflects the
elapsed time (`map_impactStep_flux_prod`), so the tubes on the two sides of an impact carry the same
measure.

The set `germTube` is the *specification* of the tube: a state of the collar which moves away from
the germ, whose energy leaves the germ with a speed of `A`, and whose travel time from the germ is
in `(0, s)`.  Only the two inclusions matter — a Borel set inside the specification is transported
by the chart — so the specification itself is never required to be Borel.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

open Set MeasureTheory PhysicalEdgeSegment
open FiniteMetricGraph.EdgeEnd (coordinate vertex)
open scoped Topology ENNReal NNReal

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)

/-! ### The speed a germ is left with -/

/-- The inward speed with which the germ `η` is left at the energy `E`. -/
noncomputable def germSpeed (η : Γ.EdgeEnd) (E : ℝ) : ℝ :=
  Real.sqrt (2 * (E - V.vertexValue (vertex Γ η)))

theorem germSpeed_def (η : Γ.EdgeEnd) (E : ℝ) :
    V.germSpeed η E = Real.sqrt (2 * (E - V.vertexValue (vertex Γ η))) := rfl

@[simp] theorem germSpeed_departureEnergy (η : Γ.EdgeEnd) {r : ℝ} (hr : 0 ≤ r) :
    V.germSpeed η (V.departureEnergy η r) = r := by
  rw [V.germSpeed_def, V.departureEnergy_eq η r,
    show 2 * (r ^ 2 / 2 + V.vertexValue (vertex Γ η) - V.vertexValue (vertex Γ η)) = r ^ 2 by ring,
    Real.sqrt_sq hr]

/-- A germ speed inside a window `(r₁, r₂)` with `r₁ > 0` forces the energy into the corresponding
energy window. -/
theorem energy_mem_of_germSpeed {η : Γ.EdgeEnd} {E r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (h : V.germSpeed η E ∈ Ioo r₁ r₂) :
    E ∈ Ioo (r₁ ^ 2 / 2 + V.vertexValue (vertex Γ η))
      (r₂ ^ 2 / 2 + V.vertexValue (vertex Γ η)) := by
  have ht := V.germSpeed_def η E
  have hy : 0 ≤ 2 * (E - V.vertexValue (vertex Γ η)) := by
    by_contra hcon
    rw [not_le] at hcon
    have hle : V.germSpeed η E ≤ 0 := by
      rw [ht]
      calc Real.sqrt (2 * (E - V.vertexValue (vertex Γ η)))
            ≤ Real.sqrt 0 := Real.sqrt_le_sqrt hcon.le
        _ = 0 := Real.sqrt_zero
    linarith [h.1]
  have hsq : V.germSpeed η E ^ 2 = 2 * (E - V.vertexValue (vertex Γ η)) := by
    rw [ht]; exact Real.sq_sqrt hy
  exact ⟨by nlinarith [h.1, hsq], by nlinarith [h.2, hsq, hr₁, h.1]⟩

/-! ### The image of a position window under the time coordinate -/

/-- The time coordinate maps a position window of the classically allowed region onto an interval:
it is continuous and strictly increasing there. -/
theorem timeAt_image_Ioo (e : Γ.Edge) {E α β : ℝ}
    (hdom : ∀ x ∈ Ioo α β, x ∈ V.domain e) (hpos : ∀ x ∈ Ioo α β, V.extension e x < E)
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo α β) {a b : ℝ} (ha : a ∈ Ioo α β) (hb : b ∈ Ioo α β) :
    (fun q => V.timeAt e E q₀ q) '' Ioo a b
      = Ioo (V.timeAt e E q₀ a) (V.timeAt e E q₀ b) := by
  have hmono : StrictMonoOn (fun x => V.timeAt e E q₀ x) (Ioo α β) :=
    V.strictMonoOn_timeAt e hq₀ hdom hpos
  have hIcc : Icc a b ⊆ Ioo α β := fun x hx =>
    ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  have hcont : ContinuousOn (fun x => V.timeAt e E q₀ x) (Icc a b) := fun x hx =>
    ((V.hasDerivAt_timeAt e (hIcc hx) hq₀ hdom hpos).continuousAt).continuousWithinAt
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    have hqmem : q ∈ Ioo α β := ⟨lt_trans ha.1 hq.1, lt_trans hq.2 hb.2⟩
    exact ⟨hmono ha hqmem hq.1, hmono hqmem hb hq.2⟩
  · rcases le_or_gt a b with hab | hab
    · exact intermediate_value_Ioo hab hcont
    · intro y hy
      exact absurd (lt_trans hy.1 hy.2) (asymm (hmono hb ha hab))

/-! ### The outgoing tube of a germ -/

/-- **The specification of the outgoing tube of a germ.**  The states of the collar of radius
`3δ / 4` around the germ `η` which move away from the germ, whose energy leaves `η` with a speed of
`A`, and whose travel time from the germ is in `(0, s)`. -/
def germTube (η : Γ.EdgeEnd) (A : Set ℝ) (δ s : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4) ∧
    V.germSpeed η (V.hamiltonian η.1 x.1 x.2) ∈ A ∧
    0 < -(FiniteMetricGraph.EdgeEnd.sign Γ η) * x.2 ∧
    -(FiniteMetricGraph.EdgeEnd.sign Γ η) *
        V.timeAt η.1 (V.hamiltonian η.1 x.1 x.2) (coordinate Γ η) x.1 ∈ Ioo 0 s}

/-- **The Liouville measure of an outgoing germ tube in flux coordinates.**  The flow box makes the
departure flight the inverse of the time coordinate, so the tube chart of Lemma VI.1 transports
`dq dp` on a Borel subset `T` of the tube to `r dr ⊗ du` on `A × (0, s)`. -/
theorem lintegral_germTube (η : Γ.EdgeEnd) {A : Set ℝ} (hA : MeasurableSet A)
    {r₁ r₂ δ u₀ : ℝ} (hbox : V.GermFlowBox η A r₁ r₂ δ u₀)
    {s : ℝ} (hsu : s ≤ u₀)
    {T : Set (ℝ × ℝ)} (hT : MeasurableSet T) (hTsub : T ⊆ V.germTube η A δ s)
    {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in T, g x ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ r in A, ENNReal.ofReal r *
          ∫⁻ u in Ioo (0 : ℝ) s, T.indicator g (V.departureFlight η r u) := by
  classical
  have hr₁ : 0 < r₁ := hbox.speed_pos
  have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ hbox.speed_le
  have hδ : 0 < δ := hbox.radius_pos
  have hgT : Measurable (T.indicator g) := hg.indicator hT
  -- the position windows
  have hsub34 : Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4) ⊆
      Ioo (coordinate Γ η - δ) (coordinate Γ η + δ) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have ha : coordinate Γ η - 3 * δ / 4 ∈ Ioo (coordinate Γ η - δ) (coordinate Γ η + δ) :=
    ⟨by linarith, by linarith⟩
  have hb : coordinate Γ η + 3 * δ / 4 ∈ Ioo (coordinate Γ η - δ) (coordinate Γ η + δ) :=
    ⟨by linarith, by linarith⟩
  have hq₀ : coordinate Γ η ∈ Ioo (coordinate Γ η - δ) (coordinate Γ η + δ) :=
    ⟨by linarith, by linarith⟩
  -- what membership of the tube gives
  have hTpos : ∀ x ∈ T, x.1 ∈ Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4) :=
    fun x hx => (hTsub hx).1
  have hTA : ∀ x ∈ T, V.germSpeed η (V.hamiltonian η.1 x.1 x.2) ∈ A := fun x hx => (hTsub hx).2.1
  have hTmom : ∀ x ∈ T, 0 < -(FiniteMetricGraph.EdgeEnd.sign Γ η) * x.2 :=
    fun x hx => (hTsub hx).2.2.1
  have hTtime : ∀ x ∈ T, -(FiniteMetricGraph.EdgeEnd.sign Γ η) *
      V.timeAt η.1 (V.hamiltonian η.1 x.1 x.2) (coordinate Γ η) x.1 ∈ Ioo 0 s :=
    fun x hx => (hTsub hx).2.2.2
  have hTJ : ∀ x ∈ T, V.hamiltonian η.1 x.1 x.2 ∈
      Ioo (r₁ ^ 2 / 2 + V.vertexValue (vertex Γ η)) (r₂ ^ 2 / 2 + V.vertexValue (vertex Γ η)) :=
    fun x hx => V.energy_mem_of_germSpeed hr₁ (hbox.speeds (hTA x hx))
  -- the momentum of a state of the tube lies in the strip `(r₁ / 2, 2 r₂)` up to sign
  have hTsq : ∀ x ∈ T, (r₁ / 2) ^ 2 < x.2 ^ 2 ∧ x.2 ^ 2 < (2 * r₂) ^ 2 := by
    intro x hx
    have hcol := abs_lt.mp (hbox.collar x.1 (hsub34 (hTpos x hx)))
    have hJ := hTJ x hx
    have hham : V.hamiltonian η.1 x.1 x.2 = x.2 ^ 2 / 2 + V.extension η.1 x.1 := rfl
    rw [hham] at hJ
    have hsq : r₁ ^ 2 ≤ r₂ ^ 2 := by nlinarith [hbox.speed_le, hr₁]
    exact ⟨by nlinarith [hJ.1, hcol.2], by nlinarith [hJ.2, hcol.1]⟩
  -- the energy window is inside the energy range of the momentum strip
  have hJsub : ∀ q ∈ Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4),
      Ioo (r₁ ^ 2 / 2 + V.vertexValue (vertex Γ η)) (r₂ ^ 2 / 2 + V.vertexValue (vertex Γ η)) ⊆
        Ioo (V.energyOfMomentum η.1 q (r₁ / 2)) (V.energyOfMomentum η.1 q (2 * r₂)) :=
    fun q hq => hbox.energy_subset (hsub34 hq)
  have hp₁ : (0 : ℝ) < r₁ / 2 := by positivity
  have hp₁₂ : r₁ / 2 ≤ 2 * r₂ := by nlinarith [hbox.speed_le, hr₁]
  -- the facts about one speed of the chart that are independent of the orientation
  have hEge : ∀ r ∈ Ioo r₁ r₂, r₁ ^ 2 / 2 + V.vertexValue (vertex Γ η) ≤
      r ^ 2 / 2 + V.vertexValue (vertex Γ η) := by
    intro r hr
    have : r₁ ^ 2 ≤ r ^ 2 := by nlinarith [hr.1, hr₁]
    linarith
  by_cases hbo : η.2 = true
  · -- the germ is the right endpoint of its edge: the flight moves leftward
    have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η = 1 := by
      simp [FiniteMetricGraph.EdgeEnd.sign, hbo]
    have hTneg : ∀ x ∈ T, x.2 < 0 := by
      intro x hx
      have h := hTmom x hx
      rw [hsgn] at h
      linarith
    have hTbox : T ⊆ (Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4)) ×ˢ
        (Ioo (-(2 * r₂)) (-(r₁ / 2))) := by
      intro x hx
      refine ⟨hTpos x hx, ?_, ?_⟩
      · exact by nlinarith [(hTsq x hx).2, hTneg x hx, hr₂]
      · exact by nlinarith [(hTsq x hx).1, hTneg x hx, hr₁]
    -- the tube chart for the leftward flights
    have hchart := V.lintegral_tube_chart_speed_neg η.1 hbox.domain hr₁ hbox.speed_le
      hbox.allowed_window ha hb hq₀ hp₁ hp₁₂ hJsub (T.indicator g) hgT
    -- the left-hand side is the integral over `T`
    have hLHS : ∫⁻ x in (Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4)) ×ˢ
          (Ioo (-(2 * r₂)) (-(r₁ / 2))),
          (Ioo (r₁ ^ 2 / 2 + V.vertexValue (vertex Γ η))
              (r₂ ^ 2 / 2 + V.vertexValue (vertex Γ η))).indicator (fun _ => (1 : ℝ≥0∞))
            (V.hamiltonian η.1 x.1 x.2) * T.indicator g x ∂(volume : Measure (ℝ × ℝ))
        = ∫⁻ x in T, g x ∂(volume : Measure (ℝ × ℝ)) := by
      have hfun : ∀ x : ℝ × ℝ,
          (Ioo (r₁ ^ 2 / 2 + V.vertexValue (vertex Γ η))
              (r₂ ^ 2 / 2 + V.vertexValue (vertex Γ η))).indicator (fun _ => (1 : ℝ≥0∞))
            (V.hamiltonian η.1 x.1 x.2) * T.indicator g x = T.indicator g x := by
        intro x
        by_cases hx : x ∈ T
        · simp only [Set.indicator_of_mem (hTJ x hx), one_mul]
        · simp only [Set.indicator_of_notMem hx, mul_zero]
      simp_rw [hfun]
      rw [lintegral_indicator hT, Measure.restrict_restrict hT,
        Set.inter_eq_self_of_subset_left hTbox]
    rw [hLHS] at hchart
    rw [hchart]
    -- the right-hand side is the flux integral over `A`
    have hAind : ∫⁻ r in Ioo r₁ r₂,
          A.indicator (fun r => ENNReal.ofReal r *
            ∫⁻ u in Ioo (0 : ℝ) s, T.indicator g (V.departureFlight η r u)) r
        = ∫⁻ r in A, ENNReal.ofReal r *
            ∫⁻ u in Ioo (0 : ℝ) s, T.indicator g (V.departureFlight η r u) := by
      rw [lintegral_indicator hA, Measure.restrict_restrict hA,
        Set.inter_eq_self_of_subset_left hbox.speeds]
    rw [← hAind]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    -- one speed of the chart
    set E : ℝ := r ^ 2 / 2 + V.vertexValue (vertex Γ η) with hEdef
    have hallow := hbox.allowed (E := E) (hEge r hr)
    set f : ℝ → ℝ := fun q => V.timeAt η.1 E (coordinate Γ η) q with hfdef
    have himg : f '' Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4)
        = Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)) :=
      V.timeAt_image_Ioo η.1 hbox.domain hallow hq₀ ha hb
    have hinj : InjOn f (Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4)) :=
      ((V.strictMonoOn_timeAt η.1 hq₀ hbox.domain hallow).injOn).mono hsub34
    rw [himg]
    -- the inverse chart point
    have hinvmem : ∀ u ∈ Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)),
        Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4)) u ∈
            Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4) ∧
          f (Function.invFunOn f
            (Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4)) u) = u := by
      intro u hu
      rw [← himg] at hu
      obtain ⟨q, hq, hqu⟩ := hu
      exact ⟨Function.invFunOn_mem ⟨q, hq, hqu⟩, Function.invFunOn_eq ⟨q, hq, hqu⟩⟩
    have hHinv : ∀ u ∈ Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)),
        V.hamiltonian η.1
            (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u)
            (-V.speedAt η.1 E (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u)) = E := by
      intro u hu
      have h := V.hamiltonian_speedAt η.1 (ε := -1) (by norm_num)
        (le_of_lt (hallow _ (hsub34 (hinvmem u hu).1)))
      rwa [neg_one_mul] at h
    -- membership of the tube forces the speed and the time
    have hΘmem : ∀ u ∈ Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)),
        ((Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
            (coordinate Γ η + 3 * δ / 4)) u,
          -V.speedAt η.1 E (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
            (coordinate Γ η + 3 * δ / 4)) u)) ∈ T) → r ∈ A ∧ u ∈ Ioo (-s) 0 := by
      intro u hu hmem
      have hH := hHinv u hu
      have hA' := hTA _ hmem
      have htime := hTtime _ hmem
      rw [hH] at hA' htime
      have hrA : r ∈ A := by
        rwa [hEdef, ← V.departureEnergy_eq η r,
          V.germSpeed_departureEnergy η (le_of_lt (lt_trans hr₁ hr.1))] at hA'
      refine ⟨hrA, ?_⟩
      have hfu : V.timeAt η.1 E (coordinate Γ η)
          (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
            (coordinate Γ η + 3 * δ / 4)) u) = u := (hinvmem u hu).2
      rw [hfu, hsgn] at htime
      exact ⟨by linarith [htime.2], by linarith [htime.1]⟩
    by_cases hrA : r ∈ A
    · -- the flight realizes the chart
      have hEr : E = V.departureEnergy η r := by rw [hEdef, V.departureEnergy_eq η r]
      have hflight : ∀ u ∈ Ioo (0 : ℝ) s,
          (V.departureFlight η r u).1 ∈
              Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4) ∧
            f (V.departureFlight η r u).1 = -u ∧
            (V.departureFlight η r u).2 =
              -V.speedAt η.1 E (V.departureFlight η r u).1 := by
        intro u hu
        have hu' : u ∈ Icc (0 : ℝ) u₀ := ⟨hu.1.le, le_trans hu.2.le hsu⟩
        have hp := abs_le.mp (hbox.position r hrA u hu')
        have hti := hbox.time r hrA u hu'
        have hmo := hbox.momentum r hrA u hu'
        have hen := hbox.energy r hrA u hu'
        rw [hsgn] at hti hmo
        refine ⟨⟨by linarith [hp.1], by linarith [hp.2]⟩, ?_, ?_⟩
        · rw [hfdef]
          simp only
          rw [hEr, hti]
          ring
        · refine V.momentum_eq_neg_speedAt η.1 (by linarith [hmo]) ?_
          rw [hen, ← hEr]
      have hIoosub : Ioo (-s) (0 : ℝ) ⊆
          Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)) := by
        intro u hu
        rw [← himg]
        refine ⟨(V.departureFlight η r (-u)).1, (hflight (-u) ⟨by linarith [hu.2],
          by linarith [hu.1]⟩).1, ?_⟩
        have h := (hflight (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩).2.1
        rw [h]
        ring
      -- restrict the inner integral to the time window
      have hinner : ∀ u ∈ Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)),
          T.indicator g (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u,
            -V.speedAt η.1 E (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u))
            = (Ioo (-s) (0 : ℝ)).indicator (fun u =>
                T.indicator g (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
                    (coordinate Γ η + 3 * δ / 4)) u,
                  -V.speedAt η.1 E (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
                    (coordinate Γ η + 3 * δ / 4)) u))) u := by
        intro u hu
        by_cases huw : u ∈ Ioo (-s) (0 : ℝ)
        · rw [Set.indicator_of_mem huw]
        · rw [Set.indicator_of_notMem huw, Set.indicator_of_notMem]
          intro hcon
          exact huw (hΘmem u hu hcon).2
      rw [setLIntegral_congr_fun measurableSet_Ioo hinner, lintegral_indicator measurableSet_Ioo,
        Measure.restrict_restrict measurableSet_Ioo,
        Set.inter_eq_self_of_subset_left hIoosub]
      -- the chart point is the flight
      have hchartpt : ∀ u ∈ Ioo (-s) (0 : ℝ),
          T.indicator g (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u,
            -V.speedAt η.1 E (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u))
            = T.indicator g (V.departureFlight η r (-u)) := by
        intro u hu
        have hu' : -u ∈ Ioo (0 : ℝ) s := ⟨by linarith [hu.2], by linarith [hu.1]⟩
        obtain ⟨hmem, htime, hmom⟩ := hflight (-u) hu'
        have hfeq : f (V.departureFlight η r (-u)).1 = u := by rw [htime]; ring
        have hinvq : Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
            (coordinate Γ η + 3 * δ / 4)) u = (V.departureFlight η r (-u)).1 := by
          have h := hinj.leftInvOn_invFunOn hmem
          rwa [hfeq] at h
        rw [hinvq, ← hmom]
      rw [setLIntegral_congr_fun measurableSet_Ioo hchartpt]
      -- reflect the time
      have hnegmp := Measure.measurePreserving_neg (volume : Measure ℝ)
      have hrefl := hnegmp.setLIntegral_comp_preimage_emb
        (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding
        (fun u => T.indicator g (V.departureFlight η r (-u))) (Ioo (-s) (0 : ℝ))
      have hpre : (fun u : ℝ => -u) ⁻¹' Ioo (-s) (0 : ℝ) = Ioo (0 : ℝ) s := by
        ext u
        constructor
        · intro hu
          exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
        · intro hu
          exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
      rw [Set.indicator_of_mem hrA]
      refine congrArg (fun y => ENNReal.ofReal r * y) ?_
      rw [← hrefl, hpre]
      refine setLIntegral_congr_fun measurableSet_Ioo (fun u _ => ?_)
      norm_num
    · -- no state over this speed belongs to the tube
      have hzero : ∀ u ∈ Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)),
          T.indicator g (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u,
            -V.speedAt η.1 E (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u)) = 0 := by
        intro u hu
        refine Set.indicator_of_notMem (fun hcon => hrA (hΘmem u hu hcon).1) g
      rw [setLIntegral_congr_fun measurableSet_Ioo hzero, lintegral_zero, mul_zero,
        Set.indicator_of_notMem hrA]
  · -- the germ is the left endpoint of its edge: the flight moves rightward
    have hbo' : η.2 = false := by
      cases h : η.2 with
      | false => rfl
      | true => exact absurd h hbo
    have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η = -1 := by
      simp [FiniteMetricGraph.EdgeEnd.sign, hbo']
    have hTpos' : ∀ x ∈ T, 0 < x.2 := by
      intro x hx
      have h := hTmom x hx
      rw [hsgn] at h
      linarith
    have hTbox : T ⊆ (Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4)) ×ˢ
        (Ioo (r₁ / 2) (2 * r₂)) := by
      intro x hx
      refine ⟨hTpos x hx, ?_, ?_⟩
      · exact by nlinarith [(hTsq x hx).1, hTpos' x hx, hr₁]
      · exact by nlinarith [(hTsq x hx).2, hTpos' x hx, hr₂]
    have hchart := V.lintegral_tube_chart_speed η.1 hbox.domain hr₁ hbox.speed_le
      hbox.allowed_window ha hb hq₀ hp₁ hp₁₂ hJsub (T.indicator g) hgT
    have hLHS : ∫⁻ x in (Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4)) ×ˢ
          (Ioo (r₁ / 2) (2 * r₂)),
          (Ioo (r₁ ^ 2 / 2 + V.vertexValue (vertex Γ η))
              (r₂ ^ 2 / 2 + V.vertexValue (vertex Γ η))).indicator (fun _ => (1 : ℝ≥0∞))
            (V.hamiltonian η.1 x.1 x.2) * T.indicator g x ∂(volume : Measure (ℝ × ℝ))
        = ∫⁻ x in T, g x ∂(volume : Measure (ℝ × ℝ)) := by
      have hfun : ∀ x : ℝ × ℝ,
          (Ioo (r₁ ^ 2 / 2 + V.vertexValue (vertex Γ η))
              (r₂ ^ 2 / 2 + V.vertexValue (vertex Γ η))).indicator (fun _ => (1 : ℝ≥0∞))
            (V.hamiltonian η.1 x.1 x.2) * T.indicator g x = T.indicator g x := by
        intro x
        by_cases hx : x ∈ T
        · simp only [Set.indicator_of_mem (hTJ x hx), one_mul]
        · simp only [Set.indicator_of_notMem hx, mul_zero]
      simp_rw [hfun]
      rw [lintegral_indicator hT, Measure.restrict_restrict hT,
        Set.inter_eq_self_of_subset_left hTbox]
    rw [hLHS] at hchart
    rw [hchart]
    have hAind : ∫⁻ r in Ioo r₁ r₂,
          A.indicator (fun r => ENNReal.ofReal r *
            ∫⁻ u in Ioo (0 : ℝ) s, T.indicator g (V.departureFlight η r u)) r
        = ∫⁻ r in A, ENNReal.ofReal r *
            ∫⁻ u in Ioo (0 : ℝ) s, T.indicator g (V.departureFlight η r u) := by
      rw [lintegral_indicator hA, Measure.restrict_restrict hA,
        Set.inter_eq_self_of_subset_left hbox.speeds]
    rw [← hAind]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    set E : ℝ := r ^ 2 / 2 + V.vertexValue (vertex Γ η) with hEdef
    have hallow := hbox.allowed (E := E) (hEge r hr)
    set f : ℝ → ℝ := fun q => V.timeAt η.1 E (coordinate Γ η) q with hfdef
    have himg : f '' Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4)
        = Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)) :=
      V.timeAt_image_Ioo η.1 hbox.domain hallow hq₀ ha hb
    have hinj : InjOn f (Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4)) :=
      ((V.strictMonoOn_timeAt η.1 hq₀ hbox.domain hallow).injOn).mono hsub34
    rw [himg]
    have hinvmem : ∀ u ∈ Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)),
        Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4)) u ∈
            Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4) ∧
          f (Function.invFunOn f
            (Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4)) u) = u := by
      intro u hu
      rw [← himg] at hu
      obtain ⟨q, hq, hqu⟩ := hu
      exact ⟨Function.invFunOn_mem ⟨q, hq, hqu⟩, Function.invFunOn_eq ⟨q, hq, hqu⟩⟩
    have hHinv : ∀ u ∈ Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)),
        V.hamiltonian η.1
            (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u)
            (V.speedAt η.1 E (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u)) = E := by
      intro u hu
      have h := V.hamiltonian_speedAt η.1 (ε := 1) (by norm_num)
        (le_of_lt (hallow _ (hsub34 (hinvmem u hu).1)))
      rwa [one_mul] at h
    have hΘmem : ∀ u ∈ Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)),
        ((Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
            (coordinate Γ η + 3 * δ / 4)) u,
          V.speedAt η.1 E (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
            (coordinate Γ η + 3 * δ / 4)) u)) ∈ T) → r ∈ A ∧ u ∈ Ioo (0 : ℝ) s := by
      intro u hu hmem
      have hH := hHinv u hu
      have hA' := hTA _ hmem
      have htime := hTtime _ hmem
      rw [hH] at hA' htime
      have hrA : r ∈ A := by
        rwa [hEdef, ← V.departureEnergy_eq η r,
          V.germSpeed_departureEnergy η (le_of_lt (lt_trans hr₁ hr.1))] at hA'
      refine ⟨hrA, ?_⟩
      have hfu : V.timeAt η.1 E (coordinate Γ η)
          (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
            (coordinate Γ η + 3 * δ / 4)) u) = u := (hinvmem u hu).2
      rw [hfu, hsgn] at htime
      exact ⟨by linarith [htime.1], by linarith [htime.2]⟩
    by_cases hrA : r ∈ A
    · have hEr : E = V.departureEnergy η r := by rw [hEdef, V.departureEnergy_eq η r]
      have hflight : ∀ u ∈ Ioo (0 : ℝ) s,
          (V.departureFlight η r u).1 ∈
              Ioo (coordinate Γ η - 3 * δ / 4) (coordinate Γ η + 3 * δ / 4) ∧
            f (V.departureFlight η r u).1 = u ∧
            (V.departureFlight η r u).2 = V.speedAt η.1 E (V.departureFlight η r u).1 := by
        intro u hu
        have hu' : u ∈ Icc (0 : ℝ) u₀ := ⟨hu.1.le, le_trans hu.2.le hsu⟩
        have hp := abs_le.mp (hbox.position r hrA u hu')
        have hti := hbox.time r hrA u hu'
        have hmo := hbox.momentum r hrA u hu'
        have hen := hbox.energy r hrA u hu'
        rw [hsgn] at hti hmo
        refine ⟨⟨by linarith [hp.1], by linarith [hp.2]⟩, ?_, ?_⟩
        · rw [hfdef]
          simp only
          rw [hEr, hti]
          ring
        · refine V.momentum_eq_speedAt η.1 (by linarith [hmo]) ?_
          rw [hen, ← hEr]
      have hIoosub : Ioo (0 : ℝ) s ⊆
          Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)) := by
        intro u hu
        rw [← himg]
        exact ⟨(V.departureFlight η r u).1, (hflight u hu).1, (hflight u hu).2.1⟩
      have hinner : ∀ u ∈ Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)),
          T.indicator g (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u,
            V.speedAt η.1 E (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u))
            = (Ioo (0 : ℝ) s).indicator (fun u =>
                T.indicator g (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
                    (coordinate Γ η + 3 * δ / 4)) u,
                  V.speedAt η.1 E (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
                    (coordinate Γ η + 3 * δ / 4)) u))) u := by
        intro u hu
        by_cases huw : u ∈ Ioo (0 : ℝ) s
        · rw [Set.indicator_of_mem huw]
        · rw [Set.indicator_of_notMem huw, Set.indicator_of_notMem]
          intro hcon
          exact huw (hΘmem u hu hcon).2
      rw [setLIntegral_congr_fun measurableSet_Ioo hinner, lintegral_indicator measurableSet_Ioo,
        Measure.restrict_restrict measurableSet_Ioo,
        Set.inter_eq_self_of_subset_left hIoosub]
      have hchartpt : ∀ u ∈ Ioo (0 : ℝ) s,
          T.indicator g (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u,
            V.speedAt η.1 E (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u))
            = T.indicator g (V.departureFlight η r u) := by
        intro u hu
        obtain ⟨hmem, htime, hmom⟩ := hflight u hu
        have hinvq : Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
            (coordinate Γ η + 3 * δ / 4)) u = (V.departureFlight η r u).1 := by
          have h := hinj.leftInvOn_invFunOn hmem
          rwa [htime] at h
        rw [hinvq, ← hmom]
      rw [setLIntegral_congr_fun measurableSet_Ioo hchartpt, Set.indicator_of_mem hrA]
    · have hzero : ∀ u ∈ Ioo (f (coordinate Γ η - 3 * δ / 4)) (f (coordinate Γ η + 3 * δ / 4)),
          T.indicator g (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u,
            V.speedAt η.1 E (Function.invFunOn f (Ioo (coordinate Γ η - 3 * δ / 4)
              (coordinate Γ η + 3 * δ / 4)) u)) = 0 := by
        intro u hu
        refine Set.indicator_of_notMem (fun hcon => hrA (hΘmem u hu hcon).1) g
      rw [setLIntegral_congr_fun measurableSet_Ioo hzero, lintegral_zero, mul_zero,
        Set.indicator_of_notMem hrA]

/-! ### The incoming tube of a germ -/

/-- **The specification of the incoming tube of a germ.**  The momentum reflection of the outgoing
tube: the states of the collar which move *towards* the germ `η` and reach it, with a speed of `A`,
within the time `s`.  The reflection is the right description because the time reverse of a flight
arriving at `η` with speed `r` is the flight departing `η` with speed `r`. -/
def germTubeIn (η : Γ.EdgeEnd) (A : Set ℝ) (δ s : ℝ) : Set (ℝ × ℝ) :=
  Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) ⁻¹' V.germTube η A δ s

theorem mem_germTubeIn_iff {η : Γ.EdgeEnd} {A : Set ℝ} {δ s : ℝ} {x : ℝ × ℝ} :
    x ∈ V.germTubeIn η A δ s ↔ (x.1, -x.2) ∈ V.germTube η A δ s := Iff.rfl

/-- **The Liouville measure of an incoming germ tube in flux coordinates.**  The momentum
reflection preserves `dq dp`, so the incoming tube carries the same flux measure as the outgoing
one, read along the reversed departure flight. -/
theorem lintegral_germTubeIn (η : Γ.EdgeEnd) {A : Set ℝ} (hA : MeasurableSet A)
    {r₁ r₂ δ u₀ : ℝ} (hbox : V.GermFlowBox η A r₁ r₂ δ u₀)
    {s : ℝ} (hsu : s ≤ u₀)
    {T : Set (ℝ × ℝ)} (hT : MeasurableSet T) (hTsub : T ⊆ V.germTubeIn η A δ s)
    {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in T, g x ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ r in A, ENNReal.ofReal r *
          ∫⁻ u in Ioo (0 : ℝ) s, T.indicator g
            (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) (V.departureFlight η r u)) := by
  classical
  have hRemb : MeasurableEmbedding (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)) :=
    measurableEmbedding_momentumReflection
  have hRmp : MeasurePreserving (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p))
      (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) :=
    measurePreserving_momentumReflection
  have hinv : ∀ x : ℝ × ℝ, Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)
      (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) x) = x :=
    fun x => Prod.ext rfl (neg_neg x.2)
  have hT' : MeasurableSet (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) ⁻¹' T) := hRemb.measurable hT
  have hT'sub : Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) ⁻¹' T ⊆ V.germTube η A δ s := by
    intro x hx
    have h2 : Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p)
        (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) x) ∈ V.germTube η A δ s := hTsub hx
    rwa [hinv x] at h2
  have hkey := V.lintegral_germTube η hA hbox hsu hT' hT'sub
    (g := fun x => g (Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) x)) (hg.comp hRemb.measurable)
  rw [hRmp.setLIntegral_comp_preimage_emb hRemb g T] at hkey
  rw [hkey]
  refine setLIntegral_congr_fun hA (fun r _ => ?_)
  refine congrArg (fun y => ENNReal.ofReal r * y) ?_
  refine setLIntegral_congr_fun measurableSet_Ioo (fun u _ => ?_)
  by_cases hmem : Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) (V.departureFlight η r u) ∈ T
  · have h1 : V.departureFlight η r u ∈
        Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) ⁻¹' T := hmem
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem hmem]
  · have h1 : V.departureFlight η r u ∉
        Prod.map (id : ℝ → ℝ) (fun p : ℝ => -p) ⁻¹' T := hmem
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem hmem]

/-! ### The departure flight lies in its own tube -/

/-- **The departure flight lies in the outgoing tube.**  This is the converse of
`lintegral_germTube`'s read-off: every state of the flow box that the departure flight reaches
within the time `s` satisfies the tube specification. -/
theorem departureFlight_mem_germTube (η : Γ.EdgeEnd) {A : Set ℝ} {r₁ r₂ δ u₀ : ℝ}
    (hbox : V.GermFlowBox η A r₁ r₂ δ u₀) {r : ℝ} (hr : r ∈ A) {s w : ℝ} (hsu : s ≤ u₀)
    (hw : w ∈ Ioo (0 : ℝ) s) : V.departureFlight η r w ∈ V.germTube η A δ s := by
  have hw' : w ∈ Icc (0 : ℝ) u₀ := ⟨hw.1.le, le_trans hw.2.le hsu⟩
  have hposb := abs_le.mp (hbox.position r hr w hw')
  have hen := hbox.energy r hr w hw'
  have hmom := hbox.momentum r hr w hw'
  have hti := hbox.time r hr w hw'
  have hδ := hbox.radius_pos
  have hr0 : 0 ≤ r := le_of_lt (lt_trans hbox.speed_pos (hbox.speeds hr).1)
  refine ⟨⟨by linarith [hposb.1], by linarith [hposb.2]⟩, ?_, hmom, ?_⟩
  · rw [hen, V.germSpeed_departureEnergy η hr0]
    exact hr
  · rw [hen, hti]
    have hself := edgeEnd_sign_mul_self η
    have hval : -(FiniteMetricGraph.EdgeEnd.sign Γ η) *
        (-(FiniteMetricGraph.EdgeEnd.sign Γ η) * w) = w := by
      have hexp : -(FiniteMetricGraph.EdgeEnd.sign Γ η) *
          (-(FiniteMetricGraph.EdgeEnd.sign Γ η) * w)
          = (FiniteMetricGraph.EdgeEnd.sign Γ η *
            FiniteMetricGraph.EdgeEnd.sign Γ η) * w := by ring
      rw [hexp, hself, one_mul]
    rw [hval]
    exact hw

/-- **The departure flight stays in the open edge.**  Inside the flow box the position is a strictly
monotone function of the time — that is what the time coordinate says — so the flight leaves the
germ at once, and the collar is too small to reach the other endpoint. -/
theorem departureFlight_mem_interiorRegular (η : Γ.EdgeEnd) {A : Set ℝ} {r₁ r₂ δ u₀ : ℝ}
    (hbox : V.GermFlowBox η A r₁ r₂ δ u₀) (hlen : δ < Γ.length η.1 / 2)
    {r : ℝ} (hr : r ∈ A) {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) u₀) :
    V.departureFlight η r w ∈ V.interiorRegular η.1 := by
  have hw' : w ∈ Icc (0 : ℝ) u₀ := ⟨hw.1.le, hw.2.le⟩
  have hposb := abs_le.mp (hbox.position r hr w hw')
  have hen := hbox.energy r hr w hw'
  have hti := hbox.time r hr w hw'
  have hδ := hbox.radius_pos
  have hreg : r ∈ V.regularSpeeds η := hbox.regular r hr
  have hE : V.hamiltonian η.1 (V.departureFlight η r w).1 (V.departureFlight η r w).2
      ∉ V.exceptionalEnergies := by rw [hen]; exact hreg.2
  have hEge : r₁ ^ 2 / 2 + V.vertexValue (vertex Γ η) ≤ V.departureEnergy η r := by
    rw [V.departureEnergy_eq η r]
    have h1 : r₁ ^ 2 ≤ r ^ 2 := by nlinarith [(hbox.speeds hr).1, hbox.speed_pos]
    linarith
  have hcmem : coordinate Γ η ∈ Ioo (coordinate Γ η - δ) (coordinate Γ η + δ) :=
    ⟨by linarith, by linarith⟩
  have hallow := hbox.allowed hEge
  have hmono := V.strictMonoOn_timeAt η.1 (E := V.departureEnergy η r)
    (q₀ := coordinate Γ η) hcmem hbox.domain hallow
  have hmemc : (V.departureFlight η r w).1 ∈
      Ioo (coordinate Γ η - δ) (coordinate Γ η + δ) :=
    ⟨by linarith [hposb.1], by linarith [hposb.2]⟩
  have htic : V.timeAt η.1 (V.departureEnergy η r) (coordinate Γ η) (coordinate Γ η) = 0 := by
    rw [timeAt, intervalIntegral.integral_same]
  have hlenpos : 0 < Γ.length η.1 := Γ.length_pos η.1
  refine ⟨?_, hE⟩
  by_cases hbo : η.2 = true
  · have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η = 1 := by
      simp [FiniteMetricGraph.EdgeEnd.sign, hbo]
    have hcoord : coordinate Γ η = Γ.length η.1 := by
      simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo]
    have hlt : (V.departureFlight η r w).1 < coordinate Γ η := by
      refine (hmono.lt_iff_lt hmemc hcmem).mp ?_
      change V.timeAt η.1 (V.departureEnergy η r) (coordinate Γ η)
        (V.departureFlight η r w).1 < V.timeAt η.1 (V.departureEnergy η r)
          (coordinate Γ η) (coordinate Γ η)
      rw [hti, htic, hsgn]
      linarith [hw.1]
    rw [hcoord] at hlt
    exact ⟨by rw [hcoord] at hposb; linarith [hposb.1], hlt⟩
  · have hbo' : η.2 = false := by
      cases h : η.2 with
      | false => rfl
      | true => exact absurd h hbo
    have hsgn : FiniteMetricGraph.EdgeEnd.sign Γ η = -1 := by
      simp [FiniteMetricGraph.EdgeEnd.sign, hbo']
    have hcoord : coordinate Γ η = 0 := by
      simp [FiniteMetricGraph.EdgeEnd.coordinate, hbo']
    have hgt : coordinate Γ η < (V.departureFlight η r w).1 := by
      refine (hmono.lt_iff_lt hcmem hmemc).mp ?_
      change V.timeAt η.1 (V.departureEnergy η r) (coordinate Γ η) (coordinate Γ η) <
        V.timeAt η.1 (V.departureEnergy η r) (coordinate Γ η) (V.departureFlight η r w).1
      rw [hti, htic, hsgn]
      linarith [hw.1]
    rw [hcoord] at hgt
    exact ⟨hgt, by rw [hcoord] at hposb; linarith [hposb.2]⟩

end MechanicalPotential

end HamiltonianMetricGraphs
