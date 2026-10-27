/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.Realization.Microscopic
import HamiltonianMetricGraphs.Realization.IntervalEstimates
import HamiltonianMetricGraphs.EdgeDynamics

/-!
# Thin Hamiltonian networks

This file introduces the *microscopic physical model* of the thin-junction limit: a family of
smooth mechanical Hamiltonians

  `H_ε(x, p) = ½ |p|² + W_ε(x)`  on `ℝ² × ℝ²`,

describing a classical particle in the plane, confined by the smooth potential `W_ε` to a network
of thin channels of width `O(ε)`.  The geometric data of the network are, for each edge `e` of a
finite metric graph `Γ`, a straight tube: a base point `base e`, a unit tangent `tang e` and a
unit normal `nrm e`.  A point `x` of the plane then has a **longitudinal** coordinate `long e x`
(measured in the graph coordinate of `e`) and a **transverse** displacement `trans e x`, and a
momentum `p` splits into `longP e p` and `transP e p`.  As `ε → 0` the channel centrelines
collapse onto the metric graph and the junction regions collapse onto the vertices.

Nothing here fixes the potential; a `ThinHamiltonianNetwork` is exactly the data of
Definition IX.3 of the paper (`def:thin-network`):

* (i) a `C²` potential `W_ε` that is **bounded below** (`contDiff_pot`, `pot_bddBelow`), so that
  the flow `Φ^ε_t` of `H_ε` is complete (`MicroscopicCompleteness.lean`);
* (ii) for each edge a straight tube (`base`, `tang`, `nrm`) and a continuous transverse profile
  `transPot ε e`;
* (iii) the six scales of the paper, all nonnegative and tending to `0` as `ε → 0⁺`:

  | field | paper | meaning |
  |---|---|---|
  | `offset ε` | `δ_ε` | the radius of the junction regions |
  | `dwell ε` | `θ_ε` | the residence time in a junction |
  | `forceErr ε` | `γ_ε` | the error in the longitudinal force |
  | `momErr ε` | `μ_ε` | the error in the outgoing momentum |
  | `tubeWidth ε` | `w_ε` | the tube width |
  | `transErr ε` | `λ_ε` | the transverse energy |

The data are given for every real `ε` (the paper gives them for `0 < ε < ε₀`; a family on
`(0, ε₀)` extends to all `ε`, and only `ε ∈ (0, ε₀)` enters the hypotheses and the theorems).

These are physical statements about the geometry of the network and the quality of the
confinement; the *dynamical* content — that the microscopic flow actually decomposes into edge
flights and junction passages with these parameters — is the content of the hypotheses (E), (J),
(D) in `ThinHypotheses.lean` and is **not** assumed here.
-/

namespace HamiltonianMetricGraphs

open Set Filter FiniteMetricGraph MechanicalPotential
open scoped Topology

/-- **A thin Hamiltonian network over the finite metric graph `Γ`** (Definition IX.3 of the
paper).  A family of `C²` potentials on the plane, bounded below, together with the straight tube
attached to each edge and the six scales `δ_ε, θ_ε, γ_ε, μ_ε, w_ε, λ_ε` of the network. -/
structure ThinHamiltonianNetwork (Γ : FiniteMetricGraph) where
  /-- the smooth confining and external potential `W_ε` at scale `ε` -/
  pot : ℝ → ℝ × ℝ → ℝ
  /-- (i) the potential is `C²`, so the Hamiltonian flow is well defined -/
  contDiff_pot : ∀ ε, ContDiff ℝ 2 (pot ε)
  /-- (i) the potential is bounded below, so the Hamiltonian flow is complete -/
  pot_bddBelow : ∀ ε, BddBelow (Set.range (pot ε))
  /-- (ii) the point `b_e` of the plane at graph coordinate `0` of the edge `e` -/
  base : Γ.Edge → ℝ × ℝ
  /-- (ii) the unit tangent `τ_e` of the tube of `e`, in the graph orientation -/
  tang : Γ.Edge → ℝ × ℝ
  /-- (ii) the unit normal `ν_e` of the tube of `e` -/
  nrm : Γ.Edge → ℝ × ℝ
  tang_sq : ∀ e, (tang e).1 ^ 2 + (tang e).2 ^ 2 = 1
  nrm_sq : ∀ e, (nrm e).1 ^ 2 + (nrm e).2 ^ 2 = 1
  tang_nrm : ∀ e, (tang e).1 * (nrm e).1 + (tang e).2 * (nrm e).2 = 0
  /-- (ii) the transverse confining profile `U_{ε,e}` of the tube of `e` at scale `ε` -/
  transPot : ℝ → Γ.Edge → ℝ → ℝ
  /-- (ii) the transverse profile is continuous -/
  continuous_transPot : ∀ ε e, Continuous (transPot ε e)
  /-- (iii) `δ_ε`: the radius of the junction regions -/
  offset : ℝ → ℝ
  /-- (iii) `θ_ε`: the residence time in a junction -/
  dwell : ℝ → ℝ
  /-- (iii) `γ_ε`: the error in the longitudinal force -/
  forceErr : ℝ → ℝ
  /-- (iii) `μ_ε`: the error in the outgoing momentum -/
  momErr : ℝ → ℝ
  /-- (iii) `w_ε`: the tube width -/
  tubeWidth : ℝ → ℝ
  /-- (iii) `λ_ε`: the transverse energy -/
  transErr : ℝ → ℝ
  offset_nonneg : ∀ ε, 0 ≤ offset ε
  dwell_nonneg : ∀ ε, 0 ≤ dwell ε
  forceErr_nonneg : ∀ ε, 0 ≤ forceErr ε
  momErr_nonneg : ∀ ε, 0 ≤ momErr ε
  tubeWidth_nonneg : ∀ ε, 0 ≤ tubeWidth ε
  transErr_nonneg : ∀ ε, 0 ≤ transErr ε
  offset_tendsto : Tendsto offset (𝓝[>] 0) (𝓝 0)
  dwell_tendsto : Tendsto dwell (𝓝[>] 0) (𝓝 0)
  forceErr_tendsto : Tendsto forceErr (𝓝[>] 0) (𝓝 0)
  momErr_tendsto : Tendsto momErr (𝓝[>] 0) (𝓝 0)
  tubeWidth_tendsto : Tendsto tubeWidth (𝓝[>] 0) (𝓝 0)
  transErr_tendsto : Tendsto transErr (𝓝[>] 0) (𝓝 0)

namespace ThinHamiltonianNetwork

variable {Γ : FiniteMetricGraph} (N : ThinHamiltonianNetwork Γ)

/-! ### The tube coordinates -/

/-- The longitudinal coordinate of a point of the plane along the tube of `e`, in the graph
coordinate of `e`. -/
noncomputable def long (e : Γ.Edge) (x : ℝ × ℝ) : ℝ :=
  (x.1 - (N.base e).1) * (N.tang e).1 + (x.2 - (N.base e).2) * (N.tang e).2

/-- The transverse displacement of a point of the plane from the centreline of the tube of `e`. -/
noncomputable def trans (e : Γ.Edge) (x : ℝ × ℝ) : ℝ :=
  (x.1 - (N.base e).1) * (N.nrm e).1 + (x.2 - (N.base e).2) * (N.nrm e).2

/-- The longitudinal momentum along the tube of `e`. -/
noncomputable def longP (e : Γ.Edge) (p : ℝ × ℝ) : ℝ :=
  p.1 * (N.tang e).1 + p.2 * (N.tang e).2

/-- The transverse momentum of the tube of `e`. -/
noncomputable def transP (e : Γ.Edge) (p : ℝ × ℝ) : ℝ :=
  p.1 * (N.nrm e).1 + p.2 * (N.nrm e).2

/-- **The projected graph state**: the longitudinal position and momentum along the tube of `e`.
This is the map `π_ε` which sends a microscopic state to a state of the metric graph. -/
noncomputable def gState (e : Γ.Edge) (x p : ℝ × ℝ) : ℝ × ℝ := (N.long e x, N.longP e p)

@[simp] theorem gState_fst (e : Γ.Edge) (x p : ℝ × ℝ) : (N.gState e x p).1 = N.long e x := rfl
@[simp] theorem gState_snd (e : Γ.Edge) (x p : ℝ × ℝ) : (N.gState e x p).2 = N.longP e p := rfl

/-- The transverse energy of a microscopic state in the tube of `e`. -/
noncomputable def transEnergy (ε : ℝ) (e : Γ.Edge) (x p : ℝ × ℝ) : ℝ :=
  N.transP e p ^ 2 / 2 + N.transPot ε e (N.trans e x)

/-! ### The Hamiltonian and its flow -/

/-- The force of the microscopic Hamiltonian, given componentwise by the two partial derivatives
of the potential.  Together with `x' = p` this is Hamilton's equations for
`H_ε(x,p) = ½|p|² + W_ε(x)`. -/
noncomputable def force (ε : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (-deriv (fun s => N.pot ε (s, x.2)) x.1, -deriv (fun s => N.pot ε (x.1, s)) x.2)

/-- The microscopic Hamiltonian. -/
noncomputable def hamiltonian (ε : ℝ) (x p : ℝ × ℝ) : ℝ := (p.1 ^ 2 + p.2 ^ 2) / 2 + N.pot ε x

/-- **The longitudinal component of the gradient**, `⟨∇W_ε(x), τ_e⟩`.  This is the quantity
compared with `V_e'(q_e(x))` in (E3). -/
noncomputable def longGrad (ε : ℝ) (e : Γ.Edge) (x : ℝ × ℝ) : ℝ :=
  deriv (fun s => N.pot ε (s, x.2)) x.1 * (N.tang e).1 +
    deriv (fun s => N.pot ε (x.1, s)) x.2 * (N.tang e).2

/-- The longitudinal force is minus the longitudinal component of the gradient. -/
theorem longP_force (ε : ℝ) (e : Γ.Edge) (x : ℝ × ℝ) :
    N.longP e (N.force ε x) = -N.longGrad ε e x := by
  simp only [longP, force, longGrad]
  ring

/-- **A genuine trajectory of the microscopic Hamiltonian** `H_ε` on the time window `[0, S]`:
a solution of Hamilton's equations `x' = p`, `p' = -∇W_ε(x)`. -/
structure MicroTrajectory (ε S : ℝ) where
  /-- the microscopic configuration -/
  x : ℝ → ℝ × ℝ
  /-- the microscopic momentum -/
  p : ℝ → ℝ × ℝ
  ode_pos : ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt x (p t) (Icc (0 : ℝ) S) t
  ode_mom : ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (N.force ε (x t)) (Icc (0 : ℝ) S) t

variable {N}

/-- The longitudinal coordinate of a trajectory has the longitudinal momentum as derivative:
the projection `π_ε` intertwines the microscopic and the graph velocity. -/
theorem hasDerivWithinAt_long (e : Γ.Edge) {x p : ℝ → ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt x (p t) s t) :
    HasDerivWithinAt (fun r => N.long e (x r)) (N.longP e (p t)) s t := by
  have h1 := h.fst_comp
  have h2 := h.snd_comp
  have key : HasDerivWithinAt
      (fun r => ((x r).1 - (N.base e).1) * (N.tang e).1 +
        ((x r).2 - (N.base e).2) * (N.tang e).2)
      ((p t).1 * (N.tang e).1 + (p t).2 * (N.tang e).2) s t :=
    ((h1.sub_const (N.base e).1).mul_const (N.tang e).1).add
      ((h2.sub_const (N.base e).2).mul_const (N.tang e).2)
  exact key

/-- The same for the transverse displacement. -/
theorem hasDerivWithinAt_trans (e : Γ.Edge) {x p : ℝ → ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt x (p t) s t) :
    HasDerivWithinAt (fun r => N.trans e (x r)) (N.transP e (p t)) s t := by
  have h1 := h.fst_comp
  have h2 := h.snd_comp
  have key : HasDerivWithinAt
      (fun r => ((x r).1 - (N.base e).1) * (N.nrm e).1 +
        ((x r).2 - (N.base e).2) * (N.nrm e).2)
      ((p t).1 * (N.nrm e).1 + (p t).2 * (N.nrm e).2) s t :=
    ((h1.sub_const (N.base e).1).mul_const (N.nrm e).1).add
      ((h2.sub_const (N.base e).2).mul_const (N.nrm e).2)
  exact key

/-- The longitudinal momentum of a trajectory has the longitudinal force as derivative. -/
theorem hasDerivWithinAt_longP (e : Γ.Edge) {p : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt p v s t) :
    HasDerivWithinAt (fun r => N.longP e (p r)) (N.longP e v) s t := by
  have h1 := h.fst_comp
  have h2 := h.snd_comp
  have key : HasDerivWithinAt (fun r => (p r).1 * (N.tang e).1 + (p r).2 * (N.tang e).2)
      (v.1 * (N.tang e).1 + v.2 * (N.tang e).2) s t :=
    (h1.mul_const (N.tang e).1).add (h2.mul_const (N.tang e).2)
  exact key

/-- The same for the transverse momentum. -/
theorem hasDerivWithinAt_transP (e : Γ.Edge) {p : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt p v s t) :
    HasDerivWithinAt (fun r => N.transP e (p r)) (N.transP e v) s t := by
  have h1 := h.fst_comp
  have h2 := h.snd_comp
  have key : HasDerivWithinAt (fun r => (p r).1 * (N.nrm e).1 + (p r).2 * (N.nrm e).2)
      (v.1 * (N.nrm e).1 + v.2 * (N.nrm e).2) s t :=
    (h1.mul_const (N.nrm e).1).add (h2.mul_const (N.nrm e).2)
  exact key

/-- **The projected graph state moves with the projected vector field.** -/
theorem hasDerivWithinAt_gState (e : Γ.Edge) {x p : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x (p t) s t) (hp : HasDerivWithinAt p v s t) :
    HasDerivWithinAt (fun r => N.gState e (x r) (p r)) (N.longP e (p t), N.longP e v) s t :=
  (hasDerivWithinAt_long e hx).prodMk (hasDerivWithinAt_longP e hp)

/-! ### Conservation of the microscopic energy -/

section Energy

variable {W : ℝ × ℝ → ℝ}

/-- The two partial derivatives of a differentiable function of two variables are the values of
its total derivative on the two coordinate directions. -/
theorem hasDerivAt_partial_fst (hW : Differentiable ℝ W) (z : ℝ × ℝ) :
    HasDerivAt (fun s => W (s, z.2)) (fderiv ℝ W z (1, 0)) z.1 := by
  have h1 : HasFDerivAt (fun s : ℝ => (s, z.2)) ((ContinuousLinearMap.id ℝ ℝ).prod 0) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have h2 : HasFDerivAt W (fderiv ℝ W (z.1, z.2)) (z.1, z.2) := (hW _).hasFDerivAt
  have h3 := h2.comp z.1 h1
  exact h3.hasDerivAt.congr_deriv (by simp)

theorem hasDerivAt_partial_snd (hW : Differentiable ℝ W) (z : ℝ × ℝ) :
    HasDerivAt (fun s => W (z.1, s)) (fderiv ℝ W z (0, 1)) z.2 := by
  have h1 : HasFDerivAt (fun s : ℝ => (z.1, s)) ((0 : ℝ →L[ℝ] ℝ).prod
      (ContinuousLinearMap.id ℝ ℝ)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have h2 : HasFDerivAt W (fderiv ℝ W (z.1, z.2)) (z.1, z.2) := (hW _).hasFDerivAt
  have h3 := h2.comp z.2 h1
  exact h3.hasDerivAt.congr_deriv (by simp)

/-- The total derivative of `W` in the direction `v` is `∂₁W · v₁ + ∂₂W · v₂`. -/
theorem fderiv_apply_eq (hW : Differentiable ℝ W) (z v : ℝ × ℝ) :
    fderiv ℝ W z v =
      deriv (fun s => W (s, z.2)) z.1 * v.1 + deriv (fun s => W (z.1, s)) z.2 * v.2 := by
  rw [(hasDerivAt_partial_fst hW z).deriv, (hasDerivAt_partial_snd hW z).deriv]
  have hv : (fderiv ℝ W z) v
      = (fderiv ℝ W z) (v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ))) := by
    congr 1
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm, mul_comm v.2]

/-- **The microscopic energy is conserved along every trajectory of `H_ε`.**  This is the exact
statement `dH/dt = ∂_p H · ṗ + ∂_x H · ẋ = 0` for the Hamiltonian `H_ε = ½|p|² + W_ε`. -/
theorem MicroTrajectory.hamiltonian_eq {ε S : ℝ} (hpot : Differentiable ℝ (N.pot ε))
    (Θ : N.MicroTrajectory ε S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    N.hamiltonian ε (Θ.x t) (Θ.p t) = N.hamiltonian ε (Θ.x 0) (Θ.p 0) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) S := ⟨le_rfl, ht.1.trans ht.2⟩
  have hzero : ∀ r ∈ Icc (0 : ℝ) S,
      HasDerivWithinAt (fun s => N.hamiltonian ε (Θ.x s) (Θ.p s)) 0 (Icc (0 : ℝ) S) r := by
    intro r hr
    have hx := Θ.ode_pos r hr
    have hp := Θ.ode_mom r hr
    have hkin : HasDerivWithinAt (fun s => ((Θ.p s).1 ^ 2 + (Θ.p s).2 ^ 2) / 2)
        ((Θ.p r).1 * (N.force ε (Θ.x r)).1 + (Θ.p r).2 * (N.force ε (Θ.x r)).2)
        (Icc (0 : ℝ) S) r := by
      have h1 := hp.fst_comp
      have h2 := hp.snd_comp
      have key : HasDerivWithinAt (fun s => ((Θ.p s).1 ^ 2 + (Θ.p s).2 ^ 2) / 2)
          ((2 * (Θ.p r).1 ^ (2 - 1) * (N.force ε (Θ.x r)).1 +
            2 * (Θ.p r).2 ^ (2 - 1) * (N.force ε (Θ.x r)).2) / 2) (Icc (0 : ℝ) S) r :=
        ((h1.pow 2).add (h2.pow 2)).div_const 2
      convert key using 1
      ring
    have hpot' : HasDerivWithinAt (fun s => N.pot ε (Θ.x s))
        (fderiv ℝ (N.pot ε) (Θ.x r) (Θ.p r)) (Icc (0 : ℝ) S) r :=
      ((hpot (Θ.x r)).hasFDerivAt).comp_hasDerivWithinAt r hx
    rw [fderiv_apply_eq hpot] at hpot'
    have hsum := hkin.add hpot'
    have hz : (Θ.p r).1 * (N.force ε (Θ.x r)).1 + (Θ.p r).2 * (N.force ε (Θ.x r)).2 +
        (deriv (fun s => N.pot ε (s, (Θ.x r).2)) (Θ.x r).1 * (Θ.p r).1 +
          deriv (fun s => N.pot ε ((Θ.x r).1, s)) (Θ.x r).2 * (Θ.p r).2) = 0 := by
      show _ + _ + _ = 0
      rw [ThinHamiltonianNetwork.force]
      ring
    rw [hz] at hsum
    exact hsum
  have hconst := abs_image_sub_le_mul_sub_of_abs_hasDerivWithinAt_le
    (f := fun s => N.hamiltonian ε (Θ.x s) (Θ.p s)) (f' := fun _ => (0 : ℝ)) (C := 0)
    hzero (fun _ _ => by simp) h0 ht ht.1
  have : |N.hamiltonian ε (Θ.x t) (Θ.p t) - N.hamiltonian ε (Θ.x 0) (Θ.p 0)| ≤ 0 := by
    simpa using hconst
  linarith [abs_nonpos_iff.mp this]

end Energy

end ThinHamiltonianNetwork

end HamiltonianMetricGraphs
