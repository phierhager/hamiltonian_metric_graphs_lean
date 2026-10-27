/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.PotentialExact

/-!
# Definition II.1: the induced path metric of a metric graph

**Definition II.1 (Finite compact metric graph).**  *A finite compact metric graph `Γ` consists of
a finite combinatorial graph with vertex set `𝒱`, edge set `ℰ`, and a length `ℓ_e ∈ (0, ∞)` for
each edge `e`.  Each edge is represented by an interval `[0, ℓ_e]`, and endpoints are glued
according to the incidence relation.  The distance is the induced path metric.*

The points of `Γ` are `Γ.Point` (`PotentialExact.lean`): the quotient of
`𝒱 ⊔ ∐_e [0, ℓ_e]` by the gluing of every endpoint `(e, a)` to its vertex, with the quotient
topology.  This file equips that type with the induced path metric:

* `graphEDist`: the infimum, over all finite chains `x = z₀, z₁, …, z_n = y` of points of `Γ` in
  which consecutive points coincide or lie on a common edge `e` at coordinates `q_i, q_{i+1}`, of
  the sum of the within-edge distances `|q_i − q_{i+1}|`.  Points in different connected
  components are joined by no chain and have distance `∞`, so we use Mathlib's extended metric
  spaces (`EMetricSpace`);
* `Point.instEMetricSpace`: `graphEDist` is an extended metric on `Γ.Point`, and its topology is
  (definitionally) the quotient topology; `pathMetric_topology_eq` is the proof that the two
  topologies agree;
* `graphEDist_ne_top_iff`: the distance is finite exactly between points of the same connected
  component of the combinatorial graph, so it is a genuine metric on each component;
* `graphEDist_edgePoint_le`, `graphEDist_edgePoint_eq_of_near`, `graphEDist_vertexPoint_eq_of_near`:
  on one edge the distance is at most `|q − q'|`, and equals `|q − q'|` for nearby points;
* `Point.instCompactSpace`: `Γ` is compact (the remark after Definition II.1).

`GraphSpace Γ` is a type synonym of `Γ.Point` carrying the path-metric structure *before* the
topology is identified with the quotient topology; `pointHomeomorph` is the identity
homeomorphism `Γ.Point ≃ₜ GraphSpace Γ`.
-/

namespace HamiltonianMetricGraphs

open Set
open scoped ENNReal

namespace FiniteMetricGraph

variable (Γ : FiniteMetricGraph)

/-! ### Points of the glued graph -/

instance : Finite Γ.VertexPoint := inferInstanceAs (Finite Γ.Vertex)

instance : DecidableEq Γ.VertexPoint := inferInstanceAs (DecidableEq Γ.Vertex)

/-- The disjoint union `∐_e [0, ℓ_e]` of the edge intervals. -/
abbrev EdgeInterval := Σ e : Γ.Edge, Icc (0 : ℝ) (Γ.length e)

/-- The endpoint of the edge interval of `η.1` represented by the edge-end `η`. -/
def endPointRep (η : Γ.EdgeEnd) : Γ.EdgeInterval := ⟨η.1, EdgeEnd.closedPoint Γ η⟩

/-- Every point of an edge interval is an endpoint or lies in the open edge. -/
theorem edgeInterval_cases (x : Γ.EdgeInterval) :
    (∃ η : Γ.EdgeEnd, x = Γ.endPointRep η) ∨ (x.2 : ℝ) ∈ Ioo (0 : ℝ) (Γ.length x.1) := by
  obtain ⟨e, q, hq0, hql⟩ := x
  by_cases h0 : q = 0
  · subst h0
    exact Or.inl ⟨(e, false), rfl⟩
  by_cases hl : q = Γ.length e
  · subst hl
    exact Or.inl ⟨(e, true), rfl⟩
  exact Or.inr ⟨lt_of_le_of_ne hq0 (Ne.symm h0), lt_of_le_of_ne hql hl⟩

/-- Lift a function on `𝒱 ⊔ ∐_e [0, ℓ_e]` which is compatible with the endpoint gluing. -/
noncomputable def liftFun {β : Type*} (f : Γ.PreGraph → β)
    (hf : ∀ η : Γ.EdgeEnd, f (Sum.inr (Γ.endPointRep η)) = f (Sum.inl η.vertex)) :
    Γ.Point → β :=
  Quot.lift f (by rintro _ _ ⟨η⟩; exact hf η)

@[simp] theorem liftFun_mk {β : Type*} (f : Γ.PreGraph → β) (hf) (a : Γ.PreGraph) :
    Γ.liftFun f hf (Quot.mk _ a) = f a := rfl

/-! ### The induced path metric -/

/-- The cost of one step: `0` for a trivial step `z = z'`, and otherwise the infimum of
`|q − q'|` over all representatives `(e, q)` of `z` and `(e, q')` of `z'` on a common edge `e`
(`∞` if there are none). -/
noncomputable def stepCost (z z' : Γ.Point) : ℝ≥0∞ :=
  min (⨅ (_ : z = z'), 0)
    (⨅ (e : Γ.Edge) (q : Icc (0 : ℝ) (Γ.length e)) (q' : Icc (0 : ℝ) (Γ.length e))
      (_ : Γ.edgePoint e q = z ∧ Γ.edgePoint e q' = z'), ENNReal.ofReal |(q : ℝ) - q'|)

/-- The length of the chain `x, z₁, …, z_n, y` (intermediate points listed in `l`): the sum of the
step costs. -/
noncomputable def chainCost : Γ.Point → List Γ.Point → Γ.Point → ℝ≥0∞
  | x, [], y => Γ.stepCost x y
  | x, z :: l, y => Γ.stepCost x z + chainCost z l y

/-- **The induced path metric** of Definition II.1: the infimum of the lengths of all finite
chains from `x` to `y` whose consecutive points lie on a common edge.  It is `∞` between points of
different connected components. -/
noncomputable def graphEDist (x y : Γ.Point) : ℝ≥0∞ := ⨅ l, Γ.chainCost x l y

theorem stepCost_le (e : Γ.Edge) (q q' : Icc (0 : ℝ) (Γ.length e)) :
    Γ.stepCost (Γ.edgePoint e q) (Γ.edgePoint e q') ≤ ENNReal.ofReal |(q : ℝ) - q'| :=
  min_le_of_right_le <|
    iInf_le_of_le e <| iInf_le_of_le q <| iInf_le_of_le q' <| iInf_le_of_le ⟨rfl, rfl⟩ le_rfl

theorem stepCost_comm (z z' : Γ.Point) : Γ.stepCost z z' = Γ.stepCost z' z := by
  have key : ∀ z z' : Γ.Point, Γ.stepCost z z' ≤ Γ.stepCost z' z := by
    intro z z'
    refine le_min (le_iInf fun h => min_le_of_left_le (iInf_le_of_le h.symm le_rfl)) ?_
    refine le_iInf fun e => le_iInf fun q => le_iInf fun q' => le_iInf fun h => ?_
    refine min_le_of_right_le <| iInf_le_of_le e <| iInf_le_of_le q' <| iInf_le_of_le q <|
      iInf_le_of_le ⟨h.2, h.1⟩ ?_
    rw [abs_sub_comm]
  exact le_antisymm (key z z') (key z' z)

theorem stepCost_self (z : Γ.Point) : Γ.stepCost z z = 0 :=
  le_antisymm (min_le_of_left_le (iInf_le_of_le rfl le_rfl)) bot_le

theorem chainCost_append (x y z : Γ.Point) (l₁ l₂ : List Γ.Point) :
    Γ.chainCost x (l₁ ++ z :: l₂) y = Γ.chainCost x l₁ z + Γ.chainCost z l₂ y := by
  induction l₁ generalizing x with
  | nil => rfl
  | cons w l₁ ih =>
    change Γ.stepCost x w + Γ.chainCost w (l₁ ++ z :: l₂) y = _
    rw [ih]
    change _ = Γ.stepCost x w + Γ.chainCost w l₁ z + _
    rw [add_assoc]

theorem chainCost_reverse (x y : Γ.Point) (l : List Γ.Point) :
    Γ.chainCost x l y = Γ.chainCost y l.reverse x := by
  induction l generalizing x y with
  | nil => exact Γ.stepCost_comm x y
  | cons z l ih =>
    rw [List.reverse_cons, chainCost_append]
    change Γ.stepCost x z + Γ.chainCost z l y = Γ.chainCost y l.reverse z + Γ.stepCost z x
    rw [ih z y, Γ.stepCost_comm x z, add_comm]

theorem graphEDist_le_chainCost (x y : Γ.Point) (l : List Γ.Point) :
    Γ.graphEDist x y ≤ Γ.chainCost x l y := iInf_le _ l

theorem graphEDist_le_stepCost (x y : Γ.Point) : Γ.graphEDist x y ≤ Γ.stepCost x y :=
  Γ.graphEDist_le_chainCost x y []

theorem graphEDist_self (x : Γ.Point) : Γ.graphEDist x x = 0 :=
  le_antisymm ((Γ.graphEDist_le_stepCost x x).trans (Γ.stepCost_self x).le) bot_le

theorem graphEDist_comm (x y : Γ.Point) : Γ.graphEDist x y = Γ.graphEDist y x := by
  have key : ∀ x y : Γ.Point, Γ.graphEDist x y ≤ Γ.graphEDist y x := by
    intro x y
    refine le_iInf fun l => ?_
    refine (Γ.graphEDist_le_chainCost x y l.reverse).trans_eq ?_
    rw [chainCost_reverse, List.reverse_reverse]
  exact le_antisymm (key x y) (key y x)

theorem graphEDist_triangle (x y z : Γ.Point) :
    Γ.graphEDist x z ≤ Γ.graphEDist x y + Γ.graphEDist y z := by
  unfold graphEDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun l₁ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun l₂ => ?_
  exact (iInf_le _ (l₁ ++ y :: l₂)).trans_eq (Γ.chainCost_append x z y l₁ l₂)

/-- **On one edge the path distance is at most the within-edge distance.** -/
theorem graphEDist_edgePoint_le (e : Γ.Edge) (q q' : Icc (0 : ℝ) (Γ.length e)) :
    Γ.graphEDist (Γ.edgePoint e q) (Γ.edgePoint e q') ≤ ENNReal.ofReal |(q : ℝ) - q'| :=
  (Γ.graphEDist_le_stepCost _ _).trans (Γ.stepCost_le e q q')

/-! ### Lower bounds by edgewise `1`-Lipschitz functions -/

/-- A function which is `1`-Lipschitz along every edge lowers every step cost. -/
theorem le_add_stepCost (F : Γ.Point → ℝ≥0∞)
    (hF : ∀ (e : Γ.Edge) (q q' : Icc (0 : ℝ) (Γ.length e)),
      F (Γ.edgePoint e q) ≤ F (Γ.edgePoint e q') + ENNReal.ofReal |(q : ℝ) - q'|)
    (z z' : Γ.Point) : F z ≤ F z' + Γ.stepCost z z' := by
  unfold stepCost
  rw [← min_add_add_left]
  refine le_min ?_ ?_
  · rw [ENNReal.add_iInf]
    refine le_iInf fun h => ?_
    subst h
    simp
  · simp only [ENNReal.add_iInf]
    refine le_iInf fun e => le_iInf fun q => le_iInf fun q' => le_iInf fun h => ?_
    obtain ⟨rfl, rfl⟩ := h
    exact hF e q q'

/-- **Lipschitz lower bound for the path metric.**  A function which is `1`-Lipschitz along every
edge is `1`-Lipschitz for `graphEDist`. -/
theorem le_add_graphEDist (F : Γ.Point → ℝ≥0∞)
    (hF : ∀ (e : Γ.Edge) (q q' : Icc (0 : ℝ) (Γ.length e)),
      F (Γ.edgePoint e q) ≤ F (Γ.edgePoint e q') + ENNReal.ofReal |(q : ℝ) - q'|)
    (x y : Γ.Point) : F x ≤ F y + Γ.graphEDist x y := by
  have hchain : ∀ (l : List Γ.Point) (x : Γ.Point), F x ≤ F y + Γ.chainCost x l y := by
    intro l
    induction l with
    | nil => exact fun x => Γ.le_add_stepCost F hF x y
    | cons z l ih =>
      intro x
      change F x ≤ F y + (Γ.stepCost x z + Γ.chainCost z l y)
      calc F x ≤ F z + Γ.stepCost x z := Γ.le_add_stepCost F hF x z
        _ ≤ F y + Γ.chainCost z l y + Γ.stepCost x z := by gcongr; exact ih z
        _ = F y + (Γ.stepCost x z + Γ.chainCost z l y) := by ring
  unfold graphEDist
  rw [ENNReal.add_iInf]
  exact le_iInf fun l => hchain l x

private theorem min_le_min_add {a b a' b' d : ℝ} (ha : a ≤ a' + d) (hb : b ≤ b' + d) :
    min a b ≤ min a' b' + d :=
  (min_le_min ha hb).trans_eq (min_add_add_right _ _ _)

private theorem ofReal_le_ofReal_add {a b d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (h : a ≤ b + d) :
    ENNReal.ofReal a ≤ ENNReal.ofReal b + ENNReal.ofReal d := by
  rw [← ENNReal.ofReal_add hb hd]
  exact ENNReal.ofReal_le_ofReal h

/-- Real version of `le_add_graphEDist`, for a nonnegative function on `𝒱 ⊔ ∐_e [0, ℓ_e]` which
is compatible with the gluing and `1`-Lipschitz along every edge. -/
theorem ofReal_le_graphEDist (f : Γ.PreGraph → ℝ)
    (hglue : ∀ η : Γ.EdgeEnd, f (Sum.inr (Γ.endPointRep η)) = f (Sum.inl η.vertex))
    (hnonneg : ∀ a, 0 ≤ f a)
    (hlip : ∀ (e : Γ.Edge) (q q' : Icc (0 : ℝ) (Γ.length e)),
      f (Sum.inr ⟨e, q⟩) ≤ f (Sum.inr ⟨e, q'⟩) + |(q : ℝ) - q'|)
    (a b : Γ.PreGraph) (hb : f b = 0) :
    ENNReal.ofReal (f a) ≤ Γ.graphEDist (Quot.mk _ a) (Quot.mk _ b) := by
  have h := Γ.le_add_graphEDist (fun z => ENNReal.ofReal (Γ.liftFun f hglue z))
    (fun e q q' => ofReal_le_ofReal_add (hnonneg _) (abs_nonneg _) (hlip e q q'))
    (Quot.mk _ a) (Quot.mk _ b)
  simpa [hb] using h

/-! #### The bump at an interior point -/

/-- The within-edge distance to an interior point `(e₀, q₀)`, truncated at `r`; it is the
constant `r` at the vertices and off the edge `e₀`. -/
noncomputable def interiorBump (e₀ : Γ.Edge) (q₀ r : ℝ) : Γ.PreGraph → ℝ
  | Sum.inl _ => r
  | Sum.inr x => if x.1 = e₀ then min |(x.2 : ℝ) - q₀| r else r

theorem interiorBump_endPointRep {e₀ : Γ.Edge} {q₀ r : ℝ}
    (hr : r ≤ min q₀ (Γ.length e₀ - q₀)) (η : Γ.EdgeEnd) :
    Γ.interiorBump e₀ q₀ r (Sum.inr (Γ.endPointRep η)) =
      Γ.interiorBump e₀ q₀ r (Sum.inl η.vertex) := by
  simp only [interiorBump]
  split_ifs with h
  · apply min_eq_right
    rcases η with ⟨e, b⟩
    change e = e₀ at h
    subst h
    cases b
    · change r ≤ |0 - q₀|
      rw [zero_sub, abs_neg]
      exact (hr.trans (min_le_left _ _)).trans (le_abs_self _)
    · change r ≤ |Γ.length e - q₀|
      exact (hr.trans (min_le_right _ _)).trans (le_abs_self _)
  · rfl

theorem interiorBump_nonneg {e₀ : Γ.Edge} {q₀ r : ℝ} (hr : 0 ≤ r) (a : Γ.PreGraph) :
    0 ≤ Γ.interiorBump e₀ q₀ r a := by
  rcases a with _ | x
  · exact hr
  · simp only [interiorBump]
    split_ifs
    · exact le_min (abs_nonneg _) hr
    · exact hr

theorem interiorBump_lip (e₀ : Γ.Edge) (q₀ r : ℝ) (e : Γ.Edge)
    (q q' : Icc (0 : ℝ) (Γ.length e)) :
    Γ.interiorBump e₀ q₀ r (Sum.inr ⟨e, q⟩) ≤
      Γ.interiorBump e₀ q₀ r (Sum.inr ⟨e, q'⟩) + |(q : ℝ) - q'| := by
  simp only [interiorBump]
  split_ifs
  · refine min_le_min_add ?_ (le_add_of_nonneg_right (abs_nonneg _))
    calc |(q : ℝ) - q₀| = |((q : ℝ) - q') + ((q' : ℝ) - q₀)| := by ring_nf
      _ ≤ |(q : ℝ) - q'| + |(q' : ℝ) - q₀| := abs_add_le _ _
      _ = _ := add_comm _ _
  · exact le_add_of_nonneg_right (abs_nonneg _)

/-- **Lower bound near a point of an edge.**  The path distance from `(e, q)` to `(e, q₀)` is at
least `min (|q − q₀|, dist(q₀, {0, ℓ_e}))`. -/
theorem ofReal_min_le_graphEDist (e : Γ.Edge) (q₀ q : Icc (0 : ℝ) (Γ.length e)) :
    ENNReal.ofReal (min |(q : ℝ) - q₀| (min (q₀ : ℝ) (Γ.length e - q₀))) ≤
      Γ.graphEDist (Γ.edgePoint e q) (Γ.edgePoint e q₀) := by
  set r := min (q₀ : ℝ) (Γ.length e - q₀)
  have hr0 : 0 ≤ r := le_min q₀.2.1 (sub_nonneg.mpr q₀.2.2)
  have h := Γ.ofReal_le_graphEDist (Γ.interiorBump e q₀ r)
    (Γ.interiorBump_endPointRep le_rfl) (Γ.interiorBump_nonneg hr0)
    (Γ.interiorBump_lip e q₀ r) (Sum.inr ⟨e, q⟩) (Sum.inr ⟨e, q₀⟩) (by simp [interiorBump, hr0])
  refine le_trans (le_of_eq ?_) h
  simp [interiorBump]

/-- **The path metric restricts to `|q − q'|` on an edge for nearby points**: if `q'` is at most as
far from `q` as `q` is from the ends of the edge, the path distance is the within-edge
distance. -/
theorem graphEDist_edgePoint_eq_of_near (e : Γ.Edge) (q q' : Icc (0 : ℝ) (Γ.length e))
    (hnear : |(q : ℝ) - q'| ≤ min (q : ℝ) (Γ.length e - q)) :
    Γ.graphEDist (Γ.edgePoint e q) (Γ.edgePoint e q') = ENNReal.ofReal |(q : ℝ) - q'| := by
  refine le_antisymm (Γ.graphEDist_edgePoint_le e q q') ?_
  have h := Γ.ofReal_min_le_graphEDist e q q'
  rw [abs_sub_comm (q' : ℝ), min_eq_left hnear, graphEDist_comm] at h
  exact h

/-! #### The bump at a vertex -/

/-- The within-edge distance to the vertex `v` (through the ends of the current edge incident
to `v`), truncated at `R`; at a vertex `w` it is `0` if `w = v` and `R` otherwise. -/
noncomputable def vertexBump (v : Γ.Vertex) (R : ℝ) : Γ.PreGraph → ℝ
  | Sum.inl w => if (w : Γ.Vertex) = v then 0 else R
  | Sum.inr x => min (min (if Γ.endpoint x.1 false = v then (x.2 : ℝ) else R)
      (if Γ.endpoint x.1 true = v then Γ.length x.1 - x.2 else R)) R

theorem vertexBump_endPointRep {v : Γ.Vertex} {R : ℝ} (hR : 0 ≤ R)
    (hRl : ∀ e, R ≤ Γ.length e) (η : Γ.EdgeEnd) :
    Γ.vertexBump v R (Sum.inr (Γ.endPointRep η)) = Γ.vertexBump v R (Sum.inl η.vertex) := by
  rcases η with ⟨e, b⟩
  have hl := hRl e
  have hl0 := (Γ.length_pos e).le
  cases b
  · change min (min (if Γ.endpoint e false = v then (0 : ℝ) else R)
      (if Γ.endpoint e true = v then Γ.length e - 0 else R)) R =
      if Γ.endpoint e false = v then 0 else R
    split_ifs <;> simp_all
  · change min (min (if Γ.endpoint e false = v then Γ.length e else R)
      (if Γ.endpoint e true = v then Γ.length e - Γ.length e else R)) R =
      if Γ.endpoint e true = v then 0 else R
    split_ifs <;> simp_all

theorem vertexBump_nonneg {v : Γ.Vertex} {R : ℝ} (hR : 0 ≤ R) (a : Γ.PreGraph) :
    0 ≤ Γ.vertexBump v R a := by
  rcases a with w | x
  · simp only [vertexBump]
    split_ifs
    · exact le_rfl
    · exact hR
  · simp only [vertexBump]
    refine le_min (le_min ?_ ?_) hR
    · split_ifs
      · exact x.2.2.1
      · exact hR
    · split_ifs
      · exact sub_nonneg.mpr x.2.2.2
      · exact hR

theorem vertexBump_lip (v : Γ.Vertex) (R : ℝ) (e : Γ.Edge) (q q' : Icc (0 : ℝ) (Γ.length e)) :
    Γ.vertexBump v R (Sum.inr ⟨e, q⟩) ≤ Γ.vertexBump v R (Sum.inr ⟨e, q'⟩) + |(q : ℝ) - q'| := by
  have hd := abs_nonneg ((q : ℝ) - q')
  have h1 : (q : ℝ) - q' ≤ |(q : ℝ) - q'| := le_abs_self _
  have h2 : (q' : ℝ) - q ≤ |(q : ℝ) - q'| := by rw [abs_sub_comm]; exact le_abs_self _
  simp only [vertexBump]
  refine min_le_min_add (min_le_min_add ?_ ?_) (by linarith)
  · split_ifs <;> linarith
  · split_ifs <;> linarith

/-- A positive radius below every edge length. -/
theorem exists_radius_le_length : ∃ R : ℝ, 0 < R ∧ ∀ e, R ≤ Γ.length e := by
  by_cases h : Nonempty Γ.Edge
  · obtain ⟨R, hR, hRl⟩ := Γ.exists_uniform_endpointCollarRadius
    exact ⟨R, hR, fun e => by linarith [hRl e, Γ.length_pos e]⟩
  · exact ⟨1, one_pos, fun e => absurd ⟨e⟩ h⟩

/-- Lower bound near a vertex: the distance from a point to the vertex `v` is at least the
truncated within-edge distance to `v`. -/
theorem ofReal_vertexBump_le_graphEDist {R : ℝ} (hR : 0 ≤ R) (hRl : ∀ e, R ≤ Γ.length e)
    (v : Γ.Vertex) (a : Γ.PreGraph) :
    ENNReal.ofReal (Γ.vertexBump v R a) ≤ Γ.graphEDist (Quot.mk _ a) (Γ.vertexPoint v) :=
  Γ.ofReal_le_graphEDist (Γ.vertexBump v R) (Γ.vertexBump_endPointRep hR hRl)
    (Γ.vertexBump_nonneg hR) (Γ.vertexBump_lip v R) a (Sum.inl v) (by simp [vertexBump])

/-- **Near a vertex the path metric is the within-edge distance**: if `2 d ≤ ℓ_f` for every edge
`f`, the point at distance `d` from the end `η` along its edge is at path distance exactly `d`
from the vertex of `η`. -/
theorem graphEDist_vertexPoint_eq_of_near (η : Γ.EdgeEnd) (q : Icc (0 : ℝ) (Γ.length η.1))
    (hnear : ∀ f, 2 * |(q : ℝ) - η.coordinate| ≤ Γ.length f) :
    Γ.graphEDist (Γ.vertexPoint η.vertex) (Γ.edgePoint η.1 q) =
      ENNReal.ofReal |(q : ℝ) - η.coordinate| := by
  set d := |(q : ℝ) - η.coordinate|
  refine le_antisymm ?_ ?_
  · rw [← Γ.edgePoint_endpoint η]
    have h := Γ.graphEDist_edgePoint_le η.1 (EdgeEnd.closedPoint Γ η) q
    rw [abs_sub_comm] at h
    exact h
  · have hd : 0 ≤ d := abs_nonneg _
    have hRl : ∀ e, d ≤ Γ.length e := fun e => by linarith [hnear e]
    have h := Γ.ofReal_vertexBump_le_graphEDist hd hRl η.vertex (Sum.inr ⟨η.1, q⟩)
    rw [graphEDist_comm] at h
    refine le_trans (le_of_eq ?_) h
    congr 1
    symm
    have hq0 := q.2.1
    have hql := q.2.2
    have hle := hnear η.1
    rcases η with ⟨e, b⟩
    cases b
    · have hdq : d = q := by
        change |(q : ℝ) - 0| = q
        rw [sub_zero, abs_of_nonneg hq0]
      change min (min (if Γ.endpoint e false = Γ.endpoint e false then (q : ℝ) else d)
        (if Γ.endpoint e true = Γ.endpoint e false then Γ.length e - q else d)) d = d
      rw [if_pos rfl]
      split_ifs <;> simp only [hdq] at hle ⊢ <;> simp only [min_def] <;> split_ifs <;> linarith
    · have hdq : d = Γ.length e - q := by
        change |(q : ℝ) - Γ.length e| = Γ.length e - q
        rw [abs_of_nonpos (sub_nonpos.mpr hql)]; ring
      change min (min (if Γ.endpoint e false = Γ.endpoint e true then (q : ℝ) else d)
        (if Γ.endpoint e true = Γ.endpoint e true then Γ.length e - q else d)) d = d
      rw [if_pos rfl]
      split_ifs <;> simp only [hdq] at hle ⊢ <;> simp only [min_def] <;> split_ifs <;> linarith

/-! ### Separation -/

/-- A point at path distance zero from a vertex is that vertex. -/
theorem eq_vertexPoint_of_graphEDist_eq_zero {v : Γ.Vertex} {y : Γ.Point}
    (h : Γ.graphEDist y (Γ.vertexPoint v) = 0) : y = Γ.vertexPoint v := by
  obtain ⟨R, hR, hRl⟩ := Γ.exists_radius_le_length
  obtain ⟨b, rfl⟩ := Quot.exists_rep y
  have hb := Γ.ofReal_vertexBump_le_graphEDist hR.le hRl v b
  rw [h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hb
  have h0 : Γ.vertexBump v R b = 0 := le_antisymm hb (Γ.vertexBump_nonneg hR.le b)
  rcases b with w | ⟨e, q, hq0, hql⟩
  · simp only [vertexBump] at h0
    split_ifs at h0 with hw
    · change Γ.vertexPoint w = Γ.vertexPoint v
      rw [show (w : Γ.Vertex) = v from hw]
    · exact absurd h0 hR.ne'
  · simp only [vertexBump] at h0
    by_cases hA : Γ.endpoint e false = v ∧ q = 0
    · obtain ⟨hv, rfl⟩ := hA
      rw [← hv]
      exact Γ.edgePoint_endpoint (e, false)
    by_cases hB : Γ.endpoint e true = v ∧ q = Γ.length e
    · obtain ⟨hv, rfl⟩ := hB
      rw [← hv]
      exact Γ.edgePoint_endpoint (e, true)
    exfalso
    have hA' : 0 < (if Γ.endpoint e false = v then q else R) := by
      split_ifs with hv
      · exact lt_of_le_of_ne hq0 (fun h' => hA ⟨hv, h'.symm⟩)
      · exact hR
    have hB' : 0 < (if Γ.endpoint e true = v then Γ.length e - q else R) := by
      split_ifs with hv
      · exact sub_pos.mpr (lt_of_le_of_ne hql (fun h' => hB ⟨hv, h'⟩))
      · exact hR
    have : 0 < min (min (if Γ.endpoint e false = v then q else R)
        (if Γ.endpoint e true = v then Γ.length e - q else R)) R :=
      lt_min (lt_min hA' hB') hR
    exact this.ne' h0

/-- Points at path distance zero coincide. -/
theorem eq_of_graphEDist_eq_zero {x y : Γ.Point} (h : Γ.graphEDist x y = 0) : x = y := by
  obtain ⟨a, rfl⟩ := Quot.exists_rep x
  rcases a with v | p
  · rw [graphEDist_comm] at h
    exact (Γ.eq_vertexPoint_of_graphEDist_eq_zero h).symm
  rcases Γ.edgeInterval_cases p with ⟨η, rfl⟩ | hp
  · have hx : Quot.mk Γ.Glue (Sum.inr (Γ.endPointRep η)) = Γ.vertexPoint η.vertex :=
      Γ.edgePoint_endpoint η
    rw [hx, graphEDist_comm] at h
    rw [hx]
    exact (Γ.eq_vertexPoint_of_graphEDist_eq_zero h).symm
  -- `x` is an interior point of an edge: use the interior bump.
  obtain ⟨e, q₀⟩ := p
  have hr : 0 < min (q₀ : ℝ) (Γ.length e - q₀) := lt_min hp.1 (sub_pos.mpr hp.2)
  set r := min (q₀ : ℝ) (Γ.length e - q₀)
  obtain ⟨b, rfl⟩ := Quot.exists_rep y
  have hb := Γ.ofReal_le_graphEDist (Γ.interiorBump e q₀ r)
    (Γ.interiorBump_endPointRep le_rfl) (Γ.interiorBump_nonneg hr.le)
    (Γ.interiorBump_lip e q₀ r) b (Sum.inr ⟨e, q₀⟩) (by simp [interiorBump, hr.le])
  rw [graphEDist_comm, h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hb
  rcases b with w | ⟨e', q'⟩
  · simp only [interiorBump] at hb
    linarith
  simp only [interiorBump] at hb
  split_ifs at hb with he
  · change e' = e at he
    subst he
    have habs : |(q' : ℝ) - q₀| ≤ 0 := by
      rcases le_total |(q' : ℝ) - q₀| r with hle | hle
      · rwa [min_eq_left hle] at hb
      · rw [min_eq_right hle] at hb; linarith
    have hqq : (q' : ℝ) = q₀ := by
      have := abs_nonpos_iff.mp habs; linarith
    have : q' = q₀ := Subtype.ext hqq
    subst this
    rfl
  · linarith

/-! ### The extended metric space -/

/-- The path metric as an extended metric on the points of `Γ`, with the uniform structure (and
topology) generated by the distance.  `pathMetric_topology_eq` shows that this topology is the
quotient topology; the instance `Point.instEMetricSpace` records this definitionally. -/
@[reducible] noncomputable def pathEMetric : EMetricSpace Γ.Point where
  edist := Γ.graphEDist
  edist_self := Γ.graphEDist_self
  edist_comm := Γ.graphEDist_comm
  edist_triangle := Γ.graphEDist_triangle
  eq_of_edist_eq_zero := Γ.eq_of_graphEDist_eq_zero

/-- **The points of `Γ` with the induced path metric** (a type synonym of `Γ.Point` carrying the
metric topology). -/
def GraphSpace := Γ.Point

noncomputable instance GraphSpace.instEMetricSpace : EMetricSpace Γ.GraphSpace := Γ.pathEMetric

/-- The identity of the underlying points, from the quotient topology to the metric one. -/
def toGraphSpace : Γ.Point ≃ Γ.GraphSpace := Equiv.refl _

theorem edist_toGraphSpace (x y : Γ.Point) :
    edist (Γ.toGraphSpace x) (Γ.toGraphSpace y) = Γ.graphEDist x y := rfl

/-- On each edge the inclusion `[0, ℓ_e] → Γ` is `1`-Lipschitz for the path metric. -/
theorem lipschitzWith_edgePoint (e : Γ.Edge) :
    LipschitzWith 1 (fun q : Icc (0 : ℝ) (Γ.length e) => Γ.toGraphSpace (Γ.edgePoint e q)) := by
  refine LipschitzWith.of_edist_le fun q q' => ?_
  rw [edist_toGraphSpace, Subtype.edist_eq, edist_dist, Real.dist_eq]
  exact Γ.graphEDist_edgePoint_le e q q'

/-- The identity is continuous from the quotient topology to the path-metric topology. -/
theorem continuous_toGraphSpace : Continuous Γ.toGraphSpace := by
  refine (isQuotientMap_quot_mk (r := Γ.Glue)).continuous_iff.mpr ?_
  refine continuous_sum_dom.mpr ⟨continuous_of_discreteTopology, ?_⟩
  exact continuous_sigma_iff.mpr fun e => (Γ.lipschitzWith_edgePoint e).continuous

/-- **`Γ` is compact** (Sec. II: finitely many edges of finite length): it is the image of the
compact space `𝒱 ⊔ ∐_e [0, ℓ_e]` under the continuous quotient map. -/
instance Point.instCompactSpace : CompactSpace Γ.Point :=
  ⟨by simpa [(Quot.mk_surjective (r := Γ.Glue)).range_eq] using
    isCompact_range (continuous_quot_mk (r := Γ.Glue))⟩

/-- The identity `Γ.Point ≃ₜ GraphSpace Γ` is a homeomorphism: a continuous bijection from a
compact space to a Hausdorff (metric) space. -/
noncomputable def pointHomeomorph : Γ.Point ≃ₜ Γ.GraphSpace :=
  Γ.continuous_toGraphSpace.homeoOfEquivCompactToT2

/-- **The path-metric topology is the quotient topology** of `𝒱 ⊔ ∐_e [0, ℓ_e]` by the endpoint
gluing. -/
theorem pathMetric_topology_eq :
    (inferInstance : TopologicalSpace Γ.Point) =
      Γ.pathEMetric.toUniformSpace.toTopologicalSpace := by
  have h := (Γ.pointHomeomorph).coinduced_eq
  exact h

/-- **Definition II.1: `Γ` with the induced path metric.**  The extended metric space structure
on the points of `Γ` with distance `graphEDist`; its topology is the quotient topology already on
`Γ.Point`. -/
noncomputable instance Point.instEMetricSpace : EMetricSpace Γ.Point :=
  Γ.pathEMetric.replaceTopology Γ.pathMetric_topology_eq

theorem edist_eq_graphEDist (x y : Γ.Point) : edist x y = Γ.graphEDist x y := rfl

/-- The topology of the path metric on `Γ.Point` is, definitionally, the quotient topology. -/
theorem point_topology_eq_quotient :
    (Point.instEMetricSpace Γ).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (Quot Γ.Glue)) := rfl

/-! ### Connected components: finite distance -/

/-- The combinatorial graph underlying `Γ` (loops and multiple edges forgotten): two distinct
vertices are adjacent when some edge joins them. -/
def adjacency : SimpleGraph Γ.Vertex :=
  SimpleGraph.fromRel fun v w => ∃ e, Γ.endpoint e false = v ∧ Γ.endpoint e true = w

theorem reachable_endpoints (e : Γ.Edge) :
    Γ.adjacency.Reachable (Γ.endpoint e false) (Γ.endpoint e true) := by
  by_cases h : Γ.endpoint e false = Γ.endpoint e true
  · rw [h]
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).mpr
      ⟨h, Or.inl ⟨e, rfl, rfl⟩⟩)

theorem connectedComponentMk_vertex (η : Γ.EdgeEnd) :
    Γ.adjacency.connectedComponentMk (Γ.endpoint η.1 false) =
      Γ.adjacency.connectedComponentMk η.vertex := by
  rcases η with ⟨e, b⟩
  cases b
  · rfl
  · exact SimpleGraph.ConnectedComponent.sound (Γ.reachable_endpoints e)

/-- The connected component of a point of `Γ`. -/
noncomputable def component : Γ.Point → Γ.adjacency.ConnectedComponent :=
  Γ.liftFun
    (Sum.elim (fun w => Γ.adjacency.connectedComponentMk w)
      (fun x => Γ.adjacency.connectedComponentMk (Γ.endpoint x.1 false)))
    (fun η => Γ.connectedComponentMk_vertex η)

/-- The two ends of an edge are at finite distance. -/
theorem graphEDist_vertexPoint_endpoints_ne_top (e : Γ.Edge) :
    Γ.graphEDist (Γ.vertexPoint (Γ.endpoint e false)) (Γ.vertexPoint (Γ.endpoint e true)) ≠ ⊤ := by
  have h1 : Γ.vertexPoint (Γ.endpoint e false) =
      Γ.edgePoint e (EdgeEnd.closedPoint Γ (e, false)) := (Γ.edgePoint_endpoint (e, false)).symm
  have h2 : Γ.vertexPoint (Γ.endpoint e true) =
      Γ.edgePoint e (EdgeEnd.closedPoint Γ (e, true)) := (Γ.edgePoint_endpoint (e, true)).symm
  rw [h1, h2]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (Γ.graphEDist_edgePoint_le e _ _)

theorem graphEDist_vertexPoint_ne_top {v w : Γ.Vertex} (W : Γ.adjacency.Walk v w) :
    Γ.graphEDist (Γ.vertexPoint v) (Γ.vertexPoint w) ≠ ⊤ := by
  induction W with
  | nil => rw [graphEDist_self]; exact ENNReal.zero_ne_top
  | @cons v u w hadj W ih =>
    obtain ⟨-, hr⟩ := (SimpleGraph.fromRel_adj _ _ _).mp hadj
    have hvu : Γ.graphEDist (Γ.vertexPoint v) (Γ.vertexPoint u) ≠ ⊤ := by
      rcases hr with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      · exact Γ.graphEDist_vertexPoint_endpoints_ne_top e
      · rw [graphEDist_comm]; exact Γ.graphEDist_vertexPoint_endpoints_ne_top e
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hvu, ih⟩) (Γ.graphEDist_triangle _ _ _)

/-- Every point is at finite distance from a vertex of its own component. -/
theorem exists_vertexPoint_near (x : Γ.Point) :
    ∃ w : Γ.Vertex, Γ.adjacency.connectedComponentMk w = Γ.component x ∧
      Γ.graphEDist x (Γ.vertexPoint w) ≠ ⊤ := by
  obtain ⟨a, rfl⟩ := Quot.exists_rep x
  rcases a with v | ⟨e, q⟩
  · refine ⟨v, rfl, ?_⟩
    change Γ.graphEDist (Γ.vertexPoint v) (Γ.vertexPoint v) ≠ ⊤
    rw [graphEDist_self]; exact ENNReal.zero_ne_top
  · refine ⟨Γ.endpoint e false, rfl, ?_⟩
    have h1 : Γ.vertexPoint (Γ.endpoint e false) =
        Γ.edgePoint e (EdgeEnd.closedPoint Γ (e, false)) :=
      (Γ.edgePoint_endpoint (e, false)).symm
    rw [h1]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (Γ.graphEDist_edgePoint_le e q _)

/-- **The distance is finite exactly within a connected component**: `graphEDist x y < ∞` iff
`x` and `y` lie in the same connected component of the combinatorial graph.  Thus `graphEDist`
is a genuine (finite) metric on each connected component, and `∞` between components. -/
theorem graphEDist_ne_top_iff (x y : Γ.Point) :
    Γ.graphEDist x y ≠ ⊤ ↔ Γ.component x = Γ.component y := by
  classical
  constructor
  · intro hfin
    by_contra hne
    have h := Γ.le_add_graphEDist (fun z => if Γ.component z = Γ.component y then 0 else ⊤)
      (fun e q q' => by
        have : Γ.component (Γ.edgePoint e q) = Γ.component (Γ.edgePoint e q') := rfl
        rw [this]; exact le_self_add) x y
    simp only [hne, if_false, if_true, zero_add, top_le_iff] at h
    exact hfin h
  · intro hcomp
    obtain ⟨w, hw, hxw⟩ := Γ.exists_vertexPoint_near x
    obtain ⟨w', hw', hyw'⟩ := Γ.exists_vertexPoint_near y
    obtain ⟨W⟩ : Γ.adjacency.Reachable w w' :=
      SimpleGraph.ConnectedComponent.exact (hw.trans (hcomp.trans hw'.symm))
    have hmid := Γ.graphEDist_vertexPoint_ne_top W
    rw [graphEDist_comm] at hyw'
    refine ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨hxw, ENNReal.add_ne_top.mpr ⟨hmid, hyw'⟩⟩) ?_
    exact (Γ.graphEDist_triangle _ _ _).trans (add_le_add le_rfl (Γ.graphEDist_triangle _ _ _))

/-- The metric topology of `Γ` is the quotient topology: the gluing map
`𝒱 ⊔ ∐_e [0, ℓ_e] → Γ` is a quotient map for the path-metric topology. -/
theorem isQuotientMap_mk : Topology.IsQuotientMap (Quot.mk Γ.Glue) :=
  isQuotientMap_quot_mk

end FiniteMetricGraph

end HamiltonianMetricGraphs
