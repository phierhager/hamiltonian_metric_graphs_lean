# Restricted microscopic-realization theorem

Lean 4 / Mathlib formalization (directory `HamiltonianMetricGraphs/Realization/`) of the
following statement.

**Theorem.** Let `Γ` be a finite compact metric graph with edge Hamiltonians
`H_e(q,p) = p²/2 + V_e(q)`, `V` continuous on `Γ` and `C²` on each edge, and let `K` be a compact
regular energy window (`K ∩ {V(v)} = ∅`). At each vertex let `F_v` be a speed-independent
reversible routing law on the incident edge-ends (`F_v² = id`). Let `g` be the graph-scattering
trajectory of an initial state inside an edge with energy in `K`, on a time window `[0, T]`, and
let `ε ↦ chain ε` describe the well-prepared trajectories of the thin Hamiltonian networks `M_ε`
(tubes of width `O(ε)`, routers `J_{v,ε} = ε J_v`), projected to the graph, with initial data
converging to those of `g`. Then, as `ε → 0⁺`, the microscopic trajectories pass through the same
routers through the same edge-ends, their impact times converge to the graph impact times, and
their longitudinal states converge to `g` uniformly on compact subsets of `[0, T]` avoiding the
impact times, and pointwise at every non-impact time.

**Theorem (explicit branching model).** There is an explicit smooth, genuinely branching
microscopic Hamiltonian `H_ε(x, p) = ½|p|² + microPot ε x` on `ℝ² × ℝ²` whose trajectories realize
the deterministic routing law `F⋆(η₁) = η₂`, `F⋆(η₂) = η₁`, `F⋆(η₃) = η₃` at a **valence-3**
vertex of the star graph `Γ⋆`, and for which the chain hypotheses above are *proved rather than
assumed*.

**Theorem (universal model, zero potential).** For **every** finite metric graph `Γ`, **every**
speed-independent involutive routing law `F` on it, the zero graph potential, the compact regular
window `K⋆ = [1/2, 2]`, **every** well-prepared initial state and **every** horizon `T`, there is
an explicit smooth microscopic Hamiltonian `H_ε(x,p) = ½|p|² + netPot ε x` on `ℝ² × ℝ²`,
constructed functorially from `(Γ, F)`, whose genuine trajectories project to the deterministic
graph-scattering trajectory of `(Γ, F)` as `ε → 0⁺`.  See
[the universal model](#the-universal-model-arbitrary-γ-arbitrary-f) below for exactly what is and
is not covered.

**Theorem (thin-junction Hamiltonian limit, Theorem IX.6).** Let a particle be governed by the
smooth mechanical Hamiltonian `H_ε = ½|p|² + W_ε` on `ℝ² × ℝ²` (`W_ε` `C²` and bounded below, so the
flow `Φ^ε_t` is complete) and confined to a family of thin tubular networks collapsing onto `Γ` as
`ε → 0⁺`.  Suppose that on a compact window `K ⊂ (max_Γ V, ∞)` the edge dynamics becomes
asymptotically one-dimensional — hypothesis (E): vanishing transverse displacement and transverse
energy, longitudinal force `⟨∇W_ε, τ_e⟩` equal to `V_e'(q)` up to `γ_ε → 0` — and that each
junction routes by `F` within a vanishing residence time — hypothesis (J).  Then the projected
flow `π_ε Φ^ε_t(z_ε)` of prepared initial states converges, on every finite time interval, to the
deterministic metric-graph flow `Φ_t^{Γ,F}(z)`.  The graph vertex law
`F_v` is therefore literally the limiting channel map of a collapsed microscopic junction.  Both
hypotheses are *local statements about the Hamiltonian flow*; neither the projected `HybridChain`
nor its four convergence parameters are assumed.  See
[the thin-junction limit theorem](#the-thin-waveguide--thin-junction-limit-theorem) below for
exactly what is and is not covered.

**Theorem (explicit thin junction).** The explicit valence-3 model above satisfies the hypotheses
(E), (J) and (D) — proved from Hamilton's equations, energy conservation and barrier estimates
— so the deterministic law `F⋆(η₁) = η₂`, `F⋆(η₂) = η₁`, `F⋆(η₃) = η₃` at the branching vertex
arises as an *instance* of the thin-junction limit theorem.

**Theorem (the limit is the paper's global graph flow).** Every routing law is a Borel
energy-preserving vertex scattering law of the paper (`RoutingLaw.toBorelScattering`), and every
finite time window of the paper's global metric-graph flow
`Φ_t^{Γ,F} = FlightState.trajectory V (F.toBorelScattering V) a` **is** a `GraphTrajectory V F`
(`exists_graphTrajectory_of_flow`).  Combining this with the previous theorem gives, for
well-prepared microscopic data converging to a limiting graph state `z`,

`π_ε Φ_t^{H_ε}(z_ε) ⟶ Φ_t^{Γ,F}(z)`  uniformly on compact subsets of `[0, T]` avoiding the impacts

(`thin_junction_global_flow_limit`).  See
[the global graph flow](#the-global-graph-flow-interface) below.

**Theorem (energy-dependent deterministic junction).**  There is **one** explicit smooth
microscopic Hamiltonian family `H_ε(x,p) = ½|p|² + gatePot2 ε x` on `ℝ² × ℝ²` and two **disjoint**
compact regular energy windows `K₋ = [1/2, 3/5]` and `K₊ = [3/2, 2]`, lying on either side of the
gate, `max K₋ < g₀ = 7/10 < E_c < min K₊` with `E_c = max G_ε ∈ (1.15, 1.365)` independent of `ε`,
on which that *same* family realizes, for every `ε ∈ (0, 1/100)` and with residence time
`θ_ε = 32ε`, **different** deterministic routing laws: total reflection `F₋` below the gate and the
transmitting law `F₊ = F⋆` above it (`explicit_energy_dependent_junction`, Theorem IX.10).  The
mechanism is an energy-selective barrier across the through channel at the branching vertex.
Nothing is claimed for energies between the windows.
See [the energy-dependent junction](#an-explicit-energy-dependent-deterministic-junction) below.

**Theorem (determinism of the energy-dependent junction).**  On each of the two windows the gated
family has a **deterministic channel reduction**: whatever the unresolved transverse data of the
incoming state, the particle leaves through the routed germ and through no other
(`explicit_energy_dependent_junction_deterministic`).  Consequently the coarse-grained vertex
kernel is the Dirac mass at `F₋(η)` on `K₋` and at `F₊(η)` on `K₊`, for *every* probability measure
on the unresolved data, and the two kernels differ already on the channel `η₁`
(`gate_channelKernel_differs`).

**Proposition (coarse-graining).**  With unresolved transverse data `ξ` distributed according to a
probability measure `μ` and a microscopic outgoing-channel map `C_v(η, r, ξ)`, the observed vertex
law is the channel kernel `P_v(ζ ∣ η, r) = μ{ξ : C_v(η, r, ξ) = ζ}`.  If `C_v(η, r, ·) = F_v(η, r)`
for `μ`-almost every `ξ`, then `P_v(· ∣ η, r) = δ_{F_v(η,r)}` (`channelKernel_dirac`); if two
distinct germs are each attained on a set of positive measure, no Dirac mass is the kernel
(`channelKernel_ne_dirac`).  `HasDeterministicChannelReduction` is exactly the first case
(`channelKernel_of_deterministic`).  See
[coarse-graining](#deterministic-and-stochastic-coarse-graining) below.

Main declarations:

* `MechanicalPotential.microscopic_realization`, `MechanicalPotential.microscopic_realization_state`
  (`Realization.lean`) — the general theorem;
* `explicit_branching_hamiltonian_realization` (`BranchingRealization.lean`) — the explicit
  valence-3 smooth Hamiltonian model, with the general theorem instantiated on it;
* `universal_reversible_realization` (`UniversalRealization.lean`) — the universal model for
  arbitrary `Γ` and arbitrary `F`, with the zero graph potential;
* `thin_junction_hamiltonian_limit` (`ThinLimit.lean`) — the general thin-waveguide /
  thin-junction limit theorem, with hypotheses at the level of the microscopic Hamiltonian edge
  and junction dynamics;
* `explicit_thin_junction_realization` (`StarLimit.lean`) — the explicit smooth three-channel
  junction as an instance of it, together with `explicit_star_junction` (Theorem IX.9: the scales
  `δ_ε = 8ε`, `θ_ε = 23ε` and the hypotheses for every `ε ∈ (0, 1/100)`),
  `starNetwork_satisfiesEdgeReduction`, `starNetwork_junctionScattering`,
  `starNetwork_hasDeterministicChannelReduction` and `starNetwork_channelsSeparated`;
* `RoutingLaw.toBorelScattering`, `exists_graphTrajectory_of_flow` (`GraphFlow.lean`) and
  `thin_junction_global_flow_limit` (`ThinGlobalFlow.lean`) — the interface to the paper's own
  global metric-graph flow;
* `explicit_energy_dependent_junction` (`GateLimit.lean`) — one microscopic Hamiltonian family
  realizing two different deterministic routing laws on two disjoint energy windows, together with
  the corollaries `gate_realization_low` and `gate_realization_high`;
* `explicit_energy_dependent_junction_deterministic`, `gate_channelKernel_differs`
  (`GateDeterminism.lean`) — the outgoing channel is independent of the unresolved transverse data
  in both regimes, so the coarse-grained kernels are Dirac and differ;
* `channelKernel_dirac`, `channelKernel_ne_dirac`, `channelKernel_of_deterministic`
  (`ChannelKernel.lean`) — the deterministic / stochastic coarse-graining dichotomy.

All of them depend only on the axioms `propext`, `Classical.choice`, `Quot.sound` (checked with
`#print axioms`); there is no `sorry` in the directory. Build with `lake build` from the repository
root (Lean `v4.31.0`, Mathlib `v4.31.0`).

## How the analytic input enters

The theorem is formalized with the *hybrid chain* as the central object (`HybridChain.lean`).
A hybrid chain is a finite alternating sequence of edge flights and router passages with four
nonnegative parameters:

| parameter | meaning | graph trajectory | thin network | explicit model (`starNetwork`) | gated model (`gateNetwork`) |
|---|---|---|---|---|---|
| `offset` | the tube of an edge ends at longitudinal distance `offset` from each vertex | `0` | `O(ε)` | `8ε` | `8ε` |
| `dwell` | maximal time spent inside a router | `0` | `O(ε)` | `23ε` | `32ε` |
| `odeErr` | tolerance in Hamilton's equations along a flight | `0` | `→ 0` | **exactly `0`** | **exactly `0`** |
| `momErr` | tolerance in the outgoing longitudinal momentum after a passage | `0` | `→ 0` | **exactly `0`** | **exactly `0`** |

(The hybrid chains of the branching model `explicit_branching_hamiltonian_realization` and of the
universal model are built with the cruder dwell bound `100ε` of `capReflTime_le`; the two thin
networks use the paper's `θ_ε = 23ε` and `32ε`, from the sharp reflection time of Lemma IX.8.)

The **graph-scattering trajectory** is the chain with all parameters `0`
(`GraphTrajectory := HybridChain V F ChainParams.zero`): exact edge Hamiltonian flights,
instantaneous impacts, exit edge-end `F_v(η)` and departure momentum `-σ(F_v η)|p_in|`.
The **thin-network family** (`ThinNetworkFamily`, `Microscopic.lean`) is a family of chains whose
four parameters tend to `0`.

## The explicit branching model

Configuration space `ℝ²` with coordinates `(u, w)`; the star `Γ⋆` is embedded as three unit
segments meeting at the origin: edge `0` along `u ∈ [-1,0]` (graph coordinate `q = -u`), edge `1`
along `u ∈ [0,1]` (`q = u`), edge `2` along `w ∈ [0,1]` (`q = w`). The potential is

```
microPot ε (u,w) = (1-m)·(wellPot ε w + capPot ε u) + m·(wellPot ε u + armPot ε w),
m = plateau (3ε) (6ε) w
```

with `wellPot ε z = wellProfile (z/ε)` (the transverse tube wall, zero on `|z| ≤ ε`, height `4`
outside `|z| ≥ 2ε`), `capPot ε u = barrierProfile ((u-1)/ε) + barrierProfile ((-u-1)/ε)` (the caps
at the outer vertices) and `armPot ε w = barrierProfile ((7ε-w)/ε) + barrierProfile ((w-1)/ε)`
(the junction barrier of the third arm and its cap). It is `C^∞` for every `ε`.

Two design points make the model completely analysable while keeping it genuinely branching:

* **Exact separability and dynamical disconnection.** On `w ≤ 3ε` the potential is an exact *sum*
  `wellPot ε w + capPot ε u`; on `w ≥ 6ε` it is the exact sum `wellPot ε u + armPot ε w`; and on
  the interpolation zone `3ε ≤ w ≤ 6ε` it is `≥ 4`, which exceeds every energy of the window
  `K⋆ = [1/2, 2]` (`microPot_ge_four_of_mid`). A trajectory of the window therefore never enters
  the glue, so no estimate on it is ever needed, while the junction still has three channels.
* **`expNegInvGlue` rather than `Real.smoothTransition`.** Mathlib proves nothing about
  `deriv Real.smoothTransition`, so a turning-time estimate built on it would be out of reach;
  `expNegInvGlue` has the explicit derivative `s⁻²·expNegInvGlue s`, which yields the slope bound
  `deriv barrierProfile ≥ 4e⁻³` on `[1/4, 1]` and hence an explicit `O(ε)` dwell time.

## Fully proved in Lean

### The general theorem

| Mathematical step | Lean declarations | File |
|---|---|---|
| finite graph, edge-ends | `FiniteMetricGraph`, `EdgeEnd` (existing) | `Basic.lean` |
| involutive speed-independent routing | `RoutingLaw`, `routeGerm`, `routeGerm_routeGerm`, `departureMomentum`, `sign_mul_departureMomentum`, `abs_departureMomentum` | `Routing.lean` |
| routing laws are the paper's scattering laws | `RoutingLaw.toScattering`, `speedEndpoint_toScattering` (Prop. III.2), `toScattering_isReversible` (Lemma III.5) | `RoutingScattering.lean` |
| graph Hamiltonian trajectories, impact times, projected state | `HybridChain`, `GraphTrajectory`, `flightIndex`, `state`, `flight_ode_exact`, `arrive_eq`, `depart_mom_eq` | `HybridChain.lean` |
| energy conservation along the graph trajectory | `hamiltonian_eq_start`, `hamiltonian_start_succ`, `hamiltonian_eq_energy` | `HybridChain.lean` |
| regular-energy lemma (uniform positive speed at/near vertices) | `exists_vertex_speed_lower_bound`, `exists_collar_speed_lower_bound`, `exists_impact_speed_lower_bound` | `RegularEnergy.lean` |
| transversality of impacts | `sign_mul_impact_pos`, `impact_energy` | `RegularEnergy.lean` |
| speed / force bounds on `K` | `exists_graph_speed_bound`, `exists_force_bound`, `exists_length_lower_bound` | `RegularEnergy.lean` |
| **no-Zeno**: uniform lower bound between graph impacts on `K` | `IsFlight.duration_lower_bound_departure`, `exists_noZeno_separation` | `FlightEstimates.lean`, `RegularEnergy.lean` |
| microscopic no early re-entry | `IsFlight.duration_lower_bound_interior`, `eventually_duration_lower_bound` | `FlightEstimates.lean`, `Step.lean` |
| single-flight estimates | `IsFlight.momentum_drift`, `coordinate_travel`, `directed`, `dist_le`, `norm_w_le` | `FlightEstimates.lean` |
| **transverse crossing** | `IsFlight.crossing`, `germ_eq_of_boundary_eq`, `boundary_cases` | `FlightEstimates.lean` |
| **edge approximation** `(q_ε, p_∥,ε) → (q, p)` before the next junction (Grönwall) | `exists_uniform_lipschitz_edgeVectorField`, `IsFlight.dist_le_gronwallBound`, `IsFlight.dist_le_closeness` | `EdgeApproximation.lean` |
| one impact, deterministic estimate | `exists_interior_margin`, `impact_approach`, `coordinate_at_entry`, `step_core` | `StepCore.lean` |
| **convergence of impact times**, channel stability, invariant propagation | `GraphConstants`, `exists_graphConstants`, `step_quant`, `step` | `Step.lean` |
| last flight | `final_core`, `final_step` | `Realization.lean` |
| **global convergence by finite induction over impacts** | `matches_all`, `microscopic_realization`, `microscopic_realization_state` | `Realization.lean` |
| rescaling `J_{v,ε} = εJ_v`, perturbation, channel stability, `O(ε)` dwell | `scaledRouter_hasDerivAt`, `dist_le_of_perturbed_junction`, `channel_stability`, `physical_dwell_le` | `ScaledJunction.lean` |
| one-sided mean-value estimates | — | `IntervalEstimates.lean` |

### The explicit branching model

| Mathematical step | Lean declarations | File |
|---|---|---|
| valence-3 star `Γ⋆`, `card_starIncidentEnds = 3` | `starGraph`, `vStar`, `starIncidentEquiv`, `card_starIncidentEnds` | `BranchingGraph.lean` |
| the routing law `F⋆(η₁)=η₂`, `F⋆(η₂)=η₁`, `F⋆(η₃)=η₃`, involutive | `starRouting`, `starRouting_channel₁/₂/₃`, `starRouting_involutive` | `BranchingGraph.lean` |
| compact regular window `K⋆ = [1/2,2]` | `windowStar`, `isCompact_windowStar`, `windowStar_regular` | `BranchingGraph.lean` |
| the deterministic graph trajectory of `Γ⋆` (all `HybridChain` fields at `ChainParams.zero`) | `freeGraphTrajectory`, `starTrajectory` | `FreeGraphTrajectory.lean`, `BranchingGraph.lean` |
| smooth profiles with **explicit derivative bounds** | `barrierProfile`, `deriv_barrierProfile_ge`, `barrierProfile_le_quarter`, `wellProfile` | `BarrierProfile.lean` |
| the smooth microscopic potential and its force | `microPot`, `contDiff_microPot`, `microForce`, `microForce_of_through` | `MicroscopicPotential.lean` |
| exact separability; the glue is inside a barrier of height `4 > max K⋆` | `microPot_of_through`, `microPot_of_arm`, `microPot_ge_four_of_mid` | `MicroscopicPotential.lean` |
| **reflection at a barrier** with exact momentum reversal and explicit dwell bound | `Reflection.Setup`, `reflect_of_barrier`, `reflectionTime` | `Reflection.lean` |
| global ODE existence on `[0,T]` for a bounded `C¹` field | `exists_integralCurve_Icc` | `GlobalFlow.lean` |
| 1-D Newtonian existence with bounded force (momentum cutoff) | `exists_newton1D` | `MicroscopicTrajectory.lean` |
| **existence of a genuine 2-D microscopic trajectory; transverse confinement `\|w\| < 2ε`; exactly free longitudinal motion** | `exists_microTrajectory` | `MicroscopicTrajectory.lean` |
| energy conservation of `H_ε`; `1 ↔ 2` channel selection; `3 ↦ 3` barrier margin `4 - E ≥ 2` | `microHamiltonian_conserved`, `stays_in_through_channel`, `arm_barrier_margin`, `channels_disjoint` | `BranchingModel.lean` |
| the chain parameters of the model and their vanishing | `starParams`, `starParams_offset/dwell/odeErr/momErr_tendsto` | `BranchingModel.lean` |
| exact decoupling of the two caps (`deriv (wallPot ε) y = 0` for `y ≤ 0`) | `deriv_wallPot_of_nonpos`, `deriv_capPot_right/_left` | `CapDynamics.lean` |
| **`O(ε)` dwell time of a cap passage** (`≤ 100ε`, using `e³ ≤ 21`) | `capReflTime`, `capReflTime_le` | `CapDynamics.lean` |
| **exactly free motion in a flat region** (first-crossing bootstrap) | `free_motion`, `CapSolution.free`, `free_of_endpoints` | `CapDynamics.lean` |
| **the caps reverse the momentum *exactly*** | `CapSolution.reflect_right/_left/reflect` | `CapDynamics.lean` |
| the itinerary of the through channel (`0,1,1,0,0,…`, alternating selector) | `itinerary_snd_channel₁`, `itinerary_through` | `MicroscopicChain.lean` |
| **the recursion over the cap passages and its invariant** | `ThroughRun`, `beta`, `alpha`, `sigma`, `Inv`, `Inv.flight`, `Inv.exit`, `Inv.succ`, `inv` | `MicroscopicChain.lean` |
| **the projected `HybridChain` of a microscopic trajectory** (all 18 fields) | `ThroughRun.chain` | `MicroscopicChain.lean` |
| **the chain is the graph projection of the microscopic trajectory** | `ThroughRun.projection`, `embedSign` | `MicroscopicChain.lean` |
| the microscopic window covers the graph one | `startT_lower`, `stopT_lower`, `stopT_le_horizon` | `MicroscopicChain.lean` |
| exact separability and force of the arm; the `3 ↦ 3` confinement `w > 6ε` | `microForce_of_arm`, `ArmSolution.gt_six`, `exists_armTrajectory` | `ArmDynamics.lean` |
| **exact reflection at the junction barrier of the arm** (`F⋆(η₃) = η₃`) and at its cap | `ArmSolution.reflect_junction`, `ArmSolution.reflect_cap`, `armReflTime_le_cap` | `ArmDynamics.lean` |
| **the projected `HybridChain` of the third arm**, its invariant and its projection | `ArmRun`, `ArmRun.Inv`, `ArmRun.chain`, `ArmRun.projection` | `ArmChain.lean` |
| **the concrete `ThinNetworkFamily` and the final theorem, for both channels** | `IsMicroscopicProjection`, `RunPackage`, `exists_throughPackage`, `exists_armPackage`, `realization_core`, `explicit_branching_hamiltonian_realization` | `BranchingRealization.lean` |

The docstring of every theorem names the step of the mathematical proof it implements.

## What the explicit model proves, and what it does not

**Proved from the Hamiltonian, not assumed** (this was item 1 of the previous "assumed" list):

* thin-tube confinement `|w(t)| < 2ε` for well-prepared transverse data — `exists_microTrajectory`;
* the projected longitudinal dynamics solves the graph Hamilton equations **exactly**
  (`odeErr = 0`) — `CapSolution.free`, `ThroughRun.chain.flight_ode`;
* the flights enter a router only at the tube boundary `q = 8ε` resp. `q = 1 - 8ε` —
  `crv_fst_mem_Icc`, `crv_fst_mem_Ioo`, `arrive`;
* the passage entered through `η` leaves on the edge of `F⋆(η)` at the tube boundary —
  `edge_succ`, `depart_coord`, built on `itinerary_through`; in particular the particle arriving at
  the valence-3 vertex along `η₁` leaves along `η₂` and **not** along `η₃`;
* the passage takes a time `≤ 100ε → 0` — `capReflTime_le`, `start_succ_le`;
* the outgoing longitudinal momentum is **exactly** the routed momentum (`momErr = 0`) —
  `CapSolution.reflect`, `depart_mom`;
* finitely many passages in the window, and a last flight covering it — `ThroughRun.inv`,
  `stopT_lower`, `ConvergesInitially.finalTime`;
* and the resulting chain *is* the projection of a genuine solution of Hamilton's equations for
  `H_ε` — `IsMicroscopicProjection`, `exists_throughRun`.

**Both channels are realized.**  `MicroInitialState` carries a `Channel` — `through` (edge `0`,
routed `η₁ ↔ η₂`) or `arm` (edge `2`, routed `η₃ ↦ η₃`) — and
`explicit_branching_hamiltonian_realization` covers both.  In the through channel the particle
passes *straight through* the valence-3 vertex, leaving along `η₂` and never along `η₃`; in the
arm it is turned around by the junction barrier, leaving along `η₃`.

**Restrictions of the explicit model** (stated honestly, not hidden):

1. The initial data are on the axis of their tube: `exists_throughPackage` uses the transverse
   data `w(0) = 0`, `p_w(0) = 0` and `exists_armPackage` uses `u(0) = 0`, `p_u(0) = 0`. The
   longitudinal analysis is independent of the transverse motion (the potential is an exact sum in
   each channel), and `exists_microTrajectory` proves the confinement `|w| < 2ε` for *arbitrary*
   well-prepared transverse data.
2. Uniqueness of the microscopic trajectory is not used and not proved: `exists_throughPackage`
   and `exists_armPackage` exhibit *a* solution and show the chain is its projection.
3. The initial speed is normalized to `c ∈ [1,2]`, equivalently the energy to `K⋆ = [1/2,2]`;
   this is the compact regular window of the model, not a further restriction.

## Still assumed in the general theorem

For the *general* theorem (`microscopic_realization`), the chain description remains a hypothesis:
`ThinNetworkFamily` is the interface, and the explicit model above is a proof that the interface is
non-vacuous and satisfiable by a genuine smooth branching Hamiltonian. Two further items remain
outside this development:

1. **Reference-junction hypotheses 1–4** (`ReferencePassage`, `ScaledJunction.lean`) for a
   *general* scaled router `J_{v,ε} = εJ_v`: exit through `F_v(η)` with a positive basin margin,
   bounded scaled dwell time, exit speed close to the incoming speed. `ReferencePassage.scaled_exit`
   derives the router properties from them for an `O(ε)`-perturbation of the reference passage.
   For the explicit model this route is bypassed entirely: the router is analysed directly by
   `reflect_of_barrier`.
2. **Existence of the graph trajectory** for arbitrary given initial data on an arbitrary graph.
   This is now *proved*, not assumed: `RoutingLaw.toBorelScattering` makes a routing law a Borel
   vertex datum of the paper, and `exists_graphTrajectory_of_flow` (`GraphFlow.lean`) turns every
   finite window of the resulting global flow `FlightState.trajectory` into a `GraphTrajectory V F`
   with the same projected state function.  Since that flow exists for *every* `C²` edge potential
   and every regular initial flight state, a graph trajectory is available for arbitrary `V`.  See
   [the global graph flow](#the-global-graph-flow-interface).

## The universal model: arbitrary `Γ`, arbitrary `F`

`universal_reversible_realization` (`UniversalRealization.lean`) is the universal counterpart of
the valence-3 theorem:

```lean
theorem universal_reversible_realization (Γ : FiniteMetricGraph) (F : RoutingLaw Γ)
    (x₀ : WellPreparedState Γ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ g : GraphTrajectory (zeroPotential Γ) F,
      (g.germ 0 = x₀.germ ∧ g.curve 0 0 = (x₀.q₀, EdgeEnd.sign Γ x₀.germ * x₀.c) ∧
        g.energy = x₀.c ^ 2 / 2 ∧ g.energy ∈ window) ∧
      UniversalMicroscopicConvergence g T
```

The quantifier order is `∀ Γ, ∀ F, ∀ x₀, ∀ T, ∃ (explicit microscopic realization)`; the graph `Γ`,
the routing law `F` and the vertex valences are arbitrary, and no low-valence case is enumerated.

### The construction

Every involution is a disjoint union of transpositions and fixed points, so `F` **resolves** `Γ`
into a `1`-manifold: gluing the edges along `F` at every vertex produces a disjoint union of
intervals and circles.  The microscopic network is a thin neighbourhood of that resolution.

1. **The layout** (`UniversalLayout.lean`, `UniversalFolds.lean`).  Starting from a germ `η₀`, the
   itinerary `η_j` is generated by `σ = otherEnd ∘ F`, a bijection of the finite set of germs, so
   it is purely periodic (`RoutingLaw.exists_period`).  A **fold** is an impact with
   `F(η_j) = η_j`, i.e. a `U`-turn.  `dirSign j ∈ {±1}` is the direction of flight `j`, reversing
   exactly at a fold, and `vpos j` is the corridor coordinate of the vertex reached by flight `j`.
   The **retrace lemma** — after a fold the itinerary, the directions and the vertex positions are
   the exact mirror images of the ones before it (`itinerary_retrace`, `dirSign_retrace`,
   `vpos_retrace`) — is the combinatorial form of reversibility `ρΦρ = Φ⁻¹`.  From it:
   the folds form an arithmetic progression `a, a+d, a+2d, …` (`FoldData.isFold_iff`), the fold
   positions alternate between exactly two values (`FoldData.vpos_fold`), every vertex position
   lies between them (`FoldData.vpos_mem`), and a vertex which is not a fold keeps a whole edge
   length of margin from both (`FoldData.interior_margin`).  Hence
   **`exists_corridor`**: every routing component has a corridor `[low, high]` whose two ends are
   exactly the two `F`-fixed germs of the component.
2. **The potential** (`UniversalCorridor.lean`, `UniversalNetwork.lean`).  With one corridor per
   edge-end germ, laid out at the integer heights `w = 0, 1, …, m-1` (`m = |EdgeEnd Γ|`),

   ```
   netPot ε m Λ (u,w) = tubeWall ε m w + Σ_i sel ε i w · corridorPot ε (Λ i) u,
   corridorPot ε Λ u  = wallPot ε (u - Λ) + wallPot ε (-u).
   ```

   `tubeWall` is at once the **transverse confinement** of every tube and the **barrier separating
   distinct routing components**; its height `4` exceeds `sup K⋆ = 2` (`netPot_ge_four_of_far`).
   `sel ε i` is `1` on the whole reachable tube `|w - i| ≤ 2ε`, so there the potential is the
   **exact sum** `wellPot ε (w-i) + corridorPot ε (Λ i) u` (`netPot_of_corridor`).
3. **The dynamics** (`UniversalTrajectory.lean`, `UniversalRun.lean`).  `exists_netTrajectory`
   produces a genuine solution of Hamilton's equations for `H_ε = ½|p|² + netPot ε m Λ` and proves
   the thin-tube confinement `|w - i| < 2ε` from conservation of the transverse energy against the
   wall height `4`; exact separability makes the longitudinal pair an exact solution of the
   one-dimensional corridor system, so `odeErr = 0`.  A single recursion over the flights
   (`NetRun.Inv`, `NetRun.Inv.router`, `NetRun.inv`) alternates *exactly free motion* between
   routers with the *exact cap reflection* at a fold and discharges all 18 fields of `HybridChain`
   (`NetRun.chain`) with `offset = 8ε`, `dwell = 100ε`, `odeErr = momErr = 0`.
4. **The family and the theorem** (`UniversalRealization.lean`).  `exists_netPackage` produces the
   run and the projection certificate `IsNetworkProjection` at every admissible scale;
   `universal_reversible_realization` assembles the `ThinNetworkFamily`, proves the four `tendsto`
   statements and feeds `microscopic_realization`.

### The five router properties, for arbitrary valence and arbitrary involution

| requirement | Lean | status |
|---|---|---|
| (1) cannot enter a competing routing component | `exists_netTrajectory` (`\|w - i\| < 2ε` for all time), `netPot_ge_four_of_far` | proved |
| (2) exits through exactly `F_v(η)` | `NetRun.chain.edge_succ`, `.depart_coord`, built on `Corridor.cap` / `Corridor.interior` | proved |
| (3) longitudinal speed preserved | `CorridorSolution.reflect` (exact reversal), `NetRun.Inv.router` | proved, exactly |
| (4) `O(ε)` physical time in the router | `capReflTime_le` (`≤ 100ε`), `NetRun.pass_le` (`16ε/c ≤ 100ε`) | proved |
| (5) leaves well-prepared | `NetRun.Inv` (`u = startPos j`, `p_u = dirSign j · c`) | proved |

### What the universal model does **not** cover

Stated explicitly rather than hidden.

1. **The graph potential is zero.**  This is the intermediate milestone: `universal_reversible_realization`
   is proved for `zeroPotential Γ`, i.e. free motion on the edges.  Arbitrary smooth edge potentials
   `V_e` are **not** covered; the corridor potential would have to carry `V` along the corridor and
   `CorridorSolution.free` (exactly free motion) would have to be replaced by an approximation
   argument.  The full target — arbitrary smooth `V` — is therefore *not* reached.
2. **The energy window is fixed at `K⋆ = [1/2, 2]`.**  The barrier height is the constant `4`
   built into `barrierProfile` and `wellProfile`.  An arbitrary compact regular window `K` would
   need a height-parameterized barrier `h · barrierProfile` with `h > sup K`; this is routine but
   is not done.
3. **The routers of the transpositions are geometric, not dynamical.**  A transposition
   `F_v(η) = ζ ≠ η` is realized by laying the two edges out *collinearly inside one straight
   corridor*, where the potential is flat: the particle passes straight through, which is exactly
   `F_v(η) = ζ` and nothing else.  Only the routers of the `F`-fixed germs are genuinely dynamical
   (a reflection off a smooth cap with exact momentum reversal and `O(ε)` dwell).  Consequently
   the microscopic network is a thin neighbourhood of the **routing-resolved `1`-manifold**
   `R(Γ, F)` — a disjoint family of straight corridors — rather than of an embedding of `Γ` in the
   plane: the `d_v` ports of a vertex `v` are all present in the network, but the ones belonging to
   different routing components sit in different corridors instead of meeting in a single cell of
   diameter `O(ε)`.
   This is a deliberate design decision, and it is where a genuine analytic obstruction sits: an
   *exactly separable* potential can never bend a trajectory, and a bent thin tube — where the
   particle physically turns a corner inside an `O(ε)` cell — is not exactly solvable.  Proving
   the five router properties for a bent tube is the thin-tube adiabatic limit (a Born–Oppenheimer
   /  geometric-potential analysis), which has no exact solution and is not formalized here.
   **The unproved statement is precisely this: for a smooth corridor whose core curve is bent by a
   right angle inside a cell of diameter `O(ε)`, a trajectory entering along the core with speed
   `c ∈ [1,2]` leaves along the outgoing core with speed `c + o(1)` after time `O(ε)`.**  It is not
   assumed anywhere in this development; the development avoids needing it by using straight
   corridors.
4. **Fold-free (circle) components are truncated to the horizon.**  A routing component with no
   `F`-fixed germ is a circle in `R(Γ, F)`; a straight corridor cannot be a circle.  For such a
   component `exists_corridor` places the two caps beyond the horizon of the run
   (`high = vpos (M+2) + minLen`, `low = -minLen`), so the caps are never reached and the corridor
   is a finite unrolling of the circle.  This is legitimate because the quantifier order allows the
   microscopic model to depend on `T`, but it means that for such components the corridor length
   grows with `T`.  For components *with* a fold — every component of a graph that has any
   `F`-fixed germ — the corridor is the interval between the two fold positions and is completely
   independent of `T`.
5. **Initial transverse data on the tube axis.**  As in the valence-3 model, the run is launched
   with `w(0) = i`, `p_w(0) = 0`.  `exists_netTrajectory` proves the confinement for arbitrary
   well-prepared transverse data; only the assembled package fixes the axis.
6. **Uniqueness of the microscopic trajectory is neither used nor proved.**

Items 4–6 are removed by `universal_reversible_realization_uniform` (`UniversalNetwork*.lean`):
one potential `uniPot F ε`, fixed by `(Γ, F)` and `ε` alone, serves every initial state and every
horizon; a circle component is an infinite corridor with zero longitudinal potential and no caps;
the initial data are any family of prepared states converging to the graph state; and the
convergence holds for every Hamiltonian trajectory through those data, on every compact time set
avoiding the impacts.  Uniqueness of microscopic trajectories is proved in
`MicroscopicCompleteness.lean` (`MicroTrajectory.eq_of_initial`).

### Universal model: file map

| step | declarations | file |
|---|---|---|
| corridor potential with two caps, exactly free motion, exact reflection at either cap | `corridorPot`, `CorridorSolution`, `.free`, `.free_of_endpoints`, `.reflect_top`, `.reflect_bot`, `.reflect` | `UniversalCorridor.lean` |
| the multi-corridor network potential, exact separability, the separating barrier | `coreFactor`, `tubeWall`, `sel`, `netPot`, `netPot_of_corridor`, `netPot_ge_four_of_far` | `UniversalNetwork.lean` |
| free graph trajectory for arbitrary edge lengths | `genTrajectory` | `UniversalGraphTrajectory.lean` |
| pure periodicity of the itinerary; folds; directions; vertex positions; the retrace lemma | `RoutingLaw.step`, `RoutingLaw.exists_period`, `IsFold`, `dirSign`, `vpos`, `itinerary_retrace`, `dirSign_retrace`, `vpos_retrace`, `vpos_mirror` | `UniversalLayout.lean` |
| the two-cap structure theorem and the corridor of a routing component | `Consec`, `FoldData`, `FoldData.isFold_iff`, `.dirSign_fold`, `.vpos_fold`, `.vpos_mem`, `.interior_margin`, `Corridor`, `exists_corridor` | `UniversalFolds.lean` |
| 2-D trajectories, thin-tube confinement, exact projection to the corridor system | `netForce`, `netForce_of_corridor`, `exists_netTrajectory`, `corridorSolution_of_net` | `UniversalTrajectory.lean` |
| corridor coordinates of a run, the flight recursion and the projected chain | `clen`, `cpos`, `spos`, `epos`, `NetRun`, `NetRun.Inv`, `NetRun.Inv.router`, `NetRun.inv`, `NetRun.chain`, `NetRun.chain_proj` | `UniversalRun.lean` |
| the network of `(Γ, F)`, the package, the family and the theorem | `theCorridor`, `netLengths`, `IsNetworkProjection`, `NetPackage`, `exists_netPackage`, `WellPreparedState`, `universal_reversible_realization` | `UniversalRealization.lean` |


## The thin-waveguide / thin-junction limit theorem

The universal model of the previous section answers *"which routing laws are realizable at all"*
by an artificial construction (straight corridors, geometric transposition routers).  The present
section answers a different and physically more meaningful question: **is the deterministic
metric-graph dynamics the singular thin-network limit of an ordinary smooth classical Hamiltonian
system?**  It is, and the limit theorem is stated with hypotheses that are *local statements about
the Hamiltonian flow* rather than statements about the projected chain.

### The microscopic physical model

`ThinHamiltonianNetwork Γ` (`ThinNetwork.lean`) is the data of Definition IX.3 of the paper:

* (i) a family of `C²` potentials `W_ε : ℝ² → ℝ`, **bounded below** (`contDiff_pot`,
  `pot_bddBelow`), giving the mechanical Hamiltonian `H_ε(x, p) = ½|p|² + W_ε(x)` on `ℝ² × ℝ²`;
* (ii) for each edge `e` a straight tube: a base point `base e`, a unit tangent `tang e` and a unit
  normal `nrm e`, hence a longitudinal coordinate `long e x` (in the graph coordinate of `e`) and a
  transverse displacement `trans e x`, with the corresponding momenta `longP e p`, `transP e p`,
  and a continuous transverse profile `transPot ε e`;
* (iii) the six scales of the paper, all `≥ 0` and tending to `0` as `ε → 0⁺`: `offset ε = δ_ε`
  (radius of the junction regions), `dwell ε = θ_ε` (residence time in a junction),
  `forceErr ε = γ_ε` (error in the longitudinal force), `momErr ε = μ_ε` (error in the outgoing
  momentum), `tubeWidth ε = w_ε`, `transErr ε = λ_ε` (transverse energy).

`MicroTrajectory ε S` is a genuine solution of Hamilton's equations `x' = p`, `p' = -∇W_ε(x)` on
`[0, S]`.  `MicroTrajectory.hamiltonian_eq` is the exact conservation law `H_ε(x(t), p(t)) = const`,
proved from the chain rule for the total derivative of `W_ε`.

**The flow `Φ^ε_t`** (`MicroscopicCompleteness.lean`).  Since `W_ε` is bounded below, through every
state there is a trajectory on every `[0, A]` (`exists_microTrajectory_of_bddBelow`, by a
cut-off and first-exit argument); since `W_ε` is `C²`, it is unique
(`MicroTrajectory.eq_of_initial`).  `ThinHamiltonianNetwork.flow ε t z` is the resulting complete
flow, for all `t ∈ ℝ` (`t < 0` through the reversal `ρ̃(x, ξ) = (x, -ξ)`), with `flow_zero`,
`flow_add` (`Φ_{s+t} = Φ_t ∘ Φ_s`, `s, t ≥ 0`), `flow_neg`, `flow_reversal`
(`Φ_b(ρ̃ Φ_b z) = ρ̃ z`), `hasDerivAt_flow` (Hamilton's equations at every `t`),
`hamiltonian_flow`, and `flowTraj` / `MicroTrajectory.eq_flow` (every trajectory is the flow).

The projection `π_ε` is `gState e x p = (long e x, longP e p)`.

### Prepared states and the hypotheses (E), (J), (D)

All are stated in `ThinHypotheses.lean`, exactly as printed in Sec. IX.B, and mention only the flow
`Φ^ε_t`, the tube geometry and the compact energy window `K`.  A state `(x, ξ)` is
**`Prepared` towards `η`** (Definition IX.4) if (P1) `δ_ε ≤ q_e(x) ≤ ℓ_e - δ_ε`, (P2)
`|y_e(x)| ≤ w_ε` and `E^⊥_{ε,e}(x, ξ) ≤ λ_ε`, (P3) `σ(η) p_e(ξ) > 0`, (P4) `H_e(pr_e(x, ξ)) ∈ K`;
**`Arriving` at `η`** if moreover `q_e(x) = a_η - σ(η) δ_ε`; **`Departing` through `η`** if
prepared towards `η̄` with `q_e(x) = a_η - σ(η) δ_ε`.  With `z(t) = Φ^ε_t(z)`, for every
`ε ∈ (0, ε₀)`, every end `η` and **every state** `z`:

* **(E) `SatisfiesEdgeReduction V K ε₀`** — if `z` is prepared towards `η` and not arriving at
  `η`, there is `b > 0` with an `EdgeFlight` on `[0, b]`: (E1) `δ_ε < q_e(x(t)) < ℓ_e - δ_ε` for
  `0 < t < b` and (P2) for `0 ≤ t ≤ b`; (E2) `z(b)` is arriving at `η`; (E3)
  `|⟨∇W_ε(x(t)), τ_e⟩ - V_e'(q_e(x(t)))| ≤ γ_ε` for `0 ≤ t ≤ b` (`longGrad`).
* **(J) `JunctionScatteringMap V K F ε₀`** (for a family `F : RoutingMap Γ` of maps;
  `JunctionScatteringConvergesTo` for a routing law) — if `z` is arriving at `η`, there is
  `b ∈ (0, θ_ε]` with `z(b)` departing through `F(η)` and
  `|p_{e'}(ξ(b)) + σ(F(η)) |p_e(ξ(0))|| ≤ μ_ε` (`JunctionPassage`).
* **(D) `ChannelUniquenessMap V K F ε₀`** — if `z` is arriving at `η`, then `z(t)` is departing
  through no end other than `F(η)` for `0 < t ≤ θ_ε`.

`HasDeterministicChannelReduction F ε₀` is (J) together with (D): whatever the unresolved
transverse data of the incoming state, the particle leaves through `F_v(η)` and through no other
germ.  `ChannelsSeparated` is the purely geometric companion: no microscopic state is departing
through two different germs.

**Proposition IX.5 (reversibility is forced)** is `ForcedInvolution.forced_involution`, as printed:
if a thin network satisfies (J) and (D) for a family `F` of maps, then `F(F(η)) = η` for every end
`η` at which, for some `ε ∈ (0, ε₀)`, a state is arriving.  The proof is the paper's, through
`flow_reversal` and the reversal of prepared states (`prepared_neg_iff`, `arriving_neg_iff`).

### The theorem

```lean
theorem thin_junction_hamiltonian_limit
    (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (F : RoutingLaw Γ)
    (K : Set ℝ) (hK : IsCompact K) (hwin : V.IsWindowAbove K)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hEdge : N.SatisfiesEdgeReduction V K ε₀)
    (hJunction : N.JunctionScatteringConvergesTo V K F ε₀)
    (x₀ : WellPreparedInitialState N V K ε₀)
    (g : GraphTrajectory V F) (hg : IsThinGraphLimit x₀ g) (hE : g.energy ∈ K)
    (hinit : (g.curve 0 0).1 ∈ Ioo (0 : ℝ) (Γ.length (g.edge 0)))
    {T : ℝ} (hT : T ≤ g.stop g.N) :
    ThinTrajectoryConvergesTo N x₀ g T
```

`V.IsWindowAbove K` is the window condition `K ⊂ (max_Γ V, ∞)` of the paper (every energy of `K`
exceeds every vertex value and every value of `V` on the closed edges); it implies
`K ∩ Exc = ∅` (`IsWindowAbove.not_mem_exceptionalEnergies`).  `x₀ : WellPreparedInitialState`
is a family `z_ε` prepared towards `η₀`, not arriving at `η₀`, with `pr_e(z_ε) → (q, r)`.

The conclusion `ThinTrajectoryConvergesTo` says: there is a `ThinNetworkFamily V F` whose chain is,
for all small `ε`, the `π_ε`-image of the flow `Φ^ε_t(z_ε)` (`IsThinProjection`,
`IsThinProjectionFrom`), whose initial data converge to those of `g`, and which `ThinRealizes g` —
i.e. the routed edge sequence matches, the junction entrance times converge with agreement of the
entry germs, and the projected longitudinal state converges uniformly on compact subintervals
avoiding the impacts.

**Neither the projected `HybridChain` nor its four convergence parameters are assumed.**  The
bridge is `ThinRun.lean`: along the flow `Φ^ε_t(z_ε)`, (E) and (J) are applied alternately by
finite induction, each time to the current state `Φ^ε_a(z_ε)` (`ThinRun.exists_flight`,
`exists_passage`, `Inv`, `Inv.flight`, `Inv.passage`, `Inv.succ`, `inv`), the impact germs are
produced by `RoutingLaw.itinerary`, and all eighteen fields of `HybridChain` are discharged
(`ThinRun.chain`), with parameters `thinParams N ε = (δ_ε, θ_ε, γ_ε, μ_ε)` whose four limits are
exactly the scale limits of the network; the chain's ODE tolerance is `γ_ε`, because the projected
curve has derivative `(p, -⟨∇W_ε, τ_e⟩)` (`ThinRun.flight_ode`).  The only further input is that the
run covers `[0, T]`, which needs a lower bound on the duration of a full flight.  It is *derived*
from the window condition (`ThinFlightBounds.lean`): along an edge flight, `(E + γ_ε σ q)' ≥ 0`
and `(E - γ_ε σ q)' ≤ 0` as long as `σ p > 0`, so the edge energy changes by at most `γ_ε ℓ_e`,
which keeps `p² ≥ 2(g - γ_ε ℓ_e) > 0` (`g` the gap of the window) and hence `σ p > 0` on the
whole flight (`EdgeFlight.sign_pos_and_energy`); this bounds the speed (`EdgeFlight.abs_longP_le`)
and the distance travelled (`EdgeFlight.toGo_le`) by constants of `K` and `V`
(`exists_window_constants`).  `microscopic_realization` then propagates the local estimates over
the finitely many impacts in `[0, T]` (`thin_family_exists`, `exists_thin_threshold`).

### The explicit smooth Hamiltonian junction

The valence-3 model of `MicroscopicPotential.lean` is presented as a `ThinHamiltonianNetwork` over
the star `Γ⋆` (`StarNetwork.lean`):

```
H_ε(x, p) = ½|p|² + microPot ε x        on ℝ² × ℝ²
offset = 8ε   dwell = 23ε   forceErr = 0   momErr = 0   tubeWidth = 2ε   transErr = ε
```

— the paper's network `N⋆` with `δ_ε = 8ε`, `θ_ε = 23ε`, `γ_ε = μ_ε = 0`, `w_ε = 2ε`, `λ_ε = ε`,
for every `ε ∈ (0, ε₀)`, `ε₀ = 1/100` (`explicit_star_junction`, Theorem IX.9) — with three
straight tubes — the two halves of the `u`-axis (edges `0`, `1`) and the positive
`w`-axis (edge `2`) — and the hypotheses (E), (J), (D) **proved**, not assumed (each from the flow
`Φ^ε_t` of an arbitrary prepared or arriving state, restricted to `[0, 2]` resp. `[0, 1]`):

| step | declarations | file |
|---|---|---|
| **the sharp reflection time of Lemma IX.8** and the paper's `eq:cap-time` `t_* < 2d/c + 7ε` | `Reflection.SharpSetup`, `Reflection.reflect_of_barrier_sharp`, `barrierTime`, `barrierTime_lt`, `capTime_lt` (`< 23ε`), `armTime_lt` (`< 9ε`) | `StarReflection.lean` |
| **Lemma IX.7** (the printed properties of `B` and `A_ε`) and **Lemma IX.8 as printed** (`P` agrees with `Ψ(y/ε)` only on `[-d, ε]`; return at `t_* ≤ 2d/c + 2ε(1/(4√E) + √(3/(2k)))` with `-d < y < ε` in between), derived from the global version by gluing the free continuation after the first exit below `-d` | `barrier_profile`, `barrier_reflection` | `StarBarrier.lean` |
| the longitudinal motions at every scale `0 < ε ≤ 1/100`, with the reflections in `23ε` and `9ε` | `CapMotion`, `CapMotion.reflect`, `ArmMotion`, `ArmMotion.reflect_cap`, `ArmMotion.reflect_junction` | `StarDynamics.lean` |
| the network, the tube frames, the junction disc of radius `8ε` | `starNetwork`, `starTang`, `starNrm`, `star_mouths_in_junction`, `star_junction_segment` | `StarNetwork.lean` |
| microscopic energy `≤ 2 + ε`; the interpolation zone `[3ε, 6ε]` is never entered; each channel is invariant; the exact one-dimensional reduction | `star_hamiltonian_le`, `star_not_mid`, `star_through_confined`, `star_arm_confined`, `StarThrough`, `StarArm`, `star_through`, `star_arm` | `StarConfinement.lean` |
| the edge-reduction hypothesis in both channels | `star_mk_edgeFlight`, `star_through_edgeFlight`, `star_arm_edgeFlight`, `starNetwork_satisfiesEdgeReduction` | `StarEdge.lean` |
| the four junction passages and the junction-scattering hypothesis | `star_junction_through_inner`, `star_junction_through_outer`, `star_junction_arm_inner`, `star_junction_arm_outer`, `starNetwork_junctionScattering` | `StarJunction.lean` |
| channel separation and deterministic channel reduction | `starNetwork_channelsSeparated`, `star_through_exit_unique`, `star_arm_exit_unique`, `starNetwork_hasDeterministicChannelReduction` | `StarDeterminism.lean` |
| Theorem IX.9 (scales, (E), (J), (D) for `ε ∈ (0, 1/100)`), the window above the potential, prepared initial data, the corollary | `explicit_star_junction`, `windowStar_isWindowAbove`, `starX`, `starP`, `starWellPrepared`, `explicit_thin_junction_realization` | `StarLimit.lean` |

What the explicit model **proves from Hamilton's equations** (each item is a Lean theorem, not a
hypothesis):

1. **The potential is bounded below** (`microPot_nonneg`), so the flow is complete.
2. **Transverse confinement.**  The transverse energy is exactly conserved and stays `≤ ε`, hence
   `|trans| < 2ε` — a tube of width `O(ε)` (`StarThrough.abs_trans_lt`, `StarArm.abs_trans_lt`).
3. **Correct outgoing-channel selection.**  The two-dimensional energy is `≤ 2 + ε` while the
   interpolation zone `3ε ≤ w ≤ 6ε` carries potential `≥ 4`; since that zone is a *closed* band
   separating the two channels, the intermediate value theorem alone confines every trajectory to
   the side it started on.  Inside the junction window the particle cannot reach any junction
   boundary other than `F⋆(η)` (`star_through_exit_unique`, `star_arm_exit_unique`).
4. **Exactly free longitudinal edge motion**: the projected pair solves `q' = p`, `p' = 0` exactly
   (`CapMotion.free_of_endpoints`, `ArmMotion.free_of_endpoints`), so the longitudinal force
   vanishes and (E3) holds with `γ_ε = 0` (`MicroTrajectory.longGrad_eq_zero_of_const`).
5. **Junction residence time `θ_ε = 23ε`**, as in the paper: `16ε/c ≤ 16ε` for the through
   crossing, `< 2ε/c + 7ε ≤ 9ε` for the arm barrier and `< 16ε/c + 7ε ≤ 23ε` for the outer caps
   (Lemma IX.8 with the sharp time `Reflection.sharpTime`, and `eq:cap-time`, `barrierTime_lt`).
   The paper's turning-time integral `∫ dy/√(2(E - P))` and time-reversal argument are replaced
   by an equivalent differential inequality: below the turning point `√(y_* - y)` changes at rate
   at least `√(2k)/2` (`Reflection.sqrt_gap_climb`, `sqrt_gap_descend`), which gives exactly the
   paper's bound `2d/c + 2ε(1/(4√E) + √(3/(2k)))`.
6. **Exact momentum reversal**, hence `momErr = 0` (`CapMotion.reflect`,
   `ArmMotion.reflect_cap`, `ArmMotion.reflect_junction`).
7. **Impact-time convergence and convergence on every finite time interval**, inherited from the
   general theorem via `explicit_thin_junction_realization`.

The explicit realization is therefore an **instance** of the general physical-limit theorem, not a
parallel development:

```lean
theorem explicit_thin_junction_realization (η₀ : starGraph.EdgeEnd) {q₀ c : ℝ}
    (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) {M : ℕ} (hM : 1 ≤ M) {T : ℝ}
    (hT : T ≤ FreeTrajectory.stopTime η₀ q₀ c M M) :
    ∃ g : GraphTrajectory (zeroPotential starGraph) starRouting,
      g.N = M ∧ (∀ j, g.germ j = starRouting.itinerary η₀ j) ∧
        IsThinGraphLimit (starWellPrepared η₀ hq₀ hc1 hc2) g ∧
        ThinTrajectoryConvergesTo starNetwork (starWellPrepared η₀ hq₀ hc1 hc2) g T
```

with `explicit_star_routing : F⋆(η₁) = η₂ ∧ F⋆(η₂) = η₁ ∧ F⋆(η₃) = η₃`.

### What the thin-junction development does **not** cover

Stated explicitly rather than hidden.

1. **The scattering law is `RoutingLaw Γ`, not the paper's full `ScatteringLaw`.**  A `RoutingLaw`
   is a *speed-independent involutive* per-vertex germ map, with departure momentum
   `p ↦ -sign(F_v(η)) · |p|`.  This is the strongest subclass that the microscopic hypotheses can
   support here, and the restriction is real: the junction hypothesis demands that the outgoing
   longitudinal momentum equal the routed momentum up to `momErr ε → 0`, so the microscopic
   junction must preserve the speed in the limit; and the abstract machinery
   (`HybridChain`, `RegularEnergy`) uses involutivity to run the impact induction backwards.  A
   speed-dependent or non-involutive law is *not* covered.  This is the "strongest correct
   subclass" the request asks for, stated rather than papered over.
2. **The graph trajectory `g` is a hypothesis of the general theorem, but no longer a
   restriction.**  `thin_junction_hamiltonian_limit` takes `g : GraphTrajectory V F` as an input.
   `exists_graphTrajectory_of_flow` now supplies it for arbitrary `V` from the paper's own flow,
   and `thin_junction_global_flow_limit` is the resulting unconditional form; the only residual
   input is the compatibility clause `g.germ 0 = x₀.germ` already present in `IsThinGraphLimit`
   (see [the global graph flow](#the-global-graph-flow-interface)).
3. **The microscopic configuration space is the plane and the tubes are straight.**  `base`,
   `tang`, `nrm` are constant along each edge.  Bent tubes — where the particle physically turns a
   corner inside an `O(ε)` cell — are not covered; this is the same analytic obstruction (the
   thin-tube adiabatic / geometric-potential limit) documented for the universal model above, and
   it is nowhere assumed.
4. **The explicit model has `V = 0` and the fixed window `K⋆ = [1/2, 2]`, with `ε < 1/100`.**  The
   *general* theorem allows arbitrary `C²` edge potentials `V` and arbitrary compact `K` above the
   potential; only the explicit verification is specialized, because the barrier height `4` of
   `barrierProfile` is a constant of the model.
5. **The three channels are attached to one connected geometric junction region, but the region is
   dynamically split — and that is the physics.**  `star_junction_segment` proves that the three
   tube mouths *and the radial segments joining them to the origin* lie in the single disc of
   radius `8ε` about the origin, so the model really is one junction cell of diameter `O(ε)` with
   three ports, not three unrelated corridors.  Inside that cell the junction barrier at `w ≈ 7ε`
   blocks passage between the third arm and the through channel; that is exactly how
   `F⋆(η₃) = η₃` is realized, and it is proved (`ArmMotion.reflect_junction`,
   `star_arm_confined`), not assumed.  What is **not** claimed is that a particle can pass from the
   arm into the through channel — it cannot, by design.
6. **The window condition.**  The theorem assumes `K ⊂ (max_Γ V, ∞)`, as the paper does
   (`eq:window-above`), not merely `K ∩ Exc = ∅`: with (E) as printed, the speed along a flight is
   controlled only through the window gap (`ThinFlightBounds.lean`), and that control is what makes
   the run cover a given time window.

## The global graph flow interface

The realization programme's limiting object is a `GraphTrajectory V F` — a finite hybrid chain with
all four parameters `0`.  The paper's own object is the global flow

```
Φ_t^{Γ,F}(z) = MechanicalPotential.FlightState.trajectory V S a t,   S a Borel vertex datum,
```

defined for every `t ≥ 0` by `UnifiedTrajectory.lean`.  Two steps connect them.

### Step 1: a routing law is a Borel vertex datum

`RoutingScattering.lean` already produced the *algebraic* law `F.toScattering V`.  What the paper's
flow needs in addition is Borel measurability of the vertex bijection.  In the speed charts of
`Measurable.lean` — `Γ.incomingSpeedChart v`, `Γ.outgoingSpeedChart v`, which are measurable
equivalences `IncidentEnds v × PositiveSpeed ≃ᵐ IncomingBoundary v` — the routing law is literally

```
(η, r) ↦ (F_v η, r),
```

a permutation of the finitely many incident germs times the identity on the speed.  The germ space
carries the discrete σ-algebra, so both directions are measurable and

```lean
noncomputable def RoutingLaw.toBorelScattering (V : MechanicalPotential Γ) :
    MechanicalPotential.BorelEnergyPreservingScattering V
```

is a genuine vertex datum of the paper.  `scatter_germ` and `scatter_momentum` identify its vertex
step with `F.routeGerm` and `F.departureMomentum`, and `speedEndpoint_toBorelScattering` is
Proposition III.2 for it.

### Step 2: a finite window of the flow is a graph trajectory

`FlowRun S a M TM` records a finite window: the scattered chain of `a` is defined through `M`
scattering events, and the last flight is followed to a time `TM` still strictly inside it.
`exists_flowRun` produces such a window past every horizon.  `FlowRun.chain` then builds a
`GraphTrajectory V F` out of it, discharging all nineteen `HybridChain` fields from the existing
flight-state API:

| chain field | flow ingredient |
|---|---|
| `start j`, `stop j` | `impactReal V S a j`, `impactReal V S a (j+1)` (or `TM` on the last flight) |
| `edge j`, `curve j t` | `(iterate V S a j).edge`, `flightCurve V (iterate V S a j) (t - impactReal j)` |
| `flight_ode` (`odeErr = 0`) | `flightCurve_hasDerivWithinAt_Icc` — the flight curve solves the edge system on the *closed* interval, one-sidedly at both ends |
| `flight_tube`, `flight_inside`, `final_inside` | `flightCurve_physical`, `flightCurve_interior` |
| `germ j`, `germ_edge`, `arrive` | `FlightState.arrivalGerm` from `maximalArrivalCovector`; `maximalArrivalCovector_coordinate` |
| `edge_succ`, `depart_coord`, `depart_mom` (`momErr = 0`) | `next_eq_some_of_bddAbove` together with `scatter_germ` / `scatter_momentum` |

and `chain_state_eq` proves that the chain's projected state function **is** the flow:

```lean
theorem exists_graphTrajectory_of_flow [Nonempty Γ.Edge] (F : RoutingLaw Γ) (a : V.FlightState)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ g : GraphTrajectory V F, g.edge 0 = a.edge ∧ g.germ 0 = a.arrivalGerm ∧
      g.curve 0 0 = a.state ∧ T ≤ g.stop g.N ∧
      ∀ t ∈ Icc (0 : ℝ) (g.stop g.N),
        g.state t = FlightState.trajectory V (F.toBorelScattering V) a t
```

### The corollary

`thin_junction_global_flow_limit` (`ThinGlobalFlow.lean`) combines the two:

```lean
theorem thin_junction_global_flow_limit [Nonempty Γ.Edge]
    (N : ThinHamiltonianNetwork Γ) (V : MechanicalPotential Γ) (F : RoutingLaw Γ)
    (K : Set ℝ) (hK : IsCompact K) (hwin : V.IsWindowAbove K)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hEdge : N.SatisfiesEdgeReduction V K ε₀)
    (hJunction : N.JunctionScatteringConvergesTo V K F ε₀)
    (x₀ : WellPreparedInitialState N V K ε₀) (a : V.FlightState)
    (hedge : a.edge = x₀.germ.1) (hstate : a.state = (x₀.q, x₀.r))
    (hgerm : a.arrivalGerm = x₀.germ)
    (hE : V.hamiltonian a.edge a.state.1 a.state.2 ∈ K)
    (hinit : a.state.1 ∈ Ioo (0 : ℝ) (Γ.length a.edge))
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ g : GraphTrajectory V F,
      (∀ t ∈ Icc (0 : ℝ) (g.stop g.N),
        g.state t = FlightState.trajectory V (F.toBorelScattering V) a t) ∧
      IsThinGraphLimit x₀ g ∧ ThinTrajectoryConvergesTo N x₀ g T
```

Read out: *the projected microscopic Hamiltonian trajectories converge, on `[0, T]`, to the paper's
graph flow through the limiting state `z`.*  `thin_junction_global_flow_limit_of_interior` supplies
the flight state `a` from a regular interior graph state via `FlightState.ofInterior`.

### The exact interface limitation

Two hypotheses remain, and both are honest.

1. **The flight state carries a witnessing segment.**  A `V.FlightState` is not a bare phase point:
   it carries a `PhysicalEdgeSegment`, a genuine short-time solution of the edge system through its
   initial point.  For a regular *interior* state such a segment always exists
   (`exists_physicalEdgeSegment_from_interior`), so `FlightState.ofInterior` turns a limiting graph
   state `z = (q, r)` strictly inside an edge at a regular energy into a flight state; a limiting
   state exactly *at* a vertex is outside the interface.
2. **`hgerm : a.arrivalGerm = x₀.germ`** — the first graph flight must leave the edge through the
   same germ the microscopic particle is prepared towards.  This is *not* an extra assumption of the
   bridge: it is the clause `g.germ 0 = x₀.germ` already built into `IsThinGraphLimit`, and hence
   into `thin_junction_hamiltonian_limit`, transported to the flow side.  It is a genuine condition
   only because a graph flight in a nonzero potential may turn around and leave through the
   *opposite* end of its edge; for the zero potential — the setting of all explicit models here —
   the outgoing germ is determined by the sign of `r` and the condition holds automatically.

Nothing else is assumed.  In particular no new existence theory is introduced: the flow
`FlightState.trajectory` is the repository's own, and the bridge only *reads* it.

## An explicit energy-dependent deterministic junction

The three-channel model of `MicroscopicPotential.lean` realizes one routing law.  The gated model
of `GatePotential.lean` realizes **two**, with the *same* microscopic Hamiltonian family, on two
disjoint energy windows.

### The gate

The paper's gate `G_ε = gateBump ε`, with `g₀ = gateHeight = 7/10`, is inserted across the through
channel at the branching vertex, supported in `|u| ≤ 2ε`; the network `N^g = gateNetwork` is
`N⋆` with this potential and `θ_ε = 32ε`:

```
gateBump ε u = (h/4)·((1 - m)·wallPot ε (u + 2ε) + m·wallPot ε (2ε - u)),   m = plateau (-ε) ε u,
gatePot ε    = capPot ε + gateBump ε,
gatePot2 ε (u,w) = (1-M)·(wellPot ε w + gatePot ε u) + M·(wellPot ε u + armPot ε w),
                                                       M = plateau (3ε) (6ε) w.
```

Three design points make it work.

* **Each flank is exactly a scaled `wallPot`.**  For `u ≤ -ε` the mixing weight `m` is exactly `0`,
  so `gateBump ε u = (h/4)·wallPot ε (u + 2ε)`, and for `u ≥ ε` it is exactly the mirror image.
  The reflection machinery `Reflection.reflect_of_barrier_sharp` — which needs a *positive derivative
  lower bound* on the barrier flank, available for `wallPot` and **not** for `plateau` — therefore
  applies verbatim on each side.  A naive product bump would have had a `plateau` flank and would
  have been unusable.
* **The blocking and transmission heights are close.**  On the core `|u| ≤ ε` both wall arguments
  lie in `[ε, 3ε]`, so both `wallPot` values are `≥ 4` and the convex combination is `≥ g₀`
  (`gateBump_ge`).  Globally the value is `≤ (g₀/4)·barrierProfile 3 = g₀·e^{2/3} < 1.365`
  (`gateBump_le_sharp`, `gateBump_lt`, from `e² < 7.41 < 1.95³`).  The **gate height**
  `E_c = max G_ε` is `gateCritical`: it is attained and independent of `ε`, because
  `G_ε(u) = G_1(u/ε)` (`gateBump_scale`, `gateCritical_isGreatest`), and `G_ε(0) = g₀e^{1/2}`
  gives `1.15 < E_c < 1.365` (`gateBump_zero`, `gateCritical_gt`, `gateCritical_lt`).  Hence
  `max K₋ < g₀ < E_c < min K₊`, which leaves room for two energy windows on either side.
* **Outside `|u| ≥ 2ε` the gate and its derivative vanish identically** (`gateBump_of_le_neg`,
  `deriv_gateBump_of_two_le`), so edge flights, the outer caps and the whole third arm are
  completely unaffected: `gatePot2 ε = microPot ε` for `w ≥ 6ε` (`gatePot2_eq_microPot_of_arm`).

### The two regimes

| window | energies | speeds `c = √(2E)` | gate | routing law |
|---|---|---|---|---|
| `K₋ = [1/2, 3/5]` | `< g₀ = gateHeight = 7/10` | `[1, √1.2]` | reflects | `F₋ = RoutingLaw.reflection Γ⋆` |
| `K₊ = [3/2, 2]` | `> 1.365 > E_c = gateCritical` | `[√3, 2]` | is crossed | `F₊ = F⋆` |

Both regimes are consequences of energy conservation for the *same* potential:

* below `g₀` the longitudinal energy cannot reach the core, so the particle is turned around
  *exactly*, at the junction boundary it came from, within `t_* < 12ε + 2ε(0.36 + 6.57) < 26ε`
  (Lemma IX.8 with `Ψ = (g₀/4)B`, `k = g₀e⁻³`, `d = 6ε`: `gateTime_lt`,
  `GateSolution.reflect_gate_left`, `reflect_gate_right`);
* above `3/2 > 1.365` the energy exceeds the gate by more than `1/8`, so the speed stays above
  `1/2` inside the junction, and the particle crosses in time `≤ 32ε` and emerges on the other side
  with *exactly* its incoming speed (`GateSolution.cross_gate_right`, `cross_gate_left`).

The outer caps and the third-arm barrier have height `4`, above every energy of `[1/2, 2]`, so
those three passages are identical in the two regimes and are proved once for an arbitrary routing
law fixing the germ.

### The theorem

```lean
theorem explicit_energy_dependent_junction :
    (∀ ε, gateNetwork.pot ε = gatePot2 ε) ∧
    (∀ ε, 0 < ε → gateNetwork.offset ε = 8 * ε ∧ gateNetwork.dwell ε = 32 * ε) ∧
    IsCompact windowLow ∧ IsCompact windowHigh ∧
    (zeroPotential starGraph).IsWindowAbove windowLow ∧
    (zeroPotential starGraph).IsWindowAbove windowHigh ∧
    Disjoint windowLow windowHigh ∧
    gateHeight = 7 / 10 ∧
    (∀ ε, 0 < ε → ∀ u, |u| ≤ ε → gateHeight ≤ gateBump ε u) ∧
    (∀ ε, 0 < ε → IsGreatest (Set.range (gateBump ε)) gateCritical) ∧
    (115 / 100 : ℝ) < gateCritical ∧ gateCritical < 1365 / 1000 ∧
    sSup windowLow < gateHeight ∧ gateHeight < gateCritical ∧ gateCritical < sInf windowHigh ∧
    gateNetwork.RealizesOnEnergyWindow (zeroPotential starGraph) windowLow gateRoutingLow
      (1 / 100) ∧
    gateNetwork.RealizesOnEnergyWindow (zeroPotential starGraph) windowHigh gateRoutingHigh
      (1 / 100) ∧
    gateRoutingLow ≠ gateRoutingHigh ∧
    gateRoutingLow.routeGerm channel₁ = channel₁ ∧
    gateRoutingHigh.routeGerm channel₁ = channel₂
```

with `windowLow = Icc (1/2) (3/5)`, `windowHigh = Icc (3/2) 2`; the hypotheses hold for every
`ε ∈ (0, 1/100)`, the paper's `ε₀`.

`RealizesOnEnergyWindow N V K F ε₀` is `SatisfiesEdgeReduction V K ε₀ ∧
JunctionScatteringConvergesTo V K F ε₀` — exactly (E) and (J), with the window
a parameter of the predicate rather than of the network.  That is the whole point: the *same* `N`
realizes different laws on different windows.  `gate_realization_low` (speed `1`, energy
`1/2 ∈ K₋`) and `gate_realization_high` (speed `2`, energy `2 ∈ K₊`) then instantiate
`thin_junction_hamiltonian_limit` on each window and exhibit the same microscopic family converging
to two different graph flows; `gate_itinerary_differs` records that the limiting itineraries
separate at the very first junction.

### Channel selection is independent of the transverse data

`GateJunction.lean` produces *a* passage through the routed germ.  `GateDeterminism.lean` proves the
stronger `HasDeterministicChannelReduction`: within the junction window the particle can reach **no
other** junction boundary.  Since the incoming trajectory in these statements is arbitrary — only
its projected graph state is constrained — the outgoing channel is shown to be independent of the
unresolved transverse data, which is the microscopic meaning of the determinism of the two limiting
laws.  Three ingredients, all consequences of the gated flow:

* `GateSolution.same_sign` — **below the gate the particle never changes side.**  Its longitudinal
  energy is below the gate height, so `ε < |u(t)|` at *all* times (`abs_gt_of_low`), and the
  intermediate value theorem forbids a sign change.  This is what excludes the opposite through
  channel at low energy.
* `GateSolution.mom_le_of_high` / `mom_ge_of_high` — **above the gate the longitudinal momentum
  keeps its sign** inside the closed edge, with modulus `≥ 2/5` (the crude bound `G_ε ≤ 2g₀`
  suffices here).  Hence the longitudinal coordinate
  is strictly monotone across the whole junction window and the particle cannot return to the
  boundary it entered through.
* the travel bound `|Δq| ≤ 2 · dwell = 64ε`, which excludes the far boundary of any edge
  (`1 - 16ε > 64ε` for `ε < 1/100`, as in the paper), together with the geometric separation of
  the three channels (`gateNetwork_channelsSeparated`).

Feeding this into `ChannelKernel.channelKernel_of_deterministic` gives the coarse-grained vertex
kernels: `δ_{η}` on `K₋` and `δ_{F⋆(η)}` on `K₊`, for **every** probability measure on the
unresolved data, and `gate_channelKernel_differs` records that the two differ already on `η₁`.

### Between the windows nothing is claimed

`max K₋ = 3/5 < g₀ = 7/10 < E_c < 1.365 < 3/2 = min K₊`.  **No claim whatever is made for energies
between the windows**, where the junction passes from reflection to transmission, and no
uniformity across them is asserted.

| step | declarations | file |
|---|---|---|
| the gate, its two exact `wallPot` flanks, the bounds `g₀ ≤ G_ε` on the core and `G_ε ≤ g₀e^{2/3} < 1.365`, the gate height `E_c` with `1.15 < E_c < 1.365`, smoothness, exact separability | `gateHeight`, `mixG`, `gateBump`, `gateBump_ge`, `gateBump_le_sharp`, `gateBump_lt`, `gateBump_zero`, `gateBump_scale`, `gateCritical`, `gateCritical_isGreatest`, `gateCritical_gt`, `gateCritical_lt`, `gatePot`, `gatePot2`, `gatePot2_of_through`, `gatePot2_eq_microPot_of_arm`, `gateForce_of_through` | `GatePotential.lean` |
| the one-dimensional gated dynamics: free motion, cap reflections (`< 23ε`), **gate reflection** (`< 26ε`) and **gate crossing** (`≤ 32ε`) | `GateSolution`, `free_right/left_of_endpoints`, `reflect_cap_right/left`, `gateTime`, `gateTime_lt`, `reflect_gate_left/right`, `cross_gate_right/left` | `GateDynamics.lean` |
| the gated thin network and the two windows | `gateNetwork`, `windowLow`, `windowHigh`, `windowLow_disjoint_windowHigh`, `windowLow_lt_gateHeight`, `windowHigh_ge` | `GateNetwork.lean` |
| confinement and the exact one-dimensional reduction | `gate_hamiltonian_le`, `gate_not_mid`, `gate_through_confined`, `gate_arm_confined`, `GateThrough`, `GateArm` | `GateConfinement.lean` |
| the edge-reduction hypothesis on every window `K ⊆ [1/2, 2]` | `gate_mk_edgeFlight`, `gate_free_through`, `gateNetwork_satisfiesEdgeReduction` | `GateEdge.lean` |
| the junction-scattering hypothesis in both regimes | `gate_junction_through_inner_low`, `gate_junction_through_inner_high`, `gate_junction_through_outer`, `gate_junction_arm_inner/outer`, `gateNetwork_junctionScattering_low/high` | `GateJunction.lean` |
| the realization predicate, the theorem and the two limit corollaries | `RealizesOnEnergyWindow`, `explicit_energy_dependent_junction`, `gate_thin_junction_realization`, `gate_realization_low/high`, `gate_itinerary_differs` | `GateLimit.lean` |
| **channel selection is independent of the transverse data** in both regimes, and the coarse-grained kernels | `GateSolution.same_sign`, `mom_le_of_high`, `mom_ge_of_high`, `gateNetwork_channelsSeparated`, `gate_through_exit_unique_low/high/outer`, `gate_arm_exit_unique`, `gateNetwork_hasDeterministicChannelReduction_low/high`, `gate_channelKernel_low/high/differs` | `GateDeterminism.lean` |

### What the energy-dependent model does **not** cover

1. **Two windows, not a continuum.**  The theorem exhibits two disjoint windows with different
   laws.  It does *not* produce an energy-parameterized family of laws, and it says nothing at the
   threshold.
2. **The branching structure is the same as the ungated model**, and so is the third arm: the arm
   is closed at every energy of `[1/2, 2]`.  The energy dependence lives entirely in the through
   channel.
3. **The window is fixed at `K ⊆ [1/2, 2]`** for the same reason as before: the barrier height `4`
   of `barrierProfile` and the hard-coded speed range `c ∈ [1,2]` of `CapMotion` / `ArmMotion`.
4. **The gate is a scalar barrier.**  Magnetic or velocity-dependent selectivity is not treated.

## Deterministic and stochastic coarse-graining

A full microscopic incoming state of a junction is a triple `(η, r, ξ)`: the projected graph state
together with **unresolved data** `ξ` — the transverse displacement and momentum inside the tube,
the exact arrival time, the past of the trajectory.  The microscopic scattering process is
deterministic and assigns to it an outgoing channel `C_v(η, r, ξ)`.  An observer who measures only
the graph state must average over `ξ`; given a probability measure `μ` on the unresolved data the
observed vertex law is the **channel kernel**

```
P_v(ζ ∣ η, r) = μ {ξ : C_v(η, r, ξ) = ζ}.
```

`ChannelKernel.lean` makes the dichotomy precise.

* `channelKernel_of_ae_eq`, `channelKernel_dirac` — **one outgoing basin gives a deterministic
  graph law.**  If `C_v(η, r, ·) = F_v(η, r)` for `μ`-almost every `ξ`, then
  `P_v(· ∣ η, r) = δ_{F_v(η,r)}`.  No measurability of `C_v` is needed: subadditivity of `μ`
  suffices.
* `channelKernel_ne_dirac` — **several outgoing basins give a genuinely stochastic law.**  If two
  distinct germs are each attained on a set of positive measure, no Dirac mass can be the kernel.
* `ExitGerms`, `channel`, `channel_eq_routeGerm`, `channelKernel_of_deterministic` — the link to
  the microscopic hypothesis.  `HasDeterministicChannelReduction F ε₀` says exactly that the exit
  set of every well-prepared incoming state is the **singleton** `{F_v(η)}`
  (`exitGerms_eq_singleton`); so the microscopic channel map is constant on the whole preparation
  class and the induced kernel is Dirac for *every* probability measure on the unresolved data.
  `Incoming` packages an unresolved incoming state (scale, horizon, trajectory, arrival time) and
  `Incoming.channel_eq` computes its channel.

### What the coarse-graining layer does **not** cover

Only the deterministic implication is developed.  Building the general stochastic vertex law into a
**Markov process on a metric graph** — transition kernels along the flow, a semigroup, invariant
measures — is deliberately out of scope, and no such theory is claimed.  The second implication
(`channelKernel_ne_dirac`) is stated and proved as a converse *criterion*, not as the construction
of a stochastic dynamics.

## What remains outside the whole development

A consolidated list, gathering the per-section statements above.

1. **Bent thin tubes.**  All microscopic networks here are unions of *straight* tubes (`base`,
   `tang`, `nrm` constant along an edge).  A particle physically turning a corner inside an `O(ε)`
   cell is the thin-tube adiabatic / geometric-potential limit; it has no exact solution and is not
   formalized.  The precise unproved statement is spelled out in
   [what the universal model does not cover](#what-the-universal-model-does-not-cover), item 3.  It
   is nowhere assumed.
2. **Speed-dependent or non-involutive vertex laws.**  The realized class is `RoutingLaw Γ`:
   speed-independent involutive germ maps with departure momentum `-σ(F_v η)·|p|`.  The paper's
   full `ScatteringLaw` — an arbitrary Borel energy-preserving vertex bijection, whose fixed-speed
   endpoint permutation may vary with the speed — is *not* realized by any model here.  The
   energy-dependent junction is a step in that direction but produces two constant laws on two
   windows, not a genuine speed-dependent law.
3. **Arbitrary smooth edge potentials in the explicit models.**  The general theorems
   (`microscopic_realization`, `thin_junction_hamiltonian_limit`, `thin_junction_global_flow_limit`)
   allow arbitrary `C²` edge potentials.  Every *explicit* microscopic model realizes the **zero**
   graph potential.
4. **Arbitrary compact energy windows in the explicit models.**  The barrier height `4` of
   `barrierProfile` / `wellProfile`, and the hard-coded `c ∈ [1, 2]` of `CapSolution` /
   `ArmSolution` / `GateSolution`, fix the explicit windows inside `[1/2, 2]`.  A
   height-parameterized barrier would remove this; it is routine and not done.
5. **Uniqueness of the microscopic trajectory** is proved for thin networks
   (`MicroTrajectory.eq_of_initial`) and used to define the flow `Φ^ε_t`; the branching and
   universal models do not use it.
6. **A Markov process on a metric graph.**  `ChannelKernel.lean` proves the coarse-graining
   dichotomy for a single junction; no transition semigroup, invariant measure or stochastic flow is
   constructed.
7. **The transition region of the gated model.**  Nothing is claimed for energies between the
   windows, `3/5 < E < 3/2`, which contain `g₀ = 7/10` and the gate height `E_c`.
8. **Limiting graph states exactly at a vertex.**  The flow interface starts from a regular
   *interior* state (`FlightState.ofInterior`).
9. **Magnetic or velocity-dependent microscopic Hamiltonians.**  Every model here is
   `H_ε = ½|p|² + W_ε(x)` with a scalar `W_ε`.

## Module dependency order

`Routing` → `IntervalEstimates` → `HybridChain` → `FlightEstimates` → `RegularEnergy`,
`EdgeApproximation` → `Microscopic` → `StepCore` → `Step` → `Realization`;
`ScaledJunction` (independent of the chain layer); `RoutingScattering`, `Examples`.

Explicit model: `SmoothPlateau` → `BarrierProfile` → `MicroscopicPotential`;
`GlobalFlow`, `Newton1D` → `MicroscopicTrajectory`; `Newton1D` → `Reflection` → `CapDynamics`;
`FreeGraphTrajectory` → `BranchingGraph` → `BranchingModel`;
`CapDynamics`, `BranchingModel` → `MicroscopicChain`;
`CapDynamics`, `MicroscopicTrajectory` → `ArmDynamics` → `ArmChain`;
`MicroscopicChain`, `ArmChain` → `BranchingRealization`.

Universal model: `CapDynamics` → `UniversalCorridor` → `UniversalNetwork`;
`FreeGraphTrajectory` → `UniversalGraphTrajectory` → `UniversalLayout` → `UniversalFolds`;
`UniversalNetwork`, `MicroscopicTrajectory` → `UniversalTrajectory`;
`UniversalTrajectory`, `UniversalFolds`, `MicroscopicChain` → `UniversalRun` →
`UniversalRealization`.

Thin-junction limit: `Microscopic`, `IntervalEstimates`, `EdgeDynamics` → `ThinNetwork` →
`MicroscopicCompleteness` (with `GlobalFlow`, `SmoothPlateau`) → `ThinHypotheses` →
`ThinFlightBounds` → `ThinRun` → `ThinLimit` → `ThinGlobalFlow` → `ThinLimitInitial`;
`ThinHypotheses` → `ForcedInvolution`;
`ThinLimit`, `MicroscopicChain`, `ArmDynamics` → `StarNetwork` → `StarConfinement` → `StarEdge` →
`StarJunction` → `StarDeterminism` → `StarLimit`.

Coarse-graining: `ThinHypotheses` → `ChannelKernel`.

Energy-dependent junction: `ArmDynamics` → `GatePotential` → `GateDynamics`;
`GateDynamics`, `StarJunction` → `GateNetwork` → `GateConfinement` → `GateEdge` → `GateJunction`;
`GateJunction`, `StarLimit` → `GateLimit`;
`GateLimit`, `StarDeterminism`, `ChannelKernel` → `GateDeterminism`.

Global graph flow: `RoutingScattering`, `HybridChain`, `UnifiedTrajectory` → `GraphFlow`;
`GraphFlow`, `ThinLimit` → `ThinGlobalFlow`.
