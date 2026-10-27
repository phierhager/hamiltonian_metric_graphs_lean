/-
Copyright (c) 2026 Philip Hierhager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Hierhager
-/

import HamiltonianMetricGraphs.QuotientPhaseSpace
import HamiltonianMetricGraphs.StandardBorel

/-!
# Standard Borel structure for the scattering sections

With `NonzeroPrequotientPhase` standard Borel (see `StandardBorel`), every Borel subsection is again
standard Borel.  In particular the outgoing representative section — the Borel transversal of the
scattering quotient — is standard Borel, so `outgoingRepresentativeMap` is a measurable bijection
*out of a standard Borel space*.  That is the exact hypothesis of Lusin--Souslin
(`Measurable.measurableEmbedding`) needed to upgrade the outgoing chart of Lemma IV.4 to a
`MeasurableEquiv`.
-/

namespace HamiltonianMetricGraphs

namespace MechanicalPotential

variable {Γ : FiniteMetricGraph} (V : MechanicalPotential Γ)
variable (S : BorelEnergyPreservingScattering V)

/-- The outgoing representative section is a Borel subset of the (standard Borel)
`NonzeroPrequotientPhase`, hence itself standard Borel. -/
noncomputable instance : StandardBorelSpace (OutgoingRepresentativeSpace (V := V) S) :=
  (measurableSet_outgoingRepresentativeSpace (V := V) S).standardBorel

end MechanicalPotential

end HamiltonianMetricGraphs
