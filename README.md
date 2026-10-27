# Liouville-preserving Hamiltonian scattering on finite metric graphs in Lean 4

A formalization, in Lean 4 with Mathlib, of

> P. Hierhager, *Liouville-Preserving Hamiltonian Scattering on Finite Compact Metric Graphs*,
> submitted to the Journal of Mathematical Physics.

A mechanical Hamiltonian `H_e(q, p) = p²/2 + V_e(q)` on each edge of a finite compact metric graph,
together with an energy-preserving Borel scattering law at each vertex, generates a global
bimeasurable flow on the regular quotient phase space that preserves energy and the quotient
Liouville measure (Theorem VI.5 of the paper). The development proves this theorem, the
cycle structure of a shell-regular energy surface (Sec. VIII), the classification of
flux-preserving Markov vertex laws (Sec. X) and the thin-network results of Sec. IX.

## Building

```bash
lake exe cache get    # downloads the prebuilt Mathlib
lake build
```

Lean `v4.31.0` (`lean-toolchain`) and Mathlib `v4.31.0` (pinned in `lake-manifest.json`).

## Checking

* `lake build` finishes with no error and no `declaration uses 'sorry'` warning, and
  `grep -rn "sorry\|admit" HamiltonianMetricGraphs` finds no proof term.
* `lake env lean scripts/Axioms.lean` prints the axioms of the main theorems; each must be
  exactly `[propext, Classical.choice, Quot.sound]`.

## Where things are

The [supplementary material](paper/paper_jmp_supplement.pdf) is the authoritative
statement-to-declaration map for the revised article. Every numbered result is formalized,
including the trajectory lemmas on open intervals. Tables S1 and S2 pair these results
with Lean declarations; the remaining sections record the formal encodings, proof routes and
scope qualifications, including the combinatorial interpretation of the ribbon-graph genus.
The public export includes this PDF. [PROOF_MAP.md](PROOF_MAP.md) separates the current
correspondence from the historical development log; its archived unfinished rows are superseded.
The thin-network results live under `HamiltonianMetricGraphs/Realization/`, with their own
`README.md`.

## License

Apache 2.0; see `LICENSE`.
