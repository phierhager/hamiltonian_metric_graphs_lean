# Proof map

## Current correspondence

The [supplementary material](paper/paper_jmp_supplement.pdf), Tables S1 and S2, is the
**authoritative statement-to-declaration map** for the revised article. Every numbered result
of the revised article is formalized, including the trajectory lemmas on arbitrary open intervals.
The supplement is included in the
public export. Sections S3 and S4 describe the formal encodings and proof routes, including the
combinatorial genus qualification for Proposition XI.1; coverage of numbered results does not
claim that every mathematical sentence or interpretation is formalized.

The latest changes in Sections IV–V have the following correspondence. Numbers refer to the
revised manuscript's compiled labels.

| Revised article | Lean declarations | Modules |
|---|---|---|
| Definition IV.4 (vertex section and vertex impacts) | `IsVertexImpactClass`, `vertexImpactSet`, `vertexImpactSetOn` | `ScatteredTrajectoryLocal`, `NoZenoExact`, `ScatteredTrajectoryOn` |
| Lemma IV.5 (quotient charts) | `quotient_charts` | `ChartsExact` |
| Definition IV.6 (quotient Liouville measure) | `quotientLiouville` | `LiouvilleMeasure` |
| Lemma IV.7 (momentum reversal) | `quotientMomentumReversal` | `QuotientReversal` |
| Definition V.2 (scattered trajectory) | `IsScatteredTrajectoryOn`, `IsScatteredTrajectory` | `ScatteredTrajectoryOn`, `ScatteredTrajectory` |
| Lemma V.3 (energy conservation) | `quotientHamiltonian_isScatteredTrajectoryOn`, `quotientHamiltonian_isScatteredTrajectory` | `ScatteredTrajectoryOn`, `NoZenoExact` |
| Lemma V.4 (no-Zeno estimate) | `no_zeno_on`, `no_zeno` | `ScatteredTrajectoryOn`, `NoZenoExact` |
| Lemma V.5 (uniform separation of impacts) | `impact_local_finiteness_on`, `impact_local_finiteness` | `ScatteredTrajectoryOn`, `NoZenoExact` |
| Proposition V.6 (existence and uniqueness) | `existsUnique_scatteredTrajectoryOn`, `existsUnique_scatteredTrajectory` | `ScatteredTrajectoryOn`, `ScatteredTrajectory` |
| Theorem VIII.5 (cycle structure) | `shellGermPerm`, `regularShell_decomposition`, `regularShell_measure` | `Structure`, `ShellMeasure` |
| Theorem X.4 (Markov vertex laws) | `birkhoff_vertexLaws` | `VertexLawExact` |
