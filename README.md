# lean-trominoes

Lean formalization of
[*Undecidability of Tiling with a Tromino*](https://arxiv.org/abs/2509.07906)
by the MIT--ULB CompGeom Group, Zachary Abel, Hugo Akitaya, Lily Chung,
Erik D. Demaine, Jenny Diomidova, Della Hendrickson, Stefan Langerman, and
Jayson Lynch. The working paper is included as
[PDF](trominoes.pdf) and [source](trominoes.texlish).

The eventual goal is every theorem and lemma in the paper. The current focus
is Theorem 5.2: tiling a periodic subset by either single tromino. Its plane
co-r.e.-completeness result and strip PSPACE membership are proved; strip
PSPACE hardness remains unfinished.

## Main statements and proofs

Start with [Theorem52.lean](LeanTrominoes/Theorem52.lean) to read the complete
target without importing its construction. In namespace
`LeanTrominoes.Theorem52`, the three propositions are:

| Declaration | Statement | Status |
| --- | --- | --- |
| `planeStatement` | For each tromino, periodic-subset tiling in 2D is co-r.e.-complete. | Proved |
| `stripStatement` | For each tromino, periodic-strip tiling under the flat encoding is PSPACE-complete. | Membership proved; hardness open |
| `statement` | `planeStatement ∧ stripStatement`, the complete Theorem 5.2. | Open |

These are **definitions of propositions**, not proofs. The main proof
declarations are below; names are relative to `LeanTrominoes` unless marked
otherwise.

| Result | Proof declaration | Module |
| --- | --- | --- |
| Theorem 5.2, complete plane result | `PeriodicWangPlanarThreeDMReduction.theorem52_planeStatement` | [PeriodicWangPlanarThreeDMReduction](LeanTrominoes/PeriodicWangPlanarThreeDMReduction.lean) |
| Plane co-r.e. membership | `periodicTrominoTiling_coRE` | [ComputableSearch](LeanTrominoes/ComputableSearch.lean) |
| Theorem 5.2, strip PSPACE membership | `PeriodicStrip.RawWindowState.FlatStripDeciderPartrec.flatPeriodicStripTrominoTiling_inPSPACE` | [PartrecFlatStripDeciderSpace](LeanTrominoes/PartrecFlatStripDeciderSpace.lean) |
| Theorem 3.2, local 1D periodic CNF SAT PSPACE hardness | `PeriodicCNF.PolySpaceHardness.localPeriodicCNF1DSAT_PSPACEHard` | [PeriodicCNFPolySpaceHardness](LeanTrominoes/PeriodicCNFPolySpaceHardness.lean) |
| Theorem 3.1, Wang tiling co-r.e.-completeness | `LeanWang.domino_problem_coRE_complete` | Dependency module `LeanWang.Final` |

`import LeanTrominoes` exposes these main results. Import
`LeanTrominoes.Theorem52` when only the target statements are needed, or an
individual construction module for its implementation API.

The [final source-emitter closure](LeanTrominoes/Theorem52DirectSparseSourceEmitterClosure.lean)
and [appender closure](LeanTrominoes/Theorem52DirectSparseClosure.lean) prove
Theorem 5.2 **assuming** the remaining compiler witnesses. They do not yet
give an unconditional proof of `Theorem52.statement`.
The [route-record appender](LeanTrominoes/PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler.lean)
is constructed; the vertex-record appender remains.

## Definitions

| Objects | Module |
| --- | --- |
| Integer-grid cells, polyominoes, square-grid symmetries, I and L trominoes | [Basic](LeanTrominoes/Basic.lean) |
| Placements and exact tilings | [Tiling](LeanTrominoes/Tiling.lean) |
| Equivalent tilings by geometric three-cell footprints | [FootprintTiling](LeanTrominoes/FootprintTiling.lean) |
| `PeriodicRegion`, `PeriodicStrip`, and their tilability predicates | [Periodic](LeanTrominoes/Periodic.lean) |
| Target strip encoding and decoder | [PeriodicStripFlatEncoding](LeanTrominoes/PeriodicStripFlatEncoding.lean) |
| Finite-alphabet polynomial-space deciders, polynomial-time reductions, PSPACE completeness | [Complexity](LeanTrominoes/Complexity.lean) |
| Periodic CNF formulas and satisfiability | [PeriodicCNF](LeanTrominoes/PeriodicCNF.lean) |
| Finite presentations of periodic graphs | [PeriodicGraph](LeanTrominoes/PeriodicGraph.lean) |
| Scaled integer-grid periodic drawings | [PeriodicGridDrawing](LeanTrominoes/PeriodicGridDrawing.lean) |

A plane input has a finite motif and two full-rank period vectors. A strip
input has a finite motif in a bounded-height strip and one positive
horizontal period. Malformed presentations are no-instances. Complexity
claims use the explicit encodings named in their statements.

## Current work and paper coverage

[PROOF_FRONTIER.md](PROOF_FRONTIER.md) records the exact outstanding witness
types, the next semantic theorem, and the constructors that consume them.
It is the current work list; intermediate lemmas do not by themselves close
a paper theorem.

| Paper results | Current coverage |
| --- | --- |
| Theorem 3.1 | Imported Wang tiling theorem |
| Theorem 3.2 | Local 1D CNF SAT hardness proved; full theorem open |
| Theorem 5.2 | Plane result and strip membership proved; strip hardness open |
| Theorems 2.1–2.2, Lemma 2.3, Theorems 3.3–3.8 | Construction infrastructure exists; full paper statements remain open |
| Section 4, Lemma 5.1 in its full generality, and results 5.3–5.15 | Open |

The [historical progress archive](PROGRESS_ARCHIVE.md) preserves the detailed
construction checklist and development history.

## Build

```sh
lake build
```

The library's `LeanTrominoes.*` glob includes every Lean source module, even
when it is not imported by the small public root. New files therefore enter
the default build automatically. To build one module and its dependencies:

```sh
lake build +LeanTrominoes.Theorem52:olean
```

The project uses Lean 4.31.0 and depends on
[`lean-wang`](https://github.com/edemaine/lean-wang).
[lean-toolchain](lean-toolchain) pins Lean;
[lake-manifest.json](lake-manifest.json) pins the fetched dependencies.
