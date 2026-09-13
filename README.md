# lean-trominoes

Lean formalization of
[*Undecidability of Tiling with a Tromino*](https://arxiv.org/abs/2509.07906)
by the MIT--ULB CompGeom Group, Zachary Abel, Hugo Akitaya, Lily Chung,
Erik D. Demaine, Jenny Diomidova, Della Hendrickson, Stefan Langerman, and
Jayson Lynch. The working paper is included as
[PDF](trominoes.pdf) and [source](trominoes.texlish).

The eventual goal is every theorem and lemma in the paper. Theorem 5.2 is
proved: for either single tromino, periodic-subset tiling is co-r.e.-complete
in the plane and PSPACE-complete in a strip.

The plane assertion of Theorem 5.5 is also proved: tiling by a fixed connected
15-omino and an input disconnected polyomino is co-r.e.-complete, allowing
arbitrary rotations and reflections. The strip assertion remains open.
[THEOREM55_FRONTIER.md](THEOREM55_FRONTIER.md) records the construction and validation.

Tiling the height-2 slab with a fixed connected 15-voxel polycube and an
input connected polycube is also proved co-r.e.-complete, allowing all cube
rotations and reflections. Full 3D has a co-r.e. upper bound and a fixed-tile
non-tiling obstruction; its hardness construction remains open. [POLYCUBE_FRONTIER.md](POLYCUBE_FRONTIER.md)
records the established results and remaining obligations.

## Main statements and proofs

Start with [Theorem52.lean](LeanTrominoes/Theorem52.lean) to read the complete
target without importing its construction. In namespace
`LeanTrominoes.Theorem52`, the three propositions are:

| Declaration | Statement | Status |
| --- | --- | --- |
| `planeStatement` | For each tromino, periodic-subset tiling in 2D is co-r.e.-complete. | Proved |
| `stripStatement` | For each tromino, periodic-strip tiling under the flat encoding is PSPACE-complete. | Proved |
| `statement` | `planeStatement ∧ stripStatement`, the complete Theorem 5.2. | Proved |

These are **definitions of propositions**, not proofs. The main proof
declarations are below; names are relative to `LeanTrominoes` unless marked
otherwise.

| Result | Proof declaration | Module |
| --- | --- | --- |
| Theorem 5.2, complete result | `Theorem52.proved` | [Theorem52Proof](LeanTrominoes/Theorem52Proof.lean) |
| Theorem 5.2, strip PSPACE completeness | `Theorem52.stripProved` | [Theorem52Proof](LeanTrominoes/Theorem52Proof.lean) |
| Theorem 5.2, complete plane result | `PeriodicWangPlanarThreeDMReduction.theorem52_planeStatement` | [PeriodicWangPlanarThreeDMReduction](LeanTrominoes/PeriodicWangPlanarThreeDMReduction.lean) |
| Theorem 5.5, plane co-r.e. completeness | `Theorem55.planeProved` | [Theorem55Proof](LeanTrominoes/Theorem55Proof.lean) |
| Two connected polycubes, height-2 slab co-r.e. completeness | `TwoConnectedPolycubes.slabTwoProved` | [TwoConnectedPolycubesSlabProof](LeanTrominoes/TwoConnectedPolycubesSlabProof.lean) |
| Plane co-r.e. membership | `periodicTrominoTiling_coRE` | [ComputableSearch](LeanTrominoes/ComputableSearch.lean) |
| Theorem 5.2, strip PSPACE membership | `PeriodicStrip.RawWindowState.FlatStripDeciderPartrec.flatPeriodicStripTrominoTiling_inPSPACE` | [PartrecFlatStripDeciderSpace](LeanTrominoes/PartrecFlatStripDeciderSpace.lean) |
| Theorem 3.2, local 1D periodic CNF SAT PSPACE hardness | `PeriodicCNF.PolySpaceHardness.localPeriodicCNF1DSAT_PSPACEHard` | [PeriodicCNFPolySpaceHardness](LeanTrominoes/PeriodicCNFPolySpaceHardness.lean) |
| Theorem 3.1, Wang tiling co-r.e.-completeness | `LeanWang.domino_problem_coRE_complete` | Dependency module `LeanWang.Final` |

`import LeanTrominoes` exposes these main results. Import
`LeanTrominoes.Theorem52` when only the target statements are needed, or an
individual construction module for its implementation API.

The full proof instantiates the [appender closure](LeanTrominoes/Theorem52DirectSparseClosure.lean)
with the concrete [vertex](LeanTrominoes/PeriodicCNFStripDirectSourceFinalVertexRecordCompiler.lean)
and [route](LeanTrominoes/PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler.lean)
compilers. No compiler witness remains assumed.

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

PSPACE hardness uses polynomial-time many-one reductions from every encoded
polynomial-space language. Both deciders and reduction machines require finite
alphabets on every stack. The [finite-alphabet certificate](LeanTrominoes/FiniteAlphabetPolyTime.lean)
strengthens Mathlib’s machine interface; a [verified alphabet restriction](LeanTrominoes/TM2FiniteAlphabetRestriction.lean)
converts existing certificates without changing their encodings or running time.
Finite control ensures that each program can write only finitely many symbols.

## Current work and paper coverage

[PROOF_FRONTIER.md](PROOF_FRONTIER.md) records the exact outstanding witness
types, the next semantic theorem, and the constructors that consume them.
It is the current work list; intermediate lemmas do not by themselves close
a paper theorem.

| Paper results | Current coverage |
| --- | --- |
| Theorem 3.1 | Imported Wang tiling theorem |
| Theorem 3.2 | Local 1D CNF SAT hardness proved; full theorem open |
| Theorem 5.2 | Fully proved |
| Theorem 5.5 | Plane co-r.e. completeness proved; strip assertion open |
| Two connected polycubes | Height-2 slab proved; full 3D and taller slabs open |
| Theorems 2.1–2.2, Lemma 2.3, Theorems 3.3–3.8 | Construction infrastructure exists; full paper statements remain open |
| Section 4, Lemma 5.1 in its full generality, and other results 5.3–5.15 | Open |

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
