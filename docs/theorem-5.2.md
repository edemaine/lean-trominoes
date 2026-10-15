# Theorem 5.2: periodic-subset tiling with one tromino

[Theorem52.proved](../LeanTrominoes/Tiling/Tromino/Theorem52Proof.lean) proves the
[complete statement](../LeanTrominoes/Tiling/Tromino/Theorem52.lean): for either tromino,
periodic-subset tiling is co-r.e.-complete in the plane and PSPACE-complete
in a strip under the flat encoding. `Theorem52.stripProved` exposes the strip
assertion. All compiler witnesses are constructed.

## Plane proof

[PeriodicWangPlanarThreeDMReduction](../LeanTrominoes/ThreeDM/PeriodicWangPlanarThreeDMReduction.lean)
combines the Wang source reduction, periodic planar geometry, and tromino
gadgets to prove plane completeness. The co-r.e. upper bound is provided by
[ComputableSearch](../LeanTrominoes/Tiling/Periodic/ComputableSearch.lean): finite obstructions
can be enumerated, and compactness supplies a tiling when none exists.

## Strip proof

The hardness construction starts from an arbitrary encoded language with a
finite-alphabet polynomial-space decider. The
[periodic CNF reduction](../LeanTrominoes/SAT/CNF/PeriodicCNFPolySpaceHardness.lean)
provides the source formulas. The geometric compiler emits the periodic
strip motif with a polynomial-time machine, including the actual coordinates
and route data.

The final proof instantiates
[Theorem52DirectSparseClosure](../LeanTrominoes/Tiling/Tromino/Strip/Theorem52DirectSparseClosure.lean)
with two concrete appenders:

| Component | Entry point |
| --- | --- |
| Vertex records | [PeriodicCNFStripDirectSourceFinalVertexRecordCompiler](../LeanTrominoes/Tiling/Tromino/Strip/Direct/Source/Final/Vertex/PeriodicCNFStripDirectSourceFinalVertexRecordCompiler.lean) |
| Route raster requests and records | [PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler](../LeanTrominoes/Tiling/Tromino/Strip/Direct/Source/Final/Route/PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler.lean) |
| Combined witnesses | `PeriodicCNFStripReduction.directSparseSplitRecordAppenders` in [Theorem52Proof](../LeanTrominoes/Tiling/Tromino/Theorem52Proof.lean) |
| Polynomial-space membership | [PartrecFlatStripDeciderSpace](../LeanTrominoes/Tiling/Tromino/Strip/PartrecFlatStripDeciderSpace.lean) |

The vertex appender joins retained-element and triple records in canonical
order and applies the verified affine expansion. The route appender assembles
signed coordinates, colors, and normalization data in exact edge order.
Both retain the source workspace and have finite-alphabet machine certificates.

For route semantics, start with
[SourceOccurrence](../LeanTrominoes/SAT/CNF/FormulaShape/Source/PeriodicCNFFormulaShapeFigureNineSourceOccurrences.lean)
and its [metadata witness](../LeanTrominoes/SAT/CNF/FormulaShape/Source/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceMetadata.lean).
These preserve the original parent and literal indices through reordered
metadata. The [presented direction words](../LeanTrominoes/Tiling/Tromino/Strip/Direct/Source/Final/Presented/PeriodicCNFStripDirectSourceFinalPresentedDirectionWords.lean)
and [endpoint directions](../LeanTrominoes/Tiling/Tromino/Strip/Direct/Source/Final/Endpoint/PeriodicCNFStripDirectSourceFinalEndpointDirections.lean)
connect the emitted records to the actual routed drawing, including reversed
occurrence routes and completed variable-fan tails.

## Validation

The full theorem and strip projection use only `propext`, `Classical.choice`,
and `Quot.sound`. All finite certificates use kernel reduction.
[Axiom regression checks](../LeanTrominoes/Verification/AxiomAudit.lean) cover the full theorem.

To check the proof and inspect its current dependencies:

```sh
lake build +LeanTrominoes.Tiling.Tromino.Theorem52Proof:olean
```

In a Lean file importing that module, use
`#print axioms LeanTrominoes.Theorem52.proved`.
See [README](../README.md) for current paper coverage and build conventions.
