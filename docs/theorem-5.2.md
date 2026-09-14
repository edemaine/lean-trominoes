# Theorem 5.2: periodic-subset tiling with one tromino

[Theorem52.proved](../LeanTrominoes/Theorem52Proof.lean) proves the
[complete statement](../LeanTrominoes/Theorem52.lean): for either tromino,
periodic-subset tiling is co-r.e.-complete in the plane and PSPACE-complete
in a strip under the flat encoding. `Theorem52.stripProved` exposes the strip
assertion. All compiler witnesses are constructed.

## Plane proof

[PeriodicWangPlanarThreeDMReduction](../LeanTrominoes/PeriodicWangPlanarThreeDMReduction.lean)
combines the Wang source reduction, periodic planar geometry, and tromino
gadgets to prove plane completeness. The co-r.e. upper bound is provided by
[ComputableSearch](../LeanTrominoes/ComputableSearch.lean): finite obstructions
can be enumerated, and compactness supplies a tiling when none exists.

## Strip proof

The hardness construction starts from an arbitrary encoded language with a
finite-alphabet polynomial-space decider. The
[periodic CNF reduction](../LeanTrominoes/PeriodicCNFPolySpaceHardness.lean)
provides the source formulas. The geometric compiler emits the periodic
strip motif with a polynomial-time machine, including the actual coordinates
and route data.

The final proof instantiates
[Theorem52DirectSparseClosure](../LeanTrominoes/Theorem52DirectSparseClosure.lean)
with two concrete appenders:

| Component | Entry point |
| --- | --- |
| Vertex records | [PeriodicCNFStripDirectSourceFinalVertexRecordCompiler](../LeanTrominoes/PeriodicCNFStripDirectSourceFinalVertexRecordCompiler.lean) |
| Route raster requests and records | [PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler](../LeanTrominoes/PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler.lean) |
| Combined witnesses | `PeriodicCNFStripReduction.directSparseSplitRecordAppenders` in [Theorem52Proof](../LeanTrominoes/Theorem52Proof.lean) |
| Polynomial-space membership | [PartrecFlatStripDeciderSpace](../LeanTrominoes/PartrecFlatStripDeciderSpace.lean) |

The vertex appender joins retained-element and triple records in canonical
order and applies the verified affine expansion. The route appender assembles
signed coordinates, colors, and normalization data in exact edge order.
Both retain the source workspace and have finite-alphabet machine certificates.

For route semantics, start with
[SourceOccurrence](../LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrences.lean)
and its [metadata witness](../LeanTrominoes/PeriodicCNFFormulaShapeFigureNineSourceOccurrenceMetadata.lean).
These preserve the original parent and literal indices through reordered
metadata. The [presented direction words](../LeanTrominoes/PeriodicCNFStripDirectSourceFinalPresentedDirectionWords.lean)
and [endpoint directions](../LeanTrominoes/PeriodicCNFStripDirectSourceFinalEndpointDirections.lean)
connect the emitted records to the actual routed drawing, including reversed
occurrence routes and completed variable-fan tails.

## Validation

The completion build on September 12, 2026 passed all 10,469 jobs, followed
by a public-import audit. The audited full theorem and strip projection
contained no `sorryAx`; they retained the standard axioms and 5,877 inherited
native-evaluation certificates. This is a historical completion audit, not a
claim that every dependency uses kernel reduction alone.

To check the proof and inspect its current dependencies:

```sh
lake build +LeanTrominoes.Theorem52Proof:olean
```

In a Lean file importing that module, use
`#print axioms LeanTrominoes.Theorem52.proved`.
See [README](../README.md) for current paper coverage and build conventions.
