# Theorem 5.5: tiling by two polyominoes

The [target statements](../LeanTrominoes/Theorem55.lean) fix a connected
15-omino P and take an explicit cell list for a disconnected polyomino Q.
Empty and connected Q inputs are rejected. Rotations and reflections are allowed.
[Theorem55.planeProved](../LeanTrominoes/Theorem55Proof.lean) proves plane
co-r.e. completeness; [Theorem55.stripProved](../LeanTrominoes/Theorem55StripProof.lean)
proves strip PSPACE completeness under the original unary encoding of the
height and cell list.

## Plane geometry and hardness

[Theorem55Construction](../LeanTrominoes/Theorem55Construction.lean) exposes
the geometric components. P is the bumpy cross refinement of the I tromino;
it cannot tile the plane alone. The keyed periodic complement Q fills the
background around the refined source region. Its two locks force neighboring
Q placements, and propagation forces a canonical quadrant.

[KeyCornerCompression](../LeanTrominoes/KeyCornerCompression.lean) reduces
corner matching for periods at least 96 and divisible by three to finite
checks at period 96. [KeyCornerFinite](../LeanTrominoes/KeyCornerFinite.lean)
uses kernel-checked certificates; [KeyCornerArithmetic](../LeanTrominoes/KeyCornerArithmetic.lean)
transfers them back to arbitrary allowed periods.

[KeyedComplementGridCompactness](../LeanTrominoes/KeyedComplementGridCompactness.lean)
recenters forced quadrants and obtains a new tiling containing the complete
canonical Q grid. Additional Q placements are excluded by a solid-square
obstruction. This need not be the grid of the original mixed tiling.
[Theorem55Geometry](../LeanTrominoes/Theorem55Geometry.lean) then proves the
exact source-tiling equivalence.

[Theorem55SourcePreparation](../LeanTrominoes/Theorem55SourcePreparation.lean)
uses a proved blank margin in the normalized source drawing and adds isolated
padding. This preserves tileability, reserves the corner neighborhoods, and
supplies a source square that makes Q disconnected.
[Theorem55SourceMask](../LeanTrominoes/Theorem55SourceMask.lean) certifies the
finite mask and its periodic carrier. The explicit compiler in
[Theorem55Compiler](../LeanTrominoes/Theorem55Compiler.lean) is certified
primitive recursive by [Theorem55CompilerComputability](../LeanTrominoes/Theorem55CompilerComputability.lean).
[Theorem55Hardness](../LeanTrominoes/Theorem55Hardness.lean) composes it with
the Wang reduction.

## Strip geometry and polynomial-time compilation

The strip complement moves only the horizontal lock cells, leaving the
bounded edges flat. Orientation constraints, lock matching, row propagation,
and compactness give a canonical Q row and recover the source I-tromino tiling.

The unary complement compiler emits the exact target encoding in polynomial
time: it enumerates the square, refines the motif and padding, filters holes
and lock cells, and appends the moved keys. Its geometry identifies the emitted
list with the keyed complement, including signed coordinates, boundary copies,
and Q's disconnectedness. The hard-source compiler obtains unary fields from
the existing machine before binary serialization. Start from
[Theorem55StripProof](../LeanTrominoes/Theorem55StripProof.lean) for the final
composition and its compiler imports.

## Upper bounds

[Theorem55UpperBound](../LeanTrominoes/Theorem55UpperBound.lean) combines
primitive-recursive finite patch search with the connectivity cut test.
Compactness proves that successful searches at every radius yield a plane tiling.

[Theorem55StripMembership](../LeanTrominoes/Theorem55StripMembership.lean)
provides the finite-alphabet polynomial-space machine for the original unary
input. A bounded-window transition relation, disconnectedness test, and
Savitch reachability/cycle search are compiled to arithmetic evaluators.
Polynomial-time preprocessing supplies their fields;
[PartrecPreparedEvaluatorSpace](../LeanTrominoes/PartrecPreparedEvaluatorSpace.lean)
and [TM2SequentialSpace](../LeanTrominoes/TM2SequentialSpace.lean) retain a
space bound polynomial in the original input length through composition.

## Validation

The strip completion build passed 9,854 jobs and the public import check.
Its audit found no `sorryAx`: 5,315 inherited native checks came from hardness
and 12 from membership. The new geometric identification used only standard
axioms. Plane completeness likewise added no axioms to its existing source proof.

```sh
lake build +LeanTrominoes.Theorem55Proof:olean +LeanTrominoes.Theorem55StripProof:olean
```

Inspect current dependencies with `#print axioms` on `Theorem55.planeProved`
and `Theorem55.stripProved`, fully qualified by `LeanTrominoes`.
The translation-only extension is described in [Corollary 5.6](corollary-5.6.md).
See [README](../README.md) for current paper coverage.
