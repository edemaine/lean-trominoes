# Three polyominoes, translations only

**Corollary 5.6 is proved** by `ThreeTranslationPolyominoes.proved` in
[ThreeTranslationProof.lean](LeanTrominoes/ThreeTranslationProof.lean): two fixed connected 15-ominoes (the horizontal
and vertical versions of P), and an input disconnected Q. Every placement
must be a translation. The plane problem is co-r.e.-complete; the strip
problem is PSPACE-complete under the same unary encoding as Theorem 5.5.

## Established reductions

- `TranslationTiling` defines restricted and translation-only exact tilings,
  and proves that replacing placements by identical footprints preserves tilings.
- `ThreeTranslationPolyominoes.translationTileable_iff` identifies the three
  translation-only kinds with P/Q tilings where only P may rotate or reflect.
- `ThreeTranslationGeometry` proves that both keyed constructions obey the
  restriction on Q, and retains the exact source-tiling equivalence.
- `ThreeTranslationCompilerCorrect` verifies the existing plane and unary
  strip compilers against the new predicates.
- `plane_coREHard` and `strip_PSPACEHard` are proved
  in namespace `LeanTrominoes.ThreeTranslationPolyominoes`.
- `RestrictedStripWindow` proves the finite-window characterization with an
  arbitrary allowed-orientation predicate.

## Upper bounds and completeness

`TranslationPlaneSearch` adds the allowed-orientation condition to finite
patch search. Its compactness proof forces every forbidden placement to be
absent, and its finite checker is primitive recursive. This proves
`ThreeTranslationPolyominoes.plane_coRE`.

`TranslationStripRaw` restricts the existing transition relation by checking
selected placements in the first column. `TranslationStripExpr` compiles this
condition to bounded arithmetic. The Savitch wrappers reuse the existing input
adapters and relation-independent bounds, with the new transition evaluator.
`TranslationStripEvaluatorSpace` bounds the complete run by a polynomial in
the original unary input length. `ThreeTranslationStripMembership` supplies
the actual finite-alphabet polynomial-space machine.

The final declarations are `planeProved`, `stripProved`, and `proved` in
namespace `LeanTrominoes.ThreeTranslationPolyominoes`. `fixed_card`,
`fixed_connected`, and `fixed_distinct` establish the two fixed tiles' properties.
The target definitions are in
[ThreeTranslationStatements.lean](LeanTrominoes/ThreeTranslationStatements.lean).

Validation: `lake build +LeanTrominoes.ThreeTranslationProof:olean` completed
successfully (9880 jobs).

The public import also passes `lake env lean LeanTrominoes.lean`.
`tmp/ThreeTranslationAudit.lean` reports no `sorryAx`. The new plane upper
bound, fixed-tile connectivity, strip compiler correctness, and arithmetic
transition certificate use only standard axioms. Strip membership retains
the same 12 existing arithmetic native checks. The combined completeness
proof reports 5388 inherited native-check dependencies; no new axiom or
`native_decide` call was introduced.
