# Three polyominoes, translations only

The target is Corollary 5.6: two fixed connected 15-ominoes (the horizontal
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

The hardness target builds (9790 jobs). Orientation-restricted upper bounds
are in progress; the completeness assertions are not yet proved.
