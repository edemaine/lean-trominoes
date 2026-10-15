# Tiling and completion

Section 5: tile and placement definitions, periodic-subspace membership, tromino hardness, polyomino and polycube constructions, completion, and domino algorithms. Wang contains adapters to the external lean-wang results.

The reorganization placed 2,623 existing modules here.

Import `LeanTrominoes.Tiling.Results` for the curated public results.

Useful entry points:

- [Tromino periodic-subset tiling](Tromino/Theorem52Proof.lean)
- [Two-polyomino plane theorem](Polyomino/Theorem55Proof.lean)
- [Two connected polycubes in space](Polycube/TwoConnectedPolycubesSpaceProof.lean)
- [Periodic completion completeness](Completion/CompletionCompleteness.lean)
- [Finite completion decision](Completion/FiniteCompletionDecision.lean)
- [Domino tiling and completion](Domino/DominoTheorems.lean)

See the [repository overview](../../README.md#repository-organization) for the
paper map and the [maintenance guide](../../docs/organization.md) for import
migration and validation commands.
