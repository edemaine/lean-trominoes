# lean-trominoes

Lean formalization of the theorems in
[*Undecidability of Tiling with a Tromino*](https://arxiv.org/abs/2509.07906)
by the MIT--ULB CompGeom Group, Zachary Abel, Hugo Akitaya, Lily Chung,
Erik D. Demaine, Jenny Diomidova, Della Hendrickson, Stefan Langerman, and
Jayson Lynch.  The repository includes the working paper as
[`trominoes.pdf`](trominoes.pdf) and [`trominoes.texlish`](trominoes.texlish).

## Goal

The eventual goal is to formalize every theorem and lemma in the paper.  The
main result says that, given an infinite periodic partial placement of copies
of either tromino, deciding whether it extends to a tiling of the plane is
co-r.e.-complete and therefore undecidable.  The project will also cover the
paper's contrasting decidability results and the periodic-graph theory used by
the reductions.

The formalization is planned in four layers:

1. **Tiling foundations.** Define integer-lattice polyominoes and polycubes,
   their allowed rigid motions, exact tilings, partial placements, periodic
   subsets, periodic completion, translation-only tiling, and the finite,
   1.5-dimensional, 2-dimensional, and higher-dimensional problem encodings.
2. **Periodic graphs and drawings.** Formalize finite presentations of
   infinite periodic graphs, locality and periodic labelings, together with
   the orthocrossing and orthogonal drawing constructions and their grid-size
   bounds (Theorems 2.1--2.2 and Lemma 2.3).
3. **Complexity and algorithms.** Verify the periodic reductions through CNF
   SAT, 3SAT-3, planar 1-in-3SAT, planar 3-dimensional matching, and
   trichromatic graph orientation (Theorems 3.2--3.8), plus the algorithms for
   periodic 2SAT, Horn SAT, and bipartite perfect matching
   (Theorems 4.1--4.7).
4. **Tiling consequences.** Formalize the reductions to tromino subspace
   tiling and completion; the two-polyomino and connected-polycube results;
   the translation-only variants; finite-completion decidability; the
   existence of completable periodic placements having only aperiodic
   completions; and the polynomial-time periodic-domino results
   (Lemma 5.1 and Theorems/Corollaries 5.2--5.15).

The intended endpoint includes both halves of each completeness claim:
computable hardness reductions and membership in the stated complexity class,
as well as the constructive algorithms and quantitative bounds appearing in
the theorem statements.

## Relationship to `lean-wang`

This project depends on
[`edemaine/lean-wang`](https://github.com/edemaine/lean-wang), which already
formalizes co-r.e.-completeness and undecidability of Wang tiling (the starting
point recorded as Theorem 3.1 in the paper).  The initial module imports its
proof-neutral public interface, `LeanWang.Final`; later reductions should reuse
that interface and its computability definitions where possible.

The Lean version is kept in sync with `lean-wang` at Lean 4.31.0.  Lake records
the exact fetched dependency revision in the committed `lake-manifest.json`.

## Status

The Lake project and dependency are initialized.  No tromino theorem has been
formalized yet; [`LeanTrominoes/Basic.lean`](LeanTrominoes/Basic.lean) is the
starting point for the common definitions.

## Build

```bash
lake build
```
