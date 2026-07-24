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

The formalization is planned in four layers.  A box is checked only when the
corresponding definitions and proof are available through this project's Lean
build; an imported proof counts when its statement matches the paper.

### 1. Tiling foundations

- [x] Define 2D integer-lattice cells and polyominoes, all square-grid rigid
  motions, placements, and exact tilings by one or more prototiles.
- [x] Define the periodic-subset tiling inputs and predicates needed in 2D and
  1.5D for Theorem 5.2.
- [ ] Define partial placements, completion, finite-region tiling, and
  translation-only tiling.
- [ ] Generalize the geometric and input definitions to polycubes and arbitrary
  dimension.
- [x] **Theorem 3.1 (Berger):** Wang tiling is co-r.e.-complete.  This is
  supplied by the imported `LeanWang.Final` interface.

### 2. Periodic graphs and drawings

- [ ] Define finite presentations of infinite periodic graphs, protovertices,
  protoedges, locality, and periodic labelings and drawings.
- [ ] **Theorem 2.1:** Every local 1D or 2D periodic graph has a linear-grid
  orthocrossing drawing, orthogonal when its maximum degree is at most four.
- [ ] **Theorem 2.2:** A planar local periodic drawing of maximum degree four
  can be made planar and orthogonal on an $O(M^3)$ grid while preserving its
  vertex positions.
- [ ] **Lemma 2.3:** Normalize degree-three vertices in a periodic planar
  orthogonal drawing, including a chosen left edge, with linear grid blowup.

### 3. Complexity and algorithms

- [ ] **Theorem 3.2:** Local Periodic CNF SAT is PSPACE-complete in 1D and
  co-r.e.-complete in 2D and higher dimensions (including nonlocal instances
  in dimensions above two).
- [ ] **Theorem 3.3:** Local Periodic 3SAT is PSPACE-complete in 1D and
  co-r.e.-complete in 2D.
- [ ] **Theorem 3.4:** The same bounds hold for Local Periodic 3SAT-3.
- [ ] **Theorem 3.5:** The same bounds hold for Local Periodic Planar 3SAT and
  3SAT-3, even with polynomial drawing-grid size.
- [ ] **Theorem 3.6:** The same bounds hold for Local Periodic Planar
  1-in-3SAT and 1-in-3SAT-3, even with polynomial drawing-grid size.
- [ ] **Theorem 3.7:** Local Periodic Planar 3DM has the same bounds, even when
  every colored vertex has degree two or three.
- [ ] **Theorem 3.8:** Local Periodic Planar Trichromatic Graph Orientation is
  PSPACE-complete in 1D and co-r.e.-complete in 2D; its finite form is
  NP-complete.
- [ ] **Theorem 4.1:** Local Periodic 2SAT is solvable in polynomial time in
  every dimension.
- [ ] **Theorem 4.2:** Periodic Horn and Dual Horn SAT are solvable in linear
  time, and every satisfiable instance has a 1-periodic solution.
- [ ] **Lemma 4.3:** If a local periodic graph admits a perfect matching, an
  imperfect 1-periodic matching has an augmenting path of diameter
  $2d|E|$ from every free vertex.
- [ ] **Lemma 4.4:** The bipartition of a connected bipartite periodic graph is
  2-periodic.
- [ ] **Lemma 4.5:** A bipartite periodic graph with a perfect matching has an
  augmenting path of length less than $|V|$ with no repeated protovertex.
- [ ] **Theorem 4.6:** A bipartite periodic graph with a perfect matching has a
  1-periodic perfect matching.
- [ ] **Theorem 4.7:** Periodic bipartite perfect matching is solvable in
  $O(|E|\sqrt{|V|})$ time and returns a 1-periodic matching.

### 4. Tiling consequences

- [ ] **Lemma 5.1:** Periodic subspace tiling and completion are in co-r.e. for
  polynomial-bounding-box prototiles, and in PSPACE in 1.5D.
- [ ] **Theorem 5.2:** Tiling a periodic subset of $\mathbb Z^2$ by either
  single tromino is co-r.e.-complete; the 1.5D problem is PSPACE-complete.
  - [x] Prove co-r.e. membership of the 2D problem for each tromino.
  - [ ] Prove co-r.e.-hardness of the 2D problem for each tromino.
  - [ ] Prove PSPACE membership of the 1.5D problem for each tromino.
  - [ ] Prove PSPACE-hardness of the 1.5D problem for each tromino.
- [ ] **Corollary 5.3:** The translation-only variant with the two orientations
  of the I tromino has the same complexity bounds.
- [ ] **Corollary 5.4:** Tiling a finite subset of $\mathbb Z^2$ by either
  single tromino is NP-complete.
- [ ] **Theorem 5.5:** Tiling with one constant-size connected polyomino and
  one polynomial-bounding-box disconnected polyomino is co-r.e.-complete, and
  PSPACE-complete in 1.5D.
- [ ] **Corollary 5.6:** Translation-only tiling with two constant-size
  connected polyominoes and one disconnected polyomino has the same bounds.
- [ ] **Corollary 5.7:** Completion from a finite preplacement is
  co-r.e.-complete for two fixed polyominoes.
- [ ] **Corollary 5.8:** Tiling 3D, or any fixed-height 2.5D slab of height
  greater than one, is co-r.e.-complete for two connected polycubes, one of
  constant size.
- [ ] **Corollary 5.9:** Translation-only tiling of 2.5D or 3D is
  co-r.e.-complete for three connected polycubes, two of constant size.
- [ ] **Theorem 5.10:** Completion of an infinite periodic partial tiling by
  either single tromino is co-r.e.-complete in 2D and PSPACE-complete in 1.5D.
- [ ] **Corollary 5.11:** For each tromino, some completable periodic partial
  tiling has only aperiodic completions.
- [ ] **Theorem 5.12:** Completion from a finite tromino preplacement is
  decidable, and is NP-complete for polynomial-size bounding boxes.
- [ ] **Theorem 5.13:** Every tileable periodic polycube subset has a periodic
  domino tiling with at most twice the original period.
- [ ] **Corollary 5.14:** Every completable periodic partial domino tiling has
  such an at-most-double-period completion.
- [ ] **Corollary 5.15:** Periodic-subset domino tiling is decidable in
  polynomial time in every dimension.

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

The definition layer needed to state Theorem 5.2 is complete.  Its 2D
co-r.e. upper bound is now proved by `periodicTrominoTiling_coRE`, using a
primitive-recursive exhaustive search for a finite obstruction.  The complete
formal target remains `LeanTrominoes.Theorem52.statement`, the conjunction of:

- `planeStatement`: co-r.e.-completeness in 2D for each of the I and L
  trominoes; and
- `stripStatement`: PSPACE-completeness in 1.5D for each tromino.

The representation choices for this target are:

- [`LeanTrominoes/Basic.lean`](LeanTrominoes/Basic.lean) defines polyominoes,
  the eight square-grid symmetries, placements, and the I and L trominoes.
- [`LeanTrominoes/Tiling.lean`](LeanTrominoes/Tiling.lean) defines a tiling by
  requiring every placed tile to lie in the region and every region cell to
  have a unique covering placement.
- [`LeanTrominoes/FootprintTiling.lean`](LeanTrominoes/FootprintTiling.lean)
  proves that tromino tilings can equivalently be represented by their
  geometric three-cell footprints, matching the boundary data used to compose
  adjacent gadgets.
- [`LeanTrominoes/Periodic.lean`](LeanTrominoes/Periodic.lean) represents a 2D
  `PeriodicRegion` by a finite motif and two full-rank period vectors.  Its
  1.5D analogue, `PeriodicStrip`, uses a finite motif in
  $\mathbb Z \times \{0,\ldots,W-1\}$ and one positive horizontal period.
  Malformed finite presentations are no-instances of the decision predicates.
- [`LeanTrominoes/Complexity.lean`](LeanTrominoes/Complexity.lean) supplies the
  missing PSPACE interface on top of Mathlib's finite multi-stack Turing
  machines.  Its `Primcodable` encoding is ordinary little-endian binary in
  the four-symbol alphabet of Mathlib's partial-recursive evaluator, followed
  by one list delimiter; this makes the verified evaluator directly usable
  without changing asymptotic input length.  Space is the total number of
  occupied stack cells, and hardness uses polynomial-time many-one reductions.
- [`LeanTrominoes/EncodingBounds.lean`](LeanTrominoes/EncodingBounds.lean)
  proves size bounds for the actual pairing-based `PeriodicStrip` input
  encoding.  Both `⌈log₂ period⌉` and motif length are at most the binary
  input length; combined with the sparse state count, the Savitch recursion
  depth is at most `21 × input length + 1`.
- [`LeanTrominoes/FiniteState.lean`](LeanTrominoes/FiniteState.lean) proves the
  pumping fact underlying the 1.5D upper bound: a finite transition system has
  a bi-infinite path exactly when it has a nonempty directed cycle.  The strip
  argument will instantiate its states with bounded tiling frontiers.
- [`LeanTrominoes/FiniteStateSearch.lean`](LeanTrominoes/FiniteStateSearch.lean)
  shortens every such cycle to at most the number of states and packages this
  bounded witness as a decidable finite-search predicate.
- [`LeanTrominoes/FiniteStateReachability.lean`](LeanTrominoes/FiniteStateReachability.lean)
  verifies the Savitch recurrence used for polynomial-space cycle search:
  recursion depth `d` decides walks of length at most $2^d$, so depth one
  above the base-two logarithm of the state count covers the finite graph.
- [`LeanTrominoes/FiniteStateCycleSearch.lean`](LeanTrominoes/FiniteStateCycleSearch.lean)
  turns that reachability procedure into an executable Boolean cycle search:
  it chooses one edge and checks bounded reachability back to its source, and
  proves this succeeds exactly when the finite graph contains a directed
  cycle.
- [`LeanTrominoes/FiniteTMCompiler.lean`](LeanTrominoes/FiniteTMCompiler.lean)
  fills a machine-level gap in Mathlib's computability stack.  A TM2 program
  described over an infinite ambient label type can be restricted to a
  certified finite reachable-label set and bundled as the `FinTM2` required
  by the PSPACE interface.  Erasing label-membership proofs is proved to
  preserve individual steps, complete finite executions, stack contents, and
  stack-space usage; conversely, every supported ambient execution lifts
  uniquely to the restricted machine.  This is the first compiler layer
  needed to package the verified strip decider as an explicit
  polynomial-space machine.
- [`LeanTrominoes/PartrecFiniteEvaluator.lean`](LeanTrominoes/PartrecFiniteEvaluator.lean)
  applies that compiler to Mathlib's verified four-stack evaluator for
  partial-recursive codes.  For each fixed code it produces a genuine finite
  `FinTM2`, proves that its initial and halting configurations erase to
  Mathlib's configurations, and transfers the evaluator's output-correctness
  theorem to the finite machine.  `finiteEvaluatorComputable` now packages
  any total represented code directly against the project's standard input
  and output encodings.  `primrecFiniteEvaluatorComputable` additionally
  extracts a `ToPartrec.Code` from any typed primitive-recursive function and
  compiles it all the way to such a finite machine.  Proving the strip decider
  primitive recursive and establishing its polynomial stack-space bound
  remain separate steps.
- [`LeanTrominoes/PartrecPolySpace.lean`](LeanTrominoes/PartrecPolySpace.lean)
  isolates the quantitative half of that compilation.  A
  `PolySpaceDecider` supplies a fixed evaluator code, its Boolean correctness,
  and a polynomial bound on every reachable ambient four-stack
  configuration.  `PolySpaceDecider.toFiniteDecider` transfers the execution
  to the finite supported machine and proves the exact
  `Complexity.DeciderInPolySpace` certificate, using preservation of all
  stack contents under label restriction.  The file also gives exact native
  tape-size formulas for encoded natural lists, retained continuation data,
  initial and halting configurations, and every high-level evaluator
  milestone related by Mathlib's transcription invariant.
- [`LeanTrominoes/StripFrontier.lean`](LeanTrominoes/StripFrontier.lean)
  defines that finite system using overlapping five-column windows.  Its
  states store assignments only at cells from the finite motif, so sparse
  presentations do not incur space proportional to the binary-encoded strip
  width; the transition predicate is decidable.
- [`LeanTrominoes/StripFrontierSpace.lean`](LeanTrominoes/StripFrontierSpace.lean)
  computes the exact frontier-state count as
  `period × 9^(5 × distinct motif cells)`.  Consequently the Savitch depth is
  at most `⌈log₂ period⌉ + 20 × distinct motif cells + 1`, the quantitative
  sparse bound needed for polynomial space.
- [`LeanTrominoes/StripFrontierCorrectness.lean`](LeanTrominoes/StripFrontierCorrectness.lean)
  proves the forward correctness direction: a globally locally valid strip
  assignment cuts into a bi-infinite path of normalized, overlapping sparse
  frontier states, preserving the center-column placement and coverage
  constraints exactly.
- [`LeanTrominoes/StripFrontierReconstruction.lean`](LeanTrominoes/StripFrontierReconstruction.lean)
  proves the converse, including alignment of an arbitrary path's cyclic
  phase with actual strip coordinates.  Thus a well-formed periodic strip is
  tileable exactly when its finite sparse-frontier graph has a directed
  cycle of length at most the number of frontier states.  Its executable
  decision procedure now uses the verified logarithmic-depth cycle search,
  rather than enumerating and retaining a full cycle.  Turning this algorithm
  and the sparse state-count estimate into the explicit polynomial-space
  Turing machine required by `Complexity.InPSPACE` remains the upper-bound
  task.
- [`LeanTrominoes/Gadget.lean`](LeanTrominoes/Gadget.lean) and
  [`LeanTrominoes/ExactCover.lean`](LeanTrominoes/ExactCover.lean) define
  open gadget windows and a verified exact-cover enumerator for their local
  tilings and geometric boundary states.
- [`LeanTrominoes/GadgetLibrary.lean`](LeanTrominoes/GadgetLibrary.lean)
  records all 46 nonblank `6 × 6` pixel masks from Figures 11 and 12, plus the
  blank local drawing cell, in a typed gadget library.  Every mask is
  mechanically certified to have no duplicate pixels and to lie in its
  window.
- [`LeanTrominoes/GadgetWire.lean`](LeanTrominoes/GadgetWire.lean) computes
  and prunes local transfer relations; in particular, each pictured red
  horizontal wire has exactly two states that extend bi-infinitely.
- [`LeanTrominoes/GadgetPorts.lean`](LeanTrominoes/GadgetPorts.lean) normalizes
  north, east, south, and west boundary footprints so adjacent gadget windows
  can be composed by equality of finite port states.
- [`LeanTrominoes/GadgetAssembly.lean`](LeanTrominoes/GadgetAssembly.lean)
  proves that every verified open-window tiling induces a unique local cover
  by geometric tromino footprints and that its four ports depend only on this
  cover, not on redundant placement encodings.  It also proves an abstract
  gluing theorem: coherent exact covers on a plane-covering family of windows
  form one global tromino tiling.  Conversely, restricting any global tiling
  to a finite window is proved to give the corresponding exact open-window
  tiling whenever the local mask is the global carrier inside that window.
- [`LeanTrominoes/GadgetBehavior.lean`](LeanTrominoes/GadgetBehavior.lean)
  defines the intermediate infinite finite-state system: every lifted drawing
  cell selects a verified exact-cover state, and neighboring selections agree
  on their normalized geometric ports.  It records the two central gadget
  correctness goals separating finite-state behavior from geometric gluing;
  the orientation goal explicitly restricts the gadget side to well-formed
  drawings, whose adjacent half-edge colors agree.
  The forward gluing theorem is already proved under its precise geometric
  coherence condition, including equality between the infinite block atlas
  and the carrier of the compiled finite `PeriodicRegion`.  Equality of
  adjacent ports is proved to propagate every shared footprint across each of
  the four corresponding neighboring block boundaries.  The footprint
  geometry is bounded mechanically from the two prototiles: a tromino can
  meet only its selected block and the eight immediately neighboring blocks.
  Every Figure 11/12 mask is also certified to omit all four window corners;
  together with tromino connectivity, this proves that any footprint crossing
  a side actually meets the corresponding cardinal-neighbor block.
  Consequently, every locally exact, port-compatible infinite gadget
  assignment is proved to glue into a tiling of the compiled periodic region.
  In the converse direction, every global tiling of that region is now proved
  to restrict and translate to a verified exact-cover state in each local
  `6 × 6` gadget window.  The translated footprints of each extracted state
  are characterized exactly as the globally selected footprints meeting that
  block, which supplies geometric coherence independently of placement
  representation.  Geometric coherence is proved equivalent to equality of
  adjacent normalized ports for locally exact states, so the extracted states
  are port-compatible.  Thus `substitutionAssemblyCorrect` proves the full
  equivalence between compatible gadget assignments and tilings of the
  compiled periodic region.
- [`LeanTrominoes/GadgetColoring.lean`](LeanTrominoes/GadgetColoring.lean)
  formalizes the periodic marker colorings in Figures 11(a) and 12(a), the
  center-to-colored-pixel orientation vectors, and the invariant that a
  placed tromino contains at most one pixel of each marker color.
- [`LeanTrominoes/GadgetOrientation.lean`](LeanTrominoes/GadgetOrientation.lean)
  extracts those vectors from local exact tilings and proves that every target
  pixel receives a unique center-to-pixel vector.
- [`LeanTrominoes/GadgetOrientationBehavior.lean`](LeanTrominoes/GadgetOrientationBehavior.lean)
  support-prunes the complete four-port state table and mechanically certifies
  the local Figure 11 behavior for L trominoes.  Every supported state obeys
  its wire/vertex orientation rule, every legal local orientation is
  represented, and equal ports on opposite sides encode complementary values.
  These certificates are lifted to the full infinite assignment:
  `lHasOrientation_of_hasCompatibleGadgetTiling` proves that every compatible
  Figure 11 assignment over a well-formed normalized drawing induces a valid
  graph orientation.
- [`LeanTrominoes/GadgetIOrientationBehavior.lean`](LeanTrominoes/GadgetIOrientationBehavior.lean)
  recovers the richer Figure 12 phase carried by an I-tromino footprint: its
  center, the marker pixel of the edge color, and their direction vector.
  Neutral phases are completed against the full local cell constraint, with
  the trichromatic gadget read from its single central 0-or-3 phase.  The raw
  open-window table contains extra vertex states that can connect only
  directly to another degree-three vertex; the orthogonal normalization never
  permits such an interface.  The formal table therefore retains exactly the
  states whose active vertex arms all have nonvertex support.  Exhaustive
  certificates prove local soundness and completeness and complementary
  values across matching viable ports.  These facts are lifted to the
  infinite assignment in
  `iHasOrientation_of_hasCompatibleGadgetTiling`: every compatible Figure 12
  assignment over a well-formed vertex-separated drawing induces a valid
  graph orientation.
- [`LeanTrominoes/GadgetIPortRefinement.lean`](LeanTrominoes/GadgetIPortRefinement.lean)
  retains the exact Figure 12 boundary footprints forgotten by the Boolean
  orientation and proves that every coherent selection of viable I-port
  states lifts to compatible exact local I-tromino tilings.
- [`LeanTrominoes/GadgetIPhaseTable.lean`](LeanTrominoes/GadgetIPhaseTable.lean)
  isolates the only remaining local ambiguity: straight vertical I wires
  admit an optional neutral phase in addition to their visibly directed
  phase.  Removing that redundant phase preserves every legal local
  orientation.  An exhaustive certificate proves that preferred states with
  complementary directions have exactly equal geometric ports.
- [`LeanTrominoes/GadgetIPhaseLift.lean`](LeanTrominoes/GadgetIPhaseLift.lean)
  selects a preferred state at every drawing cell; the certified port law
  makes these arbitrary local choices globally coherent.  It proves
  completeness and combines it with soundness to discharge the full Figure
  12 theorem `iOrientationBehaviorCorrect` on normalized vertex-separated
  drawings.
- [`LeanTrominoes/GadgetPortRefinement.lean`](LeanTrominoes/GadgetPortRefinement.lean)
  retains the geometric phase forgotten by the Boolean L-port value.  It
  proves that a compatible local L-tromino assignment is exactly a valid
  orientation together with a globally coherent selection from the supported
  port table, and conversely lifts any such coherent selection back to exact
  local tilings.  This isolates L completeness as a finite port-phase lifting
  theorem.
- [`LeanTrominoes/GadgetLPhaseTable.lean`](LeanTrominoes/GadgetLPhaseTable.lean)
  exhaustively certifies the geometric phase laws needed for that lift:
  phases can be recombined across degree-two routes, one side can be spliced
  independently into another supported state, and adjacent complementary
  same-color half-edges always admit exactly matching ports.
- [`LeanTrominoes/GadgetLPhaseLift.lean`](LeanTrominoes/GadgetLPhaseLift.lean)
  chooses a matching phase on every drawing edge and uses the splice law to
  combine the four incident choices at each cell.  It proves that every valid
  orientation has a coherent L-port refinement and therefore discharges the
  full Figure 11 theorem `lOrientationBehaviorCorrect`.
- [`LeanTrominoes/GadgetReduction.lean`](LeanTrominoes/GadgetReduction.lean)
  composes the full Figure 11/12 orientation theorems with exact geometric
  assembly.  For each tromino, `orientationReductionRegion` maps every
  well-formed vertex-separated source drawing to its substituted periodic
  region and maps malformed presentations to a dependent-period no-instance.
  The resulting end-to-end equivalence is proved for both trominoes.
- [`LeanTrominoes/GadgetReductionComputability.lean`](LeanTrominoes/GadgetReductionComputability.lean)
  gives the block substitution an extensionally equal natural-range
  implementation and proves it primitive recursive under the canonical
  encodings.  `NormalizedOrientationReduction` packages the exact source
  certificate needed from the paper's earlier reductions: a computable
  well-formed, vertex-separated drawing with orientation equivalence.
  Such certificates compose with either gadget library to give computable
  many-one reductions, and `theorem52_planeStatement_of_normalizedOrientation`
  proves the entire 2D conjunct conditionally on the isolated
  `NormalizedOrientationCoREHard` interface.  Establishing that source
  interface remains the 2D hardness gap.
- [`LeanTrominoes/OrthogonalDrawing.lean`](LeanTrominoes/OrthogonalDrawing.lean)
  defines the finite toroidal normalized source drawings, colored port
  matching, and their global 1-in-3 / 0-or-3 orientation predicate on the
  full infinite periodic lift.  Orientations are not required to share the
  input periods.  The finite cell list has a standard primitive-recursive
  encoding for later reductions.  It also records the normalization invariant
  that degree-three vertices are separated by routing cells and proves its
  lift to every adjacent pair in the infinite drawing.
- [`LeanTrominoes/GadgetSubstitution.lean`](LeanTrominoes/GadgetSubstitution.lean)
  replaces each drawing cell by its `6 × 6` paper mask and packages the
  resulting motif as a full-rank `PeriodicRegion`; its carrier is proved equal
  to the infinite periodic union of the translated gadget blocks.
- [`LeanTrominoes/Theorem52.lean`](LeanTrominoes/Theorem52.lean) assembles
  these definitions with `LeanWang.CoREComplete` into the formal target.

## Build

```bash
lake build
```
