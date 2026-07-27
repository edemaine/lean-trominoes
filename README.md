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
- [`LeanTrominoes/PeriodicGraph.lean`](LeanTrominoes/PeriodicGraph.lean)
  represents an infinite periodic graph by finite protovertices and
  offset-labelled protoedges, with locality, degree, and lifted-adjacency
  predicates.  It also constructs the periodic incidence graph of a CNF
  presentation, anchoring each clause orbit at its first literal.  The
  companion
  [`LeanTrominoes/PeriodicThreeSATThreeGraph.lean`](LeanTrominoes/PeriodicThreeSATThreeGraph.lean)
  proves that the occurrence-split formula produces a well-formed local
  incidence graph of maximum degree three.
- [`LeanTrominoes/PeriodicGridDrawing.lean`](LeanTrominoes/PeriodicGridDrawing.lean)
  gives rational periodic drawings their scaled integer-grid representation:
  vertex positions, protoedge polylines, translated segment occurrences,
  route compatibility, orthogonality, and proper orthocrossing.
- [`LeanTrominoes/PeriodicOrthocrossingConstruction.lean`](LeanTrominoes/PeriodicOrthocrossingConstruction.lean)
  implements the linear-grid track construction: three private port columns
  per degree-three vertex, private rows per protoedge, boundary-aware
  neighbor-cell routes, and private gate columns for vertical translations.
  [`LeanTrominoes/PeriodicOrthocrossingCorrectness.lean`](LeanTrominoes/PeriodicOrthocrossingCorrectness.lean)
  proves distinct in-domain vertex positions and exact translated endpoints
  for every generated protoedge route.
  [`LeanTrominoes/PeriodicOrthocrossingPorts.lean`](LeanTrominoes/PeriodicOrthocrossingPorts.lean)
  proves that port count equals graph degree and that all real edge-end ports
  receive distinct columns under the maximum-degree-three premise.
  [`LeanTrominoes/PeriodicOrthocrossingOrthogonal.lean`](LeanTrominoes/PeriodicOrthocrossingOrthogonal.lean)
  classifies every local offset into the five cardinal cases, proves each
  complete route orthogonal, and identifies drawing orthogonality with
  route-by-route orthogonal polylines before lifting the construction to the
  full periodic drawing.
  [`LeanTrominoes/PeriodicOrthocrossingSegments.lean`](LeanTrominoes/PeriodicOrthocrossingSegments.lean)
  exposes the equivalent protoedge-first enumeration of drawing segments and
  proves periodic-coordinate and common-lane lemmas for the crossing proof;
  it also reduces orthocrossing to uniqueness of parallel interiors.
  [`LeanTrominoes/PeriodicOrthocrossingClassification.lean`](LeanTrominoes/PeriodicOrthocrossingClassification.lean)
  assigns every erased route piece its exact semantic role and preserves its
  protoedge and within-route indices for the private-lane argument.
  [`LeanTrominoes/PeriodicOrthocrossingHorizontal.lean`](LeanTrominoes/PeriodicOrthocrossingHorizontal.lean)
  normalizes every horizontal segment to a private fundamental-domain lane,
  proves those lane representatives lie within one drawing period, and proves
  uniqueness of overlapping translates whose horizontal span is at most one
  period; its fanout midpoint invariant separately identifies the short
  source and target fanout pieces by their real graph ports.
  [`LeanTrominoes/PeriodicOrthocrossingHorizontalUnique.lean`](LeanTrominoes/PeriodicOrthocrossingHorizontalUnique.lean)
  combines the private-lane and fanout-midpoint invariants to prove that
  horizontal segment occurrences with a common interior point have identical
  occurrence keys.
  [`LeanTrominoes/PeriodicOrthocrossingVertical.lean`](LeanTrominoes/PeriodicOrthocrossingVertical.lean)
  eliminates unit vertical fanout and boundary pieces from integer-grid
  crossings, then normalizes the remaining real-port and private-gate columns
  and proves that equal normalized columns identify equal semantic roles.
  [`LeanTrominoes/PeriodicOrthocrossingVerticalUnique.lean`](LeanTrominoes/PeriodicOrthocrossingVerticalUnique.lean)
  bounds every vertical route piece by one drawing period and proves that
  vertical occurrences with a common interior point have identical occurrence
  keys.
  [`LeanTrominoes/PeriodicOrthocrossingCertified.lean`](LeanTrominoes/PeriodicOrthocrossingCertified.lean)
  combines the two axis-specific uniqueness theorems with orthogonality to
  certify the complete constructed drawing as a proper periodic
  orthocrossing drawing.
  [`LeanTrominoes/PeriodicOrthocrossingBounds.lean`](LeanTrominoes/PeriodicOrthocrossingBounds.lean)
  bounds every stored segment endpoint inside the surrounding `3 × 3` block
  of drawing cells and proves that only the nine neighboring translates can
  meet the canonical fundamental square, making crossing enumeration finite.
  [`LeanTrominoes/PeriodicOrthocrossingTranslationDegree.lean`](LeanTrominoes/PeriodicOrthocrossingTranslationDegree.lean)
  sharpens that finite bound for one fixed segment: its parallel coordinate
  selects a unique neighboring shift, and its one-period axial span prevents
  both opposite shifts from meeting the half-open square.  Consequently at
  most two translated copies of a segment can participate in the canonical
  square, the quotient bound needed for periodic terminal occurrence counts.
  [`LeanTrominoes/PeriodicOrthocrossingCrossingTranslationDegree.lean`](LeanTrominoes/PeriodicOrthocrossingCrossingTranslationDegree.lean)
  specializes the bound to translations that actually carry a canonical
  crossing.  It also projects every crossover boundary to its indexed segment
  and translation and proves that translation belongs to the resulting
  at-most-two-element set.
  [`LeanTrominoes/PeriodicOrthocrossingCrossings.lean`](LeanTrominoes/PeriodicOrthocrossingCrossings.lean)
  enumerates the finite neighboring segment occurrences and fundamental-square
  lattice points, filters them to proper crossings of distinct occurrences,
  and proves that every actual crossing in the square appears in this
  executable canonical list.
  [`LeanTrominoes/PeriodicOrthocrossingCanonical.lean`](LeanTrominoes/PeriodicOrthocrossingCanonical.lean)
  orders every crossing horizontal-first, deduplicates the resulting records,
  and proves that every actual crossing selects one of the two possible
  occurrence orders in this normalized gadget-site list.
  [`LeanTrominoes/PeriodicOrthocrossingPlanarCrossovers.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarCrossovers.lean)
  replaces those records by positioned crossover formulas in `20 × 20`
  macrocells, with four explicit boundary-wire variables and internals scoped
  by the crossing record.  Segment-occurrence assignments extend through all
  crossovers, while every satisfying family propagates both carrier signals.
  [`LeanTrominoes/PeriodicOrthocrossingPlanarWires.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarWires.lean)
  groups boundary ports by translated segment-occurrence key, sorts them
  along their carrier axis, and inserts positioned equality links between
  consecutive distinct crossover sites.  Every link is certified to remain
  on one carrier, so carrier assignments satisfy the complete wire layer.
  [`LeanTrominoes/PeriodicOrthocrossingPlanarCore.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarCore.lean)
  renames the wire variables into the crossover formula's external summand
  and appends both clause families.  Every segment-carrier assignment extends
  to a satisfying core assignment, and every satisfying core assignment
  obeys all crossover propagation and inter-site equality laws.
  [`LeanTrominoes/PeriodicOrthocrossingPlanarTerminals.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarTerminals.lean)
  adds explicit start and finish variables to every neighboring segment
  occurrence.  Sorting terminals together with crossing boundaries produces
  complete carrier chains, including carriers with no crossings and the
  portions before the first and after the last crossing.  Each terminal is
  placed at the directional port of its `20 × 20` macrocell, matching the
  crossover boundary coordinates; these ports are proved interior to the
  macrocell, distinct across the ends of every genuine segment, and
  equivariant under periodic translation.
  [`LeanTrominoes/PeriodicOrthocrossingPlanarBends.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarBends.lean)
  places equality links at every turn of every neighboring route occurrence.
  Exact duplicate bend records are removed before links are generated.
  Together with the straight-segment carrier chains, one Boolean value now
  propagates through an entire translated route.
  [`LeanTrominoes/PeriodicOrthocrossingPlanarRouteCore.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarRouteCore.lean)
  embeds crossover boundaries into that complete carrier-node type and
  combines all crossover, straight-chain, and bend clauses.  Its interface
  proves both simultaneous extension of arbitrary route values and all three
  propagation laws for every satisfying core assignment.
  [`LeanTrominoes/PeriodicOrthocrossingPlanarCarrierSoundness.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarCarrierSoundness.lean)
  combines internal crossover propagation with the equality links between
  consecutive sites, proving that the start and finish terminals of every
  neighboring straight segment occurrence carry the same value.
  [`LeanTrominoes/PeriodicOrthocrossingPlanarRouteSoundness.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarRouteSoundness.lean)
  composes straight-segment and bend propagation by induction over each
  constructed polyline, equating the canonical first and last terminals of
  every neighboring translated route.
  [`LeanTrominoes/PeriodicOrthocrossingPlanarEndpoints.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarEndpoints.lean)
  recovers the source and target terminal of every neighboring translated
  protoedge route, retains the lifted graph vertex reached at each end, and
  proves that every terminal has the advertised route-occurrence key.
  [`LeanTrominoes/PeriodicCNFPlanarIncidences.lean`](LeanTrominoes/PeriodicCNFPlanarIncidences.lean)
  retains the source clause, literal index, sign, and atom behind every
  incidence protoedge.  Forgetting this metadata is proved to reproduce the
  graph's edge list in exactly the same global order, so routed endpoints can
  be attached back to their SAT meaning.
  [`LeanTrominoes/PeriodicCNFPlanarVertexGadgets.lean`](LeanTrominoes/PeriodicCNFPlanarVertexGadgets.lean)
  groups routed source endpoints into the original signed clauses and routed
  target endpoints into Figure 8(a) variable duplicators.  Clause sites are
  enumerated independently of their incidences, so empty clauses remain
  explicit contradictions.  Both positioned finite families have exact
  satisfaction characterizations.
  [`LeanTrominoes/PeriodicCNFPlanarFormula.lean`](LeanTrominoes/PeriodicCNFPlanarFormula.lean)
  combines the complete crossover/route core with both routed vertex
  families under one variable type.  Componentwise satisfaction is exact,
  and compatible route and atom values extend simultaneously through every
  fresh crossover internal.
  [`LeanTrominoes/PeriodicCNFPlanarAssignment.lean`](LeanTrominoes/PeriodicCNFPlanarAssignment.lean)
  pulls a plane-wide atom assignment onto routes by their global incidence
  index.  Every in-range lookup is proved exact, and the resulting target
  terminal values satisfy all routed variable duplicators.
  [`LeanTrominoes/PeriodicCNFPlanarCompleteness.lean`](LeanTrominoes/PeriodicCNFPlanarCompleteness.lean)
  proves that every satisfying assignment of the original periodic CNF
  satisfies all routed clause copies and therefore extends through the full
  finite planarized drawing formula.
  [`LeanTrominoes/PeriodicCNFPlanarRouteSoundness.lean`](LeanTrominoes/PeriodicCNFPlanarRouteSoundness.lean)
  specializes complete route propagation to metadata-rich CNF incidences,
  proving equality of every canonical routed clause terminal and its
  corresponding variable terminal.
  [`LeanTrominoes/PeriodicCNFPlanarDegree.lean`](LeanTrominoes/PeriodicCNFPlanarDegree.lean)
  proves that a fixed incidence has at most one translated route reaching a
  lifted variable site.  Thus each routed variable list is bounded by the
  source protovariable's formal occurrence count, and by three for 3SAT-3.
  [`LeanTrominoes/PeriodicCNFPlanarWidth.lean`](LeanTrominoes/PeriodicCNFPlanarWidth.lean)
  proves that the complete routed planar block retains width three.  The
  fixed crossover, equality-wire, bend, and duplicator components inherit
  the generic gadget certificates; a keyed-incidence argument shows that
  each routed source clause has exactly its original number of literals.
  [`LeanTrominoes/PeriodicCNFPlanarVariableSoundness.lean`](LeanTrominoes/PeriodicCNFPlanarVariableSoundness.lean)
  uses that bound to show every routed target is one of the three duplicator
  ports.  In a satisfying combined formula, every routed clause terminal
  therefore equals the central atom at the incidence route's target.
  [`LeanTrominoes/PeriodicCNFPlanarPeriodicization.lean`](LeanTrominoes/PeriodicCNFPlanarPeriodicization.lean)
  turns the finite neighboring drawing block into a genuine periodic CNF:
  explicit terminal and atom translations become literal offsets.  Its
  satisfaction is proved equivalent to satisfying the routed finite block
  at every lattice translate.
  [`LeanTrominoes/PeriodicCNFPlanarPeriodicCompleteness.lean`](LeanTrominoes/PeriodicCNFPlanarPeriodicCompleteness.lean)
  assembles plane-wide atom and route values with independently chosen
  crossover internals in every translated block, proving that source
  satisfiability implies periodicized planar satisfiability.
  [`LeanTrominoes/PeriodicCNFPlanarPeriodicSoundness.lean`](LeanTrominoes/PeriodicCNFPlanarPeriodicSoundness.lean)
  follows each satisfied routed clause terminal through its route and
  degree-three duplicator, reconstructing a satisfying source assignment.
  Thus the periodicized planar formula preserves satisfiability exactly for
  occurrence-three sources.
  [`LeanTrominoes/PeriodicCNFPlanarOneInThree.lean`](LeanTrominoes/PeriodicCNFPlanarOneInThree.lean)
  applies the positioned Figure 9 replacement to the complete routed block
  and periodicizes it.  Explicit translations on original routed variables
  become literal offsets, clause-local auxiliaries remain at offset zero,
  and periodic exact-one satisfaction is proved equivalent to satisfying
  the finite positioned formula at every lattice translate.
  [`LeanTrominoes/PeriodicCNFPlanarOneInThreeCorrectness.lean`](LeanTrominoes/PeriodicCNFPlanarOneInThreeCorrectness.lean)
  assembles the finite Figure 9 auxiliary choices into a plane-wide
  exact-one assignment and restricts any such assignment back to the routed
  SAT variables.  This proves exact satisfiability preservation relative to
  the routed planar block and, for width-three occurrence-three sources,
  relative to the original periodic CNF.
  [`LeanTrominoes/PeriodicCNFPlanarThreeSATThree.lean`](LeanTrominoes/PeriodicCNFPlanarThreeSATThree.lean)
  applies the paper's implication-cycle occurrence split after planarization,
  where crossover internals may have acquired degree above three.  The
  resulting periodic formula is proved equisatisfiable with the routed
  formula, retains width three, and has at most three occurrences of every
  protovariable.
  [`LeanTrominoes/PeriodicCNFPlanarOneInThreeThree.lean`](LeanTrominoes/PeriodicCNFPlanarOneInThreeThree.lean)
  then applies Figure 9 to that repaired formula.  It proves the resulting
  periodic exact-one instance has width and occurrence bound three and is
  satisfiable exactly when the original width-three occurrence-three source
  is satisfiable.  Its geometric placement is deliberately factored into the
  following embedding layer.
  [`LeanTrominoes/PeriodicCNFPlanarThreeSATThreePositioned.lean`](LeanTrominoes/PeriodicCNFPlanarThreeSATThreePositioned.lean)
  introduces positioned periodic clauses, which retain both drawing
  coordinates and periodic literal offsets.  It assigns canonical positions
  to routed protovariables, places every occurrence copy and implication-cycle
  clause in a refined variable macrocell, and proves that forgetting all
  positions gives exactly the verified occurrence-split periodic formula.
  [`LeanTrominoes/PeriodicCNFPlanarOneInThreeThreePositioned.lean`](LeanTrominoes/PeriodicCNFPlanarOneInThreeThreePositioned.lean)
  applies the local Figure 9 placement to that offset-preserving
  representation.  Erasure is proved equal to the logical exact-one
  endpoint, transferring its width-three, occurrence-three, and end-to-end
  satisfiability theorems.
  [`LeanTrominoes/PeriodicCNFPlanarOneInThreeNoUnitsPositioned.lean`](LeanTrominoes/PeriodicCNFPlanarOneInThreeNoUnitsPositioned.lean)
  places the final unit-elimination gadgets in constant-size refinements of
  those exact-one clause cells.  Erasing positions is exactly the verified
  logical unit-free formula, and its end-to-end satisfiability theorem is
  retained.
  [`LeanTrominoes/PeriodicCNFPlanarOneInThreePlacements.lean`](LeanTrominoes/PeriodicCNFPlanarOneInThreePlacements.lean)
  carries canonical protovariable positions and the physical drawing period
  through occurrence splitting, Figure 9, its opaque wrapper, and final
  unit-clause elimination.  Clause-local auxiliaries compensate for their
  logical anchor offsets, with checked cancellation lemmas showing that each
  translated occurrence lands at its declared local gadget vertex.  Explicit
  noncrossing incidence routes remain for the subsequent geometric layer.
  [`LeanTrominoes/PeriodicCNFPlanarSATGeometry.lean`](LeanTrominoes/PeriodicCNFPlanarSATGeometry.lean)
  connects the finite routed block to that periodic placement.  It proves
  that removing a neighboring translate from a finite variable name and
  storing it as a literal offset preserves the physical vertex exactly.
  Subtracting a clause's common anchor from a finite incidence polyline then
  produces the canonical periodic clause and translated-variable endpoints
  required by the incidence graph.
  [`LeanTrominoes/PeriodicCNFDeduplication.lean`](LeanTrominoes/PeriodicCNFDeduplication.lean)
  removes repeated protoclauses from an ordinary periodic CNF.  Membership,
  assignment satisfaction, satisfiability, locality, and every clause-width
  bound are proved unchanged; its occurrence list is a sublist of the source
  list, so every finite-presentation occurrence bound is preserved as well.
  [`LeanTrominoes/PeriodicEqualityNormalization.lean`](LeanTrominoes/PeriodicEqualityNormalization.lean)
  gives translated equality families a sharper quotient count.  It identifies
  a normalized link by its endpoint protovariables and relative offset, proves
  that anchor normalization followed by clause deduplication retains exactly
  the two implication clauses for each distinct normalized link, and derives
  that formula occurrence degree is twice normalized endpoint degree.
  [`LeanTrominoes/PositionedPeriodicCNFDeduplication.lean`](LeanTrominoes/PositionedPeriodicCNFDeduplication.lean)
  removes repeated periodic clause orbits from neighboring-block
  presentations while retaining one geometric representative.  Erasure is
  exactly the generic semantic deduplication, so all of those invariants
  transfer.
  [`LeanTrominoes/PositionedPeriodicCNFDeduplicationRoutes.lean`](LeanTrominoes/PositionedPeriodicCNFDeduplicationRoutes.lean)
  transports finite geometric incidence routes through that changed clause
  indexing.  It also proves that normalizing every source clause and its
  physical routes together preserves their endpoints.  Each retained clause
  then selects its first anchor-normalized representative and reuses the
  matching literal route.  The transported family is proved to satisfy every
  periodic incidence endpoint, and compatibility is reduced to finite
  distinctness and fundamental-square bounds for the retained vertices.
  [`LeanTrominoes/PeriodicCNFPlanarSATDeduplication.lean`](LeanTrominoes/PeriodicCNFPlanarSATDeduplication.lean)
  first puts every routed clause orbit in its canonical anchor gauge, then
  removes exact duplicates and wraps its variables.  Normalizing before
  deduplication ensures that uniformly translated finite clauses select one
  periodic representative.  The resulting positioned source remains
  equisatisfiable with the full routed periodic formula and retains its width
  bound; it is the finite clause-vertex set used by the geometry-ordered
  pipeline.
  [`LeanTrominoes/PeriodicCNFPlanarSATIncidenceRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarSATIncidenceRoutes.lean)
  reduces the routed SAT block's periodic endpoint proof to a finite physical
  obligation: connect each displayed clause to the displayed position of each
  literal in its presentation order.  Any such route family is transported
  through periodicization, opaque variable wrapping, clause-orbit
  deduplication, and clause-anchor normalization, yielding both pointwise
  endpoint identities and the complete periodic `RoutesMatch` certificate.
  In particular, its canonical direct rays have exact normalized endpoints
  and induce a lawful polar-angle occurrence order before high-degree
  variables are split; these rays are not claimed to be orthogonal routes.
  [`LeanTrominoes/PositionedPeriodicCNFIncidenceDrawing.lean`](LeanTrominoes/PositionedPeriodicCNFIncidenceDrawing.lean)
  defines that layer's exact certificate: one polyline per literal in the
  incidence graph's presentation order, compatible variable-then-clause
  vertex positions, orthogonality, and periodic planarity.  Clause prototype
  positions subtract the common logical anchor, and verified endpoint
  identities recover both the displayed clause point and each translated
  literal point.
  [`LeanTrominoes/PositionedPeriodicCNFIncidenceRouteLookup.lean`](LeanTrominoes/PositionedPeriodicCNFIncidenceRouteLookup.lean)
  bridges the certificate's flat drawing lists back to individual
  clause/literal occurrences.  It proves pointwise vertex-position and route
  lookup, recovers each occurrence's positioned metadata, and derives the
  exact source and translated-target endpoints of its declared route; every
  genuine pointwise route is also recovered from the flat list with its
  orthogonal-polyline certificate.  Fundamental-square bounds and injective
  vertex placement furthermore separate its endpoints, so its polyline has
  at least one segment.  This is the splice interface used by the planar 3DM
  gadget assembly.
  [`LeanTrominoes/PositionedPeriodicCNFOrthogonalIncidenceRoutes.lean`](LeanTrominoes/PositionedPeriodicCNFOrthogonalIncidenceRoutes.lean)
  supplies a total canonical Manhattan detour for every positioned literal
  incidence.  Fresh detour coordinates make all four segments nondegenerate
  and axis-aligned even for coincident advertised endpoints; the assembled
  drawing is proved to have exact periodic endpoints and to be orthogonal.
  These deliberately generic routes do not assert planarity, leaving later
  construction files to choose noncrossing lanes.
  [`LeanTrominoes/PositionedPeriodicCNFFinitePlanarCertificate.lean`](LeanTrominoes/PositionedPeriodicCNFFinitePlanarCertificate.lean)
  packages the remaining geometric proof boundary into finite data.  Given
  distinct bounded vertices, bounded route endpoints, exact compatibility,
  orthogonality, and three Boolean checks over the nine neighboring period
  translates, it derives an infinite continuously planar incidence drawing
  and the presentation consumed by the exact-one-to-3DM reduction.
  [`LeanTrominoes/PositionedPeriodicCNFExpandedFinitePlanarCertificate.lean`](LeanTrominoes/PositionedPeriodicCNFExpandedFinitePlanarCertificate.lean)
  supplies the corresponding certificate for genuine periodic incidences:
  route endpoints may occupy the one-cell halo, route contacts are checked
  over 25 relative translations, and successful checks still promote to the
  same continuously planar incidence-presentation interface.  Its
  ribbon-ready refinement additionally carries pointwise route bounds and
  the endpoint-contact check, promoting directly to the strengthened source
  interface used by topological lane expansion.
  [`LeanTrominoes/PositionedPeriodicCNFAnchorNormalization.lean`](LeanTrominoes/PositionedPeriodicCNFAnchorNormalization.lean)
  fixes the periodic gauge used by that splice: it subtracts each clause's
  first literal offset from every literal and from the displayed clause
  position.  Every resulting clause has anchor zero, while satisfaction by
  every plane-wide assignment—and therefore satisfiability—is unchanged.
  [`LeanTrominoes/PositionedPeriodicCNFAnchorNormalizationDrawing.lean`](LeanTrominoes/PositionedPeriodicCNFAnchorNormalizationDrawing.lean)
  proves that this change of gauge preserves the finite incidence graph,
  vertex positions, route list, and complete periodic drawing exactly.
  Consequently a certified planar incidence presentation transports directly
  to the normalized formula.
  [`LeanTrominoes/PositionedPeriodicCNFRebasedRouteBounds.lean`](LeanTrominoes/PositionedPeriodicCNFRebasedRouteBounds.lean)
  states the pointwise one-cell-halo bound needed after a source incidence is
  reversed and rebased from its clause prototype to its variable prototype.
  It proves that anchor normalization maps the metadata-rich incidence list
  pointwise while leaving every such rebased route unchanged, and packages
  the bound together with continuous source planarity for the three-strand
  assembly.  Its upper-margin variant records the extra unit of room needed
  by a closed refined ribbon block and is likewise invariant under anchor
  normalization.
  [`LeanTrominoes/PeriodicOneInThreeAnchorNormalization.lean`](LeanTrominoes/PeriodicOneInThreeAnchorNormalization.lean)
  closes the corresponding semantic obligation for exact-one formulas:
  normalization preserves each ordered clause-value list up to translation,
  exact-one satisfiability, occurrence bounds, and the arity-two-or-three
  promise.
  [`LeanTrominoes/PeriodicGridDrawingFinitePlanarity.lean`](LeanTrominoes/PeriodicGridDrawingFinitePlanarity.lean)
  reduces the certificate's two infinite nonintersection predicates to
  executable finite checks whenever all stored vertices and segment endpoints
  lie inside one fundamental square.  Translation-normalization lemmas prove
  that every possible global contact becomes a contact in the canonical
  square with one of only nine neighboring route translations; successful
  finite route/route and vertex/route checks therefore imply full periodic
  planarity.  The checker enumerates only integer points in each segment
  interior, rather than the area of the whole fundamental square, so the
  fixed gadget certificates remain practical to evaluate.
  [`LeanTrominoes/PeriodicGridDrawingContinuousPlanarity.lean`](LeanTrominoes/PeriodicGridDrawingContinuousPlanarity.lean)
  closes the checker’s continuous-geometry gap for collinear unit segments:
  it adds exact open-interior separation for every pair of periodic segment
  occurrences, packages this with the established endpoint and vertex
  conditions, and defines the strengthened positioned-incidence
  presentation required for safe gadget substitution.  The stronger
  certificate is invariant under clause-anchor normalization.
  [`LeanTrominoes/PeriodicGridDrawingScaling.lean`](LeanTrominoes/PeriodicGridDrawingScaling.lean)
  supplies the positive integral-refinement algebra used by local
  substitutions.  Scaling commutes with translations and polyline
  segmentation and preserves orthogonality, open and closed containment,
  continuous segment-interior intersection, and route endpoints exactly.
  At the whole-drawing level it scales the period and all vertex and route
  lookups coherently, preserving fundamental-square bounds, endpoint
  compatibility, orthogonality, disjoint continuous route interiors, and
  avoidance of route interiors by graph vertices.  Continuous separation
  also rules out contacts at newly introduced intermediate grid points, so
  continuous planarity is preserved as a whole.
  [`LeanTrominoes/PeriodicMacrocellGeometry.lean`](LeanTrominoes/PeriodicMacrocellGeometry.lean)
  records the arithmetic for placing bounded local gadgets inside a uniform
  periodic refinement.  Open offsets stay inside the enlarged fundamental
  square, and equality of two refined points recovers both their source
  lattice cells and local offsets; in particular, gadgets based at distinct
  source vertices cannot collide.
  [`LeanTrominoes/PositionedPeriodicCNFScaling.lean`](LeanTrominoes/PositionedPeriodicCNFScaling.lean)
  lifts that refinement operation to positioned clauses, variable
  placements, and clause-major incidence routes.  It proves that logical
  literals and their periodic offsets are unchanged, while every physical
  clause vertex, variable vertex, literal endpoint, route point, and period
  scales uniformly.  Assembling the scaled data is exactly whole-drawing
  scaling, so every continuously planar incidence presentation transports
  directly to the refined coordinates needed for bounded-degree local fans.
  [`LeanTrominoes/PositionedPeriodicCNFRibbonScaling.lean`](LeanTrominoes/PositionedPeriodicCNFRibbonScaling.lean)
  specializes that refinement to the padding needed by ribbon routing.
  Doubling an open-halo source point leaves one full integer unit below the
  doubled upper boundary, and positive scaling preserves endpoint-only
  listed-point contacts.  Thus any halo-bounded ribbon-ready presentation
  doubles to another ribbon-ready presentation carrying the stronger upper
  route margin.
  [`LeanTrominoes/PeriodicGridDrawingFiniteContinuousPlanarity.lean`](LeanTrominoes/PeriodicGridDrawingFiniteContinuousPlanarity.lean)
  makes that extra condition executable.  An interval-overlap bound reduces
  every possible continuous contact to the same nine neighboring periodic
  translations, and a finite Boolean check now certifies exact continuous
  planarity together with the existing endpoint and vertex checks.
  [`LeanTrominoes/PeriodicGridDrawingPointBounds.lean`](LeanTrominoes/PeriodicGridDrawingPointBounds.lean)
  converts pointwise bounds on every stored polyline into the indexed
  segment-endpoint bounds required by the finite periodic checker.  Its
  route-splice membership lemma lets assembly proofs establish those bounds
  independently for each local prefix, corridor, and suffix.  Conversely,
  endpoint bounds control every point of any nondegenerate stored route,
  which is the form needed when refining a certified source drawing.  The
  same point-to-segment conversion is available for the one-cell halo used
  by boundary-crossing periodic routes.
  [`LeanTrominoes/PeriodicGridDrawingExpandedBounds.lean`](LeanTrominoes/PeriodicGridDrawingExpandedBounds.lean)
  replaces the unusably strict fundamental-square endpoint hypothesis by the
  natural one-cell halo `(-P,2P)²`.  It proves that any contact between two
  halo-bounded route occurrences has relative translation in an explicit
  `5 × 5` set, accommodating genuine nonzero-offset periodic edges.  Closed
  containment also preserves the one-unit upper-margin variant used by
  padded ribbon routes.
  [`LeanTrominoes/PeriodicGridDrawingExpandedFinitePlanarity.lean`](LeanTrominoes/PeriodicGridDrawingExpandedFinitePlanarity.lean)
  evaluates route/route avoidance over those 25 relative translations and
  proves the check complete for the infinite periodic lift.  Because stored
  vertices remain in the canonical square, its vertex/route half reuses the
  smaller nine-translation Boolean check.
  [`LeanTrominoes/PeriodicGridDrawingExpandedFiniteContinuousPlanarity.lean`](LeanTrominoes/PeriodicGridDrawingExpandedFiniteContinuousPlanarity.lean)
  proves the matching 25-translation bound for open collinear interval
  overlap and adds an executable exact-interior check.  Together the expanded
  checks certify continuous planarity of periodic drawings with genuine
  boundary-crossing edges.
  [`LeanTrominoes/PeriodicGridDrawingEndpointContacts.lean`](LeanTrominoes/PeriodicGridDrawingEndpointContacts.lean)
  closes the remaining contact loophole needed before ribbon thickening.
  Distinct lifted listed route points may coincide only when both are outer
  route endpoints; thus two unrelated bends cannot conceal a four-way
  topological crossing.  Pointwise halo bounds reduce this condition to an
  executable check over the same 25 relative translations and prove the
  check sound for the complete infinite periodic lift.
  [`LeanTrominoes/PeriodicGridDrawingRibbonSeparation.lean`](LeanTrominoes/PeriodicGridDrawingRibbonSeparation.lean)
  bridges that global periodic certificate to the finite two-route predicate
  used by ribbon geometry.  Any two distinct lifted occurrences of stored
  nondegenerate orthogonal routes are proved to have disjoint segment
  interiors, symmetric point/interior avoidance, and endpoint-only listed
  contacts after applying their independent period translations.
  [`LeanTrominoes/PeriodicGridDrawingRouteSimplicity.lean`](LeanTrominoes/PeriodicGridDrawingRouteSimplicity.lean)
  extracts the corresponding one-route invariant.  A stored orthogonal route
  with distinct advertised endpoints is proved duplicate-free, disjoint from
  its own segment interiors at every listed point, and free of intersections
  between distinct segment interiors; together these are the finite
  `RouteIsSimple` certificate needed by unit subdivision.
  [`LeanTrominoes/OrthogonalPolylineRouteReversalContacts.lean`](LeanTrominoes/OrthogonalPolylineRouteReversalContacts.lean)
  proves that this finite separation certificate is preserved when both
  routes are traversed in reverse, as required by variable-to-clause routing.
  [`LeanTrominoes/OrthogonalPolylineStrictSeparation.lean`](LeanTrominoes/OrthogonalPolylineStrictSeparation.lean)
  strengthens the finite predicate to forbid all listed-point contact and
  proves that this strict form composes through endpoint joins on either
  side.  This is the form needed while tile endpoints become internal
  points of a recursively assembled corridor.
  [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceSeparation.lean)
  identifies each active rebased source route by its stable drawing-route
  index and lattice translate, proves this key injective on active
  variable/slot entries, and transfers complete separation to any two
  unequal entries.  Unit subdivision can create contacts only at both
  routes' advertised outer endpoints.
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
- [`LeanTrominoes/EncodingLengthComputability.lean`](LeanTrominoes/EncodingLengthComputability.lean)
  computes that exact binary input length with a bounded halving loop.  The
  loop retains only its current quotient and counter, is primitive recursive,
  and is proved equal to Mathlib's standard `encodeNat` length.
- [`LeanTrominoes/PartrecBinaryLength.lean`](LeanTrominoes/PartrecBinaryLength.lean)
  implements that computation as explicit `ToPartrec.Code` instead of
  selecting an arbitrary extensionally correct primitive-recursive program.
  Division by two is a flat quotient/parity countdown, and a second flat loop
  repeatedly halves the input while incrementing its length; both programs
  are proved correct.  A reusable affine wrapper adds a fixed amount per bit;
  the strip search-depth leaf is now the explicit instance
  `21 × bitLength + 22`.
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
- [`LeanTrominoes/IndexedSavitch.lean`](LeanTrominoes/IndexedSavitch.lean)
  gives the same verified cycle search an arithmetic interface.  States and
  midpoints are natural numbers below an explicit count, and bounded
  existential search is a direct primitive recursion rather than
  `List.range` followed by `List.any`.  Its result is proved equivalent to
  the semantic cycle predicate on `Fin stateCount`; neither the state list nor
  a range of all state indices is constructed.
- [`LeanTrominoes/IndexedSavitchComputability.lean`](LeanTrominoes/IndexedSavitchComputability.lean)
  proves that the direct bounded search, including its two nested state-index
  loops, preserves primitive recursiveness for any primitive-recursive
  indexed predicate.  The proof compiles the loop through `Nat.rec` and does
  not replace it with a list enumeration.
- [`LeanTrominoes/IndexedSavitchDFS.lean`](LeanTrominoes/IndexedSavitchDFS.lean)
  refines the recursive reachability specification to an explicit
  depth-first evaluator.  A configuration stores one current query and one
  continuation frame per unfinished query, never the recursive-call tree.
  The formal depth invariant proves that every reachable configuration has
  at most the original Savitch depth many frames.
- [`LeanTrominoes/IndexedSavitchDFSCorrectness.lean`](LeanTrominoes/IndexedSavitchDFSCorrectness.lean)
  proves that the evaluator's exact fixed-fuel run returns the original
  Savitch reachability answer, and hence that the resulting directed-cycle
  search is extensionally equal to the already verified indexed search.
- [`LeanTrominoes/IndexedSavitchDFSComputability.lean`](LeanTrominoes/IndexedSavitchDFSComputability.lean)
  proves the query, frame, and configuration encodings primitive recursive,
  then compiles the small-step transition, exact fuel recurrence, fixed-fuel
  iteration, and complete bounded cycle driver.  This supplies an executable
  primitive-recursive program whose live continuation stack is the one
  bounded in `IndexedSavitchDFS.lean`.
- [`LeanTrominoes/IndexedSavitchDFSSpace.lean`](LeanTrominoes/IndexedSavitchDFSSpace.lean)
  measures the evaluator's storage frame by frame, with binary natural-number
  fields and constant-size tags.  Every reachable graph index remains below
  the state count, so if both the state count and root depth fit in `bits`
  bits, every configuration uses at most
  `3 × (bits + 1) + depth × (4 × (bits + 1) + 3) + 2` cells.  This flat
  measure avoids the artificial exponential growth caused by treating the
  nested generic list encoding as one natural number.
- [`LeanTrominoes/IndexedSavitchDFSListEncoding.lean`](LeanTrominoes/IndexedSavitchDFSListEncoding.lean)
  serializes that same state as a genuine flat `List Nat`: four leading
  answer/query fields followed by six fields per continuation frame.  Parsing
  is proved to invert serialization, and the native delimited-binary tape
  length used by Mathlib's partial-recursive evaluator is bounded directly,
  with only constant overhead for the Boolean tags.
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
  compiles it all the way to such a finite machine.  The strip decider is now
  primitive recursive, but its generic list-as-a-natural encoding does not
  expose the evaluator's flat stack-space bound; connecting the direct DFS
  representation to a finite machine remains separate.
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
- [`LeanTrominoes/SpaceRefinement.lean`](LeanTrominoes/SpaceRefinement.lean)
  restores the intermediate-state information discarded by ordinary
  deterministic reachability.  Its space-aware executions bound every
  prefix, compose across macro steps, and show that a bounded run to a
  terminal configuration controls every low-level configuration reachable
  from the same start.
- [`LeanTrominoes/PartrecEvaluatorSpaceRefinement.lean`](LeanTrominoes/PartrecEvaluatorSpaceRefinement.lean)
  begins the corresponding quantitative refinement of Mathlib's four-stack
  evaluator.  Its `copy` certificate covers the evaluator's only
  data-duplicating primitive and proves that every intermediate
  configuration is bounded by the final two-copy footprint.  The generic
  move, reverse-move, and clear loops are also certified to preserve or
  decrease total stack space at every step.  This includes the evaluator's
  stable two-pass move, with its temporarily removed and restored delimiter,
  which is used to shuffle continuation data among the four stacks, and
  main-stack head extraction, whose synthesized empty-list zero needs at
  most one additional delimiter cell.  Continuation-stack head extraction is
  bounded by its input footprint because the consumed outer-list delimiter
  pays for the inserted natural-number delimiter.  Its binary-successor
  certificate bounds carry propagation at every bit and allows one extra
  cell precisely for a newly created high bit.  The matching binary
  predecessor certificate covers borrow propagation plus the evaluator's
  empty-list and zero-head case branches without increasing the input
  footprint.  A structural `normalSimulationFits` invariant now composes
  these primitives across every `Code` constructor, and
  `trNormal_respects_inSpace` gives the resulting normalization call one
  common bound covering all of its low-level configurations.  The companion
  `retSimulationFits` and `tr_ret_respects_inSpace` handle every continuation
  return, including the three-way stack rotation for `cons`, nested returns,
  composition, and both branches of `fix`.  `EvaluatorRunFits` packages these
  local obligations across an entire high-level execution; the resulting
  run-level refinement splices all corresponding low-level segments into one
  bounded run from the concrete evaluator input to its unique halt
  configuration.  Determinism then bounds every low-level configuration
  reachable from that input, which is the quantitative premise needed by
  `PolySpaceDecider`.  `inPSPACE_of_evaluatorRunFits` packages such
  input-indexed run certificates all the way through the finite-machine
  compiler to the project's proposition-level PSPACE interface.  Normal,
  return, configuration, and whole-run certificates are all monotone in the
  chosen budget, so separately derived local bounds can be combined under
  one polynomial.  A generic invariant rule reduces the reachable-state
  obligation to an initial predicate, one-step preservation, and a local
  simulation bound.  Exact numeric requirements
  (`normalSimulationSpace`, `retSimulationSpace`, and
  `cfgSimulationSpace`) are proved equivalent to the corresponding logical
  obligations, leaving ordinary natural-number inequalities for
  program-specific space proofs.  `EvaluatorExecutionFits` and
  `EvaluatorCallFits` additionally support a backward,
  continuation-passing proof style: a finite fitted call automatically
  bounds every high-level state reachable during that call and yields an
  `EvaluatorRunFits` certificate at the halting continuation.  Constructor
  rules mirror normalization through `cons`, `comp`, `case`, and `fix` and
  returns through every continuation form, so larger fitted programs can be
  assembled from fitted subcalls.  Successful compositional evaluation is
  now connected to the exact high-level point where its result enters the
  supplied continuation, including recursive `fix` runs.  A bounded trace
  can therefore be prepended to an already fitted continuation execution;
  `EvaluatorCallFits.of_trace` packages this boundary theorem with a numeric
  invariant over the trace.  This supplies the reusable interface needed to
  certify a tail-recursive countdown without replaying the continuation
  plumbing of every derived code combinator.
- [`LeanTrominoes/PartrecCodeSpace.lean`](LeanTrominoes/PartrecCodeSpace.lean)
  separates a finite code call's data cost from its ambient continuation.
  Primitive, composition, pairing, and selected-case rules compose these
  costs while producing full `EvaluatorCallFits` certificates.  This is the
  arithmetic layer used to certify explicit list programs without repeatedly
  unfolding the evaluator's saved continuation data.
- [`LeanTrominoes/PartrecFlatIteration.lean`](LeanTrominoes/PartrecFlatIteration.lean)
  supplies the evaluator-level countdown loop used by the direct machine
  program.  A state `remaining :: payload` is updated through `Code.fix`;
  correctness for any total payload-step code is proved by induction.  The
  recursive call is in tail position, so exponential iteration does not
  accumulate an exponential continuation stack.
- [`LeanTrominoes/PartrecFlatIterationSpace.lean`](LeanTrominoes/PartrecFlatIterationSpace.lean)
  proves the matching fitted-call rule.  A certificate for one fixed-point
  body trace, its normalization, and its returned tagged value lifts to any
  number of countdown iterations under the same evaluator-space budget.
  Thus the space proof depends on the largest live iteration payload, not on
  the possibly exponential iteration count.
- [`LeanTrominoes/PartrecListCode.lean`](LeanTrominoes/PartrecListCode.lean)
  builds direct `ToPartrec.Code` combinators for fixed-offset fields, preserved
  zero-branches, and Boolean tags.  Their list semantics are verified without
  pairing the variable-length payload into one natural; they form the
  instruction layer for compiling the flat DFS transition.
- [`LeanTrominoes/PartrecListCodeSpace.lean`](LeanTrominoes/PartrecListCodeSpace.lean)
  gives those list combinators compositional evaluator data costs, including
  selected `branchZero` paths and a generic tagged-countdown body rule.
- [`LeanTrominoes/PartrecBinaryLengthSpace.lean`](LeanTrominoes/PartrecBinaryLengthSpace.lean)
  gives the matching quantitative proof for the explicit binary search-depth
  computation.  Division by two is a fully fitted evaluator call: its
  quotient/parity loop uses a preserved processed-count invariant, and
  monotonicity of binary encoding length bounds every live quotient by the
  original input's bit length.  The outer binary-length loop preserves the
  sum of its counter and remaining bit length, after which a fixed fitted
  countdown computes `21 × length + 22`.
- [`LeanTrominoes/PartrecFuel.lean`](LeanTrominoes/PartrecFuel.lean)
  computes the exact Savitch evaluator fuel with explicit nested flat
  countdowns.  The innermost loop increments a monotone partial total, the
  middle loop implements multiplication by the frontier-state count, and the
  outer loop implements the depth recurrence.  Its semantic correctness is
  proved directly, exposing the live states needed by the space certificate.
- [`LeanTrominoes/PartrecFuelSpace.lean`](LeanTrominoes/PartrecFuelSpace.lean)
  fits all three fuel countdowns under nested invariants.  Every partial sum
  is bounded by its enclosing loop's result, and every intermediate fuel is
  bounded by the final depth's fuel, so the calculation uses space
  proportional to the binary lengths of its inputs and result.
- [`LeanTrominoes/PartrecPowerTwo.lean`](LeanTrominoes/PartrecPowerTwo.lean)
  computes `2 ^ depth` by a flat doubling loop, reusing the explicit addition
  machinery.  This supplies the padded graph bound used by the indexed
  search.  Every padded index decodes to a valid frontier representative, and
  semantic projection together with the canonical embedding proves that the
  padded graph has a cycle exactly when the sparse-frontier graph does.
- [`LeanTrominoes/PartrecPowerTwoSpace.lean`](LeanTrominoes/PartrecPowerTwoSpace.lean)
  fits the doubling loop under the invariant that its singleton payload is
  `2 ^ processed`.  Every intermediate value is bounded by the final power,
  yielding a linear-space certificate in the binary lengths of the depth and
  padded graph bound.
- [`LeanTrominoes/PartrecSqrt.lean`](LeanTrominoes/PartrecSqrt.lean) and
  [`LeanTrominoes/PartrecSqrtSpace.lean`](LeanTrominoes/PartrecSqrtSpace.lean)
  begin the explicit decoder layer for the remaining strip predicates.
  A flat scan maintains the distance to the next square, the odd gap between
  squares, and the current root; its invariant proves the result is
  `Nat.sqrt`, while all live fields and evaluator traces use linear space.
  This supplies the square-root operation needed by Mathlib's standard
  pairing decoder `Nat.unpair`.
- [`LeanTrominoes/PartrecAdd.lean`](LeanTrominoes/PartrecAdd.lean) and
  [`LeanTrominoes/PartrecAddSpace.lean`](LeanTrominoes/PartrecAddSpace.lean)
  provide fixed-width natural addition for frontier phase arithmetic.  A
  flat countdown increments one accumulator, whose invariant bounds every
  intermediate value by the final sum and yields a reusable linear-space
  evaluator certificate.
- [`LeanTrominoes/PartrecSubtract.lean`](LeanTrominoes/PartrecSubtract.lean),
  [`LeanTrominoes/PartrecSubtractSpace.lean`](LeanTrominoes/PartrecSubtractSpace.lean),
  [`LeanTrominoes/PartrecUnpair.lean`](LeanTrominoes/PartrecUnpair.lean), and
  [`LeanTrominoes/PartrecUnpairSpace.lean`](LeanTrominoes/PartrecUnpairSpace.lean)
  complete an explicit fitted implementation of `Nat.unpair`.  Truncated
  subtraction is a decreasing singleton countdown.  The unpair program
  recovers the offset from the square-root scan's distance and odd gap, then
  uses two bounded subtractions to select and compute the appropriate
  coordinate.  Its result is proved exactly equal to Mathlib's pairing
  decoder.
- [`LeanTrominoes/PartrecPeriodicStripDecode.lean`](LeanTrominoes/PartrecPeriodicStripDecode.lean)
  and
  [`LeanTrominoes/PartrecPeriodicStripDecodeSpace.lean`](LeanTrominoes/PartrecPeriodicStripDecodeSpace.lean)
  apply that decoder twice to the standard nested-pair encoding of a periodic
  strip.  The fitted header program exposes native evaluator fields
  `[width, period, motifCode]`, leaving the variable-length motif encoded for
  the following traversal.
- [`LeanTrominoes/PartrecEncodedListDecode.lean`](LeanTrominoes/PartrecEncodedListDecode.lean)
  and
  [`LeanTrominoes/PartrecEncodedListDecodeSpace.lean`](LeanTrominoes/PartrecEncodedListDecodeSpace.lean)
  provide the fitted one-constructor view used by that traversal.  They
  distinguish the zero-encoded empty list from a successor-encoded cons and
  return the fixed-width native state `[tag, headCode, tailCode]`.  A fitted
  tail step then discards the head while retaining the encoded tail; iterating
  it with the original list code as a safe countdown is proved to exhaust
  every standard encoded list.
- [`LeanTrominoes/PartrecDiv2Parity.lean`](LeanTrominoes/PartrecDiv2Parity.lean)
  and
  [`LeanTrominoes/PartrecDiv2ParitySpace.lean`](LeanTrominoes/PartrecDiv2ParitySpace.lean)
  expose the fitted binary-division loop's complete result
  `[quotient, lowBit]`.  This low bit is the sign tag in Mathlib's standard
  integer encoding, while the quotient is the coordinate magnitude needed
  by motif predicates.
- [`LeanTrominoes/PartrecCellDecode.lean`](LeanTrominoes/PartrecCellDecode.lean)
  and
  [`LeanTrominoes/PartrecCellDecodeSpace.lean`](LeanTrominoes/PartrecCellDecodeSpace.lean)
  combine quotient/parity with standard unpairing to decode an encoded lattice
  cell into `[xMagnitude, xSign, yMagnitude, ySign]`.  Correctness is tied
  directly to Mathlib's even/odd encoding of nonnegative and negative
  integers, and every component has a fitted evaluator certificate.
- [`LeanTrominoes/PartrecBooleanSpace.lean`](LeanTrominoes/PartrecBooleanSpace.lean)
  fits Boolean normalization and short-circuiting conjunction, while
  [`LeanTrominoes/PartrecNatCompare.lean`](LeanTrominoes/PartrecNatCompare.lean)
  and
  [`LeanTrominoes/PartrecNatCompareSpace.lean`](LeanTrominoes/PartrecNatCompareSpace.lean)
  use fitted truncated subtraction to return a normalized tag for natural
  strict comparison.  These operations express positive strip dimensions
  and coordinate upper bounds.
- [`LeanTrominoes/PartrecNatEquality.lean`](LeanTrominoes/PartrecNatEquality.lean)
  and
  [`LeanTrominoes/PartrecNatEqualitySpace.lean`](LeanTrominoes/PartrecNatEqualitySpace.lean)
  compare two native naturals by conjoining zero tests for both truncated
  differences.  The result is a normalized fitted Boolean used by the strip
  base case and by first-occurrence searches through encoded motif cells.
- [`LeanTrominoes/PartrecDivision.lean`](LeanTrominoes/PartrecDivision.lean)
  and
  [`LeanTrominoes/PartrecDivisionSpace.lean`](LeanTrominoes/PartrecDivisionSpace.lean)
  implement binary natural quotient and remainder with one flat countdown.
  The live state stores only its quotient, remainder, and unchanged divisor;
  a reachable-state invariant bounds both accumulators by the original
  dividend, yielding a uniform input-linear evaluator-space certificate.
  This shared primitive supports both period division of frontier indices
  and repeated base-nine assignment-word decoding.
- [`LeanTrominoes/PartrecFrontierIndexDecode.lean`](LeanTrominoes/PartrecFrontierIndexDecode.lean)
  and
  [`LeanTrominoes/PartrecFrontierIndexDecodeSpace.lean`](LeanTrominoes/PartrecFrontierIndexDecodeSpace.lean)
  turn `[period, firstIndex, lastIndex]` into the fixed-width packed view
  `[firstWord, firstPhase, lastWord, lastPhase]`, then expose each word's
  low base-nine digit and residual quotient on demand.  Repeated digit steps
  are proved extensionally equal to the existing assignment-list decoder,
  and every projection, period division, and paired digit step has a
  compositional evaluator-space certificate.  Thus later motif scans can
  stream both frontier assignments without allocating either assignment
  list.
- [`LeanTrominoes/PartrecPackedAssignmentLookup.lean`](LeanTrominoes/PartrecPackedAssignmentLookup.lean)
  implements one streaming motif-column lookup over that packed word.  Its
  fixed-width state peels one base-nine digit per motif cell and freezes at
  the first matching occurrence, including when the motif contains repeated
  cells.  The explicit tail loop is proved equal to a closed recursive scan;
  selected, absent, and skipped-column outcomes are tied to the same
  `List.idxOf` digit used by the semantic packed frontier.
- [`LeanTrominoes/PartrecPackedAssignmentLookupSpace.lean`](LeanTrominoes/PartrecPackedAssignmentLookupSpace.lean)
  fits every projection, encoded-list view, equality test, quotient/remainder
  digit peel, branch, complete lookup step, and flat-countdown body on the
  typed packed state.  Its reachable-suffix invariant proves that motif
  encodings and residual words only decrease, while a newly exposed digit is
  at most eight.  Consequently the complete numeric countdown reuses one
  uniform workspace allowance linear in the encoded live fields.
- [`LeanTrominoes/PartrecPackedAssignmentAt.lean`](LeanTrominoes/PartrecPackedAssignmentAt.lean)
  unrolls the fixed five frontier columns around that scanner.  Each numbered
  stage either skips one complete motif-sized base-nine block or freezes a
  first-occurrence result.  The composed program returns `[digit, found]`,
  and its successful digit is proved to occur at exactly the canonical
  `assignmentKeys` index
  `column * motif.length + motif.idxOf target`.
- [`LeanTrominoes/PartrecPackedAssignmentAtSpace.lean`](LeanTrominoes/PartrecPackedAssignmentAtSpace.lean)
  fits the five-column construction compositionally: numbered-column
  equality, scan-input assembly, each reuse of the uniform motif loop,
  retained accumulator fields, all five stages, and the final
  `[digit, found]` projection.  The accumulator word is proved never to grow,
  while its digit offset grows by at most eight per column and hence remains
  at most forty.  These invariants yield a named input-linear workspace bound
  for the complete packed assignment lookup.
- [`LeanTrominoes/PartrecPackedAssignmentPredicates.lean`](LeanTrominoes/PartrecPackedAssignmentPredicates.lean)
  and
  [`LeanTrominoes/PartrecPackedAssignmentPredicatesSpace.lean`](LeanTrominoes/PartrecPackedAssignmentPredicatesSpace.lean)
  turn that lookup into the first semantic packed-frontier predicate:
  digit zero is proved equivalent to an absent assignment, and the resulting
  `none` test is fitted by composing the lookup, one projection, and one
  zero test.  The projected lookup digit also has its own named input-linear
  evaluator-space bound for reuse by later packed predicates.
- [`LeanTrominoes/PartrecPackedColumnPhase.lean`](LeanTrominoes/PartrecPackedColumnPhase.lean)
  and
  [`LeanTrominoes/PartrecPackedColumnPhaseSpace.lean`](LeanTrominoes/PartrecPackedColumnPhaseSpace.lean)
  compute the wrapped horizontal coordinate of any of the five packed
  frontier columns.  Three fitted additions, two predecessors, and the
  quotient/remainder primitive implement the semantic phase formula on a
  fixed-width native state.
- [`LeanTrominoes/PartrecPackedNormalizedAt.lean`](LeanTrominoes/PartrecPackedNormalizedAt.lean)
  and
  [`LeanTrominoes/PartrecPackedNormalizedAtSpace.lean`](LeanTrominoes/PartrecPackedNormalizedAtSpace.lean)
  decide normalization at one motif occurrence.  The program compares the
  signed horizontal cell coordinate with its wrapped column phase or accepts
  an absent packed assignment; the fitted Boolean composition is proved
  equal to `PackedWindowState.normalizedAtBool`.  Its evaluator cost is
  bounded explicitly by a fixed constant times the encoded size of one
  arithmetic envelope containing the period, phase, motif, cell, column,
  and packed word.
- [`LeanTrominoes/PartrecPackedNormalizationLoop.lean`](LeanTrominoes/PartrecPackedNormalizationLoop.lean)
  and
  [`LeanTrominoes/PartrecPackedNormalizationLoopSpace.lean`](LeanTrominoes/PartrecPackedNormalizationLoopSpace.lean)
  streams that predicate through one complete encoded motif column.  Its
  fixed-width state retains the original motif for assignment lookup, a
  decreasing suffix, the packed phase and word, and one validity bit; the
  closed loop is proved equal to `PackedWindowState.normalizedColumnBool`.
  Exact evaluator-space certificates fit every component of one streaming
  step and the surrounding flat-countdown body.  A preserved reachable-state
  invariant restricts those steps to actual motif suffixes, yielding one
  finite workspace envelope for the complete fitted column program.
  `packedNormalizationColumnCost_le_linear` bounds that entire program by a
  fixed constant times one encoded arithmetic envelope for the period, phase,
  motif, column, and packed word.
- [`LeanTrominoes/PartrecPackedOverlapAt.lean`](LeanTrominoes/PartrecPackedOverlapAt.lean)
  and
  [`LeanTrominoes/PartrecPackedOverlapAtSpace.lean`](LeanTrominoes/PartrecPackedOverlapAtSpace.lean)
  compare adjacent packed windows at one shared motif occurrence.  Two
  streamed assignment lookups expose only the relevant base-nine digits;
  bounded-digit injectivity proves their numeric equality equivalent to the
  semantic `PackedWindowState.overlapsAtBool` test.  The complete projection,
  pair assembly, and equality program has a named evaluator-space bound
  linear in one encoded envelope for both columns and packed words.
- [`LeanTrominoes/PartrecPackedOverlapLoop.lean`](LeanTrominoes/PartrecPackedOverlapLoop.lean)
  streams the one-occurrence comparison through an encoded motif suffix,
  retaining only the two packed assignment words and one validity bit.
  Its closed loop is proved equal to
  `PackedWindowState.overlapsColumnBool`; four explicitly assembled copies
  then compute exactly the shared-column conjunction over `List.finRange 4`.
  [`LeanTrominoes/PartrecPackedOverlapLoopSpace.lean`](LeanTrominoes/PartrecPackedOverlapLoopSpace.lean)
  fits every component of one suffix step and the surrounding countdown
  body.  Its motif-suffix invariant lifts the local bound through the
  complete flat countdown, and the fitted one-column program has an explicit
  linear envelope in the motif encoding and both packed words.  The four
  fixed column adapters and their nested conjunction are also fitted exactly;
  only their final shared linear majorant remains on the membership track.
- [`LeanTrominoes/PartrecStripFrontierContext.lean`](LeanTrominoes/PartrecStripFrontierContext.lean)
  and
  [`LeanTrominoes/PartrecStripFrontierContextSpace.lean`](LeanTrominoes/PartrecStripFrontierContextSpace.lean)
  connect that decoder to the actual leaf payload
  `[encodedStrip, firstIndex, lastIndex]`.  The explicit program returns the
  fixed-width native context
  `[width, period, motifCode, firstWord, firstPhase, lastWord, lastPhase]`;
  its fitted certificate composes only the verified strip-header decoder,
  quotient/remainder calls, field projections, and native-list assembly.
- [`LeanTrominoes/PartrecStripCellBounds.lean`](LeanTrominoes/PartrecStripCellBounds.lean)
  and
  [`LeanTrominoes/PartrecStripCellBoundsSpace.lean`](LeanTrominoes/PartrecStripCellBoundsSpace.lean)
  assemble those pieces into the first strip-specific fitted predicate.
  Given `[width, period, cellCode]`, it returns one exactly when the decoded
  cell is nonnegative in both coordinates and lies below the selected
  `period × width` bounds, equivalently in the strip fundamental domain.
- [`LeanTrominoes/PartrecStripWellFormed.lean`](LeanTrominoes/PartrecStripWellFormed.lean)
  lifts the cell predicate over an encoded motif without materializing the
  list.  Its tail-style state retains only the encoded suffix, one validity
  bit, and the two dimensions; the original motif code safely bounds the
  countdown.  Composed with the explicit strip-header decoder, the resulting
  unary program is proved exactly equal to `PeriodicStrip.wellFormed`.
- [`LeanTrominoes/PartrecStripWellFormedSpace.lean`](LeanTrominoes/PartrecStripWellFormedSpace.lean)
  fits every reachable motif-step component, including encoded-list view,
  cell bounds, validity accumulation, and preservation of dimensions.
  It lifts these certificates through the complete typed countdown, dimension
  checks, loop-input assembly, header projection, and strip-header decoder,
  yielding an `EvaluatorCodeFits` certificate for the full explicit unary
  well-formedness program.  Its reachable-state loop certificate tracks that
  every live motif is a suffix of the input motif, so all iterations reuse one
  input-linear workspace allowance instead of summing space over the numeric
  countdown.
- [`LeanTrominoes/IndexedSavitchDFSPartrec.lean`](LeanTrominoes/IndexedSavitchDFSPartrec.lean)
  compiles one structural step of the flat Savitch evaluator directly to
  `ToPartrec.Code`.  Its machine payload retains the context, state count,
  explicit frame count, and six natural fields per continuation frame.
  The compiled step is proved equal to the semantic DFS transition, and its
  tail-recursive countdown loop is proved equal to repeated semantic steps.
- [`LeanTrominoes/StripFrontierPartrec.lean`](LeanTrominoes/StripFrontierPartrec.lean)
  supplies the evaluator's strip-specific depth-zero program.  It extracts
  the encoded strip and two queried frontier indices from the flat payload,
  computes equality or the indexed frontier edge relation, and is connected
  to both the verified small step and the tail-recursive iterator.  A
  separately verified raw-edge program supports the outer cycle scan.
- [`LeanTrominoes/StripFrontierCyclePartrec.lean`](LeanTrominoes/StripFrontierCyclePartrec.lean)
  builds the complete parameterized cycle-search driver.  One wrapper
  initializes a reachability query and runs its exact verified fuel; nested
  tail-recursive countdowns then scan both frontier endpoints while retaining
  only loop counters, a Boolean accumulator, and the current flat DFS stack.
  The parameterized driver is proved equal to
  `cycleSearchIndexDFSBoolAtDepth`; a unary front end computes the strip's
  padded state bound and certified search depth, rejects malformed presentations,
  and is proved equal to `periodicStripTrominoTilingIndexBool`.
  Its state-bound, depth, well-formedness, parameter-assembly, and guarded
  driver codes are named public control points for the evaluator-space proof.
- [`LeanTrominoes/StripFrontierPartrecSpace.lean`](LeanTrominoes/StripFrontierPartrecSpace.lean)
  bounds the complete serialized payload of each compiled exact-fuel
  reachability loop.  Although the countdown's numeric value is exponential,
  its little-endian binary encoding has quadratic length; combining that
  bound with the flat DFS theorem accounts explicitly for the strip context,
  graph-size and stack-length counters, and every semantic loop milestone.
  The surrounding first- and second-endpoint countdown payloads have a
  separate explicit linear bound, including all loop counters and their
  Boolean accumulator.  `stripEvaluatorSpacePolynomial` combines both bounds
  with the exact typed-input size, constant Boolean-output size, and a linear
  allowance for explicit arithmetic into one polynomial envelope for the
  evaluator proof.  `stripSearchDepthCode_fits` certifies the complete
  binary-length and affine search-depth call within that shared envelope.
  `stripStateBoundCode_fits` composes it with the fitted repeated-doubling
  calculation of the padded graph bound.
  `stripFuelCode_fits` similarly certifies the explicit exact-fuel
  computation within a quadratic reserve.  `stripWellFormedCode_fits`
  certifies the complete explicit well-formedness program within the shared
  arithmetic reserve.  `StripEvaluatorLeafCallsFit` isolates the two
  remaining leaf calls as continuation-passing fitted-call obligations:
  only the base relation and raw edge still use correctness-only code
  selection while their explicit fitted implementations are developed.
- [`LeanTrominoes/StripFrontier.lean`](LeanTrominoes/StripFrontier.lean)
  defines that finite system using overlapping five-column windows.  Its
  states store assignments only at cells from the finite motif, so sparse
  presentations do not incur space proportional to the binary-encoded strip
  width; the transition predicate is decidable.
- [`LeanTrominoes/StripFrontierEncoding.lean`](LeanTrominoes/StripFrontierEncoding.lean)
  gives those input-dependent, function-valued states a uniform raw
  representation: a natural phase and a list over the nine assignment
  symbols.  Five columns of the input motif traversal determine a canonical
  word of length `5 × motif length`; repeated motif cells create harmless
  redundant coordinates whose first copy determines the semantic assignment.
  Encoding produces a valid raw state, decoding recovers the original
  semantic state exactly, and the verified fixed-length word generator
  contains an encoding of every semantic frontier state.  Avoiding an
  explicit deduplication pass makes this the streaming storage format for the
  space-bounded strip evaluator.
- [`LeanTrominoes/StripFrontierIndex.lean`](LeanTrominoes/StripFrontierIndex.lean)
  ranks a raw frontier arithmetically: its assignment word is a base-nine
  number and its phase is the residue modulo the strip period.  The resulting
  indices range below exactly
  `period × 9^(5 × motif length)`.  Ranking and on-demand decoding are proved
  inverse on every valid raw state, and every natural index decodes to a valid
  state when the period is positive.  The canonical range—and padded indices
  beyond it—may contain multiple representatives of one semantic state, but
  the canonical range still surjects onto the semantic frontier graph.  Thus
  later midpoint searches can loop over natural indices without materializing
  the exponential state list.
- [`LeanTrominoes/StripFrontierIndexComputability.lean`](LeanTrominoes/StripFrontierIndexComputability.lean)
  begins the compiler-facing proof for that representation.  The decoder is
  expressed as a map over the polynomial word length, with each digit read as
  `(code / 9^position) % 9`; digit lookup, exponentiation, and the complete
  assignment-word decoder are all proved primitive recursive.  Computable
  motif traversal, the canonical five-column key list, and the exact
  arithmetic raw-index count are now primitive recursive as well.  Raw-state
  phase and assignment projections and lookup of a raw assignment at a window
  cell are primitive recursive too, as is on-demand decoding of a complete
  state index; semantic decoding is factored through one verified conversion
  from valid raw states to `WindowState`.
- [`LeanTrominoes/StripFrontierRawTransition.lean`](LeanTrominoes/StripFrontierRawTransition.lean)
  gives normalization, center-column exact-cover, and four-column overlap
  checks directly on uniform raw states, using only explicit finite lists and
  Boolean tests.  On valid raw states, the combined raw transition is proved
  equivalent to the original semantic `WindowState.Transition`.
- [`LeanTrominoes/StripFrontierPacked.lean`](LeanTrominoes/StripFrontierPacked.lean)
  replaces each decoded assignment list by one base-nine natural while
  preserving the same phase, first-occurrence lookup for repeated motif
  cells, normalization, center validity, overlap, and complete transition
  Boolean.  Decoding a packed state is proved equal to the existing raw state
  obtained from an arithmetic index, so the indexed edge predicate can now be
  implemented against fixed-width packed data without changing its meaning.
- [`LeanTrominoes/StripFrontierRawTransitionComputability.lean`](LeanTrominoes/StripFrontierRawTransitionComputability.lean)
  proves primitive recursiveness of every layer of that executable
  transition: modular phases, raw and local lookups, active candidates,
  containment and single-coverage checks, overlap, and their final Boolean
  conjunction.
- [`LeanTrominoes/StripFrontierIndexedSearch.lean`](LeanTrominoes/StripFrontierIndexedSearch.lean)
  instantiates arithmetic Savitch search with the tromino frontier relation.
  Each padded index is decoded to one raw state only when its transition is
  checked; no input-dependent state is constructed by the executable test.
  Every such index projects to a semantic state, while canonical indices
  embed all semantic states.  Cycles in this padded graph are therefore
  proved equivalent to cycles in the original `WindowState` graph, in both
  directions, yielding
  `periodicStripTrominoTilingIndexBool` and a proof that it decides the full
  strip-tiling predicate.  This removes the exponential state enumeration
  from the executable upper-bound algorithm.  The decider uses the already
  certified sufficient depth `21 × binary input length + 1`, avoiding any
  need to compute `Nat.log` in the primitive-recursive program.
- [`LeanTrominoes/StripFrontierIndexedSearchComputability.lean`](LeanTrominoes/StripFrontierIndexedSearchComputability.lean)
  composes on-demand arithmetic decoding directly with the raw transition
  verifier; no exact exponential range calculation is needed by an edge
  check.  Thus the indexed edge predicate consumed by Savitch search is
  primitive recursive without enumerating the state space.  The certified search depth
  `21 × binary input length + 1` is primitive recursive as well, and the
  complete well-formedness-guarded strip tiling decider is now proved
  primitive recursive through the depth-first Savitch driver.
- [`LeanTrominoes/StripFrontierIndexedSearchSpace.lean`](LeanTrominoes/StripFrontierIndexedSearchSpace.lean)
  specializes the flat DFS bound to sparse strip frontiers.  Taking one more
  bit than the certified search depth bounds both every frontier index and
  the depth counter, and substitution of
  `depth = 21 × binary input length + 1` gives an explicit quadratic
  polynomial bounding every reachability configuration, both abstractly and
  in the evaluator backend's actual delimited-`List Nat` tape format.
- [`LeanTrominoes/StripFrontierSpace.lean`](LeanTrominoes/StripFrontierSpace.lean)
  computes the exact semantic frontier-state count as
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
- [`LeanTrominoes/PlanarThreeSATGadgets.lean`](LeanTrominoes/PlanarThreeSATGadgets.lean)
  records the positioned clauses and literal signs of both Figure 8
  primitives.  Exhaustive Lean certificates prove that the duplicator copies
  its center value to all three ports and that the Lichtenstein crossover's
  two Boolean signals propagate independently between opposite ports.
- [`LeanTrominoes/EmbeddedCNFIncidenceDrawing.lean`](LeanTrominoes/EmbeddedCNFIncidenceDrawing.lean)
  packages a finite positioned CNF with variable coordinates and one
  presentation-indexed route per literal.  Its finitely decidable certificate
  checks exact endpoints, orthogonality, continuous route separation,
  endpoint-only contact, vertex-interior avoidance, and distinct graph
  vertices; bridge lemmas recover the membership-style endpoint obligation
  used by the input-dependent periodic routing layer.
- [`LeanTrominoes/OccurrenceSplitRingDrawing.lean`](LeanTrominoes/OccurrenceSplitRingDrawing.lean)
  encodes the worst-case degree-eight neighborhood of Figure 7.  Eight
  occurrence copies lie on an inner square, the implication clauses occupy
  its eight gaps, and the four diagonal old rays bend outside the ring.
  Finite computation certifies all 24 incidences simultaneously: exact
  endpoints, orthogonality, and continuous planarity.  This is the local
  kernel for the geometry-ordered occurrence-splitting substitution.
- [`LeanTrominoes/PeriodicEightOccurrenceSplit.lean`](LeanTrominoes/PeriodicEightOccurrenceSplit.lean)
  gives that geometric kernel a matching periodic Boolean reduction.  Every
  source occurrence selects one of eight compass copies, all eight copies
  remain on the implication ring, and unused copies are harmless.  The
  resulting formula is proved equisatisfiable for every slot assignment;
  it also preserves width three and locality.  The geometric no-collision
  condition is intentionally reserved for the degree-three certificate.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitOccurrences.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitOccurrences.lean)
  isolates that no-collision condition and proves the promised degree
  accounting.  A selected compass copy occurs at most once in the copied
  source clauses, while its fixed implication ring contributes at most two
  occurrences, so every output variable occurs at most three times.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitPortAssignment.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitPortAssignment.lean)
  assigns a chosen rotation order to the eight clockwise Figure 7 ports.
  Whenever every per-variable occurrence list has length at most eight, the
  induced total clause/literal-indexed assignment is proved collision-free.
  This premise is also derived from the standard
  `PeriodicCNF.OccurrencesAtMost 8` predicate.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitOrdered.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitOrdered.lean)
  packages the ordered construction behind that single eight-slot premise.
  It preserves satisfiability, locality, and width three, and a fitting
  rotation order yields the full three-occurrence certificate.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitTerminalPorts.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitTerminalPorts.lean)
  classifies the eight axis and 45-degree terminal rays used by the
  planarization gadgets.  A source certificate that every genuine route has
  one of these directions and separates same-atom incidences is transported
  to the split formula's collision-free and three-occurrence certificates.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitTerminalPortGeometry.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitTerminalPortGeometry.lean)
  characterizes those valid rays as the nonzero vectors on the two axes or
  two 45-degree diagonals, numbers them in the east-first cyclic order used
  by occurrence splitting, and proves that positive integral refinement
  preserves both terminal vectors' directions and complete terminal-port
  certificates.
- [`LeanTrominoes/PeriodicThreeSATThreeAngularOrderSorted.lean`](LeanTrominoes/PeriodicThreeSATThreeAngularOrderSorted.lean)
  proves that the arbitrary integer-ray polar comparator is total and
  transitive, including its zero fallback.  Consequently each stable
  merge-sorted occurrence list is pairwise ordered by its actual terminal
  rays, providing the rotation-system fact needed by the noncrossing local
  fan even when an incidence is not compass-aligned.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitAngularFanOrder.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitAngularFanOrder.lean)
  identifies each angular occurrence-list index with its east-first Figure 7
  port, cyclic port rank, and positioned split-copy vertex.  Increasing list
  indices are also proved to follow the actual polar order of the source
  terminal rays, giving the local fan a direct combinatorial interface.
- [`LeanTrominoes/OccurrenceSplitAngularFanDrawing.lean`](LeanTrominoes/OccurrenceSplitAngularFanDrawing.lean)
  extracts the first `n` east-first Figure 7 spokes together with the full
  implication ring.  All nine possible sizes `0 ≤ n ≤ 8` are mechanically
  certified for exact endpoints, orthogonality, and continuous planarity,
  providing the finite geometric kernel for each angular variable fan.
- [`LeanTrominoes/EmbeddedCNFIncidenceDrawingRenaming.lean`](LeanTrominoes/EmbeddedCNFIncidenceDrawingRenaming.lean)
  transports a complete finite incidence-drawing certificate through an
  injective logical variable renaming whose target placement preserves the
  source coordinates.  Incidence order and routes remain unchanged, while
  injectivity preserves the deduplicated graph-vertex list.
- [`LeanTrominoes/OccurrenceSplitAngularFanInstantiation.lean`](LeanTrominoes/OccurrenceSplitAngularFanInstantiation.lean)
  renames a certified angular fan's ports to the actual
  `copy atom port` variables and translates it into the selected positioned
  source-variable macrocell.  The resulting total variable placement is
  proved identical to the semantic fixed-eight placement, and every fitting
  instance inherits the full finite drawing certificate.
- [`LeanTrominoes/OccurrenceSplitAngularFanBoundary.lean`](LeanTrominoes/OccurrenceSplitAngularFanBoundary.lean)
  exposes one positioned boundary point and one local route suffix for each
  angular occurrence index.  Every suffix is proved orthogonal with exact
  endpoints at that boundary and the selected semantic copy, and is
  identified with the corresponding route of the certified local fan.
  Periodically translated variants correctly lift the boundary and suffix to
  the neighboring occurrence named by a literal's anchor-relative offset.
- [`LeanTrominoes/OrthogonalPolylineJoin.lean`](LeanTrominoes/OrthogonalPolylineJoin.lean)
  joins independently certified route pieces at a shared endpoint while
  removing its duplicate list entry.  The joined route is proved to preserve
  both outer endpoints and any caller-specified chain relation, with
  orthogonality as an immediate specialization, supplying the generic splice
  lemma used by fan and later gadget routing.
- [`LeanTrominoes/OrthogonalPolylineRibbon.lean`](LeanTrominoes/OrthogonalPolylineRibbon.lean)
  introduces directed normal offsets as the replacement for unsound uniform
  diagonal lane translation.  It gives exact endpoint and orthogonality
  infrastructure for offset segments, corner pieces, and their recursive
  composition; the nonoverlapping inside/outside turn geometry used by the
  final construction is refined and certified in the next module.
- [`LeanTrominoes/OrthogonalPolylineUnitSubdivision.lean`](LeanTrominoes/OrthogonalPolylineUnitSubdivision.lean)
  replaces each nondegenerate axis-aligned source segment by its ordered
  lattice points.  It proves exact first and last endpoints, preserves
  orthogonality across joins, and strengthens the result to a chain in which
  every consecutive pair is exactly one genuine cardinal step.  This is the
  discrete interface used to assemble certified ribbon-turn templates across
  adjacent 128-by-128 macrocells.
- [`LeanTrominoes/OrthogonalPolylineEndpointDirections.lean`](LeanTrominoes/OrthogonalPolylineEndpointDirections.lean)
  exposes total first- and last-edge direction lookups for unit orthogonal
  polylines.  Every route with at least one edge receives genuine cardinal
  endpoint directions, and the last lookup is identified with the forward
  direction of any explicitly displayed final edge.  These are the finite
  direction parameters consumed by the ribbon endpoint fans.
- [`LeanTrominoes/OrthogonalPolylineUnitSubdivisionContacts.lean`](LeanTrominoes/OrthogonalPolylineUnitSubdivisionContacts.lean)
  tracks every point introduced by unit subdivision back to either an
  original listed route point or the relative interior of an original
  segment.  It uses that provenance to prove that continuously separated
  original routes whose listed contacts are endpoint-only retain
  endpoint-only contacts after subdivision; in particular, their strictly
  internal unit points are distinct.
- [`LeanTrominoes/OrthogonalPolylineUnitSubdivisionSimplicity.lean`](LeanTrominoes/OrthogonalPolylineUnitSubdivisionSimplicity.lean)
  proves that subdivision of one simple orthogonal route is duplicate-free.
  Each individual segment subdivision is injective, while source point/segment
  and distinct-segment separation exclude every possible duplicate across
  recursively joined segments.  The module also proves that route simplicity
  is preserved by reversal.
- [`LeanTrominoes/PeriodicGridDrawingNoImmediateReversal.lean`](LeanTrominoes/PeriodicGridDrawingNoImmediateReversal.lean)
  turns continuous planarity into the local route condition needed by ribbon
  assembly.  An immediate reversal makes two adjacent open segment interiors
  overlap, contradicting the drawing certificate; consequently every stored
  orthogonal route in a continuously planar drawing has no immediate
  reversal.
- [`LeanTrominoes/OrthogonalPolylineRibbonTurnGeometry.lean`](LeanTrominoes/OrthogonalPolylineRibbonTurnGeometry.lean)
  certifies the finite same-corridor kernel.  At an inside turn the two
  offset lines are trimmed to their intersection; at an outside turn they
  follow the three-point corner rectangle.  Exhaustive checks over all legal
  direction and color cases prove each standard lane simple and every pair
  of red, green, and blue lanes continuously separated.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonMacrocells.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonMacrocells.lean)
  converts that kernel into half-edge tiles for the actual 128-fold
  refinement.  A tile is centered at local coordinate `(64, 64)` in its
  owning `128 × 128` refined block and occupies the 64 units on either side;
  neighboring translated tiles are proved to assign exactly the same point
  to their shared boundary.  Every legal translated tile is rectilinear and
  simple, and its three colored lanes are pairwise continuously separated.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellBounds.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellBounds.lean)
  proves that every tile point and segment stays in its closed owning
  `128 × 128` block, centered at local coordinate `(64, 64)`.  Tiles whose
  source centers differ by at least two lattice units in either coordinate
  cannot share points, contain each other's points in segment interiors, or
  have meeting segment interiors.  Any two finite routes contained in such
  far blocks therefore satisfy the stronger contact-free separation
  predicate; the tile theorem is an immediate specialization.  One
  certified finite check covers all 10,368 pairs of legal tiles at the eight
  nonzero offsets in the surrounding `3 × 3` block, and translation lifts it
  to arbitrary source centers.  An exact equal/far/adjacent trichotomy then
  proves complete separation for any legal tiles with distinct centers.
  Thus only equal-center contacts remain in the global corridor-planarity
  proof.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellContacts.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellContacts.lean)
  classifies every possible advertised-endpoint contact between legal tiles
  at adjacent centers.  An exhaustive exact check proves that contact occurs
  only when both tiles traverse their common source edge in the same
  direction and color; same-entry, same-exit, opposite-direction, and
  different-color coincidences are impossible.  Translation lifts this
  classification from the origin to arbitrary adjacent source centers.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellStrictSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellStrictSeparation.lean)
  turns those exact contact classifications into contact-free separation
  certificates.  Different colors in one legal tile never meet, and tiles
  at distinct centers strictly avoid one another whenever the one classified
  common-directed-edge contact is excluded; distinct colors exclude that
  contact automatically.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceMacrocellSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceMacrocellSeparation.lean)
  excludes that last adjacent-tile contact for interior tiles inherited from
  two source routes whose listed contacts are endpoint-only.  Either possible
  shared boundary would identify one route's internal center with a listed
  neighbor on the other route, contradicting the source separation
  certificate; the resulting strict separation holds for arbitrary colors.
  Companion lemmas handle the singleton core of a one-edge source route and
  prove that same-center exits in different genuine directions are distinct.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonCorridorAssembly.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonCorridorAssembly.lean)
  recursively joins those half-edge tiles along a unit-step source route.
  Under the explicit no-immediate-reversal condition, the assembled core is
  proved rectilinear with exact first and last macrocell-boundary endpoints;
  every join uses the proved equality of the two neighboring half-edge
  boundary points.  A one-edge source route is handled uniformly by the
  single point shared by its two endpoint macrocells.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonCorridorSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonCorridorSeparation.lean)
  proves that the three differently colored cores assembled along one
  duplicate-free unit-step source route are pairwise contact-free.  The
  recursive proof separates each leading tile from all later tiles and then
  composes the four resulting piecewise certificates across both joins.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceCorridorSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceCorridorSeparation.lean)
  retains full-route provenance while recursively comparing every tile in
  two different corridor cores.  Duplicate-freeness makes each displayed
  tile center internal to its complete source route, so endpoint-only source
  contact and the local macrocell theorem give strict separation for
  arbitrary colors.  Separate singleton/long and singleton/singleton cases
  make the specialization unconditional: the colored cores of any two
  unequal active occurrences strictly avoid one another.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonRouteSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonRouteSeparation.lean)
  packages the remaining endpoint geometry without asserting it prematurely.
  Core-versus-core separation is unconditional for every pair of distinct
  colored strands; five endpoint-containing pair types form the exact local
  interface still to prove.  Once supplied, strict separation composes across
  both endpoint joins to separate the complete corrected routes.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointFanSystemSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointFanSystemSeparation.lean)
  lifts the same five obligations to an arbitrary coordinated fan system.
  Together with unconditional core separation, they imply strict separation
  of every pair of distinct complete colored routes selected by that system.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedRouting.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedRouting.lean)
  makes the factor-two padded construction the final normalized corrected
  routing candidate.  Pointwise corrected-route bounds combine with the
  unchanged finite gadget prefixes and clause routes to bound every assembled
  route, proving the open-halo endpoint hypothesis required by the expanded
  finite checker.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonFiniteGeometry.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonFiniteGeometry.lean)
  transfers normalized gadget-vertex distinctness and fundamental-square
  bounds to the corrected ribbon routing.  Because the corrected construction
  retains the standard period and gadget origins, these facts hold
  definitionally.  For the padded final routing it also supplies the proved
  segment-endpoint bounds and packages the exact three remaining executable
  route/route, vertex/route, and continuous-interior checks into global
  continuous assembly geometry.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonCorridorBounds.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonCorridorBounds.lean)
  lifts the closed-block bound from individual ribbon tiles to recursively
  assembled corridor cores.  Every listed core point is assigned to the
  refined block of an actual point on its selected unit source route.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonUnitRoutes.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonUnitRoutes.lean)
  specializes unit subdivision to every active exact-one incidence.  Each
  selected route retains its exact variable and clause endpoints, remains
  rectilinear, has at least two points, and is a chain of genuine unit
  cardinal steps.  Continuous planarity rules out immediate reversals on the
  stored route, and that certificate is proved invariant under reversal,
  periodic rebasing, and unit subdivision.  Ribbon-ready source certificates
  additionally make the unit route duplicate-free, so differently colored
  corridor cores along the same occurrence are pairwise contact-free.  Thus
  each core has exact half-edge boundary endpoints and is unconditionally
  rectilinear for a continuously planar source presentation.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirections.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirections.lean)
  names the genuine cardinal directions in which every active unit route
  leaves its variable and enters its clause.  Ordered unit subdivision is
  proved to preserve both endpoint directions.  The module rewrites the two
  ribbon-core endpoints as the standard exit and entry points of those
  endpoint macrocells, reducing each remaining endpoint fan to finite gadget
  data, color, and one of four directions.
- [`LeanTrominoes/OrthogonalPolylineEndpointDirectionSeparation.lean`](LeanTrominoes/OrthogonalPolylineEndpointDirectionSeparation.lean)
  proves the local topological fact behind endpoint fanout: two
  nondegenerate axis-aligned segments leaving one point in the same direction
  overlap immediately.  Thus continuously separated orthogonal routes that
  share their first or last point must use distinct endpoint directions.  It
  also extracts the basic discrete consequence of endpoint-only contact:
  listed points on two such routes are unequal whenever either point is
  internal.
- [`LeanTrominoes/OrthogonalPolylineElbow.lean`](LeanTrominoes/OrthogonalPolylineElbow.lean)
  supplies horizontal-first and vertical-first one-bend routes for those
  finite endpoint fans.  Coincident or already aligned endpoints are
  simplified so all retained segments are nondegenerate.  Each route has
  certified exact endpoints and orthogonality, and every listed point is an
  endpoint or the single coordinatewise bend; unlike a fresh-coordinate
  detour, it therefore cannot leave the coordinate box of its endpoints.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointFans.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointFans.lean)
  instantiates those elbows between every exact finite-gadget port and its
  direction-dependent ribbon boundary point.  The variable fan approaches
  the boundary parallel to the outgoing source edge, while the clause fan
  leaves it parallel to the incoming edge.  Exhaustive finite checks put
  every possible variable and clause port in the standard block; the elbow
  membership theorem then proves that every translated fan point remains in
  its owning refined block.  Both fans have certified exact endpoints and
  orthogonality.  These independently chosen elbows are geometric candidates,
  not yet a certificate that the three colors respect the cyclic boundary
  order at every source vertex.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointFanSystem.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointFanSystem.lean)
  makes that coordination requirement explicit.  A fan system selects every
  variable- and clause-side stub together and certifies its exact finite
  gadget and corridor endpoints, orthogonality, and containment in the
  endpoint macrocell.  Any such system composes with the certified ribbon
  cores to give the endpoint and orthogonality portions of a
  `ThreeStrandRouting`, and every resulting route point retains an explicit
  endpoint-or-corridor macrocell owner.  The independent one-bend candidates
  are packaged as one such system without asserting the still-missing
  separation property.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonRouting.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonRouting.lean)
  joins the two certified block-local endpoint fans to each corrected
  corridor core.  The complete route is proved to have the exact endpoints
  and orthogonality required by `ThreeStrandRouting`, yielding a normalized
  corrected routing object for the hardness assembly.  Contact-freeness of
  the endpoint fans remains the next geometric layer.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonRoutingBounds.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonRoutingBounds.lean)
  propagates block ownership through both endpoint joins.  Every point of a
  complete corrected colored route lies in the refined block of a listed
  point on its unit source route, including the variable and lifted clause
  endpoint blocks.  Unit subdivision preserves both ordinary and
  upper-margin source halo bounds; with the latter, every complete corrected
  occurrence route lies in the assembled open halo.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirectionSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirectionSeparation.lean)
  specializes endpoint-direction separation to the active exact-one
  incidences.  Unequal occurrences sharing any unitized start leave in
  different directions (in particular, so do occurrences of one variable),
  and unequal occurrences sharing one lifted clause endpoint enter in
  different directions.  These are the finite direction constraints
  available to the remaining noncrossing endpoint-fan construction.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirectionFamilies.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirectionFamilies.lean)
  packages the coordinated local inputs needed by that construction.
  Occurrences at one variable and at one lifted clause target are enumerated
  without duplicates; their outgoing or incoming cardinal directions are
  proved genuine and pairwise distinct.  Variable families are additionally
  bounded by the three available occurrence slots.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitAngularBoundaryRoutes.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitAngularBoundaryRoutes.lean)
  isolates the remaining global obligation for copied source incidences:
  route each copied clause to its angular fan boundary.  Joining any such
  certified prefix with the translated local spoke is proved to give the
  copied literal's exact canonical endpoint while preserving orthogonality.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitAngularSplicedRoutes.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitAngularSplicedRoutes.lean)
  assembles those copied-incidence splices with every certified implication
  ring into one total route family for the final positioned split formula.
  All genuine routes are proved to have exact canonical endpoints and to
  remain orthogonal.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitCanonicalAngularRoutes.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitCanonicalAngularRoutes.lean)
  instantiates the boundary interface unconditionally with canonical
  Manhattan prefixes and specializes the resulting complete angular-spliced
  drawing to the concrete planarized hardness source.  Endpoint compatibility
  and orthogonality are now unconditional; only global nonintersection
  remains.
- [`LeanTrominoes/PlanarThreeSATTerminalPortCertificates.lean`](LeanTrominoes/PlanarThreeSATTerminalPortCertificates.lean)
  packages compass-validity for finite embedded incidence drawings and
  exhaustively certifies every direct incidence of the fixed Figure 8(a)
  duplicator and Figure 8(b) crossover.  Collinear ties are allowed here
  because the later stable angular split separates them into adjacent ports.
- [`LeanTrominoes/PositionedPeriodicCNFDeduplicationTerminalPorts.lean`](LeanTrominoes/PositionedPeriodicCNFDeduplicationTerminalPorts.lean)
  proves that subtracting a retained clause's periodic anchor changes no
  terminal ray.  It reduces the canonical deduplicated source certificate to
  validity and separation checks on the corresponding raw representative
  routes in the finite planar-SAT presentation.
- [`LeanTrominoes/PlanarThreeSATInstantiation.lean`](LeanTrominoes/PlanarThreeSATInstantiation.lean)
  proves that renaming and affine placement preserve the finite gadget
  semantics.  It packages caller-supplied duplicator ports and crossover
  ports with nine fresh internal crossover variables, proving that an
  instantiated crossover extends exactly when its opposite boundary signals
  agree independently.
- [`LeanTrominoes/PlanarThreeSATFamilies.lean`](LeanTrominoes/PlanarThreeSATFamilies.lean)
  concatenates finite families of positioned gadget formulas.  Crossover
  internals are scoped by their canonical site key, and the family semantics
  are proved to be precisely the conjunction of the independent crossover
  propagation or duplicator equality laws at all listed sites.
- [`LeanTrominoes/PlanarThreeSATFamilyExtensions.lean`](LeanTrominoes/PlanarThreeSATFamilyExtensions.lean)
  composes local crossover completeness across the whole finite family:
  an assignment to the external wire variables extends simultaneously to all
  site-scoped internals exactly when both opposite-port equalities hold at
  every listed crossing.
- [`LeanTrominoes/PlanarThreeSATWires.lean`](LeanTrominoes/PlanarThreeSATWires.lean)
  packages the standard two binary implication clauses as a positioned
  equality link.  It proves that a finite link family is satisfied exactly
  when every pair of wire endpoints agrees, including a factoring lemma for
  assignments pulled back from common carrier keys.
- [`LeanTrominoes/PlanarThreeSATWidth.lean`](LeanTrominoes/PlanarThreeSATWidth.lean)
  gives embedded formulas a compositional clause-width predicate.  Renaming,
  affine placement, concatenation, and finite gadget families preserve width,
  and the fixed crossover, duplicator, and equality-link libraries are all
  certified to have width at most three.
- [`LeanTrominoes/PlanarThreeSATOcurrences.lean`](LeanTrominoes/PlanarThreeSATOcurrences.lean)
  gives finite embedded formulas compositional occurrence counts.  Injective
  affine instantiation preserves these counts; exhaustive certificates bound
  every Figure 8 crossover variable by eight occurrences and every
  duplicator variable by six, while a single equality link contributes at
  most four.  A jointly injective site/role naming map preserves a member
  gadget's bound across a noduplicated family, and equality-family counts are
  exactly twice their link-endpoint counts.
- [`LeanTrominoes/PeriodicCNFPlanarOccurrences.lean`](LeanTrominoes/PeriodicCNFPlanarOccurrences.lean)
  proves the componentwise degree-eight bound for the complete finite routed
  planarizer.
  Canonical crossing records and fixed crossover roles are jointly
  injective, so the complete family of crossover gadgets retains the
  exhaustively certified eight-occurrence bound without accumulating across
  sites.  Complete carrier chains are normalized to simple sorted paths;
  adjacent-pair endpoint counting and the disjoint carrier-key partition show
  that every carrier node meets at most two chain links, hence occurs at most
  four times in all complete-carrier equality clauses.  Bend identity and
  endpoint-role arguments show that a terminal meets at most one bend link,
  contributing at most two more occurrences; the entire route-wire family is
  therefore bounded by six.  A target-sensitive family-counting lemma sharpens
  the crossover contribution to two occurrences for external ports, while
  scoped internals never occur in wire clauses.  Splitting on these two
  variable kinds proves that the complete crossover-and-route core has at
  most eight occurrences per variable.  Routed clause terminals are then
  proved duplicate-free, so they contribute at most one occurrence.  The
  variable gadget contains only its active Figure 8(a) equality arms:
  target terminals meet one arm and the central atom meets at most three.
  Finally, constructor-level separation of crossover boundaries, source
  terminals, target terminals, and central atoms gives the complete finite
  planar SAT formula an eight-occurrence certificate (`6 + 1` at source
  terminals and `6 + 2` at target terminals).
- [`LeanTrominoes/PeriodicOrthocrossingCarrierTerminalDegree.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierTerminalDegree.lean)
  sharpens the finite complete-carrier accounting at segment terminals.
  The two directional terminal ports are proved to lie strictly beyond every
  crossover boundary on their translated segment occurrence, including the
  closest possible integer crossing.  Together with the opposite terminal,
  this makes each terminal a strict extreme of the carrier's sorted simple
  node chain.  It follows that a terminal can be an endpoint of at most one
  retained consecutive-pair equality link, improving the generic
  two-link bound at exactly the variables that can collapse under periodic
  translation normalization.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierNormalizationDegree.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierNormalizationDegree.lean)
  performs that periodic quotient for all complete-carrier equality links.
  Distinct normalized links at a fixed terminal inject into one direct-link
  class plus the segment's crossing-bearing translations.  The direct class
  is canonical across neighboring copies, while at most two translations can
  contain canonical crossings.  Hence every terminal prototype has normalized
  link-endpoint degree at most three and occurs at most six times in the
  deduplicated periodic equality formula.
- [`LeanTrominoes/PeriodicOrthocrossingBendNormalizationDegree.lean`](LeanTrominoes/PeriodicOrthocrossingBendNormalizationDegree.lean)
  performs the corresponding periodic quotient for route-bend equalities.
  Erasing a bend record's explicit translation preserves its normalized link,
  and route plus incoming-segment index determine this erased geometry.
  Endpoint orientation then forces all normalized bend links incident to a
  fixed terminal prototype to coincide.  Thus bend deduplication contributes
  at most two occurrences, and the complete normalized route wire has the
  terminal bound `6 + 2 = 8`.
- [`LeanTrominoes/PeriodicOrthocrossingRouteEndpointNormalizationDegree.lean`](LeanTrominoes/PeriodicOrthocrossingRouteEndpointNormalizationDegree.lean)
  sharpens the normalized route-wire bound at the CNF incidence endpoints.
  Source terminals use segment index zero, while every bend's outgoing
  segment has successor index; every bend's incoming segment is likewise
  proved to precede the route's final target segment.  Thus neither endpoint
  prototype occurs in the normalized bend family, leaving only the
  at-most-six complete-carrier occurrences before clause and variable
  attachments are added.
- [`LeanTrominoes/PeriodicCNFPlanarVariableNormalizationDegree.lean`](LeanTrominoes/PeriodicCNFPlanarVariableNormalizationDegree.lean)
  normalizes the active variable-duplicator arms together with their terminal
  and central-atom offsets.  Each normalized arm is determined by its source
  incidence edge, independent of the explicit neighboring translation, so a
  target terminal meets at most one distinct arm and receives at most two
  implication-literal occurrences.  Embedding the normalized carrier formula
  into the full periodic SAT variable type then proves the sharp target
  terminal total `6 + 2 = 8`.
- [`LeanTrominoes/PeriodicCNFPlanarClauseNormalizationDegree.lean`](LeanTrominoes/PeriodicCNFPlanarClauseNormalizationDegree.lean)
  anchor-normalizes the routed source clauses before periodic clause
  deduplication.  All literals at one explicit clause site share its
  translation offset, so normalization yields a zero-offset prototype
  determined only by the original clause index.  Global incidence indices
  make every prototype's terminal atoms duplicate-free and identify at most
  one distinct clause containing a fixed source terminal.  Consequently the
  source attachment contributes one occurrence, and the complete normalized
  external family has sharp endpoint totals seven at sources and eight at
  targets.
- [`LeanTrominoes/PeriodicCNFPlanarAtomNormalizationDegree.lean`](LeanTrominoes/PeriodicCNFPlanarAtomNormalizationDegree.lean)
  bounds the remaining external variable class, the central SAT atoms.
  Distinct normalized active arms at a fixed atom inject into distinct global
  source-incidence indices.  The source formula's three-occurrence hypothesis
  therefore permits at most three arms and six implication-literal
  occurrences.  Route wires and routed source clauses contain no central
  atoms, so the same six-occurrence bound holds for their complete normalized
  external union.
- [`LeanTrominoes/PeriodicCNFPlanarCrossoverNormalizationDegree.lean`](LeanTrominoes/PeriodicCNFPlanarCrossoverNormalizationDegree.lean)
  handles crossover boundaries and internal variables.  Both classes have
  zero normalization offset and a unique finite-variable preimage, so their
  finite degree-eight bounds transfer through periodicization, anchor
  normalization, opaque wrapping, and clause deduplication without
  accumulation.
- [`LeanTrominoes/PeriodicCNFPlanarDeduplicationWrapping.lean`](LeanTrominoes/PeriodicCNFPlanarDeduplicationWrapping.lean)
  proves that opaque variable wrapping commutes exactly with clause-anchor
  normalization and deduplication.  It exposes an equivalent unwrapped
  deduplicated formula for the remaining occurrence accounting, together
  with exact equality of every wrapped and unwrapped variable count.
- [`LeanTrominoes/PeriodicCNFPlanarNormalizationComponents.lean`](LeanTrominoes/PeriodicCNFPlanarNormalizationComponents.lean)
  decomposes the anchor-normalized drawing exactly into crossover,
  straight-carrier, bend, routed-clause, and variable-arm families.  A
  general list lemma then shows that global clause deduplication can only
  reduce occurrences relative to deduplicating these five components
  separately, providing the bridge from local bounds to the actual formula.
- [`LeanTrominoes/PeriodicCNFPlanarComponentNormalizationDegree.lean`](LeanTrominoes/PeriodicCNFPlanarComponentNormalizationDegree.lean)
  transfers the normalized carrier bounds through the full planar-SAT
  variable embedding and proves that an absent indexed segment contributes
  no carrier occurrence.  Crossover, carrier, bend, and routed-clause
  separation then leaves central atoms with only their active-arm family,
  preserving its six-occurrence bound in the componentwise formula.
- [`LeanTrominoes/PeriodicCNFPlanarTerminalNormalizationDegree.lean`](LeanTrominoes/PeriodicCNFPlanarTerminalNormalizationDegree.lean)
  recovers represented route occurrences from normalized source-clause and
  target-arm attachments.  An active attachment excludes the bend family at
  that terminal; otherwise bends contribute at most two occurrences.  With
  at most six complete-carrier occurrences, every normalized terminal
  prototype has degree at most eight.
- [`LeanTrominoes/PeriodicCNFPlanarNormalizationDegree.lean`](LeanTrominoes/PeriodicCNFPlanarNormalizationDegree.lean)
  combines the terminal, central-atom, boundary, and crossover-internal
  estimates.  Global clause deduplication can only decrease their counts,
  and opaque wrapping preserves them exactly, so the actual wrapped
  planar-SAT output has at most eight occurrences of every variable.
- [`LeanTrominoes/PeriodicCNFPlanarEightOccurrenceSplit.lean`](LeanTrominoes/PeriodicCNFPlanarEightOccurrenceSplit.lean)
  applies that degree bound to the routed angular occurrence order.  Its
  east-first compass enumeration matches the absolute starting ray of the
  polar-angle sort and keeps collinear ties in adjacent slots.  Every local
  width-three, occurrence-three source fits the eight Figure 7 compass slots;
  the resulting fixed implication rings have degree three and remain
  satisfiable exactly when the planarized formula is.
- [`LeanTrominoes/PeriodicCNFPlanarEightOccurrenceSplitPositioned.lean`](LeanTrominoes/PeriodicCNFPlanarEightOccurrenceSplitPositioned.lean)
  places those fixed rings in uniform `12 × 12` refinement macrocells using
  the verified Figure 7 copy and implication-clause coordinates.  Erasing
  positions recovers exactly the semantic fixed-eight split, and the refined
  placement retains a positive drawing period.
- [`LeanTrominoes/OccurrenceSplitRingCycleDrawing.lean`](LeanTrominoes/OccurrenceSplitRingCycleDrawing.lean)
  extracts the eight implication clauses as an independently indexed local
  drawing.  Its sixteen routes have exhaustively verified endpoints,
  orthogonality, and continuous planarity, and its erasure is definitionally
  the semantic fixed-eight cycle for any renamed source atom.  A general
  translation-invariance theorem for embedded CNF drawings then places this
  complete certificate at every input-dependent ring macrocell.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitPositionedCycleDrawing.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitPositionedCycleDrawing.lean)
  identifies each positioned atom cycle definitionally with that translated
  template: local compass ports are renamed to the corresponding fixed
  copies, and the refined variable placement agrees exactly with the
  translated local vertices.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitPositionedCycleIndex.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitPositionedCycleIndex.lean)
  carries each flattened cycle clause's source atom and local Figure 7 index
  in a parallel metadata list.  Projecting the metadata recovers the existing
  formula exactly, so global route lookup can select certified local routes
  without arithmetic assumptions about block size.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitPositionedOccurrenceIndex.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitPositionedOccurrenceIndex.lean)
  gives the copied source-clause prefix its matching lossless index bridge.
  Every transformed clause and literal recovers the original positioned
  incidence at the same presentation indices together with the exact angular
  compass copy selected for its endpoint.
- [`LeanTrominoes/PeriodicCNFPlanarEightOccurrenceSplitRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarEightOccurrenceSplitRoutes.lean)
  equips the positioned split with canonical orthogonal incidence detours.
  Their periodic endpoints agree exactly with the refined formula and
  placement.  It also defines the first exact route splice: copied source
  clauses retain those canonical detours, while every appended implication
  cycle selects its translated certified Figure 7 route through the parallel
  metadata index.  The spliced family is proved to retain the complete
  periodic endpoint condition and orthogonality; its remaining obligation is
  global noncrossing geometry for the copied source incidences.
- [`LeanTrominoes/PeriodicCNFPlanarEightOccurrenceTerminalSplit.lean`](LeanTrominoes/PeriodicCNFPlanarEightOccurrenceTerminalSplit.lean)
  assigns the eight copies by their actual routed terminal rays rather than
  by an arbitrary starting point in the cyclic angular order.  The resulting
  semantic and positioned formulas preserve satisfiability, locality, and
  width; their degree-three proof is reduced exactly to validity and
  separation of the physical compass-ray ports.
- [`LeanTrominoes/PlanarOneInThree.lean`](LeanTrominoes/PlanarOneInThree.lean)
  packages Figure 9 as a positioned constant-size replacement for each
  embedded width-three disjunction.  Generated clauses occupy an explicit
  `12 × 12` refinement box and use clause-index-scoped auxiliaries; completeness,
  soundness, and exact finite satisfiability preservation are proved by
  connecting the layout to the verified periodic exact-one truth table.
- [`LeanTrominoes/PlanarOneInThreeFigureNineDrawing.lean`](LeanTrominoes/PlanarOneInThreeFigureNineDrawing.lean)
  realizes every arity-zero-through-three Figure 9 neighborhood as explicit
  rectilinear incidence routes, including the forced-false padding clauses
  needed by short inputs.  Finite exact checkers prove their endpoints,
  orthogonality, route simplicity, vertex avoidance, and continuous pairwise
  planarity; unit elimination remains a separate local replacement.
- [`LeanTrominoes/PlanarOneInThreeNoUnitsDrawing.lean`](LeanTrominoes/PlanarOneInThreeNoUnitsDrawing.lean)
  certifies all four local cases of the subsequent `6 × 6` unit-elimination
  refinement: the empty-clause triangle, unit-clause diamond, and retained
  binary and ternary clauses.  Each exact finite certificate includes
  endpoints, orthogonality, simplicity, vertex avoidance, and continuous
  pairwise planarity.
- [`LeanTrominoes/PlanarOneInThreeOccurrences.lean`](LeanTrominoes/PlanarOneInThreeOccurrences.lean)
  proves that adding Figure 9's positions does not change the underlying
  literal-occurrence list.  The periodic exact-one accounting therefore
  transfers verbatim: original variables retain their occurrence counts and
  every fresh auxiliary occurs at most twice, preserving the 3-occurrence
  bound.
- [`LeanTrominoes/PeriodicCNF.lean`](LeanTrominoes/PeriodicCNF.lean) defines
  the local translation-invariant Boolean formulas used at the beginning of
  that source reduction chain: each finite clause refers to variables at
  integer-lattice offsets, and the finite conjunction is imposed at every
  translate of the plane.
- [`LeanTrominoes/PeriodicThreeCNF.lean`](LeanTrominoes/PeriodicThreeCNF.lean)
  implements the standard auxiliary-variable chain that splits arbitrary
  protoclauses into clauses of width at most three.  Auxiliary variables are
  anchored at the first source-literal offset, and the output is proved to
  preserve the paper's locality condition.
- [`LeanTrominoes/PeriodicThreeCNFCorrectness.lean`](LeanTrominoes/PeriodicThreeCNFCorrectness.lean)
  proves the split equisatisfiable in both directions.  The canonical
  extension makes each chain bit describe whether its unconsumed suffix has a
  true literal; conversely, a verified chain with a true incoming bit must
  expose a true source literal.
- [`LeanTrominoes/PeriodicThreeCNFComputability.lean`](LeanTrominoes/PeriodicThreeCNFComputability.lean)
  names auxiliary variables by their remaining suffix so that the clause
  chain is a direct primitive-recursive list traversal.  It proves the entire
  width-three conversion computable and composes it with the Wang encoding to
  establish co-r.e.-hardness of local periodic 3CNF satisfiability.
- [`LeanTrominoes/PeriodicThreeSATThree.lean`](LeanTrominoes/PeriodicThreeSATThree.lean)
  begins the paper's cycle reduction to periodic 3SAT-3.  It gives every
  syntactic literal occurrence its own variable copy, links the copies of
  each source variable in a directed implication cycle at a common lattice
  offset, and proves that the resulting clauses remain local and of width at
  most three.
- [`LeanTrominoes/PeriodicThreeSATThreeCorrectness.lean`](LeanTrominoes/PeriodicThreeSATThreeCorrectness.lean)
  proves that a satisfied directed cycle forces all occurrence copies to have
  the same cell-by-cell value.  Extending and restricting assignments then
  proves that occurrence splitting preserves periodic satisfiability exactly,
  including presentations with repeated clauses or literals.
- [`LeanTrominoes/PeriodicThreeSATThreeOrdered.lean`](LeanTrominoes/PeriodicThreeSATThreeOrdered.lean)
  parameterizes occurrence splitting by a per-variable permutation of the
  genuine syntactic copies.  Every such cyclic order is proved
  equisatisfiable with the source, allowing the geometric construction to
  follow the rotation order of incident edges around each planar variable
  vertex instead of the unrelated clause-presentation order.
- [`LeanTrominoes/PeriodicThreeSATThreeOrderedPositioned.lean`](LeanTrominoes/PeriodicThreeSATThreeOrderedPositioned.lean)
  lifts the same geometry-selected order to the positioned reduction and its
  variable placement.  Erasing coordinates recovers the ordered semantic
  formula exactly; satisfiability and the occurrence-three bound therefore
  transfer, while presentation order remains a definitional specialization.
- [`LeanTrominoes/PeriodicCNFPlanarOrderedOneInThreePositioned.lean`](LeanTrominoes/PeriodicCNFPlanarOrderedOneInThreePositioned.lean)
  threads that geometric order from the deduplicated routed clause-orbit
  source through the positioned Figure 9 replacement, opaque wrapping, and
  unit-clause elimination.  Erasure, end-to-end satisfiability, the
  occurrence-three bound, and final clause arity two or three are certified
  for every lawful rotation order.
- [`LeanTrominoes/PeriodicThreeSATThreeGeometricOrder.lean`](LeanTrominoes/PeriodicThreeSATThreeGeometricOrder.lean)
  extracts such an order from a planar incidence route family by sorting
  genuine occurrence copies in cyclic order of their terminal segment
  directions.  Merge-sort permutation certifies that no syntactic
  occurrence is introduced or lost, while metadata lookup and route
  orthogonality prove that every genuine occurrence has a final segment with
  a nondegenerate direction, whose rank lies in the four-position cyclic
  range.  The construction is specialized to the deduplicated wrapped routed
  SAT presentation, so every geometric clause vertex represents a distinct
  periodic clause orbit.
- [`LeanTrominoes/PeriodicThreeSATThreeAngularOrder.lean`](LeanTrominoes/PeriodicThreeSATThreeAngularOrder.lean)
  handles the earlier unsplit routed source, whose crossover variables can
  have degree greater than four.  It sorts every genuine occurrence by the
  polar angle of its full terminal ray, uses stable presentation order for
  collinear ties, and proves that sorting preserves exactly the source
  occurrences.  This supplies the cyclic order consumed by occurrence
  splitting without prematurely asserting an orthogonal drawing.
- [`LeanTrominoes/PeriodicCNFPlanarAngularOneInThreePositioned.lean`](LeanTrominoes/PeriodicCNFPlanarAngularOneInThreePositioned.lean)
  specializes the full positioned ordered pipeline to those terminal-ray
  angles.  It fixes the occurrence-split formula and placement, carries them
  through Figure 9 and unit elimination, and proves the resulting exact-one
  source has occurrence degree at most three, clause arity two or three, and
  exactly the original periodic-CNF satisfiability semantics.  Its physical
  period is proved positive, and the canonical detour family supplies
  unconditional endpoint and orthogonality certificates for this concrete
  source; nonintersection remains the geometric obligation.
- [`LeanTrominoes/PeriodicOccurrences.lean`](LeanTrominoes/PeriodicOccurrences.lean)
  defines the finite-presentation literal count used by the paper's
  “each variable occurs at most three times” restriction, and proves that
  this bound is independent of the chosen lawful Boolean equality
  implementation.
- [`LeanTrominoes/PeriodicThreeSATThreeOccurrences.lean`](LeanTrominoes/PeriodicThreeSATThreeOccurrences.lean)
  proves that positional occurrence copies are duplicate-free and that every
  output variable occurs once in the copied source formula and at most twice
  in its implication cycle.  Thus the cycle construction genuinely produces
  periodic 3SAT-3 instances.
- [`LeanTrominoes/PeriodicThreeSATThreeComputability.lean`](LeanTrominoes/PeriodicThreeSATThreeComputability.lean)
  implements indexed list traversal, duplicate removal, and directed
  implication cycles by primitive recursion.  It proves the complete
  occurrence-splitting reduction computable and composes it with the Wang and
  width-three reductions to establish co-r.e.-hardness of local periodic
  3SAT-3.
- [`LeanTrominoes/PeriodicOneInThree.lean`](LeanTrominoes/PeriodicOneInThree.lean)
  defines periodic exact-one satisfaction and the paper's three-clause
  reduction from a width-three disjunction, padding short clauses with fresh
  variables forced false.  Its finite Boolean truth table is verified, and
  the generated formula is proved local and of width at most three.
- [`LeanTrominoes/PeriodicOneInThreeCorrectness.lean`](LeanTrominoes/PeriodicOneInThreeCorrectness.lean)
  gives every source assignment a canonical assignment of the clause-local
  auxiliary variables.  The gadget truth table proves completeness, while
  its converse and the forced-false padding clauses prove soundness; together
  they establish exact preservation of periodic satisfiability.
- [`LeanTrominoes/PeriodicOneInThreeOccurrences.lean`](LeanTrominoes/PeriodicOneInThreeOccurrences.lean)
  formalizes the gadget's incidence accounting.  Each source occurrence is
  preserved once, while every choice, slack, or padding auxiliary occurs at
  most twice, so the reduction takes periodic 3SAT-3 instances to periodic
  1-in-3SAT-3 instances.
- [`LeanTrominoes/PeriodicOneInThreeNoUnits.lean`](LeanTrominoes/PeriodicOneInThreeNoUnits.lean)
  removes the unit clauses used to pin Figure 9's padding variables.  A unit
  literal is forced by one ternary and one binary exact-one clause, while an
  empty clause maps to an unsatisfiable triangle of binary clauses.  The
  translation preserves periodic satisfiability exactly and, on width-three
  inputs, leaves every clause with arity two or three while preserving
  locality.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsOccurrences.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsOccurrences.lean)
  proves that unit elimination preserves every original occurrence count
  exactly and uses each clause-local auxiliary at most twice.  Consequently
  the transformation preserves the occurrence-three restriction needed by
  the six-triple variable gadget.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMTyped.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMTyped.lean)
  assembles the typed periodic 3DM presentation: six triples and alternating
  red/green elements per occurring variable, paired literal/complement blue
  ports, one red/green clause core and auxiliary triple per literal, and
  degree-two blue caps for unused slots.  Variable-to-clause references use
  the negated literal offset, with a checked coordinate-cancellation lemma.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMSemantics.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMSemantics.lean)
  defines direct periodic exact-cover semantics for the typed presentation,
  together with typed well-formedness and degree-two-or-three predicates.
  Incidence values use the same translated-cell convention as
  `PeriodicThreeDM`, including a verified reversed-offset calculation.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMOccurrences.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMOccurrences.lean)
  proves the occurrence-slot bookkeeping: tagged clause/literal positions are
  duplicate-free, filtering by atom has exactly the ordinary occurrence
  count, and the occurrence-three bound assigns every tagged literal to one
  unique pair of complementary variable ports.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMWellFormed.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMWellFormed.lean)
  proves that every generated triple reference names an element in the
  corresponding finite typed red, green, or blue list.  In particular,
  variable ports distinguish valid clause cores, occurrence-specific
  complements, and the private caps of unused slots.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMEncode.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMEncode.lean)
  compiles each typed color class to natural-number indices and produces a
  concrete `PeriodicThreeDM`.  Typed well-formedness proves that all three
  references of every encoded triple are strictly within their declared
  color counts.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMMatching.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMMatching.lean)
  defines the canonical triple selection induced by an exact-one assignment.
  Variable cycles are proved to take an alternating matching, literal and
  complementary ports carry opposite truth values at the correctly translated
  variable cell, and clause auxiliaries repeat their source literals.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMNodup.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMNodup.lean)
  proves that the typed red, green, blue, and triple prototype lists are all
  duplicate-free.  Consequently the natural-number encoding gives every
  declared prototype a unique `idxOf` position instead of merging names.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMAssignmentEncoding.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMAssignmentEncoding.lean)
  transports matching assignments between typed triples and natural-number
  prototype indices.  The two transports are proved inverse on every declared
  typed triple and every valid numbered index.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMMatchingSoundness.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMMatchingSoundness.lean)
  recovers a Boolean assignment from the top-left port of each arbitrary valid
  variable-cycle matching.  The six-cycle classification then proves that
  every literal port is the recovered literal truth value and every paired
  port is its complement; a clause gadget recovers the exact-one clause.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMVariableIncidences.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMVariableIncidences.lean)
  proves that the typed incidence enumerator gives every internal red and
  green variable element exactly the two neighbors in the symbolic six-cycle,
  at zero offset.  Thus exact cover on those elements implies the verified
  `VariableGadgetHolds` predicate.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMClauseIncidences.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMClauseIncidences.lean)
  proves that each clause-core red and green element sees exactly its
  zero-offset auxiliary triples, with one incidence per tagged literal in
  source order.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMBlueClauseIncidences.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMBlueClauseIncidences.lean)
  classifies every main clause-blue incidence by variable and occurrence
  slot: precisely the literal-side port of each occurrence in that clause is
  retained, with the reversed source-literal offset.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMBlueComplementIncidences.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMBlueComplementIncidences.lean)
  classifies an occurrence-specific complement blue element as the opposite
  variable port followed by the matching zero-offset clause auxiliary in the
  stable typed enumeration.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMBlueUnusedIncidences.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMBlueUnusedIncidences.lean)
  proves that a private cap for an unused occurrence slot has exactly the two
  complementary variable-port incidences, both at zero offset.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMBlueComplementUnique.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMBlueComplementUnique.lean)
  uses uniqueness of tagged clause/literal positions and occurrence slots to
  prove that every genuine complement blue element has exactly two
  incidences: one opposite variable port and one clause auxiliary.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMMainClauseOccurrences.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMMainClauseOccurrences.lean)
  proves that variable/slot order and source-clause literal order enumerate
  the same main-blue tagged occurrences up to permutation whenever every
  variable occurs at most three times.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMClauseOccurrenceValues.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMClauseOccurrenceValues.lean)
  reconnects a valid filtered tagged-occurrence list to its source clause and
  proves that their literal truth-value lists are permutations, preserving
  the exact-one predicate.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMMainClauseValues.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMMainClauseValues.lean)
  proves that the canonical matching's actual main clause-blue incident
  values are a permutation of the corresponding source clause truth values.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMTypedCompleteness.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMTypedCompleteness.lean)
  assembles all typed incidence cases and proves the forward correctness
  direction: every satisfying occurrence-three exact-one assignment induces
  a perfect matching of the typed periodic 3DM construction.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMTypedSoundness.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMTypedSoundness.lean)
  recovers a Boolean assignment from any typed perfect matching, proves every
  source clause exact-one, and concludes satisfiability equivalence for the
  typed reduction under the occurrence-three bound.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMDegree.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMDegree.lean)
  proves the typed construction's degree-two-or-three condition from the
  occurrence-three bound and the source formula's unit-free arity-two-or-three
  invariant.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMEncodingSemantics.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMEncodingSemantics.lean)
  begins the semantic bridge to natural-number `PeriodicThreeDM`, proving
  generically that numbered incidence enumeration is a permutation of the
  corresponding duplicate-free typed incidence list.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMEncodingCorrectness.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMEncodingCorrectness.lean)
  specializes the encoding bridge to red, green, and blue and proves incident
  truth-value permutations for both encoded typed assignments and decoded
  natural-number assignments.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMEncodedSatisfiability.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMEncodedSatisfiability.lean)
  transports exact cover in both directions, proving the encoded
  `PeriodicThreeDM` instance (and its abstract trichromatic orientation
  problem) satisfiable exactly when the occurrence-three source is.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMReductionCorrectness.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMReductionCorrectness.lean)
  composes unit elimination with encoded 3DM, proves the resulting typed
  instance has degree two or three, and preserves exact-one satisfiability
  and abstract trichromatic orientability.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsComputability.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsComputability.lean)
  proves that the reviewed empty- and unit-clause elimination is primitive
  recursive, both clause by clause and over a complete periodic formula.
- [`LeanTrominoes/PeriodicThreeDMComputability.lean`](LeanTrominoes/PeriodicThreeDMComputability.lean)
  supplies canonical primitive-recursive encodings for natural-number
  periodic 3DM references, triples, and complete finite presentations.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMEnumerationComputability.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMEnumerationComputability.lean)
  proves primitive recursiveness of the typed reduction's occurring-variable,
  unused-slot, colored-element, and prototype-triple enumerations.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMEncodingComputability.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMEncodingComputability.lean)
  proves that typed reference calculation, first-index numbering, complete
  natural-number 3DM encoding, and its unit-free composition are computable.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMEncodedDegree.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMEncodedDegree.lean)
  transports typed incidence degrees through the natural-number encoding and
  proves that the complete unit-free output has degree two or three.
- [`LeanTrominoes/PeriodicThreeDMHardness.lean`](LeanTrominoes/PeriodicThreeDMHardness.lean)
  composes the computable Wang reduction through exact-one SAT and unit-free
  encoded 3DM, proving co-r.e.-hardness for well-formed periodic 3DM of degree
  two or three and for its equivalent abstract trichromatic orientation.
- [`LeanTrominoes/PeriodicOneInThreeComputability.lean`](LeanTrominoes/PeriodicOneInThreeComputability.lean)
  and
  [`LeanTrominoes/PeriodicOneInThreeClauseComputability.lean`](LeanTrominoes/PeriodicOneInThreeClauseComputability.lean)
  give primitive-recursive implementations of every exact-one gadget and of
  the complete short-clause case split.  The latter uses indexed lookup with
  fresh-padding defaults, proved extensionally equal to the declarative
  pattern match.
- [`LeanTrominoes/PeriodicOneInThreeReductionComputability.lean`](LeanTrominoes/PeriodicOneInThreeReductionComputability.lean)
  maps the clause gadget over the indexed periodic presentation and proves
  the full conversion computable.  Composing it with the Wang-to-periodic-
  3SAT-3 chain establishes co-r.e.-hardness of local periodic 1-in-3SAT-3.
- [`LeanTrominoes/PeriodicThreeDM.lean`](LeanTrominoes/PeriodicThreeDM.lean)
  defines periodic 3-dimensional matching by translated red, green, and blue
  element references.  It proves the semantic core of Theorem 3.8: selecting
  triples to cover each element exactly once is equivalent to directing every
  triple's three incidences coherently while exactly one incidence points
  into each colored element.
- [`LeanTrominoes/PeriodicThreeDMGraph.lean`](LeanTrominoes/PeriodicThreeDMGraph.lean)
  compiles periodic 3DM into its colored bipartite periodic incidence graph.
  The graph is well formed whenever all element references are in range, its
  colored-element graph degrees are exactly the corresponding 3DM degrees,
  and a well-formed degree-two-or-three instance has ordinary maximum degree
  three, as required by the drawing construction.  The edge list is proved
  index-for-index equal to the separately retained colored incidence tags.
- [`LeanTrominoes/PeriodicThreeDMGraphOrientation.lean`](LeanTrominoes/PeriodicThreeDMGraphOrientation.lean)
  expresses orientations directly as values on those colored incidence-edge
  orbits.  It proves this tagged graph presentation equivalent to the
  triple/color presentation and therefore proves that perfect periodic 3D
  matchings are exactly valid 1-in-3/0-or-3 orientations of the incidence
  graph.
- [`LeanTrominoes/PeriodicThreeDMContractionSemantics.lean`](LeanTrominoes/PeriodicThreeDMContractionSemantics.lean)
  isolates the degree-two contraction used by Theorem 3.8.  At a suppressed
  colored vertex, the two former incidence values become the opposite
  endpoint values of one directed wire; degree-three colored vertices retain
  their exact-one constraint.  Under the degree-two-or-three promise this
  transformed orientation problem is proved equivalent to periodic 3DM.
- [`LeanTrominoes/PeriodicThreeDMContraction.lean`](LeanTrominoes/PeriodicThreeDMContraction.lean)
  makes that contraction executable.  Degree-three elements retain their
  three colored incidence edges, while each degree-two element becomes one
  colored edge between its two incident triples with the correct periodic
  offset.  Every edge retains its original incidence tags for later route
  concatenation and orientation transport.
- [`LeanTrominoes/PeriodicThreeDMContractionOrientation.lean`](LeanTrominoes/PeriodicThreeDMContractionOrientation.lean)
  transports a suppressed 3DM orientation to the actual endpoints of the
  executable contracted edges.  It proves that every emitted retained or
  through edge has opposite inward endpoint values at the correct periodic
  translates, that retained degree-three element endpoints satisfy exact
  one, and that the triple-endpoint values remain trichromatically coherent.
- [`LeanTrominoes/PeriodicThreeDMContractionDrawing.lean`](LeanTrominoes/PeriodicThreeDMContractionDrawing.lean)
  retrieves original planar routes by their unique incidence tags and
  realizes every contracted edge geometrically.  Retained routes are reused;
  for a suppressed element, the second route is period-translated, reversed,
  and joined to the first at their common colored endpoint.  The resulting
  polyline is proved to have exactly the contracted edge's periodic
  endpoints; restricted vertex positions remain distinct and inside the
  fundamental square, completing compatibility with the executable
  contracted graph.
- [`LeanTrominoes/PeriodicThreeDMContractionCoverage.lean`](LeanTrominoes/PeriodicThreeDMContractionCoverage.lean)
  reconciles the contracted graph's element-major edge order with the
  original graph's triple-major incidence order.  Under the well-formed
  degree-two-or-three promise, flattening the tags stored on contracted edges
  is a duplicate-free permutation of all original incidence tags, so every
  original route is consumed exactly once; the endpoint-opposition law is
  also lifted from one element block to every executable contracted edge.
- [`LeanTrominoes/PeriodicThreeDMContractionGeometry.lean`](LeanTrominoes/PeriodicThreeDMContractionGeometry.lean)
  proves the first geometric invariant of contraction: translating,
  reversing, and joining the original incidence polylines preserves
  orthogonality, so the complete compatible contracted drawing remains
  orthogonal.
- [`LeanTrominoes/PeriodicThreeDMContractionPlanarity.lean`](LeanTrominoes/PeriodicThreeDMContractionPlanarity.lean)
  records segment-level provenance for every retained and through route.
  Joining is proved to introduce no segment, while translation and reversal
  realize each contracted segment from its unique original incidence segment.
  The provenance enumeration is index-for-index equal to the contracted
  drawing's indexed segments, and its original occurrence-key map is
  injective under the degree promise.  Periodic translation and optional
  reversal preserve closed and relative-interior containment, which transfers
  both route-interior avoidance and vertex-interior avoidance from the
  original presentation.  Thus the complete contracted drawing is certified
  planar.
- [`LeanTrominoes/PeriodicContinuousPlanarThreeDM.lean`](LeanTrominoes/PeriodicContinuousPlanarThreeDM.lean)
  strengthens the planar 3DM presentation interface with exact continuous
  relative-interior separation between distinct lifted route segments.
- [`LeanTrominoes/PeriodicThreeDMContractionContinuousPlanarity.lean`](LeanTrominoes/PeriodicThreeDMContractionContinuousPlanarity.lean)
  proves that degree-two contraction preserves this stronger certificate.
  Reversing a segment is shown not to change continuous interior
  intersection, and segment provenance transports any alleged contracted
  overlap to two distinct original occurrences, contradicting the source
  certificate.
- [`LeanTrominoes/PeriodicPlanarThreeDM.lean`](LeanTrominoes/PeriodicPlanarThreeDM.lean)
  defines the geometric certificate still required for planar hardness: a
  compatible orthogonal drawing of the periodic 3DM incidence graph whose
  lifted routes avoid every other route interior and every lifted vertex.
  The certificate retains route colors through the verified edge/tag ordering
  and packages the degree-two-or-three restriction.
- [`LeanTrominoes/PlanarThreeDMVariableGadget.lean`](LeanTrominoes/PlanarThreeDMVariableGadget.lean)
  transcribes the six-triple variable gadget of Figure 10(a), including its
  planar coordinates and open blue interface ports.  An exhaustive finite
  truth table proves that covering its internal red and green elements permits
  exactly the two alternating selections encoding the variable's truth value.
- [`LeanTrominoes/PlanarX3CClauseGadget.lean`](LeanTrominoes/PlanarX3CClauseGadget.lean)
  transcribes the nine-set clause core in Figure 5 of the Dyer--Frieze planar
  3DM reduction.  Its twelve elements, incidence lists, degrees, and triangular
  coordinates are explicit.  It records and verifies an explicit coloring in
  which every set and every three-element terminal contains one red, one
  green, and one blue element.  The canonical local covers `EFI`, `BDH`, and
  `ACG` are defined explicitly for their three external terminal choices.
  A machine-checked exhaustive truth table
  proves that the internal elements and all nonexternal terminal elements
  have an exact cover precisely when exactly one terminal is covered
  externally.
- [`LeanTrominoes/PlanarX3CClauseDrawing.lean`](LeanTrominoes/PlanarX3CClauseDrawing.lean)
  gives the nine-set clause core an explicit orthogonal drawing: an
  eighteen-vertex boundary cycle and three disjoint internal tripods.  The
  exact checker proves continuous planarity and records the three boundary
  terminal orders needed for noncrossing colored-strand attachment.
- [`LeanTrominoes/PlanarThreeDMConnectorGadget.lean`](LeanTrominoes/PlanarThreeDMConnectorGadget.lean)
  transcribes the fixed-red connector detour in Dyer--Frieze Figure 6 as a
  planar two-by-three ladder and one auxiliary triple.  Every triple has an
  explicit red, green, and blue reference, every internal element has degree
  two, and its complete seven-bit truth table proves that the connector's
  three colored ports carry one common all-or-none state while its two
  variable-cycle continuation ports remain complementary.
- [`LeanTrominoes/PlanarThreeDMVariableOccurrenceGadget.lean`](LeanTrominoes/PlanarThreeDMVariableOccurrenceGadget.lean)
  gives the ordinary three-triple occurrence modules with fixed-green and
  fixed-blue terminals.  Both variants use red continuation ports and have
  explicit trichromatic references.  Their exhaustive truth table proves the
  same all-or-none RGB-terminal contract as the fixed-red detour, so the three
  module kinds cover every terminal order needed by the colored clause core.
- [`LeanTrominoes/LocalIncidenceDrawing.lean`](LeanTrominoes/LocalIncidenceDrawing.lean)
  defines finite orthogonal incidence-drawing certificates with exact
  continuous tests for collinear overlap, route simplicity, endpoint-only
  contact, vertex-interior avoidance, and injective positions for all
  vertices in both parts of the incidence graph.
- [`LeanTrominoes/PlanarThreeDMConnectorDrawings.lean`](LeanTrominoes/PlanarThreeDMConnectorDrawings.lean)
  supplies explicit orthogonal routes for both ordinary occurrence modules
  and the fixed-red detour.  Finite computation verifies every advertised
  endpoint and proves all three connector drawings continuously planar.  A
  second family of outer-face templates exposes all five degree-one ports and
  puts the two polarity-normalized cycle ports at the common coordinates
  `(4, 0)` and `(12, 0)`.
- [`LeanTrominoes/PlanarThreeDMVariableSiteDrawing.lean`](LeanTrominoes/PlanarThreeDMVariableSiteDrawing.lean)
  places one, two, or three selected occurrence modules above a common port
  line and closes their red continuations on private lanes below it.  The
  actual shared cycle-link elements are identified in the finite incidence
  graph, and exhaustive computation certifies a planar orthogonal drawing
  for every connector-kind and polarity pattern.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMVariableSiteDrawing.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMVariableSiteDrawing.lean)
  identifies the periodic reduction's occurrence slots with those finite
  drawing slots and instantiates the checked one-, two-, or three-module
  site at every occurring source variable.  Every listed periodic
  variable triple is packaged as an active finite triple, with exact route
  endpoints and orthogonality inherited from the exhaustive local
  certificate.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMThreeStrandRouting.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMThreeStrandRouting.lean)
  isolates the topological thickening step that turns one exact-one
  incidence into three distinct RGB corridors.  Its certificate fixes the
  physical period and variable/clause gadget origins, then requires exact
  endpoints from the checked variable-site ports to the correctly
  translated clause-terminal positions, together with rectilinearity of
  every strand.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMThreeStrandConstruction.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMThreeStrandConstruction.lean)
  provides the original endpoint-and-orthogonality prototype.  It positively
  refines and uniformly shifts each source route, then joins it to the checked
  variable and clause ports.  This establishes the assembly interfaces and
  coordinate bookkeeping, but its diagonal shifts are not used as a
  noncrossing theorem: bends require the corrected ribbon construction below.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonCorridors.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonCorridors.lean)
  instantiates the corrected normal-offset construction for the three 3DM
  colors at lane distances `40`, `44`, and `48` inside each `128`-cell
  refinement corridor.  Every genuine rebased source incidence is proved
  nondegenerate, and each resulting central lane has exact computed
  variable/clause-side endpoints and is orthogonal.  Noncrossing endpoint
  fans into the finite gadgets remain separate from this central-corridor
  theorem.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMVertexGeometry.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMVertexGeometry.lean)
  chooses concrete variable-site and clause-core templates centered in the
  same `128 × 128` block as each ribbon tile and certifies the complete finite
  coordinate range of every template vertex.  Every assembled vertex is
  expressed as its source incidence vertex plus an
  open-macrocell offset.  Source compatibility and zero-anchor normalization
  therefore prove, unconditionally, that all assembled vertices remain
  strictly inside the refined fundamental square.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRouteBounds.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRouteBounds.lean)
  completes the corresponding route-coordinate proof.  Exhaustive checks
  bound every finite variable-site and clause-core route, while pointwise
  bounds on a reversed-and-rebased source incidence control all three refined
  RGB lanes.  One-unit upper margins handle the canonical endpoint detours,
  and the bounds lift through every splice and encoded incidence to prove the
  assembled drawing's indexed segment endpoints lie in the one-cell halo.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMVariableSiteElements.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMVariableSiteElements.lean)
  identifies every listed typed red, green, and blue variable-side element
  with an active element of the exhaustively checked complete variable-site
  drawing.  The corresponding macrocell offsets are proved equal, exposing
  the finite drawing's injective-position certificate to the global
  distinctness proof.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMVertexDistinctness.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMVertexDistinctness.lean)
  tags the four assembled vertex families uniformly.  Source drawing
  injectivity separates different owner macrocells, while the exhaustive
  variable-site and X3C clause-core certificates separate vertices within
  one owner.  Consequently the complete normalized assembled position list
  is duplicate-free.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMFiniteGeometry.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMFiniteGeometry.lean)
  reduces the remaining infinite periodic planarity field to an executable
  finite certificate: all stored segment endpoints lie in the one-cell halo,
  the route/route checks pass over 25 relative translations, and the
  vertex/route check passes over the nine neighboring translates.  For the
  normalized halo-bounded construction, endpoint bounds are now discharged
  automatically by the route-coordinate theorem.  Thus exactly three finite
  Boolean checks remain: route/vertex avoidance, route/route interior
  disjointness, and the exact collinear-interior refinement.  Passing those
  checks combines with the established vertex distinctness and bounds to
  produce the stronger 3DM presentation needed by degree-two contraction
  without overlooking coincident unit segments.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMGlobalPositions.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMGlobalPositions.lean)
  translates every typed triple and colored element from its checked
  variable-site or clause-core template into the reserved global gadget
  neighborhood.  It emits these coordinates in exactly the
  triple/red/green/blue vertex order of the encoded 3DM incidence graph and
  proves the resulting list has the required length.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMGlobalRoutes.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMGlobalRoutes.lean)
  emits one route per encoded RGB incidence in triple-major order.  Local
  clause and complete-variable-site routes are translated into their global
  neighborhoods, while exactly the classified routed connector incidence
  is joined to its three-strand corridor.  The resulting list has the
  encoded edge count, every assembled route is proved rectilinear, and
  tag-indexed lookup proves its endpoints are exactly the corresponding
  global typed triple and periodically translated colored element.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMGlobalDrawing.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMGlobalDrawing.lean)
  packages those typed positions and routes as the numeric periodic grid
  drawing of the encoded 3DM incidence graph.  Four-block vertex lookup and
  incidence-tag route lookup prove full graph endpoint compatibility, while
  a separate global geometry certificate isolates the remaining
  distinctness, fundamental-square, and periodic-planarity obligations.
- [`LeanTrominoes/PlanarThreeDMVariableConnectorBoundary.lean`](LeanTrominoes/PlanarThreeDMVariableConnectorBoundary.lean)
  packages the fixed-red, fixed-green, and fixed-blue modules behind one
  boundary relation.  Exhaustive checks of the actual finite gadgets prove
  that each kind realizes exactly two boundaries: complementary red
  continuation states and one common RGB connector state.  Reflecting the
  continuation attachment formalizes Figure 4 negation, making that signal
  equal to `variable == polarity`.
- [`LeanTrominoes/PlanarThreeDMVariableCycle.lean`](LeanTrominoes/PlanarThreeDMVariableCycle.lean)
  closes one, two, or three occurrence modules with degree-two red
  continuation elements, covering the source's three-occurrence bound.  The
  assembly theorems prove that every connector-kind sequence has exactly two
  cycle phases.  The signed versions classify every occurrence terminal as
  the corresponding source literal value of one common variable assignment.
- [`LeanTrominoes/PlanarThreeDMGadgetSemantics.lean`](LeanTrominoes/PlanarThreeDMGadgetSemantics.lean)
  matches the three noncrossing clause-terminal orders to the fixed-red,
  fixed-blue, and fixed-green connector kinds and composes their contracts.
  It proves that three connected terminals implement exact-one, that leaving
  one degree-two terminal unconnected implements the two-literal case, and
  that substituting signed variable-cycle signals recovers the source literal
  clauses exactly.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTyped.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTyped.lean)
  assembles those local gadgets into an inspectable typed periodic 3DM
  presentation.  Used occurrence slots are closed cyclically by red
  continuation elements; connector kind and polarity come from the source
  literal; RGB connector ports are identified with the correctly ordered
  clause terminal at the reversed literal offset; and every clause receives
  the nine colored core triples.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMSemantics.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMSemantics.lean)
  defines translated typed incidences, perfect-matching semantics,
  well-formedness, and the degree-two-or-three invariant for that
  presentation.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMWellFormed.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMWellFormed.lean)
  proves every listed ordinary connector, fixed-red detour, and clause-core
  triple references declared colored elements.  In particular, it verifies
  that signed continuation swaps preserve membership in each finite
  variable cycle.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEnumeration.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEnumeration.lean)
  packages the nested variable/used-slot order as a duplicate-free module
  enumeration and relates its flat-map back to the actual triple list.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMPrivateIncidences.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMPrivateIncidences.lean)
  localizes the global incidence filters for ordinary fixed-green and
  fixed-blue modules, proving that each of their private colored elements
  has exactly the two advertised local incidences.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMFixedRedIncidences.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMFixedRedIncidences.lean)
  performs the analogous global check for all eight private elements of the
  seven-triple fixed-red detour.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMClauseInternalIncidences.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMClauseInternalIncidences.lean)
  proves that each colored internal element of every assembled Figure 5
  clause core has exactly its three local incidences.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMCycleLinkIncidences.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMCycleLinkIncidences.lean)
  proves every used red variable-cycle link has degree two, for all one-,
  two-, and three-occurrence cycles and both literal polarities.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMOccurrenceCorrespondence.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMOccurrenceCorrespondence.lean)
  proves that the assembled variable/used-slot module order is a
  duplicate-free permutation of the source tagged-literal order under the
  occurrence-three bound, including its restriction to each clause
  terminal.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTerminalOccurrenceCounts.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTerminalOccurrenceCounts.lean)
  derives the zero-or-one source occurrence count at every clause terminal:
  arity-two clauses leave the right terminal unused, while arity-three
  clauses use all three.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMVariableTerminalIncidences.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMVariableTerminalIncidences.lean)
  verifies that every assembled occurrence contributes exactly one
  incidence of each color to its selected clause terminal, so variable-side
  terminal incidence counts equal the source occurrence counts.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMClauseTerminalIncidences.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMClauseTerminalIncidences.lean)
  adds the two local Figure 5 incidences at each colored terminal, yielding
  total terminal degree two or three.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMDegree.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMDegree.lean)
  combines every element classification to prove the complete typed
  assembly has degree two or three under the source occurrence and arity
  bounds.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMMatching.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMMatching.lean)
  defines the canonical periodic matching induced by a source assignment.
  Ordinary and fixed-red occurrence modules use their verified alternating
  selections, while each clause translate chooses its explicit `EFI`,
  `BDH`, or `ACG` core cover from the three signed terminal signals.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMClauseSignals.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMClauseSignals.lean)
  proves that a binary source clause presents its two literal truth values
  and a false unused right terminal, while a ternary clause presents all
  three truth values.  Source exact-one satisfaction therefore supplies the
  exact boundary condition required by the canonical clause-core cover.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTerminalValues.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTerminalValues.lean)
  strengthens variable-side terminal incidence counting to an equality of
  Boolean value lists: every RGB occurrence incidence carries exactly its
  signed source literal truth value at the correctly translated cell.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTerminalCovers.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTerminalCovers.lean)
  combines those variable values with the two local Figure 5 incidences.
  It proves every colored terminal is covered exactly once, including the
  binary clause's unused right terminal where the absent variable incidence
  is represented by the clause core's false external signal.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMCycleLinkCovers.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMCycleLinkCovers.lean)
  proves that each occurrence contributes the variable phase to its own
  red cycle link and the complementary phase to its successor, independently
  of sign and connector kind.  Closing the one-, two-, or three-module cycle
  therefore covers every link exactly once.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTypedCompleteness.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTypedCompleteness.lean)
  assembles the private-element, cycle-link, clause-internal, and merged
  terminal cases.  Every satisfying occurrence-three, arity-two-or-three
  exact-one assignment now induces a perfect matching of the complete typed
  planar 3DM presentation.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMLocalSoundness.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMLocalSoundness.lean)
  restricts any perfect matching back to the finite gadgets: every ordinary
  occurrence module and fixed-red detour satisfies its verified private
  constraints, and every clause core satisfies all three internal
  exact-cover constraints.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMVariableSoundness.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMVariableSoundness.lean)
  reads each occurrence module as a signed connector boundary.  Coverage of
  the red cycle links synchronizes the first boundary field across all used
  slots, yielding a recovered source assignment whose literal value equals
  every occurrence connector signal.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMMatchingTerminalValues.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMMatchingTerminalValues.lean)
  propagates that recovered literal value through every connector variant
  and color.  Consequently the variable-side incidences selected by an
  arbitrary perfect matching at each merged clause terminal are exactly the
  truth values of its corresponding source occurrences.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTypedSoundness.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTypedSoundness.lean)
  combines those arbitrary variable-side values with the global terminal
  covers and local clause-core covers.  The Figure 5 truth table then forces
  each recovered binary or ternary source clause to satisfy exact-one,
  completing the typed satisfiability equivalence.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMNodup.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMNodup.lean)
  proves that the assembled prototype triples and each of the three colored
  element lists are duplicate-free.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEncode.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEncode.lean)
  assigns those typed prototypes faithful natural-number names, proves all
  encoded references are in range, and defines matching round trips.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEncodingSemantics.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEncodingSemantics.lean)
  proves that numbered and typed incidence enumerations agree up to
  permutation.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEncodingCorrectness.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEncodingCorrectness.lean)
  transports the incidence permutations through encoded and decoded
  matching assignments for all three colors.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEncodedSatisfiability.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEncodedSatisfiability.lean)
  proves that the natural-number instance has a perfect matching (or graph
  orientation) exactly when the source exact-one formula is satisfiable.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEncodedDegree.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEncodedDegree.lean)
  transfers the typed degree-two-or-three invariant to the natural-number
  periodic 3DM instance.
- [`LeanTrominoes/PeriodicPlanarThreeDMIncidenceRouting.lean`](LeanTrominoes/PeriodicPlanarThreeDMIncidenceRouting.lean)
  reorients each certified exact-one incidence route into the offset
  convention used by the 3DM assembly.  Reversing the clause-to-variable
  route and translating by `anchor - literal.offset` produces an orthogonal
  variable-to-clause route from the variable prototype at cell zero to the
  displayed clause gadget at the negated literal offset, with both endpoints
  proved exactly.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMNormalized.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMNormalized.lean)
  fixes the exact normalized source and natural-number 3DM target for the
  geometric assembly.  It packages well-formedness, colored degree two or
  three, perfect-matching and graph-orientation equivalence to the original
  exact-one source, and the transported routed incidence presentation,
  including the halo bounds and endpoint-only contact certificate needed by
  ribbon thickening.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRoutedTriples.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRoutedTriples.lean)
  identifies, for every used occurrence slot and color, the unique typed
  triple whose terminal incidence leaves the variable gadget.  It proves
  membership and stable natural-number indices, the exact encoded terminal
  reference and reversed offset, correspondence with flattened CNF incidence
  metadata, and recovers the certified route and its two endpoints for every
  occurrence entry.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMIncidenceClassification.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMIncidenceClassification.lean)
  assigns every typed triple and colored element to a variable or clause
  gadget site.  It proves that every colored incidence of every listed triple
  is either local to one site with zero offset or exactly one of the routed
  occurrence incidences, giving the geometric assembly an exhaustive splice
  interface.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMLocalDrawings.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMLocalDrawings.lean)
  exposes all three verified finite templates through one typed interface.
  Every typed triple has a local position, every colored incidence has a
  temporary port, and its local route prefix is proved orthogonal with exact
  endpoints; clause ports are additionally identified with their assembled
  typed element positions.  Polarity-normalized occurrence templates are
  also certified: their two red continuations are proved to reference the
  current and successor cycle links in one fixed geometric order, using the
  common outer-face boundary coordinates of all three connector kinds.
- [`LeanTrominoes/PlanarThreeDMClauseGadget.lean`](LeanTrominoes/PlanarThreeDMClauseGadget.lean)
  gives a smaller paired-port clause relation tailored to that variable cycle.
  Literal ports share one blue exact-one element, while complementary ports
  force three auxiliary triples to repeat the literal values through
  degree-two blue elements and common red and green elements.  Its generic
  correctness theorem and its arity-two and arity-three truth tables are
  machine checked; every colored element has degree two or three.  This is the
  semantic reduction only: a planar embedding with the alternating port order
  is not claimed, and must instead meet the separate planar-presentation
  certificate above.
- [`LeanTrominoes/WangPeriodicCNF.lean`](LeanTrominoes/WangPeriodicCNF.lean)
  starts the 2D hardness construction from the imported Wang domino problem.
  It activates at least one Wang tile at every cell and forbids incompatible
  active pairs across horizontal and vertical edges.  The semantic
  correctness theorem proves that this periodic CNF is satisfiable exactly
  when the original tileset tiles the plane; no uniqueness clauses are needed
  because any active tile can be chosen at each cell.  The generated formula
  is also proved local in the paper's Manhattan-distance sense.
- [`LeanTrominoes/WangPeriodicCNFComputability.lean`](LeanTrominoes/WangPeriodicCNFComputability.lean)
  proves that translation primitive recursive, including its ordered-pair
  enumeration and incompatibility filters.  Composing it with
  `LeanWang.domino_problem_coRE_hard` establishes a concrete computable
  many-one reduction and co-r.e.-hardness of the local periodic-CNF endpoint.
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
