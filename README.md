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
  complete route orthogonal, and lifts this fact to the full periodic drawing.
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
  portions before the first and after the last crossing.
  [`LeanTrominoes/PeriodicOrthocrossingPlanarBends.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarBends.lean)
  places equality links at every turn of every neighboring route occurrence.
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
  exact source and translated-target endpoints of its declared route.  This
  is the splice interface used by the planar 3DM gadget assembly.
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
- [`LeanTrominoes/PlanarOneInThree.lean`](LeanTrominoes/PlanarOneInThree.lean)
  packages Figure 9 as a positioned constant-size replacement for each
  embedded width-three disjunction.  Generated clauses occupy an explicit
  `4 × 4` refinement box and use clause-index-scoped auxiliaries; completeness,
  soundness, and exact finite satisfiability preservation are proved by
  connecting the layout to the verified periodic exact-one truth table.
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
