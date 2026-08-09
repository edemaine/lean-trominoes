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
  [`LeanTrominoes/PeriodicOrthocrossingCrossingHalo.lean`](LeanTrominoes/PeriodicOrthocrossingCrossingHalo.lean)
  enlarges the physical site inventory to every proper crossing among the
  nine neighboring segment translates retained by the finite route formula.
  It computes the unique possible horizontal/vertical intersection directly,
  proves soundness and completeness for the retained occurrences, and proves
  that every canonical crossing remains in the halo.
  [`LeanTrominoes/PeriodicOrthocrossingCrossingNormalization.lean`](LeanTrominoes/PeriodicOrthocrossingCrossingNormalization.lean)
  computes the common periodic shift of every halo crossing, moves both
  segment occurrences and the crossing point into the canonical square, and
  proves that the normalized record belongs to the canonical oriented list.
  It also certifies reconstruction of the physical point, segments, and
  occurrence translations from that canonical representative and shift.
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
  be attached back to their SAT meaning.  The flattened metadata list is
  duplicate-free, and two genuine incidences with equal clause and literal
  presentation indices are equal.
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
  [`LeanTrominoes/PeriodicOneInThreePositionedIndex.lean`](LeanTrominoes/PeriodicOneInThreePositionedIndex.lean)
  gives the flattened Figure 9 clause list a parallel lossless metadata
  index.  Every output clause recovers its source clause, source
  presentation index, and local generated-clause index, allowing global
  route lookup to select the certified local drawing without assuming a
  fixed block size.
  [`LeanTrominoes/PeriodicOneInThreePositionedLocalRoutes.lean`](LeanTrominoes/PeriodicOneInThreePositionedLocalRoutes.lean)
  uses that index to select the exact certified Figure 9 route at every
  global output incidence.  Every selected local route is proved orthogonal
  and continuously simple for width-three, atom-distinct sources;
  source-variable incidences still require a suffix inherited from the
  preceding drawing.
  [`LeanTrominoes/PeriodicOneInThreePositionedNormalizedLocalRoutes.lean`](LeanTrominoes/PeriodicOneInThreePositionedNormalizedLocalRoutes.lean)
  translates those selected routes into the canonical periodic
  clause-anchor gauge.  Every genuine route has its exact generated-clause
  start, its exact local boundary or auxiliary endpoint, and an
  orthogonality and simplicity certificate, exposing the endpoint used by
  the inherited-route splice.
  [`LeanTrominoes/PeriodicOneInThreeAuxiliaryIncidences.lean`](LeanTrominoes/PeriodicOneInThreeAuxiliaryIncidences.lean)
  proves that every Figure 9 auxiliary literal carries exactly its source
  clause/index scope and the source anchor offset.
  [`LeanTrominoes/PeriodicOneInThreePositionedAuxiliaryEndpoints.lean`](LeanTrominoes/PeriodicOneInThreePositionedAuxiliaryEndpoints.lean)
  combines that semantic fact with the instantiated local placement to show
  that every normalized auxiliary endpoint is already the final canonical
  periodic literal endpoint.  It completes any inherited-variable suffix
  family with singleton auxiliary suffixes and packages the resulting
  canonical orthogonal splice; only source-variable ports remain to supply.
  [`LeanTrominoes/PeriodicOneInThreePositionedAuxiliaryRouteIsolation.lean`](LeanTrominoes/PeriodicOneInThreePositionedAuxiliaryRouteIsolation.lean)
  observes that a fresh Figure 9 auxiliary's singleton suffix leaves its
  normalized local route unchanged.  Local simplicity and orthogonality then
  isolate both route endpoints after unit subdivision, providing the
  loop-erasure certificates for every auxiliary incidence.
  [`LeanTrominoes/PeriodicOneInThreeInheritedIncidences.lean`](LeanTrominoes/PeriodicOneInThreeInheritedIncidences.lean)
  classifies every inherited source literal in a generated Figure 9 clause
  by its precise source-clause presentation index, proving that its atom and
  periodic offset are unchanged.
  [`LeanTrominoes/PeriodicOneInThreePositionedInheritedEndpoints.lean`](LeanTrominoes/PeriodicOneInThreePositionedInheritedEndpoints.lean)
  lifts that classification through the flattened positioned formula.  It
  recovers the genuine source incidence behind every inherited output
  incidence and identifies its normalized local endpoint as the corresponding
  index-selected boundary port in the generated clause's anchor gauge.
  [`LeanTrominoes/PeriodicOneInThreePositionedOriginalOccurrenceProvenance.lean`](LeanTrominoes/PeriodicOneInThreePositionedOriginalOccurrenceProvenance.lean)
  synchronizes those flattened metadata indices with the explicit
  order-preserving Figure 7 occurrence pairs, certifying the exact source
  clause and literal presentation indices of every inherited incidence.
  [`LeanTrominoes/PeriodicOneInThreePositionedInheritedRouteSplicing.lean`](LeanTrominoes/PeriodicOneInThreePositionedInheritedRouteSplicing.lean)
  scales an inherited source incidence route by the `12 × 12` Figure 9
  refinement and translates it from the source clause's anchor gauge to the
  generated clause's gauge.  A boundary-port connector then yields exact
  canonical endpoints and orthogonality for one complete inherited suffix;
  replacing that clause-side prefix preserves the source route's final
  direction.  Its generic Manhattan connector is the remaining piece to
  replace by a noncrossing clause-boundary fan.
  [`LeanTrominoes/PositionedPeriodicCNFOrthogonalDetourTranslation.lean`](LeanTrominoes/PositionedPeriodicCNFOrthogonalDetourTranslation.lean)
  proves that a common translation of the two advertised detour endpoints
  translates the entire five-point route.  Unit-subdivision translation then
  reduces positioned connector questions to finite local-coordinate checks.
  [`LeanTrominoes/PeriodicOneInThreePositionedInheritedRouteIsolation.lean`](LeanTrominoes/PeriodicOneInThreePositionedInheritedRouteIsolation.lean)
  performs that finite check for all three Figure 9 boundary ports.  The
  connector contains no scale-twelve source-lattice point except its
  source-clause target, so attaching it to a nondegenerate simple source
  route preserves isolation of the final variable endpoint.
  [`LeanTrominoes/PeriodicOneInThreePositionedInheritedRouteFamily.lean`](LeanTrominoes/PeriodicOneInThreePositionedInheritedRouteFamily.lean)
  packages those per-incidence splices into the total inherited-suffix
  interface.  Any source route family with pointwise canonical endpoints and
  orthogonality now induces all inherited Figure 9 suffixes, with a
  proof-backed selector carrying the corresponding source-occurrence
  provenance certificate.
  [`LeanTrominoes/PeriodicOneInThreePositionedInheritedRouteFamilyIsolation.lean`](LeanTrominoes/PeriodicOneInThreePositionedInheritedRouteFamilyIsolation.lean)
  lifts the connector result through that proof-backed selector.  Pointwise
  source simplicity and nondegeneracy yield final-endpoint isolation for
  every genuine inherited suffix in the complete Figure 9 family.
  [`LeanTrominoes/PeriodicOneInThreePositionedInheritedSplicedRouteIsolation.lean`](LeanTrominoes/PeriodicOneInThreePositionedInheritedSplicedRouteIsolation.lean)
  characterizes each inherited local Figure 9 route as its explicit
  clause-to-boundary segment and proves that this segment misses the refined
  source lattice.  Consequently the normalized local prefix misses the final
  canonical literal endpoint, and joining it to any isolated inherited
  suffix preserves final-endpoint isolation for the complete route.  In the
  other direction, unit subdivision of every scaled source route stays on the
  translated scale grid, while the three Figure 9 clause ports and their
  connector paths avoid that grid.  Joining the two pieces therefore also
  preserves first-endpoint isolation.  A final inherited/auxiliary
  classification proves both endpoint-isolation properties for every genuine
  Figure 9 incidence.
  [`LeanTrominoes/EmbeddedCNFIncidenceDrawingMiddleRouteDirections.lean`](LeanTrominoes/EmbeddedCNFIncidenceDrawingMiddleRouteDirections.lean),
  [`LeanTrominoes/PlanarOneInThreeFigureNineMiddleRouteDirections.lean`](LeanTrominoes/PlanarOneInThreeFigureNineMiddleRouteDirections.lean), and
  [`LeanTrominoes/PeriodicOneInThreePositionedMiddleRouteDirections.lean`](LeanTrominoes/PeriodicOneInThreePositionedMiddleRouteDirections.lean)
  isolate the clause-side directional fact needed by unit elimination.
  Native finite checks cover every Figure 9 source arity and truth pattern:
  a literal-index-one route always exits weakly left of its clause point.
  Translation, renaming, anchor normalization, and route splicing preserve
  this property.
  [`LeanTrominoes/EmbeddedCNFIncidenceDrawingTwoPointRoutes.lean`](LeanTrominoes/EmbeddedCNFIncidenceDrawingTwoPointRoutes.lean),
  [`LeanTrominoes/PlanarOneInThreeFigureNineTwoPointRoutes.lean`](LeanTrominoes/PlanarOneInThreeFigureNineTwoPointRoutes.lean), and
  [`LeanTrominoes/PeriodicOneInThreePositionedTwoPointRoutes.lean`](LeanTrominoes/PeriodicOneInThreePositionedTwoPointRoutes.lean)
  isolate the only degenerate source-route case needed by the next reduction.
  Finite checks show that every two-point auxiliary Figure 9 route is
  vertical; inherited original-variable routes either have at least three
  points or inherit the same vertical exception.  Scaling, anchor
  normalization, and complete route splicing preserve this dichotomy.
  [`LeanTrominoes/PeriodicCNFPlanarOneInThreeNoUnitsPositioned.lean`](LeanTrominoes/PeriodicCNFPlanarOneInThreeNoUnitsPositioned.lean)
  places the final unit-elimination gadgets in constant-size refinements of
  those exact-one clause cells.  Erasing positions is exactly the verified
  logical unit-free formula, and its end-to-end satisfiability theorem is
  retained.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedIndex.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedIndex.lean)
  supplies the analogous lossless index for the variable-size
  unit-elimination blocks, retaining both source and local generated-clause
  memberships at every flattened output index.  The pair consisting of the
  source-clause index and local generated-clause index is proved globally
  duplicate-free, hence injective back to the flattened output index.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedLocalRoutes.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedLocalRoutes.lean)
  selects the corresponding certified unit-elimination route at every
  global output incidence and proves all such local routes orthogonal and
  continuously simple under the same width-three and atom-distinct
  hypotheses.  Distinct finite gadget vertices also prove that every genuine
  local route contains at least one edge.  Any two distinct incidences in one
  source-clause block inherit complete continuous separation from the same
  certified finite drawing, with distinctness accepted directly in either
  local-block or global generated-formula coordinates.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedNormalizedLocalRoutes.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedNormalizedLocalRoutes.lean)
  supplies the analogous canonical-gauge endpoints, orthogonality, and
  continuous-simplicity theorems for unit elimination.  Its
  inherited-variable endpoints are the precise splice boundary, while its
  new auxiliary endpoints are already final.  Every generated clause retains
  its source block's periodic anchor, so the same-block pairwise separation
  theorem survives canonical-gauge normalization, again with a
  global-incidence-coordinate interface.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsAuxiliaryIncidences.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsAuxiliaryIncidences.lean)
  identifies the exact source scope and source-anchor offset of every fresh
  unit-elimination auxiliary literal.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsInheritedIncidences.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsInheritedIncidences.lean)
  classifies every inherited unit-elimination literal by its precise source
  presentation index, preserving its atom and periodic offset.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedAuxiliaryEndpoints.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedAuxiliaryEndpoints.lean)
  then proves that each normalized auxiliary endpoint is already its final
  canonical periodic endpoint.  As at the Figure 9 layer, it completes any
  inherited-variable suffix family automatically and packages the resulting
  canonical orthogonal splice, leaving only source-variable ports to supply.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedEndpoints.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedEndpoints.lean)
  lifts the inherited semantic classification through the flattened final
  formula and identifies each local endpoint with its exact source-clause
  boundary port.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedOriginalOccurrenceProvenance.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedOriginalOccurrenceProvenance.lean)
  synchronizes the flattened unit-elimination metadata with its explicit
  order-preserving occurrence pairs, certifying the selected source clause
  and literal presentation indices.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedRouteSplicing.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedRouteSplicing.lean)
  scales and translates the corresponding source incidence route through
  the `6 × 6` unit-elimination refinement, removes its obsolete clause
  endpoint, and connects the boundary port directly to its transformed first
  exit.  Exact canonical endpoints, orthogonality, and the source route's
  final direction are preserved.  Generated clauses in a common source block
  are also shown to induce one common inherited-route translation.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedRouteIsolation.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedRouteIsolation.lean)
  applies the positive-scaling and translation transport to the inherited
  source route before its clause-side head is replaced.  Both isolated
  endpoints of an arbitrary orthogonal source route survive the `6 × 6`
  refinement and anchor-gauge change, even if it has internal loops.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedConnectorIsolation.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedConnectorIsolation.lean)
  develops the complementary head-replacement geometry.  A connector's
  target remains isolated whenever it is outside the first detour segment;
  in particular this holds for the vertical first exits of eliminated
  Figure 9 unit clauses.  A scaled source endpoint outside the source
  route's first segment cannot occur on the connector, and an
  endpoint-isolated route ending at its first exit is proved to consist of
  exactly that one segment.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamily.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamily.lean)
  packages those per-incidence splices into a total proof-backed inherited
  suffix family.  Any canonical orthogonal source route family with certified
  first exits can therefore be lifted through unit elimination, with the
  selector carrying source-occurrence provenance; the concrete wrapped
  Figure 9 family supplies the first-exit certificate.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedSuffixIsolation.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedSuffixIsolation.lean),
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamilyIsolation.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamilyIsolation.lean), and
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedSplicedRouteIsolation.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedSplicedRouteIsolation.lean)
  lift endpoint isolation through head replacement, the proof-backed
  inherited selector, and the complete local-plus-suffix splice.  The local
  unit-elimination prefix misses the transformed source endpoint because the
  former lies strictly between scale-six grid lines while the latter lies on
  their lattice.  Conversely, the generated clause endpoint misses every
  inherited suffix: all literal indices are handled arithmetically, with the
  middle route using the weak-left first-exit invariant.  The resulting
  two-sided theorem covers both inherited and auxiliary incidences and also
  records that every complete route contains an edge.
  [`LeanTrominoes/PeriodicOneInThreePositionedRouteTerminalDirections.lean`](LeanTrominoes/PeriodicOneInThreePositionedRouteTerminalDirections.lean)
  proves that completing either transformation's inherited suffix family and
  prepending its normalized local clause route preserves the inherited
  variable-side terminal direction.  It also proves that a genuine Figure 9
  inherited route has at least three listed points when both its local prefix
  and inherited suffix contain an edge.
  [`LeanTrominoes/PeriodicOneInThreePositionedRouteTerminalDirectionTransport.lean`](LeanTrominoes/PeriodicOneInThreePositionedRouteTerminalDirectionTransport.lean)
  combines those splice lemmas with exact selector provenance to prove the
  concrete terminal-direction preservation hypotheses used by the abstract
  occurrence-order transport theorem for both transformations.  Its unit-
  elimination interface can restrict the three-point source-route hypothesis
  to atoms that actually reach the third occurrence slot.
  [`LeanTrominoes/PeriodicOneInThreeNoUnitsClauseRouteOrder.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsClauseRouteOrder.lean)
  proves that every ternary output clause starts its literal-indexed routes
  toward south, west, and east.  Anchor normalization and arbitrary inherited
  suffix splicing preserve that rotation order, isolating it from the
  earlier long-route geometry.
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
  transfer; the retained positioned clause list is itself duplicate-free.
  [`LeanTrominoes/PositionedPeriodicCNFDeduplicationRoutes.lean`](LeanTrominoes/PositionedPeriodicCNFDeduplicationRoutes.lean)
  transports finite geometric incidence routes through that changed clause
  indexing.  It also proves that normalizing every source clause and its
  physical routes together preserves their endpoints.  Each retained clause
  then selects its first anchor-normalized representative and reuses the
  matching literal route.  The transported family is proved to satisfy every
  periodic incidence endpoint, and compatibility is reduced to finite
  distinctness and fundamental-square bounds for the retained vertices.
  [`LeanTrominoes/PositionedPeriodicCNFVariableGauge.lean`](LeanTrominoes/PositionedPeriodicCNFVariableGauge.lean)
  moves each periodic protovariable by an independently chosen lattice
  period while compensating every literal offset.  Periodic satisfiability
  and all physical literal and raw-route endpoints are unchanged.  A
  canonical quotient gauge reduces stored variable coordinates modulo the
  period and supplies the corresponding fundamental-square bounds.
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
  [`LeanTrominoes/PositionedPeriodicCNFTaggedRouteLookup.lean`](LeanTrominoes/PositionedPeriodicCNFTaggedRouteLookup.lean)
  additionally recovers the metadata-rich incidence, positioned clause, and
  positioned literal belonging to a route tagged by its global flat-list
  index.  This preserves the occurrence identity needed when normalized
  periodic routes are transferred back to a finite drawing.
  [`LeanTrominoes/PositionedPeriodicCNFOrthogonalIncidenceRoutes.lean`](LeanTrominoes/PositionedPeriodicCNFOrthogonalIncidenceRoutes.lean)
  supplies a total canonical Manhattan detour for every positioned literal
  incidence.  Fresh detour coordinates make all four segments nondegenerate
  and axis-aligned even for coincident advertised endpoints; the assembled
  drawing is proved to have exact periodic endpoints and to be orthogonal.
  These deliberately generic routes do not assert planarity, leaving later
  construction files to choose noncrossing lanes.
  [`LeanTrominoes/PositionedPeriodicCNFCanonicalOrthogonalRoutes.lean`](LeanTrominoes/PositionedPeriodicCNFCanonicalOrthogonalRoutes.lean)
  packages any pointwise canonical endpoint and orthogonality proofs into a
  complete route family.  It derives the assembled periodic drawing's
  graph-level `RoutesMatch` and `IsOrthogonal` predicates, keeping vertex
  separation and planarity as explicit independent obligations.
  [`LeanTrominoes/PositionedPeriodicCNFCanonicalOrthogonalPlanarization.lean`](LeanTrominoes/PositionedPeriodicCNFCanonicalOrthogonalPlanarization.lean)
  transfers the route-independent vertex geometry from any compatible
  reference drawing, then unit-subdivides a canonical orthogonal route
  family.  The result is packaged as a complete compatible, orthogonal, and
  planar positioned incidence presentation.
  [`LeanTrominoes/PositionedPeriodicCNFCanonicalRouteRenaming.lean`](LeanTrominoes/PositionedPeriodicCNFCanonicalRouteRenaming.lean)
  proves that position- and period-preserving variable renaming reuses a
  canonical route family verbatim, retaining pointwise clause/literal
  endpoints and orthogonality.
  [`LeanTrominoes/PositionedPeriodicCNFVariableRouteOrderRenaming.lean`](LeanTrominoes/PositionedPeriodicCNFVariableRouteOrderRenaming.lean)
  proves that injective variable renaming maps tagged occurrences without
  changing their clause/literal presentation indices.  Bijective renaming
  therefore preserves clockwise variable-route order, and every target
  incidence can be recovered from its source incidence at the same indices.
  [`LeanTrominoes/PositionedPeriodicCNFLocalRouteSplicing.lean`](LeanTrominoes/PositionedPeriodicCNFLocalRouteSplicing.lean)
  packages orthogonal suffixes from arbitrary local gadget splice points to
  canonical periodic literal endpoints.  Its generic join theorem combines
  such a suffix with a normalized local clause route while preserving both
  outer endpoints and orthogonality.
  [`LeanTrominoes/PositionedPeriodicCNFLocalRouteSplicingEndpointDirections.lean`](LeanTrominoes/PositionedPeriodicCNFLocalRouteSplicingEndpointDirections.lean)
  shows that sum-family completion leaves inherited routes verbatim and that
  adjoining any local prefix preserves a nondegenerate suffix's final
  direction.
  [`LeanTrominoes/OrthogonalPolylineHeadReplacement.lean`](LeanTrominoes/OrthogonalPolylineHeadReplacement.lean)
  supports the complementary source-side operation: replace a route's old
  first point by a certified prefix ending at the first point of its nonempty
  tail.  The replacement preserves the far endpoint and orthogonality, which
  lets coordinated gadget fans attach to distinct source-route exits instead
  of converging again at the replaced vertex.
  [`LeanTrominoes/OrthogonalPolylineHeadReplacementEndpointDirections.lean`](LeanTrominoes/OrthogonalPolylineHeadReplacementEndpointDirections.lean)
  proves that this source-side prefix replacement also preserves the final
  direction of every route with at least three points.
  [`LeanTrominoes/EmbeddedCNFIncidenceRouteExits.lean`](LeanTrominoes/EmbeddedCNFIncidenceRouteExits.lean)
  proves that every genuine route in a valid finite embedded drawing has
  such a first exit: its clause and variable endpoints belong to opposite
  halves of the drawing's duplicate-free vertex list and are therefore
  distinct.  The Figure 9 route layer lifts this witness through anchor
  normalization, local-suffix splicing, and opaque variable wrapping.
  [`LeanTrominoes/PositionedPeriodicCNFSumRouteSuffixes.lean`](LeanTrominoes/PositionedPeriodicCNFSumRouteSuffixes.lean)
  reduces that suffix obligation for source/auxiliary sum types to inherited
  source variables alone.  New auxiliaries receive a singleton suffix at
  their already-final local endpoint, while supplied inherited suffixes are
  retained with their endpoint and orthogonality certificates.
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
  [`LeanTrominoes/PeriodicGridDrawingMixedContinuousBounds.lean`](LeanTrominoes/PeriodicGridDrawingMixedContinuousBounds.lean)
  sharpens that continuous-contact bound when either segment stays in the
  half-open fundamental square.  Even if the other segment uses the full
  one-cell halo, a meeting can then occur only at one of the nine neighboring
  relative translations.
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
  [`LeanTrominoes/PeriodicGridDrawingRouteOccurrenceSeparation.lean`](LeanTrominoes/PeriodicGridDrawingRouteOccurrenceSeparation.lean)
  extracts complete finite separation for distinct lifted occurrences of
  possibly diagonal routes.  The stronger segment-endpoint/interior
  certificate handles both directed listed-point cases, while continuous
  planarity and endpoint-only contacts supply segment and point contacts.
  For a unit-step drawing the stronger segment-endpoint certificate is now
  automatic, because a unit lattice segment has no lattice point inside it.
  [`LeanTrominoes/OrthogonalPolylineRouteReversalContacts.lean`](LeanTrominoes/OrthogonalPolylineRouteReversalContacts.lean)
  proves that this finite separation certificate is preserved when both
  routes are traversed in reverse, as required by variable-to-clause routing.
  [`LeanTrominoes/OrthogonalPolylineStrictSeparation.lean`](LeanTrominoes/OrthogonalPolylineStrictSeparation.lean)
  strengthens the finite predicate to forbid all listed-point contact and
  proves that this strict form is preserved by positive uniform scaling and
  composes through endpoint joins on either side.  Restricting either route
  to one of its listed singleton points also preserves strict separation.
  This is the form needed while tile endpoints become internal points of a
  recursively assembled corridor.
  [`LeanTrominoes/OrthogonalPolylineMiddleCoarsening.lean`](LeanTrominoes/OrthogonalPolylineMiddleCoarsening.lean)
  proves that strict continuous separation survives removal of a listed
  point lying inside one axis-aligned segment.  It accounts for the possible
  crossing at the removed point as well as contacts with either resulting
  open subsegment.  Its join lemmas also extract separation of either
  constituent route and support coarsening a trailing subdivided segment
  inside a longer joined route.
  [`LeanTrominoes/OrthogonalPolylineLinearSeparation.lean`](LeanTrominoes/OrthogonalPolylineLinearSeparation.lean)
  proves a complementary half-plane certificate: strict opposite-side
  bounds for an integer linear functional imply complete continuous route
  separation.  The proof covers perpendicular crossings, listed-point
  contacts, and collinear open-interval overlap, enabling parametric
  separation of arbitrary-length angular ray families.
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
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCertificate.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCertificate.lean)
  packages the complete retained planar-SAT endpoint behind the standard
  local 3SAT-3 hypotheses (and source-clause nonemptiness).  The output is
  equisatisfiable with its source, has width at most three and occurrence
  degree at most eight, has no empty clauses, and carries a compatible,
  continuously planar, endpoint-clean incidence drawing whose route points
  lie in the one-cell halo.  It now also contains a compatible orthogonal
  presentation obtained by retained-ray rasterization and unit subdivision.
  The original continuously planar drawing remains the geometric source for
  the subsequent fixed-eight occurrence split, because the unsplit Figure 8
  terminal rays also use 45-degree diagonals.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedEightOccurrenceSplit.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedEightOccurrenceSplit.lean)
  sorts the final retained incidence routes by terminal angle, assigns their
  at-most-eight occurrences injectively to the fixed Figure 7 compass ports,
  and applies the generic occurrence split.  The positioned result remains
  equisatisfiable with the original local 3SAT-3 source, retains width three,
  has at most three occurrences per output variable, and has a positive
  uniformly refined drawing period.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedEightOccurrenceSplitRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedEightOccurrenceSplitRoutes.lean)
  instantiates the generic angular Figure 7 route splice at that same retained
  formula.  The complete positioned split drawing has exact periodic
  incidence endpoints and is orthogonal.  Its canonical copied-source
  prefixes intentionally make no noncrossing claim; replacing those prefixes
  by geometry inherited from the retained planar drawing is the remaining
  global planarity obligation.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreePositioned.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreePositioned.lean)
  threads the retained fixed-eight formula through the positioned Figure 9
  exact-one reduction, opaque wrapping, and unit-clause elimination.  The
  final formula is equisatisfiable with the original local 3SAT-3 source, has
  only binary or ternary clauses, retains occurrence degree at most three and
  atom-distinct clauses, and has a positive refined period.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreeRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreeRoutes.lean)
  carries the retained angular-spliced source routes through the positioned
  Figure 9 adapter and completes its fresh local incidences.  Every genuine
  raw exact-one route has exact canonical endpoints, is orthogonal, and
  records the first exit needed by the later unit-elimination splice.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreeWrappedRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreeWrappedRoutes.lean)
  transports those routes through the exact-one formula's opaque variable
  wrapper without changing their polylines, preserving canonical endpoints,
  orthogonality, and first exits.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreeNoUnitsRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreeNoUnitsRoutes.lean)
  completes the unit-elimination splice and packages the final retained,
  unit-free exact-one route family.  Its assembled periodic incidence drawing
  matches every graph edge and is orthogonal; global planarity remains tied
  to the coordinated copied-source boundary fans.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreeNoUnitsVariableRouteOrder.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreeNoUnitsVariableRouteOrder.lean)
  proves that the retained fixed-eight source routes follow syntactic
  occurrence order clockwise, then carries that invariant through Figure 9,
  opaque wrapping, and unit elimination.  Third-occurrence provenance again
  limits the three-point route requirement to embedded source variables, so
  the final retained unit-free routes satisfy the variable-fan rotation
  premise used by the planar 3DM ribbon construction.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreeNoUnitsRibbonOrders.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreeNoUnitsRibbonOrders.lean)
  pairs that variable rotation with the canonical ternary clause-exit order
  supplied by unit elimination, and records the final width-three bound.
  Equality-independent promise transport then combines those facts with the
  occurrence-three and arity promises: every ribbon-ready presentation using
  these routes has the complete coordinated source-fan clockwise certificate.
  Constructing that presentation is now the remaining geometric obligation.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightThreeDM.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightThreeDM.lean)
  names the normalized periodic 3DM target of the retained fixed-eight
  exact-one pipeline.  It proves the target well-formed, proves that every
  colored element has degree two or three, and identifies both perfect
  matchings and abstract incidence orientations exactly with satisfiability
  of the original local 3SAT-3 source.  This completes the nongeometric 3DM
  endpoint; the retained exact-one planarity certificate remains geometric.
- [`LeanTrominoes/OrthogonalPolylineSymmetries.lean`](LeanTrominoes/OrthogonalPolylineSymmetries.lean)
  centralizes the facts that translation and route reversal preserve
  rectilinearity, formerly embedded in the later 3DM-contraction layer.
- [`LeanTrominoes/OrthogonalPolylineTailReplacement.lean`](LeanTrominoes/OrthogonalPolylineTailReplacement.lean)
  provides the reverse dual of route-head replacement.  It preserves the
  clause-side endpoint while replacing a route's variable-side tail at its
  old penultimate point, and proves the resulting endpoint and orthogonality
  laws needed to splice coordinated Figure 7 fans into retained routes.
- [`LeanTrominoes/OctilinearRayStaircase.lean`](LeanTrominoes/OctilinearRayStaircase.lean)
  gives every axis or 45-degree compass ray a narrow rectilinear
  rasterization.  Axis rays remain direct and diagonal rays alternate unit
  horizontal and vertical steps; Lean proves exact endpoints, preservation
  of the compass classification, and orthogonality for all eight directions.
- [`LeanTrominoes/OctilinearPolylineRasterization.lean`](LeanTrominoes/OctilinearPolylineRasterization.lean)
  joins those segment rasterizations along an arbitrary octilinear polyline.
  It preserves both outer endpoints, yields a certified orthogonal route, and
  lifts uniformly to scaled incidence-route families.
- [`LeanTrominoes/OctilinearEmbeddedCNFIncidenceDrawing.lean`](LeanTrominoes/OctilinearEmbeddedCNFIncidenceDrawing.lean)
  packages octilinearity for every genuine route of a finite embedded CNF.
  The certificate follows automatically from orthogonality, follows for a
  direct drawing from its eight-direction terminal certificate, and is
  preserved in both directions by logical renaming and by coordinate
  translation.  This covers retained carriers, bends, crossovers, and
  variable arms.  Routed source-clause rays additionally use three fixed
  non-compass slopes, which the next rasterization layer must handle
  explicitly.
- [`LeanTrominoes/RoutedClauseRayStaircase.lean`](LeanTrominoes/RoutedClauseRayStaircase.lean)
  supplies that exceptional rasterization for the three routed-clause slopes
  `(-9, -4)`, `(-4, 1)`, and `(1, -4)`.  Each fixed balanced unit-step block
  is orthogonal and returns exactly to its original straight ray; repeated
  blocks therefore preserve exact endpoints while remaining in a narrow
  corridor.  An executable classifier recognizes every positive multiple
  and recovers its arm and exact repeat count.
- [`LeanTrominoes/RetainedRayRasterization.lean`](LeanTrominoes/RetainedRayRasterization.lean)
  unifies the eight compass directions and the three routed-clause slopes
  into one executable retained-ray classifier.  Lean proves classification
  soundness, preservation under positive integral scaling, exact endpoints,
  and orthogonality after rasterizing supported segments, polylines, and
  whole incidence-route families.
- [`LeanTrominoes/RetainedRayRasterizationCorridor.lean`](LeanTrominoes/RetainedRayRasterizationCorridor.lean)
  gives the staircase construction a uniform quantitative bound.  Every
  listed rasterized point lies within coordinate radius nine of an exact
  checkpoint on its source ray, independently of the ray's length; the
  certificate lifts from all eleven primitive slopes to supported segments,
  nondegenerate polylines, and scaled incidence routes.
- [`LeanTrominoes/RetainedTerminalDirections.lean`](LeanTrominoes/RetainedTerminalDirections.lean)
  reverses those clause-to-variable rays into the terminal vectors used by
  the angular occurrence sort.  It classifies the eight compass directions
  and three exceptional routed-clause directions with positive lengths,
  assigns their exact east-first ranks, and proves that the integer
  cross-product comparator agrees with those ranks for arbitrary positive
  multiples.  Every nondegenerate retained-ray polyline therefore has a
  classified terminal vector in this finite vocabulary.
- [`LeanTrominoes/RetainedEmbeddedCNFIncidenceDrawing.lean`](LeanTrominoes/RetainedEmbeddedCNFIncidenceDrawing.lean)
  packages that segment condition over every genuine route of a finite
  embedded CNF.  The certificate follows from octilinearity, is preserved by
  translation and logical renaming in both directions, and has a
  membership-style interface.  The direct routed-clause star is certified
  separately from its three exceptional primitive vectors.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATLocalRetainedRays.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATLocalRetainedRays.lean)
  proves the combined certificate for every metadata-selected local
  planar-SAT component.  Carrier lenses and bend corners inherit
  orthogonality, crossovers and variable arms inherit their compass
  certificates, and routed clauses use the three exceptional slopes; the
  cases assemble into a certificate for the complete retained finite
  incidence drawing.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRetainedRays.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRetainedRays.lean)
  transports that finite certificate through the actual periodic quotient
  bookkeeping.  The quotient-to-finite occurrence witness reduces every
  genuine route in the gauged, wrapped, and orbit-deduplicated drawing to a
  translate of a retained finite route, so every final segment has one of
  the eleven rasterizable slopes.
- [`LeanTrominoes/EmbeddedCNFIncidenceDrawingOrthogonalPrefixes.lean`](LeanTrominoes/EmbeddedCNFIncidenceDrawingOrthogonalPrefixes.lean)
  packages the complementary route-shape invariant needed for raster
  separation: every genuine route is orthogonal after removing its final
  point.  It also packages the sharper dichotomy that every route is either
  fully orthogonal or has a singleton prefix.  Both certificates follow from
  full drawing orthogonality, are preserved in both directions by logical
  renaming and by translation, and the singleton branch holds automatically
  for direct two-point incidence drawings.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATLocalOrthogonalPrefixes.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATLocalOrthogonalPrefixes.lean)
  proves both route-shape invariants componentwise for the retained planar-SAT
  construction.  Carrier lenses and bend corners are fully orthogonal, while
  crossover, routed-variable, and routed source-clause components select the
  singleton-prefix branch inherited from their direct route drawings.  The
  metadata lookup then assembles both certificates for the complete finite
  drawing.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedOrthogonalPrefixes.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedOrthogonalPrefixes.lean)
  transports prefix orthogonality and the full-orthogonal-or-singleton
  dichotomy through gauging, clause-anchor normalization, and orbit
  deduplication.  The quotient-to-finite occurrence witness now certifies
  both the rectilinear prefix of every genuine final route and the direct
  shape of every route that is not fully rectilinear.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedTerminalDirections.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedTerminalDirections.lean)
  combines retained-ray transport with compatibility and looplessness to
  prove that every genuine final retained route has at least one segment and
  that its backwards terminal vector belongs to the exact eleven-direction
  vocabulary.  This supplies the finite angular data needed to construct the
  local order-preserving adapter into Figure 7's consecutive compass gates.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedTerminalDirectionOrder.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedTerminalDirectionOrder.lean)
  attaches that eleven-direction classification to every genuine occurrence
  and every indexed entry of the retained angular occurrence lists.  Earlier
  entries receive nondecreasing east-first direction ranks, exposing the
  order-preserving boundary correspondence needed by the local adapter.
- [`LeanTrominoes/RetainedAngularDirectionProfile.lean`](LeanTrominoes/RetainedAngularDirectionProfile.lean)
  projects classified terminal vectors to a total finite direction list and
  packages, for each retained source variable, the list's nondecreasing
  eleven-direction ranks together with its eight-slot bound.  This is the
  compact input interface for the forthcoming local adapter construction.
- [`LeanTrominoes/RetainedTerminalDirectionEnumeration.lean`](LeanTrominoes/RetainedTerminalDirectionEnumeration.lean)
  enumerates the eleven retained terminal directions in exact east-first
  angular-rank order.  The catalog is proved complete and duplicate-free,
  and its ranks are proved to equal its indices, supplying the finite search
  domain for the annular adapter.
- [`LeanTrominoes/RetainedAngularTerminalDataProfile.lean`](LeanTrominoes/RetainedAngularTerminalDataProfile.lean)
  retains the positive primitive-block length alongside each sorted
  direction.  Equal-direction incidences intentionally present in Figure
  8(b) remain separate radial splice data instead of collapsing to one gate,
  and their lengths are proved nondecreasing from the variable endpoint
  outward.
- [`LeanTrominoes/RetainedTerminalSplicePoint.lean`](LeanTrominoes/RetainedTerminalSplicePoint.lean)
  identifies each classified `(direction, length)` datum with the actual
  penultimate point of its source polyline.  Thus the overlapping old final
  segment can be discarded and a new local suffix can attach at an exact,
  nondegenerate radial splice point.
- [`LeanTrominoes/RetainedTerminalDirectionAlignment.lean`](LeanTrominoes/RetainedTerminalDirectionAlignment.lean)
  proves that two successfully classified terminal segments with different
  axis-alignment status have different retained directions.  A route-level
  form applies this directly to the exact discarded final segments exposed
  by the splice-point interface.
- [`LeanTrominoes/RetainedTerminalScaling.lean`](LeanTrominoes/RetainedTerminalScaling.lean)
  proves that positive integral refinement preserves each retained terminal
  direction and its angular rank, multiplies only its primitive-block length,
  and carries the source splice point to the exact penultimate point of the
  scaled route.
- [`LeanTrominoes/RetainedAngularTerminalDataScaling.lean`](LeanTrominoes/RetainedAngularTerminalDataScaling.lean)
  lifts that pointwise theorem through angular sorting with its radial
  tie-break: the scaled route family has the identical occurrence order,
  while its complete local profile is obtained by mapping only the terminal
  lengths.
- [`LeanTrominoes/RetainedAngularTerminalGateDistinctness.lean`](LeanTrominoes/RetainedAngularTerminalGateDistinctness.lean)
  proves that positive `(direction, length)` data are represented injectively
  by their radial splice gates.  Thus the annular adapter can permit
  equal-direction ties while asking precisely for duplicate-free gates, a
  condition preserved by positive refinement; combined with the radial
  tie-break, duplicate-freeness makes earlier tied slots strictly nearer the
  variable.  The module also isolates the
  source-level geometric obligation: injectivity of genuine same-variable
  terminal vectors implies duplicate-free angular profiles.
- [`LeanTrominoes/RetainedOccurrenceTerminalVectorDistinctness.lean`](LeanTrominoes/RetainedOccurrenceTerminalVectorDistinctness.lean)
  derives that source-level terminal-vector injectivity from the actual
  endpoint-only route-contact interface, compatibility, and per-clause
  incidence-key distinctness.  Equal vectors align the two penultimate points
  after undoing their periodic endpoint shifts; endpoint-only contact forces
  the exceptional direct-route case, where fundamental-square uniqueness
  identifies the clause and the route alignment identifies the offset.
  Uniqueness of `(atom, offset)` then identifies the literal.  This deliberately
  permits legitimate periodic self-links whose two occurrences use different
  offsets, and leaves only that weaker syntactic certificate to discharge
  before the generic gate-separation theorem applies.
- [`LeanTrominoes/RetainedSourceIncidenceDistinctness.lean`](LeanTrominoes/RetainedSourceIncidenceDistinctness.lean)
  proves that every finite retained construction clause has distinct atoms
  and transports this fact through periodicization.  It then establishes
  generic incidence-key preservation under injective renaming, variable
  gauging, clause-anchor normalization, and representative deduplication.
- [`LeanTrominoes/RetainedFinalSourceIncidenceDistinctness.lean`](LeanTrominoes/RetainedFinalSourceIncidenceDistinctness.lean)
  assembles those component and preservation results across the complete
  retained-source bookkeeping pipeline, certifying the incidence-key
  distinctness needed by the terminal-vector argument.
- [`LeanTrominoes/RetainedFinalRoutePrefixSeparation.lean`](LeanTrominoes/RetainedFinalRoutePrefixSeparation.lean)
  instantiates nonorthogonal route-occurrence separation and route simplicity
  at the final retained drawing.  Two different stored incidences with
  different clause endpoints therefore have strictly separated
  final-point-deleted prefixes, exactly the source/source case needed before
  angular-fan tail replacement.  A head-aware variant also allows the two
  routes to share their clause endpoint: if the second deleted prefix is not
  a singleton, the first prefix still strictly avoids its discarded final
  segment.
- [`LeanTrominoes/RetainedFinalRoutePrefixRectangleSeparation.lean`](LeanTrominoes/RetainedFinalRoutePrefixRectangleSeparation.lean)
  combines that strict prefix separation with the transported prefix-shape
  certificate.  Flat route membership recovers the positioned incidence
  metadata needed for orthogonality, after which every point/segment and
  segment/segment pair in the two prefixes has separated integral endpoint
  rectangles.  When the reference route's discarded final segment is
  axis-aligned, its strict separation certificate supplies the last
  rectangles and an exact `dropLast`/final-segment decomposition extends the
  result to the complete reference route.  This is the quantitative
  prefix/route input for raster clearance in every orthogonal-terminal case.
  The transported route-shape dichotomy additionally proves that every
  non-axis-aligned final segment belongs to a route whose deleted prefix has
  length one, isolating the remaining oblique-terminal case to fan geometry.
  A complementary generic lemma upgrades ordinary endpoint-contact planarity
  to strict separation of two axis-aligned discarded-final-segment
  rectangles whenever cross endpoints differ and the retained prefixes are
  not both singletons.  This isolates common-head carrier and bend routes to
  a finite route-length check.
- [`LeanTrominoes/RetainedFinalTerminalGateDistinctness.lean`](LeanTrominoes/RetainedFinalTerminalGateDistinctness.lean)
  instantiates the terminal-vector argument at the complete retained drawing.
  Its compatibility, endpoint-only route-contact, and final incidence-key
  certificates prove injectivity of same-variable terminal vectors and hence
  duplicate-free radial splice gates for every fitted angular profile.
- [`LeanTrominoes/RetainedAngularFanBoundaryGeometry.lean`](LeanTrominoes/RetainedAngularFanBoundaryGeometry.lean)
  identifies Figure 7's eight boundary sites with the east-first compass
  vectors of radius twelve around the scaled source-variable center.  It
  proves those sites distinct and proves every positive factor-36 retained
  splice gate lies strictly outside the local fan square.
- [`LeanTrominoes/RetainedAngularTerminalInterfaceGeometry.lean`](LeanTrominoes/RetainedAngularTerminalInterfaceGeometry.lean)
  uses the factor-36 refinement to put all eleven retained slopes on one
  fixed radius-36 square.  Every unbounded scaled splice gate is proved to be
  a positive radial multiple of its direction's fixed interface point,
  reducing the remaining annular adapter to finite geometry.
- [`LeanTrominoes/RetainedAngularTerminalShape.lean`](LeanTrominoes/RetainedAngularTerminalShape.lean)
  reduces each length-aware profile to eight fixed optional direction slots
  and a finite matrix of strict radial comparisons.  The shape preserves
  exactly the ordering information needed to separate same-ray ties,
  is unchanged by positive uniform refinement, and is a finite type suitable
  for exhaustive adapter search.  An executable validity predicate restricts
  that raw type to initial active slots with sorted directions and strict
  total radial orders that follow slot order; every duplicate-free concrete
  profile is proved valid.
- [`LeanTrominoes/RetainedAngularTerminalLaneRanks.lean`](LeanTrominoes/RetainedAngularTerminalLaneRanks.lean)
  converts the strict radial-order matrix into a zero-based lane number by
  counting closer gates.  Validity proves every number is below eight and
  proves both lane injectivity and strict lane growth with slot order within
  each tied direction block; the assignment is unchanged by positive
  refinement.
- [`LeanTrominoes/RetainedAngularTerminalAdapterPorts.lean`](LeanTrominoes/RetainedAngularTerminalAdapterPorts.lean)
  combines the eleven retained angular directions with the eight radial
  lanes into 88 fixed adapter-port identities.  The direction-and-lane
  encoding is injective, distinct active slots of every valid finite shape
  select distinct ports, and positive uniform refinement preserves those
  selections.
- [`LeanTrominoes/RetainedAngularTerminalAdapterPortGeometry.lean`](LeanTrominoes/RetainedAngularTerminalAdapterPortGeometry.lean)
  embeds the 88 radial-lane adapter identities at every second lattice point
  of a radius-22 square, enumerated clockwise from due east.  These
  coordinates are injective, lie outside the radius-12 Figure 7 fan and
  inside the radius-36 retained-terminal interface, and remain unchanged by
  positive refinement.
- [`LeanTrominoes/RetainedAngularTerminalFanPorts.lean`](LeanTrominoes/RetainedAngularTerminalFanPorts.lean)
  places direction-and-occurrence-slot fan ports on a distinct radius-33
  square.  Valid profiles select these outer-frame sites in strictly
  clockwise slot order, and the radial tie-break proves that this order is
  compatible with the radial lanes near tied source gates.
- [`LeanTrominoes/RetainedAngularFanAnchorRoutes.lean`](LeanTrominoes/RetainedAngularFanAnchorRoutes.lean)
  identifies square-frame indices `0, 11, …, 77` with the eight radius-22
  compass anchors and gives fixed orthogonal inward routes to the matching
  radius-12 Figure 7 boundary sites.  Their endpoints are exact and the eight
  translated route point sets are pairwise disjoint.  The shape-dependent
  fan-facing sites lie on the separate radius-33 outer frame.
- [`LeanTrominoes/RetainedAngularFanAnnulusDemands.lean`](LeanTrominoes/RetainedAngularFanAnnulusDemands.lean)
  packages each active fan-side connection as an exact radius-33 outer
  endpoint and radius-22 compass anchor.  Both endpoint families are
  injective, their strict clockwise orders are proved equivalent to slot
  order, and the complete finite demand is invariant under positive
  refinement.
- [`LeanTrominoes/RetainedAngularFanAnnulusRoutes.lean`](LeanTrominoes/RetainedAngularFanAnnulusRoutes.lean)
  constructs an elementary finite orthogonal witness for every annular
  demand.  Each route has exact radius-33 and radius-22 endpoints, and all
  listed points remain inside the radius-36 interface and outside the
  radius-21 square.  These individual witnesses share a radius-34 cut; the
  coordinated router will replace that choice to obtain pairwise separation.
- [`LeanTrominoes/RetainedAngularFanAnnulusRefinedRoutes.lean`](LeanTrominoes/RetainedAngularFanAnnulusRefinedRoutes.lean)
  gives that coordinated router after a fixed factor-eight local refinement.
  Square-boundary interpolation constructs one finite orthogonal route for
  each direction and occurrence slot.  Lean checks exact refined endpoints,
  annular bounds, and strict continuous separation for every
  order-compatible pair among the 88 routes, then joins the pairwise
  separated scaled compass routes down to the refined Figure 7 boundary.
- [`LeanTrominoes/RetainedAngularFanPositionedRoutes.lean`](LeanTrominoes/RetainedAngularFanPositionedRoutes.lean)
  translates the complete finite router to an arbitrary variable center.
  Exact fan-port and Figure 7 endpoints, orthogonality, shell bounds, and
  strict continuous separation all survive the common translation.
- [`LeanTrominoes/RetainedAngularTerminalSlotLookup.lean`](LeanTrominoes/RetainedAngularTerminalSlotLookup.lean)
  bridges source incidence identities to the finite router.  A genuine
  occurrence's index in the angular-and-radial list is proved below eight,
  looking that slot up recovers the same occurrence and exact classified
  terminal datum, and the extracted finite shape selects precisely the
  corresponding complete refined fan route.
- [`LeanTrominoes/RetainedAngularFanSpliceInterface.lean`](LeanTrominoes/RetainedAngularFanSpliceInterface.lean)
  fixes the combined source/router refinement at `36 * 8 = 288` and packages
  the exact outer-adapter demand.  Its source gate is a radial multiple of a
  radius-288 direction interface, its inner endpoint is the certified
  radius-264 fan-route head, and genuine occurrence lookup selects the demand
  carrying the occurrence's exact classified terminal datum.
- [`LeanTrominoes/RetainedAngularFanOuterRadialRoutes.lean`](LeanTrominoes/RetainedAngularFanOuterRadialRoutes.lean)
  starts the outer adapter at each exact scaled source gate.  Eight-unit
  tangential offsets select distinct radius-288 interface ports, and a
  translated retained-ray staircase joins every gate to its port with exact
  endpoints and orthogonality.  The canonical radial tie-break makes these
  parallel lanes advance in occurrence-slot order.
- [`LeanTrominoes/RetainedAngularFanOuterCollarRoutes.lean`](LeanTrominoes/RetainedAngularFanOuterCollarRoutes.lean)
  fills the finite 24-layer collar from those radius-288 lane ports to the
  certified radius-264 fan-route heads.  Rounded square-boundary
  interpolation gives exact endpoints, orthogonality, and shell containment;
  coordinated pairwise rasterization remains the next splice subproblem.
- [`LeanTrominoes/RetainedAngularFanOuterCollarSeparatedRoutes.lean`](LeanTrominoes/RetainedAngularFanOuterCollarSeparatedRoutes.lean)
  supplies that coordinated rasterization.  Neighboring-corridor crossing
  lines handle nine direction families, while explicit nested tracks handle
  the corner-heavy right-arm and southwest families without following the
  inner frame before their own endpoints.
  Finite certification proves exact endpoints, orthogonality, collar
  containment, and strict continuous separation for every
  order-compatible pair.
- [`LeanTrominoes/RetainedAngularFanOuterLocalRoutes.lean`](LeanTrominoes/RetainedAngularFanOuterLocalRoutes.lean)
  joins each separated collar route to its complete refined fan route,
  producing a finite radius-288-to-Figure-7 adapter.  Exhaustive cross-piece
  checks prove strict continuous separation of every order-compatible pair,
  while endpoint, orthogonality, frame, and fan-interior certificates
  describe each complete route; translation positions the same adapter at
  any retained variable center.
- [`LeanTrominoes/RetainedAngularFanOuterCompleteRoutes.lean`](LeanTrominoes/RetainedAngularFanOuterCompleteRoutes.lean)
  splices each source-gate-to-radius-288 radial lane to that positioned
  finite adapter.  Positive profile entries select complete routes with
  exact source-gate and Figure 7 endpoints and certified orthogonality, and
  genuine source occurrences select their exact classified route.  General
  separation of the arbitrary-length radial pieces remains the next layer.
- [`LeanTrominoes/RetainedAngularFanOuterEscapedRoutes.lean`](LeanTrominoes/RetainedAngularFanOuterEscapedRoutes.lean)
  splits off 64 primitive blocks of the original terminal ray before the
  occurrence-lane shift.  This exceeds the maximum 56-unit shift, and at the
  concrete factor-four source scale the escape always fits.  Exact endpoint
  and orthogonality theorems show that it rejoins the unchanged radial tail
  and preserves the radius-288 port and Figure 7 boundary endpoint.
  Independent staircase escapes can still share their first grid step, so
  the direct component families use this layer through coordinated,
  clause-level escape certificates rather than treating the default escape
  as a planarity theorem.
- [`LeanTrominoes/RetainedAngularFanOuterCoordinatedPrefixes.lean`](LeanTrominoes/RetainedAngularFanOuterCoordinatedPrefixes.lean)
  isolates the only clause-specific part of those escape certificates.
  A finite relative route selects the first two primitive blocks jointly at
  a shared clause gate; a generic construction translates it, appends the
  remaining 62 canonical blocks, and packages the result as the exact
  64-block source escape required by the complete outer-fan route.
- [`LeanTrominoes/RetainedAngularFanOuterCoordinatedSeparation.lean`](LeanTrominoes/RetainedAngularFanOuterCoordinatedSeparation.lean)
  factors everything after that escape into one complete tail: the occurrence
  lane shift, remaining radial raster, and local fan adapter.  A generic
  assembly theorem reduces complete-route separation to the escape pair, two
  directed escape--tail pairs, and the tail pair, while preserving the fact
  that the common clause head is the only permitted contact.  A replacement
  corollary also transfers strict separation of the canonical rasterized
  escaped route to any coordinated escape, leaving only that replacement
  escape's interaction with the other complete route to check.
- [`LeanTrominoes/RetainedAngularFanDirectFallbackOuterReduction.lean`](LeanTrominoes/RetainedAngularFanDirectFallbackOuterReduction.lean)
  specializes escape replacement to the finite direct-source atlas.  Under
  strict common-center angular order, both ordinary and delayed-lane
  fallback cases reduce complete outer-route separation to the selected
  direct escape versus the fallback complete route.
- [`LeanTrominoes/RetainedAngularFanDirectSourceEscapeSideBounds.lean`](LeanTrominoes/RetainedAngularFanDirectSourceEscapeSideBounds.lean)
  checks that every point of every finite direct-atlas escape stays strictly
  outside its terminal direction's radius-288 supporting side.  The bound is
  translation-invariant and separates a positioned direct escape from every
  complete local fan adapter at the same center, closing the local half of
  the residual direct-escape/fallback interaction.
- [`LeanTrominoes/RetainedAngularFanDirectSourceEscapeAngularBounds.lean`](LeanTrominoes/RetainedAngularFanDirectSourceEscapeAngularBounds.lean)
  checks both strict-order orientations of the ordinary angular separator
  against every point in every finite direct-atlas escape.  The resulting
  weak/strict bounds are translation-invariant and supply the radial half of
  the residual direct-escape/fallback interaction.
- [`LeanTrominoes/RetainedAngularFanDirectSourceEscapeRadialSeparation.lean`](LeanTrominoes/RetainedAngularFanDirectSourceEscapeRadialSeparation.lean)
  combines those atlas bounds with the canonical ordinary and delayed-lane
  radial bounds.  Strict compatible direction/slot order now separates a
  translated custom direct escape from either kind of fallback radial route
  at the same translated fan center.
- [`LeanTrominoes/RetainedAngularFanDirectSourceFallbackCompleteSeparation.lean`](LeanTrominoes/RetainedAngularFanDirectSourceFallbackCompleteSeparation.lean)
  joins each separated fallback radial to its local adapter and discharges
  the escape premise of the direct-tail replacement reducers.  Strict
  compatible angular order therefore automatically separates the complete
  custom direct route from either ordinary or delayed-lane fallback routes.
- [`LeanTrominoes/RetainedAngularFanOuterRouteTranslation.lean`](LeanTrominoes/RetainedAngularFanOuterRouteTranslation.lean)
  proves that source gates, lane shifts, local adapters, and ordinary and
  delayed-lane radial and complete outer routes all commute with translation
  of their variable center.  Local direct/fallback certificates can therefore
  be transported without unfolding the final positioned route definitions.
- [`LeanTrominoes/RetainedAngularFanDirectSourcePositionedFallbackSeparation.lean`](LeanTrominoes/RetainedAngularFanDirectSourcePositionedFallbackSeparation.lean)
  transports the automatic strict-order separation theorem through a checked
  direct choice's physical component offset.  Its complete positioned route
  now avoids either ordinary or delayed-lane fallback complete routes at the
  same positioned fan center.
- [`LeanTrominoes/RetainedAngularFanFinalDirectSourceTerminalClassification.lean`](LeanTrominoes/RetainedAngularFanFinalDirectSourceTerminalClassification.lean)
  specializes successful final direct-choice representation to an exact
  unscaled terminal-classification theorem.  Later alignment arguments can
  use the atlas direction directly without expanding source scaling or the
  full final route selector.
- [`LeanTrominoes/RetainedAngularFanDirectSourceSegmentClassification.lean`](LeanTrominoes/RetainedAngularFanDirectSourceSegmentClassification.lean)
  classifies the positioned source segment stored by any successful direct
  choice directly from the finite atlas.  Mixed alignment arguments can now
  avoid reconstructing the full final direct-route metadata.
- [`LeanTrominoes/RetainedAngularFanFinalFallbackSegmentClassification.lean`](LeanTrominoes/RetainedAngularFanFinalFallbackSegmentClassification.lean)
  transfers a genuine final source route's retained-terminal classification
  to its explicit penultimate-to-final segment, matching the endpoint form
  used by the mixed direct/fallback alignment argument.
- [`LeanTrominoes/RetainedAngularFanDirectSourceMixedDirectionInequality.lean`](LeanTrominoes/RetainedAngularFanDirectSourceMixedDirectionInequality.lean)
  proves that an oblique selected direct segment cannot share a retained
  terminal direction with any classified axis-aligned segment.  The final
  fallback branch instantiates this small geometry lemma with its endpoint
  classification and failed-choice alignment certificate.
- [`LeanTrominoes/RetainedAngularFanFinalDirectSourceAlignedOrthogonality.lean`](LeanTrominoes/RetainedAngularFanFinalDirectSourceAlignedOrthogonality.lean)
  records the complementary aligned direct-source branch: because every
  successful choice represents an exact two-point route, alignment of its
  stored segment recovers orthogonality of the original final source route.
- [`LeanTrominoes/RetainedAngularFanFinalCrossClauseSourceRouteSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalCrossClauseSourceRouteSeparation.lean)
  extracts a choice-independent consequence of inherited source planarity:
  original final source routes belonging to different clauses avoid each
  other.  This is the reusable geometric input for aligned mixed terminals.
- [`LeanTrominoes/RetainedTerminalDataEndpointSeparation.lean`](LeanTrominoes/RetainedTerminalDataEndpointSeparation.lean)
  packages the shared-endpoint direction-separation theorem in whole
  terminal-data records, avoiding expensive normalization of direction and
  length projections during final-route composition.
- [`LeanTrominoes/RetainedAngularFanFinalMixedAlignedDirectionSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalMixedAlignedDirectionSeparation.lean)
  combines source-route separation with direct and fallback orthogonality.
  Aligned mixed routes ending at one canonical variable center must therefore
  have different classified terminal directions.
- [`LeanTrominoes/RetainedAngularFanFinalMixedDirectionSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalMixedDirectionSeparation.lean)
  joins the aligned planarity branch with exact classified-segment separation
  for oblique direct choices, giving unconditional direction inequality for
  same-center direct/fallback pairs from different clauses.
- [`LeanTrominoes/RetainedAngularFanFinalMixedAlignedCorridorSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalMixedAlignedCorridorSeparation.lean)
  lifts inherited strict prefix separation through orthogonal source-route
  rectangles, automatically producing the mixed source corridor whenever
  the selected direct segment is axis-aligned.
- [`LeanTrominoes/RetainedAngularFanFinalMixedCenter.lean`](LeanTrominoes/RetainedAngularFanFinalMixedCenter.lean)
  transports equality of canonical direct/fallback literal positions to
  equality of their fully refined physical fan centers, matching the center
  expected by the positioned outer-route separation certificates.
- [`LeanTrominoes/RetainedAngularFanDirectSourcePositionedScaledFallbackSeparation.lean`](LeanTrominoes/RetainedAngularFanDirectSourcePositionedScaledFallbackSeparation.lean)
  specializes positioned strict-order separation to the scaled fallback
  terminal data used by the final router.  Equal physical centers now give
  the exact ordinary and delayed-lane outer-route avoidance certificates
  needed in the overlapping mixed branch.
- [`LeanTrominoes/RetainedAngularFanFinalMixedOuterSelection.lean`](LeanTrominoes/RetainedAngularFanFinalMixedOuterSelection.lean)
  performs the final router's singleton-prefix case split.  Strict angular
  order at an equal physical center now separates a direct route from the
  actually selected ordinary or delayed-lane fallback outer replacement.
- [`LeanTrominoes/RetainedAngularFanFinalMixedOrderedOccurrenceAssembly.lean`](LeanTrominoes/RetainedAngularFanFinalMixedOrderedOccurrenceAssembly.lean)
  threads selected outer-route avoidance through the source corridor,
  fallback-boundary splice, and both Figure 7 suffix interactions.  A
  non-routed direct occurrence and cross-clause fallback occurrence are now
  completely separated once strict order and their common physical center
  are supplied.  A same-center wrapper derives those facts, terminal
  positivity, and escape room automatically, leaving only the source
  corridor as an explicit geometric premise.  An atlas-kind-independent
  same-center wrapper instead accepts strict separation from the fully
  refined fallback source prefix; it derives outer-route avoidance from the
  same order data and reuses the complete boundary-and-suffix assembly.
- [`LeanTrominoes/RetainedAngularFanFinalMixedAlignedOccurrenceSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalMixedAlignedOccurrenceSeparation.lean)
  discharges that last corridor premise for every axis-aligned successful
  direct segment.  Consequently a non-routed aligned direct occurrence and
  a same-center cross-clause fallback occurrence automatically have strictly
  disjoint complete routes in the final coordinated drawing.
- [`LeanTrominoes/RetainedAngularFanFinalMixedOccurrenceSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalMixedOccurrenceSeparation.lean)
  derives the oblique mixed occurrence theorem from the flat-component
  corridor and combines it with the aligned branch for non-routed choices.
  For a routed-clause choice it combines flat-macrocell prefix reduction,
  the specialized inward carrier-boundary escape, and ordinary corridor
  control of the remaining tail.  These cases yield unconditional
  same-center cross-clause direct/fallback separation for every successful
  direct choice.  Its routed-clause argument is factored through an abstract
  selected-outer-route certificate, so the same wide-prefix reduction also
  applies away from a shared variable center.
- [`LeanTrominoes/RetainedAngularFanFinalMixedDistinctCenterSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalMixedDistinctCenterSeparation.lean)
  completes the complementary distinct-center mixed proof for every direct
  choice.  When the selected
  direct source segment is axis-aligned, failure of the other selector makes
  its source segment axis-aligned as well.  Distinct clause heads, distinct
  literal centers, and retained source compatibility then separate the two
  terminal rectangles, which combines with the established source corridor
  to separate the complete direct and fallback occurrences.  For an oblique
  direct segment, flat physical-component reduction, normalized carrier
  contact geometry, and the finite equality-lens certificate separate the
  terminal rectangles; the certificate's equal-endpoint alternative
  contradicts the distinct canonical literal centers.  The aligned and
  oblique branches are combined, while routed-clause choices reuse their
  specialized wide-prefix reduction with rectangle-separated outer fans.
  The result is one unconditional complete-occurrence theorem.
- [`LeanTrominoes/RetainedAngularFanFinalMixedPublicSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalMixedPublicSeparation.lean)
  identifies the selected fallback boundary join and direct occurrence with
  their total route-family lookups.  The same- and distinct-center theorems,
  including routed-clause direct choices, are therefore combined at the
  public interface in both route orders with no center hypothesis.
- [`LeanTrominoes/RetainedAngularFanFinalCrossClausePublicSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalCrossClausePublicSeparation.lean)
  hides the final route selector for two copied-source incidences in
  different clauses.  Its four-way selector split dispatches to the completed
  direct/direct, fallback/fallback, and two mixed separation theorems, yielding
  one unconditional public `RoutesAvoidEachOther` certificate for later
  whole-family planarity assembly.  A second wrapper handles any two distinct
  copied-source incidence keys: indexed clause uniqueness sends equal clause
  indices to the same-clause theorem, while unequal indices use the unified
  cross-clause result.
- [`LeanTrominoes/RetainedAngularFanFinalPublicRouteSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalPublicRouteSeparation.lean)
  proves pairwise continuous separation for every two distinct genuine
  incidence keys in the complete final fixed-eight family.  It removes the
  final coordinate scaling, recovers copied-source metadata or a relative
  implication-cycle index at the append boundary, and dispatches the four
  source/source, source/cycle, cycle/source, and cycle/cycle cases to their
  public separation theorems.
- [`LeanTrominoes/OrthogonalPolylineLoopErasure.lean`](LeanTrominoes/OrthogonalPolylineLoopErasure.lean)
  supplies the route-normalization layer needed before ribbon thickening.
  Some coordinated collar routes are certified orthogonal walks but revisit
  lattice points, so they are not simple as listed.  The normalizer first
  inserts every unit axis step, regards the result as a walk in the unit-grid
  graph, and applies Mathlib's verified loop bypass.  It proves that the
  result preserves both endpoints, retains only source unit edges and points,
  remains orthogonal, and is geometrically simple.  A total computable
  wrapper makes this operation available to the final incidence-route
  family without proof arguments in its definition.
- [`LeanTrominoes/RetainedAngularFanFinalNormalizedRouteFamily.lean`](LeanTrominoes/RetainedAngularFanFinalNormalizedRouteFamily.lean)
  applies the loop-erasure normalizer to every final coordinated incidence
  route.  For every genuine incidence it proves that normalization preserves
  both canonical endpoints and orthogonality, and that the resulting route
  is geometrically simple (including vertex/interior and distinct-segment
  interior avoidance).  It also packages the normalized routes in the
  standard canonical orthogonal-family interface.
- [`LeanTrominoes/OrthogonalPolylineLoopErasureSeparation.lean`](LeanTrominoes/OrthogonalPolylineLoopErasureSeparation.lean)
  proves that complete continuous separation survives normalization.  Each
  retained dart is traced to a unit-subdivision edge and then to an original
  parent segment; an intersection after loop erasure would therefore give
  an intersection before it.  Unit edges make point/interior contacts
  impossible, while endpoint-only contacts transfer through the preserved
  outer endpoints.
- [`LeanTrominoes/RetainedAngularFanFinalNormalizedRouteSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalNormalizedRouteSeparation.lean)
  applies that generic transport theorem to the final construction, proving
  complete zero-shift continuous separation for every pair of distinct
  genuine normalized incidences.
- [`LeanTrominoes/RetainedAngularFanFinalNormalizedDrawing.lean`](LeanTrominoes/RetainedAngularFanFinalNormalizedDrawing.lean)
  assembles the normalized routes into the positioned periodic incidence
  drawing.  It proves exact graph-route endpoint matching, unit-step support,
  orthogonality, and unconditional integer-grid planarity.  The remaining
  ribbon-ready obligations are the stronger translated continuous and
  listed-point contact conditions.  It also identifies the concrete drawing
  definitionally with drawing-level normalization of the coordinated source,
  so route-independent certificates and geometric bounds can be transported
  through the generic normalization interface.
- [`LeanTrominoes/PeriodicGridDrawingLoopErasure.lean`](LeanTrominoes/PeriodicGridDrawingLoopErasure.lean)
  lifts verified loop erasure from one polyline to an entire periodic grid
  drawing.  It preserves exact route endpoints, graph compatibility,
  orthogonality, unit-step structure, and both fundamental-square and open
  halo route-point bounds.  Later stages can therefore normalize inherited
  routes without rebuilding their finite-presentation bookkeeping or halo
  estimates.
- [`LeanTrominoes/PeriodicGridDrawingLoopErasureRouteOrders.lean`](LeanTrominoes/PeriodicGridDrawingLoopErasureRouteOrders.lean)
  isolates the exact condition under which loop erasure also preserves the
  cyclic route orders used by the ribbon source fans.  It first handles
  simple routes, where normalization is just ordered unit subdivision, and
  then proves the sharper endpoint-isolation criterion needed by the actual
  construction: interior loops are allowed as long as the route does not
  revisit its clause or variable endpoint.  Memberwise versions transfer the
  variable occurrence order, ternary clause order, or both at once; the
  remaining concrete task is to establish those endpoint-isolation
  conditions for the inherited final exact-one splices.
- [`LeanTrominoes/PeriodicGridDrawingLiftedRouteSeparation.lean`](LeanTrominoes/PeriodicGridDrawingLiftedRouteSeparation.lean)
  bridges pairwise complete-route geometry back to the global periodic
  drawing interface.  If every two distinct lifted route occurrences avoid
  each other and each stored route is simple, then all globally indexed
  segment interiors are disjoint and all listed-point contacts occur only at
  outer endpoints.  Unit-step support therefore promotes the drawing to the
  exact ribbon-ready predicate; same-route, same-translate comparisons are
  discharged from simplicity rather than left implicit.  A translation-
  invariant equivalent form fixes the first route at shift zero and asks
  only about the second route's relative periodic shift, matching the local
  macrocell geometry used by the remaining construction.  Conversely, a
  ribbon-ready unit-step drawing with nondegenerate routes supplies that
  relative complete-route predicate directly.
- [`LeanTrominoes/PositionedPeriodicCNFRelativeRouteSeparation.lean`](LeanTrominoes/PositionedPeriodicCNFRelativeRouteSeparation.lean)
  transports that relative-shift predicate through the lossless flat route
  enumeration.  The remaining geometry can therefore quantify over genuine
  metadata-rich clause/literal incidences while retaining exactly the route
  indices used to distinguish periodic occurrences.  It also transports
  relative separation through pointwise orthogonal loop erasure.  Distinct
  flattened incidence indices are reflected to distinct clause/literal
  coordinates, and the relative obligation is decomposed into distinct
  zero-shift incidences versus arbitrary incidences at nonzero lattice shifts.
- [`LeanTrominoes/PositionedPeriodicCNFRelativeRouteSeparationScaling.lean`](LeanTrominoes/PositionedPeriodicCNFRelativeRouteSeparationScaling.lean)
  proves that the metadata-rich relative certificate survives every positive
  integral coordinate refinement.  Scaling leaves the logical incidence
  enumeration unchanged and commutes with semantic period translation, while
  injectivity of positive scaling transports all four continuous route-contact
  conditions.
- [`LeanTrominoes/PositionedPeriodicCNFRelativeRouteSeparationOrdering.lean`](LeanTrominoes/PositionedPeriodicCNFRelativeRouteSeparationOrdering.lean)
  gives an equivalent coordinate-indexed form of relative separation and
  transports it through stable clause-direction sorting.  It follows each
  original tagged literal through the permutation, combines the two
  route-specific anchor gauges with the requested relative shift, and then
  translates the source separation certificate back to the reordered
  representatives.  Presentation indices, rather than literal values, keep
  the argument valid when a clause contains duplicate literal values.
- [`LeanTrominoes/RetainedAngularFanFinalSourceRelativeRouteSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalSourceRelativeRouteSeparation.lean)
  packages the retained pre-split drawing's global continuous planarity,
  endpoint-only contacts, segment-endpoint/interior avoidance, and
  nondegenerate route lengths into complete separation for every pair of
  periodic incidence occurrences, including after any positive source
  refinement.  This supplies the metadata-rich relative source certificate
  needed to transport inherited route geometry through clause-direction
  ordering and the later exact-one splices.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeSourcePrefixSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeSourcePrefixSeparation.lean)
  specializes that periodic certificate to the source-prefix pieces retained
  by the final angular-fan replacement.  Nonzero period shifts force the two
  clause heads apart; deleting both final variable points then upgrades
  endpoint-only source separation to strict contact-free prefix separation,
  even when the two translated incidences share their variable endpoint.
  The result is also transported through the complete source-first scaling.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeDirectSourceModels.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeDirectSourceModels.lean)
  identifies semantic translation of every successful public direct-source
  route with translation of its checked finite-atlas choice's component
  origin.  The atlas positioning offset is proved equal to the fully refined
  drawing period shift, and the represented source segment translates in the
  same unscaled retained-source frame.  Periodic direct-route geometry can
  therefore reuse the existing finite complete-Figure-7 models.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeDirectSourceSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeDirectSourceSeparation.lean)
  proves strict separation of two successful direct-source routes across
  every nonzero period shift.  Different translated component origins use
  disjoint macrocell envelopes; coincident origins are classified into the
  finite crossover or duplicator atlas, with translated target equality
  recovering the wrapped atom and the semantic angular-slot order.
- [`LeanTrominoes/RetainedAngularFanSourceSpliceTranslation.lean`](LeanTrominoes/RetainedAngularFanSourceSpliceTranslation.lean)
  proves exact translation covariance for the ordinary and delayed-lane
  fallback source splices.  Tail replacement and whole retained-ray
  rasterization commute with translation, while the source offset is scaled
  through the terminal refinement before positioning the translated outer
  fan.  This exposes translated fallback routes by the same geometric pieces
  used in the within-cell separation proof.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeFallbackSourceModels.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeFallbackSourceModels.lean)
  gives the public failed-selector route an exact periodic model: the same
  singleton-prefix policy rebuilds its ordinary or delayed-lane boundary from
  the translated retained source route, then joins the translated unchanged
  Figure 7 suffix.  The fully refined drawing period is identified with the
  terminal refinement of the source-scaled semantic period.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedSourceSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedSourceSeparation.lean)
  starts the periodic direct/fallback geometry.  A translated Figure 7
  occurrence suffix retains its radius-96 bound around the translated
  canonical center, so every direct source-to-boundary route whose
  source-segment envelope excludes that center is strictly separated from
  the suffix.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedSourceCorridorSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedSourceCorridorSeparation.lean)
  upgrades periodic retained-source planarity to strict separation.  Distinct
  targets separate the complete routes; at a shared target, deleting the
  translated fallback endpoint still separates its prefix from the complete
  direct route.  Physical component reduction and the arbitrary common-frame
  carrier boundary now turn this prefix separation into the translated source
  corridor for every successful direct route at a nonzero shift, including
  the non-axis-aligned residual case.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeRoutedClausePrefixSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeRoutedClausePrefixSeparation.lean)
  extends that arbitrary-shift prefix result through the routed-clause
  choice's customized escape.  It recovers the raw routed-clause source and
  its exact physical origin, applies either scaled component rectangles or
  the transported carrier half-plane there, and joins the escape to the
  corridor-controlled radial and local tails.  Consequently every successful
  direct replacement strictly avoids a translated failed-choice scaled
  prefix at every nonzero relative shift.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeTranslatedFallbackOuterSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeTranslatedFallbackOuterSeparation.lean)
  models the selected ordinary-or-escaped outer fan at a translated fallback
  endpoint.  Its radius-288 terminal-segment envelope is disjoint from every
  aligned direct envelope at a nonzero shift with distinct canonical targets.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeTranslatedFallbackBoundarySeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeTranslatedFallbackBoundarySeparation.lean)
  assembles the translated retained prefix and selected outer fan.  Thus a
  successful aligned direct source-to-boundary route strictly avoids the
  complete translated failed-choice boundary under the same hypotheses.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedOccurrenceSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedOccurrenceSeparation.lean)
  moves a direct Figure 7 suffix backward into the fallback cell and applies
  the complete fallback-versus-radius-96 theorem there.  Translating forward
  separates that suffix from the whole translated fallback occurrence.  The
  four piece pairs then assemble into complete public relative separation for
  every aligned successful/failed pair at distinct translated centers; shift
  negation and symmetry also supply the failed/successful orientation.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedSameCenterOrder.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedSameCenterOrder.lean)
  handles the metadata of a nonzero translated center coincidence.  It proves
  distinct stored occurrences of one atom and strict direct/fallback terminal
  order for both aligned and oblique direct choices.  The oblique branch uses
  the fallback's classified axis-aligned final segment to rule out equal
  terminal directions.  Equality of the physical fan centers then separates
  either direct route from the translated selected outer replacement.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedSameCenterBoundarySeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedSameCenterBoundarySeparation.lean)
  combines that order with the all-choice translated scaled-prefix theorem.
  Every successful direct boundary, aligned or oblique, therefore strictly
  avoids the complete translated failed-choice boundary even at a shared
  physical target.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedSameCenterSpokeSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedSameCenterSpokeSeparation.lean)
  identifies both suffixes at a shared physical target with positioned copies
  of the same finite Figure 7 spoke family.  Strict angular order makes their
  slots different, which proves both direct-prefix/fallback-suffix and
  direct-suffix/fallback-suffix separation.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedSameCenterFallbackSpokeSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedSameCenterFallbackSpokeSeparation.lean)
  proves the slot-parametric complementary interaction: a selected ordinary
  or singleton-escaped fallback boundary avoids every other spoke at its own
  center.  Translating this local certificate proves direct-suffix versus
  translated-fallback-boundary separation.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedSameCenterOccurrenceSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedSameCenterOccurrenceSeparation.lean)
  combines the four boundary/suffix cross interactions into strict separation
  of the complete direct and translated fallback occurrence routes at a
  shared physical target.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedCompleteSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedCompleteSeparation.lean)
  splits on translated target-center equality and thereby removes that
  geometric side condition from aligned successful/failed relative route
  separation.  Shift negation supplies the reverse failed/successful order.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeCopiedSourceReduction.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeCopiedSourceReduction.lean)
  reduces the last copied-source periodic separation premise to its selector
  cases.  All zero-shift, direct/direct, and mixed-selector cases are now
  discharged by public theorems, leaving only failed/failed route separation
  at a nonzero shift.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeFallbackSameCenterData.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeFallbackSameCenterData.lean)
  proves that failed-choice routes meeting at one physical target across a
  nonzero period shift still have different stored occurrence slots and
  different orthogonal terminal directions, and combines both facts with
  the retained terminal profile to recover their strict angular order.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeFallbackPrefixOuterSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeFallbackPrefixOuterSeparation.lean)
  proves the center-independent cross interaction needed for two translated
  failed-choice boundaries: the fully refined translated source prefix of
  either fallback strictly avoids the other fallback's policy-selected
  ordinary or delayed-lane outer replacement at every nonzero shift.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeFallbackSameCenterOuterSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeFallbackSameCenterOuterSeparation.lean)
  handles the complementary shared-target interaction.  Strict agreement of
  terminal-direction and occurrence-slot order separates the two selected
  outer replacements across all four ordinary/delayed-lane policy pairs,
  after transporting the second fan center through the period translation.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeFallbackSameCenterBoundarySeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeFallbackSameCenterBoundarySeparation.lean)
  assembles the four prefix/outer interactions into strict separation of the
  two complete selected fallback boundaries at a shared translated target.
  Reverse-shift transport supplies the asymmetric unshifted-prefix versus
  translated-outer case and records covariance of both selected pieces.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeFallbackSameCenterOccurrenceSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeFallbackSameCenterOccurrenceSeparation.lean)
  identifies both occurrence suffixes with translated copies of the finite
  Figure 7 spoke family at the common center.  Distinct slots separate both
  boundary/spoke orientations and the spoke pair, and endpoint joins then
  separate the two complete fallback occurrence routes.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeFallbackDistinctCenterBoundarySeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeFallbackDistinctCenterBoundarySeparation.lean)
  handles the other target-center branch.  Relative route separation gives
  disjoint discarded terminal rectangles; conservative outer-fan bounds and
  the already symmetric prefix interactions then assemble strict separation
  of the two selected fallback boundaries.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeFallbackDistinctCenterOccurrenceSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeFallbackDistinctCenterOccurrenceSeparation.lean)
  extends the distinct-center boundary result through the unchanged Figure 7
  suffixes.  Point-neighborhood separation is applied in both relative
  orientations, one certificate is transported back to the original frame,
  and endpoint joins assemble the complete translated fallback occurrences.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeFallbackCompleteSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeFallbackCompleteSeparation.lean)
  combines the shared-target and distinct-target branches into unconditional
  strict separation of two failed-choice occurrence routes at every nonzero
  shift.  Composing this with the completed oblique mixed theorem discharges
  every copied-source selector case and proves that the final normalized
  fixed-eight periodic incidence drawing is ribbon-ready without additional
  geometric premises.
- [`LeanTrominoes/RetainedFinalRouteMacrocellShapeClassification.lean`](LeanTrominoes/RetainedFinalRouteMacrocellShapeClassification.lean)
  extends the final macrocell wrapper from flat routes to arbitrary period
  occurrences.  Equal physical centers transfer direct-component shape, so
  a failed selector and a successful selector can never occupy the same
  translated noncarrier macrocell.
- [`LeanTrominoes/RetainedFinalRouteCarrierBounds.lean`](LeanTrominoes/RetainedFinalRouteCarrierBounds.lean)
  supplies the complementary arbitrary-shift carrier-lens wrapper and its
  narrow translated bounding rectangle.  Carrier/macrocell occurrence pairs
  therefore yield the source-prefix raster certificate whenever those two
  explicit enclosing rectangles are separated.
- [`LeanTrominoes/RetainedFinalRouteCarrierMacrocellOverlapNormalization.lean`](LeanTrominoes/RetainedFinalRouteCarrierMacrocellOverlapNormalization.lean)
  moves arbitrary carrier and macrocell occurrences into their common
  physical frame.  The four translated rectangle corners reduce exactly to
  a relative carrier link and the original macrocell center, preserving and
  reflecting the remaining overlap test.
- [`LeanTrominoes/RetainedFinalRouteCarrierFrameOverlapNormalization.lean`](LeanTrominoes/RetainedFinalRouteCarrierFrameOverlapNormalization.lean)
  gives the complementary common-frame normalization that keeps the
  carrier's original selected retained link fixed and translates the
  macrocell by the opposite relative shift; overlap then places the relative
  macrocell center on that selected carrier's supporting segment.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierLiftedVertexOccurrenceProximity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierLiftedVertexOccurrenceProximity.lean)
  strengthens retained-carrier terminal proximity to arbitrary lifts of a
  declared clause or variable vertex.  A carrier endpoint at that lift is
  converted back into an exact globally represented routed occurrence
  without first assuming the translated site belongs to the finite retained
  enumeration.
- [`LeanTrominoes/RetainedFinalRouteCarrierFrameTerminalContacts.lean`](LeanTrominoes/RetainedFinalRouteCarrierFrameTerminalContacts.lean)
  applies that arbitrary-lift proximity in the selected carrier frame.
  Overlapping routed-clause and routed-variable direct components yield exact
  source- and target-terminal incidences, reducing the direct-source case to
  those two contacts plus one translated-crossover residue.
- [`LeanTrominoes/RetainedFinalRouteCarrierCrossoverNormalizedContact.lean`](LeanTrominoes/RetainedFinalRouteCarrierCrossoverNormalizedContact.lean)
  begins the translated-crossover branch by normalizing its halo crossing to
  the fundamental square.  The correspondingly translated selected carrier
  support contains that canonical point, which proves its occurrence is
  neighboring and hence that the translated link is a raw retained lens;
  preserved overlap then gives exact incidence with the canonical crossover.
- [`LeanTrominoes/RetainedFinalRouteCommonFrameSelections.lean`](LeanTrominoes/RetainedFinalRouteCommonFrameSelections.lean)
  reindexes any recovered final route into an arbitrary finite component
  frame, proves exact route equivariance under the compensating physical
  translation, and transports its local clause and literal indices for the
  common carrier-boundary argument.
- [`LeanTrominoes/RetainedFinalRouteCommonFrameSourceSelections.lean`](LeanTrominoes/RetainedFinalRouteCommonFrameSourceSelections.lean)
  turns those translated indices into genuine routes of concrete finite
  drawings: through a formula-realizing presentation for noncarriers and
  through raw retained-link membership for carriers.
- [`LeanTrominoes/RetainedFinalRouteContactCommonFrameSources.lean`](LeanTrominoes/RetainedFinalRouteContactCommonFrameSources.lean)
  constructs those concrete noncarrier presentations from arbitrary terminal
  contacts and canonical crossover normalization.  In particular, it proves
  directly that translated active routed-variable arms still realize their
  abstract two-clause formulas, without requiring the translated presentation
  to lie in the retained enumeration window.
- [`LeanTrominoes/RetainedFinalRouteCommonFrameOffsets.lean`](LeanTrominoes/RetainedFinalRouteCommonFrameOffsets.lean)
  proves that the independently reindexed carrier and direct routes receive
  the same compensating physical translation in both the terminal and
  normalized-crossover cases.
- [`LeanTrominoes/RetainedFinalRouteCommonFrameBoundaryTranslation.lean`](LeanTrominoes/RetainedFinalRouteCommonFrameBoundaryTranslation.lean)
  transports a carrier-boundary certificate from such a common finite frame
  back to the two original final route occurrences.
- [`LeanTrominoes/RetainedFinalRouteCommonFrameBoundaries.lean`](LeanTrominoes/RetainedFinalRouteCommonFrameBoundaries.lean)
  applies the raw carrier-lens interface geometry in those frames and obtains
  an outside/inside carrier-boundary certificate for every arbitrary
  overlapping carrier/direct pair, covering both terminal contacts and the
  normalized crossover residue.  For routed-clause direct occurrences it
  additionally transports the carrier-side outside half-plane to the exact
  physical routed-clause origin.
- [`LeanTrominoes/RetainedFinalRouteCommonFrameTerminalSeparation.lean`](LeanTrominoes/RetainedFinalRouteCommonFrameTerminalSeparation.lean)
  reindexes a successful oblique direct choice and an arbitrary selected
  carrier occurrence into the same physical frame.  The finite equality-lens
  endpoint calculation then proves that every overlapping terminal or
  normalized-crossover contact has strictly separated final-segment
  rectangles unless the two final endpoints coincide, and the dichotomy is
  transported back to the original occurrences.
- [`LeanTrominoes/RetainedFinalRouteCommonFrameCorridorSeparation.lean`](LeanTrominoes/RetainedFinalRouteCommonFrameCorridorSeparation.lean)
  packages an arbitrary final carrier boundary and strict prefix avoidance
  into the refined terminal-corridor predicate.  Isolating this dependent
  boundary projection keeps the larger relative component reduction both
  reusable and tractable for Lean's elaborator.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedComponentCorridorReduction.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedComponentCorridorReduction.lean)
  performs the arbitrary-shift selector/component split for a successful
  direct route against a translated failed route.  Macrocell pairs and
  separated carrier/macrocell boxes produce the exact terminal corridor,
  leaving only an overlapping carrier lens as a local callback.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedObliqueTerminalSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedObliqueTerminalSeparation.lean)
  closes that overlapping carrier callback for final-segment geometry.  A
  common-frame terminal or crossover contact gives separation or equal final
  endpoints; distinct physical canonical literal centers exclude equality.
  The surrounding carrier-box and macrocell-box cases complete strict
  endpoint-rectangle separation for an oblique direct/translated-fallback
  pair.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedObliqueBoundarySeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedObliqueBoundarySeparation.lean)
  scales that terminal separation to the two complete outer replacements and
  combines it with translated source-prefix isolation.  It proves that an
  oblique selected direct boundary avoids the whole translated fallback
  boundary and that the direct replacement avoids the fallback Figure 7
  suffix whenever their physical target centers differ.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeMixedObliqueOccurrenceSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeMixedObliqueOccurrenceSeparation.lean)
  assembles all four boundary/suffix interactions for oblique selected direct
  and translated fallback occurrences.  Distinct centers use the global
  terminal rectangles, while coincident centers use strict angular slot
  order; splitting between them closes the complete oblique mixed-selector
  route family at every nonzero shift.
- [`LeanTrominoes/OrthogonalPolylineLoopErasureTranslation.lean`](LeanTrominoes/OrthogonalPolylineLoopErasureTranslation.lean)
  proves the translation covariance needed by that transport.  Walk
  `dropUntil` and `bypass` commute with injective graph maps, hence translating
  an orthogonal lattice route before normalization exactly translates the
  resulting simple unit path.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedAuxiliaryRouteIsolation.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedAuxiliaryRouteIsolation.lean)
  discharges both endpoint-isolation obligations for every fresh auxiliary
  incidence in the final unit-elimination layer.  The completed auxiliary
  suffix is a singleton, so its spliced route is exactly the already-simple
  normalized local route.  Consequently, two distinct auxiliaries in one
  source-clause block inherit the normalized local drawing's complete
  pairwise separation.  Only inherited source-variable incidences now need
  separate endpoint-isolation and splice geometry.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedSplicedRouteSeparation.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedSplicedRouteSeparation.lean)
  packages the remaining pairwise splice geometry into six component facts:
  local-route avoidance with head-only contact, strict avoidance for both
  local/suffix cross pairs, and suffix avoidance with tail-only contact.  The
  standard local and canonical-suffix endpoint certificates then assemble
  those facts into separation of the complete final routes.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedPairSeparation.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedPairSeparation.lean)
  proves the local-prefix contact condition for an inherited pair in one
  source block: distinct recovered source-occurrence indices give distinct
  splice ports, so the already-separated local routes can meet only at their
  generated clause heads.  The selector-level wrapper obtains those distinct
  source indices automatically from distinct generated incidence coordinates.
  For the source-tail component, simple separated source routes remain
  separated after deleting their obsolete heads and applying the block's
  common refinement transform; every remaining listed contact is confined to
  their variable-side tails.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamily.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamily.lean)
  stores exact generated-to-source occurrence provenance in every selected
  inherited suffix.  Distinct generated incidence coordinates now imply
  distinct selected source incidence coordinates by injectivity of the
  ordered occurrence pairing.  Each selector record also retains its exact
  flattened unit-elimination metadata entry, including the source block and
  generated clause equalities needed by pairwise geometry.  Equal source
  block indices recover equal positioned source clauses and equal generated
  anchors, hence equal scale-and-translation maps for their inherited source
  routes.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedEndpoints.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedInheritedEndpoints.lean)
  identifies an inherited local endpoint with its source-occurrence boundary
  port.  The three possible source-port coordinates are injective, and every
  genuine port is distinct from the generated clause's local vertex.  These
  facts persist in the canonical gauge shared by all generated clauses in a
  source block, so normalized port equality recovers the source index.  When
  source-occurrence provenance is already known, a direct theorem identifies
  the normalized local endpoint with that exact indexed port.
- [`LeanTrominoes/RetainedAngularFanOccurrenceSuffixSimplicity.lean`](LeanTrominoes/RetainedAngularFanOccurrenceSuffixSimplicity.lean)
  certifies the terminal geometry shared by all inherited coordinated
  routes.  Each of the eight explicit Figure 7 spokes is simple, and remains
  so after periodic translation and positive refinement scaling; consequently
  its variable endpoint is isolated after unit subdivision.  The remaining
  work is to exclude that endpoint from the prefixes joined ahead of the
  terminal spoke.
- [`LeanTrominoes/OrthogonalPolylineUnitSubdivisionTranslation.lean`](LeanTrominoes/OrthogonalPolylineUnitSubdivisionTranslation.lean)
  proves that translating an integral orthogonal polyline commutes with its
  ordered unit subdivision.  Injectivity of translation then transports
  both endpoint-isolation certificates to every positioned copy.
- [`LeanTrominoes/RetainedAngularFanDirectOccurrenceEndpointIsolation.lean`](LeanTrominoes/RetainedAngularFanDirectOccurrenceEndpointIsolation.lean)
  checks the complete finite atlas of coordinated direct-source routes and
  all eight Figure 7 terminal spokes.  Although some collar walks revisit
  interior points, none revisits its final variable endpoint; translation
  lifts this exact property to every positioned direct route choice.  The
  fallback branches remain to be treated before the final inherited route
  family can preserve its variable occurrence orders through loop erasure.
- [`LeanTrominoes/OrthogonalPolylineUnitSubdivisionJoin.lean`](LeanTrominoes/OrthogonalPolylineUnitSubdivisionJoin.lean)
  proves that ordered unit subdivision commutes with a correctly matched
  endpoint join, transports isolation forward through a join, and restricts
  final-endpoint isolation back to the joined suffix.  It also turns strict
  continuous separation from any orthogonal witness route through the target
  into endpoint isolation for a joined route with a simple terminal suffix.
- [`LeanTrominoes/OrthogonalPolylineUnitSubdivisionScaling.lean`](LeanTrominoes/OrthogonalPolylineUnitSubdivisionScaling.lean)
  proves that positive integral refinement cannot create a new visit to a
  scaled source-lattice point.  This reflection principle transports both
  first- and final-endpoint isolation through scaling, even when the source
  route has internal loops elsewhere.
- [`LeanTrominoes/RetainedAngularFanFallbackEndpointIsolation.lean`](LeanTrominoes/RetainedAngularFanFallbackEndpointIsolation.lean)
  applies that bridge to both ordinary and delayed-lane retained fallbacks.
  Their source-to-boundary prefixes strictly avoid the matching implication
  cycle, whose selected entering edge ends at the same ring vertex as the
  simple Figure 7 spoke.  Thus neither fallback can revisit its variable
  endpoint after unit subdivision.
- [`LeanTrominoes/RetainedAngularFanFinalFallbackEndpointIsolation.lean`](LeanTrominoes/RetainedAngularFanFinalFallbackEndpointIsolation.lean)
  instantiates those reusable ordinary and delayed-lane certificates with
  the retained source geometry, terminal classification, and exact Figure 7
  spoke used by the final positioned construction.
- [`LeanTrominoes/RetainedAngularFanFinalOccurrenceEndpointIsolation.lean`](LeanTrominoes/RetainedAngularFanFinalOccurrenceEndpointIsolation.lean)
  resolves the final copied-source route selector.  Direct atlas choices,
  ordinary fallbacks, and singleton-prefix escaped fallbacks all isolate the
  same variable endpoint after unit subdivision.
- [`LeanTrominoes/RetainedAngularFanFinalRouteEndpointIsolation.lean`](LeanTrominoes/RetainedAngularFanFinalRouteEndpointIsolation.lean)
  combines copied-source incidences with the appended implication-cycle
  clauses at the public fixed-eight interface.  Existing cycle simplicity
  handles the appended suffix, so every genuine final coordinated route now
  has an isolated variable endpoint.
- [`LeanTrominoes/RetainedAngularFanFinalNormalizedVariableRouteOrder.lean`](LeanTrominoes/RetainedAngularFanFinalNormalizedVariableRouteOrder.lean)
  uses that isolation together with route nondegeneracy and orthogonality to
  carry clockwise variable occurrence order through verified fixed-eight
  loop erasure.  It also proves that every normalized route still contains an
  edge, supplying the nondegeneracy required by the downstream Figure 9
  terminal-direction transport.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsNormalizedRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsNormalizedRoutes.lean)
  applies that normalization at the final unit-free exact-one interface
  consumed by the ribbon and 3DM reductions.  Every genuine route has its
  canonical endpoints, is a geometrically simple unit-step path, and the
  assembled drawing is orthogonal, endpoint-compatible, and integer-grid
  planar.  Simplicity is also lifted from genuine incidences to every stored
  route, and relative separation of the genuine raw incidence routes is now
  the single premise that packages the normalized drawing as ribbon-ready;
  translation-equivariant loop erasure transports that premise automatically.
  The drawing is
  identified with drawing-level normalization of the preceding coordinated
  exact-one drawing for later certificate transport.
- [`LeanTrominoes/RetainedFinalFlatCorridorComponentCases.lean`](LeanTrominoes/RetainedFinalFlatCorridorComponentCases.lean)
  reduces an oblique final source-corridor obligation by the physical
  carrier/macrocell decomposition.  Carrier reference routes are impossible,
  while separated component boxes close automatically, leaving only an
  overlapping carrier--macrocell pair and an equal-macrocell pair.
- [`LeanTrominoes/RetainedFinalFlatFinalSegmentComponentCases.lean`](LeanTrominoes/RetainedFinalFlatFinalSegmentComponentCases.lean)
  supplies the parallel component reduction for the routes' final segments.
  Endpoint containment turns separated carrier or macrocell boxes directly
  into separated segment rectangles without assuming axis alignment; an
  oblique reference again rules out its carrier branch, isolating the same
  overlap and equal-center residues.
- [`LeanTrominoes/RetainedDirectSourceEqualityLensFinalSegmentSeparation.lean`](LeanTrominoes/RetainedDirectSourceEqualityLensFinalSegmentSeparation.lean)
  proves the terminal geometry needed at that remaining carrier overlap.
  An exact finite certificate for the oblique direct-route atlas, together
  with translation invariance and symbolic equality-lens bounds, shows that
  a direct terminal rectangle and either endpoint of a retained equality
  lens are strictly separated unless both routes finish at that endpoint.
  Intrinsic-link and natural-index wrappers expose the certificate directly
  to normalized carrier route selections.
- [`LeanTrominoes/RetainedFinalFlatNormalizedTerminalContactSeparation.lean`](LeanTrominoes/RetainedFinalFlatNormalizedTerminalContactSeparation.lean)
  applies that finite lens certificate at every normalized carrier contact.
  It recovers exact direct-atlas and intrinsic carrier-lens selections,
  identifies their common physical origin for crossover, routed-clause, and
  routed-variable contacts, and proves that the two selected final rectangles
  are strictly separated unless their final endpoints coincide.
- [`LeanTrominoes/RetainedAngularFanFinalFallbackMacrocellSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalFallbackMacrocellSeparation.lean)
  excludes the equal-macrocell residue for failed choices.  At its general
  interface, any second route already known to come from a direct component
  makes both equal-center components direct, contradicting the failed
  selector because every genuine direct-component route produces a
  successful checked choice.  Conversely, a successful final selector now
  certifies that its recovered occurrence witness belongs to a direct
  component, so a failed fallback macrocell and a successfully selected
  direct macrocell are proved to have unequal translated centers without any
  extra geometric premise.  The earlier oblique-reference theorem is a
  corollary that obtains directness from the terminal geometry.
- [`LeanTrominoes/RetainedAngularFanFinalMixedObliqueCorridorSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalMixedObliqueCorridorSeparation.lean)
  closes the source-prefix corridor for a failed fallback route against an
  oblique selected direct route.  It combines flat component reduction,
  normalized carrier boundaries, and recovered incidence indices to
  discharge both residual configurations.
- [`LeanTrominoes/RetainedAngularFanOuterEscapedTailCardinalBounds.lean`](LeanTrominoes/RetainedAngularFanOuterEscapedTailCardinalBounds.lean)
  bounds every point of a cardinal escaped complete tail in the inward
  half-plane 64 blocks beyond its source gate.  Its separation corollary
  reduces avoidance of any route on the opposite side to one pointwise
  linear lower bound, which is the certificate needed for the singleton
  equality-lens fallback.
- [`LeanTrominoes/RetainedAngularFanEqualityLensSingletonGeometry.lean`](LeanTrominoes/RetainedAngularFanEqualityLensSingletonGeometry.lean)
  classifies the two possible singleton-prefix routes in an equality lens
  after arbitrary signed-axis placement.  Each has a cardinal terminal of
  length at least two, while the other route in its clause remains on the
  source gate's outward side under every natural scaling.  It then checks the
  finite 64-block escape geometry and combines it with the strict post-escape
  half-plane bound, proving that the complete escaped fan and partner prefix
  remain continuously separated and meet only at their common clause head.
- [`LeanTrominoes/RetainedAngularFanCarrierLensSingletonGeometry.lean`](LeanTrominoes/RetainedAngularFanCarrierLensSingletonGeometry.lean)
  transports that complete singleton-fallback certificate through the
  route-preserving endpoint and planar-SAT variable renamings, so it applies
  directly to every geometrically certified retained carrier lens.
- [`LeanTrominoes/RetainedAngularFanFinalCarrierLensSingletonGeometry.lean`](LeanTrominoes/RetainedAngularFanFinalCarrierLensSingletonGeometry.lean)
  absorbs a final zero-shift occurrence's clause-anchor translation into its
  carrier link, identifies the physical route with that anchor-normalized
  lens route, and lifts the complete escaped-fallback separation certificate
  to the final retained route family.  It also recovers the carrier
  equality clause's two-literal bound and proves that every segment of the
  translated final carrier occurrence remains axis-aligned.
- [`LeanTrominoes/RetainedRayRasterizationTranslation.lean`](LeanTrominoes/RetainedRayRasterizationTranslation.lean)
  proves that both retained-ray raster families and endpoint joins commute
  with translation.  It also transports ordinary continuous avoidance and
  head-only contact certificates, letting a finite source atlas proved at
  the origin be reused at any shared clause gate.
- [`LeanTrominoes/RetainedAngularFanDirectSourcePrefixAtlas.lean`](LeanTrominoes/RetainedAngularFanDirectSourcePrefixAtlas.lean)
  gives the finite two-block choices for all 26 crossover clauses, both
  clauses of each duplicator arm, and the routed three-arm source clause.
  Executable certificates check every entry's endpoint and orthogonality and
  prove that distinct 64-block escapes in each direct clause are continuously
  separated and meet only at their shared head.
- [`LeanTrominoes/RetainedAngularFanDirectSourcePrefixProfiles.lean`](LeanTrominoes/RetainedAngularFanDirectSourcePrefixProfiles.lean)
  matches that atlas to the construction's fixed local formulas.  Finite
  checks prove that every crossover and duplicator-arm clause has exactly one
  entry per literal and that every selected entry has the route's exact
  classified terminal direction; routed clauses select the same certificate
  by their physical left, middle, or right arm.
- [`LeanTrominoes/RetainedAngularFanDirectSourcePrefixSelections.lean`](LeanTrominoes/RetainedAngularFanDirectSourcePrefixSelections.lean)
  turns retained planar-SAT clause metadata and a genuine literal index into
  a typed atlas selection.  Crossover and routed-variable selections recover
  their bounded local clause indices, while a routed source clause selects by
  physical arm even for a reordered subset of its three ports; every case
  carries equality with the positioned local route's classified direction.
  Its pair interface proves distinct literals select distinct entries of one
  common profile and immediately transports the atlas's separation and
  head-only-contact certificate to any shared clause gate.  It also packages
  those entries as the exact 64-block source-escape certificates for the two
  actual centers, lengths, and occurrence slots once their demand gates are
  identified with that common clause gate.  The pair interface feeds those
  certificates directly into the complete-route assembly, reducing the
  remaining same-clause geometry to the two escape--tail directions and
  tail--tail strict separation.
- [`LeanTrominoes/RetainedAngularFanDirectSourceCompleteTails.lean`](LeanTrominoes/RetainedAngularFanDirectSourceCompleteTails.lean)
  recovers the concrete two-point local route, factor-four fan center, scaled
  terminal datum, coordinated escape, and complete tail from each direct
  atlas index.  Finite checks prove those terminals exactly match the local
  incidence geometry, have room for the escape, and select one common clause
  gate for every pair of occurrence slots.  The gate is also exactly the
  fully refined factor-four local clause endpoint.  Thus a metadata-selected
  pair now exposes only three concrete strict-separation premises.
- [`LeanTrominoes/RetainedAngularFanDirectSourceTailSeparation.lean`](LeanTrominoes/RetainedAngularFanDirectSourceTailSeparation.lean)
  discharges those last three premises.  Computed linear extrema replace a
  quadratic comparison of long staircase routes, while a four-normal
  half-plane family covers the bisector, the tight `56 / 64` lane-clearance
  case, and both ray boundaries.  A finite atlas-and-slot check certifies
  both escape--tail directions and tail--tail separation, so a genuine
  metadata-selected direct-clause pair now yields separated coordinated
  complete routes with their shared clause gate as the only possible
  contact.
- [`LeanTrominoes/RetainedAngularFanDirectSourcePositionedRoutes.lean`](LeanTrominoes/RetainedAngularFanDirectSourcePositionedRoutes.lean)
  transports those local coordinated routes to an arbitrary direct
  component origin.  Its combined translation records source scale four
  followed by the full fan refinement, and translation invariance preserves
  both continuous avoidance and common-head-only contact.  This is the
  physical-coordinate interface used when the specialized final router
  substitutes coordinated routes for ordinary same-clause fans.
- [`LeanTrominoes/RetainedAngularFanDirectSourceRouteChoice.lean`](LeanTrominoes/RetainedAngularFanDirectSourceRouteChoice.lean)
  makes that substitution interface total and metadata-driven.  It checks
  unbounded local clause and literal indices against the finite crossover,
  duplicator-arm, and routed-clause atlases, records the component's physical
  origin, and returns `none` for malformed or non-direct sources.  Genuine
  retained direct metadata is proved to select an entry whose direction
  exactly matches its positioned local incidence, and every successful
  lookup is proved to represent that entire positioned local route.  Each
  choice also exposes its exact fully scaled local head and fan-boundary
  endpoint, together with an orthogonality certificate for its complete
  coordinated route.
- [`LeanTrominoes/RetainedAngularFanDirectSourceTransverseBounds.lean`](LeanTrominoes/RetainedAngularFanDirectSourceTransverseBounds.lean)
  gives finite transverse envelopes for complete coordinated atlas routes.
  Every direct route fits in radius 3103 around its represented terminal
  line, while every crossover and routed-variable route fits in the much
  tighter radius 495 envelope; that tight bound is transported through a
  checked choice's physical component translation.  After every customized
  escape, the shifted radial tail for all atlas kinds returns to the ordinary
  radius-845 transverse corridor and a radius-65 rectangle around its source
  segment.  Thus the only exceptional piece is the routed source clause's
  deliberately wide first escape, isolated for a separate carrier-interface
  argument.
- [`LeanTrominoes/RetainedAngularFanFinalDirectSourceFallbackPrefixSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalDirectSourceFallbackPrefixSeparation.lean)
  combines the tight transverse envelope with the radius-288 source-segment
  rectangle.  It identifies a successful final choice's represented segment
  with the actual retained route's discarded final edge, then applies the
  generic rectangle-or-line corridor theorem to separate any factor-1152
  fallback source prefix from a non-routed direct complete route.  A second
  specialization uses the radius-65/radius-845 certificates to separate the
  same fallback prefix from every direct route's shifted radial tail,
  including routed-clause choices.  The retained drawing's distinct-endpoint
  certificate separately clears the fixed Figure 7 local adapter; an
  endpoint-join theorem then clears the whole post-escape complete tail.
  Consequently the routed-clause choice's customized first escape is now the
  only unresolved mixed fallback/direct piece.
- [`LeanTrominoes/RetainedAngularFanDirectSourceCarrierBoundarySeparation.lean`](LeanTrominoes/RetainedAngularFanDirectSourceCarrierBoundarySeparation.lean)
  treats that customized routed-clause escape at the carrier interface.  It
  orients each compass carrier boundary by an inward unit normal, proves
  that combined factor-1152 scaling leaves every carrier-prefix point on
  the closed outside, and exhaustively certifies that every routed-clause
  escape point lies strictly inside.  The generic linear half-plane theorem
  then gives strict continuous separation of the two positioned routes.
  For a normalized final contact, route equality recovers the checked
  choice's routed-clause kind and exact physical origin, so the boundary
  witness discharges those positioning obligations automatically.  Finally,
  an endpoint-join bridge combines this exceptional-escape certificate with
  the already-controlled post-escape tail to clear the selected complete
  direct route.  A finite atlas check also proves that every routed-clause
  source segment is oblique, and translation preserves this fact for every
  positioned routed-clause choice; the exceptional escape therefore belongs
  entirely to the oblique mixed branch.  Raw selector success now also
  characterizes routed-clause metadata exactly, and route equality transports
  that characterization through a normalized flat macrocell witness.  Thus a
  routed-clause final choice recovers the normalized routed-clause source
  needed by the carrier-boundary theorem without an extra metadata premise.
  In an overlapping carrier--macrocell branch, normalization and the local
  contact certificate are consequently automatic; separation from the
  post-escape tail now closes the complete positioned routed-clause route.
- [`LeanTrominoes/RetainedAngularFanFinalRoutedClausePrefixSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRoutedClausePrefixSeparation.lean)
  supplies the complementary coarse geometry for that exceptional route.
  Route representation lifts the finite radius-288 direct-replacement bound
  from its source segment to the whole normalized flat macrocell.  More
  generally, component rectangles that are separated before refinement stay
  separated after factor-1152 scaling and radius-288 expansion, strictly
  separating any bounded flat source prefix from the direct replacement.
  The resulting carrier/macrocell case split eliminates every routed-clause
  prefix interaction except equal translated macrocells: direct carriers are
  ruled out by obliqueness, separated carrier and macrocell boxes use the
  coarse bound, and overlapping carriers use the specialized inward-boundary
  escape plus the already-controlled post-escape tail.
- [`LeanTrominoes/RetainedAngularFanFinalMixedOccurrenceAssembly.lean`](LeanTrominoes/RetainedAngularFanFinalMixedOccurrenceAssembly.lean)
  packages the structural endpoint-join step for a mixed cross-clause pair.
  Four strict certificates between the coordinated direct prefix and suffix
  and an arbitrary fallback prefix and suffix now imply strict separation of
  the two complete occurrence routes; the validated direct boundary equation
  discharges its join automatically, and a symmetric wrapper exposes either
  route orientation.  For different genuine source clauses, the established
  cross-clause spoke and suffix theorems discharge both interactions with the
  fallback suffix automatically, reducing the complete mixed pair to exactly
  the two interactions with its fallback boundary prefix.  The selected
  fallback-prefix theorem then discharges the reverse suffix interaction as
  well, leaving a single geometric premise: the coordinated direct prefix
  must avoid the selected fallback boundary.  For every non-routed direct
  atlas kind, that premise is now itself assembled from a source-corridor
  certificate and separation from the selected fallback outer replacement;
  these are the only two geometric obligations left for the complete mixed
  occurrence pair.  An atlas-kind-independent variant accepts direct
  separation from the fully refined fallback source prefix and outer
  replacement separately, so the routed-clause carrier argument can enter
  the same occurrence assembly without duplicating its endpoint joins or
  suffix proofs.  When the discarded terminal rectangles are separated, the
  shared radius bound discharges the outer obligation too, so the complete
  mixed pair follows from the corridor certificate alone.
- [`LeanTrominoes/RetainedAngularFanMixedBoundaryAssembly.lean`](LeanTrominoes/RetainedAngularFanMixedBoundaryAssembly.lean)
  decomposes either ordinary or delayed-lane fallback boundary into its
  refined retained prefix and outer-fan replacement.  Strict avoidance of
  those two pieces composes across their certified gate, and orthogonality
  removes the final rasterization wrapper, so the result applies directly to
  the actual fallback boundary route.
- [`LeanTrominoes/RetainedAngularFanFinalMixedFallbackSuffixSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalMixedFallbackSuffixSeparation.lean)
  names the boundary prefix selected by a failed final direct-source lookup:
  singleton raw prefixes use the delayed-lane escape and all others use the
  ordinary splice.  Existing shared-center and distinct-center geometry is
  combined with orthogonal rasterization to prove that this selected prefix
  avoids every other final clause's Figure 7 occurrence suffix.
- [`LeanTrominoes/RetainedAngularFanFinalMixedBoundaryAssembly.lean`](LeanTrominoes/RetainedAngularFanFinalMixedBoundaryAssembly.lean)
  mirrors that fallback selection for the outer replacement and lifts the
  two-piece boundary assembly theorem to the final router.  Thus a route
  avoids the selected rasterized fallback boundary once it avoids the fully
  refined retained source prefix and the selected ordinary or delayed-lane
  outer replacement.  Both replacements share the same conservative
  radius-288 discarded-segment bound, which closes direct/fallback outer
  separation whenever the two unscaled segment rectangles are separated.
  The two-piece interface itself is independent of the direct atlas kind;
  for non-routed choices its source-prefix premise follows from the existing
  corridor theorem, while routed-clause choices may supply the specialized
  carrier-boundary certificate.  In particular, a corridor certificate and
  separated discarded-terminal rectangles discharge the non-routed boundary
  interaction with no additional geometric premise.
- [`LeanTrominoes/RetainedAngularFanFinalMixedOrder.lean`](LeanTrominoes/RetainedAngularFanFinalMixedOrder.lean)
  transports the final occurrence sort to a successful direct choice and a
  genuine fallback route of the same atom.  Their coordinated slots and
  classified terminal-direction ranks increase in the same orientation,
  supplying the exact order premise for the remaining overlapping local-fan
  certificate.  A final wrapper derives the required atom equality and
  occurrence distinction directly from a shared canonical variable center
  and different source-clause indices.
- [`LeanTrominoes/RetainedAngularFanFinalMixedStrictOrder.lean`](LeanTrominoes/RetainedAngularFanFinalMixedStrictOrder.lean)
  upgrades that compatible weak order to the strict angular order required by
  complete direct/fallback outer-route separation whenever their classified
  terminal directions differ.  It also combines terminal classification with
  an aligned fallback segment and an oblique direct segment to supply that
  direction inequality and hence strict order in one step.  The final wrapper
  now discharges direction inequality unconditionally and derives strict order
  directly from different source clauses sharing a canonical variable center.
- [`LeanTrominoes/RetainedAngularFanDirectSourceCycleSeparation.lean`](LeanTrominoes/RetainedAngularFanDirectSourceCycleSeparation.lean)
  exhaustively checks the missing inner-neighborhood interaction for all 33
  direct clause shapes: every coordinated outer prefix is strictly
  contact-free from every factor-eight implication route around its own
  source-variable center.  Translation transports the certificate to each
  metadata-selected retained component.
- [`LeanTrominoes/RetainedAngularFanDirectSourceCompleteCycleSeparation.lean`](LeanTrominoes/RetainedAngularFanDirectSourceCompleteCycleSeparation.lean)
  combines the strict outer-prefix certificate with the terminal-contact
  spoke/cycle certificate.  The complete joined direct occurrence therefore
  avoids every implication route in its own Figure 7 ring, allowing only
  the intended contact at its final ring vertex.
- [`LeanTrominoes/RetainedAngularFanFinalDirectSourceOwnCycleSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalDirectSourceOwnCycleSeparation.lean)
  identifies that atlas ring with the matching periodically lifted cycle in
  the final coordinates.  Equality of the common nonempty Figure 7 spoke
  fixes the translation offset, yielding the mixed separation theorem for
  the actual final successful direct-occurrence route.
- [`LeanTrominoes/RetainedAngularFanDirectSourceSpokeSeparation.lean`](LeanTrominoes/RetainedAngularFanDirectSourceSpokeSeparation.lean)
  centers the actual factor-eight Figure 7 spoke at every direct-source
  atlas endpoint.  An exhaustive finite certificate proves both directed
  interactions between one coordinated complete prefix and the other
  literal's spoke are contact-free, for every distinct atlas pair and all
  eight-by-eight occurrence-slot choices.
- [`LeanTrominoes/RetainedAngularFanDirectSourceRouteChoicePairs.lean`](LeanTrominoes/RetainedAngularFanDirectSourceRouteChoicePairs.lean)
  reconstructs one common finite-atlas pair from two independently checked
  choices for distinct literals of the same direct source.  Crossover and
  duplicator sources preserve distinct presentation indices directly;
  routed-clause sources use duplicate-free physical ports.  In every case,
  the two complete routes are separated and can meet only at their heads.
- [`LeanTrominoes/RetainedAngularFanDirectSourceRouteChoiceSpokePairs.lean`](LeanTrominoes/RetainedAngularFanDirectSourceRouteChoiceSpokePairs.lean)
  positions the certified Figure 7 spoke with each checked route choice.
  For two distinct literals selected from the same raw direct source, it
  proves both directed prefix--spoke interactions strictly avoid one
  another after the common component-origin translation.
- [`LeanTrominoes/RetainedAngularFanFinalDirectSourceRouteChoice.lean`](LeanTrominoes/RetainedAngularFanFinalDirectSourceRouteChoice.lean)
  lifts the checked selector through clause-anchor normalization and
  representative-clause deduplication.  It recovers the retained metadata
  representative of a final clause and translates the chosen component
  origin by the exact physical anchor shift used by the quotient route.  The
  selector fails closed unless that translated atlas route equals the actual
  deduplicated source route, so every successful final choice carries exact
  route equality and exact translated head and last-point formulas.
- [`LeanTrominoes/RetainedAngularFanFinalDirectSourceRouteChoicePairs.lean`](LeanTrominoes/RetainedAngularFanFinalDirectSourceRouteChoicePairs.lean)
  inverts successful final choices to their canonical raw metadata
  representative and atlas entry.  Choices at distinct literal indices of
  one final clause therefore share one source and one anchor-normalization
  offset; transporting the raw pair certificate proves their complete
  coordinated routes avoid each other and meet only at their common heads.
- [`LeanTrominoes/RetainedAngularFanFinalDirectSourceChoiceUniformity.lean`](LeanTrominoes/RetainedAngularFanFinalDirectSourceChoiceUniformity.lean)
  proves that one successful direct-source choice determines a direct
  canonical metadata representative for the entire final clause.  Every
  other genuine literal of that clause therefore also has a successful
  checked choice, closing the selector-uniformity case needed by the total
  same-clause route-family proof.
- [`LeanTrominoes/RetainedAngularFanFinalDirectSourceChoiceFailure.lean`](LeanTrominoes/RetainedAngularFanFinalDirectSourceChoiceFailure.lean)
  proves the complementary selector classification.  A genuine final-route
  witness from any crossover, routed-clause, or routed-variable component
  reconstructs a successful checked choice, so failure exposes a physical
  retained carrier-lens or bend-corner witness for the fallback geometry.
  Failure is uniform within a genuine final clause, and any two failed
  literals recover the same canonical metadata representative.
- [`LeanTrominoes/RetainedAngularFanFallbackPrefixLengths.lean`](LeanTrominoes/RetainedAngularFanFallbackPrefixLengths.lean)
  checks the finite route tables behind that fallback.  Distinct literals in
  one carrier clause cannot both use the lens's singleton prefix, while
  every bend-corner prefix has length at least two.  Route-length
  preservation through placement and final quotient normalization lifts
  this dichotomy to failed choices at any two distinct genuine literals of
  one final clause.
- [`LeanTrominoes/RetainedAngularFanFinalDirectSourceRouteChoiceSpokePairs.lean`](LeanTrominoes/RetainedAngularFanFinalDirectSourceRouteChoiceSpokePairs.lean)
  transports the raw prefix--spoke certificate through that same
  anchor-normalization shift.  Thus two successful final choices at
  distinct literal indices retain both directed strict-separation
  statements between one coordinated prefix and the other selected spoke.
- [`LeanTrominoes/RetainedAngularFanFinalCoordinatedRoutes.lean`](LeanTrominoes/RetainedAngularFanFinalCoordinatedRoutes.lean)
  defines the specialized final fixed-eight route family.  Successful direct
  choices replace the ordinary source-to-fan boundary piece by the
  coordinated complete route and then reuse the unchanged scaled Figure 7
  occurrence suffix.  Failed choices whose discarded-final-point source
  prefix is a singleton use the corresponding delayed-lane escaped occurrence
  splice, reusing the same source scaling, terminal data, occurrence slot, and
  Figure 7 suffix.  Other failed choices, malformed indices, non-direct
  clauses, and appended cycle clauses retain the established route exactly.
- [`LeanTrominoes/RetainedAngularFanFinalCoordinatedRouteValidity.lean`](LeanTrominoes/RetainedAngularFanFinalCoordinatedRouteValidity.lean)
  proves that each validated coordinated prefix meets that unchanged suffix
  at exactly the same fan-boundary point.  The resulting substituted route
  therefore retains the canonical clause and copied-literal endpoints and
  remains orthogonal.  It likewise validates the exceptional delayed-lane
  fallback from its retained source certificate through the scaled terminal
  classification and clearance bound, proving that the complete escaped
  occurrence route has the same canonical endpoints and orthogonality.
- [`LeanTrominoes/RetainedAngularFanFinalDirectSourceSpokeIdentification.lean`](LeanTrominoes/RetainedAngularFanFinalDirectSourceSpokeIdentification.lean)
  identifies the selected occurrence slot with its exact angular-order
  index and proves that a successful final choice's positioned certified
  spoke is literally the unchanged scaled Figure 7 suffix.  The proof uses
  their common validated boundary point and the fact that both routes are
  translations of the same nonempty local spoke.
- [`LeanTrominoes/RetainedAngularFanFinalCoordinatedRoutePairs.lean`](LeanTrominoes/RetainedAngularFanFinalCoordinatedRoutePairs.lean)
  assembles the same-clause prefix certificate through the two validated
  Figure 7 endpoint joins.  Separation of the actual coordinated occurrence
  routes is reduced to exactly three strict suffix-involving interactions:
  the two directed prefix--spoke pairs and the spoke--spoke pair; the only
  possible remaining contact is their inherited common clause head.
- [`LeanTrominoes/RetainedAngularFanFinalOccurrenceSuffixSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalOccurrenceSuffixSeparation.lean)
  proves that different literal entries of one final retained clause have
  different canonical source occurrence centers, using the canonical gauge,
  valid-variable position injectivity, and incidence-key distinctness.
  Their factor-36 Figure 7 macrocells, and hence their scaled spoke suffixes,
  are therefore strictly separated.
- [`LeanTrominoes/RetainedAngularFanFinalCycleSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalCycleSeparation.lean)
  discharges occurring-variable position injectivity for the retained source
  from its planar-SAT validity certificate.  It applies the generic
  different-macrocell theorem after factor-4 source clearance, transports
  avoidance through the factor-8 routing refinement, and identifies the
  resulting routes with the actual appended implication-cycle lookups of the
  public coordinated family.  Positive scaling also preserves full route
  simplicity, so every cycle-suffix route is simple and every distinct pair
  in that complete suffix is continuously separated.  The same local/global
  split proves that every Figure 7 ring-copy or implication-clause vertex
  avoids every cycle-route interior, and exposes both results at the final
  factor-8 placement and public coordinated route indices.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeCycleSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeCycleSeparation.lean)
  extends the cycle/cycle branch to arbitrary periodic copies.  It proves
  generically that a semantic translation moves the second factor-36 Figure
  7 macrocell with its route, while two source points in the open fundamental
  square cannot coincide under a nonzero period shift.  Thus every nonzero
  translated cycle pair is strictly contact-free; combined with the existing
  distinct-incidence theorem at shift zero, this gives complete relative
  cycle-route separation at both the scaled and public fixed-eight interfaces.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeDirectCycleSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeDirectCycleSeparation.lean)
  completes the mixed successful-direct-source/cycle periodic branch.  Equality
  of a genuine source occurrence center with a translated cycle center
  identifies both the underlying atom and the exact semantic period offset.  The translated
  flattened Figure 7 route is therefore the occurrence's already-certified
  matching cycle lift.  For unequal centers, periodic macrocell decomposition
  and a transported radius-48 cycle bound put the routes in strictly separated
  rectangles.  Thus every successful direct route avoids every genuine cycle
  route in every relative period cell, at both internal and public interfaces.
- [`LeanTrominoes/RetainedFinalSourceRouteOtherTranslatedVertexSeparation.lean`](LeanTrominoes/RetainedFinalSourceRouteOtherTranslatedVertexSeparation.lean)
  extends retained source-route/vertex separation to arbitrary periodic copies.
  Relative route separation moves a witnessing target incidence so its final
  point is the requested translated variable position; periodic vertex
  planarity also clears that point from any axis-aligned discarded final
  segment.  The failed-selector theorem is the immediate specialization that
  obtains this alignment from the fallback policy.
- [`LeanTrominoes/RetainedFinalSourceRouteOtherTranslatedTargetSeparation.lean`](LeanTrominoes/RetainedFinalSourceRouteOtherTranslatedTargetSeparation.lean)
  converts the fundamental-square vertex interfaces into occurrence-center
  interfaces.  It absorbs a target literal's clause-relative period offset,
  proving that source prefixes and aligned discarded final segments avoid
  arbitrary translated canonical literal positions.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeFallbackCycleSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeFallbackCycleSeparation.lean)
  completes the failed-selector half of periodic source/cycle separation.  A
  reusable point-neighborhood assembly covers both ordinary and escaped
  fallback prefixes.  Equal translated centers reuse the matching Figure 7
  lift, while unequal centers use the translated source-vertex and radius-48
  cycle bounds.  The resulting combined theorem covers every copied-source
  route, whether direct or fallback, against every translated cycle route.
- [`LeanTrominoes/RetainedAngularFanFinalRelativeRouteSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalRelativeRouteSeparation.lean)
  dispatches the complete final fixed-eight route family into copied-source,
  mixed source/cycle, and cycle/cycle pairs.  The mixed and cycle branches
  are fully discharged for arbitrary relative period shifts; copied-source
  versus copied-source separation is exposed as the sole remaining geometric
  premise.  From that premise the module transports separation through
  pointwise loop erasure, lifts it to all periodic drawing occurrences, and
  packages the normalized drawing as ribbon-ready.
- [`LeanTrominoes/RetainedAngularFanFinalCycleBounds.lean`](LeanTrominoes/RetainedAngularFanFinalCycleBounds.lean)
  recovers the source atom owning any genuine appended implication route
  and proves that every point of its factor-eight realization lies within
  coordinate radius 48 of that atom's fully refined original position.
  This is the uniform neighborhood certificate used by the mixed
  copied-source/cycle separation layer.
- [`LeanTrominoes/RetainedAngularFanFinalCoordinatedRouteSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalCoordinatedRouteSeparation.lean)
  discharges all three suffix-involving premises of the endpoint-join
  separator.  Consequently, any two successful coordinated direct
  occurrences of one final clause avoid one another and can meet only at
  their inherited common clause gate.  The result is also exposed through
  the public total incidence-route family for two successful selectors.
  The exceptional failed-selector case with exactly one singleton prefix is
  likewise exposed in either literal order through a compact
  `RoutesSeparatedAtHeads` certificate: selector uniformity makes the other
  selector fail, the prefix-length dichotomy makes its route ordinary, and
  stored model equalities transfer the completed escaped/ordinary separation
  theorem to both total lookups without unfolding the geometric predicates.
  The complementary failed-selector case with two non-singleton prefixes is
  now exposed by the same interface, using two explicit ordinary occurrence
  joins and the completed ordinary/ordinary separation theorem.  A final
  selector-and-prefix case split packages all successful and failed cases
  into one unconditional avoidance-and-head-contact theorem for distinct
  genuine entries of a single final clause.
- [`LeanTrominoes/RetainedAngularFanFinalCoordinatedRouteFamily.lean`](LeanTrominoes/RetainedAngularFanFinalCoordinatedRouteFamily.lean)
  lifts that local splice certificate to every incidence in the final
  fixed-eight formula.  Successful direct copied-source choices use their
  coordinated routes; singleton-prefix failed choices use the escaped
  fallback; other failed choices and all appended implication-cycle clauses
  use the established fallback.  The total family is packaged with canonical
  endpoints and pointwise orthogonality, ready for the global nonintersection
  proof.
- [`LeanTrominoes/RetainedAngularFanFinalCoordinatedTerminalDirections.lean`](LeanTrominoes/RetainedAngularFanFinalCoordinatedTerminalDirections.lean)
  proves that joining any boundary prefix to the nondegenerate scaled
  Figure 7 suffix preserves that suffix's final direction.  Coordinated
  direct, delayed-lane fallback, and ordinary retained copied-source routes
  therefore all reach their split variable with the same selected terminal
  direction.
- [`LeanTrominoes/RetainedAngularFanSourceScaledVariableRouteOrder.lean`](LeanTrominoes/RetainedAngularFanSourceScaledVariableRouteOrder.lean)
  compares the retained complete routes with the uniformly scaled canonical
  Figure 7 family.  Copied-source routes share their final spoke and cycle
  routes agree outright, so source-first refinement preserves the clockwise
  first/second/third occurrence order at every degree-three split variable.
- [`LeanTrominoes/RetainedAngularFanFinalCoordinatedVariableRouteOrder.lean`](LeanTrominoes/RetainedAngularFanFinalCoordinatedVariableRouteOrder.lean)
  compares the final coordinated family incidence-by-incidence with that
  source-scaled fallback family.  Successful direct choices and escaped
  singleton fallbacks end in the same spoke, while all other copied routes
  and all cycle routes are unchanged; hence the coordinated family preserves
  the same clockwise variable occurrence order.
- [`LeanTrominoes/RetainedAngularFanFinalCoordinatedRouteLength.lean`](LeanTrominoes/RetainedAngularFanFinalCoordinatedRouteLength.lean)
  proves that every source-scaled fallback route contains a genuine final
  edge and transfers this nondegeneracy to the coordinated family using its
  terminal-direction equality and orthogonality.  This is the remaining
  local hypothesis needed to preserve route order through Figure 9.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeRoutes.lean)
  feeds the source-scaled coordinated fixed-eight formula, placement, and
  normalized canonical route family into the generic positioned Figure 9
  adapter.  Coordinate scaling preserves the fixed-eight width and
  atom-distinctness premises, and every resulting raw exact-one route has
  canonical endpoints, is orthogonal, and exposes the first exit required by
  unit elimination.  Normalizing before Figure 9 removes inherited collar
  loops while preserving the coordinated clockwise route order.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeInheritedRouteIsolation.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeInheritedRouteIsolation.lean)
  instantiates the generic connector theorem with the normalized retained
  fixed-eight source family.  Every genuine inherited Figure 9 suffix and
  every complete raw Figure 9 route now has isolated clause and variable
  endpoints after unit subdivision.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeWrappedRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeWrappedRoutes.lean)
  transports the coordinated raw Figure 9 formula, placement, and routes
  through the exact-one variable wrapper.  The wrapper changes no geometry
  or presentation indices, so generic renaming preserves canonical
  endpoints, orthogonality, both endpoint-isolation conditions, atom
  distinctness, width three, and the first-exit certificate verbatim.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsRoutes.lean)
  applies positioned unit elimination to the wrapped coordinated Figure 9
  routes.  The final unit-free exact-one formula has only binary or ternary
  clauses and positive physical period; its complete route family has
  canonical endpoints, is orthogonal, and realizes every incidence-graph
  edge.  Thus the coordinated geometry is now threaded through the full
  exact-one route pipeline.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeTwoPointRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeTwoPointRoutes.lean)
  specializes the Figure 9 two-point invariant to the raw coordinated family
  and transports it through opaque variable wrapping.  Thus any wrapped
  route whose first exit is already its final endpoint is necessarily a
  vertical segment.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeMiddleRouteDirections.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeMiddleRouteDirections.lean)
  specializes the Figure 9 weak-left middle-route invariant to the raw
  coordinated family and transports it through opaque variable wrapping.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsRouteIsolation.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsRouteIsolation.lean)
  combines wrapped endpoint isolation with that vertical exception and the
  scale-six local-prefix separation theorem.  Every route in the concrete
  final unit-free exact-one family now has both endpoints isolated after unit
  subdivision, including the one-segment source edge case, and contains at
  least one local unit-elimination edge.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsVariableRouteOrder.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsVariableRouteOrder.lean)
  transports the normalized coordinated clockwise variable-route order
  through Figure 9, opaque wrapping, and unit elimination.  It also proves
  the inherited Figure 9 routes are long enough for both terminal-direction
  splice certificates.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsRibbonOrders.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsRibbonOrders.lean)
  pairs the final clockwise variable-route order with the canonical ternary
  clause-route order from unit elimination.  The two endpoint-isolation
  certificates then transport both cyclic orders through final loop erasure.
  Consequently a ribbon-ready presentation built from the normalized routes
  has compatible clockwise source fans for the normalized 3DM construction.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeSemantics.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeSemantics.lean)
  observes that the coordinated construction changes positions and routes
  but not the erased exact-one formula.  It transfers the width-three and
  occurrence-three promises and proves that the final coordinated unit-free
  instance is satisfiable exactly when the original periodic CNF is.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightThreeDM.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightThreeDM.lean)
  names the normalized 3DM target of the coordinated pipeline.  The target is
  well-formed, every colored element has degree two or three, and both perfect
  matching and the abstract trichromatic orientation are equivalent to
  satisfiability of the original periodic CNF.  A ribbon-ready coordinated
  incidence presentation is now the only missing input to the generic
  geometric 3DM assembly.
- [`LeanTrominoes/RetainedAngularFanOuterRadialSeparation.lean`](LeanTrominoes/RetainedAngularFanOuterRadialSeparation.lean)
  separates every ordered pair of arbitrary-length radial lanes.  A finite
  table of integer half-planes, the uniform radius-nine staircase corridor,
  and one exact angular-wrap case handle distinct directions.  Exact
  length-independent transverse staircase bands and radial gate thresholds
  handle nested parallel lanes.  The profile-level theorem obtains direction
  order, positive lengths, and strict same-direction radial order directly
  from a duplicate-free angular terminal profile.
- [`LeanTrominoes/RetainedAngularFanOuterRadialFinalStubs.lean`](LeanTrominoes/RetainedAngularFanOuterRadialFinalStubs.lean)
  isolates the last primitive raster block immediately outside each exact
  radius-288 lane port.  Exhaustive finite certificates prove that these
  stubs strictly avoid all order-compatible local fan routes in both
  orientations, and translation positions the certificates at any retained
  source center.
- [`LeanTrominoes/RetainedAngularFanOuterRadialPrefixes.lean`](LeanTrominoes/RetainedAngularFanOuterRadialPrefixes.lean)
  removes that last block from every nonempty radial raster.  Exact endpoint
  and orthogonality theorems place the shortened route one primitive beyond
  its lane port; monotonicity of compass and exceptional staircases then
  proves the entire arbitrary-length prefix strictly outside a supporting
  side of the radius-288 frame, hence strictly separated from every local
  fan route.
- [`LeanTrominoes/RetainedAngularFanOuterZeroRadialRoutes.lean`](LeanTrominoes/RetainedAngularFanOuterZeroRadialRoutes.lean)
  isolates the sole positive zero-block case: a length-one compass terminal.
  Its radial route is exactly the finite tangential lane shift, whose
  order-compatible interactions with local fan routes are exhaustively
  certified; the excluded equal-direction case cannot occur in a
  duplicate-free terminal profile.
- [`LeanTrominoes/RetainedAngularFanOuterRadialDecomposition.lean`](LeanTrominoes/RetainedAngularFanOuterRadialDecomposition.lean)
  splits the last primitive block from every positive diagonal or
  routed-clause radial raster and proves the split route avoids the finite
  local fan adapters.  Cardinal rasters are represented by one long segment;
  an explicit collinear coarsening certificate relates that direct segment
  to the same split geometry.
- [`LeanTrominoes/RetainedAngularFanOuterCrossSeparation.lean`](LeanTrominoes/RetainedAngularFanOuterCrossSeparation.lean)
  proves both radial-versus-local separation orientations for ordered active
  profile slots.  It transports positive cardinal routes through collinear
  coarsening, handles the finite zero-block case separately, and uses
  duplicate-free gates to exclude the sole obstructed equal-direction
  ordering.
- [`LeanTrominoes/RetainedAngularFanOuterCompleteSeparation.lean`](LeanTrominoes/RetainedAngularFanOuterCompleteSeparation.lean)
  combines radial/radial, radial/local, local/radial, and local/local
  separation through the exact radius-288 joins.  Thus every two ordered
  active slots in a duplicate-free profile select strictly separated
  complete source-gate-to-Figure-7 routes.
- [`LeanTrominoes/RetainedAngularFanOuterRouteFamily.lean`](LeanTrominoes/RetainedAngularFanOuterRouteFamily.lean)
  packages those routes as the profile-ordered finite family of at most
  eight active incidences.  Every indexed route has its exact source gate
  and refined Figure 7 boundary endpoint and is orthogonal; duplicate-free
  gates make the entire family pairwise strictly separated.
- [`LeanTrominoes/RetainedAngularFanOccurrenceOuterSeparation.lean`](LeanTrominoes/RetainedAngularFanOccurrenceOuterSeparation.lean)
  connects profile slots back to genuine retained source occurrences.
  Two distinct occurrences select their exact classified replacement
  suffixes; their positions in the duplicate-free angular list choose the
  orientation automatically, and terminal-vector injectivity proves those
  complete outer-fan routes strictly separated.  The same theorem is
  transported through any positive source-refinement factor, scaling radial
  lengths while preserving complete fan/fan separation.
- [`LeanTrominoes/OrthogonalPolylineTailReplacementSeparation.lean`](LeanTrominoes/OrthogonalPolylineTailReplacementSeparation.lean)
  proves that strict continuous separation is preserved by simultaneously
  replacing the tails of two routes.  Separation of the unchanged
  `dropLast` prefixes follows from endpoint-only separation, route
  duplicate-freedom, and distinct source endpoints; positive scaling then
  preserves it.  Tail replacement reduces the new geometry to exactly three
  cross/suffix cases before the four pieces are reassembled compositionally.
  A parallel ordinary-avoidance theorem covers routes with a shared clause
  head: duplicate-freedom proves that this head is the only inherited contact,
  it remains an advertised endpoint after splicing, and positive uniform
  scaling preserves the endpoint-only certificate.  The fully endpoint-aware
  composition rule also permits each prefix/fan and fan/fan pair to meet at
  that common head, provided every such piece pair has ordinary continuous
  avoidance and no other listed contact.  This covers the shape of two
  direct, two-point incidences leaving one clause source.  Its asymmetric
  companion handles exactly one such source: one replacement fan may meet
  the other retained prefix at their heads, and the single owning-head
  equation transports that contact to the completed routes while every
  other replacement-involving pair remains strictly separated.
- [`LeanTrominoes/RetainedRayPolylineTailReplacement.lean`](LeanTrominoes/RetainedRayPolylineTailReplacement.lean)
  equips retained-ray polylines with a consecutive-point chain
  characterization, final-prefix and endpoint-join closure, and safe
  replacement of a route's old variable endpoint by a retained fan suffix.
  This is the source-prefix splice used before final orthogonal
  rasterization.
- [`LeanTrominoes/RetainedAngularFanSourceSplice.lean`](LeanTrominoes/RetainedAngularFanSourceSplice.lean)
  performs that splice on one classified retained source route at the
  combined scale `288`.  It names the pre-rasterized source-prefix/fan-suffix
  splice for compositional separation, replaces the old variable endpoint
  by the exact profile-selected outer fan route, rasterizes the retained
  result, and proves the scaled clause endpoint, refined Figure 7 boundary
  endpoint, and orthogonality.  When the source route was already
  orthogonal, the pre-rasterized replacement splice is proved orthogonal
  too.
- [`LeanTrominoes/RetainedAngularFanSourceEscapedSplice.lean`](LeanTrominoes/RetainedAngularFanSourceEscapedSplice.lean)
  packages the delayed-lane outer fan as an alternative replacement tail.
  It follows the source terminal for 64 primitive blocks before selecting
  the occurrence lane, avoiding an immediate shared-clause tangency, while
  retaining the ordinary splice's exact clause endpoint, Figure 7 boundary
  endpoint, and orthogonality contract.  An additional pre-rasterization
  theorem preserves orthogonality from an already orthogonal source route.
- [`LeanTrominoes/RetainedAngularFanSourceEscapedSpliceSeparation.lean`](LeanTrominoes/RetainedAngularFanSourceEscapedSpliceSeparation.lean)
  packages the asymmetric same-clause tail replacement used by a singleton
  failed-choice route against an ordinary non-singleton fallback.  The
  escaped fan may meet the other retained source prefix only at their common
  clause head; strict separation of the other three new piece pairs then
  yields endpoint-only avoidance and common-head-only contact for both
  complete pre-rasterized splices.
- [`LeanTrominoes/RetainedAngularFanFinalFallbackSpliceSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalFallbackSpliceSeparation.lean)
  discharges every premise of that asymmetric adapter for two distinct
  literals of one genuine final clause.  Selector failure gives shared
  carrier-or-bend witnesses; a singleton first prefix rules out the bend,
  the equality-lens theorem controls the escaped-fan/partner-prefix contact,
  and retained global planarity separates the old routes and discarded
  terminal corridors.  The resulting escaped and ordinary boundary
  polylines are orthogonal, avoid each other, and meet only at their common
  clause head.  Because retained rasterization is the identity on these
  orthogonal carrier routes, the same certificate now holds for the actual
  rasterized boundary routes.  The theorem also carries both directed
  boundary-splice/Figure-7-suffix separation facts through rasterization.
- [`LeanTrominoes/RetainedAngularFanFinalFallbackOrthogonality.lean`](LeanTrominoes/RetainedAngularFanFinalFallbackOrthogonality.lean)
  transports finite bend-corner orthogonality through the physical
  translation used by final route occurrences, complementing the carrier
  certificate.  A single fallback interface now proves every failed-choice
  carrier-or-bend route orthogonal without exposing which component family
  supplied it.
- [`LeanTrominoes/RetainedAngularFanFinalOrdinaryFallbackSpliceSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalOrdinaryFallbackSpliceSeparation.lean)
  handles the complementary failed-choice branch in which both source
  prefixes are non-singletons.  For two different literals in one genuine
  final clause, carrier-or-bend orthogonality makes both discarded terminal
  segments axis-aligned; retained planarity separates the complete outer
  fans, and the head-aware splice theorem proves that the ordinary boundary
  routes avoid each other except for their common clause head.  Because both
  splices are orthogonal, the same certificate holds after retained
  rasterization.  Pointwise prefix clearance and discarded-terminal
  rectangle separation additionally prove both directed
  boundary-splice/Figure-7-suffix separations, again before and after
  rasterization.
- [`LeanTrominoes/RetainedAngularFanFinalFallbackOccurrenceSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalFallbackOccurrenceSeparation.lean)
  joins both the exceptional escaped/ordinary boundary pair and the
  complementary non-singleton ordinary/ordinary pair to their unchanged
  Figure 7 suffixes.  The generic endpoint-join theorem combines head-only
  prefix contact, both directed cross-suffix bounds, and suffix/suffix
  separation into completed occurrence-route certificates.  A separate
  public lookup theorem identifies each genuine established route-family
  entry directly with its explicit boundary-prefix/Figure-7-suffix join,
  keeping that definitional normalization independent of the geometric
  certificate.
- [`LeanTrominoes/RetainedAngularFanSourceSpliceSeparation.lean`](LeanTrominoes/RetainedAngularFanSourceSpliceSeparation.lean)
  applies simultaneous tail-replacement separation to two classified
  retained splices.  Positive scaling preserves strict source-prefix
  separation and the exact classified gate equations discharge both endpoint
  joins, leaving only the two directed source-prefix/fan-suffix cross cases
  plus the already certified fan/fan case.  It also exposes the common-clause
  variant, preserving the one legal shared source endpoint while keeping all
  fan-involving pairs contact-free, and a stronger tail-replacement theorem
  records both route avoidance and meet-only-at-heads simultaneously.
- [`LeanTrominoes/RetainedAngularFanSourceScaling.lean`](LeanTrominoes/RetainedAngularFanSourceScaling.lean)
  scales the retained source before inserting the fixed-size angular fans.
  Positive refinement preserves the angular occurrence order and the logical
  fixed-eight formula while multiplying the global source clearance.  The
  concrete factor `4` makes the scale-288 source clearance exceed the
  radius-845 terminal corridor.
- [`LeanTrominoes/RetainedAngularFanSourceScaledSeparation.lean`](LeanTrominoes/RetainedAngularFanSourceScaledSeparation.lean)
  transports the simultaneous splice-separation interface through that
  source-first refinement.  It additionally identifies every scaled
  singleton prefix with the singleton containing its exact own-fan gate, so
  restricting an existing complete fan/fan certificate discharges the
  directed singleton-prefix-versus-other-fan cross case with no new geometry.
  For two singleton-prefix incidences, it further reduces ordinary planarity
  of both completed splices to one ordinary fan/fan certificate whose listed
  contacts occur only at the fan heads; the four prefix/fan piece cases then
  follow by singleton restriction.  The common-clause certificate is also
  transported through positive source scaling with both avoidance and
  head-contact information intact.
- [`LeanTrominoes/RetainedAngularFanSourceScaledDrawing.lean`](LeanTrominoes/RetainedAngularFanSourceScaledDrawing.lean)
  packages the source-first-scaled retained family and its unchanged local
  fans as canonical orthogonal incidence routes.  Its concrete factor-four
  planar-SAT construction has positive period and erases to exactly the
  established retained fixed-eight logical formula.  A separate pointwise
  transport theorem exposes the established route's endpoints and
  orthogonality without unfolding the large bundled certificate, which is
  the fallback interface used by the final coordinated router.
- [`LeanTrominoes/RetainedFinalSourceScaledSpliceSeparation.lean`](LeanTrominoes/RetainedFinalSourceScaledSpliceSeparation.lean)
  packages the final route-shape reduction for separating two source-to-fan
  splices.  Each directed cross case follows either from a singleton source
  prefix or from an axis-aligned terminal on the other fan route; consequently
  aligned/aligned and singleton/singleton pairs are complete, isolating only
  the mixed aligned-prefix-versus-oblique-fan geometry.  For shared-clause
  routes it separately packages the non-singleton, axis-aligned case,
  returning both avoidance and meet-only-at-heads for the completed splices.
- [`LeanTrominoes/RectangleLineEnvelope.lean`](LeanTrominoes/RectangleLineEnvelope.lean)
  gives the diagonal cross case an explicit closed-envelope contact
  predicate: a point must satisfy both the reference segment's coordinate
  bounds and supporting-line equation, while an axis-aligned segment contact
  is exactly rectangle overlap plus bracketing of that line.  The mixed
  separating-axis predicates are proved to be the exact complements of
  these contacts.
- [`LeanTrominoes/RetainedTerminalSegmentEnvelope.lean`](LeanTrominoes/RetainedTerminalSegmentEnvelope.lean)
  proves that the selected transverse functional is constant on every
  classified retained terminal segment and specializes the envelope to the
  discarded final segment.  It restates the remaining source-prefix corridor
  certificate as a finite, decidable absence of point and axis-segment
  contacts, without treating the axis-only `InteriorsMeet` predicate as
  diagonal geometry.
- [`LeanTrominoes/RetainedTerminalEnvelopeCheckpoints.lean`](LeanTrominoes/RetainedTerminalEnvelopeCheckpoints.lean)
  proves that every lattice point contacting a retained terminal envelope
  becomes an exact primitive checkpoint on the discarded segment after the
  common `288`-fold fan refinement, and that every axis-aligned segment
  contacting the envelope contains such a refined checkpoint.  The proofs
  cover both orientations for all eleven retained directions and convert
  their integer parameters into finite, decidable natural-number checkpoint
  predicates.  A combined source-prefix checkpoint-avoidance certificate is
  proved sufficient for the mixed outer-corridor separation hypothesis.
- [`LeanTrominoes/RetainedTerminalCheckpointRasterization.lean`](LeanTrominoes/RetainedTerminalCheckpointRasterization.lean)
  connects those finite checkpoints to the executable route geometry.
  Ordered unit subdivision lists every lattice point on an axis segment;
  whole-polyline rasterization retains each source segment's rasterization;
  and every primitive checkpoint of all eleven retained ray types is listed
  after rasterization and subdivision.  In particular, the scaled discarded
  final segment of a classified route rasterizes to its exact canonical
  forward retained ray, while a completely orthogonal retained polyline is
  fixed pointwise by rasterization.  Thus each refined terminal checkpoint
  is an actual point of that unit-grid route.  These local membership facts lift to the
  complete scaled route.  The exact global adapter rasterizes the first
  route's `dropLast` prefix separately and proves that its disjointness from
  the second complete unit-grid route implies the finite checkpoint-avoidance
  certificate and hence the mixed source-prefix corridor separation needed by
  the angular fan.  This prefix/route form deliberately permits two incidence
  routes of one variable to share their final variable endpoint; a stronger
  complete-route disjointness wrapper is also available when applicable.
- [`LeanTrominoes/RetainedRayRasterizationSeparation.lean`](LeanTrominoes/RetainedRayRasterizationSeparation.lean)
  makes the rasterization clearance quantitative.  Every point introduced by
  retained-ray rasterization and unit subdivision lies within radius nine of
  the endpoint rectangle of a specific source segment, and every raster
  segment retains its source-segment provenance.  Thus pairwise separation of
  integral source-segment rectangles survives any scale greater than `18`;
  at the common factor `288` this directly supplies the prefix/route
  disjointness and terminal-corridor certificates.  The lift separately
  handles the singleton `dropLast` prefix of a two-point incidence route
  through point/segment rectangle separation.  Strict separation of two
  orthogonal source routes is also converted into the complete
  point/segment and segment/segment rectangle certificate, and certificates
  for a route prefix and its final two-point segment recombine over the
  complete route.
- [`LeanTrominoes/RetainedAngularFanSourceRasterSeparation.lean`](LeanTrominoes/RetainedAngularFanSourceRasterSeparation.lean)
  applies the rasterization lift to genuine flat-indexed routes of the final
  retained planar-SAT drawing.  Route membership recovers the corresponding
  positioned clause and literal metadata, hence both retained-ray
  certificates, automatically.  The finite source-polyline rectangle
  certificate then proves the directed scaled source-prefix versus complete
  outer-fan separation theorem without leaving a separate corridor premise.
- [`LeanTrominoes/RetainedAngularFanSourceSpliceBounds.lean`](LeanTrominoes/RetainedAngularFanSourceSpliceBounds.lean)
  bounds every ordinary or escaped source/fan splice inside the radius-288
  expansion of any rectangle containing its raw source route, and bounds
  every factor-eight Figure 7 occurrence suffix inside radius 96 of its
  refined canonical source center.  These reusable estimates reduce the two
  cross-splice/suffix obligations for a completed fallback route pair to
  separation of their original source-route rectangles.
- [`LeanTrominoes/RetainedAngularFanSourceSplicePointSeparation.lean`](LeanTrominoes/RetainedAngularFanSourceSplicePointSeparation.lean)
  combines pointwise lattice clearance for the retained source prefix with
  the radius-288 bound for its replacement fan.  If the raw prefix and its
  discarded axis-aligned final segment both avoid another integral endpoint,
  the complete ordinary splice strictly avoids every route in that endpoint's
  refined radius-96 neighborhood.
- [`LeanTrominoes/RetainedAngularFanSourceEscapedSplicePointSeparation.lean`](LeanTrominoes/RetainedAngularFanSourceEscapedSplicePointSeparation.lean)
  proves the same point-neighborhood theorem for the delayed-lane escaped
  splice.  Its additional escape-fit premise selects the certified escaped
  fan bound; the retained prefix and endpoint-clearance argument are shared
  with the ordinary case.
- [`LeanTrominoes/RetainedAngularFanEqualityLensSingletonSpokeSeparation.lean`](LeanTrominoes/RetainedAngularFanEqualityLensSingletonSpokeSeparation.lean)
  proves both directed cross-splice/suffix obligations for the exceptional
  singleton route in either clause of an arbitrarily oriented equality
  lens.  The proof isolates exact narrow rectangles for the singleton route,
  its partner route, and their opposite variable endpoints, scales their
  integral gaps by the factor-four source clearance, and lifts the result
  through the carrier-lens endpoint renaming.
- [`LeanTrominoes/PolylineBoundingBoxRasterSeparation.lean`](LeanTrominoes/PolylineBoundingBoxRasterSeparation.lean)
  converts containment in two separated closed rectangles into the complete
  point/segment and segment/segment certificate required by factor-288
  rasterization, without assuming that the reference route is orthogonal.
  It specializes this fact both to the retained-terminal corridor and
  directly to two genuine final retained routes, thereby closing every mixed
  source-prefix/fan case whose route pieces occupy distinct bounding boxes.
- [`LeanTrominoes/RetainedFinalRouteMacrocellBounds.lean`](LeanTrominoes/RetainedFinalRouteMacrocellBounds.lean)
  transfers the finite planar-SAT macrocell bound through clause-anchor
  normalization and periodic translation for an entire final noncarrier
  route occurrence.  Distinct translated component centers therefore give
  the exact source-polyline rectangle certificate consumed by retained-ray
  rasterization, reducing the remaining mixed cases to routes whose physical
  components share an interface.
- [`LeanTrominoes/RetainedFinalFlatRouteMacrocellBounds.lean`](LeanTrominoes/RetainedFinalFlatRouteMacrocellBounds.lean)
  recovers that physical occurrence directly from flat final
  `(route, routeIndex)` membership and packages every noncarrier route with
  its translated macrocell center.  Two unequal centers automatically prove
  the directed source-prefix/complete-route rectangle certificate and the
  resulting scaled source-prefix versus outer-fan separation theorem.
- [`LeanTrominoes/RetainedFinalFlatCarrierRouteBounds.lean`](LeanTrominoes/RetainedFinalFlatCarrierRouteBounds.lean)
  packages a flat carrier route with its retained equality lens and transfers
  the lens's explicit narrow rectangle through clause-anchor normalization.
  A carrier source prefix and noncarrier complete route are therefore
  separated whenever that translated carrier rectangle and the noncarrier
  macrocell rectangle are separated, leaving only genuine
  corridor--macrocell interface overlap.
- [`LeanTrominoes/RetainedFinalFlatRouteShapeClassification.lean`](LeanTrominoes/RetainedFinalFlatRouteShapeClassification.lean)
  restores component-sensitive route shape after quotient bookkeeping:
  crossover, routed-clause, and routed-variable routes have singleton
  prefixes, while bend routes remain fully orthogonal.  Translated-center
  classification then closes every directed noncarrier/noncarrier
  source-prefix/fan cross: distinct centers use macrocell separation, and an
  equal-center oblique fan forces the source into the singleton branch.
- [`LeanTrominoes/RetainedFinalFlatRouteComponentCases.lean`](LeanTrominoes/RetainedFinalFlatRouteComponentCases.lean)
  recovers the carrier/noncarrier dichotomy directly from flat route
  membership and proves every carrier route remains fully orthogonal.
  Its component-case reducer discharges carrier fan routes, all noncarrier
  pairs, and separated carrier--macrocell pairs, isolating one exact local
  obligation: a carrier source prefix against an oblique noncarrier fan whose
  translated enclosing rectangles overlap.
- [`LeanTrominoes/RetainedFinalFlatCarrierMacrocellOverlapNormalization.lean`](LeanTrominoes/RetainedFinalFlatCarrierMacrocellOverlapNormalization.lean)
  translates that final overlapping pair into the noncarrier occurrence's
  physical frame.  The noncarrier macrocell returns to its finite center,
  the carrier becomes the link translated by the difference of the two
  recovered physical shifts, and failure of rectangle separation is
  preserved exactly.  This is the common-frame input expected by the
  retained carrier proximity API.
- [`LeanTrominoes/RetainedFinalFlatAnchorNormalizedComponents.lean`](LeanTrominoes/RetainedFinalFlatAnchorNormalizedComponents.lean)
  observes that flat routes already use external period shift zero, so their
  physical shifts are precisely the negatives of their finite clause
  anchors.  It packages the carrier as a neighboring raw retained link,
  realizes the noncarrier orbit by a retained finite source with the exact
  final translated center, and rewrites final rectangle overlap directly in
  this anchor-normalized frame.
- [`LeanTrominoes/RetainedFinalFlatNormalizedDirectComponents.lean`](LeanTrominoes/RetainedFinalFlatNormalizedDirectComponents.lean)
  transfers the oblique fan route's directness into that retained
  anchor-normalized source.  The remaining finite component is therefore
  classified, with all constructor witnesses intact, as exactly a
  crossover, routed clause, or routed-variable arm.
- [`LeanTrominoes/RetainedFinalFlatNormalizedSourceOccurrences.lean`](LeanTrominoes/RetainedFinalFlatNormalizedSourceOccurrences.lean)
  recovers a represented CNF route occurrence for either kind of normalized
  terminal component.  Routed-variable membership exposes its active
  target occurrence directly; a routed-clause literal supplies an original
  source occurrence that is transported into the normalized finite frame.
- [`LeanTrominoes/RetainedFinalFlatNormalizedCarrierContacts.lean`](LeanTrominoes/RetainedFinalFlatNormalizedCarrierContacts.lean)
  applies the raw retained-carrier proximity theorems to an overlapping
  normalized direct component.  The unresolved final pair now carries an
  exact local contact certificate: crossover boundary incidence,
  routed-clause source-terminal incidence, or routed-variable
  target-terminal incidence.
- [`LeanTrominoes/RetainedFinalFlatNormalizedRoutes.lean`](LeanTrominoes/RetainedFinalFlatNormalizedRoutes.lean)
  identifies the final quotient route lists with routes of those exact
  anchor-normalized finite drawings.  Carrier routes come from the raw
  normalized equality lens, while noncarrier routes retain their local
  clause and literal indices in the selected normalized source.
- [`LeanTrominoes/RetainedFinalFlatNormalizedRouteSelections.lean`](LeanTrominoes/RetainedFinalFlatNormalizedRouteSelections.lean)
  transports the corresponding clause and literal witnesses into the actual
  normalized incidence-drawing formulas.  Each final route is now packaged
  as a genuine raw-carrier or retained-noncarrier drawing route, ready for
  the carrier-boundary separation theorem without reconstructing finite
  incidence indices.
- [`LeanTrominoes/RetainedFinalFlatNormalizedContactSeparation.lean`](LeanTrominoes/RetainedFinalFlatNormalizedContactSeparation.lean)
  instantiates the raw crossover and terminal carrier-interface theorems in
  all three normalized contact branches.  Consequently the exact final
  carrier and noncarrier route lists satisfy the complete continuous
  route-avoidance predicate at their shared local boundary.
- [`LeanTrominoes/RetainedFinalFlatNormalizedBoundary.lean`](LeanTrominoes/RetainedFinalFlatNormalizedBoundary.lean)
  preserves the stronger pointwise carrier-interface invariant through the
  normalized route selections.  Each of the crossover, routed-clause, and
  routed-variable contact branches now yields one explicit physical port
  and origin, with the exact final carrier route outside and the exact final
  noncarrier route inside that boundary.
- [`LeanTrominoes/RetainedTerminalBoundaryCheckpointSeparation.lean`](LeanTrominoes/RetainedTerminalBoundaryCheckpointSeparation.lean)
  sharpens that shared-boundary geometry to the factor-288 terminal
  checkpoints used by the oblique raster corridor.  Exact checkpoints stay
  on the refined inside, while points of an outside carrier segment stay on
  the refined outside; their only possible contact is the scaled physical
  port and hence one of the terminal endpoints.  Together with strict
  source-prefix/route separation, these endpoint reductions prove the full
  mixed source-prefix corridor certificate.
- [`LeanTrominoes/RetainedFinalFlatNormalizedCorridorSeparation.lean`](LeanTrominoes/RetainedFinalFlatNormalizedCorridorSeparation.lean)
  combines the final drawing's strict prefix/full-route separation with the
  normalized boundary and checkpoint bridge.  It discharges the last
  overlapping carrier-prefix versus oblique noncarrier-fan case, exporting
  the resulting source-corridor certificate for reuse, and closes the older
  outer-route component reducer.  The resulting unconditional directed
  separation, applied in both directions, closes the complete pairwise
  splice theorem once separation of the selected outer fans is supplied.
- [`LeanTrominoes/RetainedAngularFanOuterSourceSeparation.lean`](LeanTrominoes/RetainedAngularFanOuterSourceSeparation.lean)
  bounds every complete outer fan in the radius-288 expansion of its
  combined-scaled discarded source-terminal rectangle.  Two source terminal
  rectangles separated by one integral lattice unit therefore yield
  strictly separated complete outer fans after the factor-four source
  refinement.
- [`LeanTrominoes/RetainedAngularFanOuterEscapedSourceSeparation.lean`](LeanTrominoes/RetainedAngularFanOuterEscapedSourceSeparation.lean)
  proves that delaying the lane shift preserves the ordinary radius-65
  source-terminal corridor and hence the same radius-288 discarded-terminal
  rectangle bound.  The existing rectangle-separation certificate therefore
  separates escaped/ordinary and escaped/escaped complete fan pairs without
  new global geometry.
- [`LeanTrominoes/RetainedFinalOuterFanSeparation.lean`](LeanTrominoes/RetainedFinalOuterFanSeparation.lean)
  derives that terminal-rectangle premise from the final retained drawing
  itself for the broad axis-aligned, endpoint-distinct class.  Endpoint-only
  route planarity becomes strict separation when all four advertised
  endpoint pairs differ; axis alignment then separates the two discarded
  terminal rectangles, hence the complete outer fans and finally the two
  full source-to-boundary splices.  A head-aware companion permits the two
  source routes to share their clause endpoint: cross endpoints must still
  differ, but excluding two simultaneous singleton prefixes is enough to
  recover strict terminal-rectangle and complete-outer-fan separation.
- [`LeanTrominoes/RetainedFinalEscapedOuterFanSeparation.lean`](LeanTrominoes/RetainedFinalEscapedOuterFanSeparation.lean)
  reuses that shared-head terminal-rectangle certificate when the first fan
  is the delayed-lane escape.  Thus a singleton escaped fallback and its
  necessarily non-singleton ordinary partner have strictly separated fan
  tails; restricting the escaped fan to its head also supplies the directed
  singleton-prefix/ordinary-fan cross case.
- [`LeanTrominoes/RetainedFinalSharedCenterFanSeparation.lean`](LeanTrominoes/RetainedFinalSharedCenterFanSeparation.lean)
  closes the complementary shared-variable-center class.  Two distinct
  genuine occurrences ending at the same variable point select different
  angular slots, so the order-free occurrence theorem separates their
  complete outer fans; the unconditional prefix/fan cross theorem then
  separates their full source-to-boundary splices.  This result includes
  every certified oblique terminal direction and requires no axis-alignment
  hypothesis.
- [`LeanTrominoes/PositionedPeriodicCNFTaggedRouteLookup.lean`](LeanTrominoes/PositionedPeriodicCNFTaggedRouteLookup.lean)
  now provides both directions of the bridge between genuine positioned
  clause/literal incidences and the drawing's flat indexed route list.
  In the forward direction it returns the metadata incidence and physical
  route at one common index, allowing source-coordinate distinctness to
  discharge flat-index distinctness.  Compatibility also separates the
  head of any genuine incidence route from the tail of any other genuine
  incidence route: a clause lift cannot equal a periodically translated
  variable lift.
- [`LeanTrominoes/RetainedFinalPositionedOccurrenceSpliceSeparation.lean`](LeanTrominoes/RetainedFinalPositionedOccurrenceSpliceSeparation.lean)
  exposes both completed splice separators directly at the positioned source
  interface.  Shared-center occurrences may have arbitrary retained terminal
  directions; distinct-center occurrences use the axis-aligned final-segment
  case.  Both theorems derive flat memberships and indices, route lengths,
  classified endpoints, distinct-index facts, and every clause-versus-variable
  endpoint inequality automatically, leaving global route-pair assembly to
  supply only the incidence memberships and the relevant physical
  source/center case.
- [`LeanTrominoes/RetainedAngularFanBoundaryRouteFamily.lean`](LeanTrominoes/RetainedAngularFanBoundaryRouteFamily.lean)
  lifts the splice to a total clause/literal-indexed boundary-route family.
  Genuine source incidences select their exact classified terminal data and
  bounded angular slot, with certified scale-288 clause endpoints,
  factor-eight Figure 7 boundary endpoints, and orthogonality.
- [`LeanTrominoes/OrthogonalPolylineScaling.lean`](LeanTrominoes/OrthogonalPolylineScaling.lean)
  packages the reusable fact that positive integral scaling preserves
  orthogonality of a polyline.
- [`LeanTrominoes/RetainedAngularFanOccurrenceSplice.lean`](LeanTrominoes/RetainedAngularFanOccurrenceSplice.lean)
  joins each retained source-to-boundary route to the factor-eight local fan
  spoke.  Genuine source incidences thereby reach their exact copied-literal
  endpoints while preserving orthogonality.
- [`LeanTrominoes/RetainedAngularFanCompleteRoutes.lean`](LeanTrominoes/RetainedAngularFanCompleteRoutes.lean)
  assembles one total route family: retained fan splices for copied source
  clauses and factor-eight certified Figure 7 routes for implication-cycle
  clauses.  It also packages the matching refined positioned formula and
  placement without changing the logical fixed-eight formula.
- [`LeanTrominoes/RetainedAngularFanCompleteRouteCertificates.lean`](LeanTrominoes/RetainedAngularFanCompleteRouteCertificates.lean)
  proves canonical endpoints and orthogonality for every genuine route in
  that refined formula, separately transporting the copied-clause splice and
  scaled implication-cycle certificates.
- [`LeanTrominoes/RetainedAngularFanDrawing.lean`](LeanTrominoes/RetainedAngularFanDrawing.lean)
  instantiates the route certificates with the retained planar-SAT source and
  packages the resulting family with canonical endpoints and pointwise
  orthogonality.
- [`LeanTrominoes/PositionedPeriodicCNFRetainedRayRasterization.lean`](LeanTrominoes/PositionedPeriodicCNFRetainedRayRasterization.lean)
  packages canonical incidence endpoints together with the retained-ray
  condition.  Positive integral scaling preserves that complete certificate
  before rasterization; executable staircase rasterization then preserves the
  exact scaled endpoints and produces a canonical orthogonal route family
  for the unchanged logical incidence graph.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATRasterizedDrawing.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATRasterizedDrawing.lean)
  applies that interface to the final gauged, wrapped, and orbit-deduplicated
  planar-SAT routes.  It defines the scaled rasterized incidence drawing and
  proves exact canonical endpoints and orthogonality for every genuine
  route.  Unit subdivision below turns this orthogonal drawing into a
  presentation satisfying the project's integer-grid planarity predicate.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATPlanarizedDrawing.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATPlanarizedDrawing.lean)
  transfers compatibility from the positively scaled retained reference
  drawing to the rasterized route family and applies ordered unit
  subdivision.  It packages the resulting scaled drawing as a complete
  `PlanarIncidencePresentation` of the retained planar-SAT incidence graph.
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
- [`LeanTrominoes/EmbeddedCNFIncidenceDrawingPlanarity.lean`](LeanTrominoes/EmbeddedCNFIncidenceDrawingPlanarity.lean)
  extracts route simplicity, pairwise continuous separation, and
  vertex/route-interior avoidance from those finite-index certificates using
  ordinary vertex, clause, literal, and segment membership data, which is the
  form needed by global assembly proofs.
- [`LeanTrominoes/EmbeddedCNFIncidenceDrawingIndexedSegmentSeparation.lean`](LeanTrominoes/EmbeddedCNFIncidenceDrawingIndexedSegmentSeparation.lean)
  repackages finite planarity for flat `zipIdx` incidence and segment
  occurrences: differing incidence or within-route indices imply disjoint
  continuous segment interiors.
- [`LeanTrominoes/EmbeddedCNFIncidenceDrawingIndexedRoutePointSeparation.lean`](LeanTrominoes/EmbeddedCNFIncidenceDrawingIndexedRoutePointSeparation.lean)
  transfers the finite endpoint-only contact certificate to indexed route
  points: a listed point geometrically equal to the head or last point is
  certified as an outer route endpoint.
- [`LeanTrominoes/EmbeddedCNFIncidenceDrawingMapPoints.lean`](LeanTrominoes/EmbeddedCNFIncidenceDrawingMapPoints.lean)
  proves a generic transport theorem for complete finite drawing
  certificates under any injective point map preserving axis alignment,
  point/segment interiors, and segment/segment interior intersection.
- [`LeanTrominoes/EmbeddedCNFIncidenceDrawingAxisPlacement.lean`](LeanTrominoes/EmbeddedCNFIncidenceDrawingAxisPlacement.lean)
  instantiates that transport theorem for all four signed grid axes.
  Quarter-turn orientation followed by arbitrary translation preserves
  endpoints, orthogonality, and continuous planarity.
- [`LeanTrominoes/OccurrenceSplitRingDrawing.lean`](LeanTrominoes/OccurrenceSplitRingDrawing.lean)
  encodes the worst-case degree-eight neighborhood of Figure 7.  Eight
  source-port copies and one degree-two separator lie on an inner square,
  nine implication clauses occupy their cyclic gaps, and the four diagonal
  old rays bend outside the ring.  The separator cuts the clause presentation
  so that every real degree-three copy has its copied source occurrence
  first, its incoming ring edge second, and its outgoing ring edge third;
  their terminal directions are clockwise in Lean's axis convention.
  Finite computation certifies all 26 incidences
  simultaneously: exact endpoints, orthogonality, and continuous planarity.
  This is the local kernel for the geometry-ordered occurrence-splitting
  substitution.
- [`LeanTrominoes/PeriodicEightOccurrenceSplit.lean`](LeanTrominoes/PeriodicEightOccurrenceSplit.lean)
  gives that geometric kernel a matching periodic Boolean reduction.  Every
  source occurrence selects one of eight compass copies, those copies and
  the degree-two separator remain on the implication ring, and unused copies
  are harmless.  The resulting formula is proved equisatisfiable for every
  slot assignment; it also preserves width three and locality.  The geometric
  no-collision condition is intentionally reserved for the degree-three
  certificate.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitOccurrences.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitOccurrences.lean)
  isolates that no-collision condition and proves the promised degree
  accounting.  A selected compass copy occurs at most once in the copied
  source clauses, while its fixed implication ring contributes at most two
  occurrences, so every output variable occurs at most three times.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitDegreeThreeOriginal.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitDegreeThreeOriginal.lean)
  uses the two-occurrence cycle bound to classify every output variable that
  reaches its third occurrence slot.  It must be the selected real port copy
  of a genuine tagged source occurrence, so the separator and all unselected
  copies create no variable-order obligation.  It also splits every complete
  three-slot occurrence lookup into exactly one copied-source occurrence
  followed by the two shifted cycle occurrences in presentation order.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitCycleOccurrenceIndex.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitCycleOccurrenceIndex.lean)
  identifies the clause/literal indices of a renamed semantic implication
  ring with the corresponding finite embedded-cycle incidences.  Filtering
  any real port copy therefore recovers exactly the two local indices used
  by the clockwise-direction certificate.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitRouteTerminalDirections.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitRouteTerminalDirections.lean)
  proves that periodic translations and copied-route splicing preserve the
  certified terminal directions of local Figure 7 spokes and implication
  routes.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitCycleBlockIndex.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitCycleBlockIndex.lean)
  proves that filtering the flattened implication suffix preserves the two
  local cycle indices in order, shifted by the atom's unique block origin,
  and that those shifted indices retrieve the corresponding positioned
  Figure 7 routes.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitVariableRouteOrder.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitVariableRouteOrder.lean)
  combines copied-source provenance, global ring-block indexing, and the
  local Figure 7 direction certificate.  Every degree-three split variable's
  actual angular-spliced routes therefore end in clockwise occurrence order:
  copied source spoke first, incoming ring incidence second, and outgoing
  ring incidence third.  The result applies to arbitrary certified boundary
  prefixes and specializes to the concrete canonical route family.
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
  proves that the arbitrary integer-ray polar comparator and its squared-
  radius tie-break are total and transitive, including the angle comparator's
  zero fallback.  Consequently each merge-sorted occurrence list is pairwise
  ordered by its actual terminal rays and from near to far within collinear
  blocks, providing the rotation-system fact needed by the noncrossing local
  fan even when an incidence is not compass-aligned.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitAngularFanOrder.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitAngularFanOrder.lean)
  identifies each angular occurrence-list index with its east-first Figure 7
  port, cyclic port rank, and positioned split-copy vertex.  Increasing list
  indices are also proved to follow the actual polar-and-radial order of the
  source terminal rays, giving the local fan a direct combinatorial
  interface.
- [`LeanTrominoes/OccurrenceSplitAngularFanDrawing.lean`](LeanTrominoes/OccurrenceSplitAngularFanDrawing.lean)
  extracts the first `n` east-first Figure 7 spokes together with the full
  separator-enhanced implication ring.  All nine possible sizes
  `0 ≤ n ≤ 8` are mechanically certified for exact endpoints,
  orthogonality, and continuous planarity, providing the finite geometric
  kernel for each angular variable fan.
- [`LeanTrominoes/EmbeddedCNFIncidenceDrawingRenaming.lean`](LeanTrominoes/EmbeddedCNFIncidenceDrawingRenaming.lean)
  transports a complete finite incidence-drawing certificate through an
  logical variable renaming that is injective on the variables actually
  occurring in the drawing and whose target placement preserves their source
  coordinates.  Incidence order and routes remain unchanged; unused template
  roles impose no artificial injectivity obligation.  A canonical
  image-placement construction now derives those target coordinates
  automatically from any injective-on-occurrences variable map.
- [`LeanTrominoes/OccurrenceSplitAngularFanInstantiation.lean`](LeanTrominoes/OccurrenceSplitAngularFanInstantiation.lean)
  renames a certified angular fan's port and separator vertices via
  `ringCopy` and translates it into the selected positioned source-variable
  macrocell.  The resulting total variable placement is proved identical to
  the semantic fixed-eight placement, and every fitting instance inherits
  the full finite drawing certificate.
- [`LeanTrominoes/OccurrenceSplitAngularFanBoundary.lean`](LeanTrominoes/OccurrenceSplitAngularFanBoundary.lean)
  exposes one positioned boundary point and one local route suffix for each
  angular occurrence index.  Every suffix is proved orthogonal with exact
  endpoints at that boundary and the selected semantic copy, and is
  identified with the corresponding route of the certified local fan.
  Periodically translated variants correctly lift the boundary and suffix to
  the neighboring occurrence named by a literal's anchor-relative offset.
- [`LeanTrominoes/OccurrenceSplitAngularFanSpokeSeparation.lean`](LeanTrominoes/OccurrenceSplitAngularFanSpokeSeparation.lean)
  certifies that distinct valid slots select contact-free Figure 7 spokes at
  a common positioned occurrence origin.  Every spoke is also enclosed in
  its translated `24 × 24` macrocell, so strictly separated occurrence
  rectangles give contact-free spokes without any condition on their slots.
- [`LeanTrominoes/OrthogonalPolylineJoin.lean`](LeanTrominoes/OrthogonalPolylineJoin.lean)
  joins independently certified route pieces at a shared endpoint while
  removing its duplicate list entry.  The joined route is proved to preserve
  both outer endpoints and any caller-specified chain relation, with
  orthogonality as an immediate specialization, supplying the generic splice
  lemma used by fan and later gadget routing.
- [`LeanTrominoes/OrthogonalPolylineJoinSimplicity.lean`](LeanTrominoes/OrthogonalPolylineJoinSimplicity.lean)
  proves the corresponding geometric-simplicity rule.  Two individually
  simple and continuously separated routes whose join boundary is their only
  common listed point remain simple after the duplicate boundary entry is
  removed.
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
- [`LeanTrominoes/PeriodicGridDrawingUnitSubdivision.lean`](LeanTrominoes/PeriodicGridDrawingUnitSubdivision.lean)
  applies ordered unit subdivision to every route in a periodic grid
  drawing.  Compatibility and orthogonality are preserved.  Because a
  genuine unit axis segment contains no integer lattice point in its
  relative interior, every subdivided orthogonal drawing automatically
  satisfies the route-interior and vertex-interior obligations of
  `PeriodicGridDrawing.IsPlanar`.
- [`LeanTrominoes/OrthogonalPolylineEndpointDirections.lean`](LeanTrominoes/OrthogonalPolylineEndpointDirections.lean)
  exposes total first- and last-edge direction lookups for unit orthogonal
  polylines.  Every route with at least one edge receives genuine cardinal
  endpoint directions, and the last lookup is identified with the forward
  direction of any explicitly displayed final edge.  These are the finite
  direction parameters consumed by the ribbon endpoint fans.
- [`LeanTrominoes/OrthogonalPolylineNoImmediateReversalJoin.lean`](LeanTrominoes/OrthogonalPolylineNoImmediateReversalJoin.lean)
  proves that two nondegenerate orthogonal no-reversal routes can be spliced
  at a shared endpoint whenever their newly adjacent directions are
  compatible.  This isolates the only new local condition introduced by a
  route join and supplies the compositional invariant used by the
  orthocrossing construction.
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
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonCorridorSimplicity.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonCorridorSimplicity.lean)
  handles the same-colored, same-route case.  Consecutive tiles share only
  their intended half-edge boundary, while duplicate freedom makes every
  nonconsecutive tile pair contact-free; induction with endpoint-join
  simplicity proves that each complete corridor core is geometrically simple.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceCorridorSimplicity.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceCorridorSimplicity.lean)
  applies corridor simplicity to every active occurrence of a ribbon-ready
  source.  Unitization supplies genuine steps, continuous planarity rules out
  immediate reversals, and ribbon readiness supplies duplicate freedom, so
  each selected occurrence corridor core is geometrically simple.
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
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedRouteLength.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedRouteLength.lean)
  proves that the same factor-two padding inserts a genuine interior lattice
  point into every active source route.  The proof transports this
  length-at-least-three invariant through anchor normalization, giving the
  source fact needed to exclude the mixed-fan classifier's sole exceptional
  first-neighbor offset.
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
  internal.  Its adjacent-start variant proves that two separated routes
  cannot point toward each other through the unit edge joining their starts;
  reversing both routes gives the analogous obstruction for adjacent final
  points entered from their shared edge.
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
  while unequal incidences of one clause orbit enter every translated clause
  copy in different directions.  Translation invariance connects those
  directions to the stored routes at their common canonical clause vertex.
  It also rules out the opposing-direction pattern that could make two
  variable endpoint fans in adjacent macrocells touch, and the corresponding
  incoming pattern for clause fans at adjacent lifted targets.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirectionFamilies.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirectionFamilies.lean)
  packages the coordinated local inputs needed by that construction.
  Occurrences at one variable and in one finite clause orbit are enumerated
  without duplicates; their outgoing or incoming cardinal directions are
  proved genuine and pairwise distinct.  Grouping clause incidences by orbit
  correctly allows different literal offsets, whose physical fans are
  period translates.  Variable families are additionally bounded by the
  three available occurrence slots.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonLaneAssignment.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonLaneAssignment.lean)
  separates semantic 3DM colors from the three physical tracks of a source
  ribbon.  The fixed-red, fixed-blue, and fixed-green connector kinds select
  the three cyclic lane permutations required by the top, left, and right
  clause terminals.  The assignment is proved bijective, puts every
  connector's fixed color on the outermost lane, and makes all three clause
  attachment orders agree with one uniform physical-lane order.  The
  occurrence-level corridor, endpoint, bounds, and separation APIs all route
  a semantic color through this connector-dependent lane assignment.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableFanFinite.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableFanFinite.lean)
  erases one variable endpoint neighborhood to its finite connector kinds,
  polarities, and outgoing cardinal directions, while retaining its exact
  routed RGB ports.  A certified one-occurrence counterexample shows that the
  old independently selected green and blue elbows already cross, so the
  remaining fan construction must coordinate colors even before coordinating
  distinct occurrences.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableLocalGates.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableLocalGates.lean)
  coordinates each of the six variable connector patterns into the same
  kind-independent physical-lane gate triple above its occurrence slot,
  applying the connector's semantic-color permutation along the way.
  Exhaustive finite certificates prove exact port and gate endpoints,
  rectilinearity, standard-macrocell containment, and strict separation
  across every choice of colors and active slot patterns.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableOuterFans.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableOuterFans.lean)
  enumerates all 28 cyclically admissible families of one, two, or three
  distinct variable-side exit directions and supplies a simultaneous
  annular RGB router for each.  Lean exhaustively certifies the generated
  tables' exact standardized-gate and ribbon-exit endpoints, rectilinearity,
  macrocell and protected-frame bounds, and strict separation of every pair
  of active colored strands.  A common lower-detour correction leaves a
  one-row gap below the complete variable-site core, and every outer segment
  is classified into one of the four safe-frame arms.  This makes the required
  cyclic-order invariant explicit at the remaining source-presentation
  boundary.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentVariableOuterFans.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentVariableOuterFans.lean)
  classifies contacts between two selected variable outer-fan tables in
  neighboring ribbon macrocells.  An exhaustive certificate covers all 28
  templates, active slots, colors, and eight adjacent offsets: contact is
  impossible unless the centers differ by one cardinal step and both source
  directions point along that shared unit edge.  Compatible abstract fan
  data are connected back to the finite table by certified template lookup.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentVariableFans.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentVariableFans.lean)
  extends that adjacent-macrocell classifier from outer annular routes to
  complete connector-to-boundary variable stubs.  Three smaller exhaustive
  checks certify local/local and both local/outer interactions; the endpoint
  joins leave the same single possible contact pattern, namely two source
  directions facing through their common cardinal edge.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableFanMacrocellSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableFanMacrocellSeparation.lean)
  classifies contact between a complete coordinated variable fan and one
  legal corridor tile in an adjacent macrocell.  The actual first source
  tile on the selected physical lane is ordinarily separated from the fan
  and shares only its advertised exit; all other neighboring tiles, and the
  connector-local gates outright, are contact-free.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentClauseFans.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentClauseFans.lean)
  performs the reflected clause-side classification.  Exhaustive certificates
  cover outer/outer, local/local, and both cross interactions for two- and
  three-terminal fans.  Complete clause stubs in adjacent macrocells are
  contact-free unless both source routes enter their targets from the shared
  edge.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonClauseFanMacrocellSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonClauseFanMacrocellSeparation.lean)
  classifies contact between a complete coordinated clause fan and one legal
  corridor tile in an adjacent macrocell.  The actual final source tile on
  the selected physical lane is ordinarily separated from the fan and shares
  only its advertised entry; all other neighboring tiles, and the
  connector-local gates outright, are contact-free.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentVariableClauseFans.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentVariableClauseFans.lean)
  performs the mixed variable/clause finite classification across all
  `28 × 28` outer-template pairs and the three local/outer interactions.
  Complete mixed fans are contact-free in every adjacent macrocell except
  when the clause center is exactly the selected first source neighbor of the
  variable fan.  This isolates the source-level padding invariant needed to
  finish the `variableClause` obligation.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoordinatedFans.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoordinatedFans.lean)
  joins each connector-dependent gate route to its selected cyclic outer
  route.  Finite interface checks show that the two pieces meet only at the
  advertised gate and that different pieces are contact-free; the resulting
  complete variable stubs have exact gadget-port and ribbon-exit endpoints,
  with each semantic color ending on its assigned physical lane.  They are
  rectilinear, bounded, simple, and pairwise strictly separated.  Their sole
  remaining premise is the now-explicit clockwise compatibility of the source
  occurrence directions.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreLocalGates.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreLocalGates.lean)
  checks the interface between the finite variable-site drawing and those
  coordinated gates.  Every site route and every active gate have disjoint
  segment interiors and mutually avoid point-to-interior contacts; the
  selected occurrence-and-color route has the stronger certificate that its
  only listed contact with the gate is their unique splice port.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreCoordinatedFans.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreCoordinatedFans.lean)
  extends the core-to-gate certificates through complete coordinated variable
  fans.  Every variable-site route strictly avoids every outer fan and avoids
  the interiors of every complete fan, including nonmatching occurrence/color
  pairs whose listed points may coincide.  The selected matching pair retains
  the stronger endpoint-only contact certificate at its advertised port.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonClauseOuterFans.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonClauseOuterFans.lean)
  packages the active top/left or top/left/right clause terminals and reuses
  the 28 certified variable outer-fan templates by vertical reflection and
  route reversal.  Finite certificates prove exact physical-lane entry and
  gate endpoints, rectilinearity, macrocell containment, and pairwise strict
  separation.  The same module records the semantic clause ports in uniform
  physical-lane order.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonFanClockwiseOrder.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonFanClockwiseOrder.lean)
  characterizes membership in the 28 finite endpoint-fan templates by a
  four-way clockwise rank.  One- and two-incidence fans require only genuine,
  distinct directions; three-incidence variable and clause fans add exactly
  one cyclic-order condition, stated respectively in occurrence-slot and
  literal order.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonClauseLocalGates.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonClauseLocalGates.lean)
  shifts the small clause core downward within its macrocell to reserve a
  protected upper annulus, then supplies simultaneous two- and
  three-terminal physical-lane routes from the reflected outer gates to the
  exact core ports.  Lean exhaustively certifies their endpoints,
  rectilinearity, simplicity, bounds, pairwise strict separation, and
  endpoint-only contact with every route of the clause-core drawing.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonClauseCoordinatedFans.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonClauseCoordinatedFans.lean)
  joins the reflected outer fans to those local clause gates.  The resulting
  complete physical strands run from direction-dependent ribbon entries to
  exact clause-core ports; Lean certifies their geometry, simplicity,
  macrocell bounds, pairwise strict separation, and endpoint-only contact
  with the finite clause core.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableFans.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableFans.lean)
  instantiates the finite variable-fan record from an actual active source
  occurrence.  It proves that the record has exactly the source variable's
  active prefix and agrees with the source connector kind, literal polarity,
  and outgoing incidence direction on every active occurrence slot.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableFanOrder.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableFanOrder.lean)
  identifies the finite fan's active prefix with the source occurrence
  prefix and reifies each active slot as its actual occurrence.  Source
  planarity then supplies genuine, pairwise distinct directions
  automatically, reducing variable-fan compatibility to the one clockwise
  condition for variables with exactly three occurrences.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFans.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFans.lean)
  instantiates the finite clause-fan record from all source occurrences
  belonging to one clause orbit.  It detects the optional right terminal,
  activates every represented group, and recovers each genuine incoming
  direction under the explicit one-occurrence-per-terminal condition.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanUniqueness.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanUniqueness.lean)
  discharges that terminal condition for every width-three source.  It
  combines the common clause index, the width-three literal bound, and
  occurrence-slot uniqueness.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanOrder.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanOrder.lean)
  reifies every active clause-terminal group as its source occurrence.
  Source planarity then supplies genuine, pairwise distinct directions,
  reducing clause-fan compatibility to the one clockwise condition for a
  ternary clause; binary clauses are automatic.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseRouteOrder.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseRouteOrder.lean)
  connects that condition to the final unit-elimination route family.
  Ternary routes leave their stored clause south/west/east, so the incoming
  fan directions are north/east/west in clockwise order; binary clauses have
  no right terminal.  Thus every source clause fan is compatible.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanRouteOrder.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanRouteOrder.lean)
  isolates the remaining variable-side invariant both on stored route
  endings and on rebased outgoing directions: at a degree-three variable,
  they follow occurrence slots `first`/`second`/`third` clockwise.  It
  transfers the route form to planar presentations and proves that this
  invariant and the unit-elimination clause order together discharge the
  single compatibility premise required by the coordinated source
  endpoint-fan system.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanPorts.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanPorts.lean)
  identifies the finite coordinated-fan ports and physical lanes with the
  occurrence-level variable ports, clause ports, and corridor lanes.  The
  variable result applies to every occurrence represented by one shared
  source-variable fan.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoordinatedStubs.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoordinatedStubs.lean)
  translates the variable fans and each shared clause-orbit fan into their
  actual source macrocells.  Given the explicit clockwise-order obligation,
  it proves exact global endpoints, rectilinearity, and macrocell
  containment, and packages the result as a `RibbonEndpointFanSystem`.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreSplice.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreSplice.lean)
  identifies the finite fan's selected core route with the routed typed
  variable-site route used by the global assembly, including its dependent
  count and connector indices.  It then composes the macrocell and global
  variable-origin translations and proves that the resulting constructed
  prefix meets the complete coordinated source-variable stub only at their
  advertised port.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreFanSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreFanSeparation.lean)
  transports the finite all-pairs core/fan theorem to source coordinates.
  Every route in a variable-site core avoids the interiors of every
  coordinated variable fan at the same source variable, including
  nonmatching routes with listed-point coincidences permitted by the
  continuous-planarity interface; cores and fans owned by distinct variable
  macrocells are strictly separated.  A sharper exhaustive certificate now
  proves full endpoint-aware `RoutesAvoidEachOther` whenever the core and fan
  belong to different occurrence slots, and transports that fact through the
  complete coordinated fan.  Consequently the listed contacts that still
  need a clearance repair before assignment rasterization are confined to a
  single occurrence module, rather than the whole variable macrocell.  A
  shorter fixed-blue/false local-gate table now removes that module's
  contacts as well.  The executable
  `VariableLocalGateTableEndpointClear` certificate gives full
  endpoint-aware core/fan separation throughout every one-, two-, and
  three-module variable site for the false fixed-red and fixed-blue
  patterns.  Thus the unresolved local clearance cases require either a
  fixed-green connector or the true orientation.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreRouteSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreRouteSeparation.lean)
  extends that all-pairs result across every complete coordinated occurrence
  route.  Source-route endpoint separation makes every variable center fresh
  from unrelated corridor interiors; strict inset bounds then separate the
  corridor and clause-side fan, while the variable-side fan retains the
  precise no-segment-interior-contact guarantee needed for global planarity.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceAssembledRouteSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceAssembledRouteSeparation.lean)
  decomposes every typed incidence route into its finite gadget core and an
  optional coordinated occurrence suffix.  It combines core/core, both
  core/suffix directions, and suffix/suffix separation to prove that every
  pair of distinct colored typed routes has disjoint segment interiors and
  no listed point in the other route's interior.  The core/core stage now
  retains the stronger endpoint-aware `RoutesAvoidEachOther` certificate,
  including its proof that every listed-point contact is an endpoint of both
  finite cores; the former interior-only result is derived from it.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedAssembledRoutes.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedAssembledRoutes.lean)
  transports that decomposition through arbitrary physical translations,
  including the translated splice endpoint.  At the source level it augments
  each stable route identity by an arbitrary lattice shift and proves that a
  nonzero relative shift always selects distinct lifted route occurrences,
  which therefore inherit separation from source continuous planarity.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedCorridorSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedCorridorSeparation.lean)
  proves that ribbon-corridor assembly commutes with source-lattice
  translation.  Lifted source-route separation survives unit subdivision,
  so the existing corridor theorem proves strict separation of length-three
  corridor cores at arbitrary distinct lifted route keys, and in particular
  against every nonzero period translate.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedFanCorridorSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedFanCorridorSeparation.lean)
  transports duplicate-freeness, unit steps, and no-immediate-reversal to
  shifted occurrence routes.  These certificates feed the existing
  endpoint-fan/corridor inductions, separating an unshifted variable or
  clause fan from a shifted corridor; reversing the relative frame gives
  corridor separation from a forward-shifted clause fan.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedFanSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedFanSeparation.lean)
  completes the nonzero-translate endpoint-fan matrix.  Macrocell bounds
  settle distant variable and clause fans; continuous separation of the
  underlying lifted source routes rules out the finite classifiers' facing
  cases for adjacent macrocells.  Coincident translated clause targets are
  traced back to one prototype clause and still select distinct local fan
  strands because the relative period shift is nonzero.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedOccurrenceRouteSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedOccurrenceRouteSeparation.lean)
  supplies the two missing reverse-frame component orientations and composes
  all nine variable-fan/corridor/clause-fan pairs through their certified
  endpoints.  Thus any complete coordinated occurrence route strictly avoids
  every nonzero relative period translate of every other complete occurrence
  route, without requiring the prototype entries or colors to differ.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedCoreSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedCoreSeparation.lean)
  expresses every finite variable-site or clause incidence core as a route in
  the strict inset of its source-owner macrocell.  Periodic source-vertex
  injectivity keeps any two owner macrocells distinct under a nonzero lattice
  shift, proving strict separation of arbitrary finite cores from all their
  nonzero relative period translates.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedCoreCorridorSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedCoreCorridorSeparation.lean)
  covers every finite-core owner by an endpoint of an active source route.
  Endpoint-only contact between distinct lifted source routes then keeps the
  owner fresh from nonzero-translated corridor interiors; strict inset bounds
  also settle the exceptional two-point source route, proving strict
  core/corridor separation at every nonzero relative shift.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedCoreFanSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedCoreFanSeparation.lean)
  separates every finite incidence core from translated variable and clause
  endpoint fans.  Distinct owner centers follow from periodic vertex
  injectivity and strict inset bounds; when a translated clause fan shares a
  clause-core center, the checked finite fan/core table permits only the
  advertised outer-endpoint contact.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedAssembledRouteSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedAssembledRouteSeparation.lean)
  composes finite-core/core, both finite-core/occurrence-route orientations,
  and occurrence-route/occurrence-route separation.  Decomposing both full
  assembled incidences at their certified splice endpoints proves that any
  complete typed route avoids every nonzero relative period translate of any
  other complete typed route.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedAssembledRouteSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedAssembledRouteSeparation.lean)
  specializes complete typed-route separation to the final doubled,
  anchor-normalized construction.  It also transfers the result through
  numeric incidence-tag lookup, proving separation for every pair of
  distinct genuine routes stored by the assembled periodic drawing.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedCoordinatedBounds.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedCoordinatedBounds.lean)
  uses the coordinated fan system's macrocell-containment contract to prove
  that every point of every final assembled route lies in the open one-cell
  halo.  The proof covers the finite variable and clause prefixes as well as
  the genuinely coordinated occurrence-route suffixes.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedVertexCoverage.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedVertexCoverage.lean)
  proves the complementary vertex condition for that final assembly.  The
  encoded degree-two-or-three promise rules out isolated vertices, while
  compatibility and looplessness make every stored graph-vertex position an
  endpoint of a lifted route segment.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedLiftedContactReduction.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedLiftedContactReduction.lean)
  transports distinct stored route indices to unique incidence tags and
  discharges the zero-relative-shift case with the preceding same-period
  theorem.  Halo bounds reduce every possible nonzero translated contact to
  the 24 nonzero shifts in the surrounding `5 × 5` block; checking those
  finite cases, together with simplicity, endpoint coverage, and
  orthogonality, now suffices for continuous planarity of the assembly.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedTranslatedPlanarity.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedTranslatedPlanarity.lean)
  specializes complete translated typed-route separation to the doubled,
  anchor-normalized source and transports it through numeric incidence tags
  to every stored route.  This discharges all nonzero relative lifted
  contacts and proves continuous planarity of the final padded coordinated
  assembly without any remaining finite-neighbor hypothesis.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedContinuousPresentation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedContinuousPresentation.lean)
  combines that continuous-planarity theorem with the already proved
  normalized vertex distinctness and fundamental-square bounds.  The final
  padded coordinated assembly is thereby packaged as a concrete continuously
  planar periodic 3DM presentation, with no residual geometric assumption.
- [`LeanTrominoes/PeriodicGridDrawingExpandedLiftedInteriorContactSeparation.lean`](LeanTrominoes/PeriodicGridDrawingExpandedLiftedInteriorContactSeparation.lean)
  proves the reusable finite-to-infinite bridge behind that reduction.  A
  halo-bounded route pair at any shift outside the `5 × 5` block
  automatically has disjoint segment interiors and both directed
  point/interior separation properties.
- [`LeanTrominoes/PeriodicGridDrawingLiftedInteriorContactSeparation.lean`](LeanTrominoes/PeriodicGridDrawingLiftedInteriorContactSeparation.lean)
  lifts that deliberately weaker three-field separation predicate to the
  infinite periodic drawing.  Pairwise lifted separation plus stored-route
  simplicity proves both global route-interior predicates; ordinary endpoint
  coverage then supplies graph-vertex/interior avoidance, so harmless shared
  bend points do not obstruct continuous planarity.  Its stored/nonzero
  factorization isolates the genuinely periodic translated-route cases.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonAssembledVariablePrefix.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonAssembledVariablePrefix.lean)
  exposes that constructed route as the global assembly's common routed
  variable prefix.  Both the ordinary and fixed-red prefix branches are
  identified with it, and the routed typed-incidence branch is exactly this
  prefix joined to the selected occurrence route.  Assemblies using the
  standard constructed variable origins inherit the coordinated-stub
  avoidance certificate directly.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreMacrocellSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreMacrocellSeparation.lean)
  exhaustively certifies the next finite interface: every selected
  variable-site core remains in its standard ribbon macrocell, misses every
  possible ribbon exit, and strictly avoids every legal corridor tile in
  each of the eight neighboring macrocells.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreClauseFanSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreClauseFanSeparation.lean)
  strengthens that core bound to the one-cell inset rectangle
  `[1, 127] × [1, 127]`.  A generic separated-rectangle argument then proves
  that a selected core strictly avoids any route bounded in an adjacent
  closed macrocell, in particular every complete coordinated clause fan.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreCorridorSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreCorridorSeparation.lean)
  lifts those finite facts into source coordinates.  Duplicate freedom of
  each unit source route lets the neighboring/far-macrocell argument recurse
  over the entire corridor, proving that the assembled routed prefix
  strictly avoids its corridor core and avoids the joined variable-stub plus
  corridor prefix with only the advertised variable-port contact.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreClauseStubSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreClauseStubSeparation.lean)
  lifts the inset certificate to the occurrence's clause target, using
  vertex separation for equal centers and macrocell bounds for far centers.
  It closes the same-incidence splice: the assembled variable prefix avoids
  the complete coordinated variable-stub, corridor-core, and clause-stub
  occurrence route with only its intended variable-port contact.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoordinatedSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoordinatedSeparation.lean)
  begins the global separation proof for that fan system.  Source-variable
  fan data uses a canonical inactive-slot fallback, so every occurrence of
  one variable produces literally the same finite fan.  For different
  variables, compatible drawing positions separate equal centers, macrocell
  bounds separate far centers, and source-route planarity eliminates the one
  facing-direction contact left by the adjacent finite classifier.  Thus all
  distinct variable-side colored stubs are now strictly separated globally.
  Clause-side stubs now have the same complete result: compatibility identifies
  equal lifted clause targets (even across period translations), macrocell
  bounds handle far targets, and source-route planarity discharges the
  adjacent classifier.  Width three recovers occurrence identity inside one
  shared clause fan from its terminal group and physical lane.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreSeparation.lean)
  discharges the coordinated fan system's `variableCore` obligation.  A
  one-edge core is handled by restricting global variable-stub separation to
  its last point.  Longer cores recursively join the finite fan/tile
  certificates: distinct colors separate the intended first-tile lanes,
  while source-route endpoint separation and duplicate freedom exclude that
  contact at every later or inter-occurrence interior center.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableClauseSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableClauseSeparation.lean)
  discharges `variableClause` for any source whose active unit routes have
  length at least three.  Periodic vertex injectivity excludes equal
  variable/clause centers, macrocell bounds handle far centers, and the
  route's first neighbor is an internal point, eliminating the sole adjacent
  placement left by the mixed finite classifier.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoreClauseSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoreClauseSeparation.lean)
  discharges the coordinated fan system's `coreClause` obligation.  It
  exposes every source route as a prefix followed by its final edge and
  inducts toward that edge: duplicate freedom separates every earlier tile,
  while distinct semantic colors select different physical lanes at the
  intended final tile.  Endpoint-only source contact supplies the same
  exclusions for cores belonging to another occurrence.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanCorridorContacts.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanCorridorContacts.lean)
  treats the complementary same-strand interfaces needed for route
  simplicity.  Translation preserves each finite fan's simplicity, and the
  matching first and final corridor tiles are ordinarily separated from
  their endpoint fans with their advertised boundary as the only listed
  contact.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCorridorSimplicity.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCorridorSimplicity.lean)
  extends the first matching interface across the complete occurrence
  corridor.  Duplicate freedom makes every tile after the first contact-free
  from the variable fan, so the complete fan/core join is geometrically
  simple whenever the source route has an interior lattice point.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceOccurrenceRouteSimplicity.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceOccurrenceRouteSimplicity.lean)
  peels the corridor from its variable end to propagate the final tile's
  tail-only clause-fan contact across all earlier contact-free tiles.  Joining
  the simple clause fan to the simple variable-fan/corridor prefix proves
  every complete coordinated occurrence route simple under the same
  length-at-least-three hypothesis.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMGlobalRouteSimplicity.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMGlobalRouteSimplicity.lean)
  exposes the simple-route fields of the checked variable-site and clause
  drawings and transports them to every translated ordinary, fixed-red, and
  clause-core route piece used by the global assembly.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceAssembledRouteSimplicity.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceAssembledRouteSimplicity.lean)
  closes the routed-incidence splice.  A finite table certifies that the
  variable port is the only listed contact between a routed variable-site
  prefix and its coordinated fan; translation and strict corridor/clause
  separation lift that fact to the complete source route.  Together with
  simplicity of both pieces, this proves the assembled routed typed
  incidence simple whenever its unit source route has length at least three.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceEndpointFanSystemSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceEndpointFanSystemSeparation.lean)
  assembles the five source-level pairwise results into the coordinated
  endpoint-fan system's complete separation certificate.  Besides width and
  clockwise compatibility, its sole hypothesis is the proved
  length-at-least-three condition that supplies an interior source-route
  point for the mixed variable/clause case.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceRouting.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceRouting.lean)
  joins those coordinated endpoint fans to the certified corridor cores and
  packages the result as a `ThreeStrandRouting`.  The complete fan-system
  certificate immediately proves contact-free separation of every pair of
  distinct colored occurrence routes, assuming the same source route-length
  invariant.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonFanCompatibilityTransport.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonFanCompatibilityTransport.lean)
  proves that positive coordinate scaling and clause-anchor normalization
  preserve the variable and ternary-clause cyclic route orders.  It combines
  those transports into the clockwise compatibility certificate needed by
  the coordinated fans on the final doubled, normalized ribbon source.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedCoordinatedRouting.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedCoordinatedRouting.lean)
  constructs the final doubled and anchor-normalized coordinated
  `ThreeStrandRouting`.  Width, cyclic order, and the proved padded
  length-at-least-three invariant discharge the complete fan-system
  certificate, so all distinct colored occurrence routes are strictly
  separated.  The same invariant now also proves every occurrence suffix
  and every complete assembled typed incidence route geometrically simple;
  the result is lifted through total tag lookup to every stored edge route.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonRouting.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonRouting.lean)
  specializes that routing to the retained, ordered, fixed-eight final
  gauged Figure 9 presentation.  Its stored width, occurrence, arity, and
  cyclic-order certificates produce one concrete padded normalized routing
  whose distinct colored occurrence routes are all proved contact-free.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonThreeDM.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonThreeDM.lean)
  packages that exact concrete routing as a continuously planar periodic 3DM
  presentation.  Every colored element has degree two or three, and both
  perfect matching and abstract trichromatic orientation are proved
  equivalent to satisfiability of the original local periodic CNF.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonContraction.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonContraction.lean)
  suppresses every degree-two colored element in that concrete endpoint.
  The resulting executable colored graph has a compatible, orthogonal, and
  continuously planar drawing, and its suppressed orientation predicate is
  still equivalent to satisfiability of the original periodic CNF.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitAngularBoundaryRoutes.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitAngularBoundaryRoutes.lean)
  isolates the remaining global obligation for copied source incidences:
  route each copied clause to its angular fan boundary.  Joining any such
  certified prefix with the translated local spoke is proved to give the
  copied literal's exact canonical endpoint while preserving orthogonality.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitAngularSuffixSeparation.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitAngularSuffixSeparation.lean)
  identifies each clause-indexed Figure 7 macrocell origin with the
  factor-36 refinement of its canonical source occurrence center.  Distinct
  integer centers therefore have strictly separated `24 × 24` spoke
  rectangles, both before and after any positive uniform refinement.
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
  because the later angular split orders them radially into adjacent ports.
- [`LeanTrominoes/PlanarThreeSATIncidencePlanarity.lean`](LeanTrominoes/PlanarThreeSATIncidencePlanarity.lean)
  records executable continuous-planarity certificates for the direct
  incidence drawings of both fixed Figure 8 templates, ready for the global
  macrocell assembly.
- [`LeanTrominoes/PlanarThreeSATDuplicatorArm.lean`](LeanTrominoes/PlanarThreeSATDuplicatorArm.lean)
  defines the left, middle, and right fanout-aligned duplicator arms, their
  actual target-terminal ports, their common center, and the two
  compass-compatible equality-clause positions assigned to each arm.
- [`LeanTrominoes/PlanarThreeSATDuplicatorArmIncidenceDrawing.lean`](LeanTrominoes/PlanarThreeSATDuplicatorArmIncidenceDrawing.lean)
  extracts the two-clause direct incidence drawing for one active left,
  middle, or right arm of Figure 8(a), adapted to the actual target-fanout
  ports.  Each arm has exact endpoints, continuous planarity, and
  compass-valid terminal rays; the complete three-arm equality star is also
  certified continuously planar.
- [`LeanTrominoes/PlanarThreeSATDuplicatorArmSeparation.lean`](LeanTrominoes/PlanarThreeSATDuplicatorArmSeparation.lean)
  exhaustively certifies that every genuine route selected from one physical
  arm of the Figure 8(a) duplicator avoids every route selected from either
  of the other two arms.
- [`LeanTrominoes/PlanarThreeSATEqualityLens.lean`](LeanTrominoes/PlanarThreeSATEqualityLens.lean)
  replaces each collinear four-incidence equality link on a long carrier by
  a narrow rectilinear lens.  For every span of at least eight cells, explicit
  finite-index proofs certify exact endpoints, orthogonality, route
  simplicity, pairwise continuous separation, vertex avoidance, and distinct
  vertex positions.  Its endpoint rays are coordinated so consecutive lenses
  use the four compass directions exactly once at their shared variable; a
  symbolic theorem certifies separation of every such adjacent route pair.
- [`LeanTrominoes/PlanarThreeSATEqualityLensPlacement.lean`](LeanTrominoes/PlanarThreeSATEqualityLensPlacement.lean)
  rotates and translates that lens onto any directed grid axis, then
  injectively renames its Boolean roles to any two distinct logical
  variables.  The resulting theorem exposes the exact equality formula and
  endpoint positions together with the transported complete certificate.
- [`LeanTrominoes/PlanarThreeSATEqualityLensCarrierInterface.lean`](LeanTrominoes/PlanarThreeSATEqualityLensCarrierInterface.lean)
  bounds every point of a placed lens in the external closed region of both
  endpoint macrocells.  The proof transports the canonical endpoint wedges
  and endpoint-only port contacts through signed-axis orientation,
  translation, and logical renaming.  Each selected lens route then avoids
  every route of any drawing certified inside either endpoint macrocell.
- [`LeanTrominoes/PlanarThreeSATEqualityLensBoundingBox.lean`](LeanTrominoes/PlanarThreeSATEqualityLensBoundingBox.lean)
  bounds the canonical lens between its endpoints and within normal offsets
  `-2` through `1`, transports the exact narrow rectangle through signed-axis
  placement and renaming, and exposes the resulting corridor for every
  geometrically certified positioned link.
- [`LeanTrominoes/PlanarThreeSATEqualityLinkLens.lean`](LeanTrominoes/PlanarThreeSATEqualityLinkLens.lean)
  reduces drawing one positioned equality link to four carrier facts:
  distinct endpoints, axis alignment, span at least eight, and the advertised
  clause offsets.  Those facts automatically produce the exact formula,
  endpoint positions, and complete finite planarity certificate.
- [`LeanTrominoes/PlanarThreeSATCornerEquality.lean`](LeanTrominoes/PlanarThreeSATCornerEquality.lean)
  supplies the complementary local equality drawing for a route bend.
  Explicit rectilinear four-cycles cover all twelve ordered pairs of distinct
  compass ports in one `20 × 20` macrocell; exhaustive finite checks certify
  exact endpoints, orthogonality, and continuous planarity, and translation
  plus injective renaming place the template at arbitrary bend links.  Each
  port uses the inward and free perpendicular rays and stays on the macrocell
  side of the port, complementing the adjacent straight-carrier lens.
- [`LeanTrominoes/PlanarThreeSATCornerEqualityCarrierInterface.lean`](LeanTrominoes/PlanarThreeSATCornerEqualityCarrierInterface.lean)
  formalizes the internal and external closed regions at every compass port.
  They meet only at the port itself, and pointwise containment on opposite
  sides yields complete continuous route separation in local or translated
  coordinates.  Exhaustive checks put every corner route on the internal
  side of both occupied ports and make all port contact endpoint-only;
  translation and logical renaming preserve both certificates.
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
- [`LeanTrominoes/PeriodicCNFPlanarSATClauseIndex.lean`](LeanTrominoes/PeriodicCNFPlanarSATClauseIndex.lean)
  indexes every clause of the finite planar-SAT formula by one of its five
  geometric sources: a crossover, straight carrier link, route bend, routed
  source clause, or routed variable arm.  The parallel metadata list projects
  exactly to the original flattened formula and retains both finite-family
  membership and the exact local clause index.  In particular, bend metadata
  preserves its `RouteBend`; variable-arm metadata preserves its lifted site,
  enumeration index, and independently classified physical arm, enabling
  lossless selection of the corresponding certified local incidence drawing.
- [`LeanTrominoes/PeriodicCNFPlanarVariablePortGeometry.lean`](LeanTrominoes/PeriodicCNFPlanarVariablePortGeometry.lean)
  computes the exact left, middle, or right local endpoint of every
  constructed target fanout from its target-port rank.  It then proves that
  every selected target terminal is physically identical to the endpoint of
  its classified equality arm at the corresponding lifted variable site.
- [`LeanTrominoes/PeriodicCNFPlanarClausePortGeometry.lean`](LeanTrominoes/PeriodicCNFPlanarClausePortGeometry.lean)
  computes the corresponding physical arm and exact translated port of every
  routed source-clause occurrence.  Degree three makes these source arms
  pairwise distinct within each clause site.
- [`LeanTrominoes/PlanarThreeSATRoutedClauseIncidenceDrawing.lean`](LeanTrominoes/PlanarThreeSATRoutedClauseIncidenceDrawing.lean)
  certifies the fixed source-clause star: any signed subset of the three
  distinct fanout ports has exact straight-ray endpoints and a continuously
  planar incidence drawing.
- [`LeanTrominoes/PlanarThreeSATTerminalCarrierInterface.lean`](LeanTrominoes/PlanarThreeSATTerminalCarrierInterface.lean)
  identifies the left, middle, and right fanout arms with the west, north,
  and east carrier ports.  It proves that every active duplicator-arm route
  and every source-clause ray stays on the internal side of each incident
  port boundary, with endpoint-only contact, and transports both certificates
  through macrocell translation.
- [`LeanTrominoes/PeriodicOrthocrossingCrossoverCarrierInterface.lean`](LeanTrominoes/PeriodicOrthocrossingCrossoverCarrierInterface.lean)
  identifies the crossover's left, right, top, and bottom variables with
  the west, east, south, and north carrier ports.  It certifies that every
  fixed-template incidence route stays on the internal side of all four
  boundaries and has endpoint-only contact at each port.
- [`LeanTrominoes/PeriodicOrthocrossingCrossoverIncidenceDrawing.lean`](LeanTrominoes/PeriodicOrthocrossingCrossoverIncidenceDrawing.lean)
  translates the continuously planar Figure 8(b) incidence template to each
  canonical crossing and injectively renames its boundary and internal roles
  into the final planar-SAT variable type.  The adapter proves the exact
  local clause formula, every realized variable position, physical route
  endpoints, continuous planarity, and preservation of the fixed
  eight-direction compass terminal rays.
- [`LeanTrominoes/PeriodicOrthocrossingCrossoverComponentCarrierInterface.lean`](LeanTrominoes/PeriodicOrthocrossingCrossoverComponentCarrierInterface.lean)
  transports all four internal boundary and endpoint-contact certificates
  to each actual placed and logically scoped crossover drawing.
- [`LeanTrominoes/PeriodicOrthocrossingWireIncidenceDrawings.lean`](LeanTrominoes/PeriodicOrthocrossingWireIncidenceDrawings.lean)
  embeds both certified wire templates into the final planar-SAT variable
  type through one common carrier map.  Every represented straight-carrier
  lens and route-bend corner is identified with its exact indexed clause
  block and retains its complete endpoint, orthogonality, and continuous
  finite-planarity certificate under that embedding.  Both adapters also
  expose the external lens and internal corner port-boundary bounds and
  endpoint-only contact certificates in their final variable type.
- [`LeanTrominoes/PeriodicOrthocrossingRoutedVariableIncidenceDrawing.lean`](LeanTrominoes/PeriodicOrthocrossingRoutedVariableIncidenceDrawing.lean)
  translates the certified two-clause template for an active physical arm
  into its lifted variable macrocell and renames its endpoint roles to the
  indexed equality link.  The adapter proves the exact clause block,
  realized endpoint positions, route endpoints, continuous planarity, and
  compass-valid terminal rays.
- [`LeanTrominoes/PeriodicOrthocrossingRoutedClauseIncidenceDrawing.lean`](LeanTrominoes/PeriodicOrthocrossingRoutedClauseIncidenceDrawing.lean)
  translates the fixed three-port source-clause star into each routed clause
  macrocell and renames its ports to the actual source terminals.  The
  adapter proves the exact singleton formula, realized terminal positions,
  route endpoints, and continuous planarity.
- [`LeanTrominoes/PeriodicOrthocrossingTerminalComponentCarrierInterface.lean`](LeanTrominoes/PeriodicOrthocrossingTerminalComponentCarrierInterface.lean)
  transports the internal carrier-boundary and endpoint-only contact
  certificates from the fixed arm and clause-star templates to the actual
  placed routed-variable and routed-clause drawings.
- [`LeanTrominoes/PeriodicOrthocrossingPlanarSATLocalIncidenceDrawings.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarSATLocalIncidenceDrawings.lean)
  turns the five-way clause-source metadata into a total component-aware
  route selector.  Every genuine global clause is proved to occur at the
  selected drawing's recorded local index, and the selected crossover, lens,
  corner, source-clause, or variable-arm route has its exact global
  incidence endpoints, and every selected local drawing is continuously
  planar.  The same endpoint certificate is transported
  through periodicization, opaque wrapping, clause-orbit deduplication, and
  anchor normalization.
- [`LeanTrominoes/PeriodicOrthocrossingPlanarSATFiniteIncidenceDrawing.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarSATFiniteIncidenceDrawing.lean)
  packages the metadata-selected routes as one finite embedded incidence
  drawing.  It proves exact endpoints and route simplicity for every global
  incidence, exposes each route's precise valid local witness, and proves
  pairwise route separation within every shared geometric component,
  including distinct clauses of one gadget.  A generic duplicate-free
  incidence-index theorem lifts those local certificates to global incidence
  indices.  The five clause families now have certified, pairwise-distinct
  `(geometric component, local clause index)` keys.  The remaining
  cross-component obligation has also been factored into a purely geometric
  certificate on two valid metadata-selected local drawings, with all global
  clause-index and lookup bookkeeping discharged by a lifting theorem.
  After that geometric certificate, complete finite planarity reduces exactly
  to global vertex avoidance and assembled vertex-position distinctness.
- [`LeanTrominoes/OrthogonalPolylineBoundingBox.lean`](LeanTrominoes/OrthogonalPolylineBoundingBox.lean)
  defines closed integer rectangles and proves that routes contained in
  strictly separated rectangles have neither continuous interior
  intersections nor shared listed points.  Its route-point predicate is
  preserved by point maps, variable renaming, and translation; a parallel
  predicate records and transports endpoint-only contact at a designated
  physical point.
- [`LeanTrominoes/PeriodicOrthocrossingPlanarSATMacrocellBounds.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarSATMacrocellBounds.lean)
  bounds every crossover, bend,
  source-clause, and active variable-arm route inside the first `13 × 13`
  cells of its `20 × 20` macrocell and proves contact-free separation for
  any two such components at distinct drawing-grid centers.
- [`LeanTrominoes/PeriodicOrthocrossingPlanarSATMacrocellCenters.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarSATMacrocellCenters.lean)
  proves that a lifted constructed-drawing vertex position uniquely
  determines its protovertex and lattice translate.  Consequently,
  represented clause sites are position-injective, represented variable
  sites are position-injective, and a clause site can never coincide with a
  variable site, including when the source formula contains empty clauses.
  It also proves that two active links at one represented variable site
  classified as the same physical duplicator arm are the same link, and
  that two canonical crossover records at the same drawing point are equal.
- [`LeanTrominoes/PeriodicOrthocrossingRouteBendCenters.lean`](LeanTrominoes/PeriodicOrthocrossingRouteBendCenters.lean)
  classifies every inner point of a constructed route as one of eight
  semantic port, track, gate, boundary, or fanout positions in the half-open
  fundamental square.  The generated route list is proved to enumerate
  exactly those indexed placements.  For a well-formed local degree-three
  graph, periodic normalization and the within-route no-duplicate
  classification then prove that two enumerated bends at the same drawing
  point are the same bend.
- [`LeanTrominoes/PeriodicOrthocrossingMacrocellCenterDisjointness.lean`](LeanTrominoes/PeriodicOrthocrossingMacrocellCenterDisjointness.lean)
  proves that no enumerated route-bend center can coincide with any lifted
  declared graph-vertex position.  The local proof separates track and port
  heights from vertex height, while the only remaining fanout case uses the
  construction's explicit off-center condition; half-open periodic
  normalization then lifts the disjointness to the infinite drawing.
- [`LeanTrominoes/PeriodicOrthocrossingCrossoverCenterDisjointness.lean`](LeanTrominoes/PeriodicOrthocrossingCrossoverCenterDisjointness.lean)
  proves that no canonical crossover center can coincide with a lifted
  declared graph vertex.  A reusable one-coordinate normalization lemma
  first identifies the crossover's horizontal lane: private tracks are too
  high, and the unique interior grid point of a remaining fanout lane lies
  one column away from every vertex center.  It also recovers the exact two
  classified segments adjacent to every enumerated bend, proves that two
  vertical adjacent roles characterize exactly the height-three port
  markers, and proves the period-wide endpoint/interior exclusion lemma
  needed to separate bend centers from genuine crossings.  Combining those
  facts with an even-endpoint/odd-fanout-midpoint invariant proves that no
  canonical crossover center can coincide with any enumerated bend center.
- [`LeanTrominoes/PeriodicOrthocrossingPlanarSATRoutedVariableSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarSATRoutedVariableSeparation.lean)
  transports the finite different-arm certificate through macrocell
  translation and logical renaming.  Thus two distinct routed-variable
  components sharing a lifted variable center must use different physical
  arms, and every pair of their selected routes avoids one another.
- [`LeanTrominoes/PeriodicOrthocrossingPlanarSATNoncarrierSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarSATNoncarrierSeparation.lean)
  combines the macrocell rectangle bounds with all center-uniqueness and
  center-disjointness theorems.  Selected routes from any two distinct
  non-carrier components therefore avoid one another; the only possible
  shared center is handled by the certified different-arm routed-variable
  theorem.
- [`LeanTrominoes/PeriodicOrthocrossingPlanarSATCarrierSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarSATCarrierSeparation.lean)
  isolates the remaining component-level geometry to pairs involving at
  least one straight carrier lens.  A proof of that precise residual
  certificate now combines automatically with non-carrier separation and
  lifts through clause metadata to the globally indexed route family.
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
- [`LeanTrominoes/PeriodicOrthocrossingCarrierLensGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierLensGeometry.lean)
  certifies the equality lens for every retained complete-carrier link.
  Uniform terminal/boundary coordinates put all axial ports in one residue
  class modulo ten; strict sorted order, including a canonical-crossing
  uniqueness proof, therefore gives at least ten cells of clearance.  Each
  link consequently has its exact formula and endpoint positions together
  with a complete finite orthogonality and continuous-planarity certificate.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierCoordinateOrder.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierCoordinateOrder.lean)
  proves that distinct nodes on one complete carrier cannot share an axis
  coordinate, upgrades each weakly sorted carrier list to strict pairwise
  order, and shows that every retained adjacent pair advances by at least
  the full ten-cell port spacing.  It also orients any two distinct retained
  links on one carrier into one of the two nonoverlapping axial orders.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierAxisInterface.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierAxisInterface.lean)
  proves that every node on one occurrence has the same horizontal/vertical
  tag and reduces retained-link directions and ports to their forward and
  backward compass directions.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierBoundingBox.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierBoundingBox.lean)
  simplifies every retained link's generic corridor to an explicit narrow
  rectangle between its two physical nodes.  The bound survives final
  planar-SAT renaming, and separated rectangles immediately give complete
  contact-free separation of all selected route pairs.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierSupportGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierSupportGeometry.lean)
  identifies a carrier's fixed normal coordinate with its translated source
  segment line, scaled by twenty and shifted by the port coordinate six.
  Hence parallel retained links on different source rows or columns have
  strictly separated physical rectangles.  It also bounds every carrier
  node between the two inward-facing endpoint ports of its source segment;
  thus source intervals with disjoint continuous interiors yield strictly
  separated lens rectangles even when the source segments share an endpoint.
- [`LeanTrominoes/PeriodicOrthocrossingContinuousParallel.lean`](LeanTrominoes/PeriodicOrthocrossingContinuousParallel.lean)
  strengthens parallel private-lane uniqueness from integer contacts to
  continuous open-interval overlap.  Horizontal endpoints are even, so
  horizontal overlap contains an integer witness.  For vertical segments,
  a normalized lane-owner classification additionally handles the unit
  fanout steps and periodic boundary steps that have no integer interior.
- [`LeanTrominoes/PeriodicOrthocrossingParallelCarrierSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingParallelCarrierSeparation.lean)
  combines continuous source separation with the physical corridor bounds.
  Consequently all parallel retained links on different occurrence keys
  have strictly separated lens rectangles, including collinear links in
  either orientation.
- [`LeanTrominoes/PeriodicOrthocrossingSameCarrierSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingSameCarrierSeparation.lean)
  turns strict carrier order into route separation for every pair of
  distinct links on one carrier.  The later lens lies inside the earlier
  lens's terminal boundary; adjacent links may share the boundary port, but
  both drawings certify that contact as an advertised route endpoint.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierCarrierSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierCarrierSeparation.lean)
  combines same-carrier order with different-key continuous parallel
  separation.  Thus every pair of distinct nonperpendicular carrier lenses
  has separated selected routes, isolating perpendicular carriers as the
  exact remaining carrier-pair obligation.
- [`LeanTrominoes/PeriodicOrthocrossingPerpendicularCarrierGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingPerpendicularCarrierGeometry.lean)
  reconstructs source geometry from any putative overlap of a horizontal and
  a vertical retained lens.  The links have different occurrence keys, their
  narrow physical rectangles force the translated source intervals to cross
  properly, and the resulting exact indexed-segment/translation record is
  proved to belong to the retained crossing halo.
- [`LeanTrominoes/PeriodicOrthocrossingBendCornerGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingBendCornerGeometry.lean)
  adapts the fixed corner-equality template to one syntactic route bend.
  Genuine incoming and outgoing segments determine their compass ports; a
  no-immediate-reversal hypothesis makes those ports distinct.  The adapter
  then exposes the bend link's exact positioned formula, both real
  carrier-node endpoints, the transported complete local certificate, and
  the internal bounds and endpoint-only contacts at both physical ports.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierTerminalPortGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierTerminalPortGeometry.lean)
  identifies the endpoint interface computed by every retained carrier lens.
  Complete-carrier order makes a first terminal the lower segment endpoint
  and a second terminal the upper endpoint, which determines the exact
  compass port; the reconstructed lens macrocell origin is proved to be the
  terminal's scaled drawing cell.  Four corollaries identify these data with
  either physical port of an incident route bend.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierCrossoverPortGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierCrossoverPortGeometry.lean)
  uses strict carrier order to show that retained links leave crossovers
  only through right or bottom boundaries and enter only through left or
  top boundaries.  It then identifies both lens ports and reconstructed
  macrocell origins with the exact incident crossover interfaces.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierCrossoverSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierCrossoverSeparation.lean)
  applies the external-lens/internal-crossover boundary separator at that
  exact interface, proving that every genuine carrier route avoids every
  genuine route of an incident crossover drawing.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierTerminalComponentGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierTerminalComponentGeometry.lean)
  identifies each selected occurrence terminal's carrier port with its
  routed-variable or routed-clause fanout arm, and its scaled drawing point
  with that component's macrocell origin.  Four interface theorems match
  these data to either endpoint of an incident retained carrier lens.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierTerminalComponentSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierTerminalComponentSeparation.lean)
  plugs those endpoint identities into the external-lens/internal-component
  boundary separator.  Genuine carrier routes therefore avoid genuine
  routed-variable and routed-clause routes whenever they share the selected
  occurrence terminal.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierBendSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierBendSeparation.lean)
  plugs those endpoint identities into the external-lens/internal-corner
  boundary separator.  Every genuine local incidence route of a carrier
  lens therefore avoids every genuine local incidence route of any bend
  corner with which it shares a terminal.
- [`LeanTrominoes/PeriodicOrthocrossingRouteNoImmediateReversalComponents.lean`](LeanTrominoes/PeriodicOrthocrossingRouteNoImmediateReversalComponents.lean)
  proves no-immediate-reversal certificates for source fanouts, all five
  local edge-core shapes, and translated reversed target fanouts.  Their
  endpoint directions are fixed: the source/core join heads north and the
  core/target join heads south.
- [`LeanTrominoes/PeriodicOrthocrossingRouteNoImmediateReversal.lean`](LeanTrominoes/PeriodicOrthocrossingRouteNoImmediateReversal.lean)
  splices those component certificates into a route-wide theorem for every
  edge of a well-formed local degree-three periodic graph.
- [`LeanTrominoes/PeriodicOrthocrossingBendCornerDrawingFamily.lean`](LeanTrominoes/PeriodicOrthocrossingBendCornerDrawingFamily.lean)
  lifts route orthogonality and the new no-reversal theorem through
  `routeBendsAux`.  Every deduplicated bend link now has a fixed corner
  drawing with exact incoming and outgoing carrier positions, orthogonal
  routes, and continuous finite planarity.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierNormalizationDegree.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierNormalizationDegree.lean)
  performs that periodic quotient for all complete-carrier equality links.
  Distinct normalized links at a fixed terminal inject into one direct-link
  class plus the segment's crossing-bearing translations.  The direct class
  is canonical across neighboring copies, while at most two translations can
  contain canonical crossings.  Hence every terminal prototype has normalized
  link-endpoint degree at most three and occurs at most six times in the
  deduplicated periodic equality formula.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierTranslationCore.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierTranslationCore.lean)
  defines the common period action on physical crossings, carrier nodes, and
  positioned carrier links upstream of retained-link enumeration, together
  with normalization invariance and the zero action.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierOrbitOwnership.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierOrbitOwnership.lean)
  separates retained split points from periodic carrier-link representatives.
  It enumerates a fixed `5 × 5` orbit window of each canonical crossing; its
  zero-shift ownership rule prevents the outer edge of that finite window from
  being mistaken for an edge of the infinite carrier, while every retained
  boundary normalizes to a listed canonical boundary.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierLinks.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierLinks.lean)
  builds sorted carrier chains through all retained halo crossings and then
  filters them by the zero-shift ownership rule.  The selected physical links
  are duplicate-free, remain on one segment-occurrence key, and their
  equality clauses are satisfied by every carrier assignment.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedFormula.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedFormula.lean)
  replaces only the canonical straight-carrier clauses by their selected
  retained representatives, leaving crossover, bend, routed-clause, and
  routed-variable components unchanged.  It proves the exact componentwise
  satisfaction interface and extends compatible route and atom assignments
  through the retained core.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedSATClauseIndex.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedSATClauseIndex.lean)
  indexes the retained formula by the same five geometric component kinds,
  with carrier validity changed to selected retained-link membership.
  Projecting its metadata recovers the retained clause list exactly, and
  membership in the metadata enumeration is equivalent to valid
  component/local-clause source data.  Every genuine clause lookup therefore
  returns valid local-source data.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATSourceMembership.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATSourceMembership.lean)
  separates retained source validity into physical component membership and
  same-index membership in the component's local clause family.  Their
  conjunction exactly characterizes the retained metadata enumeration and
  yields a concrete global lookup for any such local source witness.
- [`LeanTrominoes/PeriodicOrthocrossingPlanarSATSourceClauseTranslation.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarSATSourceClauseTranslation.lean)
  proves that source period translation preserves both the ordered
  clause-arity profile and the exact translated literal list of every gadget
  family.  Consequently, valid clause and literal indices select same-index
  counterparts; after periodic normalization and canonical variable gauging,
  every literal offset—and hence every nonempty clause anchor—gains exactly
  the source translation.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierTranslation.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierTranslation.lean)
  defines common period translation for crossing records, boundaries,
  terminals, carrier nodes, and equality links.  Crossing normalization is
  invariant under this action, carrier-node offsets add the common shift, and
  normalized equality links are unchanged.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierRepresentativeTranslation.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierRepresentativeTranslation.lean)
  translates a physical carrier link by the inverse of its owner shift.  The
  result has zero representative shift and the same normalized equality link;
  its selected boundary is exactly the canonical normalized boundary (or its
  selected direct terminal has translation zero).
- [`LeanTrominoes/PeriodicOrthocrossingCarrierTranslationGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierTranslationGeometry.lean)
  proves covariance of refined carrier geometry under a common drawing-period
  translation: positions move by one macro-period vector, while axis, relative
  order, crossover-site identity, and positioned link construction are
  preserved.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierRetentionBounds.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierRetentionBounds.lean)
  bounds every point on a neighboring segment occurrence between drawing
  periods `-2` and `3`.  Its extracted period shift therefore lies in the
  retained `5 × 5` window, and any such physical crossing can be reconstructed
  exactly from its canonical normalization and retained shift.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedBoundaryGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedBoundaryGeometry.lean)
  lifts canonical crossing soundness across the period action.  Every retained
  boundary names a listed indexed segment and an interior point of its exact
  physical occurrence, and both properties persist under any further common
  translation.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierCorrectionEndpoints.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierCorrectionEndpoints.lean)
  proves that representative correction keeps both endpoints of every raw
  retained carrier link inside the retained enumeration.  The canonical owner
  fixes a neighboring occurrence key; the other boundary then satisfies the
  retained-shift bound, while terminal endpoints remain explicitly listed.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierOrder.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierOrder.lean)
  transfers strict coordinate order to the retained carrier chains.  It
  preserves crossing orientation, proves uniqueness of retained crossing
  records and boundary coordinates, places every retained boundary strictly
  between its occurrence terminals, and concludes that each sorted retained
  chain is pairwise strictly ordered.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierGeometry.lean)
  transfers common-axis geometry to retained carrier nodes: every node lies
  on its supporting occurrence, its axis tag is exact, and nodes with one key
  share a refined support line whose axial coordinates are all `1 mod 10`.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierLensGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierLensGeometry.lean)
  turns strict retained order and the common axial residue into forward
  clearance for every adjacent pair.  Raw links and their selected zero-shift
  representatives therefore instantiate the certified equality-lens drawing,
  with exact formula, endpoint positions, orthogonality, and finite planarity.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierInterfaces.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierInterfaces.lean)
  identifies every selected-lens endpoint orientation.  A lens beginning at a
  crossover boundary leaves only through its right or bottom port, one ending
  there enters only through its left or top port, and a terminal occurs at the
  lower or upper end dictated by its segment endpoint.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierPortGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierPortGeometry.lean)
  upgrades those orientations to exact component interfaces.  Every selected
  lens exposes the expected compass port at a crossover or segment terminal,
  and reconstructs the same macrocell origin as that adjacent component.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierWireIncidenceDrawings.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierWireIncidenceDrawings.lean)
  embeds each selected retained lens into the final planar-SAT variable type.
  Its indexed formula and full drawing validity are certified together with
  external-side and endpoint-only-contact facts at both carrier boundaries.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierCrossoverSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierCrossoverSeparation.lean)
  matches those external lens boundaries with the internal boundaries of an
  incident crossover.  The generic boundary separator proves that every
  genuine selected-lens route avoids every genuine crossover route.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierTerminalComponentGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierTerminalComponentGeometry.lean)
  matches either endpoint of a selected retained lens with the exact fanout
  arm and macrocell origin of an incident routed-variable target or
  routed-clause source component.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierTerminalComponentSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierTerminalComponentSeparation.lean)
  applies the common-boundary separator at those interfaces.  Genuine routes
  of a selected retained lens avoid genuine routes of both incident
  routed-variable arms and routed-clause sources.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierBendComponentGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierBendComponentGeometry.lean)
  identifies the port and macrocell origin shared by a selected retained lens
  and either the incoming or outgoing terminal of an incident route-bend
  corner.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierBendSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierBendSeparation.lean)
  handles all four shared incoming/outgoing and first/second endpoint cases.
  Genuine selected-lens routes avoid genuine routes of every incident
  certified bend-corner drawing.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierBoundingBox.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierBoundingBox.lean)
  fixes each selected link's forward axis direction and explicit narrow
  rectangle.  Its renamed route points stay inside that rectangle, so
  separated rectangles give strict selected-lens route separation.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierMacrocellSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierMacrocellSeparation.lean)
  separates a selected carrier route from any non-carrier route in a
  disjoint standard macrocell.  Conversely, rectangle overlap forces that
  macrocell onto the carrier's exact source row or column and into its axial
  interval—equivalently, its center lies on the exact translated supporting
  segment—supplying the common proximity interface for the remaining
  carrier-to-component cases.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierTerminalProximity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierTerminalProximity.lean)
  proves the reusable terminal half of that proximity argument.  A source
  terminal is a strict retained-chain extreme at local axial coordinate
  `11` or `1`; hence a selected lens on the same occurrence can overlap the
  terminal macrocell only when the terminal is one of its endpoints.
- [`LeanTrominoes/PeriodicOrthocrossingDrawingVertexAvoidance.lean`](LeanTrominoes/PeriodicOrthocrossingDrawingVertexAvoidance.lean)
  proves that the constructed orthogonal drawing meets every lifted graph
  vertex only at route endpoints: no translated indexed segment contains a
  lifted vertex in its relative interior.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierTerminalComponentProximity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierTerminalComponentProximity.lean)
  uses vertex avoidance to classify every retained-carrier overlap with a
  routed variable or clause macrocell.  The carrier must end at an external
  route terminal, which is lifted back to a metadata-rich CNF occurrence at
  the exact variable or clause site.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierTerminalComponentAllSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierTerminalComponentAllSeparation.lean)
  observes that each active duplicator arm lies inside all three external
  fanout boundaries.  Combining this finite gadget fact with terminal
  proximity and disjoint-macrocell separation proves route avoidance for
  every selected carrier/routed-variable and carrier/routed-clause pair.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATLocalIncidenceDrawing.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATLocalIncidenceDrawing.lean)
  selects the certified local drawing named by each retained metadata entry.
  The assembled retained formula has exact incidence endpoints, while each
  selected component retains orthogonality, route simplicity, and continuous
  local planarity.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATComponentSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATComponentSeparation.lean)
  packages carrier–carrier, carrier–crossover, carrier–bend,
  carrier–variable, and carrier–clause separation at the metadata level, then
  combines them with the existing non-carrier macrocell theorem to separate
  every pair of distinct retained components.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATClauseKeys.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATClauseKeys.lean)
  proves that the retained five-family metadata has duplicate-free
  component/local-clause keys.  Equal keys returned by global lookups
  therefore identify the same retained formula clause index.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGlobalRouteSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGlobalRouteSeparation.lean)
  lifts component separation and key injectivity to the assembled incidence
  drawing.  Every retained route is simple, and every two distinct globally
  indexed incidences satisfy complete continuous route separation.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATFinitePlanarity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATFinitePlanarity.lean)
  first reduces complete finite planarity of the retained drawing exactly to
  its two remaining vertex conditions.  Endpoint coverage discharges
  vertex/interior avoidance, while used-variable injectivity, global
  clause-position injectivity, and cross-part separation prove that all graph
  vertex positions are duplicate-free.  The module then assembles the
  complete finite `IsPlanar` certificate.
- [`LeanTrominoes/EmbeddedCNFIncidenceDrawingVertexCoverage.lean`](LeanTrominoes/EmbeddedCNFIncidenceDrawingVertexCoverage.lean)
  proves a reusable endpoint-coverage principle: exact incidence endpoints
  cover every vertex of a formula with no empty clauses, after which route
  simplicity and pairwise route separation imply vertex/interior avoidance.
- [`LeanTrominoes/PeriodicOrthocrossingPlanarSATVertexPositionGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarSATVertexPositionGeometry.lean)
  proves uniqueness of the `20 × 20` macrocell representation and classifies
  the four genuine carrier-port coordinates.  Carrier ports, crossover
  internals, and routed-variable centers are pairwise separated locally.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATVariableVertices.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATVariableVertices.lean)
  classifies every variable used by the retained formula as a retained
  carrier node, routed-variable center, or internal variable of a retained
  halo crossing.  The proof first classifies each local gadget and then
  lifts the result through retained clause metadata.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierPositionInjectivity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierPositionInjectivity.lean)
  proves that retained carrier nodes have distinct refined positions.
  Equal local ports make their supporting segments overlap in one continuous
  lane; lane uniqueness and strict carrier order then identify the nodes.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATVariablePositionInjectivity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATVariablePositionInjectivity.lean)
  proves position injectivity for every variable used by the retained SAT
  drawing.  Macrocell uniqueness handles the carrier, routed-variable, and
  internal-crossover families uniformly and separates the three local
  coordinate tables.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATNoncarrierVariableClausePositions.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATNoncarrierVariableClausePositions.lean)
  proves that retained variable positions avoid every non-carrier clause
  position.  Fixed local-coordinate tables settle the direct cases; drawing
  center separation handles the few coordinates reused by different
  macrocell kinds.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATLocalVertexDistinctness.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATLocalVertexDistinctness.lean)
  extracts local vertex distinctness from each component's planarity
  certificate: clause positions are locally injective, local variables
  avoid local clauses, and equal clause positions in one component identify
  the same local clause index.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATNoncarrierClausePositions.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATNoncarrierClausePositions.lean)
  proves that nonempty retained clauses in non-carrier components identify
  their geometric component by position.  Standard macrocell bounds identify
  the center; center uniqueness and the fixed routed-variable arm coordinates
  identify the component at that center.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATCarrierClausePositions.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATCarrierClausePositions.lean)
  proves that equal clause positions in retained straight-carrier lenses
  identify the same lens.  Rectangle separation handles every nonadjacent
  pair; consecutive lenses remain distinct because their clauses lie strictly
  inside the eight-cell-clearance spans on opposite sides of the shared port.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATCarrierNoncarrierClausePositions.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATCarrierNoncarrierClausePositions.lean)
  separates carrier-lens clause positions from all non-carrier component
  clauses.  Disjoint macrocells use rectangle bounds; an overlapping
  component is incident, so complementary carrier-boundary certificates force
  any common point to be a variable port excluded by local planarity.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGlobalClausePositions.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGlobalClausePositions.lean)
  combines the three component pairings to prove global clause-position
  injectivity.  Equal nonempty clause positions identify the component, its
  local clause index, and finally the unique retained global clause index.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGlobalVariableClausePositions.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGlobalVariableClausePositions.lean)
  proves that no retained variable position is a retained clause position.
  Non-carrier components use fixed local coordinates; carrier components use
  rectangle separation, certified shared-port boundaries, and the clearance
  between consecutive equality lenses.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATPeriodicization.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATPeriodicization.lean)
  transports the planar retained finite block through periodic variable
  normalization, opaque wrapping, clause-anchor normalization, and
  clause-orbit deduplication.  The resulting periodic incidence drawing has
  a graph-level exact-endpoint certificate; quotient planarity is kept as the
  next geometric obligation.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariablePositions.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariablePositions.lean)
  gives each retained periodic routed-SAT protovariable a canonical
  translation-zero finite lift.  Every variable surviving wrapping and
  clause-orbit deduplication has a valid lift, so finite geometric
  injectivity proves that the variable-position prefix of the final periodic
  incidence drawing is duplicate-free.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATVariableGauge.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATVariableGauge.lean)
  applies the canonical per-variable period gauge before clause-anchor
  normalization.  The transported retained routes keep their exact physical
  endpoints, the final graph-level route certificate is reassembled, and
  the gauged, wrapped, normalized, deduplicated source remains
  equisatisfiable with the retained periodic formula.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions.lean)
  proves the variable geometry of that quotient.  Strictly interior
  macrocell coordinates put every gauged variable in the open fundamental
  square; a neighboring finite lift of each terminal lets retained finite
  injectivity prove that the final variable-position prefix is
  duplicate-free.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedClausePositions.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedClausePositions.lean)
  identifies each retained clause's canonical quotient position with the
  coordinatewise residue of its finite drawing position.  Carrier and
  macrocell gadgets keep the clause and its first literal in the same period
  cell; strict local-coordinate bounds then put every deduplicated clause
  position in the open fundamental square.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierClauseOrbits.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierClauseOrbits.lean)
  classifies the clause offsets in crossover, bend, routed-clause, and
  routed-variable gadgets.  Equal fundamental-domain residues identify the
  same non-carrier clause orbit after periodic normalization, opaque wrapping,
  and the canonical variable gauge.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierClauseSignatures.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierClauseSignatures.lean)
  extracts a rigid modulo-ten signature from every retained carrier clause.
  Equal residues recover its axis, implication index, and first carrier-node
  position modulo the drawing period; exact first nodes uniquely determine
  their raw retained links.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierClauseOrbits.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierClauseOrbits.lean)
  proves the corresponding carrier-clause orbit theorem.  A translation
  covariance lemma for raw retained chains moves terminal-start links to
  translation zero, where adjacency identifies the complete normalized link;
  equal residues therefore yield the same gauged periodic clause.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedClauseOrbits.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedClauseOrbits.lean)
  separates carrier and non-carrier clause orbits using their exact offsets
  in a 20-cell macrocell.  Combining this obstruction with both same-kind
  classifications proves that an equal clause-position residue determines
  one gauged normalized clause across all retained gadget families.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedClausePositionInjectivity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedClausePositionInjectivity.lean)
  transfers the global orbit classification through first-representative
  clause deduplication.  Thus the final retained stored clause positions
  are duplicate-free.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedVertexPositions.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedVertexPositions.lean)
  rules out every variable–clause collision in the periodic quotient,
  including translated crossover–bend contacts.  Combining this separation
  with variable and clause injectivity proves that the complete final
  incidence-vertex list is duplicate-free and lies in the open fundamental
  square.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedDrawingCompatibility.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedDrawingCompatibility.lean)
  packages the final vertex bounds with the transported exact route
  endpoints.  The resulting gauged, anchor-normalized, clause-deduplicated
  incidence drawing is compatible with its periodic incidence graph.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierRouteBounds.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierRouteBounds.lean)
  proves that clause-anchor normalization reduces every route point in a
  crossover, bend, routed-clause, or routed-variable component to its
  coordinatewise period residue.  All normalized non-carrier route points
  therefore lie in the half-open canonical square.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierRouteBounds.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierRouteBounds.lean)
  proves that consecutive retained carrier nodes are separated by less than
  one physical period along their common axis.  Together with the equality
  lens's fixed transverse width, this places every clause-anchor-normalized
  carrier route point in the open neighboring-period square `(-P, 2P)²`.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRouteBounds.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRouteBounds.lean)
  combines the carrier and non-carrier bounds and transports them through
  metadata lookup, clause-anchor normalization, and first-representative
  clause deduplication.  The final gauged periodic incidence drawing thus
  satisfies `RoutePointsInExpandedSquare`.
- [`LeanTrominoes/PositionedPeriodicCNFRouteOccurrenceNormalization.lean`](LeanTrominoes/PositionedPeriodicCNFRouteOccurrenceNormalization.lean)
  proves that lifting an anchor-normalized route at lattice shift `s` is
  exactly the original physical route lifted at `s - anchor`.  It also
  exposes the representative route selected by anchor-zero clause
  deduplication, providing the quotient-to-finite bridge for periodic
  planarity.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRouteOccurrences.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRouteOccurrences.lean)
  specializes that bridge to the final retained drawing.  Every translated
  final incidence route now carries a genuine incidence of the certified
  finite retained drawing whose physical route is equal after the exact
  anchor-adjusted lattice translation.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedSegmentOccurrences.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedSegmentOccurrences.lean)
  refines the quotient-to-finite bridge to indexed segment occurrences,
  preserving the final and retained-finite flat incidence indices together
  with the within-route segment index, and proving exact equality of the
  translated final and physical segments.  The two incidence indexings
  determine each other, so its anchor-adjusted finite occurrence key is equal
  exactly when the original periodic segment-occurrence key is equal.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointOccurrences.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointOccurrences.lean)
  performs the analogous transfer for every listed route point.  The
  same-indexed physical point has the exact translated coordinate and route
  length, so outer-endpoint status is preserved; a fixed first-segment
  witness proves that the anchor-adjusted physical point key is equal exactly
  when the final periodic route-point occurrence key is equal.  This is the
  quotient interface needed to rule out hidden bend-to-bend contacts before
  ribbon thickening.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointCommonShiftRepresentatives.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointCommonShiftRepresentatives.lean)
  isolates a same-shift finite representative for an indexed final route
  point.  Two distinct finite point indices represented at one common shift
  can coincide only at outer endpoints, by retained route simplicity and the
  finite endpoint-contact certificate.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierSegmentBounds.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierSegmentBounds.lean)
  transfers the noncarrier route-point residue theorem through that
  occurrence bridge.  Every final segment represented by crossover, bend,
  routed-clause, or routed-variable metadata has both endpoints in the
  half-open fundamental square.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedContactTranslationBounds.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedContactTranslationBounds.lean)
  combines those half-open bounds with the all-route halo bound.  Any
  continuous contact involving at least one noncarrier segment is reduced to
  the nine neighboring relative translations, while every contact is reduced
  to the doubled `5 × 5` neighboring block.  Thus only carrier--carrier
  contacts can require the full 25-shift analysis.
- [`LeanTrominoes/PeriodicOrthocrossingPlanarSATSourceTranslation.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarSATSourceTranslation.lean)
  defines one physical period-translation action for all five planar-SAT
  clause-source families, including bends, routed vertex sites, external
  nodes, equality links, and source components.  It proves exact translation
  laws for drawing-grid centers and refined macrocell origins, providing the
  common language needed to reindex finite representatives.
- [`LeanTrominoes/PeriodicOrthocrossingPlanarSATSourceRouteTranslation.lean`](LeanTrominoes/PeriodicOrthocrossingPlanarSATSourceRouteTranslation.lean)
  proves the action is geometric: at unchanged local clause and literal
  indices, every crossover, carrier lens, bend corner, routed-clause ray, and
  routed-variable arm is exactly the pointwise refined-period translate of
  its original local route.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedCommonShiftRepresentatives.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedCommonShiftRepresentatives.lean)
  isolates the remaining orbit interface.  If two final occurrences are
  reindexed as distinct genuine retained-drawing segments at one common
  physical shift, finite retained planarity immediately transfers their
  continuous separation back to the periodic quotient.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedReindexedRepresentatives.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedReindexedRepresentatives.lean)
  turns a component-equivalent retained-metadata lookup at unchanged local
  clause and literal indices into that common-shift representative
  automatically.  It preserves the within-route segment index and balances
  source translation against the external occurrence shift, while permitting
  enumeration-only source fields to change at the retained-window boundary.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointReindexedRepresentatives.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointReindexedRepresentatives.lean)
  lifts the same source reindexing to whole routes.  It preserves the selected
  point index, route length, endpoint status, and lifted coordinate while
  moving the point representative to the adjusted common physical shift.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedAutomaticReindexing.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedAutomaticReindexing.lean)
  discharges that metadata-entry obligation from retained membership of
  either the literal translated source or any source with the same geometric
  component and local clause index.  This covers routed-variable arms whose
  global per-site enumeration index changes near a retained-window boundary,
  and produces the finite common-shift representative used by planarity
  transfer.  Reindexing also preserves the anchor-normalized gauged clause
  exactly and adds its physical shift to the pre-normalization clause anchor,
  providing the two invariants needed to preserve occurrence identity.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedAnchorReindexing.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedAnchorReindexing.lean)
  chooses source translations by their desired canonically gauged clause
  anchors.  Reindexing two final occurrences to anchors equal to their
  relative external shift and zero places both finite representatives at the
  second occurrence's external shift, reducing the remaining orbit proof to
  family-by-family retained component membership.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedSourceOrbitMembership.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedSourceOrbitMembership.lean)
  packages that family-by-family membership interface.  Crossovers,
  carriers, bends, and routed clauses reuse their exact translated sources;
  routed-variable arms may change only their finite per-site presentation
  index while preserving the translated component and local clause index.
  It also proves neighboring-window closure for route occurrences, bends,
  routed sites, and crossover records whose two translated carriers remain
  among the nine neighboring occurrences.  For routed-variable sources, the
  degree-three bound guarantees that the translated terminal remains among
  the target site's three active arms, yielding a retained translated source
  even when sorting assigns that arm a different local presentation index.
  A uniform orbit condition then packages the five family-specific premises
  and returns a retained component-equivalent translated source.  Final
  segment witnesses consume this condition directly to align one occurrence
  with another at a common finite-drawing shift.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedSourceOrbitNecessity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedSourceOrbitNecessity.lean)
  proves the converse for exact or component-equivalent source translates.
  Membership of a translated crossover, carrier, bend, routed-clause site, or
  routed-variable arm recovers the corresponding orbit condition; for
  variable arms, equality of the translated first terminal recovers the
  neighboring route-occurrence coordinate even if the finite arm index
  changes.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedReindexingInjectivity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedReindexingInjectivity.lean)
  proves that source reindexing cannot collapse distinct periodic segment
  occurrences.  Equality of the target finite incidence and within-route
  segment index recovers equality of the normalized final clause, literal
  index, and external shift, hence equality of the original occurrence keys.
  The resulting transfer theorem turns any first-source orbit condition into
  continuous separation by finite retained planarity.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointReindexingInjectivity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointReindexingInjectivity.lean)
  proves the corresponding identity theorem for route points.  The
  first-segment witness recovers the original route and external shift, while
  the retained point index completes the occurrence key; consequently any
  first-source orbit condition transfers finite endpoint-only contact to the
  original periodic pair.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointLocalRouteAvoidance.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointLocalRouteAvoidance.lean)
  transfers the endpoint-contact clause of a component-level
  `RoutesAvoidEachOther` certificate through the final route-point
  occurrence witnesses.  The two source components may be translated
  independently provided their remaining physical shifts agree, so the
  component geometry already used for continuous planarity can be reused
  without weakening its stronger listed-point conclusion.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointCarrierNoncarrierReduction.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointCarrierNoncarrierReduction.lean)
  develops the pointwise carrier--noncarrier reduction.  It cancels final
  quotient shifts, bounds the carrier point in its anchor-normalized raw
  lens rectangle and the noncarrier point in its translated macrocell, and
  turns equality into the same corridor--macrocell overlap used by the
  continuous proof.  A common-shift bridge then transfers the resulting raw
  local-route certificate, including endpoint-only listed-point contact.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedComponentAlignmentSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedComponentAlignmentSeparation.lean)
  packages the common aligned-component case.  When translating the first
  source by the physical-shift difference identifies the second retained
  component, orbit necessity and reindexing injectivity immediately transfer
  both finite continuous separation and endpoint-only route-point contact to
  the periodic pair.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointCarrierContacts.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointCarrierContacts.lean)
  proves endpoint-only contact for every pair of final carrier route-point
  occurrences.  It reuses the continuous carrier classification into
  perpendicular axes, distinct parallel physical keys, and one physical
  carrier; the last case separates distinct raw links and reindexes an
  exactly aligned link.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointNoncarrierContacts.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointNoncarrierContacts.lean)
  proves endpoint-only contact for every pair of final noncarrier
  route-point occurrences.  Unequal translated macrocell centers give
  strict local-route avoidance; equal centers give component reindexing
  except for distinct routed-variable arms, whose certified local routes
  already avoid one another.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointCarrierNoncarrierContacts.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointCarrierNoncarrierContacts.lean)
  proves endpoint-only contact between final carrier and noncarrier route
  points.  The bend, routed-clause, and routed-variable cases balance one
  source occurrence; the crossover case balances its two coupled segment
  occurrences.  In every case, point equality supplies the same
  supporting-segment proximity certificate as continuous contact.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointContacts.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointContacts.lean)
  assembles carrier--carrier, carrier--noncarrier, and
  noncarrier--noncarrier cases.  The complete final periodic incidence
  drawing consequently satisfies `RoutePointsMeetOnlyAtEndpoints`, ruling
  out hidden bend crossings before ribbon thickening.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRibbonReady.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRibbonReady.lean)
  combines continuous planarity with endpoint-only route-point contacts.
  Thus the complete final gauged periodic incidence drawing satisfies
  `IsRibbonReady`, the geometric interface consumed by ribbon thickening.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierRepresentativeMembership.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierRepresentativeMembership.lean)
  proves the semantic ownership bridge for retained carrier wires.  Every
  raw equality link on a neighboring physical carrier translates to a
  selected zero-owner representative, so the finite selected formula can
  recover all equalities needed along neighboring periodic carrier chains.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierPeriodicSoundness.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierPeriodicSoundness.lean)
  performs that recovery under a satisfying periodic assignment.  Evaluation
  of translated physical carrier nodes is proved covariant with the
  finite-block translate, and each selected representative equality is
  transported back to its original raw neighboring link.  Canonical
  crossover laws are likewise transported to every retained physical
  crossover; together these two cases make every retained carrier chain
  constant and equate the start and finish terminals of every neighboring
  segment occurrence.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarRoutePeriodicSoundness.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarRoutePeriodicSoundness.lean)
  extracts the unchanged bend equalities from the retained periodic formula
  at every block translate.  Alternating those equalities with retained
  segment propagation proves that the first and last terminals of every
  neighboring constructed incidence route have one value.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedVariableSoundness.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedVariableSoundness.lean)
  specializes complete-route propagation to every metadata-rich CNF
  incidence occurrence.  Under the occurrence-three premise, the unchanged
  variable duplicator then equates each routed clause terminal with the
  corresponding central periodic atom occurrence.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedPeriodicSoundness.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedPeriodicSoundness.lean)
  reconstructs every original periodic source clause from the retained routed
  clauses and recovered central atom values.  It also proves retained
  completeness using the canonical periodic route assignment, establishing
  exact satisfiability preservation for well-formed local degree-three
  incidence graphs with at most three occurrences per source variable.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedFinalCorrectness.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedFinalCorrectness.lean)
  transports that equivalence through variable wrapping, canonical variable
  and clause gauges, and clause-orbit deduplication.  The final positioned
  retained planar formula is therefore satisfiable exactly when the original
  periodic CNF is satisfiable.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierNormalizationDegree.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierNormalizationDegree.lean)
  proves that every retained physical carrier node has at most one selected
  predecessor and successor, then lifts both uniqueness statements through
  periodic normalization.  Consequently every normalized carrier prototype
  is incident to at most two retained equality links and occurs at most four
  times in the deduplicated retained straight-carrier formula.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedNormalizationComponents.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedNormalizationComponents.lean)
  decomposes the retained periodic planar-SAT formula into the unchanged
  crossover, bend, routed-clause, and routed-variable families plus the new
  retained straight-carrier family.  It also proves that global clause
  deduplication can only reduce occurrences relative to separately
  deduplicating these five normalized components.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedNormalizationDegree.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedNormalizationDegree.lean)
  combines the retained carrier degree-four theorem with the existing four
  noncarrier component bounds.  Terminal, crossing-boundary, central-atom,
  and crossover-internal cases all have degree at most eight, and the bound
  transfers through global clause deduplication to the unwrapped retained
  planar-SAT formula.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedDegree.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedDegree.lean)
  proves that gauged wrapping is injective on anchor-normalized clause
  representatives, so it commutes with clause-orbit deduplication.  The final
  canonically gauged positioned formula therefore has exactly the unwrapped
  occurrence list behind the opaque variable wrapper and retains the
  degree-eight bound.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedWidth.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedWidth.lean)
  proves width three for every retained finite component, its periodicized
  formula, and the final wrapped, variable-gauged, anchor-normalized,
  clause-deduplicated positioned source.  Retaining selected carrier links
  changes no arity because they use the same binary equality template.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedNonempty.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedNonempty.lean)
  proves that source-clause nonemptiness is the only extra structural premise
  needed by the retained planarity construction.  Fixed crossover and
  equality components are intrinsically nonempty, while each routed source
  clause has exactly its source arity; the property survives every final
  wrapper, gauge, normalization, and deduplication step.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedTranslatedComponentCenters.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedTranslatedComponentCenters.lean)
  extends macrocell-center uniqueness beyond the finite retained window.
  An arbitrary period translate of an enumerated crossing, route bend,
  routed-clause site, or routed-variable site is identified by its physical
  center against a retained occurrence.  Crossing normalization and
  translation-erased bend geometry avoid any assumption that the translated
  occurrence itself belongs to the bounded halo.  A complete translated
  noncarrier classification then proves that equal macrocell centers force
  exact component alignment, except for distinct routed-variable arms at
  the same translated variable site; cross-family center coincidences are
  excluded without enlarging the retained window.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierPeriodicSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierPeriodicSeparation.lean)
  turns that translated-center classification into continuous periodic
  separation for every pair of retained noncarrier segment occurrences.
  Unequal aligned centers are separated by their planar-SAT macrocells.
  Equal centers either give exact translated component alignment, which
  transfers finite retained planarity, or two routed-variable sources at
  one site; equal duplicator arms reconstruct the same translated active
  link, while distinct arms reuse the finite duplicator-star route
  separation certificate.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierAnchorGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierAnchorGeometry.lean)
  develops the carrier-side anchor geometry needed for the remaining
  periodic pairs.  It identifies a gauged carrier clause's lattice anchor
  with the coordinatewise period quotient of its first carrier position,
  proves that subtracting this anchor puts the first carrier drawing point
  in the fundamental square, and keeps its supporting segment occurrence
  inside the neighboring `3 × 3` window.  The anchor-normalized link is
  consequently retained in the raw carrier window; the selected carrier
  family continues to enforce its separate zero-owner convention.  More
  precisely, the normalized link is selected exactly when the source anchor
  is zero; its representative-owner shift is otherwise the negative anchor.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierOrbitOwnership.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierOrbitOwnership.lean)
  exposes the carrier zero-owner rule through the source-reindexing API.  A
  selected carrier link remains selected after period translation exactly
  when that translation is zero.  Accordingly, a final carrier occurrence
  satisfies the generic retained-orbit condition for a target physical shift
  exactly when it already has that physical shift; nonzero-shift carrier
  pairs must use the direct periodic carrier geometry.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRouteSimplicity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedRouteSimplicity.lean)
  transfers finite retained route simplicity through the occurrence bridge,
  proving that every route stored in the final periodic quotient is simple.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedSameRouteSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedSameRouteSeparation.lean)
  converts that simplicity certificate to the global indexed-segment
  language, excluding continuous overlap and endpoint contact between
  distinct segments of one periodic route occurrence.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedSamePhysicalShiftSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedSamePhysicalShiftSeparation.lean)
  transfers the full finite planarity certificate to any two distinct final
  segment occurrences with the same anchor-adjusted physical shift, proving
  that their continuous interiors remain disjoint in the periodic lift.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedSamePhysicalShiftRoutePointContacts.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATGaugedSamePhysicalShiftRoutePointContacts.lean)
  proves the route-point analogue for a common anchor-adjusted physical
  shift.  Equal lifted coordinates on distinct final point occurrences force
  both points to be outer route endpoints, using finite route nondegeneracy,
  `Nodup`, and the retained drawing's endpoint-only contact certificate.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierBendProximity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierBendProximity.lean)
  classifies neighboring segment terminals as internal bend terminals or
  external graph endpoints and proves their exact lifted drawing points.
  Continuous lane uniqueness and the reserved port row then show that a
  bend macrocell can overlap a selected carrier only at a genuinely incident
  terminal.  Together with rectangle separation, this proves route avoidance
  for every selected carrier–bend pair.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierCrossoverProximity.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierCrossoverProximity.lean)
  proves the matched-carrier half of crossover proximity.  If a selected
  horizontal or vertical link uses the corresponding source occurrence of a
  retained crossing, overlap with that crossing's macrocell forces one link
  endpoint to be one of the crossing's two carrier ports.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierCrossoverGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierCrossoverGeometry.lean)
  uses continuous lane uniqueness to show that any crossover macrocell
  overlapping a selected horizontal or vertical lens lies on that lens's
  source occurrence.  The matched-carrier theorem then forces genuine
  endpoint incidence, completing route avoidance for every selected
  carrier–crossover pair.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierPairOrder.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierPairOrder.lean)
  proves common-axis agreement for retained nodes and transfers strict
  consecutive-pair order to the selected family: two distinct links with one
  carrier key have nonoverlapping axial intervals in one of the two orders.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedSameCarrierSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedSameCarrierSeparation.lean)
  separates distinct selected lenses sharing one carrier.  Nonadjacent links
  have strictly separated rectangles; adjacent links use complementary
  boundaries at their common node and permit only advertised endpoint contact.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierSupportGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierSupportGeometry.lean)
  bounds halo-only boundary nodes using strict containment in their translated
  source segments, and reuses the terminal endpoint bound.  Selected links
  therefore remain in their source axial corridors with the exact normal line;
  different normal lines or disjoint source intervals separate their explicit
  lens rectangles.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedParallelCarrierSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedParallelCarrierSeparation.lean)
  combines those corridor bounds with continuous source-interior disjointness.
  Horizontal or vertical selected links on distinct occurrence keys have
  strictly separated lens rectangles, including collinear occurrences.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierCarrierSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierCarrierSeparation.lean)
  combines same-key chain order with different-key parallel separation.
  Every pair of distinct nonperpendicular selected carrier lenses has
  separated genuine routes, leaving exactly the perpendicular case.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPerpendicularCarrierCore.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPerpendicularCarrierCore.lean)
  uses zero-shift ownership to recover a neighboring first source occurrence
  for every selected link.  It also proves that perpendicular selected links
  necessarily have different physical occurrence keys, and that every
  genuine neighboring-halo crossing occurs in the retained 5×5 orbit.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPerpendicularCarrierGeometry.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPerpendicularCarrierGeometry.lean)
  reconstructs the exact horizontal-first retained crossing record forced by
  any overlap of a horizontal and vertical selected lens rectangle.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPerpendicularCarrierSeparation.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPerpendicularCarrierSeparation.lean)
  observes that such an overlap would force the selected horizontal link to
  join the crossover's left and right ports, exactly the internal pair omitted
  from every carrier chain.  Thus perpendicular lens rectangles are strictly
  separated; together with the parallel and same-carrier cases, all genuine
  routes of distinct selected carrier lenses avoid one another.
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
  polar-angle sort and keeps radially ordered collinear ties in adjacent
  slots.  Every local
  width-three, occurrence-three source fits the eight Figure 7 compass slots;
  the resulting fixed implication rings have degree three and remain
  satisfiable exactly when the planarized formula is.
- [`LeanTrominoes/PeriodicCNFPlanarEightOccurrenceSplitPositioned.lean`](LeanTrominoes/PeriodicCNFPlanarEightOccurrenceSplitPositioned.lean)
  places those fixed rings in uniform `24 × 24` refinement macrocells using
  the verified Figure 7 copy and implication-clause coordinates.  Erasing
  positions recovers exactly the semantic fixed-eight split, and the refined
  placement retains a positive drawing period.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitLocalDistinctness.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitLocalDistinctness.lean)
  proves that collision-free compass assignment makes every copied source
  clause atom-distinct and that every binary clause of the nine-vertex
  separator ring has distinct endpoints.  The positioned fixed-eight output
  therefore satisfies the local distinctness hypothesis needed by every
  Figure 9 drawing instance.
- [`LeanTrominoes/OccurrenceSplitRingCycleDrawing.lean`](LeanTrominoes/OccurrenceSplitRingCycleDrawing.lean)
  extracts the nine implication clauses as an independently indexed local
  drawing.  Its eighteen routes have exhaustively verified endpoints,
  orthogonality, and continuous planarity, and its erasure is definitionally
  the semantic fixed-eight cycle for any renamed source atom.  A general
  translation-invariance theorem for embedded CNF drawings then places this
  complete certificate at every input-dependent ring macrocell.
- [`LeanTrominoes/OccurrenceSplitRingSpokeCycleSeparation.lean`](LeanTrominoes/OccurrenceSplitRingSpokeCycleSeparation.lean)
  exposes the mixed part of the complete Figure 7 certificate: every old
  incidence spoke continuously avoids every implication route, with only
  advertised endpoint contacts permitted.  Positive scaling and a common
  translation preserve this predicate, matching the geometry used by the
  retained source-to-cycle splice.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitSpokeCycleSeparation.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitSpokeCycleSeparation.lean)
  positions that mixed certificate at an arbitrary source atom and periodic
  literal translate.  The occurrence spoke and its translated implication
  ring receive exactly the same macrocell offset; positive refinement
  preserves their endpoint-only continuous avoidance and the fact that any
  contact occurs at the spoke's terminal ring vertex.
- [`LeanTrominoes/OrthogonalPolylineTailEndpointContactSeparation.lean`](LeanTrominoes/OrthogonalPolylineTailEndpointContactSeparation.lean)
  packages that asymmetric contact condition and proves the corresponding
  composition rule: a strictly separated prefix can be joined to such a
  tail-contacting final piece without losing ordinary route separation.  It
  also handles the two-sided splice used by unit elimination: local prefixes
  may meet only at their clause-side heads, inherited suffixes may meet only
  at their variable-side tails, and strictly separated cross pairs compose
  to complete endpoint-only route separation.  Ordinary route avoidance can
  be upgraded to either head-only or tail-only contact by ruling out the
  other three endpoint pairings.  Symmetrically to the existing `dropLast`
  results, deleting the heads of two simple separated routes preserves
  avoidance and makes every surviving contact tail-only.  Tail-only contact
  is also preserved by injective point maps, in particular by the common
  positive scaling and translation used to position inherited Figure 9
  suffixes.
- [`LeanTrominoes/OccurrenceSplitRingOccurrenceOrder.lean`](LeanTrominoes/OccurrenceSplitRingOccurrenceOrder.lean)
  filters the local implication incidences at each ring vertex in syntactic
  order.  Every real port has exactly two cycle incidences, the separator
  remains degree two, and finite computation certifies that a port's source
  spoke followed by those two incidences leaves the variable in clockwise
  cardinal order.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitPositionedCycleDrawing.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitPositionedCycleDrawing.lean)
  identifies each positioned atom cycle definitionally with that translated
  template: local compass ports are renamed to the corresponding fixed
  copies, and the refined variable placement agrees exactly with the
  translated local vertices.  The renamed positioned ring now carries the
  full finite validity certificate, and genuine positioned cycle routes
  expose route simplicity, complete pairwise continuous separation, and
  avoidance of every ring-variable and implication-clause vertex directly
  from the template.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitPositionedCycleIndex.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitPositionedCycleIndex.lean)
  carries each flattened cycle clause's source atom and local Figure 7 index
  in a parallel metadata list.  Projecting the metadata recovers the existing
  formula exactly, so global route lookup can select certified local routes
  without arithmetic assumptions about block size.  Its atom/local-clause
  keys are duplicate-free, making the flattened index recoverable from this
  semantic key.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitCyclePlanarity.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitCyclePlanarity.lean)
  lifts the positioned Figure 7 certificate through that flattened metadata:
  every genuine cycle-suffix route is simple, and any two distinct routes in
  the same source atom's implication ring satisfy complete continuous
  separation.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitCycleMacrocellSeparation.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitCycleMacrocellSeparation.lean)
  bounds every local implication route inside its inner `12 × 12` Figure 7
  square.  Distinct integer source positions put those squares in strictly
  separated factor-36 macrocells; combining this geometry with the same-ring
  certificate proves complete pairwise continuous separation across the
  flattened cycle suffix whenever occurring source variables have injective
  positions.  The same argument bounds every ring variable in its inner
  square, bounds every genuine implication-clause vertex there as well, and
  proves that all such graph vertices avoid every flattened cycle-route
  interior, using local Figure 7 planarity for their own ring and macrocell
  separation for all other rings.
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
  planarity.  Exact formula equalities identify all four templates with the
  actual positioned semantic replacement, and exhaustive certificates cover
  every polarity pattern of the present source literals; unit elimination
  remains a separate local replacement.
- [`LeanTrominoes/PlanarOneInThreeFigureNineInstantiation.lean`](LeanTrominoes/PlanarOneInThreeFigureNineInstantiation.lean)
  renames every certified arity template to arbitrary present source atoms
  and offset-zero clause-scoped Figure 9 auxiliaries, then translates it into
  the source clause's refinement cell.  Each local formula is definitionally
  its finite `clauseGadget` output, and every instantiated drawing inherits
  the complete geometric certificate; only source atoms that occur in a
  template must be distinct.
- [`LeanTrominoes/PlanarOneInThreePositionedInstantiation.lean`](LeanTrominoes/PlanarOneInThreePositionedInstantiation.lean)
  bijectively swaps those offset-zero auxiliary scopes for the actual
  periodic source clauses, including nonzero literal offsets, without
  changing any route or coordinate.  All four arities embed exactly the real
  positioned `clauseGadget` blocks, and a uniform selector proves validity
  from width three and per-clause atom distinctness.  The selector also
  identifies every scoped auxiliary's physical position with its declared
  local Figure 9 coordinate in the refined source-clause box, and assigns
  every genuine source occurrence its index-selected boundary port.
- [`LeanTrominoes/PlanarOneInThreeNoUnitsDrawing.lean`](LeanTrominoes/PlanarOneInThreeNoUnitsDrawing.lean)
  certifies all four local cases of the subsequent `6 × 6` unit-elimination
  refinement: the empty-clause triangle, unit-clause diamond, and retained
  binary and ternary clauses.  Each exact finite certificate includes
  endpoints, orthogonality, simplicity, vertex avoidance, and continuous
  pairwise planarity, and exact formula equalities identify every template
  with the corresponding positioned unit-elimination output.  Exhaustive
  certificates cover every possible source-literal polarity pattern.
- [`LeanTrominoes/PlanarOneInThreeNoUnitsFigureNineDrawing.lean`](LeanTrominoes/PlanarOneInThreeNoUnitsFigureNineDrawing.lean)
  gives the composed geometric certificates for Figure 9 followed by unit
  elimination.  For all four possible source arities it clips every scaled
  Figure 9 route past the closed `6 × 6` replacement cell and supplies
  coordinated connectors from the new local ports.  Exact finite
  certificates verify endpoints, orthogonality, simplicity, vertex
  avoidance, and continuous planarity for each complete two-stage
  neighborhood, including all auxiliaries created from padding unit clauses.
  Exhaustive polarity-independent certificates and exact formula equalities
  identify every template with the actual composition of the two positioned
  transformations.
- [`LeanTrominoes/PlanarOneInThreeNoUnitsFigureNineInstantiation.lean`](LeanTrominoes/PlanarOneInThreeNoUnitsFigureNineInstantiation.lean)
  instantiates all four composed templates at arbitrary positioned source
  clauses.  It renames both nested levels of scoped variables, accounts for
  the flattened global Figure 9 clause index, translates the checked
  geometry by the combined `72 × 72` refinement, and inherits each complete
  validity certificate (requiring distinctness only among source atoms that
  actually occur).  Exact formula identities cover arbitrary positions,
  presentation indices, polarities, and periodic literal offsets.
- [`LeanTrominoes/PlanarOneInThreeNoUnitsFigureNineSelector.lean`](LeanTrominoes/PlanarOneInThreeNoUnitsFigureNineSelector.lean)
  packages the four composed instances behind a uniform arity selector.
  Width three gives exact agreement with the actual two-stage clause block,
  while per-clause atom distinctness yields its complete continuous-planarity
  certificate.  It also identifies every genuine original source occurrence
  with its exact boundary port—`(36, 0)`, `(0, 30)`, or `(72, 30)`—inside
  the combined `72 × 72` refinement box.  A uniform template/map
  decomposition additionally exposes the complete image of occurring
  finite roles and preserves each role's exact translated position.  It
  consequently identifies every occurring second-stage auxiliary with its
  globally indexed unit-elimination vertex and every occurring first-stage
  auxiliary with the sixfold-scaled Figure 9 vertex.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineIndex.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineIndex.lean)
  indexes the actual two-stage positioned formula one original source block
  at a time.  Every final clause is linked to its original source clause, the
  global start of its Figure 9 block, and its exact local occurrence in the
  certified composed drawing.  The resulting source-block/local-clause keys
  are proved globally unique, and each stored block start is proved to turn
  every local Figure 9 clause index into its exact first-stage global index.
  Exact lookup bridges recover both the standard Figure 9 metadata entry and
  the standard local unit-elimination metadata entry represented by each
  composed entry, preserving both layers' source indices.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineLocalRoutes.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineLocalRoutes.lean)
  uses that index to select one route from the appropriate certified
  `72 × 72` composed neighborhood for every final incidence.  Every genuine
  selected route has its exact displayed endpoints, is orthogonal, and is
  continuously simple; distinct incidences in the same original source block
  satisfy the complete pairwise continuous-separation predicate.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineLocalRouteBounds.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineLocalRouteBounds.lean)
  certifies that every genuine finite-template route stays in the tight
  radius-36 neighborhood centered at offset `(36, 32)`, transports that
  bound through logical renaming and factor-72 placement, and exposes the
  resulting physical bound through the flattened composed metadata index.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRouteBounds.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRouteBounds.lean)
  translates the same radius-36 offset bound into each generated clause's
  canonical anchor gauge, factors its center through the combined factor-72
  source gauge, and transports relative output translations through that
  factorization.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineLocalRouteSeparation.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineLocalRouteSeparation.lean)
  recovers the unscaled clockwise source clauses for any relative pair of
  generated incidences and closes the distinct-center local/local case:
  the extra source factor two makes their radius-36 neighborhoods distinct
  factor-144 lattice neighborhoods, hence contact-free.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRoutes.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRoutes.lean)
  transports those selected routes into each final clause's canonical
  periodic anchor gauge.  The normalized family has exact periodic clause
  and local splice endpoints, remains orthogonal, and preserves continuous
  route simplicity.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineInheritedEndpoints.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineInheritedEndpoints.lean)
  classifies every twice-inherited final literal through unit elimination
  and Figure 9 back to its precise original source-clause occurrence.  Its
  offset is unchanged, and the normalized composed route ends at that
  occurrence's exact index-selected `72 × 72` boundary port.  The richer
  classifier also stores the global final-to-Figure-9 and Figure-9-to-source
  occurrence-pair witnesses used by periodic separation.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineAuxiliaryEndpoints.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineAuxiliaryEndpoints.lean)
  handles both fresh-variable generations in the same composed block.  Each
  Figure 9 auxiliary inherited through unit elimination and each later
  unit-elimination auxiliary is proved to end exactly at its canonical
  two-stage periodic variable position after clause-anchor normalization.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineInheritedRouteSplicing.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineInheritedRouteSplicing.lean)
  scales an original source incidence route directly by the combined factor
  `72`, changes it into the final clause's anchor gauge, and replaces its
  obsolete source-clause head by a connector from the certified composed
  port to its transformed first exit.  Exact endpoints and orthogonality
  are preserved; coordinating these connectors continuously remains part
  of the global planarity proof.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineInheritedRouteFamily.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineInheritedRouteFamily.lean)
  packages the two-stage classifier behind a proof-backed total selector.
  Any original canonical orthogonal route family with genuine first exits
  thereby induces exact, orthogonal suffixes for all and only the final
  incidences inherited through both transformations.  Composing the two
  stored occurrence pairings proves that distinct final inherited incidences
  always select distinct original source coordinates.
- [`LeanTrominoes/PeriodicOneInThreePositionedInheritedRouteFamily.lean`](LeanTrominoes/PeriodicOneInThreePositionedInheritedRouteFamily.lean)
  records that the Figure 9 occurrence selector is injective back to source
  incidence coordinates: two distinct generated incidences cannot select the
  same source clause and literal indices.  This is the first provenance layer
  needed to lift source-route separation through the composed replacement.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineRouteFamily.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineRouteFamily.lean)
  completes that inherited family with singleton suffixes for both
  generations of auxiliaries and splices every suffix onto its certified
  normalized local route.  Every final incidence thereby has exact canonical
  clause and literal endpoints and an orthogonal complete route.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsComposedRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsComposedRoutes.lean)
  instantiates the composed Figure 9 and unit-elimination route family over
  the normalized retained fixed-eight source.  The four finite templates
  replace the crossing-prone pair of sequential Manhattan adapters by one
  certified local route selection, while direct source suffixes retain exact
  canonical endpoints and orthogonality.  This intermediate family keeps the
  raw nested variable type so that a later coordinate-preserving renaming can
  identify it with the public wrapped formula.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedRenaming.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedRenaming.lean)
  proves that unit elimination is natural under source-variable renaming,
  including the complete renamed source clause stored in every auxiliary
  key.  The positioned formula and induced placement preserve clause
  positions, the physical period, and all renamed variable positions.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsComposedWrappedRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsComposedWrappedRoutes.lean)
  applies that naturality theorem to the public opaque wrapper.  It identifies
  the public unit-free formula and placement with their raw composed versions,
  reuses every certified route coordinate verbatim, and packages canonical
  endpoints and orthogonality for the public final formula.
- [`LeanTrominoes/PositionedPeriodicCNFClauseDirectionOrdering.lean`](LeanTrominoes/PositionedPeriodicCNFClauseDirectionOrdering.lean)
  stably sorts each positioned clause's tagged literals by the clockwise rank
  of their source-route first directions.  Original indices remain attached,
  so the unchanged source routes can be reindexed exactly; clause positions,
  widths, atom distinctness, assignment satisfaction, and satisfiability are
  all proved invariant under the reordering.  The canonical-route package
  also applies the necessary whole-period translation between the old and new
  first-literal anchor gauges, preserving exact endpoints and orthogonality.
  Pointwise transport lemmas also preserve unit steps and route-length lower
  bounds through that gauge change.  The complete finite variable-occurrence
  list is preserved up to permutation, so every occurrence bound is invariant
  as well.
  A finite cardinal-direction
  lemma turns nondecreasing ranks of three distinct genuine exits into the
  clockwise condition needed by the composed boundary-port router.
- [`LeanTrominoes/PositionedPeriodicCNFClauseDirectionVariableRouteOrder.lean`](LeanTrominoes/PositionedPeriodicCNFClauseDirectionVariableRouteOrder.lean)
  proves that the same per-clause sort preserves variable occurrence order.
  It matches slots by their unchanged clause-index sequence, uses per-clause
  atom distinctness to recover the unique source literal, and proves that
  route reindexing and the whole-period gauge translation preserve its final
  direction.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightClauseDirectionOrdering.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightClauseDirectionOrdering.lean)
  instantiates clause-direction ordering for the normalized retained
  fixed-eight source drawing.  Continuous separation forces distinct exits
  at each shared clause endpoint, while unit steps make every exit genuine;
  consequently every reordered ternary clause exposes its three routes in
  clockwise order.  The reordered presentation also retains the width-three
  bound, per-clause atom distinctness, canonical route geometry, route
  point injectivity, and
  satisfiability equivalence with the original source.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance.lean)
  inserts the extra factor-two whole-source refinement required before the
  fixed-size Figure 9 connector fan.  It scales the completed clockwise
  source drawing and then normalizes each route back to unit steps, proving
  canonical endpoints, orthogonality, simplicity, a nontrivial first edge,
  exact preservation of first directions and strict clockwise ranks, valid
  finite exit-fan selection, unchanged satisfiability, and complete relative
  route separation.  It also retains the occurrence-three promise needed by
  the later exact-one reductions.  Thus the later factor-72 inheritance sees a source
  lattice spacing of `144`, safely larger than the connector fan's radius-73
  reach.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearanceVariableRouteOrder.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearanceVariableRouteOrder.lean)
  specializes variable-order preservation to the retained clockwise source.
  Positive factor-two scaling preserves all terminal directions, while
  endpoint freshness of the scaled simple routes proves that the clearance
  loop erasure preserves them as well.
- [`LeanTrominoes/PlanarOneInThreeNoUnitsFigureNineClauseExitFans.lean`](LeanTrominoes/PlanarOneInThreeNoUnitsFigureNineClauseExitFans.lean)
  gives the finite noncrossing fan from the three fixed composed Figure 9
  source ports to the radius-72 first exits of an ordered source clause.
  The fourteen possible unary, binary, and ternary direction subsets have
  machine-checked endpoints, orthogonality, outer-frame and radius-73
  containment, and pairwise strict continuous separation.
- [`LeanTrominoes/PositionedPeriodicCNFClauseExitFanOrdering.lean`](LeanTrominoes/PositionedPeriodicCNFClauseExitFanOrdering.lean)
  packages the first directions of any nonempty width-three positioned
  clause as finite composed exit-fan data.  Generic genuine-direction and
  strict clockwise-rank invariants prove that the selected fan is one of the
  fourteen certified configurations.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineOrderedInheritedRouteSplicing.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineOrderedInheritedRouteSplicing.lean)
  translates a selected fan into a generated clause's canonical gauge and
  splices each connector directly to the scaled inherited unit-step route.
  The splice has exact endpoints and orthogonality, while common translation
  preserves both the fan's certified pairwise strict separation and its
  radius-73 source-neighborhood bound.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineInheritedRouteSplicing.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineInheritedRouteSplicing.lean)
  now also transports relative continuous separation through the combined
  factor-72 refinement and the two generated-clause anchor gauges, reducing
  transformed inherited-core separation to the original source certificate
  at an explicit anchor-adjusted lattice offset; the affine identity is
  discharged for the concrete composed placement.  Deleting the obsolete
  source heads preserves this separation and leaves only variable-tail
  contacts, exactly the suffix-side interface needed by route splicing.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineOrderedInheritedRouteFamily.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineOrderedInheritedRouteFamily.lean)
  recovers each twice-inherited original occurrence from the composed
  metadata, converts its index to a certified three-port fan slot, and
  packages the selected splices as a total canonical suffix family.
- [`LeanTrominoes/PositionedPeriodicCNFNormalizedRouteSeparation.lean`](LeanTrominoes/PositionedPeriodicCNFNormalizedRouteSeparation.lean)
  computes the exact physical relative offset represented by two distinct
  clause-anchor gauges and one semantic lattice translation.  Ordinary and
  contact-free route separation transport through this two-anchor identity.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRouteSeparation.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRouteSeparation.lean)
  specializes the two-anchor transport to the selected composed local route
  family, reducing stored relative separation back to displayed physical
  geometry in the certified Figure 9-plus-unit-elimination neighborhoods.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineSplicedRouteSeparation.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineSplicedRouteSeparation.lean)
  packages the six local/local, local/suffix, and suffix/suffix conditions
  sufficient for two complete composed routes at an arbitrary semantic lattice
  offset to avoid each other, with all four splice-endpoint equations discharged
  by the canonical certificates.  The two strict cross-piece conditions force
  the five semantic endpoint inequalities automatically, leaving only four
  continuous-avoidance obligations.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineClauseRouteOrder.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineClauseRouteOrder.lean)
  machine-checks the canonical south-west-east first-edge order on every
  ternary clause of the four finite composed templates.  The invariant is
  transported through logical renaming, geometric translation, clause-anchor
  normalization, metadata selection, and arbitrary inherited-suffix splicing.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRoutes.lean)
  instantiates the ordered suffix family over the factor-two clearance
  presentation of the retained source, then completes both generations of
  auxiliary routes and splices them to the certified local Figure 9 and
  unit-elimination drawings.  Every genuine twice-replaced route has exact
  canonical endpoints and is orthogonal.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineClauseRouteOrder.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineClauseRouteOrder.lean)
  specializes that finite-template invariant to the retained fixed-eight
  construction, proving that its complete raw ternary clause routes already
  have the exit order required by the normalized 3DM ribbon source.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineTerminalDirections.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineTerminalDirections.lean)
  proves that positive scaling, canonical-gauge translation, the ordered fan
  head replacement, and the final local splice preserve variable-side
  terminal direction.  Every twice-inherited final incidence recovers its
  exact factor-two clearance-source occurrence, and its complete raw route
  has that occurrence's final direction.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineOccurrenceSlots.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineOccurrenceSlots.lean)
  composes the occurrence-pair correspondences of Figure 9 and unit
  elimination.  A twice-inherited endpoint recovers its original incidence in
  the same first, second, or third occurrence slot, and any final atom reaching
  the third slot is inherited from an original source atom through both layers.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineVariableRouteOrder.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineVariableRouteOrder.lean)
  combines same-slot provenance with terminal-direction preservation.  The
  three raw routes of every degree-three final atom therefore inherit the
  clockwise order already proved for their factor-two clearance-source routes.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineInheritedEndpointIsolation.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineInheritedEndpointIsolation.lean)
  proves variable-endpoint isolation for every twice-inherited raw route.  Its
  transformed source tail inherits isolation from the simple clearance route,
  while the local route and finite ordered fan stay inside radius `73`, strictly
  below the combined source scale `144`.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedRoutes.lean)
  applies final loop erasure to the ordered composed family and packages both
  raw and normalized canonical route certificates.  The normalized drawing
  realizes every incidence edge, is orthogonal and integer-grid planar, and
  consists entirely of simple unit-step paths.  A generic relative-separation
  premise now suffices to promote it to the ribbon-ready interface.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedVariableRouteOrder.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedVariableRouteOrder.lean)
  uses inherited endpoint isolation to preserve terminal directions through
  final loop erasure.  Because every degree-three final atom is twice inherited,
  its three normalized routes retain the raw clockwise occurrence order.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedClauseRouteOrder.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedClauseRouteOrder.lean)
  proves that final loop erasure preserves the canonical exit order at every
  ternary clause.  A non-inherited second literal supplies a local route through
  the clause vertex that is strictly separated from each inherited suffix;
  hence no raw route can revisit its clause endpoint, and orthogonal loop
  erasure preserves its first direction.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRibbonOrders.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRibbonOrders.lean)
  combines the normalized variable and ternary-clause route orders, transports
  the variable certificate to the endpoint's opaque decidable equality, and
  discharges the clockwise-compatibility condition for every ribbon-ready
  presentation carrying the final Figure 9 route family.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRibbonCompatibility.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRibbonCompatibility.lean)
  isolates the finite compatibility boundary.  Graph well-formedness, both
  presentation lengths, and exact periodic route endpoints are automatic;
  compatibility is therefore equivalent to duplicate-free final vertex
  positions lying strictly inside the fundamental square.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRouteRadiusBounds.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRouteRadiusBounds.lean)
  carries the strict fixed-eight variable-centered route bound through both
  Figure 9 transformations.  Inherited source tails scale their old bound,
  ordered connectors add at most 73 cells, and auxiliary routes use the full
  144-cell reserve created by factor-two clearance followed by factor-72
  refinement.  Raw and finally normalized routes therefore lie within one
  output period of their canonical variable endpoint.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRibbonPresentation.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRibbonPresentation.lean)
  packages the completed route geometry at the precise source interface used
  by ribbon thickening.  Continuous planarity, orthogonality, exact endpoints,
  endpoint-only contacts, and the rebased-route halo bound are discharged;
  finite drawing compatibility is the sole remaining explicit premise, after
  which the concrete presentation also inherits clockwise-compatible fans.
- [`LeanTrominoes/PositionedPeriodicCNFVariableGaugeRouteOrders.lean`](LeanTrominoes/PositionedPeriodicCNFVariableGaugeRouteOrders.lean)
  proves that canonical variable gauging preserves occurrence-slot lookup,
  occurrence bounds, binary-or-ternary arity, clockwise variable-route order,
  and clockwise ternary-clause route order.  It also supplies the generic
  bridge from those two route-order certificates to clockwise-compatible
  source ribbon fans.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonPresentation.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonPresentation.lean)
  carries that one-period route-radius certificate through the final stable
  clause ordering and the canonical variable gauge.  At this final endpoint,
  the already verified vertex compatibility combines with continuous
  planarity and endpoint-only contacts to give an unconditional halo-bounded,
  ribbon-ready source presentation; no finite-geometry premise remains.  The
  final gauge also preserves clockwise variable and ternary-clause route
  orders and carries the binary-or-ternary and width-three promises to the
  finished formula.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonFans.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonFans.lean)
  transports the occurrence-three promise through the final clause sort and
  variable gauge, then assembles geometry and both cyclic route orders in one
  enriched presentation.  Its generic bridge proves that the final variable
  and clause endpoint fans are clockwise-compatible with the ribbon source
  tables, closing the remaining combinatorial side condition at this endpoint.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRouteSeparation.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRouteSeparation.lean)
  instantiates the relative splice assembly for the retained ordered fixed-eight
  route family.  Four explicit avoidance conditions imply all six splice
  conditions, global raw route separation, and hence ribbon readiness of the
  normalized drawing.  It consumes the relative separation and route
  simplicity certificates of the factor-two clearance source, supplying the
  inherited geometry used by the suffix side of that splice.  The composed
  occurrence provenance discharges the adjusted source-occurrence inequality
  for every distinct final relative occurrence; the factor-72 transport
  theorem then proves that both transformed inherited route tails avoid each
  other and can meet only at their variable-side endpoints.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineCompleteRouteSeparation.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineCompleteRouteSeparation.lean)
  discharges the four remaining local/local, local/inherited, inherited/local,
  and inherited/inherited avoidance obligations for every relative pair of
  final incidences.  Consequently the raw route family is globally separated,
  and the normalized drawing is route-matching, orthogonal, planar, and
  ribbon-ready without any residual geometric hypothesis.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSemantics.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSemantics.lean)
  reconnects that completed ordered drawing to the two verified logical
  exact-one transformations.  The erased endpoint is satisfiable exactly when
  the original local periodic CNF is satisfiable, has width at most three,
  has only binary or ternary clauses, and preserves the occurrence-three
  promise.  Named opaque equality and occurrence interfaces keep these facts
  usable without repeatedly normalizing the deeply nested reduction-variable
  type.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineThreeDM.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineThreeDM.lean)
  applies the normalized periodic 3DM encoding to that exact ordered formula
  and placement.  The result is well formed, every colored element has degree
  two or three, and both perfect-matching existence and the abstract required
  incidence orientation are equivalent to satisfiability of the original
  local periodic CNF.
- [`LeanTrominoes/PlanarOneInThreeNoUnitsInstantiation.lean`](LeanTrominoes/PlanarOneInThreeNoUnitsInstantiation.lean)
  renames and translates all four unit-elimination templates to actual
  positioned periodic source clauses.  Forgetting only logical literal
  offsets identifies each embedded formula with the real positioned
  `clauseGadget` output, and every instance inherits the complete local
  geometric certificate.
- [`LeanTrominoes/PlanarOneInThreeNoUnitsSelector.lean`](LeanTrominoes/PlanarOneInThreeNoUnitsSelector.lean)
  packages the four unit-elimination instances behind one total arity
  selector.  For width-three clauses it proves exact agreement with the
  positioned output block and derives the complete local validity
  certificate from per-clause atom distinctness.  It also identifies every
  scoped auxiliary's translated physical position with its declared local
  unit-elimination coordinate, and assigns every genuine source occurrence
  its index-selected boundary port.
- [`LeanTrominoes/PlanarOneInThreeLocalDistinctness.lean`](LeanTrominoes/PlanarOneInThreeLocalDistinctness.lean)
  proves that every clause produced by Figure 9 has distinct variable atoms,
  independently of repetitions in its source clause.  It also packages
  per-clause atom distinctness for positioned formulas and proves that
  injective renaming, uniform coordinate scaling, and the unit-elimination
  replacement preserve it.
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
  polar angle of its full terminal ray, orders same-direction ties by
  increasing squared radius, and proves that sorting preserves exactly the
  source occurrences.  This supplies the cyclic and radial order consumed by
  occurrence splitting without prematurely asserting an orthogonal drawing.
- [`LeanTrominoes/PeriodicCNFPlanarAngularOneInThreePositioned.lean`](LeanTrominoes/PeriodicCNFPlanarAngularOneInThreePositioned.lean)
  specializes the full positioned ordered pipeline to those terminal-ray
  angles.  It fixes the occurrence-split formula and placement, carries them
  through Figure 9 and unit elimination, and proves the resulting exact-one
  source has occurrence degree at most three, clause arity two or three, and
  exactly the original periodic-CNF satisfiability semantics.  Its physical
  period is proved positive, and the canonical detour family supplies
  unconditional endpoint and orthogonality certificates for this concrete
  source; nonintersection remains the geometric obligation.
- [`LeanTrominoes/PeriodicCNFPlanarFixedEightOneInThreePositioned.lean`](LeanTrominoes/PeriodicCNFPlanarFixedEightOneInThreePositioned.lean)
  aligns that downstream exact-one pipeline with the certified fixed-eight
  Figure 7 presentation.  It carries the same positioned formula used by
  the angular-spliced routes through Figure 9, opaque wrapping, and unit
  elimination, proving erasure, width three, occurrence degree three,
  final arity two or three, positive period, and end-to-end satisfiability.
  Subsequent geometric work can therefore use one common intermediate
  formula instead of bridging variable-size and fixed-eight cycles.
- [`LeanTrominoes/PeriodicCNFPlanarFixedEightOneInThreeRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarFixedEightOneInThreeRoutes.lean)
  feeds the fixed-eight angular-spliced routes into the inherited Figure 9
  adapter and then completes fresh auxiliaries through the local-route splice.
  The actual raw exact-one formula now has a total route family with exact
  canonical endpoints and orthogonality.  Its generic source-port Manhattan
  connectors isolate the remaining noncrossing clause-boundary-fan
  obligation.
- [`LeanTrominoes/PeriodicCNFPlanarFixedEightOneInThreeVariableRouteOrder.lean`](LeanTrominoes/PeriodicCNFPlanarFixedEightOneInThreeVariableRouteOrder.lean)
  proves every genuine fixed-eight source route is nondegenerate, using the
  angular spoke suffix for copied incidences and the certified local Figure 7
  drawing for ring incidences.  It specializes the fixed-eight clockwise
  route-order theorem to the hardness pipeline and proves that the concrete
  raw Figure 9 splice preserves every inherited terminal direction.  Together
  with the generic Figure 9 transport theorem, this is the compositional
  certificate carrying variable order across the first exact-one layer.
- [`LeanTrominoes/PeriodicCNFPlanarFixedEightOneInThreeWrappedRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarFixedEightOneInThreeWrappedRoutes.lean)
  transports that complete route family through the pipeline's opaque
  variable wrapper without changing any polyline.  The wrapped Figure 9
  formula therefore retains the same pointwise canonical endpoints and
  orthogonality certificates needed by unit elimination.
- [`LeanTrominoes/PeriodicCNFPlanarFixedEightOneInThreeNoUnitsRoutes.lean`](LeanTrominoes/PeriodicCNFPlanarFixedEightOneInThreeNoUnitsRoutes.lean)
  feeds those wrapped routes through the inherited unit-elimination adapter
  and completes all local auxiliary incidences.  Thus the final fixed-eight,
  unit-free exact-one formula has a total route family with exact canonical
  endpoints and orthogonality.  The file also proves the assembled drawing's
  complete `RoutesMatch` and `IsOrthogonal` predicates; proving that drawing
  globally planar remains the next geometric obligation.
- [`LeanTrominoes/PeriodicCNFPlanarFixedEightOneInThreeNoUnitsVariableRouteOrder.lean`](LeanTrominoes/PeriodicCNFPlanarFixedEightOneInThreeNoUnitsVariableRouteOrder.lean)
  carries clockwise variable-route order through the opaque Figure 9 wrapper
  and final unit-elimination splice.  A wrapped variable with a third
  occurrence is proved to be an embedded source variable, whose inherited
  Figure 9 routes have at least three points; the degree-three-scoped
  terminal-direction theorem then proves that the final unit-free routes
  follow syntactic occurrence order clockwise.
- [`LeanTrominoes/PeriodicCNFPlanarAngularOneInThreeDistinctness.lean`](LeanTrominoes/PeriodicCNFPlanarAngularOneInThreeDistinctness.lean)
  threads the local atom-distinctness certificates through opaque wrapping
  and unit elimination, then specializes them to the angular hardness
  pipeline.  Consequently every final binary or ternary source clause meets
  the distinct-boundary assumptions of its certified local drawing.
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
  count, reaching the third slot certifies at least three occurrences, and
  the occurrence-three bound assigns every tagged literal to one unique pair
  of complementary variable ports.
- [`LeanTrominoes/PeriodicOneInThreeToThreeDMDegreeThreeOriginal.lean`](LeanTrominoes/PeriodicOneInThreeToThreeDMDegreeThreeOriginal.lean)
  combines that third-slot lower bound with the occurrence accounting of both
  exact-one transformations.  Because every fresh auxiliary occurs at most
  twice, any degree-three output variable must be an embedded source
  variable; only inherited variable fans therefore need their cyclic order
  transported.
- [`LeanTrominoes/PeriodicOneInThreeOriginalOccurrenceOrder.lean`](LeanTrominoes/PeriodicOneInThreeOriginalOccurrenceOrder.lean)
  gives the Figure 7 transformation an explicit order-preserving pairing
  between embedded output occurrences and their tagged source occurrences.
  In particular, each output occurrence slot maps to the identical source
  slot, even though the gadget distributes source literals among different
  generated clauses and negates its second and third inputs.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsOriginalOccurrenceOrder.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsOriginalOccurrenceOrder.lean)
  gives unit elimination the analogous pairing.  Unit literals move,
  negated, into the first generated ternary clause while non-unit clauses
  lift pointwise; in both cases the ordered output occurrence slots coincide
  exactly with the ordered source slots.
- [`LeanTrominoes/PeriodicOneInThreeVariableRouteOrderTransport.lean`](LeanTrominoes/PeriodicOneInThreeVariableRouteOrderTransport.lean)
  isolates the geometric part of both transports as a pointwise terminal-
  direction preservation predicate on paired inherited routes.  Once that
  predicate holds, the occurrence pairing and degree-three classification
  automatically carry clockwise variable-route order through Figure 7 and
  through unit elimination.  For unit elimination, a weaker certificate
  scoped to source atoms with a third occurrence is sufficient, so
  degree-at-most-two auxiliaries require no irrelevant length hypothesis.
- [`LeanTrominoes/PeriodicOneInThreeWrappedVariableRouteOrderTransport.lean`](LeanTrominoes/PeriodicOneInThreeWrappedVariableRouteOrderTransport.lean)
  composes Figure 9 route-order transport with the opaque variable wrapper
  and packages the analogous unit-elimination result behind equality-instance
  independent interfaces.  It also proves that any wrapped variable reaching
  the third occurrence slot wraps an embedded Figure 9 source variable.
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
  index-for-index equal to the separately retained duplicate-free colored
  incidence tags.
- [`LeanTrominoes/PeriodicThreeDMIncidenceVertexCoverage.lean`](LeanTrominoes/PeriodicThreeDMIncidenceVertexCoverage.lean)
  shows that this incidence graph is loopless and, under the degree-two-or-
  three promise, has no isolated vertices.  Consequently every compatible
  nondegenerate incidence drawing covers all of its stored vertex positions
  by lifted route-segment endpoints.
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
- [`LeanTrominoes/DegreeThreeVertexNormalizationTemplates.lean`](LeanTrominoes/DegreeThreeVertexNormalizationTemplates.lean)
  transcribes the four `6 × 6` replacement templates and the cyclic
  port-rotation template from Lemma 2.3.  Finite computation verifies exact
  endpoints, unit rectilinear steps, square containment, the omitted-side
  permutation, and disjointness away from the common vertex center.
- [`LeanTrominoes/DegreeThreeVertexNormalizationPorts.lean`](LeanTrominoes/DegreeThreeVertexNormalizationPorts.lean)
  formalizes the finite port bookkeeping behind those templates.  It inverts
  the omitted-side permutation, tracks zero, one, or two cyclic rotations,
  moves the red incidence to the north port, and proves that the resulting
  RGB assignment exactly matches one of the two trichromatic cell types.
- [`LeanTrominoes/DegreeThreeVertexNormalizationFans.lean`](LeanTrominoes/DegreeThreeVertexNormalizationFans.lean)
  packages the three colored endpoint directions at a degree-three vertex.
  It selects the unique unused cardinal side and proves that the Figure 2
  permutation transports all three old edge colors, including both the
  monochromatic and distinct-RGB cases, to the canonical ports.
- [`LeanTrominoes/PeriodicThreeDMContractedEndpointFans.lean`](LeanTrominoes/PeriodicThreeDMContractedEndpointFans.lean)
  enumerates the source and target ends of the executable contracted 3DM
  edges, carrying their vertex, color, route, and outward direction.  It
  proves contraction creates no prototype loops and that every actual end
  has a genuine cardinal direction in the certified orthogonal drawing.
- [`LeanTrominoes/PeriodicThreeDMContractedEndpointDegree.lean`](LeanTrominoes/PeriodicThreeDMContractedEndpointDegree.lean)
  identifies endpoint-fan length with graph-theoretic degree and uses the
  incidence-tag permutation preserved by contraction to prove that every
  indexed trichromatic triple still has exactly three endpoint occurrences.
- [`LeanTrominoes/PeriodicThreeDMContractedElementDegree.lean`](LeanTrominoes/PeriodicThreeDMContractedElementDegree.lean)
  proves the complementary monochromatic invariant: every retained colored
  element (equivalently, each degree-three element) has exactly three
  contracted endpoint occurrences, while all other element blocks
  contribute zero ends to that vertex.
- [`LeanTrominoes/PeriodicThreeDMContractedEndpointRays.lean`](LeanTrominoes/PeriodicThreeDMContractedEndpointRays.lean)
  realizes each contracted source or target end as the actual first
  axis-aligned segment leaving the base vertex occurrence.  Target rays are
  reversed and period-translated back from their stored endpoint, while
  retaining the indexed segment occurrence needed for planarity arguments.
- [`LeanTrominoes/PeriodicThreeDMContractedEndpointDirectionSeparation.lean`](LeanTrominoes/PeriodicThreeDMContractedEndpointDirectionSeparation.lean)
  proves that the endpoint enumeration is duplicate-free and that distinct
  endpoints at one contracted vertex leave in distinct cardinal directions.
  Equal directions would force their realized segment interiors to overlap,
  contradicting continuous planarity of the contracted drawing.
- [`LeanTrominoes/PeriodicThreeDMContractedVertexFans.lean`](LeanTrominoes/PeriodicThreeDMContractedVertexFans.lean)
  packages each exact three-entry endpoint list into the colored-fan
  interface used by the finite normalization templates.  Triple fans have
  pairwise-distinct RGB colors, while retained element fans induce the
  constant coloring of their element color.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationRoutes.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationRoutes.lean)
  defines the executable three-round geometric replacement.  It first maps
  arbitrary endpoint directions to west/north/east, then applies up to two
  clockwise port rotations to put red north, magnifying by twelve and
  splicing verified local templates onto every contracted route each round.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationColors.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationColors.lean)
  identifies the executable list-based color lookups with the certified
  contracted fans.  It proves the selected final cell has the normalized RGB
  colors at each triple and the constant element color at every retained
  monochromatic vertex.
- [`LeanTrominoes/PeriodicThreeDMNormalizationRasterization.lean`](LeanTrominoes/PeriodicThreeDMNormalizationRasterization.lean)
  compiles the final unit-route geometry into a finite square-torus
  `PeriodicOrthogonalDrawing`: centers become normalized vertex cells,
  internal route points become colored wires or bends, and every unused cell
  is blank.  Its row-major array has exactly the advertised positive period.
- [`LeanTrominoes/PeriodicThreeDMNormalizationRasterizationCorrectness.lean`](LeanTrominoes/PeriodicThreeDMNormalizationRasterizationCorrectness.lean)
  proves the local rasterizer semantics and the row-major lookup theorem.
  It reduces drawing well-formedness and degree-three vertex separation to
  explicit neighboring-cell obligations on the finite assignment lookup,
  isolating those remaining obligations from array-index bookkeeping.  It
  also proves that reflected geometric unit steps commute with finite-torus
  projection, including wraparound in both periods.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationRouteGeometry.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationRouteGeometry.lean)
  verifies the first two points and first direction of every final normalized
  route.  In particular, each source route leaves its normalized vertex by
  one unit step through the endpoint's computed west, north, or east port,
  and that step projects to the matching neighbor in the finite drawing.
  It also proves the twelvefold magnification leaves at least seven middle
  points after trimming, so the reversed target template survives the splice
  and the final route reaches the normalized periodic target occurrence.
  The target-adjacent point is likewise identified as the outward unit step
  through that endpoint's final canonical port.  Finally, the stored target
  offset is proved to become an integer multiple of the final torus period,
  so the translated occurrence and base target vertex have the same raster
  key.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationEndpointColors.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationEndpointColors.lean)
  proves that the two executable Boolean rotation rounds implement the
  selected zero/one/two-step port permutation.  Every certified fan endpoint
  therefore finds its contracted-edge color at its computed final normalized
  port, and both the trichromatic and monochromatic vertex cell constructors
  are proved to expose that color there.  A final enumeration theorem
  reconstructs the appropriate fan automatically for every listed contracted
  endpoint, so later route proofs need no hand-supplied local fan data.
- [`LeanTrominoes/PeriodicThreeDMNormalizationAssignmentLookup.lean`](LeanTrominoes/PeriodicThreeDMNormalizationAssignmentLookup.lean)
  isolates raster collision freedom as duplicate-freeness of assigned torus
  locations.  Under this one explicit invariant, every listed degree-three
  vertex and every emitted route-interior assignment is recovered exactly by
  the compiled cell lookup.
- [`LeanTrominoes/PeriodicThreeDMNormalizationAssignmentGeometry.lean`](LeanTrominoes/PeriodicThreeDMNormalizationAssignmentGeometry.lean)
  identifies those assignment locations with the torus image of exactly the
  normalized vertex centers and route-interior points.  Equality of raster
  locations is characterized as equality up to a whole-period translation,
  and a duplicate-free occurrence-indexed enumeration gives every vertex or
  route-interior point a stable key.  Thus `FinalAssignmentsCollisionFree`
  reduces to the single geometric certificate that distinct keyed
  occurrences have distinct torus locations.  Compatible fundamental-square
  placement proves the vertex/vertex cases, while endpoint-only route
  contacts prove the route-interior/route-interior cases.  Exact compatible
  route endpoints and graph incidence cover every stored vertex by a route
  endpoint, so the same endpoint-contact certificate also excludes all mixed
  vertex/route-interior collisions.  Thus, for an incident compatible graph,
  endpoint-only route contacts alone imply complete assignment separation.
  A degree calculation proves every retained contracted 3DM vertex is
  incident, specializing the result so endpoint-only contacts in the final
  normalized drawing are the sole remaining input to assignment collision
  freedom.
- [`LeanTrominoes/PeriodicThreeDMNormalizationEndpointRasterization.lean`](LeanTrominoes/PeriodicThreeDMNormalizationEndpointRasterization.lean)
  proves that every final route begins and ends with two nonreversing unit
  steps at its normalized endpoint occurrences.  Its first and last routing
  assignments are therefore emitted, expose the edge color toward their
  vertices under collision freedom, and match the automatically recovered
  colors of both vertex ports after finite-torus projection.
- [`LeanTrominoes/PeriodicThreeDMNormalizationRouteRasterization.lean`](LeanTrominoes/PeriodicThreeDMNormalizationRouteRasterization.lean)
  proves the uniform route-interior counterpart: every displayed route triple
  emits its middle assignment, and every four-point window in a unit-step,
  nonreversing final route compiles to two routing cells whose common ports
  expose the same edge color under collision freedom.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationRouteValidity.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationRouteValidity.lean)
  begins discharging those route-validity hypotheses: affine magnification,
  ordered unit subdivision, and endpoint trimming preserve orthogonality and
  produce a unit-step middle in every normalization round.  It also computes
  both splice boundaries exactly: trimming lands three unit steps along the
  old first segment and three reverse unit steps along the old last segment.
  The finite direction-normalization and cyclic-rotation templates are
  certified to end at those same boundaries, yielding a reusable theorem
  that each complete two-ended splice is a unit-step route.  Instantiating
  it with the contracted drawing and its certified nonomitted endpoint sides
  proves that every first-round `normalizationRoute1` is a unit-step chain.
  The preserved endpoint/adjacent-point interface then lifts this invariant
  through both cyclic-rotation rounds, proving every
  `finalNormalizationRoute` is a unit-step chain.  For the remaining
  validity invariant, continuous planarity rules out reversals in every
  contracted route, and affine magnification, unit subdivision, and trimming
  are proved to preserve that nonreversal property.  All finite Figure 2 and
  cyclic-rotation templates are also certified nonreversing, with their final
  directed steps identified as the exact incoming old endpoint directions;
  trimming is now proved to preserve both endpoint directions as well.  These
  facts feed a generic two-ended splice theorem proving that neither join can
  introduce an immediate reversal.  The theorem has been instantiated for
  the Figure 2 replacement, so every first-round `normalizationRoute1` is now
  nonreversing as well as unit-step.  The invariant is then lifted through
  both cyclic replacements: every `finalNormalizationRoute` is now formally
  certified as a nonreversing unit-step route, discharging both validity
  hypotheses of the normalized-route rasterizer.  Consequently every
  four-point route window compiles to adjacent routing cells with matching
  colored ports, assuming only the remaining global assignment-collision
  certificate.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationDrawing.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationDrawing.lean)
  packages the final normalized positions and routes as a standard
  `PeriodicGridDrawing`.  It proves exact vertex/edge lookup, injective
  fundamental-square vertex placement, source/translated-target route
  compatibility, and the drawing-wide unit-step invariant.  This certified
  occurrence-indexed drawing is the interface for the remaining global
  separation and assignment-collision proof.
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
  instantiates the corrected normal-offset construction at physical lane
  distances `40`, `44`, and `48` inside each `128`-cell refinement corridor,
  after applying the occurrence's semantic-color lane permutation.  Every
  genuine rebased source incidence is proved
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
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalization.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalization.lean)
  supplies the logical preprocessing demanded by the variable-ribbon
  geometry.  It normalizes clause positions to the fixed-red/fixed-blue/
  fixed-green polarity pattern `false`, `false`, `true`.  An incompatible
  occurrence is replaced by a fresh complement variable and the binary
  exact-one clause `[fresh = false, original = false]`; the file proves both
  directions of satisfiability preservation, locality, binary-or-ternary
  arity, and the polarity certificate for every generated clause.  The
  geometric route subdivision is described below; the remaining work is to
  prove its global separation and planarity properties and to finish the
  site-wide fixed-green/true strand, whose route cannot be chosen independently
  in each occurrence slot.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationOccurrences.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationOccurrences.lean)
  proves that the same preprocessing preserves the occurrence-three
  restriction.  Every embedded source variable has exactly its original
  occurrence count, while each occurrence-indexed fresh complement variable
  appears at most twice: once in its normalized source clause and once in its
  binary complement clause.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationPositioned.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationPositioned.lean)
  lifts the construction to positioned formulas.  It exposes the incompatible
  incidence replacement as the three-edge path from the source clause through
  its fresh variable and binary complement clause to the original variable,
  with the two new vertex positions abstracted for the planar route layer.
  Erasure is proved equal to the logical normalization, so satisfiability,
  locality, arity, polarity, and occurrence bounds transfer immediately.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationPositionedIndex.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationPositionedIndex.lean)
  gives the variable-size positioned replacement a parallel lossless clause
  index.  Every generated clause retains its source clause and is classified
  as either the normalized main clause or the binary clause of one exact
  incompatible source occurrence.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteSubdivision.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteSubdivision.lean)
  realizes that three-edge path geometrically.  It
  anchor-normalizes and refines each source route by a factor of three, proving
  that two interior unit-subdivision points are available.  The fresh
  complement variable and binary clause occupy those points, while a
  fresh-only variable gauge makes the fresh literal offset zero and preserves
  both physical placement and exact-one satisfiability.  The indexed output
  route family keeps a compatible route whole and splits every incompatible
  route into the clause-side prefix, reversed middle edge, and translated
  original-variable suffix.
- [`LeanTrominoes/PositionedPeriodicCNFPresentationCanonicalRoutes.lean`](LeanTrominoes/PositionedPeriodicCNFPresentationCanonicalRoutes.lean)
  converts an assembled planar incidence presentation into the pointwise
  canonical endpoint/orthogonality interface and proves that unit subdivision
  preserves that interface.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteCorrectness.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteCorrectness.lean)
  certifies the complete subdivided route table.  Every normalized-main and
  complement-clause incidence has its exact canonical endpoints, every route
  is orthogonal, and both properties are transported through the fresh-variable
  gauge to the final normalized incidence drawing.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationRoutePlanarity.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRoutePlanarity.lean)
  proves that all those prefixes, reverse middle edges, suffixes, and gauge
  translations consist of genuine unit lattice steps.  Consequently the final
  normalized incidence drawing satisfies the integer-grid planarity predicate.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteVertices.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteVertices.lean)
  identifies the two inserted vertices after gauging: each fresh variable is
  subdivision point one and its complement clause is subdivision point two.
  It also proves that normalized main clauses and binary complement clauses
  both have zero canonical anchor.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMPolarityNormalization.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMPolarityNormalization.lean)
  transports that formula-level certificate through the actual occurrence
  lookup table used by the typed planar 3DM assembly.  Every active occurrence
  is proved to be either fixed-red/fixed-blue with the already checked
  endpoint-clear false table, or exactly fixed-green/true.  Thus the latter is
  now the sole explicitly isolated variable-core/local-gate clearance case.
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
