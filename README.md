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
  - [x] Prove co-r.e.-hardness of the 2D problem for each tromino.
    - [x] Normalize exact-one literal polarities while preserving
      satisfiability, occurrence and arity bounds, and the complete
      halo-bounded ribbon-ready planar presentation.
    - [x] Connect the normalized presentation to the padded planar 3DM ribbon
      assembly, retaining degree two or three and exact orientation semantics.
    - [x] Specialize the continuously planar 3DM construction to Wang tile
      sets, including a fixed contradictory fallback for the empty tile set
      and the lifted-route separation and route-simplicity certificates.
    - [x] Prove the total Wang source-formula map primitive recursive and the
      logical polarity-normalization transform computable.
    - [x] Prove the finite periodic-CNF incidence graph primitive recursive,
      including its tagged bipartite vertices and literal-indexed edges.
    - [x] Prove the executable orthocrossing track drawing primitive recursive,
      from ranked edge-end ports through complete protoedge polylines.
    - [x] Encode metadata-rich CNF incidences and translated route occurrences,
      and prove their constructed segments and canonical endpoint terminals
      primitive recursive.
    - [x] Prove the finite retained crossing-halo enumeration primitive
      recursive, including translated segment occurrences, crossing records,
      and the proper-crossing filter.
    - [x] Prove the canonical fundamental-square crossings and their
      horizontal-first representatives primitive recursive.
    - [x] Give segment terminals, crossing boundaries, carrier nodes, and
      positioned equality links canonical primitive-recursive encodings.
    - [x] Prove the retained crossing orbit, carrier-node geometry, and stable
      per-carrier chain sorting primitive recursive.
    - [x] Prove consecutive retained carrier links and their positioned raw
      equality-link family primitive recursive.
    - [x] Prove integer period-quotient extraction and the zero-shift orbit-
      representative filter for retained carrier links primitive recursive.
    - [x] Give embedded clauses a canonical encoding and prove the retained
      positioned carrier-equality formula primitive recursive.
    - [x] Encode route bends and prove their neighboring-occurrence
      enumeration, equality links, and retained wire formula primitive
      recursive.
    - [x] Encode the fixed crossover variables and ports, and prove generic
      embedded-formula renaming, placement, and crossover-family
      instantiation primitive recursive.
    - [x] Prove the retained crossover family and its combination with the
      retained route-wire formula primitive recursive.
    - [x] Prove the ordered routed clause and variable-duplicator families,
      and the resulting complete retained planar-SAT formula, primitive
      recursive.
    - [x] Give the five retained planar-SAT clause-source kinds canonical
      encodings and prove their exact global metadata enumeration primitive
      recursive in formula order.
    - [x] Prove the five retained local incidence-route templates and their
      exact metadata-indexed route lookup primitive recursive.
    - [x] Encode periodic planar-SAT protovariables and prove retained
      finite-block periodicization and opaque variable wrapping primitive
      recursive.
    - [x] Prove the retained positioned planar-SAT presentation, its
      canonical variable and clause-anchor gauges, and its periodic
      clause-orbit representatives primitive recursive.
    - [x] Transport the exact retained incidence routes through variable
      gauging, clause-anchor normalization, and clause-orbit deduplication,
      then compute their angular fixed-eight occurrence split.
    - [x] Prove the positioned fixed-eight ring compiler primitive recursive,
      including its clause coordinates and companion placement queries, and
      specialize it to the exact retained positioned split.
    - [x] Prove the exact canonical angular-spliced Figure 7 route lookup
      computable for positioned fixed-eight splits, including copied
      incidences and appended implication rings, and specialize it to the
      retained planar-SAT source.
    - [x] Prove the flattened positioned Figure 9 clause metadata and exact
      arity-selected local route lookup primitive recursive, including
      clause-anchor normalization in the induced Figure 9 placement.
    - [x] Prove the positioned Figure 9 and unit-elimination compilers
      primitive recursive, including their placement queries, and specialize
      them through the retained unit-free exact-one endpoint.
    - [x] Compose the retained fixed-eight split through Figure 9 exact-one
      conversion, opaque wrapping, unit elimination, anchor normalization,
      and the finite planar 3DM encoding primitive recursively.
    - [x] Prove positioned periodic-CNF erasure, variable renaming,
      anchor normalization, and clause-orbit deduplication primitive
      recursive.
    - [x] Prove clause-anchor normalization and input-dependent variable
      gauges primitive recursive on finite periodic CNF presentations.
    - [x] Prove stable route-direction sorting of positioned periodic clauses
      primitive recursive from a primitive-recursive route lookup.
    - [x] Prove computable finite-list folds, maps, and stable insertion sort,
      then lift route-direction clause sorting to computable source formulas
      and merely computable route lookups.
    - [x] Prove verified orthogonal-route loop erasure primitive recursive by
      identifying `Walk.bypass` support with a proof-free list algorithm.
    - [x] Give dependent coordinated direct-route atlas choices canonical
      encodings and compute their complete positioned routes.
    - [x] Prove the raw metadata-indexed coordinated direct-route choice
      selector primitive recursive, including its checked source cases.
    - [x] Prove the final representative-metadata lookup and checked
      translated direct-route selector primitive recursive through
      clause-anchor normalization and clause-orbit deduplication.
    - [x] Prove the exact source-scaled occurrence-slot and Figure 7 suffix
      queries primitive recursive, and assemble each successful final
      coordinated direct occurrence route primitive recursively.
    - [x] Prove the final singleton-prefix escape test and scaled-source
      clause lookup primitive recursive for total-route branch selection.
    - [x] Prove the exact eleven-direction retained-ray classifiers,
      staircase generators, and whole-polyline rasterizer primitive recursive.
    - [x] Prove the generic delayed-lane escaped fan, variable-tail
      replacement, and rasterized source boundary splice primitive recursive.
    - [x] Prove the generic ordinary retained fan, variable-tail replacement,
      and rasterized source boundary splice primitive recursive.
    - [x] Assemble each exceptional final escaped-fallback occurrence route
      primitive recursively with its exact slot and Figure 7 suffix.
    - [x] Compute the established ordinary copied-occurrence and translated
      implication-cycle fallback route lookup primitive recursively.
    - [x] Assemble the exact final direct, escaped, ordinary, and cycle route
      dispatcher primitive recursively, including every malformed-index
      fallback.
    - [x] Compute each final unit-subdivided, loop-erased route and its first
      direction primitive recursively.
    - [x] Prove fixed-eight occurrence splitting primitive recursive from a
      primitive-recursive source formula and compass-port lookup.
    - [x] Prove stable terminal-angle occurrence sorting and its induced
      fixed-eight compass-port lookup primitive recursive from finite routes.
    - [x] Compute the first clockwise retained clause ordering, its Figure 9
      clearance scale, and the twice-replaced raw unit-free exact-one formula
      primitive recursively.
    - [x] Compute the flattened composed Figure 9 metadata, twice-refined
      placement, finite local route tables, and anchor-normalized local route
      lookup primitive recursively.
    - [x] Compute the inherited Figure 9 connector-and-source suffix lookup
      primitive recursively and prove exact pointwise agreement with the
      proof-backed ordered fan suffix family.
    - [x] Complete the proof-free Figure 9 suffix lookup for both auxiliary
      generations and prove exact agreement with the certified complete
      suffix family.
    - [x] Splice every computed local Figure 9 route to its complete suffix
      primitive recursively and identify the result with the proof-backed
      complete route family.
    - [x] Normalize the complete retained routes and compute the second,
      final clockwise clause ordering primitive recursively.
    - [x] Compute the canonical final variable gauge and the resulting gauged
      clockwise exact-one formula primitive recursively.
    - [x] Compute the final factor-two padded, clause-anchor-normalized planar
      3DM instance and prove exact equality with the continuously planar
      proof-backed endpoint.
    - [x] Compute the routed polarity-normalized erased formula and its final
      padded planar 3DM endpoint, and prove exact equality with the
      proof-backed construction.
    - [x] Prove the exact Wang-to-planar-3DM problem map computable and pair it
      computably with the first verified finite drawing.
    - [x] Prove the finite Dyer--Frieze planar exact-one-to-3DM problem
      encoding primitive recursive, including its connector references and
      natural-number color-class numbering.
    - [x] Reduce the planar drawing obligations to a finite Boolean
      certificate and prove every accepted drawing supplies the continuous
      planarity, separation, and route-simplicity data needed by the compiler.
      - [x] Give the graph, grid-drawing, indexed-segment, and indexed-route-
        point data canonical encodings, and prove the 3DM incidence-graph and
        finite drawing enumerations primitive recursive.
      - [x] Prove the integer interval enumeration and all segment predicates
        used by the verifier primitive recursive.
      - [x] Prove the complete finite drawing verifier primitive recursive.
      - [x] Enumerate encoded periodic grid drawings, select the first
        accepted certificate by total unbounded search, prove the selector
        computable from a computable source, and instantiate search
        termination for every Wang input.
      - [x] Compute every complete typed RGB incidence route of the explicit
        horizontal 3DM drawing primitive recursively, including finite
        variable-site prefixes, the unique coordinated occurrence extension,
        and translated clause-core routes; enumerate those routes in the
        encoded problem's stable incidence-tag order.
    - [x] Rasterize the planar 3DM drawing to the normalized orthogonal-cell
      interface and compose the I- and L-tromino gadget reductions.
      - [x] Prove that every compiled vertex cell comes from the coarse
        normalized vertex lattice and that adjacent cells are nonvertices.
      - [x] Prove that affine magnification, ordered unit subdivision, and a
        common translation preserve endpoint-only route contacts, with all
        contracted-drawing side conditions derived from the existing API.
      - [x] Rotate the ordinary fixed-green occurrence tree without changing
        its boundary truth table, aligning its connector leaves with the
        physical ribbon-lane order.
      - [x] Give fixed-green/true a lane-aligned embedding and certify full
        endpoint-aware separation between every core route and local gate.
      - [x] Prove that polarity normalization selects exactly the three
        endpoint-clear tables (fixed-red/false, fixed-blue/false, and
        fixed-green/true), and preserve that prerequisite through scaling,
        anchor normalization, padded assembly, and continuous planarity.
      - [x] Prove contracted-drawing endpoint contacts and preserve them
        through the local endpoint-template splices.
        - [x] Lift the normalized endpoint-aware variable-core/gate tables
          through source coordinates, coordinated fans, complete occurrence
          routes, and the typed finite-core interface.
        - [x] Classify variable-core/occurrence contacts: every nonmatching
          routed triple/color is strictly separated, while the unique
          matching route retains only its intended variable-port splice.
        - [x] Prove endpoint-only contacts for distinct complete assembled
          incidence routes.
        - [x] Lift endpoint-only contacts to stored routes and all relevant
          periodic translates.
        - [x] Preserve endpoint-only contacts through degree-two contraction,
          including uniqueness of every suppressed splice occurrence.
        - [x] Preserve endpoint-only contacts through the first local
          endpoint-template normalization round.
        - [x] Preserve endpoint-only contacts through the second local
          endpoint-template normalization round.
        - [x] Preserve endpoint-only contacts through the third local
          endpoint-template normalization round.
      - [x] Deduce global assignment collision freedom from the completed
        endpoint-contact certificate.
      - [x] Prove matching ports for the compiled drawing.
      - [x] Transport suppressed 3DM orientations through the normalized
        routed drawing in both directions.
      - [x] Prove the concrete normalized-drawing compiler computable.
      - [x] Assemble the final many-one reductions for both trominoes and
        derive the complete 2D `planeStatement` of Theorem 5.2.
  - [x] Prove PSPACE membership of the 1.5D problem for each tromino under the
    target flat strip encoding.
    - [x] Characterize tilings by directed cycles in the finite strip-frontier
      graph and compile its indexed transition predicate.
    - [x] Compute a polynomial-bit state bound and a sufficient Savitch search
      depth from the periodic-strip input.
    - [x] Implement and verify the flat depth-first Savitch evaluator and its
      exact finite fuel.
    - [x] Bound every reachable Savitch configuration and one complete
      reachability call by a polynomial in the encoded strip length.
    - [x] Fit one complete second-endpoint candidate update, including its raw
      edge test, reverse-reachability query, Boolean accumulation, and rebuilt
      countdown payload, into a uniform polynomial reserve.
    - [x] Lift the candidate-step certificate through the complete
      second-endpoint countdown.
    - [x] Lift the inner scan through the complete first-endpoint countdown.
    - [x] Fit the fixed initialization and result projection around the complete
      nested endpoint scan at the exact frontier-index count.
    - [x] Extend the endpoint and reachability certificates to the padded
      power-of-two state bound used by the compiled unary driver.
    - [x] Fit parameter assembly and the guarded cycle-search driver.
    - [x] Fit the unary input wrapper and package the verified evaluator as a
      PSPACE decision procedure for each tromino under the legacy standard
      `Primcodable` encoding.
    - [x] Reprove the motif-length, period-bit-length, and linear Savitch-depth
      bounds for the target flat strip encoding.
    - [x] Generalize the verified finite-evaluator PSPACE packaging from one
      nested natural code to evaluator-native flat natural fields.
    - [x] Port the structural well-formedness scan to the target flat fields,
      consuming one coordinate pair per iteration without recursive list
      packing.
      - [x] Fit one complete coordinate-pair scanner step compositionally.
      - [x] Lift the step certificate through the exact motif-length countdown.
    - [x] Prove the flat well-formedness scan's evaluator-space certificate.
    - [x] Port the cycle-search input/context assembly and its evaluator-space
      certificates to the target flat strip fields.
      - [x] Prove the generic Savitch structural step and complete iteration
        preserve an arbitrary variable-length context suffix exactly.
      - [x] Compute the variable DFS-stack field count at runtime and recover
        the complete appended flat context by a tail-style dynamic drop.
      - [x] Combine the recovered strip header and coordinate stream with the
        fixed query endpoints, decoding both frontier indices without
        reconstructing the recursively paired motif code.
      - [x] Port the depth-zero strip edge oracle to the recovered flat
        context.
        - [x] Implement one flat coordinate-stream packed-assignment lookup
          pass and prove that it preserves the legacy first-occurrence
          semantics for repeated motif cells.
        - [x] Restore the coordinate stream across all five assignment-column
          passes and prove the resulting `[digit, found]` output matches the
          established packed frontier lookup.
        - [x] Derive flat lookup predicates for absent and fixed assignment
          values, with semantic theorems against packed frontier states.
        - [x] Implement dynamic indexed access to a flat motif cell while
          retaining the complete coordinate stream for nested lookups.
        - [x] Port the one-cell packed normalization predicate to the shared
          indexed flat transition-scan state.
        - [x] Lift indexed normalization through the exact motif-length
          countdown for one complete frontier column.
        - [x] Conjoin the five flat normalization-column passes and recover
          the established packed-state normalization predicate.
        - [x] Port canonical target-cell membership to flat motif fields and
          connect it to center-source containment on well-formed strips.
        - [x] Port one fixed center-placement candidate to flat motif fields,
          retaining the coordinate stream across assignment and containment
          scans.
        - [x] Conjoin all eight fixed center-placement candidates into the
          complete containment predicate for one motif base.
        - [x] Port one fixed center-covering placement query to the flat motif
          stream as the leaf of the exact-one coverage count.
        - [x] Count all 24 fixed covering candidates and decide exact-one
          coverage for one center target from flat motif fields.
        - [x] Add the center-phase guard and combine containment with
          exact-one coverage at one indexed flat motif base.
        - [x] Lift one-base center validity through the exact motif-length
          countdown and recover the full packed center-validity predicate.
        - [x] Compare current and next assignment digits at one shared flat
          motif occurrence.
        - [x] Lift indexed overlap through one exact motif countdown and
          conjoin all four shared-column scans.
        - [x] Compose flat normalization, center validity, cyclic phase
          advance, and overlap into the complete packed transition predicate.
        - [x] Connect the flat transition and reflexive equality test to the
          recovered Savitch context, preserving the native strip suffix.
        - [x] Prove evaluator-space certificates for the flat edge oracle.
          - [x] Fit one coordinate-pair assignment-lookup step
            compositionally.
          - [x] Fit the complete one-column countdown with an exact additive
            evaluator cost.
          - [x] Bound that countdown cost quadratically in the original flat
            motif stream and actual iterator input.
            - [x] Bound every reachable motif suffix, scanner payload, and
              countdown input by one original native-field envelope.
            - [x] Establish compositional budget lemmas for primitive list
              operations, branches, and flat countdown bodies.
            - [x] Bound each positive and zero countdown body by that
              envelope, then sum the exact additive cost.
              - [x] Bound target/current coordinate projections and both
                coordinate equalities.
              - [x] Bound Boolean coordinate matching and the selected-column
                conjunction.
              - [x] Bound packed-word quotient/remainder stepping through the
                certified division-by-nine evaluator.
              - [x] Bound the found/continue state-reconstruction branches
                and both enclosing step selectors.
              - [x] Lift positive, frozen-found, and zero steps through their
                exact countdown bodies.
              - [x] Sum frozen and consuming countdown recurrences into the
                complete one-pass bound.
              - [x] Convert the motif-length factor and affine accumulator
                envelope to a quadratic bound in the actual flat input.
          - [x] Fit the complete five-column assignment lookup with an exact
            additive evaluator cost over native motif fields.
          - [x] Bound the five-column assignment lookup and fit its predicate
            wrappers.
            - [x] Place every reachable one-column scanner call in one common
              five-pass quadratic envelope.
            - [x] Bound selected-column testing, native scanner-input
              reconstruction, and one complete scanner invocation.
            - [x] Bound one complete numbered stage, including output-field
              projection and state reconstruction.
            - [x] Unroll all five stages within the common quadratic envelope.
            - [x] Bound initialization and final projection, then relate the
              complete lookup allowance quadratically to its public native
              input footprint.
            - [x] Fit exact digit, `none`, and fixed-state predicate wrappers.
            - [x] Bound the predicate wrappers in the same quadratic input
              footprint.
          - [x] Fit normalization, center validity, overlap, and the complete
            flat packed transition.
            - [x] Fit and linearly bound runtime suffix selection for dynamic
              flat motif indexing.
            - [x] Fit exact offset construction and coordinate projection for
              dynamic flat motif indexing.
            - [x] Bound dynamic motif indexing on reachable transition scan
              states.
            - [x] Fit the exact one-cell flat normalization predicate.
            - [x] Bound one-cell normalization in the native scan footprint.
            - [x] Lift bounded normalization across the motif.
            - [x] Bound the fixed conjunction of all five normalization
              columns.
            - [x] Fit center assignment and translated source-membership
              leaves on the native flat motif.
            - [x] Fit and bound fixed-symmetry center candidates.
              - [x] Fit the three-source conjunction and containment
                implication.
              - [x] Bound the fixed Boolean composition in the native
                candidate footprint.
            - [x] Fit and bound per-base center validity.
              - [x] Lift containment through the eight square symmetries.
              - [x] Fit and bound exact-one covering placement counts.
                - [x] Fit one reconstructed covering-placement query.
                - [x] Sum the fixed candidate list and compare with one.
              - [x] Combine phase, containment, and coverage at one base.
            - [x] Lift bounded center validity across the motif.
            - [x] Fit and bound one-cell overlap using the two native flat
              assignment lookups.
            - [x] Lift bounded overlap across the motif and four shared
              columns.
            - [x] Fit cyclic phase advance and combine normalization, center
              validity, and overlap into the complete flat transition.
            - [x] Fit exact native-field target construction and membership.
            - [x] Bound target membership in its native input footprint.
              - [x] Bound target-header reconstruction and both coordinate
                constructors.
              - [x] Bound reconstructed lookup input, lookup, and projection.
          - [ ] Fit context recovery and the suffix-preserving Savitch driver,
            then package the flat evaluator as a PSPACE decider.
            - [x] Fit and linearly bound variable-stack offset computation and
              dynamic recovery of the complete flat context suffix.
            - [x] Fit and polynomially bound reconstruction of the native
              seven-field transition context from that recovered suffix.
            - [x] Fit and polynomially bound the recovered indexed edge and
              reflexive-or-edge Savitch base oracle.
            - [x] Fit every control-flow branch of one complete
              suffix-preserving Savitch structural step against a common
              exact cost.
            - [x] Instantiate a sufficient power-of-two state bound and
              Savitch depth from the target flat input length, then bound
              every reachable DFS state, retained strip suffix, and exact
              fuel counter in that representation.
            - [x] Bound the structural-step cost uniformly over every
              reachable native flat state.
            - [x] Lift that uniform bound through the exact-fuel iteration.
            - [x] Assemble and fit the native-suffix reachability request,
              complete exact-fuel call, answer projection, and Boolean
              normalization.
            - [x] Bound the complete reachability wrapper uniformly by the
              target flat input length.
            - [x] Preserve the native strip suffix through both endpoint
              countdowns and prove that the nested scan decides existence of
              a directed frontier cycle.
            - [x] Fit and polynomially bound both native-flat endpoint scans.
              - [x] Fit and uniformly bound one edge/reverse-reachability
                candidate update.
              - [x] Lift that update through the second-endpoint countdown.
              - [x] Fit one complete inner scan.
              - [x] Lift complete row scans through the first-endpoint
                countdown.
            - [x] Assemble the flat well-formedness guard, search parameters,
              and cycle scan into the final PSPACE decider.
              - [x] Stream the exact target-encoding length and compute the
                Savitch depth and padded state bound on native flat fields.
              - [x] Compose the well-formedness guard and cycle scan, and
                prove the resulting Boolean equivalent to strip tileability.
              - [x] Fit and polynomially bound the complete guarded evaluator.
                - [x] Fit the exact streamed target-encoding-length fold in a
                  polynomial reserve over the native flat input footprint.
                - [x] Fit the depth and padded-state-bound parameter pipeline.
                - [x] Fit the well-formedness guard and final cycle-search
                  composition.
                  - [x] Fit every reachable native guard step and countdown
                    body within one input-linear workspace reserve.
                  - [x] Lift the body bound through the full guard loop with
                    an exact reachable-suffix invariant.
                  - [x] Assemble and fit dimension checks, loop input, and
                    final projection into the complete well-formedness guard.
                  - [x] Compose the guard, parameter assembly, and native
                    cycle search into one exact evaluator certificate.
                  - [x] Bound the combined exact cost by one explicit
                    polynomial in the target encoding length.
              - [x] Package the evaluator certificate as flat-encoding PSPACE
                membership.
  - [ ] Prove PSPACE-hardness of the 1.5D problem for each tromino.
    - [x] Prove encoded polynomial-time many-one reductions compose through
      their finite intermediate alphabet.
    - [x] Prove 1D local Periodic CNF SAT PSPACE-hard using cyclic
      polynomial-space computation histories.
      - [x] Define the horizontal CNF fragment and prove its line semantics
        equivalent to the existing plane semantics.
      - [x] Prove that a clocked accepting-reset system has a directed cycle
        exactly when the original deterministic system has a bounded
        accepting trace.
      - [x] Identify forward-local horizontal CNF models with bi-infinite
        paths through their induced Boolean transition relation.
      - [x] Verify constant-size forward-local CNF encodings for constants,
        equality, negation, conjunction, and disjunction.
      - [x] Assemble the gates into a linear-size structural Tseitin compiler
        with fresh-root, exact clause-count, and forward-locality proofs.
      - [x] Prove semantic soundness of the structural compiler: every model
        assigns the root atom the direct expression value.
      - [x] Prove the generated-atom range invariant needed for constructive
        completeness and noninterference between compiled subexpressions.
      - [x] Prove constructive semantic completeness by canonically assigning
        every generated atom while preserving the source valuation.
      - [x] Build verified Boolean-vector expressions for exact-one finite
        fields, current/next equality, and no-overflow binary succession.
      - [x] Allocate a collision-free finite atom vocabulary for bounded
        labels, states, stack cells, and reset-clock bits.
        - [x] Replace width-dependent atom enumeration by an explicit affine
          layout whose only chosen finite codes are fixed by the decider, and
          expose closed arithmetic codes for every constructor and field.
      - [x] Define the canonical Boolean valuation of a bounded clocked
        configuration and verify all label/state/stack exact-one fields.
      - [x] Enforce that every bounded stack is an occupied prefix followed by
        an unused suffix, and verify canonical list encodings satisfy it.
      - [x] Decode every structurally well-formed valuation into a unique
        bounded machine slice and recover every source field bit.
      - [x] Verify fixed-width little-endian clock decoding, no-overflow
        succession, and accepting reset expressions.
      - [x] Reconstruct ordinary TM2 configurations from list-shaped decoded
        slices and prove bounded canonical encodings round-trip exactly.
      - [x] Verify label, control, stack-cell selection, and field-preservation
        expressions against arbitrary decoded one-hot valuations.
      - [x] Normalize atomic push/pop sequences to prepend/drop stack
        transforms and verify their linear-size bounded expressions.
      - [x] Generate finite guarded paths through TM2 statements without
        enumerating stacks, and assemble their bounded step expression.
      - [x] Prove the bounded ordinary-step expression equivalent to Mathlib's
        TM2 step semantics on decoded and canonically encoded configurations.
      - [x] Assemble structural, ordinary-step, clock-successor, and accepting
        reset expressions and prove their reset-clock relation semantics.
      - [x] Force a compiled transition-expression root and identify the
        resulting horizontal CNF models with direct bi-infinite paths.
      - [x] Instantiate the construction for any certified polynomial-space
        decider and prove that its designated-output formula is satisfiable
        exactly on accepted inputs.
      - [x] Encode polynomial-space machine configurations and their local
        clocked transitions as a polynomial-size horizontal CNF formula.
      - [x] Define a flat finite encoding of periodic CNF whose list structure
        has linear overhead, with a verified decoder round trip.
      - [x] Bound the complete flat encoding of the emitted machine formula by
        an explicit polynomial in encoded source-input length.
      - [x] Factor the reduction through a raw source-symbol-list compiler and
        prove agreement with the semantic reduction on valid encodings.
      - [x] Certify the resulting reduction as polynomial-time.
        - [x] Build an exact linear-time finite block transducer and use it to
          encode every arbitrary finite source alphabet as evaluator-native
          delimiter-terminated natural fields.
        - [x] Implement the native-field formula compiler and bound its
          evaluator runtime by an explicit polynomial.
          - [x] Expose a total natural-field compiler interface, prove that
            generated source fields recover the original symbols, and identify
            its native output with the verified flat formula encoding.
          - [x] Compile every Tseitin gate directly to native clause fields and
            prove the streaming field compiler exactly equals the nested CNF
            construction on all inputs.
          - [x] Flatten transition expressions to compact postorder programs,
            verify the one-pass stack interpreter against structural
            compilation, and bound generated requests by an explicit
            polynomial number of native fields.
          - [x] Implement the field-to-formula evaluator and certify its
            polynomial running time.
            - [x] Verify the finite-machine variable-width atom emitter: it
              appends one native binary field, restores its source register,
              and takes exactly two steps per bit plus two.
            - [x] Verify in-place little-endian successor for the fresh-atom
              counter, including exact `trNat` semantics and a linear runtime
              bound.
            - [x] Implement the reusable fixed-field phase emitter and verify
              the complete constant-gate machine script against its native
              field block with an exact linear runtime bound.
            - [x] Verify the shared equality/negation machine script against
              its native two-clause field block, restoring both source
              registers with an exact linear runtime bound.
            - [x] Verify the shared conjunction/disjunction machine script
              against its native three-clause field block, restoring all
              source registers with an exact linear runtime bound.
            - [x] Verify the evaluator's native stack plumbing: delimited
              input/root field transfer, fresh-root pushing, register
              clearing, and final output reversal, all with exact linear
              runtime bounds.
            - [x] Implement the finite compact-instruction decoder and prove
              the exact machine path for every legal constant, wire,
              negation, conjunction, and disjunction tag and payload.
            - [x] Compose decoding, operand-stack reads, native gate emission,
              register cleanup, root replacement, and fresh increment into
              exact linear-time execution theorems for every instruction.
            - [x] Lift instruction execution over complete expression
              postorder programs and prove exact agreement with the direct
              structural compiler's fields, fresh boundary, and unique root.
            - [x] Verify the complete finite-machine wrapper: copy the header,
              read the initial fresh atom, run the postorder compiler, force
              its root, clear internal stacks, reverse output, and halt with
              the exact required-formula native encoding.
            - [x] Bound complete evaluator execution quadratically in its
              bounded native request length and package the machine as a
              `TM2ComputableInPolyTime` compiler.
        - [x] Compose source preprocessing with formula generation into the
          final `TM2ComputableInPolyTime` reduction certificate.
          - [x] Package every decoded source-field list as a bounded compiler
            request and identify its encoded request and compiled output with
            the native frontend definitions.
          - [x] Bound the output length of every polynomial-time `FinTM2` by
            an explicit polynomial using its fixed statement-push allowance.
          - [x] Construct and verify polynomial-time sequential composition
            of two finite multi-stack machines.
          - [x] Assemble the source encoder, an abstract native request
            generator, the quadratic formula evaluator, and semantic
            correctness into the final reduction and PSPACE-hardness theorem;
            isolate request generation as the sole remaining certificate.
          - [x] Generate the bounded compact request directly from finite
            source symbols in polynomial time.
            - [x] Materialize the source decider's fixed space polynomial as
              unary loop padding while preserving the native source stream.
              - [x] Implement the finite Horner machine and prove exact
                source scanning, restoration, and one complete
                multiply-and-add phase.
              - [x] Lift execution across every coefficient, emit the padded
                word, and package its polynomial-time certificate.
              - [x] Specialize the coefficient list to the reduction's exact
                stack-width polynomial and prove that native delimiter count
                agrees with source-field count.
            - [x] Materialize the affine reset-clock width as a second unary
              marker block and compose both padding phases in polynomial time.
            - [x] Materialize the exact source-atom boundary used as the
              request's first fresh Tseitin atom as a third marker block.
            - [x] Verify a quadratic finite machine that preserves a word and
              converts any selected unary marker class to canonical native
              binary.
            - [x] Specialize and compose that converter for the stack, clock,
              and fresh blocks, preserving their tagged separation.
            - [x] Prepare direct finite-source input for the request printer.
              - [x] Retain each original finite source symbol behind an
                always-inhabited option tag, including for empty source
                alphabets.
              - [x] Append the exact unary and canonical binary space, clock,
                and fresh values, and certify the complete pipeline in
                polynomial time.
              - [x] Flatten the prepared nested-sum word into seven tagged
                blocks and prove exact recovery of the source, unary counters,
                binary fields, and normalized token-request specification.
            - [x] Stream the normalized bounded-expression postorder program.
              - [x] Mirror conjunction, disjunction, equality, exact-one,
                vector equality, and binary successor directly on instruction
                lists, and prove exact agreement with expression postorder.
              - [x] Normalize bounded-machine fields, configurations, clocks,
                statement paths, and the designated reset relation.
                - [x] Normalize affine label, control, stack-cell, complete
                  configuration, and reset-clock programs.
                - [x] Normalize one-hot and stack-suffix well-formedness.
                - [x] Normalize bounded push/pop stack transformations.
                - [x] Normalize symbolic statement paths and assemble the
                  designated accepting-reset program.
              - [x] Implement the finite counter-driven instruction emitter.
                - [x] Factor compact instructions, arbitrary wire atoms, and
                  the fresh header into a finite token alphabet whose fixed
                  block expansion is exactly the evaluator-native request.
                - [x] Mark every emitted instruction by its exact Tseitin
                  clause weight and materialize the total clause count in
                  canonical binary with the verified padding machine.
                - [x] Rotate the counted suffix into the native request
                  header, insert its delimiter, expand every finite token,
                  and verify the finalizer in linear time.
                - [x] Verify a finite polynomial-time machine that converts
                  delimiter-terminated unary fields into the evaluator's
                  canonical native natural-number fields.
                - [x] Factor the concrete emitter target through an all-unary
                  finite token stream, prove its exact expansion to normalized
                  fields, and append its exact unary clause count in
                  polynomial time.
                - [x] Rotate that unary clause-count suffix to the request
                  header, expand the retained tokens, and compose both passes
                  into one verified polynomial-time postprocessor.
                - [x] Reduce the concrete printer input from seven prepared
                  blocks to source symbols plus unary space, clock, and fresh
                  blocks, with exact recovery and polynomial-time preparation.
                - [x] Verify the reusable finite-control position loop that
                  retains its input and emits fixed templates whose unary atom
                  fields have length `base + stride × position`.
                - [x] Bound that affine emitter's output and complete halted
                  execution quadratically and package its polynomial-time
                  certificate for later machine composition.
                - [x] Lift affine atom recipes to a compositional postorder
                  language and prove exact unary-token agreement for Boolean
                  operators, vector equality, exactly-one, and succession.
                - [x] Instantiate affine programs for shifted bounded-stack
                  cells, exact-one fields, vector equality, and every
                  nonterminal occupied-prefix constraint.
                - [x] Compose any fixed list of affine appenders over one
                  stable prepared-symbol/token alphabet, preserving selector
                  counts and extracting the exact token suffix in polynomial time.
                - [x] Lift capped-prefix affine phase lists to input-preserving
                  marked workspace passes, retaining every earlier token and
                  removing the temporary tags in polynomial time.
                - [x] Prove token append/fold identities for normalized finite
                  conjunctions and disjunctions and identify affine ranges
                  with their per-position ordinary program streams.
                - [x] Verify a finite-state prefix marker that retains the
                  prepared word and tags each symbol by its capped number of
                  earlier selected symbols, enabling fixed boundary skips.
                - [x] Prove that every fixed tagged-prefix selector has count
                  `selectedCount − skip` and certify the marker's linear
                  polynomial-time execution.
                - [x] Assemble fixed and affine phases whose exact output is
                  the complete normalized one-hot program for every bounded
                  stack and represented position.
                - [x] Use the `space − 1` prefix selector and terminal boundary
                  phases to emit the exact occupied-prefix program and complete
                  normalized structural well-formedness block.
                - [x] Split every fixed stack into its literal occupied prefix
                  and affine `none` tail, and emit exact current/next complete
                  configuration tests whenever the fixed endpoint fits.
                - [x] Fix the prefix cutoff to the canonical accepting
                  configuration and connect its endpoint phases to the actual
                  prepared unary space block.
                - [x] Compose accepting-prefix marking with the fixed affine
                  phases and certify exact current/next endpoint emission in
                  polynomial time.
                - [x] Lift accepting-endpoint emission to the shared workspace,
                  preserving prepared data and every earlier token exactly.
                - [x] Specialize one-symbol prefix marking to the prepared
                  space block and certify exact polynomial-time emission of
                  the complete structural well-formedness program.
                - [x] Lift structural well-formedness emission to the shared
                  workspace while preserving prepared data and prior tokens.
                - [x] Define bivariate affine atom recipes and normalized
                  Boolean programs for fields depending on both a runtime
                  width and an iteration position.
                - [x] Verify the finite two-counter template emitter, including
                  exact context/position rescans, counter restoration, work
                  stack cleanup, output reversal, and genuine halting.
                - [x] Bound two-counter output and execution quadratically and
                  package the emitter as a polynomial-time TM2 computation.
                - [x] Identify every bivariate emitted position range with the
                  exact evaluated postorder-program token stream.
                - [x] Instantiate the exact bivariate clock-atom layout and
                  recover the normalized reset-clock token word.
                - [x] Compose bivariate reset operands with affine conjunction
                  closers into an exact polynomial-time clock-reset emitter.
                - [x] Prove both clock-reset passes preserve the shared
                  prepared workspace and every earlier token prefix.
                - [x] Flatten normalized binary succession into outer frames,
                  triangular equality operands, and its exact unwind suffix.
                - [x] Specialize rise, fall, and equality frames to runtime
                  clock atoms and state the exact triangular token recursion.
                - [x] Factor that recursion into a finite generic triangular
                  recipe contract for the successor emitter machine.
                - [x] Define the finite triangular emitter's counters, control
                  states, and complete transition program.
                - [x] Isolate its invariant configurations, stack-update
                  algebra, and generic token-push execution identities.
                - [x] Verify input retention and both selector counts through
                  the complete linear scan phase.
                - [x] Verify every atom's persistent-counter scan/restoration
                  and the held-current offset of inner templates.
                - [x] Verify the completed-outer counter scan/restoration and
                  its stage-specific continuation.
                - [x] Verify the processed-inner counter scan/restoration and
                  exact advancement of inner recipes.
                - [x] Verify fixed-token and affine-atom recipe entry steps.
                - [x] Compose complete outer-stage recipe execution with exact
                  token output, counter restoration, and runtime.
                - [x] Compose complete inner-stage recipe execution across all
                  three counters with exact output and runtime.
                - [x] Lift complete non-inner recipe execution over both outer
                  template lists, preserving counters and exact token order.
                - [x] Lift the three-counter recipe execution over the full
                  inner template at every triangular equality position.
                - [x] Execute one complete higher inner position, including
                  empty templates and exact marker transfer between counters.
                - [x] Lift that iteration over the complete strictly-higher
                  range with exact consecutive-position token output.
                - [x] Restore the higher range while emitting the exact inner
                  base, per-position closers, and frame closer.
                - [x] Package both possibly empty outer templates behind one
                  exact full-stage execution theorem.
                - [x] Compose one complete triangular outer frame from marker
                  selection through both templates and the full inner fold.
                - [x] Lift complete frames over every selected outer position,
                  with the exact triangular frame-prefix token stream.
                - [x] Emit the final base and unwind every completed frame with
                  one exact final-closer block per outer position.
                - [x] Clear the persistent counter, reverse the accumulated
                  workspace exactly, and prove genuine machine halting.
                - [x] Compose scanning, all triangular frames, final folding,
                  cleanup, and reversal into exact whole-machine semantics.
                - [x] Bound template, inner-range, frame, and complete
                  frame-range output and runtime by fixed cubic-scale forms.
                - [x] Bound exact total execution by a fixed cubic polynomial
                  and package the emitter as polynomial-time TM2 computation.
                - [x] Specialize the triangular machine to the clock templates
                  and recover the exact normalized successor program.
                - [x] Prove triangular clock-successor emission preserves the
                  shared prepared workspace and every earlier token prefix.
                - [x] Compose structural well-formedness, the current accepting
                  endpoint, and clock reset into the exact polynomial-time
                  normalized-program prefix before the next-initial endpoint.
                - [x] Decompose the source-dependent next-initial endpoint into
                  its ordered decoded-source prefix, indexed empty tails, and
                  exact nested postorder conjunction schedule.
                - [x] Materialize the input stack's polynomial-length empty
                  tail as an exact unary marker block while preserving the
                  shared workspace and earlier tokens.
                - [x] Specify data-indexed affine emission, where each selected
                  input item chooses its finite recipe and advances one exact
                  selected-position counter.
                - [x] Specialize indexed recipes to decoded input-stack cells
                  and recover the exact source-prefix tokens while ignoring all
                  prepared markers, earlier tokens, and tail padding.
                - [x] Define the finite indexed-template emitter's stacks and
                  control flow for online data-dependent recipes, unary position
                  rescans, and input-before-token output reversal.
                - [x] Name every indexed-emitter invariant configuration and
                  prove exact dependent-stack update identities for its later
                  small-step verification.
                - [x] Verify indexed-emitter input retention and optional recipe
                  dispatch, including selected empty recipes and exact position
                  advancement.
                - [x] Verify indexed fixed-token and affine-atom recipe entry,
                  including arbitrary reverse-token pushes and base atom runs.
                - [x] Verify affine-atom position rescanning and exact restoration
                  of the indexed emitter's unary processed-position counter.
                - [x] Compose one complete indexed fixed or affine recipe with
                  exact semantic token output, restored counters, and runtime.
                - [x] Lift indexed recipe execution across one selected item's
                  complete template, append exact `positionTokens`, and advance
                  the selected-position counter once.
                - [x] Lift indexed item execution across the complete input,
                  retaining exact input order and accumulating the exact
                  data-indexed token word and selected-position count.
                - [x] Clear the indexed position counter, reverse tokens and
                  retained input in the required order, and prove genuine
                  halted cleanup with exact output.
                - [x] Compose indexed scanning, data-dependent template
                  execution, and cleanup from initialized input to genuine
                  halting with exact appended output and runtime.
                - [x] Bound indexed-family recipe size, emitted token length,
                  and exact scan runtime by fixed quadratic-scale forms over
                  the complete input length.
                - [x] Package indexed data-dependent template emission as a
                  quadratic polynomial-time TM2 computation with exact
                  retained-input-plus-token output.
                - [x] Compose polynomial initial-tail materialization with the
                  indexed decoded-source emitter, flattening the workspace
                  while preserving every earlier token and exact source word.
                - [x] Define the two-counter affine empty-cell template for the
                  input stack and prove its complete range equals the exact
                  `sourceLength + offset` initial-tail schedule.
                - [x] Verify exact source and tail counts on the mixed retained
                  workspace, run the bivariate input-tail emitter, and compose
                  it polynomially after source-prefix emission.
                - [x] Verify a reusable two-pass affine empty-stack emitter:
                  all `none` cell operands, the constant-true base, and every
                  conjunction closer, preserving an arbitrary mixed workspace.
                - [x] Split the fixed finite stack enumeration exactly as
                  `before ++ [k₀] ++ after`, proving both side lists exclude
                  `k₀` and stack-token flat maps preserve this order.
                - [x] Lift empty-stack emission over any fixed stack list,
                  preserving the selected width and appending the exact
                  stack-order flat map in polynomial time.
                - [x] Verify a reusable polynomial-time `all`-fold ending pass
                  that appends the true base followed by one conjunction
                  closer per selected operand.
                - [x] Identify the prepared `space` count across the workspace
                  type change and prove every input and non-input emitted word
                  equals its exact initial `stackSchedule`.
                - [x] Assemble label/control fields, all stacks in exact finite
                  order, and configuration closers into a polynomial-time pass
                  whose extracted suffix is exactly the full initial schedule.
                - [x] Prove the initial label/control prefix is source
                  independent and expose one fixed initial-stack schedule
                  machine valid for every prepared source word.
                - [x] Compose well-formedness, accepting-current, clock reset,
                  and next-initial emission, then close both conjunctions to
                  obtain the complete polynomial-time designated reset prefix.
                - [x] Lift accepting-current and clock-successor emission to
                  the expanded post-reset workspace, with exact selected-count
                  interfaces and polynomial-time certificates.
                - [x] Decompose the stable workspace after complete reset
                  emission and prove it preserves the exact unary space and
                  clock widths required by the ordinary branch.
                - [x] Compose accepting-current, negation, and clock-successor
                  emission into the exact polynomial-time ordinary-branch
                  prefix immediately before the machine-step program.
                - [x] Build a generic polynomial-time padding pass that adds
                  and later removes constant-many temporary data markers while
                  preserving every retained symbol and formula token exactly.
                - [x] Wrap fixed-marker padding around the bivariate emitter,
                  yielding a polynomial-time pass for fixed-many templates
                  whose atoms depend affinely on the runtime stack width.
                - [x] Prove exact selected counts for fixed prefixes and
                  half-open intervals in prefix-marked unary data, enabling
                  runtime-width boundary and tail schedules.
                - [x] Specialize marked intervals to a fixed occurrence,
                  proving its selector count is exactly the corresponding
                  runtime-bound comparison bit.
                - [x] Prove the prefix marker's final capped control count is
                  exactly `min(selectedCount, cutoff)`, enabling one-sentinel
                  branching on fixed runtime-width thresholds.
                - [x] Verify complementary one-sentinel selectors whose exact
                  counts distinguish widths below a fixed cutoff from widths
                  at or above it.
                - [x] Turn either sentinel comparison bit into an exact
                  zero-or-one bivariate program emission, returning to the
                  original workspace in polynomial time.
                - [x] Verify a prefix-marked bivariate wrapper that exposes
                  two tagged interval counts to affine templates while
                  preserving and untagging the shared workspace.
                - [x] Instantiate bivariate stack-cell and optional-cell
                  equality templates at `fixedOffset + first + position`,
                  with exact normalized token-range identities.
                - [x] Emit every represented pushed cell and every shifted
                  source/target equality in one stack transform using marked
                  zero-or-one prefix phases and an affine interior phase.
                - [x] Append the source-out-of-range `none` tail with marked
                  bivariate interval counts, completing a polynomial-time
                  emitter for all transformed stack-cell operands.
                - [x] Split the represented stack range at the pushed-prefix
                  and source-validity boundaries, proving the three emitted
                  cell blocks exactly equal normalized `stackTransformCell`.
                - [x] Emit the normalized stack-transform fit operand by
                  complementary width-threshold branches, including the exact
                  first omitted-cell test, in polynomial time.
                - [x] Compose the fit operand, represented-cell schedule,
                  `all` ending, and final conjunction into the exact complete
                  normalized stack-transform program in polynomial time.
                - [x] Iterate complete normalized transforms over any fixed
                  dependent stack list, preserving the runtime width and exact
                  stack order in polynomial time.
                - [x] Close the canonical finite stack family with its fixed
                  `all` ending, yielding the exact stack program of a terminal
                  symbolic statement path.
                - [x] Surround a terminal path's stack program with its guard,
                  next label/control operands, and four-input `all` ending to
                  emit the exact complete path program in polynomial time.
                - [x] Iterate any fixed terminal-path list and append its
                  `any` ending, obtaining the exact normalized path
                  disjunction in polynomial time.
                - [x] Prove program-valued symbolic statement paths stabilize
                  above the fixed observation-depth cutoff, and equal their
                  construction at the runtime width capped by that cutoff.
                - [x] Build a generic polynomial-time capped-regime wrapper
                  that makes an arbitrary input-preserving token emitter an
                  exact conditional no-op outside one selected width regime.
                - [x] Dispatch over all fixed capped-width regimes and retain
                  the unique active terminal-path disjunction, proving exact
                  runtime `statementPathsProgram` emission in polynomial time.
                - [x] Fold runtime path disjunctions over every fixed control
                  value with current-control guards and an `any` ending,
                  yielding exact `statementProgram` emission.
                - [x] Fold exact statement programs over every fixed live
                  label with current-label guards and an `any` ending, yielding
                  the complete normalized `machineStep` program.
                - [x] Append the exact machine-step program and both fixed
                  conjunction closers to the ordinary prefix, yielding the
                  complete normalized ordinary branch in polynomial time.
                - [x] Propagate the fixed initial-stack interface through the
                  reset and ordinary branches, obtaining one source-uniform
                  polynomial-time emitter for all prepared inputs.
                - [x] Emit the exact unary fresh-atom header and forced-root
                  clause marker while preserving the prepared source word.
                - [x] Compose the fresh header, complete reset and ordinary
                  branches, and outer Boolean closers into one source-uniform
                  polynomial-time machine whose extracted output is exactly
                  the normalized finite-token compact request.
    - [ ] Transport 1D PSPACE-hardness through the bounded-occurrence planar
      trichromatic-orientation reductions.
      - [x] Guard arbitrary source presentations and normalize valid local 1D
        CNF to nonempty local 3SAT-3 with exactly preserved semantics.
      - [x] Prove the executable admissibility guard and complete guarded
        source-formula normalization primitive recursive.
      - [x] Compute the resulting finite planar 3DM problem without proof
        arguments and identify it with the semantic reduction endpoint.
      - [x] Prove route refinement, unit subdivision, and selection of the
        inserted polarity-normalization vertices primitive recursive.
      - [x] Prove the refined placement, raw inserted positions, and final
        fresh-variable gauge primitive recursive.
      - [x] Lift polarity normalization to a primitive-recursive positioned
        formula from its complement-clause position query.
      - [x] Compose source refinement, route-selected complement positions,
        and fresh-variable gauging into the exact positioned routed formula.
      - [x] Prove the positioned polarity-normalization placement period and
        pointwise variable positions primitive recursive.
      - [x] Specialize that placement to route-selected fresh vertices and
        prove its final gauged period and positions primitive recursive.
      - [x] Give flattened positioned polarity-normalization clause origins
        and source metadata canonical primitive-recursive encodings.
      - [x] Compute the complete flattened source/origin metadata list in
        exact parallel with the generated positioned clauses.
      - [x] Compute the retained, shortened, and two translated split-route
        branches selected by each generated incidence's origin metadata.
      - [x] Compute the complete metadata-indexed raw incidence-route family
        and its final whole-period transport through the fresh-variable gauge.
      - [x] Specialize route computability through the retained final clause
        sort, canonical gauge, and routed-polarity formula/placement/routes.
      - [x] Compose the proof-free routed formula, complete placement, and
        routed incidence family with the guarded concrete strip source.
      - [x] Identify all three concrete executable routed objects with the
        corresponding retained semantic terms used by the 3DM encoder.
      - [x] Compute the padded three-strand drawing period and stored grid
        predecessor, and identify both with the semantic presentation.
      - [x] Compute the doubled, clause-anchor-normalized positioned formula
        that indexes the typed 3DM drawing assembly.
      - [x] Compute the doubled variable-macrocell origins and normalized
        clause-macrocell origins used by the three-strand assembly.
      - [x] Factor assembled vertex positions through proof-free origins and
        compute every concrete typed-triple position.
      - [x] Compute every concrete assembled red-element position from finite
        cycle, fixed-red, and clause-core tables.
      - [x] Compute every concrete assembled green-element position, including
        source-kind- and polarity-selected ordinary internals.
      - [x] Compute every concrete assembled blue-element position, including
        ordinary, fixed-red, clause-core, and clause-terminal branches.
      - [x] Enumerate the complete assembled vertex-position list, prove it
        primitive recursive, and identify it with the generic data assembly.
      - [x] Give the finite variable- and clause-fan configurations canonical
        encodings, totalize the proof-indexed variable-site route, and prove
        the local clause-core and both coordinated endpoint-fan route tables
        primitive recursive.
      - [x] Prove the reusable macrocell ribbon-corridor assembler primitive
        recursive via a proof-free right fold.
      - [x] Compute each horizontal occurrence's normalized, doubled, reversed,
        and periodically rebased source route primitive recursively.
      - [x] Identify proof-free occurrence rebasing with the choice-backed
        semantic source route on every active occurrence.
      - [x] Unit-subdivide each executable occurrence route, compute its two
        endpoint directions, and identify all three values with the semantic
        coordinated-ribbon inputs.
      - [x] Compute each normalized source variable's finite ribbon-fan count,
        connector kinds, polarities, and endpoint directions, decode the
        complete fan record, and identify it with the semantic fan data.
      - [x] Instantiate the finite coordinated variable-fan route table from
        each computed fan record and identify every colored local route with
        its semantic counterpart.
      - [x] Enumerate each normalized clause orbit's active occurrences,
        compute its finite terminal activity and endpoint directions, decode
        the complete clause-fan record, and identify it with the semantic fan.
      - [x] Compute each occurrence's clause orbit, terminal group, and
        group-dependent physical lane, instantiate the coordinated clause-fan
        route table, and identify the local route with its semantic counterpart.
      - [x] Translate both endpoint fans to their computed macrocells, assemble
        the central ribbon corridor and complete colored occurrence route
        primitive recursively, and identify it with the certified coordinated
        routing field.
      - [x] Enumerate every normalized active occurrence in stable RGB order,
        compute the complete finite occurrence-route table primitive
        recursively, and identify it with the certified routing enumeration.
      - [x] Prove width splitting, occurrence splitting, and the guarded
        fallback preserve zero vertical literal offsets.
      - [x] Lift one-dimensionality to the source incidence graph by proving
        every clause-anchored graph edge has zero vertical lattice offset.
      - [x] Prove every route point in the canonical track drawing of a local
        zero-vertical-offset graph lies strictly inside its vertical period.
      - [x] Deduce that both segment occurrences at every canonical crossing
        of that drawing have zero vertical period translation.
      - [x] Extend the crossing invariant to the physical halo: both segment
        translations equal the crossing point's common vertical period shift.
      - [x] Prove an anchor-normalized equality family is one dimensional
        whenever each physical link's endpoints have equal vertical shifts.
      - [x] Prove clausewise literal maps preserve one-dimensionality whenever
        they preserve each literal's vertical offset.
      - [x] Prove concatenation and clause deduplication preserve the
        one-dimensional fragment.
      - [x] Prove opaque planar-SAT variable wrapping preserves every literal
        offset and hence one-dimensionality.
      - [x] Apply the equality invariant to every route-bend link and its
        embedded normalized planar-SAT clause family.
      - [x] Prove every anchor-normalized crossover template literal has zero
        offset after removing its physical site's common periodic shift.
      - [x] Relate each retained carrier node's normalization shift to its
        supporting segment translate and equate both endpoints of every link.
      - [x] Lift equal retained-carrier endpoint shifts through the complete
        anchor-normalized equality-clause family.
      - [x] Prove the carrier-to-planar-SAT atom embedding preserves every
        normalized clause's one-dimensionality.
      - [x] Apply the embedding invariant to the typed retained-carrier
        component without unfolding its physical link enumeration.
      - [x] Prove anchor normalization sends every routed original-clause
        literal to its explicit zero-offset terminal prototype.
      - [x] Prove every normalized routed variable arm retains exactly its
        source incidence edge offset, hence is horizontal for a 1D source.
      - [x] Assemble the five retained anchor-normalized planar-SAT clause
        families and prove the complete formula remains one dimensional.
      - [x] Prove every valid retained planar-SAT variable has zero vertical
        canonical-position gauge for a horizontal source incidence graph.
      - [x] Apply that gauge certificate to every variable occurrence after
        opaque wrapping of the raw retained formula.
      - [x] Prove a zero-vertical variable gauge preserves
        one-dimensionality after clause-anchor normalization.
      - [x] Prove ordinary clause-anchor normalization and zero-vertical
        variable gauging each preserve one-dimensionality directly.
      - [x] Transport the retained formula's one-dimensionality through
        opaque wrapping, canonical variable gauging, and anchor normalization.
      - [x] Prove positioned literal-list deduplication preserves
        one-dimensionality after erasing positions.
      - [x] Apply positioned deduplication to the final wrapped, gauged, and
        anchor-normalized retained planar-SAT formula.
      - [x] Prove fixed-eight occurrence splitting preserves
        one-dimensionality for every compass-port assignment.
      - [x] Prove Figure 9 exact-one conversion preserves
        one-dimensionality through inherited offsets and clause anchors.
      - [x] Prove exact-one unit elimination preserves one-dimensionality for
        empty, unit, and nonunit source clauses.
      - [x] Prove logical polarity normalization preserves every source
        occurrence's periodic offset.
      - [x] Prove the routed fresh-complement gauge makes fresh offsets zero
        while retaining horizontal embedded-original offsets.
      - [x] Transport one-dimensionality through the actual routed polarity
        formula's anchor normalization, physical refinement, and fresh gauge.
      - [x] Define one-dimensional periodic 3DM and prove typed Figure 10
        construction plus finite-index encoding preserve it.
      - [x] Prove the richer planar Figure 10 assembly's ordinary, fixed-red,
        clause-core, and encoded references remain horizontal.
      - [x] Apply planar 3DM horizontality to the exact anchor-normalized
        positioned source consumed by the geometric assembly.
      - [x] Prove stable route-direction ordering preserves every literal's
        vertical offset in a positioned periodic CNF.
      - [x] Carry the concrete retained formula through fixed-eight splitting,
        clockwise clause ordering, and Figure 9 clearance scaling.
      - [x] Carry the concrete Figure 9 output through unit elimination and
        its final stable clause-direction ordering.
      - [x] Prove every occurring final canonical position gauge has zero
        vertical component and preserve one-dimensionality through it.
      - [x] Instantiate normalized planar Figure 10 on the twice-scaled final
        gauged source and prove all colored references remain horizontal.
      - [x] Instantiate the retained planar-SAT, exact-one, planar-3DM, and
        orthogonal-normalization pipeline, proving the output drawing is
        well formed, vertex separated, and semantically exact.
    - [ ] Compile the normalized periodic drawing into a polynomial-height
      strip drawing.
      - [x] Define the open three-period vertical halo and prove that a
        shift/reflection maps it strictly between blank raster boundaries.
      - [x] Prove every genuine 3DM incidence and every emitted contracted
        edge has zero vertical period offset for a one-dimensional instance.
      - [x] Prove horizontal degree-two contraction preserves the open
        vertical halo for every stored route point.
      - [x] Prove the common affine magnification, center translation, and
        unit-subdivision stage preserves the open vertical halo.
      - [x] Prove Figure 2 and cyclic endpoint templates, trimming, reversal,
        and endpoint splicing preserve the enlarged open vertical halo.
      - [x] Apply the Figure 2 splice to every contracted edge and prove the
        complete first normalization-round drawing stays in the halo.
      - [x] Apply the first cyclic splice to every round-1 edge and prove the
        complete second normalization-round drawing stays in the halo.
      - [x] Apply the second cyclic splice and identify its scale-12 period,
        proving every final normalized route point stays in the halo.
      - [x] Define the rectangular strip rasterizer of width `P` and height
        `3P + 1`, with geometric row map `y ↦ 2P - y`.
      - [x] Factor the complete rectangular rasterizer through a finite,
        proof-free compiler input and identify it definitionally with the
        verified presentation-level strip drawing.
      - [x] Prove the proof-free rectangular compiler primitive recursive,
        from reflected route assignments through prioritized lookup and the
        complete row-major cell array.
      - [x] Prove the exact rectangular cell count and bound the compiled
        target's complete flat encoding by an explicit polynomial in the
        final normalization period.
      - [x] Bound the guarded 3CNF and occurrence-splitting presentation
        sizes, trace every fixed geometric period multiplier, and thereby
        bound the complete target flat encoding by an explicit polynomial
        in the source flat-encoding length, packaged as a concrete
        `Polynomial Nat`.
      - [x] Prove every generated vertex and route cell occupies a strict
        interior row and both wraparound boundary rows are blank.
      - [x] Prove the rectangular raster preserves the normalized drawing's
        assignment collision freedom, and instantiate it from the final
        endpoint-contact certificate.
      - [x] Prove exact strip lookup for every listed normalized vertex and
        route-interior assignment under that collision certificate.
      - [x] Prove finite strip neighbors of strict-interior assignments agree
        with reflected geometric unit steps and cannot wrap across a seam.
      - [x] Prove strip lookup recovers every displayed route triple and that
        consecutive routing cells expose matching colored ports.
      - [x] Match each normalized source vertex to its first strip routing
        cell with the correct endpoint color.
      - [x] Match each normalized target vertex to its last strip routing
        cell at the routed periodic target occurrence.
      - [x] Prove one-dimensional contracted offsets identify each routed
        target occurrence with its base target in the rectangular raster.
      - [x] Recover the unique displayed route triple and owning contracted
        edge behind every emitted strip route assignment.
      - [x] Prove every exposed port of a strip route cell matches its
        predecessor or successor, including both endpoint boundary windows.
      - [x] Classify every nonblank strip lookup result and prove each exposed
        colored port matches the opposite port of its finite neighbor.
      - [x] Lift lookup-level port matching and vertex isolation to the
        packaged rectangular drawing interfaces.
      - [x] Prove the concrete normalized rectangular strip drawing is well
        formed, including equality of unused ports in both directions.
      - [x] Prove degree-three vertex cells remain nonadjacent in the
        rectangular strip by transfer to the coarse-lattice torus theorem.
      - [x] Attach exact vertex/route provenance to every nonblank strip cell
        and prove collision-free provenance lookup erases to its cell type.
      - [x] Lift finite strip provenance to arbitrary cells of the infinite
        rectangular drawing and identify successful and blank lookups.
      - [x] Characterize equality of finite strip representatives by unique
        translations through the positive strip width and height.
      - [x] Reconstruct the unique rectangular block occurrence behind every
        successful infinite-lift provenance lookup.
      - [x] Prove the square and rectangular rasterizers enumerate identical
        orientation provenance values despite using different location keys.
      - [x] Define the suppressed-orientation-induced infinite strip
        orientation and prove every local cell constraint.
      - [x] Evaluate that orientation at explicit strip-block occurrences and
        commute geometric unit steps with rectangular block translations.
      - [x] Prove membership constructors for every listed strip vertex site
        and every displayed route-triple site.
      - [x] Prove the forward strip orientation assigns complementary values
        across every source-vertex/first-route-cell boundary.
      - [x] Reconcile horizontal contracted target offsets with strip-block
        translations and orient every target boundary compatibly.
      - [x] Prove consecutive internal strip route cells receive
        complementary values on their shared port in every block occurrence.
      - [x] Dispatch every exposed strip vertex port through its unique
        source or translated-target endpoint compatibility theorem.
      - [x] Classify every exposed strip route port and dispatch its source,
        internal-window, or target-boundary compatibility theorem.
      - [x] Lift finite strip-site port compatibility through provenance
        reconstruction to every exposed port of the infinite strip drawing.
      - [x] Package the induced strip assignment as a valid global drawing
        orientation whenever the suppressed 3DM orientation is valid.
      - [x] Read contracted endpoint values from any valid strip orientation
        and prove all endpoint ports at a translated triple agree.
      - [x] Prove the graph assignment extracted from a valid strip
        orientation is coherent at every translated triple.
      - [x] Prove reverse orientation transport preserves the forward-facing
        value across one internal strip route cell.
      - [x] Iterate reverse value transport from any displayed strip route
        pair through the fixed final pair.
      - [x] Identify strip route values with their source endpoint and the
        complement of their translated target endpoint.
      - [x] Prove every complete contracted strip route gives unequal inward
        values at its two endpoint occurrences.
      - [x] Identify extracted strip tag values at retained and through edges
        with the corresponding contracted endpoint values.
      - [x] Transfer the local monochromatic strip vertex rule to exact-one
        among the three retained endpoint values.
      - [x] Prove degree-two and degree-three element constraints and package
        strip-orientation readback as a valid suppressed 3DM orientation.
      - [x] Conclude the normalized rectangular strip drawing is orientable
        exactly when the original periodic 3DM instance is satisfiable.
      - [x] Prove the concrete retained polarity-normalized 3DM target remains
        one dimensional and its presentation stays inside the raster halo.
      - [x] Instantiate the rectangular compiler for guarded local periodic
        CNF, proving well-formedness, vertex separation, blank vertical
        boundary, and exact source-orientation semantics.
    - [ ] Specialize the tromino gadget substitution to that strip drawing and
      assemble the polynomial-time reductions for both trominoes.
      - [x] Identify the concrete verified strip drawing with the proof-free
        rectangular compiler, define the actual gadget-substituted target
        instance, and prove its exact tiling semantics for either tromino.
      - [x] Package any finite normalized drawing domain as a horizontally
        periodic expanded tromino strip, prove its presentation well formed,
        characterize its carrier exactly, and prove the construction
        computable.
      - [x] Prove the doubly periodic gadget carrier is the disjoint vertical
        stack of its strip carriers and that any strip tiling repeats to a
        plane tiling, giving the unconditional soundness direction.
        - [x] Identify the base strip carrier exactly with the plane carrier
          intersected by one half-open expanded vertical-period band.
      - [x] Restrict the footprint atlas to the finite vertical block band and
        prove locally tiled, port-compatible, vertically closed assignments
        glue to an exact tiling of the compiled strip.
      - [x] Prove blank first and last drawing rows force vertical closure, so
        compatible local gadget states tile the compiled strip.
      - [x] Prove exact strip-substitution correctness for normalized,
        vertex-separated drawings with blank vertical boundary rows.
      - [x] Package the remaining local-CNF drawing compiler contract and
        prove it composes with 1D PSPACE-hardness and both tromino gadgets.
      - [x] Prove ordinary computability and polynomial output length for the
        exact semantic local-CNF-to-tromino-strip compiler.
      - [x] Bypass malformed general CNF inputs by packaging hardness directly
        from the bounded formulas generated by the PSPACE source reduction.
      - [x] Reduce the remaining direct machine certificate to a raw-symbol
        emitter of unary natural-number fields, followed by the verified
        unary-to-native binary field encoder.
      - [x] Identify the semantic target fields with a shallow proof-free
        generator using natural-range raster and fixed-gadget pixel loops.
      - [ ] Implement and verify the direct unary field emitter for the
        bounded PSPACE-generated formula templates.
        - [x] Specify the counted-header permutation and verify every
          transition of its fixed four-stack finite machine.
        - [x] Prove exact executions for all six scan, emit, copy, and output
          reversal phases on arbitrary unary streams.
        - [x] Prove the header-rotation machine's complete exact run and
          linear polynomial-time certificate.
        - [x] Stream one counted finite block per motif cell, interleaving its
          marker with its coordinate fields, then compose the verified
          postprocessors to obtain the exact executable unary field stream.
        - [x] Replace gadget-coordinate arithmetic by a finite prepared-token
          alphabet: fixed block expansion turns each horizontal or vertical
          index unit and bounded local offset into the exact encoded pixel
          coordinate, with a polynomial-time transducer certificate.
        - [x] Derive exact clause, literal, variable, and incidence-drawing
          sizes for the bounded PSPACE source, reducing its orthocrossing grid
          size to a fixed weighted count of transition-program instructions.
        - [x] Expand the existing finite request-token stream into exactly one
          unary marker per orthocrossing grid unit with a fixed block
          transducer and polynomial-time certificate.
        - [x] Feed that exact unary scale through the prepared-header machine,
          proving that it emits the compiled strip's precise `3P+1` height and
          `P` width fields in polynomial time.
        - [x] Replace the blank-heavy complete normalization raster by the
          collision-free assignment-order motif, proving identical carrier,
          well-formedness, and tiling semantics for both trominoes.
        - [x] Define the sparse motif's finite prepared-pixel stream and prove
          that fixed expansion, marker counting, header rotation, and binary
          field encoding recover the exact sparse flat strip.
        - [x] Rewrite compact affine vertex requests as one indexed triple
          scan and three degree-filtered color scans, and prove that four
          retained-input appenders compose into the exact request appender.
        - [x] Materialize the assembled 3DM drawing's exact grid size as a
          unary stream by fixed expansion of the direct source-grid markers,
          with a polynomial-time machine certificate.
        - [x] Bridge each numeric color-list degree test to the incidence
          degree of the typed element at the same stable list index, in
          independently compiled red, green, and blue leaves.
        - [x] Classify degree-three typed elements by constructor and rewrite
          every color's indexed request block as a typed-element scan, with
          data, predicate transport, and list algebra compiled separately.
        - [x] Erase stable color indices after selection and prove every
          degree-three colored request comes from the clause-element suffix;
          every variable-module colored element is discarded.
        - [x] Reduce each surviving colored clause scan to the exact fixed
          block consisting of internal, top, and left requests, plus a right
          request exactly for ternary clauses.
        - [x] Rewrite the red, green, and blue retained-element scans as one
          uniform finite position table translated by the clause origin, with
          block length three or four according to clause arity.
        - [x] Split the indexed triple scan into variable-module and clause-core
          blocks, and reduce the clause suffix to nine fixed requests with
          stable index `variableCount + 9 * clauseIndex + localIndex`.
        - [x] Reduce the variable triple prefix to the stable used-occurrence
          scan, carrying the next triple index through fixed three- and
          seven-request connector blocks.
        - [x] Rewrite every variable-triple position as its computed variable
          origin plus a finite local table selected only by occurrence slot,
          polarity, connector kind, and local triple.
        - [x] Prove contraction preserves the original incidence's first
          direction at both the source and suppressed-edge target forms of a
          contracted triple endpoint.
        - [x] Reduce every genuine triple's final normalized cell type to the
          finite side/color data obtained from the first directions of its
          three original tagged incidence routes.
        - [x] Prove endpoint enumeration order is irrelevant and rewrite that
          data in the fixed red/green/blue incidence order.
        - [x] Resolve each source-specific incidence direction: clause triples
          use the fixed clause-route table, while variable triples use their
          nondegenerate finite local prefix and are unchanged by the optional
          routed occurrence suffix.
        - [x] Rewrite the final cell type of every clause, ordinary, and
          fixed-red triple as a finite local RGB direction-table lookup.
        - [x] Lift those cell tables over the stable variable and clause
          triple scans, eliminating normalized-route queries from the complete
          triple request block.
        - [x] Expose exact source-symbol contracts for four table-driven
          retained-input appenders and transport them to the existing compact
          affine vertex-request pipeline.
        - [x] Build a polynomial-time shared-scan pipeline for any fixed
          sequence of data-indexed affine record families, preserving the
          variable-triple/clause-triple/red/green/blue phase order without
          duplicating the raw source.
        - [x] Reduce the complete compact vertex compiler to five exact
          blockwise record-family equalities over the uniform unary-program
          stream, behind a certified opaque output boundary that keeps each
          Lean compiler leaf below the resource cap.
        - [x] Extract the exact unary, binary, and ternary clause-arity stream
          from that unary program with a finite block scan, prove agreement
          with the source formula's clause lengths, and certify the complete
          source-symbol scan polynomial time.
        - [x] Refine that scan to a finite clause-profile stream retaining
          every literal's polarity and current/next-slice offset, prove exact
          formula-order agreement, and certify its source compiler polynomial
          time.
        - [x] Preserve those profiles through vacuous width-three conversion,
          append exactly one fixed implication profile per literal for
          occurrence splitting, and identify the resulting polynomial-time
          stream with the guarded geometric `sourceFormula`.
        - [x] Enrich the guarded profile stream with one finite unary marker
          per distinct occurrence variable, proving the marker count exact
          and compiling the combined formula shape directly from source
          symbols in polynomial time.
        - [x] Expand each guarded clause profile through the Figure 9
          exact-one gadget and unit-clause elimination, proving that the
          finite lookup gives the exact final binary/ternary clause order and
          certifying the lookup scan polynomial time.
        - [x] Refine that Figure 9 expansion to preserve every generated
          literal's polarity and current/next-slice offset, including padding
          and unit-removal auxiliaries, with exact formula-order semantics and
          a finite polynomial-time compiler.
        - [x] Apply the fixed terminal-polarity convention to an exact clause
          profile stream, emitting precisely the required binary complement
          clauses in occurrence order and certifying the transformation
          polynomial time.
        - [x] Compose Figure 9, unit elimination, and polarity normalization
          into one exact polynomial-time finite-profile compiler for the
          final exact-one endpoint.
        - [x] Lift that finite transformation to formula-shape streams,
          preserving every incoming distinct-variable marker and appending
          the Figure 9, unit-removal, and polarity-complement markers with a
          verified polynomial-time block transducer.
        - [x] Prove those appended markers equal the actual distinct-variable
          count of the fully normalized exact-one formula, while the same
          shape theorem retains the exact final clause-profile order.
        - [x] Package the final retained, wrapped, gauged, and deduplicated
          planar-SAT presentation as a canonical formula shape, and prove it
          records the exact ordered clause profiles and distinct-variable
          count under the retained planarization certificate.
        - [x] Compile fixed-eight formula shapes by retaining all source
          profiles and appending one nine-clause implication ring plus nine
          distinct-variable markers per incoming variable marker.
        - [x] Prove the fixed-eight shape agrees with the semantic formula's
          exact clause profiles and exact nine-copies-per-source-variable
          distinct-variable count.
        - [x] Transport the named exact-shape contract from the certified
          retained planar formula through fixed-eight for any port assignment,
          so the actual angular route-induced assignment remains composable
          without unfolding the geometry in one Lean leaf.
        - [x] Package the actual clockwise, Figure 9-clearance-scaled source
          as an exact formula shape, with width and erased-clause nonemptiness
          discharged in separate resource-bounded leaves.
        - [x] Transport named exact-shape contracts through the complete
          Figure 9, unit-elimination, and polarity-normalization transform,
          and define the resulting retained final exact-one shape.
        - [x] Name the exact direct source-symbol Figure 9 and final exact-one
          shapes, certify the former against the actual ordered retained
          formula, and reduce the latter's polynomial-time compiler to the
          single missing retained Figure 9 source-shape compiler.
        - [x] Encode every width-three clause profile together with its finite
          route-first directions and compile stable clockwise profile sorting
          as a fixed finite block transduction.  Prove that canonical route
          descriptors recover the exact ordered formula shape and reduce the
          remaining ordering machine to a finite per-literal descriptor
          emitter.
        - [x] Prove canonical formula-shape streams are uniquely determined by
          their exact semantics, then identify the retained direction-sorted
          descriptor output with the actual Figure 9 source shape after its
          coordinate-only clearance scale.
        - [x] Compose any polynomial-time retained direction-descriptor emitter
          with the fixed clockwise lookup and the complete finite exact-one
          postprocessor, leaving one explicit finite-stream compiler boundary.
        - [x] Isolate fixed-eight occurrence splitting as a finite direction-
          descriptor expansion.  Its closed nine-clause ring is checked
          exactly, its one-pass stream preserves the required semantics, and
          a two-pass retained-source emitter produces the exact phase-major
          descriptor list in polynomial time.
        - [x] Name the exact pre-split retained-planar descriptor stream on
          direct PSPACE source symbols and prove that any polynomial-time
          emitter for it composes with the two-pass fixed-eight expander.  This
          separates the remaining planar component scan from the already
          compiled fixed-eight phase expansion.
        - [x] Express the final retained planar clause list exactly as ordinary
          deduplication of the five-family retained metadata after wrapping,
          canonical variable gauging, and clause-anchor normalization.
        - [x] Reduce every retained route-first direction through that same
          representative metadata lookup to its raw finite component route,
          prove the resulting position-free descriptor stream exact, and
          specialize the corresponding compiler boundary to source symbols.
        - [x] Split that source-symbol stream definitionally into a
          deduplicated clause-descriptor prefix and an exact distinct-variable
          marker suffix, with a verified two-pass retained-input compiler.
        - [x] Prove clause deduplication preserves the exact distinct-variable
          count and reduce the metadata marker suffix past wrapping, gauging,
          normalization, and deduplication to the finite retained planar-SAT
          variable count.
        - [x] Factor every semantic incidence route through a compact numeric
          metadata descriptor, then reconstruct the exact edge-route and
          indexed-segment streams in presentation order.
        - [x] Replace crossing-record allocation by one graph-free Boolean
          filter over the ordered product of neighboring numeric segment
          occurrences, and expose the already compiled unary grid-unit stream
          as its exact drawing period.
        - [x] Implement the polynomial-time retained direction-descriptor
          emitter from the uniform source stream: one finite profile/direction
          record per retained clause followed by the exact variable markers.
          - [x] Compile the complete counted unary route-descriptor stream,
            including copied incidences and occurrence-cycle links, directly
            from the guarded source symbols.
          - [x] Factor the canonical crossing scan through that compact route
            stream and recover its drawing period from the repeated descriptor
            header.
          - [x] Normalize the compiled stream by a fixed finite transducer to
            explicit record starts and delimiter-terminated unary fields,
            erasing all irrelevant token constructors.
          - [x] Verify a total eleven-field decoder for the normalized stream
            and package its exact round trip as a finite encoding of route-
            descriptor lists.
          - [x] Decompose reconstructed geometry into per-descriptor segment
            blocks and prove the fixed bounds of nine segments and eighty-one
            neighboring occurrences per route record.
          - [x] Rewrite the canonical quadratic crossing count as the exact
            descriptor/first-occurrence/descriptor/second-occurrence nested
            scan and flatten its per-route thirteen-marker blocks.
          - [x] Implement the finite descriptor segment-pair filter and emit
            thirteen variable markers per retained crossing.
            - [x] Re-encode each normalized eleven-field descriptor as one
              delimiter-framed binary word using a verified eleven-state
              finite transducer.
            - [x] Form the row-major ordered product of descriptor words with
              the verified generic quadratic-time pair machine.
            - [x] Evaluate the bounded segment-occurrence crossing predicate
              on each descriptor pair.
              - [x] Replace external route positions by the edge indices
                stored in canonical descriptors, factor the exact global
                count into pair-local counts, and prove the fixed bounds of
                6,561 tests and 85,293 markers per pair.
              - [x] Verify total single-word and pair decoders, and prove that
                interpreting the compiled canonical word pairs yields exactly
                the direct crossing-marker target.
              - [x] Prove the evaluator output linear in the encoded pair
                stream and compose its single fixed compiler boundary with
                the direct ordered-pair producer.
              - [x] Compile the pair-local predicate and marker output from
                the two decoded eleven-field words.
                - [x] Compile pair tokens through a fixed finite-state pass
                  to exact pair boundaries and unary units tagged by first or
                  second descriptor and field position `0` through `10`.
                - [x] Prove that counting those tagged unary units recovers
                  every numeric field of each descriptor in the pair exactly.
                - [x] Express the period, port columns, track rows, gate
                  column, and signed offsets as fixed affine forms, and prove
                  their tagged-token evaluations exact.
                - [x] Package signed affine equality, disequality, strict and
                  nonstrict comparisons into fixed Boolean formulas whose
                  tagged-token and semantic pair evaluations agree exactly.
                - [x] Verify fixed affine addition, scaling, subtraction, and
                  two-dimensional point evaluation, including both vertex-
                  center columns needed by the route templates.
                - [x] Give all seven local route-core branches exact affine
                  point templates, with exact tagged-field guards for offset
                  and port order, and prove each template equals the semantic
                  descriptor core under its guard.
                - [x] Add exact straight/bent source and target fanout guards,
                  prove local period translation of target fanouts, and
                  assemble each guarded affine template into the complete
                  semantic descriptor route.
                - [x] Convert affine route points to exact consecutive segment
                  templates and verify fixed neighboring-period translation
                  of every affine endpoint and segment.
                - [x] Package the twenty-eight local route shapes, prove each
                  combined guard and affine segment list exact, and check the
                  nine-segment bound for every finite shape/side case.
                - [x] Enumerate all twenty-eight route shapes and prove that
                  every locally shaped descriptor selects exactly one matching
                  combined guard.
                - [x] Expand each finite shape to exact self-indexed affine
                  neighboring occurrences, verify first-period translated
                  geometry, and retain the eighty-one-occurrence bound.
                - [x] Instantiate the four bounds, occurrence-key inequality,
                  axis tests, and two strict interval tests as one fixed
                  affine Boolean formula per occurrence pair, and prove its
                  tagged evaluation equals the canonical linear predicate.
                - [x] Define the fixed twenty-eight-squared guarded shape scan
                  over tagged fields and prove every enabled shape pair's
                  at-most-eighty-one-squared occurrence count exact.
                - [x] Prove uniqueness collapses that complete finite scan to
                  one matching shape pair and hence emits exactly the canonical
                  thirteen-marker block for every local descriptor pair.
                - [x] Prove every numeric incidence descriptor emitted from a
                  forward-local CNF has one of those twenty-eight shapes, so
                  the exact finite scan applies to the complete source stream.
                - [x] Lift the exact pair evaluator across the ordered route-
                  descriptor square and recover the global thirteen-markers-
                  per-crossing stream from self-index and common-period data.
                - [x] Reduce the canonical proper-crossing predicate to its
                  unique oriented intersection, four fundamental-square
                  bounds, distinct keys, fixed axes, and two strict linear
                  interval tests.
                - [x] Evaluate the fixed linear coordinate and proper-
                  crossing tests over the tagged unary fields.
                  - [x] Define a finite TM2 machine comparing two delimited
                    word lengths and verify all of its one-step transitions.
                  - [x] Verify the complete word-reading and length-comparison
                    phases with exact step counts.
                  - [x] Assemble exact one-pair, pair-list, and output-reversal
                    executions for the length comparator.
                  - [x] Prove its complete execution and package the exact
                    `3n+2` linear runtime as a polynomial-time compiler.
                  - [x] Feed the comparator signed affine unary totals.
                    - [x] Split every signed affine difference into natural
                      positive and negative totals and prove all four relation
                      interpretations exact.
                    - [x] Emit the two unary totals from each tagged block by
                      fixed affine phases and prove the result is exactly one
                      canonical delimiter-encoded comparison pair.
                    - [x] Certify that emitter as a polynomial-time compiler
                      and compose it with length comparison.
                    - [x] Interpret the singleton comparison ordering by its
                      fixed relation and prove the compiled Boolean equals
                      the affine atom's tagged-field truth value.
                  - [x] Compile every fixed affine Boolean predicate by
                    structural composition of constants, atoms, same-input
                    forks for conjunction/disjunction, and negation.
                  - [x] Certify a compact finite-control evaluator for an
                    arbitrary fixed-length result word, avoiding expansion of
                    the millions of fixed occurrence tests into fork trees.
                  - [x] Batch any fixed atom list into one affine phase
                    pipeline and one length-comparator run, with exact ordered
                    comparison-pair and ordering semantics.
                  - [x] Interpret the batched ordering word back into any
                    fixed predicate list, proving exact left-to-right atom
                    consumption and tagged-field Boolean semantics.
                  - [x] Compose batched comparison with fixed-length finite
                    control and emit exactly thirteen markers for every true
                    predicate in any fixed predicate list.
              - [x] Map the compiled evaluator independently over the
                pair-delimited tagged-field stream.
                - [x] Define a generic end-delimited block-map TM2 that
                  collects one block, runs an inner compiler, appends its
                  output, clears every inner stack, and repeats.
                - [x] Verify the block-map execution and polynomial runtime,
                  then instantiate it with the affine crossing compiler.
          - [x] Compose the crossing markers with the compiled segment and
            source-atom markers to obtain the exact retained variable-marker
            suffix.
          - [x] Convert those crossing markers to the fixed Figure 8(b)
            crossover descriptor blocks and identify their exact public
            descriptor prefix.
          - [x] Reduce every remaining retained metadata family to compact
            canonical data: two-token straight-carrier, bend-corner, and
            routed-variable equality templates, plus routed source-clause
            tokens whose geometric directions are uniformly invalid.
          - [x] Compile and assemble the remaining ordered descriptor scans.
            - [x] Compile retained carrier-link descriptors.
              - [x] Compile the fixed two-bit carrier descriptor-block
                expansion.
              - [x] Name the exact presentation-order carrier-link axis and
                next-slice bit target independently of formula normalization.
              - [x] Emit the exact ordered carrier-link axis/next-slice bit
                stream.
                - [x] Emit the affine axis candidates in selected segment and
                  neighboring-translation order without importing the
                  crossing-enumeration proof stack.
                - [x] Recover the exact last-occurrence retained carrier-key
                  order from duplicated neighboring terminal keys and fixed
                  retention shifts of the exact ordered crossing-pair scan.
                - [x] Filter and expand those candidates to the exact ordered
                  representative carrier links, including their next-slice
                  ownership bits.
                  - [x] Decompose the exact global retained-link bit order into
                    presentation-order representative-link blocks indexed by
                    the retained neighboring carrier keys.
                  - [x] Prove that the descriptor-derived unary axis selected
                    for each retained key is exactly the physical axis of
                    every representative carrier link in that key's block.
                  - [x] Reconstruct the exact retained terminal-and-crossing
                    carrier-node event stream from ordered neighboring
                    occurrences and canonical crossing pairs, preserving full
                    crossing records and retained period translations.
                  - [x] Compute every reconstructed carrier node's physical
                    macro position and axis-order coordinate from the numeric
                    drawing period, and identify them with the semantic sort
                    coordinates.
                  - [x] Reproduce each retained key's exact deduplicated,
                    filtered, stably sorted node chain and adjacent
                    non-crossover link-endpoint order from that event stream.
                  - [x] Compute link-orbit ownership from the explicit period,
                    filter to zero-shift representatives, and identify the
                    resulting per-key endpoint blocks with the semantic
                    representative links in exact order.
                  - [x] Compute each representative pair's periodically
                    normalized endpoint offsets and prove its graph-free
                    next-slice bit equals the retained metadata bit.
                  - [x] Map the axis and next-slice bits over every exact
                    representative pair block and preserve the established
                    per-key link order.
                  - [x] Factor the full retained carrier-node scan and every
                    per-key representative bit block through the compact
                    numeric route descriptors at the explicit drawing period.
                  - [x] Establish rank-major reconstruction for strictly
                    ordered carrier chains: counting lower coordinates in the
                    original presentation recovers each exact sorted index,
                    so the compiler need not materialize an encoded sort.
                    - [x] Specialize that lower-rank scan to the graph-free
                      deduplicated same-key carrier-node candidates and its
                      exact semantic chain lookup.
                    - [x] Recover the unique node at any exact carrier rank by
                      scanning the original candidates, with pointwise
                      equality to sorted-chain lookup.
                    - [x] Enumerate the complete rank-major carrier chain and
                      its adjacent non-crossover pairs, proving exact equality
                      to the established sorted endpoint-pair list.
                    - [x] Apply zero-owner representative filtering and the
                      axis/next-slice projection to that rank-major stream,
                      recovering the exact per-key target bit block.
                    - [x] Factor ranking, crossover suppression, orbit
                      ownership, and next-slice projection through a compact
                      compiler-facing numeric datum for each carrier node.
                    - [x] Name the complete datum-only rank scan and its
                      specialization to the retained route-descriptor node
                      stream as the explicit machine-compilation target.
                    - [x] Prove that target equals the exact route-descriptor
                      bit block from duplicate-free physical and projected
                      node streams with strict per-key coordinate order.
                    - [x] Retain a reversible proof-free code for finite
                      source identity in each numeric datum, prove projection
                      injectivity and deduplication-through-map, and reduce
                      the semantic obligation to strict per-key coordinate
                      order alone.  The code flattens indexed segments,
                      terminals, crossing records, and boundary sides to
                      finite natural/integer data suitable for unary emission.
                    - [x] Remove that final obligation generically: tag every
                      candidate with its presentation index, rank by the
                      lexicographic pair `(coordinate, index)`, and prove that
                      erasing the tags recovers Lean's stable insertion sort
                      even when coordinates tie.
                    - [x] Specialize indexed stable ranks to retained carrier
                      datums and replace the strict-order target theorem by an
                      unconditional equality, while preserving the older
                      hypothesis-bearing compatibility theorems.
                    - [x] Construct fixed padded terminal and crossing
                      carrier-node candidate blocks aligned with the affine
                      route predicates, and concatenate them in exact
                      descriptor-square then occurrence-slot-square order.
                    - [x] Prove that compacting those active padded candidates
                      recovers the complete retained route-descriptor carrier
                      node stream, then project the active slots to rank data.
                      - [x] Identify the compacted terminal descriptor-square
                        prefix with the two semantic endpoint nodes of every
                        neighboring indexed segment occurrence.
                      - [x] Identify the compacted occurrence-slot crossing
                        suffix with all retained crossing-boundary nodes.
                      - [x] Append the two exact streams and identify the
                        result with the complete retained carrier-node stream.
                      - [x] Project every active padded slot to its
                        compiler-facing rank datum.
                    - [x] Compile duplicate removal for the padded rank-data
                      stream by comparing reversible carrier-node identities.
                      - [x] Define a constructor-tagged, self-delimiting
                        binary word for every carrier-node identity.
                      - [x] Define a suffix-retaining decoder for the nested
                        identity fields.
                      - [x] Prove the decoder is a left inverse and the word
                        encoding is injective.
                      - [x] Define the active-support identity stream in exact
                        alignment with the padded rank-data candidates and
                        prove its guarded representative rows select the last
                        active occurrence of every distinct identity.
                      - [x] Compile the aligned guarded identity-word emitter
                        from the numeric route-descriptor stream.
                        - [x] Reduce full node identity, on the exact retained
                          stream, to an injective pair of carrier keys whose
                          first segment index carries a terminal/boundary-side
                          tag.
                        - [x] Define, verify, and compile the finite-state pass
                          that merges adjacent guarded key words, suppressing
                          the second component of inactive pairs.
                        - [x] Compile two guarded key components per padded
                          terminal and crossing node slot, concatenate the
                          streams, and pass them through the merger.
                        - [x] Identify the merged physical output with the
                          compact source-identity words in exact padded-slot
                          order.
                        - [x] Prove compact source-key equality equivalent to
                          reversible carrier-node-code equality on the exact
                          retained stream, and hence identify the compiled
                          compact representative rows with the full identity
                          representative rows on valid numeric routes.
                    - [x] Compile all fifty identity-free carrier rank-datum
                      columns selected by those compact representative rows.
                      - [x] Project the complete padded carrier-node stream to
                        carrier keys, align the existing sentinel-completed
                        axis stream with source-key rows, and compile its
                        selected horizontal bit.  Prove numeric-route equality
                        with zero-indexed rank-scan field eight.
                      - [x] Compile the active carrier-key route index and prove
                        that its representative-selected values are exactly
                        zero-indexed rank-scan field zero at every period.
                      - [x] Compile the carrier-key segment index through a
                        reusable six-column key-field selector and prove that
                        it is zero-indexed rank-scan field one at every period.
                      - [x] Compile the positive and negative horizontal and
                        vertical carrier-key translation coordinates, including
                        the `Int.negSucc` magnitude adjustment, and prove that
                        they are zero-indexed rank-scan fields two through five.
                      - [x] Compile direction-split affine terminal and
                        crossing order coordinates, merge their full compact
                        source identities, and prove representative lookup
                        gives the positive and negative signed magnitudes in
                        zero-indexed rank-scan fields six and seven.
                      - [x] Assemble all fifty compiled fields into the
                        column-major scan.
                        - [x] Compile the signed horizontal and vertical
                          normalization offsets of terminal and crossing
                          carrier nodes.  Prove the affine point-gauge and
                          crossing-boundary normalization laws, align compact
                          representative lookup, and identify the results with
                          rank-scan fields nine through twelve.
                        - [x] Compile terminal-zero/crossing-one guarded streams,
                          append one rejection sentinel, and perform compact
                          representative lookup for boundary presence.
                        - [x] Prove terminal/crossing candidate-kind alignment
                          and identify that compiler with rank-scan field
                          thirteen.
                        - [x] Select either member of every compiled compact
                          source-key pair with a reusable finite-state pass,
                          then project the two crossing occurrences' route and
                          translation data.  Prove exact alignment with the
                          first route field fourteen, first-translation fields
                          twenty-four through twenty-seven, second route and
                          segment fields twenty-eight and twenty-nine, and
                          second-translation fields thirty-eight through
                          forty-one.
                        - [x] Compile the crossing point's positive and
                          negative horizontal and vertical affine coordinates,
                          align active candidates through compact
                          representative lookup, and prove numeric-route
                          equality with rank-scan fields forty-two through
                          forty-five.
                        - [x] Compile the first crossing segment index and all
                          signed endpoint coordinates of both indexed crossing
                          segments.  Prove active-candidate alignment and
                          numeric-route equality with rank-scan field fifteen,
                          fields sixteen through twenty-three, and fields
                          thirty through thirty-seven.
                        - [x] Compile the signed carrier ownership shift for
                          terminals and crossing boundaries.  Prove that an
                          active retained crossing's period quotient equals
                          its fixed retention shift, then identify the results
                          with rank-scan fields forty-six through forty-nine.
                    - [x] Compile arbitrary unary natural columns to
                      unary-length binary words and then to their exact
                      row-major strict-lower comparison rows, providing the
                      unsigned comparison primitive for stable carrier ranks.
                    - [x] Compile aligned Boolean negation, conjunction, and
                      disjunction, combine the positive and negative unary
                      order-coordinate columns, and prove that fields six and
                      seven yield the exact signed strict-lower matrix on
                      numeric routes.
                    - [x] Compile unary natural and canonical signed-integer
                      equality matrices, then prove that carrier-rank fields
                      six and seven yield exact order-coordinate equality for
                      stable tie breaking.
                    - [x] Compile and conjunct equality for both carrier-key
                      indices and both signed translation coordinates, and
                      prove that fields zero through five yield the exact
                      same-carrier matrix on numeric routes.
                      - [x] Bundle those six proof-free compiler columns at
                        their common indices and prove, for arbitrary
                        descriptor inputs, that the flat compiled square is
                        exactly equality on the resulting aggregate keys.
                        - [x] Reconstruct exact equality rows, compile stable
                          within-key occurrence ranks and full key
                          multiplicities, retain each multiplicity only at
                          its final occurrence, prefix-sum those contributions,
                          and broadcast the resulting dedup-last-ordered block
                          start to every aggregate-key occurrence.
                        - [x] Add each broadcast block start to the compiled
                          stable geometric rank, yielding a polynomial-time
                          global unary rank column, and identify it exactly on
                          numeric routes with key-block start plus same-key
                          stable coordinate rank.
                          - [x] Define the corresponding indexed global
                            enumeration and prove every presented datum's
                            semantic global rank is its exact list index in
                            that dedup-last-key-major, stable-coordinate order.
                            - [x] Prove that the global enumeration neither
                              drops nor duplicates indexed datums, and hence is
                              a permutation of the complete indexed input.
                            - [x] Prove that projecting one global key block
                              recovers the established stable per-carrier datum
                              enumeration, its adjacent pairs, and its filtered
                              representative axis/next-slice bit block.
                            - [x] Compile the row-major unary rank-difference
                              square, test `second - first = 1`, conjoin the
                              result with aggregate-key equality, and prove that
                              it selects exactly adjacent pairs within global
                              carrier-key blocks on numeric routes.
                            - [x] Compile aligned unary zero, one, and
                              consecutive-index streams, together with a
                              finite-state pass that keeps only the first true
                              bit of every equality row, preparing exact
                              global-rank-order field lookup.
                            - [x] Compose those primitives with last-
                              representative equality rows and unary lookup,
                              and prove that any aligned field column is
                              emitted in exact increasing-rank order whenever
                              its ranks permute the canonical range.
                              - [x] Prove that the compiled global carrier-rank
                                column satisfies that permutation promise on
                                numeric route descriptors.
                              - [x] Prove unconditional alignment for all
                                fifty compiled carrier-datum fields and compile
                                each field into increasing global-rank order.
                                - [x] Prove on numeric routes that every
                                  rank-ordered field is exactly its projection
                                  from the global key-major, stable-coordinate
                                  datum enumeration.
                                - [x] Reconstruct canonical positions from the
                                  rank-ordered fields, compile their immediate-
                                  successor square and the six-field same-key
                                  square, and conjunct them into the candidate
                                  adjacent-carrier-pair matrix.
                                  - [x] Prove on numeric routes that this matrix
                                    marks exactly consecutive entries of the
                                    global enumeration within one carrier-key
                                    block.
                                  - [x] Compile positivity and zero projections
                                    of any ordered endpoint field, specialize
                                    them to the first endpoint's axis and both
                                    boundary-presence bits, and prove their
                                    exact numeric semantics.
                                  - [x] Compile all four ownership-shift zero
                                    tests at either endpoint, select the owner
                                    by boundary priority, and prove the result
                                    is exactly the representative-pair
                                    predicate.
                                  - [x] Give the thirty-two-field crossing
                                    payload a verified inverse, proving it
                                    retains the complete crossing-record
                                    identity needed for crossover suppression.
                                  - [x] Compile equality of all thirty-two
                                    ordered crossing-payload fields together
                                    with both boundary guards, and prove its
                                    negation is exactly crossover suppression.
                                  - [x] Compile a reusable signed-unary
                                    successor matrix and prove that canonical
                                    positive/negative magnitudes mark exactly
                                    pairs satisfying `second = first + 1`.
                                  - [x] Apply signed succession horizontally
                                    and signed equality vertically to ordered
                                    normalization fields nine through twelve,
                                    recovering the exact next-slice bit.
                                  - [x] Conjoin adjacency, crossover
                                    suppression, ownership, axis, and
                                    next-slice matrices; encode each selected
                                    pair sparsely and prove that decoding emits
                                    the exact row-major selected-pair stream.
                                  - [x] Group row-major successors into the
                                    dedup-last carrier-key blocks, recover every
                                    established per-key bit block, and identify
                                    the result with the exact semantic global
                                    carrier-link bit stream.
                                  - [x] Compose the exact sparse bit compiler
                                    with the fixed two-token descriptor-block
                                    expansion and prove its semantic output.
                                  - [x] Reinterpret the direct source's exact
                                    binary route words as numeric descriptors
                                    and compose them with the complete retained
                                    carrier descriptor compiler.
                    - [x] Prove unconditional row-count alignment between the
                      key and order-coordinate representative pipelines, then
                      compile same-key strict-lower row counts and equal-key,
                      equal-coordinate presentation-prefix counts into one
                      unary stable-rank candidate per compact datum.
                      - [x] Prove on numeric routes that the compiled matrices,
                        reconstructed rows, full and prefix counts, and their
                        sum are exactly those stable-rank counts.
                      - [x] Identify each such sum with the strict lower rank
                        in its same-key fiber under lexicographic coordinate
                        and original-presentation-index order.
                  - [x] Compile the retained representative rows to one unary
                    active-node multiplicity per retained carrier key, and
                    prove that padded rejection guards do not affect those
                    counts and that numeric CNF routes retain their exact
                    stable key order.
                  - [x] Prove that the same selected rows recover any unary
                    datum determined by the retained key, so later carrier
                    metadata can be broadcast without rebuilding the key
                    selector.
                  - [x] Compile an activation-aligned unary axis value for
                    every padded terminal and crossing candidate slot,
                    assigning zero to inactive slots.
                  - [x] Map those fields over the complete descriptor and
                    occurrence-slot pair products and compose the terminal
                    prefix with the crossing suffix in polynomial time.
                  - [x] Prove that the complete axis-value stream has exactly
                    one entry per padded carrier-key candidate, pairwise and
                    after terminal/crossing stream composition.
                  - [x] Append a unary-zero semantic sentinel and prove its
                    length matches the representative rows' final rejection
                    guard.
                  - [x] Compile the sentinel-completed axis stream by appending
                    one fixed delimiter to the existing physical pipeline.
                  - [x] Fork the representative rows with those sentinel
                    values, prove the dependent lookup input is length-valid,
                    and compile one selected unary axis per representative.
                  - [x] Prove that the aligned zero sentinel preserves
                    support-aware lookup and that any key-derived padded axis
                    stream is returned in exact retained carrier-key order.
                  - [x] Prove the compiled terminal/crossing padded axis stream
                    is a function of its active carrier key.
                    - [x] Prove generic activated axis/template block
                      semantics and define a well-defined descriptor-level
                      axis datum for every padded carrier key.
                    - [x] Expose the terminal recipe axes as explicit
                      segment/shape blocks and prove key-derived alignment
                      for one selected diagonal segment.
                    - [x] Lift terminal key-derived alignment through route
                      shapes, diagonal and off-diagonal numeric descriptor
                      pairs, and the complete descriptor square.
                    - [x] Lift crossing key-derived alignment through retained
                      shifts, active and inactive slots, tagged descriptor-slot
                      pairs, and the complete numeric crossing suffix.
                    - [x] Combine both numeric streams and prove the compiled
                      lookup returns exact descriptor-derived axes in retained
                      carrier-key order.
            - [x] Compile retained route-bend descriptors.
            - [x] Compile retained routed-variable-link descriptors.
            - [x] Compile retained gauged routed-clause descriptors from the
              exact finite source clause-profile stream.
            - [x] Append all four scans to the compiled crossover prefix.
        - [ ] Implement the polynomial-time prepared-token emitter for the
          sparse normalization assignments; the fixed gadget-pixel expansion,
          exact header, and every downstream postprocessor are now verified.
          - [x] Compose any canonical assignment-record emitter with the exact
            prepared header, fixed record expander, and prepared-token
            interface.
          - [x] Split the compact vertex boundary into exact variable-triple,
            clause-triple, red, green, and blue scans, and carry any verified
            five-family instance through affine expansion to the canonical
            vertex-record appender.
          - [x] Expose the existing polynomial-time numeric incidence-route
            descriptor compiler as a shared input to the remaining geometry
            passes.
          - [ ] Construct the five concrete affine vertex table families.
          - [ ] Implement the canonical route-record appender.
            - [x] Prove retained-ray rasterization exposes a genuine first
              direction and preserves it for orthogonal retained routes.
            - [x] Identify every public ordinary non-singleton fallback's
              first direction with its scaled source route.
            - [x] Identify the singleton escaped fallback's first direction
              with its scaled source route at both the coordinated and
              normalized public route boundaries.
            - [x] Prove the unit-subdivided cardinal escaped fan keeps its
              source gate isolated, so loop erasure preserves that direction.
            - [x] Prove every genuine non-singleton ordinary fallback keeps
              its scaled source head out of its outer fan and Figure 7 spoke.
            - [x] Compose the ordinary prefix, outer fan, and matching spoke
              while preserving source-head isolation under unit subdivision.
            - [ ] Combine direct, fallback, and implication-cycle directions
              into the actual final route-descriptor stream.
            - [ ] Compile the canonical route records from that stream.
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

The definition layer needed to state Theorem 5.2 is complete.  Its entire 2D
conjunct is now proved: `periodicTrominoTiling_coRE` supplies the upper bound,
and `PeriodicWangPlanarThreeDMReduction.theorem52_planeStatement` supplies the
matching Wang-tiling hardness reductions for both trominoes.  The 1.5D upper
bound is now proved directly for the target flat encoding by
`flatPeriodicStripTrominoTiling_inPSPACE`; the remaining 1.5D work is the
PSPACE-hardness proof.  The complete formal target remains
`LeanTrominoes.Theorem52.statement`, the conjunction of:

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
- [`LeanTrominoes/PeriodicStripFlatEncoding.lean`](LeanTrominoes/PeriodicStripFlatEncoding.lean)
  gives the 1.5D target a delimiter-based binary encoding with explicit motif
  length and two signed-coordinate fields per motif cell.  Its decoder round
  trip is verified, and motif-list structure has linear rather than recursively
  paired overhead.
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
  matching literal route; the same representative-index operation is exposed
  generically for arbitrary finite auxiliary data.  The transported family is
  proved to satisfy every periodic incidence endpoint, and compatibility is
  reduced to finite distinctness and fundamental-square bounds for the
  retained vertices.
  [`LeanTrominoes/PeriodicCNFPlanarRetainedRepresentativeItem.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedRepresentativeItem.lean)
  specializes that auxiliary-data lookup to the retained wrapped planar-SAT
  source and proves the exact final-clause/source-representative lookup bridge.
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
- [`LeanTrominoes/PeriodicCNFOneDimensional.lean`](LeanTrominoes/PeriodicCNFOneDimensional.lean)
  identifies the horizontal fragment of the existing periodic-CNF syntax,
  defines direct line assignments and locality, and proves that both agree
  with the existing plane semantics.
- [`LeanTrominoes/PeriodicComputationCycle.lean`](LeanTrominoes/PeriodicComputationCycle.lean)
  formalizes the cyclic-computation core of the PSPACE-hardness proof.  A
  bounded clock advances on ordinary deterministic steps and an accepting
  state resets to the initial configuration; the reset system has a directed
  cycle exactly when the original system has a bounded accepting trace.
- [`LeanTrominoes/PeriodicComputationTrace.lean`](LeanTrominoes/PeriodicComputationTrace.lean)
  reconstructs every intermediate state from Mathlib's counted `EvalsTo`
  iterate witness and packages a terminating TM2 computation as an explicit
  accepting trace.  Each trace state is proved reachable, so a source PSPACE
  decider's global configuration-space certificate bounds every encoded
  stack throughout the trace.
- [`LeanTrominoes/PeriodicCNFTransition.lean`](LeanTrominoes/PeriodicCNFTransition.lean)
  views every forward-local horizontal CNF formula as a transition relation
  between consecutive Boolean slices and proves that satisfying line
  assignments are exactly its bi-infinite paths.
- [`LeanTrominoes/PeriodicCNFTransitionGates.lean`](LeanTrominoes/PeriodicCNFTransitionGates.lean)
  supplies truth-table-verified constant-size Tseitin clauses for constants,
  equality, negation, conjunction, and disjunction over current- and
  next-slice wires; every generated clause is forward-local.
- [`LeanTrominoes/PeriodicCNFTransitionExpr.lean`](LeanTrominoes/PeriodicCNFTransitionExpr.lean)
  assembles those gates into a structural Tseitin compiler.  It allocates one
  fresh current-slice atom per expression node and proves the exact fresh
  range, root bounds, linear clause count, and forward locality of the result.
- [`LeanTrominoes/PeriodicCNFTransitionExprSoundness.lean`](LeanTrominoes/PeriodicCNFTransitionExprSoundness.lean)
  proves semantic soundness compositionally: satisfying every generated
  clause forces the fresh root atom to equal direct evaluation of the source
  transition expression.
- [`LeanTrominoes/PeriodicCNFTransitionExprBounds.lean`](LeanTrominoes/PeriodicCNFTransitionExprBounds.lean)
  proves the complementary freshness invariant: when all source atoms precede
  the initial fresh index, every atom mentioned by the generated clauses lies
  below the returned `nextFresh`, including across nested subexpressions.
- [`LeanTrominoes/PeriodicCNFTransitionExprCompleteness.lean`](LeanTrominoes/PeriodicCNFTransitionExprCompleteness.lean)
  constructs the canonical valuation of all fresh Tseitin atoms.  It preserves
  every source atom, satisfies every compiled clause, and makes the compiled
  root equal direct evaluation of the transition expression.
- [`LeanTrominoes/PeriodicCNFTransitionExprVectors.lean`](LeanTrominoes/PeriodicCNFTransitionExprVectors.lean)
  provides the verified Boolean-vector layer for bounded configurations:
  finite conjunction and disjunction, exact-one fields, equality between
  adjacent slices, and a little-endian no-overflow successor relation.  It
  also proves the source-atom bounds needed by constructive CNF compilation.
- [`LeanTrominoes/PeriodicCNFTransitionExprFormula.lean`](LeanTrominoes/PeriodicCNFTransitionExprFormula.lean)
  appends the unit clause requiring a compiled root to be true.  Generated
  gates remain edge-local: the next endpoint is read only through source
  atoms, which yields an exact equivalence between line satisfiability and
  bi-infinite paths through the direct Boolean expression relation.
- [`LeanTrominoes/PeriodicCNFTransitionExprFields.lean`](LeanTrominoes/PeriodicCNFTransitionExprFields.lean)
  removes nested clause construction from the executable path.  It gives each
  constant, wire, and Boolean gate an exact native natural-field block, streams
  those blocks during structural Tseitin recursion, and proves the complete
  clause-count-prefixed result identical to the verified flat formula fields.
- [`LeanTrominoes/PeriodicCNFTransitionProgram.lean`](LeanTrominoes/PeriodicCNFTransitionProgram.lean)
  flattens every transition expression to a compact postorder instruction
  stream.  Its one-pass stack interpreter emits exactly the direct structural
  compiler fields, with one instruction per expression node and at most three
  natural fields per instruction.
- [`LeanTrominoes/PeriodicCNFTransitionProgramVectors.lean`](LeanTrominoes/PeriodicCNFTransitionProgramVectors.lean)
  mirrors the reusable Boolean-vector expression combinators directly on flat
  postorder instruction lists.  It covers finite conjunction and disjunction,
  Boolean and vector equality, recursive exact-one constraints, and binary
  succession, proving each list-level program exactly equals the ordinary
  expression traversal.  This is the normalized instruction interface used
  by the bounded request printer.
- [`LeanTrominoes/PeriodicCNFTransitionProgramEncoding.lean`](LeanTrominoes/PeriodicCNFTransitionProgramEncoding.lean)
  fixes the native evaluator request format, proves exact decoder round trips,
  and identifies a total request evaluator with the verified formula-field
  stream.  A request carries the clause header and fresh-atom boundary before
  the compact postorder program.
- [`LeanTrominoes/PeriodicCNFTransitionEvaluatorMachine.lean`](LeanTrominoes/PeriodicCNFTransitionEvaluatorMachine.lean)
  implements the fixed finite-machine request evaluator.
  Its reusable variable-width primitive copies a binary atom into the reverse
  output accumulator as one complete native field, restores the source stack
  exactly, and has an exact linear step count.  Its carry-and-restore routine
  also increments the canonical little-endian fresh-atom counter in linear
  time, including the possible new high bit.  A finite-control fixed-field
  emitter now combines with those primitives to produce the complete verified
  constant-gate block in linear time.
- [`LeanTrominoes/PeriodicCNFTransitionEvaluatorTime.lean`](LeanTrominoes/PeriodicCNFTransitionEvaluatorTime.lean)
  bounds the exact complete evaluator execution quadratically in its native
  request length.  A bounded semantic request type records the fresh-atom
  invariant supplied by the machine front end, and the resulting compiler is
  packaged as an explicit `TM2ComputableInPolyTime` certificate.
- [`LeanTrominoes/PeriodicCNFTransitionExprSize.lean`](LeanTrominoes/PeriodicCNFTransitionExprSize.lean)
  begins the quantitative hardness certificate.  It bounds Tseitin clauses
  by three per expression node, accounts for the forced root clause exactly,
  and proves quadratic node bounds for finite exact-one fields and binary
  clock succession.
- [`LeanTrominoes/PeriodicCNFMachineAtoms.lean`](LeanTrominoes/PeriodicCNFMachineAtoms.lean)
  defines the finite atom vocabulary of a bounded machine slice: optional
  control labels, internal states, optional symbols in every bounded stack
  cell, and little-endian clock bits.  Its explicit affine equivalence uses
  fixed machine-alphabet codes plus arithmetic runtime positions, allocating
  every constructor injectively below one `atomCount` fresh boundary with
  field-specific vectors and bounds.  Exact arithmetic equations identify the
  code and complete field vector for labels, states, stack cells, and clock
  bits, making the width-dependent layout suitable for the pending executable
  formula compiler.
- [`LeanTrominoes/PeriodicCNFMachineValuation.lean`](LeanTrominoes/PeriodicCNFMachineValuation.lean)
  maps a bounded clocked TM2 configuration to its canonical Boolean slice.
  Labels, finite control states, and optional values in every bounded stack
  cell are proved exactly-one; the combined structural expression holds on
  every encoding and mentions only atoms below `atomCount`.
- [`LeanTrominoes/PeriodicCNFMachineWellFormed.lean`](LeanTrominoes/PeriodicCNFMachineWellFormed.lean)
  excludes one-hot stack assignments with holes by requiring `none` to be
  suffix-closed at every adjacent pair.  Canonical list encodings satisfy the
  resulting constraint, which combines with exact-one fields into the full
  structural well-formedness expression and retains the source-atom bound.
- [`LeanTrominoes/PeriodicCNFMachineDecode.lean`](LeanTrominoes/PeriodicCNFMachineDecode.lean)
  proves that each exact-one field has a unique selected value and decodes an
  arbitrary well-formed valuation to a bounded machine slice.  Every label,
  state, stack-cell, and clock source bit is recovered exactly, and the stack
  suffix constraints make each decoded fixed-width stack list-shaped.
- [`LeanTrominoes/PeriodicCNFMachineClock.lean`](LeanTrominoes/PeriodicCNFMachineClock.lean)
  interprets fixed-width little-endian clock fields and proves that the
  no-overflow ripple-carry expression is equivalent to incrementing their
  natural-number values.  It verifies the canonical clock encoding and both
  ordinary-step successor and accepting-step reset expressions, including
  their generated-atom bounds.
- [`LeanTrominoes/PeriodicCNFMachineConfiguration.lean`](LeanTrominoes/PeriodicCNFMachineConfiguration.lean)
  recovers ordinary variable-length TM2 stacks from the occupied prefixes of
  decoded fixed-width cell vectors.  Suffix-shaped vectors preserve every
  represented cell, and bounded canonical encodings reconstruct both the TM2
  configuration and reset-clock state exactly.
- [`LeanTrominoes/PeriodicCNFMachineConfigurationCount.lean`](LeanTrominoes/PeriodicCNFMachineConfigurationCount.lean)
  injects every width-bounded configuration into its finite canonical Boolean
  slice.  A terminating deterministic run cannot repeat a configuration, so
  its length is bounded by one less than the number of Boolean slices; this
  supplies the reset clock without assuming a separate running-time bound.
- [`LeanTrominoes/PeriodicCNFMachineFields.lean`](LeanTrominoes/PeriodicCNFMachineFields.lean)
  defines current/next tests for labels, finite control, and optional stack
  cells, together with field and whole-stack preservation expressions.  Their
  semantics are bidirectional for arbitrary one-hot valuations, and every
  expression retains the bounded source-atom invariant.
- [`LeanTrominoes/PeriodicCNFMachineProgramFields.lean`](LeanTrominoes/PeriodicCNFMachineProgramFields.lean)
  replaces those semantic field expressions by direct postorder programs.
  Labels, controls, stack cells, full fixed configurations, preservation
  fields, and clock reset/successor use the explicit affine atom layout, with
  proofs that every instruction word is exactly the corresponding expression
  traversal.
- [`LeanTrominoes/PeriodicCNFMachineProgramWellFormed.lean`](LeanTrominoes/PeriodicCNFMachineProgramWellFormed.lean)
  normalizes every one-hot field and adjacent occupied-prefix constraint into
  flat instruction lists, then assembles the complete bounded-slice
  well-formedness program and proves exact postorder agreement.
- [`LeanTrominoes/PeriodicCNFMachineStackTransform.lean`](LeanTrominoes/PeriodicCNFMachineStackTransform.lean)
  normalizes any atomic sequence of pushes and pops to a known prefix followed
  by a fixed drop from the source stack.  Its linear-width expression checks
  overflow and every output cell; on suffix-shaped decoded vectors this is
  equivalent to the same transformation of ordinary TM2 stack lists.
- [`LeanTrominoes/PeriodicCNFMachineProgramStackTransform.lean`](LeanTrominoes/PeriodicCNFMachineProgramStackTransform.lean)
  gives the normalized stack transform a direct instruction-level interface.
  Its fit check and each width-indexed output cell branch over only fixed
  transform data and the runtime width, and the complete program is proved
  identical to the semantic stack-transform expression postorder.
- [`LeanTrominoes/PeriodicCNFMachineProgramStatementPaths.lean`](LeanTrominoes/PeriodicCNFMachineProgramStatementPaths.lean)
  mirrors the finite symbolic TM2 executor with postorder programs in place of
  semantic expression guards.  Push, pop, peek, load, branch, goto, and halt
  paths agree exactly with the original executor, and their stack transforms,
  finite control branches, and label branches assemble the exact ordinary-step
  instruction word.
- [`LeanTrominoes/PeriodicCNFMachineProgramResetRelation.lean`](LeanTrominoes/PeriodicCNFMachineProgramResetRelation.lean)
  combines normalized structural well-formedness, ordinary steps, reset-clock
  arithmetic, and fixed initial/designated accepting configurations into the
  complete bounded relation program, proved equal to the semantic expression
  postorder.
- [`LeanTrominoes/PeriodicCNFMachineStatementPaths.lean`](LeanTrominoes/PeriodicCNFMachineStatementPaths.lean)
  symbolically executes an atomic TM2 statement after specializing its finite
  control value.  Unknown `peek` and `pop` observations branch only over one
  finite optional alphabet, while stacks remain normalized transforms; the
  terminal paths assemble a complete bounded ordinary-step expression.
- [`LeanTrominoes/PeriodicCNFMachineStatementSemantics.lean`](LeanTrominoes/PeriodicCNFMachineStatementSemantics.lean)
  proves by structural induction that the generated guarded paths realize
  exactly Mathlib's `TM2.stepAux`.  Consequently the complete bounded step
  expression is equivalent to `FinTM2.step` on every well-formed decoded slice
  and on canonical encodings whose stacks fit the selected width.
- [`LeanTrominoes/PeriodicCNFMachineResetRelation.lean`](LeanTrominoes/PeriodicCNFMachineResetRelation.lean)
  combines the ordinary machine step with structural well-formedness, a
  no-overflow successor clock, and a halted-label reset to a fixed initial
  configuration.  Canonical bounded encodings satisfy the resulting local
  expression exactly when their semantic states satisfy `ResetClockRelation`.
- [`LeanTrominoes/PeriodicCNFMachineFormula.lean`](LeanTrominoes/PeriodicCNFMachineFormula.lean)
  compiles that accepting-reset expression to a forward-local horizontal CNF.
  Every satisfying line model is decoded into a genuine bounded accepting
  machine trace, while every accepting trace that respects the selected stack
  width closes into a satisfying periodic model.  Soundness also covers
  noncanonical Boolean slices by proving that well-formed decoding and
  re-encoding preserves every source atom.
- [`LeanTrominoes/PeriodicCNFMachineDesignatedFormula.lean`](LeanTrominoes/PeriodicCNFMachineDesignatedFormula.lean)
  tightens the accepting reset to one designated terminal configuration.
  This distinction is essential for total deciders, whose `true` and `false`
  outputs are both halted: the designated formula cycles exactly through the
  chosen output, while retaining the same forward-local 1D CNF guarantees.
- [`LeanTrominoes/PeriodicCNFMachineSize.lean`](LeanTrominoes/PeriodicCNFMachineSize.lean)
  makes the bounded machine construction quantitative.  It gives an exact
  affine count for source atoms and fixed-configuration tests, affine bounds
  for one-hot and stack-shape constraints, and a quadratic bound for the reset
  clock.  The resulting clause bound isolates the remaining finite-statement
  expansion as a single `machineStepExpression` term.
- [`LeanTrominoes/PeriodicCNFMachineStatementSize.lean`](LeanTrominoes/PeriodicCNFMachineStatementSize.lean)
  bounds that finite-statement expansion by syntax-directed machine constants.
  Structural induction verifies a fixed upper bound on terminal symbolic paths
  and a fixed observation-depth bound on every generated guard, independent of
  stack and clock widths.
- [`LeanTrominoes/PeriodicCNFMachineStepSize.lean`](LeanTrominoes/PeriodicCNFMachineStepSize.lean)
  finishes the local machine-formula size proof.  Normalized stack transforms
  are affine in represented width; finite control, label, and symbolic-path
  enumeration contribute only fixed machine constants.  Combining this with
  the structural and reset-clock estimates gives a complete explicit clause
  bound for the designated horizontal CNF, with no residual expression term.
- [`LeanTrominoes/PeriodicCNFMachineStepAffine.lean`](LeanTrominoes/PeriodicCNFMachineStepAffine.lean)
  exposes the ordinary-step budget as an exact slope-times-width plus intercept.
  Both coefficients are closed finite sums over the fixed machine's labels,
  controls, statement paths, and stack alphabets, making polynomial
  composition with a source space certificate direct.
- [`LeanTrominoes/PeriodicCNFPolySpaceReductionSemantics.lean`](LeanTrominoes/PeriodicCNFPolySpaceReductionSemantics.lean)
  instantiates the clocked formula for an arbitrary certified polynomial-space
  decider.  The reset clock is sized by the finite bounded-configuration count,
  and the resulting local 1D periodic CNF is satisfiable exactly when the
  source input belongs to the decider's language.
- [`LeanTrominoes/PeriodicCNFPolySpaceReductionSize.lean`](LeanTrominoes/PeriodicCNFPolySpaceReductionSize.lean)
  composes those machine bounds with the source decider's polynomial space
  certificate.  The selected stack width and clock width are exact evaluations
  of explicit natural polynomials, and a final explicit polynomial bounds the
  emitted horizontal CNF's clause count in encoded source input length.  It
  also combines the flat-encoding estimates with a polynomial atom boundary
  to bound the complete output symbol stream by an explicit polynomial.  The
  polynomial-time machine certificate for emitting that stream remains.
- [`LeanTrominoes/PeriodicCNFPolySpaceCompiler.lean`](LeanTrominoes/PeriodicCNFPolySpaceCompiler.lean)
  factors the reduction through the raw finite list of source-encoding symbols
  and returns the flat CNF symbol stream directly.  On every valid encoded
  input it agrees exactly with the semantic formula, inherits its correctness,
  and satisfies the same polynomial output-length bound.
- [`LeanTrominoes/FiniteBlockTransducer.lean`](LeanTrominoes/FiniteBlockTransducer.lean)
  constructs a three-stack finite machine for fixed finite-alphabet block
  substitution.  It proves an exact run length of twice the input length plus
  the output length and two, then packages the finite block-size bound as an
  explicit linear `TM2ComputableInPolyTime` certificate.
- [`LeanTrominoes/FiniteEncodingNativeFields.lean`](LeanTrominoes/FiniteEncodingNativeFields.lean)
  numbers any finite source alphabet and specializes the block transducer to
  emit canonical delimiter-terminated natural fields over the evaluator's
  native alphabet.  This supplies the polynomial-time input front end needed
  by the pending machine-to-periodic-CNF compiler certificate.  The same
  transducer is also presented semantically as computing the natural field
  list under its native `trList` encoding, ready for machine composition.
- [`LeanTrominoes/PeriodicCNFPolySpaceNativeCompiler.lean`](LeanTrominoes/PeriodicCNFPolySpaceNativeCompiler.lean)
  gives the formula generator a total evaluator-native natural-field
  interface.  It proves generated fields recover the original finite-alphabet
  stream, now generates the Tseitin field stream directly without an
  intermediate clause list, factors generation through the compact postorder
  request and fixed evaluator, identifies that output with the verified flat
  formula, and gives explicit polynomial bounds for both request field count
  and native output length.  It also packages every total decoded-field input
  as the evaluator's bounded semantic request, proving both encoding and
  compiled-output identities needed for machine composition.
  It also exposes the identical compiler request directly on the original
  finite source-symbol list, so the remaining printer need not decode its
  initial configuration from native natural fields.
- [`LeanTrominoes/PeriodicCNFPolySpaceProgramSpec.lean`](LeanTrominoes/PeriodicCNFPolySpaceProgramSpec.lean)
  instantiates the expression-free bounded program for one polynomial-space
  decider and direct source-symbol list.  It prefixes the instruction-derived
  exact clause count and affine fresh boundary, then proves the resulting
  natural fields and native encoding are exactly the compact request already
  consumed by the verified structural evaluator.
- [`LeanTrominoes/PeriodicCNFPolySpaceHardness.lean`](LeanTrominoes/PeriodicCNFPolySpaceHardness.lean)
  packages the complete complexity-theoretic endpoint around one explicit
  remaining contract: a polynomial-time machine from decoded native source
  fields to bounded compact compiler requests.  Given that certificate, it
  composes the finite source encoder and quadratic structural evaluator,
  presents the output as the semantic flat formula, and proves both the
  many-one reduction and uniform PSPACE-hardness statement.
- [`LeanTrominoes/UnaryPolynomialPaddingMachine.lean`](LeanTrominoes/UnaryPolynomialPaddingMachine.lean)
  supplies the remaining request generator with a reusable finite Horner
  machine.  It retains a native source word, counts selected delimiters,
  multiplies a unary accumulator by that count, adds one fixed coefficient,
  lifts the execution across every coefficient, and emits the source followed
  by exactly the resulting number of unary markers.  Exact execution and
  runtime proofs package the construction as an explicit polynomial-time
  machine certificate.
- [`LeanTrominoes/BinaryCountPaddingMachine.lean`](LeanTrominoes/BinaryCountPaddingMachine.lean)
  converts a selected unary marker class into a canonical native binary
  counter while preserving the complete source word.  Its verified carry
  scan, counter restoration, source scan, and output reversal give exact
  execution and output theorems, packaged with an explicit quadratic
  polynomial-time certificate.
- [`LeanTrominoes/UnaryFieldEncoderMachine.lean`](LeanTrominoes/UnaryFieldEncoderMachine.lean)
  converts any sequence of delimiter-terminated unary natural-number fields
  into the evaluator's canonical binary-list representation.  Its finite
  scanner, increment, field emission, and output reversal are proved exact,
  and the complete conversion has an explicit quadratic polynomial-time
  certificate.
- [`LeanTrominoes/UnaryFieldHeaderRotation.lean`](LeanTrominoes/UnaryFieldHeaderRotation.lean)
  specifies the total unary-stream permutation that moves a counted first
  field behind width and period, with an exact theorem on canonical field
  lists.  This is the final ordering step needed by counted strip emitters.
- [`LeanTrominoes/UnaryFieldHeaderRotationMachine.lean`](LeanTrominoes/UnaryFieldHeaderRotationMachine.lean)
  implements that permutation as a fixed four-stack `FinTM2` and proves every
  transition case, including total behavior on prematurely terminated unary
  streams.
- [`LeanTrominoes/UnaryFieldHeaderRotationMachineExecution.lean`](LeanTrominoes/UnaryFieldHeaderRotationMachineExecution.lean)
  lifts those transitions through exact inductive executions for all six
  machine phases and identifies the parsed field prefixes with the total
  semantic rotation specification.
- [`LeanTrominoes/UnaryFieldHeaderRotationMachineTime.lean`](LeanTrominoes/UnaryFieldHeaderRotationMachineTime.lean)
  composes the phases into the exact total rotation, proves the coarse linear
  bound `9n + 9`, and packages the result as an explicit
  `TM2ComputableInPolyTime` certificate.
- [`LeanTrominoes/CountedUnaryFieldTokens.lean`](LeanTrominoes/CountedUnaryFieldTokens.lean)
  packages arbitrary unary natural fields as finite tokens and proves that
  the existing marker counter/finalizer prepends their exact counted header.
- [`LeanTrominoes/CountedUnaryFieldTokenCompiler.lean`](LeanTrominoes/CountedUnaryFieldTokenCompiler.lean)
  precomposes marker counting, token expansion, and header rotation once in a
  low-dependency environment, exposing a reusable polynomial-time compiler
  bridge for counted-token emitters.
- [`LeanTrominoes/PeriodicCNFUnaryProgramTokens.lean`](LeanTrominoes/PeriodicCNFUnaryProgramTokens.lean)
  gives the concrete request emitter an entirely finite output alphabet:
  runtime atoms and the fresh boundary become unary runs, while fixed tokens
  carry instruction tags and exact clause weights.  Fixed expansion is proved
  to produce precisely the normalized unary fields, and a verified unary
  Horner pass appends their exact clause count in polynomial time.
- [`LeanTrominoes/PeriodicCNFUnaryProgramTokenFinalizer.lean`](LeanTrominoes/PeriodicCNFUnaryProgramTokenFinalizer.lean)
  rotates the appended unary clause-count suffix to the request header and
  expands the retained finite token body.  Exact execution and a linear time
  bound certify the four-stack finalizer; composition with clause counting
  maps the emitter source directly to the normalized unary request fields in
  polynomial time.
- [`LeanTrominoes/PeriodicCNFPolySpaceUnaryPreparedLayout.lean`](LeanTrominoes/PeriodicCNFPolySpaceUnaryPreparedLayout.lean)
  removes the binary space, clock, and fresh blocks from the concrete printer
  input.  The resulting four-block word retains only finite source symbols and
  the three unary counters; exact projection theorems recover the normalized
  unary-token request, and the existing source-preparation machine supplies
  its polynomial-time certificate.
- [`LeanTrominoes/PeriodicCNFAffineTemplateEmitterMachine.lean`](LeanTrominoes/PeriodicCNFAffineTemplateEmitterMachine.lean)
  verifies the reusable finite-control core of the counter-driven printer.  It
  retains an arbitrary finite workspace, counts selected symbols, and appends
  one fixed recipe template at every selected position; fixed tokens are
  copied literally and affine atoms become unary runs of exact length
  `base + stride × position`.  Its exact execution proof includes restoration
  of the position counter, cleanup of every work stack, output reversal, and a
  genuinely halted final configuration.
- [`LeanTrominoes/PeriodicCNFAffineTemplateEmitterTime.lean`](LeanTrominoes/PeriodicCNFAffineTemplateEmitterTime.lean)
  bounds each recipe, complete position template, selected-position range, and
  final output length.  The resulting fixed quadratic polynomial bounds the
  exact halted execution and packages the emitter for polynomial-time TM2
  composition without enlarging the machine-proof module.
- [`LeanTrominoes/PeriodicCNFAffineProgramTemplates.lean`](LeanTrominoes/PeriodicCNFAffineProgramTemplates.lean)
  lifts those recipes to affine postorder instructions and programs.  Exact
  evaluation and token theorems cover constants, wires, Boolean operators,
  finite conjunction/disjunction, equality, exactly-one vectors, and binary
  succession, so concrete bounded-machine phases can be specified by their
  ordinary normalized programs rather than by raw token arithmetic.
- [`LeanTrominoes/PeriodicCNFBivariateProgramTemplates.lean`](LeanTrominoes/PeriodicCNFBivariateProgramTemplates.lean)
  extends the semantic recipe language to atom runs affine in two independent
  runtime counters.  Its compositional postorder interface proves exact token
  agreement for wires, Boolean folds, equality, vector equality, and binary
  succession, providing the precise target for the clock emitter.
- [`LeanTrominoes/PeriodicCNFBivariateTemplateEmitterMachine.lean`](LeanTrominoes/PeriodicCNFBivariateTemplateEmitterMachine.lean)
  realizes those recipes with a finite two-counter machine.  It independently
  counts a persistent context class and a position-loop class, rescans and
  restores both unary counters for every affine atom, retains the full input,
  clears every work stack, reverses the exact appended token stream, and proves
  the final configuration genuinely halted.
- [`LeanTrominoes/PeriodicCNFBivariateTemplateEmitterTime.lean`](LeanTrominoes/PeriodicCNFBivariateTemplateEmitterTime.lean)
  bounds every two-counter recipe, position template, complete emitted range,
  and verified execution.  Both counters are bounded by retained input length,
  yielding one explicit quadratic polynomial and a reusable
  `TM2ComputableInPolyTime` certificate.
- [`LeanTrominoes/PeriodicCNFBivariateProgramTokenAlgebra.lean`](LeanTrominoes/PeriodicCNFBivariateProgramTokenAlgebra.lean)
  identifies the two-counter emitter's recursive position range with the flat
  unary-token stream of the corresponding evaluated ordinary postorder
  programs, supplying the exact semantic bridge needed by clock phases.
- [`LeanTrominoes/PeriodicCNFMachineBivariateClockTemplates.lean`](LeanTrominoes/PeriodicCNFMachineBivariateClockTemplates.lean)
  instantiates bivariate atoms with the bounded machine's exact reset-clock
  layout.  One fixed bit-zero template over the runtime clock-marker range,
  followed by the precise finite-conjunction ending, recovers the complete
  normalized clock-reset token word.
- [`LeanTrominoes/PeriodicCNFPolySpaceClockResetEmitterSpec.lean`](LeanTrominoes/PeriodicCNFPolySpaceClockResetEmitterSpec.lean)
  composes the bivariate clock-reset operand pass with an affine pass that
  emits one conjunction closer per unary clock marker.  Both retain the
  four-block prepared input, and the composed polynomial-time TM2 certificate
  extracts exactly the normalized reset-clock program at the reduction widths.
- [`LeanTrominoes/PeriodicCNFBinarySuccessorSchedule.lean`](LeanTrominoes/PeriodicCNFBinarySuccessorSchedule.lean)
  flattens the recursive no-overflow binary-successor program into explicit
  outer frames.  Each frame exposes its triangular higher-bit equality stream
  and fold ending, while one final suffix closes every carry branch, giving the
  next counter machine an exact postorder target.
- [`LeanTrominoes/PeriodicCNFMachineBivariateClockSuccessorTemplates.lean`](LeanTrominoes/PeriodicCNFMachineBivariateClockSuccessorTemplates.lean)
  specializes rise, fall, and bit-equality frames to the exact bivariate clock
  atom layout.  Its recursive triangular unary-token stream is proved equal to
  the complete normalized bounded-machine clock-successor program.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterSpec.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterSpec.lean)
  factors the successor recursion into a generic finite-recipe contract:
  outer templates, a strictly-higher inner range and fold, and fixed frame/base
  closers.  Its clock specialization is exactly the normalized successor token
  target, separating the future machine proof from clock semantics.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterMachine.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterMachine.lean)
  defines the finite triangular emitter core.  Separate persistent, outer,
  current, inner, and scratch counters drive the three fixed recipe blocks;
  higher-position markers are restored while emitting fold closers, and final
  carry closures are emitted while clearing the outer counter.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterConfigurations.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterConfigurations.lean)
  names every invariant control configuration, supplies exact update lemmas
  for all ten machine stacks, and proves the generic token/atom-unit push
  identities shared by scan, recipe, frame, cleanup, and reversal proofs.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterScan.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterScan.lean)
  bundles one machine instance's fixed selectors, recipes, and token blocks,
  proves all four selector cases, and lifts them across the complete input.
  The exact `length + 1` execution retains every workspace symbol and
  materializes both unary counts at the first outer-frame configuration.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterFirstCounter.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterFirstCounter.lean)
  verifies the first half of atom emission: the persistent runtime-width
  counter is scanned and restored exactly, emitting one first-stride block per
  marker.  Inner templates also emit precisely one second-stride block for the
  held current marker before position scanning begins.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterOuterCounter.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterOuterCounter.lean)
  verifies scanning and restoration of the completed-outer-position counter,
  including its exact second-stride output.  Outer stages advance to their next
  recipe or frame phase, while inner stages enter the additional inner-counter
  scan without changing any restored invariant stack.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterInnerCounter.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterInnerCounter.lean)
  verifies the final atom component for inner templates: each processed higher
  position emits one second-stride block, the counter is restored exactly, and
  control advances to the next equality recipe or the completed inner-position
  phase.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterRecipeStep.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterRecipeStep.lean)
  closes the one-step interface around those counter subroutines: fixed recipes
  append their literal token and advance, while atom recipes append their base
  unary run and enter the verified counter pipeline.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterOuterRecipe.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterOuterRecipe.lean)
  composes entry, persistent-width, and outer-position phases for a complete
  non-inner recipe.  It proves exact bivariate recipe-token output, restores
  both counters and scratch stacks, enters the correct continuation, and gives
  the closed runtime `2·first + 2·position + 5` for atom recipes.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterInnerRecipe.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterInnerRecipe.lean)
  composes entry with all three counter pairs for a complete inner recipe.  It
  proves that the atom position is exactly `outer + 1 + inner`, restores every
  invariant stack, and gives runtime `2·first + 2·outer + 2·inner + 7`.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterOuterTemplate.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterOuterTemplate.lean)
  lifts the verified non-inner recipe run over either complete outer template
  suffix.  Exact recipe tokens accumulate in semantic order, both unary
  counters and scratch stacks are restored between recipes, and the machine
  reaches the appropriate stage continuation with an additive exact runtime.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterInnerTemplate.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterInnerTemplate.lean)
  lifts the verified three-counter recipe run over the complete inner template.
  Every recipe is evaluated at the same exact triangular position
  `outer + 1 + inner`, invariant stacks are restored between recipes, and the
  final continuation records that the higher position has been completed.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterInnerPosition.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterInnerPosition.lean)
  verifies one full higher-position iteration, including both empty and
  nonempty inner templates.  It removes exactly one `remaining` marker, emits
  the template at `outer + 1 + inner`, transfers that marker to
  `innerProcessed`, and returns to the common inner-loop invariant.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterInnerRange.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterInnerRange.lean)
  lifts the one-position theorem over every strictly higher marker.  Its exact
  output is the consecutive bivariate position range used by the semantic
  contract, all markers move from `remaining` to `innerProcessed`, and its
  recursive runtime has a genuine zero-step empty-range base case.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterInnerFold.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterInnerFold.lean)
  emits the inner base, restores every higher marker while emitting one fold
  closer, appends the frame closer, and enters the possibly empty outer-second
  template.  The proof gives the exact semantic token order and restores the
  full higher range to `remaining`.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterOuterStage.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterOuterStage.lean)
  packages the common entry convention for both non-inner templates.  Empty
  templates take a genuine zero-step run; nonempty templates use the verified
  recipe-list induction, and both paths reach the same continuation with exact
  full-template tokens and runtime.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterOuterFrame.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterOuterFrame.lean)
  composes one complete triangular frame: current-marker selection, the first
  outer template, every higher inner position, the full inner fold, the second
  outer template, and transfer to `processed`.  Its output is exactly the
  semantic `frameTokens` block and every scratch invariant is restored.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterOuterRange.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterOuterRange.lean)
  lifts that theorem over all outer markers.  It emits the exact consecutive
  triangular frame prefix, empties `remaining`, accumulates every completed
  position in `processed`, and stops immediately before the final base and
  unwind suffix with a zero-step empty-range case.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterFinalFold.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterFinalFold.lean)
  handles that suffix: it emits `finalBase`, removes every completed outer
  marker while emitting one `finalCloser`, and reaches `clearFirst` with both
  outer counters empty.  The emitted suffix order and linear runtime are exact.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterCleanup.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterCleanup.lean)
  clears the persistent first counter and reverses an arbitrary accumulated
  workspace onto the output stack.  The generic execution theorems give exact
  runtimes, exact forward output, empty work stacks, and a genuinely halted
  configuration.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterSemantics.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterSemantics.lean)
  identifies the iterative frame prefix plus final unwind with the recursive
  semantic contract, then composes every verified phase from `initList` to
  `haltList`.  The resulting `TM2OutputsInTime` theorem emits exactly
  `TriangularTemplateEmitter.emitted` after the retained input workspace.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterBounds.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterBounds.lean)
  supplies fixed-coefficient bounds for recipe templates, inner-position
  ranges, individual frames, and complete frame ranges.  Both emitted token
  length and runtime are bounded by cubic-scale expressions in the two runtime
  selector counts, ready for the workspace polynomial certificate.
- [`LeanTrominoes/PeriodicCNFTriangularTemplateEmitterTime.lean`](LeanTrominoes/PeriodicCNFTriangularTemplateEmitterTime.lean)
  bounds both selector counts by the retained workspace length, derives a
  fixed cubic bound for exact output and total execution, and packages the
  finite machine as a `TM2ComputableInPolyTime` implementation of the complete
  triangular semantic emitter.
- [`LeanTrominoes/PeriodicCNFPolySpaceClockSuccessorEmitterSpec.lean`](LeanTrominoes/PeriodicCNFPolySpaceClockSuccessorEmitterSpec.lean)
  specializes that machine to the fixed rise, equality, and fall clock recipes.
  Its input-preserving pass and embedding/extraction wrapper are polynomial-time,
  and on prepared sources the exact emitted suffix is the normalized bounded-
  machine clock-successor program.
- [`LeanTrominoes/PeriodicCNFMachineAffineStackTemplates.lean`](LeanTrominoes/PeriodicCNFMachineAffineStackTemplates.lean)
  instantiates the affine language for the bounded machine's explicit stack
  atom layout.  It recovers shifted current and next cell tests, exact-one
  fields, cell-vector equality, and every interior occupied-prefix formula
  token for token, leaving the terminal constant-true suffix case explicit.
- [`LeanTrominoes/PeriodicCNFAffineEmitterPipeline.lean`](LeanTrominoes/PeriodicCNFAffineEmitterPipeline.lean)
  composes fixed affine phases over one stable `Data ⊕ Token` alphabet.
  Earlier token suffixes provably leave every later selector count unchanged;
  exact phase-order semantics, one-time input embedding, final token extraction,
  and a polynomial-time certificate are supplied for arbitrary fixed phase lists.
- [`LeanTrominoes/PeriodicCNFUnaryProgramTokenAlgebra.lean`](LeanTrominoes/PeriodicCNFUnaryProgramTokenAlgebra.lean)
  supplies the exact append laws and closing token suffixes for normalized
  finite conjunctions and disjunctions.  It also identifies a recursive affine
  position range with the flat unary-token stream of the corresponding
  evaluated ordinary postorder programs.
- [`LeanTrominoes/SelectedPrefixMarkerMachine.lean`](LeanTrominoes/SelectedPrefixMarkerMachine.lean)
  verifies the stateful preprocessing needed by boundary-sensitive phases.
  For a fixed finite cutoff it retains every input symbol, tags it by the
  number of earlier selected symbols capped at that cutoff, restores order,
  resets its finite state, and halts with exactly the tagged output.
- [`LeanTrominoes/SelectedPrefixMarkerTime.lean`](LeanTrominoes/SelectedPrefixMarkerTime.lean)
  proves the tag's boundary semantics: for every fixed `skip ≤ cutoff`,
  selecting tagged occurrences at or after `skip` has count exactly the
  original selected count minus `skip`.  Projection recovers the original word,
  and the exact two-pass execution receives a linear polynomial-time certificate.
- [`LeanTrominoes/PeriodicCNFMachineOneHotEmitterSpec.lean`](LeanTrominoes/PeriodicCNFMachineOneHotEmitterSpec.lean)
  gives the first complete concrete emitter schedule.  Two literal finite
  fields, one affine cell phase per machine stack, and fixed/dynamic closing
  phases emit exactly the normalized `oneHotFields` postorder program for any
  runtime stack width, including its precise right-associated conjunction suffix.
- [`LeanTrominoes/PeriodicCNFMachineWellFormedEmitterSpec.lean`](LeanTrominoes/PeriodicCNFMachineWellFormedEmitterSpec.lean)
  uses capped prefix tags to run each occupied-prefix phase exactly `space − 1`
  times, adds the terminal constant-true boundary per stack, and emits the exact
  dynamic conjunction suffix.  Concatenating this schedule with the one-hot
  phases recovers the complete normalized `wellFormedFields` token stream.
- [`LeanTrominoes/PeriodicCNFMachineFixedConfigurationEmitterSpec.lean`](LeanTrominoes/PeriodicCNFMachineFixedConfigurationEmitterSpec.lean)
  splits every stack of a fixed endpoint into literal occupied-prefix tests and
  an affine unused-cell tail selected by its capped prefix tag.  Exact range and
  fold identities prove the resulting fixed phase schedule emits the complete
  normalized current- or next-configuration test at every fitting runtime width.
- [`LeanTrominoes/PeriodicCNFPolySpaceAcceptingEmitterSpec.lean`](LeanTrominoes/PeriodicCNFPolySpaceAcceptingEmitterSpec.lean)
  chooses the designated accepting configuration's fixed configuration-space
  size as its prefix-marker cutoff.  It proves every accepting stack fits both
  that cutoff and the runtime reduction width, then identifies the phase output
  on the concrete prepared unary word with the exact current/next endpoint test.
- [`LeanTrominoes/PeriodicCNFPolySpaceRequestPadding.lean`](LeanTrominoes/PeriodicCNFPolySpaceRequestPadding.lean)
  specializes unary Horner padding to the exact stack-width polynomial of a
  source decider.  It proves that the reversed native polynomial coefficient
  list evaluates correctly, counts one delimiter per canonical source field,
  identifies the resulting padding with the bounded compiler's selected
  stack width, then composes a second Horner phase that appends the exact
  reset-clock width and a third phase that appends the exact source-atom
  boundary used as the request's `fresh` header.  The resulting polynomial-time
  certificate exposes the preserved native source and all three dynamic
  counters as distinct finite marker blocks.  Three subsequent verified
  binary-count passes append their exact canonical native encodings without
  allowing any later appendix to affect an earlier marker count.
- [`LeanTrominoes/PeriodicCNFPolySpaceSourcePreparation.lean`](LeanTrominoes/PeriodicCNFPolySpaceSourcePreparation.lean)
  prepares the simpler direct finite-source stream for the concrete request
  printer.  It first embeds source symbols into an always-inhabited option
  alphabet, then appends tagged unary space, clock, and fresh blocks and their
  three canonical native binary counters.  Exact layout and marker-count
  theorems connect the stream to the bounded compiler parameters, while
  verified finite transduction, Horner, binary-count, and composition
  certificates prove that the entire preparation is polynomial-time.
- [`LeanTrominoes/TM2OutputLength.lean`](LeanTrominoes/TM2OutputLength.lean)
  counts primitive pushes along every finite statement path and sums those
  counts into a uniform one-step allowance.  It proves total stack population
  grows by at most that allowance per counted step, yielding an explicit
  polynomial output-length bound for every `TM2ComputableInPolyTime` witness
  and the quantitative intermediate-size fact needed for composition.
- [`LeanTrominoes/TM2CompositionMachine.lean`](LeanTrominoes/TM2CompositionMachine.lean)
  constructs polynomial-time sequential composition through a finite
  intermediate alphabet.  It embeds both component machines step-for-step,
  transfers the intermediate stream in order by two stack reversals in
  exactly four steps per symbol plus two, and combines that run with the
  first machine's output-length envelope into an explicit polynomial-time
  certificate.
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
  selected `branchZero` paths and a generic tagged-countdown body rule.  It
  also exposes reusable input-linear estimates for tail, fixed-index `get`,
  constant-zero output, and `prepend`, plus a common bound for encoded lists
  whose fields share one numeric limit.  Thus the remaining transition
  majorants can reuse one fixed-width adapter calculation.
- [`LeanTrominoes/PartrecBinaryLengthSpace.lean`](LeanTrominoes/PartrecBinaryLengthSpace.lean)
  gives the matching quantitative proof for the explicit binary search-depth
  computation.  Division by two is a fully fitted evaluator call: its
  quotient/parity loop uses a preserved processed-count invariant, and
  monotonicity of binary encoding length bounds every live quotient by the
  original input's bit length.  The outer binary-length loop preserves the
  sum of its counter and remaining bit length, after which a fixed fitted
  countdown computes `21 × length + 22`.  Reusable lemmas now also bound the
  binary lengths of sums, products, and natural pairs by the operand lengths,
  supporting polynomial input-length bounds for nested geometric codes.
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
  compositional evaluator-space certificate.  The complete paired frontier
  quotient/remainder decoder now also has one explicit input-linear workspace
  bound.  Thus later motif scans can stream both frontier assignments without
  allocating either assignment list.
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
  for the complete packed assignment lookup; the named envelope itself is now
  bounded directly by the four native query-field bit lengths.
- [`LeanTrominoes/PartrecPackedAssignmentPredicates.lean`](LeanTrominoes/PartrecPackedAssignmentPredicates.lean)
  and
  [`LeanTrominoes/PartrecPackedAssignmentPredicatesSpace.lean`](LeanTrominoes/PartrecPackedAssignmentPredicatesSpace.lean)
  turn that lookup into the first semantic packed-frontier predicate:
  digit zero is proved equivalent to an absent assignment, and the resulting
  `none` test is fitted by composing the lookup, one projection, and one
  zero test.  They also compare the selected digit with the canonical digit
  of any fixed assignment state, proved semantically equivalent to selecting
  that state and fitted through explicit equality arguments.  The projected
  lookup digit and the complete fixed-state equality test now each have named
  evaluator-space bounds, and all three predicate envelopes are bounded
  directly by the four native query-field bit lengths for reuse by later
  packed predicates.
- [`LeanTrominoes/PartrecPackedColumnPhase.lean`](LeanTrominoes/PartrecPackedColumnPhase.lean)
  and
  [`LeanTrominoes/PartrecPackedColumnPhaseSpace.lean`](LeanTrominoes/PartrecPackedColumnPhaseSpace.lean)
  compute the wrapped horizontal coordinate of any of the five packed
  frontier columns.  Three fitted additions, two predecessors, and the
  quotient/remainder primitive implement the semantic phase formula on a
  fixed-width native state.
- [`LeanTrominoes/PartrecMultiply.lean`](LeanTrominoes/PartrecMultiply.lean)
  and
  [`LeanTrominoes/PartrecMultiplySpace.lean`](LeanTrominoes/PartrecMultiplySpace.lean)
  supply the missing forward natural-multiplication program as a flat
  repeated-addition countdown with the fixed payload
  `[right, left, partialProduct]`.  Its nested fixed-width accumulator and
  outer countdown have an exact evaluator certificate and one explicit
  input-linear workspace majorant.  This is the arithmetic foundation for
  constructing the paired cell encodings needed by the center-validity leaf.
- [`LeanTrominoes/PartrecPair.lean`](LeanTrominoes/PartrecPair.lean) combines
  explicit comparison, multiplication, and addition into the forward
  `Nat.pair` program inverse to the existing unpairer.  In particular, later
  transition code can build encoded `Cell` queries for the packed frontier
  lookup without appealing to an opaque primitive-recursive compiler.
  [`LeanTrominoes/PartrecPairSpace.lean`](LeanTrominoes/PartrecPairSpace.lean)
  fits both square-and-add branches and their explicit comparison selector,
  yielding an exact evaluator-space certificate and a common input-linear
  workspace majorant for forward pairing.  That workspace unit is now also
  bounded directly by the two operand bit lengths.
- [`LeanTrominoes/PartrecIntOffset.lean`](LeanTrominoes/PartrecIntOffset.lean)
  implements successor, predecessor, and addition by a fixed integer directly
  on Mathlib's even/odd integer encoding.  These programs construct the
  vertically shifted motif coordinates inspected by center validity.
- [`LeanTrominoes/PartrecIntOffsetSpace.lean`](LeanTrominoes/PartrecIntOffsetSpace.lean)
  follows every parity branch of those offset programs with exact evaluator
  costs, composes them over arbitrary fixed offsets, and bounds the result
  linearly in one encoded arithmetic envelope.  Both the envelope and the
  shifted result code have explicit bit-length bounds in the input and fixed
  offset magnitude.
- [`LeanTrominoes/PartrecPackedTargetCell.lean`](LeanTrominoes/PartrecPackedTargetCell.lean)
  constructs the canonical encoded cell addressed by a packed frontier
  column and a fixed vertical source offset.  It explicitly computes and
  encodes the wrapped horizontal phase, offsets the row, and pairs the two
  coordinates in Mathlib's standard `Cell` encoding.
- [`LeanTrominoes/PartrecPackedTargetCellSpace.lean`](LeanTrominoes/PartrecPackedTargetCellSpace.lean)
  fits every stage of that target-cell constructor, culminating in an exact
  evaluator-space certificate for the encoded canonical cell.  Its final
  theorem combines one affine arithmetic envelope with the existing pairing
  envelope to give a linear encoded-space majorant, and that unit is now
  bounded directly by the five native arithmetic-field bit lengths.
- [`LeanTrominoes/PeriodicStripCanonicalMembership.lean`](LeanTrominoes/PeriodicStripCanonicalMembership.lean)
  proves that well-formed strip carrier membership is exactly finite motif
  membership at the unique fundamental-domain representative, and specializes
  this bridge to the physical and canonical coordinates of packed columns.
- [`LeanTrominoes/PeriodicStripFlatEncoding.lean`](LeanTrominoes/PeriodicStripFlatEncoding.lean)
  serializes width, period, motif length, and motif coordinates as one flat
  delimiter-separated binary stream and proves its executable decoder is a
  left inverse.  This is the finite encoding now used by `Theorem52.stripStatement`.
- [`LeanTrominoes/PeriodicStripFlatEncodingSize.lean`](LeanTrominoes/PeriodicStripFlatEncodingSize.lean)
  proves the flat symbol length dominates motif length and the period's binary
  length.  Consequently the existing sparse frontier graph still has Savitch
  depth at most a linear function of the new input size.
- [`LeanTrominoes/PartrecFlatFieldPolySpace.lean`](LeanTrominoes/PartrecFlatFieldPolySpace.lean)
  packages a run-fitted partial-recursive evaluator on any verified flat field
  representation as the project's explicit finite-machine PSPACE certificate.
  The native `trList` input identity avoids constructing a nested code or an
  alphabet-conversion machine.
- [`LeanTrominoes/PartrecFlatSavitchContextSpace.lean`](LeanTrominoes/PartrecFlatSavitchContextSpace.lean)
  fits runtime computation of the seven fixed Savitch fields plus six fields
  per continuation frame, preserves the complete evaluator payload, and
  bounds the ensuing dynamic suffix drop linearly in the native-list input
  footprint.
- [`LeanTrominoes/PartrecFlatSavitchStepSpace.lean`](LeanTrominoes/PartrecFlatSavitchStepSpace.lean)
  gives a compositional evaluator-space certificate for every branch of one
  flat Savitch DFS transition.  It retains the native strip fields after the
  variable DFS stack and substitutes the bounded recovered reflexive-or-edge
  oracle at recursion depth zero.
- [`LeanTrominoes/PartrecFlatSavitchReachSpace.lean`](LeanTrominoes/PartrecFlatSavitchReachSpace.lean)
  replaces the legacy paired-encoding search parameters by a sufficient
  power-of-two state bound and linear Savitch depth measured in the target
  flat input.  It bounds every reachable serialized DFS state together with
  the unchanged strip suffix and any remaining exact-fuel counter, then
  absorbs context recovery and the complete depth-zero edge oracle into one
  input-polynomial allowance for every reachable structural step.  A
  suffix-aware invariant lifts that allowance through the entire exact-fuel
  tail iteration without parsing motif fields as continuation frames.
- [`LeanTrominoes/PartrecFlatStripReach.lean`](LeanTrominoes/PartrecFlatStripReach.lean)
  initializes one indexed reachability query from four search fields followed
  by the native strip suffix, runs the suffix-preserving Savitch program, and
  proves that its projected output is the verified DFS reachability Boolean.
- [`LeanTrominoes/PartrecFlatStripReachSpace.lean`](LeanTrominoes/PartrecFlatStripReachSpace.lean)
  gives the corresponding exact evaluator-space composition, including fuel
  construction, retained-suffix input assembly, the complete Savitch call,
  answer projection, and Boolean normalization.  Its final theorem absorbs
  all of these costs into one polynomial bound in the target flat encoding
  length.
- [`LeanTrominoes/PartrecFlatStripCycle.lean`](LeanTrominoes/PartrecFlatStripCycle.lean)
  and [`LeanTrominoes/PartrecFlatStripCycleSpace.lean`](LeanTrominoes/PartrecFlatStripCycleSpace.lean)
  scan both frontier endpoints over the padded state space, preserve the
  native strip suffix through every countdown, and decide whether the finite
  strip-frontier graph contains a directed cycle within a polynomial
  evaluator-space reserve.
- [`LeanTrominoes/PartrecFlatStripDecider.lean`](LeanTrominoes/PartrecFlatStripDecider.lean)
  and [`LeanTrominoes/PartrecFlatStripDeciderSpace.lean`](LeanTrominoes/PartrecFlatStripDeciderSpace.lean)
  assemble the streamed target length, Savitch parameters, structural guard,
  and cycle scan into the final native-flat Boolean evaluator.  The latter
  mirrors the complete exact cost by an explicit polynomial and packages
  `flatPeriodicStripTrominoTiling_inPSPACE` for
  `PeriodicStripFlatEncoding.finEncoding`.
- [`LeanTrominoes/PartrecFlatStripFrontierContextSpace.lean`](LeanTrominoes/PartrecFlatStripFrontierContextSpace.lean)
  fits the strip-suffix projections, decodes both queried frontier indices
  into word and phase, and assembles the native seven-field packed-transition
  context while retaining the motif-coordinate stream.  Its explicit bound
  charges suffix recovery, arithmetic decoding, every field projection, and
  all intermediate list assembly to one polynomial native-input envelope.
- [`LeanTrominoes/PartrecFlatStripTransitionSpace.lean`](LeanTrominoes/PartrecFlatStripTransitionSpace.lean)
  composes that recovered context with the bounded complete packed transition,
  then fits query-index equality and their reflexive disjunction.  The public
  certificates bound both the indexed edge and the full depth-zero Savitch
  oracle in the original variable-suffix input representation.
- [`LeanTrominoes/PartrecFlatStripWellFormed.lean`](LeanTrominoes/PartrecFlatStripWellFormed.lean)
  ports periodic-strip structural validation to those native flat fields.  Its
  exact motif-length countdown consumes two coordinate fields per cell,
  reuses the verified cell-bounds predicate, and never constructs the legacy
  recursively paired motif code.
- [`LeanTrominoes/PartrecFlatStripWellFormedSpace.lean`](LeanTrominoes/PartrecFlatStripWellFormedSpace.lean)
  fits every coordinate-pair step, lifts the fits through the exact flat
  countdown, and bounds header preparation, the complete scan, and result
  projection quadratically in the target flat input length.
- [`LeanTrominoes/PartrecFlatPackedCenterCoverageSpace.lean`](LeanTrominoes/PartrecFlatPackedCenterCoverageSpace.lean)
  fits the 24 fixed center-covering candidate tests, their exact sum, and the
  final comparison with one over the native flat motif fields.  Reconstructed
  target queries have a uniform quadratic bound, which is lifted through the
  compile-time candidate list to a quadratic evaluator-space certificate for
  exact-one coverage.
- [`LeanTrominoes/PartrecFlatPackedCenterBaseSpace.lean`](LeanTrominoes/PartrecFlatPackedCenterBaseSpace.lean)
  fits the native phase guard and combines it with eight-way containment and
  exact-one coverage at one flat motif base.  Its only compatibility adapter
  pairs the two base-coordinate fields for an existing verified arithmetic
  predicate; the complete one-base evaluator has a quadratic native-input
  space certificate.
- [`LeanTrominoes/PartrecFlatPackedCenterLoopSpace.lean`](LeanTrominoes/PartrecFlatPackedCenterLoopSpace.lean)
  reconstructs each one-base center input from the indexed transition scan,
  fits the exact motif-length countdown, and proves a uniform polynomial-space
  bound for checking center validity over the complete flat motif.  The public
  wrapper computes `isCenterValidBool` directly and includes initialization,
  the full scan, and final result projection in its workspace certificate.
- [`LeanTrominoes/PartrecFlatPackedOverlapAtSpace.lean`](LeanTrominoes/PartrecFlatPackedOverlapAtSpace.lean)
  fits both native assignment-query adapters and their verified lookup calls
  for one shared-cell overlap comparison.  The final digit equality and all
  adapter overhead have a common quadratic bound in the seven-field flat
  overlap input, specialized to the semantic `overlapsAtBool` predicate.
- [`LeanTrominoes/PartrecFlatPackedOverlapLoopSpace.lean`](LeanTrominoes/PartrecFlatPackedOverlapLoopSpace.lean)
  reconstructs each indexed overlap query from the shared transition scan and
  lifts the quadratic leaf through the exact motif countdown.  It then fits
  and bounds the fixed conjunction of all four shared columns, including each
  scan's initialization and result projection.
- [`LeanTrominoes/PartrecFlatPackedNormalizationAllSpace.lean`](LeanTrominoes/PartrecFlatPackedNormalizationAllSpace.lean)
  combines the five individually bounded flat normalization scans with their
  exact nested Boolean conjunction.  Its public certificate evaluates
  `isNormalizedBool` on the native transition context within one explicit
  polynomial workspace bound.
- [`LeanTrominoes/PartrecFlatPackedTransitionSpace.lean`](LeanTrominoes/PartrecFlatPackedTransitionSpace.lean)
  fits cyclic phase advance directly on the flat fields, including the
  quotient/remainder evaluator, and proves a native-context linear bound for
  that computation.  It then combines the bounded normalization,
  center-validity, phase, and four-column overlap components through all three
  Boolean layers to certify the complete flat packed transition in polynomial
  workspace.
- [`LeanTrominoes/PartrecPackedTargetMembership.lean`](LeanTrominoes/PartrecPackedTargetMembership.lean)
  composes canonical-cell construction with the five-column motif scanner and
  projects its `found` bit.  The resulting explicit program is proved equal to
  physical periodic-strip membership for every translated source cell of a
  packed center candidate.
- [`LeanTrominoes/PartrecPackedTargetMembershipSpace.lean`](LeanTrominoes/PartrecPackedTargetMembershipSpace.lean)
  fits the complete membership leaf compositionally: fixed-column input
  assembly, canonical target construction, streaming motif lookup, and the
  final normalized `found` projection all have exact evaluator-space costs.
  A shared unit combining the target constructor, lookup scanner, and bounded
  list adapters now gives the whole leaf an explicit input-linear workspace
  majorant.  That unit is itself bounded linearly by the bit lengths of the
  period, phase, encoded motif and row, assignment word, column, and fixed
  vertical-offset magnitude; the lookup-input prefix inherits the same
  envelope for reuse by covering-candidate queries.
- [`LeanTrominoes/PartrecPackedCenterCandidate.lean`](LeanTrominoes/PartrecPackedCenterCandidate.lean)
  combines one fixed assignment-selection test with the three translated
  membership leaves of a tromino placement.  For either tromino and every
  square symmetry, the explicit program computes exactly the corresponding
  center-containment implication at one motif base.
- [`LeanTrominoes/PartrecPackedCenterCandidateSpace.lean`](LeanTrominoes/PartrecPackedCenterCandidateSpace.lean)
  fits that candidate implication end to end, including center assignment
  selection, three canonical membership calls, both fixed conjunctions, and
  the final Boolean implication, all without decoding the packed frontier.
  Linear bounds for both six-field adapters feed explicit envelopes for each
  source-cell test, their fixed three-way conjunction, and the complete
  center-candidate predicate.
- [`LeanTrominoes/PartrecPackedCenterSymmetries.lean`](LeanTrominoes/PartrecPackedCenterSymmetries.lean)
  folds the eight fixed square-symmetry candidate implications at one motif
  base and proves that the explicit program computes exactly the semantic
  `List.all` center-containment condition.
- [`LeanTrominoes/PartrecPackedCenterSymmetriesSpace.lean`](LeanTrominoes/PartrecPackedCenterSymmetriesSpace.lean)
  fits that eight-way conjunction compositionally, with an exact recursive
  evaluator cost built from the already fitted candidate leaves.  A matching
  recursive workspace envelope now lifts the candidate bound through every
  Boolean node and specializes to the fixed list of eight symmetries.
- [`LeanTrominoes/PartrecPackedCenterCoveringCandidate.lean`](LeanTrominoes/PartrecPackedCenterCoveringCandidate.lean)
  constructs the canonical assignment lookup for one of the 24 fixed
  symmetry/source pairs that can cover a center target and proves that it is
  exactly the packed active-placement filter predicate.
- [`LeanTrominoes/PartrecPackedCenterCoveringCandidateSpace.lean`](LeanTrominoes/PartrecPackedCenterCoveringCandidateSpace.lean)
  fits that active-candidate lookup compositionally from the canonical target
  constructor and fixed-assignment predicate.  Both its query adapter and
  complete selection test now have explicit workspace bounds assembled from
  those two reusable envelopes.
- [`LeanTrominoes/PartrecPackedCenterCoverage.lean`](LeanTrominoes/PartrecPackedCenterCoverage.lean)
  sums the 24 fixed covering-candidate bits and compares the result with one;
  the program is proved equal to the length-one test on the semantic packed
  `activePlacementList`.
- [`LeanTrominoes/PartrecPackedCenterCoverageSpace.lean`](LeanTrominoes/PartrecPackedCenterCoverageSpace.lean)
  fits the complete fixed candidate sum and exact-one comparison, with exact
  evaluator costs for every addition and list-composition node.  A recursive
  bound controls the counter by the remaining candidate-list length; after
  specializing to the 24 candidates, it yields an explicit workspace bound
  for the complete exact-one predicate.
- [`LeanTrominoes/PartrecPackedCenterBase.lean`](LeanTrominoes/PartrecPackedCenterBase.lean)
  adds the horizontal phase guard to containment and exact-one coverage,
  yielding explicit programs for both semantic center conditions and their
  conjunction at one motif occurrence.
- [`LeanTrominoes/PartrecPackedCenterBaseSpace.lean`](LeanTrominoes/PartrecPackedCenterBaseSpace.lean)
  fits the direct phase comparison and both guarded center conditions through
  their final one-base conjunction.  Explicit envelopes now cover the phase
  adapter and test, the guarded containment and coverage branches, and the
  complete validity predicate for one motif base.
- [`LeanTrominoes/PartrecPackedCenterLoop.lean`](LeanTrominoes/PartrecPackedCenterLoop.lean)
  streams the combined one-base checker across the encoded motif, recovers
  each head cell's row code on demand, and proves that the final accumulator
  is exactly `PackedWindowState.isCenterValidBool`.
- [`LeanTrominoes/PartrecPackedCenterLoopSpace.lean`](LeanTrominoes/PartrecPackedCenterLoopSpace.lean)
  fits every streaming center step and the complete motif scan under one exact
  reachable-suffix workspace envelope.  The local center-base bounds and
  shared normalization projections now yield one explicit polynomial
  envelope for every reachable suffix state and for the closed center-validity
  program.  Every fixed assignment, translated-membership, symmetry, and
  covering-candidate layer is now bounded by the shared six-field center
  input size.  A motif member's encoded base and row are bounded by the
  encoded motif itself, so the maximum over all bases introduces no motif
  length factor; consequently the complete center-validity envelope is
  linear in the four native normalization-scan field lengths.
- [`LeanTrominoes/PartrecPackedNormalizedAt.lean`](LeanTrominoes/PartrecPackedNormalizedAt.lean)
  and
  [`LeanTrominoes/PartrecPackedNormalizedAtSpace.lean`](LeanTrominoes/PartrecPackedNormalizedAtSpace.lean)
  decide normalization at one motif occurrence.  The program compares the
  signed horizontal cell coordinate with its wrapped column phase or accepts
  an absent packed assignment; the fitted Boolean composition is proved
  equal to `PackedWindowState.normalizedAtBool`.  Its evaluator cost is
  bounded explicitly by a fixed constant times the encoded size of one
  arithmetic envelope containing the period, phase, motif, cell, column,
  and packed word.  This envelope is now bounded linearly by those six native
  field bit lengths; its always-evaluated coordinate-test prefix inherits the
  same bound for reuse by center phase guards.
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
- [`LeanTrominoes/PartrecPackedNormalizationAll.lean`](LeanTrominoes/PartrecPackedNormalizationAll.lean)
  invokes that streaming checker at each of the five fixed frontier columns
  and conjoins the results directly.  Its four-field program is proved
  exactly equal to `PackedWindowState.isNormalizedBool` without constructing
  either the motif assignment list or a list of columns.
  [`LeanTrominoes/PartrecPackedNormalizationAllSpace.lean`](LeanTrominoes/PartrecPackedNormalizationAllSpace.lean)
  composes the five fitted column calls through the four short-circuiting
  conjunctions, giving an exact continuation-independent evaluator-space
  certificate for the complete normalization program and a single explicit
  input-linear workspace majorant shared by all five calls.
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
  fixed column adapters and their nested conjunction are fitted exactly, and
  the complete conjunction now has one shared input-linear evaluator-space
  majorant.
- [`LeanTrominoes/PartrecPackedTransition.lean`](LeanTrominoes/PartrecPackedTransition.lean)
  composes packed normalization, center validity, cyclic phase advance, and
  the four shared-column checks into one explicit six-field transition
  program.  Its acceptance theorem identifies the computed Boolean exactly
  with the raw semantic `Transition` relation used by the strip proof.
  [`LeanTrominoes/PartrecPackedTransitionSpace.lean`](LeanTrominoes/PartrecPackedTransitionSpace.lean)
  fits every adapter and component of that complete transition, including the
  modulo-period phase comparison and both final Boolean conjunctions, with an
  exact continuation-independent evaluator-space cost.  Its six-field input
  adapters and cyclic phase computation now share one explicit polynomial
  workspace envelope.  The fitted normalization, center-validity, and overlap
  majorants and all three final Boolean conjunction layers are absorbed into
  one explicit polynomial-space bound for the complete transition program.
- [`LeanTrominoes/PartrecStripTransition.lean`](LeanTrominoes/PartrecStripTransition.lean)
  and
  [`LeanTrominoes/PartrecStripTransitionSpace.lean`](LeanTrominoes/PartrecStripTransitionSpace.lean)
  connect the packed predicate to the indexed-search leaf.  They explicitly
  decode `[encodedStrip, firstIndex, lastIndex]`, retain the motif and two
  assignment words in packed form, permute the seven native context fields,
  and prove both semantic correctness and an exact fitted evaluator cost for
  `indexedTransitionRawBool`.  The context decoder, fixed field permutation,
  and complete packed predicate now compose into one polynomial-space bound
  for this indexed edge.  They also explicitly implement and fit the
  reflexive-or-edge predicate used at Savitch recursion depth zero, including
  a polynomial-space bound for its equality test and final disjunction.
  Binary-length bounds now absorb the packed normalization, center,
  overlap, and native-transition envelopes into one common strip-context
  unit.  The complete indexed edge and reflexive-or-edge leaf therefore each
  have an explicit constant-linear bound in the encoded strip and the two
  queried frontier indices.
- [`LeanTrominoes/PartrecStripFrontierContext.lean`](LeanTrominoes/PartrecStripFrontierContext.lean)
  and
  [`LeanTrominoes/PartrecStripFrontierContextSpace.lean`](LeanTrominoes/PartrecStripFrontierContextSpace.lean)
  connect that decoder to the actual leaf payload
  `[encodedStrip, firstIndex, lastIndex]`.  The explicit program returns the
  fixed-width native context
  `[width, period, motifCode, firstWord, firstPhase, lastWord, lastPhase]`;
  its fitted certificate composes only the verified strip-header decoder,
  quotient/remainder calls, field projections, and native-list assembly.  A
  common encoded-input envelope now bounds that complete seven-field decoder.
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
  supplies the evaluator's strip-specific depth-zero program from the
  concrete indexed transition code, replacing the earlier noncomputable
  code-choice leaves.  It extracts
  the encoded strip and two queried frontier indices from the flat payload,
  computes equality or the indexed frontier edge relation, and is connected
  to both the verified small step and the tail-recursive iterator under the
  well-formed strip invariant.  A
  separately verified raw-edge program supports the outer cycle scan.
- [`LeanTrominoes/StripFrontierCyclePartrec.lean`](LeanTrominoes/StripFrontierCyclePartrec.lean)
  builds the complete parameterized cycle-search driver.  One wrapper
  initializes a reachability query and runs its exact verified fuel; nested
  tail-recursive countdowns then scan both frontier endpoints while retaining
  only loop counters, a Boolean accumulator, and the current flat DFS stack.
  The parameterized driver is proved equal to
  `cycleSearchIndexDFSBoolAtDepth`; a unary front end computes the strip's
  padded state bound and certified search depth, branches before search to
  reject malformed presentations,
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
  arithmetic reserve.  Bounded frontier indices are now converted to the
  original unary strip input length, and one tromino-independent polynomial
  reserve covers both explicit transition leaves.
  `StripEvaluatorLeafCallsFit` records the continuation-passing reserve
  contract, while `stripEvaluatorLeafCallsFit_explicit` discharges it for
  both the base relation and raw edge using the fitted transition programs.
  `StripSavitchStep.exactStep` gives a uniform compositional evaluator
  certificate for every control-flow branch of one compiled
  strip-specialized Savitch DFS transition, including its depth-zero leaf,
  stack-frame rewrites, and Boolean accumulator updates.
  `stripSavitchStepCost_le` absorbs that exact branch certificate into one
  input-polynomial allowance for every reachable state with bounded frontier
  indices.  `stripSavitchFlatUniform` then carries the reachable-state
  invariant through the complete exact-fuel tail iterator, so the entire
  indexed reachability search reuses one polynomial workspace reserve.
  `stripReachInput_fits` certifies the preceding fixed-width adapter,
  including its exact-fuel subcall, and `stripReachInputCost_le` absorbs that
  adapter into the polynomial reserve for one complete reachability query.
  `stripReachBool_fits_polynomial` composes the adapter, full Savitch search,
  answer-field projection, and Boolean normalization into the bounded
  reachability call consumed by the outer endpoint scans.
  `StripCandidateStep.exactStep_polynomial` now composes that call with the
  raw edge leaf and both Boolean combinators, rebuilds the six-field inner
  countdown payload, and bounds the entire candidate update by the common
  input polynomial.  A generic bounded-field assembly lemma keeps this
  fixed-width accounting reusable without expanding every nested list
  prepend.  `StripCandidateStep.flatUniform` then carries a canonical
  six-field reachable-payload invariant through the complete synchronized
  second-endpoint countdown.  Its semantic iterate theorem proves that the
  Boolean accumulator checks exactly all smaller endpoint indices, while the
  evaluator reuses one polynomial body reserve independent of the number of
  graph states.  `StripCandidateStep.InnerScan.exact_polynomial` wraps that
  loop with verified fixed-width input and output adapters, so one complete
  second-endpoint scan is now available as a polynomial-space outer-loop
  step.  `StripCandidateStep.OuterScan.flatUniform` carries that step through
  every first endpoint with a canonical five-field invariant and proves that
  the resulting accumulator checks every ordered endpoint pair.
  `StripCandidateStep.CycleSearch.exact_polynomial` adds the fixed initializer
  and Boolean projection around that nested scan, obtaining a polynomial-space
  certificate for the complete parameterized search at the exact frontier
  index count.  The parallel `StripCandidateStep.Padded` hierarchy generalizes
  the reachability calls, candidate update, both synchronized endpoint scans,
  initializer, and Boolean projection to any count at most the unary driver's
  padded power-of-two bound.  `StripCycleParameters.exact_polynomial` then
  assembles that count and the certified depth, while
  `StripGuardedCycle.exact_polynomial` connects the complete search to the
  malformed-input rejection guard.  Finally,
  `periodicStripTrominoTilingCode_fits` and
  `periodicStripTrominoTilingCode_run_fits` package the unary evaluator and its
  complete run under the explicit polynomial, and
  `periodicStripTrominoTiling_inPSPACE` derives the PSPACE decision procedure
  for every tromino.
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
  proves the entire 2D conjunct from the isolated
  `NormalizedOrientationCoREHard` interface.  The Wang-to-planar-3DM
  construction now supplies that interface.
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
- [`LeanTrominoes/PeriodicCNFPlanarRetainedEightOccurrenceSplitRoutesComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedEightOccurrenceSplitRoutesComputability.lean)
  proves that exact retained angular-spliced route lookup computable from the
  retained positioned formula, placement, compass ports, and ordered copies.
  An explicit proof-free equality connects the computation to the certified
  route family; every local Figure 7 geometry operation is primitive
  recursive.
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
- [`LeanTrominoes/RetainedRayRasterizationComputability.lean`](LeanTrominoes/RetainedRayRasterizationComputability.lean)
  equips the retained direction and ray types with primitive-recursive
  encodings, computes both exact ray classifiers and their length data, and
  proves the compass and routed-clause staircase generators primitive
  recursive.  Segment fallback and structural whole-polyline rasterization
  are therefore primitive recursive as well.
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
- [`LeanTrominoes/OrthogonalPolylineLoopErasureComputability.lean`](LeanTrominoes/OrthogonalPolylineLoopErasureComputability.lean)
  makes that verified normalizer executable.  It defines a proof-free
  right-to-left list loop erasure, proves that it selects exactly the support
  of Mathlib's dependent `Walk.bypass`, proves orthogonality testing primitive
  recursive, and derives primitive recursiveness of the total route
  normalizer.
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
- [`LeanTrominoes/RetainedAngularFanDirectSourceRouteChoiceComputability.lean`](LeanTrominoes/RetainedAngularFanDirectSourceRouteChoiceComputability.lean)
  encodes the finite clause kind and its kind-dependent literal index as
  canonical primitive-recursive data.  It provides checked and total choice
  constructors and proves that the complete positioned coordinated route is
  primitive recursive.  It also computes the raw retained clause-source
  selector, including bounded crossover and duplicator cases and routed-clause
  port lookup, separating the finite local atlas choice from the unbounded
  component-origin translation.
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
  route equality and exact translated head and last-point formulas.  Named
  uncurried metadata, candidate, and checked-selection stages expose the same
  pipeline compositionally.
- [`LeanTrominoes/RetainedAngularFanFinalDirectSourceRouteChoicePairs.lean`](LeanTrominoes/RetainedAngularFanFinalDirectSourceRouteChoicePairs.lean)
  inverts successful final choices to their canonical raw metadata
  representative and atlas entry.  Choices at distinct literal indices of
  one final clause therefore share one source and one anchor-normalization
  offset; transporting the raw pair certificate proves their complete
  coordinated routes avoid each other and meet only at their common heads.
- [`LeanTrominoes/RetainedAngularFanFinalDirectSourceRouteChoiceComputability.lean`](LeanTrominoes/RetainedAngularFanFinalDirectSourceRouteChoiceComputability.lean)
  proves every stage of that final selector primitive recursive: canonical
  representative metadata, physical anchor translation, optional raw-atlas
  selection, and the exact equality check against the deduplicated gauged
  route.
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
- [`LeanTrominoes/RetainedAngularFanFinalCoordinatedRoutesComputability.lean`](LeanTrominoes/RetainedAngularFanFinalCoordinatedRoutesComputability.lean)
  computes the exact source-scaled angular slot and Figure 7 occurrence
  suffix through flat clause/literal data, then combines them with a checked
  direct-source atlas choice.  The resulting complete successful direct
  occurrence route is primitive recursive, including its endpoint join.  It
  also computes the exact singleton-prefix escape test and scaled-source
  clause lookup used to dispatch the remaining fallback branches.  The
  exceptional branch classifies and source-scales its raw terminal, applies
  the computable escaped boundary splice, and joins the exact unchanged
  Figure 7 suffix, yielding a primitive-recursive complete occurrence route.
  The ordinary copied-occurrence path is computed from the scaled source
  terminal and the same suffix; a flattened metadata lookup also computes
  every translated implication-cycle route.  Together they recover the exact
  established total fallback family primitive recursively.  A proof-free
  staged dispatcher then selects among the direct, escaped, ordinary, and
  cycle routes, and is proved primitive recursive and extensionally equal to
  the published total route family, including malformed-index fallbacks.
  Composing this dispatcher with verified loop erasure computes the exact
  final normalized route and its first direction primitive recursively.
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
- [`LeanTrominoes/RetainedAngularFanSourceEscapedSpliceComputability.lean`](LeanTrominoes/RetainedAngularFanSourceEscapedSpliceComputability.lean)
  computes both the ordinary retained radial lane and the delayed-lane
  escape, their finite fan adapters, variable-tail replacement, and
  whole-polyline rasterization.  Consequently both complete generic boundary
  routes are primitive recursive in their source route, terminal datum, and
  slot.
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
  coordinated gates for the three polarity-normalized connector tables.
  Every site route and every active gate have disjoint segment interiors and
  mutually avoid point-to-interior contacts; the selected occurrence-and-color
  route has the stronger certificate that its only listed contact with the
  gate is their unique splice port.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMFixedGreenContactAudit.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMFixedGreenContactAudit.lean)
  records the repaired fixed-green/true interface explicitly.  Exhaustive
  finite certificates show endpoint-aware separation for every core/gate
  pair and identify the three intended splice contacts, one on each physical
  color lane.
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
  The executable `VariableLocalGateTableEndpointClear` certificate now gives
  full endpoint-aware `RoutesAvoidEachOther` for every core route and every
  coordinated fan in all three polarity-normalized tables, including the
  repaired fixed-green/true case.  Exhaustive finite classification further
  proves strict separation unless the core triple/color is exactly the fan's
  selected routed pair.  Both results survive source-coordinate translation;
  cores and fans owned by distinct variable macrocells remain strictly
  separated.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreRouteSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreRouteSeparation.lean)
  extends that all-pairs result across every complete coordinated occurrence
  route.  Source-route endpoint separation makes every variable center fresh
  from unrelated corridor interiors; strict inset bounds then separate the
  corridor and clause-side fan.  Because those two suffixes are contact-free,
  both joins preserve either the variable-side fan's endpoint-aware contact
  law or, for a nonmatching routed triple/color, its strict separation.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseCoreRouteSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseCoreRouteSeparation.lean)
  proves the complementary clause-side contact classifier.  A complete
  occurrence route can meet a finite clause core only at the occurrence
  route's outer clause tail, and this property is preserved while the
  variable fan, corridor, and clause fan are joined.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceAssembledRouteSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonSourceAssembledRouteSeparation.lean)
  decomposes every typed incidence route into its finite gadget core and an
  optional coordinated occurrence suffix.  It combines core/core, both
  core/suffix directions, and suffix/suffix separation to prove that every
  pair of distinct colored typed routes has full endpoint-aware
  `RoutesAvoidEachOther` separation.  Variable-owned cores are strictly
  separated from nonmatching suffixes; clause-owned contacts occur only at
  the suffix's outer tail.  These classifications make all four assembly
  cases preserve only advertised outer-endpoint contacts.
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
  clause-core center, the checked finite fan/core table classifies its only
  possible contact as the first point of the translated fan's outer tail.
  Variable-owned cores remain strictly separated from every translated
  clause fan.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedAssembledRouteSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMTranslatedAssembledRouteSeparation.lean)
  composes finite-core/core, both finite-core/occurrence-route orientations,
  and occurrence-route/occurrence-route separation.  Decomposing both full
  assembled incidences at their certified splice endpoints, with exact
  first-tail classifiers for the exceptional clause contact, proves full
  endpoint-aware separation between any complete typed route and every
  nonzero relative period translate of any other complete typed route.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedAssembledRouteSeparation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedAssembledRouteSeparation.lean)
  specializes full endpoint-aware typed-route separation to the final
  doubled, anchor-normalized construction.  It also transfers the result
  through numeric incidence-tag lookup, proving the same separation for
  every pair of distinct genuine routes stored by the assembled periodic
  drawing.
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
  specializes endpoint-aware translated typed-route separation to the
  doubled, anchor-normalized source and transports it through numeric
  incidence tags to every stored route.  Combining the nonzero translations
  with same-period separation proves both relative and absolute separation
  of all distinct lifted occurrences, and hence endpoint-only listed-point
  contacts for the final padded drawing.  It also proves continuous planarity
  without any remaining finite-neighbor hypothesis.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedContinuousPresentation.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedContinuousPresentation.lean)
  combines that continuous-planarity theorem with the already proved
  normalized vertex distinctness and fundamental-square bounds.  The final
  padded coordinated assembly is thereby packaged as a concrete continuously
  planar periodic 3DM presentation, with no residual geometric assumption.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedContractionEndpointContacts.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMRibbonPaddedContractionEndpointContacts.lean)
  applies the generic contraction theorem to that concrete padded assembly.
  Its previously proved simple routes and complete lifted separation now
  yield endpoint-only contacts for the actual contracted drawing consumed by
  vertex normalization.
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
  packages that exact concrete routing as a periodic 3DM presentation.  Its
  continuous-planarity certificate now states the required polarity
  convention explicitly; the separate routed polarity-normalization pipeline
  above supplies it.  Every colored element has degree two or three, and both
  perfect matching and abstract trichromatic orientation are proved equivalent
  to satisfiability of the original local periodic CNF.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonThreeDMComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonThreeDMComputability.lean)
  computes the final quotient gauge, gauged clockwise formula, factor-two
  padding, clause-anchor normalization, and finite Dyer--Frieze encoding
  primitive recursively.  Its proof-free `PeriodicThreeDM` endpoint is proved
  exactly equal to the proof-backed continuously planar instance above.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonContraction.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonContraction.lean)
  suppresses every degree-two colored element in that concrete endpoint.
  Under the same explicit polarity convention, the resulting executable
  colored graph has a compatible, orthogonal, and continuously planar drawing;
  independently, its suppressed orientation predicate remains equivalent to
  satisfiability of the original periodic CNF.
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
  composition rules: a tail-contacting final piece can be joined on either
  side of an ordinarily separated pair without losing route separation.  It
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
- [`LeanTrominoes/PeriodicEightOccurrenceSplitPositionedRoutesComputability.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitPositionedRoutesComputability.lean)
  proves primitive recursiveness of the Manhattan detours, angular fan
  geometry, translated Figure 7 ring routes, and flattened cycle metadata
  used by the positioned fixed-eight route family.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitPositionedOccurrenceRouteComputability.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitPositionedOccurrenceRouteComputability.lean)
  gives proof-free data definitions for copied and complete angular-spliced
  route lookup, identifies them with the certified construction, and proves
  one copied occurrence route primitive recursive.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitPositionedCopiedRouteComputability.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitPositionedCopiedRouteComputability.lean)
  computes the nested copied-clause route lookup through balanced, flattened
  clause and literal data while retaining primitive-recursive local geometry.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitPositionedRouteLookupComputability.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitPositionedRouteLookupComputability.lean)
  combines copied incidences with appended Figure 7 implication-ring routes
  and proves both the proof-free and certified total route families
  computable.
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
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderingComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderingComputability.lean)
  instantiates the generic stable route-direction sorter with the exact
  primitive-recursive normalized retained route query.  It computes the
  first clockwise fixed-eight formula, the factor-two Figure 9 clearance
  scale, and both finite positioned exact-one replacements, yielding the
  twice-replaced raw unit-free exact-one formula primitive recursively.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalOrderingComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalOrderingComputability.lean)
  specializes the proof-free complete Figure 9 route computation to the
  retained source, normalizes each complete route, and computes the second
  and final clockwise clause ordering primitive recursively.  Pointwise
  agreement lemmas identify all three computed lookups with their existing
  proof-backed geometric definitions.
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
- [`LeanTrominoes/PeriodicCNFFlatEncoding.lean`](LeanTrominoes/PeriodicCNFFlatEncoding.lean)
  replaces the recursively paired standard list code with a flat stream over
  Mathlib's finite evaluator alphabet, using zero, one, and field delimiter
  while rejecting its unused list delimiter.  Explicit clause and literal
  counts make the executable decoder unambiguous, its round trip is verified,
  and formula list structure contributes only linearly many fields to the
  encoded output.
- [`LeanTrominoes/PeriodicCNFFlatEncodingSize.lean`](LeanTrominoes/PeriodicCNFFlatEncodingSize.lean)
  converts clause width, atom range, and clause count into a bound on actual
  encoded symbols.  It proves the transition compiler has width at most three
  and bounds all generated atoms by its final fresh boundary.
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
- [`LeanTrominoes/PeriodicCNFIncidenceGraphComputability.lean`](LeanTrominoes/PeriodicCNFIncidenceGraphComputability.lean)
  gives tagged clause/variable incidence vertices primitive-recursive
  constructors and proves the complete finite incidence-graph presentation
  primitive recursive from a periodic CNF source.
- [`LeanTrominoes/PeriodicCNFPlanarIncidenceComputability.lean`](LeanTrominoes/PeriodicCNFPlanarIncidenceComputability.lean)
  encodes metadata-rich CNF incidences and their translated route occurrences,
  proves the complete neighboring occurrence family primitive recursive, and
  computes every occurrence's constructed segments and canonical source and
  target terminals.
- [`LeanTrominoes/PeriodicOrthocrossingConstructionComputability.lean`](LeanTrominoes/PeriodicOrthocrossingConstructionComputability.lean)
  encodes edge-end ports and proves their ranks, private track coordinates,
  case-split edge cores, complete polylines, and the resulting periodic grid
  drawing primitive recursive from a finite periodic graph.
- [`LeanTrominoes/PeriodicOrthocrossingCrossingHaloComputability.lean`](LeanTrominoes/PeriodicOrthocrossingCrossingHaloComputability.lean)
  encodes retained crossing records and proves the neighboring translated
  segment occurrences, oriented intersection candidates, genuine-crossing
  predicate, filtering, and deduplication primitive recursive.
- [`LeanTrominoes/PeriodicOrthocrossingCanonicalComputability.lean`](LeanTrominoes/PeriodicOrthocrossingCanonicalComputability.lean)
  proves the finite fundamental-square point enumeration, full canonical
  crossing candidate product and filter, and horizontal-first representative
  list primitive recursive.
- [`LeanTrominoes/PeriodicOrthocrossingCarrierEncodingComputability.lean`](LeanTrominoes/PeriodicOrthocrossingCarrierEncodingComputability.lean)
  gives segment endpoints and terminals, crossing sides and boundaries,
  carrier nodes, equality positions, and generic positioned equality links
  canonical product/sum encodings with primitive-recursive accessors.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierComputability.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierComputability.lean)
  proves the bounded canonical crossing orbit, retained boundary and terminal
  enumerations, carrier keys and macro-grid positions, axial order, and stable
  per-carrier chain sorting primitive recursive.  It also certifies adjacent
  pairs, crossover-site suppression, equality-clause positions, and the raw
  flattened carrier-link family, then computes period shifts and filters it
  to the zero-shift representative of each retained-link orbit.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedCarrierFormulaComputability.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedCarrierFormulaComputability.lean)
  gives embedded clauses their canonical product encoding, proves positioned
  equality instances and finite equality families primitive recursive, and
  specializes this construction to the retained carrier formula.
- [`LeanTrominoes/PeriodicOrthocrossingBendComputability.lean`](LeanTrominoes/PeriodicOrthocrossingBendComputability.lean)
  encodes route bends, enumerates every bend in the neighboring route block,
  constructs their positioned equality links, and combines them with the
  retained carriers into the executable wire formula.
- [`LeanTrominoes/PlanarThreeSATComputability.lean`](LeanTrominoes/PlanarThreeSATComputability.lean)
  gives the fixed crossover variables, internal variables, and four-port
  records canonical encodings, then proves generic embedded-clause renaming,
  placement, gadget instantiation, and finite crossover families primitive
  recursive.
- [`LeanTrominoes/PeriodicOrthocrossingCrossoverComputability.lean`](LeanTrominoes/PeriodicOrthocrossingCrossoverComputability.lean)
  proves the canonical crossing ports and fixed crossover family primitive
  recursive, scopes the retained route-wire formula into the gadget variable
  type, and combines both parts into an executable retained planar core.
- [`LeanTrominoes/PeriodicCNFPlanarVertexGadgetsComputability.lean`](LeanTrominoes/PeriodicCNFPlanarVertexGadgetsComputability.lean)
  computes neighboring clause and variable sites, their stable routed
  incidence orders and endpoint terminals, the positioned signed-clause and
  active duplicator-arm families, and their composition with the retained
  crossover/wire core into the complete retained planar-SAT formula.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedClauseMetadataComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedClauseMetadataComputability.lean)
  gives the five crossover, retained-carrier, bend, routed-clause, and
  routed-variable source kinds canonical encodings, computes each local
  embedded formula with its source indices, and proves their exact global
  metadata enumeration primitive recursive in retained formula order.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputability.lean)
  computes the fixed crossover rays, retained carrier lenses, routed-clause
  ports, routed-variable arms, and translated corner-table routes used by the
  retained local incidence drawing.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedBendRouteComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedBendRouteComputability.lean)
  computes each retained bend route directly from the CNF presentation size
  and proves it equals the corresponding semantic corner-drawing route.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedLocalIncidenceRouteLookupComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedLocalIncidenceRouteLookupComputability.lean)
  decodes all five clause-source constructors, selects their exact local
  route, and proves the complete metadata-indexed semantic route family
  primitive recursive and computable.
- [`LeanTrominoes/PositionedPeriodicCNFRouteTransportComputability.lean`](LeanTrominoes/PositionedPeriodicCNFRouteTransportComputability.lean)
  proves the generic clause-anchor route normalization and first-orbit
  representative reindexing primitive recursive from a positioned formula,
  physical period, and finite route lookup, together with the corresponding
  representative-indexed lookup for arbitrary primitive-recursive auxiliary
  lists.
- [`LeanTrominoes/PeriodicCNFPlanarPeriodicizationComputability.lean`](LeanTrominoes/PeriodicCNFPlanarPeriodicizationComputability.lean)
  gives periodic planar-SAT protovariables and their opaque wrappers canonical
  encodings, computes canonical crossing representatives and literal period
  shifts, and proves retained finite-block periodicization and formula
  wrapping primitive recursive.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATPeriodicizationComputability.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPlanarSATPeriodicizationComputability.lean)
  lifts that construction to positioned clauses, applies the opaque wrapper,
  computes every periodic variable position and its canonical period-cell
  quotient, applies the variable and clause-anchor gauges, and selects one
  representative per periodic clause orbit.  Thus the final
  `retainedPlanarSATFormula` is primitive recursive.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedGaugedRoutesComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedGaugedRoutesComputability.lean)
  specializes generic route transport to the retained planar-SAT source,
  proving its exact anchor-normalized and clause-orbit-deduplicated incidence
  route lookups primitive recursive and computable.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedRepresentativeItemComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedRepresentativeItemComputability.lean)
  specializes the generic auxiliary representative lookup once to the large
  retained wrapped planar-SAT quotient, keeping that type-level construction
  out of downstream selector proofs.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedEightOccurrenceSplitComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedEightOccurrenceSplitComputability.lean)
  computes the angular east-first compass port at every retained incidence and
  proves the exact retained fixed-eight occurrence-split formula primitive
  recursive and computable.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitPositionedComputability.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitPositionedComputability.lean)
  encodes the fixed nine-copy ring vertices and proves all local ring
  coordinates, positioned clauses, positioned split formulas, and companion
  placement queries primitive recursive from finite source data.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedEightOccurrenceSplitPositionedComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedEightOccurrenceSplitPositionedComputability.lean)
  specializes the positioned compiler to the gauged retained planar-SAT
  construction, proving its exact positioned fixed-eight formula computable
  and its retained period and variable-position queries primitive recursive.
- [`LeanTrominoes/PeriodicOneInThreePositionedComputability.lean`](LeanTrominoes/PeriodicOneInThreePositionedComputability.lean)
  computes the positioned Figure 9 clause gadgets and full formula, together
  with the induced period and every original or auxiliary variable position.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedComputability.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsPositionedComputability.lean)
  does the same for the empty- and unit-clause exact-one replacements,
  including the arity-dependent generated clause coordinates.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineMetadataComputability.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineMetadataComputability.lean)
  flattens the proof-oriented composed Figure 9 metadata to its source and
  presentation indices, proves exact agreement with the certified metadata,
  and computes the resulting clause-index table primitive recursively.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineLocalRouteComputability.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineLocalRouteComputability.lean)
  computes the finite arity-specific Figure 9 route tables, the twice-refined
  placement, and the exact anchor-normalized local route lookup primitive
  recursively.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineSuffixCoreComputability.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineSuffixCoreComputability.lean)
  computes source-literal indices, bounded connector slots, finite connector
  routes, and the translated connector-plus-source-tail suffix, proving exact
  agreement with the certified ordered fan construction.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineSuffixComputability.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineSuffixComputability.lean)
  combines the proof-free connector core with flattened clause metadata,
  proves the total inherited-suffix dispatcher primitive recursive, and
  identifies it pointwise with the existing proof-backed suffix family.
- [`LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineCompleteRouteComputability.lean`](LeanTrominoes/PeriodicOneInThreeNoUnitsFigureNineCompleteRouteComputability.lean)
  extends the inherited dispatcher with singleton suffixes for both auxiliary
  generations, computes each complete local-plus-suffix splice primitive
  recursively, and proves exact pointwise agreement with the certified
  complete Figure 9 route family.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreePositionedComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightOneInThreePositionedComputability.lean)
  composes the positioned retained fixed-eight source through Figure 9,
  opaque wrapping, and unit elimination, proving the exact final positioned
  formula computable and all companion placement queries primitive recursive.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightThreeDMComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedFixedEightThreeDMComputability.lean)
  composes that split through Figure 9 exact-one conversion, opaque variable
  wrapping, unit-clause elimination, canonical clause-anchor normalization,
  and the finite planar 3DM encoding, proving the exact named retained 3DM
  endpoint primitive recursive and computable.
- [`LeanTrominoes/PositionedPeriodicCNFComputability.lean`](LeanTrominoes/PositionedPeriodicCNFComputability.lean)
  proves the reusable positioned-formula bookkeeping executable: erasure,
  input-dependent variable renaming and gauging, total clause-position
  lookup, canonical position quotients, physical clause-anchor normalization,
  and first-representative literal-list deduplication are all primitive
  recursive.
- [`LeanTrominoes/PeriodicEightOccurrenceSplitComputability.lean`](LeanTrominoes/PeriodicEightOccurrenceSplitComputability.lean)
  gives the eight compass ports a canonical finite encoding and proves the
  fixed-eight copied clauses, separator implication rings, and full formula
  primitive recursive from a primitive-recursive source and total
  clause/literal-indexed port lookup.
- [`LeanTrominoes/PeriodicThreeSATThreeAngularOrderComputability.lean`](LeanTrominoes/PeriodicThreeSATThreeAngularOrderComputability.lean)
  proves the terminal-vector angular-radial comparison, stable angular
  occurrence ordering, east-first compass-port lookup, and resulting
  fixed-eight split primitive recursive from a finite source and route lookup.
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
- [`LeanTrominoes/PeriodicGridDrawingComputability.lean`](LeanTrominoes/PeriodicGridDrawingComputability.lean)
  gives grid segments, indexed segments and route points, periodic grid
  drawings, 3DM incidence vertices, periodic edges, and periodic graphs their
  canonical primitive-recursive encodings.  It proves that polyline segment
  enumeration, indexed drawing enumeration, and the complete periodic 3DM
  incidence-graph construction are primitive recursive.
- [`LeanTrominoes/PeriodicGridDrawingGeometryComputability.lean`](LeanTrominoes/PeriodicGridDrawingGeometryComputability.lean)
  proves primitive recursiveness of integer interval enumeration, segment
  translation, all exact axis-aligned containment and intersection
  predicates, interior lattice-point enumeration, occurrence keys, and the
  route-endpoint test used by finite drawing certificates.
- [`LeanTrominoes/PeriodicThreeDMIncidenceVertexCoverage.lean`](LeanTrominoes/PeriodicThreeDMIncidenceVertexCoverage.lean)
  shows that this incidence graph is loopless and, under the degree-two-or-
  three promise, has no isolated vertices.  Consequently every compatible
  nondegenerate incidence drawing covers all of its stored vertex positions
  by lifted route-segment endpoints.
- [`LeanTrominoes/PeriodicThreeDMFiniteDrawingCertificate.lean`](LeanTrominoes/PeriodicThreeDMFiniteDrawingCertificate.lean)
  combines finite compatibility, orthogonality, halo-bound, integer
  planarity, continuous-interior, and endpoint-contact checks.  Any accepted
  candidate reconstructs a continuously planar 3DM presentation together
  with complete lifted-route separation and route simplicity; the concrete
  Wang construction is proved to pass this verifier.
- [`LeanTrominoes/PeriodicThreeDMFiniteDrawingCertificateComputability.lean`](LeanTrominoes/PeriodicThreeDMFiniteDrawingCertificateComputability.lean)
  proves every compatibility and exact integer-geometry check primitive
  recursive, including the nested finite segment, route-point, and relative-
  translation scans, and therefore proves the complete certificate verifier
  primitive recursive and computable.
- [`LeanTrominoes/PeriodicThreeDMFiniteDrawingSearch.lean`](LeanTrominoes/PeriodicThreeDMFiniteDrawingSearch.lean)
  enumerates the standard natural-number encoding of periodic grid drawings
  and chooses the first accepted certificate.  It proves this total search
  computable for every computable source problem that always admits a
  certificate; the Wang construction supplies termination for every tile
  set.
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
- [`LeanTrominoes/PeriodicThreeDMContractedTagEndpoints.lean`](LeanTrominoes/PeriodicThreeDMContractedTagEndpoints.lean)
  enumerates the triple endpoints represented by retained and through edges
  and proves their incidence tags form a duplicate-free permutation of the
  original tag list, giving every tag one unique contracted endpoint and a
  canonical executable selector for decoding it.
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
- [`LeanTrominoes/PeriodicThreeDMContractionEndpointContacts.lean`](LeanTrominoes/PeriodicThreeDMContractionEndpointContacts.lean)
  proves the complementary listed-point invariant.  Original incidence
  routes are represented as optionally reversed lifted pieces; duplicate-free
  contracted metadata and the degree-two singleton block make every
  suppressed splice occurrence unique.  Retained/through and through/through
  joins therefore preserve complete lifted separation and route simplicity,
  which together imply endpoint-only contacts for the contracted drawing.
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
- [`LeanTrominoes/PeriodicGridDrawingAffineUnitRefinement.lean`](LeanTrominoes/PeriodicGridDrawingAffineUnitRefinement.lean)
  packages the common affine stage used by vertex normalization.  For a
  ribbon-ready orthogonal drawing with nondegenerate simple routes, complete
  lifted-route separation is derived, preserved by positive scaling and
  ordered unit subdivision, and transported through a common coordinate
  translation.  Consequently endpoint-only route contacts survive the whole
  magnify/subdivide/translate operation.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationMagnifiedContacts.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationMagnifiedContacts.lean)
  identifies that generic affine stage at scale twelve with the executable
  `normalizeVertexPosition` and `magnifiedUnitRoute` data.  For the contracted
  3DM drawing, compatibility, looplessness, continuous planarity, route
  nondegeneracy, orthogonality, and route simplicity are all discharged from
  existing certificates; endpoint-contact preservation therefore has only
  the contracted drawing's endpoint-contact certificate as a geometric
  premise.  The later local endpoint-template splices remain to be handled.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationStageDrawings.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationStageDrawings.lean)
  packages the periodic drawings after the first and second local template
  rounds, giving the contact proof explicit invariant boundaries between
  the three repeated magnify-and-splice operations.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationOccurrences.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationOccurrences.lean)
  proves translation-equivariance of magnification, endpoint trimming, and
  template splicing, and identifies every lifted first-round route with the
  same replacement applied directly to its lifted contracted occurrence.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationEndpointOccurrences.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationEndpointOccurrences.lean)
  packages source and offset-adjusted target occurrences of contracted
  endpoints and proves that their old-scale geometric centers uniquely
  determine the lifted prototype-vertex occurrence.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationLocalTemplateSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationLocalTemplateSeparation.lean)
  strengthens the finite Figure 2 checks to full route separation, proves
  their radius-three bound, separates templates based at distinct old
  lattice points after scale twelve, and handles distinct ports at one
  contracted vertex.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationTemplateOccurrenceSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationTemplateOccurrenceSeparation.lean)
  lifts the local Figure 2 checks to arbitrary endpoint occurrences:
  distinct centers are strictly separated, while distinct ports at one
  center can meet only at source heads or reversed target tails.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationCorridorSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationCorridorSeparation.lean)
  proves strict-separation inheritance for the symmetric three-point
  corridor trim and separates a trimmed magnified corridor from every local
  template centered at an old point avoided by the source route.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationCorridorOccurrenceSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationCorridorOccurrenceSeparation.lean)
  decomposes every lifted first-round route into its source template,
  trimmed corridor, and reversed target template, and proves strict
  separation of the middle corridors of distinct contracted occurrences.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationIncidentCorridorSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationIncidentCorridorSeparation.lean)
  splits an incident trimmed corridor into its initial outward ray and its
  remote tail, then proves that it strictly avoids every different-port
  Figure 2 arm at the same vertex center.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationTemplateCorridorOccurrenceSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationTemplateCorridorOccurrenceSeparation.lean)
  classifies every lifted template--corridor pairing as source-incident,
  target-incident, or remote; endpoint keys identify shared centers, while
  complete old-route separation handles the remote case.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationOccurrenceSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationOccurrenceSeparation.lean)
  records the exact splice junctions of lifted first-round pieces and
  assembles their local contact classifications into complete normalized
  route-occurrence separation.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationDrawingSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationDrawingSeparation.lean)
  recovers each stored first-round route's contracted edge and transfers the
  occurrence-level theorem to complete lifted-route separation of the first
  intermediate normalization drawing.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationRouteSimplicity.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationRouteSimplicity.lean)
  proves that each first-round splice remains duplicate-free and hence
  geometrically simple, completing the first intermediate drawing's
  endpoint-only route-contact invariant for reuse by the cyclic rounds.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicOccurrences.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicOccurrences.lean)
  names the lifted endpoint centers, templates, corridors, and complete
  routes of the first cyclic-rotation round, and gives its exact translated
  three-piece splice formula.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicTemplateSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicTemplateSeparation.lean)
  verifies the finite identity/clockwise Figure 3 route families and lifts
  their radius-three and same-center head-contact separation to arbitrary
  endpoint occurrences of the first intermediate drawing.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicCorridorSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicCorridorSeparation.lean)
  transports the first drawing's complete lifted separation and route
  simplicity through another scale/subdivide/trim stage, making the middle
  corridors of distinct second-round occurrences strictly disjoint.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicIncidentCorridorSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicIncidentCorridorSeparation.lean)
  proves the reusable local half-plane and remote-neighborhood lemmas showing
  that a trimmed cyclic-round corridor strictly avoids every different
  template arm at either incident endpoint.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicTemplateCorridorOccurrenceSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicTemplateCorridorOccurrenceSeparation.lean)
  classifies every lifted cyclic template--corridor pairing as source-
  incident, target-incident, or remote and proves strict separation in all
  three cases.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicOccurrenceSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicOccurrenceSeparation.lean)
  proves the exact cyclic-template/corridor splice junctions and assembles
  all pairwise piece invariants into complete separation of distinct lifted
  second-round route occurrences.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicDrawingSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicDrawingSeparation.lean)
  recovers the contracted edge owning each stored second-round route and
  lifts occurrence separation to the complete periodic drawing invariant.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicRouteSimplicity.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationCyclicRouteSimplicity.lean)
  proves each second-round splice duplicate-free and geometrically simple,
  completing the second intermediate drawing's endpoint-only route-contact
  certificate for the final cyclic round.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicOccurrences.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicOccurrences.lean)
  names the lifted templates, corridors, endpoint centers, and complete
  routes of the final cyclic round and proves its exact translated
  three-piece splice formula.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicTemplateSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicTemplateSeparation.lean)
  proves that the preceding cyclic port permutation preserves distinctness
  and lifts the reusable finite Figure 3 separation facts to every pair of
  final-round endpoint-template occurrences.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicCorridorSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicCorridorSeparation.lean)
  transports the second drawing's lifted separation and simplicity through
  the final scale/subdivide/trim operation, proving strict separation of all
  distinct final-round middle corridors.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicTemplateCorridorOccurrenceSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicTemplateCorridorOccurrenceSeparation.lean)
  classifies every final template--corridor pair as source-incident,
  target-incident, or remote and proves strict separation in all three cases.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicOccurrenceSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicOccurrenceSeparation.lean)
  proves the exact final-round splice junctions and assembles all nine
  pairwise piece invariants into complete separation of distinct lifted
  final route occurrences.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicDrawingSeparation.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicDrawingSeparation.lean)
  recovers the contracted edge owning each stored final route and lifts
  occurrence separation to the complete periodic final drawing.
- [`LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicRouteSimplicity.lean`](LeanTrominoes/PeriodicThreeDMVertexNormalizationFinalCyclicRouteSimplicity.lean)
  proves every final splice duplicate-free and geometrically simple,
  completing the final drawing's endpoint-only route-contact certificate.
- [`LeanTrominoes/PeriodicThreeDMNormalizationFinalAssignmentCollisionFreedom.lean`](LeanTrominoes/PeriodicThreeDMNormalizationFinalAssignmentCollisionFreedom.lean)
  feeds the final endpoint-contact certificate into the generic assignment
  geometry theorem, proving all compiled vertex and route-interior raster
  locations pairwise distinct.
- [`LeanTrominoes/PeriodicThreeDMNormalizationVertexPortCompleteness.lean`](LeanTrominoes/PeriodicThreeDMNormalizationVertexPortCompleteness.lean)
  proves the converse of endpoint color correctness: every exposed port of a
  final normalized vertex belongs to one of its three contracted endpoints,
  with the same side and edge color.
- [`LeanTrominoes/PeriodicThreeDMNormalizationRoutePortCompleteness.lean`](LeanTrominoes/PeriodicThreeDMNormalizationRoutePortCompleteness.lean)
  inverts the recursive route rasterizer, recovering the displayed route
  triple behind every emitted interior assignment and proving that its only
  exposed sides point to the predecessor and successor.
- [`LeanTrominoes/PeriodicThreeDMNormalizationRoutePortMatching.lean`](LeanTrominoes/PeriodicThreeDMNormalizationRoutePortMatching.lean)
  proves that every exposed final route-interior port matches its geometric
  unit-step neighbor, including the source and target boundary cases.
- [`LeanTrominoes/PeriodicThreeDMNormalizationExposedPortMatching.lean`](LeanTrominoes/PeriodicThreeDMNormalizationExposedPortMatching.lean)
  classifies every nonblank compiled lookup result and proves that each
  exposed port meets the same color at its finite-torus neighbor.
- [`LeanTrominoes/PeriodicThreeDMNormalizationWellFormed.lean`](LeanTrominoes/PeriodicThreeDMNormalizationWellFormed.lean)
  proves the compiled normalized drawing well formed by combining forward
  exposed-port matching with the reverse empty-port case.
- [`LeanTrominoes/PeriodicThreeDMNormalizationOrientationSites.lean`](LeanTrominoes/PeriodicThreeDMNormalizationOrientationSites.lean)
  augments every nonblank raster assignment with its contracted vertex or
  displayed route-triple provenance and proves that erasing this metadata
  recovers the existing collision-free lookup exactly.
- [`LeanTrominoes/PeriodicThreeDMNormalizationOrientationLift.lean`](LeanTrominoes/PeriodicThreeDMNormalizationOrientationLift.lean)
  lifts finite provenance lookup to arbitrary cells of the infinite drawing
  and reconstructs the unique geometric period translate represented by
  every successful lookup.
- [`LeanTrominoes/PeriodicThreeDMNormalizationEndpointOrientation.lean`](LeanTrominoes/PeriodicThreeDMNormalizationEndpointOrientation.lean)
  selects the unique contracted endpoint at every exposed normalized vertex
  port and identifies its inward value with the appropriate original 3DM
  incidence value at the lifted vertex translate.
- [`LeanTrominoes/PeriodicThreeDMNormalizationVertexOrientation.lean`](LeanTrominoes/PeriodicThreeDMNormalizationVertexOrientation.lean)
  proves the three normalized port selectors permute the contracted endpoint
  fan and transports suppressed triple coherence and retained-element
  exact-one constraints to the local trichromatic and monochromatic cells.
- [`LeanTrominoes/PeriodicThreeDMNormalizationForwardOrientation.lean`](LeanTrominoes/PeriodicThreeDMNormalizationForwardOrientation.lean)
  defines the plane-wide normalized drawing orientation induced by a
  suppressed 3DM solution and proves every blank, routing, trichromatic, and
  monochromatic cell satisfies its local orientation constraint.
- [`LeanTrominoes/PeriodicThreeDMNormalizationOrientationOccurrence.lean`](LeanTrominoes/PeriodicThreeDMNormalizationOrientationOccurrence.lean)
  evaluates that orientation at every explicit period translate of a listed
  provenance site and identifies drawing-lattice neighbors with translated
  geometric unit steps.
- [`LeanTrominoes/PeriodicThreeDMNormalizationForwardSourceCompatibility.lean`](LeanTrominoes/PeriodicThreeDMNormalizationForwardSourceCompatibility.lean)
  proves the forward orientation assigns opposite values to every normalized
  source-vertex port and its first routing-cell neighbor.
- [`LeanTrominoes/PeriodicThreeDMNormalizationForwardTargetCompatibility.lean`](LeanTrominoes/PeriodicThreeDMNormalizationForwardTargetCompatibility.lean)
  reconciles source- and target-based period translates and proves the last
  routing-cell port is compatible with its translated target vertex.
- [`LeanTrominoes/PeriodicThreeDMNormalizationForwardRouteCompatibility.lean`](LeanTrominoes/PeriodicThreeDMNormalizationForwardRouteCompatibility.lean)
  proves consecutive internal cells of every normalized route carry
  compatible forward-orientation values at all period translates.
- [`LeanTrominoes/PeriodicThreeDMNormalizationForwardVertexCompatibility.lean`](LeanTrominoes/PeriodicThreeDMNormalizationForwardVertexCompatibility.lean)
  dispatches every exposed normalized vertex port through its unique
  contracted endpoint to the source or translated-target compatibility law.
- [`LeanTrominoes/PeriodicThreeDMNormalizationForwardRoutePortCompatibility.lean`](LeanTrominoes/PeriodicThreeDMNormalizationForwardRoutePortCompatibility.lean)
  classifies every exposed route port as a predecessor or successor interface
  and dispatches endpoint and internal cases to their compatibility laws.
- [`LeanTrominoes/PeriodicThreeDMNormalizationForwardCompatibility.lean`](LeanTrominoes/PeriodicThreeDMNormalizationForwardCompatibility.lean)
  lifts finite vertex/route compatibility to arbitrary cells of the infinite
  periodic drawing and proves a suppressed 3DM orientation induces a valid
  global orientation of the compiled normalized drawing.
- [`LeanTrominoes/PeriodicThreeDMNormalizationReverseOrientation.lean`](LeanTrominoes/PeriodicThreeDMNormalizationReverseOrientation.lean)
  reads each original incidence value from its unique contracted triple
  endpoint in an arbitrary valid drawing orientation and proves the extracted
  values are coherent at every translated trichromatic vertex.
- [`LeanTrominoes/PeriodicThreeDMNormalizationReverseRouteStep.lean`](LeanTrominoes/PeriodicThreeDMNormalizationReverseRouteStep.lean)
  derives the two-port inequality of every normalized wire or bend and proves
  that an arbitrary valid drawing orientation preserves its forward-facing
  value across each internal route cell.
- [`LeanTrominoes/PeriodicThreeDMNormalizationReverseRouteCompatibility.lean`](LeanTrominoes/PeriodicThreeDMNormalizationReverseRouteCompatibility.lean)
  iterates that invariant along every complete normalized route, reconciles
  source and target period coordinates, and proves the two contracted endpoint
  inward values are opposite in any valid drawing orientation.
- [`LeanTrominoes/PeriodicThreeDMNormalizationReverseElementOrientation.lean`](LeanTrominoes/PeriodicThreeDMNormalizationReverseElementOrientation.lean)
  recovers the suppressed wire constraint at degree-two elements and exact-one
  at retained monochromatic vertices, completing validity of the graph
  orientation extracted from any valid normalized drawing orientation.
- [`LeanTrominoes/PeriodicThreeDMNormalizationOrientationEquivalence.lean`](LeanTrominoes/PeriodicThreeDMNormalizationOrientationEquivalence.lean)
  packages both semantic directions, proving that the normalized drawing is
  orientable exactly when the contracted graph has a suppressed orientation
  and exactly when the original periodic 3DM instance is satisfiable.
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
- [`LeanTrominoes/PeriodicThreeDMNormalizationVertexSeparation.lean`](LeanTrominoes/PeriodicThreeDMNormalizationVertexSeparation.lean)
  proves the compiled drawing's unconditional `VerticesSeparated`
  certificate.  A successful vertex-valued lookup must come from the
  vertex-assignment prefix because every route assignment is a wire, bend,
  or blank.  Three affine normalization rounds place all such vertex centers
  in residue class `(471, 471)` modulo `12³`, so no whole-period translate of
  one center can be a cardinal neighbor of another.  The result includes
  finite-torus wraparound and does not assume the still-pending global route
  collision certificate.
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
- [`LeanTrominoes/PeriodicCNFStripHorizontalAssembledRouteData.lean`](LeanTrominoes/PeriodicCNFStripHorizontalAssembledRouteData.lean)
  gives the explicit horizontal source a proof-free version of every complete
  typed RGB incidence route.  Variable incidences start with their translated
  checked finite-site route and extend exactly the selected routed triple by
  its coordinated occurrence corridor; clause incidences use the translated
  finite clause-core route.
- [`LeanTrominoes/PeriodicCNFStripHorizontalTypedIncidenceRouteComputability.lean`](LeanTrominoes/PeriodicCNFStripHorizontalTypedIncidenceRouteComputability.lean)
  proves that complete typed-route dispatcher primitive recursive.  Its
  ordinary, fixed-red, and clause constructor inputs are deliberately split
  into small computability leaves, as are the variable prefix, normalized
  routed-triple query, occurrence extension, and clause route.
- [`LeanTrominoes/PeriodicCNFStripHorizontalThreeDMTypedTriplesSemanticBridge.lean`](LeanTrominoes/PeriodicCNFStripHorizontalThreeDMTypedTriplesSemanticBridge.lean)
  identifies the proof-free typed-triple enumeration with the certified
  semantic enumeration used by the assembled 3DM reduction.
- [`LeanTrominoes/PeriodicCNFStripHorizontalTypedIncidenceRouteSemanticBridge.lean`](LeanTrominoes/PeriodicCNFStripHorizontalTypedIncidenceRouteSemanticBridge.lean)
  proves pointwise that every computed ordinary, fixed-red, and clause RGB
  incidence route is the corresponding certified assembled route, including
  the optional coordinated occurrence-corridor splice.
- [`LeanTrominoes/PeriodicCNFStripHorizontalAssembledEdgeRouteData.lean`](LeanTrominoes/PeriodicCNFStripHorizontalAssembledEdgeRouteData.lean)
  performs total tag-indexed lookup in the proof-free typed triple list and
  maps the complete route dispatcher over the encoded problem's stable
  incidence tags.
- [`LeanTrominoes/PeriodicCNFStripHorizontalThreeDMEdgeRoutesComputability.lean`](LeanTrominoes/PeriodicCNFStripHorizontalThreeDMEdgeRoutesComputability.lean)
  proves the resulting complete stored edge-route list primitive recursive,
  through separately checked leaves for typed-triple lookup, route selection,
  problem encoding, tag enumeration, and the final list map.
- [`LeanTrominoes/PeriodicCNFStripHorizontalThreeDMEdgeRoutesSemanticBridge.lean`](LeanTrominoes/PeriodicCNFStripHorizontalThreeDMEdgeRoutesSemanticBridge.lean)
  identifies that executable edge-route list with the certified assembled
  route family in the same incidence-tag order.  The proof transports an
  already-certified optional triple lookup through a shallow route selector,
  avoiding normalization of the full horizontal formula.
- [`LeanTrominoes/PeriodicCNFStripHorizontalThreeDMDrawingData.lean`](LeanTrominoes/PeriodicCNFStripHorizontalThreeDMDrawingData.lean)
  packages the executable period, vertex positions, and complete stored edge
  routes as the finite horizontal 3DM drawing and pairs it with its encoded
  problem for rectangular normalization.
- [`LeanTrominoes/PeriodicCNFStripHorizontalNormalizationInputComputability.lean`](LeanTrominoes/PeriodicCNFStripHorizontalNormalizationInputComputability.lean)
  proves that the complete problem-and-drawing normalization input is
  primitive recursive through its canonical product encoding.
- [`LeanTrominoes/PeriodicCNFStripHorizontalThreeDMDrawingPresentationBridge.lean`](LeanTrominoes/PeriodicCNFStripHorizontalThreeDMDrawingPresentationBridge.lean)
  extracts the already-certified coordinated-routing witnesses opaquely and
  proves that the fully executable grid drawing is exactly the drawing stored
  by the established continuous planar presentation.
- [`LeanTrominoes/PeriodicCNFStripNormalizationInputComputability.lean`](LeanTrominoes/PeriodicCNFStripNormalizationInputComputability.lean)
  identifies the executable problem-and-drawing pair with the semantic
  `normalizationInput`.  Consequently the proof-backed normalization input
  itself is computable, without re-elaborating its large geometric
  certificates.
- [`LeanTrominoes/PeriodicCNFStripCompiledTrominoComputability.lean`](LeanTrominoes/PeriodicCNFStripCompiledTrominoComputability.lean)
  composes normalization, rectangular strip compilation, and tromino gadget
  substitution to prove ordinary computability of the exact target function
  `compiledTrominoStrip` for either tromino.
- [`LeanTrominoes/PeriodicCNFStripReductionPackaging.lean`](LeanTrominoes/PeriodicCNFStripReductionPackaging.lean)
  fills every geometric and semantic field of the concrete local-CNF strip
  reduction.  Together with the existing polynomial output-size theorem, it
  isolates the remaining 1.5D hardness obligation to a machine-level
  `TM2ComputableInPolyTime` certificate for `compiledTrominoStrip`.
- [`LeanTrominoes/PeriodicCNFStripFlatCompiler.lean`](LeanTrominoes/PeriodicCNFStripFlatCompiler.lean)
  expresses that last machine obligation as a raw finite-alphabet stream
  transducer with identity input and output encodings.  Its verified wrapper
  transports any such polynomial-time machine to the canonical flat CNF and
  strip encodings and hence to the strip statement of Theorem 5.2.
- [`LeanTrominoes/PeriodicCNFStripFieldCompiler.lean`](LeanTrominoes/PeriodicCNFStripFieldCompiler.lean)
  tightens the machine boundary further: both canonical flat encodings are
  proved to be Mathlib's native `trList` encoding of natural-number fields.
  Thus the remaining machine can operate directly as a
  `List Nat → List Nat` transformer, while a small verified wrapper handles
  both semantic encoding round trips.
- [`LeanTrominoes/PeriodicCNFStripFieldMachineBridge.lean`](LeanTrominoes/PeriodicCNFStripFieldMachineBridge.lean)
  removes malformed-input parsing from the time obligation.  A native-field
  machine may have arbitrary behavior off the canonical `formulaFields`
  image; pointwise agreement on encoded source formulas is sufficient to
  obtain the exact semantic polynomial-time reduction.
- [`LeanTrominoes/PeriodicCNFStripDirectHardnessPackaging.lean`](LeanTrominoes/PeriodicCNFStripDirectHardnessPackaging.lean)
  composes the existing PSPACE source formula with the verified semantic strip
  compiler directly.  Consequently hardness only needs a polynomial-time
  machine on the bounded generated formula family, not on arbitrary malformed
  or unbounded local-CNF presentations.
- [`LeanTrominoes/PeriodicCNFStripDirectSymbolCompiler.lean`](LeanTrominoes/PeriodicCNFStripDirectSymbolCompiler.lean)
  moves that direct machine boundary to the original finite source-symbol
  stream and verifies its specialization to every canonical source encoding.
- [`LeanTrominoes/TM2PolyTimeOutputEncodingTransport.lean`](LeanTrominoes/TM2PolyTimeOutputEncodingTransport.lean)
  gives a generic cast-free transport from a polynomial-time machine to a new
  semantic codomain whose requested output has the same finite encoding.
- [`LeanTrominoes/PeriodicCNFStripDirectUnaryEmitter.lean`](LeanTrominoes/PeriodicCNFStripDirectUnaryEmitter.lean)
  reduces the remaining strip-hardness machine to an emitter for the target
  strip's natural-number fields in unary form.  Sequential composition with
  the verified unary-field encoder supplies the exact canonical binary strip
  output required by `Theorem52.stripStatement`.
- [`LeanTrominoes/PeriodicCNFStripDirectExecutableFields.lean`](LeanTrominoes/PeriodicCNFStripDirectExecutableFields.lean)
  exposes those target fields as a proof-free natural-range computation: two
  arithmetic header fields and the fixed-gadget pixels of the row-major
  normalized raster.  A verified equality transports any machine for this
  shallow generator back to the exact semantic strip reduction.
- [`LeanTrominoes/GadgetStripFlatFields.lean`](LeanTrominoes/GadgetStripFlatFields.lean)
  states the explicit three-field header and coordinate payload of any
  natural-range gadget strip without unfolding its input drawing.
- [`LeanTrominoes/PeriodicCNFStripDirectCountedTokens.lean`](LeanTrominoes/PeriodicCNFStripDirectCountedTokens.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectCountedTokenFinalization.lean`](LeanTrominoes/PeriodicCNFStripDirectCountedTokenFinalization.lean),
  and [`LeanTrominoes/PeriodicCNFStripDirectCountedTokenSemantics.lean`](LeanTrominoes/PeriodicCNFStripDirectCountedTokenSemantics.lean)
  encode the width and period header followed by one streamable finite block
  per motif cell, interleaving its count marker with its coordinate fields.
  They prove that counting, finalization, and rotation produce exactly the
  executable strip field stream.
- [`LeanTrominoes/PeriodicCNFStripDirectCountedTokenMachineBridge.lean`](LeanTrominoes/PeriodicCNFStripDirectCountedTokenMachineBridge.lean)
  and [`LeanTrominoes/PeriodicCNFStripDirectCountedTokenCompiler.lean`](LeanTrominoes/PeriodicCNFStripDirectCountedTokenCompiler.lean)
  compose those fixed postprocessors with any polynomial-time geometric token
  emitter and carry the resulting certificate through to
  `Theorem52.stripStatement`.
- [`LeanTrominoes/GadgetPixelFiniteTokens.lean`](LeanTrominoes/GadgetPixelFiniteTokens.lean),
  [`LeanTrominoes/GadgetExpandedMotifFiniteTokens.lean`](LeanTrominoes/GadgetExpandedMotifFiniteTokens.lean),
  and [`LeanTrominoes/GadgetPixelFiniteTokenCompiler.lean`](LeanTrominoes/GadgetPixelFiniteTokenCompiler.lean)
  replace all unbounded gadget-coordinate arithmetic by a finite prepared
  alphabet.  Header units expand by six, block-coordinate units by twelve,
  and bounded local offsets by twice their value, exactly matching Lean's
  encoding of each nonnegative translated pixel.  The natural-range loop
  theorem and fixed block-transducer certificate recover the complete counted
  motif stream in polynomial time.
- [`LeanTrominoes/GadgetPreparedHeaderData.lean`](LeanTrominoes/GadgetPreparedHeaderData.lean),
  [`LeanTrominoes/GadgetPreparedHeaderSemantics.lean`](LeanTrominoes/GadgetPreparedHeaderSemantics.lean),
  and [`LeanTrominoes/GadgetPreparedHeaderEmitter.lean`](LeanTrominoes/GadgetPreparedHeaderEmitter.lean)
  construct the rectangular strip header directly from a unary geometric
  scale.  For a fixed refinement factor and scale length `g`, three verified
  unary-padding passes and one finite block transducer emit exactly the two
  prepared fields for height `3P+1` and width `P`, where `P = factor * g`.
  Thus neither header field requires binary arithmetic or an unbounded
  intermediate alphabet.
- [`LeanTrominoes/PeriodicCNFTransitionProgramLiteralCount.lean`](LeanTrominoes/PeriodicCNFTransitionProgramLiteralCount.lean),
  [`LeanTrominoes/PeriodicThreeCNFExactSize.lean`](LeanTrominoes/PeriodicThreeCNFExactSize.lean),
  [`LeanTrominoes/PeriodicThreeSATThreeExactSize.lean`](LeanTrominoes/PeriodicThreeSATThreeExactSize.lean),
  [`LeanTrominoes/PeriodicThreeSATThreeExactVariableCount.lean`](LeanTrominoes/PeriodicThreeSATThreeExactVariableCount.lean),
  and [`LeanTrominoes/PeriodicThreeSATThreeExactDrawingSize.lean`](LeanTrominoes/PeriodicThreeSATThreeExactDrawingSize.lean)
  compute the exact source sizes needed by the raster emitter.  On the
  already-width-three PSPACE formulas, clause splitting is inert; the
  bounded-occurrence conversion has exactly one output variable per source
  literal occurrence, and its incidence drawing has grid size
  `16 * (clauses + 5 * literals + 1)`.
- [`LeanTrominoes/PeriodicCNFTransitionExprNonempty.lean`](LeanTrominoes/PeriodicCNFTransitionExprNonempty.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectSourceFormulaFacts.lean`](LeanTrominoes/PeriodicCNFStripDirectSourceFormulaFacts.lean),
  [`LeanTrominoes/PeriodicCNFStripSourceExactGridSize.lean`](LeanTrominoes/PeriodicCNFStripSourceExactGridSize.lean),
  and [`LeanTrominoes/PeriodicCNFStripDirectGridSize.lean`](LeanTrominoes/PeriodicCNFStripDirectGridSize.lean)
  specialize those counts to the generated transition program.  They prove
  every generated clause nonempty and obtain the exact direct-source grid
  size `16 * (program clauses + 5 * program literals + 7)`.
- [`LeanTrominoes/PeriodicCNFStripGridUnitTokens.lean`](LeanTrominoes/PeriodicCNFStripGridUnitTokens.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectGridUnitData.lean`](LeanTrominoes/PeriodicCNFStripDirectGridUnitData.lean),
  and [`LeanTrominoes/PeriodicCNFStripDirectGridUnitEmitter.lean`](LeanTrominoes/PeriodicCNFStripDirectGridUnitEmitter.lean)
  exploit the fixed clause/literal contribution of each transition
  instruction.  A finite block transducer maps the existing request-token
  stream to exactly one unary marker per orthocrossing grid unit and carries
  the source emitter's polynomial-time certificate through unchanged.
- [`LeanTrominoes/PeriodicCNFStripDirectPreparedHeaderData.lean`](LeanTrominoes/PeriodicCNFStripDirectPreparedHeaderData.lean)
  and [`LeanTrominoes/PeriodicCNFStripDirectPreparedHeaderEmitter.lean`](LeanTrominoes/PeriodicCNFStripDirectPreparedHeaderEmitter.lean)
  specialize the generic prepared-header machine to that exact grid stream.
  The resulting polynomial-time emitter produces precisely the compiled
  drawing's height and width fields, with horizontal period
  `normalizationPeriodFactor * gridSize` and vertical period one more than
  three times that value.
- [`LeanTrominoes/GadgetSparseExpandedMotif.lean`](LeanTrominoes/GadgetSparseExpandedMotif.lean),
  [`LeanTrominoes/GadgetSparseStripData.lean`](LeanTrominoes/GadgetSparseStripData.lean),
  [`LeanTrominoes/GadgetSparseStripMotif.lean`](LeanTrominoes/GadgetSparseStripMotif.lean),
  and [`LeanTrominoes/GadgetSparseStripSemantics.lean`](LeanTrominoes/GadgetSparseStripSemantics.lean)
  eliminate the unnecessary scan over every blank cell of the rectangular
  normalization raster.  Collision-free vertex and route assignments can be
  substituted directly in their existing order; the resulting motif has
  exactly the same membership, infinite carrier, well-formedness, and tiling
  predicate as the complete-raster strip.
- [`LeanTrominoes/PeriodicCNFStripSparseCompiledTromino.lean`](LeanTrominoes/PeriodicCNFStripSparseCompiledTromino.lean)
  and [`LeanTrominoes/PeriodicCNFStripDirectSparseHardnessPackaging.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseHardnessPackaging.lean)
  specialize that sparse presentation to the guarded local-CNF pipeline and
  the direct PSPACE source.  They preserve exact reduction correctness for
  both trominoes and reduce the remaining hardness certificate to a uniform
  polynomial-time compiler for the sparse assignment list.
- [`LeanTrominoes/GadgetSparseStripCompiler.lean`](LeanTrominoes/GadgetSparseStripCompiler.lean)
  makes that target proof-free: its width, period, and motif are computed
  directly from `NormalizationCompiler.Input`, with exact bridges to the
  proof-backed assignment list and sparse presentation.
- [`LeanTrominoes/GadgetSparseExpandedMotifFiniteTokens.lean`](LeanTrominoes/GadgetSparseExpandedMotifFiniteTokens.lean)
  emits affine prepared coordinate blocks for the pixels of each sparse
  assignment.  Nonnegative strip-coordinate bounds prove that fixed expansion
  recovers exactly the assignment-order motif's counted natural fields.
- [`LeanTrominoes/GadgetSparseAssignmentTokens.lean`](LeanTrominoes/GadgetSparseAssignmentTokens.lean)
  encodes each sparse drawing-cell assignment as two unary coordinates and one
  symbol from a finite cell-type alphabet.  Its total parser expands every
  canonical record to exactly the previously verified prepared pixel stream,
  reducing repetitive gadget-pixel emission to a fixed transducer.
- [`LeanTrominoes/GadgetSparseAssignmentTokenMachine.lean`](LeanTrominoes/GadgetSparseAssignmentTokenMachine.lean),
  [`LeanTrominoes/GadgetSparseAssignmentTokenMachineExecution.lean`](LeanTrominoes/GadgetSparseAssignmentTokenMachineExecution.lean),
  [`LeanTrominoes/GadgetSparseAssignmentTokenMachineTime.lean`](LeanTrominoes/GadgetSparseAssignmentTokenMachineTime.lean),
  and [`LeanTrominoes/GadgetSparseAssignmentTokenCompiler.lean`](LeanTrominoes/GadgetSparseAssignmentTokenCompiler.lean)
  implement that transducer as a fixed finite multi-stack machine.  Small
  intermediate leaves verify every transition, coordinate-copy phase, pixel
  cursor, cleanup, and total parser execution.  The resulting machine agrees
  with the parser on arbitrary words, runs in at most `513 * (n + 1)^2`
  steps, and transports any polynomial-time canonical-record emitter to the
  exact prepared sparse motif.
- [`LeanTrominoes/GadgetSparseAffineVertexTokens.lean`](LeanTrominoes/GadgetSparseAffineVertexTokens.lean)
  factors normalized vertex-coordinate emission into three fixed factor-12
  block transducers.  A compact record containing the original horizontal
  coordinate, reflected vertical complement, and finite cell type expands to
  the exact canonical unary record with coordinates `1728·x+471` and
  `1728·(2·gridSize−y−1)+1257`, without any single transition
  constructing a 1728-symbol block.
- [`LeanTrominoes/GadgetSparseAffineVertexWorkspace.lean`](LeanTrominoes/GadgetSparseAffineVertexWorkspace.lean)
  and [`LeanTrominoes/GadgetSparseAffineVertexWorkspaceCompiler.lean`](LeanTrominoes/GadgetSparseAffineVertexWorkspaceCompiler.lean)
  lift those three fixed passes to a sum workspace.  Source symbols remain
  unchanged on the left while only appended affine requests expand into
  canonical assignment tokens on the right.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseAssignmentData.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAssignmentData.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectSparseAssignmentBounds.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAssignmentBounds.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectSparseAssignmentRecordData.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAssignmentRecordData.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectSparseAssignmentRecordCompiler.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAssignmentRecordCompiler.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectSparseTargetPeriods.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseTargetPeriods.lean),
  and [`LeanTrominoes/PeriodicCNFStripDirectSparseTargetMotif.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseTargetMotif.lean)
  expose the direct source's proof-free assignment list, prove its coordinates
  nonnegative, encode it as canonical finite unary records, and identify its
  exact dimensions and motif with the semantic sparse target.  The record
  compiler proves that this finite geometry-emitter boundary composes with
  the fixed quadratic parser to recover the exact prepared motif.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseComputedAssignmentData.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseComputedAssignmentData.lean)
  replaces the proof-backed presentation at that boundary by the established
  executable horizontal problem-and-drawing constructor.  Its canonical
  record word is proved exactly equal to the semantic direct record word, so
  the remaining machine never inspects planarity certificates.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseComputedRecordSplit.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseComputedRecordSplit.lean)
  splits that executable word exactly into normalized contracted-vertex
  records followed by flattened route-interior records.  The two remaining
  geometry generators can therefore be constructed and bounded separately.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseComputedRecordBlocks.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseComputedRecordBlocks.lean)
  refines both halves into independent per-object blocks: one canonical unary
  record for each contracted vertex and one canonical record list for each
  contracted edge.  This exposes the granularity needed by indexed emitters
  without unfolding the complete normalized assignment stream.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseRouteRecordData.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseRouteRecordData.lean)
  rewrites every edge block as a flat map over consecutive triples of final
  route points.  Each triple independently determines exactly one rasterized
  coordinate and routing-cell record, exposing the route suffix as an
  edge-major, local-triple-minor stream.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseVertexRecordData.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseVertexRecordData.lean)
  expands all three vertex-normalization rounds to the exact affine formula
  `1728 · p + (471, 471)`.  Each vertex block is thereby reduced to its
  original contracted position, the input drawing period, and a finite cell
  type, with no normalized route data involved.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseVertexInputData.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseVertexInputData.lean)
  proves that every listed stage-zero contracted position is the matching
  lookup in the original input drawing.  The direct vertex-record stream is
  consequently expressed without constructing the contracted drawing's
  derived position list.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseVertexRecordSplit.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseVertexRecordSplit.lean)
  splits that stream into its triple prefix and stable red, green, and blue
  degree-three element blocks.  Each element block now carries a constant
  monochromatic cell type; only the triple block retains a normalized
  direction-order query.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseVertexRecordAffineBounds.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseVertexRecordAffineBounds.lean)
  and [`LeanTrominoes/PeriodicCNFStripDirectSparseVertexRecordDirectBounds.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseVertexRecordDirectBounds.lean)
  expose all four certified fundamental-square inequalities and eliminate the
  horizontal remainder operation from every direct vertex record.  Its two
  coordinates are now the fixed affine expressions `1728·x+471` and
  `3456·gridSize−(1728·y+471)`.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestData.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestData.lean)
  encodes each direct contracted vertex by the original horizontal coordinate,
  reflected vertical complement, and finite cell type.  Coordinate arithmetic
  proves that fixed affine expansion of the whole compact request stream is
  exactly the previously verified canonical direct vertex-record stream.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestAppender.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestAppender.lean)
  packages the remaining compact request generator as a retained-input
  appender contract.  Composing any implementation with the fixed workspace
  expander automatically satisfies the canonical vertex-record appender
  required by the split direct hardness pipeline.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestSplit.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestSplit.lean)
  splits the compact request stream into its stable triple, red, green, and
  blue blocks.  Each colored block scans only degree-three atom indices and
  emits a constant monochromatic cell tag.
- [`LeanTrominoes/PeriodicCNFStripHorizontalThreeDMVertexPositionAtData.lean`](LeanTrominoes/PeriodicCNFStripHorizontalThreeDMVertexPositionAtData.lean),
  [`LeanTrominoes/PeriodicCNFStripHorizontalThreeDMVertexPositionAtLengths.lean`](LeanTrominoes/PeriodicCNFStripHorizontalThreeDMVertexPositionAtLengths.lean),
  [`LeanTrominoes/PeriodicCNFStripHorizontalThreeDMVertexPositionAtAlignment.lean`](LeanTrominoes/PeriodicCNFStripHorizontalThreeDMVertexPositionAtAlignment.lean),
  and [`LeanTrominoes/PeriodicCNFStripHorizontalThreeDMVertexPositionAtComputed.lean`](LeanTrominoes/PeriodicCNFStripHorizontalThreeDMVertexPositionAtComputed.lean)
  expose the four computed position lists as one proof-free pointwise table.
  Length and order alignment prove that executable drawing lookup agrees with
  this table on every listed incidence vertex.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestPositionData.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestPositionData.lean)
  rewrites the entire compact direct request stream to traverse that explicit
  pointwise table, removing drawing lookup and certificate structure from the
  remaining request-emitter boundary.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestPositionSplit.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestPositionSplit.lean)
  carries the triple/red/green/blue decomposition across the lookup-free
  equality.  The three element scans now expose both their degree-three index
  filter and constant finite cell tag over the computed position table.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestTripleIndexed.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestTripleIndexed.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestElementIndexed.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestElementIndexed.lean),
  and [`LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestIndexedData.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAffineVertexRequestIndexedData.lean)
  eliminate in-range `getD` calls by converting every block to a `zipIdx`
  traversal.  The resulting exact stream consists of one indexed triple scan
  and three degree-filtered monochromatic position scans.
- [`LeanTrominoes/RetainedInputAppendPipeline.lean`](LeanTrominoes/RetainedInputAppendPipeline.lean)
  provides a generic polynomial-time composition pattern for passes that
  retain source symbols while appending output symbols.  Its direct sparse
  specializations split the remaining geometry machine into a vertex pass
  and a route pass, compose them sequentially, extract their concatenated
  record word, and discharge the existing whole-record emitter contract.
- [`LeanTrominoes/PeriodicCNFStripDirectSparsePreparedTokenData.lean`](LeanTrominoes/PeriodicCNFStripDirectSparsePreparedTokenData.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectSparsePreparedTokenSemantics.lean`](LeanTrominoes/PeriodicCNFStripDirectSparsePreparedTokenSemantics.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectSparseCountedTokenSemantics.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseCountedTokenSemantics.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectSparsePreparedTokenMachineBridge.lean`](LeanTrominoes/PeriodicCNFStripDirectSparsePreparedTokenMachineBridge.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectSparsePreparedTokenCompiler.lean`](LeanTrominoes/PeriodicCNFStripDirectSparsePreparedTokenCompiler.lean),
  and [`LeanTrominoes/PeriodicCNFStripDirectSparsePreparedTokenEmitterCompiler.lean`](LeanTrominoes/PeriodicCNFStripDirectSparsePreparedTokenEmitterCompiler.lean)
  connect the verified direct header and sparse pixel stream to every existing
  fixed postprocessor.  Any polynomial-time emitter for the canonical unary
  assignment records now supplies the exact prepared stream, flat target, and
  complete `Theorem52.stripStatement`.
- [`LeanTrominoes/PeriodicCNFStripDirectSparseAffineTablePhaseData.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAffineTablePhaseData.lean)
  and [`LeanTrominoes/PeriodicCNFStripDirectSparseAffineTablePhaseCompiler.lean`](LeanTrominoes/PeriodicCNFStripDirectSparseAffineTablePhaseCompiler.lean)
  split the phase-major compact vertex stream into variable triples, clause
  triples, red, green, and blue.  Any five exact finite families now compile
  through retained-source wrapping and fixed affine expansion to the canonical
  vertex-record appender.
- [`LeanTrominoes/PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler.lean`](LeanTrominoes/PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler.lean)
  exposes the already verified polynomial-time numeric incidence-route stream
  as a reusable geometry compiler instead of keeping it private to the carrier
  descriptor pass.
- [`LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarDirectionData.lean`](LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarDirectionData.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarDirectionDescriptorData.lean`](LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarDirectionDescriptorData.lean),
  and [`LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarDirectionDescriptorCompiler.lean`](LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarDirectionDescriptorCompiler.lean)
  expose the exact retained planar clause-profile/first-direction stream before
  occurrence splitting, specialize it to direct PSPACE source words, and
  compose any emitter for that stream with the verified exact two-pass
  fixed-eight descriptor expansion.
- [`LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataDirectionData.lean`](LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataDirectionData.lean)
  and [`LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataDirectionClauses.lean`](LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataDirectionClauses.lean)
  remove positioned-formula bookkeeping from that boundary: the final erased
  retained clauses are exactly the deduplicated normalized clauses projected
  from the existing five-family finite metadata list.
- [`LeanTrominoes/PositionedPeriodicCNFRouteFirstDirections.lean`](LeanTrominoes/PositionedPeriodicCNFRouteFirstDirections.lean)
  isolates the cheap geometric fact needed by the metadata bridge: subtracting
  one common clause-period translation preserves a route's first direction.
  Keeping this lemma independent of retained-planarity certificates also keeps
  its leaf compilation within the project's low-memory build boundary.
- [`LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRouteData.lean`](LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRouteData.lean)
  and [`LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRoutes.lean`](LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRoutes.lean)
  remove final clause deduplication and outer anchor normalization from the
  direction stream.  Each final first direction is now exactly the direction
  of the first normalized source route whose metadata clause has the retained
  literal list.
- [`LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRouteData.lean`](LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRouteData.lean)
  and [`LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRoutes.lean`](LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRoutes.lean)
  then erase the remaining inner anchor normalization.  Thus every retained
  first direction is the first direction of a raw local component route
  selected by `idxOf` in the normalized five-family metadata list.
- [`LeanTrominoes/RetainedRayRasterizationFirstDirections.lean`](LeanTrominoes/RetainedRayRasterizationFirstDirections.lean),
  [`LeanTrominoes/RetainedAngularFanFallbackFirstDirections.lean`](LeanTrominoes/RetainedAngularFanFallbackFirstDirections.lean),
  [`LeanTrominoes/RetainedAngularFanEscapedFirstDirections.lean`](LeanTrominoes/RetainedAngularFanEscapedFirstDirections.lean),
  [`LeanTrominoes/RetainedAngularFanEscapedCardinalClassification.lean`](LeanTrominoes/RetainedAngularFanEscapedCardinalClassification.lean),
  [`LeanTrominoes/RetainedAngularFanFinalFallbackFirstDirections.lean`](LeanTrominoes/RetainedAngularFanFinalFallbackFirstDirections.lean),
  [`LeanTrominoes/RetainedAngularFanFinalEscapedFirstDirections.lean`](LeanTrominoes/RetainedAngularFanFinalEscapedFirstDirections.lean),
  and [`LeanTrominoes/RetainedAngularFanFinalCoordinatedFallbackFirstDirections.lean`](LeanTrominoes/RetainedAngularFanFinalCoordinatedFallbackFirstDirections.lean)
  prove that retained-ray rasterization preserves the first direction of an
  orthogonal retained route, carry that edge through both ordinary and
  singleton-escaped fan-tail replacement and suffix joining, and expose the
  result at the public final route boundary for every failed-direct incidence.
  The singleton classifier also rules out every diagonal and routed-clause
  terminal for an axis-aligned two-point source route.
- [`LeanTrominoes/RetainedAngularFanFinalSourceRouteGeometry.lean`](LeanTrominoes/RetainedAngularFanFinalSourceRouteGeometry.lean)
  exposes the unscaled geometry needed by ordinary-fallback normalization:
  every genuine copied-source route is simple, and failed direct selection
  makes that raw route orthogonal before either refinement scale is applied.
- [`LeanTrominoes/RetainedAngularFanFinalSourceHeadSeparationSupport.lean`](LeanTrominoes/RetainedAngularFanFinalSourceHeadSeparationSupport.lean),
  [`LeanTrominoes/RetainedAngularFanFinalOrdinaryFallbackRawHeadSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalOrdinaryFallbackRawHeadSeparation.lean),
  [`LeanTrominoes/RetainedAngularFanFinalOuterSpokeSourceHeadSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalOuterSpokeSourceHeadSeparation.lean),
  and [`LeanTrominoes/RetainedAngularFanFinalOrdinaryFallbackHeadSeparation.lean`](LeanTrominoes/RetainedAngularFanFinalOrdinaryFallbackHeadSeparation.lean)
  turn that raw simplicity into the source-head isolation needed for ordinary
  normalization.  A non-singleton fallback's head is separated from its final
  segment; both refinement scales then keep the scaled head outside the
  unit-subdivided outer fan and matching Figure 7 spoke.
- [`LeanTrominoes/RetainedAngularFanOrdinaryFigure7HeadIsolation.lean`](LeanTrominoes/RetainedAngularFanOrdinaryFigure7HeadIsolation.lean)
  composes those two exclusions with a simple refined source prefix.  The
  complete ordinary prefix/fan/spoke splice therefore keeps its head isolated
  after unit subdivision.
- [`LeanTrominoes/RetainedAngularFanOuterEscapedHeadIsolation.lean`](LeanTrominoes/RetainedAngularFanOuterEscapedHeadIsolation.lean)
  [`LeanTrominoes/RetainedAngularFanOuterEscapedNormalizedFirstDirections.lean`](LeanTrominoes/RetainedAngularFanOuterEscapedNormalizedFirstDirections.lean),
  [`LeanTrominoes/RetainedAngularFanOuterEscapedFigure7HeadIsolation.lean`](LeanTrominoes/RetainedAngularFanOuterEscapedFigure7HeadIsolation.lean),
  [`LeanTrominoes/RetainedAngularFanOuterEscapedFigure7NormalizedFirstDirections.lean`](LeanTrominoes/RetainedAngularFanOuterEscapedFigure7NormalizedFirstDirections.lean),
  [`LeanTrominoes/RetainedAngularFanEscapedOwnFigure7NormalizedFirstDirections.lean`](LeanTrominoes/RetainedAngularFanEscapedOwnFigure7NormalizedFirstDirections.lean),
  [`LeanTrominoes/RetainedAngularFanFinalEscapedNormalizedFirstDirections.lean`](LeanTrominoes/RetainedAngularFanFinalEscapedNormalizedFirstDirections.lean),
  and [`LeanTrominoes/RetainedAngularFanFinalCoordinatedEscapedNormalizedFirstDirections.lean`](LeanTrominoes/RetainedAngularFanFinalCoordinatedEscapedNormalizedFirstDirections.lean)
  prove that unit subdivision of a cardinal escaped fan never revisits its
  source gate and that loop erasure therefore preserves its first direction.
  The initial 64-block escape is duplicate-free, while every point of the
  remaining fan stays strictly inward of the gate.  Appending the matching
  radius-96 Figure 7 spoke preserves the same source-head isolation and hence
  the first direction through normalization.  The complete generic singleton
  splice and its genuine final positioned specialization therefore normalize
  to the direction of their original source edge, including at the public
  normalized route-family boundary.
- [`LeanTrominoes/PeriodicCNFFormulaShapeDirectionOrderingExtensionality.lean`](LeanTrominoes/PeriodicCNFFormulaShapeDirectionOrderingExtensionality.lean),
  [`LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorData.lean`](LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorData.lean),
  and [`LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptors.lean`](LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptors.lean)
  package those clauses and raw routes as a position-free descriptor stream
  and prove it exactly equals the canonical retained-planar stream.  The
  pre-split compiler obligation is therefore reduced to a finite emitter over
  the five explicit metadata families.
- [`LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorData.lean`](LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorData.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorSemantics.lean`](LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorSemantics.lean),
  and [`LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorCompiler.lean`](LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorCompiler.lean)
  specialize that equality to direct PSPACE source-symbol words.  Any
  polynomial-time metadata emitter now supplies both the canonical pre-split
  compiler and the already verified fixed-eight descriptor compiler.
- [`LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorBlockData.lean`](LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorBlockData.lean),
  [`LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorBlocks.lean`](LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorBlocks.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlockData.lean`](LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlockData.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlocks.lean`](LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlocks.lean),
  and [`LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlockCompiler.lean`](LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlockCompiler.lean)
  split the remaining emitter into two independently bounded retained-input
  passes: the deduplicated clause records and the distinct-variable marker
  suffix.  Their standard composition recovers the exact metadata and
  fixed-eight streams.
- [`LeanTrominoes/PeriodicCNFDeduplicationExactVariableCount.lean`](LeanTrominoes/PeriodicCNFDeduplicationExactVariableCount.lean)
  proves that removing duplicate clauses preserves the number of distinct
  variables, and [`LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataVariableCount.lean`](LeanTrominoes/PeriodicCNFFormulaShapeRetainedPlanarMetadataVariableCount.lean)
  uses it to identify the exact marker suffix length with the finite retained
  planar-SAT variable count before wrapping and geometric gauges.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableEnumeration.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableEnumeration.lean)
  gives that marker pass a canonical finite target: the two terminal variables
  on every indexed segment, every canonical crossing boundary, every
  represented translation-zero source atom, and all nine internals at every
  canonical crossing.  Membership in this four-block list is exactly the
  retained periodic variable-validity predicate.
- [`LeanTrominoes/PlanarThreeSATCrossoverInternalOccurrenceData.lean`](LeanTrominoes/PlanarThreeSATCrossoverInternalOccurrenceData.lean),
  [`LeanTrominoes/PlanarThreeSATCrossoverInternalOccurrences.lean`](LeanTrominoes/PlanarThreeSATCrossoverInternalOccurrences.lean),
  [`LeanTrominoes/PeriodicCNFPlanarRetainedOccurrences.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedOccurrences.lean),
  and [`LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATCrossoverInternalOccurrences.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATCrossoverInternalOccurrences.lean)
  prove the first converse coverage block needed for that enumeration.  Every
  one of the nine fixed Figure 8 internal names has an explicit clause
  witness; every such variable at a canonical crossing survives the retained
  core, the complete finite planar formula, and periodicization as the same
  canonical protovariable.  Occurrence-list renaming and periodicization are
  factored into small reusable leaves so this chain remains within the
  low-memory build boundary.
- [`LeanTrominoes/PeriodicCNFPlanarRoutedVariableLinkExistence.lean`](LeanTrominoes/PeriodicCNFPlanarRoutedVariableLinkExistence.lean),
  [`LeanTrominoes/PeriodicCNFPlanarRoutedVariableCenterOccurrence.lean`](LeanTrominoes/PeriodicCNFPlanarRoutedVariableCenterOccurrence.lean),
  [`LeanTrominoes/PeriodicCNFPlanarRoutedVariableOccurrences.lean`](LeanTrominoes/PeriodicCNFPlanarRoutedVariableOccurrences.lean),
  and [`LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATAtomOccurrences.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATAtomOccurrences.lean)
  prove the second converse coverage block.  A represented variable-route
  site comes from an actual route occurrence, so it has an active equality
  link whose center occurs in the routed-variable formula; retained embedding
  and zero-translation periodicization preserve that center as the original
  source atom.
- [`LeanTrominoes/PlanarThreeSATCrossoverVariableOccurrences.lean`](LeanTrominoes/PlanarThreeSATCrossoverVariableOccurrences.lean),
  [`LeanTrominoes/PeriodicOrthocrossingCrossoverBoundaryOccurrences.lean`](LeanTrominoes/PeriodicOrthocrossingCrossoverBoundaryOccurrences.lean),
  [`LeanTrominoes/PeriodicOrthocrossingRetainedBoundaryOccurrences.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedBoundaryOccurrences.lean),
  and [`LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATBoundaryOccurrences.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATBoundaryOccurrences.lean)
  prove the third converse coverage block.  Each of the four fixed crossover
  ports occurs in Figure 8, every canonical drawing boundary therefore occurs
  in the retained finite formula, and canonical boundary normalization fixes
  its periodic protovariable.
- [`LeanTrominoes/PeriodicOrthocrossingTerminalClassification.lean`](LeanTrominoes/PeriodicOrthocrossingTerminalClassification.lean),
  [`LeanTrominoes/PeriodicCNFPlanarRouteEndpointMetadata.lean`](LeanTrominoes/PeriodicCNFPlanarRouteEndpointMetadata.lean),
  and [`LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATTerminalOccurrences.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATTerminalOccurrences.lean)
  prove the fourth converse coverage block.  Every neighboring segment
  terminal is either attached to an enumerated route bend or is the source or
  target endpoint of a metadata-rich CNF route occurrence.  Bend equality
  links, routed-clause sources, and the at-most-three routed-variable arms
  therefore retain every finite terminal; the translation-zero occurrence of
  each indexed segment periodicizes to its canonical terminal protovariable.
  The classification, endpoint metadata, finite retention, and periodic lift
  are separate leaf modules so each check stays within the low-memory build
  boundary.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableCompleteness.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableCompleteness.lean),
  [`LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableCoverage.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableCoverage.lean),
  and [`LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableCount.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableCount.lean)
  combine all four converse blocks with the existing occurrence-validity
  direction.  Under the occurrence-three and standard drawing hypotheses,
  membership in the retained periodic formula is exactly membership in the
  canonical enumeration, and their deduplicated lengths are equal.  Thus the
  marker suffix no longer depends on the expanded clause occurrence list.
- [`LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariablesNodup.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariablesNodup.lean),
  [`LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableExactCount.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableExactCount.lean),
  and [`LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataVariableMarkers.lean`](LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataVariableMarkers.lean)
  prove that presentation indices, crossing-side names, translation-zero
  source sites, and the nine internal names make the four canonical blocks
  individually duplicate-free and constructor-disjoint.  The exact marker
  count is therefore their ordinary combined length, and this equality is
  specialized to the guarded direct PSPACE source with all drawing hypotheses
  discharged.
- [`LeanTrominoes/PeriodicCNFPlanarZeroVariableRouteSites.lean`](LeanTrominoes/PeriodicCNFPlanarZeroVariableRouteSites.lean),
  [`LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableLengthFormula.lean`](LeanTrominoes/PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableLengthFormula.lean),
  and [`LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataVariableMarkerCounts.lean`](LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataVariableMarkerCounts.lean)
  reduce that direct marker length to three streamable counts.  Locality makes
  the translation-zero route sites exactly the source formula's distinct
  variables, while the two terminal names and the four boundary plus nine
  internal names give the closed formula `2·segments + variables +
  13·crossings`.  The variable term can therefore reuse the already compiled
  formula-shape marker stream; only segment and crossing scans remain new.
- [`LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataAtomMarkerCompiler.lean`](LeanTrominoes/PeriodicCNFStripDirectRetainedPlanarMetadataAtomMarkerCompiler.lean)
  implements that reuse.  It composes the polynomial-time guarded
  formula-shape compiler with a fixed token filter, and its separate semantic
  leaf proves that the output is exactly one retained metadata marker per
  distinct source-formula variable.
- [`LeanTrominoes/PeriodicCNFStripDirectPreparedTokenData.lean`](LeanTrominoes/PeriodicCNFStripDirectPreparedTokenData.lean),
  [`LeanTrominoes/PeriodicCNFStripDirectPreparedTokenMachineBridge.lean`](LeanTrominoes/PeriodicCNFStripDirectPreparedTokenMachineBridge.lean),
  and [`LeanTrominoes/PeriodicCNFStripDirectPreparedTokenCompiler.lean`](LeanTrominoes/PeriodicCNFStripDirectPreparedTokenCompiler.lean)
  specialize that finite expansion to the direct PSPACE-source drawing and
  transport any prepared-raster emitter through the complete counted-token
  compiler.  Thus the remaining hardness obligation is only the prepared
  normalized-raster stream, not unary coordinate generation or finalization.
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
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEnumerationComputability.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEnumerationComputability.lean)
  gives primitive-recursive encodings to the planar construction's typed
  elements and triples, then proves its source-occurrence, connector-module,
  color-class, and prototype-triple enumerations primitive recursive.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEncodingComputability.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMEncodingComputability.lean)
  proves the complete Dyer--Frieze connector-reference calculation,
  first-index color numbering, and natural-number `PeriodicThreeDM` encoding
  primitive recursive and hence computable.
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
  geometric route subdivision described below now proves the complete
  halo-bounded ribbon-ready interface for the normalized formula.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationComputability.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationComputability.lean)
  implements the logical polarity normalization as primitive-recursive list
  traversals.  This includes occurrence indexing, literal replacement, and
  generation of the binary complement clauses, independently of the later
  geometric subdivision choices.
- [`LeanTrominoes/PeriodicCNFGaugeComputability.lean`](LeanTrominoes/PeriodicCNFGaugeComputability.lean)
  proves clause-anchor normalization and source-dependent variable gauging
  primitive recursive.  Its family interface allows the finite formula and
  per-variable offset function to depend on the same reduction input, as
  required by the canonical gauges in the planar Wang construction.
- [`LeanTrominoes/PrimrecListSort.lean`](LeanTrominoes/PrimrecListSort.lean)
  supplies a stable Boolean insertion sort with a common external parameter,
  proves it primitive recursive, and identifies it with Mathlib's relational
  `List.insertionSort` whenever the Boolean comparison decides that relation.
  Its indexed stable-sort interface is additionally proved equal to Lean's
  `List.mergeSort` for every total transitive Boolean comparison.
- [`LeanTrominoes/PositionedPeriodicCNFClauseOrderingComputability.lean`](LeanTrominoes/PositionedPeriodicCNFClauseOrderingComputability.lean)
  encodes finite positioned periodic formulas and proves their stable
  clockwise route-direction clause ordering primitive recursive from a
  primitive-recursive route lookup.  It also exposes the corresponding
  reindexed route dispatcher, including the canonical whole-period gauge
  translation, as a reusable primitive-recursive operation.
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
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteVertexBounds.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteVertexBounds.lean)
  derives a two-cell boundary margin from strict source-vertex bounds and
  threefold scaling, then proves that both inserted unit-subdivision vertices
  remain strictly inside the refined fundamental square.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteVertexSeparation.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteVertexSeparation.lean)
  locates each inserted vertex in the relative interior of the first scaled
  source segment.  Source planarity then proves that no inserted vertex is an
  old source vertex, that the two vertices of one split incidence differ, and
  that vertices reserved for distinct source occurrences differ.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteVertexInjectivity.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteVertexInjectivity.lean)
  recovers the exact source occurrence carried by every appearing fresh
  variable and gives every generated clause a duplicate-free origin key.
  Combining those provenance results with subdivision-point separation proves
  that the final variable prefix, clause suffix, and their concatenation are
  all duplicate-free.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteCompatibility.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRouteCompatibility.lean)
  classifies every final vertex as either a retained scaled source vertex or
  one of the two bounded subdivision points.  It proves strict
  fundamental-square bounds for the complete vertex list and packages those
  bounds, vertex injectivity, and exact route endpoints into the final finite
  compatibility certificate.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationRawRouteBounds.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRawRouteBounds.lean)
  classifies every split incidence as a fragment of one refined source route.
  It cancels each fragment's canonical lattice shift after rebasing and
  transports the source route's open-halo bound to all raw normalized routes.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationRawLiftedSeparation.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRawLiftedSeparation.lean)
  combines fragment provenance, source simplicity, and translated source-route
  separation to prove complete lifted separation and simplicity for the raw
  normalized route family.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationEndpointContacts.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationEndpointContacts.lean)
  transports raw relative separation and simplicity through the final
  fresh-variable gauge, yielding endpoint-only listed-point contacts for the
  final normalized drawing.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationHaloBounds.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationHaloBounds.lean)
  transports the raw halo certificate through that gauge.  Embedded-original
  routes have zero gauge; on fresh-variable routes the inverse gauge cancels
  the occurrence offset, leaving only the first three bounded refined-route
  vertices.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationRibbonReadyPresentation.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRibbonReadyPresentation.lean)
  packages continuous planarity, halo bounds, and endpoint-only contacts as
  the complete `HaloBoundedRibbonReadyIncidencePresentation` consumed by the
  planar 3DM ribbon construction.
- [`LeanTrominoes/PeriodicOneInThreePolarityNormalizationRibbonThreeDM.lean`](LeanTrominoes/PeriodicOneInThreePolarityNormalizationRibbonThreeDM.lean)
  feeds that presentation and the transported variable/clause route orders
  into the padded three-strand assembly.  The resulting periodic 3DM target
  is well formed, has colored degree two or three, has a concrete continuously
  planar presentation, and admits a graph orientation exactly when the
  original exact-one source is satisfiable.
- [`LeanTrominoes/PeriodicCNFPlanarRetainedPolarityNormalizedRibbonThreeDMComputability.lean`](LeanTrominoes/PeriodicCNFPlanarRetainedPolarityNormalizedRibbonThreeDMComputability.lean)
  computes the erased routed polarity normalization independently of its
  proof-oriented positions, applies the fresh-variable gauge and final padded
  3DM encoding, and proves exact equality with the continuously planar
  proof-backed endpoint.
- [`LeanTrominoes/PeriodicWangPlanarThreeDMReduction.lean`](LeanTrominoes/PeriodicWangPlanarThreeDMReduction.lean)
  specializes the construction to Wang tile sets.  Its total source-formula
  map uses the standard Wang reduction for nonempty inputs and a fixed
  contradictory fallback for the empty tileset.  The exact planar 3DM problem
  and its first verified finite drawing are computable; together they form the
  normalization compiler input.  Composing that compiler with both tromino
  gadget reductions proves co-r.e.-hardness and the complete 2D
  `Theorem52.planeStatement`.
- [`LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMPolarityNormalization.lean`](LeanTrominoes/PeriodicPlanarOneInThreeToThreeDMPolarityNormalization.lean)
  transports that formula-level certificate through the actual occurrence
  lookup table used by the typed planar 3DM assembly.  Every active occurrence
  is proved to select exactly one of the three endpoint-clear tables:
  fixed-red/false, fixed-blue/false, or fixed-green/true.  Anchor normalization
  preserves the certificate, so the padded assembly and its continuous
  planarity proof consume the same convention explicitly.
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
