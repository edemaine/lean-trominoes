import LeanTrominoes.Common.Results
import LeanTrominoes.Complexity.Results
import LeanTrominoes.Computation.Results
import LeanTrominoes.Graphs.Results
import LeanTrominoes.SAT.Results
import LeanTrominoes.ThreeDM.Results
import LeanTrominoes.Tiling.Results

/-!
# Main theorem interface

`PeriodicOrthocrossing.GeneralPorts.local_orthocrossing_drawing` proves
Theorem 2.1 for every well-formed local periodic graph, including loops and
isolated vertices. The grid size is at most `16(V+E+1)`, or `32(V+E)` for
nonempty graphs. `local_orthogonal_orthocrossing_drawing` adds orthogonality
for maximum degree four. Real crossings lie on the grid, and three distinct
route occurrences cannot cross at one point away from their endpoints.

`GeneralVertexNormalization.lemma23` proves whole-drawing vertex
normalization for any real planar orthogonal drawing, including loops.
It preserves rational vertex positions and locality, multiplies the grid
size by 32, and makes the selected incidence point west at every
degree-three vertex, whose outward directions are west, north, east.

Theorem 2.2 has checked finite crossing tables and a rectangle router
for straight local planar inputs of degree at most four. Rational row and
column cuts give proper ports of the original edge occurrences, preserve
crossing and incidence order in every period, and reserve margins for
enlarged vertex connectors. The computable port enumeration groups ports
by their parent edge; every nonempty group has exactly two ordered ports.
Every original edge portion entering a virtual rectangle has a chord in
the assembled matching, which covers every retained boundary port. Its
assembled chord family has at most 18M² members and is noninterlacing;
the resulting orthogonal routes are simple, pairwise disjoint, confined
to their rectangles, and meet the boundary only at their own ports.
The proposed grid has size ≤3300M³. Crossing bars avoid every enlarged
vertex connector, and connector endpoints agree with adjacent slab ports.
Periodic rectangle routes can meet distinct rectangles only at endpoints.
Rectangle contacts with crossing bars and vertex fans are endpoints of
both pieces. Periodic vertex fans remain within their own cells and meet
only at their common vertex center; distinct crossing bars are disjoint.
The actual crossing routes commute with periods and join adjacent ports.
A general separated-chain lemma preserves simplicity and orthogonality
when joining a finite word of pieces.
Sorting a disjoint rational interval cover determines a gap-free chain.
The interval assembler checks the final route's source, target, simplicity,
orthogonality, and exact image from its pieces and their joining conditions.
The computed rectangle groups delimit the exact rational affine clips,
whose points lie strictly inside their original edge segments.
For each straight nonvertical edge, an executable list of rectangle clips,
crossing bars, and vertex fans covers every original edge parameter.
Distinct pieces have disjoint parameter interiors. Sorting and removing
duplicates gives a consecutive partition from zero to one, and the
executable route assembler has the exact scaled graph endpoints.
All consecutive computed pieces join, including rectangle period seams,
crossing bars, and source and target fans. The assembled route is orthogonal
and has exactly the union of its piece images. Shared new endpoints recover
equal original parameters, excluding nonadjacent contacts. The assembled
nonvertical route is simple without extra join or separation hypotheses.
Vertical edges use their directly scaled segments. The executable finite
straight-edge drawing is compatible, has simple orthogonal routes, avoids
graph vertices in every periodic copy, and has grid size at most 3300M³.
Global periodic planarity, locality, and polygonal bends remain open.
A checked example shows why row seams matter: a dogleg
spanning more than one period can overlap its translated copy.

`PeriodicTrominoPrefill.planeProblem_coREComplete` proves co-r.e. completeness
of periodic L- and I-tromino completion in the plane. `compileDrawing_valid`
in `CompletionPattern.LBricks` and `CompletionPattern.IBricks` proves that
every hardness reduction output is a valid partial tiling.
`PeriodicTrominoPrefill.exists_aperiodic_completion` proves that each tromino
admits a valid periodic prefill whose completions exist but have no nonzero
translation period.
`PeriodicStripTrominoPrefill.problem_PSPACEComplete` proves strip completion
PSPACE completeness under the explicit unary encoding for both trominoes.
`CompletionPattern.StripOrientation.compile_valid` proves validity of every
strip reduction output, including those for unsatisfiable inputs.

`Theorem52.proved` proves the complete plane and strip result, and
`Theorem52.stripProved` exposes strip PSPACE completeness. Import
`LeanTrominoes.Tiling.Tromino.Theorem52` separately to read only the target statements.
See README.md for the main declarations and docs/theorem-5.2.md for the
completed construction and validation.

`TwoTranslationTrominoes.proved` proves Corollary 5.3: tiling periodic
plane regions by translations of the horizontal and vertical I trominoes is
co-r.e. complete, and the strip problem is PSPACE complete.

`Theorem55.planeProved` proves co-r.e. completeness of plane tiling by a fixed
connected 15-omino and an input disconnected polyomino, allowing rotations
and reflections. `Theorem55.stripProved` proves PSPACE completeness of the
corresponding strip problem under its original unary encoding. See
docs/theorem-5.5.md for the construction and validation.

`ThreeTranslationPolyominoes.proved` proves Corollary 5.6: tiling by translations
of two fixed connected 15-ominoes and an input disconnected Q is co-r.e. complete
in the plane and PSPACE complete in strips. See docs/corollary-5.6.md.

`TwoConnectedPolycubes.slabTwoProved` proves co-r.e. completeness of tiling
the height-two slab with a fixed connected 15-voxel polycube and an input
connected polycube. `TwoConnectedPolycubes.spaceProved` proves full-space
co-r.e. completeness with a fixed connected 45-voxel polycube and an input
connected polycube. Both allow all cube rotations and reflections. See
docs/two-connected-polycubes.md.

`TwoConnectedPolycubes.slabsProved` proves co-r.e. completeness for every
fixed slab height greater than one. The fixed connected tile has at most
45 voxels, independently of the height.

`ThreeTranslationPolycubes.proved` proves Corollary 5.9: tiling full 3D space
or any fixed slab height greater than one by translations of three connected
polycubes is co-r.e. complete. Two tiles are fixed, each with at most 45 voxels.
See docs/corollary-5.9.md.

`WangPeriodicCNF.coREComplete` and `WangPeriodicCNF.localCoREComplete`
prove two-dimensional periodic CNF SAT co-r.e. completeness.
`PeriodicThreeCNF.localThreeCNFCoREComplete` and
`PeriodicThreeSATThree.localThreeSATThreeCoREComplete` prove the corresponding
local 3SAT and 3SAT-3 results. Together with the native flat-encoded one-dimensional PSPACE endpoints,
these complete Theorems 3.3–3.4.

`PeriodicPlanarSAT.ordinary_PSPACEComplete`, `ordinaryThree_PSPACEComplete`,
`exactOne_PSPACEComplete`, and `exactOneThree_PSPACEComplete` prove local
one-dimensional planar 3SAT, 3SAT-3, 1-in-3SAT, and 1-in-3SAT-3 PSPACE
completeness, with supplied drawings under the native flat encoding and
the original fixed linear grid bounds.

`Gadget.NormalizedOrientation.lineProblem_PSPACEComplete` proves normalized
one-dimensional trichromatic orientation PSPACE-complete under the native binary
cell-table encoding, with separated vertices and a blank vertical boundary.

`PeriodicThreeDM.localPlanarLineProblem_PSPACEComplete` proves local planar
one-dimensional 3DM with colored degree 2 or 3 PSPACE-complete under the native
binary encoding, including verification of the complete supplied drawing.

`PeriodicTwoSAT.local_certified` proves Theorem 4.1 in every fixed dimension:
an executable local periodic 2SAT solver, with a complete polynomial bound of
degree `3(d*d+d+1)` in the explicit indexed input size. It includes clause
anchoring, an explicitly indexed finite lattice cover, and verified Horn
worklist reachability queries. Locality concerns offset differences, allowing
arbitrary common offsets. The cost model is the unit-cost indexed RAM.

`PeriodicLatticeGraph.bounded_augmenting_path` proves Lemma 4.3 in every
dimension, including general nonbipartite graphs. From each free vertex,
it gives a simple augmenting path of diameter at most `2*d*|E|`.

`PeriodicLatticeGraph.bipartition_two_periodic` proves Lemma 4.4 in every
dimension: a connected bipartite periodic graph's coloring is invariant under
twice any lattice translation.
`PeriodicBipartite.perfect_or_short_augmenting` proves Lemma 4.5 for arbitrary
period-one partial matchings of the infinite graph. The augmenting path has
free endpoints, unmatched forward edges, no repeated protovertex, and fewer
edges than the quotient has vertices.

`PeriodicBipartite.exists_period_one` proves Theorem 4.6 in every dimension.
`PeriodicBipartite.perfect_iff_quotient` characterizes perfect matchings by the
finite bipartite quotient, without a locality restriction.
`PeriodicBipartite.matchingSolver_certified` proves Theorem 4.7: an executable
indexed solver decides perfect matching and constructs a finite protoedge table
for a period-one matching, in every dimension. The complete unit-cost RAM
bound is `1000(E+1)(sqrt(V)+1)`; `matchingSolver_edge_sqrt_bound` gives
`4000E*sqrt(V)` for nonempty edge tables, including preparation and construction.

`Horn.exists_period_one` and `Horn.dual_exists_period_one` give constant models
for satisfiable periodic Horn and dual Horn formulas in every dimension.
`PeriodicCNF.hornCheck_correct` and `dualHornCheck_correct` certify executable
solvers on the existing periodic-CNF representation.
`Horn.PeriodicIndexed.certified` adds a linear operation bound for explicitly
indexed inputs in the unit-cost RAM model, including input preparation.
This does not assert a bit-Turing or Lean VM runtime bound.

This module is the public result interface. Lake's `LeanTrominoes.*` glob
checks every construction module independently of this import list.
-/

/-!
`FixedPolyominoSeed.corollary57` proves Corollary 5.7: two fixed polyominoes
have co-r.e.-complete finite-seed plane completion. The small tile is the
connected 15-cell bumpy I-tromino. The computable seed includes one prescribed
Q and finite P patterns; soundness recovers the source input from that same tiling.
-/

/-!
`PeriodicSubspaceTiling.lemma51` packages Lemma 5.1: arbitrary finite-footprint
periodic subspace tiling and completion are co-r.e. in every dimension, and
both strip problems are in PSPACE for each fixed polynomial bounding box.
The strip inputs use native binary fields; the window-to-Savitch evaluator
has a run-level finite-alphabet Turing-machine space certificate.
-/

/-!
`PeriodicGridDrawing.polygonal_cubic_refinement` proves Theorem 2.2 for
arbitrary planar local polygonal drawings of degree-four periodic graphs,
including loops and bends on period seams. The output is planar, local,
and orthogonal, with grid size at most `84480*M^3`. Original vertices are
scaled exactly by `(16*M+32)*(160*M+1600)`.
-/
