import LeanTrominoes.PeriodicGridDrawing
import LeanTrominoes.PeriodicThreeDMGraphOrientation

/-!
# Planar presentations of periodic three-dimensional matching

The semantic 3DM reduction and its geometric realization are deliberately
separate.  This file states the exact certificate expected from a geometric
construction: the periodic 3DM incidence graph is drawn by compatible
orthogonal routes, no lifted route enters another route, and no lifted route
passes through a vertex.

Edge routes use the incidence graph's list order.  By
`PeriodicThreeDM.incidenceGraph_edges_eq_tags_map`, that is also the order of
the retained red, green, and blue incidence tags, so a later normalization
can color every route without reconstructing color information from its
geometry.
-/

namespace LeanTrominoes

namespace PeriodicThreeDM

/-- A certified planar orthogonal drawing of one periodic 3DM incidence
graph. -/
structure PlanarPresentation (problem : PeriodicThreeDM) where
  drawing : PeriodicGridDrawing
  problemWellFormed : problem.IsWellFormed
  compatible : drawing.IsCompatible problem.incidenceGraph
  orthogonal : drawing.IsOrthogonal
  planar : drawing.IsPlanar

/-- A periodic 3DM instance admits a certified planar grid presentation. -/
def HasPlanarPresentation (problem : PeriodicThreeDM) : Prop :=
  Nonempty problem.PlanarPresentation

/-- The restricted source problem used by Theorems 3.7 and 3.8 additionally
requires every colored element to have degree two or three. -/
structure RestrictedPlanarPresentation (problem : PeriodicThreeDM)
    extends problem.PlanarPresentation where
  degreeTwoOrThree : problem.DegreeTwoOrThree

namespace PlanarPresentation

/-- Compatibility certifies the well-formed incidence graph consumed by the
drawing. -/
theorem incidenceGraph_isWellFormed {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    problem.incidenceGraph.IsWellFormed :=
  presentation.compatible.1

/-- A planar presentation does not alter the matching/orientation semantics
of its underlying periodic 3DM instance. -/
theorem satisfiable_iff_graphHasOrientation
    {problem : PeriodicThreeDM}
    (_presentation : problem.PlanarPresentation) :
    problem.Satisfiable ↔ problem.GraphHasOrientation :=
  problem.satisfiable_iff_graphHasOrientation

end PlanarPresentation

namespace RestrictedPlanarPresentation

/-- The incidence graph of a restricted planar presentation has maximum
degree three. -/
theorem incidenceGraph_degreeAtMost_three
    {problem : PeriodicThreeDM}
    (presentation : problem.RestrictedPlanarPresentation) :
    problem.incidenceGraph.DegreeAtMost 3 :=
  problem.incidenceGraph_degreeAtMostThree
    presentation.problemWellFormed presentation.degreeTwoOrThree

end RestrictedPlanarPresentation

end PeriodicThreeDM

end LeanTrominoes
