import LeanTrominoes.PositionedPeriodicCNFRelativeRouteSeparation
import LeanTrominoes.PositionedPeriodicCNFScaling
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation

/-!
# Relative route separation under positive scaling

Uniform positive integral refinement preserves both the logical incidence
enumeration and complete continuous route separation.  This module lifts the
route-level scaling theorem to the metadata-rich relative-shift interface.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Relative incidence-route separation survives positive uniform coordinate
scaling. -/
theorem RelativeIncidenceRoutesAvoidEachOther.scale
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    {factor : Nat}
    (factorPositive : 0 < factor)
    (separated :
      RelativeIncidenceRoutesAvoidEachOther source placement routes) :
    RelativeIncidenceRoutesAvoidEachOther
      (source.scale factor)
      (placement.scale factor)
      (scaleIncidenceRoutes factor routes) := by
  intro first firstMember second secondMember
    relativeTranslate occurrencesDifferent
  have firstSourceMember :
      first ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    simpa using firstMember
  have secondSourceMember :
      second ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    simpa using secondMember
  have avoids :=
    separated first firstSourceMember second secondSourceMember
      relativeTranslate occurrencesDifferent
  have factorPositiveInt : 0 < (factor : Int) := by
    exact_mod_cast factorPositive
  have scaled := avoids.scalePolyline factorPositiveInt
  simpa [scaleIncidenceRoutes, scalePolyline,
    PeriodicOrthocrossing.translatePolyline,
    List.map_map, Function.comp_def, Cell.scale_add] using scaled

end PositionedPeriodicCNF
end LeanTrominoes
