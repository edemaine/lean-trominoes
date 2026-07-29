import LeanTrominoes.RetainedRayRasterization
import LeanTrominoes.PlanarThreeSATRoutedClauseIncidenceDrawing

/-!
# Retained-ray embedded-CNF incidence drawings

This file packages retained-ray rasterizability for every genuine route of a
finite embedded CNF.  The certificate is stable under coordinate translation
and logical-variable renaming.  Octilinear drawings satisfy it immediately,
while the direct routed-clause star is certified separately by its three
exceptional primitive vectors.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT

/-- Common translation preserves retained-ray rasterizability. -/
theorem RetainedRayPolyline.translate
    {points : List Cell}
    (retained : RetainedRayPolyline points)
    (offset : Cell) :
    RetainedRayPolyline
      (points.map (Cell.add offset)) := by
  intro translatedSegment translatedSegmentMember
  rw [EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
    at translatedSegmentMember
  rcases List.mem_map.mp translatedSegmentMember with
    ⟨segment, segmentMember, rfl⟩
  simpa [GridSegment.translate, Cell.add, Cell.sub] using
    retained segment segmentMember

end PeriodicEightOccurrenceSplit

namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

open PeriodicEightOccurrenceSplit

/-- Every genuine route of a finite embedded-CNF drawing uses only retained
ray slopes. -/
def RoutesRetainedRay
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ incidenceIndex : Fin drawing.incidences.length,
    RetainedRayPolyline
      (drawing.routeAt
        (drawing.incidenceAt incidenceIndex))

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.RoutesRetainedRay := by
  unfold RoutesRetainedRay RetainedRayPolyline
    RetainedRayVector
  unfold incidenceAt incidences routeAt
  infer_instance

/-- Every octilinear drawing is retained-ray rasterizable. -/
theorem RoutesRetainedRay.of_routesOctilinear
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (octilinear : drawing.RoutesOctilinear) :
    drawing.RoutesRetainedRay := by
  intro incidenceIndex
  exact RetainedRayPolyline.of_octilinear
    (octilinear incidenceIndex)

/-- Every orthogonal finite drawing is retained-ray rasterizable. -/
theorem RoutesRetainedRay.of_isOrthogonal
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (orthogonal : drawing.IsOrthogonal) :
    drawing.RoutesRetainedRay :=
  RoutesRetainedRay.of_routesOctilinear
    (RoutesOctilinear.of_isOrthogonal orthogonal)

/-- Translation preserves the retained-ray route certificate. -/
theorem RoutesRetainedRay.translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (retained : drawing.RoutesRetainedRay)
    (offset : Cell) :
    (drawing.translate offset).RoutesRetainedRay := by
  intro translatedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  rw [incidenceEqual, routeAt_translate_incidence]
  exact (retained originalIndex).translate offset

/-- Logical-variable renaming changes no route coordinates. -/
theorem RoutesRetainedRay.rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (retained : drawing.RoutesRetainedRay)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename
      variableMap targetPosition).RoutesRetainedRay := by
  intro renamedIndex
  let originalIndex :
      Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length
          drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
  exact retained originalIndex

/-- A retained-ray certificate can also be pulled back through a logical
rename because renaming leaves all route coordinates unchanged. -/
theorem RoutesRetainedRay.of_rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (retained :
      (drawing.rename
        variableMap targetPosition).RoutesRetainedRay) :
    drawing.RoutesRetainedRay := by
  intro originalIndex
  let renamedIndex :
      Fin (drawing.rename
        variableMap targetPosition).incidences.length :=
    ⟨originalIndex.val, by
      simpa only [rename_incidences_length] using
        originalIndex.isLt⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  have renamedRoute := retained renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
    at renamedRoute
  exact renamedRoute

/-- Membership-style form of the finite retained-ray certificate. -/
theorem routesRetainedRay_iff
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    drawing.RoutesRetainedRay ↔
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈
            drawing.formula.zipIdx →
          ∀ literal literalIndex,
            (literal, literalIndex) ∈
                clause.literals.zipIdx →
              RetainedRayPolyline
                (drawing.routes
                  clauseIndex literalIndex) := by
  constructor
  · intro retained clause clauseIndex clauseMember
      literal literalIndex literalMember
    let incidence : EmbeddedCNFIncidence Variable :=
      ⟨clause, clauseIndex, literal, literalIndex⟩
    have incidenceMember :
        incidence ∈ drawing.incidences := by
      exact
        (mem_embeddedCNFIncidences_iff
          drawing.formula incidence).mpr
          ⟨clauseMember, literalMember⟩
    rcases List.mem_iff_get.mp incidenceMember with
      ⟨incidenceIndex, incidenceEqual⟩
    have routeRetained := retained incidenceIndex
    have incidenceAtEqual :
        drawing.incidenceAt incidenceIndex =
          incidence := incidenceEqual
    rw [incidenceAtEqual] at routeRetained
    exact routeRetained
  · intro retained incidenceIndex
    let incidence :=
      drawing.incidenceAt incidenceIndex
    have incidenceMember :
        incidence ∈ drawing.incidences :=
      List.get_mem drawing.incidences incidenceIndex
    have indexedMembers :=
      (mem_embeddedCNFIncidences_iff
        drawing.formula incidence).mp incidenceMember
    exact retained
      incidence.clause incidence.clauseIndex
        indexedMembers.1
      incidence.literal incidence.literalIndex
        indexedMembers.2

/-- A direct route is retained-ray rasterizable when its forward
clause-to-variable displacement is classified. -/
theorem straightIncidenceRoute_retainedRay
    {source target : Cell}
    (retained :
      RetainedRayVector
        (Cell.sub target source)) :
    RetainedRayPolyline
      (straightIncidenceRoute source target) := by
  intro segment segmentMember
  simp only [straightIncidenceRoute,
    gridPolylineSegments, List.mem_cons]
    at segmentMember
  rcases segmentMember with rfl | impossible
  · exact retained
  · contradiction

/-- A pointwise displacement certificate makes every route of a direct
incidence drawing retained-ray rasterizable. -/
theorem straightIncidenceDrawing_routesRetainedRay
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell)
    (valid :
      ∀ clause ∈ formula,
        ∀ literal ∈ clause.literals,
          RetainedRayVector
            (Cell.sub
              (variablePosition literal.1)
              clause.position)) :
    (straightIncidenceDrawing
      formula variablePosition).RoutesRetainedRay := by
  rw [routesRetainedRay_iff]
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  have sourceClauseMember :
      (clause, clauseIndex) ∈ formula.zipIdx := by
    simpa [straightIncidenceDrawing] using
      clauseMember
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      sourceClauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  change
    RetainedRayPolyline
      (straightIncidenceRoutes
        formula variablePosition
        clauseIndex literalIndex)
  rw [straightIncidenceRoutes, clauseLookup]
  change
    RetainedRayPolyline
      (match clause.literals[literalIndex]? with
      | none => []
      | some literal =>
          straightIncidenceRoute
            clause.position
            (variablePosition literal.1))
  rw [literalLookup]
  exact straightIncidenceRoute_retainedRay
    (valid clause
      (List.fst_mem_of_mem_zipIdx
        sourceClauseMember)
      literal
      (List.fst_mem_of_mem_zipIdx literalMember))

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT

namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT

/-- The three-port routed-clause template uses exactly the three exceptional
retained primitive rays. -/
theorem routedClausePortFormula_retainedRayVectors
    (literals : List (DuplicatorArm × Bool)) :
    ∀ clause ∈ routedClausePortFormula literals,
      ∀ literal ∈ clause.literals,
        RetainedRayVector
          (Cell.sub
            (DuplicatorArm.portPosition literal.1)
            clause.position) := by
  intro clause clauseMember literal literalMember
  simp only [routedClausePortFormula,
    List.mem_singleton] at clauseMember
  subst clause
  rcases literal with ⟨arm, polarity⟩
  change
    RetainedRayVector
      (Cell.sub arm.portPosition (10, 10))
  cases arm <;> native_decide

/-- Every genuine route of the direct routed-clause template is supported
by the combined retained-ray rasterizer. -/
theorem routedClausePortStraightIncidenceDrawing_routesRetainedRay
    (literals : List (DuplicatorArm × Bool)) :
    (routedClausePortStraightIncidenceDrawing
      literals).RoutesRetainedRay := by
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routesRetainedRay
      (routedClausePortFormula literals)
      DuplicatorArm.portPosition
      (routedClausePortFormula_retainedRayVectors
        literals)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
