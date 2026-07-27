import LeanTrominoes.PeriodicOrthocrossingCrossoverCenterDisjointness
import LeanTrominoes.PeriodicOrthocrossingPlanarSATRoutedVariableSeparation

/-!
# Separation of non-carrier planar-SAT components

Every component other than a straight carrier lens is contained in one
standard macrocell.  The center-classification theorems show that distinct
components have distinct centers, except for different active arms at one
routed-variable site; that exceptional case is handled by the certified
finite duplicator-arm separation theorem.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Routes selected from two distinct non-carrier components avoid one
another.  The assumptions naming their centers exclude carrier lenses
without introducing a separate component predicate. -/
theorem drawingPlanarSATMetadata_noncarrierRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (firstMetadata secondMetadata :
      DrawingPlanarSATClauseMetadata Variable)
    (firstValid : firstMetadata.Valid formula)
    (secondValid : secondMetadata.Valid formula)
    (firstCenter secondCenter : Cell)
    (firstCenterEq :
      firstMetadata.source.component.macrocellCenter formula =
        some firstCenter)
    (secondCenterEq :
      secondMetadata.source.component.macrocellCenter formula =
        some secondCenter)
    (differentComponents :
      firstMetadata.source.component ≠
        secondMetadata.source.component)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMem :
      (firstLiteral, firstLiteralIndex) ∈
        firstMetadata.clause.literals.zipIdx)
    (secondLiteralMem :
      (secondLiteral, secondLiteralIndex) ∈
        secondMetadata.clause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((firstMetadata.source.incidenceDrawing formula).routes
        firstMetadata.source.localClauseIndex firstLiteralIndex)
      ((secondMetadata.source.incidenceDrawing formula).routes
        secondMetadata.source.localClauseIndex secondLiteralIndex) := by
  rcases firstMetadata with ⟨firstClause, firstSource⟩
  rcases secondMetadata with ⟨secondClause, secondSource⟩
  cases firstSource with
  | carrier firstLink firstLocalClauseIndex =>
      simp [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter] at firstCenterEq
  | crossover firstCrossing firstLocalClauseIndex =>
      cases secondSource with
      | carrier secondLink secondLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
      | crossover secondCrossing secondLocalClauseIndex =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .crossover firstCrossing firstLocalClauseIndex⟩
              ⟨secondClause, .crossover secondCrossing secondLocalClauseIndex⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              firstCrossing.point = secondCrossing.point := by
            apply Option.some.inj
            exact firstCenterEq.trans
              ((congrArg some centersEq).trans secondCenterEq.symm)
          apply differentComponents
          simp only [DrawingPlanarSATClauseSource.component]
          congr 1
          exact
            orientedCrossing_eq_of_point_eq
              wellFormed degree isLocal
              firstValid.1 secondValid.1
              actualCentersEq
      | bend secondBend secondLocalClauseIndex =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .crossover firstCrossing firstLocalClauseIndex⟩
              ⟨secondClause, .bend secondBend secondLocalClauseIndex⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              firstCrossing.point =
                secondBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula) := by
            apply Option.some.inj
            exact firstCenterEq.trans
              ((congrArg some centersEq).trans secondCenterEq.symm)
          exact
            (orientedCrossing_point_ne_drawingRouteBend_drawingPoint
              wellFormed degree isLocal firstValid.1
              (List.mem_dedup.mp secondValid.1))
              actualCentersEq
      | routedClause secondSite =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .crossover firstCrossing firstLocalClauseIndex⟩
              ⟨secondClause, .routedClause secondSite⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              firstCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1) secondSite.2 := by
            apply Option.some.inj
            exact firstCenterEq.trans
              ((congrArg some centersEq).trans secondCenterEq.symm)
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree firstValid.1
              (drawingClauseRouteSite_vertex_mem formula secondValid.1)
              secondSite.2)
              (by simpa [liftedIncidenceVertexPosition] using
                actualCentersEq)
      | routedVariable secondSite secondArmIndex secondArm secondLink
          secondLocalClauseIndex =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .crossover firstCrossing firstLocalClauseIndex⟩
              ⟨secondClause, .routedVariable secondSite secondArmIndex
                secondArm secondLink secondLocalClauseIndex⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              firstCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.variable secondSite.1) secondSite.2 := by
            apply Option.some.inj
            exact firstCenterEq.trans
              ((congrArg some centersEq).trans secondCenterEq.symm)
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree firstValid.1
              (drawingVariableRouteSite_vertex_mem formula secondValid.1)
              secondSite.2)
              (by simpa [liftedIncidenceVertexPosition] using
                actualCentersEq)
  | bend firstBend firstLocalClauseIndex =>
      cases secondSource with
      | carrier secondLink secondLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
      | crossover secondCrossing secondLocalClauseIndex =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .bend firstBend firstLocalClauseIndex⟩
              ⟨secondClause, .crossover secondCrossing secondLocalClauseIndex⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              secondCrossing.point =
                firstBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula) := by
            apply Option.some.inj
            exact secondCenterEq.trans
              ((congrArg some centersEq.symm).trans firstCenterEq.symm)
          exact
            (orientedCrossing_point_ne_drawingRouteBend_drawingPoint
              wellFormed degree isLocal secondValid.1
              (List.mem_dedup.mp firstValid.1))
              actualCentersEq
      | bend secondBend secondLocalClauseIndex =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .bend firstBend firstLocalClauseIndex⟩
              ⟨secondClause, .bend secondBend secondLocalClauseIndex⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              firstBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula) =
                secondBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula) := by
            apply Option.some.inj
            exact firstCenterEq.trans
              ((congrArg some centersEq).trans secondCenterEq.symm)
          apply differentComponents
          simp only [DrawingPlanarSATClauseSource.component]
          congr 1
          exact
            drawingRouteBends_eq_of_drawingPoint_eq
              (PeriodicCNF.incidenceGraph formula)
              wellFormed degree isLocal
              (List.mem_dedup.mp firstValid.1)
              (List.mem_dedup.mp secondValid.1)
              actualCentersEq
      | routedClause secondSite =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .bend firstBend firstLocalClauseIndex⟩
              ⟨secondClause, .routedClause secondSite⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              firstBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula) =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1) secondSite.2 := by
            apply Option.some.inj
            exact firstCenterEq.trans
              ((congrArg some centersEq).trans secondCenterEq.symm)
          exact
            (drawingRouteBend_drawingPoint_ne_liftedVertexPosition
              wellFormed degree isLocal
              (drawingClauseRouteSite_vertex_mem formula secondValid.1)
              secondSite.2
              (List.mem_dedup.mp firstValid.1))
              (by simpa [liftedIncidenceVertexPosition] using
                actualCentersEq)
      | routedVariable secondSite secondArmIndex secondArm secondLink
          secondLocalClauseIndex =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .bend firstBend firstLocalClauseIndex⟩
              ⟨secondClause, .routedVariable secondSite secondArmIndex
                secondArm secondLink secondLocalClauseIndex⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              firstBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula) =
                liftedIncidenceVertexPosition formula
                  (.variable secondSite.1) secondSite.2 := by
            apply Option.some.inj
            exact firstCenterEq.trans
              ((congrArg some centersEq).trans secondCenterEq.symm)
          exact
            (drawingRouteBend_drawingPoint_ne_liftedVertexPosition
              wellFormed degree isLocal
              (drawingVariableRouteSite_vertex_mem formula secondValid.1)
              secondSite.2
              (List.mem_dedup.mp firstValid.1))
              (by simpa [liftedIncidenceVertexPosition] using
                actualCentersEq)
  | routedClause firstSite =>
      cases secondSource with
      | carrier secondLink secondLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
      | crossover secondCrossing secondLocalClauseIndex =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .routedClause firstSite⟩
              ⟨secondClause, .crossover secondCrossing secondLocalClauseIndex⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              secondCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.clause firstSite.1) firstSite.2 := by
            apply Option.some.inj
            exact secondCenterEq.trans
              ((congrArg some centersEq.symm).trans firstCenterEq.symm)
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree secondValid.1
              (drawingClauseRouteSite_vertex_mem formula firstValid.1)
              firstSite.2)
              (by simpa [liftedIncidenceVertexPosition] using
                actualCentersEq)
      | bend secondBend secondLocalClauseIndex =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .routedClause firstSite⟩
              ⟨secondClause, .bend secondBend secondLocalClauseIndex⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              secondBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula) =
                liftedIncidenceVertexPosition formula
                  (.clause firstSite.1) firstSite.2 := by
            apply Option.some.inj
            exact secondCenterEq.trans
              ((congrArg some centersEq.symm).trans firstCenterEq.symm)
          exact
            (drawingRouteBend_drawingPoint_ne_liftedVertexPosition
              wellFormed degree isLocal
              (drawingClauseRouteSite_vertex_mem formula firstValid.1)
              firstSite.2
              (List.mem_dedup.mp secondValid.1))
              (by simpa [liftedIncidenceVertexPosition] using
                actualCentersEq)
      | routedClause secondSite =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .routedClause firstSite⟩
              ⟨secondClause, .routedClause secondSite⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              liftedIncidenceVertexPosition formula
                  (.clause firstSite.1) firstSite.2 =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1) secondSite.2 := by
            apply Option.some.inj
            exact firstCenterEq.trans
              ((congrArg some centersEq).trans secondCenterEq.symm)
          apply differentComponents
          simp only [DrawingPlanarSATClauseSource.component]
          congr 1
          exact
            liftedClauseRouteSite_eq
              formula firstValid.1 secondValid.1
              actualCentersEq
      | routedVariable secondSite secondArmIndex secondArm secondLink
          secondLocalClauseIndex =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .routedClause firstSite⟩
              ⟨secondClause, .routedVariable secondSite secondArmIndex
                secondArm secondLink secondLocalClauseIndex⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          apply
            liftedClauseRouteSite_ne_liftedVariableRouteSite
              formula firstValid.1 secondValid.1
          apply Option.some.inj
          exact firstCenterEq.trans
            ((congrArg some centersEq).trans secondCenterEq.symm)
  | routedVariable firstSite firstArmIndex firstArm firstLink
      firstLocalClauseIndex =>
      cases secondSource with
      | carrier secondLink secondLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
      | crossover secondCrossing secondLocalClauseIndex =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .routedVariable firstSite firstArmIndex
                firstArm firstLink firstLocalClauseIndex⟩
              ⟨secondClause, .crossover secondCrossing secondLocalClauseIndex⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              secondCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.variable firstSite.1) firstSite.2 := by
            apply Option.some.inj
            exact secondCenterEq.trans
              ((congrArg some centersEq.symm).trans firstCenterEq.symm)
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree secondValid.1
              (drawingVariableRouteSite_vertex_mem formula firstValid.1)
              firstSite.2)
              (by simpa [liftedIncidenceVertexPosition] using
                actualCentersEq)
      | bend secondBend secondLocalClauseIndex =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .routedVariable firstSite firstArmIndex
                firstArm firstLink firstLocalClauseIndex⟩
              ⟨secondClause, .bend secondBend secondLocalClauseIndex⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          have actualCentersEq :
              secondBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula) =
                liftedIncidenceVertexPosition formula
                  (.variable firstSite.1) firstSite.2 := by
            apply Option.some.inj
            exact secondCenterEq.trans
              ((congrArg some centersEq.symm).trans firstCenterEq.symm)
          exact
            (drawingRouteBend_drawingPoint_ne_liftedVertexPosition
              wellFormed degree isLocal
              (drawingVariableRouteSite_vertex_mem formula firstValid.1)
              firstSite.2
              (List.mem_dedup.mp secondValid.1))
              (by simpa [liftedIncidenceVertexPosition] using
                actualCentersEq)
      | routedClause secondSite =>
          apply
            DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
              wellFormed degree isLocal
              ⟨firstClause, .routedVariable firstSite firstArmIndex
                firstArm firstLink firstLocalClauseIndex⟩
              ⟨secondClause, .routedClause secondSite⟩
              firstValid secondValid firstCenter secondCenter
              firstCenterEq secondCenterEq
              firstLiteralMem secondLiteralMem
          intro centersEq
          apply
            liftedClauseRouteSite_ne_liftedVariableRouteSite
              formula secondValid.1 firstValid.1
          apply Option.some.inj
          exact secondCenterEq.trans
            ((congrArg some centersEq.symm).trans firstCenterEq.symm)
      | routedVariable secondSite secondArmIndex secondArm secondLink
          secondLocalClauseIndex =>
          by_cases centersEq : firstCenter = secondCenter
          · have actualCentersEq :
                liftedIncidenceVertexPosition formula
                    (.variable firstSite.1) firstSite.2 =
                  liftedIncidenceVertexPosition formula
                    (.variable secondSite.1) secondSite.2 := by
              apply Option.some.inj
              exact firstCenterEq.trans
                ((congrArg some centersEq).trans secondCenterEq.symm)
            exact
              drawingPlanarSATRoutedVariableMetadata_routesAvoidEachOther_of_sameCenter
                formula wellFormed degree
                firstValid secondValid actualCentersEq
                differentComponents
                firstLiteralMem secondLiteralMem
          · exact
              DrawingPlanarSATClauseMetadata.localRoutes_avoidEachOther_of_macrocellCenters_ne
                wellFormed degree isLocal
                ⟨firstClause, .routedVariable firstSite firstArmIndex
                  firstArm firstLink firstLocalClauseIndex⟩
                ⟨secondClause, .routedVariable secondSite secondArmIndex
                  secondArm secondLink secondLocalClauseIndex⟩
                firstValid secondValid firstCenter secondCenter
                firstCenterEq secondCenterEq
                firstLiteralMem secondLiteralMem centersEq

end PeriodicOrthocrossing
end LeanTrominoes
