import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATLocalVertexDistinctness
import LeanTrominoes.PeriodicOrthocrossingPlanarSATNoncarrierSeparation

/-!
# Distinct clause positions in retained non-carrier components

Every retained component except a straight carrier lens lies in the closed
standard part of one planar-SAT macrocell.  A common clause point forces the
two macrocell centers to agree.  Existing center uniqueness identifies the
component, except for multiple routed-variable arms at one lifted variable
site; the six fixed arm-clause coordinates separate that final case.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Two standard planar-SAT macrocells containing one common point have the
same drawing-grid center. -/
theorem planarSATMacrocellCenter_eq_of_common_point
    {firstCenter secondCenter point : Cell}
    (firstBounded : InPlanarSATMacrocell firstCenter point)
    (secondBounded : InPlanarSATMacrocell secondCenter point) :
    firstCenter = secondCenter := by
  rcases firstCenter with ⟨firstX, firstY⟩
  rcases secondCenter with ⟨secondX, secondY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [InPlanarSATMacrocell,
    planarSATMacrocellRouteLower,
    planarSATMacrocellRouteUpper,
    InClosedGridRectangle, planarMacroScale,
    Cell.add, Cell.scale] at firstBounded secondBounded
  apply Prod.ext <;> omega

/-- The clause vertex of a nonempty retained non-carrier component lies in
the component's standard macrocell. -/
theorem DrawingPlanarSATClauseMetadata.retainedClausePosition_in_macrocell
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (center : Cell)
    (centerEq :
      metadata.source.component.macrocellCenter formula = some center)
    (nonempty : metadata.clause.literals ≠ []) :
    InPlanarSATMacrocell center metadata.clause.position := by
  have notCarrier :
      ¬∃ link, metadata.source.component = .carrier link := by
    rintro ⟨link, componentEq⟩
    rw [componentEq] at centerEq
    simp [DrawingPlanarSATComponent.macrocellCenter] at centerEq
  have originalValid : metadata.Valid formula :=
    metadata.valid_of_retainedValid_of_not_carrier valid notCarrier
  have clauseMember :=
    metadata.retainedLocalClauseMember
      wellFormed degree isLocal valid
  have routesMatch :=
    metadata.retainedLocalDrawingRoutesMatch
      wellFormed degree isLocal valid
  cases literalsEq : metadata.clause.literals with
  | nil => exact (nonempty literalsEq).elim
  | cons literal rest =>
      have literalMember :
          (literal, 0) ∈ metadata.clause.literals.zipIdx := by
        simp [literalsEq]
      have endpoints :=
        (metadata.source.incidenceDrawing formula).physicalRoutesMatch
          routesMatch metadata.clause
          metadata.source.localClauseIndex clauseMember
          literal 0 literalMember
      have positionMember :
          metadata.clause.position ∈
            (metadata.source.incidenceDrawing formula).routes
              metadata.source.localClauseIndex 0 :=
        List.mem_of_mem_head? (by simp [endpoints.1])
      exact
        metadata.localRoutePoints_inPlanarSATMacrocell
          wellFormed degree isLocal originalValid
          center centerEq literalMember positionMember

/-- Two retained non-carrier components at one center are equal, unless they
are two active arms of the same routed-variable site. -/
theorem
    retainedNoncarrierComponents_eq_or_routedVariable_of_center_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (center : Cell)
    (firstCenterEq :
      first.source.component.macrocellCenter formula = some center)
    (secondCenterEq :
      second.source.component.macrocellCenter formula = some center) :
    first.source.component = second.source.component ∨
      ∃ site firstArm firstLink secondArm secondLink,
        first.source.component =
            .routedVariable site firstArm firstLink ∧
          second.source.component =
            .routedVariable site secondArm secondLink := by
  rcases first with ⟨firstClause, firstSource⟩
  rcases second with ⟨secondClause, secondSource⟩
  cases firstSource with
  | carrier firstLink firstIndex =>
      simp [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter] at firstCenterEq
  | crossover firstCrossing firstIndex =>
      cases secondSource with
      | carrier secondLink secondIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
      | crossover secondCrossing secondIndex =>
          left
          simp only [DrawingPlanarSATClauseSource.component]
          congr 1
          apply orientedCrossing_eq_of_point_eq
            wellFormed degree isLocal firstValid.1 secondValid.1
          apply Option.some.inj
          simpa [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] using
              firstCenterEq.trans secondCenterEq.symm
      | bend secondBend secondIndex =>
          exfalso
          apply orientedCrossing_point_ne_drawingRouteBend_drawingPoint
            wellFormed degree isLocal firstValid.1
            (List.mem_dedup.mp secondValid.1)
          apply Option.some.inj
          simpa [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] using
              firstCenterEq.trans secondCenterEq.symm
      | routedClause secondSite =>
          exfalso
          have actualCentersEq :
              firstCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1) secondSite.2 := by
            apply Option.some.inj
            simpa [DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          apply orientedCrossing_point_ne_liftedVertexPosition
            wellFormed degree firstValid.1
            (drawingClauseRouteSite_vertex_mem formula secondValid.1)
            secondSite.2
          simpa [liftedIncidenceVertexPosition] using actualCentersEq
      | routedVariable secondSite secondArmIndex secondArm secondLink
          secondIndex =>
          exfalso
          have actualCentersEq :
              firstCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.variable secondSite.1) secondSite.2 := by
            apply Option.some.inj
            simpa [DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          apply orientedCrossing_point_ne_liftedVertexPosition
            wellFormed degree firstValid.1
            (drawingVariableRouteSite_vertex_mem formula secondValid.1)
            secondSite.2
          simpa [liftedIncidenceVertexPosition] using actualCentersEq
  | bend firstBend firstIndex =>
      cases secondSource with
      | carrier secondLink secondIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
      | crossover secondCrossing secondIndex =>
          exfalso
          apply orientedCrossing_point_ne_drawingRouteBend_drawingPoint
            wellFormed degree isLocal secondValid.1
            (List.mem_dedup.mp firstValid.1)
          apply Option.some.inj
          simpa [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] using
              secondCenterEq.trans firstCenterEq.symm
      | bend secondBend secondIndex =>
          left
          simp only [DrawingPlanarSATClauseSource.component]
          congr 1
          apply drawingRouteBends_eq_of_drawingPoint_eq
            (PeriodicCNF.incidenceGraph formula)
            wellFormed degree isLocal
            (List.mem_dedup.mp firstValid.1)
            (List.mem_dedup.mp secondValid.1)
          apply Option.some.inj
          simpa [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] using
              firstCenterEq.trans secondCenterEq.symm
      | routedClause secondSite =>
          exfalso
          have actualCentersEq :
              firstBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula) =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1) secondSite.2 := by
            apply Option.some.inj
            simpa [DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          apply drawingRouteBend_drawingPoint_ne_liftedVertexPosition
            wellFormed degree isLocal
            (drawingClauseRouteSite_vertex_mem formula secondValid.1)
            secondSite.2 (List.mem_dedup.mp firstValid.1)
          simpa [liftedIncidenceVertexPosition] using actualCentersEq
      | routedVariable secondSite secondArmIndex secondArm secondLink
          secondIndex =>
          exfalso
          have actualCentersEq :
              firstBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula) =
                liftedIncidenceVertexPosition formula
                  (.variable secondSite.1) secondSite.2 := by
            apply Option.some.inj
            simpa [DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          apply drawingRouteBend_drawingPoint_ne_liftedVertexPosition
            wellFormed degree isLocal
            (drawingVariableRouteSite_vertex_mem formula secondValid.1)
            secondSite.2 (List.mem_dedup.mp firstValid.1)
          simpa [liftedIncidenceVertexPosition] using actualCentersEq
  | routedClause firstSite =>
      cases secondSource with
      | carrier secondLink secondIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
      | crossover secondCrossing secondIndex =>
          exfalso
          have actualCentersEq :
              secondCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.clause firstSite.1) firstSite.2 := by
            apply Option.some.inj
            simpa [DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                secondCenterEq.trans firstCenterEq.symm
          apply orientedCrossing_point_ne_liftedVertexPosition
            wellFormed degree secondValid.1
            (drawingClauseRouteSite_vertex_mem formula firstValid.1)
            firstSite.2
          simpa [liftedIncidenceVertexPosition] using actualCentersEq
      | bend secondBend secondIndex =>
          exfalso
          have actualCentersEq :
              secondBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula) =
                liftedIncidenceVertexPosition formula
                  (.clause firstSite.1) firstSite.2 := by
            apply Option.some.inj
            simpa [DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                secondCenterEq.trans firstCenterEq.symm
          apply drawingRouteBend_drawingPoint_ne_liftedVertexPosition
            wellFormed degree isLocal
            (drawingClauseRouteSite_vertex_mem formula firstValid.1)
            firstSite.2 (List.mem_dedup.mp secondValid.1)
          simpa [liftedIncidenceVertexPosition] using actualCentersEq
      | routedClause secondSite =>
          left
          simp only [DrawingPlanarSATClauseSource.component]
          congr 1
          apply liftedClauseRouteSite_eq
            formula firstValid.1 secondValid.1
          apply Option.some.inj
          simpa [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] using
              firstCenterEq.trans secondCenterEq.symm
      | routedVariable secondSite secondArmIndex secondArm secondLink
          secondIndex =>
          exfalso
          apply liftedClauseRouteSite_ne_liftedVariableRouteSite
            formula firstValid.1 secondValid.1
          apply Option.some.inj
          simpa [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] using
              firstCenterEq.trans secondCenterEq.symm
  | routedVariable firstSite firstArmIndex firstArm firstLink firstIndex =>
      cases secondSource with
      | carrier secondLink secondIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
      | crossover secondCrossing secondIndex =>
          exfalso
          have actualCentersEq :
              secondCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.variable firstSite.1) firstSite.2 := by
            apply Option.some.inj
            simpa [DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                secondCenterEq.trans firstCenterEq.symm
          apply orientedCrossing_point_ne_liftedVertexPosition
            wellFormed degree secondValid.1
            (drawingVariableRouteSite_vertex_mem formula firstValid.1)
            firstSite.2
          simpa [liftedIncidenceVertexPosition] using actualCentersEq
      | bend secondBend secondIndex =>
          exfalso
          have actualCentersEq :
              secondBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula) =
                liftedIncidenceVertexPosition formula
                  (.variable firstSite.1) firstSite.2 := by
            apply Option.some.inj
            simpa [DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                secondCenterEq.trans firstCenterEq.symm
          apply drawingRouteBend_drawingPoint_ne_liftedVertexPosition
            wellFormed degree isLocal
            (drawingVariableRouteSite_vertex_mem formula firstValid.1)
            firstSite.2 (List.mem_dedup.mp secondValid.1)
          simpa [liftedIncidenceVertexPosition] using actualCentersEq
      | routedClause secondSite =>
          exfalso
          apply liftedClauseRouteSite_ne_liftedVariableRouteSite
            formula secondValid.1 firstValid.1
          apply Option.some.inj
          simpa [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter] using
              secondCenterEq.trans firstCenterEq.symm
      | routedVariable secondSite secondArmIndex secondArm secondLink
          secondIndex =>
          have siteEq : firstSite = secondSite := by
            apply liftedVariableRouteSite_eq
              formula firstValid.1 secondValid.1
            apply Option.some.inj
            simpa [DrawingPlanarSATClauseSource.component,
              DrawingPlanarSATComponent.macrocellCenter] using
                firstCenterEq.trans secondCenterEq.symm
          subst secondSite
          right
          exact
            ⟨firstSite, firstArm, firstLink, secondArm, secondLink,
              rfl, rfl⟩

/-- Two routed-variable components at one site with equal clause positions
use the same physical arm and hence are the same component. -/
theorem routedVariableComponents_eq_of_clause_position_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (site : VariableRouteSite Variable)
    (firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable))
    (firstArmIndex secondArmIndex : Nat)
    (firstArm secondArm : DuplicatorArm)
    (firstLink secondLink :
      EqualityLink (PlanarSATNode Variable))
    (firstClauseIndex secondClauseIndex : Nat)
    (firstValid :
      (⟨firstClause,
        .routedVariable site firstArmIndex firstArm
          firstLink firstClauseIndex⟩ :
        DrawingPlanarSATClauseMetadata Variable).RetainedValid formula)
    (secondValid :
      (⟨secondClause,
        .routedVariable site secondArmIndex secondArm
          secondLink secondClauseIndex⟩ :
        DrawingPlanarSATClauseMetadata Variable).RetainedValid formula)
    (positionEq :
      firstClause.position = secondClause.position) :
    DrawingPlanarSATComponent.routedVariable site firstArm firstLink =
      .routedVariable site secondArm secondLink := by
  have firstLinkMem :
      firstLink ∈ routedVariableLinksAt formula site :=
    List.fst_mem_of_mem_zipIdx firstValid.2.1
  have secondLinkMem :
      secondLink ∈ routedVariableLinksAt formula site :=
    List.fst_mem_of_mem_zipIdx secondValid.2.1
  have firstClauseMem := firstValid.2.2.2
  have secondClauseMem := secondValid.2.2.2
  simp [drawingPlanarSATRoutedVariableFormulaAt,
    equalityInstance, EmbeddedClause.rename,
    EmbeddedClause.map] at firstClauseMem secondClauseMem
  rcases firstClauseMem with
      ⟨firstClauseEq, firstIndexEq⟩ |
      ⟨firstClauseEq, firstIndexEq⟩ <;>
    rcases secondClauseMem with
      ⟨secondClauseEq, secondIndexEq⟩ |
      ⟨secondClauseEq, secondIndexEq⟩
  all_goals
    have firstArmEq :
        firstArm = firstLink.first.duplicatorArm :=
      firstValid.2.2.1
    have secondArmEq :
        secondArm = secondLink.first.duplicatorArm :=
      secondValid.2.2.1
    have firstPositions :=
      routedVariableLink_positions formula site firstLinkMem
    have secondPositions :=
      routedVariableLink_positions formula site secondLinkMem
    rw [firstClauseEq, secondClauseEq] at positionEq
    rw [firstPositions, secondPositions,
      ← firstArmEq, ← secondArmEq] at positionEq
    have armsEq : firstArm = secondArm := by
      cases firstArm <;> cases secondArm <;>
        simp_all [routedVariableEqualityPositions,
          duplicatorArmEqualityPositions,
          routedVariableOrigin, Cell.add]
    have linksEq :
        firstLink = secondLink :=
      routedVariableLinksAt_eq_of_duplicatorArm_eq
        formula wellFormed degree site
        firstLinkMem secondLinkMem
        (firstArmEq.symm.trans (armsEq.trans secondArmEq))
    cases linksEq
    exact congrArg
      (fun arm =>
        DrawingPlanarSATComponent.routedVariable
          site arm firstLink)
      armsEq

/-- Nonempty retained non-carrier components with equal clause positions are
the same geometric component. -/
theorem retainedNoncarrierComponents_eq_of_clause_position_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (firstCenter secondCenter : Cell)
    (firstCenterEq :
      first.source.component.macrocellCenter formula =
        some firstCenter)
    (secondCenterEq :
      second.source.component.macrocellCenter formula =
        some secondCenter)
    (firstNonempty : first.clause.literals ≠ [])
    (secondNonempty : second.clause.literals ≠ [])
    (positionEq : first.clause.position = second.clause.position) :
    first.source.component = second.source.component := by
  have firstBounded :=
    first.retainedClausePosition_in_macrocell
      wellFormed degree isLocal firstValid
      firstCenter firstCenterEq firstNonempty
  have secondBounded :=
    second.retainedClausePosition_in_macrocell
      wellFormed degree isLocal secondValid
      secondCenter secondCenterEq secondNonempty
  have centersEq : firstCenter = secondCenter :=
    planarSATMacrocellCenter_eq_of_common_point
      firstBounded (by simpa [positionEq] using secondBounded)
  subst secondCenter
  rcases
      retainedNoncarrierComponents_eq_or_routedVariable_of_center_eq
        wellFormed degree isLocal first second
        firstValid secondValid firstCenter
        firstCenterEq secondCenterEq with
    componentsEq | routed
  · exact componentsEq
  · rcases routed with
      ⟨site, firstArm, firstLink, secondArm, secondLink,
        firstComponentEq, secondComponentEq⟩
    rcases first with ⟨firstClause, firstSource⟩
    rcases second with ⟨secondClause, secondSource⟩
    cases firstSource with
    | crossover crossing clauseIndex =>
        simp [DrawingPlanarSATClauseSource.component] at firstComponentEq
    | carrier link clauseIndex =>
        simp [DrawingPlanarSATClauseSource.component] at firstComponentEq
    | bend routeBend clauseIndex =>
        simp [DrawingPlanarSATClauseSource.component] at firstComponentEq
    | routedClause routedSite =>
        simp [DrawingPlanarSATClauseSource.component] at firstComponentEq
    | routedVariable actualFirstSite firstArmIndex actualFirstArm
        actualFirstLink firstClauseIndex =>
        injection firstComponentEq with siteEq firstArmEq firstLinkEq
        subst actualFirstSite
        subst actualFirstArm
        subst actualFirstLink
        cases secondSource with
        | crossover crossing clauseIndex =>
            simp [DrawingPlanarSATClauseSource.component] at secondComponentEq
        | carrier link clauseIndex =>
            simp [DrawingPlanarSATClauseSource.component] at secondComponentEq
        | bend routeBend clauseIndex =>
            simp [DrawingPlanarSATClauseSource.component] at secondComponentEq
        | routedClause routedSite =>
            simp [DrawingPlanarSATClauseSource.component] at secondComponentEq
        | routedVariable actualSecondSite secondArmIndex actualSecondArm
            actualSecondLink secondClauseIndex =>
            injection secondComponentEq with
              siteEq secondArmEq secondLinkEq
            subst actualSecondSite
            subst actualSecondArm
            subst actualSecondLink
            exact
              routedVariableComponents_eq_of_clause_position_eq
                wellFormed degree site
                firstClause secondClause
                firstArmIndex secondArmIndex
                firstArm secondArm firstLink secondLink
                firstClauseIndex secondClauseIndex
                firstValid secondValid positionEq

end LeanTrominoes.PeriodicOrthocrossing
