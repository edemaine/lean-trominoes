import LeanTrominoes.RetainedAngularFanFinalFallbackCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOwnCycleSeparation
import LeanTrominoes.RetainedFinalSourceRouteOtherVertexFinalSegmentSeparation

/-!
# Final direct occurrences avoid cycles at other source centers

The direct-source atlas replaces a two-point source incidence by a
coordinated outer fan.  A finite certificate bounds every such replacement
inside the radius-288 expansion of the fully refined source segment.  This
lets the retained source drawing's vertex/segment separation clear every
cycle centered at a different source atom.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Every finite direct-source atlas route stays within the radius-288
expansion of its fully refined two-point local source segment. -/
theorem
    retainedDirectSourceFanCompleteRouteAt_point_in_scaledLocalSegmentRectangle :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈ retainedDirectSourceFanCompleteRouteAt kind index slot →
        let localSegment : GridSegment :=
          ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
            (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateLower))
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateUpper))
          point := by
  native_decide

/-- The original positioned two-point source segment represented by a
successful direct-source choice. -/
def RetainedDirectSourceRouteChoice.sourceSegment
    (choice : RetainedDirectSourceRouteChoice) :
    GridSegment :=
  ⟨Cell.add choice.origin
      ((retainedDirectSourceLocalRouteAt
        choice.kind choice.index).headD (0, 0)),
    Cell.add choice.origin
      ((retainedDirectSourceLocalRouteAt
        choice.kind choice.index).getLastD (0, 0))⟩

/-- Both endpoints of every direct local incidence lie in its half-open
`20 × 20` planar-SAT macrocell. -/
theorem retainedDirectSourceLocalRouteAt_endpoints_in_macrocell :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length),
      let route := retainedDirectSourceLocalRouteAt kind index
      (0 ≤ (route.headD (0, 0)).1 ∧
          (route.headD (0, 0)).1 < planarMacroScale ∧
          0 ≤ (route.headD (0, 0)).2 ∧
          (route.headD (0, 0)).2 < planarMacroScale) ∧
        (0 ≤ (route.getLastD (0, 0)).1 ∧
          (route.getLastD (0, 0)).1 < planarMacroScale ∧
          0 ≤ (route.getLastD (0, 0)).2 ∧
          (route.getLastD (0, 0)).2 < planarMacroScale) := by
  native_decide

/-- Local variable-coordinate families compatible with the macrocell named
by each direct atlas kind. -/
def RetainedDirectClauseKind.CompatibleVariableLocalPosition
    (kind : RetainedDirectClauseKind)
    (position : Cell) : Prop :=
  match kind with
  | .crossover _ =>
      IsCarrierPortLocalPosition position ∨
        ∃ internal : CrossoverInternal,
          position =
            CrossoverVariable.position
              (crossoverInternalVariable internal)
  | .duplicator _ _ =>
      IsCarrierPortLocalPosition position ∨
        position = duplicatorArmCenterPosition
  | .routedClause =>
      IsCarrierPortLocalPosition position

instance (kind : RetainedDirectClauseKind) (position : Cell) :
    Decidable (kind.CompatibleVariableLocalPosition position) := by
  cases kind <;>
    simp [RetainedDirectClauseKind.CompatibleVariableLocalPosition] <;>
    infer_instance

/-- Among the local variable coordinates compatible with a direct
component, its endpoint rectangle contains only the represented incidence's
variable endpoint. -/
theorem
    retainedDirectSourceLocalRouteAt_rectangle_contains_only_compatibleVariablePosition
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (position : Cell)
    (compatible :
      kind.CompatibleVariableLocalPosition position)
    (bounded :
      let route := retainedDirectSourceLocalRouteAt kind index
      InClosedGridRectangle
        (⟨route.headD (0, 0),
            route.getLastD (0, 0)⟩ :
          GridSegment).coordinateLower
        (⟨route.headD (0, 0),
            route.getLastD (0, 0)⟩ :
          GridSegment).coordinateUpper
        position) :
    position =
      (retainedDirectSourceLocalRouteAt
        kind index).getLastD (0, 0) := by
  cases kind with
  | crossover clauseIndex =>
      rcases compatible with carrierPort | internal
      · rcases carrierPort with
          left | right | top | bottom <;>
          subst position <;>
          native_decide +revert
      · rcases internal with ⟨internal, rfl⟩
        cases internal <;>
          native_decide +revert
  | duplicator arm clauseIndex =>
      rcases compatible with carrierPort | center
      · rcases carrierPort with
          left | right | top | bottom <;>
          subst position <;>
          native_decide +revert
      · subst position
        native_decide +revert
  | routedClause =>
      rcases compatible with
        left | right | top | bottom <;>
        subst position <;>
        native_decide +revert

/-- A point written in two half-open `20 × 20` macrocell coordinate systems
has the same macrocell center.  Membership in a translated endpoint
rectangle then descends to membership of the local coordinate. -/
theorem in_localCoordinateRectangle_of_macrocell_decompositions
    {sourceCenter targetCenter targetLocal : Cell}
    {segment : GridSegment}
    (startBounds :
      0 ≤ segment.start.1 ∧
        segment.start.1 < planarMacroScale ∧
        0 ≤ segment.start.2 ∧
        segment.start.2 < planarMacroScale)
    (finishBounds :
      0 ≤ segment.finish.1 ∧
        segment.finish.1 < planarMacroScale ∧
        0 ≤ segment.finish.2 ∧
        segment.finish.2 < planarMacroScale)
    (targetLocalBounds :
      0 ≤ targetLocal.1 ∧
        targetLocal.1 < planarMacroScale ∧
        0 ≤ targetLocal.2 ∧
        targetLocal.2 < planarMacroScale)
    (bounded :
      InClosedGridRectangle
        (Cell.add
          (Cell.scale planarMacroScale sourceCenter)
          segment.coordinateLower)
        (Cell.add
          (Cell.scale planarMacroScale sourceCenter)
          segment.coordinateUpper)
        (Cell.add
          (Cell.scale planarMacroScale targetCenter)
          targetLocal)) :
    sourceCenter = targetCenter ∧
      InClosedGridRectangle
        segment.coordinateLower
        segment.coordinateUpper
        targetLocal := by
  rcases sourceCenter with ⟨sourceX, sourceY⟩
  rcases targetCenter with ⟨targetX, targetY⟩
  rcases targetLocal with ⟨localX, localY⟩
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [
    InClosedGridRectangle,
    GridSegment.coordinateLower,
    GridSegment.coordinateUpper,
    Cell.add, Cell.scale] at startBounds finishBounds targetLocalBounds bounded ⊢
  norm_num [planarMacroScale] at startBounds finishBounds targetLocalBounds bounded ⊢
  omega

/-- Once a direct choice's origin and a retained variable position are
written in macrocell coordinates, endpoint-rectangle membership forces the
variable position to be the represented incidence endpoint. -/
theorem
    RetainedDirectSourceRouteChoice.sourceSegment_contains_only_retainedMacrocellPosition
    (choice : RetainedDirectSourceRouteChoice)
    (sourceCenter targetCenter targetLocal target : Cell)
    (originEq :
      choice.origin =
        Cell.scale planarMacroScale sourceCenter)
    (targetEq :
      target =
        Cell.add
          (Cell.scale planarMacroScale targetCenter)
          targetLocal)
    (targetLocalBounds :
      0 ≤ targetLocal.1 ∧
        targetLocal.1 < planarMacroScale ∧
        0 ≤ targetLocal.2 ∧
        targetLocal.2 < planarMacroScale)
    (compatible :
      sourceCenter = targetCenter →
        choice.kind.CompatibleVariableLocalPosition targetLocal)
    (bounded :
      InClosedGridRectangle
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        target) :
    target = choice.sourceSegment.finish := by
  let route :=
    retainedDirectSourceLocalRouteAt choice.kind choice.index
  let localSegment : GridSegment :=
    ⟨route.headD (0, 0), route.getLastD (0, 0)⟩
  have endpointBounds :=
    retainedDirectSourceLocalRouteAt_endpoints_in_macrocell
      choice.kind choice.index
  have translatedBounded :
      InClosedGridRectangle
        (Cell.add
          (Cell.scale planarMacroScale sourceCenter)
          localSegment.coordinateLower)
        (Cell.add
          (Cell.scale planarMacroScale sourceCenter)
          localSegment.coordinateUpper)
        (Cell.add
          (Cell.scale planarMacroScale targetCenter)
          targetLocal) := by
    have lowerEq :
        choice.sourceSegment.coordinateLower =
          Cell.add choice.origin localSegment.coordinateLower := by
      rcases choice with ⟨⟨originX, originY⟩, kind, index⟩
      rcases route.headD (0, 0) with ⟨headX, headY⟩
      rcases route.getLastD (0, 0) with ⟨lastX, lastY⟩
      simp [RetainedDirectSourceRouteChoice.sourceSegment,
        route, localSegment,
        GridSegment.coordinateLower, Cell.add,
        min_add_add_left]
    have upperEq :
        choice.sourceSegment.coordinateUpper =
          Cell.add choice.origin localSegment.coordinateUpper := by
      rcases choice with ⟨⟨originX, originY⟩, kind, index⟩
      rcases route.headD (0, 0) with ⟨headX, headY⟩
      rcases route.getLastD (0, 0) with ⟨lastX, lastY⟩
      simp [RetainedDirectSourceRouteChoice.sourceSegment,
        route, localSegment,
        GridSegment.coordinateUpper, Cell.add,
        max_add_add_left]
    rw [lowerEq, upperEq, originEq, targetEq] at bounded
    exact bounded
  have localData :=
    in_localCoordinateRectangle_of_macrocell_decompositions
      endpointBounds.1 endpointBounds.2 targetLocalBounds
      translatedBounded
  have localEq :=
    retainedDirectSourceLocalRouteAt_rectangle_contains_only_compatibleVariablePosition
      choice.kind choice.index targetLocal
      (compatible localData.1)
      (by simpa [route, localSegment] using localData.2)
  rw [targetEq, ← localData.1, localEq]
  change
    Cell.add
        (Cell.scale planarMacroScale sourceCenter)
        ((retainedDirectSourceLocalRouteAt
          choice.kind choice.index).getLastD (0, 0)) =
      Cell.add choice.origin
        ((retainedDirectSourceLocalRouteAt
          choice.kind choice.index).getLastD (0, 0))
  rw [originEq]

/-- Geometric kind and translated drawing-grid center represented by a
successful final direct choice. -/
inductive RetainedFinalDirectSourceCenterKind
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    RetainedDirectClauseKind → Cell → Prop
  | crossover
      (clauseIndex : Fin 26)
      (crossing : CrossingRecord)
      (shift : Cell)
      (crossingMember :
        crossing ∈ orientedCrossingHalo formula.incidenceGraph) :
      RetainedFinalDirectSourceCenterKind formula
        (.crossover clauseIndex)
        (Cell.add crossing.point
          ((drawing formula.incidenceGraph).periodTranslation shift))
  | duplicator
      (arm : DuplicatorArm)
      (clauseIndex : Fin 2)
      (site : VariableRouteSite Variable)
      (shift : Cell)
      (siteMember : site ∈ drawingVariableRouteSites formula) :
      RetainedFinalDirectSourceCenterKind formula
        (.duplicator arm clauseIndex)
        (Cell.add
          (liftedIncidenceVertexPosition formula
            (.variable site.1) site.2)
          ((drawing formula.incidenceGraph).periodTranslation shift))
  | routedClause
      (site : ClauseRouteSite)
      (shift : Cell)
      (siteMember : site ∈ drawingClauseRouteSites formula) :
      RetainedFinalDirectSourceCenterKind formula
        .routedClause
        (Cell.add
          (liftedIncidenceVertexPosition formula
            (.clause site.1) site.2)
          ((drawing formula.incidenceGraph).periodTranslation shift))

/-- A successful final direct choice starts at the lower-left origin of the
translated macrocell advertised by its atlas kind. -/
structure RetainedFinalDirectSourceOriginData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (choice : RetainedDirectSourceRouteChoice) where
  center : Cell
  originEq :
    choice.origin = Cell.scale planarMacroScale center
  centerKind :
    RetainedFinalDirectSourceCenterKind
      formula choice.kind center

/-- A metadata representative recovered by a successful final direct lookup
is one of the retained finite planar-SAT metadata entries. -/
theorem retainedFinalDirectSourceMetadata_retainedValid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (lookup :
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some metadata) :
    metadata.RetainedValid formula := by
  unfold retainedFinalDirectSourceMetadata? at lookup
  unfold retainedRepresentativeItem? at lookup
  unfold PositionedPeriodicCNF.representativeItem? at lookup
  split at lookup
  next => cases lookup
  next finalClause =>
    have metadataMember :
        metadata ∈ retainedDrawingPlanarSATClauseMetadata formula :=
      List.mem_iff_getElem?.mpr
        ⟨_, lookup⟩
    exact
      retainedDrawingPlanarSATClauseMetadata_valid
        formula metadataMember

/-- Inverting a successful final direct selector recovers its translated
crossover, routed-variable, or routed-clause macrocell center. -/
theorem retainedFinalDirectSourceRouteChoice_originData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    Nonempty
      (RetainedFinalDirectSourceOriginData
        formula choice) := by
  rcases retainedFinalDirectSourceRouteChoice_exists_raw
      formula clauseIndex literalIndex choice lookup with
    ⟨metadata, rawChoice, metadataLookup,
      rawLookup, choiceEq⟩
  have metadataValid :=
    retainedFinalDirectSourceMetadata_retainedValid
      formula clauseIndex metadata metadataLookup
  have sourceMember :=
    (metadata.retainedValid_iff_sourceMember_and_localClauseMember
      formula).mp metadataValid |>.1
  let shift : Cell :=
    Cell.sub (0, 0)
      (PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause
          formula metadata).literals)
  cases sourceEq : metadata.source with
  | crossover crossing localClauseIndex =>
      simp only [sourceEq,
        retainedDirectSourceRouteChoice?] at rawLookup
      split at rawLookup
      next localClauseIndexLt =>
        split at rawLookup
        next literalIndexLt =>
          simp only [Option.some.injEq] at rawLookup
          subst rawChoice
          subst choice
          let center :=
            Cell.add crossing.point
              ((drawing formula.incidenceGraph).periodTranslation
                shift)
          refine Nonempty.intro {
            center := center
            originEq := ?_
            centerKind := ?_
          }
          · change
              Cell.add
                  ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
                    formula).translation shift)
                  (crossingMacroOrigin crossing) =
                Cell.scale planarMacroScale center
            rw [
              retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro]
            rcases crossing.point with ⟨crossingX, crossingY⟩
            rcases shift with ⟨shiftX, shiftY⟩
            simp [center, crossingMacroOrigin,
              carrierMacroPeriodTranslation,
              PeriodicGridDrawing.periodTranslation,
              planarMacroScale, Cell.add, Cell.scale]
            constructor <;> ring
          · exact
              RetainedFinalDirectSourceCenterKind.crossover
                (formula := formula)
                (crossing := crossing) (shift := shift)
                (clauseIndex :=
                  ⟨localClauseIndex, localClauseIndexLt⟩)
                (by
                  simpa [sourceEq,
                    DrawingPlanarSATClauseSource.RetainedComponentMember]
                    using sourceMember)
        next => cases rawLookup
      next => cases rawLookup
  | carrier link localClauseIndex =>
      simp [sourceEq,
        retainedDirectSourceRouteChoice?] at rawLookup
  | bend routeBend localClauseIndex =>
      simp [sourceEq,
        retainedDirectSourceRouteChoice?] at rawLookup
  | routedClause site =>
      simp only [sourceEq,
        retainedDirectSourceRouteChoice?] at rawLookup
      split at rawLookup
      next literalIndexLt =>
        simp only [Option.some.injEq] at rawLookup
        subst rawChoice
        subst choice
        let center :=
          Cell.add
            (liftedIncidenceVertexPosition formula
              (.clause site.1) site.2)
            ((drawing formula.incidenceGraph).periodTranslation
              shift)
        refine Nonempty.intro {
          center := center
          originEq := ?_
          centerKind := ?_
        }
        · change
            Cell.add
                ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
                  formula).translation shift)
                (routedClauseOrigin formula site) =
              Cell.scale planarMacroScale center
          rw [
            retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro]
          rcases
              liftedIncidenceVertexPosition formula
                (.clause site.1) site.2 with
            ⟨siteX, siteY⟩
          rcases shift with ⟨shiftX, shiftY⟩
          simp [center, routedClauseOrigin,
            liftedIncidenceVertexMacroOrigin,
            carrierMacroPeriodTranslation,
            PeriodicGridDrawing.periodTranslation,
            planarMacroScale, Cell.add, Cell.scale]
          constructor <;> ring
        · exact
            RetainedFinalDirectSourceCenterKind.routedClause
              (formula := formula)
              (site := site) (shift := shift)
              (by
                simpa [sourceEq,
                  DrawingPlanarSATClauseSource.RetainedComponentMember]
                  using sourceMember)
      next => cases rawLookup
  | routedVariable
      site armIndex arm link localClauseIndex =>
      simp only [sourceEq,
        retainedDirectSourceRouteChoice?] at rawLookup
      split at rawLookup
      next localClauseIndexLt =>
        split at rawLookup
        next literalIndexLt =>
          simp only [Option.some.injEq] at rawLookup
          subst rawChoice
          subst choice
          let center :=
            Cell.add
              (liftedIncidenceVertexPosition formula
                (CNFVertex.variable site.1) site.2)
              ((drawing formula.incidenceGraph).periodTranslation
                shift)
          refine Nonempty.intro {
            center := center
            originEq := ?_
            centerKind := ?_
          }
          · change
              Cell.add
                  ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
                    formula).translation shift)
                  (routedVariableOrigin formula site) =
                Cell.scale planarMacroScale center
            rw [
              retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro]
            rcases
                liftedIncidenceVertexPosition formula
                  (CNFVertex.variable site.1) site.2 with
              ⟨siteX, siteY⟩
            rcases shift with ⟨shiftX, shiftY⟩
            simp [center, routedVariableOrigin,
              liftedIncidenceVertexMacroOrigin,
              carrierMacroPeriodTranslation,
              PeriodicGridDrawing.periodTranslation,
              planarMacroScale, Cell.add, Cell.scale]
            constructor <;> ring
          · exact
              RetainedFinalDirectSourceCenterKind.duplicator
                (formula := formula)
                (site := site) (shift := shift)
                (arm := arm)
                (clauseIndex :=
                  ⟨localClauseIndex, localClauseIndexLt⟩)
                (by
                  have routedSourceMember := sourceMember
                  rw [sourceEq] at routedSourceMember
                  exact routedSourceMember.1)
        next => cases rawLookup
      next => cases rawLookup

/-- The three retained local-variable families, together with the
drawing-grid center of the macrocell containing them. -/
inductive RetainedFinalVariableCenterKind
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    Cell → Cell → Prop
  | carrier
      (node : CarrierNode)
      (nodeMember :
        node ∈ retainedDrawingCarrierNodes formula.incidenceGraph) :
      RetainedFinalVariableCenterKind formula
        (node.drawingPoint formula.incidenceGraph)
        node.localPosition
  | atom
      (site : VariableRouteSite Variable)
      (siteMember : site ∈ drawingVariableRouteSites formula) :
      RetainedFinalVariableCenterKind formula
        (liftedIncidenceVertexPosition formula
          (.variable site.1) site.2)
        duplicatorArmCenterPosition
  | crossoverInternal
      (crossing : CrossingRecord)
      (internal : CrossoverInternal)
      (crossingMember :
        crossing ∈ orientedCrossingHalo formula.incidenceGraph) :
      RetainedFinalVariableCenterKind formula
        crossing.point
        (CrossoverVariable.position
          (crossoverInternalVariable internal))

/-- Macrocell decomposition of one valid final wrapped variable position. -/
structure RetainedFinalVariablePositionData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable) where
  center : Cell
  localPosition : Cell
  positionEq :
    (finalCoordinatedPlacement formula).position atom =
      Cell.add
        (Cell.scale planarMacroScale center)
        localPosition
  localBounds :
    0 ≤ localPosition.1 ∧ localPosition.1 < planarMacroScale ∧
      0 ≤ localPosition.2 ∧
        localPosition.2 < planarMacroScale
  centerKind :
    RetainedFinalVariableCenterKind
      formula center localPosition

/-- The finite gauge lift gives every geometrically valid final variable its
retained local-coordinate and macrocell-center decomposition. -/
theorem retainedFinalVariablePositionData_of_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (valid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula atom.original) :
    Nonempty
      (RetainedFinalVariablePositionData formula atom) := by
  rcases atom with ⟨original⟩
  let lifted :=
    periodicPlanarSATVariableGaugeLift formula original
  have liftedValid :
      RetainedDrawingPlanarSATVariableValid formula lifted :=
    periodicPlanarSATVariableGaugeLift_valid
      formula wellFormed degree isLocal original valid
  have liftedPosition :=
    drawingPlanarSATVariablePosition_gaugeLift
      formula wellFormed original valid
  have finalLiftedPosition :
      (finalCoordinatedPlacement formula).position
          ({ original := original } :
            WrappedPeriodicPlanarSATVariable Variable) =
        drawingPlanarSATVariablePosition formula lifted := by
    simpa [lifted, finalCoordinatedPlacement] using
      liftedPosition.symm
  cases liftedEq : lifted with
  | inl node =>
      cases node with
      | carrier node =>
          have nodeMember :
              node ∈
                retainedDrawingCarrierNodes formula.incidenceGraph := by
            simpa [lifted, liftedEq,
              RetainedDrawingPlanarSATVariableValid] using
              liftedValid
          refine Nonempty.intro {
            center := node.drawingPoint formula.incidenceGraph
            localPosition := node.localPosition
            positionEq := ?_
            localBounds := node.localPosition_in_macrocell
            centerKind :=
              RetainedFinalVariableCenterKind.carrier
                (formula := formula) node nodeMember
          }
          rw [finalLiftedPosition, liftedEq]
          simpa [lifted, liftedEq,
            drawingPlanarSATVariablePosition] using
              (CarrierNode.position_eq_scale_add_local
                formula.incidenceGraph node)
      | atom site =>
          have siteMember :
              site ∈ drawingVariableRouteSites formula := by
            simpa [lifted, liftedEq,
              RetainedDrawingPlanarSATVariableValid] using
              liftedValid
          refine Nonempty.intro {
            center :=
              liftedIncidenceVertexPosition formula
                (.variable site.1) site.2
            localPosition := duplicatorArmCenterPosition
            positionEq := ?_
            localBounds := duplicatorArmCenterPosition_in_macrocell
            centerKind :=
              RetainedFinalVariableCenterKind.atom
                (formula := formula) site siteMember
          }
          rw [finalLiftedPosition, liftedEq]
          simp [drawingPlanarSATVariablePosition,
            liftedIncidenceVertexMacroOrigin]
  | inr internal =>
      rcases internal with ⟨crossing, internal⟩
      have crossingMember :
          crossing ∈
            orientedCrossingHalo formula.incidenceGraph := by
        simpa [lifted, liftedEq,
          RetainedDrawingPlanarSATVariableValid] using
          liftedValid
      refine Nonempty.intro {
        center := crossing.point
        localPosition :=
          CrossoverVariable.position
            (crossoverInternalVariable internal)
        positionEq := ?_
        localBounds :=
          CrossoverVariable.position_in_macrocell
            (crossoverInternalVariable internal)
        centerKind :=
          RetainedFinalVariableCenterKind.crossoverInternal
            (formula := formula)
            crossing internal crossingMember
      }
      rw [finalLiftedPosition, liftedEq]
      simp [drawingPlanarSATVariablePosition,
        crossingMacroOrigin]

/-- Equal macrocell centers make a valid retained variable's local
coordinate compatible with the direct component occupying that macrocell.
The excluded cases are exactly crossover centers versus declared graph
vertices, or clause vertices versus variable vertices. -/
theorem compatibleVariableLocalPosition_of_centerKinds
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {kind : RetainedDirectClauseKind}
    {sourceCenter targetCenter localPosition : Cell}
    (sourceKind :
      RetainedFinalDirectSourceCenterKind
        formula kind sourceCenter)
    (targetKind :
      RetainedFinalVariableCenterKind
        formula targetCenter localPosition)
    (centersEqual : sourceCenter = targetCenter) :
    kind.CompatibleVariableLocalPosition localPosition := by
  cases sourceKind with
  | crossover
      clauseIndex crossing shift crossingMember =>
      cases targetKind with
      | carrier node nodeMember =>
          exact Or.inl
            (retainedCarrierNode_localPosition_isCarrierPort
              wellFormed degree isLocal nodeMember)
      | atom site siteMember =>
          exfalso
          have backEq :
              crossing.point =
                liftedIncidenceVertexPosition formula
                  (.variable site.1)
                  (Cell.add site.2
                    (Cell.sub (0, 0) shift)) := by
            have cancelled :=
              point_eq_add_periodTranslation_neg_of_add_periodTranslation_eq
                formula.incidenceGraph
                crossing.point
                (liftedIncidenceVertexPosition formula
                  (.variable site.1) site.2)
                shift
                (by simpa using centersEqual)
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact cancelled
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree crossingMember
              (drawingVariableRouteSite_vertex_mem
                formula siteMember)
              (Cell.add site.2
                (Cell.sub (0, 0) shift)))
              (by
                simpa [liftedIncidenceVertexPosition] using
                  backEq)
      | crossoverInternal
          targetCrossing internal targetCrossingMember =>
          exact Or.inr ⟨internal, rfl⟩
  | duplicator
      arm clauseIndex site shift siteMember =>
      cases targetKind with
      | carrier node nodeMember =>
          exact Or.inl
            (retainedCarrierNode_localPosition_isCarrierPort
              wellFormed degree isLocal nodeMember)
      | atom targetSite targetSiteMember =>
          exact Or.inr rfl
      | crossoverInternal
          crossing internal crossingMember =>
          exfalso
          have pointEq :
              crossing.point =
                liftedIncidenceVertexPosition formula
                  (.variable site.1)
                  (Cell.add site.2 shift) := by
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact centersEqual.symm
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree crossingMember
              (drawingVariableRouteSite_vertex_mem
                formula siteMember)
              (Cell.add site.2 shift))
              (by
                simpa [liftedIncidenceVertexPosition] using
                  pointEq)
  | routedClause site shift siteMember =>
      cases targetKind with
      | carrier node nodeMember =>
          exact
            retainedCarrierNode_localPosition_isCarrierPort
              wellFormed degree isLocal nodeMember
      | atom targetSite targetSiteMember =>
          exfalso
          have positionEq :
              liftedIncidenceVertexPosition formula
                  (.clause site.1)
                  (Cell.add site.2 shift) =
                liftedIncidenceVertexPosition formula
                  (.variable targetSite.1)
                  targetSite.2 := by
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact centersEqual
          have vertexData :=
            liftedDrawingVertexPosition_eq
              formula.incidenceGraph
              (drawingClauseRouteSite_vertex_mem
                formula siteMember)
              (drawingVariableRouteSite_vertex_mem
                formula targetSiteMember)
              (by
                simpa [liftedIncidenceVertexPosition] using
                  positionEq)
          cases vertexData.1
      | crossoverInternal
          crossing internal crossingMember =>
          exfalso
          have pointEq :
              crossing.point =
                liftedIncidenceVertexPosition formula
                  (.clause site.1)
                  (Cell.add site.2 shift) := by
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact centersEqual.symm
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree crossingMember
              (drawingClauseRouteSite_vertex_mem
                formula siteMember)
              (Cell.add site.2 shift))
              (by
                simpa [liftedIncidenceVertexPosition] using
                  pointEq)

/-- Cancel the translation on the first of two equal translated drawing
centers.  This is the two-shift form needed when a literal occurrence moves
an already decomposed retained variable to another periodic copy. -/
theorem point_eq_add_periodTranslation_sub_of_two_adds_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (first second firstShift secondShift : Cell)
    (equal :
      Cell.add first ((drawing graph).periodTranslation firstShift) =
        Cell.add second ((drawing graph).periodTranslation secondShift)) :
    first =
      Cell.add second
        ((drawing graph).periodTranslation
          (Cell.sub secondShift firstShift)) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases firstShift with ⟨firstShiftX, firstShiftY⟩
  rcases secondShift with ⟨secondShiftX, secondShiftY⟩
  simp only [PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.sub, Cell.scale, Prod.mk.injEq] at equal ⊢
  constructor
  · linear_combination equal.1
  · linear_combination equal.2

/-- A periodic copy of a valid retained variable has a local coordinate
compatible with any successful direct component occupying the same copied
macrocell. -/
theorem compatibleVariableLocalPosition_of_centerKinds_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {kind : RetainedDirectClauseKind}
    {sourceCenter targetCenter localPosition targetShift : Cell}
    (sourceKind :
      RetainedFinalDirectSourceCenterKind
        formula kind sourceCenter)
    (targetKind :
      RetainedFinalVariableCenterKind
        formula targetCenter localPosition)
    (centersEqual :
      sourceCenter =
        Cell.add targetCenter
          ((drawing formula.incidenceGraph).periodTranslation
            targetShift)) :
    kind.CompatibleVariableLocalPosition localPosition := by
  cases sourceKind with
  | crossover
      clauseIndex crossing sourceShift crossingMember =>
      cases targetKind with
      | carrier node nodeMember =>
          exact Or.inl
            (retainedCarrierNode_localPosition_isCarrierPort
              wellFormed degree isLocal nodeMember)
      | atom site siteMember =>
          exfalso
          have pointEq :
              crossing.point =
                liftedIncidenceVertexPosition formula
                  (.variable site.1)
                  (Cell.add site.2
                    (Cell.sub targetShift sourceShift)) := by
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact
              point_eq_add_periodTranslation_sub_of_two_adds_eq
                formula.incidenceGraph crossing.point
                (liftedIncidenceVertexPosition formula
                  (.variable site.1) site.2)
                sourceShift targetShift centersEqual
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree crossingMember
              (drawingVariableRouteSite_vertex_mem
                formula siteMember)
              (Cell.add site.2
                (Cell.sub targetShift sourceShift)))
              (by
                simpa [liftedIncidenceVertexPosition] using pointEq)
      | crossoverInternal
          targetCrossing internal targetCrossingMember =>
          exact Or.inr ⟨internal, rfl⟩
  | duplicator
      arm clauseIndex site sourceShift siteMember =>
      cases targetKind with
      | carrier node nodeMember =>
          exact Or.inl
            (retainedCarrierNode_localPosition_isCarrierPort
              wellFormed degree isLocal nodeMember)
      | atom targetSite targetSiteMember =>
          exact Or.inr rfl
      | crossoverInternal
          crossing internal crossingMember =>
          exfalso
          have pointEq :
              crossing.point =
                liftedIncidenceVertexPosition formula
                  (.variable site.1)
                  (Cell.add site.2
                    (Cell.sub sourceShift targetShift)) := by
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact
              point_eq_add_periodTranslation_sub_of_two_adds_eq
                formula.incidenceGraph crossing.point
                (liftedIncidenceVertexPosition formula
                  (.variable site.1) site.2)
                targetShift sourceShift centersEqual.symm
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree crossingMember
              (drawingVariableRouteSite_vertex_mem
                formula siteMember)
              (Cell.add site.2
                (Cell.sub sourceShift targetShift)))
              (by
                simpa [liftedIncidenceVertexPosition] using pointEq)
  | routedClause site sourceShift siteMember =>
      cases targetKind with
      | carrier node nodeMember =>
          exact
            retainedCarrierNode_localPosition_isCarrierPort
              wellFormed degree isLocal nodeMember
      | atom targetSite targetSiteMember =>
          exfalso
          have positionEq :
              liftedIncidenceVertexPosition formula
                  (.clause site.1)
                  (Cell.add site.2 sourceShift) =
                liftedIncidenceVertexPosition formula
                  (.variable targetSite.1)
                  (Cell.add targetSite.2 targetShift) := by
            rw [liftedIncidenceVertexPosition_periodTranslate,
              liftedIncidenceVertexPosition_periodTranslate]
            exact centersEqual
          have vertexData :=
            liftedDrawingVertexPosition_eq
              formula.incidenceGraph
              (drawingClauseRouteSite_vertex_mem
                formula siteMember)
              (drawingVariableRouteSite_vertex_mem
                formula targetSiteMember)
              (by
                simpa [liftedIncidenceVertexPosition] using positionEq)
          cases vertexData.1
      | crossoverInternal
          crossing internal crossingMember =>
          exfalso
          have pointEq :
              crossing.point =
                liftedIncidenceVertexPosition formula
                  (.clause site.1)
                  (Cell.add site.2
                    (Cell.sub sourceShift targetShift)) := by
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact
              point_eq_add_periodTranslation_sub_of_two_adds_eq
                formula.incidenceGraph crossing.point
                (liftedIncidenceVertexPosition formula
                  (.clause site.1) site.2)
                targetShift sourceShift centersEqual.symm
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree crossingMember
              (drawingClauseRouteSite_vertex_mem
                formula siteMember)
              (Cell.add site.2
                (Cell.sub sourceShift targetShift)))
              (by
                simpa [liftedIncidenceVertexPosition] using pointEq)

/-- No geometrically valid final source variable other than the represented
endpoint can lie inside a successful direct choice's source-segment
rectangle. -/
theorem
    retainedFinalDirectSourceRouteChoice_sourceSegment_contains_only_variablePosition_of_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (choice : RetainedDirectSourceRouteChoice)
    (clauseIndex literalIndex : Nat)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    (targetAtom :
      WrappedPeriodicPlanarSATVariable Variable)
    (targetValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula targetAtom.original)
    (bounded :
      InClosedGridRectangle
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        ((finalCoordinatedPlacement formula).position
          targetAtom)) :
    (finalCoordinatedPlacement formula).position targetAtom =
      choice.sourceSegment.finish := by
  rcases retainedFinalDirectSourceRouteChoice_originData
      formula clauseIndex literalIndex choice choiceLookup with
    ⟨sourceData⟩
  rcases retainedFinalVariablePositionData_of_valid
      formula wellFormed degree isLocal
      targetAtom targetValid with
    ⟨targetData⟩
  exact
    choice.sourceSegment_contains_only_retainedMacrocellPosition
      sourceData.center targetData.center
      targetData.localPosition
      ((finalCoordinatedPlacement formula).position targetAtom)
      sourceData.originEq targetData.positionEq
      targetData.localBounds
      (fun centersEqual =>
        compatibleVariableLocalPosition_of_centerKinds
          formula wellFormed degree isLocal
          sourceData.centerKind targetData.centerKind
          centersEqual)
      bounded

/-- The represented variable endpoint of a successful direct choice is the
canonical center of the selected final source occurrence. -/
theorem retainedFinalDirectSourceRouteChoice_sourceSegment_finish
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    choice.sourceSegment.finish =
      PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula)
        clause literal := by
  have representedLast :=
    retainedFinalDirectSourceRouteChoice_route_getLastD
      formula clauseIndex literalIndex choice choiceLookup
  have finalEndpoint :=
    (finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember).2
  have retainedEndpoint :
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula clauseIndex literalIndex).getLast? =
      some
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal) := by
    simpa only [finalCoordinatedSourceRoutes] using
      finalEndpoint
  calc
    choice.sourceSegment.finish =
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula clauseIndex literalIndex).getLastD (0, 0) := by
      simpa [RetainedDirectSourceRouteChoice.sourceSegment] using
        representedLast.symm
    _ =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal := by
      rw [List.getLastD_eq_getLast?, retainedEndpoint]
      rfl

/-- The common coordinate calculation transporting any local atlas point
bound through a choice's physical component translation. -/
private theorem
    RetainedDirectSourceRouteChoice.translatedPoint_in_sourceSegmentRectangle
    (choice : RetainedDirectSourceRouteChoice)
    (localPoint : Cell)
    (localBound :
      let localSegment : GridSegment :=
        ⟨(retainedDirectSourceLocalRouteAt
            choice.kind choice.index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt
            choice.kind choice.index).getLastD (0, 0)⟩
      InClosedGridRectangle
        (coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            localSegment.coordinateLower))
        (coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            localSegment.coordinateUpper))
        localPoint) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateUpper))
      (Cell.add
        (retainedDirectSourceFanPositioningOffset choice.origin)
        localPoint) := by
  let localSegment : GridSegment :=
    ⟨(retainedDirectSourceLocalRouteAt
        choice.kind choice.index).headD (0, 0),
      (retainedDirectSourceLocalRouteAt
        choice.kind choice.index).getLastD (0, 0)⟩
  let positioningOffset :=
    retainedDirectSourceFanPositioningOffset choice.origin
  have lowerEq :
      Cell.add positioningOffset
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateLower)) =
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateLower) := by
    rcases choice.origin with ⟨originX, originY⟩
    rcases localSegment.start with ⟨startX, startY⟩
    rcases localSegment.finish with ⟨finishX, finishY⟩
    simp [localSegment, positioningOffset,
      RetainedDirectSourceRouteChoice.sourceSegment,
      retainedDirectSourceFanPositioningOffset,
      GridSegment.coordinateLower, coordinateRadiusLower,
      Cell.add, Cell.scale,
      min_add_add_left]
    constructor <;> ring
  have upperEq :
      Cell.add positioningOffset
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateUpper)) =
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateUpper) := by
    rcases choice.origin with ⟨originX, originY⟩
    rcases localSegment.start with ⟨startX, startY⟩
    rcases localSegment.finish with ⟨finishX, finishY⟩
    simp [localSegment, positioningOffset,
      RetainedDirectSourceRouteChoice.sourceSegment,
      retainedDirectSourceFanPositioningOffset,
      GridSegment.coordinateUpper, coordinateRadiusUpper,
      Cell.add, Cell.scale,
      max_add_add_left]
    constructor <;> ring
  rw [← lowerEq, ← upperEq]
  simpa [localSegment, positioningOffset] using
    PeriodicOrthocrossing.InClosedGridRectangle.add localBound
      positioningOffset

/-- Positioning a direct atlas choice transports its finite radius-288
bound to the fully refined represented source segment. -/
theorem RetainedDirectSourceRouteChoice.completeRoute_point_in_sourceSegmentRectangle
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember : point ∈ choice.completeRoute slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateUpper))
      point := by
  unfold RetainedDirectSourceRouteChoice.completeRoute
    retainedDirectSourcePositionedFanCompleteRouteAt
    translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localBound :=
    retainedDirectSourceFanCompleteRouteAt_point_in_scaledLocalSegmentRectangle
      choice.kind choice.index slot localPoint localPointMember
  exact choice.translatedPoint_in_sourceSegmentRectangle
    localPoint localBound

/-- The local Figure 7 spoke appended to a direct route stays inside the
same conservative source-segment rectangle. -/
theorem
    retainedDirectSourceFigure7SpokeAt_point_in_scaledLocalSegmentRectangle :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈ retainedDirectSourceFigure7SpokeAt kind index slot →
        let localSegment : GridSegment :=
          ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
            (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateLower))
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateUpper))
          point := by
  native_decide

/-- The positioned direct Figure 7 spoke inherits the same source-segment
rectangle. -/
theorem RetainedDirectSourceRouteChoice.figure7Spoke_point_in_sourceSegmentRectangle
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember : point ∈ choice.figure7Spoke slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateUpper))
      point := by
  unfold RetainedDirectSourceRouteChoice.figure7Spoke
    translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  exact choice.translatedPoint_in_sourceSegmentRectangle
    localPoint
    (retainedDirectSourceFigure7SpokeAt_point_in_scaledLocalSegmentRectangle
      choice.kind choice.index slot localPoint localPointMember)

/-- The direct source prefix joined to its matching Figure 7 spoke stays
inside the same source-segment rectangle. -/
theorem
    RetainedDirectSourceRouteChoice.completeFigure7Route_point_in_sourceSegmentRectangle
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember : point ∈ choice.completeFigure7Route slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateUpper))
      point := by
  rcases mem_joinAtEndpoint pointMember with
    prefixMember | spokeMember
  · exact choice.completeRoute_point_in_sourceSegmentRectangle
      slot prefixMember
  · exact choice.figure7Spoke_point_in_sourceSegmentRectangle
      slot spokeMember

/-- A lattice point outside a segment's endpoint rectangle is separated
from that rectangle.  Unlike `coordinateRectangle_separated_point`, this
fact does not require the segment itself to be axis-aligned. -/
theorem GridSegment.coordinateRectangle_separated_point_of_not_in
    {segment : GridSegment}
    {point : Cell}
    (outside :
      ¬InClosedGridRectangle
        segment.coordinateLower
        segment.coordinateUpper
        point) :
    ClosedGridRectanglesSeparated
      segment.coordinateLower
      segment.coordinateUpper
      point point := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [GridSegment.coordinateLower,
    GridSegment.coordinateUpper,
    InClosedGridRectangle,
    ClosedGridRectanglesSeparated] at outside ⊢
  omega

/-- After the final common refinement, a direct source route's radius-288
rectangle is separated from the radius-48 neighborhood of every source
point outside its original endpoint rectangle. -/
theorem
    RetainedDirectSourceRouteChoice.scaledSourceRectangle_separated_pointCycleRectangle
    (choice : RetainedDirectSourceRouteChoice)
    {point : Cell}
    (outside :
      ¬InClosedGridRectangle
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        point) :
    ClosedGridRectanglesSeparated
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateUpper))
      (coordinateRadiusLower 48
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          point))
      (coordinateRadiusUpper 48
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          point)) := by
  have separated :=
    ClosedGridRectanglesSeparated.scale_both_coordinateRadius
      (GridSegment.coordinateRectangle_separated_point_of_not_in
        (segment := choice.sourceSegment) outside)
      (factor := retainedTerminalFanTotalRefinement * 4)
      (radius := 288)
      (by native_decide)
      (by native_decide)
  norm_num [retainedTerminalFanTotalRefinement,
    PeriodicEightOccurrenceSplitPositioned.refinementScale,
    retainedTerminalFanRoutingRefinement] at separated ⊢
  simp only [ClosedGridRectanglesSeparated,
    coordinateRadiusLower, coordinateRadiusUpper,
    Cell.scale] at separated ⊢
  rcases separated with
      forwardX | backwardX | forwardY | backwardY
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- If the represented direct source-segment rectangle is separated from a
cycle metadata center, the complete direct occurrence is strictly separated
from that flattened cycle route. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_allCycleRoute_of_rectanglesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (cycleLiteralIndex : Nat)
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        (coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateLower))
        (coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateUpper))
        (coordinateRadiusLower 48
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).position
              metadata.atom)))
        (coordinateRadiusUpper 48
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).position
              metadata.atom)))) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex)) := by
  have routeEqual :=
    retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
  rw [routeEqual]
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateLower))
      (firstUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateUpper))
      (secondLower :=
        coordinateRadiusLower 48
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).position
              metadata.atom)))
      (secondUpper :=
        coordinateRadiusUpper 48
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).position
              metadata.atom)))
  · intro point pointMember
    exact
      choice.completeFigure7Route_point_in_sourceSegmentRectangle
        (retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex)
        pointMember
  · intro point pointMember
    exact
      retainedFinalSourceScaledAllCycleRoute_point_in_metadataCenterRectangle
        formula metadataLookup cycleLiteralIndex pointMember
  · exact rectanglesSeparated

/-- A successful direct occurrence strictly avoids every flattened cycle
whose source center lies outside the endpoint rectangle of the represented
direct source segment. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_allCycleRoute_of_center_outside
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (cycleLiteralIndex : Nat)
    (centerOutside :
      ¬InClosedGridRectangle
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        ((finalCoordinatedPlacement formula).position
          metadata.atom)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex)) := by
  apply
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_allCycleRoute_of_rectanglesSeparated
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
      metadataLookup cycleLiteralIndex
  simpa [retainedAngularFanSourceClearanceFactor_eq] using
    choice.scaledSourceRectangle_separated_pointCycleRectangle
      centerOutside

/-- A genuine cycle center different from the represented direct
occurrence cannot lie in the endpoint rectangle of its source segment. -/
theorem
    retainedFinalDirectSourceRouteChoice_cycleCenter_outside_of_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal ≠
        (finalCoordinatedPlacement formula).position
          metadata.atom) :
    ¬InClosedGridRectangle
      choice.sourceSegment.coordinateLower
      choice.sourceSegment.coordinateUpper
      ((finalCoordinatedPlacement formula).position
        metadata.atom) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  have targetAtomMemberScaled :
      metadata.atom ∈ sourceVariables source.erase := by
    exact
      allCycleClauseMetadata_lookup_atom_mem
        source placement metadataLookup
  have targetAtomMember :
      metadata.atom ∈
        sourceVariables
          (finalCoordinatedSource formula).erase := by
    simpa only [source,
      PositionedPeriodicCNF.erase_scale] using
      targetAtomMemberScaled
  rcases
      exists_positioned_members_of_mem_sourceVariables
        (finalCoordinatedSource formula) targetAtomMember with
    ⟨targetClause, targetClauseIndex,
      targetLiteral, targetLiteralIndex,
      targetClauseMember, targetLiteralMember,
      targetAtomEqual⟩
  have targetOccurrence :
      metadata.atom ∈
        (finalCoordinatedSource formula).erase.variableOccurrences := by
    have occurrence :=
      positionedLiteral_atom_mem_variableOccurrences_of_members
        (finalCoordinatedSource formula)
        targetClauseMember targetLiteralMember
    rw [targetAtomEqual] at occurrence
    exact occurrence
  have targetValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula metadata.atom.original := by
    apply
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
        formula
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
    simpa only [finalCoordinatedSource] using targetOccurrence
  intro centerInside
  have targetEqualsFinish :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_contains_only_variablePosition_of_valid
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      choice clauseIndex literalIndex choiceLookup
      metadata.atom targetValid centerInside
  have finishEqualsCanonical :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_finish
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
  apply centersDifferent
  exact (targetEqualsFinish.trans finishEqualsCanonical).symm

/-- A successful direct occurrence avoids a flattened cycle route at the
same canonical source center. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_allCycleRoute_of_center_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx)
    (centersEqual :
      ∀ metadata,
        (allCycleClauseMetadata
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
            some metadata →
        PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause literal =
          (finalCoordinatedPlacement formula).position
            metadata.atom) :
    RoutesAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex)) := by
  rcases allCycleClauseMetadata_lookup_valid
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      cycleClauseMember with
    ⟨metadata, metadataLookup, metadataClauseEqual,
      localClauseMember⟩
  have routeEqual :=
    retainedFinalScaledAllCycleRoute_eq_matchingCycleLift_of_center_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      metadataLookup cycleLiteralIndex
      (centersEqual metadata metadataLookup)
  have localClauseIndexLt :
      metadata.localClauseIndex <
        presentedCycleVertices.length :=
    positionedCycleClause_localIndex_lt
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      metadata.atom localClauseMember
  have localLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [metadataClauseEqual] using cycleLiteralMember
  have cycleLiteralIndexLt :
      cycleLiteralIndex < 2 :=
    positionedCycleClause_literalIndex_lt_two
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      metadata.atom localClauseMember localLiteralMember
  have avoids :=
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_matchingCycleLift
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
      metadata.localClauseIndex cycleLiteralIndex
      localClauseIndexLt cycleLiteralIndexLt
  dsimp only at avoids
  rw [routeEqual]
  exact avoids

/-- A successful direct occurrence strictly avoids a flattened cycle route
whose genuine source center is different from its canonical source center. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_allCycleRoute_of_center_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (cycleLiteralIndex : Nat)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal ≠
        (finalCoordinatedPlacement formula).position
          metadata.atom) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex)) := by
  exact
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_allCycleRoute_of_center_outside
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
      metadataLookup cycleLiteralIndex
      (retainedFinalDirectSourceRouteChoice_cycleCenter_outside_of_ne
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        clauseMember literalMember choiceLookup
        metadataLookup centersDifferent)

/-- The public coordinated route selected by a successful direct choice
inherits the same-center cycle certificate. -/
theorem
    retainedFinalCoordinatedDirectSourceRoute_avoids_allCycleRoute_of_center_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx)
    (centersEqual :
      ∀ metadata,
        (allCycleClauseMetadata
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
            some metadata →
        PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause literal =
          (finalCoordinatedPlacement formula).position
            metadata.atom) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex)) := by
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor,
          clauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp scaledClauseMember
  have literalLookup :
      (clause.scale
        retainedAngularFanSourceClearanceFactor).literals[
          literalIndex]? =
        some literal := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp literalMember
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
      formula clauseIndex literalIndex choice
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal choiceLookup clauseLookup literalLookup]
  exact
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_allCycleRoute_of_center_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
      cycleClauseMember cycleLiteralMember centersEqual

/-- The public coordinated route selected by a successful direct choice
strictly avoids every cycle whose metadata center is outside its represented
source-segment rectangle. -/
theorem
    retainedFinalCoordinatedDirectSourceRoute_strictlyAvoids_allCycleRoute_of_center_outside
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (_cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx)
    (centerOutside :
      ∀ metadata,
        (allCycleClauseMetadata
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
            some metadata →
        ¬InClosedGridRectangle
          choice.sourceSegment.coordinateLower
          choice.sourceSegment.coordinateUpper
          ((finalCoordinatedPlacement formula).position
            metadata.atom)) :
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex)) := by
  rcases allCycleClauseMetadata_lookup_valid
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      cycleClauseMember with
    ⟨metadata, metadataLookup, _metadataClauseEqual,
      _localClauseMember⟩
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor,
          clauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp scaledClauseMember
  have literalLookup :
      (clause.scale
        retainedAngularFanSourceClearanceFactor).literals[
          literalIndex]? =
        some literal := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp literalMember
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
      formula clauseIndex literalIndex choice
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal choiceLookup clauseLookup literalLookup]
  exact
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_allCycleRoute_of_center_outside
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
      metadataLookup cycleLiteralIndex
      (centerOutside metadata metadataLookup)

/-- Every public coordinated route selected by a successful direct choice
avoids every genuine flattened cycle route.  Equal centers use the local
same-center atlas certificate; unequal centers use the global rectangle
separation proved above. -/
theorem
    retainedFinalCoordinatedDirectSourceRoute_avoids_allCycleRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex)) := by
  rcases allCycleClauseMetadata_lookup_valid
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      cycleClauseMember with
    ⟨metadata, metadataLookup, _metadataClauseEqual,
      _localClauseMember⟩
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor,
          clauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp scaledClauseMember
  have literalLookup :
      (clause.scale
        retainedAngularFanSourceClearanceFactor).literals[
          literalIndex]? =
        some literal := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp literalMember
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
      formula clauseIndex literalIndex choice
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal choiceLookup clauseLookup literalLookup]
  by_cases centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal =
        (finalCoordinatedPlacement formula).position
          metadata.atom
  · exact
      retainedFinalCoordinatedDirectOccurrenceRoute_avoids_allCycleRoute_of_center_eq
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        clauseMember literalMember choiceLookup
        cycleClauseMember cycleLiteralMember
        (fun otherMetadata otherLookup => by
          have metadataEqual : otherMetadata = metadata := by
            exact Option.some.inj (otherLookup.symm.trans metadataLookup)
          rw [metadataEqual]
          exact centersEqual)
  · exact
      (retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_allCycleRoute_of_center_ne
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        clauseMember literalMember choiceLookup
        metadataLookup cycleLiteralIndex centersEqual).toRoutesAvoidEachOther

end PeriodicOrthocrossing
end LeanTrominoes
