import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRouteSimplicity
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVertexGeometry
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVertexDistinctness
import LeanTrominoes.OrthogonalPolylineBoundingBox
import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceRouteTranslation

/-!
# Separation of finite assembled route pieces

The checked local incidence drawings express separation using route keys and
list membership.  The global periodic drawing uses the equivalent indexed
continuous-separation predicate.  This file bridges the two formulations and
applies the result to variable-site prefixes and clause-core routes.
-/

namespace LeanTrominoes

namespace LocalIncidenceDrawing

open Gadget

/-- Two distinct routes in a valid local incidence drawing satisfy the
indexed continuous-separation predicate used by global drawings. -/
theorem routeAt_routesAvoidEachOther_of_isValid
    {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element)
    (valid : drawing.IsValid)
    {first second : RouteKey Triple}
    (different : first ≠ second) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (drawing.routeAt first) (drawing.routeAt second) := by
  have forward := valid.2.2.2.1 first second different
  have backward := valid.2.2.2.1 second first different.symm
  constructor
  · intro firstIndex secondIndex interiorsMeet
    exact forward.1.1
      ((gridPolylineSegments (drawing.routeAt first)).get firstIndex)
      (List.get_mem _ _)
      ((gridPolylineSegments (drawing.routeAt second)).get secondIndex)
      (List.get_mem _ _)
      interiorsMeet
  constructor
  · intro firstPointIndex secondSegmentIndex interiorContains
    exact forward.1.2
      ((drawing.routeAt first).get firstPointIndex)
      (List.get_mem _ _)
      ((gridPolylineSegments (drawing.routeAt second)).get
        secondSegmentIndex)
      (List.get_mem _ _)
      interiorContains
  constructor
  · intro secondPointIndex firstSegmentIndex interiorContains
    exact backward.1.2
      ((drawing.routeAt second).get secondPointIndex)
      (List.get_mem _ _)
      ((gridPolylineSegments (drawing.routeAt first)).get
        firstSegmentIndex)
      (List.get_mem _ _)
      interiorContains
  · intro firstPointIndex secondPointIndex pointsEqual
    have secondMembership :
        (drawing.routeAt first).get firstPointIndex ∈
          drawing.routeAt second := by
      rw [pointsEqual]
      exact List.get_mem _ _
    have endpoints := forward.2
      ((drawing.routeAt first).get firstPointIndex)
      (List.get_mem _ _) secondMembership
    have firstEndpoint :
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
          (drawing.routeAt first)
          ((drawing.routeAt first).get firstPointIndex) := by
      rcases endpoints.1 with sourceEq | targetEq
      · left
        exact (valid.1 first).1.trans (congrArg some sourceEq.symm)
      · right
        exact (valid.1 first).2.trans (congrArg some targetEq.symm)
    have secondEndpoint :
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
          (drawing.routeAt second)
          ((drawing.routeAt first).get firstPointIndex) := by
      rcases endpoints.2 with sourceEq | targetEq
      · left
        exact (valid.1 second).1.trans (congrArg some sourceEq.symm)
      · right
        exact (valid.1 second).2.trans (congrArg some targetEq.symm)
    rw [pointsEqual] at secondEndpoint
    exact ⟨firstEndpoint, secondEndpoint⟩

end LocalIncidenceDrawing

namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000

/-! ## Strict inset bounds -/

/-- Every route in every finite one-, two-, or three-occurrence variable
site lies in the strict one-cell inset of its standard macrocell. -/
theorem all_variableSiteRoute_points_in_inset_rectangle :
    ∀ (countPred : Fin 3)
      (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      (triple :
        ActiveVariableSiteTriple (countPred + 1) kind)
      (color : WireColor)
      (point : Cell),
      point ∈
          translatePolyline standardThreeStrandLayout.variableOffset
            ((variableSiteDrawing (countPred + 1) kind polarity).route
              triple color) →
        InClosedGridRectangle (1, 1) (127, 127) point := by
  native_decide

/-- Every route in the fixed clause core has the same strict inset bound. -/
theorem all_clauseRoute_points_in_inset_rectangle :
    ∀ (set : X3CClauseSet) (color : WireColor) (point : Cell),
      point ∈
          translatePolyline standardThreeStrandLayout.clauseOffset
            (X3CClauseOrthogonal.route set color) →
        InClosedGridRectangle (1, 1) (127, 127) point := by
  native_decide

/-- Routes contained in strict standard-macrocell insets become
contact-free after placement at two distinct source lattice points. -/
theorem insetRoutes_strictlyAvoidEachOther_of_centers_ne
    {first second : List Cell}
    {firstCenter secondCenter : Cell}
    (firstBounded :
      ∀ point ∈ first,
        InClosedGridRectangle (1, 1) (127, 127) point)
    (secondBounded :
      ∀ point ∈ second,
        InClosedGridRectangle (1, 1) (127, 127) point)
    (centersNe : firstCenter ≠ secondCenter) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor firstCenter) first)
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor secondCenter)
        second) := by
  apply routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        Cell.add
          (Cell.scale standardThreeStrandLayout.factor firstCenter)
          (1, 1))
      (firstUpper :=
        Cell.add
          (Cell.scale standardThreeStrandLayout.factor firstCenter)
          (127, 127))
      (secondLower :=
        Cell.add
          (Cell.scale standardThreeStrandLayout.factor secondCenter)
          (1, 1))
      (secondUpper :=
        Cell.add
          (Cell.scale standardThreeStrandLayout.factor secondCenter)
          (127, 127))
  · intro point pointMember
    unfold translatePolyline at pointMember
    rcases List.mem_map.mp pointMember with
      ⟨localPoint, localMember, rfl⟩
    have bounded := firstBounded localPoint localMember
    rcases firstCenter with ⟨centerX, centerY⟩
    rcases localPoint with ⟨pointX, pointY⟩
    simp only [InClosedGridRectangle, standardThreeStrandLayout,
      Cell.add, Cell.scale] at bounded ⊢
    omega
  · intro point pointMember
    unfold translatePolyline at pointMember
    rcases List.mem_map.mp pointMember with
      ⟨localPoint, localMember, rfl⟩
    have bounded := secondBounded localPoint localMember
    rcases secondCenter with ⟨centerX, centerY⟩
    rcases localPoint with ⟨pointX, pointY⟩
    simp only [InClosedGridRectangle, standardThreeStrandLayout,
      Cell.add, Cell.scale] at bounded ⊢
    omega
  · rcases firstCenter with ⟨firstX, firstY⟩
    rcases secondCenter with ⟨secondX, secondY⟩
    have coordinateNe : firstX ≠ secondX ∨ firstY ≠ secondY := by
      by_cases xEq : firstX = secondX
      · right
        intro yEq
        exact centersNe (Prod.ext xEq yEq)
      · exact Or.inl xEq
    simp only [ClosedGridRectanglesSeparated,
      standardThreeStrandLayout, Cell.add, Cell.scale]
    rcases coordinateNe with xNe | yNe <;> omega

/-- Every route in an actually instantiated source-variable site inherits
the exhaustive strict-inset certificate. -/
theorem sourceVariableSiteRoute_points_in_inset_rectangle
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source) :
    ∀ triple color point,
      point ∈
          translatePolyline standardThreeStrandLayout.variableOffset
            ((sourceVariableSiteDrawing source atom).route
              triple color) →
        InClosedGridRectangle (1, 1) (127, 127) point := by
  rcases usedSlots_cases_of_atom_mem source atom atomMember with
    one | twoOrThree
  · unfold sourceVariableSiteDrawing sourceVariableSiteCount
      sourceVariableSiteKind sourceVariableSitePolarity
    rw [one]
    intro triple color point pointMember
    exact all_variableSiteRoute_points_in_inset_rectangle
      ⟨0, by decide⟩ _ _ triple color point pointMember
  · rcases twoOrThree with two | three
    · unfold sourceVariableSiteDrawing sourceVariableSiteCount
        sourceVariableSiteKind sourceVariableSitePolarity
      rw [two]
      intro triple color point pointMember
      exact all_variableSiteRoute_points_in_inset_rectangle
        ⟨1, by decide⟩ _ _ triple color point pointMember
    · unfold sourceVariableSiteDrawing sourceVariableSiteCount
        sourceVariableSiteKind sourceVariableSitePolarity
      rw [three]
      intro triple color point pointMember
      exact all_variableSiteRoute_points_in_inset_rectangle
        ⟨2, by decide⟩ _ _ triple color point pointMember

/-- Distinct declared source owners have distinct lattice centers. -/
theorem assemblyMacrocellOwnerPosition_ne_of_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (first second : AssemblyMacrocellOwner Variable)
    (firstDeclared : first.IsDeclared source.erase)
    (secondDeclared : second.IsDeclared source.erase)
    (ownersNe : first ≠ second) :
    assemblyMacrocellOwnerPosition source placement first ≠
      assemblyMacrocellOwnerPosition source placement second := by
  intro centersEqual
  exact ownersNe
    (assemblyMacrocellOwnerPosition_injective_on
      presentation anchorsZero first second firstDeclared secondDeclared
      centersEqual)

/-! ## Separation across distinct source cores -/

/-- Arbitrary finite routes housed at two distinct source variables are
contact-free after standard placement. -/
theorem constructedVariableSiteRoutes_strictlyAvoidEachOther_of_atoms_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (firstAtom secondAtom : Variable)
    (firstAtomMember : firstAtom ∈ occurringVariables source.erase)
    (secondAtomMember : secondAtom ∈ occurringVariables source.erase)
    (atomsNe : firstAtom ≠ secondAtom)
    (firstTriple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase firstAtom)
        (sourceVariableSiteKind source.erase firstAtom))
    (firstColor : WireColor)
    (secondTriple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase secondAtom)
        (sourceVariableSiteKind source.erase secondAtom))
    (secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout
          firstAtom)
        ((sourceVariableSiteDrawing source.erase firstAtom).route
          firstTriple firstColor))
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout
          secondAtom)
        ((sourceVariableSiteDrawing source.erase secondAtom).route
          secondTriple secondColor)) := by
  have centersNe :
      placement.position firstAtom ≠ placement.position secondAtom := by
    exact assemblyMacrocellOwnerPosition_ne_of_ne
      presentation anchorsZero (.atom firstAtom) (.atom secondAtom)
      firstAtomMember secondAtomMember
      (fun equal => atomsNe (AssemblyMacrocellOwner.atom.inj equal))
  have separated := insetRoutes_strictlyAvoidEachOther_of_centers_ne
    (sourceVariableSiteRoute_points_in_inset_rectangle
      source.erase firstAtom firstAtomMember firstTriple firstColor)
    (sourceVariableSiteRoute_points_in_inset_rectangle
      source.erase secondAtom secondAtomMember secondTriple secondColor)
    centersNe
  simpa [constructedVariableOrigin, translatePolyline_add,
    Cell.add, add_comm] using separated

/-- Every finite source-variable route strictly avoids every finite clause
route housed at a distinct source owner. -/
theorem constructedVariableSiteRoute_strictlyAvoids_clauseRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source.erase)
    (variableTriple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase atom)
        (sourceVariableSiteKind source.erase atom))
    (variableColor : WireColor)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet) (clauseColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout atom)
        ((sourceVariableSiteDrawing source.erase atom).route
          variableTriple variableColor))
      (translatePolyline
        (constructedClauseOrigin source standardThreeStrandLayout clauseIndex)
        (X3CClauseOrthogonal.route set clauseColor)) := by
  have centersNe :
      placement.position atom ≠
        positionedClausePositionAt source clauseIndex := by
    exact assemblyMacrocellOwnerPosition_ne_of_ne
      presentation anchorsZero (.atom atom) (.clause clauseIndex)
      atomMember (by
        simpa [AssemblyMacrocellOwner.IsDeclared,
          PositionedPeriodicCNF.erase] using indexLt)
      (by intro equal; cases equal)
  have separated := insetRoutes_strictlyAvoidEachOther_of_centers_ne
    (sourceVariableSiteRoute_points_in_inset_rectangle
      source.erase atom atomMember variableTriple variableColor)
    (all_clauseRoute_points_in_inset_rectangle set clauseColor)
    centersNe
  simpa [constructedVariableOrigin, constructedClauseOrigin,
    translatePolyline_add, Cell.add, add_comm] using separated

/-- Finite clause-core routes belonging to distinct clauses are
contact-free after standard placement. -/
theorem constructedClauseRoutes_strictlyAvoidEachOther_of_indices_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (firstIndex secondIndex : Nat)
    (firstIndexLt : firstIndex < source.clauses.length)
    (secondIndexLt : secondIndex < source.clauses.length)
    (indicesNe : firstIndex ≠ secondIndex)
    (firstSet secondSet : X3CClauseSet)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        (constructedClauseOrigin source standardThreeStrandLayout firstIndex)
        (X3CClauseOrthogonal.route firstSet firstColor))
      (translatePolyline
        (constructedClauseOrigin source standardThreeStrandLayout secondIndex)
        (X3CClauseOrthogonal.route secondSet secondColor)) := by
  have centersNe :
      positionedClausePositionAt source firstIndex ≠
        positionedClausePositionAt source secondIndex := by
    exact assemblyMacrocellOwnerPosition_ne_of_ne
      presentation anchorsZero (.clause firstIndex) (.clause secondIndex)
      (by simpa [AssemblyMacrocellOwner.IsDeclared,
        PositionedPeriodicCNF.erase] using firstIndexLt)
      (by simpa [AssemblyMacrocellOwner.IsDeclared,
        PositionedPeriodicCNF.erase] using secondIndexLt)
      (fun equal => indicesNe (AssemblyMacrocellOwner.clause.inj equal))
  have separated := insetRoutes_strictlyAvoidEachOther_of_centers_ne
    (all_clauseRoute_points_in_inset_rectangle firstSet firstColor)
    (all_clauseRoute_points_in_inset_rectangle secondSet secondColor)
    centersNe
  simpa [constructedClauseOrigin, translatePolyline_add,
    Cell.add, add_comm] using separated

/-- Distinct selected incidences in one finite variable site avoid each
other continuously. -/
theorem typedVariableSiteRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (firstSlot : OccurrenceSlot)
    (firstSlotMember : firstSlot ∈ usedSlots source atom)
    (firstTriple : Triple Variable)
    (firstTripleMember :
      firstTriple ∈ occurrenceTriples source atom firstSlot)
    (firstColor : WireColor)
    (secondSlot : OccurrenceSlot)
    (secondSlotMember : secondSlot ∈ usedSlots source atom)
    (secondTriple : Triple Variable)
    (secondTripleMember :
      secondTriple ∈ occurrenceTriples source atom secondSlot)
    (secondColor : WireColor)
    (different :
      (activeVariableSiteTriple source atom atomMember
          firstSlot firstSlotMember firstTriple firstTripleMember,
        firstColor) ≠
      (activeVariableSiteTriple source atom atomMember
          secondSlot secondSlotMember secondTriple secondTripleMember,
        secondColor)) :
    RoutesAvoidEachOther
      (typedVariableSiteRoute source atom atomMember
        firstSlot firstSlotMember firstTriple firstTripleMember firstColor)
      (typedVariableSiteRoute source atom atomMember
        secondSlot secondSlotMember secondTriple secondTripleMember
        secondColor) := by
  exact LocalIncidenceDrawing.routeAt_routesAvoidEachOther_of_isValid
    (sourceVariableSiteDrawing source atom)
    (sourceVariableSiteDrawing_isValid source atom atomMember)
    different

/-- Translating two distinct incidences from the same variable site
preserves their continuous separation. -/
theorem translatedTypedVariableSiteRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (firstSlot : OccurrenceSlot)
    (firstSlotMember : firstSlot ∈ usedSlots source atom)
    (firstTriple : Triple Variable)
    (firstTripleMember :
      firstTriple ∈ occurrenceTriples source atom firstSlot)
    (firstColor : WireColor)
    (secondSlot : OccurrenceSlot)
    (secondSlotMember : secondSlot ∈ usedSlots source atom)
    (secondTriple : Triple Variable)
    (secondTripleMember :
      secondTriple ∈ occurrenceTriples source atom secondSlot)
    (secondColor : WireColor)
    (different :
      (activeVariableSiteTriple source atom atomMember
          firstSlot firstSlotMember firstTriple firstTripleMember,
        firstColor) ≠
      (activeVariableSiteTriple source atom atomMember
          secondSlot secondSlotMember secondTriple secondTripleMember,
        secondColor))
    (offset : Cell) :
    RoutesAvoidEachOther
      (translatePolyline offset
        (typedVariableSiteRoute source atom atomMember
          firstSlot firstSlotMember firstTriple firstTripleMember
          firstColor))
      (translatePolyline offset
        (typedVariableSiteRoute source atom atomMember
          secondSlot secondSlotMember secondTriple secondTripleMember
          secondColor)) := by
  exact routesAvoidEachOther_translate
    (typedVariableSiteRoutes_avoidEachOther source atom atomMember
      firstSlot firstSlotMember firstTriple firstTripleMember firstColor
      secondSlot secondSlotMember secondTriple secondTripleMember
      secondColor different)
    offset

/-- Distinct colored incidences in the checked clause core avoid each other
continuously. -/
theorem orientedClauseLocalRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (firstSet secondSet : X3CClauseSet)
    (firstColor secondColor : WireColor)
    (different :
      (firstSet, firstColor) ≠ (secondSet, secondColor)) :
    RoutesAvoidEachOther
      (orientedIncidenceLocalRoute source
        (.clause clauseIndex firstSet) firstColor)
      (orientedIncidenceLocalRoute source
        (.clause clauseIndex secondSet) secondColor) := by
  simpa [orientedIncidenceLocalRoute,
    LocalIncidenceDrawing.routeAt, X3CClauseOrthogonal.drawing] using
    (LocalIncidenceDrawing.routeAt_routesAvoidEachOther_of_isValid
      X3CClauseOrthogonal.drawing
      X3CClauseOrthogonal.drawing_isValid different)

/-- Distinct colored routes assembled in one clause core retain continuous
separation after placement at the global clause origin. -/
theorem assembledClauseRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (clauseIndex : Nat)
    (firstSet secondSet : X3CClauseSet)
    (firstColor secondColor : WireColor)
    (different :
      (firstSet, firstColor) ≠ (secondSet, secondColor)) :
    RoutesAvoidEachOther
      (assembledClauseRoute routing clauseIndex firstSet firstColor)
      (assembledClauseRoute routing clauseIndex secondSet secondColor) := by
  simpa [assembledClauseRoute, translatePolyline] using
    routesAvoidEachOther_translate
      (orientedClauseLocalRoutes_avoidEachOther source clauseIndex
        firstSet secondSet firstColor secondColor different)
      (routing.clauseOrigin clauseIndex)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
