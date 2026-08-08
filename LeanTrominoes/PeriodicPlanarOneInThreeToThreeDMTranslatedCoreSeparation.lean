import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTranslatedOccurrenceRouteSeparation

/-!
# Separation of translated finite incidence cores

Every finite variable-site or clause-core route lies in the strict inset of
the macrocell belonging to its source incidence vertex.  Periodic source
vertex injectivity keeps two such owner macrocells distinct under every
nonzero relative lattice shift.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A declared source-owner position cannot equal a nonzero period translate
of another declared source-owner position. -/
theorem assemblyMacrocellOwnerPosition_ne_translated_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (first second : AssemblyMacrocellOwner Variable)
    (firstDeclared : first.IsDeclared source.erase)
    (secondDeclared : second.IsDeclared source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0)) :
    assemblyMacrocellOwnerPosition source placement first ≠
      Cell.add (placement.translation translate)
        (assemblyMacrocellOwnerPosition source placement second) := by
  have firstMember :=
    AssemblyMacrocellOwner.toCNFVertex_mem
      source.erase first firstDeclared
  have secondMember :=
    AssemblyMacrocellOwner.toCNFVertex_mem
      source.erase second secondDeclared
  have firstPosition :
      assemblyMacrocellOwnerPosition source placement first =
        PositionedPeriodicCNF.incidenceVertexPositionAt
          source placement first.toCNFVertex := by
    calc
      assemblyMacrocellOwnerPosition source placement first =
          (PositionedPeriodicCNF.incidenceDrawing
            source placement presentation.routes).vertexPosition
              source.erase.incidenceGraph first.toCNFVertex :=
        assemblyMacrocellOwnerPosition_eq_vertexPosition
          presentation anchorsZero first firstDeclared
      _ = PositionedPeriodicCNF.incidenceVertexPositionAt
            source placement first.toCNFVertex :=
        PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
          source placement presentation.routes firstMember
  have secondPosition :
      assemblyMacrocellOwnerPosition source placement second =
        PositionedPeriodicCNF.incidenceVertexPositionAt
          source placement second.toCNFVertex := by
    calc
      assemblyMacrocellOwnerPosition source placement second =
          (PositionedPeriodicCNF.incidenceDrawing
            source placement presentation.routes).vertexPosition
              source.erase.incidenceGraph second.toCNFVertex :=
        assemblyMacrocellOwnerPosition_eq_vertexPosition
          presentation anchorsZero second secondDeclared
      _ = PositionedPeriodicCNF.incidenceVertexPositionAt
            source placement second.toCNFVertex :=
        PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
          source placement presentation.routes secondMember
  intro positionsEqual
  have verticesEqual : first.toCNFVertex = second.toCNFVertex :=
    presentation.incidenceVertexPositionAt_eq_translated_imp_eq
      firstMember secondMember translate (by
        simpa [firstPosition, secondPosition] using positionsEqual)
  have ownersEqual : first = second := by
    cases first <;> cases second <;>
      simp_all [AssemblyMacrocellOwner.toCNFVertex]
  subst second
  have translationZero : placement.translation translate = (0, 0) := by
    apply Cell.add_left_injective
      (assemblyMacrocellOwnerPosition source placement first)
    simpa [Cell.add, add_comm] using positionsEqual.symm
  have periodNonzero : (placement.period : Int) ≠ 0 := by
    exact_mod_cast presentation.periodPositive.ne'
  have translateZero : translate = (0, 0) := by
    apply Cell.scale_injective periodNonzero
    simpa [PeriodicVariablePlacement.translation, Cell.scale] using
      translationZero
  exact translateNonzero translateZero

/-- Every assembled finite incidence core is a translated local route with
the common strict-inset bound, centered at its declared source owner. -/
theorem assembledTypedIncidenceCoreRoute_eq_ownerInsetRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (triple : {triple : Triple Variable // triple ∈ triples source.erase})
    (color : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    ∃ localRoute : List Cell,
      (∀ point ∈ localRoute,
        InClosedGridRectangle (1, 1) (127, 127) point) ∧
      assembledTypedIncidenceCoreRoute routing triple color =
        translatePolyline
          (ribbonMacrocellOrigin
            (assemblyMacrocellOwnerPosition source placement
              (tripleMacrocellOwner triple.1)))
          localRoute := by
  dsimp only
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  rcases triple with ⟨triple, tripleMember⟩
  cases triple with
  | ordinary atom slot variant localTriple =>
      let location := ordinaryTriple_location source.erase
        atom slot variant localTriple tripleMember
      let localRoute :=
        translatePolyline standardThreeStrandLayout.variableOffset
          ((sourceVariableSiteDrawing source.erase atom).route
            (activeVariableSiteTriple source.erase atom location.1
              slot location.2.1
              (.ordinary atom slot variant localTriple) location.2.2)
            color)
      refine ⟨localRoute, ?_, ?_⟩
      · exact sourceVariableSiteRoute_points_in_inset_rectangle
          source.erase atom location.1
          _ color
      · simp [assembledTypedIncidenceCoreRoute, assembledOrdinaryPrefix,
          typedVariableSiteRoute, localRoute,
          coordinatedSourceRibbonThreeStrandRouting,
          RibbonEndpointFanSystem.threeStrandRouting,
          assemblyMacrocellOwnerPosition, tripleMacrocellOwner,
          constructedVariableOrigin, ribbonMacrocellOrigin,
          translatePolyline_add, Cell.add, add_comm]
  | fixedRed atom slot localTriple =>
      let location := fixedRedTriple_location source.erase
        atom slot localTriple tripleMember
      let localRoute :=
        translatePolyline standardThreeStrandLayout.variableOffset
          ((sourceVariableSiteDrawing source.erase atom).route
            (activeVariableSiteTriple source.erase atom location.1
              slot location.2.1
              (.fixedRed atom slot localTriple) location.2.2)
            color)
      refine ⟨localRoute, ?_, ?_⟩
      · exact sourceVariableSiteRoute_points_in_inset_rectangle
          source.erase atom location.1
          _ color
      · simp [assembledTypedIncidenceCoreRoute, assembledFixedRedPrefix,
          typedVariableSiteRoute, localRoute,
          coordinatedSourceRibbonThreeStrandRouting,
          RibbonEndpointFanSystem.threeStrandRouting,
          assemblyMacrocellOwnerPosition, tripleMacrocellOwner,
          constructedVariableOrigin, ribbonMacrocellOrigin,
          translatePolyline_add, Cell.add, add_comm]
  | clause clauseIndex set =>
      let localRoute :=
        translatePolyline standardThreeStrandLayout.clauseOffset
          (X3CClauseOrthogonal.route set color)
      refine ⟨localRoute, all_clauseRoute_points_in_inset_rectangle
        set color, ?_⟩
      simp [assembledTypedIncidenceCoreRoute, assembledClauseRoute,
        orientedIncidenceLocalRoute, localRoute,
        coordinatedSourceRibbonThreeStrandRouting,
        RibbonEndpointFanSystem.threeStrandRouting,
        assemblyMacrocellOwnerPosition, tripleMacrocellOwner,
        constructedClauseOrigin, ribbonMacrocellOrigin,
        translatePolyline_add, Cell.add, add_comm]

/-- Finite cores of arbitrary typed incidences are strictly separated from
every nonzero period translate of one another. -/
theorem assembledTypedIncidenceCoreRoute_strictlyAvoids_nonzeroTranslate
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first second :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (firstColor secondColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesStrictlyAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (assembledTypedIncidenceCoreRoute routing second secondColor)) := by
  dsimp only
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  let firstOwner := tripleMacrocellOwner first.1
  let secondOwner := tripleMacrocellOwner second.1
  let firstCenter :=
    assemblyMacrocellOwnerPosition source placement firstOwner
  let secondBaseCenter :=
    assemblyMacrocellOwnerPosition source placement secondOwner
  let secondCenter :=
    Cell.add (placement.translation translate) secondBaseCenter
  rcases assembledTypedIncidenceCoreRoute_eq_ownerInsetRoute
      presentation width compatible first firstColor with
    ⟨firstLocal, firstBounded, firstEq⟩
  rcases assembledTypedIncidenceCoreRoute_eq_ownerInsetRoute
      presentation width compatible second secondColor with
    ⟨secondLocal, secondBounded, secondEq⟩
  have firstDeclared : firstOwner.IsDeclared source.erase :=
    tripleMacrocellOwner_declared source.erase first.1 first.2
  have secondDeclared : secondOwner.IsDeclared source.erase :=
    tripleMacrocellOwner_declared source.erase second.1 second.2
  have centersNe : firstCenter ≠ secondCenter :=
    assemblyMacrocellOwnerPosition_ne_translated_of_nonzero
      presentation.toPlanarIncidencePresentation anchorsZero
      firstOwner secondOwner firstDeclared secondDeclared
      translate translateNonzero
  have separated :=
    insetRoutes_strictlyAvoidEachOther_of_centers_ne
      (firstCenter := firstCenter) (secondCenter := secondCenter)
      firstBounded secondBounded centersNe
  have separated' :
      RoutesStrictlyAvoidEachOther
        (translatePolyline (ribbonMacrocellOrigin firstCenter) firstLocal)
        (translatePolyline (ribbonMacrocellOrigin secondCenter) secondLocal) := by
    simpa [ribbonMacrocellOrigin] using separated
  have secondOriginEq :
      ribbonMacrocellOrigin secondCenter =
        Cell.add (ribbonMacrocellOrigin secondBaseCenter)
          (ribbonMacrocellOrigin (placement.translation translate)) := by
    rcases translate with ⟨translateX, translateY⟩
    rcases baseEq : secondBaseCenter with ⟨baseX, baseY⟩
    apply Prod.ext <;>
      simp [secondCenter, ribbonMacrocellOrigin,
        PeriodicVariablePlacement.translation,
        standardThreeStrandLayout, baseEq, Cell.add, Cell.scale] <;> ring
  rw [firstEq, secondEq]
  rw [secondOriginEq] at separated'
  simpa [firstCenter, secondBaseCenter, firstOwner, secondOwner,
    ribbonMacrocellOrigin, translatePolyline_add,
    add_comm, add_left_comm, add_assoc] using separated'

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
