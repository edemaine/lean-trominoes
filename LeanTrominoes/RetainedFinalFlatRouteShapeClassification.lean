/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalFlatCarrierRouteBounds
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedTranslatedComponentCenters
import LeanTrominoes.RetainedFinalSourceScaledSpliceSeparation

/-!
# Component-sensitive shape of flat final routes

The generic final-route shape theorem deliberately forgets which branch of
the orthogonal-or-singleton dichotomy came from each local component.  The
mixed angular-fan residue needs that information back: crossover,
routed-clause, and routed-variable drawings consist of direct two-point
routes, whereas bend drawings are fully orthogonal.

This file records singleton prefixes as a drawing-level invariant, transports
it through renaming and translation, and then recovers the exact branch from
a flat final route occurrence.
-/

namespace LeanTrominoes

namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

open PeriodicOrthocrossing

/-- Every genuine route of a drawing has a singleton `dropLast` prefix. -/
def RoutePrefixesSingleton
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ incidenceIndex : Fin drawing.incidences.length,
    (drawing.routeAt
      (drawing.incidenceAt incidenceIndex)).dropLast.length = 1

/-- Translation preserves singleton route prefixes. -/
theorem RoutePrefixesSingleton.translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (singleton : drawing.RoutePrefixesSingleton)
    (offset : Cell) :
    (drawing.translate offset).RoutePrefixesSingleton := by
  intro translatedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  rw [incidenceEqual, routeAt_translate_incidence]
  rw [← List.map_dropLast, List.length_map]
  exact singleton originalIndex

/-- Logical-variable renaming preserves singleton route prefixes. -/
theorem RoutePrefixesSingleton.rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (singleton : drawing.RoutePrefixesSingleton)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename
      variableMap targetPosition).RoutePrefixesSingleton := by
  intro renamedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length
          drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
  exact singleton originalIndex

/-- Singleton prefixes can be pulled back through a logical rename. -/
theorem RoutePrefixesSingleton.of_rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (singleton :
      (drawing.rename
        variableMap targetPosition).RoutePrefixesSingleton) :
    drawing.RoutePrefixesSingleton := by
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
  have renamedSingleton := singleton renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
    at renamedSingleton
  exact renamedSingleton

/-- Membership-style form of the singleton-prefix invariant. -/
theorem routePrefixesSingleton_iff
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    drawing.RoutePrefixesSingleton ↔
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ drawing.formula.zipIdx →
          ∀ literal literalIndex,
            (literal, literalIndex) ∈ clause.literals.zipIdx →
              (drawing.routes
                clauseIndex literalIndex).dropLast.length = 1 := by
  constructor
  · intro singleton clause clauseIndex clauseMember
      literal literalIndex literalMember
    let incidence : EmbeddedCNFIncidence Variable :=
      ⟨clause, clauseIndex, literal, literalIndex⟩
    have incidenceMember :
        incidence ∈ drawing.incidences :=
      (mem_embeddedCNFIncidences_iff
        drawing.formula incidence).mpr
        ⟨clauseMember, literalMember⟩
    rcases List.mem_iff_get.mp incidenceMember with
      ⟨incidenceIndex, incidenceEqual⟩
    have routeSingleton := singleton incidenceIndex
    have incidenceAtEqual :
        drawing.incidenceAt incidenceIndex = incidence :=
      incidenceEqual
    rw [incidenceAtEqual] at routeSingleton
    exact routeSingleton
  · intro singleton incidenceIndex
    let incidence := drawing.incidenceAt incidenceIndex
    have incidenceMember :
        incidence ∈ drawing.incidences :=
      List.get_mem drawing.incidences incidenceIndex
    have indexedMembers :=
      (mem_embeddedCNFIncidences_iff
        drawing.formula incidence).mp incidenceMember
    exact singleton
      incidence.clause incidence.clauseIndex indexedMembers.1
      incidence.literal incidence.literalIndex indexedMembers.2

/-- Every direct two-point incidence drawing has singleton prefixes. -/
theorem straightIncidenceDrawing_routePrefixesSingleton
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell) :
    (straightIncidenceDrawing
      formula variablePosition).RoutePrefixesSingleton := by
  rw [routePrefixesSingleton_iff]
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  change (clause, clauseIndex) ∈ formula.zipIdx
    at clauseMember
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  simp [straightIncidenceDrawing, straightIncidenceRoutes,
    straightIncidenceRoute, clauseLookup, literalLookup]

/-- Orthogonality of a drawing supplies orthogonality of any route selected
by genuine clause and literal membership. -/
theorem IsOrthogonal.route_orthogonal_of_members
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (orthogonal : drawing.IsOrthogonal)
    {clause : EmbeddedClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    OrthogonalPolyline
      (drawing.routes clauseIndex literalIndex) := by
  let incidence : EmbeddedCNFIncidence Variable :=
    ⟨clause, clauseIndex, literal, literalIndex⟩
  have incidenceMember :
      incidence ∈ drawing.incidences :=
    (mem_embeddedCNFIncidences_iff
      drawing.formula incidence).mpr
      ⟨clauseMember, literalMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have originalOrthogonal :
      OrthogonalPolyline
        (drawing.routeAt
          (drawing.incidenceAt incidenceIndex)) := by
    rw [orthogonalPolyline_iff_segments]
    intro segment segmentMember
    rcases List.mem_iff_get.mp segmentMember with
      ⟨segmentIndex, rfl⟩
    exact orthogonal incidenceIndex segmentIndex
  have incidenceAtEqual :
      drawing.incidenceAt incidenceIndex = incidence :=
    incidenceEqual
  rw [incidenceAtEqual] at originalOrthogonal
  exact originalOrthogonal

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT

namespace PeriodicOrthocrossing

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit

/-- The three direct local component families. -/
def DrawingPlanarSATComponent.IsDirect
    {Variable : Type*} :
    DrawingPlanarSATComponent Variable → Prop
  | .crossover _ => True
  | .routedClause _ => True
  | .routedVariable _ _ _ => True
  | .carrier _ => False
  | .bend _ => False

/-- Period translation does not change whether a component belongs to a
direct two-point family. -/
theorem DrawingPlanarSATClauseSource.component_periodTranslate_isDirect_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell) :
    (source.periodTranslate formula shift).component.IsDirect ↔
      source.component.IsDirect := by
  cases source <;>
    simp [DrawingPlanarSATClauseSource.periodTranslate,
      DrawingPlanarSATClauseSource.component,
      DrawingPlanarSATComponent.IsDirect]

/-- Every placed crossover route has a singleton prefix. -/
theorem drawingPlanarSATCrossoverIncidenceDrawing_routePrefixesSingleton
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord) :
    (drawingPlanarSATCrossoverIncidenceDrawing
      formula crossing).RoutePrefixesSingleton := by
  unfold drawingPlanarSATCrossoverIncidenceDrawing
  apply EmbeddedCNFIncidenceDrawing.RoutePrefixesSingleton.rename
  apply EmbeddedCNFIncidenceDrawing.RoutePrefixesSingleton.translate
  simpa [crossoverStraightIncidenceDrawing] using
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routePrefixesSingleton
      crossoverFormula CrossoverVariable.position

/-- Every placed routed-variable route has a singleton prefix. -/
theorem drawingPlanarSATRoutedVariableIncidenceDrawing_routePrefixesSingleton
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing
      formula site arm link).RoutePrefixesSingleton := by
  unfold drawingPlanarSATRoutedVariableIncidenceDrawing
  apply EmbeddedCNFIncidenceDrawing.RoutePrefixesSingleton.rename
  apply EmbeddedCNFIncidenceDrawing.RoutePrefixesSingleton.translate
  simpa [duplicatorArmStraightIncidenceDrawing] using
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routePrefixesSingleton
      (duplicatorArmFormula arm)
      (DuplicatorArmVariable.position arm)

/-- Every placed routed-clause route has a singleton prefix. -/
theorem drawingPlanarSATRoutedClauseIncidenceDrawing_routePrefixesSingleton
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    (drawingPlanarSATRoutedClauseIncidenceDrawing
      formula site).RoutePrefixesSingleton := by
  apply EmbeddedCNFIncidenceDrawing.RoutePrefixesSingleton.of_rename
    planarSATRoutedClauseArm
    (routedClauseArmPosition formula site)
  rw [drawingPlanarSATRoutedClauseIncidenceDrawing_rename]
  apply EmbeddedCNFIncidenceDrawing.RoutePrefixesSingleton.translate
  simpa [routedClausePortStraightIncidenceDrawing] using
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routePrefixesSingleton
      (routedClausePortFormula
        (routedClausePortLiterals formula site))
      DuplicatorArm.portPosition

/-- Component-sensitive singleton-prefix selection for retained metadata. -/
theorem
    DrawingPlanarSATClauseMetadata.retainedLocalDrawingRoutePrefixesSingleton_of_direct
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (direct : metadata.source.component.IsDirect) :
    (metadata.source.incidenceDrawing
      formula).RoutePrefixesSingleton := by
  rcases metadata with ⟨clause, source⟩
  cases source with
  | crossover crossing localClauseIndex =>
      exact
        drawingPlanarSATCrossoverIncidenceDrawing_routePrefixesSingleton
          formula crossing
  | carrier link localClauseIndex =>
      simp [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.IsDirect] at direct
  | bend routeBend localClauseIndex =>
      simp [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.IsDirect] at direct
  | routedClause site =>
      exact
        drawingPlanarSATRoutedClauseIncidenceDrawing_routePrefixesSingleton
          formula site
  | routedVariable site armIndex arm link localClauseIndex =>
      exact
        drawingPlanarSATRoutedVariableIncidenceDrawing_routePrefixesSingleton
          formula site arm link

/-- A retained metadata source known to be a bend selects a fully
orthogonal local drawing. -/
theorem
    DrawingPlanarSATClauseMetadata.retainedLocalDrawingIsOrthogonal_of_bend
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (routeBend : RouteBend)
    (componentEq :
      metadata.source.component = .bend routeBend) :
    (metadata.source.incidenceDrawing formula).IsOrthogonal := by
  rcases metadata with ⟨clause, source⟩
  cases source <;>
    simp_all [DrawingPlanarSATClauseSource.component,
      DrawingPlanarSATClauseSource.incidenceDrawing]
  exact
    (drawingPlanarSATBendCornerIncidenceDrawing_isValid
      wellFormed degree isLocal valid.1).2.1

/-- A flat final occurrence selected from a direct component has a
singleton source prefix. -/
theorem
    FinalGaugedFlatRouteOccurrenceWitness.routePrefix_length_eq_one_of_direct
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatRouteOccurrenceWitness
        formula taggedRoute)
    (direct :
      witness.routeWitness.metadata.source.component.IsDirect) :
    taggedRoute.1.dropLast.length = 1 := by
  have singleton :=
    witness.routeWitness.metadata
      |>.retainedLocalDrawingRoutePrefixesSingleton_of_direct
        (formula := formula) direct
  have localClauseMember :=
    witness.routeWitness.metadata.retainedLocalClauseMember
      wellFormed degree isLocal
      witness.routeWitness.metadata_retainedValid
  have localSingleton :=
    (EmbeddedCNFIncidenceDrawing.routePrefixesSingleton_iff
      (witness.routeWitness.metadata.source.incidenceDrawing
        formula)).mp singleton
      witness.routeWitness.metadata.clause
      witness.routeWitness.metadata.source.localClauseIndex
      localClauseMember
      witness.routeWitness.literal
      witness.coordinates.taggedLiteral.2
      witness.routeWitness.literalMember
  rw [witness.finalRoute_eq_occurrence,
    witness.routeWitness.routeEq]
  unfold metadataPhysicalRouteOccurrence
  unfold translatePolyline
  rw [← List.map_dropLast, List.length_map]
  simpa [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
    retainedDrawingPlanarSATLocalIncidenceRoutes,
    metadataPhysicalIncidence,
    EmbeddedCNFIncidenceDrawing.routeAt,
    witness.routeWitness.metadataLookup] using localSingleton

/-- A flat final occurrence selected from a bend component remains fully
orthogonal after physical translation and quotient normalization. -/
theorem
    FinalGaugedFlatRouteOccurrenceWitness.routeOrthogonal_of_component_eq_bend
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatRouteOccurrenceWitness
        formula taggedRoute)
    (routeBend : RouteBend)
    (componentEq :
      witness.routeWitness.metadata.source.component =
        .bend routeBend) :
    OrthogonalPolyline taggedRoute.1 := by
  have localDrawingOrthogonal :=
    witness.routeWitness.metadata
      |>.retainedLocalDrawingIsOrthogonal_of_bend
        wellFormed degree isLocal
        witness.routeWitness.metadata_retainedValid
        routeBend componentEq
  have localClauseMember :=
    witness.routeWitness.metadata.retainedLocalClauseMember
      wellFormed degree isLocal
      witness.routeWitness.metadata_retainedValid
  have localOrthogonal :=
    localDrawingOrthogonal.route_orthogonal_of_members
      localClauseMember witness.routeWitness.literalMember
  have physicalOrthogonal :
      OrthogonalPolyline
        ((retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).routeAt
            (metadataPhysicalIncidence
              witness.routeWitness.metadata
              witness.routeWitness.metadataIndex
              witness.routeWitness.literal
              witness.coordinates.taggedLiteral.2)) := by
    simpa [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
      retainedDrawingPlanarSATLocalIncidenceRoutes,
      metadataPhysicalIncidence,
      EmbeddedCNFIncidenceDrawing.routeAt,
      witness.routeWitness.metadataLookup] using localOrthogonal
  rw [witness.finalRoute_eq_occurrence,
    witness.routeWitness.routeEq]
  simpa [metadataPhysicalRouteOccurrence, translatePolyline,
    FinalGaugedRouteOccurrenceWitness.physicalShift] using
    physicalOrthogonal.translate
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).translation
        witness.routeWitness.physicalShift)

/-- A noncarrier flat route with a non-axis-aligned discarded final segment
must come from one of the three direct two-point component families. -/
theorem
    FinalGaugedFlatRouteMacrocellWitness.component_isDirect_of_finalSegment_not_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute)
    (routeLength : 2 ≤ taggedRoute.1.length)
    {target : Cell}
    (routeLast : taggedRoute.1.getLast? = some target)
    (finalSegmentNotAxisAligned :
      ¬(⟨polylineLastEntrance taggedRoute.1, target⟩ :
        GridSegment).IsAxisAligned) :
    witness.routeWitness.metadata.source.component.IsDirect := by
  let source := witness.routeWitness.metadata.source
  rcases sourceEq : source with
    crossover | carrier | bend | routedClause | routedVariable
  · simp [source, sourceEq, DrawingPlanarSATClauseSource.component,
      DrawingPlanarSATComponent.IsDirect]
  · exfalso
    have centerEq := witness.centerEq
    simp [source, sourceEq, DrawingPlanarSATClauseSource.component,
      DrawingPlanarSATComponent.macrocellCenter] at centerEq
  · exfalso
    have componentEq :
        witness.routeWitness.metadata.source.component =
          .bend bend := by
      simp [source, sourceEq,
        DrawingPlanarSATClauseSource.component]
    have orthogonal :=
      witness.toFinalGaugedFlatRouteOccurrenceWitness
        |>.routeOrthogonal_of_component_eq_bend
          formula wellFormed degree isLocal bend componentEq
    apply finalSegmentNotAxisAligned
    have finalMember :=
      finalGridSegment_mem taggedRoute.1 routeLength
    have aligned :=
      (orthogonalPolyline_iff_segments taggedRoute.1).mp
        orthogonal
        (⟨polylineLastEntrance taggedRoute.1,
          taggedRoute.1.getLastD (0, 0)⟩ : GridSegment)
        finalMember
    have lastD :
        taggedRoute.1.getLastD (0, 0) = target := by
      rw [List.getLastD_eq_getLast?, routeLast, Option.getD_some]
    rw [lastD] at aligned
    exact aligned
  · simp [source, sourceEq, DrawingPlanarSATClauseSource.component,
      DrawingPlanarSATComponent.IsDirect]
  · simp [source, sourceEq, DrawingPlanarSATClauseSource.component,
      DrawingPlanarSATComponent.IsDirect]

/-- Equal translated centers transfer directness from the second noncarrier
flat route to the first, including the exceptional same-site
routed-variable-arm classification. -/
theorem
    FinalGaugedFlatRouteMacrocellWitness.first_component_isDirect_of_translatedCenters_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstTaggedRoute secondTaggedRoute : List Cell × Nat}
    (first :
      FinalGaugedFlatRouteMacrocellWitness
        formula firstTaggedRoute)
    (second :
      FinalGaugedFlatRouteMacrocellWitness
        formula secondTaggedRoute)
    (centersEqual :
      first.translatedCenter = second.translatedCenter)
    (secondDirect :
      second.routeWitness.metadata.source.component.IsDirect) :
    first.routeWitness.metadata.source.component.IsDirect := by
  let reindexShift :=
    Cell.sub first.routeWitness.physicalShift
      second.routeWitness.physicalShift
  have relativeCentersEqual :
      Cell.add first.center
          ((drawing formula.incidenceGraph).periodTranslation
            reindexShift) =
        second.center := by
    rcases firstCenterValue : first.center with
      ⟨firstX, firstY⟩
    rcases secondCenterValue : second.center with
      ⟨secondX, secondY⟩
    rcases firstShiftEq : first.routeWitness.physicalShift with
      ⟨firstShiftX, firstShiftY⟩
    rcases secondShiftEq : second.routeWitness.physicalShift with
      ⟨secondShiftX, secondShiftY⟩
    simp [FinalGaugedFlatRouteMacrocellWitness.translatedCenter,
      FinalGaugedRouteOccurrenceWitness.translatedMacrocellCenter,
      reindexShift, PeriodicGridDrawing.periodTranslation,
      firstCenterValue, secondCenterValue,
      firstShiftEq, secondShiftEq,
      Cell.add, Cell.sub, Cell.scale] at centersEqual ⊢
    ring_nf at centersEqual ⊢
    omega
  have firstTranslatedCenterEq :
      ((first.routeWitness.metadata.source.periodTranslate
          formula reindexShift).component
        |>.macrocellCenter formula) =
        some second.center := by
    rw [DrawingPlanarSATClauseSource.component_periodTranslate,
      DrawingPlanarSATComponent.macrocellCenter_periodTranslate,
      first.centerEq]
    exact congrArg some relativeCentersEqual
  have classification :=
    retainedNoncarrierComponents_periodTranslate_eq_or_routedVariable_of_center_eq
      formula wellFormed degree isLocal
      first.routeWitness.metadata second.routeWitness.metadata
      first.routeWitness.metadata_retainedValid
      second.routeWitness.metadata_retainedValid
      reindexShift second.center
      firstTranslatedCenterEq second.centerEq
  have translatedDirect :
      (first.routeWitness.metadata.source.periodTranslate
        formula reindexShift).component.IsDirect := by
    rcases classification with componentAlignment | exception
    · rw [← componentAlignment]
      exact secondDirect
    · rcases exception with
        ⟨site, firstArm, firstLink, secondArm, secondLink,
          firstComponentEq, secondComponentEq⟩
      rw [firstComponentEq]
      trivial
  exact
    (DrawingPlanarSATClauseSource.component_periodTranslate_isDirect_iff
      formula first.routeWitness.metadata.source
      reindexShift).mp translatedDirect

/-- For equal translated noncarrier centers, an oblique second terminal
forces the first route's prefix to be a singleton. -/
theorem
    FinalGaugedFlatRouteMacrocellWitness.first_routePrefix_length_eq_one_of_translatedCenters_eq_of_second_finalSegment_not_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstTaggedRoute secondTaggedRoute : List Cell × Nat}
    (first :
      FinalGaugedFlatRouteMacrocellWitness
        formula firstTaggedRoute)
    (second :
      FinalGaugedFlatRouteMacrocellWitness
        formula secondTaggedRoute)
    (centersEqual :
      first.translatedCenter = second.translatedCenter)
    (secondLength : 2 ≤ secondTaggedRoute.1.length)
    {secondTarget : Cell}
    (secondLast :
      secondTaggedRoute.1.getLast? = some secondTarget)
    (secondFinalSegmentNotAxisAligned :
      ¬(⟨polylineLastEntrance secondTaggedRoute.1,
          secondTarget⟩ : GridSegment).IsAxisAligned) :
    firstTaggedRoute.1.dropLast.length = 1 := by
  have secondDirect :=
    second.component_isDirect_of_finalSegment_not_axisAligned
      formula wellFormed degree isLocal
      secondLength secondLast secondFinalSegmentNotAxisAligned
  have firstDirect :=
    first.first_component_isDirect_of_translatedCenters_eq
      formula wellFormed degree isLocal
      second centersEqual secondDirect
  exact
    first.toFinalGaugedFlatRouteOccurrenceWitness
      |>.routePrefix_length_eq_one_of_direct
        formula wellFormed degree isLocal firstDirect

end PeriodicOrthocrossing

namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every directed noncarrier source-prefix/fan cross is complete.  Distinct
translated centers use macrocell rectangles.  At an equal center, either the
fan terminal is axis-aligned or its obliqueness forces the source prefix into
the direct-component singleton branch. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_noncarrierMacrocells
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈
          PeriodicOrthocrossing.retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {factor : Nat} (factorGreaterThanOne : 1 < factor)
    (clearance :
      845 <
        retainedTerminalFanTotalRefinement * factor)
    {sourceRoute fanRoute : List Cell}
    {sourceIndex fanIndex : Nat}
    {sourcePoint fanCenter : Cell}
    (sourceMember :
      (sourceRoute, sourceIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (fanMember :
      (fanRoute, fanIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (sourceLength : 2 ≤ sourceRoute.length)
    (fanLength : 2 ≤ fanRoute.length)
    (indicesDifferent : sourceIndex ≠ fanIndex)
    (headsDifferent : sourceRoute.head? ≠ fanRoute.head?)
    (sourceHead : sourceRoute.head? = some sourcePoint)
    (fanLast : fanRoute.getLast? = some fanCenter)
    (sourceNeCenter : sourcePoint ≠ fanCenter)
    (sourceTerminal fanTerminal : RetainedTerminalData)
    (sourceSlot fanSlot : RetainedTerminalSlot)
    (sourceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector sourceRoute) =
        some sourceTerminal)
    (fanClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector fanRoute) =
        some fanTerminal)
    (sourceMacrocell :
      PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
        formula (sourceRoute, sourceIndex))
    (fanMacrocell :
      PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
        formula (fanRoute, fanIndex))
    (fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor sourceRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor sourceTerminal)
          sourceSlot)
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor fanRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor fanTerminal)
          fanSlot)) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor sourceRoute)).dropLast
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale factor fanCenter))
        (scaleRetainedTerminalData factor fanTerminal)
        fanSlot) := by
  by_cases centersDifferent :
      sourceMacrocell.translatedCenter ≠
        fanMacrocell.translatedCenter
  · exact
      retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_flatRouteMacrocellCenters_ne
        formula wellFormed degree isLocal clausesNonempty
        factorGreaterThanOne clearance
        sourceMember fanMember sourceLength fanLength
        indicesDifferent sourceHead fanLast sourceNeCenter
        fanTerminal fanSlot fanClassified
        sourceMacrocell fanMacrocell centersDifferent
  · have centersEqual :
        sourceMacrocell.translatedCenter =
          fanMacrocell.translatedCenter :=
      not_ne_iff.mp centersDifferent
    by_cases fanAligned :
        (⟨polylineLastEntrance fanRoute, fanCenter⟩ :
          GridSegment).IsAxisAligned
    · have separated :=
        retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_singleton_or_axisAligned
          formula wellFormed degree isLocal clausesNonempty
          factorGreaterThanOne
          sourceMember fanMember sourceLength fanLength
          indicesDifferent headsDifferent sourceHead fanLast
          sourceNeCenter
          sourceTerminal fanTerminal sourceSlot fanSlot
          sourceClassified fanClassified
          (Or.inr fanAligned) fansAvoid
      have fanLastD :
          fanRoute.getLastD (0, 0) = fanCenter := by
        simp [List.getLastD_eq_getLast?, fanLast]
      rw [scalePolyline_getLastD, fanLastD] at separated
      exact separated
    · have sourceSingleton :=
        sourceMacrocell
          |>.first_routePrefix_length_eq_one_of_translatedCenters_eq_of_second_finalSegment_not_axisAligned
            formula wellFormed degree isLocal
            fanMacrocell centersEqual fanLength fanLast fanAligned
      have separated :=
        retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_singleton_or_axisAligned
          formula wellFormed degree isLocal clausesNonempty
          factorGreaterThanOne
          sourceMember fanMember sourceLength fanLength
          indicesDifferent headsDifferent sourceHead fanLast
          sourceNeCenter
          sourceTerminal fanTerminal sourceSlot fanSlot
          sourceClassified fanClassified
          (Or.inl sourceSingleton) fansAvoid
      have fanLastD :
          fanRoute.getLastD (0, 0) = fanCenter := by
        simp [List.getLastD_eq_getLast?, fanLast]
      rw [scalePolyline_getLastD, fanLastD] at separated
      exact separated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
