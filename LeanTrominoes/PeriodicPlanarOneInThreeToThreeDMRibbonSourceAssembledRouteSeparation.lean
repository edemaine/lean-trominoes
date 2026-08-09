import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreRouteSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseCoreRouteSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRouteSeparation

/-!
# Separation of complete assembled source routes

Each assembled typed incidence route is its translated finite core, possibly
joined to one complete coordinated occurrence-route suffix.  This file
separates all four component pairings and packages them into an all-pairs
continuous interior-separation theorem for distinct colored typed incidences.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOneInThreePolarityNormalization

/-- The finite variable-site or clause-core prefix underlying an assembled
typed incidence, before its optional routed occurrence suffix is attached. -/
def assembledTypedIncidenceCoreRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (triple : {triple : Triple Variable // triple ∈ triples source})
    (color : WireColor) : List Cell :=
  match tripleEq : triple.1 with
  | .ordinary atom slot variant localTriple =>
      let member :
          Triple.ordinary atom slot variant localTriple ∈ triples source :=
        tripleEq ▸ triple.2
      assembledOrdinaryPrefix routing atom slot variant localTriple
        member color
  | .fixedRed atom slot localTriple =>
      let member :
          Triple.fixedRed atom slot localTriple ∈ triples source :=
        tripleEq ▸ triple.2
      assembledFixedRedPrefix routing atom slot localTriple member color
  | .clause clauseIndex set =>
      assembledClauseRoute routing clauseIndex set color

/-- The core selector reduces to the translated ordinary prefix. -/
theorem assembledTypedIncidenceCoreRoute_eq_ordinary
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (triple : {triple : Triple Variable // triple ∈ triples source})
    (color : WireColor)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (tripleEq : triple.1 =
      .ordinary atom slot variant localTriple) :
    assembledTypedIncidenceCoreRoute routing triple color =
      assembledOrdinaryPrefix routing atom slot variant localTriple
        (tripleEq ▸ triple.2) color := by
  rcases triple with ⟨triple, member⟩
  cases tripleEq
  rfl

/-- The core selector reduces to the translated fixed-red prefix. -/
theorem assembledTypedIncidenceCoreRoute_eq_fixedRed
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (triple : {triple : Triple Variable // triple ∈ triples source})
    (color : WireColor)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (tripleEq : triple.1 = .fixedRed atom slot localTriple) :
    assembledTypedIncidenceCoreRoute routing triple color =
      assembledFixedRedPrefix routing atom slot localTriple
        (tripleEq ▸ triple.2) color := by
  rcases triple with ⟨triple, member⟩
  cases tripleEq
  rfl

/-- The core selector reduces to the translated clause-core route. -/
theorem assembledTypedIncidenceCoreRoute_eq_clause
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (triple : {triple : Triple Variable // triple ∈ triples source})
    (color : WireColor)
    (clauseIndex : Nat) (set : X3CClauseSet)
    (tripleEq : triple.1 = .clause clauseIndex set) :
    assembledTypedIncidenceCoreRoute routing triple color =
      assembledClauseRoute routing clauseIndex set color := by
  rcases triple with ⟨triple, member⟩
  cases tripleEq
  rfl

/-- Distinct colored typed incidences have fully endpoint-aware separated
finite cores, including pairs housed in the same finite gadget. -/
theorem assembledTypedIncidenceCoreRoutes_avoidEachOther
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
    (firstColor secondColor : WireColor)
    (different : (first.1, firstColor) ≠ (second.1, secondColor)) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing first firstColor)
      (assembledTypedIncidenceCoreRoute routing second secondColor) := by
  dsimp only
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  cases first with
  | mk first firstMember =>
    cases second with
    | mk second secondMember =>
      cases first with
      | ordinary firstAtom firstSlot firstVariant firstLocal =>
          cases second with
          | ordinary secondAtom secondSlot secondVariant secondLocal =>
              let firstLocation := ordinaryTriple_location source.erase
                firstAtom firstSlot firstVariant firstLocal firstMember
              let secondLocation := ordinaryTriple_location source.erase
                secondAtom secondSlot secondVariant secondLocal secondMember
              by_cases atomsEq : firstAtom = secondAtom
              · subst secondAtom
                have keysDifferent :
                    (activeVariableSiteTriple source.erase firstAtom
                        firstLocation.1 firstSlot firstLocation.2.1
                        (.ordinary firstAtom firstSlot firstVariant firstLocal)
                        firstLocation.2.2,
                      firstColor) ≠
                    (activeVariableSiteTriple source.erase firstAtom
                        secondLocation.1 secondSlot secondLocation.2.1
                        (.ordinary firstAtom secondSlot secondVariant secondLocal)
                        secondLocation.2.2,
                      secondColor) := by
                  intro keysEq
                  apply different
                  rcases Prod.mk.inj keysEq with
                    ⟨activeEq, colorEq⟩
                  apply Prod.ext
                  · congr 1
                    have underlyingEq := congrArg Subtype.val activeEq
                    cases firstSlot <;> cases secondSlot <;>
                      cases firstVariant <;> cases secondVariant <;>
                      cases firstLocal <;> cases secondLocal <;>
                      simp_all [activeVariableSiteTriple,
                        variableSiteTripleOfTyped,
                        occurrenceVariableSiteSlot]
                  · exact colorEq
                exact (by
                  simpa [assembledTypedIncidenceCoreRoute,
                    assembledOrdinaryPrefix, typedVariableSiteRoute,
                    firstLocation, secondLocation, routing,
                    coordinatedSourceRibbonThreeStrandRouting,
                    RibbonEndpointFanSystem.threeStrandRouting] using
                    translatedTypedVariableSiteRoutes_avoidEachOther
                      source.erase firstAtom firstLocation.1
                      firstSlot firstLocation.2.1
                      (.ordinary firstAtom firstSlot firstVariant firstLocal)
                      firstLocation.2.2 firstColor
                      secondSlot secondLocation.2.1
                      (.ordinary firstAtom secondSlot secondVariant secondLocal)
                      secondLocation.2.2 secondColor keysDifferent
                      (constructedVariableOrigin placement
                        standardThreeStrandLayout firstAtom))
              · exact RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther (by
                  simpa [assembledTypedIncidenceCoreRoute,
                    assembledOrdinaryPrefix, typedVariableSiteRoute,
                    firstLocation, secondLocation, routing,
                    coordinatedSourceRibbonThreeStrandRouting,
                    RibbonEndpointFanSystem.threeStrandRouting] using
                    constructedVariableSiteRoutes_strictlyAvoidEachOther_of_atoms_ne
                      presentation.toPlanarIncidencePresentation anchorsZero
                      firstAtom secondAtom firstLocation.1 secondLocation.1
                      atomsEq
                      (activeVariableSiteTriple source.erase firstAtom
                        firstLocation.1 firstSlot firstLocation.2.1
                        (.ordinary firstAtom firstSlot firstVariant firstLocal)
                        firstLocation.2.2)
                      firstColor
                      (activeVariableSiteTriple source.erase secondAtom
                        secondLocation.1 secondSlot secondLocation.2.1
                        (.ordinary secondAtom secondSlot secondVariant secondLocal)
                        secondLocation.2.2)
                      secondColor)
          | fixedRed secondAtom secondSlot secondLocal =>
              let firstLocation := ordinaryTriple_location source.erase
                firstAtom firstSlot firstVariant firstLocal firstMember
              let secondLocation := fixedRedTriple_location source.erase
                secondAtom secondSlot secondLocal secondMember
              by_cases atomsEq : firstAtom = secondAtom
              · subst secondAtom
                have keysDifferent :
                    (activeVariableSiteTriple source.erase firstAtom
                        firstLocation.1 firstSlot firstLocation.2.1
                        (.ordinary firstAtom firstSlot firstVariant firstLocal)
                        firstLocation.2.2,
                      firstColor) ≠
                    (activeVariableSiteTriple source.erase firstAtom
                        secondLocation.1 secondSlot secondLocation.2.1
                        (.fixedRed firstAtom secondSlot secondLocal)
                        secondLocation.2.2,
                      secondColor) := by
                  intro keysEq
                  have activeEq := congrArg (fun key => key.1) keysEq
                  have underlyingEq := congrArg Subtype.val activeEq
                  simp [activeVariableSiteTriple,
                    variableSiteTripleOfTyped] at underlyingEq
                exact (by
                  simpa [assembledTypedIncidenceCoreRoute,
                    assembledOrdinaryPrefix, assembledFixedRedPrefix,
                    typedVariableSiteRoute, firstLocation, secondLocation,
                    routing, coordinatedSourceRibbonThreeStrandRouting,
                    RibbonEndpointFanSystem.threeStrandRouting] using
                    translatedTypedVariableSiteRoutes_avoidEachOther
                      source.erase firstAtom firstLocation.1
                      firstSlot firstLocation.2.1
                      (.ordinary firstAtom firstSlot firstVariant firstLocal)
                      firstLocation.2.2 firstColor
                      secondSlot secondLocation.2.1
                      (.fixedRed firstAtom secondSlot secondLocal)
                      secondLocation.2.2 secondColor keysDifferent
                      (constructedVariableOrigin placement
                        standardThreeStrandLayout firstAtom))
              · exact RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther (by
                  simpa [assembledTypedIncidenceCoreRoute,
                    assembledOrdinaryPrefix, assembledFixedRedPrefix,
                    typedVariableSiteRoute, firstLocation, secondLocation,
                    routing, coordinatedSourceRibbonThreeStrandRouting,
                    RibbonEndpointFanSystem.threeStrandRouting] using
                    constructedVariableSiteRoutes_strictlyAvoidEachOther_of_atoms_ne
                      presentation.toPlanarIncidencePresentation anchorsZero
                      firstAtom secondAtom firstLocation.1 secondLocation.1
                      atomsEq
                      (activeVariableSiteTriple source.erase firstAtom
                        firstLocation.1 firstSlot firstLocation.2.1
                        (.ordinary firstAtom firstSlot firstVariant firstLocal)
                        firstLocation.2.2)
                      firstColor
                      (activeVariableSiteTriple source.erase secondAtom
                        secondLocation.1 secondSlot secondLocation.2.1
                        (.fixedRed secondAtom secondSlot secondLocal)
                        secondLocation.2.2)
                      secondColor)
          | clause secondIndex secondSet =>
              let firstLocation := ordinaryTriple_location source.erase
                firstAtom firstSlot firstVariant firstLocal firstMember
              have secondDeclared :=
                tripleMacrocellOwner_declared source.erase
                  (.clause secondIndex secondSet) secondMember
              have secondIndexLt : secondIndex < source.clauses.length := by
                simpa [tripleMacrocellOwner,
                  AssemblyMacrocellOwner.IsDeclared,
                  PositionedPeriodicCNF.erase] using secondDeclared
              exact RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther (by
                simpa [assembledTypedIncidenceCoreRoute,
                  assembledOrdinaryPrefix, typedVariableSiteRoute,
                  assembledClauseRoute, orientedIncidenceLocalRoute,
                  firstLocation, routing,
                  coordinatedSourceRibbonThreeStrandRouting,
                  RibbonEndpointFanSystem.threeStrandRouting] using
                  constructedVariableSiteRoute_strictlyAvoids_clauseRoute
                    presentation.toPlanarIncidencePresentation anchorsZero
                    firstAtom firstLocation.1
                    (activeVariableSiteTriple source.erase firstAtom
                      firstLocation.1 firstSlot firstLocation.2.1
                      (.ordinary firstAtom firstSlot firstVariant firstLocal)
                      firstLocation.2.2)
                    firstColor secondIndex secondIndexLt secondSet secondColor)
      | fixedRed firstAtom firstSlot firstLocal =>
          cases second with
          | ordinary secondAtom secondSlot secondVariant secondLocal =>
              let firstLocation := fixedRedTriple_location source.erase
                firstAtom firstSlot firstLocal firstMember
              let secondLocation := ordinaryTriple_location source.erase
                secondAtom secondSlot secondVariant secondLocal secondMember
              by_cases atomsEq : firstAtom = secondAtom
              · subst secondAtom
                have keysDifferent :
                    (activeVariableSiteTriple source.erase firstAtom
                        firstLocation.1 firstSlot firstLocation.2.1
                        (.fixedRed firstAtom firstSlot firstLocal)
                        firstLocation.2.2,
                      firstColor) ≠
                    (activeVariableSiteTriple source.erase firstAtom
                        secondLocation.1 secondSlot secondLocation.2.1
                        (.ordinary firstAtom secondSlot secondVariant secondLocal)
                        secondLocation.2.2,
                      secondColor) := by
                  intro keysEq
                  have activeEq := congrArg (fun key => key.1) keysEq
                  have underlyingEq := congrArg Subtype.val activeEq
                  simp [activeVariableSiteTriple,
                    variableSiteTripleOfTyped] at underlyingEq
                exact (by
                  simpa [assembledTypedIncidenceCoreRoute,
                    assembledOrdinaryPrefix, assembledFixedRedPrefix,
                    typedVariableSiteRoute, firstLocation, secondLocation,
                    routing, coordinatedSourceRibbonThreeStrandRouting,
                    RibbonEndpointFanSystem.threeStrandRouting] using
                    translatedTypedVariableSiteRoutes_avoidEachOther
                      source.erase firstAtom firstLocation.1
                      firstSlot firstLocation.2.1
                      (.fixedRed firstAtom firstSlot firstLocal)
                      firstLocation.2.2 firstColor
                      secondSlot secondLocation.2.1
                      (.ordinary firstAtom secondSlot secondVariant secondLocal)
                      secondLocation.2.2 secondColor keysDifferent
                      (constructedVariableOrigin placement
                        standardThreeStrandLayout firstAtom))
              · exact RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther (by
                  simpa [assembledTypedIncidenceCoreRoute,
                    assembledOrdinaryPrefix, assembledFixedRedPrefix,
                    typedVariableSiteRoute, firstLocation, secondLocation,
                    routing, coordinatedSourceRibbonThreeStrandRouting,
                    RibbonEndpointFanSystem.threeStrandRouting] using
                    constructedVariableSiteRoutes_strictlyAvoidEachOther_of_atoms_ne
                      presentation.toPlanarIncidencePresentation anchorsZero
                      firstAtom secondAtom firstLocation.1 secondLocation.1
                      atomsEq
                      (activeVariableSiteTriple source.erase firstAtom
                        firstLocation.1 firstSlot firstLocation.2.1
                        (.fixedRed firstAtom firstSlot firstLocal)
                        firstLocation.2.2)
                      firstColor
                      (activeVariableSiteTriple source.erase secondAtom
                        secondLocation.1 secondSlot secondLocation.2.1
                        (.ordinary secondAtom secondSlot secondVariant secondLocal)
                        secondLocation.2.2)
                      secondColor)
          | fixedRed secondAtom secondSlot secondLocal =>
              let firstLocation := fixedRedTriple_location source.erase
                firstAtom firstSlot firstLocal firstMember
              let secondLocation := fixedRedTriple_location source.erase
                secondAtom secondSlot secondLocal secondMember
              by_cases atomsEq : firstAtom = secondAtom
              · subst secondAtom
                have keysDifferent :
                    (activeVariableSiteTriple source.erase firstAtom
                        firstLocation.1 firstSlot firstLocation.2.1
                        (.fixedRed firstAtom firstSlot firstLocal)
                        firstLocation.2.2,
                      firstColor) ≠
                    (activeVariableSiteTriple source.erase firstAtom
                        secondLocation.1 secondSlot secondLocation.2.1
                        (.fixedRed firstAtom secondSlot secondLocal)
                        secondLocation.2.2,
                      secondColor) := by
                  intro keysEq
                  apply different
                  rcases Prod.mk.inj keysEq with
                    ⟨activeEq, colorEq⟩
                  apply Prod.ext
                  · congr 1
                    have underlyingEq := congrArg Subtype.val activeEq
                    cases firstSlot <;> cases secondSlot <;>
                      cases firstLocal <;> cases secondLocal <;>
                      simp_all [activeVariableSiteTriple,
                        variableSiteTripleOfTyped,
                        occurrenceVariableSiteSlot]
                  · exact colorEq
                exact (by
                  simpa [assembledTypedIncidenceCoreRoute,
                    assembledFixedRedPrefix, typedVariableSiteRoute,
                    firstLocation, secondLocation, routing,
                    coordinatedSourceRibbonThreeStrandRouting,
                    RibbonEndpointFanSystem.threeStrandRouting] using
                    translatedTypedVariableSiteRoutes_avoidEachOther
                      source.erase firstAtom firstLocation.1
                      firstSlot firstLocation.2.1
                      (.fixedRed firstAtom firstSlot firstLocal)
                      firstLocation.2.2 firstColor
                      secondSlot secondLocation.2.1
                      (.fixedRed firstAtom secondSlot secondLocal)
                      secondLocation.2.2 secondColor keysDifferent
                      (constructedVariableOrigin placement
                        standardThreeStrandLayout firstAtom))
              · exact RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther (by
                  simpa [assembledTypedIncidenceCoreRoute,
                    assembledFixedRedPrefix, typedVariableSiteRoute,
                    firstLocation, secondLocation, routing,
                    coordinatedSourceRibbonThreeStrandRouting,
                    RibbonEndpointFanSystem.threeStrandRouting] using
                    constructedVariableSiteRoutes_strictlyAvoidEachOther_of_atoms_ne
                      presentation.toPlanarIncidencePresentation anchorsZero
                      firstAtom secondAtom firstLocation.1 secondLocation.1
                      atomsEq
                      (activeVariableSiteTriple source.erase firstAtom
                        firstLocation.1 firstSlot firstLocation.2.1
                        (.fixedRed firstAtom firstSlot firstLocal)
                        firstLocation.2.2)
                      firstColor
                      (activeVariableSiteTriple source.erase secondAtom
                        secondLocation.1 secondSlot secondLocation.2.1
                        (.fixedRed secondAtom secondSlot secondLocal)
                        secondLocation.2.2)
                      secondColor)
          | clause secondIndex secondSet =>
              let firstLocation := fixedRedTriple_location source.erase
                firstAtom firstSlot firstLocal firstMember
              have secondDeclared :=
                tripleMacrocellOwner_declared source.erase
                  (.clause secondIndex secondSet) secondMember
              have secondIndexLt : secondIndex < source.clauses.length := by
                simpa [tripleMacrocellOwner,
                  AssemblyMacrocellOwner.IsDeclared,
                  PositionedPeriodicCNF.erase] using secondDeclared
              exact RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther (by
                simpa [assembledTypedIncidenceCoreRoute,
                  assembledFixedRedPrefix, typedVariableSiteRoute,
                  assembledClauseRoute, orientedIncidenceLocalRoute,
                  firstLocation, routing,
                  coordinatedSourceRibbonThreeStrandRouting,
                  RibbonEndpointFanSystem.threeStrandRouting] using
                  constructedVariableSiteRoute_strictlyAvoids_clauseRoute
                    presentation.toPlanarIncidencePresentation anchorsZero
                    firstAtom firstLocation.1
                    (activeVariableSiteTriple source.erase firstAtom
                      firstLocation.1 firstSlot firstLocation.2.1
                      (.fixedRed firstAtom firstSlot firstLocal)
                      firstLocation.2.2)
                    firstColor secondIndex secondIndexLt secondSet secondColor)
      | clause firstIndex firstSet =>
          have firstDeclared :=
            tripleMacrocellOwner_declared source.erase
              (.clause firstIndex firstSet) firstMember
          have firstIndexLt : firstIndex < source.clauses.length := by
            simpa [tripleMacrocellOwner,
              AssemblyMacrocellOwner.IsDeclared,
              PositionedPeriodicCNF.erase] using firstDeclared
          cases second with
          | ordinary secondAtom secondSlot secondVariant secondLocal =>
              let secondLocation := ordinaryTriple_location source.erase
                secondAtom secondSlot secondVariant secondLocal secondMember
              exact routesAvoidEachOther_comm
                (RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther (by
                simpa [assembledTypedIncidenceCoreRoute,
                  assembledOrdinaryPrefix, typedVariableSiteRoute,
                  assembledClauseRoute, orientedIncidenceLocalRoute,
                  secondLocation, routing,
                  coordinatedSourceRibbonThreeStrandRouting,
                  RibbonEndpointFanSystem.threeStrandRouting] using
                  constructedVariableSiteRoute_strictlyAvoids_clauseRoute
                    presentation.toPlanarIncidencePresentation anchorsZero
                    secondAtom secondLocation.1
                    (activeVariableSiteTriple source.erase secondAtom
                      secondLocation.1 secondSlot secondLocation.2.1
                      (.ordinary secondAtom secondSlot secondVariant secondLocal)
                      secondLocation.2.2)
                    secondColor firstIndex firstIndexLt firstSet firstColor))
          | fixedRed secondAtom secondSlot secondLocal =>
              let secondLocation := fixedRedTriple_location source.erase
                secondAtom secondSlot secondLocal secondMember
              exact routesAvoidEachOther_comm
                (RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther (by
                simpa [assembledTypedIncidenceCoreRoute,
                  assembledFixedRedPrefix, typedVariableSiteRoute,
                  assembledClauseRoute, orientedIncidenceLocalRoute,
                  secondLocation, routing,
                  coordinatedSourceRibbonThreeStrandRouting,
                  RibbonEndpointFanSystem.threeStrandRouting] using
                  constructedVariableSiteRoute_strictlyAvoids_clauseRoute
                    presentation.toPlanarIncidencePresentation anchorsZero
                    secondAtom secondLocation.1
                    (activeVariableSiteTriple source.erase secondAtom
                      secondLocation.1 secondSlot secondLocation.2.1
                      (.fixedRed secondAtom secondSlot secondLocal)
                      secondLocation.2.2)
                    secondColor firstIndex firstIndexLt firstSet firstColor))
          | clause secondIndex secondSet =>
              have secondDeclared :=
                tripleMacrocellOwner_declared source.erase
                  (.clause secondIndex secondSet) secondMember
              have secondIndexLt : secondIndex < source.clauses.length := by
                simpa [tripleMacrocellOwner,
                  AssemblyMacrocellOwner.IsDeclared,
                  PositionedPeriodicCNF.erase] using secondDeclared
              by_cases indicesEq : firstIndex = secondIndex
              · subst secondIndex
                have keysDifferent :
                    (firstSet, firstColor) ≠ (secondSet, secondColor) := by
                  intro keysEq
                  apply different
                  rcases Prod.mk.inj keysEq with ⟨setEq, colorEq⟩
                  cases setEq
                  cases colorEq
                  rfl
                exact (by
                  simpa [assembledTypedIncidenceCoreRoute, routing] using
                    assembledClauseRoutes_avoidEachOther routing firstIndex
                      firstSet secondSet firstColor secondColor keysDifferent)
              · exact RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther (by
                  simpa [assembledTypedIncidenceCoreRoute,
                    assembledClauseRoute, orientedIncidenceLocalRoute, routing,
                    coordinatedSourceRibbonThreeStrandRouting,
                    RibbonEndpointFanSystem.threeStrandRouting] using
                    constructedClauseRoutes_strictlyAvoidEachOther_of_indices_ne
                      presentation.toPlanarIncidencePresentation anchorsZero
                      firstIndex secondIndex firstIndexLt secondIndexLt indicesEq
                      firstSet secondSet firstColor secondColor)

/-- The endpoint-aware finite-core theorem in particular supplies the three
interior-contact fields used by continuous planarity. -/
theorem assembledTypedIncidenceCoreRoutes_avoidInteriors
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
    (firstColor secondColor : WireColor)
    (different : (first.1, firstColor) ≠ (second.1, secondColor)) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidInteriorContacts
      (assembledTypedIncidenceCoreRoute routing first firstColor)
      (assembledTypedIncidenceCoreRoute routing second secondColor) := by
  exact RoutesAvoidEachOther.toRoutesAvoidInteriorContacts
    (assembledTypedIncidenceCoreRoutes_avoidEachOther
      presentation anchorsZero width compatible first second
      firstColor secondColor different)

/-- Every assembled finite core avoids every complete coordinated source
occurrence route. -/
theorem assembledTypedIncidenceCoreRoute_avoids_coordinatedSourceRouteInteriors
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source.erase)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (routeColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidInteriorContacts
      (assembledTypedIncidenceCoreRoute
        routing coreTriple coreColor)
      (routing.route entry routeColor) := by
  dsimp only
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  rcases coreTriple with ⟨coreTriple, coreMember⟩
  cases coreTriple with
  | ordinary atom slot variant localTriple =>
      let location := ordinaryTriple_location source.erase
        atom slot variant localTriple coreMember
      let owner : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      simpa [assembledTypedIncidenceCoreRoute,
        assembledOrdinaryPrefix, typedVariableSiteRoute,
        location, owner, routing,
        coordinatedSourceRibbonThreeStrandRouting,
        RibbonEndpointFanSystem.threeStrandRouting] using
        constructedVariableSiteRoute_avoids_coordinatedSourceRibbonRouteInteriors
          presentation anchorsZero width normalized compatible owner entry
          (activeVariableSiteTriple source.erase atom location.1
            slot location.2.1
            (.ordinary atom slot variant localTriple) location.2.2)
          coreColor routeColor
  | fixedRed atom slot localTriple =>
      let location := fixedRedTriple_location source.erase
        atom slot localTriple coreMember
      let owner : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      simpa [assembledTypedIncidenceCoreRoute,
        assembledFixedRedPrefix, typedVariableSiteRoute,
        location, owner, routing,
        coordinatedSourceRibbonThreeStrandRouting,
        RibbonEndpointFanSystem.threeStrandRouting] using
        constructedVariableSiteRoute_avoids_coordinatedSourceRibbonRouteInteriors
          presentation anchorsZero width normalized compatible owner entry
          (activeVariableSiteTriple source.erase atom location.1
            slot location.2.1
            (.fixedRed atom slot localTriple) location.2.2)
          coreColor routeColor
  | clause clauseIndex set =>
      have declared :=
        tripleMacrocellOwner_declared source.erase
          (.clause clauseIndex set) coreMember
      have indexLt : clauseIndex < source.clauses.length := by
        simpa [tripleMacrocellOwner,
          AssemblyMacrocellOwner.IsDeclared,
          PositionedPeriodicCNF.erase] using declared
      exact RoutesAvoidEachOther.toRoutesAvoidInteriorContacts (by
        simpa [assembledTypedIncidenceCoreRoute, routing] using
          assembledClauseRoute_avoids_coordinatedSourceRibbonRoute
            presentation anchorsZero occurrences arity width compatible
            clauseIndex indexLt set coreColor entry routeColor)

/-- An assembled typed incidence is either its core alone or that core joined
at the certified variable port to one routed occurrence suffix. -/
theorem assembledTypedIncidenceRoute_eq_core_or_join
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (triple : {triple : Triple Variable // triple ∈ triples source})
    (color : WireColor) :
    assembledTypedIncidenceRoute routing triple color =
        assembledTypedIncidenceCoreRoute routing triple color ∨
      ∃ (entry : ActiveOccurrenceEntry source) (boundary : Cell),
        triple.1 =
            routedOccurrenceTriple source entry.1.1 entry.1.2 color ∧
          (assembledTypedIncidenceCoreRoute
            routing triple color).getLast? = some boundary ∧
          (routing.route entry color).head? = some boundary ∧
          assembledTypedIncidenceRoute routing triple color =
            joinAtEndpoint
              (assembledTypedIncidenceCoreRoute routing triple color)
              (routing.route entry color) := by
  unfold assembledTypedIncidenceRoute
  split
  next atom slot variant localTriple tripleEq =>
    let member :
        Triple.ordinary atom slot variant localTriple ∈ triples source :=
      tripleEq ▸ triple.2
    split
    next routed =>
      let location := ordinaryTriple_location source atom slot variant
        localTriple member
      let entry : ActiveOccurrenceEntry source :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      let boundary := Cell.add (routing.variableOrigin atom)
        (routedVariablePortPosition source entry color)
      right
      refine ⟨entry, boundary, tripleEq.trans routed, ?_, ?_, ?_⟩
      · rw [assembledTypedIncidenceCoreRoute_eq_ordinary
          routing triple color atom slot variant localTriple tripleEq]
        simpa [boundary, entry] using
          assembledOrdinaryPrefix_getLast_routed routing atom slot variant
            localTriple member color routed
      · simpa [boundary, entry] using (routing.routeEndpoints entry color).1
      · dsimp only
        rw [assembledTypedIncidenceCoreRoute_eq_ordinary
          routing triple color atom slot variant localTriple tripleEq]
    next notRouted =>
      left
      exact (assembledTypedIncidenceCoreRoute_eq_ordinary
        routing triple color atom slot variant localTriple tripleEq).symm
  next atom slot localTriple tripleEq =>
    let member :
        Triple.fixedRed atom slot localTriple ∈ triples source :=
      tripleEq ▸ triple.2
    split
    next routed =>
      let location := fixedRedTriple_location source atom slot
        localTriple member
      let entry : ActiveOccurrenceEntry source :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      let boundary := Cell.add (routing.variableOrigin atom)
        (routedVariablePortPosition source entry color)
      right
      refine ⟨entry, boundary, tripleEq.trans routed, ?_, ?_, ?_⟩
      · rw [assembledTypedIncidenceCoreRoute_eq_fixedRed
          routing triple color atom slot localTriple tripleEq]
        simpa [boundary, entry] using
          assembledFixedRedPrefix_getLast_routed routing atom slot
            localTriple member color routed
      · simpa [boundary, entry] using (routing.routeEndpoints entry color).1
      · dsimp only
        rw [assembledTypedIncidenceCoreRoute_eq_fixedRed
          routing triple color atom slot localTriple tripleEq]
    next notRouted =>
      left
      exact (assembledTypedIncidenceCoreRoute_eq_fixedRed
        routing triple color atom slot localTriple tripleEq).symm
  next clauseIndex set tripleEq =>
    left
    exact (assembledTypedIncidenceCoreRoute_eq_clause
      routing triple color clauseIndex set tripleEq).symm

/-- Every pair of distinct colored typed incidence routes in the coordinated
source assembly avoids all segment-interior contacts. -/
theorem coordinatedSourceAssembledTypedIncidenceRoutes_avoidInteriors
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source.erase)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (lengthGeThree :
      ∀ entry : ActiveOccurrenceEntry source.erase,
        3 ≤ (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry).length)
    (first second :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (firstColor secondColor : WireColor)
    (different : (first.1, firstColor) ≠ (second.1, secondColor)) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidInteriorContacts
      (assembledTypedIncidenceRoute routing first firstColor)
      (assembledTypedIncidenceRoute routing second secondColor) := by
  dsimp only
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  have coreAvoid :=
    assembledTypedIncidenceCoreRoutes_avoidInteriors
      presentation anchorsZero width compatible first second
      firstColor secondColor different
  have firstParts :=
    assembledTypedIncidenceRoute_eq_core_or_join
      routing first firstColor
  have secondParts :=
    assembledTypedIncidenceRoute_eq_core_or_join
      routing second secondColor
  rcases firstParts with firstCore | firstJoined
  · rcases secondParts with secondCore | secondJoined
    · rw [firstCore, secondCore]
      exact coreAvoid
    · rcases secondJoined with
        ⟨secondEntry, secondBoundary, secondTripleEq,
          secondCoreLast, secondRouteHead, secondJoined⟩
      have coreRouteAvoid :=
        assembledTypedIncidenceCoreRoute_avoids_coordinatedSourceRouteInteriors
          presentation anchorsZero occurrences arity width normalized compatible
          first firstColor secondEntry secondColor
      have joinedAvoid := coreAvoid.join_right coreRouteAvoid
        secondCoreLast secondRouteHead
      rw [firstCore, secondJoined]
      exact joinedAvoid
  · rcases firstJoined with
      ⟨firstEntry, firstBoundary, firstTripleEq,
        firstCoreLast, firstRouteHead, firstJoined⟩
    rcases secondParts with secondCore | secondJoined
    · have routeCoreAvoid :=
        (assembledTypedIncidenceCoreRoute_avoids_coordinatedSourceRouteInteriors
          presentation anchorsZero occurrences arity width normalized compatible
          second secondColor firstEntry firstColor).symm
      have joinedAvoid := coreAvoid.join_left routeCoreAvoid
        firstCoreLast firstRouteHead
      rw [firstJoined, secondCore]
      exact joinedAvoid
    · rcases secondJoined with
        ⟨secondEntry, secondBoundary, secondTripleEq,
          secondCoreLast, secondRouteHead, secondJoined⟩
      have firstCoreSecondRoute :=
        assembledTypedIncidenceCoreRoute_avoids_coordinatedSourceRouteInteriors
          presentation anchorsZero occurrences arity width normalized compatible
          first firstColor secondEntry secondColor
      have firstRouteSecondCore :=
        (assembledTypedIncidenceCoreRoute_avoids_coordinatedSourceRouteInteriors
          presentation anchorsZero occurrences arity width normalized compatible
          second secondColor firstEntry firstColor).symm
      have strandsDifferent :
          RibbonStrandsDifferent firstEntry firstColor
            secondEntry secondColor := by
        intro strandsEq
        apply different
        rcases Prod.mk.inj strandsEq with ⟨entryEq, colorEq⟩
        apply Prod.ext
        · rw [firstTripleEq, secondTripleEq, entryEq, colorEq]
        · exact colorEq
      have routeRouteAvoid :=
        RoutesStrictlyAvoidEachOther.toRoutesAvoidInteriorContacts
          (coordinatedSourceRibbonThreeStrandRoutes_strictlyAvoidEachOther
            presentation width compatible lengthGeThree strandsDifferent)
      have firstCoreSecondFull := coreAvoid.join_right
        firstCoreSecondRoute secondCoreLast secondRouteHead
      have firstRouteSecondFull := firstRouteSecondCore.join_right
        routeRouteAvoid secondCoreLast secondRouteHead
      have fullAvoid := firstCoreSecondFull.join_left
        firstRouteSecondFull firstCoreLast firstRouteHead
      rw [firstJoined, secondJoined]
      exact fullAvoid

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
