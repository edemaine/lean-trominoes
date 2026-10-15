/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computation.Encoding.Finite.FiniteBoolCheck
import LeanTrominoes.SAT.CNF.FormulaShape.Final.PeriodicCNFFormulaShapeFigureNineFinalClauseOrderingSemantics
import LeanTrominoes.SAT.CNF.FormulaShape.Route.PeriodicCNFFormulaShapeFigureNineRoutePrefixLocalDirectionSemantics
import LeanTrominoes.SAT.CNF.PeriodicCNFClauseProfilePolarityIndexedRouteOperationSemantics
import LeanTrominoes.SAT.CNF.FormulaShape.Polarity.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailPairs

/-! # Presentation coordinates selected by final Figure 9 headers -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open ClauseProfilePolarityRouteOperation
open FormulaShapeDirectionOrdering
open FormulaShapeFigureNineFinalClauseOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open PlanarOneInThreeNoUnitsFigureNine

/-- The polarity operation and original template incidence coordinates
selected by one final Figure 9 route header. -/
structure HeaderTemplateCoordinate where
  polarity : IndexedDescriptor
  clauseIndex : Nat
  literalIndex : Nat
  deriving DecidableEq

/-- Read a header's exact clause-major, literal-minor template coordinates. -/
def headerTemplateCoordinate (header : Header) : HeaderTemplateCoordinate :=
  let query := header.figurePrefix.localQuery
  let incidence :=
    (templateDrawingOfClauseProfile query.1).incidenceAt query.2
  ⟨header.polarity.indexed, incidence.clauseIndex, incidence.literalIndex⟩

/-- The coordinate schedule obtained directly from the finite template,
including the final within-clause clockwise permutation. -/
def expectedSourceClauseHeaderTemplateCoordinates
    (profile : DirectedClauseProfile) : List HeaderTemplateCoordinate :=
  let ordered := orderedDirectedProfile profile
  let drawing := templateDrawingOfClauseProfile (clauseProfile ordered)
  drawing.formula.zipIdx.flatMap fun taggedClause =>
    let generatedProfile := embeddedClauseProfile taggedClause.1
    let sourceOrder :=
      reorderList (List.range taggedClause.1.literals.length)
    (ClauseProfilePolarityRouteOperation.descriptors
      (reorderProfile generatedProfile)).map fun polarity =>
        ⟨polarity.indexed, taggedClause.2,
          sourceOrder.getD (sourceSlotNat polarity.sourceSlot) 0⟩

/-- The parent local-query profile together with the existing operation and
template incidence coordinates selected by one final Figure 9 header. -/
structure HeaderTemplateProfileCoordinate where
  profile : UnaryProgramClauseProfile.ClauseProfile
  coordinate : HeaderTemplateCoordinate
  deriving DecidableEq

/-- Read the profile-qualified finite coordinate of one header. -/
def headerTemplateProfileCoordinate
    (header : Header) : HeaderTemplateProfileCoordinate :=
  ⟨header.figurePrefix.localQuery.1,
    headerTemplateCoordinate header⟩

/-- Profile-qualified coordinate block prescribed by one directed source
clause before Figure 9 expansion. -/
def expectedSourceClauseHeaderTemplateProfileCoordinates
    (profile : DirectedClauseProfile) :
    List HeaderTemplateProfileCoordinate :=
  (expectedSourceClauseHeaderTemplateCoordinates profile).map fun coordinate =>
    ⟨clauseProfile (orderedDirectedProfile profile), coordinate⟩

/-- Check both coordinate columns for one directed source profile. -/
def sourceHeaderCoordinatesCheck (profile : DirectedClauseProfile) : Bool :=
  decide ((sourceClauseHeaders profile).map headerTemplateCoordinate =
    expectedSourceClauseHeaderTemplateCoordinates profile) &&
  decide ((sourceClauseHeaders profile).map headerTemplateProfileCoordinate =
    expectedSourceClauseHeaderTemplateProfileCoordinates profile)

/-- Fix the first literal and direction, then enumerate all remaining slots. -/
def firstSourceHeaderCoordinatesCheck
    (first : UnaryProgramClauseProfile.LiteralProfile)
    (direction : AxisDirection) : Bool :=
  sourceHeaderCoordinatesCheck (.unary first direction) &&
    finiteAll fun second : UnaryProgramClauseProfile.LiteralProfile × AxisDirection =>
      sourceHeaderCoordinatesCheck (.binary first direction second.1 second.2) &&
        finiteAll fun third : UnaryProgramClauseProfile.LiteralProfile × AxisDirection =>
          sourceHeaderCoordinatesCheck
            (.ternary first direction second.1 second.2 third.1 third.2)

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
