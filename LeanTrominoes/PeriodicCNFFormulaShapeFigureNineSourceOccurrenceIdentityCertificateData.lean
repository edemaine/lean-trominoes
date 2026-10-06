/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.DirectedClauseProfileSecondLiteralCheck
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceMetadata

/-! # Equality of occurrence-local identities and global source coordinates -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open FormulaShapeRetainedFigureNineSourceTail

def sourceOccurrencePrefixCoordinates (routePrefix : Descriptor) : Nat × Nat :=
  let query := routePrefix.localQuery
  let drawing := PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile query.1
  let incidence := drawing.incidenceAt query.2
  let arity := ((drawing.formula[incidence.clauseIndex]?).map
    (fun clause => clause.literals.length)).getD 0
  (incidence.clauseIndex,
    match arity with
    | 2 => if incidence.literalIndex = 0 then 1 else 0
    | 3 => if incidence.literalIndex = 0 then 1 else
        if incidence.literalIndex = 1 then 2 else 0
    | _ => incidence.literalIndex)

def sourceOccurrencePrefixAtCoordinates (profile : DirectedClauseProfile)
    (coordinates : Nat × Nat) : Descriptor :=
  let ordered := orderedDirectedProfile profile
  let profiles := figureClauseProfiles ordered
  let skipped := ((profiles.take coordinates.1).map (fun clause => clause.literals.length)).sum
  let count := ((profiles[coordinates.1]?).map (fun clause => clause.literals.length)).getD 0
  (FormulaShapeFigureNineFinalClauseOrdering.reorderList
    (((clauseDescriptors ordered).drop skipped).take count)).getD coordinates.2 default

/-- A genuine header prefix is recovered from its clause and literal indices. -/
def sourcePrefixRoundtripCheck (profile : DirectedClauseProfile) : Bool :=
  (sourceClauseHeaders profile).all fun header => decide (
    let coordinates := ((headerTemplateCoordinate header).clauseIndex,
      header.polarity.indexed.sourceLiteralIndex)
    sourceOccurrencePrefixCoordinates header.figurePrefix = coordinates ∧
      sourceOccurrencePrefixAtCoordinates profile coordinates = header.figurePrefix)

end LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
