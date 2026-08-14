/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalPositions

/-!
# Data-only global positions for the planar 3DM assembly

The certified routing record carries endpoint and orthogonality proofs, but
assembled vertex positions inspect only its variable and clause origins.
These definitions expose that proof-free interface explicitly.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

def assembledTriplePositionData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) :
    Triple Variable → Cell
  | triple@(.ordinary atom slot _ _) =>
      Cell.add (variableOrigin atom)
        (placeVariableModulePoint
          (occurrenceVariableSiteSlot slot)
          (orientedTripleLocalPosition source triple))
  | triple@(.fixedRed atom slot _) =>
      Cell.add (variableOrigin atom)
        (placeVariableModulePoint
          (occurrenceVariableSiteSlot slot)
          (orientedTripleLocalPosition source triple))
  | triple@(.clause clauseIndex _) =>
      Cell.add (clauseOrigin clauseIndex)
        (orientedTripleLocalPosition source triple)

def assembledRedElementPositionData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) :
    RedElement Variable → Cell
  | .cycleLink atom slot =>
      Cell.add (variableOrigin atom)
        (variableCycleLinkPosition
          (occurrenceVariableSiteSlot slot))
  | .fixedRedInternal atom slot element =>
      Cell.add (variableOrigin atom)
        (fixedRedInternalSitePosition source atom slot
          (fixedRedInternalRedLocalElement element))
  | element@(.clauseInternal clauseIndex) =>
      Cell.add (clauseOrigin clauseIndex)
        (redClauseElementLocalPosition element)
  | element@(.clauseTerminal clauseIndex _) =>
      Cell.add (clauseOrigin clauseIndex)
        (redClauseElementLocalPosition element)

def assembledGreenElementPositionData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) :
    GreenElement Variable → Cell
  | .ordinaryInternal atom slot element =>
      Cell.add (variableOrigin atom)
        (ordinaryInternalSitePosition source atom slot element)
  | .fixedRedInternal atom slot element =>
      Cell.add (variableOrigin atom)
        (fixedRedInternalSitePosition source atom slot
          (fixedRedInternalGreenLocalElement element))
  | element@(.clauseInternal clauseIndex) =>
      Cell.add (clauseOrigin clauseIndex)
        (greenClauseElementLocalPosition element)
  | element@(.clauseTerminal clauseIndex _) =>
      Cell.add (clauseOrigin clauseIndex)
        (greenClauseElementLocalPosition element)

def assembledBlueElementPositionData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) :
    BlueElement Variable → Cell
  | .ordinaryInternal atom slot element =>
      Cell.add (variableOrigin atom)
        (ordinaryInternalSitePosition source atom slot element)
  | .fixedRedInternal atom slot element =>
      Cell.add (variableOrigin atom)
        (fixedRedInternalSitePosition source atom slot
          (fixedRedInternalBlueLocalElement element))
  | element@(.clauseInternal clauseIndex) =>
      Cell.add (clauseOrigin clauseIndex)
        (blueClauseElementLocalPosition element)
  | element@(.clauseTerminal clauseIndex _) =>
      Cell.add (clauseOrigin clauseIndex)
        (blueClauseElementLocalPosition element)

def assembledVertexPositionsData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) : List Cell :=
  (triples source).map
      (assembledTriplePositionData source variableOrigin clauseOrigin) ++
    (redElements source).map
      (assembledRedElementPositionData source variableOrigin clauseOrigin) ++
    (greenElements source).map
      (assembledGreenElementPositionData source variableOrigin clauseOrigin) ++
    (blueElements source).map
      (assembledBlueElementPositionData source variableOrigin clauseOrigin)

theorem assembledVertexPositionsData_eq_routing
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    assembledVertexPositionsData source routing.variableOrigin
        routing.clauseOrigin =
      assembledVertexPositions routing := by
  rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
