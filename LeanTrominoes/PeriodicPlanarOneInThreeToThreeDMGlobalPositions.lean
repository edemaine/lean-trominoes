/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMThreeStrandRouting

/-!
# Global vertex positions for the planar 3DM assembly

Given three-strand routing data, this file translates the checked finite
variable and clause templates into their reserved global neighborhoods.  It
defines positions for every typed triple and every typed colored element,
then emits them in exactly the vertex order of the encoded 3DM incidence
graph.

Separation and fundamental-square bounds are intentionally left to the
global geometric certificate.  This module establishes the deterministic
coordinate assignment and its list-order bookkeeping.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- Ordinary template selected at an occurrence slot.  The fallback is used
only on a fixed-red slot, where no ordinary internal element is listed. -/
def ordinaryVariantAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    VariableOccurrenceVariant :=
  match occurrenceConnectorKind source atom slot with
  | .fixedBlue => .fixedBlue
  | .fixedRed | .fixedGreen => .fixedGreen

/-- Local ordinary element represented by an assembled private internal
element. -/
def ordinaryInternalLocalElement :
    OrdinaryInternal → VariableOccurrenceElement
  | .cycleShared => .cycleShared
  | .auxiliaryShared => .auxiliaryShared

/-- Local fixed-red element represented by an assembled red internal
element. -/
def fixedRedInternalRedLocalElement :
    FixedRedInternalRed → FixedRedConnectorElement
  | .middleRung => .red .middleRung
  | .topAuxiliary => .red .topAuxiliary

/-- Local fixed-red element represented by an assembled green internal
element. -/
def fixedRedInternalGreenLocalElement :
    FixedRedInternalGreen → FixedRedConnectorElement
  | .leftRung => .green .leftRung
  | .topRightLink => .green .topRightLink
  | .bottomRightLink => .green .bottomRightLink

/-- Local fixed-red element represented by an assembled blue internal
element. -/
def fixedRedInternalBlueLocalElement :
    FixedRedInternalBlue → FixedRedConnectorElement
  | .topLeftLink => .blue .topLeftLink
  | .bottomLeftLink => .blue .bottomLeftLink
  | .rightRung => .blue .rightRung

/-- Relative position of an ordinary private element in its complete
variable-site drawing. -/
def ordinaryInternalSitePosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (element : OrdinaryInternal) : Cell :=
  placeVariableModulePoint
    (occurrenceVariableSiteSlot slot)
    ((VariableOccurrence.orientedBoundaryDrawing
      (ordinaryVariantAt source atom slot)
      (occurrencePolarity source atom slot)).elementPosition
        (ordinaryInternalLocalElement element))

/-- Relative position of a fixed-red private element in its complete
variable-site drawing. -/
def fixedRedInternalSitePosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (element : FixedRedConnectorElement) : Cell :=
  placeVariableModulePoint
    (occurrenceVariableSiteSlot slot)
    ((FixedRedConnector.boundaryDrawing
      (occurrencePolarity source atom slot)).elementPosition element)

/-- Global position of a typed triple. -/
def assembledTriplePosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    Triple Variable → Cell
  | triple@(.ordinary atom slot _ _) =>
      Cell.add (routing.variableOrigin atom)
        (placeVariableModulePoint
          (occurrenceVariableSiteSlot slot)
          (orientedTripleLocalPosition source triple))
  | triple@(.fixedRed atom slot _) =>
      Cell.add (routing.variableOrigin atom)
        (placeVariableModulePoint
          (occurrenceVariableSiteSlot slot)
          (orientedTripleLocalPosition source triple))
  | triple@(.clause clauseIndex _) =>
      Cell.add (routing.clauseOrigin clauseIndex)
        (orientedTripleLocalPosition source triple)

/-- Global position of a typed red element. -/
def assembledRedElementPosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    RedElement Variable → Cell
  | .cycleLink atom slot =>
      Cell.add (routing.variableOrigin atom)
        (variableCycleLinkPosition
          (occurrenceVariableSiteSlot slot))
  | .fixedRedInternal atom slot element =>
      Cell.add (routing.variableOrigin atom)
        (fixedRedInternalSitePosition source atom slot
          (fixedRedInternalRedLocalElement element))
  | element@(.clauseInternal clauseIndex) =>
      Cell.add (routing.clauseOrigin clauseIndex)
        (redClauseElementLocalPosition element)
  | element@(.clauseTerminal clauseIndex _) =>
      Cell.add (routing.clauseOrigin clauseIndex)
        (redClauseElementLocalPosition element)

/-- Global position of a typed green element. -/
def assembledGreenElementPosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    GreenElement Variable → Cell
  | .ordinaryInternal atom slot element =>
      Cell.add (routing.variableOrigin atom)
        (ordinaryInternalSitePosition source atom slot element)
  | .fixedRedInternal atom slot element =>
      Cell.add (routing.variableOrigin atom)
        (fixedRedInternalSitePosition source atom slot
          (fixedRedInternalGreenLocalElement element))
  | element@(.clauseInternal clauseIndex) =>
      Cell.add (routing.clauseOrigin clauseIndex)
        (greenClauseElementLocalPosition element)
  | element@(.clauseTerminal clauseIndex _) =>
      Cell.add (routing.clauseOrigin clauseIndex)
        (greenClauseElementLocalPosition element)

/-- Global position of a typed blue element. -/
def assembledBlueElementPosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    BlueElement Variable → Cell
  | .ordinaryInternal atom slot element =>
      Cell.add (routing.variableOrigin atom)
        (ordinaryInternalSitePosition source atom slot element)
  | .fixedRedInternal atom slot element =>
      Cell.add (routing.variableOrigin atom)
        (fixedRedInternalSitePosition source atom slot
          (fixedRedInternalBlueLocalElement element))
  | element@(.clauseInternal clauseIndex) =>
      Cell.add (routing.clauseOrigin clauseIndex)
        (blueClauseElementLocalPosition element)
  | element@(.clauseTerminal clauseIndex _) =>
      Cell.add (routing.clauseOrigin clauseIndex)
        (blueClauseElementLocalPosition element)

/-- Typed triples followed by red, green, and blue elements, exactly as in
the encoded incidence graph. -/
def assembledVertexPositions
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
  (routing : ThreeStrandRouting source) : List Cell :=
  (triples source).map (assembledTriplePosition routing) ++
    (redElements source).map (assembledRedElementPosition routing) ++
    (greenElements source).map (assembledGreenElementPosition routing) ++
    (blueElements source).map (assembledBlueElementPosition routing)

/-- The assembled position list has one entry for every encoded incidence
graph vertex. -/
theorem assembledVertexPositions_length
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    (assembledVertexPositions routing).length =
      (encodedProblem source).incidenceGraph.vertices.length := by
  simp [assembledVertexPositions, encodedProblem, TypedProblem.encode,
    PeriodicThreeDM.incidenceGraph, PeriodicThreeDM.tripleVertices,
    PeriodicThreeDM.elementVertices,
    PeriodicThreeDM.coloredElementVertices,
    PeriodicThreeDM.elementCount, problem]

/-- Looking up a typed triple position in the first position block recovers
the declared global triple position. -/
theorem assembledVertexPositions_triple_getElem
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (index : Nat) (indexLt : index < (triples source).length) :
    (assembledVertexPositions routing)[index]'(by
      simp only [assembledVertexPositions, List.length_append,
        List.length_map]
      omega) =
      assembledTriplePosition routing
        ((triples source)[index]'indexLt) := by
  simp [assembledVertexPositions, indexLt]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
