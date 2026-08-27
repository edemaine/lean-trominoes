/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceStubDirectionData
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceFiniteDirectionData
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchInnerCompiler

/-! # Finite queries for horizontal local incidence directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget
open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

/-- The two finite local tables contributing to horizontal typed incidence
words.  Variable queries select a variable-site route from its fan data;
clause queries select one fixed clause-core route. -/
inductive HorizontalFiniteIncidenceDirectionQuery where
  | variable
      (fan : VariableRibbonFanData)
      (triple : VariableSiteTriple)
      (color : WireColor)
  | clause (set : X3CClauseSet) (color : WireColor)
  | variableStub
      (fan : VariableRibbonFanData)
      (slot : VariableSiteSlot)
      (color : WireColor)
  | clauseStub
      (fan : ClauseRibbonFanData)
      (group : X3CClauseTerminalGroup)
      (lane : WireColor)
  deriving DecidableEq, Fintype

instance : Inhabited HorizontalFiniteIncidenceDirectionQuery :=
  ⟨.clause .topLeftOuter .red⟩

namespace HorizontalFiniteIncidenceDirectionQuery

/-- Exact unit direction word selected by one finite local query. -/
def directions : HorizontalFiniteIncidenceDirectionQuery → List AxisDirection
  | .variable fan triple color =>
      unitSubdivisionDirections (variableSiteRouteData fan triple color)
  | .clause set color =>
      unitSubdivisionDirections (X3CClauseOrthogonal.route set color)
  | .variableStub fan slot color =>
      unitSubdivisionDirections (fan.coordinatedRoute slot color)
  | .clauseStub fan group lane =>
      unitSubdivisionDirections (fan.coordinatedRoute group lane)

/-- Independently delimited form used when a finite query supplies a whole
incidence word. -/
def block (query : HorizontalFiniteIncidenceDirectionQuery) :
    List PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken :=
  (directions query).map .direction ++ [.routeEnd]

def output (queries : List HorizontalFiniteIncidenceDirectionQuery) :
    List AxisDirection :=
  queries.flatMap directions

def delimitedOutput
    (queries : List HorizontalFiniteIncidenceDirectionQuery) :
    List PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken :=
  queries.flatMap block

/-- The proof-free query extracted from a variable incidence selects exactly
its finite prefix direction word. -/
@[simp] theorem directions_variable_input
    (input : HorizontalVariableIncidencePrefixInput) :
    directions (.variable
        (horizontalVariableIncidenceLocalRouteInputComputed input).1
        (horizontalVariableIncidenceLocalRouteInputComputed input).2.1
        (horizontalVariableIncidenceLocalRouteInputComputed input).2.2) =
      horizontalVariableIncidencePrefixDirections input := by
  rfl

/-- The finite clause query selects exactly the clause-core incidence word. -/
@[simp] theorem directions_clause_input
    (input : X3CClauseSet × WireColor) :
    directions (.clause input.1 input.2) =
      horizontalClauseIncidenceDirections input := by
  rfl

/-- The extracted variable-fan query selects exactly the finite source-end
stub of a coordinated occurrence route. -/
@[simp] theorem directions_variableStub_input
    (input : HorizontalOccurrenceColoredRouteInput) :
    directions (.variableStub
        (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).1
        (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).2.1
        (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).2.2) =
      horizontalOccurrenceVariableStubDirections input := by
  rfl

/-- The extracted clause-fan query selects exactly the finite target-end stub
of a coordinated occurrence route. -/
@[simp] theorem directions_clauseStub_input
    (input : HorizontalOccurrenceColoredRouteInput) :
    directions (.clauseStub
        (horizontalOccurrenceClauseCoordinatedRouteInputComputed input).1
        (horizontalOccurrenceClauseCoordinatedRouteInputComputed input).2.1
        (horizontalOccurrenceClauseCoordinatedRouteInputComputed input).2.2) =
      horizontalOccurrenceClauseStubDirections input := by
  rfl

end HorizontalFiniteIncidenceDirectionQuery

end PeriodicCNFStripReduction
end LeanTrominoes

end
