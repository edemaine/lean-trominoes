/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendRecordFamilyPresentation
import LeanTrominoes.RetainedAngularFanFinalBendTaggedLiteralInputData

/-! # Indexed final retained-bend occurrences -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalBendIndexedOccurrenceThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- All source hypotheses and lookup witnesses for one genuine literal of
an indexed final retained-bend clause. -/
structure FinalBendIndexedOccurrence
    (Variable : Type) [DecidableEq Variable] where
  source : PeriodicCNF Variable
  sourceLocal : source.IsLocal
  sourceWidth : source.WidthAtMost 3
  sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ []
  positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
    incidence.edge.offset = (0, 0) ∨ incidence.edge.offset = (1, 0)
  taggedBend : RouteBend × Bool
  clauseIndex : Nat
  taggedBendIndexed :
    finalBendTaggedBendIndexed source taggedBend clauseIndex
  clause : PositionedPeriodicClause
    (WrappedPeriodicPlanarSATVariable
      (ThreeOccurrenceVariable Variable))
  clauseMember :
    (clause, clauseIndex) ∈
      (finalCoordinatedSource
        (PeriodicThreeSATThree.formula source)).clauses.zipIdx
  literal : PeriodicLiteral
    (WrappedPeriodicPlanarSATVariable
      (ThreeOccurrenceVariable Variable))
  literalIndex : Fin 2
  literalMember :
    (literal, literalIndex.val) ∈ clause.literals.zipIdx

namespace FinalBendIndexedOccurrence

/-- The retained three-occurrence formula addressed by this occurrence. -/
def retained
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :=
  PeriodicThreeSATThree.formula occurrence.source

/-- The positively scaled source route addressed by this occurrence. -/
abbrev scaledRoute
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) : List Cell :=
  scalePolyline retainedAngularFanSourceClearanceFactor
    (finalCoordinatedSourceRoutes occurrence.retained
      occurrence.clauseIndex occurrence.literalIndex)

/-- The exact final occurrence slot used by this bend route. -/
abbrev slot
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    RetainedTerminalSlot :=
  retainedFinalCoordinatedOccurrenceSlot occurrence.retained
    occurrence.literal occurrence.clauseIndex occurrence.literalIndex

/-- The local implication-clause index selected by this bend direction. -/
abbrev localClauseIndex
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) : Fin 2 :=
  if occurrence.taggedBend.2 then 0 else 1

/-- The finite normalized compiler geometry addressed by this bend. -/
abbrev geometry
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    BendFallbackRouteTailRecords.Geometry :=
  { firstPort := occurrence.taggedBend.1.incomingPort
    secondPort := occurrence.taggedBend.1.outgoingPort }

end FinalBendIndexedOccurrence
end PeriodicEightOccurrenceSplit
end LeanTrominoes
