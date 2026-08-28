/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalColumnData
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanRouteTailRecordDecoderData
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Packed carrier-span terminal-column decoding data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierPackedSpanTerminalColumns

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open CarrierPackedSpanRouteTailRecords

abbrev Symbol := UnaryFieldEncoderMachine.Symbol

/-- A canonical unary field is active exactly when its first symbol is a
unit rather than its delimiter. -/
def hasUnit (block : List Symbol) : Bool :=
  block.headD .delimiter == .unit

/-- Four direction ranks for one selected carrier axis. -/
def directionRankValues (horizontal : Bool) : List Nat :=
  if horizontal then [0, 8, 3, 6] else [3, 0, 6, 8]

/-- Select the fixed rank block matching one packed metadata residue. -/
def guardedDirectionCandidate
    (residue : Residue) (horizontal : Bool)
    (block : List Symbol) : List Symbol :=
  SeparatedBooleanGuard.guarded
    (hasUnit block && hasResidue residue block,
      UnaryFieldEncoderMachine.unaryFields
        (directionRankValues horizontal))

/-- Decode one packed carrier field to four direction-rank fields. -/
def directionRankBlockOutput (block : List Symbol) : List Symbol :=
  guardedDirectionCandidate .zero false block ++
    guardedDirectionCandidate .one false block ++
      guardedDirectionCandidate .two true block ++
        guardedDirectionCandidate .three true block

/-- Decode all packed carrier fields to their selected direction ranks. -/
def directionRankStream (source : List Symbol) : List Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput
    CarrierSpanRouteDirections.isFieldEnd directionRankBlockOutput source

/-- Encoded four-length candidate.  The packed quotient produces
`span + 2`; deleting eight leading units leaves `span - 6`. -/
def radialLengthCandidate (block : List Symbol) : List Symbol :=
  UnaryFieldEncoderMachine.unaryFields [3, 2, 1] ++
    (reducedOutput block).drop 8

/-- Decode one active packed carrier field to its four radial lengths. -/
def radialLengthBlockOutput (block : List Symbol) : List Symbol :=
  SeparatedBooleanGuard.guarded
    (hasUnit block, radialLengthCandidate block)

/-- Decode all packed carrier fields to their selected radial lengths. -/
def radialLengthStream (source : List Symbol) : List Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput
    CarrierSpanRouteDirections.isFieldEnd radialLengthBlockOutput source

end CarrierPackedSpanTerminalColumns
end LeanTrominoes.PeriodicOrthocrossing
