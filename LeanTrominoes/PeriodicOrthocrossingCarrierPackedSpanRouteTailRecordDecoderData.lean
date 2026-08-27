/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordFormatterData
import LeanTrominoes.PeriodicOrthocrossingCarrierTaggedSpanRouteDirectionDecoderData

/-! # Packed retained carrier-span Figure 9 tail-record decoding data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierPackedSpanRouteTailRecords

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open CarrierSpanRouteDirections

abbrev SourceSymbol := UnaryFieldEncoderMachine.Symbol
abbrev Token :=
  PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord.Token

inductive ReductionControl
  | zero
  | one
  | two
  | three
  | four
  deriving DecidableEq, Fintype, Inhabited

/-- Divide a positive packed field by four and add one: every canonical
`4 * span + 4 + residue` field becomes the span decoder's `span + 2` field.
Zero remains zero. -/
def reducedTransition : ReductionControl → SourceSymbol →
    ReductionControl × List SourceSymbol
  | .zero, .unit => (.one, [])
  | .one, .unit => (.two, [])
  | .two, .unit => (.three, [])
  | .three, .unit => (.four, [.unit])
  | .four, .unit => (.one, [])
  | .zero, .delimiter => (.zero, [.delimiter])
  | .one, .delimiter => (.one, [.unit, .delimiter])
  | .two, .delimiter => (.two, [.unit, .delimiter])
  | .three, .delimiter => (.three, [.unit, .delimiter])
  | .four, .delimiter => (.four, [.unit, .delimiter])

def reducedFinish (_ : ReductionControl) : List SourceSymbol := []

def reducedOutput (block : List SourceSymbol) : List SourceSymbol :=
  FiniteStateTransducer.output .zero
    reducedTransition reducedFinish block

inductive Residue
  | zero
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Inhabited

def Residue.code : Residue → Nat
  | .zero => 0
  | .one => 1
  | .two => 2
  | .three => 3

def metadataResidue (horizontal nextSlice : Bool) : Residue :=
  match horizontal, nextSlice with
  | false, false => .zero
  | false, true => .one
  | true, false => .two
  | true, true => .three

inductive ResidueControl
  | residue (value : Residue)
  | done
  deriving DecidableEq, Fintype, Inhabited

def Residue.next : Residue → Residue
  | .zero => .one
  | .one => .two
  | .two => .three
  | .three => .zero

def residueTransition (target : Residue) :
    ResidueControl → SourceSymbol → ResidueControl × List Bool
  | .residue value, .unit => (.residue value.next, [])
  | .residue value, .delimiter => (.done, [value == target])
  | .done, _ => (.done, [])

def residueFinish (target : Residue) : ResidueControl → List Bool
  | .residue value => [value == target]
  | .done => []

def residueOutput (target : Residue)
    (block : List SourceSymbol) : List Bool :=
  FiniteStateTransducer.output (.residue .zero)
    (residueTransition target) (residueFinish target) block

def hasResidue (target : Residue) (block : List SourceSymbol) : Bool :=
  (residueOutput target block).headD false

def candidate (horizontal nextSlice : Bool)
    (block : List SourceSymbol) : List Token :=
  BinaryRouteTailRecordFormatter.output
    (BinaryRouteTailRecordFormatter.descriptorProfile
      (carrierClauseDescriptor horizontal nextSlice true))
    (BinaryRouteTailRecordFormatter.descriptorProfile
      (carrierClauseDescriptor horizontal nextSlice false))
    (CarrierSpanRouteDirections.blockOutput horizontal
      (reducedOutput block))

def guardedCandidate (residue : Residue)
    (horizontal nextSlice : Bool) (block : List SourceSymbol) : List Token :=
  SeparatedBooleanGuard.guarded
    (hasResidue residue block, candidate horizontal nextSlice block)

/-- Select the unique axis/next-slice interpretation given by the residue.
The zero field enters the residue-zero branch, whose candidate is empty. -/
def blockOutput (block : List SourceSymbol) : List Token :=
  guardedCandidate .zero false false block ++
    guardedCandidate .one false true block ++
      guardedCandidate .two true false block ++
        guardedCandidate .three true true block

def stream (source : List SourceSymbol) : List Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    CarrierSpanRouteDirections.isFieldEnd blockOutput source

end CarrierPackedSpanRouteTailRecords
end LeanTrominoes.PeriodicOrthocrossing
