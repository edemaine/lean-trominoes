/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteTailRecordData

/-! # Relabeling binary route tails into clockwise source slots -/

namespace LeanTrominoes
namespace BinaryRouteTailRecordClockwiseRelabel

open PeriodicCNF
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord

abbrev Token := HorizontalRoutedRouteTailRecord.Token

/-- A binary presentation pair must be reversed exactly when its second
route begins strictly earlier in clockwise order. -/
def profileNeedsSwap : DirectedClauseProfile → Bool
  | .binary _ firstDirection _ secondDirection =>
      decide (secondDirection.clockwiseRank < firstDirection.clockwiseRank)
  | _ => false

/-- Exchange the first two source slots, leaving the unused ternary slot
fixed. -/
def swapSourceSlot : SourceLiteralSlot → SourceLiteralSlot
  | .first => .second
  | .second => .first
  | .third => .third

def relabeledSourceSlot (swap : Bool)
    (slot : SourceLiteralSlot) : SourceLiteralSlot :=
  if swap then swapSourceSlot slot else slot

/-- The finite control remembers whether the current binary clause's two
presentation slots must be exchanged. -/
abbrev State := Bool

def initial : State := false

def transition (swap : State) : Token → State × List Token
  | .profile profile =>
      (profileNeedsSwap profile, [.profile profile])
  | .direction slot direction =>
      (swap, [.direction (relabeledSourceSlot swap slot) direction])
  | .clauseEnd => (false, [.clauseEnd])

def finish (_ : State) : List Token := []

def output (input : List Token) : List Token :=
  FiniteStateTransducer.output initial transition finish input

/-- Explicit record obtained by relabeling two presentation-ordered tails. -/
def relabeledBinaryClauseRecord
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection) : List Token :=
  if profileNeedsSwap profile then
    .profile profile ::
      (tailBlock .second first ++ tailBlock .first second ++ [.clauseEnd])
  else
    clauseRecord profile [first, second]

end BinaryRouteTailRecordClockwiseRelabel
end LeanTrominoes
