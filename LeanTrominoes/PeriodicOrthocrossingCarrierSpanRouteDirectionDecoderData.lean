/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRouteDirectionWords
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchInnerCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapData
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Retained carrier-span route-decoder data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSpanRouteDirections

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

abbrev Token :=
  PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken

abbrev SourceSymbol := UnaryFieldEncoderMachine.Symbol

def directionTokens (directions : List AxisDirection) : List Token :=
  directions.map .direction

def delimitedDirections (directions : List AxisDirection) : List Token :=
  directionTokens directions ++ [.routeEnd]

/-- Four route-delimited words for one retained carrier lens. -/
def canonicalBlock (horizontal : Bool) (span : Nat) : List Token :=
  delimitedDirections
      (carrierLensRouteDirections horizontal span 0 0) ++
    delimitedDirections
      (carrierLensRouteDirections horizontal span 0 1) ++
    delimitedDirections
      (carrierLensRouteDirections horizontal span 1 0) ++
    delimitedDirections
      (carrierLensRouteDirections horizontal span 1 1)

def dynamicDirection (horizontal : Bool) : AxisDirection :=
  if horizontal then .east else .north

def firstPrefix (horizontal : Bool) : List Token :=
  if horizontal then
    directionTokens (List.replicate 3 .west) ++ [.routeEnd] ++
      directionTokens (List.replicate 2 .south)
  else
    directionTokens (List.replicate 3 .south) ++ [.routeEnd] ++
      directionTokens (List.replicate 2 .east)

def firstSuffix (horizontal : Bool) : List Token :=
  if horizontal then
    directionTokens (List.replicate 2 .north) ++ [.routeEnd] ++
      directionTokens
        ([.north] ++ List.replicate 6 .west ++ [.south]) ++
      [.routeEnd]
  else
    directionTokens (List.replicate 2 .west) ++ [.routeEnd] ++
      directionTokens
        ([.west] ++ List.replicate 6 .south ++ [.east]) ++
      [.routeEnd]

inductive Control
  | zero
  | one
  | two
  | three
  | four
  | five
  | six
  | seven
  | eight
  | many
  deriving DecidableEq, Fintype, Inhabited

def firstTransition (horizontal : Bool) :
    Control → SourceSymbol → Control × List Token
  | .zero, .unit => (.one, firstPrefix horizontal)
  | .one, .unit => (.two, [])
  | .two, .unit => (.three, [])
  | .three, .unit => (.four, [])
  | .four, .unit => (.five, [])
  | .five, .unit =>
      (.six, [.direction (dynamicDirection horizontal)])
  | .six, .unit =>
      (.seven, [.direction (dynamicDirection horizontal)])
  | .seven, .unit =>
      (.eight, [.direction (dynamicDirection horizontal)])
  | .eight, .unit | .many, .unit =>
      (.many, [.direction (dynamicDirection horizontal)])
  | .zero, .delimiter => (.zero, [])
  | control, .delimiter => (control, firstSuffix horizontal)

def lastTransition (horizontal : Bool) :
    Control → SourceSymbol → Control × List Token
  | .zero, .unit => (.one, [])
  | .one, .unit => (.two, [])
  | .two, .unit => (.three, [])
  | .three, .unit => (.four, [])
  | .four, .unit => (.five, [])
  | .five, .unit => (.six, [])
  | .six, .unit => (.seven, [])
  | .seven, .unit => (.eight, [])
  | .eight, .unit | .many, .unit =>
      (.many, [.direction (dynamicDirection horizontal)])
  | .zero, .delimiter => (.zero, [])
  | control, .delimiter => (control, [.routeEnd])

def finish (_ : Control) : List Token := []

def firstOutput (horizontal : Bool) (block : List SourceSymbol) :
    List Token :=
  FiniteStateTransducer.output .zero
    (firstTransition horizontal) finish block

def lastOutput (horizontal : Bool) (block : List SourceSymbol) :
    List Token :=
  FiniteStateTransducer.output .zero
    (lastTransition horizontal) finish block

/-- Decode one unary field.  Zero emits nothing; canonical positive fields
encode `span + 2` and emit all four route-delimited lens words. -/
def blockOutput (horizontal : Bool) (block : List SourceSymbol) :
    List Token :=
  firstOutput horizontal block ++ lastOutput horizontal block

def isFieldEnd : SourceSymbol → Bool
  | .unit => false
  | .delimiter => true

def stream (horizontal : Bool) (source : List SourceSymbol) : List Token :=
  TM2EndDelimitedBlockMap.mappedOutput isFieldEnd
    (blockOutput horizontal) source

end CarrierSpanRouteDirections
end LeanTrominoes.PeriodicOrthocrossing
