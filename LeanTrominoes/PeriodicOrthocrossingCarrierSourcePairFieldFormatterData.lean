/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookupData

/-! # Formatting twelve unary source-pair fields as guarded binary words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourcePairFieldFormatter

inductive Side
  | first
  | second
  deriving DecidableEq, Fintype

inductive NatPart
  | route
  | segment
  deriving DecidableEq, Fintype

inductive Coordinate
  | horizontal
  | vertical
  deriving DecidableEq, Fintype

inductive Control
  | begin
  | nat (side : Side) (part : NatPart)
  | negative (side : Side) (coordinate : Coordinate) (seen : Bool)
  | positive (side : Side) (coordinate : Coordinate) (enabled : Bool)
  deriving DecidableEq, Fintype

def afterCoordinate : Side → Coordinate → Control
  | side, .horizontal => .negative side .vertical false
  | .first, .vertical => .nat .second .route
  | .second, .vertical => .begin

def coordinateSuffix : Side → Coordinate →
    List DelimitedBinaryWords.Token
  | _, .horizontal => []
  | .first, .vertical => [.bit true]
  | .second, .vertical => [.wordEnd]

def transition : Control → UnaryFieldEncoderMachine.Symbol →
    Control × List DelimitedBinaryWords.Token
  | .begin, .unit =>
      (.nat .first .route,
        [.wordStart, .bit true, .bit false])
  | .begin, .delimiter =>
      (.nat .first .segment,
        [.wordStart, .bit true, .bit true])
  | .nat side .route, .unit =>
      (.nat side .route, [.bit false])
  | .nat side .route, .delimiter =>
      (.nat side .segment, [.bit true])
  | .nat side .segment, .unit =>
      (.nat side .segment, [.bit false])
  | .nat side .segment, .delimiter =>
      (.negative side .horizontal false, [.bit true])
  | .negative side coordinate false, .unit =>
      (.negative side coordinate true, [.bit true])
  | .negative side coordinate true, .unit =>
      (.negative side coordinate true, [.bit false])
  | .negative side coordinate false, .delimiter =>
      (.positive side coordinate true, [.bit false])
  | .negative side coordinate true, .delimiter =>
      (.positive side coordinate false, [.bit true])
  | .positive side coordinate true, .unit =>
      (.positive side coordinate true, [.bit false])
  | .positive side coordinate false, .unit =>
      (.positive side coordinate false, [])
  | .positive side coordinate enabled, .delimiter =>
      (afterCoordinate side coordinate,
        (if enabled then [.bit true] else []) ++
          coordinateSuffix side coordinate)

def finish (_ : Control) : List DelimitedBinaryWords.Token := []

def output (symbols : List UnaryFieldEncoderMachine.Symbol) :
    List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output .begin transition finish symbols

/-- Guarded source-pair words reconstructed from a semantic pair list. -/
def words (sourcePairs : List CarrierNodeSourceKeys.SourceKeyPair) :
    DelimitedBinaryWords.Input :=
  ⟨sourcePairs.map fun sourcePair =>
    true :: CarrierNodeSourceKeys.word sourcePair⟩

end CarrierSourcePairFieldFormatter
end LeanTrominoes.PeriodicOrthocrossing
