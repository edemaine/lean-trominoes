/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.DirectedClauseProfileCheck
import LeanTrominoes.Computation.Encoding.Finite.FiniteBlockIndexCompiler
import LeanTrominoes.Computation.Encoding.Finite.FiniteBlockTransducer
import LeanTrominoes.Computation.Encoding.Finite.FiniteUnaryFieldMapCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderClauseFrameData
import LeanTrominoes.Computation.TM2.TM2CompositionMachine
import LeanTrominoes.Computation.Encoding.Unary.UnaryPrefixSumsTime

/-! # Parent indices of actual final clauses

One pre-Figure-9 clause descriptor can expand into many polarity-normalized
final clauses.  This compiler marks the boundary of every such final clause
inside each finite descriptor block and takes prefix sums of those markers.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderFinalClauseParentIndex

open Computability Turing
open PeriodicCNF.FormulaShapeDirectionOrdering

abbrev Frame := HorizontalRoutedRouteHeaderClauseFrame.Data

/-- Mark the last occurrence frame of every actual final clause.  A new
clause starts at a `.top` frame; the final frame of a descriptor block is
always a clause end. -/
def endingMarkers : List Frame → List Bool
  | [] => []
  | _ :: [] => [true]
  | _ :: next :: remaining =>
      decide (next.group = .top) :: endingMarkers (next :: remaining)

/-- Actual-final-clause boundaries contributed by one finite descriptor. -/
def tokenMarkers (token : Token) : List Bool :=
  endingMarkers (HorizontalRoutedRouteHeaderClauseFrame.tokenBlock token)

/-- Clause-start markers on the same finite frame block. -/
def tokenTopMarkers (token : Token) : List Bool :=
  (HorizontalRoutedRouteHeaderClauseFrame.tokenBlock token).map fun frame =>
    decide (frame.group = .top)

/-- One boundary marker per final occurrence frame. -/
def markers (source : List Token) : List Bool :=
  source.flatMap tokenMarkers

def increments (source : List Token) : List Nat :=
  FiniteUnaryFieldMap.values Bool.toNat (markers source)

/-- Zero-based actual final-clause index, repeated at every occurrence of
that clause. -/
def parentIndices (source : List Token) : List Nat :=
  PrefixSums.starts (increments source)

@[simp] theorem endingMarkers_length (frames : List Frame) :
    (endingMarkers frames).length = frames.length := by
  induction frames with
  | nil => rfl
  | cons frame frames induction =>
      cases frames with
      | nil => rfl
      | cons next remaining =>
          simp only [endingMarkers, List.length_cons, induction]

@[simp] theorem tokenMarkers_length (token : Token) :
    (tokenMarkers token).length =
      (HorizontalRoutedRouteHeaderClauseFrame.tokenBlock token).length := by
  simp [tokenMarkers]

def finalClauseParentMarkersCheck (profile : DirectedClauseProfile) : Bool :=
  decide ((tokenMarkers (.clause profile)).count true =
    (tokenTopMarkers (.clause profile)).count true) &&
  decide (tokenMarkers (.clause profile) =
    FiniteBlockIndices.markers List.length
      (HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks (.clause profile)))

end HorizontalRoutedRouteHeaderFinalClauseParentIndex
end PeriodicCNFStripReduction
end LeanTrominoes

end
