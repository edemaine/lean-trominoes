/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordFormatterCompiler

/-! # Semantics of binary-clause route-tail formatting -/

namespace LeanTrominoes
namespace BinaryRouteTailRecordFormatter

open FiniteStateTransducer
open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord
open PeriodicOrthocrossing.CarrierSpanRouteDirections

private theorem scan_firstTail
    (firstProfile secondProfile :
      FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    ∀ directions : List AxisDirection,
      scan (transition firstProfile secondProfile) .firstTail
          (directionTokens directions ++ [.routeEnd]) =
        (.secondHead, tailBlock .first directions)
  | [] => rfl
  | direction :: directions => by
      change scan (transition firstProfile secondProfile) .firstTail
          (.direction direction ::
            (directionTokens directions ++ [.routeEnd])) = _
      simp only [scan, transition, List.singleton_append]
      rw [scan_firstTail firstProfile secondProfile directions]
      rfl

private theorem scan_secondTail
    (firstProfile secondProfile :
      FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    ∀ directions : List AxisDirection,
      scan (transition firstProfile secondProfile) .secondTail
          (directionTokens directions ++ [.routeEnd]) =
        (.thirdHead, tailBlock .second directions ++ [.clauseEnd])
  | [] => rfl
  | direction :: directions => by
      change scan (transition firstProfile secondProfile) .secondTail
          (.direction direction ::
            (directionTokens directions ++ [.routeEnd])) = _
      simp only [scan, transition, List.singleton_append]
      rw [scan_secondTail firstProfile secondProfile directions]
      simp [tailBlock]

private theorem scan_thirdTail
    (firstProfile secondProfile :
      FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    ∀ directions : List AxisDirection,
      scan (transition firstProfile secondProfile) .thirdTail
          (directionTokens directions ++ [.routeEnd]) =
        (.fourthHead, tailBlock .first directions)
  | [] => rfl
  | direction :: directions => by
      change scan (transition firstProfile secondProfile) .thirdTail
          (.direction direction ::
            (directionTokens directions ++ [.routeEnd])) = _
      simp only [scan, transition, List.singleton_append]
      rw [scan_thirdTail firstProfile secondProfile directions]
      rfl

private theorem scan_fourthTail
    (firstProfile secondProfile :
      FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    ∀ directions : List AxisDirection,
      scan (transition firstProfile secondProfile) .fourthTail
          (directionTokens directions ++ [.routeEnd]) =
        (.done, tailBlock .second directions ++ [.clauseEnd])
  | [] => rfl
  | direction :: directions => by
      change scan (transition firstProfile secondProfile) .fourthTail
          (.direction direction ::
            (directionTokens directions ++ [.routeEnd])) = _
      simp only [scan, transition, List.singleton_append]
      rw [scan_fourthTail firstProfile secondProfile directions]
      simp [tailBlock]

private theorem scan_firstRoute
    (firstProfile secondProfile :
      FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (directions : List AxisDirection) :
    scan (transition firstProfile secondProfile) .firstHead
        (delimitedDirections directions) =
      (.secondHead,
        .profile firstProfile :: tailBlock .first directions.tail) := by
  cases directions with
  | nil => rfl
  | cons direction directions =>
      change scan (transition firstProfile secondProfile) .firstHead
          (.direction direction ::
            (directionTokens directions ++ [.routeEnd])) = _
      simp only [scan, transition, List.singleton_append]
      rw [scan_firstTail firstProfile secondProfile directions]
      rfl

private theorem scan_secondRoute
    (firstProfile secondProfile :
      FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (directions : List AxisDirection) :
    scan (transition firstProfile secondProfile) .secondHead
        (delimitedDirections directions) =
      (.thirdHead,
        tailBlock .second directions.tail ++ [.clauseEnd]) := by
  cases directions with
  | nil => rfl
  | cons direction directions =>
      change scan (transition firstProfile secondProfile) .secondHead
          (.direction direction ::
            (directionTokens directions ++ [.routeEnd])) = _
      simp only [scan, transition, List.nil_append]
      rw [scan_secondTail firstProfile secondProfile directions]
      rfl

private theorem scan_thirdRoute
    (firstProfile secondProfile :
      FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (directions : List AxisDirection) :
    scan (transition firstProfile secondProfile) .thirdHead
        (delimitedDirections directions) =
      (.fourthHead,
        .profile secondProfile :: tailBlock .first directions.tail) := by
  cases directions with
  | nil => rfl
  | cons direction directions =>
      change scan (transition firstProfile secondProfile) .thirdHead
          (.direction direction ::
            (directionTokens directions ++ [.routeEnd])) = _
      simp only [scan, transition, List.singleton_append]
      rw [scan_thirdTail firstProfile secondProfile directions]
      rfl

private theorem scan_fourthRoute
    (firstProfile secondProfile :
      FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (directions : List AxisDirection) :
    scan (transition firstProfile secondProfile) .fourthHead
        (delimitedDirections directions) =
      (.done, tailBlock .second directions.tail ++ [.clauseEnd]) := by
  cases directions with
  | nil => rfl
  | cons direction directions =>
      change scan (transition firstProfile secondProfile) .fourthHead
          (.direction direction ::
            (directionTokens directions ++ [.routeEnd])) = _
      simp only [scan, transition, List.nil_append]
      rw [scan_fourthTail firstProfile secondProfile directions]
      rfl

/-- The formatter has the exact two-clause semantics for any four complete
route words, including empty words. -/
theorem output_four_routes
    (firstProfile secondProfile :
      FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (first second third fourth : List AxisDirection) :
    output firstProfile secondProfile
        (delimitedDirections first ++
          delimitedDirections second ++
          delimitedDirections third ++
          delimitedDirections fourth) =
      clauseRecord firstProfile [first.tail, second.tail] ++
        clauseRecord secondProfile [third.tail, fourth.tail] := by
  unfold output FiniteStateTransducer.output
  rw [show delimitedDirections first ++
          delimitedDirections second ++
          delimitedDirections third ++
          delimitedDirections fourth =
        delimitedDirections first ++
          (delimitedDirections second ++
            (delimitedDirections third ++
              delimitedDirections fourth)) by
        simp [List.append_assoc]]
  rw [scan_append, scan_firstRoute]
  dsimp only
  rw [scan_append, scan_secondRoute]
  dsimp only
  rw [scan_append, scan_thirdRoute]
  dsimp only
  rw [scan_fourthRoute]
  simp [finish, clauseRecord, taggedTailTokens,
    List.append_assoc]

/-- Total profile projection used only with known clause descriptors below. -/
def descriptorProfile : FormulaShapeDirectionOrdering.Token →
    FormulaShapeDirectionOrdering.DirectedClauseProfile
  | .variable => default
  | .clause profile => profile

/-- Formatting the canonical four-route carrier block gives exactly the two
flat Figure 9 tail records identified at the semantic boundary. -/
theorem output_carrier_canonicalBlock
    (horizontal nextSlice : Bool) (span : Nat) :
    output
        (descriptorProfile
          (carrierClauseDescriptor horizontal nextSlice true))
        (descriptorProfile
          (carrierClauseDescriptor horizontal nextSlice false))
        (canonicalBlock horizontal span) =
      carrierLensRouteTailRecordBlock horizontal nextSlice span := by
  unfold canonicalBlock
  rw [output_four_routes]
  simp [descriptorProfile, carrierLensRouteTailRecordBlock,
    binaryRouteTailRecord, carrierClauseDescriptor]

end BinaryRouteTailRecordFormatter
end LeanTrominoes
