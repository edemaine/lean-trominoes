/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataFallbackPrefixDirectionWords
import LeanTrominoes.PeriodicOrthocrossingCarrierSpanRouteDirectionDecoderData

/-! # Finite-state trimming of retained carrier fallback prefixes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierFallbackPrefixTrimmer

open FiniteStateTransducer
open CarrierSpanRouteDirections
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The carrier block has four fixed route roles.  The first and fourth are
straight terminal segments and disappear.  The second and third retain all
but their final two and one directions respectively. -/
inductive Phase
  | discardFirst
  | secondNone
  | secondOne
  | secondTwo
  | thirdNone
  | thirdOne
  | discardFourth
  | done
  deriving DecidableEq, Fintype, Inhabited

structure Control where
  phase : Phase
  first : AxisDirection
  second : AxisDirection
  deriving DecidableEq, Fintype

instance : Inhabited Control := ⟨⟨.discardFirst, .invalid, .invalid⟩⟩

def initial : Control := ⟨.discardFirst, .invalid, .invalid⟩
def secondNone : Control := ⟨.secondNone, .invalid, .invalid⟩
def secondOne (last : AxisDirection) : Control :=
  ⟨.secondOne, last, .invalid⟩
def secondTwo (beforeLast last : AxisDirection) : Control :=
  ⟨.secondTwo, beforeLast, last⟩
def thirdNone : Control := ⟨.thirdNone, .invalid, .invalid⟩
def thirdOne (last : AxisDirection) : Control :=
  ⟨.thirdOne, last, .invalid⟩
def discardFourth : Control := ⟨.discardFourth, .invalid, .invalid⟩
def done : Control := ⟨.done, .invalid, .invalid⟩

def directionTransition (control : Control) (direction : AxisDirection) :
    Control × List Token :=
  match control.phase with
  | .discardFirst => (control, [])
  | .secondNone => (secondOne direction, [])
  | .secondOne => (secondTwo control.first direction, [])
  | .secondTwo =>
      (secondTwo control.second direction, [.direction control.first])
  | .thirdNone => (thirdOne direction, [])
  | .thirdOne => (thirdOne direction, [.direction control.first])
  | .discardFourth | .done => (control, [])

def endTransition (control : Control) : Control × List Token :=
  match control.phase with
  | .discardFirst => (secondNone, [.routeEnd])
  | .secondNone | .secondOne | .secondTwo =>
      (thirdNone, [.routeEnd])
  | .thirdNone | .thirdOne => (discardFourth, [.routeEnd])
  | .discardFourth => (done, [.routeEnd])
  | .done => (control, [])

def transition (control : Control) : Token → Control × List Token
  | .direction direction => directionTransition control direction
  | .routeEnd => endTransition control

def finish (_ : Control) : List Token := []

def output (tokens : List Token) : List Token :=
  FiniteStateTransducer.output initial transition finish tokens

/-- Four route-delimited carrier source-prefix words. -/
def canonicalPrefixBlock
    (horizontal : Bool) (span : Nat) : List Token :=
  delimitedDirections
      (carrierLensRoutePrefixDirections horizontal span 0 0) ++
    delimitedDirections
      (carrierLensRoutePrefixDirections horizontal span 0 1) ++
    delimitedDirections
      (carrierLensRoutePrefixDirections horizontal span 1 0) ++
    delimitedDirections
      (carrierLensRoutePrefixDirections horizontal span 1 1)

private theorem scan_discardFirst
    (directions : List AxisDirection) (rest : List Token) :
    scan transition initial
        (directionTokens directions ++ .routeEnd :: rest) =
      ((scan transition secondNone rest).1,
        .routeEnd :: (scan transition secondNone rest).2) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      change scan transition initial
          (.direction direction ::
            (directionTokens directions ++ .routeEnd :: rest)) = _
      simp only [scan, initial, transition, directionTransition]
      exact induction

private theorem scan_secondTwo
    (first second : AxisDirection) :
    ∀ directions : List AxisDirection,
      scan transition (secondTwo first second)
          (directionTokens directions ++ [.routeEnd]) =
        (thirdNone,
          directionTokens
              ((first :: second :: directions).take directions.length) ++
            [.routeEnd])
  | [] => rfl
  | third :: directions => by
      change scan transition (secondTwo first second)
          (.direction third ::
            (directionTokens directions ++ [.routeEnd])) = _
      simp only [scan, secondTwo, transition, directionTransition,
        List.singleton_append]
      change
        ((scan transition (secondTwo second third)
            (directionTokens directions ++ [.routeEnd])).1,
          .direction first ::
            (scan transition (secondTwo second third)
              (directionTokens directions ++ [.routeEnd])).2) = _
      rw [scan_secondTwo second third directions]
      simp [directionTokens]

private theorem scan_second
    (directions : List AxisDirection) :
    scan transition secondNone
        (delimitedDirections directions) =
      (thirdNone,
        delimitedDirections
          (directions.take (directions.length - 2))) := by
  cases directions with
  | nil => rfl
  | cons first directions =>
      cases directions with
      | nil => rfl
      | cons second directions =>
          change scan transition (secondTwo first second)
              (directionTokens directions ++ [.routeEnd]) = _
          rw [scan_secondTwo first second directions]
          simp [delimitedDirections]

private theorem scan_thirdOne
    (first : AxisDirection) :
    ∀ directions : List AxisDirection,
      scan transition (thirdOne first)
          (directionTokens directions ++ [.routeEnd]) =
        (discardFourth,
          directionTokens
              ((first :: directions).take directions.length) ++
            [.routeEnd])
  | [] => rfl
  | second :: directions => by
      change scan transition (thirdOne first)
          (.direction second ::
            (directionTokens directions ++ [.routeEnd])) = _
      simp only [scan, thirdOne, transition, directionTransition,
        List.singleton_append]
      change
        ((scan transition (thirdOne second)
            (directionTokens directions ++ [.routeEnd])).1,
          .direction first ::
            (scan transition (thirdOne second)
              (directionTokens directions ++ [.routeEnd])).2) = _
      rw [scan_thirdOne second directions]
      simp [directionTokens]

private theorem scan_third
    (directions : List AxisDirection) :
    scan transition thirdNone
        (delimitedDirections directions) =
      (discardFourth,
        delimitedDirections
          (directions.take (directions.length - 1))) := by
  cases directions with
  | nil => rfl
  | cons first directions =>
      change scan transition (thirdOne first)
          (directionTokens directions ++ [.routeEnd]) = _
      rw [scan_thirdOne first directions]
      simp [delimitedDirections]

private theorem scan_discardFourth
    (directions : List AxisDirection) :
    scan transition discardFourth
        (delimitedDirections directions) =
      (done, [.routeEnd]) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      change scan transition discardFourth
          (.direction direction ::
            (directionTokens directions ++ [.routeEnd])) = _
      simp only [scan, discardFourth, transition, directionTransition]
      exact induction

/-- The trimmer has the advertised positional semantics for arbitrary four
route words. -/
theorem output_four_routes
    (first second third fourth : List AxisDirection) :
    output
        (delimitedDirections first ++
          delimitedDirections second ++
          delimitedDirections third ++
          delimitedDirections fourth) =
      [.routeEnd] ++
        delimitedDirections (second.take (second.length - 2)) ++
        delimitedDirections (third.take (third.length - 1)) ++
        [.routeEnd] := by
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
  unfold delimitedDirections
  rw [show directionTokens first ++ [.routeEnd] ++
          (directionTokens second ++ [.routeEnd] ++
            (directionTokens third ++ [.routeEnd] ++
              (directionTokens fourth ++ [.routeEnd]))) =
        directionTokens first ++ .routeEnd ::
          (delimitedDirections second ++
            (delimitedDirections third ++
              delimitedDirections fourth)) by
        simp [delimitedDirections, List.append_assoc]]
  rw [scan_discardFirst]
  dsimp only
  rw [scan_append, scan_second]
  dsimp only
  rw [scan_append, scan_third]
  dsimp only
  rw [scan_discardFourth]
  simp [finish, delimitedDirections, List.append_assoc]

/-- On every retained carrier span, finite-state trimming recovers exactly
the four explicit unscaled fallback source prefixes. -/
theorem output_canonicalBlock
    (horizontal : Bool) (span : Nat) (large : 6 < span) :
    output (canonicalBlock horizontal span) =
      canonicalPrefixBlock horizontal span := by
  unfold canonicalBlock
  rw [output_four_routes]
  have spanThree : ((span : Int) - 3).natAbs = span - 3 := by
    exact Int.ofNat_inj.mp
      ((Int.natAbs_of_nonneg (by omega)).trans (by omega))
  cases horizontal <;>
    simp [canonicalPrefixBlock, delimitedDirections, directionTokens,
      carrierLensRouteDirections, carrierLensRoutePrefixDirections,
      spanThree, List.map_replicate, List.append_assoc]

/-- One fixed finite-state transducer extracts all retained carrier source
prefixes in linear time. -/
noncomputable def outputComputableInPolyTime :
    Turing.TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime initial transition finish

end CarrierFallbackPrefixTrimmer
end LeanTrominoes.PeriodicOrthocrossing
