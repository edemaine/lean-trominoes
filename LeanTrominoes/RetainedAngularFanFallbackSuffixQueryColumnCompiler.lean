/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionBatchCompiler
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryFormatter
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldAlternatingPaddingCompiler

/-! # Compiling aligned fallback-suffix query columns -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixQueryColumns

open Computability Turing
open FallbackSuffixDirectionCompiler
open FallbackSuffixDirectionCompiler.Batch
open FallbackSuffixQueryFormatter

def roleBase (role : HeaderRole) : Nat :=
  8 * (Fintype.equivFin HeaderRole role).val

def roleBases (roles : List HeaderRole) : List Nat :=
  roles.map roleBase

def slotValues (slots : List RetainedTerminalSlot) : List Nat :=
  slots.map Fin.val

def headerCodes
    (roles : List HeaderRole)
    (slots : List RetainedTerminalSlot) : List Nat :=
  AlignedUnaryListClosure.added (roleBases roles) (slotValues slots)

/-- Align the finite headers with their dynamic radial lengths by placing
them in alternating unary fields. -/
def alternatingCodes
    (roles : List HeaderRole)
    (radials : List Nat)
    (slots : List RetainedTerminalSlot) : List Nat :=
  AlignedUnaryListClosure.added
    (UnaryFieldAlternatingPadding.appendZeroValues
      (headerCodes roles slots))
    (UnaryFieldAlternatingPadding.prependZeroValues radials)

/-- Query zipper corresponding to the three independently compiled
columns.  The shortest column determines the result. -/
def alignedQueries :
    List HeaderRole → List Nat →
      List RetainedTerminalSlot → List Query
  | role :: roles, radial :: radials, slot :: slots =>
      { kind := role.1
        direction := role.2
        rawLength := radial
        slot := slot } :: alignedQueries roles radials slots
  | _, _, _ => []

private theorem alternatingCodes_cons
    (role : HeaderRole) (roles : List HeaderRole)
    (radial : Nat) (radials : List Nat)
    (slot : RetainedTerminalSlot)
    (slots : List RetainedTerminalSlot) :
    alternatingCodes (role :: roles) (radial :: radials) (slot :: slots) =
      [roleBase role + slot.val, radial] ++
        alternatingCodes roles radials slots := by
  simp [alternatingCodes, headerCodes, roleBases, slotValues,
    AlignedUnaryListClosure.added, UnaryAlignedAddMachine.sums,
    UnaryFieldAlternatingPadding.appendZeroValues,
    UnaryFieldAlternatingPadding.prependZeroValues]

private theorem queryCodes_alignedQueries_cons
    (role : HeaderRole) (roles : List HeaderRole)
    (radial : Nat) (radials : List Nat)
    (slot : RetainedTerminalSlot)
    (slots : List RetainedTerminalSlot) :
    FallbackSuffixQueryFormatter.queryCodes
        (alignedQueries (role :: roles) (radial :: radials) (slot :: slots)) =
      [roleBase role + slot.val, radial] ++
        FallbackSuffixQueryFormatter.queryCodes
          (alignedQueries roles radials slots) := by
  rcases role with ⟨kind, direction⟩
  rfl

@[simp] theorem alternatingCodes_eq_queryCodes
    (roles : List HeaderRole)
    (radials : List Nat)
    (slots : List RetainedTerminalSlot) :
    alternatingCodes roles radials slots =
      FallbackSuffixQueryFormatter.queryCodes
        (alignedQueries roles radials slots) := by
  induction roles generalizing radials slots with
  | nil =>
      simp [alternatingCodes, headerCodes, roleBases, slotValues,
        alignedQueries, AlignedUnaryListClosure.added,
        UnaryAlignedAddMachine.sums,
        UnaryFieldAlternatingPadding.appendZeroValues,
        UnaryFieldAlternatingPadding.prependZeroValues,
        FallbackSuffixQueryFormatter.queryCodes]
  | cons role roles induction =>
      cases radials with
      | nil =>
          simp [alternatingCodes, headerCodes, roleBases, slotValues,
            alignedQueries, AlignedUnaryListClosure.added,
            UnaryAlignedAddMachine.sums,
            UnaryFieldAlternatingPadding.appendZeroValues,
            UnaryFieldAlternatingPadding.prependZeroValues,
            FallbackSuffixQueryFormatter.queryCodes]
      | cons radial radials =>
          cases slots with
          | nil =>
              simp [alternatingCodes, headerCodes, roleBases, slotValues,
                alignedQueries, AlignedUnaryListClosure.added,
                UnaryAlignedAddMachine.sums,
                UnaryFieldAlternatingPadding.appendZeroValues,
                UnaryFieldAlternatingPadding.prependZeroValues,
                FallbackSuffixQueryFormatter.queryCodes]
          | cons slot slots =>
              rw [alternatingCodes_cons,
                queryCodes_alignedQueries_cons, induction]

/-- Exact aligned finite-role, unary-radial, and finite-slot producers can
be assembled into the compact fallback-suffix query encoding in polynomial
time. -/
noncomputable def encodeComputableInPolyTimeOf
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (roles : Input → List HeaderRole)
    (radials : Input → List Nat)
    (slots : Input → List RetainedTerminalSlot)
    (rolesSlotsLength : ∀ input,
      (roles input).length = (slots input).length)
    (rolesRadialsLength : ∀ input,
      (roles input).length = (radials input).length)
    (rolesCompiler :
      @TM2ComputableInPolyTime
        Input (List HeaderRole) InputSymbol HeaderRole
        encodeInput id roles)
    (radialsCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields radials)
    (slotsCompiler :
      @TM2ComputableInPolyTime
        Input (List RetainedTerminalSlot) InputSymbol RetainedTerminalSlot
        encodeInput id slots) :
    @TM2ComputableInPolyTime
      Input (List Query)
        InputSymbol FallbackSuffixDirectionCompiler.Token
      encodeInput Batch.encode
      (fun input =>
        alignedQueries (roles input) (radials input) (slots input)) := by
  let roleBasesCompiler :=
    TM2CompositionMachine.computableInPolyTime rolesCompiler
      (FiniteUnaryFieldMap.computableInPolyTime roleBase)
  let slotValuesCompiler :=
    TM2CompositionMachine.computableInPolyTime slotsCompiler
      (FiniteUnaryFieldMap.computableInPolyTime Fin.val)
  let headerCompiler :=
    AlignedUnaryListClosure.addedComputableInPolyTime
      encodeInput
      (fun input => roleBases (roles input))
      (fun input => slotValues (slots input))
      (fun input => by
        simp [roleBases, slotValues, rolesSlotsLength input])
      roleBasesCompiler slotValuesCompiler
  let paddedHeaders :=
    TM2CompositionMachine.computableInPolyTime headerCompiler
      UnaryFieldAlternatingPadding.appendZeroValuesComputableInPolyTime
  let paddedRadials :=
    TM2CompositionMachine.computableInPolyTime radialsCompiler
      UnaryFieldAlternatingPadding.prependZeroValuesComputableInPolyTime
  let codesCompiler :=
    AlignedUnaryListClosure.addedComputableInPolyTime
      encodeInput
      (fun input =>
        UnaryFieldAlternatingPadding.appendZeroValues
          (headerCodes (roles input) (slots input)))
      (fun input =>
        UnaryFieldAlternatingPadding.prependZeroValues
          (radials input))
      (fun input => by
        have roleSlot := rolesSlotsLength input
        have roleRadial := rolesRadialsLength input
        simp only [headerCodes,
          UnaryFieldAlternatingPadding.appendZeroValues_length,
          UnaryFieldAlternatingPadding.prependZeroValues_length,
          AlignedUnaryListClosure.added_length, roleBases, slotValues,
          List.length_map]
        omega)
      paddedHeaders paddedRadials
  let prepared : TM2ComputableInPolyTime encodeInput
      (fun queries =>
        UnaryFieldEncoderMachine.unaryFields
          (FallbackSuffixQueryFormatter.queryCodes queries))
      (fun input =>
        alignedQueries (roles input) (radials input) (slots input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      codesCompiler
      (fun input => congrArg UnaryFieldEncoderMachine.unaryFields
        (alternatingCodes_eq_queryCodes
          (roles input) (radials input) (slots input)))
  let physical := TM2CompositionMachine.computableInPolyTime prepared
    FallbackSuffixQueryFormatter.encodeComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    physical (fun _ => rfl)

/-- The same aligned producers can be interpreted immediately as their
exact route-delimited compiled suffix directions. -/
noncomputable def directionsComputableInPolyTimeOf
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (roles : Input → List HeaderRole)
    (radials : Input → List Nat)
    (slots : Input → List RetainedTerminalSlot)
    (rolesSlotsLength : ∀ input,
      (roles input).length = (slots input).length)
    (rolesRadialsLength : ∀ input,
      (roles input).length = (radials input).length)
    (rolesCompiler :
      @TM2ComputableInPolyTime
        Input (List HeaderRole) InputSymbol HeaderRole
        encodeInput id roles)
    (radialsCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields radials)
    (slotsCompiler :
      @TM2ComputableInPolyTime
        Input (List RetainedTerminalSlot) InputSymbol RetainedTerminalSlot
        encodeInput id slots) :
    @TM2ComputableInPolyTime
      Input (List FallbackSuffixDirectionCompiler.OutputToken)
        InputSymbol FallbackSuffixDirectionCompiler.OutputToken
      encodeInput id
      (fun input =>
        Batch.directions
          (alignedQueries (roles input) (radials input) (slots input))) :=
  TM2CompositionMachine.computableInPolyTime
    (encodeComputableInPolyTimeOf encodeInput roles radials slots
      rolesSlotsLength rolesRadialsLength
      rolesCompiler radialsCompiler slotsCompiler)
    Batch.directionsComputableInPolyTime

end FallbackSuffixQueryColumns
end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
