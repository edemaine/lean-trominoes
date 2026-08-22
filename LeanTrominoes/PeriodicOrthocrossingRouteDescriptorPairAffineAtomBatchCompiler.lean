/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineComparisonCompiler

/-! # Batched polynomial-time affine-atom comparisons -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags
open PeriodicCNF
open PeriodicCNF.AffineEmitterPipeline
open DelimitedBinaryWordPairLengthComparisonMachine

/-- Unary positive/negative word pair for one fixed atom difference. -/
def Atom.comparisonPair
    (atom : Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List Bool × List Bool :=
  let counts := atom.difference.tokenCounts tokens
  (List.replicate counts.1 false, List.replicate counts.2 false)

/-- All fixed affine emission phases for a list of atoms, without expanding
the list into a tree of separately forked machines. -/
def atomsComparisonPhases : List Atom →
    List (AffineEmitterPipeline.Phase RouteDescriptorPairFieldTags.Token)
  | [] => []
  | atom :: atoms =>
      atom.difference.comparisonPhases ++ atomsComparisonPhases atoms

/-- One semantic unary comparison pair per atom. -/
def atomsComparisonInput
    (atoms : List Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    DelimitedBinaryWordPairs.Input :=
  ⟨atoms.map fun atom => atom.comparisonPair tokens⟩

/-- Physical batched comparison word emitted by the single affine phase
pipeline. -/
def atomsComparisonTokens
    (atoms : List Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWordPairs.Token :=
  translateComparisonTokens
    (emittedAll (atomsComparisonPhases atoms) tokens)

@[simp] theorem atomsComparisonTokens_nil
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    atomsComparisonTokens [] tokens = [] := by
  rfl

@[simp] theorem atomsComparisonTokens_cons
    (atom : Atom) (atoms : List Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    atomsComparisonTokens (atom :: atoms) tokens =
      atom.difference.comparisonTokens tokens ++
        atomsComparisonTokens atoms tokens := by
  change translateComparisonTokens
      (emittedAll
        (atom.difference.comparisonPhases ++ atomsComparisonPhases atoms)
        tokens) =
    atom.difference.comparisonTokens tokens ++
      atomsComparisonTokens atoms tokens
  rw [emittedAll_append, translateComparisonTokens_append]
  rfl

@[simp] theorem Atom.difference_comparisonInput_eq
    (atom : Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    atom.difference.comparisonInput tokens =
      ⟨[atom.comparisonPair tokens]⟩ := by
  rfl

@[simp] theorem Atom.difference_comparisonTokens_eq_pairTokens
    (atom : Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    atom.difference.comparisonTokens tokens =
      DelimitedBinaryWordPairs.pairTokens (atom.comparisonPair tokens) := by
  rw [atom.difference.comparisonTokens_eq_encode,
    atom.difference_comparisonInput_eq]
  unfold DelimitedBinaryWordPairs.encode
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

@[simp] theorem atomsComparisonInput_encode_cons
    (atom : Atom) (atoms : List Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    DelimitedBinaryWordPairs.encode
        (atomsComparisonInput (atom :: atoms) tokens) =
      DelimitedBinaryWordPairs.pairTokens (atom.comparisonPair tokens) ++
        DelimitedBinaryWordPairs.encode
          (atomsComparisonInput atoms tokens) := by
  rfl

/-- The batched physical word is exactly the delimiter encoding of all unary
atom-comparison pairs in formula order. -/
theorem atomsComparisonTokens_eq_encode
    (atoms : List Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    atomsComparisonTokens atoms tokens =
      DelimitedBinaryWordPairs.encode (atomsComparisonInput atoms tokens) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms induction =>
      rw [atomsComparisonTokens_cons,
        atom.difference_comparisonTokens_eq_pairTokens,
        atomsComparisonInput_encode_cons, induction]

/-- The single affine phase pipeline followed by token translation compiles
the complete atom list in polynomial time. -/
def atomsComparisonTokensComputableInPolyTime (atoms : List Atom) :
    TM2ComputableInPolyTime id id (atomsComparisonTokens atoms) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (emittedAllComputableInPolyTime (atomsComparisonPhases atoms))
    translateComparisonTokensComputableInPolyTime
  unfold atomsComparisonTokens
  exact composed

/-- Semantic reinterpretation of the complete comparison-pair list. -/
def atomsComparisonInputComputableInPolyTime (atoms : List Atom) :
    @TM2ComputableInPolyTime
      (List RouteDescriptorPairFieldTags.Token)
      DelimitedBinaryWordPairs.Input
      RouteDescriptorPairFieldTags.Token DelimitedBinaryWordPairs.Token
      id DelimitedBinaryWordPairs.encode (atomsComparisonInput atoms) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (atomsComparisonTokensComputableInPolyTime atoms)
    (atomsComparisonTokens_eq_encode atoms)

/-- All comparison orderings produced by the batched affine compiler. -/
def atomsComparisonOrderings
    (atoms : List Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List LengthOrdering :=
  lengthOrderings (atomsComparisonInput atoms tokens)

/-- Each batched result is exactly the natural ordering of its atom's signed
positive and negative totals. -/
@[simp] theorem atomsComparisonOrderings_eq
    (atoms : List Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    atomsComparisonOrderings atoms tokens =
      atoms.map fun atom =>
        let counts := atom.difference.tokenCounts tokens
        compareNats counts.1 counts.2 := by
  unfold atomsComparisonOrderings atomsComparisonInput lengthOrderings
    Atom.comparisonPair compareLengths
  rw [List.map_map]
  apply List.map_congr_left
  intro atom atomMember
  simp only [Function.comp_apply, List.length_replicate]

/-- One comparator run handles the complete fixed atom list in polynomial
time. -/
def atomsComparisonOrderingsComputableInPolyTime (atoms : List Atom) :
    TM2ComputableInPolyTime id id (atomsComparisonOrderings atoms) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (atomsComparisonInputComputableInPolyTime atoms)
    DelimitedBinaryWordPairLengthComparisonMachine.computableInPolyTime
  unfold atomsComparisonOrderings
  exact composed

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
