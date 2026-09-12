/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ComplexityReductions
import LeanTrominoes.GadgetStripCorrectness
import LeanTrominoes.PeriodicCNFPolySpaceHardness

/-!
# Polynomial-time reduction through blank-bordered strip drawings

This module isolates the remaining constructive endpoint of the 1.5D
hardness proof.  A source reduction supplies normalized, vertex-separated,
blank-bordered drawings together with a polynomial-time compiler directly to
the target flat strip encoding.  The verified tromino gadget semantics and
the completed one-dimensional periodic-CNF hardness theorem then give the
full strip statement of Theorem 5.2.
-/

noncomputable section

namespace LeanTrominoes
namespace Gadget

open Computability Turing

/-- A polynomial-time source reduction to normalized periodic orientation in
a finite-height drawing.  The runtime certificate targets the actual flat
strip encoding, avoiding any dependence on a noncanonical drawing encoding. -/
structure NormalizedStripOrientationReduction
    {α : Type} (sourceEncoding : _root_.Computability.FinEncoding α)
    (source : α → Prop) where
  drawing : α → PeriodicOrthogonalDrawing
  stripComputableInPolyTime :
    ∀ tromino : Tromino,
      Nonempty
        (TM2ComputableInPolyTime sourceEncoding.encode
          PeriodicStripFlatEncoding.finEncoding.encode
          (fun input => (drawing input).periodicStrip tromino))
  wellFormed : ∀ input, (drawing input).IsWellFormed
  verticesSeparated : ∀ input, (drawing input).VerticesSeparated
  blankVerticalBoundary :
    ∀ input, (drawing input).HasBlankVerticalBoundary
  correct : ∀ input, source input ↔ (drawing input).HasOrientation

namespace NormalizedStripOrientationReduction

variable {α : Type}
    {sourceEncoding : _root_.Computability.FinEncoding α}
    {source : α → Prop}

/-- Any certified blank-bordered normalized drawing compiler is already a
polynomial-time reduction to either tromino strip problem. -/
theorem polyTimeManyOneReducible
    (reduction : NormalizedStripOrientationReduction sourceEncoding source)
    (tromino : Tromino)
    (behavior : OrientationBehaviorCorrect tromino) :
    Complexity.PolyTimeManyOneReducible sourceEncoding
      PeriodicStripFlatEncoding.finEncoding source
      (PeriodicStripTrominoTiling tromino) := by
  refine Complexity.PolyTimeManyOneReducible.of_computableInPolyTime
    (fun input => (reduction.drawing input).periodicStrip tromino)
    (reduction.stripComputableInPolyTime tromino) ?_
  intro input
  exact (reduction.correct input).trans
    (PeriodicOrthogonalDrawing.periodicStrip_correct_of_normalized_blankBoundary
      tromino behavior (reduction.drawing input)
      (reduction.wellFormed input)
      (reduction.verticesSeparated input)
      (reduction.blankVerticalBoundary input))

end NormalizedStripOrientationReduction

/-- The one remaining concrete compiler interface for the 1.5D hardness
proof: local one-dimensional periodic CNF to a blank-bordered normalized
strip drawing. -/
abbrev LocalPeriodicCNF1DStripReduction :=
  NormalizedStripOrientationReduction
    PeriodicCNFFlatEncoding.finEncoding
    PeriodicCNF.LocalPeriodicCNF1DSAT

/-- A local-periodic-CNF strip compiler transports the already proved source
PSPACE-hardness to either verified tromino gadget library. -/
theorem periodicStripTrominoTiling_PSPACEHard_of_localPeriodicCNFReduction
    (reduction : LocalPeriodicCNF1DStripReduction)
    (tromino : Tromino)
    (behavior : OrientationBehaviorCorrect tromino) :
    Complexity.PSPACEHard PeriodicStripFlatEncoding.finEncoding
      (PeriodicStripTrominoTiling tromino) := by
  intro α sourceEncoding source sourceInPSPACE
  exact
    (PeriodicCNF.PolySpaceHardness.localPeriodicCNF1DSAT_PSPACEHard
      sourceEncoding source sourceInPSPACE).trans
      (reduction.polyTimeManyOneReducible tromino behavior)

/-- One concrete local-CNF drawing compiler discharges the entire 1.5D
statement of Theorem 5.2 for both trominoes. -/
theorem theorem52_stripStatement_of_localPeriodicCNFReduction
    (membership : ∀ tromino : Tromino,
      Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
        (PeriodicStripTrominoTiling tromino))
    (reduction : LocalPeriodicCNF1DStripReduction) :
    Theorem52.stripStatement := by
  intro tromino
  refine ⟨membership tromino, ?_⟩
  cases tromino with
  | I =>
      exact periodicStripTrominoTiling_PSPACEHard_of_localPeriodicCNFReduction
        reduction .I iOrientationBehaviorCorrect
  | L =>
      exact periodicStripTrominoTiling_PSPACEHard_of_localPeriodicCNFReduction
        reduction .L lOrientationBehaviorCorrect

end Gadget
end LeanTrominoes
