/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseExpandedMotifFiniteTokens
import LeanTrominoes.PeriodicCNFStripDirectPreparedHeaderData
import LeanTrominoes.PeriodicCNFStripDirectSparseAssignmentBounds

/-! # Prepared tokens for the direct sparse strip target -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparsePreparedDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Prepared header followed by one affine finite-token block per pixel of
the sparse assignment motif. -/
def directSparseCompiledTrominoStripPreparedTokensOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) :
    List GadgetPixelFiniteTokens.Token :=
  directPreparedHeaderOfSymbols decider symbols ++
    GadgetSparseExpandedMotifFiniteTokens.preparedSparseExpandedMotif
      tromino (directSparseAssignmentsOfSymbols decider symbols)

/-- Counted finite-token stream corresponding to the sparse target's exact
flat fields before motif-length insertion. -/
def directSparseCompiledTrominoStripCountedTokensOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) :
    List PeriodicCNF.UnaryProgramTokens.Token :=
  let target := directSparseCompiledTrominoStripOfSymbols
    decider tromino symbols
  CountedUnaryFieldTokens.fields [target.width, target.period] ++
    CountedUnaryFieldTokens.countedFieldBlocks
      (target.motif.map PeriodicStripFlatEncoding.cellFields)

end PeriodicCNFStripReduction
end LeanTrominoes
