/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectExecutableFields
import LeanTrominoes.CountedUnaryFieldTokens

/-! # Counted finite-token data for direct strip hardness -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing Gadget
open UnaryFieldEncoderMachine
open PeriodicCNF.UnaryProgramTokens
open CountedUnaryFieldTokens

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Fields emitted directly before the counted motif-length header is
inserted. -/
def directCompiledTrominoStripBodyFieldsOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) : List Nat :=
  let drawing := directCompiledStripDrawingOfSymbols decider symbols
  let motif := directCompiledTrominoMotifOfSymbols decider tromino symbols
  [6 * drawing.verticalPeriod, 6 * drawing.horizontalPeriod] ++
    motif.flatMap PeriodicStripFlatEncoding.cellFields

/-- Finite unary width and period fields followed by a streamable counted
block for each motif cell. -/
def directCompiledTrominoStripCountedTokensOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) : List Token :=
  let drawing := directCompiledStripDrawingOfSymbols decider symbols
  let motif := directCompiledTrominoMotifOfSymbols decider tromino symbols
  CountedUnaryFieldTokens.fields
      [6 * drawing.verticalPeriod, 6 * drawing.horizontalPeriod] ++
    CountedUnaryFieldTokens.countedFieldBlocks
      (motif.map PeriodicStripFlatEncoding.cellFields)

end PeriodicCNFStripReduction
end LeanTrominoes
