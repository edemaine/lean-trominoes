/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierStartOriginalData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierStartRawData

/-! # Unfolded final-carrier start certificates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Opaque certificate exposing the raw start through the equality-parameterized
original computation. -/
structure DirectSourceFinalCarrierStartUnfolded
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierRawStart decider symbols =
    directSourceFinalCarrierOriginalStart decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
