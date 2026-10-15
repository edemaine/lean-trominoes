/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierStartGenericData

/-! # Formula-base equality transport for direct carrier starts -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Changing only the formula's propositionally unique base equality leaves
the structural crossover-prefix length unchanged. -/
theorem directSourceFinalCarrierStructuralRawStart_equality
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierStructuralRawStartEquality decider symbols := by
  constructor
  unfold directSourceFinalCarrierStructuralRawStart
    directSourceFinalCarrierGenericRawStart
  exact congrArg
    (fun equality =>
      (@crossoverMetadataNormalizedClausesDedup Variable
        directSourceFinalStructuralVariableDecidableEq
          (@PeriodicThreeSATThree.formula (ThreeCNFVariable Nat) equality
            (directThreeCNFSourceFormula decider symbols))).length)
    (Subsingleton.elim _ _)

end LeanTrominoes.PeriodicCNFStripReduction

end
