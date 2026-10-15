/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaFacts
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectThreeCNFOccurrencePositiveOffsets
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Final.Carrier.RetainedAngularFanFinalCarrierSourceFacts

/-! # Final retained-carrier facts for the direct source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Package the direct width-three source hypotheses at their lightweight
pre-split presentation, avoiding any dependency on final atom-code data. -/
def directThreeCNFSourceFinalCarrierFacts
    (symbols : List encoding.Γ) :
    FinalCarrierSourceFacts
      (PeriodicThreeCNF.formula
        (ProgramSource.formulaOfSymbols decider symbols)) where
  nonemptyFacts :=
    { widthFacts :=
        { localFacts :=
            { sourceLocal :=
                PeriodicThreeCNF.formula_isLocal
                  (formulaOfSymbols_sourceAdmissible
                    decider symbols).2.1 }
          sourceWidth := PeriodicThreeCNF.formula_widthAtMostThree _ }
      sourceClausesNonempty :=
        PeriodicThreeCNF.formula_clausesNonempty _
          (formulaOfSymbols_clauses_nonempty decider symbols) }
  positiveOffsets :=
    directThreeCNFSource_occurrenceIncidences_positiveOffsets
      decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
