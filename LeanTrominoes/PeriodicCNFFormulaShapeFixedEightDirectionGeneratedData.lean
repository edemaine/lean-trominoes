/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionData
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterMachine

/-! # Two-pass fixed-eight direction-descriptor generation -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFixedEightDirection

open AffineTemplateEmitterMachine
open IndexedTemplateEmitter

/-- Workspace after retaining the source descriptors and appending the fixed
ring-clause codes. -/
abbrev CycleWorkspace :=
  FormulaShapeDirectionOrdering.Token ⊕ UnaryProgramTokens.Token

/-- Nine distinct fixed codes for the nine local Figure 7 clauses.  Their
meaning is local to the final decoder. -/
def cycleCodes : List UnaryProgramTokens.Token :=
  [.clauseMarker, .constant false, .constant true,
    .wireStart false, .wireStart true, .atomUnit, .atomEnd,
    .freshUnit, .freshEnd]

/-- Decode a fixed ring-clause code to its exact finite direction
descriptor. -/
def decodeCycleCode : UnaryProgramTokens.Token →
    List FormulaShapeDirectionOrdering.Token
  | .clauseMarker => (cycleClauseDescriptors[0]?).toList
  | .constant false => (cycleClauseDescriptors[1]?).toList
  | .constant true => (cycleClauseDescriptors[2]?).toList
  | .wireStart false => (cycleClauseDescriptors[3]?).toList
  | .wireStart true => (cycleClauseDescriptors[4]?).toList
  | .atomUnit => (cycleClauseDescriptors[5]?).toList
  | .atomEnd => (cycleClauseDescriptors[6]?).toList
  | .freshUnit => (cycleClauseDescriptors[7]?).toList
  | .freshEnd => (cycleClauseDescriptors[8]?).toList
  | _ => []

/-- The first retained-input pass appends one coded nine-clause ring for
every incoming variable marker. -/
def cycleFamily :
    IndexedTemplateEmitter.Family FormulaShapeDirectionOrdering.Token
  | .clause _ => none
  | .variable => some (cycleCodes.map Recipe.fixed)

/-- The second pass ignores appended ring codes and appends nine output
variable markers for every retained source variable marker. -/
def variableFamily : IndexedTemplateEmitter.Family CycleWorkspace
  | .inl (.clause _) => none
  | .inl .variable =>
      some (List.replicate FormulaShapeFixedEight.copiesPerVariable
        (.fixed .freshUnit))
  | .inr _ => none

/-- Interpret the nested retained workspace in the desired phase order:
copied source clauses, all ring clauses, then all output variables. -/
def decodeGeneratedItem :
    (CycleWorkspace ⊕ UnaryProgramTokens.Token) →
      List FormulaShapeDirectionOrdering.Token
  | .inl (.inl token) => copiedClauseBlock token
  | .inl (.inr code) => decodeCycleCode code
  | .inr _ => [.variable]

/-- Machine-shaped two-pass descriptor stream. -/
def generatedDescriptors
    (source : List FormulaShapeDirectionOrdering.Token) :
    List FormulaShapeDirectionOrdering.Token :=
  (IndexedTemplateEmitterMachine.appendedOutput variableFamily
    (IndexedTemplateEmitterMachine.appendedOutput
      cycleFamily source)).flatMap decodeGeneratedItem

end FormulaShapeFixedEightDirection
end PeriodicCNF
end LeanTrominoes
