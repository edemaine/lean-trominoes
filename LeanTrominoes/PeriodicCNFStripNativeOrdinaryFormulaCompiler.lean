/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryClauseColumns
import LeanTrominoes.CanonicalLiteralOffsetCompiler
import LeanTrominoes.UnaryPointFieldsCompiler
import LeanTrominoes.PositionedIncidenceHeaderBlocks
import LeanTrominoes.PositionedIncidenceFormulaFields
import LeanTrominoes.UnaryFieldClosure

/-! # Complete native formula encoding for ordinary planar SAT -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn PositionedIncidenceRows PeriodicCNFFlatEncoding DelimitedDirectionDisplacement
open UnaryFieldEncoderMachine (unaryFields unaryField)
open PeriodicCNF.FormulaShapeDirectionOrdering
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryFormulaStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryFormulaVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

def nativeOrdinaryAnchoredOffsetCompiler [Inhabited encoding.Γ] (horizontal : Bool) :
    Compiler (nativeOrdinaryRows decider) (fun _ row => Encodable.encode (component horizontal
      (Cell.sub row.2.1.offset (PeriodicCNF.clauseAnchor row.1.1.literals)))) := by
  apply canonicalLiteralOffsetCompiler (rows := nativeOrdinaryRows decider) horizontal
    (nativeOrdinaryPlacement decider) (fun _ row => row.1.1) (fun _ row => row.2.1)
    (fun s row => nativeOrdinaryRoutes decider s row.1.2 row.2.2)
    (nativeOrdinaryClauseColumn decider horizontal true) (nativeOrdinaryClauseColumn decider horizontal false)
    (nativeOrdinaryDisplacementColumn decider horizontal true) (nativeOrdinaryDisplacementColumn decider horizontal false)
    (nativeOrdinaryVariableColumn decider horizontal true) (nativeOrdinaryVariableColumn decider horizontal false)
    (nativeOrdinaryPeriodCompiler decider) (nativeOrdinaryPeriod_positive decider)
    (fun s row member => (nativeOrdinaryRoute_endpoints decider s row member).1)
    (fun s row member => (nativeOrdinaryRoute_endpoints decider s row member).2)
    (nativeOrdinaryRoute_unitSteps decider)

noncomputable def nativeOrdinaryLiteralBlocksCompiler [Inhabited encoding.Γ] :
    BlocksCompiler (nativeOrdinaryRows decider)
      (fun s row => UnaryFieldEncoderMachine.unaryFields
        (literalFields (namedLiteral (nativeOrdinaryRenaming decider s) row))) := by
  let physical : BlocksCompiler (nativeOrdinaryRows decider) (fun s row =>
      UnaryFieldEncoderMachine.unaryField (nativeOrdinaryRenaming decider s row.2.1.atom) ++
      (UnaryFieldEncoderMachine.unaryField (Encodable.encode
        (Cell.sub row.2.1.offset (PeriodicCNF.clauseAnchor row.1.1.literals)).1) ++
      (UnaryFieldEncoderMachine.unaryField (Encodable.encode
        (Cell.sub row.2.1.offset (PeriodicCNF.clauseAnchor row.1.1.literals)).2) ++
       UnaryFieldEncoderMachine.unaryField row.2.1.value.toNat))) :=
    appendBlocks (blocks (nativeOrdinaryRowAtomColumn decider))
    (appendBlocks (blocks (nativeOrdinaryAnchoredOffsetCompiler decider true))
      (appendBlocks (blocks (nativeOrdinaryAnchoredOffsetCompiler decider false))
        (blocks (nativeOrdinaryRowValueColumn decider))))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply congrArg FiniteAlphabetDelimitedBlockJoin.blocks
  apply List.map_congr_left
  intro row _
  have value : encodeBoolField row.2.1.value = row.2.1.value.toNat := by cases row.2.1.value <;> rfl
  simp only [namedLiteral, literalFields, PeriodicLiteral.rename, PeriodicLiteral.anchorNormalize,
    UnaryFieldEncoderMachine.unaryFields_cons, UnaryFieldEncoderMachine.unaryFields_nil,
    List.append_nil, value]


def nativeOrdinaryHeaderBlocksCompiler : BlocksCompiler (nativeOrdinaryRows decider) (fun _ row => header row) := by
  let physical := TM2CompositionMachine.computableInPolyTime (nativeOrdinaryProfilesCompiler decider)
    (FiniteBlockTransducer.computableInPolyTime (fun profile : DirectedClauseProfile =>
      FiniteAlphabetDelimitedBlockJoin.blocks (headerBlocks profile.orderedProfile.literals.length)))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  change _ = FiniteAlphabetDelimitedBlockJoin.blocks
    ((rows (nativeOrdinaryFormula decider s)).map header)
  rw [headers_eq_lengths]
  have shape := congrArg (List.map List.length) (nativeOrdinaryProfiles_literals decider s)
  rw [nativeOrdinaryBaseInput_formula] at shape
  simp only [List.map_map, Function.comp_def, PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles,
    List.length_map] at shape
  have h := congrArg (fun lengths => FiniteAlphabetDelimitedBlockJoin.blocks (lengths.flatMap headerBlocks)) shape
  simpa only [FiniteAlphabetDelimitedBlockJoin.blocks, List.flatMap_map, List.flatMap_assoc] using h

private theorem ordinary_encoded_row (name : OrdinaryVariable → Nat) (row : Row OrdinaryVariable) :
    header row ++ unaryFields (literalFields (namedLiteral name row)) = unaryFields (rowFields name row) := by
  unfold header rowFields
  split <;> simp [unaryFields, unaryField]

def nativeOrdinaryFormulaBodyCompiler [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id unaryFields
      (fun s => (nativeOrdinaryRows decider s).flatMap (rowFields (nativeOrdinaryRenaming decider s))) := by
  let physical := finishBlocks (appendBlocks (nativeOrdinaryHeaderBlocksCompiler decider)
    (nativeOrdinaryLiteralBlocksCompiler decider))
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  simp only [id_eq, ordinary_encoded_row]
  induction nativeOrdinaryRows decider s with
  | nil => rfl
  | cons row rest ih => simp [List.flatMap_cons, ih]

def nativeOrdinaryFormulaFieldsCompiler [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id unaryFields (fun s => formulaFields (nativeOrdinaryInput decider s).1) := by
  let counts := TM2CompositionMachine.computableInPolyTime (nativeOrdinaryClauseLengthsCompiler decider)
    UnaryFieldAggregate.countCompiler
  let physical := UnaryFieldClosure.appendCompiler id _ _ counts (nativeOrdinaryFormulaBodyCompiler decider)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [nativeOrdinaryBaseInput_formula]
  change _ = formulaFields ((nativeOrdinaryFormula decider s).erase.anchorNormalize.rename (nativeOrdinaryRenaming decider s))
  rw [formulaFields_eq _ _ (nativeOrdinaryClauses_nonempty decider s)]
  simp only [List.length_map, PositionedPeriodicCNF.erase, List.singleton_append, nativeOrdinaryRows]

end LeanTrominoes.PeriodicCNFStripReduction
end
