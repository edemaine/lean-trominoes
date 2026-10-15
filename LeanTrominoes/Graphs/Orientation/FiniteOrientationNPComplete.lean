/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.FiniteOrientationNP
import LeanTrominoes.Tiling.Tromino.Finite.FiniteProgramCompletion
import LeanTrominoes.Tiling.Tromino.Finite.FiniteProgramTrominoRegionCompiler
import LeanTrominoes.Complexity.FiniteNPProgramSource
import Lean.Util.CollectAxioms

/-! # NP completeness of finite normalized planar orientation -/
noncomputable section
namespace LeanTrominoes.Gadget.FiniteOrientation
open _root_.Computability Turing Complexity PeriodicCNF PeriodicCNFStripReduction
set_option maxHeartbeats 2000000

def recordsOfEntries (data : List CompletionPattern.Runtime.DrawingEntry) : Records :=
  data.map fun a => ((a.1.1.toNat,a.1.2.toNat),a.2)

theorem entries_recordsOfEntries (data : List CompletionPattern.Runtime.DrawingEntry)
    (bounds : ∀ a ∈ data, 0 ≤ a.1.1 ∧ 0 ≤ a.1.2) :
    entries (recordsOfEntries data) = data := by
  rw [entries,recordsOfEntries,List.map_map]
  trans data.map id
  · apply List.map_congr_left
    intro a ha
    have bounded := bounds a ha
    simp [Int.toNat_of_nonneg bounded.1,Int.toNat_of_nonneg bounded.2]
  · exact List.map_id data

attribute [irreducible] recordsOfEntries

variable {Source : Type} {encoding : FiniteEncoding Source} {language : Source → Prop}
  (source : ProgramSource encoding language)
  (zero : ∀ symbols, FiniteCNF.ZeroOffsets (source.formulaOfSymbols symbols))

include zero in
private theorem reduction_valid (symbols : List encoding.Γ) :
    Valid (recordsOfEntries (FiniteProgramSparseTrominoRegion.assignments source symbols)) := by
  have model := FiniteProgramCompletion.sparseModel source zero symbols
  have recordsEq := entries_recordsOfEntries _ (fun a ha =>
    ⟨(model.bounds a ha).1,(model.bounds a ha).2.2.1⟩)
  rw [Valid,recordsEq]
  exact ⟨FiniteProgramCompletion.assignments_keysNodup source zero symbols,
    FiniteProgramCompletion.drawing source zero symbols,
    (FiniteProgramCompletion.drawing_facts source zero symbols).1,
    (FiniteProgramCompletion.drawing_facts source zero symbols).2.1,
    (FiniteProgramCompletion.drawing_facts source zero symbols).2.2.1,model⟩

def reductionOfSymbols (symbols : List encoding.Γ) : Input :=
  ⟨recordsOfEntries (FiniteProgramSparseTrominoRegion.assignments source symbols),
    reduction_valid source zero symbols⟩

theorem reduction_entries (symbols : List encoding.Γ) :
    entries (reductionOfSymbols source zero symbols).1 =
      FiniteProgramSparseTrominoRegion.assignments source symbols := by
  have model := FiniteProgramCompletion.sparseModel source zero symbols
  dsimp only [reductionOfSymbols]
  exact entries_recordsOfEntries (FiniteProgramSparseTrominoRegion.assignments source symbols) (fun a ha =>
    ⟨(model.bounds a ha).1,(model.bounds a ha).2.2.1⟩)

def reduction (input : Source) : Input := reductionOfSymbols source zero (encoding.encode input)

theorem reduction_correct (input : Source) : language input ↔ Problem (reduction source zero input) := by
  rw [problem_iff,region,reduction,reduction_entries]
  exact FiniteProgramSparseTrominoRegion.correct source zero .I input

def reductionOfSymbolsComputer : TM2ComputableInPolyTime id finEncoding.encode
    (reductionOfSymbols source zero) := by
  classical
  by_cases nonempty : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonempty⟩
    apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq
      (FiniteProgramSparseTrominoRegion.assignmentTokensComputableInPolyTime source zero)
    intro symbols
    simp only [FiniteEncoding.encode,finEncoding,reduction_entries]
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonempty ⟨symbol⟩⟩
    letI : Inhabited finEncoding.Γ := ⟨GadgetSparseAssignmentTokens.Token.fieldEnd⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime finEncoding.encode
      (reductionOfSymbols source zero)

def reductionComputer : TM2ComputableInPolyTime encoding.encode finEncoding.encode
    (reduction source zero) :=
  TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode
    (reductionOfSymbolsComputer source zero) (fun _ => rfl) (fun _ => rfl)

/-- Hardness is measured against the original NP input, before any drawing
or gadget data have been computed. -/
theorem npHard : NPHard finEncoding Problem := by
  intro Source sourceEncoding language member
  obtain ⟨verifier⟩ := member
  let source := FiniteNPProgramSource.source verifier
  let zero := FiniteNPProgramSource.formula_zero verifier
  exact PolyTimeManyOneReducible.of_computableInPolyTime (reduction source zero)
    ⟨reductionComputer source zero⟩ (reduction_correct source zero)

theorem npComplete : NPComplete finEncoding Problem := ⟨inNP,npHard⟩

open Lean Elab Command in
run_cmd do
  let name := ``npComplete
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do
    throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.Gadget.FiniteOrientation
