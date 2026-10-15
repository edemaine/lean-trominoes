/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Native.PeriodicCNFStripNativeThreeDMSourceCoordinates
import LeanTrominoes.Tiling.Tromino.Strip.Problem.PeriodicCNFStripProblemOneDimensional
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Element.PeriodicCNFStripDirectSourceFinalElementCodeNumberingSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalThreeDMProblemSemanticBridge
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnKeyedRelation
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldAggregateCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldClosure

/-! # Native 3DM element counts and dense incidence indices

Structural element codes identify the canonical color classes. A compiled
lookup recovers the actual dense indices used by the natural-number 3DM
instance; unused numeric codes do not introduce isolated elements.
-/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Gadget PeriodicThreeDM Turing UnaryColumn
attribute [local instance] sourceVariableDecidableEq horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (source : PeriodicCNF.ProgramSource encoding language)
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

abbrev programThreeDMProblem (s : List encoding.Γ) :=
  horizontalThreeDMProblemComputed (source.formulaOfSymbols s)

abbrev programThreeDMElements (s : List encoding.Γ) :=
  CountedContractedIncidence.horizontalElementPairs (programThreeDMProblem source s)

abbrev programThreeDMIncidences (s : List encoding.Γ) := (programThreeDMProblem source s).incidenceTags

theorem programThreeDMOneColorCodes (s : List encoding.Γ) (color : WireColor) :
    directSourceFinalOneColorElementCodes source color s =
      (List.range ((programThreeDMProblem source s).elementCount color)).map
        (fun atom => directSourceFinalHorizontalElementCode source s (color,atom)) := by
  rw [directSourceFinalOneColorElementCodes_eq_horizontalTyped]
  unfold programThreeDMProblem directSourceFinalHorizontalElementCode
  rw [horizontalThreeDMProblemComputed_eq_semantic]
  exact (TypedElementCode.encodedElement_map_range _ _ color).symm

def programThreeDMElementCountCompiler (color : WireColor) :
    ScalarCompiler (fun s => (programThreeDMProblem source s).elementCount color) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOneColorElementCodesComputableInPolyTime source color)
    UnaryFieldAggregate.countCompiler
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [programThreeDMOneColorCodes,List.length_map,List.length_range]

def programThreeDMElementIndexCompiler [Inhabited encoding.Γ] :
    Compiler (programThreeDMElements source) (fun _ e => e.2) := by
  let physical := UnaryFieldClosure.appendCompiler id _ _
    (naturalRange (programThreeDMElementCountCompiler source .red))
    (UnaryFieldClosure.appendCompiler id _ _
      (naturalRange (programThreeDMElementCountCompiler source .green))
      (naturalRange (programThreeDMElementCountCompiler source .blue)))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp [programThreeDMElements,CountedContractedIncidence.horizontalElementPairs,
    incidenceColors,List.map_map]

def programThreeDMElementKeyCompiler : Compiler (programThreeDMElements source)
    (directSourceFinalHorizontalElementCode source) := by
  apply TM2ComputableInPolyTime.of_eq (directSourceFinalCanonicalElementCodesComputableInPolyTime source)
  intro s
  exact directSourceFinalCanonicalElementCodes_eq_horizontal source s

def programThreeDMIncidenceKeyCompiler : Compiler (programThreeDMIncidences source)
    (fun s tag => directSourceFinalHorizontalElementCode source s ((programThreeDMProblem source s).incidenceElement tag)) := by
  apply TM2ComputableInPolyTime.of_eq (directSourceFinalCanonicalIncidenceElementCodesComputableInPolyTime source)
  intro s
  exact directSourceFinalCanonicalIncidenceElementCodes_eq_horizontal source s

theorem programThreeDMElement_mem (s : List encoding.Γ) (e : WireColor × Nat) :
    e ∈ programThreeDMElements source s ↔ e.2 < (programThreeDMProblem source s).elementCount e.1 := by
  rcases e with ⟨color,atom⟩
  cases color <;> simp [programThreeDMElements,CountedContractedIncidence.horizontalElementPairs,incidenceColors]

theorem programThreeDMWellFormed (s : List encoding.Γ) : (programThreeDMProblem source s).IsWellFormed := by
  rw [programThreeDMProblem,horizontalThreeDMProblemComputed_eq_problem]
  exact (presentation _).problemWellFormed

theorem programThreeDMIncidenceElement_mem (s : List encoding.Γ) (tag : IncidenceTag)
    (ht : tag ∈ programThreeDMIncidences source s) :
    (programThreeDMProblem source s).incidenceElement tag ∈ programThreeDMElements source s := by
  rw [programThreeDMElement_mem]
  have bound := incidenceTag_tripleIndex_lt (programThreeDMProblem source s) ht
  unfold incidenceElement
  dsimp only
  rw [List.getD_eq_getElem _ _ bound]
  exact programThreeDMWellFormed source s _ (List.getElem_mem bound) tag.color

def programThreeDMIncidenceAtomCompiler [Inhabited encoding.Γ] : Compiler (programThreeDMIncidences source)
    (fun s tag => ((programThreeDMProblem source s).incidenceElement tag).2) := by
  apply keyedRelation (programThreeDMIncidenceKeyCompiler source)
    (programThreeDMElementKeyCompiler source) (programThreeDMElementIndexCompiler source)
  · intro s a ha b hb eq
    have unique := directSourceFinalCanonicalElementCodes_nodup source s
    rw [directSourceFinalCanonicalElementCodes_eq_horizontal] at unique
    have same : a = b := List.inj_on_of_nodup_map unique ha hb eq
    exact congrArg Prod.snd same
  · intro s tag ht
    exact ⟨_,programThreeDMIncidenceElement_mem source s tag ht,rfl⟩
  · intro s tag ht e he eq
    have same := (directSourceFinalHorizontalIncidenceCode_eq_iff source s e
      ((programThreeDMElement_mem source s e).1 he) tag ht).1 eq.symm
    exact congrArg Prod.snd same.symm


theorem programThreeDMDegree (s : List encoding.Γ) : (programThreeDMProblem source s).DegreeTwoOrThree := by
  rw [programThreeDMProblem,horizontalThreeDMProblemComputed_eq_problem]
  exact problem_degreeTwoOrThree _

theorem programTriplePositions_length (s : List encoding.Γ) :
    (horizontalThreeDMTriplePositionsComputed (source.formulaOfSymbols s)).length =
      (programThreeDMProblem source s).triples.length := by
  simp [horizontalThreeDMTriplePositionsComputed,programThreeDMProblem,
    horizontalThreeDMProblemComputed,PeriodicPlanarOneInThreeToThreeDM.encodedProblem,
    PeriodicPlanarOneInThreeToThreeDM.TypedProblem.encode,PeriodicPlanarOneInThreeToThreeDM.problem]
  exact congrArg (fun deq : DecidableEq RoutedVariable =>
    (@PeriodicPlanarOneInThreeToThreeDM.triples RoutedVariable deq
      (horizontalNormalizedRoutedFormulaComputed (source.formulaOfSymbols s)).erase).length)
    (Subsingleton.elim horizontalThreeDMTripleVariableDecidableEq horizontalRibbonRoutedVariableDecidableEq)

def programThreeDMTripleCountCompiler [Inhabited encoding.Γ] :
    ScalarCompiler (fun s => (programThreeDMProblem source s).triples.length) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalTripleCoordinatesComputableInPolyTime source true true) UnaryFieldAggregate.countCompiler
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [directSourceFinalTripleCoordinates_length,programTriplePositions_length]

end LeanTrominoes.PeriodicCNFStripReduction
end
