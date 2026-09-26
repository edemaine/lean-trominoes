/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalElementCodeNumberingSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMProblemSemanticBridge
import LeanTrominoes.UnaryColumnKeyedRelation
import LeanTrominoes.UnaryFieldAggregateCompiler
import LeanTrominoes.UnaryFieldClosure

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
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeThreeDMStack (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

abbrev nativeThreeDMProblem (s : List encoding.Γ) :=
  horizontalThreeDMProblemComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)

abbrev nativeThreeDMElements (s : List encoding.Γ) :=
  CountedContractedIncidence.horizontalElementPairs (nativeThreeDMProblem decider s)

abbrev nativeThreeDMIncidences (s : List encoding.Γ) := (nativeThreeDMProblem decider s).incidenceTags

theorem nativeThreeDMOneColorCodes (s : List encoding.Γ) (color : WireColor) :
    directSourceFinalOneColorElementCodes decider color s =
      (List.range ((nativeThreeDMProblem decider s).elementCount color)).map
        (fun atom => directSourceFinalHorizontalElementCode decider s (color,atom)) := by
  rw [directSourceFinalOneColorElementCodes_eq_horizontalTyped]
  unfold nativeThreeDMProblem directSourceFinalHorizontalElementCode
  rw [horizontalThreeDMProblemComputed_eq_semantic]
  exact (TypedElementCode.encodedElement_map_range _ _ color).symm

def nativeThreeDMElementCountCompiler (color : WireColor) :
    ScalarCompiler (fun s => (nativeThreeDMProblem decider s).elementCount color) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOneColorElementCodesComputableInPolyTime decider color)
    UnaryFieldAggregate.countCompiler
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [nativeThreeDMOneColorCodes,List.length_map,List.length_range]

def nativeThreeDMElementIndexCompiler [Inhabited encoding.Γ] :
    Compiler (nativeThreeDMElements decider) (fun _ e => e.2) := by
  let physical := UnaryFieldClosure.appendCompiler id _ _
    (naturalRange (nativeThreeDMElementCountCompiler decider .red))
    (UnaryFieldClosure.appendCompiler id _ _
      (naturalRange (nativeThreeDMElementCountCompiler decider .green))
      (naturalRange (nativeThreeDMElementCountCompiler decider .blue)))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp [nativeThreeDMElements,CountedContractedIncidence.horizontalElementPairs,
    incidenceColors,List.map_map]

def nativeThreeDMElementKeyCompiler : Compiler (nativeThreeDMElements decider)
    (directSourceFinalHorizontalElementCode decider) := by
  apply TM2ComputableInPolyTime.of_eq (directSourceFinalCanonicalElementCodesComputableInPolyTime decider)
  intro s
  exact directSourceFinalCanonicalElementCodes_eq_horizontal decider s

def nativeThreeDMIncidenceKeyCompiler : Compiler (nativeThreeDMIncidences decider)
    (fun s tag => directSourceFinalHorizontalElementCode decider s ((nativeThreeDMProblem decider s).incidenceElement tag)) := by
  apply TM2ComputableInPolyTime.of_eq (directSourceFinalCanonicalIncidenceElementCodesComputableInPolyTime decider)
  intro s
  exact directSourceFinalCanonicalIncidenceElementCodes_eq_horizontal decider s

theorem nativeThreeDMElement_mem (s : List encoding.Γ) (e : WireColor × Nat) :
    e ∈ nativeThreeDMElements decider s ↔ e.2 < (nativeThreeDMProblem decider s).elementCount e.1 := by
  rcases e with ⟨color,atom⟩
  cases color <;> simp [nativeThreeDMElements,CountedContractedIncidence.horizontalElementPairs,incidenceColors]

theorem nativeThreeDMWellFormed (s : List encoding.Γ) : (nativeThreeDMProblem decider s).IsWellFormed := by
  rw [nativeThreeDMProblem,horizontalThreeDMProblemComputed_eq_problem]
  exact (presentation _).problemWellFormed

theorem nativeThreeDMIncidenceElement_mem (s : List encoding.Γ) (tag : IncidenceTag)
    (ht : tag ∈ nativeThreeDMIncidences decider s) :
    (nativeThreeDMProblem decider s).incidenceElement tag ∈ nativeThreeDMElements decider s := by
  rw [nativeThreeDMElement_mem]
  have bound := incidenceTag_tripleIndex_lt (nativeThreeDMProblem decider s) ht
  unfold incidenceElement
  dsimp only
  rw [List.getD_eq_getElem _ _ bound]
  exact nativeThreeDMWellFormed decider s _ (List.getElem_mem bound) tag.color

def nativeThreeDMIncidenceAtomCompiler [Inhabited encoding.Γ] : Compiler (nativeThreeDMIncidences decider)
    (fun s tag => ((nativeThreeDMProblem decider s).incidenceElement tag).2) := by
  apply keyedRelation (nativeThreeDMIncidenceKeyCompiler decider)
    (nativeThreeDMElementKeyCompiler decider) (nativeThreeDMElementIndexCompiler decider)
  · intro s a ha b hb eq
    have unique := directSourceFinalCanonicalElementCodes_nodup decider s
    rw [directSourceFinalCanonicalElementCodes_eq_horizontal] at unique
    have same : a = b := List.inj_on_of_nodup_map unique ha hb eq
    exact congrArg Prod.snd same
  · intro s tag ht
    exact ⟨_,nativeThreeDMIncidenceElement_mem decider s tag ht,rfl⟩
  · intro s tag ht e he eq
    have same := (directSourceFinalHorizontalIncidenceCode_eq_iff decider s e
      ((nativeThreeDMElement_mem decider s e).1 he) tag ht).1 eq.symm
    exact congrArg Prod.snd same.symm

end LeanTrominoes.PeriodicCNFStripReduction
end
