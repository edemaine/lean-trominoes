/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceTerminalCoordinateCompiler
import LeanTrominoes.PeriodicOrthocrossingActiveTerminalCompactKeyCompiler

/-! # Direct terminal dictionary keys aligned with physical coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directTerminalCoordinateKeyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- One compact key per physical terminal coordinate, including neighbor translates. -/
def directSourceTerminalCoordinateKeys (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  ActiveTerminalCompactKeys.words (numericRouteDescriptors (directSourceFormula decider symbols))

noncomputable def directSourceTerminalCoordinateKeysComputableInPolyTime :
    TM2ComputableInPolyTime id DelimitedBinaryWords.finEncoding.encode
      (directSourceTerminalCoordinateKeys decider) := by
  unfold directSourceTerminalCoordinateKeys
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
    ActiveTerminalCompactKeys.wordsComputableInPolyTime

/-- The key and coordinate compilers name exactly the same physical nodes in
exactly the same order. -/
theorem directSourceTerminalCoordinateKeys_eq_nodes (symbols : List encoding.Γ) :
    (directSourceTerminalCoordinateKeys decider symbols).words =
      (directSourceTerminalCoordinateNodes decider symbols).map ActiveTerminalCompactKeys.nodeWord := by
  let formula := directSourceFormula decider symbols
  have isLocal : formula.incidenceGraph.IsLocal := by
    unfold formula directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  unfold directSourceTerminalCoordinateKeys directSourceTerminalCoordinateNodes
  exact ActiveTerminalCompactKeys.words_numericRouteDescriptors formula
    (PeriodicCNF.incidenceGraph_isWellFormed formula)
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
    isLocal (directSourceFormula_isForwardLocal decider symbols)

/-- Each of the four signed coordinate columns has one entry for every key. -/
theorem directSourceTerminalCoordinateKeys_length_coordinates
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceTerminalCoordinateKeys decider symbols).words.length =
      (directSourceTerminalCoordinates decider horizontal keepPositive symbols).length := by
  rw [directSourceTerminalCoordinateKeys_eq_nodes, List.length_map,
    directSourceTerminalCoordinates_length]

end LeanTrominoes.PeriodicCNFStripReduction

end
