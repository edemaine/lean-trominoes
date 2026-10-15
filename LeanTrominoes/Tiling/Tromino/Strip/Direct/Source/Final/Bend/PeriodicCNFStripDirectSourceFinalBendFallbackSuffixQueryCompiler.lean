/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Base.PeriodicCNFStripDirectSourceBaseBendTerminalDirectionCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Base.PeriodicCNFStripDirectSourceBaseBendTerminalRadialCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Bend.PeriodicCNFStripDirectSourceFinalBendFallbackSuffixQueryLength
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Fallback.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceSlotCompiler
import LeanTrominoes.Computation.TM2.TM2EmptyAlphabetListInputCompiler

/-! # Compiling bend fallback-suffix directions -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Direct source symbols compile to the route-delimited direction words of
all retained-bend fallback suffixes. -/
noncomputable def
    directSourceFinalBendFallbackSuffixDirectionsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FallbackSuffixDirectionCompiler.OutputToken)
      encoding.Γ FallbackSuffixDirectionCompiler.OutputToken
      id id
      (directSourceFinalBendFallbackSuffixDirections decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    let directionsCompiler :=
      TM2CompositionMachine.computableInPolyTime
        (directSourceBaseBendTerminalDirectionRanksComputableInPolyTime decider)
        RetainedTerminalDirectionRankDecoder.directionsOfRanksComputableInPolyTime
    let rolesCompiler :=
      TM2CompositionMachine.computableInPolyTime directionsCompiler
        FallbackSuffixHeaderRoles.bendRolesComputableInPolyTime
    unfold directSourceFinalBendFallbackSuffixDirections
      directSourceFinalBendFallbackSuffixQueries
    exact
      FallbackSuffixQueryColumns.directionsComputableInPolyTimeOf
        id
        (directSourceFinalBendFallbackHeaderRoles decider)
        (directSourceBaseBendTerminalRadialLengths decider)
        (directSourceFinalBendOccurrenceSlots decider)
        (directSourceFinalBendFallbackRolesSlots_length decider)
        (directSourceFinalBendFallbackRolesRadials_length decider)
        rolesCompiler
        (directSourceBaseBendTerminalRadialLengthsComputableInPolyTime decider)
        (directSourceFinalBendOccurrenceSlotsComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
