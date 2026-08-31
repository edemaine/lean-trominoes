/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCoordinatedOccurrenceStableRankSemantics
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankSlotBlocks

/-! # Semantic occurrence slots as global stable-rank blocks -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PeriodicThreeSATThree

/-- For a genuine final clause, its semantic occurrence-slot list is exactly
its global stable-rank block before packing into a fixed-width tuple. -/
theorem retainedFinalCoordinatedOccurrenceSlots_eq_globalStableRankBlock
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedClause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat)
    (certificate :
      RetainedOccurrenceTerminalCertificate
        (retainedFinalCoordinatedScaledSource formula).erase
        (retainedFinalCoordinatedScaledSourceRoutes formula))
    (clauseMember : taggedClause ∈
      (retainedFinalCoordinatedScaledSource formula).erase.clauses.zipIdx) :
    taggedClause.1.zipIdx.map (fun taggedLiteral =>
        retainedFinalCoordinatedOccurrenceSlot
          formula taggedLiteral.1 taggedClause.2 taggedLiteral.2) =
      retainedOccurrenceGlobalStableTerminalSlotBlock
        (retainedFinalCoordinatedScaledSource formula).erase
        (retainedFinalCoordinatedScaledSourceRoutes formula)
        taggedClause := by
  unfold retainedOccurrenceGlobalStableTerminalSlotBlock
  apply List.map_congr_left
  intro taggedLiteral literalMember
  have taggedMember := taggedLiterals_mem
    (retainedFinalCoordinatedScaledSource formula).erase
    clauseMember literalMember
  have copyMember := occurrenceVariables_mem
    (retainedFinalCoordinatedScaledSource formula).erase taggedMember
  have stableGlobal := retainedOccurrenceStableTerminalRank_eq_global
    (retainedFinalCoordinatedScaledSource formula).erase
    (retainedFinalCoordinatedScaledSourceRoutes formula)
    taggedLiteral.1.atom
    (taggedLiteral.1.atom, taggedClause.2, taggedLiteral.2)
    copyMember
  have semanticSlot :=
    retainedFinalCoordinatedOccurrenceSlot_eq_boundedStableTerminalRank
      formula taggedLiteral.1 taggedClause.2 taggedLiteral.2
      certificate taggedMember
  exact semanticSlot.trans (congrArg boundedRetainedTerminalSlot
    stableGlobal)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
