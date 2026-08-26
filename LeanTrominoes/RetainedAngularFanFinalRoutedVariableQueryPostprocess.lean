/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryTemplates

/-! # Finite postprocess for final routed-variable queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The six current-slice metadata templates paired with their stable direct
query replacements. -/
def retainedFinalDirectRoutedVariableQueryTable :
    List (FormulaShapeDirectionOrdering.Token ×
      RetainedFinalCopiedClauseQuery) :=
  [(routedVariableClauseDescriptor .left false true,
      retainedFinalDirectRoutedVariableClauseQuery .left false true),
    (routedVariableClauseDescriptor .left false false,
      retainedFinalDirectRoutedVariableClauseQuery .left false false),
    (routedVariableClauseDescriptor .middle false true,
      retainedFinalDirectRoutedVariableClauseQuery .middle false true),
    (routedVariableClauseDescriptor .middle false false,
      retainedFinalDirectRoutedVariableClauseQuery .middle false false),
    (routedVariableClauseDescriptor .right false true,
      retainedFinalDirectRoutedVariableClauseQuery .right false true),
    (routedVariableClauseDescriptor .right false false,
      retainedFinalDirectRoutedVariableClauseQuery .right false false)]

/-- Replace one metadata template by its stable direct query.  The total
fallback is unreachable on normalized routed-variable blocks. -/
def retainedFinalDirectRoutedVariableQueryOfToken
    (token : FormulaShapeDirectionOrdering.Token) :
    RetainedFinalCopiedClauseQuery :=
  ((retainedFinalDirectRoutedVariableQueryTable.find? fun entry =>
      entry.1 = token).map Prod.snd).getD default

/-- Singleton-output form consumed by the finite block transducer. -/
def retainedFinalDirectRoutedVariableQueryBlock
    (token : FormulaShapeDirectionOrdering.Token) :
    List RetainedFinalCopiedClauseQuery :=
  [retainedFinalDirectRoutedVariableQueryOfToken token]

/-- The finite postprocess sends each current-slice routed-variable
descriptor to its matching stable direct query. -/
theorem retainedFinalDirectRoutedVariableQueryBlock_descriptor_eq
    (arm : DuplicatorArm) (forward : Bool) :
    retainedFinalDirectRoutedVariableQueryBlock
        (routedVariableClauseDescriptor arm false forward) =
      [retainedFinalDirectRoutedVariableClauseQuery arm false forward] := by
  cases arm <;> cases forward <;> native_decide

/-- Elementwise replacement sends one normalized metadata site block to the
six stable direct queries in the same clause order. -/
theorem routedVariableFullSiteBlock_finalQueryBlock_eq :
    routedVariableFullSiteBlock.flatMap
        retainedFinalDirectRoutedVariableQueryBlock =
      retainedFinalDirectRoutedVariableFullSiteQueries := by
  native_decide

end PeriodicEightOccurrenceSplit
end LeanTrominoes
