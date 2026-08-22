/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorMetadataData

/-! # Five retained metadata clause-descriptor families -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

def crossoverMetadataClauseDescriptors {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (drawingPlanarSATCrossoverClauseMetadata
      (PeriodicCNF.incidenceGraph source)).map
    (metadataClauseDescriptor source)

def carrierMetadataClauseDescriptors {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (retainedDrawingPlanarSATCarrierClauseMetadata
      (PeriodicCNF.incidenceGraph source)).map
    (metadataClauseDescriptor source)

def bendMetadataClauseDescriptors {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (drawingPlanarSATBendClauseMetadata
      (PeriodicCNF.incidenceGraph source)).map
    (metadataClauseDescriptor source)

def routedClauseMetadataClauseDescriptors {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (drawingPlanarSATRoutedClauseMetadata source).map
    (metadataClauseDescriptor source)

def routedVariableMetadataClauseDescriptors {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (drawingPlanarSATRoutedVariableClauseMetadata source).map
    (metadataClauseDescriptor source)

/-- The complete undeduplicated candidate stream as its exact five retained
metadata-family blocks. -/
def familyMetadataClauseDescriptors {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  crossoverMetadataClauseDescriptors source ++
    carrierMetadataClauseDescriptors source ++
      bendMetadataClauseDescriptors source ++
        routedClauseMetadataClauseDescriptors source ++
          routedVariableMetadataClauseDescriptors source

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
