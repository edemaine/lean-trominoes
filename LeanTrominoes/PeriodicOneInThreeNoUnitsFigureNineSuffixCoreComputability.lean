/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedRoutesComputability
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalRouteComputability
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOrderedInheritedRouteFamily
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerComputability

/-!
# Computability of the composed Figure 9 suffix core

For a twice-inherited literal, distinct source atoms make its original
source-clause index executable by a finite `idxOf` lookup.  The ordered
connector selected at that index depends only on the source route's first
direction.  This module computes that proof-free connector and identifies it
with the suffix selected by the established provenance certificate.
-/

noncomputable section

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

set_option maxHeartbeats 4000000
set_option linter.overlappingInstances false

open PeriodicOrthocrossing

/-- Index of an atom in the distinct atom presentation of a source clause.
The clause length is the harmless fallback when the atom is absent. -/
def sourceLiteralIndexForAtom
    {Variable : Type*} [DecidableEq Variable]
    (sourceClause : PositionedPeriodicClause Variable)
    (atom : Variable) : Nat :=
  (sourceClause.literals.map PeriodicLiteral.atom).idxOf atom

theorem sourceLiteralIndexForAtom_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PositionedPeriodicClause Variable × Variable =>
      sourceLiteralIndexForAtom input.1 input.2 := by
  have atoms : Primrec fun input :
      PositionedPeriodicClause Variable × Variable =>
      input.1.literals.map PeriodicLiteral.atom := by
    exact Primrec.list_map
      (PositionedPeriodicClause.literals_primrec.comp Primrec.fst)
      (PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd).to₂
  exact (Primrec.list_idxOf.comp Primrec.snd atoms).of_eq fun _ => rfl

/-- Saturate a natural source index to one of the three connector slots. -/
def boundedSourceSlot : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

@[simp]
theorem boundedSourceSlot_val_of_lt_three
    {index : Nat} (indexLt : index < 3) :
    (boundedSourceSlot index).val = index := by
  interval_cases index <;> rfl

theorem boundedSourceSlot_primrec : Primrec boundedSourceSlot := by
  have zero : PrimrecPred fun index : Nat => index = 0 :=
    Primrec.eq.comp Primrec.id (Primrec.const 0)
  have one : PrimrecPred fun index : Nat => index = 1 :=
    Primrec.eq.comp Primrec.id (Primrec.const 1)
  exact (Primrec.ite zero (Primrec.const 0)
    (Primrec.ite one (Primrec.const 1) (Primrec.const 2))).of_eq
      fun index => by
        rcases index with _ | _ | index <;> rfl

/-- The finite connector table, indexed directly by a natural source slot
and its source route's first direction. -/
def sourceConnectorRoute (slot : Nat)
    (direction : AxisDirection) : List Cell :=
  match slot, direction with
  | 0, .east => [(36, 0), (72, 0)]
  | 0, .south => [(36, 0), (36, -73), (0, -73), (0, -72)]
  | 0, .west =>
      [(36, 0), (36, -73), (-73, -73), (-73, 0), (-72, 0)]
  | 0, .north =>
      [(36, 0), (73, 0), (73, 73), (0, 73), (0, 72)]
  | 1, .south => [(0, 30), (0, -72)]
  | 1, .west => [(0, 30), (-73, 30), (-73, 0), (-72, 0)]
  | 1, .north => [(0, 30), (0, 72)]
  | 2, .west =>
      [(72, 30), (73, 30), (73, 73), (-73, 73),
        (-73, 0), (-72, 0)]
  | 2, .north =>
      [(72, 30), (73, 30), (73, 73), (0, 73), (0, 72)]
  | _, _ => []

private theorem sourceConnectorRoute_zero_primrec :
    Primrec (sourceConnectorRoute 0) :=
  Primrec.dom_finite (sourceConnectorRoute 0)

private theorem sourceConnectorRoute_one_primrec :
    Primrec (sourceConnectorRoute 1) :=
  Primrec.dom_finite (sourceConnectorRoute 1)

private theorem sourceConnectorRoute_two_primrec :
    Primrec (sourceConnectorRoute 2) :=
  Primrec.dom_finite (sourceConnectorRoute 2)

theorem sourceConnectorRoute_primrec :
    Primrec fun input : Nat × AxisDirection =>
      sourceConnectorRoute input.1 input.2 := by
  have zero : PrimrecPred fun input : Nat × AxisDirection =>
      input.1 = 0 :=
    Primrec.eq.comp Primrec.fst (Primrec.const 0)
  have one : PrimrecPred fun input : Nat × AxisDirection =>
      input.1 = 1 :=
    Primrec.eq.comp Primrec.fst (Primrec.const 1)
  have two : PrimrecPred fun input : Nat × AxisDirection =>
      input.1 = 2 :=
    Primrec.eq.comp Primrec.fst (Primrec.const 2)
  exact (Primrec.ite zero
    (sourceConnectorRoute_zero_primrec.comp Primrec.snd)
    (Primrec.ite one
      (sourceConnectorRoute_one_primrec.comp Primrec.snd)
      (Primrec.ite two
        (sourceConnectorRoute_two_primrec.comp Primrec.snd)
        (Primrec.const [])))).of_eq fun input => by
          rcases input with ⟨index, direction⟩
          rcases index with _ | _ | _ | index <;> rfl

theorem sourceConnectorRoute_eq
    {Variable : Type*}
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceClauseIndex sourceLiteralIndex : Nat)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceLiteralIndexLt : sourceLiteralIndex < 3) :
    sourceConnectorRoute sourceLiteralIndex
        (AxisDirection.polylineFirstDirection
          (sourceRoutes sourceClauseIndex sourceLiteralIndex)) =
      (PositionedPeriodicCNF.clauseExitFanData
        sourceClause sourceClauseIndex sourceRoutes).route
          (boundedSourceSlot sourceLiteralIndex) := by
  change sourceConnectorRoute sourceLiteralIndex
      (AxisDirection.polylineFirstDirection
        (sourceRoutes sourceClauseIndex sourceLiteralIndex)) =
    sourceConnectorRoute (boundedSourceSlot sourceLiteralIndex).val
      (AxisDirection.polylineFirstDirection
        (sourceRoutes sourceClauseIndex
          (boundedSourceSlot sourceLiteralIndex).val))
  rw [boundedSourceSlot_val_of_lt_three sourceLiteralIndexLt]

/-- Proof-free ordered inherited suffix selected by its natural source
literal index and source route. -/
def fanInheritedRouteSuffixAtIndex
    {Variable : Type*}
    (outputPeriod sourcePeriod : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable)))
    (sourceLiteralIndex : Nat)
    (sourceRoute : List Cell) : List Cell :=
  let origin :=
    Cell.sub
      (Cell.scale composedGadgetScale sourceClause.position)
      (Cell.scale outputPeriod
        (PeriodicCNF.clauseAnchor generatedClause.literals))
  let sourceCanonical :=
    Cell.sub sourceClause.position
      (Cell.scale sourcePeriod
        (PeriodicCNF.clauseAnchor sourceClause.literals))
  let shift :=
    Cell.sub origin
      (Cell.scale composedGadgetScale sourceCanonical)
  let transformed :=
    PeriodicOrthocrossing.translatePolyline shift
      (scalePolyline composedGadgetScale sourceRoute)
  replacePolylineHead
    (PeriodicOrthocrossing.translatePolyline origin
      (sourceConnectorRoute sourceLiteralIndex
        (AxisDirection.polylineFirstDirection sourceRoute)))
    transformed

private theorem scalePolyline_primrec : Primrec₂ scalePolyline := by
  change Primrec fun input : Int × List Cell =>
    scalePolyline input.1 input.2
  exact (Primrec.list_map Primrec.snd
    (Computability.cell_scale_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
        fun _ => rfl

/-- The proof-free connector-and-source-tail construction is primitive
recursive. -/
theorem fanInheritedRouteSuffixAtIndex_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input :
        (((Nat × Nat) × PositionedPeriodicClause Variable) ×
          PositionedPeriodicClause
            (OneInThreeNoUnitVariable (OneInThreeVariable Variable))) ×
          (Nat × List Cell) =>
      fanInheritedRouteSuffixAtIndex
        input.1.1.1.1 input.1.1.1.2 input.1.1.2 input.1.2
        input.2.1 input.2.2 := by
  let Query :=
    (((Nat × Nat) × PositionedPeriodicClause Variable) ×
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))) ×
      (Nat × List Cell)
  let outputAnchorFn : Query → Cell := fun input =>
    PeriodicCNF.clauseAnchor input.1.2.literals
  have outputAnchor : Primrec outputAnchorFn :=
    PeriodicCNF.clauseAnchor_primrec.comp
      (PositionedPeriodicClause.literals_primrec.comp
        (Primrec.snd.comp Primrec.fst))
  let outputTranslationFn : Query → Cell := fun input =>
    Cell.scale input.1.1.1.1
      (PeriodicCNF.clauseAnchor input.1.2.literals)
  have outputTranslation : Primrec outputTranslationFn :=
    Computability.cell_scale_primrec.comp
      (Computability.int_ofNat_primrec.comp
        (Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst))))
      outputAnchor
  let scaledSourcePositionFn : Query → Cell := fun input =>
    Cell.scale composedGadgetScale input.1.1.2.position
  have scaledSourcePosition : Primrec scaledSourcePositionFn :=
    Computability.cell_scale_primrec.comp
      (Primrec.const composedGadgetScale)
      (PositionedPeriodicClause.position_primrec.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  let originFn : Query → Cell := fun input =>
    Cell.sub (Cell.scale composedGadgetScale input.1.1.2.position)
      (Cell.scale input.1.1.1.1
        (PeriodicCNF.clauseAnchor input.1.2.literals))
  have origin : Primrec originFn :=
    Computability.cell_sub_primrec.comp
      scaledSourcePosition outputTranslation
  let sourceAnchorFn : Query → Cell := fun input =>
    PeriodicCNF.clauseAnchor input.1.1.2.literals
  have sourceAnchor : Primrec sourceAnchorFn :=
    PeriodicCNF.clauseAnchor_primrec.comp
      (PositionedPeriodicClause.literals_primrec.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  let sourceTranslationFn : Query → Cell := fun input =>
    Cell.scale input.1.1.1.2
      (PeriodicCNF.clauseAnchor input.1.1.2.literals)
  have sourceTranslation : Primrec sourceTranslationFn :=
    Computability.cell_scale_primrec.comp
      (Computability.int_ofNat_primrec.comp
        (Primrec.snd.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst))))
      sourceAnchor
  let sourceCanonicalFn : Query → Cell := fun input =>
    Cell.sub input.1.1.2.position
      (Cell.scale input.1.1.1.2
        (PeriodicCNF.clauseAnchor input.1.1.2.literals))
  have sourceCanonical : Primrec sourceCanonicalFn :=
    Computability.cell_sub_primrec.comp
      (PositionedPeriodicClause.position_primrec.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      sourceTranslation
  let shiftFn : Query → Cell := fun input =>
    Cell.sub (originFn input)
      (Cell.scale composedGadgetScale (sourceCanonicalFn input))
  have shift : Primrec shiftFn :=
    Computability.cell_sub_primrec.comp origin
      (Computability.cell_scale_primrec.comp
        (Primrec.const composedGadgetScale) sourceCanonical)
  let scaledRouteFn : Query → List Cell := fun input =>
    scalePolyline composedGadgetScale input.2.2
  have scaledRoute : Primrec scaledRouteFn :=
    scalePolyline_primrec.comp
      (Primrec.const composedGadgetScale)
      (Primrec.snd.comp Primrec.snd)
  let transformedFn : Query → List Cell := fun input =>
    PeriodicOrthocrossing.translatePolyline
      (shiftFn input) (scaledRouteFn input)
  have transformed : Primrec transformedFn :=
    PeriodicOrthocrossing.translatePolyline_primrec.comp shift scaledRoute
  let directionFn : Query → AxisDirection := fun input =>
    AxisDirection.polylineFirstDirection input.2.2
  have direction : Primrec directionFn :=
    PeriodicThreeDM.NormalizationCompiler.polylineFirstDirection_primrec.comp
      (Primrec.snd.comp Primrec.snd)
  let connectorFn : Query → List Cell := fun input =>
    sourceConnectorRoute input.2.1 (directionFn input)
  have connector : Primrec connectorFn :=
    sourceConnectorRoute_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd) direction)
  let translatedConnectorFn : Query → List Cell := fun input =>
    PeriodicOrthocrossing.translatePolyline
      (originFn input) (connectorFn input)
  have translatedConnector : Primrec translatedConnectorFn :=
    PeriodicOrthocrossing.translatePolyline_primrec.comp origin connector
  exact (joinAtEndpoint_primrec translatedConnectorFn
    (fun input => (transformedFn input).tail)
    translatedConnector
    (Primrec.list_tail.comp transformed)).of_eq fun _ => rfl

/-- On a genuine width-three source index, the proof-free construction is
exactly the certified ordered fan suffix. -/
theorem fanInheritedRouteSuffixAtIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable)))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable)))
    (sourceClauseIndex sourceLiteralIndex : Nat)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceLiteralIndexLt : sourceLiteralIndex < 3) :
    fanInheritedRouteSuffixAtIndex
        outputPlacement.period sourcePlacement.period
        sourceClause generatedClause sourceLiteralIndex
        (sourceRoutes sourceClauseIndex sourceLiteralIndex) =
      fanInheritedRouteSuffix outputPlacement sourcePlacement
        sourceClause generatedClause
        (PositionedPeriodicCNF.clauseExitFanData
          sourceClause sourceClauseIndex sourceRoutes)
        (boundedSourceSlot sourceLiteralIndex)
        (sourceRoutes sourceClauseIndex sourceLiteralIndex) := by
  unfold fanInheritedRouteSuffixAtIndex fanInheritedRouteSuffix
  rw [sourceConnectorRoute_eq sourceClause sourceClauseIndex
    sourceLiteralIndex sourceRoutes sourceLiteralIndexLt]
  unfold normalizedSourceClausePosition inheritedSourceRoute
    inheritedSourceRouteShift
    PositionedPeriodicCNF.canonicalClausePosition
    PeriodicVariablePlacement.translation
  rfl

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
