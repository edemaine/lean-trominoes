/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedMetadataComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionPositionComputability

/-! # Basic raw-route computability for routed polarity normalization -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalization
open PeriodicOneInThreePolarityNormalizationPositioned

theorem translatePolyline_primrec :
    Primrec₂ PeriodicOrthocrossing.translatePolyline := by
  change Primrec fun input : Cell × List Cell =>
    PeriodicOrthocrossing.translatePolyline input.1 input.2
  exact (Primrec.list_map Primrec.snd
    (Computability.cell_add_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
        fun _ => rfl

/-- The clause-anchor correction for a complement route is primitive
recursive in the source placement period and literal offset. -/
theorem complementCanonicalShift_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (periodPrimrec : Primrec period) :
    Primrec fun input : Input × PeriodicLiteral Variable =>
      complementCanonicalShift
        ({ period := period input.1
           position := fun _ : Variable => (0, 0) } :
          PeriodicVariablePlacement Variable) input.2 := by
  have translated : Primrec fun input :
      Input × PeriodicLiteral Variable =>
      (refinedPlacement
        ({ period := period input.1
           position := fun _ : Unit => (0, 0) } :
          PeriodicVariablePlacement Unit)).translation input.2.offset :=
    (refinedPlacement_translation_primrec period periodPrimrec).comp
      (Primrec.pair Primrec.fst
        (PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd))
  exact (Computability.cell_sub_primrec.comp
    (Primrec.const ((0, 0) : Cell)) translated).of_eq fun _ => rfl

/-- The retained-or-shortened main-clause route branch. -/
def normalizedRawRoute {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata : ClauseMetadata Variable)
    (literalIndex : Nat) : List Cell :=
  match metadata.sourceClause.literals[literalIndex]? with
  | none => []
  | some literal =>
      if literal.value = normalizedPolarity literalIndex then
        refinedRoute routes metadata.sourceClauseIndex literalIndex
      else
        (refinedRoute routes metadata.sourceClauseIndex literalIndex).take 2

/-- Main-clause raw-route selection is primitive recursive. -/
theorem normalizedRawRoute_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (routes : Input → Nat → Nat → List Cell)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × ClauseMetadata Variable) × Nat =>
      normalizedRawRoute (routes input.1.1) input.1.2 input.2 := by
  let RouteInput := (Input × ClauseMetadata Variable) × Nat
  have clauseIndex : Primrec fun input : RouteInput =>
      input.1.2.sourceClauseIndex :=
    ClauseMetadata.sourceClauseIndex_primrec.comp
      (Primrec.snd.comp Primrec.fst)
  have sourceLiterals : Primrec fun input : RouteInput =>
      input.1.2.sourceClause.literals :=
    PositionedPeriodicClause.literals_primrec.comp
      (ClauseMetadata.sourceClause_primrec.comp
        (Primrec.snd.comp Primrec.fst))
  have fullRoute : Primrec fun input : RouteInput =>
      refinedRoute (routes input.1.1)
        input.1.2.sourceClauseIndex input.2 :=
    (refinedRoute_primrec routes routesPrimrec).comp
      (Primrec.pair
        (Primrec.pair (Primrec.fst.comp Primrec.fst) clauseIndex)
        Primrec.snd)
  have shortRoute : Primrec fun input : RouteInput =>
      (refinedRoute (routes input.1.1)
        input.1.2.sourceClauseIndex input.2).take 2 :=
    Primrec.list_take.comp (Primrec.const 2) fullRoute
  have literalOption : Primrec fun input : RouteInput =>
      input.1.2.sourceClause.literals[input.2]? :=
    Primrec.list_getElem?.comp sourceLiterals Primrec.snd
  have some : Primrec₂ fun (input : RouteInput)
      (literal : PeriodicLiteral Variable) =>
      if literal.value = normalizedPolarity input.2 then
        refinedRoute (routes input.1.1)
          input.1.2.sourceClauseIndex input.2
      else
        (refinedRoute (routes input.1.1)
          input.1.2.sourceClauseIndex input.2).take 2 := by
    change Primrec fun combined : RouteInput × PeriodicLiteral Variable =>
      if combined.2.value = normalizedPolarity combined.1.2 then
        refinedRoute (routes combined.1.1.1)
          combined.1.1.2.sourceClauseIndex combined.1.2
      else
        (refinedRoute (routes combined.1.1.1)
          combined.1.1.2.sourceClauseIndex combined.1.2).take 2
    have compatible : PrimrecPred fun combined :
        RouteInput × PeriodicLiteral Variable =>
        combined.2.value = normalizedPolarity combined.1.2 :=
      Primrec.eq.comp
        (PeriodicThreeCNF.literal_value_primrec.comp Primrec.snd)
        (normalizedPolarity_primrec.comp
          (Primrec.snd.comp Primrec.fst))
    exact Primrec.ite compatible
      (fullRoute.comp Primrec.fst) (shortRoute.comp Primrec.fst)
  exact (Primrec.option_casesOn literalOption (Primrec.const [])
    some).of_eq fun input => by
      unfold normalizedRawRoute
      cases input.1.2.sourceClause.literals[input.2]? <;> rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
