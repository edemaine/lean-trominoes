/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRankOrderedWordStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourcePairFieldFormatterStreamSemantics

/-! # Numeric semantics of ranked physical carrier source-pair words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRankOrderedWordStream

/-- On valid numeric routes, formatting the rank-ordered field column gives
exactly one guarded physical source-pair word per global carrier entry. -/
theorem emittedTokens_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    emittedTokens (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
      DelimitedBinaryWords.encode
        (CarrierSourcePairFieldFormatter.words
          ((CarrierRankGlobal.enumeration datums).map
            (CarrierNodeSourceKeys.datumPair ∘ Prod.fst))) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  let sourcePairs := (CarrierRankGlobal.enumeration datums).map
    (CarrierNodeSourceKeys.datumPair ∘ Prod.fst)
  have fieldsEq :
      CarrierSourceKeyRankOrderedFields.values descriptors =
        sourcePairs.flatMap fun sourcePair =>
          CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
            (some sourcePair) := by
    simpa [descriptors, period, datums, sourcePairs, List.flatMap_map,
      Function.comp_def] using
      CarrierSourceKeyRankOrderedFields.values_numericRouteDescriptors
        formula wellFormed degree isLocal forward nonempty
  have formattedEq := congrArg
    (fun fields => CarrierSourcePairFieldFormatter.output
      (UnaryFieldEncoderMachine.unaryFields fields)) fieldsEq
  change emittedTokens descriptors =
    DelimitedBinaryWords.encode
      (CarrierSourcePairFieldFormatter.words sourcePairs)
  calc
    emittedTokens descriptors =
        CarrierSourcePairFieldFormatter.output
          (UnaryFieldEncoderMachine.unaryFields
            (CarrierSourceKeyRankOrderedFields.values descriptors)) := rfl
    _ = CarrierSourcePairFieldFormatter.output
          (UnaryFieldEncoderMachine.unaryFields
            (sourcePairs.flatMap fun sourcePair =>
              CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
                (some sourcePair))) := formattedEq
    _ = DelimitedBinaryWords.encode
          (CarrierSourcePairFieldFormatter.words sourcePairs) :=
      CarrierSourcePairFieldFormatter.output_sourcePairs sourcePairs

end CarrierSourceKeyRankOrderedWordStream
end LeanTrominoes.PeriodicOrthocrossing
