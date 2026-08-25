/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorNatWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorStreamSemantics

/-! # Stream semantics of natural carrier-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

theorem wordCorrect_route : WordCorrect .route :=
  scan_semanticWord_route

theorem wordCorrect_segment : WordCorrect .segment :=
  scan_semanticWord_segment

theorem output_encode_semanticWords_route
    (keys : List (Option CarrierKeyWords.CarrierKey)) :
    output .route (DelimitedBinaryWords.encode ⟨keys.map semanticWord⟩) =
      UnaryFieldEncoderMachine.unaryFields
        (keys.map (value .route) ++ [0]) :=
  output_encode_semanticWords .route wordCorrect_route keys

theorem output_encode_semanticWords_segment
    (keys : List (Option CarrierKeyWords.CarrierKey)) :
    output .segment
        (DelimitedBinaryWords.encode ⟨keys.map semanticWord⟩) =
      UnaryFieldEncoderMachine.unaryFields
        (keys.map (value .segment) ++ [0]) :=
  output_encode_semanticWords .segment wordCorrect_segment keys

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
