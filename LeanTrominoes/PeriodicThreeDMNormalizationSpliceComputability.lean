import LeanTrominoes.PeriodicThreeDMNormalizationSuffixComputability

/-!
# Primitive-recursive normalized-route splicing
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization
open PeriodicOrthocrossing
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

abbrev NormalizeRouteInput :=
  ((Cell × Cell) × (List Cell × List Cell)) × List Cell

theorem normalizeRouteWithTemplates_primrec :
    Primrec fun input : NormalizeRouteInput =>
      normalizeRouteWithTemplates input.1.1.1 input.1.1.2
        input.1.2.1 input.1.2.2 input.2 := by
  have sourceTemplate : Primrec (fun input : NormalizeRouteInput =>
      normalizationTemplateAt input.1.1.1 input.1.2.1) :=
    normalizationTemplateAt_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  have suffix : Primrec (fun input : NormalizeRouteInput =>
      joinAtEndpoint (trimmedMagnifiedRoute input.2)
        (normalizationTemplateAt input.1.1.2 input.1.2.2).reverse) :=
    (normalizationTargetSuffix_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        Primrec.snd)).of_eq fun _ => rfl
  exact (joinAtEndpoint_primrec.comp sourceTemplate suffix).of_eq
    fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
