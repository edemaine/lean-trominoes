import LeanTrominoes.PeriodicThreeDMNormalizationGeometryComputability

/-!
# Primitive-recursive reversed normalization templates
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

def reversedNormalizationTemplateAt
    (input : Cell × List Cell) : List Cell :=
  (normalizationTemplateAt input.1 input.2).reverse

theorem reversedNormalizationTemplateAt_primrec :
    Primrec reversedNormalizationTemplateAt :=
  (Primrec.list_reverse.comp normalizationTemplateAt_primrec).of_eq
    fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
