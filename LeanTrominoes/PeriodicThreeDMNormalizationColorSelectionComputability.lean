import LeanTrominoes.PeriodicThreeDMNormalizationEndpointTripleDataComputability

/-!
# Primitive-recursive normalized endpoint color selection

Once the three endpoint side/color records have been computed, selecting the
record on a requested side is a finite operation.
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def colorFromTripleData
    (input : VertexSide × EndpointTripleData) : WireColor :=
  if input.1 = input.2.1.1 then input.2.1.2
  else if input.1 = input.2.2.1.1 then input.2.2.1.2
  else input.2.2.2.2

theorem colorFromTripleData_primrec :
    Primrec colorFromTripleData :=
  Primrec.dom_finite _

/-- Select the color of the endpoint occupying the requested old side. -/
def endpointColorFromTriple (input : AtSide × EndpointTriple) : WireColor :=
  colorFromTripleData
    (input.1.2, endpointTripleData (input.1.1.1, input.2))

theorem endpointColorFromTriple_primrec :
    Primrec endpointColorFromTriple := by
  have tripleData : Primrec (fun input : AtSide × EndpointTriple =>
      endpointTripleData (input.1.1.1, input.2)) :=
    endpointTripleData_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)
  exact (colorFromTripleData_primrec.comp
    (Primrec.pair (Primrec.snd.comp Primrec.fst) tripleData)).of_eq
      fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
