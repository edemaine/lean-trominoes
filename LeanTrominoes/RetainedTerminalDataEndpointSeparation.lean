import LeanTrominoes.RetainedTerminalDirectionEndpointSeparation
import LeanTrominoes.RetainedAngularTerminalDataProfile

/-!
# Retained terminal-data separation at a shared endpoint

This record-valued interface avoids repeatedly normalizing the direction and
length projections of classified terminal data when composing large final
route certificates.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Two continuously separated orthogonal routes entering one endpoint have
different directions when their classifications are packaged as terminal-data
records. -/
theorem retainedTerminalDataDirections_ne_of_routesAvoidEachOther
    {first second : List Cell}
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second)
    (sameFinish : first.getLast? = second.getLast?)
    (avoid : RoutesAvoidEachOther first second)
    (firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector first) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector second) =
        some secondTerminal) :
    firstTerminal.1 ≠ secondTerminal.1 := by
  exact
    @retainedTerminalDirections_ne_of_routesAvoidEachOther
      first second
      firstTerminal.1 secondTerminal.1
      firstTerminal.2 secondTerminal.2
      firstLength secondLength
      firstOrthogonal secondOrthogonal
      sameFinish avoid
      firstClassified secondClassified

end PeriodicEightOccurrenceSplit
end LeanTrominoes
