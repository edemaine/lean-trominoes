import LeanTrominoes.PeriodicGridDrawingContinuousPlanarity
import LeanTrominoes.PeriodicPlanarThreeDM

/-!
# Continuously planar presentations of periodic three-dimensional matching

The basic planar-presentation interface rules out integer-grid crossings
and vertex/route contacts.  Geometric gadget substitution additionally
needs distinct lifted route segments to have disjoint relative interiors,
including when two unit segments coincide.  This file packages that
stronger certificate for periodic 3DM instances.
-/

namespace LeanTrominoes

namespace PeriodicThreeDM

/-- A planar presentation whose distinct lifted route segments also have
disjoint continuous relative interiors. -/
structure ContinuousPlanarPresentation (problem : PeriodicThreeDM)
    extends problem.PlanarPresentation where
  continuouslyPlanar : drawing.IsContinuouslyPlanar

/-- A periodic 3DM instance admits a continuously planar grid
presentation. -/
def HasContinuousPlanarPresentation (problem : PeriodicThreeDM) : Prop :=
  Nonempty problem.ContinuousPlanarPresentation

end PeriodicThreeDM

end LeanTrominoes
