import LeanTrominoes.Theorem52
import LeanTrominoes.PeriodicWangPlanarThreeDMReduction
import LeanTrominoes.PartrecFlatStripDeciderSpace
import LeanTrominoes.PeriodicCNFPolySpaceHardness

/-!
# Main theorem interface

`Theorem52` states the plane, strip, and combined targets. The imports expose
the complete plane theorem, strip PSPACE membership, and the local periodic
CNF SAT hardness theorem used by the unfinished strip reduction. See README.md
for their declaration names and PROOF_FRONTIER.md for remaining obligations.

This module is the public result interface. Lake's `LeanTrominoes.*` glob
checks every construction module independently of this import list.
-/
