import LeanTrominoes.Theorem52Proof
import LeanTrominoes.PeriodicCNFPolySpaceHardness
import LeanTrominoes.Theorem55Construction

/-!
# Main theorem interface

`Theorem52.proved` proves the complete plane and strip result, and
`Theorem52.stripProved` exposes strip PSPACE completeness. Import
`LeanTrominoes.Theorem52` separately to read only the target statements.
See README.md for the main declarations and PROOF_FRONTIER.md for the
completed construction and validation.

`Theorem55Construction` also exposes the proved geometric components and
forward construction for Theorem 5.5. Its full plane statement remains open;
see THEOREM55_FRONTIER.md.

This module is the public result interface. Lake's `LeanTrominoes.*` glob
checks every construction module independently of this import list.
-/
