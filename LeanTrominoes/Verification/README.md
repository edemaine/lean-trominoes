# Verification entry points

AxiomAudit retains the repository's axiom regression checks. All and the generated Isolated batches jointly cover every local module, including modules outside the curated Results entry points. Separate batches preserve legacy helpers that declare incompatible statements under the same name.

The reorganization placed one existing module here.

Useful entry points:

- [Axiom regression checks](AxiomAudit.lean)
- [Primary verification batch](All.lean)

For an optional full fresh kernel replay after building, run `python scripts/check_module_layout.py --kernel`. This also rechecks imported foundations and can take hours and substantial memory.

See the [repository overview](../../README.md#repository-organization) for the
paper map and the [maintenance guide](../../docs/organization.md) for import
migration and validation commands.
