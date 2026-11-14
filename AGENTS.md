# PNT+ migration contributions

Every PR to `TauCetiProject/TauCeti` arising from this PNT+ migration must have the
`pnt+` label. Include `--label 'pnt+'` in `gh pr create`, including for replacement
PRs, and preserve the label when updating existing PRs.

The migration excludes IEANTN and all files under `Unused/`. Files under `Unused/`
remain in the fork and its build; they are outside the Tau Ceti migration and its
roadmap requirements.

Keep `ROADMAPS.md` as the concise Zulip draft agreed with the user. Record
implementation details and progress in `MIGRATION_STATUS.md`.
