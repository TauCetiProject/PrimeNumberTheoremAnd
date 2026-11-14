# PNT+ migration contributions

Every PR to `TauCetiProject/TauCeti` arising from this PNT+ migration must have the
`pnt+` label. Include `--label 'pnt+'` in `gh pr create`, including for replacement
PRs, and preserve the label when updating existing PRs.

The migration excludes IEANTN and all files under `Unused/`. Files under `Unused/`
remain in the fork and its build; they are outside the Tau Ceti migration and its
roadmap requirements.

Keep `ROADMAPS.md` as the concise Zulip draft agreed with the user. Record
implementation details and progress in `MIGRATION_STATUS.md`.

Monitor only one priority GitHub Actions run at a time. Use the prescribed
`gh run watch` interval; queued PRs do not need parallel local watch processes.

Share the canonical Mathlib build when both the exact Mathlib commit and Lean
toolchain match. Keep each worktree's project build separate. Remove finished
worktrees and regenerable temporary build outputs after preserving source
commits, patches and validation logs, and checking active processes and references.
