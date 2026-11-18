# Concurrent experiment style guide

This guide belongs only on `verify/*` branches, including `verify/overview`.
Do not commit or cherry-pick it onto `main` or unrelated branches.

## Names and locations

- Give each experiment a stable, lowercase, hyphenated slug describing the
  approach, such as `qmdb-hax-aeneas-lean` or `qmdb-verus`. Avoid relative names
  such as `new`, `latest`, and `modern`.
- Name verification branches `verify/<slug>` and linked worktrees
  `<canonical-repo>/.worktrees/<slug>`. Other branches use their final path
  component as the directory name: `website-toc` lives in `.worktrees/website-toc`.
  Keep slugs unique across branch namespaces.
- The canonical checkout is the deliberate exception: its directory stays
  `monorepo` and hosts `verify/overview`. Experiment branches use linked worktrees.
  Keep worktrees and toolchains
  in persistent locations, not temporary directories. Ignore `.worktrees/` locally.
- Use `git worktree list` to discover current locations. Use `git branch -m` and
  `git worktree move` for renames; never move a checkout with a filesystem rename
  alone. Preserve unrelated changes and never force-reset another experiment.

## One report, traceable evidence

- `verify/overview` is the single authoritative report branch. Commit changes to
  `qmdb-inclusion-proofs.html` and `verification/qmdb/code-diff.py` only there,
  in the canonical checkout. Keep experiment implementation changes on their
  own branches. Older report copies in experiment history are snapshots, not
  competing reports; do not propagate overview commits to experiment branches.
  Coordinate edits to this shared file; reread it before writing and update only
  your experiment's entries and affected comparisons.
- Use the same approach label, branch, and worktree path in the report, the
  experiment README, and the `EXPERIMENTS` mapping in
  `verification/qmdb/code-diff.py`. A short diff-URL key may remain stable across
  a rename, but it must resolve to the correct worktree and comparison baseline.
- Link implementation, proof, assumptions, toolchain pins, validation evidence,
  and reproduction commands. Use the report's existing Open/Diff conventions.
  Worktree links show current files; source revisions identify the current code checked.
  Do not present live or uncommitted files as an immutable snapshot.
- Keep guarantees, assumptions, exclusions, and executed tests distinct. State
  the exact proved subset and remaining production boundary. Tests and mutation
  rejection do not establish a broader formal theorem or global coverage.
- Attribute results to the branch and source revision actually checked. Shared
  runtime results apply to other branches only after confirming identical relevant
  sources. Do not relabel old results as new runs.
- Describe only the current codebase in the HTML. Remove obsolete architectures,
  superseded proof counts, retired implementations and historical source snapshots;
  Git history holds that record. Keep current source revisions and toolchain pins
  for reproducibility. Baselines may identify Diff comparisons, not stand in for
  current behavior. A historical database root is a supported use case, not an
  obsolete code revision.
- Recheck source links, counts and proof scope when code changes. If validation no
  longer applies to the current source, say "not validated for current source"
  instead of presenting an old result as current. Retain detailed old logs outside
  the HTML. Default the inventory to tests matching the formal target and expose
  broader coverage with an explicit toggle; identify mixed-test matching subsets.

## Lean modules and generated artifacts

- Use Lean's module system for every Lean experiment. Start handwritten Lean
  files with `module`, declare dependencies with explicit imports, and expose
  only the definitions and theorems that downstream modules need.
- Keep generated artifacts in dedicated paths. Put handwritten proofs, models,
  and assumptions in separate modules that import the generated definitions.
- In the experiment README, list generated paths by purpose, identify their
  source inputs and pinned generator, and give the commands to regenerate and
  check them. For outputs that reviewers can skip, explain which checks justify
  skipping manual review. Link directly to anything that still needs judgment,
  including generated assumptions, external models, and handwritten overrides.

## Progress and handoff

Keep a short status block in each experiment's README (for QMDB,
`verification/qmdb/README.md`) and summarize it in the canonical HTML:

```text
Approach / branch / worktree:
Status: active | paused | blocked | complete | retired
Updated: YYYY-MM-DD
Source: code commit; if dirty, identify changed files and recorded source hashes
Proved scope and remaining assumptions:
Last validation: command, date, checked source revision, result and evidence link
Next step / blocker:
```

Update this at meaningful milestones and before handing off. A source change
invalidates earlier validation unless relevant sources are unchanged; mark current
validation pending until rechecked.
`complete` refers to the stated scope, never implicitly to the whole database.
Retired approaches leave the active comparison; keep their history and evidence.
Before switching tasks, commit a coherent checkpoint when authorized, or state
exactly what remains uncommitted. Do not mix another experiment's edits into it.

## Rename and shared-guide checklist

1. Inspect branch/worktree registrations and dirty files before changing anything.
2. Rename the branch and its linked directory together. Update the canonical HTML,
   README's current identity, diff resolver, and any live path references or
   symlinks. Keep historical commits and recorded run identities intact.
3. Check `git worktree list`, resolve Open links, and use the diff handler's
   `--check` mode to validate Diff links without launching an editor. Confirm the
   report's tables, navigation, and inventory filters remain intact.
4. Keep this guide byte-identical across local `verify/*` branches only, including
   `verify/overview`. Commit guide changes
   separately, propagate that guide-only commit with `git cherry-pick -x`, and
   verify the file contents on every verification branch. Include it when creating
   new verification branches; exclude it from `main` and non-verification branches.
   If a branch is not checked out, use a temporary clean worktree to update it.
   Resolve guide conflicts deliberately; never bundle unrelated dirty files.

Local commits do not publish branches. Push or remove branches/worktrees only
when that action is authorized.
