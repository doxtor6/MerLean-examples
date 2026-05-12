# Run milestones — fuse-test review pass

## Scope
User asked: "review the drafted fuse-test.tex and adjust any \lean anchors or \uses references you want changed".

Two passes to perform:
1. For each `\lean{...}` anchor in `numina/blueprints/fuse-test/fuse-test.tex`, confirm the named declaration actually exists in the matching Lean source file under `QEC1/Definitions|Lemmas|Theorems|Remarks/`. If not, replace with a real declaration name or remove the anchor.
2. For each `\uses{...}` list, confirm every label exists in the same `.tex` document. Drop dangling labels and add obviously missing dependencies.

Scope is strictly limited to editing `fuse-test.tex` and updating run logs. Do NOT touch Lean source or metadata stubs.

## Status
- Pending: review pass.
