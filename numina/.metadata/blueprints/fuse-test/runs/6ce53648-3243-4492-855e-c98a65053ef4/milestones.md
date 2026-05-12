# Run milestones — fuse-test review pass

## Scope
User asked: "review the drafted fuse-test.tex and adjust any \lean anchors or \uses references you want changed".

Two passes to perform:
1. For each `\lean{...}` anchor in `numina/blueprints/fuse-test/fuse-test.tex`, confirm the named declaration actually exists in the matching Lean source file under `QEC1/Definitions|Lemmas|Theorems|Remarks/`. If not, replace with a real declaration name or remove the anchor.
2. For each `\uses{...}` list, confirm every label exists in the same `.tex` document. Drop dangling labels and add obviously missing dependencies.

Scope is strictly limited to editing `fuse-test.tex` and updating run logs. Do NOT touch Lean source or metadata stubs.

## Status — completed

### Anchor fixes (3)
- `rem:12_worst_case_graph_construction`:
  `WorstCaseGraphConstruction.total_qubit_bound` →
  `WorstCaseGraphConstruction.worst_case_construction_log_squared`
  (no `total_qubit_bound` exists in the file; the new name is the main
  summary theorem combining the O(W log^2 W) overhead desiderata).
- `rem:18_relation_to_lattice_surgery`:
  `ladderGraph_connected` →
  `RelationToLatticeSurgery.ladderGraph_connected`
  (the theorem lives inside `namespace RelationToLatticeSurgery`).
- `lem:4_spacetime_code_detectors`:
  `phase1RepeatedDetector_parametric` →
  `FaultTolerantGaugingProcedure.phase1RepeatedDetector_parametric`
  (the def lives inside `namespace FaultTolerantGaugingProcedure`).

All other 45 `\lean{...}` anchors verified correct.

### \uses pruning
No changes; every label referenced in `\uses{...}` exists as a `\label{...}`
in the same .tex.

### Metadata
Refreshed via `refresh_blueprint_metadata`. 22 tracked declarations remain
(unchanged structurally: 12 def, 7 lem, 2 thm, 1 cor). The 26 remarks are
still skipped by the parser by design.

### Remaining issues for the user
None blocking. Optional manual follow-ups:
- Some lemmas/theorems pick a single anchor when the file proves multiple
  closely-related results. If you prefer multi-name `\lean{a, b}` anchors
  for any specific block, tell me and I will adjust.
- `\leanok` is still asserted on every block. When the Lean toolchain is
  restored, run `lake build QEC1` to make those claims observable in CI.
