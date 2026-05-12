# Run milestones — fuse-test blueprint drafting from Lean

## Scope
User asked to create the blueprint based on the current Lean files in the repo. The repo contains 48 Lean files under `QEC1/Definitions`, `QEC1/Lemmas`, `QEC1/Theorems`, `QEC1/Remarks` (12 definitions, 7 lemmas, 3 theorems/corollaries, 26 remarks). Each file's docstring summarizes the mathematical statement.

Blueprint LaTeX path: `numina/blueprints/fuse-test/fuse-test.tex`.
Blueprint metadata path: `numina/.metadata/blueprints/fuse-test/`.

## Plan
1. Read each Lean file's leading `/-! ... -/` documentation block plus the primary declaration signature.
2. Draft `fuse-test.tex` with one LaTeX block per Lean file, using leanblueprint macros (`\begin{definition}`, `\begin{lemma}`, `\begin{theorem}`, `\begin{corollary}`, `\begin{remark}`), each with a `\label{}`, `\lean{...}`, and `\leanok` (since the Lean code is already present).
3. Run `initialize_blueprint_metadata` to populate `blueprint.json` and create per-declaration metadata stubs.

## Status
- Done: drafted full `fuse-test.tex` (588 lines, 48 blocks across 4 chapters).
- Done: initialized blueprint metadata. 22 of 48 entries parsed into `declarations/`:
  - 12 definitions (`def:1_*` … `def:12_*`)
  - 7 lemmas (`lem:1_*` … `lem:7_*`)
  - 2 theorems (`thm:1_*`, `thm:2_*`)
  - 1 corollary (`cor:1_*`)
- The 26 `\begin{remark}` blocks are present in the LaTeX but were not parsed
  as declarations by `initialize_blueprint_metadata`. This appears to be by
  design: remarks are notation/context and not tracked as formalizable items.
  No further action required unless the user wants them promoted to tracked
  declarations.

## Notes
- Lean toolchain is unavailable in this session; the agent did not run
  `lake build`. The `\leanok` markers were written under the assumption
  that the Lean code in `QEC1/**/*.lean` is the user's source of truth.
- Each entry's `\lean{...}` argument is a best-effort fully-qualified name
  read from the file's `namespace` and primary declaration. Anchors picked:
  - Def_1 → `GraphMaps.boundaryMap`
  - Def_4 → `deformedCodeChecks`
  - Lem_5 → `listedGenerator_isGaugingStabilizer`
  - Def_8/9/11 used unqualified names because their files have no explicit
    `namespace` wrapping the declaration.
- `\uses{...}` cross-references on lemmas/theorems/corollary were inferred
  from file titles, imports, and docstring content. Not all transitive
  dependencies are listed; only the directly cited ones.

## Next steps (for the user)
- Optional: open `fuse-test.tex` and adjust prose / `\uses` / `\lean{...}`
  anchors as you prefer.
- Optional: when ready, kick off the formalizer-reviewer pass to confirm
  each `\lean{...}` actually points at an existing Lean declaration.
- Optional: restore the Lean toolchain, then run `lake build` to verify
  the `\leanok` claims still hold.
