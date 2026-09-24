# Guidance for AI coding agents

Conventions for working in a project generated from this template (a Lean 4 formalization of
a paper with a LeanArchitect blueprint). They apply to humans too. The user-facing
documentation is `README.md` (development, Japanese) and `README.public.md` (public, English).

## Workflow and documents

- `PLAN.md`: the formalization plan (paper structure, module layout, milestones, design
  decisions). `PROGRESS.md`: a dated log of what was done, what was found and what is next.
  `SUMMARY.md`: the current state of the formalization (statements, deviations from the paper,
  sizes). `ToDraft.md`: corrections and generalizations found during the formalization that
  have to be written back into the manuscript. Keep them up to date; the parent agent updates
  them and reviews, subagents formalize.
- Work per module with subagents: one agent per file set, never two agents on the same file
  (avoids conflicting edits). Give each agent the LaTeX of the target statements, the Mathlib
  names to use, the naming conventions and the requirement that the build passes.
- Iterate with `lake env lean <file>` on the file being edited, and finish with
  `lake build <module>` (then `lake build` for the whole library before committing).
- `00note/` (notes, prompts) and `00data/` (reference texts) are private: they are ignored
  by `.publishignore` and must never be published or committed to the public repository.

## Blueprint annotations

- Every definition and theorem gets `@[blueprint "label" (statement := /-- LaTeX -/)]`.
  Labels are the paper's `\label`s (`thm:bv`, `def:covering`, ...); the chapter structure of
  `blueprint/src/content.tex` follows the paper. Dependencies (`\uses`) are inferred; add
  `uses :=` / `proofUses :=` only when needed.
- Proof steps are docstrings inside the tactic proof (`/-- Step ... -/`); they become the
  proof sketch shown in the blueprint.
- Inside the blueprint LaTeX, escape underscores in backticked code spans (`` `foo\_bar` ``):
  the PDF build fails on a bare `_`. Never write `-/` inside a docstring (it closes it).
- Macros of the paper used in statements are defined in `blueprint/src/macros/common.tex`
  (`\providecommand`), for both the web and the PDF version.
- `relaxedAutoImplicit = false` is set in `lakefile.toml`: declare every variable.

## Correctness

- Never introduce axioms. The target for every main theorem is
  `#print axioms` = `propext, Classical.choice, Quot.sound`, and no `sorry` at the end.
- Lean gotchas met in practice (add hypotheses rather than trusting the literal statement):
  - the Bochner integral of a non-integrable function is `0`: add integrability hypotheses to
    statements with integrals on the right-hand side (e.g. Dudley integrals);
  - `iSup` / `sSup` of an unbounded (or empty) real family is `0`: add `BddAbove` (and
    `Nonempty`) hypotheses to statements with suprema;
  - distances on non-compact spaces are best taken `ℝ≥0∞`-valued (`edist`, `⨆ x, edist ..`);
  - Mathlib's internal covering numbers are not monotone in the set; use external covering
    numbers or `coveringNumber_subset_le`-style lemmas when monotonicity is needed.
- Statements are copied from the paper as faithfully as possible; when a statement is false
  as written, fix the Lean statement and record the change in `ToDraft.md`.

## Module layout

- Separate definition modules (`Defs`, `Setting/*`, ...) from theorem modules, so that the
  paper's statements can be written by importing definitions only. This is what makes a
  Comparator challenge possible (see below).
- General-purpose lemmas that belong upstream go to `ToMathlib/` (Mathlib material) and
  `ToFoML/`-style directories (material for a dependency library), independent of the
  project's other modules, so that they can be upstreamed later.
- The root module `<LibName>.lean` imports every module; `blueprint/src/content.tex` inputs
  every module with `\inputleanmodule{...}`.

## Comparator

Introduce [Comparator](https://github.com/leanprover/comparator) at the end of the
development: `comparator/Challenge.lean` states the paper's theorems with `sorry`, importing
only definition modules; `comparator/Solution.lean` proves them by the library theorems;
`comparator/config.json` lists the theorem names and the permitted axioms. Run
`./script/comparator.sh` (tools in `../comparator-tools/`, see `README.md`) and record the
result on `home_page/comparator.html` (the certificate page linked from the home page) and in
`comparator/README.md`. When a library statement changes, change the challenge, never the
library to fit the challenge.

## Commits and publishing

- Commit small and often, with English messages, each ending with
  `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`.
- Publishing: `./script/generate.sh` (with the PDF) builds `site/`;
  `./script/publish-code.sh` pushes a snapshot of `HEAD` to the public repository, with
  `README.public.md` as its `README.md`; `./script/publish-page.sh` pushes `site/` to the
  `gh-pages` branch. Keep `README.public.md`, `LICENSE`, `comparator/` and
  `home_page/comparator.html` up to date before publishing.
