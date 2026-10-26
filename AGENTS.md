# Working in propositional-provability-logics

The contract for AI agents in this repository.

The project formalizes and verifies, in Lean 4, the research around [Nog26], and develops new
results on top of it. The Lean formalization has not started yet; do not set it up until asked.

## Setup

Skills (`imozuru`, `japanese-tech-writing`, `lean4`) are pinned in `skills-lock.json`. Restore
them with `npx skills experimental_install`, which writes `.agents/skills/`; Claude Code reads
them through the symlinks `.claude/skills/<name> -> ../../.agents/skills/<name>`. Both
directories are git-ignored.

## Local files

Everything personal, or anything that must not be version-controlled, goes under `.local/` at
the project root (git-ignored). Never commit it, and never put such files anywhere else.

| What | Where |
|---|---|
| Reference texts (PDFs of papers, books, …) | `.local/references/` |
| Personal mathematical notes | `.local/proofs/` |

The reference texts are copyrighted: cite them, never commit or quote them at length.

## Mathematical notes

Notes in `.local/proofs/` are Typst documents in Japanese, following the
`japanese-tech-writing` skill. Write them as mathematical documents: read
`.local/proofs/README.md` before writing a note, and start from `.local/proofs/template.typ`.
The template reads the bibliography from `references.yml` at the project root; compile from
`.local/proofs/` with `typst compile --root ../.. <note>.typ`.
