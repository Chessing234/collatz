# Papers

One source per file.

Use exact citations.

Track what is read.

Track what is formalized.

Do not invent sources.

## 100-paper arXiv batch (2026-09-15)

One tracker markdown under `Papers/arxiv-*.md` and two Lean scaffolds per source:

- `Collatz/Papers/Arxiv*.lean` — Mathlib-free statement recording (root package)
- `MathlibAttack/MathlibAttack/Papers/Arxiv*.lean` — Mathlib-backed weak shells (`ℚ`, `omega`)

Index rows are under `<!-- AUTO:ARXIV100 -->` in `Papers/index.md`.
These scaffolds **record** paper claims; they do **not** prove the papers' main theorems.

## Batch B (2026-09-15)

Second tranche of 100 arXiv Collatz sources (`<!-- AUTO:ARXIV100B -->` in `index.md`).
Same scaffolding rules as batch A: recorded `mainStatement`, checked bridges only.

## Mathlib-copied support

`Collatz/Papers/MathlibCopied.lean` inlines Mathlib-style lemmas (ordered `Rat`,
Nat parity/division, Collatz step laws, power-of-two descent, verification below 8)
without depending on the Mathlib package. Paper scaffolds import it for their
checked bridges.

## Batch C (2026-09-15)

Third tranche of 100 arXiv Collatz sources (`<!-- AUTO:ARXIV100C -->` in `index.md`).
Same scaffolding rules as batches A/B: recorded `mainStatement`, checked bridges only.

## Batch D (2026-09-15)

Fourth tranche of unused arXiv Collatz sources (`<!-- AUTO:ARXIV100D -->` in `index.md`).
After batches A–C (~300 modules), only a smaller set of genuine unused Collatz arXiv IDs remained;
scaffolds follow the same recorded-`mainStatement` / weak-bridge rules.

## Batch E (2026-09-15)

Fifth tranche: primarily journal / DOI Collatz literature from OpenAlex and Crossref
(`<!-- AUTO:ARXIV100E -->` in `index.md`), after arXiv title searches were largely exhausted
by batches A–D. Same scaffolding rules: recorded `mainStatement`, checked bridges only.
Modules are named `Journal_*` (DOI-based) when no arXiv id is available.

## Batch F (2026-09-15)

Sixth tranche: additional journal / DOI Collatz literature (`<!-- AUTO:ARXIV100F -->` in `index.md`),
harvested after batch E. Same scaffolding rules: recorded `mainStatement`, checked bridges only.

## Batch G (2026-09-15)

Seventh tranche: further journal / DOI Collatz literature (`<!-- AUTO:ARXIV100G -->` in `index.md`).
Same scaffolding rules: recorded `mainStatement`, checked bridges only.

## Batch H (2026-09-15)

Eighth tranche: further journal / DOI Collatz literature (`<!-- AUTO:ARXIV100H -->` in `index.md`).
Same scaffolding rules: recorded `mainStatement`, checked bridges only.

## Batch I (2026-09-15)

Ninth tranche: further journal / DOI / preprint Collatz literature (`<!-- AUTO:ARXIV100I -->` in `index.md`).
Same scaffolding rules: recorded `mainStatement`, checked bridges only.

## Batch J (2026-09-15)

Tenth tranche: further journal / DOI Collatz literature (`<!-- AUTO:ARXIV100J -->` in `index.md`).
Same scaffolding rules: recorded `mainStatement`, checked bridges only.

## Batch K (2026-09-16)

Eleventh tranche: further journal / DOI / preprint Collatz literature (`<!-- AUTO:ARXIV100K -->` in `index.md`).
Same scaffolding rules: recorded `mainStatement`, checked bridges only.

## Batch L (2026-09-16)

Twelfth tranche: further journal / DOI / preprint Collatz literature (`<!-- AUTO:ARXIV100L -->` in `index.md`).
Same scaffolding rules: recorded `mainStatement`, checked bridges only.

## Batch M (2026-09-16)

Thirteenth tranche: further journal / DOI / preprint Collatz literature (`<!-- AUTO:ARXIV100M -->` in `index.md`).
Same scaffolding rules: recorded `mainStatement`, checked bridges only.

## Batch N (2026-09-16)

Fourteenth tranche: further journal / DOI / preprint Collatz literature (`<!-- AUTO:ARXIV100N -->` in `index.md`).
Same scaffolding rules: recorded `mainStatement`, checked bridges only.

## Batch O (2026-09-16)

Fifteenth tranche: further journal / DOI / preprint Collatz literature (`<!-- AUTO:ARXIV100O -->` in `index.md`).
Same scaffolding rules: recorded `mainStatement`, checked bridges only.

## Batch P (2026-09-16)

Sixteenth tranche: further journal / DOI / preprint Collatz literature (`<!-- AUTO:ARXIV100P -->` in `index.md`).
Same scaffolding rules: recorded `mainStatement`, checked bridges only.

## Batch Q (2026-09-16)

Seventeenth tranche: further journal / DOI / preprint Collatz literature (`<!-- AUTO:ARXIV100Q -->` in `index.md`).
Same scaffolding rules: recorded `mainStatement`, checked bridges only.

