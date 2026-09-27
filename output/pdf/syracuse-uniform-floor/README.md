# Uniform Syracuse atom theorem: verified paper and code

The theorem-specific build and the complete 824-line Lean appendix both passed
on 12 September 2026. The report is `verification.json`. The theorem assumes
no Collatz convergence hypothesis. It uses only propext, Classical.choice,
and Quot.sound. This is not a proof of the full Collatz conjecture.

## Contents

- `syracuse-uniform-floor.pdf`: 21-page paper, with the Lean proof at the end.
- `syracuse-uniform-floor.tex`: complete LaTeX source, including the exact Lean listing.
- `SyracuseUniformFloor.lean`: separately compiled consolidated proof.
- `verification.json`, `theorem-build.log`, `appendix-lean.log`: proof checks.
- `latex-build.log`: successful final typesetting pass.
- `fonts/`: JuliaMono font and its license, needed for the Lean Unicode symbols.
- `SHA256SUMS.json`: content hashes for the delivered files.

## Rebuild the PDF

From this directory, with XeLaTeX and the standard TeX Live packages installed:

```sh
xelatex -halt-on-error syracuse-uniform-floor.tex
xelatex -halt-on-error syracuse-uniform-floor.tex
```

The source uses TeX Gyre fonts from TeX Live and the bundled JuliaMono font.
It does not require the Lean project merely to typeset the PDF.

## Recheck the Lean appendix

From the existing repository's `ProofAtlasAttack` directory:

```sh
lake --rehash build +CollatzTargetDensity.SyracuseCylinderSpread:olean
lake env lean ../output/pdf/syracuse-uniform-floor/SyracuseUniformFloor.lean
```

If this document bundle is extracted elsewhere, replace the final path by the
absolute path to its `SyracuseUniformFloor.lean`. The file requires the existing
pinned project and its three declared supporting imports; the ZIP is a document
bundle, not a copy of all Mathlib and the imported analytic source library.

The paper explicitly identifies Tao's and Mazur's analytic contributions.
Historical priority and independent peer review are not claimed.
