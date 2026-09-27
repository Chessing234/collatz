# doi-10-5281-zenodo-21923376-a-certified-six-leaf-semantic-grammar-fo

Citation: Sam Hassanine, "A Certified Six-Leaf Semantic Grammar for the Collatz Dynamics in Lean 4", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21923376 [2026].

Authors: Sam Hassanine

DOI: [10.5281/zenodo.21923376](https://doi.org/10.5281/zenodo.21923376)

Year: 2026

Venue: Zenodo (CERN European Organization for Nuclear Research)

Classification: verification

Abstract:

This release provides a Lean 4.14.0 formalization of a finite, exhaustive, and exclusive six-leaf semantic grammar for the Collatz dynamics. Under the explicit premise CollatzVerifiedBelowBase68, the formal development establishes a global semantic classification with exactly six leaves. Either every positive natural number reaches 1, or there exists a unique positive minimal counterexample assigned to exactly one of five explicit failure leaves: 1. NONTRIVIAL_CYCLE2. RBC_UNBOUNDED_B_GAP3. RBC_BOUNDED_PRIME_RENEWAL4. NON_R_INTERNAL_DESCENT5. NON_R_SURVIVOR The principal publication theorem is: axisGeo_final_six_leaf_grammar_exactly_one The public API theorem is: certified_six_leaf_semantic_grammar The release includes the complete Lean source tree, reproducibility files, build logs, axiom...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_21923376.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-i (2026-09-15)
