# doi-10-5281-zenodo-22689783-residue-class-reduction-of-collatz-to-1

Citation: Andrew Stewart Caldin, "Residue-Class Reduction of Collatz to 1 mod 4 Cases — E8 Intelligence Research", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22689783 [2026].

Authors: Andrew Stewart Caldin

DOI: [10.5281/zenodo.22689783](https://doi.org/10.5281/zenodo.22689783)

Year: 2026

Venue: Zenodo (CERN European Organization for Nuclear Research)

Classification: cycle

Abstract:

FINDING: The Collatz recurrence, when analyzed via residue classes modulo 4, reduces the conjecture to checking convergence only for integers congruent to 1 mod 4 — a structural simplification that parallels lattice/root-system reduction. The Borel sigma-algebra videos are pedagogical, not novel; the arXiv paper is the substantive finding. MATH: - Collatz map: \( F(n) = n/2 \) if \( n \) even; \( F(n) = (3n+1)/2 \) if \( n \) odd. - Residue classes mod 4: \( n \equiv 0,1,2,3 \pmod{4} \). - Key reduction: If \( n \equiv 3 \pmod{4} \), then \( F(n) \equiv 1 \pmod{4} \) after one step (since \( 3(4k+3)+1 = 12k+10 = 2(6k+5) \), and \( 6k+5 \equiv 1 \pmod{4} \)). - Thus the entire orbit's converg...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_22689783.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-k (2026-09-16)
