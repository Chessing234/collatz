# Sketches — outside the build and outside the integrity gate

`ProgramA`–`ProgramG` were drafted against `Mathlib` and contain `sorry`.  This
repository has neither dependency: `lakefile.lean` does not pull `Mathlib`, and
`scripts/check_integrity.sh` rejects `sorry` anywhere under `Collatz/`.  They
were never imported by `Collatz.lean`, so nothing in the build refers to them.

They are kept verbatim here so the ideas survive; move a file back under
`Collatz/` only once it is `Mathlib`-free and `sorry`-free.
