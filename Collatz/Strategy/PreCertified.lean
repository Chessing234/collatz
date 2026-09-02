import Collatz.Strategy.CertMonotone

/-!
# Pre-certified rungs: the frontier ladder banked ahead of the verified range

`RealizableFrontier6809` reaches frontier `6809` because the verified range
reaches `1 086 464`.  Everything above that is blocked by the range alone — the
certificate is a finite kernel computation that can be done *now*, for ranges
nobody has verified yet.

This file does that.  For each of the next six rungs it records the certificate
and the exponent gap, so that the day a range extension lands, the corresponding
frontier follows immediately with no further certificate work.  With
`CertMonotone.cert_mono_c`, a range at least as large as the threshold suffices;
it need not match it.

## The ladder

`A` is the certificate's reach in odd steps, `c` the least verified range that
attains it, and `F = ⌊A·log₂ 3⌋ + 1` the frontier in accelerated steps.

| `c` at least | `A` | frontier `F` | status |
|---|---|---|---|
| `1 086 055` | `4296` | `6809` | proved — `RealizableFrontier6809` |
| `1 358 718` | `4961` | `7863` | certificate banked here |
| `1 664 599` | `5626` | `8917` | certificate banked here |
| `2 010 160` | `6291` | `9971` | proved — `Frontier9971` |
| `2 403 661` | `6956` | `11025` | certificate banked here |
| `2 855 820` | `7621` | `12079` | certificate banked here |
| `3 380 808` | `8286` | `13133` | proved — `Frontier13133` |
| `3 997 765` | `8951` | `14187` | certificate banked here (Round LXXV.14) |

Each `c` is the exact threshold: the certificate fails at `c − 1`.  The rungs are
`306 + 665k`, the one-sided semiconvergent staircase of `log₂ 3` that
`Strategy.PosLadder` derives independently — the reach `A(c)` moves only on that
staircase, never between rungs, which is why the table has risers and no slope.

## What is and is not proved here

Proved: the certificates, and the gaps `2 ^ (F−1) < 3 ^ A`.  These are the two
kernel-checkable ingredients of a `length_ge_F` theorem.

*Round LXXV.14 note.*  Rungs `7863` through `13133` are no longer conditional —
`Strategy.Frontier13133` and its predecessors supply every range in the table.
`8951` is the first entry banked past that point, computed the same way: its
threshold `3 997 765` is the least `c` for which the certificate reaches, and the
routine that produced it reproduces all seven earlier thresholds exactly.

Not proved: any `length_ge_F` for `F > 6809`.  That needs `VerifiedBelow c` for
the corresponding `c`, which this development does not have.  Nothing here
asserts a cycle bound beyond the one `RealizableFrontier6809` already proves.
-/

namespace Collatz
namespace PreCertified

open RealizableBound

/-! ## The certificates -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
set_option exponentiation.threshold 20000 in
theorem cert_4961 : cert 4961 1358718 0 1 1 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
set_option exponentiation.threshold 20000 in
theorem cert_5626 : cert 5626 1664599 0 1 1 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
set_option exponentiation.threshold 20000 in
theorem cert_6291 : cert 6291 2010160 0 1 1 = true := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
set_option exponentiation.threshold 20000 in
theorem cert_6956 : cert 6956 2403661 0 1 1 = true := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
set_option exponentiation.threshold 20000 in
theorem cert_7621 : cert 7621 2855820 0 1 1 = true := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
set_option exponentiation.threshold 20000 in
theorem cert_8286 : cert 8286 3380808 0 1 1 = true := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
set_option exponentiation.threshold 20000 in
theorem cert_8951 : cert 8951 3997765 0 1 1 = true := by decide

/-! ## The certificates in consumable form

`RealizableBound.affineC_le_Bcap` and `le_fexp_of_affineC_le` take the
certificate as `G(i) < c` for every `i` below the reach.  This is that form. -/

theorem bank_4961 (i : Nat) (hi : i < 4961) :
    Bcap i + 3 ^ i * 1358718 < 2 * 2 ^ fexp i * 1358718 := by
  have h := cert_sound 4961 0 1358718 (by simpa using cert_4961) i hi
  simpa using h

theorem bank_5626 (i : Nat) (hi : i < 5626) :
    Bcap i + 3 ^ i * 1664599 < 2 * 2 ^ fexp i * 1664599 := by
  have h := cert_sound 5626 0 1664599 (by simpa using cert_5626) i hi
  simpa using h

theorem bank_6291 (i : Nat) (hi : i < 6291) :
    Bcap i + 3 ^ i * 2010160 < 2 * 2 ^ fexp i * 2010160 := by
  have h := cert_sound 6291 0 2010160 (by simpa using cert_6291) i hi
  simpa using h

theorem bank_6956 (i : Nat) (hi : i < 6956) :
    Bcap i + 3 ^ i * 2403661 < 2 * 2 ^ fexp i * 2403661 := by
  have h := cert_sound 6956 0 2403661 (by simpa using cert_6956) i hi
  simpa using h

theorem bank_7621 (i : Nat) (hi : i < 7621) :
    Bcap i + 3 ^ i * 2855820 < 2 * 2 ^ fexp i * 2855820 := by
  have h := cert_sound 7621 0 2855820 (by simpa using cert_7621) i hi
  simpa using h

theorem bank_8286 (i : Nat) (hi : i < 8286) :
    Bcap i + 3 ^ i * 3380808 < 2 * 2 ^ fexp i * 3380808 := by
  have h := cert_sound 8286 0 3380808 (by simpa using cert_8286) i hi
  simpa using h

theorem bank_8951 (i : Nat) (hi : i < 8951) :
    Bcap i + 3 ^ i * 3997765 < 2 * 2 ^ fexp i * 3997765 := by
  have h := cert_sound 8951 0 3997765 (by simpa using cert_8951) i hi
  simpa using h

/-! ## The exponent gaps

`2 ^ (F − 1) < 3 ^ A` says every accelerated cycle shorter than `F` has fewer
than `A` odd steps — exactly the range each certificate covers. -/

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
theorem pow_gap_4961 : (2:Nat) ^ 7862 < 3 ^ 4961 := by decide

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
theorem pow_gap_5626 : (2:Nat) ^ 8916 < 3 ^ 5626 := by decide

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
theorem pow_gap_6291 : (2:Nat) ^ 9970 < 3 ^ 6291 := by decide

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
theorem pow_gap_6956 : (2:Nat) ^ 11024 < 3 ^ 6956 := by decide

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
theorem pow_gap_7621 : (2:Nat) ^ 12078 < 3 ^ 7621 := by decide

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
theorem pow_gap_8286 : (2:Nat) ^ 13132 < 3 ^ 8286 := by decide

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
theorem pow_gap_8951 : (2:Nat) ^ 14186 < 3 ^ 8951 := by decide

end PreCertified
end Collatz
