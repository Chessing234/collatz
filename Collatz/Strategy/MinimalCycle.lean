import Collatz.Strategy.CycleCriterion
import Collatz.Strategy.CycleProduct
import Collatz.Strategy.AccumulatorArith

/-!
# The minimal counterexample, and why no edit of its word can descend

A hypothetical nontrivial cycle is, by `CycleAccumulator`, a triple `(L, a, C)`
with `(2 ^ L − 3 ^ a) · n = C`, `C = affineC L n` the accumulator of the parity
word.  By `CycleCriterion.cycle_of_gap_dvd` the *converse* holds too: any word
whose gap divides its accumulator IS a cycle.  So a descent argument on a
minimal counterexample would like to *edit the word* — delete a step, shorten a
run, merge two runs — and land on a smaller cycle.

By Terras every edited word is realised by a residue class, so realisability is
never the obstruction.  The obstruction is integrality: the edited gap must
divide the edited accumulator.  This file measures exactly how far that is from
possible.

## The gap is pinned (`gap_le_half`, `three_pow_ge_half_pow`)

The product invariant with the verified floor `c = 768000` gives `2 ^ L ≤ 2·3 ^ a`,
so for any nontrivial cycle

    2 ^ (L−1)  ≤  3 ^ a  <  2 ^ L.

Two consequences.  First, `a` is *determined* by `L` (`oddCount_unique_of_pinned`):
the interval `[2^(L−1), 2^L)` has ratio `2 < 3` and so contains at most one power
of three.  Second, and decisively:

## Every deletion of an even step is impossible (`no_even_deletion`)

Deleting `e ≥ 1` even steps leaves `a` fixed and sends `L ↦ L − e`, so the new
gap is `2 ^ (L−e) − 3 ^ a ≤ 2 ^ (L−1) − 3 ^ a ≤ 0`: **not merely non-divisible,
but the wrong sign**, so there is no positive `n'` at all.  This kills, at once:
deleting an even step, shortening an even run, and merging two adjacent odd runs
(which deletes the whole even block between them).  The *only* deletion that
survives the sign test is deletion of an **odd** step, and there
(`odd_deletion_gap_large`) the new gap is at least `2 ^ (L−1) / 3` — a number of
size `2 ^ L`, so the divisibility it demands has density `2 ^ (−L)`.

This is the whole diagnosis of the edit programme.  A cycle exists because its
gap `G = 2 ^ L − 3 ^ a` is *exceptionally small* (it must divide `C`, and `n =
C / G`).  Every single-step edit moves `(L, a)` off the ledge
`2 ^ (L−1) ≤ 3 ^ a < 2 ^ L` and produces a gap of size `Θ(2 ^ L)`.  Smallness of
the gap is a continued-fraction property of `log₂ 3`, and the convergent
denominators are `1, 2, 5, 12, 29, 41, 53, 306, …`: no edit of size one can
preserve it.

## The descent direction is insertion, not deletion (`append_even_descends`)

Appending an even step keeps `a` and `C` and sends `G ↦ G + 2 ^ L`, so if the new
gap divides `C` at all the new cycle point is `n' < n / 2` — a genuine descent.
It is unconditional (`append_even_descends` needs no floor).  But the divisor is
now larger than `2 ^ L`, and `append_even_needs_large` shows the descent cannot
even get off the ground unless `C > 2 ^ L`.

## Cutting at the minimum and the maximum gains nothing (`cut_exact`)

Cut the cycle word at its minimum and at its maximum.  Each block gives an
inequality: `M ≥ 3 ^ b n / 2 ^ s` from the first, `M ≤ 2 ^ (L−s) n / 3 ^ (a−b)`
from the second.  Chaining them yields exactly `3 ^ a ≤ 2 ^ L` and nothing more,
because — `cut_exact` — the two block accumulators reassemble into the global one
with **slack exactly zero**: `3 ^ (a−b)·C₁ + 2 ^ s·C₂ = (2 ^ L − 3 ^ a)·n`, which
is the cocycle law.  The two inequalities are two readings of the single fact
`M ≥ n`; they can never contradict.

## Prefixes: minimality by *length*, not by minimum (`prefix_cycle_ge_min`)

If a proper prefix of length `j` has a positive gap dividing its accumulator, the
quotient `x` is a genuine cycle point of length `j` — and `prefix_cycle_ge_min`
shows `x ≥ n`.  So minimality *by minimum element* says nothing about prefixes;
only minimality *by length* does.  That fixes the well-order to use.

## Soundness (`d = 1`)

`gap_le_half` is the only `d = 1`-specific step: it runs through
`CycleProduct.cycle_min_bound`, whose floor `c` is the verified range.  Everything
downstream of it — the even-deletion impossibility above all — inherits that.
The rest of the file (`cut_exact`, `prefix_cycle_ge_min`, `append_even_descends`)
is `d`-uniform, and is therefore satisfied by the genuine `3x−1` cycles as well;
those are recorded in `Mirror`.  For `3x−1` the gap is *negative*
(`5 → 7 → 10` has `2 ^ 3 − 3 ^ 2 = −1`), which is exactly why even-deletion is
available there and unavailable here.
-/

namespace Collatz
namespace MinimalCycle

open Congruence AffineExact AccCycle AccumulatorClass AccumulatorArith
open CycleAccumulator CycleProduct

/-! ## 1.  The gap is pinned to the top half -/

/-- **The gap is at most half.**  From the product invariant with a floor `c`
below the whole orbit, `2 ^ L ≤ 2 · 3 ^ a`.  This is the one place a `d = 1`
input enters: `c` is the verified range. -/
theorem gap_le_half {n c L : Nat} (hn : 0 < n) (hcpos : 0 < c)
    (hc : ∀ k : Nat, c ≤ acceleratedOrbit k n) (hcyc : AccIsCycleOf n L)
    (hsmall : 2 * oddCount n L ≤ 3 * c) :
    2 ^ L ≤ 2 * 3 ^ oddCount n L := by
  have hmin := cycle_min_bound hn hcpos hc hcyc.2 hsmall
  have hstep : 3 ^ oddCount n L * (3 * c + 2 * oddCount n L)
      ≤ 3 ^ oddCount n L * (3 * c + 3 * c) :=
    Nat.mul_le_mul_left _ (by omega)
  have hre : 3 ^ oddCount n L * (3 * c + 3 * c) = (3 * c) * (2 * 3 ^ oddCount n L) := by
    have e1 : 3 * c + 3 * c = 2 * (3 * c) := by omega
    rw [e1]
    calc 3 ^ oddCount n L * (2 * (3 * c))
        = (3 ^ oddCount n L * 2) * (3 * c) := (Nat.mul_assoc _ _ _).symm
      _ = (2 * 3 ^ oddCount n L) * (3 * c) := by rw [Nat.mul_comm (3 ^ oddCount n L) 2]
      _ = (3 * c) * (2 * 3 ^ oddCount n L) := Nat.mul_comm _ _
  have hchain : (3 * c) * 2 ^ L ≤ (3 * c) * (2 * 3 ^ oddCount n L) := by
    rw [← hre]; exact Nat.le_trans hmin hstep
  exact Nat.le_of_mul_le_mul_left hchain (by omega)

/-- Restated: `3 ^ a` is at least the half-power `2 ^ (L−1)`. -/
theorem three_pow_ge_half_pow {L a : Nat} (hL : 0 < L) (h : 2 ^ L ≤ 2 * 3 ^ a) :
    2 ^ (L - 1) ≤ 3 ^ a := by
  have hsplit : (2:Nat) ^ L = 2 * 2 ^ (L - 1) := by
    have : L = (L - 1) + 1 := by omega
    rw [this, Arith.two_pow_succ]
    simp
  omega

/-- **`a` is determined by `L`.**  The window `[2 ^ (L−1), 2 ^ L)` has ratio two,
and `3 > 2`, so it holds at most one power of three. -/
theorem oddCount_unique_of_pinned {L a b : Nat}
    (ha1 : 2 ^ L ≤ 2 * 3 ^ a) (ha2 : 3 ^ a < 2 ^ L)
    (hb1 : 2 ^ L ≤ 2 * 3 ^ b) (hb2 : 3 ^ b < 2 ^ L) : a = b := by
  have key : ∀ p q : Nat, 2 ^ L ≤ 2 * 3 ^ p → 3 ^ q < 2 ^ L → ¬ (p < q) := by
    intro p q hp hq hlt
    have hstep : (3:Nat) ^ (p + 1) ≤ 3 ^ q := Nat.pow_le_pow_right (by omega) (by omega)
    have hexp : (3:Nat) ^ (p + 1) = 3 * 3 ^ p := by
      rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have h1 := key a b ha1 hb2
  have h2 := key b a hb1 ha2
  omega

/-! ## 2.  Certificates and the deletion edits -/

/-- A *certificate*: a length, an odd-step count, an accumulator and a positive
integer fitting the cycle equation.  By `CycleCriterion.cycle_of_gap_dvd` this is
exactly the data of a cycle, with no dynamical side condition left. -/
def Cert (L a C n : Nat) : Prop :=
  0 < n ∧ 3 ^ a < 2 ^ L ∧ (2 ^ L - 3 ^ a) * n = C

/-- A genuine cycle is a certificate. -/
theorem cert_of_cycle {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    Cert L (oddCount n L) (affineC L n) n :=
  ⟨hn, (accCycle_bounds hn h).2.2, cycle_gap_mul hn h⟩

/-- **No even step can be deleted.**  Deleting `e ≥ 1` even steps fixes `a` and
drops `L` to `L − e`; the resulting gap is non-positive, so *no* accumulator
value whatever admits a positive solution.  Covers "shorten an even run by one"
(`e = 1`) and "merge two adjacent odd runs" (`e` = the length of the even block
between them). -/
theorem no_even_deletion {L a e C' n' : Nat} (hpin : 2 ^ L ≤ 2 * 3 ^ a)
    (he : 0 < e) (hle : e ≤ L) : ¬ Cert (L - e) a C' n' := by
  intro hcert
  have hhalf : 2 ^ (L - 1) ≤ 3 ^ a := three_pow_ge_half_pow (by omega) hpin
  have hmono : (2:Nat) ^ (L - e) ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have := hcert.2.1
  omega

/-- Special case: one even step. -/
theorem no_single_even_deletion {L a C' n' : Nat} (hL : 0 < L)
    (hpin : 2 ^ L ≤ 2 * 3 ^ a) : ¬ Cert (L - 1) a C' n' :=
  no_even_deletion hpin (by omega) hL

/-- **The odd deletion survives the sign test but not the size test.**  Deleting
one odd step sends `(L, a) ↦ (L−1, a−1)`; the new gap is always positive, and it
is at least a third of `2 ^ (L−1)`.  So the divisibility it demands is
divisibility by a number of size `2 ^ L`. -/
theorem odd_deletion_gap_large {L a : Nat} (h : 3 ^ (a + 1) < 2 ^ (L + 1)) :
    2 ^ L ≤ 3 * (2 ^ L - 3 ^ a) := by
  have h3 : (3:Nat) ^ (a + 1) = 3 * 3 ^ a := by rw [Nat.pow_succ, Nat.mul_comm]
  have h2 : (2:Nat) ^ (L + 1) = 2 * 2 ^ L := Arith.two_pow_succ L
  omega

/-- and in particular the odd-deleted gap is positive, so the sign test alone
does not kill it. -/
theorem odd_deletion_gap_pos {L a : Nat} (h : 3 ^ (a + 1) < 2 ^ (L + 1)) (hL : 0 < 2 ^ L) :
    3 ^ a < 2 ^ L := by
  have h3 : (3:Nat) ^ (a + 1) = 3 * 3 ^ a := by rw [Nat.pow_succ, Nat.mul_comm]
  have h2 : (2:Nat) ^ (L + 1) = 2 * 2 ^ L := Arith.two_pow_succ L
  omega

/-! ## 3.  The insertion edits: descent, at the price of a huge divisor -/

/-- **Appending an even step is a descent — if it is integral at all.**  The
accumulator is unchanged (an even step feeds nothing into it) and the gap grows
by `2 ^ L`, so the new cycle point is less than half the old one.  No floor, no
verified range, no minimality: pure arithmetic. -/
theorem append_even_descends {L a C n n' : Nat}
    (h : Cert L a C n) (h' : Cert (L + 1) a C n') : 2 * n' < n := by
  obtain ⟨hn, hlt, heq⟩ := h
  obtain ⟨hn', hlt', heq'⟩ := h'
  have h2 : (2:Nat) ^ (L + 1) = 2 * 2 ^ L := Arith.two_pow_succ L
  have h3pos : 0 < (3:Nat) ^ a := Nat.pow_pos (by omega)
  -- the new gap exceeds twice the old one
  have hgap : 2 * (2 ^ L - 3 ^ a) < 2 ^ (L + 1) - 3 ^ a := by omega
  have hstrict : 2 * ((2 ^ L - 3 ^ a) * n') < (2 ^ (L + 1) - 3 ^ a) * n' :=
    by
      have := Nat.mul_lt_mul_of_lt_of_le hgap (Nat.le_refl n') hn'
      calc 2 * ((2 ^ L - 3 ^ a) * n') = (2 * (2 ^ L - 3 ^ a)) * n' := by
            rw [Nat.mul_assoc]
        _ < (2 ^ (L + 1) - 3 ^ a) * n' := this
  have hmul : (2 ^ L - 3 ^ a) * (2 * n') < (2 ^ L - 3 ^ a) * n := by
    calc (2 ^ L - 3 ^ a) * (2 * n') = 2 * ((2 ^ L - 3 ^ a) * n') := by
          rw [Nat.mul_left_comm]
      _ < (2 ^ (L + 1) - 3 ^ a) * n' := hstrict
      _ = C := heq'
      _ = (2 ^ L - 3 ^ a) * n := heq.symm
  exact Nat.lt_of_mul_lt_mul_left hmul

/-- **…but it needs a large accumulator.**  A positive solution of the appended
equation forces `C > 2 ^ L`. -/
theorem append_even_needs_large {L a C n n' : Nat} (h : Cert L a C n)
    (h' : Cert (L + 1) a C n') : 2 ^ L < C := by
  obtain ⟨hn, hlt, heq⟩ := h
  obtain ⟨hn', hlt', heq'⟩ := h'
  have h2 : (2:Nat) ^ (L + 1) = 2 * 2 ^ L := Arith.two_pow_succ L
  have hone : (2 ^ (L + 1) - 3 ^ a) * 1 ≤ (2 ^ (L + 1) - 3 ^ a) * n' :=
    Nat.mul_le_mul_left _ hn'
  rw [Nat.mul_one] at hone
  have hpos : 0 < (2:Nat) ^ L := Arith.two_pow_pos L
  omega

/-- **Inserting an odd step needs a window.**  Positivity of the inserted gap is
`3 ^ (a+1) < 2 ^ (L+1)`, i.e. `3 · 3 ^ a < 2 · 2 ^ L`; combined with the pinning
`2 ^ (L−1) ≤ 3 ^ a` this confines `3 ^ a` to `[2 ^ (L−1), 2 ^ (L+1)/3)` — a
window of multiplicative width `4/3`, so it is available for only some `L`. -/
theorem insert_odd_gap_window {L a C' n' : Nat} (hL : 0 < L)
    (hpin : 2 ^ L ≤ 2 * 3 ^ a) (h : Cert (L + 1) (a + 1) C' n') :
    2 ^ (L - 1) ≤ 3 ^ a ∧ 3 * 3 ^ a < 2 * 2 ^ L := by
  refine ⟨three_pow_ge_half_pow hL hpin, ?_⟩
  have h3 : (3:Nat) ^ (a + 1) = 3 * 3 ^ a := by rw [Nat.pow_succ, Nat.mul_comm]
  have h2 : (2:Nat) ^ (L + 1) = 2 * 2 ^ L := Arith.two_pow_succ L
  have := h.2.1
  omega

/-! ## 4.  Cutting at the minimum and the maximum: slack exactly zero -/

/-- **The cut is an identity.**  Split the window at time `s`; the two block
affine laws multiply back into the global one with no loss.  `C₁` and `C₂` are
the two block accumulators, `b` and `c` the two block odd-step counts. -/
theorem cut_no_gain {n y s k b c C1 C2 : Nat}
    (h1 : 2 ^ s * y = 3 ^ b * n + C1) (h2 : 2 ^ k * n = 3 ^ c * y + C2) :
    2 ^ (s + k) * n = 3 ^ (b + c) * n + (3 ^ c * C1 + 2 ^ s * C2) := by
  have hstep : 2 ^ s * (2 ^ k * n) = 3 ^ c * (2 ^ s * y) + 2 ^ s * C2 := by
    rw [h2, Nat.mul_add, Nat.mul_left_comm]
  rw [h1] at hstep
  have hexp2 : (2:Nat) ^ (s + k) * n = 2 ^ s * (2 ^ k * n) := by
    rw [Nat.pow_add, Nat.mul_assoc]
  have hexp3 : (3:Nat) ^ (b + c) * n = 3 ^ c * (3 ^ b * n) := by
    rw [Nat.pow_add, Nat.mul_comm ((3:Nat) ^ b) ((3:Nat) ^ c), Nat.mul_assoc]
  rw [hexp2, hexp3, hstep, Nat.mul_add, Nat.add_assoc]

/-- The same statement for the genuine accumulators of the two blocks: the
cocycle law says the reassembly is exact, so the min/max cut yields precisely
`3 ^ a ≤ 2 ^ L` and no residual inequality. -/
theorem cut_exact {n s k : Nat} (hn : 0 < n) (hcyc : AccIsCycleOf n (s + k)) :
    3 ^ oddCount (acceleratedOrbit s n) k * affineC s n
        + 2 ^ s * affineC k (acceleratedOrbit s n)
      = (2 ^ (s + k) - 3 ^ oddCount n (s + k)) * n := by
  rw [← affineC_add n s k]
  exact (cycle_gap_mul hn hcyc).symm

/-- The only inequality the cut produces.  With `y = T^s(n)` any point of the
cycle, chaining "`y` is at least `3 ^ b n / 2 ^ s`" with "`y` is at most
`2 ^ k n / 3 ^ c`" gives back the gap positivity and nothing else. -/
theorem cut_yields_only_gap {n y s k b c C1 C2 : Nat}
    (h1 : 2 ^ s * y = 3 ^ b * n + C1) (h2 : 2 ^ k * n = 3 ^ c * y + C2) :
    3 ^ (b + c) * n ≤ 2 ^ (s + k) * n := by
  have := cut_no_gain h1 h2
  omega

/-! ## 5.  Prefixes: the derived cycle is never smaller -/

/-- **A prefix certificate produces a cycle point at least as large as the
minimum.**  If `n` is below its own orbit and a proper prefix of its word has a
positive gap dividing its accumulator, the quotient `x` satisfies `n ≤ x`.  So
minimality *by minimum element* never fires on a prefix; the descent must be run
on the *length*. -/
theorem prefix_cycle_ge_min {n j x : Nat} (hmin : n ≤ acceleratedOrbit j n)
    (hlt : 3 ^ oddCount n j < 2 ^ j)
    (hx : (2 ^ j - 3 ^ oddCount n j) * x = affineC j n) :
    n ≤ x := by
  have hex := affine_exact n j
  have hmono : 2 ^ j * n ≤ 2 ^ j * acceleratedOrbit j n := Nat.mul_le_mul_left _ hmin
  have hsub : (2 ^ j - 3 ^ oddCount n j) * n = 2 ^ j * n - 3 ^ oddCount n j * n :=
    Nat.sub_mul _ _ _
  have hle : 3 ^ oddCount n j * n ≤ 2 ^ j * n := Nat.mul_le_mul_right n (by omega)
  have hstep : (2 ^ j - 3 ^ oddCount n j) * n ≤ (2 ^ j - 3 ^ oddCount n j) * x := by
    rw [hx]; omega
  have hgap : 0 < 2 ^ j - 3 ^ oddCount n j := by omega
  exact Nat.le_of_mul_le_mul_left hstep hgap

/-- Packaged with the criterion: a prefix whose gap divides its accumulator is a
genuine cycle of the *shorter* length `j`, sitting at or above `n`.  Under
minimality by length this is the contradiction; under minimality by minimum it is
not. -/
theorem prefix_gives_shorter_cycle {n j x : Nat} (hmin : n ≤ acceleratedOrbit j n)
    (hlt : 3 ^ oddCount n j < 2 ^ j)
    (hx : (2 ^ j - 3 ^ oddCount n j) * x = affineC j n) :
    acceleratedOrbit j x = x ∧ n ≤ x :=
  ⟨(CycleCriterion.cycle_of_gap_dvd hlt hx).1, prefix_cycle_ge_min hmin hlt hx⟩

end MinimalCycle
end Collatz
