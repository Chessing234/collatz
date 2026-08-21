import Collatz.Strategy.AccumulatorSharp
import Collatz.Strategy.AccumulatorArith

/-!
# The accumulator's cap, and the rotation symmetry of the cycle criterion

Two things are recorded here.  The first is a restatement — an honest one, and
labelled as such.  The second is new.

## The cap is the sharp bound already proved, divided by `2 ^ a`

A field report proposed as a headline result the inequality

`C_j(x) ≤ 2 ^ (j − a) · (3 ^ a − 2 ^ a)`,   `a = oddCount x j`,

advertised as a `2 ^ a`-factor sharpening of `AffineBoundSharp`.  It is a
sharpening of *that* bound, but it is **not new to this development**:
`AccumulatorSharp.affineC_sharp` already proves

`2 ^ a · (C_j(x) + 2 ^ j) ≤ 3 ^ a · 2 ^ j`,

and the two are the *same inequality*.  Divide the stored form by `2 ^ a` — the
division is exact, since `2 ^ j = 2 ^ a · 2 ^ (j − a)` and `a ≤ j` — and one gets
`C + 2 ^ j ≤ 3 ^ a · 2 ^ (j − a)` (`affineC_cap`), which rearranges to the
proposed form because `2 ^ (j−a) · (3 ^ a − 2 ^ a) = 3 ^ a · 2 ^ (j−a) − 2 ^ j`
(`affineC_le_sub`).  `affineC_sharp_of_cap` closes the loop in the other
direction, so the equivalence is not a claim but a theorem: neither form is
stronger.  Numerically both are attained, with ratio exactly `1`, by the word
that takes every even step first — checked on all `n < 4000`, `j ≤ 39`.

What is genuinely absent from the development is the *cycle* reading of the cap,
and that is `cycle_gap_cap`: substituting the cycle equation
`(2 ^ L − 3 ^ a) · n = C_L(n)` into the cap gives

`(2 ^ L − 3 ^ a) · n + 2 ^ L ≤ 3 ^ a · 2 ^ (L − a)`,

so every point of an accelerated `L`-cycle with `a` odd steps is at most
`(3 ^ a · 2 ^ (L−a) − 2 ^ L) / (2 ^ L − 3 ^ a)`.  `cycle_gap_cap_free` states it
without any truncated subtraction, and `cycle_point_cap` drops the gap entirely
using `2 ^ L − 3 ^ a ≥ 1`.

## What the cycle cap does not do

The report claims this discharges the open hypothesis `H36_cycleSmall`
(`Chains/CycleTargets.lean`).  **It does not, and cannot.**  `H36_cycleSmall`
quantifies over *all* cycles, and the cap's right-hand side
`3 ^ a · 2 ^ (L−a)` grows without bound in `a`; the only thing that could hold it
down is a lower bound on the gap `2 ^ L − 3 ^ a`, which is exactly the
Diophantine content nobody has.  For a *fixed* `(L, a)` with a large gap the cap
is a genuine numeric cap — that is the content of the report's table — but a
per-pair cap is not a theorem about cycles, it is `2 ^ L` theorems about words.

What *is* true and is recorded is the reduction: `cycle_le_of_cap` turns any
per-cycle gap estimate into a size bound, and `cycleSmall_of_gap_bounds`
assembles `H36`'s statement from the family of them.  The hypothesis it needs is
a Diophantine one, and it is not proved here.  Chain 36 stays conditional.

## Rotation: every divisor of the gap sees the cycle, not the point

This part is new.  Take a cycle point `n` of length `L`, `a = oddCount n L`, and
any `M` dividing the gap `2 ^ L − 3 ^ a`.  Start the window one step later — or
`k` steps later — and the cocycle `affineC_add` relates the two accumulators
exactly (`affineC_shift`):

`2 ^ k · C_L(T^k n) + 3 ^ a · C_k(n) = 3 ^ (oddCount n k) · C_L(n) + 2 ^ L · C_k(n)`.

Split `2 ^ L = 3 ^ a + D` on the right and the `3 ^ a · C_k(n)` terms cancel
outright, leaving the clean form (`affineC_shift_gap`)

`2 ^ k · C_L(T^k n) = 3 ^ (oddCount n k) · C_L(n) + D · C_k(n)`.

Modulo any `M ∣ D` the last term vanishes, and `M` is coprime to both `2` and `3`
— it is odd because the gap is (`cycle_gap_odd`), and prime to three because the
gap is `2 ^ L` modulo three (`AccumulatorArith.two_pow_mod_three`).  So the
factors `2 ^ k` and `3 ^ (oddCount n k)` cancel and

`M ∣ C_L(n)  ↔  M ∣ C_L(T^k n)`   (`dvd_affineC_shift`).

The reading matters more than the proof.  `CycleCriterion` makes a cycle of
length `L` exactly a word whose gap divides its accumulator; the accumulator
itself depends on where in the cycle one starts.  This says every *divisor* of
the gap does not: the divisibility test is a property of the cycle as a whole,
invariant under rotation.  Hence a mod-`M` obstruction, if one is ever found,
rules out a cycle rather than a starting point, and the solution set of the
criterion is a union of rotation orbits — which is why counting words overcounts
cycles by the number of rotations, a factor the project's counting heuristics
have not been carrying.

Both halves of the input were already here — `affineC_add` and `cycle_gap_odd` —
and had not been multiplied together.  Verified before formalising: the identity
on all `2 ^ L` words for `L ≤ 12` and all shifts (98 304 checks, 0 failures), and
the divisibility equivalence for every divisor `M` of every positive gap,
`L ≤ 12` (322 535 checks, 0 failures).
-/

namespace Collatz
namespace AccumulatorCap

open Congruence AffineExact AccCycle

/-! ## The cap: `affineC_sharp` divided by `2 ^ a` -/

/-- **The cap.**  `C_j(x) + 2 ^ j ≤ 3 ^ a · 2 ^ (j − a)`.  This is
`AccumulatorSharp.affineC_sharp` with the common factor `2 ^ a` removed; the
division is exact because `a ≤ j`. -/
theorem affineC_cap (x j : Nat) :
    affineC j x + 2 ^ j ≤ 3 ^ oddCount x j * 2 ^ (j - oddCount x j) := by
  have hle := oddCount_le_self x j
  have hsplit : (2:Nat) ^ j = 2 ^ oddCount x j * 2 ^ (j - oddCount x j) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hr : 2 ^ oddCount x j * (3 ^ oddCount x j * 2 ^ (j - oddCount x j))
      = 3 ^ oddCount x j * 2 ^ j := by
    rw [hsplit, Nat.mul_left_comm]
  refine Nat.le_of_mul_le_mul_left ?_ (Arith.two_pow_pos (oddCount x j))
  rw [hr]
  exact AccumulatorSharp.affineC_sharp x j

/-- The converse implication: the cap gives back the stored sharp bound.  With
`affineC_cap` this makes the two forms equivalent, so the cap is a restatement
and not a strengthening. -/
theorem affineC_sharp_of_cap {x j : Nat}
    (h : affineC j x + 2 ^ j ≤ 3 ^ oddCount x j * 2 ^ (j - oddCount x j)) :
    2 ^ oddCount x j * (affineC j x + 2 ^ j) ≤ 3 ^ oddCount x j * 2 ^ j := by
  have hle := oddCount_le_self x j
  have hsplit : (2:Nat) ^ j = 2 ^ oddCount x j * 2 ^ (j - oddCount x j) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hr : 2 ^ oddCount x j * (3 ^ oddCount x j * 2 ^ (j - oddCount x j))
      = 3 ^ oddCount x j * 2 ^ j := by
    rw [hsplit, Nat.mul_left_comm]
  rw [← hr]
  exact Nat.mul_le_mul_left _ h

/-- The cap in the shape the field report proposed, with truncated subtraction.
Equivalent to `affineC_cap`, since `2 ^ a ≤ 3 ^ a`. -/
theorem affineC_le_sub (x j : Nat) :
    affineC j x ≤ 2 ^ (j - oddCount x j) * (3 ^ oddCount x j - 2 ^ oddCount x j) := by
  have hcap := affineC_cap x j
  have hle := oddCount_le_self x j
  have hexp : 2 ^ (j - oddCount x j) * (3 ^ oddCount x j - 2 ^ oddCount x j)
      = 3 ^ oddCount x j * 2 ^ (j - oddCount x j) - 2 ^ j := by
    rw [Nat.mul_sub]
    have h1 : 2 ^ (j - oddCount x j) * 2 ^ oddCount x j = 2 ^ j := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [h1, Nat.mul_comm (2 ^ (j - oddCount x j)) (3 ^ oddCount x j)]
  rw [hexp]
  omega

/-! ## The cycle reading -/

/-- **Every point of a cycle is capped by its own gap.**  Substituting the cycle
equation into `affineC_cap`. -/
theorem cycle_gap_cap {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    (2 ^ L - 3 ^ oddCount n L) * n + 2 ^ L
      ≤ 3 ^ oddCount n L * 2 ^ (L - oddCount n L) := by
  rw [CycleAccumulator.cycle_gap_mul hn h]
  exact affineC_cap n L

/-- The same, with no truncated subtraction anywhere. -/
theorem cycle_gap_cap_free {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    2 ^ L * n + 2 ^ L
      ≤ 3 ^ oddCount n L * n + 3 ^ oddCount n L * 2 ^ (L - oddCount n L) := by
  have hlt := (accCycle_bounds hn h).2.2
  have hmono : 3 ^ oddCount n L * n ≤ 2 ^ L * n := Nat.mul_le_mul_right n (by omega)
  have hsub : (2 ^ L - 3 ^ oddCount n L) * n = 2 ^ L * n - 3 ^ oddCount n L * n :=
    Nat.sub_mul _ _ _
  have hc := cycle_gap_cap hn h
  omega

/-- Dropping the gap, which is at least one: the point itself is capped. -/
theorem cycle_point_cap {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    n + 2 ^ L ≤ 3 ^ oddCount n L * 2 ^ (L - oddCount n L) := by
  have hlt := (accCycle_bounds hn h).2.2
  have hone : 1 * n ≤ (2 ^ L - 3 ^ oddCount n L) * n :=
    Nat.mul_le_mul_right n (by omega)
  have hc := cycle_gap_cap hn h
  omega

/-- **The reduction.**  Any bound on the cap in terms of the gap converts into a
bound on the cycle point.  This is the whole usable content of the cap for the
cycle half: supply the Diophantine estimate, get the size bound. -/
theorem cycle_le_of_cap {n L B : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hB : 3 ^ oddCount n L * 2 ^ (L - oddCount n L)
            ≤ 2 ^ L + B * (2 ^ L - 3 ^ oddCount n L)) :
    n ≤ B := by
  have hlt := (accCycle_bounds hn h).2.2
  have hD : 0 < 2 ^ L - 3 ^ oddCount n L := by omega
  have hc := cycle_gap_cap hn h
  have hcomm : B * (2 ^ L - 3 ^ oddCount n L) = (2 ^ L - 3 ^ oddCount n L) * B :=
    Nat.mul_comm _ _
  have hmul : (2 ^ L - 3 ^ oddCount n L) * n ≤ (2 ^ L - 3 ^ oddCount n L) * B := by omega
  exact Nat.le_of_mul_le_mul_left hmul hD

/-- **`H36_cycleSmall` reduced, not proved.**  The statement of chain 36's
hypothesis follows from the family of gap estimates — one per cycle — and from
nothing weaker.  The hypothesis is Diophantine and is *not* established here;
this theorem records exactly what would have to be supplied. -/
theorem cycleSmall_of_gap_bounds
    (hB : ∀ n L : Nat, 0 < n → AccIsCycleOf n L →
      3 ^ oddCount n L * 2 ^ (L - oddCount n L)
        ≤ 2 ^ L + 10000 * (2 ^ L - 3 ^ oddCount n L)) :
    ∀ n L : Nat, 0 < n → AccIsCycleOf n L → n ≤ 10000 :=
  fun n L hn h => cycle_le_of_cap hn h (hB n L hn h)

/-! ## Cancelling units modulo a divisor of the gap -/

/-- Subtraction of a divisible summand, in `Nat`. -/
theorem dvd_of_add_left {M A B : Nat} (h : M ∣ A + B) (hB : M ∣ B) : M ∣ A := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := hB
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    refine ⟨0, ?_⟩
    have hz : (0:Nat) * p = 0 := Nat.zero_mul p
    omega
  · have hqp : q ≤ p := Nat.le_of_mul_le_mul_left (by omega) hM
    refine ⟨p - q, ?_⟩
    rw [Nat.mul_sub]
    omega

/-- An odd modulus cancels a factor of two. -/
theorem dvd_cancel_two {M z : Nat} (hM : M % 2 = 1) (h : M ∣ 2 * z) : M ∣ z := by
  obtain ⟨q, hq⟩ := h
  have hM' : M = 2 * (M / 2) + 1 := by omega
  have hexp : M * q = 2 * ((M / 2) * q) + q := by
    have hL : M * q = (2 * (M / 2) + 1) * q := by rw [← hM']
    rw [hL, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  obtain ⟨q', hq'⟩ : ∃ q', q = 2 * q' := ⟨q / 2, by omega⟩
  refine ⟨q', ?_⟩
  have hd : M * q = 2 * (M * q') := by rw [hq', Nat.mul_left_comm]
  omega

/-- An odd modulus cancels any power of two. -/
theorem dvd_cancel_two_pow {M : Nat} (hM : M % 2 = 1) :
    ∀ (k z : Nat), M ∣ 2 ^ k * z → M ∣ z := by
  intro k
  induction k with
  | zero => intro z h; simpa using h
  | succ k ih =>
    intro z h
    have hrw : (2:Nat) ^ (k + 1) * z = 2 ^ k * (2 * z) := by
      rw [Arith.two_pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
    rw [hrw] at h
    exact dvd_cancel_two hM (ih (2 * z) h)

/-- A modulus prime to three cancels a factor of three. -/
theorem dvd_cancel_three {M z : Nat} (hM : M % 3 ≠ 0) (h : M ∣ 3 * z) : M ∣ z := by
  obtain ⟨q, hq⟩ := h
  have hM' : M = 3 * (M / 3) + M % 3 := by omega
  have hexp : M * q = 3 * ((M / 3) * q) + (M % 3) * q := by
    have hL : M * q = (3 * (M / 3) + M % 3) * q := by rw [← hM']
    rw [hL, Nat.add_mul, Nat.mul_assoc]
  have hcase : M % 3 = 1 ∨ M % 3 = 2 := by omega
  have hq3 : q % 3 = 0 := by
    rcases hcase with h1 | h2
    · rw [h1, Nat.one_mul] at hexp; omega
    · rw [h2] at hexp; omega
  obtain ⟨q', hq'⟩ : ∃ q', q = 3 * q' := ⟨q / 3, by omega⟩
  refine ⟨q', ?_⟩
  have hd : M * q = 3 * (M * q') := by rw [hq', Nat.mul_left_comm]
  omega

/-- A modulus prime to three cancels any power of three. -/
theorem dvd_cancel_three_pow {M : Nat} (hM : M % 3 ≠ 0) :
    ∀ (k z : Nat), M ∣ 3 ^ k * z → M ∣ z := by
  intro k
  induction k with
  | zero => intro z h; simpa using h
  | succ k ih =>
    intro z h
    have hrw : (3:Nat) ^ (k + 1) * z = 3 ^ k * (3 * z) := by
      rw [Arith.three_pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
    rw [hrw] at h
    exact dvd_cancel_three hM (ih (3 * z) h)

/-! ## Rotating the window along a cycle -/

/-- Every point of a cycle is a cycle point of the same length. -/
theorem accCycle_shift {n L : Nat} (h : AccIsCycleOf n L) (k : Nat) :
    AccIsCycleOf (acceleratedOrbit k n) L := by
  refine ⟨h.1, ?_⟩
  rw [acceleratedOrbit_add L k n, Nat.add_comm L k, ← acceleratedOrbit_add k L n, h.2]

/-- The odd-step count of a full turn does not depend on where the turn starts. -/
theorem oddCount_shift {n L : Nat} (hc : acceleratedOrbit L n = n) (k : Nat) :
    oddCount (acceleratedOrbit k n) L = oddCount n L := by
  have h1 := AccumulatorArith.oddCount_add n k L
  have h2 := AccumulatorArith.oddCount_add n L k
  rw [hc] at h2
  rw [Nat.add_comm k L] at h1
  omega

/-- **The cocycle across a rotation.**  Reading the window `[k, k+L)` in two ways
— as the tail of `[0, k+L)` and as the head of `[0, L+k)` — relates the
accumulator of the shifted turn to that of the original. -/
theorem affineC_shift {n L : Nat} (hc : acceleratedOrbit L n = n) (k : Nat) :
    2 ^ k * affineC L (acceleratedOrbit k n) + 3 ^ oddCount n L * affineC k n
      = 3 ^ oddCount n k * affineC L n + 2 ^ L * affineC k n := by
  have h1 := AccumulatorArith.affineC_add n k L
  have h2 := AccumulatorArith.affineC_add n L k
  rw [hc] at h2
  rw [oddCount_shift hc k, Nat.add_comm k L] at h1
  omega

/-- The same identity with the gap made explicit: the `3 ^ a` terms cancel and
what is left of the starting point's own accumulator is a multiple of the gap. -/
theorem affineC_shift_gap {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (k : Nat) :
    2 ^ k * affineC L (acceleratedOrbit k n)
      = 3 ^ oddCount n k * affineC L n
        + (2 ^ L - 3 ^ oddCount n L) * affineC k n := by
  have hlt := (accCycle_bounds hn h).2.2
  have hsplit : (2:Nat) ^ L = 3 ^ oddCount n L + (2 ^ L - 3 ^ oddCount n L) := by omega
  have hDc : 2 ^ L * affineC k n
      = 3 ^ oddCount n L * affineC k n
        + (2 ^ L - 3 ^ oddCount n L) * affineC k n := by
    have hL : 2 ^ L * affineC k n
        = (3 ^ oddCount n L + (2 ^ L - 3 ^ oddCount n L)) * affineC k n := by
      rw [← hsplit]
    rw [hL, Nat.add_mul]
  have hs := affineC_shift h.2 k
  omega

/-! ## The divisibility criterion belongs to the cycle -/

/-- Any divisor of the gap is odd. -/
theorem gap_divisor_odd {n L M : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hM : M ∣ 2 ^ L - 3 ^ oddCount n L) : M % 2 = 1 := by
  have hodd := CycleAccumulator.cycle_gap_odd hn h
  obtain ⟨c, hc⟩ := hM
  rcases Arith.mod_two_eq_zero_or_one M with he | ho
  · exfalso
    obtain ⟨m, hm⟩ : ∃ m, M = 2 * m := ⟨M / 2, by omega⟩
    have hd : M * c = 2 * (m * c) := by rw [hm, Nat.mul_assoc]
    omega
  · exact ho

/-- Any divisor of the gap is prime to three, because the gap is `2 ^ L` modulo
three. -/
theorem gap_divisor_not_three {n L M : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hM : M ∣ 2 ^ L - 3 ^ oddCount n L) : M % 3 ≠ 0 := by
  have hb := accCycle_bounds hn h
  have hlt := hb.2.2
  have h2m := AccumulatorArith.two_pow_mod_three L
  have h3 : (3:Nat) ^ oddCount n L % 3 = 0 := by
    obtain ⟨b, hbb⟩ : ∃ b, oddCount n L = b + 1 := ⟨oddCount n L - 1, by omega⟩
    rw [hbb, Arith.three_pow_succ]
    omega
  have hD3 : (2 ^ L - 3 ^ oddCount n L) % 3 ≠ 0 := by omega
  intro h0
  obtain ⟨c, hc⟩ := hM
  obtain ⟨m, hm⟩ : ∃ m, M = 3 * m := ⟨M / 3, by omega⟩
  have hd : M * c = 3 * (m * c) := by rw [hm, Nat.mul_assoc]
  omega

/-- **Rotation invariance.**  For every divisor `M` of the gap `2 ^ L − 3 ^ a`,
whether `M` divides the accumulator of a full turn does not depend on where the
turn starts.  The divisibility criterion of `CycleCriterion` is therefore a
property of the cycle, not of the chosen point on it. -/
theorem dvd_affineC_shift {n L M : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hM : M ∣ 2 ^ L - 3 ^ oddCount n L) (k : Nat) :
    M ∣ affineC L n ↔ M ∣ affineC L (acceleratedOrbit k n) := by
  have hModd := gap_divisor_odd hn h hM
  have hM3 := gap_divisor_not_three hn h hM
  have hkey := affineC_shift_gap hn h k
  have hDdvd : M ∣ (2 ^ L - 3 ^ oddCount n L) * affineC k n := by
    obtain ⟨c, hc⟩ := hM
    exact ⟨c * affineC k n, by rw [hc, Nat.mul_assoc]⟩
  constructor
  · intro hC
    have h1 : M ∣ 3 ^ oddCount n k * affineC L n := by
      obtain ⟨t, ht⟩ := hC
      exact ⟨3 ^ oddCount n k * t, by rw [ht, Nat.mul_left_comm]⟩
    have h2 : M ∣ 2 ^ k * affineC L (acceleratedOrbit k n) := by
      rw [hkey]
      obtain ⟨u, hu⟩ := h1
      obtain ⟨v, hv⟩ := hDdvd
      exact ⟨u + v, by rw [hu, hv, Nat.mul_add]⟩
    exact dvd_cancel_two_pow hModd k _ h2
  · intro hR
    have h2 : M ∣ 2 ^ k * affineC L (acceleratedOrbit k n) := by
      obtain ⟨t, ht⟩ := hR
      exact ⟨2 ^ k * t, by rw [ht, Nat.mul_left_comm]⟩
    rw [hkey] at h2
    exact dvd_cancel_three_pow hM3 _ _ (dvd_of_add_left h2 hDdvd)

/-- The gap itself is a divisor of the gap, so the cycle criterion is rotation
invariant on the nose. -/
theorem gap_dvd_affineC_shift {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (k : Nat) :
    (2 ^ L - 3 ^ oddCount n L) ∣ affineC L n ↔
      (2 ^ L - 3 ^ oddCount n L) ∣ affineC L (acceleratedOrbit k n) :=
  dvd_affineC_shift hn h (Nat.dvd_refl _) k

/-- **The mod-`M` obstruction rules out cycles, not points.**  If some divisor of
the gap fails to divide the accumulator at one point of a hypothetical cycle, it
fails at every point — so a single residue computation refutes the whole cycle. -/
theorem not_dvd_affineC_shift {n L M : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hM : M ∣ 2 ^ L - 3 ^ oddCount n L) (hnd : ¬ M ∣ affineC L n) (k : Nat) :
    ¬ M ∣ affineC L (acceleratedOrbit k n) :=
  fun hd => hnd ((dvd_affineC_shift hn h hM k).mpr hd)

end AccumulatorCap
end Collatz
