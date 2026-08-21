import Collatz.Strategy.ValuationBudget

/-!
# Simultaneous local conditions: the 3-adic side is empty, the joint side is free

Two questions are settled here.

## 1.  Is there a 3-adic obstruction to a cycle?

The cycle criterion is the **single linear equation** `G · n = C` with
`G = 2 ^ L − 3 ^ a` and `C = affineC L n`.  A linear equation in one unknown
obeys the Hasse principle trivially: it is solvable in `Z_p` exactly when
`v_p(G) ≤ v_p(C)`, and it is solvable in `Z` exactly when that holds at every
`p` at once, i.e. exactly when `G ∣ C`.  So *no* combination of local conditions
can say anything that `G ∣ C` does not already say.

At `p = 3` the local condition is not merely implied — it is **vacuous**.  As
soon as one odd step has happened, `3 ∣ 3 ^ a` while `3 ∤ 2 ^ L`, so
`v₃(G) = 0`: `G` is a unit in `Z₃`.  Therefore for *every* parity word, every
accumulator value `C` and every precision `j`, the closure condition
`G · n ≡ C (mod 3 ^ j)` has a solution, and the solution is unique modulo
`3 ^ j`.  Both halves are proved below (`three_adic_free`,
`three_adic_unique`), so the 3-adic data of a putative cycle is *determined by*
`C` and `G` and carries no independent information.

Concretely: the Syracuse step `x_{n+1} · 2 ^ k = 3 x_n + 1` gives
`x_{n+1} ≡ 2 ^ (−k) (3 x_n + 1) (mod 3 ^ j)`, so `x_{n+1} mod 3 ^ j` is a
function of `x_n mod 3 ^ (j−1)` and `k mod ord_(3^j)(2)`; in particular
`x_{n+1} ≡ 2 ^ (−k) (mod 3)` depends on the exponent parity **alone**.  Closing
up a cycle of `r` steps therefore looks like a condition on the exponent vector
— but it is not one: the composed relation is `(2 ^ K − 3 ^ r) x_0 ≡ C`, whose
multiplier is a 3-adic unit, so it solves for `x_0` instead of constraining the
exponents.  (Checked numerically for 3000 random exponent vectors at precisions
`3 ^ 1 … 3 ^ 8`: every one has a 3-adic cycle, and no orbit point is `≡ 0
mod 3` — the "no orbit point divisible by three" condition is automatic too.)

Combined with `NewModels.word_is_cycle_word` this closes the branch: the word
already *is* a cycle word of `3x + δ`, and the 3-adic condition is satisfied by
that cycle for free.

## 2.  Can several local conditions be jointly impossible?

`ValuationBudget.word_residue_free` shows the parity word and one odd modulus
are independent.  This file upgrades it in the two directions that were left
open, and both upgrades hold:

* **Several moduli at once** (`word_free_divisors`).  Prescribe residues at any
  family of moduli by prescribing a single integer `z` and working modulo the
  product; every divisor inherits.  No Chinese-remainder machinery is needed
  because the consistency question ("is there any `z` with those residues?")
  is entirely a question about the moduli and involves no word.
* **A modulus together with an exact size class** (`word_free_dyadic`).  The
  witnesses form a full arithmetic progression of modulus `m · 2 ^ j`, so every
  dyadic block `[2 ^ B, 2 ^ (B+1))` with `2 ^ B ≥ 2 · m · 2 ^ j` contains one.
  This is strictly stronger than `word_residue_free_large`, which only pushed
  the witness *above* a bound: here the magnitude is pinned to a prescribed
  block, so an obstruction may not use `⌊log₂ x⌋` either.

`word_free_dyadic_divisors` combines them.  Consequence: **no predicate that is
a function of (finite parity word, residues at finitely many odd moduli,
dyadic size class) can obstruct anything**, since all three coordinates are
independently prescribable above the stated threshold.

Soundness filter: nothing here uses the verified range or `accOrbit_small`, and
nothing is `d`-specific — correctly so, since all of it is a *no-go*.  A no-go
that survives the `3x−1` / `3x+5` worlds is exactly what one wants.
-/

namespace Collatz
namespace PAdicJoint

open Congruence AffineExact AccumulatorClass ValuationBudget

/-! ## Part 1 — three is a unit direction, so the 3-adic condition is empty -/

/-- `2 ^ L` is never divisible by three. -/
theorem two_pow_mod_three (L : Nat) : 2 ^ L % 3 = 1 ∨ 2 ^ L % 3 = 2 := by
  induction L with
  | zero => left; rfl
  | succ L ih =>
    have hp : (2:Nat) ^ (L + 1) = 2 * 2 ^ L := by
      rw [Nat.pow_succ]; exact Nat.mul_comm _ _
    have hm : (2 * 2 ^ L) % 3 = (2 % 3 * (2 ^ L % 3)) % 3 := Nat.mul_mod 2 (2 ^ L) 3
    rcases ih with h | h <;> rw [hp, hm, h] <;> decide

/-- Three divides a product with a non-multiple of three only through the other
factor.  This is Euclid's lemma at `p = 3`, done by hand. -/
theorem three_dvd_of_mul {G y : Nat} (hG : G % 3 ≠ 0) (h : (G * y) % 3 = 0) :
    y % 3 = 0 := by
  have hm : (G * y) % 3 = (G % 3 * (y % 3)) % 3 := Nat.mul_mod G y 3
  have h1 : G % 3 = 1 ∨ G % 3 = 2 := by omega
  have h2 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
  rcases h1 with hg | hg <;> rcases h2 with hy | hy | hy <;>
    rw [hg, hy] at hm <;> omega

/-- The same statement for an arbitrary power of three: `3 ^ k ∣ G · y` with
`3 ∤ G` forces `3 ^ k ∣ y`.  This is what makes the 3-adic solution unique. -/
theorem three_pow_dvd_of_mul {G : Nat} (hG : G % 3 ≠ 0) :
    ∀ (k y : Nat), 3 ^ k ∣ G * y → 3 ^ k ∣ y := by
  intro k
  induction k with
  | zero => intro y _; exact Nat.one_dvd y
  | succ k ih =>
    intro y hdvd
    have hy3 : y % 3 = 0 := by
      refine three_dvd_of_mul hG ?_
      obtain ⟨c, hc⟩ := hdvd
      have h3 : (3:Nat) ^ (k + 1) = 3 * 3 ^ k := by
        rw [Nat.pow_succ]; exact Nat.mul_comm _ _
      rw [h3, Nat.mul_assoc] at hc
      omega
    obtain ⟨y', hy'⟩ : ∃ y', y = 3 * y' := ⟨y / 3, by omega⟩
    have hstrip : 3 ^ k ∣ G * y' := by
      obtain ⟨c, hc⟩ := hdvd
      have h3 : (3:Nat) ^ (k + 1) = 3 * 3 ^ k := by
        rw [Nat.pow_succ]; exact Nat.mul_comm _ _
      rw [h3, Nat.mul_assoc, hy'] at hc
      have hc' : 3 * (G * y') = 3 * (3 ^ k * c) := by
        rw [← hc]; rw [Nat.mul_left_comm]
      exact ⟨c, by omega⟩
    obtain ⟨e, he⟩ := ih y' hstrip
    refine ⟨e, ?_⟩
    have h3 : (3:Nat) ^ (k + 1) = 3 * 3 ^ k := by
      rw [Nat.pow_succ]; exact Nat.mul_comm _ _
    rw [hy', he, h3, Nat.mul_assoc]

/-- The Hensel step written out: if `G · n = C + 3 ^ j · t` and the correction
`t + G · (G · u)` is a multiple of three, the shifted `n` solves modulo
`3 ^ (j+1)`. -/
theorem lift_step {G n t C j u s : Nat} (hnt : G * n = C + 3 ^ j * t)
    (hs : t + G * (G * u) = 3 * s) :
    G * (n + 3 ^ j * (G * u)) = C + 3 ^ j * 3 * s := by
  have h1 : G * (n + 3 ^ j * (G * u)) = G * n + 3 ^ j * (G * (G * u)) := by
    rw [Nat.mul_add, Nat.mul_left_comm]
  calc G * (n + 3 ^ j * (G * u))
      = G * n + 3 ^ j * (G * (G * u)) := h1
    _ = C + 3 ^ j * t + 3 ^ j * (G * (G * u)) := by rw [hnt]
    _ = C + (3 ^ j * t + 3 ^ j * (G * (G * u))) := Nat.add_assoc _ _ _
    _ = C + 3 ^ j * (t + G * (G * u)) := by rw [Nat.mul_add]
    _ = C + 3 ^ j * (3 * s) := by rw [hs]
    _ = C + 3 ^ j * 3 * s := by rw [Nat.mul_assoc]

/-- **Solvability at every 3-adic precision.**  If `3 ∤ G` then for every target
`C` and every precision `j` there are `n` and `t` with `G · n = C + 3 ^ j · t`,
i.e. `G · n ≡ C (mod 3 ^ j)`.  Explicit Hensel lifting; the correction uses
`G ^ 2 ≡ 1 (mod 3)`. -/
theorem three_adic_solve {G : Nat} (hG : G % 3 ≠ 0) :
    ∀ (j C : Nat), ∃ n t : Nat, G * n = C + 3 ^ j * t := by
  intro j
  induction j with
  | zero =>
    intro C
    have hGpos : 0 < G := by omega
    have hle : C ≤ G * C := Nat.le_mul_of_pos_left C hGpos
    exact ⟨C, G * C - C, by simp; omega⟩
  | succ j ih =>
    intro C
    obtain ⟨n, t, hnt⟩ := ih C
    have hGG : (G * G) % 3 = 1 := by
      have hm : (G * G) % 3 = (G % 3 * (G % 3)) % 3 := Nat.mul_mod G G 3
      have h1 : G % 3 = 1 ∨ G % 3 = 2 := by omega
      rcases h1 with hg | hg <;> rw [hg] at hm <;> omega
    have hzero : (G * (G * ((3 - t % 3) % 3))) % 3 = (3 - t % 3) % 3 := by
      have hassoc : G * (G * ((3 - t % 3) % 3)) = (G * G) * ((3 - t % 3) % 3) :=
        (Nat.mul_assoc _ _ _).symm
      have hm : ((G * G) * ((3 - t % 3) % 3)) % 3
          = ((G * G) % 3 * (((3 - t % 3) % 3) % 3)) % 3 := Nat.mul_mod _ _ 3
      rw [hassoc, hm, hGG]
      omega
    have hdvd : (t + G * (G * ((3 - t % 3) % 3))) % 3 = 0 := by omega
    obtain ⟨s, hs⟩ : ∃ s, t + G * (G * ((3 - t % 3) % 3)) = 3 * s :=
      ⟨(t + G * (G * ((3 - t % 3) % 3))) / 3, by omega⟩
    refine ⟨n + 3 ^ j * (G * ((3 - t % 3) % 3)), s, ?_⟩
    have hpow : (3:Nat) ^ (j + 1) = 3 ^ j * 3 := Nat.pow_succ 3 j
    rw [hpow]
    exact lift_step hnt hs

/-- **The 3-adic closure condition is vacuous.**  For every `G` prime to three,
every accumulator value `C` and every precision `j`, the cycle relation
`G · n ≡ C (mod 3 ^ j)` has a solution.  So it excludes no parity word. -/
theorem three_adic_free {G : Nat} (hG : G % 3 ≠ 0) (j C : Nat) :
    ∃ n : Nat, (G * n) % 3 ^ j = C % 3 ^ j := by
  obtain ⟨n, t, hnt⟩ := three_adic_solve hG j C
  exact ⟨n, by rw [hnt, Nat.add_mul_mod_self_left]⟩

/-- …and the solution is unique modulo `3 ^ j`.  Hence the 3-adic data of a
putative cycle is *determined by* `C` and `G` and carries no extra information:
there is exactly one 3-adic candidate, always. -/
theorem three_adic_unique {G : Nat} (hG : G % 3 ≠ 0) {j n n' : Nat}
    (h : (G * n) % 3 ^ j = (G * n') % 3 ^ j) : n % 3 ^ j = n' % 3 ^ j := by
  have hcases : n' ≤ n ∨ n ≤ n' := Nat.le_total n' n
  have key : ∀ p q : Nat, q ≤ p → (G * p) % 3 ^ j = (G * q) % 3 ^ j →
      p % 3 ^ j = q % 3 ^ j := by
    intro p q hqp hpq
    obtain ⟨w, hw⟩ : ∃ w, p = q + w := ⟨p - q, by omega⟩
    have hGw : G * p = G * q + G * w := by rw [hw, Nat.mul_add]
    have hd := Nat.div_add_mod (G * p) (3 ^ j)
    have hd' := Nat.div_add_mod (G * q) (3 ^ j)
    have hq' : G * q / 3 ^ j ≤ G * p / 3 ^ j :=
      Nat.div_le_div_right (by rw [hGw]; omega)
    have he : G * p / 3 ^ j = G * q / 3 ^ j + (G * p / 3 ^ j - G * q / 3 ^ j) := by omega
    have hexp : 3 ^ j * (G * q / 3 ^ j + (G * p / 3 ^ j - G * q / 3 ^ j))
        = 3 ^ j * (G * q / 3 ^ j) + 3 ^ j * (G * p / 3 ^ j - G * q / 3 ^ j) :=
      Nat.mul_add _ _ _
    rw [he] at hd
    have hGwe : G * w = 3 ^ j * (G * p / 3 ^ j - G * q / 3 ^ j) := by omega
    have hdvd : 3 ^ j ∣ w := three_pow_dvd_of_mul hG j w ⟨_, hGwe⟩
    obtain ⟨c, hc⟩ := hdvd
    rw [hw, hc, Nat.add_mul_mod_self_left]
  rcases hcases with hle | hle
  · exact key n n' hle h
  · exact (key n' n hle h.symm).symm

/-- The gap of a cycle with at least one odd step is prime to three, because
`3 ∣ 3 ^ a` and `3 ∤ 2 ^ L`. -/
theorem gap_mod_three {L a : Nat} (ha : 0 < a) (hle : 3 ^ a ≤ 2 ^ L) :
    (2 ^ L - 3 ^ a) % 3 ≠ 0 := by
  obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have h3 : (3:Nat) ^ a = 3 ^ b * 3 := by rw [hb, Nat.pow_succ]
  have hdvd : (3:Nat) ^ a % 3 = 0 := by rw [h3]; exact Nat.mul_mod_left _ _
  have h2 := two_pow_mod_three L
  omega

/-- **The 3-adic branch is dead.**  For every length `L`, every odd-step count
`a ≥ 1` with `3 ^ a ≤ 2 ^ L`, every accumulator value `C` and every precision
`j`, the closure condition `(2 ^ L − 3 ^ a) · n ≡ C (mod 3 ^ j)` is solvable, and
its solution is unique.  Nothing about the exponent vector is constrained. -/
theorem cycle_three_adic_vacuous {L a : Nat} (ha : 0 < a) (hle : 3 ^ a ≤ 2 ^ L)
    (j C : Nat) :
    ∃ n : Nat, ((2 ^ L - 3 ^ a) * n) % 3 ^ j = C % 3 ^ j :=
  three_adic_free (gap_mod_three ha hle) j C

/-! ## Part 2 — several odd moduli, and an exact size class, are jointly free -/

/-- **Several moduli at once.**  Prescribing residues at every divisor of an odd
`M` costs nothing: the single witness congruent to `z` modulo `M` is congruent
to `z` modulo every divisor.  Consistency of the prescribed residues is a
question about the moduli alone — if any integer `z` has them, a word-preserving
witness has them too. -/
theorem word_free_divisors {M : Nat} (hM : M % 2 = 1) (x j z N : Nat) :
    ∃ y : Nat, N ≤ y ∧ (∀ m : Nat, m ∣ M → y % m = z % m) ∧
      ∀ i : Nat, i ≤ j → oddCount y i = oddCount x i ∧ affineC i y = affineC i x := by
  obtain ⟨y, hN, hr, hw⟩ := ValuationBudget.word_residue_free_large hM x j z N
  refine ⟨y, hN, ?_, hw⟩
  intro m hm
  have h1 : y % M % m = y % m := Nat.mod_mod_of_dvd y hm
  have h2 : z % M % m = z % m := Nat.mod_mod_of_dvd z hm
  rw [← h1, ← h2, hr]

/-- **A modulus together with an exact size class.**  For every odd `m`, every
window length `j`, every target residue `r`, and every `B` with
`2 · m · 2 ^ j ≤ 2 ^ B`, there is a `y` in the dyadic block `[2 ^ B, 2 · 2 ^ B)`
with `x`'s whole window and `y ≡ r (mod m)`.

This is the sharp form: the witnesses are a full arithmetic progression of
modulus `m · 2 ^ j`, so once a block is at least twice that long it must meet
the progression.  An obstruction may therefore not combine the word, an odd
congruence and `⌊log₂ x⌋`. -/
theorem word_free_dyadic {m : Nat} (hm : m % 2 = 1) (x j r B : Nat)
    (hB : 2 * (m * 2 ^ j) ≤ 2 ^ B) :
    ∃ y : Nat, 2 ^ B ≤ y ∧ y < 2 * 2 ^ B ∧ y % m = r % m ∧
      ∀ i : Nat, i ≤ j → oddCount y i = oddCount x i ∧ affineC i y = affineC i x := by
  have hmpos : 0 < m := by omega
  have hjp : 0 < 2 ^ j := Arith.two_pow_pos j
  have hPpos : 0 < m * 2 ^ j := Nat.mul_pos hmpos hjp
  obtain ⟨y0, _, h2, hrm⟩ := ValuationBudget.exists_congr_of_word hm x j r
  -- reduce the witness below the modulus of the progression
  have hdvdm : m ∣ m * 2 ^ j := ⟨2 ^ j, rfl⟩
  have hdvdj : (2:Nat) ^ j ∣ m * 2 ^ j := ⟨m, Nat.mul_comm _ _⟩
  have hy1m : y0 % (m * 2 ^ j) % m = y0 % m := Nat.mod_mod_of_dvd y0 hdvdm
  have hy1j : y0 % (m * 2 ^ j) % 2 ^ j = y0 % 2 ^ j := Nat.mod_mod_of_dvd y0 hdvdj
  have hy1lt : y0 % (m * 2 ^ j) < m * 2 ^ j := Nat.mod_lt _ hPpos
  -- the block index
  have hdm := Nat.div_add_mod (2 ^ B) (m * 2 ^ j)
  have hrlt : 2 ^ B % (m * 2 ^ j) < m * 2 ^ j := Nat.mod_lt _ hPpos
  refine ⟨y0 % (m * 2 ^ j) + m * (2 ^ j * (2 ^ B / (m * 2 ^ j) + 1)), ?_, ?_, ?_, ?_⟩
  · have hexp : m * (2 ^ j * (2 ^ B / (m * 2 ^ j) + 1))
        = m * 2 ^ j * (2 ^ B / (m * 2 ^ j)) + m * 2 ^ j := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, ← Nat.mul_assoc]
    omega
  · have hexp : m * (2 ^ j * (2 ^ B / (m * 2 ^ j) + 1))
        = m * 2 ^ j * (2 ^ B / (m * 2 ^ j)) + m * 2 ^ j := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, ← Nat.mul_assoc]
    omega
  · rw [Nat.add_mul_mod_self_left, hy1m, hrm]
  · intro i hi
    have hcomm : y0 % (m * 2 ^ j) + m * (2 ^ j * (2 ^ B / (m * 2 ^ j) + 1))
        = y0 % (m * 2 ^ j) + 2 ^ j * (m * (2 ^ B / (m * 2 ^ j) + 1)) := by
      rw [Nat.mul_left_comm]
    have hmodj : (y0 % (m * 2 ^ j) + m * (2 ^ j * (2 ^ B / (m * 2 ^ j) + 1))) % 2 ^ j
        = x % 2 ^ j := by
      rw [hcomm, Nat.add_mul_mod_self_left, hy1j, h2]
    have hmodi := ValuationBudget.mod_two_pow_of_le hi hmodj
    exact ⟨oddCount_congr_of_mod hmodi, affineC_congr_of_mod hmodi⟩

/-- **The combined no-go.**  Word, residues at every divisor of an odd `M`, and
the exact dyadic size class are simultaneously prescribable.  Hence no predicate
built from those three kinds of data can obstruct a never-dropper, a heavy word,
or a cycle word. -/
theorem word_free_dyadic_divisors {M : Nat} (hM : M % 2 = 1) (x j z B : Nat)
    (hB : 2 * (M * 2 ^ j) ≤ 2 ^ B) :
    ∃ y : Nat, 2 ^ B ≤ y ∧ y < 2 * 2 ^ B ∧ (∀ m : Nat, m ∣ M → y % m = z % m) ∧
      ∀ i : Nat, i ≤ j → oddCount y i = oddCount x i ∧ affineC i y = affineC i x := by
  obtain ⟨y, hlo, hhi, hr, hw⟩ := word_free_dyadic hM x j z B hB
  refine ⟨y, hlo, hhi, ?_, hw⟩
  intro m hm
  have h1 : y % M % m = y % m := Nat.mod_mod_of_dvd y hm
  have h2 : z % M % m = z % m := Nat.mod_mod_of_dvd z hm
  rw [← h1, ← h2, hr]

/-- Refutation form.  A set `S` of residues modulo an odd `m` that contains the
residue of *every* point of a given dyadic block sharing `x`'s window is all of
them — the size restriction buys nothing. -/
theorem no_invariant_residue_set_in_block {m : Nat} (hm : m % 2 = 1) (x j B : Nat)
    (hB : 2 * (m * 2 ^ j) ≤ 2 ^ B) (S : Nat → Prop)
    (hS : ∀ y : Nat, 2 ^ B ≤ y → y < 2 * 2 ^ B →
      (∀ i : Nat, i ≤ j → oddCount y i = oddCount x i) → S (y % m)) :
    ∀ r : Nat, r < m → S r := by
  intro r hrm
  obtain ⟨y, hlo, hhi, hr, hw⟩ := word_free_dyadic hm x j r B hB
  have hy : y % m = r := by rw [hr]; exact Nat.mod_eq_of_lt hrm
  have := hS y hlo hhi (fun i hi => (hw i hi).1)
  rw [hy] at this
  exact this

end PAdicJoint
end Collatz
