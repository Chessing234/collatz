import Collatz.Strategy.StairBound

/-!
# The spacing principle: the horizon is exponential in how sparse the elements are

Round XXIII replaced the constant `m` in the cycle product bound by the staircase
`m + 2j`, because a cycle's odd elements are **distinct**.  This file isolates the
mechanism, and then feeds it a second unused fact.

## The principle

Suppose the sorted odd elements of a cycle obey `n_j ≥ s_j` for some increasing
`s`.  Then `seq_product_bound` gives

`2 ^ L · ∏_{j<a} s_j ≤ ∏_{j<a} (3 s_j + 1)`,

and taking logarithms caps `Λ = L log 2 − a log 3` by `Σ_{j<a} log(1 + 1/(3 s_j))`.
If the elements are forced a distance `s` apart, that cap is `≈ (1/(3s))·log(1 + sa/m)`,
and it reaches the ceiling `log 2` only when

`a ≈ m · (2 ^ (3s) − 1) / s`.

**The horizon is exponential in the spacing.**  Every extra unit of provable
sparsity multiplies the reach by about eight.

| spacing | source | horizon |
|---|---|---|
| `s = 0` | constant `m` | `2.079 m` (Rounds XX–XXI) |
| `s = 2` | elements are distinct and odd | `31.5 m` (Round XXIII) |
| `s = 3` | **and coprime to 3** | `170 m` (here) |

## The second unused fact

`CycleModThree.mod_three_ne_zero_of_accCycle` already proves every element of an
accelerated cycle is coprime to `3` — `3n+1 ≢ 0 (mod 3)`, propagated around the
loop.  The product bound has never consumed it.

It forces spacing `3` rather than `2`, by an argument with no arithmetic in it at
all (`gap_six`): three odd numbers `n < n' < n''` with two gaps of `2` would be
`n, n+2, n+4`, whose residues mod `3` are `n, n+2, n+1` — all three residues, so
one of them is divisible by `3`.  **Two consecutive gaps of two are impossible**,
so every two steps advance by at least `6`, and

`n_j ≥ (m − 1) + 3j`   (`stair3_le_seq`).

`stair3_product_bound` is the resulting bound.  Against the `2j` staircase it is
termwise larger from `j = 1` on (`three_beats_two`), losing only the single factor
`m − 1` against `m` at `j = 0`.

## Honest scope

* Still a horizon, now at `170 m` instead of `31.5 m`.  Past it the bound is
  vacuous in exactly the way `ProductCeiling` describes.  **Collatz is not proved
  and neither half is closed.**
* The spacing table says where the remaining room is: `s = 3` is the last spacing
  available from local congruences, since odd-and-coprime-to-3 is `2` residues in
  `6` and finer moduli add nothing (mod `9` still leaves `6` of `9`).  Beating
  `s = 3` needs a *non-local* sparsity statement about cycle elements — that they
  cannot cluster just above the minimum.  No such statement exists here, and it is
  the natural next target.
* As in Round XXIII the bridge from the repository's cycle representation to a
  sorted enumeration of its odd elements is **not built**, so this is not yet
  plugged into `MinimalCycle`.
-/

namespace Collatz
namespace StairThree

open StairBound

/-! ## The principle, for an arbitrary lower staircase -/

/-- The cross-multiplied inequality against any dominated sequence. -/
theorem cross_prod_gen : ∀ (a : Nat) (n s : Nat → Nat),
    (∀ j, j < a → s j ≤ n j) →
    seqProdPlus n a * seqProd s a ≤ seqProd n a * seqProdPlus s a := by
  intro a
  induction a with
  | zero => intro n s _; simp [seqProdPlus, seqProd]
  | succ a ih =>
    intro n s hdom
    have hrec := ih n s (fun j hj => hdom j (by omega))
    have hterm : (3 * n a + 1) * s a ≤ n a * (3 * s a + 1) :=
      cross_step (hdom a (by omega))
    show ((3 * n a + 1) * seqProdPlus n a) * (s a * seqProd s a)
        ≤ (n a * seqProd n a) * ((3 * s a + 1) * seqProdPlus s a)
    have hL : ((3 * n a + 1) * seqProdPlus n a) * (s a * seqProd s a)
        = ((3 * n a + 1) * s a) * (seqProdPlus n a * seqProd s a) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hR : (n a * seqProd n a) * ((3 * s a + 1) * seqProdPlus s a)
        = (n a * (3 * s a + 1)) * (seqProd n a * seqProdPlus s a) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [hL, hR]
    exact Nat.mul_le_mul hterm hrec

/-- **The spacing principle.**  Any provable lower staircase `s` for the sorted odd
elements yields a product bound.  Round XXIII is the case `s j = m + 2j`. -/
theorem seq_product_bound {L a : Nat} {n s : Nat → Nat}
    (hpos : ∀ j, j < a → 0 < n j)
    (hdom : ∀ j, j < a → s j ≤ n j)
    (hcyc : 2 ^ L * seqProd n a = seqProdPlus n a) :
    2 ^ L * seqProd s a ≤ seqProdPlus s a := by
  have hcross := cross_prod_gen a n s hdom
  have hP : 0 < seqProd n a := seqProd_pos a hpos
  have hchain : seqProd n a * (2 ^ L * seqProd s a) ≤ seqProd n a * seqProdPlus s a := by
    have hrw : seqProd n a * (2 ^ L * seqProd s a) = seqProdPlus n a * seqProd s a := by
      rw [← hcyc]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [hrw]
    exact hcross
  exact Nat.le_of_mul_le_mul_left hchain hP

/-! ## Coprimality to three forces spacing three -/

/-- **No two consecutive gaps of two.**  Three increasing odd numbers with both
gaps equal to `2` are `n, n+2, n+4`, whose residues mod `3` are `n, n+2, n+1` —
every residue, so one is divisible by `3`.  Hence any two steps advance by at
least `6`. -/
theorem gap_six {n : Nat → Nat} (hodd : ∀ j, n j % 2 = 1)
    (hthree : ∀ j, n j % 3 ≠ 0) (hmono : ∀ j, n j < n (j + 1)) (j : Nat) :
    n j + 6 ≤ n (j + 2) := by
  have hje : j + 1 + 1 = j + 2 := by omega
  have m0 : n j < n (j + 1) := hmono j
  have m1 : n (j + 1) < n (j + 2) := by
    have h := hmono (j + 1)
    rw [hje] at h
    exact h
  have h0 := hodd j
  have h1 := hodd (j + 1)
  have h2 := hodd (j + 2)
  have t0 := hthree j
  have t1 := hthree (j + 1)
  have t2 := hthree (j + 2)
  rcases Nat.lt_or_ge (n (j + 2)) (n j + 6) with hlt | hge
  · exfalso
    -- both gaps would have to be exactly two, giving `n, n+2, n+4`
    have e1 : n (j + 1) = n j + 2 := by omega
    have e2 : n (j + 2) = n j + 4 := by omega
    rw [e1] at t1
    rw [e2] at t2
    rcases (by omega : n j % 3 = 1 ∨ n j % 3 = 2) with hc | hc
    · omega
    · omega
  · exact hge

/-- **The spacing-three staircase.**  With `M + 1 ≤ n 0`, coprimality to `3` gives
`n j ≥ M + 3j`.  Proved two steps at a time, which is what `gap_six` supplies. -/
theorem stair3_le_seq {n : Nat → Nat} {M : Nat} (hodd : ∀ j, n j % 2 = 1)
    (hthree : ∀ j, n j % 3 ≠ 0) (hmono : ∀ j, n j < n (j + 1))
    (h0 : M + 1 ≤ n 0) : ∀ j, M + 3 * j ≤ n j := by
  have hpair : ∀ i : Nat,
      M + 3 * (2 * i) ≤ n (2 * i) ∧ M + 3 * (2 * i + 1) ≤ n (2 * i + 1) := by
    intro i
    induction i with
    | zero =>
      have hm : n 0 < n 1 := hmono 0
      have p0 : n 0 % 2 = 1 := hodd 0
      have p1 : n 1 % 2 = 1 := hodd 1
      refine ⟨?_, ?_⟩
      · show M + 3 * 0 ≤ n 0
        omega
      · show M + 3 * 1 ≤ n 1
        omega
    | succ i ih =>
      obtain ⟨he, ho⟩ := ih
      have g0 := gap_six hodd hthree hmono (2 * i)
      have g1 := gap_six hodd hthree hmono (2 * i + 1)
      have e0 : 2 * i + 2 = 2 * (i + 1) := by omega
      have e1 : 2 * i + 1 + 2 = 2 * (i + 1) + 1 := by omega
      rw [e0] at g0
      rw [e1] at g1
      exact ⟨by omega, by omega⟩
  intro j
  rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with h | h
  · have hthis := (hpair (j / 2)).1
    have hji : 2 * (j / 2) = j := by omega
    rw [hji] at hthis
    exact hthis
  · have hthis := (hpair (j / 2)).2
    have hji : 2 * (j / 2) + 1 = j := by omega
    rw [hji] at hthis
    exact hthis

/-- **The spacing-three product bound.**  The cycle bound with the second unused
fact consumed. -/
theorem stair3_product_bound {L a M : Nat} {n : Nat → Nat}
    (hpos : ∀ j, j < a → 0 < n j)
    (hodd : ∀ j, n j % 2 = 1) (hthree : ∀ j, n j % 3 ≠ 0)
    (hmono : ∀ j, n j < n (j + 1)) (h0 : M + 1 ≤ n 0)
    (hcyc : 2 ^ L * seqProd n a = seqProdPlus n a) :
    2 ^ L * seqProd (fun j => M + 3 * j) a ≤ seqProdPlus (fun j => M + 3 * j) a :=
  seq_product_bound hpos (fun j _ => stair3_le_seq hodd hthree hmono h0 j) hcyc

/-! ## Comparison with the spacing-two staircase -/

/-- From `j = 1` on, the spacing-three staircase is termwise at least the
spacing-two one: `m + 2j ≤ (m − 1) + 3j`.  Only the `j = 0` factor is lost. -/
theorem three_beats_two {m j : Nat} (hm : 1 ≤ m) (hj : 1 ≤ j) :
    m + 2 * j ≤ (m - 1) + 3 * j := by omega

/-- The staircase of Round XXIII, as a sequence — so both bounds are instances of
the same `seq_product_bound`. -/
theorem stair_is_seqProd (m : Nat) : ∀ a : Nat,
    stair m a = seqProd (fun j => m + 2 * j) a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih => show (m + 2 * a) * stair m a = (m + 2 * a) * seqProd _ a; rw [ih]

/-- And likewise for the shifted product. -/
theorem stairPlus_is_seqProdPlus (m : Nat) : ∀ a : Nat,
    stairPlus m a = seqProdPlus (fun j => m + 2 * j) a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    show (3 * (m + 2 * a) + 1) * stairPlus m a = (3 * (m + 2 * a) + 1) * seqProdPlus _ a
    rw [ih]

end StairThree
end Collatz
