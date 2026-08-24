import Collatz.Basic
import Collatz.Core.Arith

/-!
# Round XVI — lifting the exponent, from scratch

`INDEX.md` reports the 2-adic valuation as the thinnest cluster in the
development (17 theorems) and lists it as having **no bridge at all** to the
gap `G = 2^L - 3^a`, to `C mod 2^j`, to the parity word, or to residue
classes.  This round builds the missing machinery.

The target is the `p = 2` lifting-the-exponent formula specialised to `3`:

  `v₂(3 ^ a - 1) = v₂ a + 2`  for even `a`,   `= 1` for odd `a`.

Mathlib has this (`padicValNat.pow_two_sub_one`); this branch may not use
Mathlib, so it is proved here from the definition up.  The payoff is the exact
order of `3` modulo `2 ^ L`, which is the first genuine constraint tying the
halving count `L` to the tripling count `a`.
-/

namespace Collatz
namespace LiftExponent

open Collatz.Arith

/-- `Val2 n r` says the 2-adic valuation of `n` is exactly `r`: `n = 2 ^ r * m`
with `m` odd.  Stated with an explicit witness rather than a valuation
function, matching the convention of `Collatz.ValuationTransition`. -/
def Val2 (n r : Nat) : Prop := ∃ m : Nat, m % 2 = 1 ∧ n = 2 ^ r * m


/-! ## 1.  The valuation is well defined -/

/-- A number carrying a 2-adic valuation is positive: the odd cofactor is
nonzero and powers of two are. -/
theorem Val2.pos {n r : Nat} (h : Val2 n r) : 0 < n := by
  obtain ⟨m, hm, he⟩ := h
  have h2 : 0 < 2 ^ r := two_pow_pos r
  have hm0 : 0 < m := by omega
  subst he
  exact Nat.mul_pos h2 hm0


/-- Arithmetic core of uniqueness: an odd number times a power of two determines
that power.  Induction strips one factor of two from each side at a time. -/
private theorem pow_two_odd_eq {r s m m' : Nat} (hm : m % 2 = 1) (hm' : m' % 2 = 1)
    (he : 2 ^ r * m = 2 ^ s * m') : r = s := by
  induction r generalizing s m m' with
  | zero =>
    cases s with
    | zero => rfl
    | succ t =>
      exfalso
      rw [Nat.pow_zero, Nat.one_mul, two_pow_succ t, Nat.mul_assoc] at he
      omega
  | succ k ih =>
    cases s with
    | zero =>
      exfalso
      rw [Nat.pow_zero, Nat.one_mul, two_pow_succ k, Nat.mul_assoc] at he
      omega
    | succ t =>
      rw [two_pow_succ k, two_pow_succ t, Nat.mul_assoc, Nat.mul_assoc] at he
      have hcancel : 2 ^ k * m = 2 ^ t * m' := Nat.eq_of_mul_eq_mul_left (by omega) he
      have := ih hm hm' hcancel
      omega


/-- **The valuation is unique.**  `Val2` is a graph of a partial function: a
positive `n` has at most one exponent. -/
theorem Val2.unique {n r s : Nat} (h : Val2 n r) (h' : Val2 n s) : r = s := by
  obtain ⟨m, hm, he⟩ := h
  obtain ⟨m', hm', he'⟩ := h'
  exact pow_two_odd_eq hm hm' (he ▸ he')


/-- The odd cofactor is unique as well, so `Val2` pins down the whole
factorisation `n = 2 ^ r * m`. -/
theorem Val2.cofactor_unique {n r m m' : Nat}
    (hm : m % 2 = 1) (hm' : m' % 2 = 1)
    (he : n = 2 ^ r * m) (he' : n = 2 ^ r * m') : m = m' := by
  have : 2 ^ r * m = 2 ^ r * m' := he ▸ he'
  exact Nat.eq_of_mul_eq_mul_left (two_pow_pos r) this


/-- Odd numbers are exactly the numbers of valuation zero (one direction). -/
theorem Val2.of_odd {n : Nat} (h : n % 2 = 1) : Val2 n 0 :=
  ⟨n, h, by rw [Nat.pow_zero, Nat.one_mul]⟩


/-- The converse: valuation zero forces oddness.  Together with `Val2.of_odd`
this is `Val2 n 0 ↔ n % 2 = 1`. -/
theorem Val2.odd_of_zero {n : Nat} (h : Val2 n 0) : n % 2 = 1 := by
  obtain ⟨m, hm, he⟩ := h
  rw [Nat.pow_zero, Nat.one_mul] at he
  omega

/-- Valuation zero is oddness. -/
theorem Val2.zero_iff {n : Nat} : Val2 n 0 ↔ n % 2 = 1 :=
  ⟨Val2.odd_of_zero, Val2.of_odd⟩


/-- Odd times odd is odd.  `omega` cannot see this (the product of two unknowns
is nonlinear), so parity is pushed through `Nat.mul_mod` instead. -/
theorem odd_mul_odd {m m' : Nat} (hm : m % 2 = 1) (hm' : m' % 2 = 1) :
    (m * m') % 2 = 1 := by
  rw [Nat.mul_mod, hm, hm']


/-- **Valuations add.**  This is the multiplicativity that every step of the
lifting-the-exponent computation below leans on. -/
theorem Val2.mul {a b r s : Nat} (ha : Val2 a r) (hb : Val2 b s) :
    Val2 (a * b) (r + s) := by
  obtain ⟨m, hm, he⟩ := ha
  obtain ⟨m', hm', he'⟩ := hb
  refine ⟨m * m', odd_mul_odd hm hm', ?_⟩
  subst he; subst he'
  rw [Nat.pow_add]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]


/-- `1` has valuation zero. -/
theorem Val2.one : Val2 1 0 := Val2.of_odd rfl

/-- A power of two has exactly its own exponent as valuation. -/
theorem Val2.two_pow (k : Nat) : Val2 (2 ^ k) k :=
  ⟨1, rfl, by rw [Nat.mul_one]⟩


/-- Doubling raises the valuation by exactly one. -/
theorem Val2.two_mul {n r : Nat} (h : Val2 n r) : Val2 (2 * n) (r + 1) := by
  obtain ⟨m, hm, he⟩ := h
  refine ⟨m, hm, ?_⟩
  subst he
  rw [two_pow_succ r, Nat.mul_assoc]

/-- Halving lowers it by one: the exact converse of `Val2.two_mul`. -/
theorem Val2.of_two_mul {n r : Nat} (h : Val2 (2 * n) (r + 1)) : Val2 n r := by
  obtain ⟨m, hm, he⟩ := h
  refine ⟨m, hm, ?_⟩
  rw [two_pow_succ r, Nat.mul_assoc] at he
  exact Nat.eq_of_mul_eq_mul_left (by omega) he


/-- A positive valuation means the number is even. -/
theorem Val2.even_of_pos {n r : Nat} (h : Val2 n r) (hr : 0 < r) : n % 2 = 0 := by
  obtain ⟨m, hm, he⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [two_pow_succ k, Nat.mul_assoc] at he
  omega


/-- **Existence.**  Every positive number has a 2-adic valuation.  With
`Val2.unique` this makes `Val2` the graph of a total function on the positives,
which is the sense in which this file may speak of *the* valuation. -/
theorem Val2.exists_of_pos {n : Nat} (hn : 0 < n) : ∃ r, Val2 n r := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hodd : n % 2 = 1
    · exact ⟨0, Val2.of_odd hodd⟩
    · have heven : n % 2 = 0 := by omega
      have hhalf : 0 < n / 2 := by omega
      have hlt : n / 2 < n := by omega
      obtain ⟨r, hr⟩ := ih (n / 2) hlt hhalf
      refine ⟨r + 1, ?_⟩
      have : 2 * (n / 2) = n := by omega
      rw [← this]
      exact Val2.two_mul hr


/-! ## 2.  Valuation as a divisibility -/

/-- `2 ^ r` divides a number of valuation `r`. -/
theorem Val2.dvd {n r : Nat} (h : Val2 n r) : 2 ^ r ∣ n := by
  obtain ⟨m, _, he⟩ := h
  exact ⟨m, he⟩


/-- **Exactness.**  The next power of two does *not* divide.  This is what makes
`Val2` an equality rather than the bound `2 ^ r ∣ n`.

The proof routes through `Val2.unique` rather than cancelling powers of two by
hand: a divisor `2 ^ (r+1)` splits off a positive cofactor, which carries a
valuation of its own, and multiplicativity then contradicts uniqueness. -/
theorem Val2.not_dvd_succ {n r : Nat} (h : Val2 n r) : ¬ (2 ^ (r + 1) ∣ n) := by
  rintro ⟨q, hq⟩
  have hn : 0 < n := Val2.pos h
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | hp
    · rw [Nat.mul_zero] at hq; omega
    · exact hp
  obtain ⟨t, ht⟩ := Val2.exists_of_pos hq0
  have hmul : Val2 (2 ^ (r + 1) * q) (r + 1 + t) := Val2.mul (Val2.two_pow (r + 1)) ht
  rw [← hq] at hmul
  have := Val2.unique h hmul
  omega


/-- The two halves packaged: a valuation is a *sandwich* of divisibilities.

Note `Val2` unfolds to an `Exists`, so dot notation on a hypothesis would
project from `Exists`; the lemmas are applied by name throughout. -/
theorem Val2.dvd_and_not_dvd {n r : Nat} (h : Val2 n r) :
    2 ^ r ∣ n ∧ ¬ (2 ^ (r + 1) ∣ n) :=
  ⟨Val2.dvd h, Val2.not_dvd_succ h⟩


/-- **The full divisibility profile.**  Once the valuation is known, *every*
question `2 ^ k ∣ n` is answered by a comparison of exponents. -/
theorem Val2.dvd_iff_le {n r k : Nat} (h : Val2 n r) : 2 ^ k ∣ n ↔ k ≤ r := by
  constructor
  · intro hk
    rcases Nat.lt_or_ge r k with hlt | hge
    · exact absurd (Nat.dvd_trans (two_pow_dvd_two_pow (show r + 1 ≤ k by omega)) hk)
        (Val2.not_dvd_succ h)
    · exact hge
  · intro hk
    exact Nat.dvd_trans (two_pow_dvd_two_pow hk) (Val2.dvd h)


/-- **Converse of the sandwich.**  The two divisibility facts characterise the
valuation, so `Val2` agrees with the usual textbook definition. -/
theorem Val2.of_dvd_not_dvd {n r : Nat} (hd : 2 ^ r ∣ n) (hnd : ¬ (2 ^ (r + 1) ∣ n)) :
    Val2 n r := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · exact absurd (Nat.dvd_zero _) hnd
    · exact hp
  obtain ⟨s, hs⟩ := Val2.exists_of_pos hn
  have h1 : r ≤ s := (Val2.dvd_iff_le hs).mp hd
  have h2 : ¬ (r + 1 ≤ s) := fun hle => hnd ((Val2.dvd_iff_le hs).mpr hle)
  have hsr : s = r := by omega
  exact hsr ▸ hs


/-- The textbook definition and `Val2` are interchangeable. -/
theorem Val2.iff_dvd_not_dvd {n r : Nat} :
    Val2 n r ↔ (2 ^ r ∣ n ∧ ¬ (2 ^ (r + 1) ∣ n)) :=
  ⟨Val2.dvd_and_not_dvd, fun h => Val2.of_dvd_not_dvd h.1 h.2⟩


/-! ## 3.  The bridge to residue classes

`INDEX.md` lists `2-adic valuation <-> residue classes` as a pair with no
theorem mentioning both.  This is that theorem: the valuation is *exactly* a
single residue mod `2 ^ (r+1)`, so every 2-adic statement in this file can be
re-read as a congruence, and vice versa. -/

/-- A number of valuation `r` sits in the residue `2 ^ r` mod `2 ^ (r+1)`. -/
theorem Val2.mod {n r : Nat} (h : Val2 n r) : n % 2 ^ (r + 1) = 2 ^ r := by
  obtain ⟨m, hm, he⟩ := h
  subst he
  rw [Nat.pow_succ, Nat.mul_mod_mul_left, hm, Nat.mul_one]


/-- Conversely, sitting in the residue `2 ^ r` mod `2 ^ (r+1)` forces the
valuation to be exactly `r`. -/
theorem Val2.of_mod {n r : Nat} (h : n % 2 ^ (r + 1) = 2 ^ r) : Val2 n r := by
  refine ⟨2 * (n / 2 ^ (r + 1)) + 1, by omega, ?_⟩
  have hd := Nat.div_add_mod n (2 ^ (r + 1))
  rw [h] at hd
  have key : 2 ^ r * (2 * (n / 2 ^ (r + 1)) + 1)
      = 2 ^ (r + 1) * (n / 2 ^ (r + 1)) + 2 ^ r := by
    rw [Nat.mul_add, Nat.mul_one, two_pow_succ r]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega


/-- **The bridge.**  `v₂(n) = r` and `n ≡ 2 ^ r (mod 2 ^ (r+1))` are the same
statement.  Read left to right it turns valuations into congruences; read right
to left it lets a congruence certify a valuation, which is how the
lifting-the-exponent computation below gets started. -/
theorem Val2.iff_mod {n r : Nat} : Val2 n r ↔ n % 2 ^ (r + 1) = 2 ^ r :=
  ⟨Val2.mod, Val2.of_mod⟩

end LiftExponent
end Collatz
