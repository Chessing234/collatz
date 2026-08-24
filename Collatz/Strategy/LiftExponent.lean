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


/-- The bridge at `r = 1`, in plain numerals: valuation one is the class `2`
mod `4`. -/
theorem Val2.one_iff {n : Nat} : Val2 n 1 ↔ n % 4 = 2 := by
  simpa using (@Val2.iff_mod n 1)

/-- The bridge at `r = 2`: valuation two is the class `4` mod `8`. -/
theorem Val2.two_iff {n : Nat} : Val2 n 2 ↔ n % 8 = 4 := by
  simpa using (@Val2.iff_mod n 2)


/-! ## 4.  Powers of three modulo eight

Everything in the lifting-the-exponent computation reduces to one fact: `3`
has order `2` modulo `8`, so `3 ^ k` is `1` or `3` mod `8` according to the
parity of `k`.  Both `3 ^ k - 1` and `3 ^ k + 1` then have their valuations
read straight off `Val2.iff_mod`. -/

/-- Powers of nine are `1` mod `8`. -/
theorem nine_pow_mod_eight (j : Nat) : 9 ^ j % 8 = 1 := by
  induction j with
  | zero => rfl
  | succ i ih => rw [Nat.pow_succ, Nat.mul_mod, ih]


/-- An even power of three is a power of nine. -/
theorem three_pow_two_mul (j : Nat) : 3 ^ (2 * j) = 9 ^ j := by
  rw [Nat.pow_mul]


/-- **Even exponents.**  `3 ^ k ≡ 1 (mod 8)` when `k` is even. -/
theorem three_pow_mod_eight_even {k : Nat} (h : k % 2 = 0) : 3 ^ k % 8 = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  rw [three_pow_two_mul]
  exact nine_pow_mod_eight j


/-- **Odd exponents.**  `3 ^ k ≡ 3 (mod 8)` when `k` is odd. -/
theorem three_pow_mod_eight_odd {k : Nat} (h : k % 2 = 1) : 3 ^ k % 8 = 3 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  rw [Nat.pow_succ, Nat.mul_mod, three_pow_two_mul, nine_pow_mod_eight]


/-! ## 5.  The three base valuations -/

/-- For odd `a`, `3 ^ a - 1 ≡ 2 (mod 4)`, so its valuation is exactly `1`.
This is the base case of the lifting ladder, and on its own it already says the
odd exponents carry no 2-adic leverage at all. -/
theorem val2_three_pow_sub_one_odd {a : Nat} (h : a % 2 = 1) : Val2 (3 ^ a - 1) 1 := by
  have h8 := three_pow_mod_eight_odd h
  have hp := one_le_three_pow a
  exact Val2.one_iff.mpr (by omega)


/-- For odd `a`, `3 ^ a + 1 ≡ 4 (mod 8)`, so its valuation is exactly `2`.
Together with the previous lemma this is the `1 + 2 = 3` that seeds the whole
computation. -/
theorem val2_three_pow_add_one_odd {a : Nat} (h : a % 2 = 1) : Val2 (3 ^ a + 1) 2 := by
  have h8 := three_pow_mod_eight_odd h
  exact Val2.two_iff.mpr (by omega)


/-- For even `a`, `3 ^ a + 1 ≡ 2 (mod 4)`, so its valuation is exactly `1`.
This is why doubling the exponent past the first time adds only one to the
valuation. -/
theorem val2_three_pow_add_one_even {a : Nat} (h : a % 2 = 0) : Val2 (3 ^ a + 1) 1 := by
  have h8 := three_pow_mod_eight_even h
  exact Val2.one_iff.mpr (by omega)


/-! ## 6.  The ladder -/

/-- The difference of squares, in `Nat`, with the truncated subtraction handled
explicitly.  Doubling the exponent factors `3 ^ a - 1`, and each factor's
valuation is already known, so `Val2.mul` climbs one rung. -/
theorem three_pow_double_sub_one (b : Nat) :
    3 ^ (2 * b) - 1 = (3 ^ b - 1) * (3 ^ b + 1) := by
  have hb := one_le_three_pow b
  obtain ⟨y, hy⟩ : ∃ y, 3 ^ b = y + 1 := ⟨3 ^ b - 1, by omega⟩
  have hsq : 3 ^ (2 * b) = 3 ^ b * 3 ^ b := by
    rw [Nat.two_mul, Nat.pow_add]
  rw [hsq, hy]
  have expand : (y + 1) * (y + 1) = y * (y + 1 + 1) + 1 := by
    simp [Nat.mul_add, Nat.add_mul]
    omega
  simp only [Nat.add_sub_cancel]
  omega


/-- **The ladder, in the form the induction wants.**  Each rung doubles the
exponent: `3 ^ (2b) - 1 = (3^b - 1)(3^b + 1)`, the first factor is handled by
the inductive hypothesis, and the second contributes exactly one because `b` is
already even. -/
theorem val2_three_pow_sub_one_aux :
    ∀ t a : Nat, Val2 a (t + 1) → Val2 (3 ^ a - 1) (t + 3) := by
  intro t
  induction t with
  | zero =>
    intro a ha
    obtain ⟨m, hm, he⟩ := ha
    rw [Nat.pow_one] at he
    subst he
    rw [three_pow_double_sub_one]
    have hx : (1 : Nat) + 2 = 0 + 3 := by omega
    exact hx ▸ Val2.mul (val2_three_pow_sub_one_odd hm) (val2_three_pow_add_one_odd hm)
  | succ t ih =>
    intro a ha
    obtain ⟨m, hm, he⟩ := ha
    have hb : Val2 (2 ^ (t + 1) * m) (t + 1) := ⟨m, hm, rfl⟩
    have hab : a = 2 * (2 ^ (t + 1) * m) := by
      rw [he, two_pow_succ (t + 1), Nat.mul_assoc]
    subst hab
    rw [three_pow_double_sub_one]
    have heven := Val2.even_of_pos hb (by omega)
    have hx : t + 3 + 1 = t + 1 + 3 := by omega
    exact hx ▸ Val2.mul (ih _ hb) (val2_three_pow_add_one_even heven)


/-! ## 7.  Lifting the exponent

The headline of the round.  Mathlib proves this as `padicValNat.pow_two_sub_one`;
this branch may not use Mathlib, so the statement below is the end of a chain
that starts at the definition of `Val2`. -/

/-- **Lifting the exponent for `p = 2` and base `3`.**  If `a` has 2-adic
valuation `t ≥ 1` — that is, `a` is even — then

  `v₂(3 ^ a - 1) = v₂ a + 2`.

The hypothesis `1 ≤ t` is exactly evenness of `a`, and it cannot be dropped:
`val2_three_pow_sub_one_odd` shows the odd case gives `1`, not `2`. -/
theorem val2_three_pow_sub_one {a t : Nat} (ht : 1 ≤ t) (h : Val2 a t) :
    Val2 (3 ^ a - 1) (t + 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hx : s + 3 = s + 1 + 2 := by omega
  exact hx ▸ val2_three_pow_sub_one_aux s a h


/-! ## 8.  The payoff: how large a power of two can divide `3 ^ a - 1`

`INDEX.md` lists `2-adic valuation <-> gap G = 2^L - 3^a` as a pair with no
theorem mentioning both.  The gap vanishes modulo `2 ^ L` exactly when
`2 ^ L ∣ 3 ^ a - 1` after scaling, so the next theorem is the missing bridge:
it converts a statement about `L` halvings into a statement about `a`. -/

/-- **The order of `3` modulo `2 ^ L` is `2 ^ (L-2)`, for `L ≥ 3`.**

Stated as the divisibility it is used through: `2 ^ L` divides `3 ^ a - 1`
exactly when `2 ^ (L-2)` divides `a`.  Both directions are read off the
valuation formula through `Val2.dvd_iff_le`. -/
theorem two_pow_dvd_three_pow_sub_one_iff {a L : Nat} (ha : 0 < a) (hL : 3 ≤ L) :
    2 ^ L ∣ 3 ^ a - 1 ↔ 2 ^ (L - 2) ∣ a := by
  obtain ⟨t, hat⟩ := Val2.exists_of_pos ha
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hodd : a % 2 = 1 := Val2.odd_of_zero hat
    have hv : Val2 (3 ^ a - 1) 1 := val2_three_pow_sub_one_odd hodd
    constructor
    · intro hd
      have := (Val2.dvd_iff_le hv).mp hd
      omega
    · intro hd
      have := (Val2.dvd_iff_le hat).mp hd
      omega
  · have hv : Val2 (3 ^ a - 1) (t + 2) := val2_three_pow_sub_one ht hat
    rw [Val2.dvd_iff_le hv, Val2.dvd_iff_le hat]
    omega


/-! ## 9.  Restated as a congruence, and the order of three

The divisibility `2 ^ L ∣ 3 ^ q - 1` and the congruence `3 ^ q ≡ 1 (mod 2 ^ L)`
are the same fact; `Nat` subtraction makes the translation worth isolating. -/

/-- Congruence to one gives the divisibility. -/
theorem two_pow_dvd_of_three_pow_mod {q L : Nat} (h : 3 ^ q % 2 ^ L = 1) :
    2 ^ L ∣ 3 ^ q - 1 := by
  refine ⟨3 ^ q / 2 ^ L, ?_⟩
  have hd := Nat.div_add_mod (3 ^ q) (2 ^ L)
  rw [h] at hd
  omega


/-- The divisibility gives the congruence, for `L ≥ 1`. -/
theorem three_pow_mod_of_two_pow_dvd {q L : Nat} (hL : 1 ≤ L) (h : 2 ^ L ∣ 3 ^ q - 1) :
    3 ^ q % 2 ^ L = 1 := by
  obtain ⟨k, hk⟩ := h
  have hp := one_le_three_pow q
  have h2 : 2 ≤ 2 ^ L := two_le_two_pow hL
  have he : 3 ^ q = 2 ^ L * k + 1 := by omega
  rw [he, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)


/-- `3 ^ (2 ^ (L-2)) ≡ 1 (mod 2 ^ L)`: the candidate period really is one. -/
theorem three_pow_one_mod {L : Nat} (hL : 3 ≤ L) : 3 ^ (2 ^ (L - 2)) % 2 ^ L = 1 := by
  have hpos : 0 < 2 ^ (L - 2) := two_pow_pos _
  have hd : 2 ^ L ∣ 3 ^ (2 ^ (L - 2)) - 1 :=
    (two_pow_dvd_three_pow_sub_one_iff hpos hL).mpr (Nat.dvd_refl _)
  exact three_pow_mod_of_two_pow_dvd (by omega) hd


/-- **Periodicity.**  `3 ^ a` modulo `2 ^ L` repeats with period `2 ^ (L-2)`.

This is the finite-state content of the round: the sequence `a ↦ 3 ^ a mod 2 ^ L`
is eventually — in fact immediately — periodic, and the period is named
exactly. -/
theorem three_pow_period {L a : Nat} (hL : 3 ≤ L) :
    3 ^ (a + 2 ^ (L - 2)) % 2 ^ L = 3 ^ a % 2 ^ L := by
  have h1 := three_pow_one_mod hL
  obtain ⟨k, hk⟩ : ∃ k, 3 ^ (2 ^ (L - 2)) = 2 ^ L * k + 1 := by
    refine ⟨3 ^ (2 ^ (L - 2)) / 2 ^ L, ?_⟩
    have hd := Nat.div_add_mod (3 ^ (2 ^ (L - 2))) (2 ^ L)
    omega
  rw [Nat.pow_add, hk, Nat.mul_add, Nat.mul_one]
  have hcomm : 3 ^ a * (2 ^ L * k) = 2 ^ L * (3 ^ a * k) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hcomm, Nat.mul_add_mod]


/-- **Minimality.**  No smaller positive exponent works, so `2 ^ (L-2)` is the
*order* of `3` modulo `2 ^ L` and not merely some period. -/
theorem three_pow_period_minimal {L q : Nat} (hL : 3 ≤ L) (hq : 0 < q)
    (h : 3 ^ q % 2 ^ L = 1) : 2 ^ (L - 2) ≤ q := by
  have hd : 2 ^ L ∣ 3 ^ q - 1 := two_pow_dvd_of_three_pow_mod h
  have := (two_pow_dvd_three_pow_sub_one_iff hq hL).mp hd
  exact Nat.le_of_dvd hq this


/-- **The size constraint, in the form the gap cluster can use.**  A tripling
count `a` that is congruent to the trivial one modulo `2 ^ L` is at least
`2 ^ (L-2)`: an exponential lower bound on `a` in terms of `L`.

Contrapositively, for every `a < 2 ^ (L-2)` the residue `3 ^ a mod 2 ^ L` is
*not* `1`, which is what rules out short words in a `2 ^ L` congruence
argument. -/
theorem exponent_lower_bound {a L : Nat} (ha : 0 < a) (hL : 3 ≤ L)
    (h : 2 ^ L ∣ 3 ^ a - 1) : 2 ^ (L - 2) ≤ a :=
  Nat.le_of_dvd ha ((two_pow_dvd_three_pow_sub_one_iff ha hL).mp h)


/-- The contrapositive of `exponent_lower_bound`, spelled out because it is the
direction that does work: a short tripling count is never trivial mod `2 ^ L`. -/
theorem three_pow_ne_one_of_lt {a L : Nat} (ha : 0 < a) (hL : 3 ≤ L)
    (hlt : a < 2 ^ (L - 2)) : 3 ^ a % 2 ^ L ≠ 1 := by
  intro h
  have := three_pow_period_minimal hL ha h
  omega


/-! ## 10.  The two low levels, where the order formula does not apply

`two_pow_dvd_three_pow_sub_one_iff` needs `L ≥ 3`, because the order of `3` is
`1` mod `2` and mod `4` and only becomes `2 ^ (L-2)` afterwards.  The two
missing levels are recorded here so the case analysis is complete. -/

/-- At `L = 1` the condition is vacuous: `3 ^ a` is always odd. -/
theorem two_dvd_three_pow_sub_one (a : Nat) : 2 ∣ 3 ^ a - 1 := by
  have h := three_pow_odd a
  have hp := one_le_three_pow a
  exact ⟨(3 ^ a - 1) / 2, by omega⟩


/-- At `L = 2` the condition is exactly evenness of `a`.  So the order of `3`
is `1` mod `2`, `2` mod `4`, and `2 ^ (L-2)` from `L = 3` on — and at `L = 2`
the two formulas happen to agree. -/
theorem four_dvd_three_pow_sub_one_iff {a : Nat} : 4 ∣ 3 ^ a - 1 ↔ a % 2 = 0 := by
  have hp := one_le_three_pow a
  constructor
  · intro hd
    rcases Nat.eq_zero_or_pos (a % 2) with h | h
    · exact h
    · have hodd : a % 2 = 1 := by omega
      have h8 := three_pow_mod_eight_odd hodd
      obtain ⟨k, hk⟩ := hd
      omega
  · intro heven
    have h8 := three_pow_mod_eight_even heven
    exact ⟨(3 ^ a - 1) / 4, by omega⟩


/-! ## 11.  The gap, 2-adically

`GapPrimes.gap_odd` already records that `2 ^ L - 3 ^ a` is odd.  Restating it
as a `Val2` fact is what actually joins the two clusters: it lets the gap be
carried through `Val2.mul`, which is the next lemma.  The oddness is reproved
in two lines here rather than imported, to keep this file a leaf. -/

/-- The gap has 2-adic valuation zero: even minus odd. -/
theorem val2_gap {L a : Nat} (hL : 1 ≤ L) (hlt : 3 ^ a < 2 ^ L) :
    Val2 (2 ^ L - 3 ^ a) 0 := by
  have h2 : 2 ^ L % 2 = 0 := two_pow_even (by omega)
  have h3 : 3 ^ a % 2 = 1 := three_pow_odd a
  exact Val2.of_odd (by omega)


/-- **The gap is 2-adically invisible.**  Multiplying by `2 ^ L - 3 ^ a` leaves
the valuation unchanged.

In the affine law `(2 ^ L - 3 ^ a) · n = C` this says `v₂(C) = v₂(n)`: the
accumulator of a cycle carries exactly the 2-adic content of the cycle
minimum, no more and no less.  That is the concrete bridge between the
valuation cluster and the accumulator cluster. -/
theorem val2_gap_mul {L a x r : Nat} (hL : 1 ≤ L) (hlt : 3 ^ a < 2 ^ L)
    (hx : Val2 x r) : Val2 ((2 ^ L - 3 ^ a) * x) r := by
  have h := Val2.mul (val2_gap hL hlt) hx
  have hz : 0 + r = r := by omega
  exact hz ▸ h


/-- **In cycle terms.**  If `(2 ^ L - 3 ^ a) · n = C` — the affine law of a
cycle with `L` halvings, `a` triplings, minimum `n` and accumulator `C` — then
`C` and `n` have the same 2-adic valuation. -/
theorem val2_accumulator {L a n C r : Nat} (hL : 1 ≤ L) (hlt : 3 ^ a < 2 ^ L)
    (heq : (2 ^ L - 3 ^ a) * n = C) (hn : Val2 n r) : Val2 C r :=
  heq ▸ val2_gap_mul hL hlt hn


/-- The converse, by uniqueness of the valuation: the accumulator's valuation
determines the minimum's. -/
theorem val2_min_of_accumulator {L a n C r : Nat} (hL : 1 ≤ L) (hlt : 3 ^ a < 2 ^ L)
    (hn : 0 < n) (heq : (2 ^ L - 3 ^ a) * n = C) (hC : Val2 C r) : Val2 n r := by
  obtain ⟨s, hs⟩ := Val2.exists_of_pos hn
  have hCs : Val2 C s := val2_accumulator hL hlt heq hs
  have : s = r := Val2.unique hCs hC
  exact this ▸ hs


/-- The case the cycle arguments actually meet: a cycle minimum is odd, so its
accumulator is odd too. -/
theorem accumulator_odd {L a n C : Nat} (hL : 1 ≤ L) (hlt : 3 ^ a < 2 ^ L)
    (heq : (2 ^ L - 3 ^ a) * n = C) (hn : n % 2 = 1) : C % 2 = 1 :=
  Val2.odd_of_zero (val2_accumulator hL hlt heq (Val2.of_odd hn))


/-! ## 12.  Numerical checks

The formula predicts `v₂(3 ^ a - 1) = v₂ a + 2` for even `a` and `1` for odd
`a`.  Each line below is the prediction, verified against the actual
factorisation by `rfl`. -/

/-- `v₂ 2 = 1`, so the prediction is `3`, and `3 ^ 2 - 1 = 8 = 2 ^ 3 · 1`. -/
example : Val2 (3 ^ 2 - 1) 3 := ⟨1, rfl, rfl⟩

/-- `3` is odd, so the prediction is `1`, and `3 ^ 3 - 1 = 26 = 2 · 13`. -/
example : Val2 (3 ^ 3 - 1) 1 := ⟨13, rfl, rfl⟩

/-- `v₂ 4 = 2`, prediction `4`, and `3 ^ 4 - 1 = 80 = 2 ^ 4 · 5`. -/
example : Val2 (3 ^ 4 - 1) 4 := ⟨5, rfl, rfl⟩

/-- `v₂ 6 = 1`, prediction `3`, and `3 ^ 6 - 1 = 728 = 2 ^ 3 · 91`.  Note the
valuation *drops* from `a = 4` to `a = 6`: it tracks `v₂ a`, not `a`. -/
example : Val2 (3 ^ 6 - 1) 3 := ⟨91, rfl, rfl⟩

/-- `v₂ 8 = 3`, prediction `5`, and `3 ^ 8 - 1 = 6560 = 2 ^ 5 · 205`. -/
example : Val2 (3 ^ 8 - 1) 5 := ⟨205, rfl, rfl⟩

/-- `v₂ 12 = 2`, prediction `4`, and `3 ^ 12 - 1 = 531440 = 2 ^ 4 · 33215`. -/
example : Val2 (3 ^ 12 - 1) 4 := ⟨33215, rfl, rfl⟩


/-! ## 13.  What this round does *not* give

The order formula constrains `a` only under the hypothesis `2 ^ L ∣ 3 ^ a - 1`.
That hypothesis is not supplied by the cycle equation, and the last theorem of
this section shows it is worse than that: for every shape a cycle can have, the
hypothesis is outright *false*, so the constraint is vacuous there.  This is
recorded so no later round mistakes the bound for a cycle exclusion. -/

/-- `L < 2 ^ (L-2)` from `L = 5` on. -/
theorem lt_two_pow_sub_two {L : Nat} (hL : 5 ≤ L) : L < 2 ^ (L - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 5 := ⟨L - 5, by omega⟩
  have key : ∀ k : Nat, k + 5 < 2 ^ (k + 3) := by
    intro k
    induction k with
    | zero => decide
    | succ j ih =>
      have hs : (2 : Nat) ^ (j + 1 + 3) = 2 * 2 ^ (j + 3) := two_pow_succ (j + 3)
      omega
  have hx : k + 5 - 2 = k + 3 := by omega
  rw [hx]
  exact key k


/-- **The limitation, sharply.**  A cycle has at most as many triplings as
halvings, `a ≤ L`.  From `L = 5` on that forces `a < 2 ^ (L-2)`, and so
`2 ^ L ∤ 3 ^ a - 1`: the hypothesis of `exponent_lower_bound` is false for
*every* shape a cycle can have.

So this round supplies an exact order formula and no cycle exclusion.  The
formula's use is as a bound on how far a `2 ^ L` congruence argument can reach,
not as an obstruction in its own right. -/
theorem vacuous_for_cycle_shapes {L a : Nat} (hL : 5 ≤ L) (ha : 0 < a) (hle : a ≤ L) :
    ¬ (2 ^ L ∣ 3 ^ a - 1) := by
  intro hd
  have hbig := exponent_lower_bound ha (by omega) hd
  have := lt_two_pow_sub_two hL
  omega


/-! ## 14.  The rest of the `Val2` API

Facts later rounds will want, now that the valuation is available at all. -/

/-- A number of valuation `r` is at least `2 ^ r`. -/
theorem Val2.le {n r : Nat} (h : Val2 n r) : 2 ^ r ≤ n :=
  Nat.le_of_dvd (Val2.pos h) (Val2.dvd h)


/-- The valuation is monotone along divisibility. -/
theorem Val2.mono {m n r s : Nat} (hm : Val2 m r) (hn : Val2 n s) (hd : m ∣ n) : r ≤ s :=
  (Val2.dvd_iff_le hn).mp (Nat.dvd_trans (Val2.dvd hm) hd)


/-- **The ultrametric law.**  When the two valuations differ, the sum takes the
smaller one — exactly, not just as a bound.  (When they agree the valuation of
the sum is strictly larger and this fails, which is why the hypothesis `r < s`
cannot be weakened to `r ≤ s`.) -/
theorem Val2.add_of_lt {x y r s : Nat} (hx : Val2 x r) (hy : Val2 y s) (hrs : r < s) :
    Val2 (x + y) r := by
  obtain ⟨m, hm, hex⟩ := hx
  obtain ⟨m', hm', hey⟩ := hy
  refine ⟨m + 2 ^ (s - r) * m', ?_, ?_⟩
  · have h2 : 2 ^ (s - r) % 2 = 0 := two_pow_even (by omega)
    have heven : (2 ^ (s - r) * m') % 2 = 0 := by
      rw [Nat.mul_mod, h2]
      simp
    omega
  · have hsplit : (2 : Nat) ^ s = 2 ^ r * 2 ^ (s - r) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hex, hey, hsplit, Nat.mul_add, Nat.mul_assoc]


/-- `Val2.add_of_lt` with the summands the other way round. -/
theorem Val2.add_of_lt' {x y r s : Nat} (hx : Val2 x r) (hy : Val2 y s) (hrs : r < s) :
    Val2 (y + x) r := by
  have h := Val2.add_of_lt hx hy hrs
  rw [Nat.add_comm] at h
  exact h


/-- Sharpness of the hypothesis in `Val2.add_of_lt`: at `r = s` the valuation of
the sum jumps.  `2` and `2` both have valuation `1`, but `2 + 2 = 4` has
valuation `2`. -/
example : Val2 2 1 ∧ Val2 (2 + 2) 2 := ⟨⟨1, rfl, rfl⟩, ⟨1, rfl, rfl⟩⟩


/-- Valuations multiply under powers. -/
theorem Val2.pow {n r : Nat} (h : Val2 n r) (k : Nat) : Val2 (n ^ k) (r * k) := by
  induction k with
  | zero => exact Val2.one
  | succ j ih =>
    have hm := Val2.mul ih h
    have hx : r * j + r = r * (j + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [Nat.pow_succ]
    exact hx ▸ hm


/-- Scaling by a power of two shifts the valuation by that exponent. -/
theorem Val2.two_pow_mul {n r : Nat} (h : Val2 n r) (k : Nat) : Val2 (2 ^ k * n) (k + r) :=
  Val2.mul (Val2.two_pow k) h


/-! ## 15.  The formula packaged for use

`val2_three_pow_sub_one` asks the caller to supply `Val2 a t`.  Callers rarely
have it; they have the parity of `a`.  These three restatements take parity as
the hypothesis and produce the valuation. -/

/-- The even case, with the valuation of `a` produced rather than assumed. -/
theorem val2_three_pow_sub_one_even {a : Nat} (ha : 0 < a) (heven : a % 2 = 0) :
    ∃ t, 1 ≤ t ∧ Val2 a t ∧ Val2 (3 ^ a - 1) (t + 2) := by
  obtain ⟨t, hat⟩ := Val2.exists_of_pos ha
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | hp
    · exact absurd (Val2.odd_of_zero hat) (by omega)
    · exact hp
  exact ⟨t, ht, hat, val2_three_pow_sub_one ht hat⟩


/-- **The formula, whole.**  Every positive `a` falls in exactly one of the two
cases, and the valuation of `3 ^ a - 1` is determined either way. -/
theorem val2_three_pow_sub_one_dichotomy {a : Nat} (ha : 0 < a) :
    (a % 2 = 1 ∧ Val2 (3 ^ a - 1) 1) ∨
      (∃ t, 1 ≤ t ∧ Val2 a t ∧ Val2 (3 ^ a - 1) (t + 2)) := by
  rcases Nat.eq_zero_or_pos (a % 2) with h | h
  · exact Or.inr (val2_three_pow_sub_one_even ha h)
  · have hodd : a % 2 = 1 := by omega
    exact Or.inl ⟨hodd, val2_three_pow_sub_one_odd hodd⟩

end LiftExponent
end Collatz
