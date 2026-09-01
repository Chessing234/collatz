import Collatz.Strategy.ExcursionMap

/-!
# The next odd cofactor, exactly

For odd `n` write `n + 1 = 2 ^ v * u` with `u` odd.  One excursion lands on
the odd state `e` cut out by `3 ^ v * u = 2 ^ W * e + 1`.  The next
excursion state is the odd cofactor of the landing:

  `e + 1 = 2 ^{v'} * u'`,  `u'` odd.

This file computes `u'` from `(v, W, u)` by an equality of naturals, then
asks whether `u` (or a Lyapunov built from `(v, u)`) decreases.

## The identity

Adding `2 ^ W` to the peak equation and dividing by `2 ^ W` is

  `e + 1 = (3 ^ v * u + 2 ^ W - 1) / 2 ^ W`.

The left side is `2 ^{v'} * u'`, so

  **`3 ^ v * u + 2 ^ W - 1 = 2 ^{W + v'} * u'`.**

Equivalently `u' = (3 ^ v * u + 2 ^ W - 1) / 2 ^{W + v'}`.  No residue
class is used: the next cofactor is this quotient, and it is odd because it
is the odd part of `e + 1`.

The comparison with the current cofactor is the same equality, read as an
inequality:

  `u' < u  ↔  2 ^ W - 1 < u * (2 ^{W + v'} - 3 ^ v)`.

In particular a light total exponent `2 ^{W + v'} ≤ 3 ^ v` forces `u < u'`.
Landing on a Mersenne number is `u' = 1`, which is `3 ^ v * u + 2 ^ W - 1`
being a pure power of two.

## Mixed, and no ranking

The identity is mixed.  Two witnesses, both kernel-checked:

* `7` has `(v, u) = (3, 1)` and lands on `13` with `u' = 7` — the cofactor
  grows.
* `27` has `(v, u) = (2, 7)` and lands on `31` with `u' = 1` — the cofactor
  crashes to a Mersenne.

Those two arrows are `1 → 7` and `7 → 1` on the cofactor.  Any energy that
is a function of `u` alone would have to strictly decrease along both, which
is impossible.  The same pair kills the other natural candidates on the
state `(v, u)`:

* lexicographic `(v, u)` grows at `27` (`v : 2 → 5`);
* lexicographic `(u, v)` grows at `7` (`u : 1 → 7`);
* the peak `3 ^ v * u` grows at `27` (`63 → 243`);
* the scaled cofactor `u * 3 ^{-v}` grows at `7` (`1/27 → 7/3`).

There is therefore no monotone energy of this shape.  The negative theorems
are the result; no further candidate is tried.
-/

namespace Collatz
namespace ExcursionCofactor

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap


/-! ## 1.  The next cofactor of a landing -/

/-- `e` is odd, so `e + 1` has a positive 2-adic valuation and an odd
cofactor: these are `(v', u')`. -/
theorem exists_next_cofactor {n v u W e : Nat} (h : IsExcursion n v u W e) :
    ∃ v' u' : Nat, u' % 2 = 1 ∧ 0 < v' ∧ e + 1 = 2 ^ v' * u' := by
  have he : e % 2 = 1 := h.2.2.1
  obtain ⟨v', hv'⟩ := Val2.exists_of_pos (Nat.succ_pos e)
  obtain ⟨u', hu', heq⟩ := hv'
  have hvpos : 0 < v' := by
    rcases Nat.eq_zero_or_pos v' with rfl | hp
    · have hodd : (e + 1) % 2 = 1 := Val2.odd_of_zero ⟨u', hu', heq⟩
      omega
    · exact hp
  exact ⟨v', u', hu', hvpos, heq⟩

/-- The next excursion exists, because the landing is odd. -/
theorem exists_next_excursion {n v u W e : Nat} (h : IsExcursion n v u W e) :
    ∃ v' u' W' e' : Nat, IsExcursion e v' u' W' e' :=
  exists_excursion h.2.2.1

/-- Uniqueness of the next valuation. -/
theorem next_v_unique {e v' u' v₂' u₂' : Nat}
    (hu' : u' % 2 = 1) (hu₂' : u₂' % 2 = 1)
    (h : e + 1 = 2 ^ v' * u') (h₂ : e + 1 = 2 ^ v₂' * u₂') :
    v' = v₂' :=
  Val2.unique ⟨u', hu', h⟩ ⟨u₂', hu₂', h₂⟩

/-- Uniqueness of the next odd cofactor. -/
theorem next_u_unique {e v' u' u₂' : Nat}
    (hu' : u' % 2 = 1) (hu₂' : u₂' % 2 = 1)
    (h : e + 1 = 2 ^ v' * u') (h₂ : e + 1 = 2 ^ v' * u₂') :
    u' = u₂' :=
  Val2.cofactor_unique hu' hu₂' h h₂


/-! ## 2.  Exact identities -/

/-- `3 ^ v * u + 2 ^ W − 1` is exactly `2 ^ W` times the next odd-plus-one. -/
theorem peak_plus_eq {n v u W e : Nat} (h : IsExcursion n v u W e) :
    3 ^ v * u + 2 ^ W - 1 = 2 ^ W * (e + 1) := by
  have hpeak : 3 ^ v * u = 2 ^ W * e + 1 := h.2.2.2.2.2.2
  rw [hpeak]
  have hswap : 2 ^ W * e + 1 + 2 ^ W = 2 ^ W * e + 2 ^ W + 1 := by
    rw [Nat.add_assoc, Nat.add_comm 1, Nat.add_assoc]
  rw [hswap, Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one]

/-- **The next-odd formula.**  Dual of `ExcursionAdversary.landing_div`. -/
theorem landing_succ_div {n v u W e : Nat} (h : IsExcursion n v u W e) :
    e + 1 = (3 ^ v * u + 2 ^ W - 1) / 2 ^ W := by
  have heq := peak_plus_eq h
  rw [heq]
  exact (Nat.mul_div_cancel_left (e + 1) (two_pow_pos W)).symm

/-- **Exact identity for the next cofactor.**  From `3 ^ v u = 2 ^ W e + 1`
and `e + 1 = 2 ^{v'} u'`,

  `3 ^ v u + 2 ^ W − 1 = 2 ^{W + v'} u'`. -/
theorem next_cofactor_identity {n v u W e v' u' : Nat}
    (h : IsExcursion n v u W e) (hnext : e + 1 = 2 ^ v' * u') :
    3 ^ v * u + 2 ^ W - 1 = 2 ^ (W + v') * u' := by
  have hsum := peak_plus_eq h
  rw [hsum, hnext, Nat.pow_add, Nat.mul_assoc]

/-- The same identity, packaged on two successive excursions. -/
theorem next_cofactor_of_excursions {n v u W e v' u' W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e') :
    3 ^ v * u + 2 ^ W - 1 = 2 ^ (W + v') * u' :=
  next_cofactor_identity h h'.2.2.2.2.2.1

/-- **`u'` as a `Nat.div`.**  This is the closed form in `(v, W, u, v')`. -/
theorem next_cofactor_div {n v u W e v' u' : Nat}
    (h : IsExcursion n v u W e) (hnext : e + 1 = 2 ^ v' * u') :
    u' = (3 ^ v * u + 2 ^ W - 1) / 2 ^ (W + v') := by
  have hid := next_cofactor_identity h hnext
  rw [hid]
  exact (Nat.mul_div_cancel_left u' (two_pow_pos (W + v'))).symm

/-- The identity as a valuation: `v₂(3 ^ v u + 2 ^ W − 1) = W + v'`, with
odd cofactor `u'`. -/
theorem val2_peak_plus {n v u W e v' u' : Nat}
    (h : IsExcursion n v u W e) (hu' : u' % 2 = 1)
    (hnext : e + 1 = 2 ^ v' * u') :
    Val2 (3 ^ v * u + 2 ^ W - 1) (W + v') :=
  ⟨u', hu', next_cofactor_identity h hnext⟩


/-! ## 3.  Comparison identities (no residues) -/

/-- `u'` versus `u` is the identity read as an inequality. -/
theorem cofactor_lt_iff {n v u W e v' u' : Nat}
    (h : IsExcursion n v u W e) (hnext : e + 1 = 2 ^ v' * u') :
    u' < u ↔ 3 ^ v * u + 2 ^ W - 1 < 2 ^ (W + v') * u := by
  have hid := next_cofactor_identity h hnext
  constructor
  · intro hlt
    have hmul : 2 ^ (W + v') * u' < 2 ^ (W + v') * u :=
      Nat.mul_lt_mul_of_pos_left hlt (two_pow_pos (W + v'))
    rwa [← hid] at hmul
  · intro hcmp
    have hmul : 2 ^ (W + v') * u' < 2 ^ (W + v') * u := by rwa [← hid]
    exact Nat.lt_of_mul_lt_mul_left hmul

private theorem add_pred_lt_iff {x y k : Nat} (hk : 0 < k) :
    x + k - 1 < y ↔ k - 1 < y - x := by
  omega

private theorem mul_gap_eq (a b c : Nat) :
    b * (c - a) = c * b - a * b := by
  rw [Nat.mul_sub, Nat.mul_comm b c, Nat.mul_comm b a]

/-- **Rearranged comparison.**  The factor `2 ^{W + v'} − 3 ^ v` is in `Nat`,
so the right-hand side is `0` precisely when the total exponent is light. -/
theorem cofactor_lt_iff_gap {n v u W e v' u' : Nat}
    (h : IsExcursion n v u W e) (hnext : e + 1 = 2 ^ v' * u') :
    u' < u ↔ 2 ^ W - 1 < u * (2 ^ (W + v') - 3 ^ v) := by
  have hiff := cofactor_lt_iff h hnext
  rw [hiff]
  have hx :
      3 ^ v * u + 2 ^ W - 1 < 2 ^ (W + v') * u ↔
        2 ^ W - 1 < 2 ^ (W + v') * u - 3 ^ v * u :=
    add_pred_lt_iff (two_pow_pos W)
  rw [hx, mul_gap_eq (3 ^ v) u (2 ^ (W + v'))]

/-- **Light total exponent forces growth of `u`.**  If `2 ^{W + v'} ≤ 3 ^ v`
then the rearranged gap is zero and `u < u'`. -/
theorem cofactor_grows_of_light {n v u W e v' u' : Nat}
    (h : IsExcursion n v u W e) (hnext : e + 1 = 2 ^ v' * u')
    (hlight : 2 ^ (W + v') ≤ 3 ^ v) : u < u' := by
  have hid := next_cofactor_identity h hnext
  have hle : 2 ^ (W + v') * u ≤ 3 ^ v * u := Nat.mul_le_mul_right u hlight
  have hW : 0 < W := h.2.2.2.2.1
  have hrew : 3 ^ v * u + 2 ^ W - 1 = 3 ^ v * u + (2 ^ W - 1) :=
    Nat.add_sub_assoc (one_le_two_pow W) (3 ^ v * u)
  have hgap : 0 < 2 ^ W - 1 := by
    have : 2 ≤ 2 ^ W := two_le_two_pow hW
    omega
  have hlt : 3 ^ v * u < 3 ^ v * u + 2 ^ W - 1 := by
    rw [hrew]
    exact Nat.lt_add_of_pos_right hgap
  have hlt' : 3 ^ v * u < 2 ^ (W + v') * u' := by rwa [hid] at hlt
  have hchain : 2 ^ (W + v') * u < 2 ^ (W + v') * u' :=
    Nat.lt_of_le_of_lt hle hlt'
  exact Nat.lt_of_mul_lt_mul_left hchain

/-- The complementary direction of `cofactor_lt_iff`. -/
theorem cofactor_gt_iff {n v u W e v' u' : Nat}
    (h : IsExcursion n v u W e) (hnext : e + 1 = 2 ^ v' * u') :
    u < u' ↔ 2 ^ (W + v') * u < 3 ^ v * u + 2 ^ W - 1 := by
  have hid := next_cofactor_identity h hnext
  constructor
  · intro hlt
    have hmul : 2 ^ (W + v') * u < 2 ^ (W + v') * u' :=
      Nat.mul_lt_mul_of_pos_left hlt (two_pow_pos (W + v'))
    rwa [← hid] at hmul
  · intro hcmp
    have hmul : 2 ^ (W + v') * u < 2 ^ (W + v') * u' := by rwa [← hid]
    exact Nat.lt_of_mul_lt_mul_left hmul


/-! ## 4.  Mersenne landings are `u' = 1` -/

/-- **Crash to Mersenne.**  The next cofactor is `1` if and only if
`3 ^ v u + 2 ^ W − 1` is a pure power of two. -/
theorem next_mersenne_iff {n v u W e v' u' : Nat}
    (h : IsExcursion n v u W e) (hnext : e + 1 = 2 ^ v' * u') :
    u' = 1 ↔ 3 ^ v * u + 2 ^ W - 1 = 2 ^ (W + v') := by
  have hid := next_cofactor_identity h hnext
  constructor
  · intro h1
    rw [h1, Nat.mul_one] at hid
    exact hid
  · intro hp
    have : 2 ^ (W + v') * u' = 2 ^ (W + v') * 1 := by
      rw [← hid, hp, Nat.mul_one]
    exact Nat.eq_of_mul_eq_mul_left (two_pow_pos (W + v')) this

/-- The landing itself is then the Mersenne number `2 ^{v'} − 1`. -/
theorem landing_eq_mersenne {n v u W e v' u' : Nat}
    (_h : IsExcursion n v u W e) (hnext : e + 1 = 2 ^ v' * u')
    (h1 : u' = 1) : e = 2 ^ v' - 1 := by
  rw [h1, Nat.mul_one] at hnext
  omega


/-! ## 5.  Two witnesses -/

/-- `7`: `v = 3`, `u = 1`, `W = 1`, landing `13`. -/
theorem seven_is_excursion : IsExcursion 7 3 1 1 13 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

/-- The next state of `7` is `(v', u') = (1, 7)`. -/
theorem thirteen_is_excursion : IsExcursion 13 1 7 2 5 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

/-- `27`: `v = 2`, `u = 7`, `W = 1`, landing `31`. -/
theorem twenty_seven_is_excursion : IsExcursion 27 2 7 1 31 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

/-- The next state of `27` is `(v', u') = (5, 1)` — a Mersenne landing. -/
theorem thirty_one_is_excursion : IsExcursion 31 5 1 1 121 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

/-- **Growth witness.**  `u = 1` at `7` becomes `u' = 7` at `13`. -/
theorem u_grows_at_seven :
    IsExcursion 7 3 1 1 13 ∧ 13 + 1 = 2 ^ 1 * 7 ∧ 1 < 7 :=
  ⟨seven_is_excursion, rfl, by omega⟩

/-- **Crash witness.**  `u = 7` at `27` becomes `u' = 1` at `31`. -/
theorem u_drops_at_twenty_seven :
    IsExcursion 27 2 7 1 31 ∧ 31 + 1 = 2 ^ 5 * 1 ∧ 1 < 7 ∧
      31 = 2 ^ 5 - 1 :=
  ⟨twenty_seven_is_excursion, rfl, by omega, rfl⟩

/-- The identity at the growth witness: `3^3 · 1 + 2^1 − 1 = 2^{1+1} · 7`. -/
theorem seven_identity :
    3 ^ 3 * 1 + 2 ^ 1 - 1 = 2 ^ (1 + 1) * 7 :=
  next_cofactor_identity seven_is_excursion rfl

/-- The identity at the crash witness: `3^2 · 7 + 2^1 − 1 = 2^{1+5} · 1`. -/
theorem twenty_seven_identity :
    3 ^ 2 * 7 + 2 ^ 1 - 1 = 2 ^ (1 + 5) * 1 :=
  next_cofactor_identity twenty_seven_is_excursion rfl


/-! ## 6.  No monotone energy -/

/-- A ranking on the excursion state `(v, u)` would strictly decrease along
every excursion of an odd start `> 1`. -/
def DecreasesAlong (Φ : Nat → Nat → Nat) : Prop :=
  ∀ n v u W e v' u' W' e' : Nat,
    1 < n →
    IsExcursion n v u W e →
    IsExcursion e v' u' W' e' →
    Φ v' u' < Φ v u

/-- **No energy depending on `u` alone is a ranking.**  The pair `7 ↦ 13`
(`u : 1 → 7`) and `27 ↦ 31` (`u : 7 → 1`) is a 2-cycle on cofactors. -/
theorem no_u_energy (f : Nat → Nat) :
    ¬ DecreasesAlong (fun _ u => f u) := by
  intro hf
  have h17 :=
    hf 7 3 1 1 13 1 7 2 5 (by omega) seven_is_excursion thirteen_is_excursion
  have h71 :=
    hf 27 2 7 1 31 5 1 1 121 (by omega)
      twenty_seven_is_excursion thirty_one_is_excursion
  change f 7 < f 1 at h17
  change f 1 < f 7 at h71
  omega

/-- In particular `u` itself is not a ranking. -/
theorem not_u_ranking : ¬ DecreasesAlong (fun _ u => u) :=
  no_u_energy id

/-- Lexicographic `(v, u)` (valuation first) is not a ranking: at `27` the
run length grows `2 → 5`. -/
theorem not_lex_vu :
    ¬ (∀ n v u W e v' u' W' e' : Nat,
        1 < n →
        IsExcursion n v u W e →
        IsExcursion e v' u' W' e' →
        v' < v ∨ (v' = v ∧ u' < u)) := by
  intro h
  have :=
    h 27 2 7 1 31 5 1 1 121 (by omega)
      twenty_seven_is_excursion thirty_one_is_excursion
  omega

/-- Lexicographic `(u, v)` (cofactor first) is not a ranking: at `7` the
cofactor grows `1 → 7`. -/
theorem not_lex_uv :
    ¬ (∀ n v u W e v' u' W' e' : Nat,
        1 < n →
        IsExcursion n v u W e →
        IsExcursion e v' u' W' e' →
        u' < u ∨ (u' = u ∧ v' < v)) := by
  intro h
  have :=
    h 7 3 1 1 13 1 7 2 5 (by omega) seven_is_excursion thirteen_is_excursion
  omega

/-- The peak energy `3 ^ v * u` is not a ranking: it grows at `27`
(`63 → 243`). -/
theorem not_peak_ranking : ¬ DecreasesAlong (fun v u => 3 ^ v * u) := by
  intro hf
  have hlt :=
    hf 27 2 7 1 31 5 1 1 121 (by omega)
      twenty_seven_is_excursion thirty_one_is_excursion
  have : ¬ (3 ^ 5 * 1 < 3 ^ 2 * 7) := by decide
  exact this hlt

/-- Strict decrease of the scaled cofactor `u * 3 ^{-v}`, written without
rationals as `u' * 3 ^ v < u * 3 ^{v'}`. -/
def ScaledDecrease (v u v' u' : Nat) : Prop :=
  u' * 3 ^ v < u * 3 ^ v'

/-- `u * 3 ^{-v}` is not a ranking: it grows at `7` (`1/27 → 7/3`). -/
theorem not_scaled_ranking :
    ¬ (∀ n v u W e v' u' W' e' : Nat,
        1 < n →
        IsExcursion n v u W e →
        IsExcursion e v' u' W' e' →
        ScaledDecrease v u v' u') := by
  intro h
  have hlt :=
    h 7 3 1 1 13 1 7 2 5 (by omega) seven_is_excursion thirteen_is_excursion
  have : ¬ ScaledDecrease 3 1 1 7 := by
    unfold ScaledDecrease
    decide
  exact this hlt

/-- The same scale with `W` in place of `v` also grows at `7`
(`1/3 → 7/9`). -/
theorem not_scaled_W_ranking :
    ¬ (∀ n v u W e v' u' W' e' : Nat,
        1 < n →
        IsExcursion n v u W e →
        IsExcursion e v' u' W' e' →
        u' * 3 ^ W < u * 3 ^ W') := by
  intro h
  have hlt :=
    h 7 3 1 1 13 1 7 2 5 (by omega) seven_is_excursion thirteen_is_excursion
  have : ¬ (7 * 3 ^ 1 < 1 * 3 ^ 2) := by decide
  exact this hlt

end ExcursionCofactor
end Collatz
