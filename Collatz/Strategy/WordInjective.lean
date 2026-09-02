import Collatz.Strategy.GapBarriers
import Collatz.Strategy.AccumulatorCap

/-!
# The valuation word determines the integer

`CLOSURE.md`'s track C asks for an infinite-path statement that does **not**
follow from prefix reachability, since `GapBarriers.exists_realizer` proves every
finite valuation word is realized and so every prefix-consuming argument is dead
on arrival.

The natural candidate is **isolation**: the infinite admissible valuation words
form an inverse limit (a Cantor set of `2`-adic integers), and one asks that no
positive integer sit at a divergent point of it.  It passes three of the four
membership tests — it rests on no orbit lower bound, it does not reduce to the
factors of `∏(1 + 1/(3x_t))`, and it is a statement about the limit rather than
about any prefix, so `exists_realizer` does not settle it.

**It is nevertheless dead, and this file says exactly why.**  The obstruction is
not a class membership but a circularity, in the sense of `CLOSURE.md`'s
diagnostic 5: the quantifier swap that separates track C from prefix
reachability — `∀L ∃n` versus `∃n ∀L` — has no content, because the `n` in the
second is *unique*.  `word_injective` below: two odd positive integers with the
same infinite valuation word are equal.  So an integer realizing every prefix of
a word is not a new object to be excluded; it is the integer whose word that is.
Asking whether a divergent word has an integer realizer is asking whether some
integer diverges — the divergence half verbatim, in `2`-adic coordinates.

**What this does and does not close.**  It closes the *coordinate change*: moving
to the inverse limit and asking for isolation buys nothing, because the map back
is injective.  It does **not** close every limit-object argument — an argument
that used a genuine property of the limit (a measure, a dimension, a transcendence
input) would not be refuted by injectivity alone.  What is refuted is the specific
hope that the `∃n ∀L` form is a *weaker* target than divergence itself.

## The proof

Purely `2`-adic, and it is short because the repository already has the two
inputs.  If `n` and `n'` share a word, `traj_affine_exact` gives

    2 ^ K_L · A = 3 ^ L · n  + S,      2 ^ K_L · B = 3 ^ L · n' + S

with the **same** `K_L` and `S` — they are functions of the word alone.  Hence
`3 ^ L · (n' − n) = 2 ^ K_L · (B − A)`, so `2 ^ K_L ∣ 3 ^ L · (n' − n)`, and
`AccumulatorCap.dvd_cancel_three_pow` strips the `3 ^ L` because `2 ^ K_L` is not
divisible by `3`.  Then `Ksum_ge` gives `K_L ≥ L`, and taking `L = n' + 1` makes
`2 ^ K_L` exceed `n' − n`, forcing the difference to `0`.

No `Mathlib`, no `sorry`, no axiom; the only external facts are core `Nat`
lemmas.
-/

namespace Collatz
namespace WordInjective

open GapBarriers

/-- `m < 2 ^ m`.  Core has no `Nat.lt_two_pow` in this toolchain. -/
private theorem lt_two_pow : ∀ m : Nat, m < 2 ^ m
  | 0 => by decide
  | m + 1 => by
      have ih := lt_two_pow m
      have hp : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by
        rw [Nat.pow_succ]; omega
      omega

/-- The one-sided step: if `n ≤ n'` and the two agree on the first `n' + 1`
valuations, then `n' ≤ n`.  The whole `2`-adic argument lives here, and it needs
the words to agree only on a **bounded** prefix — `Traj` quantifies below `L`, so
no `funext` and no infinite hypothesis enters. -/
private theorem ge_of_word_eq {n n' : Nat} (hn : n % 2 = 1) (hn' : n' % 2 = 1)
    (h : ∀ i : Nat, i < n' + 1 → oddK (oddOrbit i n) = oddK (oddOrbit i n'))
    (hle : n ≤ n') : n' ≤ n := by
  have ht : Traj (fun i => oddOrbit i n) (fun i => oddK (oddOrbit i n)) (n' + 1) :=
    exists_traj hn (n' + 1)
  have ht' : Traj (fun i => oddOrbit i n') (fun i => oddK (oddOrbit i n)) (n' + 1) := by
    intro i hi
    have h0 := exists_traj hn' (n' + 1) i hi
    show OddStep (oddOrbit i n') (oddK (oddOrbit i n)) (oddOrbit (i + 1) n')
    rw [h i hi]
    exact h0
  have e1 := traj_affine_exact (n' + 1) ht
  have e2 := traj_affine_exact (n' + 1) ht'
  simp only [oddOrbit_zero] at e1 e2
  have hQpos : 0 < 2 ^ Ksum (fun i => oddK (oddOrbit i n)) (n' + 1) :=
    Nat.two_pow_pos _
  have hmulle : 3 ^ (n' + 1) * n ≤ 3 ^ (n' + 1) * n' :=
    Nat.mul_le_mul_left _ hle
  have hABle : oddOrbit (n' + 1) n ≤ oddOrbit (n' + 1) n' := by
    refine Nat.le_of_mul_le_mul_left ?_ hQpos
    omega
  have key : 3 ^ (n' + 1) * (n' - n)
      = 2 ^ Ksum (fun i => oddK (oddOrbit i n)) (n' + 1)
        * (oddOrbit (n' + 1) n' - oddOrbit (n' + 1) n) := by
    rw [Nat.mul_sub, Nat.mul_sub]
    omega
  have hdvd : 2 ^ Ksum (fun i => oddK (oddOrbit i n)) (n' + 1)
      ∣ 3 ^ (n' + 1) * (n' - n) :=
    ⟨oddOrbit (n' + 1) n' - oddOrbit (n' + 1) n, key⟩
  have hmod : 2 ^ Ksum (fun i => oddK (oddOrbit i n)) (n' + 1) % 3 ≠ 0 := by
    have := two_pow_mod_three_ne (Ksum (fun i => oddK (oddOrbit i n)) (n' + 1))
    omega
  have hcancel : 2 ^ Ksum (fun i => oddK (oddOrbit i n)) (n' + 1) ∣ (n' - n) :=
    AccumulatorCap.dvd_cancel_three_pow hmod (n' + 1) (n' - n) hdvd
  have hKge : n' + 1 ≤ Ksum (fun i => oddK (oddOrbit i n)) (n' + 1) :=
    Ksum_ge (n' + 1) (fun i hi => (ht i hi).1)
  have hpow : 2 ^ (n' + 1) ≤ 2 ^ Ksum (fun i => oddK (oddOrbit i n)) (n' + 1) :=
    Nat.pow_le_pow_right (by decide) hKge
  have hsmall : n' - n < 2 ^ Ksum (fun i => oddK (oddOrbit i n)) (n' + 1) := by
    have := lt_two_pow (n' + 1)
    omega
  have := Nat.eq_zero_of_dvd_of_lt hcancel hsmall
  omega

/-- **The bounded form, which is the sharp one.**  If `n ≤ n'` and the two odd
integers agree on their first `n' + 1` valuations, they are equal.  The modulus
is explicit and linear: no limit is needed.  This is the precise sense in which
track C's `∃n ∀L` statement is not weaker than divergence — it is already decided
by a bounded prefix. -/
theorem word_injective_bounded {n n' : Nat} (hn : n % 2 = 1) (hn' : n' % 2 = 1)
    (hle : n ≤ n')
    (h : ∀ i : Nat, i < n' + 1 → oddK (oddOrbit i n) = oddK (oddOrbit i n')) :
    n = n' :=
  Nat.le_antisymm hle (ge_of_word_eq hn hn' h hle)

/-- **The valuation word determines the integer.**  Two odd positive integers
whose odd-map valuation sequences agree at every index are equal.

Consequently the `∃n ∀L` form of track C — an integer realizing every prefix of
an infinite admissible word — names a unique integer, and is therefore not a
weaker target than divergence itself.  See the module docstring. -/
theorem word_injective {n n' : Nat} (hn : n % 2 = 1) (hn' : n' % 2 = 1)
    (h : ∀ i : Nat, oddK (oddOrbit i n) = oddK (oddOrbit i n')) : n = n' := by
  rcases Nat.le_total n n' with hle | hle
  · exact word_injective_bounded hn hn' hle (fun i _ => h i)
  · exact (word_injective_bounded hn' hn hle (fun i _ => (h i).symm)).symm

end WordInjective
end Collatz
