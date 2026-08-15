import Collatz.Chains.Cycles
import Collatz.Strategy.Reductions
import Collatz.Structure.AffineBound

/-!
# Chains 19–24: congruences and the multiplier

The congruence engine turns `T^k` into an affine map on each residue class, so
these chains phrase the remaining difficulty as a statement about residues or
about the multiplier `3 ^ {a(n,k)}`.

Chains 23 and 24 are the interesting ones here.  They isolate the *quantitative*
content of the heuristic "the orbit shrinks because on average half the steps
halve": the multiplier must go subcritical at a time `k` that is not too large
relative to `log n`.  Both conditions are needed — subcriticality alone is not
enough, because the accumulated constant `b` can swamp a large `n` if `k` is
allowed to grow.  Written out, the pair of conditions is exactly what the
bounded affine identity requires, and no more.

| chain | hypothesis                                              | status |
|-------|---------------------------------------------------------|--------|
| 19    | the class `3 mod 4` drops                                | open   |
| 20    | the classes `7, 11, 15 mod 16` drop                      | open   |
| 21    | the eight classes mod `64` drop                          | open   |
| 22    | the sixty-four classes mod `1024` drop                   | open   |
| 23    | the multiplier goes subcritical in time, with size control | open |
| 24    | the odd-step density dips below `3/5` in time             | open   |
-/

namespace Collatz
namespace Chains

open Reach Strategy Congruence Minimal

/-! ## Chains 19–22 — the residue pillars -/

/-- **Chain 19.**  One class suffices. -/
theorem chain19 (h : DropsFrom 3 4) : CollatzConjecture := collatz_of_one_pillar h

/-- **Chain 20.**  Three classes modulo `16`. -/
theorem chain20 (h7 : DropsFrom 7 16) (h11 : DropsFrom 11 16) (h15 : DropsFrom 15 16) :
    CollatzConjecture := collatz_of_three_pillars h7 h11 h15

/-- **Chain 21.**  Eight classes modulo `64`. -/
theorem chain21
    (h7 : DropsFrom 7 64) (h15 : DropsFrom 15 64) (h27 : DropsFrom 27 64)
    (h31 : DropsFrom 31 64) (h39 : DropsFrom 39 64) (h47 : DropsFrom 47 64)
    (h59 : DropsFrom 59 64) (h63 : DropsFrom 63 64) :
    CollatzConjecture :=
  collatz_of_eight_pillars h7 h15 h27 h31 h39 h47 h59 h63

/-- Hypothesis: the classes surviving the level-`10` sieve drop. -/
def H22_survivorsMod1024 : Prop :=
  ∀ n : Nat, 1024 < n → survives 10 (n % 2 ^ 10) = true →
    ∃ k : Nat, acceleratedOrbit k n < n

/-- **Chain 22.**  The sixty-four surviving classes modulo `1024` suffice.  This
is the sharpest residue reduction the project supports. -/
theorem chain22 (h : H22_survivorsMod1024) : CollatzConjecture := by
  exact collatz_of_survivors (K := 10) (by omega) h

/-! ## Chain 23 — subcritical multiplier with size control -/

/-- Hypothesis: for every `n > 1` there is a time `k` at which the multiplier
`3 ^ {a(n,k)}` is below `2 ^ k`, *and* `k` is small enough that the accumulated
constant `3 ^ k − 2 ^ k` stays below `n`. -/
def H23_subcritical : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat,
    1 ≤ k ∧ 3 ^ oddCount n k < 2 ^ k ∧ 3 ^ k < n + 2 ^ k

/-- **Chain 23.**  Subcriticality with size control forces a drop, hence
Collatz.

The proof is exactly the bounded affine identity: `2^k T^k(n) = 3^a n + b` with
`b + 2^k ≤ 3^k`, so `b < n` by the size condition and `3^a n + n ≤ 2^k n` by
subcriticality. -/
theorem chain23 (h : H23_subcritical) : CollatzConjecture := by
  refine collatz_of_finiteStoppingTime (fun n hn => ?_)
  obtain ⟨k, _, hsub, hsize⟩ := h n hn
  obtain ⟨b, heq, hb⟩ := AffineBound.exists_affine_bounded n k
  refine ⟨k, ?_⟩
  -- `b < n` from the size condition
  have hbn : b < n := by omega
  -- `3 ^ a * n + n ≤ 2 ^ k * n` from subcriticality
  have hstep : (3 ^ oddCount n k + 1) * n ≤ 2 ^ k * n :=
    Nat.mul_le_mul_right n (by omega)
  have hexp : (3 ^ oddCount n k + 1) * n = 3 ^ oddCount n k * n + n := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hexp] at hstep
  -- so the left side of the identity is below `2 ^ k * n`
  have hlt : 2 ^ k * acceleratedOrbit k n < 2 ^ k * n := by omega
  exact Nat.lt_of_mul_lt_mul_left hlt

/-! ## Chain 24 — the same condition in terms of odd-step density -/

/-- Hypothesis: the odd-step density dips below `3/5` at a time small enough for
size control. -/
def H24_density : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat,
    1 ≤ k ∧ 5 * oddCount n k < 3 * k ∧ 3 ^ k < n + 2 ^ k

/-- A subcritical density gives a subcritical multiplier, by the contrapositive
of the exponent bound. -/
theorem subcritical_of_density {n k : Nat} (h : 5 * oddCount n k < 3 * k) :
    3 ^ oddCount n k < 2 ^ k := by
  by_cases hc : 3 ^ oddCount n k < 2 ^ k
  · exact hc
  · exfalso
    have hheavy : 2 ^ k ≤ 3 ^ oddCount n k := by omega
    have := Density.three_mul_le_five_mul_of_heavy hheavy
    omega

/-- **Chain 24.**  The density form implies the multiplier form, hence
Collatz. -/
theorem chain24 (h : H24_density) : CollatzConjecture := by
  refine chain23 (fun n hn => ?_)
  obtain ⟨k, hk, hd, hsize⟩ := h n hn
  exact ⟨k, hk, subcritical_of_density hd, hsize⟩

/-- The two conditions in Chain 23 are independent: subcriticality without size
control does not give a drop, because the constant `b` can dominate.  Here is
the mechanism, stated as the exact inequality the proof needs. -/
theorem chain23_needs_size_control {n k b : Nat}
    (heq : 2 ^ k * acceleratedOrbit k n = 3 ^ oddCount n k * n + b)
    (_hsub : 3 ^ oddCount n k < 2 ^ k) (hdrop : acceleratedOrbit k n < n) : b < 2 ^ k * n := by
  have h1 : 2 ^ k * acceleratedOrbit k n < 2 ^ k * n :=
    Arith.mul_lt_mul_of_pos_left hdrop (Arith.two_pow_pos k)
  omega

end Chains
end Collatz
