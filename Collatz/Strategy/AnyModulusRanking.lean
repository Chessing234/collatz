import Collatz.Strategy.NoFiniteRanking

/-!
# No modulus at all admits a decreasing rank

`NoFiniteRanking.no_class_ranking` rules out ranking functions constant on
classes modulo `2 ^ k · 3 ^ l`.  The restriction to those two primes is an
artefact of how the witness was written: the returning family
`n + 1 = 2 ^ (k+L) · M` works for **every** `M`, and taking `k = 0` and `M = m`
gives, for an arbitrary modulus `m`,

`n = 2 ^ L · m − 1`,  `T^L(n) + 1 = 3 ^ L · m`,

so `m` divides both `n + 1` and `T^L(n) + 1`: the two endpoints are both `−1`
modulo `m`, and `n < T^L(n)`.  The class of `−1` returns to itself, higher up, at
every modulus and every window length.

Three consequences, each closing a hatch that `no_class_ranking` left open:

* `no_ranking_any_modulus` — arbitrary moduli, not just `2 ^ k · 3 ^ l`;
* `no_ranking_general` — the rank may take values in *any* type with an
  irreflexive relation, so ordinal-valued ranks die with the natural-valued
  ones.  The witness gives `φ n = φ (T^L n)` — an equality, not an inequality —
  so nothing about the order structure of the codomain can help;
* the quantitative reading of the witness: it is `2 ^ L · m − 1`, so a rank that
  reads `x mod m` only survives at `x` when `m > (x+1) / 2 ^ L`.  A modulus that
  works must already know `x` to within a factor `2 ^ L`; "increase the precision
  as the orbit grows" is not a way out, because the obstruction is rebuilt at
  every precision.

This is the sharp form of the development's central negative result.
-/

namespace Collatz
namespace AnyModulusRanking

open Reach Congruence NoFiniteRanking

/-! ## The returning witness at an arbitrary modulus -/

/-- **The witness.**  For every modulus `m ≥ 1` and window `L ≥ 1` there is a
positive `n` — namely `2 ^ L · m − 1` — that grows over the window and returns to
its own class modulo `m`. -/
theorem exists_growing_return {m L : Nat} (hm : 0 < m) (hL : 0 < L) :
    ∃ n : Nat, 0 < n ∧ n = 2 ^ L * m - 1 ∧ n < acceleratedOrbit L n ∧
      n % m = acceleratedOrbit L n % m := by
  have h2L : (2:Nat) ≤ 2 ^ L := Arith.two_le_two_pow hL
  have hbig : 2 ≤ 2 ^ L * m := Nat.le_trans h2L (Nat.le_mul_of_pos_right _ hm)
  refine ⟨2 ^ L * m - 1, by omega, rfl, ?_, ?_⟩
  · have hn : (2 ^ L * m - 1) + 1 = 2 ^ (0 + L) * m := by
      rw [Nat.zero_add]; omega
    exact heavy_return_grows hL hm hn
  · have hn : (2 ^ L * m - 1) + 1 = 2 ^ (0 + L) * m := by
      rw [Nat.zero_add]; omega
    have hval := heavy_return_value hn
    rw [Nat.pow_zero, Nat.one_mul] at hval
    have hcomm : m * 2 ^ L = 2 ^ L * m := Nat.mul_comm _ _
    have hdvd1 : m ∣ ((2 ^ L * m - 1) + 1) := ⟨2 ^ L, by omega⟩
    have hdvd2 : m ∣ (acceleratedOrbit L (2 ^ L * m - 1) + 1) := ⟨3 ^ L, by
      rw [hval, Nat.mul_comm]⟩
    rw [pred_mod_of_dvd hm hdvd1, pred_mod_of_dvd hm hdvd2]

/-! ## The impossibility, at every modulus -/

/-- **No rank constant on classes modulo any fixed `m` can decrease.** -/
theorem no_ranking_any_modulus (m L : Nat) (hm : 0 < m) (hL : 0 < L) (φ : Nat → Nat)
    (hclass : ∀ x y : Nat, x % m = y % m → φ x = φ y) :
    ¬ (∀ x : Nat, 0 < x → φ (acceleratedOrbit L x) < φ x) := by
  intro hdec
  obtain ⟨n, hpos, _, _, hcongr⟩ := exists_growing_return hm hL
  have heq : φ (acceleratedOrbit L n) = φ n := hclass _ _ hcongr.symm
  have := hdec n hpos
  omega

/-- **The codomain does not matter either.**  The witness forces an *equality*
of ranks, so no irreflexive relation on any value type — ordinals included — can
be made to decrease along windows by a class function. -/
theorem no_ranking_general {β : Type} (m L : Nat) (hm : 0 < m) (hL : 0 < L)
    (φ : Nat → β) (lt : β → β → Prop) (hirr : ∀ b : β, ¬ lt b b)
    (hclass : ∀ x y : Nat, x % m = y % m → φ x = φ y) :
    ¬ (∀ x : Nat, 0 < x → lt (φ (acceleratedOrbit L x)) (φ x)) := by
  intro hdec
  obtain ⟨n, hpos, _, _, hcongr⟩ := exists_growing_return hm hL
  have heq : φ (acceleratedOrbit L n) = φ n := hclass _ _ hcongr.symm
  have hlt := hdec n hpos
  rw [heq] at hlt
  exact hirr _ hlt

/-- **Even a non-strict rank fails to be informative.**  The same witness shows a
class function cannot be strictly monotone in the other direction either: it is
*constant* on the pair `(n, T^L(n))` while the value strictly grows. -/
theorem class_blind_to_growth (m L : Nat) (hm : 0 < m) (hL : 0 < L) (φ : Nat → Nat)
    (hclass : ∀ x y : Nat, x % m = y % m → φ x = φ y) :
    ∃ n : Nat, 0 < n ∧ n < acceleratedOrbit L n ∧ φ (acceleratedOrbit L n) = φ n := by
  obtain ⟨n, hpos, _, hgrow, hcongr⟩ := exists_growing_return hm hL
  exact ⟨n, hpos, hgrow, hclass _ _ hcongr.symm⟩

end AnyModulusRanking
end Collatz
