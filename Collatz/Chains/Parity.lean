import Collatz.Chains.Modular
import Collatz.Strategy.Terras

/-!
# Chains 25–30: uniformity, and where it breaks

The chains here all ask for something *uniform* — one level of the sieve, one
time budget, one modulus — and four of the six are **refuted**.  The refutations
are the useful part: each one closes off a direction permanently, and three of
them are consequences of the obstruction theorem, which is what that theorem is
for.

| chain | hypothesis                                           | status    |
|-------|------------------------------------------------------|-----------|
| 25    | one sieve level clears every large number            | **false** |
| 26    | some level has no heavy residues                     | **false** |
| 27    | a uniform time budget for subcritical density        | **false** |
| 28    | doubling the verified range preserves it             | open      |
| 29    | one level where every class descends from `m = 1`    | **false** |
| 30    | the surviving classes mod `1024` drop                | open      |

The pattern is worth naming.  Every uniform hypothesis dies against the class
`−1 mod 2^k`, which takes `k` consecutive odd steps and so defeats any fixed
budget.  The two chains that survive are exactly the two that let their
parameter depend on `n`.
-/

namespace Collatz
namespace Chains

open Reach Strategy Congruence Density

/-! ## Chain 25 — one sieve level for everything -/

/-- Hypothesis: some fixed level of the sieve settles every large number. -/
def H25_singleLevel : Prop :=
  ∃ K : Nat, ∀ n : Nat, 10000 < n → survives K (n % 2 ^ K) = false

/-- **Chain 25 is refuted.**  Every level retains a surviving class, and that
class has arbitrarily large members. -/
theorem chain25_refuted : ¬ H25_singleLevel := by
  intro ⟨K, hK⟩
  obtain ⟨r, hr, hs⟩ := Obstruction.sieve_never_clears K
  have hpow : 0 < 2 ^ K := Arith.two_pow_pos K
  -- a large member of the surviving class
  refine absurd (hK (2 ^ K * 10001 + r) ?_) ?_
  · have : 10001 ≤ 2 ^ K * 10001 := Nat.le_mul_of_pos_left _ hpow
    omega
  · have hmod : (2 ^ K * 10001 + r) % 2 ^ K = r := by
      rw [Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hr
    rw [hmod, hs]
    simp

/-! ## Chain 26 — a level with no heavy residues -/

/-- Hypothesis: at some level no residue is heavy. -/
def H26_noHeavy : Prop := ∃ k : Nat, 0 < k ∧ heavyCount k = 0

/-- **Chain 26 is refuted.**  The residue `2 ^ k − 1` is heavy at every
level. -/
theorem chain26_refuted : ¬ H26_noHeavy := by
  intro ⟨k, hk, h0⟩
  have := heavyCount_pos hk
  omega

/-! ## Chain 27 — a uniform time budget -/

/-- The odd-step count of `2 ^ (K+1) − 1` is maximal at every time up to
`K + 1`: every one of the first `K + 1` steps is an odd step. -/
theorem oddCount_pow_two_sub_one_le {K k : Nat} (hkK : k ≤ K) :
    oddCount (2 ^ K - 1) k = k := by
  rw [Density.oddCount_mod, Obstruction.two_pow_sub_one_mod hkK]
  exact Obstruction.oddCount_two_pow_sub_one k

/-- Hypothesis: one time budget `K` works for every `n`. -/
def H27_uniformTime (K : Nat) : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat, 1 ≤ k ∧ k ≤ K ∧ 5 * oddCount n k < 3 * k

/-- **Chain 27 is refuted, for every budget.**  The number `2 ^ (K+1) − 1` takes
`K + 1` consecutive odd steps, so its density never dips inside the budget. -/
theorem chain27_refuted (K : Nat) : ¬ H27_uniformTime K := by
  intro h
  have hfour : (4:Nat) ≤ 2 ^ (K + 2) := by
    have h1 : (2:Nat) ^ 2 ≤ 2 ^ (K + 2) := Arith.two_pow_le_two_pow (by omega)
    simpa using h1
  obtain ⟨k, hk1, hkle, hlt⟩ := h (2 ^ (K + 2) - 1) (by omega)
  have hcount : oddCount (2 ^ (K + 2) - 1) k = k :=
    oddCount_pow_two_sub_one_le (by omega)
  rw [hcount] at hlt
  omega

/-! ## Chain 28 — doubling the verified range -/

/-- Hypothesis: verifying `[1, N]` verifies `[1, 2N]`. -/
def H28_doubling : Prop :=
  ∀ N : Nat, 10000 ≤ N → (∀ m : Nat, 0 < m → m ≤ N → ReachesOne m) →
    ∀ m : Nat, 0 < m → m ≤ 2 * N → ReachesOne m

/-- **Chain 28.**  A doubling step implies Collatz, by induction from the
verified base. -/
theorem chain28 (h : H28_doubling) : CollatzConjecture := by
  -- every dyadic multiple of the verified range is verified
  have key : ∀ j : Nat, ∀ m : Nat, 0 < m → m ≤ 10000 * 2 ^ j → ReachesOne m := by
    intro j
    induction j with
    | zero =>
      intro m hm hle
      exact Search.reachesOne_of_le_10000 hm (by simpa using hle)
    | succ j ih =>
      intro m hm hle
      have hN : 10000 ≤ 10000 * 2 ^ j := Nat.le_mul_of_pos_right _ (Arith.two_pow_pos j)
      have hdouble := h (10000 * 2 ^ j) hN ih m hm
      refine hdouble ?_
      have hexp : 10000 * 2 ^ (j + 1) = 2 * (10000 * 2 ^ j) := by
        rw [Arith.two_pow_succ, Nat.mul_left_comm]
      omega
  intro n hn
  refine key n n hn ?_
  have h1 : n < 2 ^ n := Arith.lt_two_pow_self n
  have h2 : (1:Nat) * 2 ^ n ≤ 10000 * 2 ^ n :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## Chain 29 — one level where every class descends -/

/-- Hypothesis: at some level every residue class descends from the very first
multiple. -/
def H29_uniformClassDescent : Prop :=
  ∃ k : Nat, 0 < k ∧ ∀ r : Nat, r < 2 ^ k → ∀ m : Nat, 1 ≤ m →
    acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r

/-- **Chain 29 is refuted.**  Take the class `−1 mod 2 ^ k`, whose multiplier is
`3 ^ k`, and take `m = 2 ^ k`: the class grows instead of dropping. -/
theorem chain29_refuted : ¬ H29_uniformClassDescent := by
  intro ⟨k, hk, h⟩
  have hpow : 0 < 2 ^ k := Arith.two_pow_pos k
  have hr : 2 ^ k - 1 < 2 ^ k := by omega
  have hlt := h (2 ^ k - 1) hr (2 ^ k) (by omega)
  -- the affine form of the class
  have hform := accOrbit_pow_two_mul_add k (2 ^ k) (2 ^ k - 1)
  rw [Obstruction.oddCount_two_pow_sub_one k] at hform
  rw [hform] at hlt
  -- `3 ^ k ≥ 2 ^ k + 1`, so `3 ^ k · 2 ^ k ≥ 2 ^ k · 2 ^ k + 2 ^ k`
  have hgt : 2 ^ k + 1 ≤ 3 ^ k := by
    have := Obstruction.two_pow_lt_three_pow hk
    omega
  have hmul : (2 ^ k + 1) * 2 ^ k ≤ 3 ^ k * 2 ^ k := Nat.mul_le_mul_right _ hgt
  have hexp : (2 ^ k + 1) * 2 ^ k = 2 ^ k * 2 ^ k + 2 ^ k := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hexp] at hmul
  omega

/-! ## Chain 30 — the sharpest surviving statement -/

/-- **Chain 30.**  Of everything above, this is the strongest chain that is not
refuted and not a bare restatement: the drop property for the sixty-four residue
classes modulo `1024` that survive the sieve. -/
theorem chain30 (h : H22_survivorsMod1024) : CollatzConjecture := chain22 h

/-! ## Summary -/

/-- The four refuted uniform hypotheses, collected.  Each fails for the same
reason: the class `−1 mod 2 ^ k` defeats any fixed budget. -/
theorem refuted_chains :
    (¬ H25_singleLevel) ∧ (¬ H26_noHeavy) ∧ (∀ K : Nat, ¬ H27_uniformTime K) ∧
      (¬ H29_uniformClassDescent) ∧ (¬ H17_quadraticExcursion) ∧ (¬ H18_linearTime) :=
  ⟨chain25_refuted, chain26_refuted, chain27_refuted, chain29_refuted,
    chain17_quadratic_refuted, chain18_linear_refuted⟩

end Chains
end Collatz
