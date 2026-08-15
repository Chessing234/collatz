import Collatz.Core.Reach
import Collatz.Core.Arith

/-!
# The congruence engine

This file proves the identity that everything about stopping times rests on:

> `T^k (2^k · m + r) = 3^{a(r,k)} · m + T^k(r)`

where `a(r,k)` is the number of odd steps in the first `k` accelerated steps
starting from `r`.  In words: **on a residue class modulo `2^k`, the `k`-fold
accelerated map is an affine function whose multiplier `3^{a}` is determined by
the residue alone.**

This is the formal content behind Terras' parity-vector analysis: the residue
`r` fixes the whole parity pattern of the first `k` steps, hence fixes the
multiplier, hence fixes whether the class descends.

From the identity we extract a *descent criterion* (`descends_of_residue`): a
residue `r` mod `2^k` whose multiplier satisfies `3^{a(r,k)} < 2^k` forces every
sufficiently large member of the class strictly below its starting point in `k`
steps.  Because the criterion is a Boolean condition on `(k, r)`, individual
residue classes are discharged by `decide`, and each one rules out an entire
congruence class of counterexamples.
-/

namespace Collatz
namespace Congruence

open Reach

/-! ## The odd-step count recurrence -/

/-- The parity vector splits into its head and the vector of the next state. -/
theorem parityVector_cons (n k : Nat) :
    parityVector n (k + 1) = (n % 2) :: parityVector (acceleratedStep n) k := by
  induction k with
  | zero => simp [parityVector]
  | succ k ih =>
    have h1 : parityVector n (k + 2)
        = parityVector n (k + 1) ++ [acceleratedOrbit (k + 1) n % 2] := by
      simp [parityVector, List.range_succ]
    have h2 : parityVector (acceleratedStep n) (k + 1)
        = parityVector (acceleratedStep n) k
            ++ [acceleratedOrbit k (acceleratedStep n) % 2] := by
      simp [parityVector, List.range_succ]
    have h3 : acceleratedOrbit (k + 1) n % 2 = acceleratedOrbit k (acceleratedStep n) % 2 := by
      rfl
    rw [h1, h2, ih, h3]
    simp

/-- The empty odd-step count. -/
@[simp] theorem oddCount_zero (n : Nat) : oddCount n 0 = 0 := by
  simp [oddCount, parityVector]

/-- The odd-step count of an even state ignores the first step. -/
theorem oddCount_succ_of_even {n : Nat} (h : n % 2 = 0) (k : Nat) :
    oddCount n (k + 1) = oddCount (acceleratedStep n) k := by
  rw [oddCount, parityVector_cons, h, oddCount]
  simp

/-- The odd-step count of an odd state counts the first step. -/
theorem oddCount_succ_of_odd {n : Nat} (h : n % 2 = 1) (k : Nat) :
    oddCount n (k + 1) = oddCount (acceleratedStep n) k + 1 := by
  rw [oddCount, parityVector_cons, h, oddCount]
  simp

/-! ## The affine action on a residue class -/

/-- One accelerated step on an even residue class. -/
theorem accStep_pow_two_mul_add_even {k m r : Nat} (hr : r % 2 = 0) :
    acceleratedStep (2 ^ (k + 1) * m + r) = 2 ^ k * m + acceleratedStep r := by
  have hsplit : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
    rw [Arith.two_pow_succ, Nat.mul_assoc]
  have heven : (2 ^ (k + 1) * m + r) % 2 = 0 := by
    rw [hsplit]; omega
  rw [acceleratedStep, if_pos heven, acceleratedStep, if_pos hr, hsplit]
  omega

/-- One accelerated step on an odd residue class, which triples the coefficient. -/
theorem accStep_pow_two_mul_add_odd {k m r : Nat} (hr : r % 2 = 1) :
    acceleratedStep (2 ^ (k + 1) * m + r) = 2 ^ k * (3 * m) + acceleratedStep r := by
  have hsplit : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
    rw [Arith.two_pow_succ, Nat.mul_assoc]
  have hodd : (2 ^ (k + 1) * m + r) % 2 = 1 := by
    rw [hsplit]; omega
  have h3 : 2 ^ k * (3 * m) = 3 * (2 ^ k * m) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (2 ^ k) 3]
  rw [acceleratedStep, if_neg (by omega), acceleratedStep, if_neg (by omega), hsplit, h3]
  omega

/-- **The congruence identity.**  On the residue class of `r` modulo `2 ^ k`, the
`k`-fold accelerated map is the affine map `m ↦ 3 ^ a(r,k) · m + T^k(r)`. -/
theorem accOrbit_pow_two_mul_add (k m r : Nat) :
    acceleratedOrbit k (2 ^ k * m + r) = 3 ^ oddCount r k * m + acceleratedOrbit k r := by
  induction k generalizing m r with
  | zero => simp [acceleratedOrbit]
  | succ k ih =>
    rw [acceleratedOrbit]
    rcases Arith.mod_two_eq_zero_or_one r with hr | hr
    · rw [accStep_pow_two_mul_add_even (k := k) (m := m) hr, ih,
        oddCount_succ_of_even hr, acceleratedOrbit]
    · rw [accStep_pow_two_mul_add_odd (k := k) (m := m) hr, ih,
        oddCount_succ_of_odd hr, acceleratedOrbit]
      have : 3 ^ (oddCount (acceleratedStep r) k + 1) * m
          = 3 ^ oddCount (acceleratedStep r) k * (3 * m) := by
        rw [Arith.three_pow_succ, ← Nat.mul_assoc,
          Nat.mul_comm 3 (3 ^ oddCount (acceleratedStep r) k)]
      rw [this]

/-- The multiplier `3 ^ a(r,k)` depends only on the residue, so the whole class
shares one affine map.  Stated as the difference of two members of the class. -/
theorem accOrbit_class_step (k m r : Nat) :
    acceleratedOrbit k (2 ^ k * (m + 1) + r)
      = acceleratedOrbit k (2 ^ k * m + r) + 3 ^ oddCount r k := by
  rw [accOrbit_pow_two_mul_add, accOrbit_pow_two_mul_add, Nat.mul_add]
  omega

/-! ## The descent criterion -/

/-- `Descends k r` says that the residue `r` modulo `2 ^ k` has a multiplier
small enough to force descent, and does not itself grow in `k` steps. -/
def Descends (k r : Nat) : Prop :=
  3 ^ oddCount r k < 2 ^ k ∧ acceleratedOrbit k r ≤ r

/-- The descent criterion is decidable, so concrete residues are settled by
`decide`. -/
instance (k r : Nat) : Decidable (Descends k r) := by
  unfold Descends
  infer_instance

/-- **Descent on a residue class.**  If the residue `r` descends, then every
member `2 ^ k · m + r` of its class with `m > 0` drops strictly below itself
after `k` accelerated steps. -/
theorem accOrbit_lt_of_descends {k r : Nat} (h : Descends k r) {m : Nat} (hm : 0 < m) :
    acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r := by
  obtain ⟨hmul, hfix⟩ := h
  rw [accOrbit_pow_two_mul_add]
  have hlt : 3 ^ oddCount r k * m < 2 ^ k * m :=
    Nat.mul_lt_mul_of_lt_of_le hmul (Nat.le_refl m) hm
  omega

/-- A number in a descending class, written through its own residue. -/
theorem accOrbit_lt_of_descends_of_mod {k n : Nat}
    (h : Descends k (n % 2 ^ k)) (hn : 2 ^ k ≤ n) :
    acceleratedOrbit k n < n := by
  have hpow : 0 < 2 ^ k := Arith.two_pow_pos k
  have hdecomp : 2 ^ k * (n / 2 ^ k) + n % 2 ^ k = n := by
    have := Nat.div_add_mod n (2 ^ k)
    omega
  have hm : 0 < n / 2 ^ k := Nat.div_pos hn hpow
  have := accOrbit_lt_of_descends (k := k) (r := n % 2 ^ k) h hm
  rw [hdecomp] at this
  exact this

/-! ## A Boolean sieve

Deciding a statement of the form `∀ r < 2 ^ k, …` through instance search does
not scale past small moduli.  The following Boolean reformulation does: the
whole sweep becomes one `List.all`, and a single `decide` closes it. -/

/-- Boolean form of the descent criterion. -/
def descendsB (k r : Nat) : Bool :=
  decide (3 ^ oddCount r k < 2 ^ k) && decide (acceleratedOrbit k r ≤ r)

/-- The Boolean and propositional descent criteria agree. -/
theorem descends_iff_descendsB (k r : Nat) : Descends k r ↔ descendsB k r = true := by
  simp [Descends, descendsB]

/-- `survives j r` says that the residue `r` escapes the descent criterion at
every modulus `2 ^ i` with `i ≤ j`. -/
def survives (j r : Nat) : Bool :=
  (List.range (j + 1)).all (fun i => !descendsB i (r % 2 ^ i))

/-- Surviving at level `j` implies escaping the criterion at each level `i ≤ j`. -/
theorem not_descends_of_survives {j r i : Nat} (h : survives j r = true) (hi : i ≤ j) :
    ¬ Descends i (r % 2 ^ i) := by
  rw [survives, List.all_eq_true] at h
  have hmem : i ∈ List.range (j + 1) := List.mem_range.mpr (by omega)
  have := h i hmem
  rw [descends_iff_descendsB]
  simp at this
  simp [this]

/-- Conversely, escaping the criterion at every level `i ≤ j` is survival. -/
theorem survives_of_not_descends {j r : Nat}
    (h : ∀ i, i ≤ j → ¬ Descends i (r % 2 ^ i)) : survives j r = true := by
  rw [survives, List.all_eq_true]
  intro i hi
  have hij : i ≤ j := by
    have := List.mem_range.mp hi; omega
  have hd : ¬ descendsB i (r % 2 ^ i) = true := by
    rw [← descends_iff_descendsB]
    exact h i hij
  simp [hd]

/-- Failing to survive means descending at some level. -/
theorem exists_descends_of_not_survives {j r : Nat} (h : ¬ survives j r = true) :
    ∃ i : Nat, i ≤ j ∧ Descends i (r % 2 ^ i) := by
  by_cases hc : ∃ i : Nat, i ≤ j ∧ Descends i (r % 2 ^ i)
  · exact hc
  · exact absurd (survives_of_not_descends (fun i hi hd => hc ⟨i, hi, hd⟩)) h

/-- `sieveCheck j allowed` verifies that every residue below `2 ^ j` which
survives the sieve is in the `allowed` list. -/
def sieveCheck (j : Nat) (allowed : List Nat) : Bool :=
  (List.range (2 ^ j)).all (fun r => !(survives j r) || allowed.contains r)

/-- A verified sieve check confines every surviving residue to the allowed
list. -/
theorem mem_allowed_of_sieveCheck {j : Nat} {allowed : List Nat} {r : Nat}
    (h : sieveCheck j allowed = true) (hr : r < 2 ^ j) (hs : survives j r = true) :
    allowed.contains r = true := by
  rw [sieveCheck, List.all_eq_true] at h
  have := h r (List.mem_range.mpr hr)
  rw [hs] at this
  simpa using this

/-! ## Concrete descending residues

Each of the following is a Boolean fact about a single residue, verified by
kernel computation.  Each one removes an entire congruence class from the set
of possible counterexamples. -/

theorem descends_1_0 : Descends 1 0 := by decide
theorem descends_2_1 : Descends 2 1 := by decide
theorem descends_3_2 : Descends 3 2 := by decide
theorem descends_4_4 : Descends 4 4 := by decide
theorem descends_4_8 : Descends 4 8 := by decide
theorem descends_5_16 : Descends 5 16 := by decide

/-- Every even residue descends in one step. -/
theorem descends_one_of_even {r : Nat} (hr : r % 2 = 0) (hle : acceleratedStep r ≤ r) :
    Descends 1 r := by
  refine ⟨?_, ?_⟩
  · rw [oddCount_succ_of_even hr, oddCount_zero]
    decide
  · rw [acceleratedOrbit, acceleratedOrbit]
    exact hle

/-- The residue `1` modulo `4` descends: `T²(4m+1) = 3m+1 < 4m+1` for `m > 0`. -/
theorem accOrbit_two_lt_of_one_mod_four {m : Nat} (hm : 0 < m) :
    acceleratedOrbit 2 (4 * m + 1) < 4 * m + 1 := by
  have h : (2:Nat) ^ 2 = 4 := rfl
  have := accOrbit_lt_of_descends (k := 2) (r := 1) descends_2_1 hm
  rw [h] at this
  exact this

/-- Explicit form of the affine map on the class `1` modulo `4`. -/
theorem accOrbit_two_one_mod_four (m : Nat) :
    acceleratedOrbit 2 (4 * m + 1) = 3 * m + 1 := by
  have h : (2:Nat) ^ 2 = 4 := rfl
  have hc := accOrbit_pow_two_mul_add 2 m 1
  rw [h] at hc
  rw [hc]
  rfl

/-- Explicit form of the affine map on the class `3` modulo `4`: it *grows*,
which is why `3 mod 4` is exactly the class a minimal counterexample must lie
in. -/
theorem accOrbit_two_three_mod_four (m : Nat) :
    acceleratedOrbit 2 (4 * m + 3) = 9 * m + 8 := by
  have h : (2:Nat) ^ 2 = 4 := rfl
  have hc := accOrbit_pow_two_mul_add 2 m 3
  rw [h] at hc
  rw [hc]
  rfl

/-- The class `3` modulo `4` is not a descending class. -/
theorem not_descends_2_3 : ¬ Descends 2 3 := by decide

end Congruence
end Collatz
