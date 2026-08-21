import Collatz.Strategy.CycleLength520
import Collatz.Strategy.CycleProduct

/-!
# The cycle frontier, reached: length at least 1539

`CycleLength520` proves that no nontrivial accelerated cycle is shorter than
`520`, and its own docstring names the real frontier of the method as
`(L, a) = (1539, 971)` — the first length the product bound cannot exclude at the
verified range `307200`.  The gap between `520` and `1539` was never
mathematical.  It was arithmetic cost: `excludedLength` scans every `a ∈ [0, L]`,
so certifying all lengths below `L` costs `O(L²)` bignum comparisons on numerals
with thousands of bits, and the kernel ran out of patience long before the
frontier.

The scan is unnecessary.  The quantity being compared,

`3 ^ a · (3c + 2a)`,

is monotone in `a` (`R_mono`), so among the admissible exponents — those with
`3 ^ a < 2 ^ L` — only the largest can violate the bound.  `topIndex L` names
that largest exponent by integer arithmetic alone, `⌊L · log₃ 2⌋` computed as
`L * 397573379 / 630138897`, and `excludedFast` checks two things: that
`topIndex L` really is maximal (`2 ^ L ≤ 3 ^ (topIndex L + 1)`), and that the
bound holds there.  Two comparisons per length instead of `L + 1`, and the
maximality check makes the shortcut self-certifying — no appeal to the accuracy
of the rational approximation is needed, because the kernel verifies the
consequence directly at every `L`.

With that, the whole range `1 ≤ L < 1539` is swept by one `decide`, and the
frontier the earlier file could only describe is now a theorem.  There is no new
mathematics here: the same product bound, the same verified range, evaluated
where it was always going to bite.
-/

namespace Collatz
namespace CycleLength1539
open Reach Congruence AccCycle CycleExtremes NeverDrops CycleProduct

/-- The product-bound quantity is monotone in the odd-step count, so only the
largest admissible exponent can fail the test. -/
theorem R_mono (c : Nat) {a b : Nat} (h : a ≤ b) :
    3 ^ a * (3 * c + 2 * a) ≤ 3 ^ b * (3 * c + 2 * b) := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · have h1 : a ≤ b := by omega
      refine Nat.le_trans (ih h1) ?_
      rw [Nat.pow_succ]
      have hm : 3 ^ b * (3 * c + 2 * b) ≤ 3 ^ b * (3 * (3 * c + 2 * (b + 1))) :=
        Nat.mul_le_mul_left _ (by omega)
      have he : 3 ^ b * (3 * (3 * c + 2 * (b + 1))) = 3 ^ b * 3 * (3 * c + 2 * (b + 1)) := by
        rw [Nat.mul_assoc]
      omega
    · have : a = b + 1 := by omega
      subst this; exact Nat.le_refl _

/-- `⌊L · log₃ 2⌋` by integer arithmetic: the largest exponent `a` that can
satisfy `3 ^ a < 2 ^ L`.  The value is *checked* at every `L` by `excludedFast`,
so the accuracy of the rational approximation `397573379 / 630138897` is never
trusted. -/
def topIndex (L : Nat) : Nat := L * 397573379 / 630138897

/-- The two-comparison replacement for the `O(L)` scan in `excludedLength`: the
top exponent is maximal, and the bound holds there. -/
def excludedFast (c L : Nat) : Bool :=
  decide (2 ^ L ≤ 3 ^ (topIndex L + 1)) &&
  decide (3 ^ (topIndex L) * (3 * c + 2 * (topIndex L)) < 3 * c * 2 ^ L)

theorem excludedLength_of_excludedFast {c L : Nat} (h : excludedFast c L = true) :
    excludedLength c L = true := by
  rw [excludedFast, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  obtain ⟨hcap, htop⟩ := h
  rw [excludedLength, List.all_eq_true]
  intro a _
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  by_cases hlt : 3 ^ a < 2 ^ L
  · refine Or.inr ?_
    have hale : a ≤ topIndex L := by
      rcases Nat.lt_or_ge (topIndex L) a with hcon | hok
      · have h1 : topIndex L + 1 ≤ a := by omega
        have h2 : 3 ^ (topIndex L + 1) ≤ 3 ^ a := Nat.pow_le_pow_right (by omega) h1
        omega
      · exact hok
    exact Nat.lt_of_le_of_lt (R_mono c hale) htop
  · exact Or.inl hlt

set_option maxHeartbeats 40000000 in
set_option exponentiation.threshold 4000 in
set_option maxRecDepth 4000000 in
theorem sweep_full :
    ((List.range 1538).map (fun i => i + 1)).all (fun L => excludedFast 307200 L) = true := by
  decide

theorem excludedLength_of_lt_1539 {L : Nat} (hL : L < 1539) (hpos : 0 < L) :
    excludedLength 307200 L = true := by
  refine excludedLength_of_excludedFast ?_
  have h := sweep_full
  rw [List.all_eq_true] at h
  exact h L (List.mem_map.mpr ⟨L - 1, List.mem_range.mpr (by omega), by omega⟩)

/-- **A nontrivial accelerated cycle has length at least `1539`.**  Three times
the previous bound, from the same ingredients evaluated at the one exponent that
matters. -/
theorem length_ge_1539 {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 1539 ≤ L := by
  rcases Nat.lt_or_ge L 1539 with hL | hL
  · exfalso
    obtain ⟨m, hm, _hmin⟩ := exists_accCycleMin n
    obtain ⟨i, hi⟩ := hm
    have hmpos : 0 < m := by rw [← hi]; exact acceleratedOrbit_positive hn i
    have htrans : ∀ k : Nat, acceleratedOrbit k m = acceleratedOrbit (k + i) n := by
      intro k; rw [← hi, acceleratedOrbit_add k i n]
    have hc : ∀ k : Nat, 307200 ≤ acceleratedOrbit k m := by
      intro k
      exact VerifiedSharp.ge_verified_sharp hn hnr ⟨k + i, (htrans k).symm⟩
    have hcyc : acceleratedOrbit L m = m := by
      rw [htrans L, Nat.add_comm L i, ← acceleratedOrbit_add i L n, h.2, hi]
    have hlt' : oddCount m L < L := Cycle.oddCount_lt_length_of_accCycle hmpos h.1 hcyc
    have hle : oddCount m L ≤ L := Nat.le_of_lt hlt'
    have hsmall : 2 * oddCount m L ≤ 3 * 307200 := by omega
    have hlt : 3 ^ oddCount m L < 2 ^ L :=
      Cycle.two_pow_gt_three_pow_of_accCycle hmpos h.1 hcyc
    exact no_cycle_of_excludedLength hmpos (by omega) hc hcyc hsmall hle hlt
      (excludedLength_of_lt_1539 hL h.1)
  · exact hL

end CycleLength1539
end Collatz
