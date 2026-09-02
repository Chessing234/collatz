import Collatz.Strategy.RealizableFrontier6809
import Collatz.Search.BarinaRange

/-!
# The certificate is monotone in the verified range

`RealizableBound.cert n c b p3 p2` tests `b + p3 · c < 2 · p2 · c` at each of `n`
indices.  Read as `Bcap i < c · (2 ^ (fexp i + 1) − 3 ^ i)`, it plainly ought to
get *easier* as the verified range `c` grows: the right-hand side scales with `c`
while the left does not.  This file proves that, which is the structural reason
the frontier ladder in `RealizableFrontier6809` only ever moves upward.

The one thing to check is that the multiplier `2 · p2 − p3` is genuinely
positive.  That is the invariant `p3 < 2 · p2` — for the carried values
`(3 ^ i, 2 ^ (fexp i))` it is exactly `fexp_spec`'s upper half — and
`carry_invariant` shows the `cert` recursion preserves it.

## What this does and does not give

It gives: any future extension of the verified range preserves every certificate
already proved, with no recomputation (`cert_barina_4296`).  So the ladder is
monotone and the work is never invalidated.

It does not give a *better* frontier at a larger range.  Reaching the frontier
that Barina's range actually supports would need `cert` evaluated to roughly
`7.2 · 10 ^ 10` indices, on integers of some `3.4 · 10 ^ 10` digits.  That is far
beyond the kernel, and beyond any scan.  See the note in
`Papers/gap-audit-formalization.md`; the number there is a numerical estimate,
not a theorem.
-/

namespace Collatz
namespace CertMonotone

open RealizableBound

/-- The `cert` recursion preserves `p3 < 2 * p2`. -/
theorem carry_invariant {p3 p2 : Nat} (h : p3 < 2 * p2) :
    3 * p3 < 2 * (if 4 * p2 ≤ 3 * p3 then 4 * p2 else 2 * p2) := by
  by_cases hb : 4 * p2 ≤ 3 * p3
  · rw [if_pos hb]; omega
  · rw [if_neg hb]; omega

/-- **Raising the verified range never invalidates a certificate.** -/
theorem cert_mono_c : ∀ (n c c' b p3 p2 : Nat), p3 < 2 * p2 → c ≤ c' →
    cert n c b p3 p2 = true → cert n c' b p3 p2 = true := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _; rfl
  | succ n ih =>
    intro c c' b p3 p2 hinv hc h
    rw [cert, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hhead, htail⟩ := h
    rw [cert, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ih _ _ _ _ _ (carry_invariant hinv) hc htail⟩
    · -- `b < c * (2 * p2 - p3)` scales with `c`
      have hgap : p3 * c + b < 2 * p2 * c := by omega
      have hstep : (2 * p2 - p3) * c ≤ (2 * p2 - p3) * c' := Nat.mul_le_mul_left _ hc
      have hexp : (2 * p2 - p3) * c = 2 * p2 * c - p3 * c := by
        rw [Nat.sub_mul]
      have hexp' : (2 * p2 - p3) * c' = 2 * p2 * c' - p3 * c' := by
        rw [Nat.sub_mul]
      have hle3 : p3 * c ≤ 2 * p2 * c := Nat.mul_le_mul_right _ (by omega)
      have hle3' : p3 * c' ≤ 2 * p2 * c' := Nat.mul_le_mul_right _ (by omega)
      omega

/-- The invariant holds at the standard start `(p3, p2) = (1, 1)`. -/
theorem start_invariant : (1 : Nat) < 2 * 1 := by decide

/-- **The 4296-index certificate holds at Barina's range for free.**  No new
computation: `RealizableFrontier6809.cert_4296` plus monotonicity. -/
theorem cert_barina_4296 :
    cert 4296 BarinaRange.barinaBound 0 1 1 = true := by
  refine cert_mono_c 4296 1086464 _ 0 1 1 start_invariant ?_ RealizableFrontier6809.cert_4296
  rw [BarinaRange.barina_value]
  omega

/-- Prefix closure: a certificate of length `n + 1` contains one of length `n`. -/
theorem cert_mono_n : ∀ (n c b p3 p2 : Nat),
    cert (n + 1) c b p3 p2 = true → cert n c b p3 p2 = true := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; rfl
  | succ n ih =>
    intro c b p3 p2 h
    rw [cert, Bool.and_eq_true] at h
    obtain ⟨hhead, htail⟩ := h
    rw [cert, Bool.and_eq_true]
    exact ⟨hhead, ih _ _ _ _ htail⟩

/-! ## The consumable form transfers too

`RESEARCH.md`'s parametricity audit records a caveat: the frontier lemmas are
generic in the verified range, but several consume a numeric certificate keyed to
the constant, "generic in statement but their certificates would need recomputing
at another bound".

For a *larger* bound they do not.  `cert_mono_c` covers the raw checker; this
covers the unpacked form those lemmas actually take, so `cert_1086464` and its
siblings apply verbatim at any larger range with no recomputation.  (A *smaller*
bound is of course a different matter, and is not claimed.) -/

/-- The certificate in the form the frontier lemmas actually consume is monotone
in the range as well. -/
theorem bank_mono {A c c' : Nat} (hcc : c ≤ c')
    (h : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) :
    ∀ i : Nat, i < A → Bcap i + 3 ^ i * c' < 2 * 2 ^ fexp i * c' := by
  intro i hi
  have hgap : 3 ^ i < 2 * 2 ^ fexp i := by
    have h1 := lt_fexp i
    have h2 : (2:Nat) ^ (fexp i + 1) = 2 ^ fexp i * 2 := Nat.pow_succ _ _
    omega
  have hstep : (2 * 2 ^ fexp i - 3 ^ i) * c ≤ (2 * 2 ^ fexp i - 3 ^ i) * c' :=
    Nat.mul_le_mul_left _ hcc
  have he : ∀ x : Nat, (2 * 2 ^ fexp i - 3 ^ i) * x = 2 * 2 ^ fexp i * x - 3 ^ i * x := by
    intro x; rw [Nat.sub_mul]
  have hle : 3 ^ i * c ≤ 2 * 2 ^ fexp i * c :=
    Nat.mul_le_mul_right _ (by omega)
  have hle' : 3 ^ i * c' ≤ 2 * 2 ^ fexp i * c' :=
    Nat.mul_le_mul_right _ (by omega)
  have e1 := he c
  have e2 := he c'
  have hi2 := h i hi
  omega

end CertMonotone
end Collatz
