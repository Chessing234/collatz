import Collatz.Strategy.FirstLightCertificates

/-!
# A linear-size checker for coefficient-gap certificates

At each length, an upper bound on the light odd counts suffices. If b≤a,
the numerator b*3^b is no larger and the gap 2^k-3^b is no smaller. The
checker visits lengths once and verifies its proposed upper count locally.
Its arithmetic search policy is not trusted by the soundness theorem.
-/
namespace Collatz.FirstLightGapCheck

/-- One checked upper odd count controls every light count at that length. -/
theorem gap_of_upper_count (k a N b : Nat)
    (hupper : 2^k ≤ 3^(a+1))
    (hgap : a*3^a < 3*(2^k-3^a)*N)
    (hlight : 3^b < 2^k) : b*3^b < 3*(2^k-3^b)*N := by
  have hba : b≤a := by
    by_cases h : b≤a
    · exact h
    · have hp : (3:Nat)^(a+1) ≤ 3^b := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have hp : (3:Nat)^b ≤ 3^a := Nat.pow_le_pow_right (by decide) hba
  have hnum : b*3^b ≤ a*3^a := Nat.mul_le_mul hba hp
  have hsub : 2^k-3^a ≤ 2^k-3^b := by omega
  have hden := Nat.mul_le_mul_right N (Nat.mul_le_mul_left 3 hsub)
  exact Nat.lt_of_le_of_lt hnum (Nat.lt_of_lt_of_le hgap hden)

/-- Check a proposed upper count; failure rejects the certificate. -/
def entry (N k a : Nat) : Bool :=
  decide (2^k ≤ 3^(a+1) ∧ a*3^a < 3*(2^k-3^a)*N)

/-- The next candidate increases by at most one because 2<3. Soundness does
not assume this heuristic is correct: each proposed candidate is checked. -/
def nextCount (k a : Nat) : Nat :=
  if 3^(a+1) < 2^(k+1) then a+1 else a

/-- Check the lengths k+1 through k+fuel, carrying the proposed upper count. -/
def run (N : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel+1, k, a =>
    entry N (k+1) (nextCount k a) && run N fuel (k+1) (nextCount k a)

/-- A successful run certifies every light count at every covered length. -/
theorem run_sound (N fuel k a : Nat) (h : run N fuel k a = true) :
    ∀ j, k<j → j≤k+fuel → ∀ b, 3^b < 2^j → b*3^b < 3*(2^j-3^b)*N := by
  induction fuel generalizing k a with
  | zero => intro j hj hjk; omega
  | succ fuel ih =>
    rw [run, Bool.and_eq_true] at h
    intro j hj hjk b hb
    by_cases he : j=k+1
    · subst he
      have hg := decide_eq_true_eq.mp h.1
      exact gap_of_upper_count _ _ _ _ hg.1 hg.2 hb
    · exact ih (k+1) (nextCount k a) h.2 j (by omega) (by omega) b hb

/-- A compact certificate for the gap component of first-crossing descent. -/
def check (H N : Nat) : Bool := run N H 0 0

/-- Compatibility with the generic first-crossing certificate interface. -/
theorem check_sound (H N : Nat) (h : check H N = true) :
    ∀ k : Fin (H+1), ∀ a : Fin (k.val+1),
      3^a.val < 2^k.val → a.val*3^a.val < 3*(2^k.val-3^a.val)*N := by
  intro k a hl
  by_cases hk : k.val=0
  · have hp : 1 ≤ (3:Nat)^a.val := Nat.one_le_pow _ _ (by decide)
    have he : (2:Nat)^k.val = 1 := by rw [hk, Nat.pow_zero]
    rw [he] at hl
    omega
  · exact run_sound N H 0 0 h k.val (by omega) (by have := k.isLt; omega) a.val hl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- An independent compact recheck of the existing 256-step gap threshold. -/
theorem gap_256 : check 256 6701 = true := by decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 2048 in
/-- The same exceptional-start threshold covers all lengths through 1024. -/
theorem gap_1024 : check 1024 99730 = true := by decide

end Collatz.FirstLightGapCheck
