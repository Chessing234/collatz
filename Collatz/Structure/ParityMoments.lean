import Collatz.Structure.Density
import Collatz.Strategy.AffineExact

/-!
# Two-parameter parity moments

Assign weight A to every odd step and weight B to every even step. Summing
the resulting products over a complete residue period gives (A+B)^k exactly.
Unlike a fixed moment base, the ratio A/B can approach one through rational
values. This is a foundation for sharper concentration estimates; it does not
by itself prove a power-threshold density theorem.
-/
namespace Collatz.ParityMoments
open _root_.Collatz.Sum Density

/-- Homogeneous weight of a parity vector with a odd steps out of k. -/
def weight (A B k a : Nat) : Nat := A^a*B^(k-a)

/-- Opposite choices of the last parity bit multiply the total weight by A+B. -/
theorem weight_split (A B k a : Nat) (ha : a≤k) :
    weight A B (k+1) a + weight A B (k+1) (a+1) =
      (A+B)*weight A B k a := by
  have he : k+1-a=k-a+1 := by omega
  have ho : k+1-(a+1)=k-a := by omega
  simp only [weight, he, ho, Nat.pow_succ, Nat.add_mul]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]

/-- Complementary lifted residues give the two possible final parity bits. -/
theorem weight_pair (A B r k : Nat) (hr : r<2^k) :
    weight A B (k+1) (oddCount r (k+1)) +
      weight A B (k+1) (oddCount (2^k+r) (k+1)) =
        (A+B)*weight A B k (oddCount r k) := by
  have hshift := oddCount_two_pow_add hr
  have horb := accOrbit_two_pow_add r k
  have hodd := Arith.three_pow_odd (oddCount r k)
  rw [oddCount_succ_last, oddCount_succ_last, hshift, horb]
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k r) with he | ho
  · have h1 : (3^oddCount r k+acceleratedOrbit k r)%2=1 := by omega
    rw [he, h1, Nat.add_zero]
    exact weight_split A B k _ (AffineExact.oddCount_le_self r k)
  · have h0 : (3^oddCount r k+acceleratedOrbit k r)%2=0 := by omega
    rw [ho, h0, Nat.add_zero, Nat.add_comm]
    exact weight_split A B k _ (AffineExact.oddCount_le_self r k)

/-- The complete homogeneous moment over one residue period. -/
def moment (A B k : Nat) : Nat := sumRange (2^k) (fun r => weight A B k (oddCount r k))

/-- Exact two-parameter moment identity, proved by residue pairing. -/
theorem moment_eq (A B k : Nat) : moment A B k=(A+B)^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [moment, Arith.two_pow_succ, sumRange_two_mul, ← sumRange_add]
    have he : sumRange (2^k) (fun r => weight A B (k+1) (oddCount r (k+1)) +
        weight A B (k+1) (oddCount (2^k+r) (k+1))) =
        sumRange (2^k) (fun r => (A+B)*weight A B k (oddCount r k)) :=
      sumRange_congr (fun r hr => weight_pair A B r k hr)
    rw [he, sumRange_const_mul]
    change (A+B)*moment A B k=(A+B)^(k+1)
    rw [ih, Nat.pow_succ, Nat.mul_comm]

/-- When A≥B, the weight increases with the number of odd steps. -/
theorem weight_mono {A B k a b : Nat} (hAB : B≤A) (hab : a≤b) (hbk : b≤k) :
    weight A B k a≤weight A B k b := by
  have hd := Nat.pow_le_pow_left hAB (b-a)
  have hm := Nat.mul_le_mul_left (A^a) hd
  have ht := Nat.mul_le_mul_right (B^(k-b)) hm
  have he : k-a=(b-a)+(k-b) := by omega
  have hb : a+(b-a)=b := by omega
  change A^a*B^(k-a)≤A^b*B^(k-b)
  rw [he, Nat.pow_add, ← Nat.mul_assoc]
  have hre : A^a*A^(b-a)=A^b := by rw [← Nat.pow_add, hb]
  rw [hre] at ht
  exact ht

/-- Count residues with at least h odd steps in k iterations. -/
def tailCount (k h : Nat) : Nat := countRange (2^k) (fun r => decide (h≤oddCount r k))

/-- An integer Chernoff/Markov bound with arbitrary rational tilt A/B.
No division or real analysis is needed in this form. -/
theorem tail_moment_bound (A B k h : Nat) (hAB : B≤A) :
    weight A B k h*tailCount k h≤(A+B)^k := by
  have ht := mul_countRange_le (n := 2^k) (w := weight A B k h)
    (p := fun r => decide (h≤oddCount r k))
    (f := fun r => weight A B k (oddCount r k)) (by
      intro r _ hr
      have hh : h≤oddCount r k := by simpa using hr
      exact weight_mono hAB hh (AffineExact.oddCount_le_self r k))
  exact Nat.le_trans ht (Nat.le_of_eq (moment_eq A B k))

/-- A small rational-tilt example is evaluated directly in the kernel. -/
theorem near_one_example : moment 11 10 4=21^4 := by decide

/-- Exact parameters for a tail slightly above one half of the parity bits. -/
theorem four_fifths_moment_gap : (125:Nat)^125 < 2^125*(63^63*62^62) := by decide

set_option exponentiation.threshold 1000 in
/-- Below this parity threshold the multiplier fits the 4/5 power scale.
Constant factors and the affine remainder still require separate treatment. -/
theorem four_fifths_multiplier_gap : (3:Nat)^315 < 2^500 := by decide

/-- The complete-period tail estimate at the selected 125-step block scale. -/
theorem four_fifths_tail_bound (s : Nat) :
    (63^63*62^62)^s*tailCount (125*s) (63*s)≤(125^125)^s := by
  have h := tail_moment_bound 63 62 (125*s) (63*s) (by decide)
  have he : 125*s-63*s=62*s := by omega
  simpa only [weight, he, Nat.pow_mul, Nat.mul_pow] using h

end Collatz.ParityMoments
