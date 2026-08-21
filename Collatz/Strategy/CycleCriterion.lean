import Collatz.Strategy.CycleAccumulator

/-!
# Cycles are exactly the words whose gap divides their accumulator

`CycleAccumulator` sends a cycle to an arithmetic condition: `(2 ^ L − 3 ^ a) · n
= C_L(n)`.  This file proves the converse, which is the statement that makes the
condition worth having.

Start from *any* residue `r` and any window `L` whose multiplier is small,
`3 ^ a < 2 ^ L` with `a = a(r,L)`.  Write `d = 2 ^ L − 3 ^ a` for the gap and
suppose only that `d` divides `C_L(r)`.  Put `x = C_L(r) / d`.  Then `x` is a
cycle point of length `L`, and its parity word is the word of `r`.

The proof is short once the accumulator is known to be a class function.  From
`affine_exact` at `r`, `3 ^ a · r + C ≡ 0 (mod 2 ^ L)`, and from `d · x = C`,
`3 ^ a · x + C ≡ 0 (mod 2 ^ L)` as well.  Subtracting, `3 ^ a` — an odd number —
annihilates `x − r` modulo `2 ^ L`, so `x ≡ r (mod 2 ^ L)`
(`dvd_of_odd_mul` supplies the cancellation).  `AccumulatorClass` then transfers
both `a` and `C` from `r` to `x`, and `affine_exact` at `x` reads
`2 ^ L · T^L(x) = 3 ^ a · x + C = 2 ^ L · x`.

So the search for a cycle of length `L` is *exactly* the search over the `2 ^ L`
words for one whose gap divides its accumulator — there is no residual dynamical
side condition, no self-consistency requirement left to check.  Positivity and
integrality do the rest by themselves.  This is the precise sense in which
Terras' theorem ("every word is realised") gives the adversary nothing: the
words are all available, but the arithmetic condition on them is not.

It is worth being clear about what this does *not* do.  It converts one hard
problem into another of the same difficulty — deciding a divisibility for
exponentially many words.  Its value is that the second problem is stated purely
in arithmetic, with the orbit eliminated, so tools that cannot see dynamics can
be brought to bear on it.
-/

namespace Collatz
namespace CycleCriterion

open Congruence AffineExact AccumulatorClass AccCycle

/-! ## Cancelling an odd factor modulo a power of two -/

/-- A power of two dividing `u · y` with `u` odd divides `y`.  The generalisation
of `OddRuns.dvd_of_three_mul` from the factor `3` to any odd factor. -/
theorem dvd_of_odd_mul {u : Nat} (hu : u % 2 = 1) : ∀ (k y : Nat), 2 ^ k ∣ u * y → 2 ^ k ∣ y := by
  intro k
  induction k with
  | zero => intro y _; simp
  | succ k ih =>
    intro y hdvd
    have hu' : u = 2 * (u / 2) + 1 := by omega
    have hexp : u * y = 2 * ((u / 2) * y) + y := by
      have h1 : u * y = (2 * (u / 2) + 1) * y := by rw [← hu']
      rw [h1, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    have heven : y % 2 = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      have h2 : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := Arith.two_pow_succ k
      rw [h2, Nat.mul_assoc] at hc
      omega
    obtain ⟨y', hy'⟩ : ∃ y', y = 2 * y' := ⟨y / 2, by omega⟩
    subst hy'
    have hstrip : 2 ^ k ∣ u * y' := by
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨c, ?_⟩
      have h2 : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := Arith.two_pow_succ k
      have hsplit : u * (2 * y') = 2 * (u * y') := by
        rw [Nat.mul_left_comm]
      rw [h2, Nat.mul_assoc] at hc
      omega
    obtain ⟨d, hd⟩ := ih y' hstrip
    refine ⟨d, ?_⟩
    have hA : (2:Nat) ^ (k + 1) * d = 2 * (2 ^ k * d) := by
      rw [Arith.two_pow_succ, Nat.mul_assoc]
    omega

/-- Odd multipliers cancel in congruences modulo a power of two. -/
theorem cancel_odd_mod_two_pow {u x y k : Nat} (hu : u % 2 = 1) (_hxy : y ≤ x)
    (h : 2 ^ k ∣ (u * x - u * y)) : 2 ^ k ∣ (x - y) := by
  have hsub : u * x - u * y = u * (x - y) := (Nat.mul_sub u x y).symm
  rw [hsub] at h
  exact dvd_of_odd_mul hu k (x - y) h

/-! ## The converse of the cycle equation -/

/-- The accumulator and the multiplier fit together modulo `2 ^ L`: the affine
identity says `3 ^ a · x + C_L(x)` is a multiple of `2 ^ L`. -/
theorem two_pow_dvd_affine (x L : Nat) :
    2 ^ L ∣ (3 ^ oddCount x L * x + affineC L x) :=
  ⟨acceleratedOrbit L x, (affine_exact x L).symm⟩

/-- **The criterion is sufficient.**  If the gap of a residue's word divides its
accumulator, the quotient is a genuine cycle point of that length, carrying that
very word. -/
theorem cycle_of_gap_dvd {r L x : Nat}
    (hgap : 3 ^ oddCount r L < 2 ^ L)
    (hx : (2 ^ L - 3 ^ oddCount r L) * x = affineC L r) :
    acceleratedOrbit L x = x ∧ x % 2 ^ L = r % 2 ^ L := by
  -- the two affine identities, one for `r` and one for `x`
  have hdr := two_pow_dvd_affine r L
  have hxexp : 3 ^ oddCount r L * x + affineC L r = 2 ^ L * x := by
    have hmono : 3 ^ oddCount r L * x ≤ 2 ^ L * x := Nat.mul_le_mul_right x (by omega)
    have hsub : (2 ^ L - 3 ^ oddCount r L) * x = 2 ^ L * x - 3 ^ oddCount r L * x :=
      Nat.sub_mul _ _ _
    omega
  -- so `2 ^ L` divides `3 ^ a · x + C` as well
  have hdx : 2 ^ L ∣ (3 ^ oddCount r L * x + affineC L r) := ⟨x, hxexp⟩
  -- subtract: `3 ^ a` annihilates the difference of `x` and `r` modulo `2 ^ L`
  have hodd : (3:Nat) ^ oddCount r L % 2 = 1 := Arith.three_pow_odd _
  have hmodeq : x % 2 ^ L = r % 2 ^ L := by
    rcases Nat.le_total r x with hle | hle
    · have hd : 2 ^ L ∣ (3 ^ oddCount r L * x - 3 ^ oddCount r L * r) := by
        obtain ⟨c, hc⟩ := hdx
        obtain ⟨e, he⟩ := hdr
        have hmono : 3 ^ oddCount r L * r ≤ 3 ^ oddCount r L * x := Nat.mul_le_mul_left _ hle
        refine ⟨c - e, ?_⟩
        have hce : e ≤ c := by
          have := Nat.mul_le_mul_left (2 ^ L) (Nat.le_refl e)
          have hle2 : 2 ^ L * e ≤ 2 ^ L * c := by omega
          exact Nat.le_of_mul_le_mul_left hle2 (Arith.two_pow_pos L)
        rw [Nat.mul_sub]
        omega
      have hdiff := cancel_odd_mod_two_pow hodd hle hd
      obtain ⟨c, hc⟩ := hdiff
      have hxr : x = r + 2 ^ L * c := by omega
      rw [hxr, Nat.add_mul_mod_self_left]
    · have hd : 2 ^ L ∣ (3 ^ oddCount r L * r - 3 ^ oddCount r L * x) := by
        obtain ⟨c, hc⟩ := hdx
        obtain ⟨e, he⟩ := hdr
        have hmono : 3 ^ oddCount r L * x ≤ 3 ^ oddCount r L * r := Nat.mul_le_mul_left _ hle
        refine ⟨e - c, ?_⟩
        have hce : c ≤ e := by
          have hle2 : 2 ^ L * c ≤ 2 ^ L * e := by omega
          exact Nat.le_of_mul_le_mul_left hle2 (Arith.two_pow_pos L)
        rw [Nat.mul_sub]
        omega
      have hdiff := cancel_odd_mod_two_pow hodd hle hd
      obtain ⟨c, hc⟩ := hdiff
      have hxr : r = x + 2 ^ L * c := by omega
      rw [hxr, Nat.add_mul_mod_self_left]
  -- transfer the word from `r` to `x` and read off the cycle
  have hcount : oddCount x L = oddCount r L := oddCount_congr_of_mod hmodeq
  have hC : affineC L x = affineC L r := affineC_congr_of_mod hmodeq
  have hexact := affine_exact x L
  rw [hcount, hC, hxexp] at hexact
  refine ⟨?_, hmodeq⟩
  exact Nat.eq_of_mul_eq_mul_left (Arith.two_pow_pos L) hexact

/-- **The criterion, both ways.**  For a positive `x` and a window `L ≥ 1` with a
contracting multiplier, `x` is a cycle point exactly when the gap of its own word
divides its accumulator — and then `x` is the quotient. -/
theorem cycle_iff_gap_mul {x L : Nat} (hx : 0 < x) (hL : 0 < L)
    (hgap : 3 ^ oddCount x L < 2 ^ L) :
    acceleratedOrbit L x = x ↔ (2 ^ L - 3 ^ oddCount x L) * x = affineC L x := by
  constructor
  · intro h
    exact CycleAccumulator.cycle_gap_mul hx ⟨hL, h⟩
  · intro h
    exact (cycle_of_gap_dvd (r := x) hgap h).1

end CycleCriterion
end Collatz
