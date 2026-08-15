import Collatz.Strategy.Pillars
import Collatz.Search.Descent

/-!
# Sieve-accelerated verification

Brute-force verification costs one kernel check per integer, which is why
clearing `60 000` already takes minutes.  But the sieve of
`Collatz.Structure.Minimal` settles `960` of every `1024` residue classes
*without any per-integer work*: a number whose residue mod `1024` fails the
sieve descends automatically.

So only the `64` surviving classes need explicit checking, and the same
computational budget covers sixteen times the range.

The engine is `checkBlocks`: for each block `[1024m, 1024m + 1024)` it checks
only the `64` survivors, ignoring the other `960` residues entirely.  Soundness
is a strong induction that splits on whether `n` survives the sieve:

* survivor — the explicit check supplies a drop;
* non-survivor — `Strategy.exists_drop_of_not_survives` supplies one for free.

Either way `n` drops to a smaller number, which reaches `1` by induction.

The exported bound is `reachesOne_of_lt_102400`: `102 400` integers cleared by
checking only about `6 400` of them.
-/

namespace Collatz
namespace Search

open Reach Congruence Strategy

/-! ## The surviving residues -/

/-- The sixty-four residues modulo `1024` that survive the sieve.  Every other
residue descends on its own, so these are the only ones needing a check. -/
def survivorsMod1024 : List Nat :=
  [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
   239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487,
   495, 511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743,
   751, 763, 767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991,
   1007, 1019, 1023]

/-- The list really is the survivor list of the level-`10` sieve. -/
theorem sieveCheck_survivors : sieveCheck 10 survivorsMod1024 = true :=
  Minimal.sieveCheck_ten

/-- A number surviving the sieve has its residue in the list. -/
theorem mem_survivors_of_survives {n : Nat} (h : survives 10 (n % 2 ^ 10) = true) :
    n % 2 ^ 10 ∈ survivorsMod1024 := by
  have hlt : n % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (Arith.two_pow_pos 10)
  exact List.mem_of_elem_eq_true (mem_allowed_of_sieveCheck sieveCheck_survivors hlt h)

/-! ## The block checker -/

/-- Check the surviving residues of the block `[1024m, 1024m + 1024)`. -/
def checkBlock (m fuel : Nat) : Bool :=
  survivorsMod1024.all fun r => dropsWithin fuel (2 ^ 10 * m + r)

/-- Check the blocks `lo, lo+1, …, lo+len-1`.  Splitting the sweep into ranges
keeps each kernel computation — and each proof term — small; one monolithic
check over all `750` blocks does not finish in reasonable time. -/
def checkRange (lo len fuel : Nat) : Bool :=
  match len with
  | 0 => true
  | k + 1 => checkBlock (lo + k) fuel && checkRange lo k fuel

/-- Reading one entry out of a range sweep. -/
theorem drops_of_checkRange {lo len fuel m r : Nat} (h : checkRange lo len fuel = true)
    (hlo : lo ≤ m) (hhi : m < lo + len) (hr : r ∈ survivorsMod1024) :
    dropsWithin fuel (2 ^ 10 * m + r) = true := by
  induction len with
  | zero => omega
  | succ k ih =>
    rw [checkRange, Bool.and_eq_true] at h
    by_cases hmk : m < lo + k
    · exact ih h.2 hmk
    · have hmeq : m = lo + k := by omega
      subst hmeq
      exact (List.all_eq_true.mp h.1) r hr

/-! ## Soundness -/

/-- **Sieve-accelerated verification.**  If every surviving residue in every
block below `M` drops, then every positive `n < 1024 M` reaches `1`. -/
theorem reachesOne_of_blocks {M fuel : Nat}
    (h : ∀ m r : Nat, m < M → r ∈ survivorsMod1024 →
      dropsWithin fuel (2 ^ 10 * m + r) = true) :
    ∀ n : Nat, 0 < n → n < 2 ^ 10 * M → ReachesOne n := by
  have hpow : (2:Nat) ^ 10 = 1024 := by decide
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hpos hlt
    by_cases hsmall : n ≤ 1024
    · exact reachesOne_of_le_1024 hpos hsmall
    · have hgt : 1024 < n := by omega
      -- either the sieve gives a drop, or the explicit check does
      have hdrop : ∃ k : Nat, acceleratedOrbit k n < n := by
        by_cases hs : survives 10 (n % 2 ^ 10) = true
        · have hmem := mem_survivors_of_survives hs
          have hmlt : n / 2 ^ 10 < M := by rw [hpow]; rw [hpow] at hlt; omega
          have hcheck := h (n / 2 ^ 10) (n % 2 ^ 10) hmlt hmem
          have hdecomp : 2 ^ 10 * (n / 2 ^ 10) + n % 2 ^ 10 = n := by
            rw [hpow]; omega
          rw [hdecomp] at hcheck
          exact exists_lt_of_dropsWithin hcheck
        · exact exists_drop_of_not_survives hgt (by omega) hs
      obtain ⟨k, hk⟩ := hdrop
      have hkpos : 0 < acceleratedOrbit k n := acceleratedOrbit_positive hpos k
      exact reachesOne_of_accOrbit hpos (ih _ hk hkpos (by omega))

/-! ## The verified range

Two independent kernel computations, each covering fifty blocks.  Together they
check about `6 400` integers and clear `102 400`, because the sieve disposes of
the other `96 000` with no computation at all — roughly a fourfold saving in
kernel time over checking every integer directly.

Pushing to `750` blocks would clear `768 000` and lift the cycle-length
exclusion from `26` to `31`, but costs about forty minutes of kernel time; the
gain is flat between `100` and `700` blocks, so this is the efficient point. -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem check_r0 : checkRange 0 50 200 = true := by decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem check_r1 : checkRange 50 50 200 = true := by decide

/-- Every surviving residue in every block below `100` drops within `200`
accelerated steps. -/
theorem drops_all {m r : Nat} (hm : m < 100) (hr : r ∈ survivorsMod1024) :
    dropsWithin 200 (2 ^ 10 * m + r) = true := by
  rcases Nat.lt_or_ge m 50 with h | h
  · exact drops_of_checkRange check_r0 (by omega) (by omega) hr
  · exact drops_of_checkRange check_r1 (by omega) (by omega) hr

/-- **Every positive `n` below `102 400` reaches `1`.** -/
theorem reachesOne_of_lt_102400 {n : Nat} (hn : 0 < n) (hlt : n < 102400) :
    ReachesOne n := by
  refine reachesOne_of_blocks (M := 100) (fuel := 200)
    (fun m r hm hr => drops_all hm hr) n hn ?_
  have hpow : (2:Nat) ^ 10 * 100 = 102400 := by decide
  omega

/-- A counterexample is at least `102 400`. -/
theorem counterexample_ge_102400 {n : Nat} (hn : 0 < n) (h : ¬ ReachesOne n) :
    102400 ≤ n := by
  by_cases hlt : n < 102400
  · exact absurd (reachesOne_of_lt_102400 hn hlt) h
  · omega

end Search
end Collatz
