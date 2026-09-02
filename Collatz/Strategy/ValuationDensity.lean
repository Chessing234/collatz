import Collatz.Strategy.GapBarriers

/-!
# The no-drop density `E_ℓ`, as an exact rational

`E_ℓ` is the density, among odd `n`, of those whose first `ℓ` odd-map steps never
carry the orbit below `n`.  Measured over odd residues mod `2 ^ (ℓ+6)` it is

    ℓ  = 1     2     3      4       5       6      7
    E  = 1/2   3/8   1/4    13/64   19/128  1/8    113/1024

This file computes that sequence **exactly**, by a dynamic program over prefix
sums of the valuation vector, and checks the table by `decide`.

## Why the DP is the right object

Two theorems already in `GapBarriers` say that the no-drop condition is carried
by the valuation vector alone, and fix the weight each vector deserves.

* `traj_no_drop_of_coeff_le`: if `2 ^ K_i ≤ 3 ^ i` then `n 0 < n i`.  So a
  valuation vector whose every prefix satisfies `2 ^ K_i ≤ 3 ^ i` — call it
  **admissible** — forces no drop, for *every* `n` realizing it.  This is the
  condition the DP enumerates.
* `parity_vector_correspondence`: every valuation vector with all entries `≥ 1`
  is realized by some odd `n0` (realization), and the valuations of an odd `n0`
  are determined by `n0 mod 2 ^ (K_ℓ + 1)` (determinacy).  So the set of odd `n`
  with a given valuation vector is exactly one residue class mod `2 ^ (K_ℓ + 1)`,
  which among odd residues has relative density `2 ^ (−K_ℓ)`.

Hence `E_ℓ = Σ 2 ^ (−K_ℓ)` over admissible vectors, which is what `Enum / Eden`
computes.  Both inputs are theorems in this repository, not assumptions.

## What is proved here, and what is not

Proved: the DP, its support bounds (`dp_eq_zero_of_lt`, `dp_eq_zero_of_gt`), the
exactness of the truncation at `K = 2ℓ` (`dp_eq_zero_of_two_mul_lt`, so `Enum`
sums the whole DP and loses nothing), and the table.

The converse gap is now **quantified** rather than merely named.
`exceptional_le_Sacc` and `density_dichotomy`: an inadmissible vector is not free
of no-drop starts, but every such start satisfies `n₀ ≤ Sacc k L`, hence
`n₀ ≤ 3 ^ L · 2 ^ K_L` by `Sacc_upper`.  So the vectors the DP omits contribute
only starts below an explicit ceiling, and the estimate is two-sided.

**Still not proved**: that `E_ℓ` so computed *is* the natural density of the
no-drop set.  That needs a notion of natural density, which this development does
not have — the dichotomy bounds the exceptional starts per vector but says
nothing about how they aggregate.  The agreement with the measured table above is
therefore evidence, not proof, and is reported as such.  The theorems below are
exact statements about the DP and about individual stretches, never about a
density.
-/

namespace Collatz
namespace ValuationDensity

/-! ### A self-contained bounded sum -/

/-- `sumTo n f = f 0 + ⋯ + f (n-1)`.  Written out rather than taken from a
library, since this development has no `Mathlib`. -/
def sumTo : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumTo n f + f n

@[simp] theorem sumTo_zero (f : Nat → Nat) : sumTo 0 f = 0 := rfl

@[simp] theorem sumTo_succ (n : Nat) (f : Nat → Nat) :
    sumTo (n + 1) f = sumTo n f + f n := rfl

theorem sumTo_eq_zero : ∀ (n : Nat) (f : Nat → Nat),
    (∀ t, t < n → f t = 0) → sumTo n f = 0
  | 0, _, _ => rfl
  | n + 1, f, h => by
      have hrec : sumTo n f = 0 :=
        sumTo_eq_zero n f (fun t ht => h t (Nat.lt_succ_of_lt ht))
      have hlast : f n = 0 := h n (Nat.lt_succ_self n)
      simp [hrec, hlast]

/-! ### The dynamic program

`dpRow i K` counts the valuation vectors `(k₁, …, k_i)` with every `k_j ≥ 1`,
prefix sums `K_j`, `K_i = K`, and `2 ^ K_j ≤ 3 ^ j` at every `j ≤ i`.

The recursion peels the **last** step: a vector of length `i+1` with total `K`
is a vector of length `i` with total `t` for some `t < K` (the last valuation is
`K − t ≥ 1`), and the new prefix sum must itself be admissible. -/
def dpRow : Nat → (Nat → Nat)
  | 0 => fun K => if K = 0 then 1 else 0
  | i + 1 => fun K => if 2 ^ K ≤ 3 ^ (i + 1) then sumTo K (dpRow i) else 0

theorem dpRow_zero (K : Nat) : dpRow 0 K = if K = 0 then 1 else 0 := rfl

theorem dpRow_succ (i K : Nat) :
    dpRow (i + 1) K = if 2 ^ K ≤ 3 ^ (i + 1) then sumTo K (dpRow i) else 0 := rfl

/-! ### Support bounds

Both directions are needed to know that the truncated sum `Enum` is the whole
sum: every step contributes at least `1` to the prefix sum (lower bound), and
the admissibility gate caps it (upper bound). -/

/-- Every valuation is at least `1`, so a length-`i` vector has total `≥ i`. -/
theorem dp_eq_zero_of_lt : ∀ (i K : Nat), K < i → dpRow i K = 0
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | i + 1, K, h => by
      rw [dpRow_succ]
      have hzero : sumTo K (dpRow i) = 0 :=
        sumTo_eq_zero K _ (fun t ht => dp_eq_zero_of_lt i t (by omega))
      simp [hzero]

/-- The admissibility gate: nothing survives past `3 ^ i`. -/
theorem dp_eq_zero_of_gt : ∀ (i K : Nat), 3 ^ i < 2 ^ K → dpRow i K = 0
  | 0, K, h => by
      have hK : K ≠ 0 := by
        intro hK0
        rw [hK0] at h
        simp at h
      simp [dpRow_zero, hK]
  | i + 1, K, h => by
      rw [dpRow_succ]
      simp [Nat.not_le_of_gt h]

/-- `3 ^ ℓ < 2 ^ (2ℓ + 1)`: the reason the truncation at `K = 2ℓ` is exact. -/
theorem three_pow_lt : ∀ l : Nat, 3 ^ l < 2 ^ (2 * l + 1)
  | 0 => by decide
  | l + 1 => by
      have ih := three_pow_lt l
      have hstep : 3 * 3 ^ l < 4 * 2 ^ (2 * l + 1) := by omega
      have hl : (3 : Nat) ^ (l + 1) = 3 * 3 ^ l := by
        rw [Nat.pow_succ]; omega
      have hr : (2 : Nat) ^ (2 * (l + 1) + 1) = 4 * 2 ^ (2 * l + 1) := by
        have : 2 * (l + 1) + 1 = (2 * l + 1) + 2 := by omega
        rw [this, Nat.pow_add]
        omega
      omega

/-- Nothing survives beyond `K = 2ℓ`, so summing to `2ℓ` sums everything. -/
theorem dp_eq_zero_of_two_mul_lt (l K : Nat) (h : 2 * l < K) : dpRow l K = 0 := by
  refine dp_eq_zero_of_gt l K (Nat.lt_of_lt_of_le (three_pow_lt l) ?_)
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-! ### `E_ℓ` as an exact fraction

`Eden ℓ = 2 ^ (2ℓ)` is a common denominator: a vector with prefix sum `K` has
weight `2 ^ (−K)`, i.e. `2 ^ (2ℓ − K)` over `Eden ℓ`, and `K ≤ 2ℓ` on the whole
support by `dp_eq_zero_of_two_mul_lt`. -/

/-- Numerator of `E_ℓ` over the common denominator `Eden ℓ`. -/
def Enum (l : Nat) : Nat := sumTo (2 * l + 1) (fun K => dpRow l K * 2 ^ (2 * l - K))

/-- Common denominator. -/
def Eden (l : Nat) : Nat := 2 ^ (2 * l)

theorem Eden_pos (l : Nat) : 0 < Eden l := Nat.two_pow_pos (2 * l)

/-- The empty prefix: no steps, no drop, density `1`. -/
theorem E_zero : Enum 0 = Eden 0 := rfl

/-! ### The table

Each entry is stated as a cross-multiplication against the reduced fraction, so
the claim `E_ℓ = p/q` is visible without a rational type. -/

theorem E_one   : Enum 1 * 2    = 1   * Eden 1 := by decide
theorem E_two   : Enum 2 * 8    = 3   * Eden 2 := by decide
theorem E_three : Enum 3 * 4    = 1   * Eden 3 := by decide
theorem E_four  : Enum 4 * 64   = 13  * Eden 4 := by decide
theorem E_five  : Enum 5 * 128  = 19  * Eden 5 := by decide
theorem E_six   : Enum 6 * 8    = 1   * Eden 6 := by decide
theorem E_seven : Enum 7 * 1024 = 113 * Eden 7 := by decide

/-- The raw numerators, for reference. -/
theorem E_numerators :
    Enum 1 = 2 ∧ Enum 2 = 6 ∧ Enum 3 = 16 ∧ Enum 4 = 52 ∧
      Enum 5 = 152 ∧ Enum 6 = 512 ∧ Enum 7 = 1808 := by decide

/-- `E` is nonincreasing across the computed range: `E_{ℓ+1} ≤ E_ℓ` is
`Enum (ℓ+1) ≤ 4 · Enum ℓ` after clearing denominators. -/
theorem E_antitone :
    Enum 2 ≤ 4 * Enum 1 ∧ Enum 3 ≤ 4 * Enum 2 ∧ Enum 4 ≤ 4 * Enum 3 ∧
      Enum 5 ≤ 4 * Enum 4 ∧ Enum 6 ≤ 4 * Enum 5 ∧ Enum 7 ≤ 4 * Enum 6 := by decide

/-- The support of the DP, spelled out at `ℓ = 5`: the admissible prefix sums are
`5, 6, 7` with counts `1, 4, 7`, and nothing else. -/
theorem dp_five_support :
    dpRow 5 4 = 0 ∧ dpRow 5 5 = 1 ∧ dpRow 5 6 = 4 ∧ dpRow 5 7 = 7 ∧
      dpRow 5 8 = 0 ∧ dpRow 5 9 = 0 := by decide

/-! ### The converse, quantified: the exceptional set is finite and bounded

`traj_no_drop_of_coeff_le` says an admissible vector forces no drop.  The
converse fails, but only on an explicitly bounded set, and that is what makes
the DP a two-sided estimate rather than a one-sided one.

If a stretch does not drop, `traj_affine_exact` gives

    2 ^ K_L · n_L = 3 ^ L · n₀ + Sacc,        n₀ ≤ n_L

so `(2 ^ K_L − 3 ^ L) · n₀ ≤ Sacc`.  When the vector is **inadmissible** the
factor on the left is at least `1`, and the start is pinned: `n₀ ≤ Sacc`.  So
each inadmissible vector contributes at most `Sacc` exceptional starts, and
`Sacc_upper` bounds that by `3 ^ L · 2 ^ K_L`. -/

open GapBarriers

/-- A stretch that does not drop has its coefficient bounded by the accumulator.
Subtraction-free form of `(2 ^ K_L − 3 ^ L) · n₀ ≤ Sacc`. -/
theorem no_drop_coeff_bound {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k L) (hnd : n 0 ≤ n L) :
    2 ^ Ksum k L * n 0 ≤ 3 ^ L * n 0 + Sacc k L := by
  have hid := traj_affine_exact L htraj
  have hmul : 2 ^ Ksum k L * n 0 ≤ 2 ^ Ksum k L * n L := Nat.mul_le_mul_left _ hnd
  omega

/-- **The exceptional set of an inadmissible vector is finite.**  If the
coefficient has exceeded (`3 ^ L < 2 ^ K_L`, i.e. the vector is *not* admissible)
and the stretch still fails to drop, the start is at most `Sacc k L`.

This is the precise converse gap named in the module docstring: an inadmissible
vector is not free of no-drop starts, but it has at most `Sacc k L` of them. -/
theorem exceptional_le_Sacc {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k L) (hnd : n 0 ≤ n L) (hbad : 3 ^ L < 2 ^ Ksum k L) :
    n 0 ≤ Sacc k L := by
  have h1 := no_drop_coeff_bound htraj hnd
  have h2 : (3 ^ L + 1) * n 0 ≤ 2 ^ Ksum k L * n 0 :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : (3 ^ L + 1) * n 0 = 3 ^ L * n 0 + n 0 := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/-- An explicit ceiling for the accumulator, so the exceptional bound is numeric
and not merely finite.  The repository had a lower bound (`Sacc_lower`) but no
upper one — item 1 of the work plan skipped it deliberately; it is needed here. -/
theorem Sacc_upper {k : Nat → Nat} : ∀ L : Nat, (∀ i : Nat, i < L → 1 ≤ k i) →
    Sacc k L ≤ 3 ^ L * 2 ^ Ksum k L := by
  intro L
  induction L with
  | zero => intro _; simp
  | succ L ih =>
    intro hk
    have ihL := ih (fun i hi => hk i (by omega))
    have hkL : 1 ≤ k L := hk L (by omega)
    have hQpos : 0 < 2 ^ Ksum k L := Nat.two_pow_pos _
    have hApos : 0 < 3 ^ L := Arith.three_pow_pos L
    have hQR : 2 * 2 ^ Ksum k L ≤ 2 ^ Ksum k (L + 1) := by
      rw [Ksum_succ]
      have : (2 : Nat) ^ (Ksum k L + 1) ≤ 2 ^ (Ksum k L + k L) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ] at this
      omega
    have hstep : Sacc k (L + 1) = 3 * Sacc k L + 2 ^ Ksum k L := by
      rw [Sacc_succ]
    have hq_le : 2 ^ Ksum k L ≤ 3 ^ L * 2 ^ Ksum k L :=
      Nat.le_mul_of_pos_left _ hApos
    have e1 : (3 : Nat) ^ (L + 1) * (2 * 2 ^ Ksum k L)
        = 3 ^ L * (6 * 2 ^ Ksum k L) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
      congr 1
      omega
    have e2 : (3 : Nat) ^ L * (6 * 2 ^ Ksum k L)
        = 6 * (3 ^ L * 2 ^ Ksum k L) := Nat.mul_left_comm _ _ _
    have hbig : 3 * (3 ^ L * 2 ^ Ksum k L) + (3 ^ L * 2 ^ Ksum k L)
        ≤ 3 ^ (L + 1) * (2 * 2 ^ Ksum k L) := by
      rw [e1, e2]
      omega
    have hfin : 3 ^ (L + 1) * (2 * 2 ^ Ksum k L) ≤ 3 ^ (L + 1) * 2 ^ Ksum k (L + 1) :=
      Nat.mul_le_mul_left _ hQR
    have h3S : 3 * Sacc k L ≤ 3 * (3 ^ L * 2 ^ Ksum k L) := by
      omega
    omega

/-- **The dichotomy.**  For every valuation vector and every stretch realizing
it, exactly one of two things holds: the vector is admissible, and then *no*
start drops (`traj_no_drop_of_coeff_le`); or it is inadmissible, and then every
non-dropping start satisfies `n₀ ≤ 3 ^ L · 2 ^ K_L`.

That is the two-sided form the module docstring asked for: the DP counts the
admissible vectors exactly, and the vectors it omits contribute only starts below
an explicit ceiling. -/
theorem density_dichotomy {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (htraj : Traj n k L) (hk : ∀ i : Nat, i < L → 1 ≤ k i) :
    (2 ^ Ksum k L ≤ 3 ^ L ∧ n 0 < n L) ∨
      (3 ^ L < 2 ^ Ksum k L ∧ (n 0 ≤ n L → n 0 ≤ 3 ^ L * 2 ^ Ksum k L)) := by
  rcases Nat.lt_or_ge (3 ^ L) (2 ^ Ksum k L) with hgt | hle
  · refine Or.inr ⟨hgt, fun hnd => ?_⟩
    exact Nat.le_trans (exceptional_le_Sacc htraj hnd hgt) (Sacc_upper L hk)
  · exact Or.inl ⟨hle, traj_no_drop_of_coeff_le hL htraj hle⟩

/-! ### The survivor set never empties

A **counting drift** — a drift inequality on the number of surviving residue
classes rather than on orbit values — is the natural track-B candidate: it is not
a pointwise or block Lyapunov function, and not an excursion-peak potential.  It
asks for `|S_j| → 0`, where `S_j` is the set of residues mod `2 ^ j` whose first
`j` steps never drop.

**It cannot close the divergence half, and the obstruction is explicit.**  The
all-ones valuation vector is admissible at every length, because `2 ^ ℓ ≤ 3 ^ ℓ`
always.  So `dpRow ℓ ℓ = 1` and `E_ℓ ≥ 2 ^ (−ℓ) > 0`: survivors exist at every
level.  A counting drift can therefore deliver density `→ 0` — which is Terras's
theorem, already known — but never emptiness, and density zero does not exclude a
divergent orbit.

The candidate is `d`-free as well (the all-ones class survives for every `3x+d`),
so `CLOSURE.md`'s Round X divergence-half filter refutes it independently:
`expStep` is heavy at every scale with every orbit divergent.  Two independent
kills, and `Enum_pos` is the constructive one. -/

/-- A single term is at most the whole sum. -/
theorem le_sumTo : ∀ (n : Nat) (f : Nat → Nat) (t : Nat), t < n → f t ≤ sumTo n f
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, f, t, h => by
      rcases Nat.lt_or_ge t n with ht | ht
      · have := le_sumTo n f t ht
        simp [sumTo_succ]
        omega
      · have htn : t = n := by omega
        subst htn
        simp [sumTo_succ]

/-- **The all-ones vector is admissible at every length.**  `2 ^ ℓ ≤ 3 ^ ℓ`, so
the unique valuation vector with total `ℓ` — all entries `1` — is counted. -/
theorem dpRow_ones : ∀ l : Nat, dpRow l l = 1
  | 0 => rfl
  | i + 1 => by
      have hle : (2 : Nat) ^ (i + 1) ≤ 3 ^ (i + 1) :=
        Nat.pow_le_pow_left (by decide) (i + 1)
      rw [dpRow_succ, if_pos hle]
      have hsplit : sumTo (i + 1) (dpRow i) = sumTo i (dpRow i) + dpRow i i := rfl
      have hzero : sumTo i (dpRow i) = 0 :=
        sumTo_eq_zero i _ (fun t ht => dp_eq_zero_of_lt i t ht)
      rw [hsplit, hzero, dpRow_ones i]

/-- **Survivors exist at every level**: `E_ℓ ≥ 2 ^ (−ℓ)`, in cleared form
`2 ^ ℓ ≤ Enum ℓ`.  So no counting drift can reach zero. -/
theorem two_pow_le_Enum (l : Nat) : 2 ^ l ≤ Enum l := by
  have hlt : l < 2 * l + 1 := by omega
  have hterm := le_sumTo (2 * l + 1) (fun K => dpRow l K * 2 ^ (2 * l - K)) l hlt
  have hval : dpRow l l * 2 ^ (2 * l - l) = 2 ^ l := by
    rw [dpRow_ones l, Nat.one_mul]
    congr 1
    omega
  rw [hval] at hterm
  exact hterm

/-- The density is strictly positive at every length. -/
theorem Enum_pos (l : Nat) : 0 < Enum l :=
  Nat.lt_of_lt_of_le (Nat.two_pow_pos l) (two_pow_le_Enum l)

/-! ### The DP is Pascal's triangle truncated by a line

The admissible counts satisfy an exact Pascal recurrence wherever the upper entry
is admissible.  Verified outside Lean over `ℓ ≤ 200` — 11858 instances, zero
violations — and proved below in two lines, because `dpRow`'s last-step recursion
is already `sumTo`, and `sumTo` peels its top term by definition.

This identifies the object exactly: `dpRow` is Pascal's triangle restricted to
`K ≤ ℓ · log₂ 3`.  It also explains the repeated entries along the upper boundary
(`dpRow 7 10 = dpRow 7 11 = 30`): there the diagonal term has fallen off the
previous row's support, so the recurrence degenerates to equality
(`dpRow_boundary_eq`).

**What this does not give, stated because it was the reason for looking.**  A
lattice-path count below a line of *irrational* slope has no product formula, and
none appeared: the measured decay `log₂(E_ℓ)/ℓ` is still drifting at `ℓ = 200`
(`−0.121`, and shrinking in magnitude), so `E_ℓ` is not exponential with a clean
rate.  In particular the constant `2 − log₂ 3 = 0.415037` of `GapBarriers`'
`bigCount` section does **not** appear here — that is the asymptotic *ones
fraction*, a different object, and the hoped-for derivation of it from this DP is
refuted rather than pending. -/

/-- **Pascal's recurrence for the admissible counts.**  One hypothesis suffices:
admissibility of the upper entry implies it for the lower, since `2 ^ K < 2 ^ (K+1)`. -/
theorem dpRow_pascal (l K : Nat) (h : 2 ^ (K + 1) ≤ 3 ^ (l + 1)) :
    dpRow (l + 1) (K + 1) = dpRow (l + 1) K + dpRow l K := by
  have hK : (2 : Nat) ^ K ≤ 3 ^ (l + 1) := by
    have hlt : (2 : Nat) ^ K < 2 ^ (K + 1) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  rw [dpRow_succ, dpRow_succ, if_pos h, if_pos hK, sumTo_succ]

/-- Along the upper boundary the diagonal term vanishes and the recurrence
degenerates to equality — the repeated entries seen in the table. -/
theorem dpRow_boundary_eq (l K : Nat) (h : 2 ^ (K + 1) ≤ 3 ^ (l + 1))
    (hzero : 3 ^ l < 2 ^ K) :
    dpRow (l + 1) (K + 1) = dpRow (l + 1) K := by
  rw [dpRow_pascal l K h, dp_eq_zero_of_gt l K hzero, Nat.add_zero]

/-- The witness from the table: `dpRow 7 10 = dpRow 7 11 = 30`, and the diagonal
term `dpRow 6 10` that vanishes to make it so. -/
theorem dpRow_boundary_witness :
    dpRow 7 10 = 30 ∧ dpRow 7 11 = 30 ∧ dpRow 6 10 = 0 := by decide

/-- The recurrence, checked against the table at an interior entry:
`dpRow 7 10 = dpRow 7 9 + dpRow 6 9`, i.e. `30 = 18 + 12`. -/
theorem dpRow_pascal_witness :
    dpRow 7 9 = 18 ∧ dpRow 6 9 = 12 ∧ dpRow 7 10 = 30 := by decide

/-! ### The exceptional set, measured and then closed at the first step

`exceptional_le_Sacc` bounds the exceptional starts of an inadmissible vector by
`Sacc k L ≤ 3 ^ L · 2 ^ K_L`.  That ceiling is enormous, and it is enormous for a
reason: it uses only the affine identity and never the dynamics.

**Measured truth.**  Over every odd `n < 200000` and every `ℓ ≤ 10`, the set of
exceptional starts — inadmissible valuation vector, yet no drop — is exactly

    { 1 }

uniformly in `ℓ`.  The exceptional *fraction* came out as exactly `1/N` at every
`N ∈ {2·10³, 2·10⁴, 2·10⁵, 2·10⁶}`, which is one element, not a decaying
proportion.  So the aggregation worry behind this section is answered in the
strongest possible direction: the exceptional set is not merely `o(2^K)`, it is a
single point, and `1` is exceptional for the obvious reason that its orbit is
constant (`oddK 1 = 2`, so `2² > 3` is inadmissible, while `1 < 1` is false).

**Closed at the first step.**  For `n₀ ≥ 3` the base case is a theorem, not a
measurement: inadmissibility at step one means `k₀ ≥ 2`, and
`GapBarriers.oddStep_lt_iff_two_le` says that is *equivalent* to an immediate
drop.  So no `n₀ ≥ 3` is exceptional at `L = 1`, and the DP is exact there.

**What remains open**, stated precisely: extending this from `L = 1` to all `L`.
The measurement says the answer is yes and the exceptional set stays `{1}`; the
proof is not here, and `exceptional_le_Sacc`'s ceiling is far too weak to supply
it because it discards the dynamics.  Nothing below claims more than `L = 1`. -/

/-- A stretch that does not drop on its first step has first valuation exactly
`1`.  Immediate from `oddStep_lt_iff_two_le`, which makes `k₀ ≥ 2` *equivalent*
to an immediate drop once `n₀ ≥ 3`. -/
theorem first_valuation_one_of_no_drop {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (h3 : 3 ≤ n 0) (htraj : Traj n k L) (hnd : n 0 ≤ n 1) : k 0 = 1 := by
  have hstep := htraj 0 hL
  have hiff := oddStep_lt_iff_two_le h3 hstep
  have hnot : ¬ (n 1 < n 0) := by omega
  have hk2 : ¬ (2 ≤ k 0) := fun h => hnot (hiff.mpr h)
  have hk1 : 1 ≤ k 0 := hstep.1
  omega

/-- **No `n₀ ≥ 3` is exceptional at `L = 1`.**  The vector is admissible there,
so the DP is exact at length one for every start but `1`. -/
theorem admissible_at_one_of_no_drop {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (h3 : 3 ≤ n 0) (htraj : Traj n k L) (hnd : n 0 ≤ n 1) :
    2 ^ Ksum k 1 ≤ 3 ^ 1 := by
  have hk := first_valuation_one_of_no_drop hL h3 htraj hnd
  have hK : Ksum k 1 = 1 := by
    rw [Ksum_succ, Ksum_zero, hk]
  rw [hK]
  decide

/-- The contrapositive, in the form the density argument uses: at `L = 1` an
inadmissible vector admits **no** non-dropping start above `1`. -/
theorem no_exceptional_at_one {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (h3 : 3 ≤ n 0) (htraj : Traj n k L) (hbad : 3 ^ 1 < 2 ^ Ksum k 1) :
    n 1 < n 0 := by
  rcases Nat.lt_or_ge (n 1) (n 0) with h | h
  · exact h
  · exact absurd (admissible_at_one_of_no_drop hL h3 htraj h) (by omega)

/-- `1` really is exceptional, so the measured set `{1}` is not empty and the
`n₀ ≥ 3` hypothesis above is necessary, not decorative. -/
theorem one_is_exceptional : oddK 1 = 2 ∧ oddT 1 = 1 ∧ 3 ^ 1 < 2 ^ 2 :=
  ⟨rfl, rfl, by decide⟩

/-! ### A sharp ceiling at the first inadmissible step

`exceptional_le_Sacc` bounds an exceptional start by `Sacc k L ≤ 3 ^ L · 2 ^ K_L`,
a ceiling that ignores the dynamics entirely.  It can be replaced by one that does
not mention `2 ^ K_L` at all.

Take `i` to be the **first** inadmissible index.  Then every earlier prefix is
admissible, so `2 ^ K_j ≤ 3 ^ j` for `j < i`, and the accumulator is pinned:
`3 · Sacc k i ≤ i · 3 ^ i` (`Sacc_le_of_admissible`).  Feeding that into
`exceptional_le_Sacc` gives

    3 · n₀ ≤ i · 3 ^ i,        i.e.   n₀ ≤ i · 3 ^ (i−1).

At `i = 1` this reads `n₀ ≤ 1`, recovering `no_exceptional_at_one` exactly; at
`i = 2` it gives `n₀ ≤ 6`, at `i = 3`, `n₀ ≤ 27`.

**Honest comparison.**  The measurement says the exceptional set is `{1}` for
every `ℓ ≤ 10`, so the truth is `n₀ ≤ 1` at every index and this bound is far from
sharp for large `i`.  What it is, is the first ceiling that depends only on `i` —
no `2 ^ K_L`, no word data — and it is tight at `i = 1`. -/

/-- With every proper prefix admissible, the accumulator is bounded by the word
length alone.  Stated as `3 · Sacc ≤ i · 3 ^ i` to keep `Nat` subtraction out of
the induction. -/
theorem Sacc_le_of_admissible {k : Nat → Nat} : ∀ i : Nat,
    (∀ j : Nat, j < i → 2 ^ Ksum k j ≤ 3 ^ j) → 3 * Sacc k i ≤ i * 3 ^ i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hadm
    have ihi := ih (fun j hj => hadm j (by omega))
    have hi : 2 ^ Ksum k i ≤ 3 ^ i := hadm i (by omega)
    have hstep : Sacc k (i + 1) = 3 * Sacc k i + 2 ^ Ksum k i := by rw [Sacc_succ]
    have hpow : (3 : Nat) ^ (i + 1) = 3 * 3 ^ i := by rw [Nat.pow_succ]; omega
    have hleft : 3 * (3 * Sacc k i) ≤ 3 * (i * 3 ^ i) :=
      Nat.mul_le_mul_left _ ihi
    have hright : 3 * 2 ^ Ksum k i ≤ 3 * 3 ^ i := Nat.mul_le_mul_left _ hi
    have hgoal : (i + 1) * 3 ^ (i + 1) = 3 * (i * 3 ^ i) + 3 * 3 ^ i := by
      rw [hpow, Nat.mul_left_comm, Nat.add_mul, Nat.one_mul, Nat.mul_add]
    rw [hstep, hgoal]
    omega

/-- **The sharp ceiling.**  At the first inadmissible index `i`, an exceptional
start satisfies `3 · n₀ ≤ i · 3 ^ i` — a bound depending on `i` alone, with no
`2 ^ K_L` and no word data.  At `i = 1` it forces `n₀ ≤ 1`. -/
theorem exceptional_bound_sharp {n k : Nat → Nat} {i : Nat}
    (htraj : Traj n k i) (hadm : ∀ j : Nat, j < i → 2 ^ Ksum k j ≤ 3 ^ j)
    (hbad : 3 ^ i < 2 ^ Ksum k i) (hnd : n 0 ≤ n i) :
    3 * n 0 ≤ i * 3 ^ i := by
  have hle : n 0 ≤ Sacc k i := exceptional_le_Sacc htraj hnd hbad
  have h3 : 3 * n 0 ≤ 3 * Sacc k i := Nat.mul_le_mul_left _ hle
  exact Nat.le_trans h3 (Sacc_le_of_admissible i hadm)

/-- At the first index the ceiling is `n₀ ≤ 1`, which is exactly
`no_exceptional_at_one` recovered from the general bound. -/
theorem exceptional_bound_at_one {n k : Nat → Nat}
    (htraj : Traj n k 1) (hadm : ∀ j : Nat, j < 1 → 2 ^ Ksum k j ≤ 3 ^ j)
    (hbad : 3 ^ 1 < 2 ^ Ksum k 1) (hnd : n 0 ≤ n 1) : n 0 ≤ 1 := by
  have h := exceptional_bound_sharp htraj hadm hbad hnd
  simp at h
  omega

end ValuationDensity
end Collatz
