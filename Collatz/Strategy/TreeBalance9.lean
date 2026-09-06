import Collatz.Strategy.TreeBranching
import Collatz.Strategy.TreeHalf
import Collatz.Strategy.TreeStochastic

/-!
# A tree of `1` balanced modulo `9` is a fat tree of `1`

**Novelty tag: NEW (conditional theorem; Round LXXVII).**  The one-hypothesis
form of `Strategy/TreeBalance`: only the 3-adic balance is assumed, and the
advanced terms of Krasikov–Lagarias are handled by expanding them to depth
`10` inside the certificate (their back-substitution, made finite and
kernel-checked) instead of by a 2-adic hypothesis.

Let `T` be the set of positive integers whose accelerated orbit reaches `1`
(any number of steps).  `M c X` counts its odd members below `X` in class
`c mod 3`, `N9 R X` those in class `R mod 9`.

* `Equi`: for `X ≥ 2^20` and every fertile `R mod 9`,
  `97 · M (R mod 3) X ≤ 300 · N9 R X` — each class mod `9` carries at least
  `1/3 − 1/100` of its class mod `3`.

**Theorem** (`count_balance9`): `Equi → ∀ N ≥ 1,
N ^ 21 < 20 ^ 21 · 10 ^ 1375 · (reachCount N) ^ 25` — at least `c · N ^ 0.84`
integers up to `N` reach `1`.  Contrapositive: a thin tree of `1` is
unbalanced modulo `9` inside some class modulo `3`, by more than `1/100`,
at infinitely many scales.

## Method

Every odd member `n` of `T` in class `c` is the child `(2^v m − 1)/3` of the
member `m = (3n+1)/2^v ≤ (3X+1)/2^v` in class `parentRes c v (mod 9)`, and
distinct `(m, v)` give distinct children (`family`).  With `Equi`, and
`Mm X := min (M 1 X) (M 2 X)`, this is the recursion

    300 · Mm X ≥ 97 · Σ_{v=1}^{16} Mm ((3X+1)/2^v)                    (R)

whose `v = 1` term is at the larger scale `3X/2`.  On the lattice of scales
`3^j 2^y`, a node at depth `d` with total valuation `V` sits at
`3^(j+d) 2^(y−V)`, *advanced* when `2^V ≤ 3^d`.  `expand` applies (R) to
every advanced node up to depth `10` (`A d V` counts the paths of depth `d`,
total valuation `V`, with all proper prefixes advanced; it is a literal table
whose recursion `A_rec` the kernel checks) and keeps the retarded nodes as
leaves; the advanced frontier at depth `10` is dropped.  Each retarded leaf
has a strictly smaller bound, so the absolute-bound induction of
`Devices/AbsoluteBound.md` applies with the `19/12` lattice of
`TreeBalance`; the certificate `cert` is one inequality at ratio
`(21/20)^12 = 2^0.8447` with `3 %` slack.
-/

set_option exponentiation.threshold 5000
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Collatz
namespace TreeBalance9

open TreeCount TreeBranching Collatz.Sum TreeStochastic Classical

/-! ## 1. Reachability, counts, the hypothesis -/

def ReachOne (n : Nat) : Prop := ∃ t, acceleratedOrbit t n = 1

def K : Nat := 10 ^ 55

noncomputable def M (c X : Nat) : Nat :=
  countUpTo (fun n => n % 2 = 1 ∧ n % 3 = c ∧ ReachOne n) X

noncomputable def N9 (R X : Nat) : Nat :=
  countUpTo (fun n => n % 2 = 1 ∧ n % 9 = R ∧ ReachOne n) X

noncomputable def Mm (X : Nat) : Nat := min (M 1 X) (M 2 X)

/-- The number of positive integers up to `N` reaching `1`. -/
noncomputable def reachCount (N : Nat) : Nat := countUpTo (fun n => 0 < n ∧ ReachOne n) N

/-- **3-adic balance** to `1/100`, above `2^20`. -/
def Equi : Prop :=
  ∀ X, 2 ^ 20 ≤ X → ∀ R, R < 9 → R % 3 ≠ 0 → 97 * M (R % 3) X ≤ 300 * N9 R X

def parentRes (c v : Nat) : Nat := (2 ^ (6 - v % 6) * (3 * c + 1)) % 9

def Y (X v : Nat) : Nat := (3 * X + 1) / 2 ^ v

theorem M_mono {c X X' : Nat} (h : X ≤ X') : M c X ≤ M c X' := countUpTo_le_of_le h

theorem Mm_mono {X X' : Nat} (h : X ≤ X') : Mm X ≤ Mm X' :=
  Nat.le_min.2 ⟨Nat.le_trans (Nat.min_le_left _ _) (M_mono h),
    Nat.le_trans (Nat.min_le_right _ _) (M_mono h)⟩

theorem one_le_countUpTo {P : Nat → Prop} [∀ a, Decidable (P a)] {k X : Nat}
    (hk : 1 ≤ k) (hkX : k ≤ X) (hP : P k) : 1 ≤ countUpTo P X := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h1 : countUpTo P (k' + 1) = countUpTo P k' + (if P (k' + 1) then 1 else 0) := rfl
  have h2 := countUpTo_le_of_le (p := P) hkX
  rw [h1, if_pos hP] at h2
  omega

theorem Mm_pos {X : Nat} (hX : 5 ≤ X) : 1 ≤ Mm X := by
  apply Nat.le_min.2
  constructor
  · exact one_le_countUpTo (k := 1) (by decide) (by omega) ⟨rfl, rfl, ⟨0, rfl⟩⟩
  · exact one_le_countUpTo (k := 5) (by decide) hX ⟨rfl, rfl, ⟨4, by decide⟩⟩

/-! ## 2. Residues -/

theorem two_pow_mod_nine_aux (q r : Nat) : 2 ^ (6 * q + r) % 9 = 2 ^ r % 9 := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
  have h64 : (2:Nat) ^ 6 % 9 = 1 := by decide
  rw [h64, Nat.one_pow, show (1:Nat) % 9 = 1 from rfl, Nat.one_mul, Nat.mod_mod]

theorem two_pow_mod_nine (v : Nat) : 2 ^ v % 9 = 2 ^ (v % 6) % 9 := by
  have h := two_pow_mod_nine_aux (v / 6) (v % 6)
  have e : 2 ^ v = 2 ^ (6 * (v / 6) + v % 6) := by rw [Nat.div_add_mod]
  rw [e]
  exact h

theorem two_pow_mod_three (k : Nat) : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> simp

theorem parentRes_lt (c v : Nat) : parentRes c v < 9 := Nat.mod_lt _ (by decide)

theorem parentRes_mod_three (c v : Nat) : parentRes c v % 3 ≠ 0 := by
  unfold parentRes
  rw [Nat.mod_mod_of_dvd _ (⟨3, rfl⟩ : (3:Nat) ∣ 9), Nat.mul_mod]
  have h3c : (3 * c + 1) % 3 = 1 := by omega
  rw [h3c]
  rcases two_pow_mod_three (6 - v % 6) with h | h <;> rw [h] <;> decide

theorem parentRes_class (c v : Nat) : parentRes c v % 3 = 1 ∨ parentRes c v % 3 = 2 := by
  have := parentRes_mod_three c v
  have := Nat.mod_lt (parentRes c v) (show 0 < 3 by decide)
  omega

theorem parent_pow_mod {c v m : Nat} (hm : m % 9 = parentRes c v) :
    (2 ^ v * m) % 9 = (3 * c + 1) % 9 := by
  unfold parentRes at hm
  have hp := two_pow_mod_nine v
  have h6 : v % 6 + (6 - v % 6) = 6 := by
    have := Nat.mod_lt v (show 0 < 6 by decide); omega
  calc (2 ^ v * m) % 9 = ((2 ^ v % 9) * (m % 9)) % 9 := Nat.mul_mod _ _ _
    _ = ((2 ^ (v % 6) % 9) * ((2 ^ (6 - v % 6) * (3 * c + 1)) % 9)) % 9 := by rw [hp, hm]
    _ = (2 ^ (v % 6) * (2 ^ (6 - v % 6) * (3 * c + 1))) % 9 := by rw [← Nat.mul_mod]
    _ = (2 ^ 6 * (3 * c + 1)) % 9 := by rw [← Nat.mul_assoc, ← Nat.pow_add, h6]
    _ = (3 * c + 1) % 9 := by
        have : (2:Nat) ^ 6 = 64 := by decide
        rw [this]; omega

theorem child_props {c v m : Nat} (hc : c = 1 ∨ c = 2) (hv : 1 ≤ v)
    (hm : m % 9 = parentRes c v) (hpos : 1 ≤ m) :
    (2 ^ v * m) % 3 = 1 ∧ child m v % 3 = c ∧ 1 ≤ child m v := by
  have h9 := parent_pow_mod hm
  have h2 : 2 ≤ 2 ^ v := by
    calc (2:Nat) = 2 ^ 1 := rfl
      _ ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hv
  have hx : 2 ≤ 2 ^ v * m := by
    have := Nat.mul_le_mul h2 hpos
    omega
  unfold child
  generalize hxx : 2 ^ v * m = x at h9 hx ⊢
  rcases hc with rfl | rfl <;> omega

theorem odd_pow_eq {a b i j : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (h : 2 ^ i * a = 2 ^ j * b) : i = j := by
  rcases Nat.lt_or_ge i j with hij | hij
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, j = i + (d + 1) := ⟨j - i - 1, by omega⟩
    rw [Nat.pow_add, Nat.mul_assoc] at h
    have h' : a = 2 ^ (d + 1) * b := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) h
    rw [two_pow_succ_mul] at h'
    omega
  · rcases Nat.lt_or_ge j i with hji | hji
    · exfalso
      obtain ⟨d, rfl⟩ : ∃ d, i = j + (d + 1) := ⟨i - j - 1, by omega⟩
      rw [Nat.pow_add, Nat.mul_assoc] at h
      have h' : 2 ^ (d + 1) * a = b := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) h
      rw [two_pow_succ_mul] at h'
      omega
    · omega

/-! ## 3. The recursion (R) -/

theorem child_into {c v m X : Nat} (hc : c = 1 ∨ c = 2) (hv : 1 ≤ v)
    (hm1 : 1 ≤ m) (hmY : m ≤ Y X v)
    (hP : m % 2 = 1 ∧ m % 9 = parentRes c v ∧ ReachOne m) :
    1 ≤ child m v ∧ child m v ≤ X ∧
      (child m v % 2 = 1 ∧ child m v % 3 = c ∧ ReachOne (child m v)) := by
  obtain ⟨_, hm9, ⟨t, ht⟩⟩ := hP
  obtain ⟨h3, hc3, hc1⟩ := child_props hc hv hm9 hm1
  have heq := child_eq h3
  have hle : 2 ^ v * m ≤ 3 * X + 1 := by
    unfold Y at hmY
    have := (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).1 hmY
    rw [Nat.mul_comm] at this
    exact this
  refine ⟨hc1, by omega, child_odd hv h3, hc3, ⟨t + v, ?_⟩⟩
  rw [← acceleratedOrbit_add, orbit_child hv h3, ht]

theorem family {c X : Nat} (hc : c = 1 ∨ c = 2) :
    sumRange 16 (fun i => N9 (parentRes c (i + 1)) (Y X (i + 1))) ≤ M c X := by
  unfold N9 M
  apply family_count (f := fun i m => child m (i + 1))
    (P := fun i m => m % 2 = 1 ∧ m % 9 = parentRes c (i + 1) ∧ ReachOne m)
    (Y := fun i => Y X (i + 1))
  · intro i hi a b ha1 haY hb1 hbY hPa hPb hab
    have ea := child_eq (child_props hc (by omega) hPa.2.1 ha1).1
    have eb := child_eq (child_props hc (by omega) hPb.2.1 hb1).1
    have : 2 ^ (i + 1) * a = 2 ^ (i + 1) * b := by omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) this
  · intro i j hi hj hij a b ha1 haY hb1 hbY hPa hPb hab
    have ea := child_eq (child_props hc (by omega) hPa.2.1 ha1).1
    have eb := child_eq (child_props hc (by omega) hPb.2.1 hb1).1
    have : 2 ^ (i + 1) * a = 2 ^ (j + 1) * b := by omega
    have := odd_pow_eq hPa.1 hPb.1 this
    omega
  · intro i hi a ha1 haY hPa
    exact child_into hc (by omega) ha1 haY hPa

theorem count_rec (hE : Equi) {X : Nat} (hX : 2 ^ 36 ≤ X) :
    97 * sumRange 16 (fun i => Mm (Y X (i + 1))) ≤ 300 * Mm X := by
  have hY : ∀ i, i < 16 → 2 ^ 20 ≤ Y X (i + 1) := by
    intro i hi
    unfold Y
    rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))]
    have h1 : 2 ^ (i + 1) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 20 * 2 ^ (i + 1) ≤ 2 ^ 20 * 2 ^ 16 := Nat.mul_le_mul_left _ h1
    have h3 : (2:Nat) ^ 20 * 2 ^ 16 = 2 ^ 36 := by decide
    omega
  have key : ∀ c, (c = 1 ∨ c = 2) →
      97 * sumRange 16 (fun i => Mm (Y X (i + 1))) ≤ 300 * M c X := by
    intro c hc
    have hfam := family (X := X) hc
    have hE' : ∀ i, i < 16 →
        97 * Mm (Y X (i + 1)) ≤ 300 * N9 (parentRes c (i + 1)) (Y X (i + 1)) := by
      intro i hi
      have h1 := hE (Y X (i + 1)) (hY i hi) (parentRes c (i + 1)) (parentRes_lt c (i + 1))
        (parentRes_mod_three c (i + 1))
      have h2 : Mm (Y X (i + 1)) ≤ M (parentRes c (i + 1) % 3) (Y X (i + 1)) := by
        rcases parentRes_class c (i + 1) with h | h <;> rw [h]
        · exact Nat.min_le_left _ _
        · exact Nat.min_le_right _ _
      have := Nat.mul_le_mul_left 97 h2
      omega
    have hsum := sumRange_le hE'
    rw [sumRange_const_mul, sumRange_const_mul] at hsum
    have := Nat.mul_le_mul_left 300 hfam
    omega
  rcases Nat.le_total (M 1 X) (M 2 X) with h | h
  · rw [show Mm X = M 1 X from Nat.min_eq_left h]; exact key 1 (Or.inl rfl)
  · rw [show Mm X = M 2 X from Nat.min_eq_right h]; exact key 2 (Or.inr rfl)

theorem Y_ge {j y v : Nat} (hv : v ≤ y) : 3 ^ (j + 1) * 2 ^ (y - v) ≤ Y (3 ^ j * 2 ^ y) v := by
  unfold Y
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))]
  have e2 : 2 ^ y = 2 ^ (y - v) * 2 ^ v := by
    rw [← Nat.pow_add]; congr 1; omega
  have : 3 ^ (j + 1) * 2 ^ (y - v) * 2 ^ v = 3 * (3 ^ j * 2 ^ y) := by
    rw [e2, Nat.pow_succ]; ac_rfl
  omega

/-- (R) on the lattice: root `3^j 2^y`, children `3^(j+1) 2^(y−v)`. -/
theorem rec_lattice (hE : Equi) {j y : Nat} (hy : 36 ≤ y) :
    97 * sumRange 16 (fun i => Mm (3 ^ (j + 1) * 2 ^ (y - (i + 1)))) ≤ 300 * Mm (3 ^ j * 2 ^ y) := by
  have hX : 2 ^ 36 ≤ 3 ^ j * 2 ^ y := by
    have h1 : 1 ≤ 3 ^ j := Nat.pow_pos (by decide)
    have h2 : 2 ^ 36 ≤ 2 ^ y := Nat.pow_le_pow_right (by decide) hy
    have := Nat.mul_le_mul h1 h2
    rw [Nat.one_mul] at this
    exact this
  have h := count_rec hE hX
  have hmono : sumRange 16 (fun i => Mm (3 ^ (j + 1) * 2 ^ (y - (i + 1))))
      ≤ sumRange 16 (fun i => Mm (Y (3 ^ j * 2 ^ y) (i + 1))) :=
    sumRange_le (fun i hi => Mm_mono (Y_ge (by omega)))
  have := Nat.mul_le_mul_left 97 hmono
  omega

/-! ## 4. The path table -/

/-- A node at depth `d`, total valuation `V`, is *advanced* when `2^V ≤ 3^d`. -/
def adv (d V : Nat) : Bool := decide (2 ^ V ≤ 3 ^ d)

/-- `tbl[d][V]`: the number of valuation words of depth `d` and total `V` all
of whose proper prefixes are advanced (valuations `1 … 16`). -/
def tbl : List (List Nat) := [[1],
  [0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,1,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,1,4,7,7,7,7,7,7,7,7,7,7,7,7,7,7,6,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,1,5,12,12,12,12,12,12,12,12,12,12,12,12,12,12,11,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,1,6,18,30,30,30,30,30,30,30,30,30,30,30,30,30,29,24,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,1,7,25,55,85,85,85,85,85,85,85,85,85,85,85,85,84,78,60,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,1,8,33,88,173,173,173,173,173,173,173,173,173,173,173,173,172,165,140,85,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,1,9,42,130,303,476,476,476,476,476,476,476,476,476,476,476,475,467,434,346,173,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]

def A (d V : Nat) : Nat := (tbl.getD d []).getD V 0

theorem A_zero (V : Nat) : A 0 V = if V = 0 then 1 else 0 := by
  cases V with
  | zero => rfl
  | succ V => rfl

theorem tbl_len : ∀ d, d ≤ 10 → (tbl.getD d []).length = 16 * d + 1 := by decide +kernel

theorem A_beyond {d V : Nat} (hd : d ≤ 10) (hV : 16 * d < V) : A d V = 0 := by
  unfold A
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.2 (by rw [tbl_len d hd]; omega)]
  rfl

theorem A_rec : ∀ d, d < 10 → ∀ V, V ≤ 16 * (d + 1) →
    A (d + 1) V = sumRange 16 (fun i =>
      if i + 1 ≤ V ∧ adv d (V - (i + 1)) then A d (V - (i + 1)) else 0) := by
  decide +kernel

theorem A_rec_all {d : Nat} (hd : d < 10) (V : Nat) :
    A (d + 1) V = sumRange 16 (fun i =>
      if i + 1 ≤ V ∧ adv d (V - (i + 1)) then A d (V - (i + 1)) else 0) := by
  rcases Nat.lt_or_ge (16 * (d + 1)) V with h | h
  · rw [A_beyond (by omega) h]
    have : sumRange 16 (fun i => if i + 1 ≤ V ∧ adv d (V - (i + 1)) then A d (V - (i + 1)) else 0)
        = sumRange 16 (fun _ => 0) :=
      sumRange_congr (fun i hi => by
        by_cases hc : i + 1 ≤ V ∧ adv d (V - (i + 1))
        · rw [if_pos hc, A_beyond (by omega) (by omega)]
        · rw [if_neg hc])
    rw [this, sumRange_const, Nat.mul_zero]
  · exact A_rec d hd V h

/-- Retarded leaves have strictly smaller bounds: `19 d < 12 V`. -/
theorem retarded_weight : ∀ d, d ≤ 10 → 1 ≤ d → ∀ V, V ≤ 160 → adv d V = false → 19 * d < 12 * V := by
  decide +kernel

theorem retarded_lt {j y d V : Nat} (h : adv d V = false) (hV : V ≤ y) :
    3 ^ (j + d) * 2 ^ (y - V) < 3 ^ j * 2 ^ y := by
  have h' : 3 ^ d < 2 ^ V := by
    have := of_decide_eq_false h
    omega
  have e2 : 2 ^ y = 2 ^ (y - V) * 2 ^ V := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e2, Nat.pow_add]
  have hp : 0 < 3 ^ j * 2 ^ (y - V) := Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  calc 3 ^ j * 3 ^ d * 2 ^ (y - V) = (3 ^ j * 2 ^ (y - V)) * 3 ^ d := by ac_rfl
    _ < (3 ^ j * 2 ^ (y - V)) * 2 ^ V := Nat.mul_lt_mul_of_pos_left h' hp
    _ = 3 ^ j * (2 ^ (y - V) * 2 ^ V) := by ac_rfl

/-! ## 5. Sums: a convolution -/

theorem sumRange_mul_const (n : Nat) (f : Nat → Nat) (c : Nat) :
    sumRange n (fun i => f i * c) = sumRange n f * c := by
  rw [Nat.mul_comm, ← sumRange_const_mul]
  exact sumRange_congr (fun i _ => Nat.mul_comm _ _)

/-- Re-indexing `Σ_V c V Σ_{i<16} g (V + i + 1)` as a sum over `V' = V + i + 1`. -/
theorem conv (n : Nat) (c g : Nat → Nat) (hc : ∀ V, n < V → c V = 0) :
    sumRange (n + 1) (fun V => c V * sumRange 16 (fun i => g (V + (i + 1))))
      = sumRange (n + 17) (fun V' =>
          (sumRange 16 (fun i => if i + 1 ≤ V' then c (V' - (i + 1)) else 0)) * g V') := by
  have h1 : sumRange (n + 1) (fun V => c V * sumRange 16 (fun i => g (V + (i + 1))))
      = sumRange (n + 1) (fun V => sumRange 16 (fun i => c V * g (V + (i + 1)))) :=
    sumRange_congr (fun V _ => (sumRange_const_mul 16 (c V) _).symm)
  have h2 : ∀ i, i < 16 → sumRange (n + 1) (fun V => c V * g (V + (i + 1)))
      = sumRange (n + 17) (fun V' => (if i + 1 ≤ V' then c (V' - (i + 1)) else 0) * g V') := by
    intro i hi
    have e : n + 17 = (i + 1) + (n + 16 - i) := by omega
    rw [e, sumRange_split (i + 1) (n + 16 - i)]
    have hA : sumRange (i + 1) (fun V' => (if i + 1 ≤ V' then c (V' - (i + 1)) else 0) * g V')
        = sumRange (i + 1) (fun _ => 0) :=
      sumRange_congr (fun V' hV' => by rw [if_neg (by omega), Nat.zero_mul])
    have hB : sumRange (n + 16 - i) (fun k => (if i + 1 ≤ i + 1 + k then c (i + 1 + k - (i + 1)) else 0) * g (i + 1 + k))
        = sumRange (n + 16 - i) (fun k => c k * g (k + (i + 1))) :=
      sumRange_congr (fun k _ => by
        rw [if_pos (by omega), show i + 1 + k - (i + 1) = k by omega, Nat.add_comm (i + 1) k])
    rw [hA, sumRange_const, Nat.mul_zero, Nat.zero_add, hB]
    have e2 : n + 16 - i = (n + 1) + (15 - i) := by omega
    rw [e2, sumRange_split (n + 1) (15 - i)]
    have hC : sumRange (15 - i) (fun k => c (n + 1 + k) * g (n + 1 + k + (i + 1)))
        = sumRange (15 - i) (fun _ => 0) :=
      sumRange_congr (fun k _ => by rw [hc (n + 1 + k) (by omega), Nat.zero_mul])
    rw [hC, sumRange_const, Nat.mul_zero]
    exact (Nat.add_zero _).symm
  rw [h1, sumRange_comm, sumRange_congr h2, sumRange_comm]
  exact sumRange_congr (fun V' _ =>
    sumRange_mul_const 16 (fun i => if i + 1 ≤ V' then c (V' - (i + 1)) else 0) (g V'))

/-! ## 6. The expansion -/

/-- A retarded node at depth `d` is a leaf, with the weight it inherits. -/
noncomputable def leaf (j y D d V : Nat) : Nat :=
  if adv d V then 0 else 97 ^ d * 300 ^ (D - d) * A d V * Mm (3 ^ (j + d) * 2 ^ (y - V))

noncomputable def Leaves (j y D : Nat) : Nat :=
  sumRange (D + 1) (fun d => sumRange (16 * d + 1) (fun V => leaf j y D d V))

/-- The advanced frontier at depth `D`. -/
noncomputable def Front (j y D : Nat) : Nat :=
  sumRange (16 * D + 1) (fun V =>
    if adv D V then 97 ^ D * A D V * Mm (3 ^ (j + D) * 2 ^ (y - V)) else 0)

theorem leaf_succ {j y D d : Nat} (hd : d ≤ D) (V : Nat) :
    leaf j y (D + 1) d V = 300 * leaf j y D d V := by
  unfold leaf
  by_cases h : adv d V = true
  · rw [if_pos h, if_pos h, Nat.mul_zero]
  · rw [if_neg h, if_neg h]
    rw [show D + 1 - d = (D - d) + 1 by omega, Nat.pow_succ]
    ac_rfl

theorem leaves_succ (j y D : Nat) :
    Leaves j y (D + 1) = 300 * Leaves j y D
      + sumRange (16 * (D + 1) + 1) (fun V => leaf j y (D + 1) (D + 1) V) := by
  unfold Leaves
  rw [sumRange_succ]
  congr 1
  rw [← sumRange_const_mul]
  refine sumRange_congr (fun d hd => ?_)
  rw [← sumRange_const_mul]
  exact sumRange_congr (fun V _ => leaf_succ (by omega) V)

/-- Expanding the advanced frontier one generation, by (R). -/
theorem front_expand (hE : Equi) {j y D : Nat} (hy : 16 * D + 52 ≤ y) :
    sumRange (16 * D + 1) (fun V =>
        (if adv D V then 97 ^ (D + 1) * A D V else 0) *
          sumRange 16 (fun i => Mm (3 ^ (j + D + 1) * 2 ^ (y - (V + (i + 1))))))
      ≤ 300 * Front j y D := by
  unfold Front
  rw [← sumRange_const_mul]
  refine sumRange_le (fun V hV => ?_)
  by_cases h : adv D V = true
  · rw [if_pos h, if_pos h]
    have hr := rec_lattice hE (j := j + D) (y := y - V) (by omega)
    simp only [Nat.sub_sub] at hr
    have := Nat.mul_le_mul_left (97 ^ D * A D V) hr
    calc 97 ^ (D + 1) * A D V * sumRange 16 (fun i => Mm (3 ^ (j + D + 1) * 2 ^ (y - (V + (i + 1)))))
        = 97 ^ D * A D V * (97 * sumRange 16 (fun i => Mm (3 ^ (j + D + 1) * 2 ^ (y - (V + (i + 1)))))) := by
          rw [Nat.pow_succ]; ac_rfl
      _ ≤ 97 ^ D * A D V * (300 * Mm (3 ^ (j + D) * 2 ^ (y - V))) := this
      _ = 300 * (97 ^ D * A D V * Mm (3 ^ (j + D) * 2 ^ (y - V))) := by ac_rfl
  · rw [if_neg h, if_neg h, Nat.zero_mul, Nat.mul_zero]
    exact Nat.le_refl 0

/-- **The expansion.**  Leaves plus frontier are dominated by `300^D` times the root. -/
theorem expand (hE : Equi) (j y : Nat) : ∀ D, D ≤ 10 → 16 * D + 36 ≤ y →
    Leaves j y D + Front j y D ≤ 300 ^ D * Mm (3 ^ j * 2 ^ y) := by
  intro D
  induction D with
  | zero =>
    intro _ _
    have hL : Leaves j y 0 = 0 := by
      show sumRange 1 (fun d => sumRange (16 * d + 1) (fun V => leaf j y 0 d V)) = 0
      rw [sumRange_one]
      show sumRange 1 (fun V => leaf j y 0 0 V) = 0
      rw [sumRange_one]
      unfold leaf
      rw [if_pos (by decide)]
    have hF : Front j y 0 = Mm (3 ^ j * 2 ^ y) := by
      show sumRange 1 (fun V => if adv 0 V then 97 ^ 0 * A 0 V * Mm (3 ^ (j + 0) * 2 ^ (y - 0)) else 0)
        = Mm (3 ^ j * 2 ^ y)
      rw [sumRange_one]
      show (if adv 0 0 then 97 ^ 0 * A 0 0 * Mm (3 ^ (j + 0) * 2 ^ (y - 0)) else 0) = _
      rw [if_pos (by decide), show A 0 0 = 1 from rfl]
      simp only [Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.sub_zero]
    rw [hL, hF, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    exact Nat.le_refl _
  | succ D ih =>
    intro hD hy
    have ih' := ih (by omega) (by omega)
    have hmul : 300 * Leaves j y D + 300 * Front j y D ≤ 300 ^ (D + 1) * Mm (3 ^ j * 2 ^ y) := by
      rw [Nat.pow_succ, Nat.mul_comm (300 ^ D) 300, Nat.mul_assoc, ← Nat.mul_add]
      exact Nat.mul_le_mul_left 300 ih'
    rw [leaves_succ]
    -- the new frontier and the new leaves come from expanding the old frontier
    have hfe := front_expand hE (j := j) (y := y) (D := D) (by omega)
    have hconv : sumRange (16 * D + 1) (fun V =>
        (if adv D V then 97 ^ (D + 1) * A D V else 0) *
          sumRange 16 (fun i => Mm (3 ^ (j + D + 1) * 2 ^ (y - (V + (i + 1))))))
        = sumRange (16 * D + 17) (fun V' =>
          (sumRange 16 (fun i => if i + 1 ≤ V' then
            (if adv D (V' - (i + 1)) then 97 ^ (D + 1) * A D (V' - (i + 1)) else 0) else 0))
            * Mm (3 ^ (j + D + 1) * 2 ^ (y - V'))) :=
      conv (16 * D) (fun V => if adv D V then 97 ^ (D + 1) * A D V else 0)
        (fun V' => Mm (3 ^ (j + D + 1) * 2 ^ (y - V')))
        (fun V hV => by
          show (if adv D V then 97 ^ (D + 1) * A D V else 0) = 0
          rw [A_beyond (by omega) hV, Nat.mul_zero]
          split <;> rfl)
    rw [hconv] at hfe
    have hrow : ∀ V', V' < 16 * D + 17 →
        (sumRange 16 (fun i => if i + 1 ≤ V' then
            (if adv D (V' - (i + 1)) then 97 ^ (D + 1) * A D (V' - (i + 1)) else 0) else 0))
          * Mm (3 ^ (j + D + 1) * 2 ^ (y - V'))
        = (if adv (D + 1) V' then 97 ^ (D + 1) * A (D + 1) V' * Mm (3 ^ (j + (D + 1)) * 2 ^ (y - V')) else 0)
          + leaf j y (D + 1) (D + 1) V' := by
      intro V' _
      have hin : sumRange 16 (fun i => if i + 1 ≤ V' then
            (if adv D (V' - (i + 1)) then 97 ^ (D + 1) * A D (V' - (i + 1)) else 0) else 0)
          = 97 ^ (D + 1) * A (D + 1) V' := by
        rw [A_rec_all (by omega) V', ← sumRange_const_mul]
        refine sumRange_congr (fun i _ => ?_)
        by_cases h1 : i + 1 ≤ V'
        · by_cases h2 : adv D (V' - (i + 1)) = true
          · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
          · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2), Nat.mul_zero]
        · rw [if_neg h1, if_neg (fun h => h1 h.1), Nat.mul_zero]
      rw [hin]
      unfold leaf
      rw [Nat.add_assoc j D 1]
      by_cases h : adv (D + 1) V' = true
      · rw [if_pos h, if_pos h]
        exact (Nat.add_zero _).symm
      · rw [if_neg h, if_neg h, Nat.zero_add, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    rw [sumRange_congr hrow, sumRange_add] at hfe
    have hF : Front j y (D + 1)
        = sumRange (16 * D + 17) (fun V' =>
            if adv (D + 1) V' then 97 ^ (D + 1) * A (D + 1) V' * Mm (3 ^ (j + (D + 1)) * 2 ^ (y - V')) else 0) := by
      unfold Front
      rw [show 16 * (D + 1) + 1 = 16 * D + 17 by omega]
    have key : sumRange (16 * (D + 1) + 1) (fun V => leaf j y (D + 1) (D + 1) V) + Front j y (D + 1)
        ≤ 300 * Front j y D := by
      rw [hF, show 16 * (D + 1) + 1 = 16 * D + 17 by omega, Nat.add_comm]
      exact hfe
    calc 300 * Leaves j y D + sumRange (16 * (D + 1) + 1) (fun V => leaf j y (D + 1) (D + 1) V)
          + Front j y (D + 1)
        = 300 * Leaves j y D
          + (sumRange (16 * (D + 1) + 1) (fun V => leaf j y (D + 1) (D + 1) V) + Front j y (D + 1)) := by
          rw [Nat.add_assoc]
      _ ≤ 300 * Leaves j y D + 300 * Front j y D := Nat.add_le_add_left key _
      _ ≤ 300 ^ (D + 1) * Mm (3 ^ j * 2 ^ y) := hmul

/-! ## 7. Claims, certificate, induction -/

def claim (j y : Nat) : Prop :=
  5 ≤ 3 ^ j * 2 ^ y → 21 ^ (12 * y + 19 * j) ≤ 20 ^ (12 * y + 19 * j) * K * Mm (3 ^ j * 2 ^ y)

/-- The weight a retarded leaf carries in the certificate. -/
def cLeaf (d V : Nat) : Nat :=
  if adv d V then 0 else
    97 ^ d * 300 ^ (10 - d) * A d V * (21 ^ (1920 + 19 * d - 12 * V) * 20 ^ (12 * V - 19 * d))

/-- **The certificate**: ratio `(21/20)^12`, tolerance `1/100`, depth `10`. -/
theorem cert : 300 ^ 10 * 21 ^ 1920 ≤ sumRange 11 (fun d => sumRange (16 * d + 1) (fun V => cLeaf d V)) := by
  decide +kernel

theorem base_bound : ∀ j, j < 12 → ∀ y, y < 196 →
    21 ^ (12 * y + 19 * j) ≤ 20 ^ (12 * y + 19 * j) * K := by
  decide +kernel

theorem base {j y : Nat} (hj : j < 12) (hy : y < 196) : claim j y := by
  intro h5
  have hb := base_bound j hj y hy
  have hM := Mm_pos h5
  calc 21 ^ (12 * y + 19 * j) ≤ 20 ^ (12 * y + 19 * j) * K := hb
    _ = 20 ^ (12 * y + 19 * j) * K * 1 := (Nat.mul_one _).symm
    _ ≤ 20 ^ (12 * y + 19 * j) * K * Mm (3 ^ j * 2 ^ y) := Nat.mul_le_mul_left _ hM

theorem drop_scale (j y : Nat) (hj : 12 ≤ j) : 3 ^ (j - 12) * 2 ^ (y + 19) < 3 ^ j * 2 ^ y := by
  obtain ⟨d, rfl⟩ : ∃ d, j = d + 12 := ⟨j - 12, by omega⟩
  have e : d + 12 - 12 = d := by omega
  rw [e, Nat.pow_add 3 d 12, Nat.pow_add 2 y 19]
  have h : (2:Nat) ^ 19 < 3 ^ 12 := by decide
  have hp : 0 < 3 ^ d * 2 ^ y := Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  calc 3 ^ d * (2 ^ y * 2 ^ 19) = (3 ^ d * 2 ^ y) * 2 ^ 19 := by ac_rfl
    _ < (3 ^ d * 2 ^ y) * 3 ^ 12 := Nat.mul_lt_mul_of_pos_left h hp
    _ = 3 ^ d * 3 ^ 12 * 2 ^ y := by ac_rfl

theorem drop {j y : Nat} (hj : 12 ≤ j) (h : claim (j - 12) (y + 19)) : claim j y := by
  intro _
  have h5 : 5 ≤ 3 ^ (j - 12) * 2 ^ (y + 19) := by
    have h1 : (5:Nat) ≤ 2 ^ 19 := by decide
    have h2 : 1 ≤ 3 ^ (j - 12) := Nat.pow_pos (by decide)
    have h3 := Nat.mul_le_mul_right (2 ^ (y + 19)) h2
    have h4 : 2 ^ 19 ≤ 2 ^ (y + 19) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.one_mul] at h3
    exact Nat.le_trans (Nat.le_trans h1 h4) h3
  have hcl := h h5
  have e : 12 * (y + 19) + 19 * (j - 12) = 12 * y + 19 * j := by omega
  rw [e] at hcl
  have hmono := Mm_mono (Nat.le_of_lt (drop_scale j y hj))
  exact Nat.le_trans hcl (Nat.mul_le_mul_left _ hmono)

/-- One retarded leaf, moved to the root's weight. -/
theorem leaf_le {j y d V : Nat} (hy : 196 ≤ y) (hd1 : 1 ≤ d) (hd : d ≤ 10) (hV : V ≤ 16 * d)
    (hadv : adv d V = false) (ihc : claim (j + d) (y - V)) :
    21 ^ (12 * y + 19 * j - 1920) * cLeaf d V
      ≤ leaf j y 10 d V * (20 ^ (12 * y + 19 * j) * K) := by
  have hw := retarded_weight d hd hd1 V (by omega) hadv
  have e1 : 12 * (y - V) + 19 * (j + d) = (12 * y + 19 * j - 1920) + (1920 + 19 * d - 12 * V) := by
    omega
  have e2 : (12 * y + 19 * j - 1920) + (1920 + 19 * d - 12 * V) + (12 * V - 19 * d)
      = 12 * y + 19 * j := by omega
  have hyV : 3 ≤ y - V := by omega
  have hna : ¬ (adv d V = true) := by rw [hadv]; decide
  unfold cLeaf leaf
  rw [if_neg hna, if_neg hna]
  have h5 : 5 ≤ 3 ^ (j + d) * 2 ^ (y - V) := by
    have h1 : 1 ≤ 3 ^ (j + d) := Nat.pow_pos (by decide)
    have h2 : 8 ≤ 2 ^ (y - V) := by
      calc (8:Nat) = 2 ^ 3 := rfl
        _ ≤ 2 ^ (y - V) := Nat.pow_le_pow_right (by decide) hyV
    have := Nat.mul_le_mul h1 h2
    rw [Nat.one_mul] at this
    exact Nat.le_trans (by decide) this
  have hcl := ihc h5
  rw [e1] at hcl
  have hcl' := Nat.mul_le_mul_right (20 ^ (12 * V - 19 * d)) hcl
  have e3 : 20 ^ ((12 * y + 19 * j - 1920) + (1920 + 19 * d - 12 * V)) * K
        * Mm (3 ^ (j + d) * 2 ^ (y - V)) * 20 ^ (12 * V - 19 * d)
      = Mm (3 ^ (j + d) * 2 ^ (y - V)) * (20 ^ (12 * y + 19 * j) * K) := by
    calc 20 ^ ((12 * y + 19 * j - 1920) + (1920 + 19 * d - 12 * V)) * K
          * Mm (3 ^ (j + d) * 2 ^ (y - V)) * 20 ^ (12 * V - 19 * d)
        = Mm (3 ^ (j + d) * 2 ^ (y - V)) *
          (20 ^ ((12 * y + 19 * j - 1920) + (1920 + 19 * d - 12 * V) + (12 * V - 19 * d)) * K) := by
          rw [Nat.pow_add 20 ((12 * y + 19 * j - 1920) + (1920 + 19 * d - 12 * V)) (12 * V - 19 * d)]
          ac_rfl
      _ = Mm (3 ^ (j + d) * 2 ^ (y - V)) * (20 ^ (12 * y + 19 * j) * K) := by rw [e2]
  rw [e3] at hcl'
  calc 21 ^ (12 * y + 19 * j - 1920) *
        (97 ^ d * 300 ^ (10 - d) * A d V * (21 ^ (1920 + 19 * d - 12 * V) * 20 ^ (12 * V - 19 * d)))
      = 97 ^ d * 300 ^ (10 - d) * A d V *
          (21 ^ ((12 * y + 19 * j - 1920) + (1920 + 19 * d - 12 * V)) * 20 ^ (12 * V - 19 * d)) := by
        rw [Nat.pow_add 21 (12 * y + 19 * j - 1920)]; ac_rfl
    _ ≤ 97 ^ d * 300 ^ (10 - d) * A d V *
          (Mm (3 ^ (j + d) * 2 ^ (y - V)) * (20 ^ (12 * y + 19 * j) * K)) :=
        Nat.mul_le_mul_left _ hcl'
    _ = 97 ^ d * 300 ^ (10 - d) * A d V * Mm (3 ^ (j + d) * 2 ^ (y - V)) *
          (20 ^ (12 * y + 19 * j) * K) := by ac_rfl

theorem cLeaf_zero (V : Nat) : cLeaf 0 V = 0 := by
  unfold cLeaf
  cases V with
  | zero => rw [if_pos (by decide)]
  | succ V =>
    rw [A_zero, if_neg (show ¬ (V + 1 = 0) by omega), Nat.mul_zero, Nat.zero_mul]
    split <;> rfl

/-- **The step**: `j < 12`, `y = y' + 196`. -/
theorem step (hE : Equi) {j y' : Nat}
    (ih : ∀ j' y'', 3 ^ j' * 2 ^ y'' < 3 ^ j * 2 ^ (y' + 196) → claim j' y'') :
    claim j (y' + 196) := by
  intro _
  have hy196 : 196 ≤ y' + 196 := Nat.le_add_left _ _
  have hyD : 16 * 10 + 36 ≤ y' + 196 := by omega
  -- the leaves dominate the certificate
  have hsum : sumRange 11 (fun d => sumRange (16 * d + 1) (fun V =>
        21 ^ (12 * (y' + 196) + 19 * j - 1920) * cLeaf d V))
      ≤ sumRange 11 (fun d => sumRange (16 * d + 1) (fun V =>
        leaf j (y' + 196) 10 d V * (20 ^ (12 * (y' + 196) + 19 * j) * K))) := by
    refine sumRange_le (fun d hd => sumRange_le (fun V hV => ?_))
    have hd10 : d ≤ 10 := by omega
    have hV16 : V ≤ 16 * d := by omega
    have hVy : V ≤ y' + 196 := by omega
    rcases Nat.eq_zero_or_pos d with rfl | hd1
    · rw [cLeaf_zero, Nat.mul_zero]; exact Nat.zero_le _
    · by_cases ha : adv d V = true
      · unfold cLeaf; rw [if_pos ha, Nat.mul_zero]; exact Nat.zero_le _
      · have ha' : adv d V = false := by
          cases hb : adv d V
          · rfl
          · exact absurd hb ha
        apply leaf_le hy196 hd1 hd10 hV16 ha'
        apply ih
        exact retarded_lt ha' hVy
  rw [sumRange_congr (fun d _ => sumRange_const_mul _ _ _), sumRange_const_mul] at hsum
  rw [sumRange_congr (fun d _ => sumRange_mul_const _ _ _), sumRange_mul_const] at hsum
  have hexp := expand hE j (y' + 196) 10 (Nat.le_refl _) hyD
  have hL : Leaves j (y' + 196) 10 ≤ 300 ^ 10 * Mm (3 ^ j * 2 ^ (y' + 196)) :=
    Nat.le_trans (Nat.le_add_right _ _) hexp
  have hL' := Nat.mul_le_mul_right (20 ^ (12 * (y' + 196) + 19 * j) * K) hL
  have hc := Nat.mul_le_mul_left (21 ^ (12 * (y' + 196) + 19 * j - 1920)) cert
  have eexp : 12 * (y' + 196) + 19 * j = (12 * (y' + 196) + 19 * j - 1920) + 1920 := by omega
  have e : 21 ^ (12 * (y' + 196) + 19 * j - 1920) * (300 ^ 10 * 21 ^ 1920)
      = 300 ^ 10 * 21 ^ (12 * (y' + 196) + 19 * j) := by
    calc 21 ^ (12 * (y' + 196) + 19 * j - 1920) * (300 ^ 10 * 21 ^ 1920)
        = 300 ^ 10 * (21 ^ (12 * (y' + 196) + 19 * j - 1920) * 21 ^ 1920) :=
          Nat.mul_left_comm _ _ _
      _ = 300 ^ 10 * 21 ^ ((12 * (y' + 196) + 19 * j - 1920) + 1920) := by rw [Nat.pow_add]
      _ = 300 ^ 10 * 21 ^ (12 * (y' + 196) + 19 * j) := by rw [← eexp]
  rw [e] at hc
  have hfin : 300 ^ 10 * 21 ^ (12 * (y' + 196) + 19 * j)
      ≤ 300 ^ 10 * (20 ^ (12 * (y' + 196) + 19 * j) * K * Mm (3 ^ j * 2 ^ (y' + 196))) := by
    unfold Leaves at hL'
    calc 300 ^ 10 * 21 ^ (12 * (y' + 196) + 19 * j)
        ≤ _ := hc
      _ ≤ _ := hsum
      _ ≤ 300 ^ 10 * Mm (3 ^ j * 2 ^ (y' + 196)) * (20 ^ (12 * (y' + 196) + 19 * j) * K) := hL'
      _ = _ := by rw [Nat.mul_assoc, Nat.mul_comm (Mm _)]
  exact Nat.le_of_mul_le_mul_left hfin (Nat.pow_pos (by decide))

theorem claims_aux (hE : Equi) : ∀ n, ∀ j y, 3 ^ j * 2 ^ y ≤ n → claim j y := by
  intro n
  induction n with
  | zero =>
    intro j y h
    have : 0 < 3 ^ j * 2 ^ y := Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
    omega
  | succ n ih =>
    intro j y hbound
    rcases Nat.lt_or_ge (3 ^ j * 2 ^ y) (n + 1) with hlt | hge
    · exact ih j y (by omega)
    · rcases Nat.lt_or_ge j 12 with hj | hj
      · rcases Nat.lt_or_ge y 196 with hy | hy
        · exact base hj hy
        · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 196 := ⟨y - 196, by omega⟩
          apply step hE
          intro j' y'' hlt'
          exact ih j' y'' (by omega)
      · exact drop hj (ih (j - 12) (y + 19) (by
          have := drop_scale j y hj
          omega))

theorem claims (hE : Equi) (j y : Nat) : claim j y := claims_aux hE _ j y (Nat.le_refl _)

/-! ## 8. The exponent `0.84` -/

theorem two_classes_le_count (X : Nat) : M 1 X + M 2 X ≤ reachCount X := by
  unfold reachCount
  rw [countUpTo_split (fun n => decide (n % 3 = 1)) X]
  apply Nat.add_le_add
  · unfold M
    apply countUpTo_mono
    intro n h1 h2 ⟨_, h3, h4⟩
    exact ⟨⟨by omega, h4⟩, by show decide (n % 3 = 1) = true; rw [h3]; rfl⟩
  · unfold M
    apply countUpTo_mono
    intro n h1 h2 ⟨_, h3, h4⟩
    exact ⟨⟨by omega, h4⟩, by show decide (n % 3 = 1) = false; rw [h3]; rfl⟩

theorem count_mono {X X' : Nat} (h : X ≤ X') : reachCount X ≤ reachCount X' := countUpTo_le_of_le h

theorem count_one : 1 ≤ reachCount 1 :=
  one_le_countUpTo (k := 1) (by decide) (by decide) ⟨by decide, ⟨0, rfl⟩⟩

theorem pow_ineq (y : Nat) : 2 ^ (21 * y) * 20 ^ (300 * y) ≤ 21 ^ (300 * y) := by
  rw [Nat.pow_mul, Nat.pow_mul, Nat.pow_mul, ← Nat.mul_pow]
  exact Nat.pow_le_pow_left (by decide) y

theorem pow_ineq2 (y : Nat) :
    2 ^ (21 * y) * 20 ^ (300 * y + 775) ≤ 21 ^ (300 * y + 775) := by
  rw [Nat.pow_add 20, Nat.pow_add 21, ← Nat.mul_assoc]
  exact Nat.mul_le_mul (pow_ineq y) (Nat.pow_le_pow_left (by decide) 775)

theorem arith_core {x P a b Q T : Nat} (hb : 0 < b) (hab : P * b ≤ a)
    (h : 2 ^ 25 * a ≤ b * Q) (hN : x < T * P) : x < T * Q := by
  have h1 : x * (b * 2 ^ 25) < T * P * (b * 2 ^ 25) :=
    Nat.mul_lt_mul_of_pos_right hN (Nat.mul_pos hb (Nat.pow_pos (by decide)))
  have h2 : T * P * (b * 2 ^ 25) ≤ (T * Q) * b := by
    calc T * P * (b * 2 ^ 25) = T * (P * b * 2 ^ 25) := by ac_rfl
      _ ≤ T * (a * 2 ^ 25) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hab)
      _ = T * (2 ^ 25 * a) := by ac_rfl
      _ ≤ T * (b * Q) := Nat.mul_le_mul_left _ h
      _ = (T * Q) * b := by ac_rfl
  have e : x * (b * 2 ^ 25) = (x * 2 ^ 25) * b := by ac_rfl
  rw [e] at h1
  have h3 := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_lt_of_le h1 h2)
  have h5 : x ≤ x * 2 ^ 25 := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
  omega

theorem K_pow : K ^ 25 = 10 ^ 1375 := by
  unfold K
  rw [← Nat.pow_mul]

/-- **At least `N ^ 0.84 / c` integers up to `N` reach `1`, if the integers
reaching `1` are balanced modulo `9` inside each class modulo `3`.** -/
theorem count_balance9 (hE : Equi) {N : Nat} (hN : 1 ≤ N) :
    N ^ 21 < 20 ^ 21 * 10 ^ 1375 * reachCount N ^ 25 := by
  have hc1 : 1 ≤ reachCount N := Nat.le_trans count_one (count_mono hN)
  rcases Nat.lt_or_ge N 10 with hsmall | hbig
  · have h1 : 1 ≤ reachCount N ^ 25 := Nat.pow_pos hc1
    have h2 : N ^ 21 ≤ 9 ^ 21 := Nat.pow_le_pow_left (by omega) 21
    have h3 : (9:Nat) ^ 21 < 20 ^ 21 * 10 ^ 1375 :=
      Nat.lt_of_lt_of_le (Nat.pow_lt_pow_left (by decide) (by decide))
        (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide)))
    have h4 : 20 ^ 21 * 10 ^ 1375 * 1 ≤ 20 ^ 21 * 10 ^ 1375 * reachCount N ^ 25 :=
      Nat.mul_le_mul_left _ h1
    rw [Nat.mul_one] at h4
    exact Nat.lt_of_le_of_lt h2 (Nat.lt_of_lt_of_le h3 h4)
  obtain ⟨y, hy1, hy2⟩ := TreeHalf.exists_bracket_ten N hbig
  have h2y : 1 ≤ 2 ^ y := Nat.pow_pos (by decide)
  have e3 : (3:Nat) ^ 1 = 3 := rfl
  have e21 : (2:Nat) ^ (y + 1) = 2 ^ y * 2 := Nat.pow_succ 2 y
  have h5 : 5 ≤ 3 ^ 1 * 2 ^ (y + 1) := by
    rw [e3, e21]; omega
  have hcl := claims hE 1 (y + 1) h5
  have hsc : 3 ^ 1 * 2 ^ (y + 1) ≤ N := by
    rw [e3, e21]; omega
  have hM : 2 * Mm (3 ^ 1 * 2 ^ (y + 1)) ≤ reachCount N := by
    have hm1 : Mm (3 ^ 1 * 2 ^ (y + 1)) ≤ M 1 (3 ^ 1 * 2 ^ (y + 1)) := Nat.min_le_left _ _
    have hm2 : Mm (3 ^ 1 * 2 ^ (y + 1)) ≤ M 2 (3 ^ 1 * 2 ^ (y + 1)) := Nat.min_le_right _ _
    have h1 := two_classes_le_count N
    have h2 := M_mono (c := 1) hsc
    have h3 := M_mono (c := 2) hsc
    calc 2 * Mm (3 ^ 1 * 2 ^ (y + 1)) = Mm (3 ^ 1 * 2 ^ (y + 1)) + Mm (3 ^ 1 * 2 ^ (y + 1)) := by
          rw [Nat.two_mul]
      _ ≤ M 1 N + M 2 N := Nat.add_le_add (Nat.le_trans hm1 h2) (Nat.le_trans hm2 h3)
      _ ≤ reachCount N := h1
  have e : 12 * (y + 1) + 19 * 1 = 12 * y + 31 := by omega
  rw [e] at hcl
  have h1 : 2 * 21 ^ (12 * y + 31) ≤ 20 ^ (12 * y + 31) * K * reachCount N := by
    have := Nat.mul_le_mul_left (20 ^ (12 * y + 31) * K) hM
    have h2 := Nat.mul_le_mul_left 2 hcl
    calc 2 * 21 ^ (12 * y + 31) ≤ 2 * (20 ^ (12 * y + 31) * K * Mm (3 ^ 1 * 2 ^ (y + 1))) := h2
      _ = 20 ^ (12 * y + 31) * K * (2 * Mm (3 ^ 1 * 2 ^ (y + 1))) := by ac_rfl
      _ ≤ 20 ^ (12 * y + 31) * K * reachCount N := this
  have hh : 2 ^ 25 * 21 ^ (300 * y + 775)
      ≤ 20 ^ (300 * y + 775) * (K ^ 25 * reachCount N ^ 25) := by
    have h2 := Nat.pow_le_pow_left h1 25
    have eL : (2 * 21 ^ (12 * y + 31)) ^ 25 = 2 ^ 25 * 21 ^ (300 * y + 775) := by
      rw [Nat.mul_pow, ← Nat.pow_mul, show (12 * y + 31) * 25 = 300 * y + 775 by omega]
    have eR : (20 ^ (12 * y + 31) * K * reachCount N) ^ 25
        = 20 ^ (300 * y + 775) * (K ^ 25 * reachCount N ^ 25) := by
      rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul,
        show (12 * y + 31) * 25 = 300 * y + 775 by omega, Nat.mul_assoc]
    rw [eL, eR] at h2
    exact h2
  have hN2 : N ^ 21 < 20 ^ 21 * 2 ^ (21 * y) := by
    have := Nat.pow_lt_pow_left hy2 (show 21 ≠ 0 by decide)
    rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm y 21] at this
    exact this
  have hres := arith_core (Nat.pow_pos (by decide)) (pow_ineq2 y) hh hN2
  rw [K_pow] at hres
  calc N ^ 21 < 20 ^ 21 * (10 ^ 1375 * reachCount N ^ 25) := hres
    _ = 20 ^ 21 * 10 ^ 1375 * reachCount N ^ 25 := by rw [Nat.mul_assoc]

end TreeBalance9
end Collatz
