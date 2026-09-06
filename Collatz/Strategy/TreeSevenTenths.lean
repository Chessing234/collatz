import Collatz.Strategy.TreeTwoThirds
import Collatz.Strategy.TreeCertificate3

/-!
# At least `N ^ (7/10) / c` integers up to `N` reach `1`

**Novelty tag: FORMALIZATION-OF-KNOWN.**  The next rung of `TreeTwoThirds`:
the same absolute-bound double induction at classes modulo `729` (children
modulo `243`), ratio `λ = 13/8` with `λ ^ 10 ≥ 2 ^ 7`, certificate
`TreeCertificate3` (`972` inequalities).  Every proof below is the
corresponding proof of `TreeTwoThirds` with the constants substituted; the
scheme is parametric in the tables.

    count_ten : 1 ≤ N → N ^ 7 < C · (reachesOneUpToCount N) ^ 10

The scalar of G6 moves from `2/3` to `7/10`.  The continuous system's value
at this level is `0.76`; the literature's record is `0.84`.
-/

namespace Collatz
namespace TreeSevenTenths

open TreeCount TreeBranching Subtree ClassChild TreeCertificate3 Collatz.Sum
  Papers.KrasikovLagarias2003

/-- Roots as in `TreeHalf`: odd, prime to `3`, at least `5`, reaching `1`. -/
abbrev Root := TreeHalf.Root

def claimF (y a : Nat) : Prop := A (a % 729) * 13 ^ y ≤ 8 ^ y * K * S a (2 ^ y * a)

def claimH (y a : Nat) : Prop := B (a % 729) * 13 ^ y ≤ 8 ^ y * K * S a (3 * 2 ^ y * a)

/-! ## 1. Children -/

theorem fvalR_eq_fval (r i : Nat) : fvalR r i = fval r i := rfl

theorem fvalR_mod (a i : Nat) : fvalR (a % 729) i = fval a i := by
  rw [fvalR_eq_fval, ← fval_eq_mod_729]

theorem childRes_eq {a : Nat} (ha : Good a) (i : Nat) :
    childRes (a % 729) (fval a i) = fch a i % 243 := by
  unfold childRes
  rw [fch_mod_243 ha i, fval_eq_mod_729]

theorem lift_le {a : Nat} (ha : Good a) (i : Nat) :
    Amin (fch a i % 243) ≤ A (fch a i % 729) ∧ Bmin (fch a i % 243) ≤ B (fch a i % 729) := by
  have h3 : (fch a i % 729) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd _ (⟨243, rfl⟩ : (3:Nat) ∣ 729)]
    exact (fch_good ha i).2
  have h := amin_le (fch a i % 729) (Nat.mod_lt _ (by decide)) h3
  rw [Nat.mod_mod_of_dvd _ (⟨3, rfl⟩ : (243:Nat) ∣ 729)] at h
  exact h

theorem two_pow_add_three_mul' (n c : Nat) : 2 ^ (n + 3) * c = 8 * (2 ^ n * c) := by
  rw [Nat.pow_add, show (2:Nat) ^ 3 = 8 from rfl, Nat.mul_comm (2 ^ n) 8, Nat.mul_assoc]

theorem eight_pow_add_two (v : Nat) : 8 ^ (v + 2) = 64 * 8 ^ v := by
  rw [Nat.pow_add, show (8:Nat) ^ 2 = 64 from rfl, Nat.mul_comm]

/-! ## 2. One summand -/

theorem rearr {y e f s bb : Nat} (h : y - 18 + e = f) :
    13 ^ (y - 18) * (s * 13 ^ e * bb) = s * (13 ^ f * bb) := by
  rw [← h, Nat.pow_add, Nat.mul_assoc s, Nat.mul_left_comm (13 ^ (y - 18)) s,
    ← Nat.mul_assoc (13 ^ (y - 18))]

theorem term_le {m n y bb b t : Nat} (hmn : m + n = y) (hb : bb ≤ b)
    (h : b * 13 ^ n ≤ 8 ^ n * K * t) :
    8 ^ m * (13 ^ n * bb) ≤ 8 ^ y * K * t := by
  have h1 : 8 ^ m * (13 ^ n * bb) ≤ 8 ^ m * (b * 13 ^ n) := by
    rw [Nat.mul_comm b]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
  have h2 : 8 ^ m * (b * 13 ^ n) ≤ 8 ^ m * (8 ^ n * K * t) := Nat.mul_le_mul_left _ h
  have h3 : 8 ^ m * (8 ^ n * K * t) = 8 ^ y * K * t := by
    rw [← hmn, Nat.pow_add, Nat.mul_assoc (8 ^ m) (8 ^ n) K, Nat.mul_assoc (8 ^ m)]
  rw [← h3]
  exact Nat.le_trans h1 h2

/-- The `F`-step summand: parent bound `2 ^ y a`, child bound `3 · 2 ^ (y−v) c`. -/
theorem childF_bound {y v c cr Ar Br : Nat} (hy : 18 ≤ y) (hv1 : 1 ≤ v) (hv : v ≤ 18)
    (hA : Amin cr ≤ Ar) (hB : Bmin cr ≤ Br)
    (hH : Br * 13 ^ (y - v) ≤ 8 ^ (y - v) * K * S c (3 * 2 ^ (y - v) * c))
    (hF : Ar * 13 ^ (y - v + 1) ≤ 8 ^ (y - v + 1) * K * S c (3 * 2 ^ (y - v) * c)) :
    13 ^ (y - 18) * max (8 ^ v * 13 ^ (18 - v) * Bmin cr)
        (8 ^ (v - 1) * 13 ^ (18 - v + 1) * Amin cr)
      ≤ 8 ^ y * K * S c (3 * 2 ^ (y - v) * c) := by
  apply TreeHalf.mul_max_le
  · rw [rearr (e := 18 - v) (f := y - v) (by omega)]
    exact term_le (by omega) hB hH
  · rw [rearr (e := 18 - v + 1) (f := y - v + 1) (by omega)]
    exact term_le (by omega) hA hF

/-- The `H`-step summand: parent bound `3 · 2 ^ y a`, child bound `2 ^ (y−v+3) c`. -/
theorem childH_bound {y v c cr Ar Br : Nat} (hy : 18 ≤ y) (hv1 : 1 ≤ v) (hv : v ≤ 18)
    (hA : Amin cr ≤ Ar) (hB : Bmin cr ≤ Br)
    (hH : Br * 13 ^ (y - v + 1) ≤ 8 ^ (y - v + 1) * K * S c (2 ^ (y - v + 3) * c))
    (hF : Ar * 13 ^ (y - v + 3) ≤ 8 ^ (y - v + 3) * K * S c (2 ^ (y - v + 3) * c)) :
    13 ^ (y - 18) * max (8 ^ (v + 1) * 13 ^ (18 - v + 1) * Bmin cr)
        (8 ^ (v - 1) * 13 ^ (18 - v + 3) * Amin cr)
      ≤ 64 * (8 ^ y * K * S c (2 ^ (y - v + 3) * c)) := by
  apply TreeHalf.mul_max_le
  · rw [rearr (e := 18 - v + 1) (f := y - v + 1) (by omega)]
    have e : 8 ^ (v + 1) = 64 * 8 ^ (v - 1) := by
      rw [← eight_pow_add_two]
      congr 1
      omega
    rw [e, Nat.mul_assoc]
    exact Nat.mul_le_mul_left 64 (term_le (by omega) hB hH)
  · rw [rearr (e := 18 - v + 3) (f := y - v + 3) (by omega)]
    have h := term_le (m := v - 1) (n := y - v + 3) (y := y + 2) (by omega) hA hF
    have e : 8 ^ (y + 2) * K * S c (2 ^ (y - v + 3) * c)
        = 64 * (8 ^ y * K * S c (2 ^ (y - v + 3) * c)) := by
      rw [eight_pow_add_two, Nat.mul_assoc 64, Nat.mul_assoc 64]
    rw [e] at h
    exact h

/-! ## 3. Assembly -/

theorem assembleF {y Ar Y a : Nat} {c Yi term : Nat → Nat} (hy : 18 ≤ y)
    (hcert : Ar * 13 ^ 18 ≤ sumRange 6 term)
    (hrec : sumRange 6 (fun i => S (c i) (Yi i)) ≤ S a Y)
    (hterm : ∀ i, i < 6 → 13 ^ (y - 18) * term i ≤ 8 ^ y * K * S (c i) (Yi i)) :
    Ar * 13 ^ y ≤ 8 ^ y * K * S a Y := by
  have h1 : Ar * 13 ^ y = 13 ^ (y - 18) * (Ar * 13 ^ 18) := by
    rw [Nat.mul_left_comm, ← Nat.pow_add]
    congr 2
    omega
  have h2 : 13 ^ (y - 18) * (Ar * 13 ^ 18) ≤ 13 ^ (y - 18) * sumRange 6 term :=
    Nat.mul_le_mul_left _ hcert
  have h3 : 13 ^ (y - 18) * sumRange 6 term = sumRange 6 (fun i => 13 ^ (y - 18) * term i) :=
    (sumRange_const_mul 6 _ term).symm
  have h4 : sumRange 6 (fun i => 13 ^ (y - 18) * term i)
      ≤ sumRange 6 (fun i => 8 ^ y * K * S (c i) (Yi i)) := sumRange_le hterm
  have h5 : sumRange 6 (fun i => 8 ^ y * K * S (c i) (Yi i))
      = 8 ^ y * K * sumRange 6 (fun i => S (c i) (Yi i)) := sumRange_const_mul 6 _ _
  have h6 : 8 ^ y * K * sumRange 6 (fun i => S (c i) (Yi i)) ≤ 8 ^ y * K * S a Y :=
    Nat.mul_le_mul_left _ hrec
  rw [h1]
  exact Nat.le_trans h2 (Nat.le_trans (h3 ▸ h4) (Nat.le_trans (h5 ▸ Nat.le_refl _) h6))

theorem assembleH {y Br Y a : Nat} {c Yi term : Nat → Nat} (hy : 18 ≤ y)
    (hcert : Br * 13 ^ 18 * 64 ≤ sumRange 6 term)
    (hrec : sumRange 6 (fun i => S (c i) (Yi i)) ≤ S a Y)
    (hterm : ∀ i, i < 6 → 13 ^ (y - 18) * term i ≤ 64 * (8 ^ y * K * S (c i) (Yi i))) :
    Br * 13 ^ y ≤ 8 ^ y * K * S a Y := by
  have h1 : 64 * (Br * 13 ^ y) = 13 ^ (y - 18) * (Br * 13 ^ 18 * 64) := by
    rw [Nat.mul_assoc Br (13 ^ 18) 64, Nat.mul_left_comm (13 ^ (y - 18)) Br,
      ← Nat.mul_assoc (13 ^ (y - 18)) (13 ^ 18) 64, ← Nat.pow_add,
      show y - 18 + 18 = y by omega, ← Nat.mul_assoc Br (13 ^ y) 64, Nat.mul_comm 64]
  have h2 : 13 ^ (y - 18) * (Br * 13 ^ 18 * 64) ≤ 13 ^ (y - 18) * sumRange 6 term :=
    Nat.mul_le_mul_left _ hcert
  have h3 : 13 ^ (y - 18) * sumRange 6 term = sumRange 6 (fun i => 13 ^ (y - 18) * term i) :=
    (sumRange_const_mul 6 _ term).symm
  have h4 : sumRange 6 (fun i => 13 ^ (y - 18) * term i)
      ≤ sumRange 6 (fun i => 64 * (8 ^ y * K * S (c i) (Yi i))) := sumRange_le hterm
  have h5 : sumRange 6 (fun i => 64 * (8 ^ y * K * S (c i) (Yi i)))
      = 64 * sumRange 6 (fun i => 8 ^ y * K * S (c i) (Yi i)) := sumRange_const_mul 6 _ _
  have h6 : sumRange 6 (fun i => 8 ^ y * K * S (c i) (Yi i))
      = 8 ^ y * K * sumRange 6 (fun i => S (c i) (Yi i)) := sumRange_const_mul 6 _ _
  have h7 : 8 ^ y * K * sumRange 6 (fun i => S (c i) (Yi i)) ≤ 8 ^ y * K * S a Y :=
    Nat.mul_le_mul_left _ hrec
  have hall : 64 * (Br * 13 ^ y) ≤ 64 * (8 ^ y * K * S a Y) := by
    rw [h1]
    refine Nat.le_trans h2 (Nat.le_trans (h3 ▸ h4) ?_)
    rw [h5, h6]
    exact Nat.mul_le_mul_left 64 h7
  exact Nat.le_of_mul_le_mul_left hall (by decide)

/-! ## 4. The two steps, with the induction hypothesis over the absolute bound -/

theorem stepF {y a : Nat} (hy : 23 ≤ y) (ha : Root a)
    (ihF : ∀ y' c, Root c → 2 ^ y' * c < 2 ^ y * a → claimF y' c)
    (ihH : ∀ y' c, Root c → 3 * 2 ^ y' * c < 2 ^ y * a → claimH y' c) : claimF y a := by
  obtain ⟨hg, h5, ht⟩ := ha
  have r_lt : a % 729 < 729 := Nat.mod_lt _ (by decide)
  have r_3 : (a % 729) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd a (⟨243, rfl⟩ : (3:Nat) ∣ 729)]
    exact hg.2
  have hy18 : 18 ≤ y := by omega
  have hv1 : ∀ i, 1 ≤ fval a i := fun i => fval_pos a i
  have hv18 : ∀ i, i < 6 → fval a i ≤ 18 := fun i hi =>
    Nat.le_trans (fval_le_tmpl a i) (tmpl_le_18 hi)
  have h3c : ∀ i, 3 * fch a i + 1 = 2 ^ fval a i * a := fun i => three_fch hg i
  have hroot : ∀ i, Root (fch a i) := fun i => TreeHalf.root_fch ⟨hg, h5, ht⟩ i
  have hlift := lift_le hg
  unfold claimF
  have hbudget : ∀ i, i < 6 → 3 * 2 ^ (y - fval a i) * fch a i + 18 ≤ 2 ^ y * a := by
    intro i hi
    have hid := TreeHalf.scale_identity (y := y) (by have := hv18 i hi; omega) (h3c i)
    have h32 := TreeHalf.thirtytwo_le (y := y) (v := fval a i) (by have := hv18 i hi; omega)
    rw [Nat.mul_assoc]
    omega
  apply assembleF hy18 (certF (a % 729) r_lt r_3)
    (S_rec (fun i => 3 * 2 ^ (y - fval a i) * fch a i) hg h5 ht hbudget)
  intro i hi
  rw [fvalR_mod, childRes_eq hg i]
  have hv := hv18 i hi
  have hid := TreeHalf.scale_identity (y := y) (by omega) (h3c i)
  have h32 := TreeHalf.thirtytwo_le (y := y) (v := fval a i) (by omega)
  -- H(y - v, c): bound 3 · 2^(y-v) c < 2^y a
  have hH := ihH (y - fval a i) (fch a i) (hroot i) (by rw [Nat.mul_assoc]; omega)
  unfold claimH at hH
  -- F(y - v + 1, c): bound 2^(y-v+1) c < 2^y a, then moved up by S_mono
  have hF := ihF (y - fval a i + 1) (fch a i) (hroot i)
    (by rw [TreeHalf.two_pow_succ_mul']; omega)
  unfold claimF at hF
  have hmono : S (fch a i) (2 ^ (y - fval a i + 1) * fch a i)
      ≤ S (fch a i) (3 * 2 ^ (y - fval a i) * fch a i) := by
    apply S_mono
    rw [TreeHalf.two_pow_succ_mul', Nat.mul_assoc]
    omega
  have hF' := Nat.le_trans hF (Nat.mul_le_mul_left _ hmono)
  exact childF_bound hy18 (hv1 i) hv (hlift i).1 (hlift i).2 hH hF'

theorem stepH {y a : Nat} (hy : 23 ≤ y) (ha : Root a)
    (ihF : ∀ y' c, Root c → 2 ^ y' * c < 3 * 2 ^ y * a → claimF y' c)
    (ihH : ∀ y' c, Root c → 3 * 2 ^ y' * c < 3 * 2 ^ y * a → claimH y' c) : claimH y a := by
  obtain ⟨hg, h5, ht⟩ := ha
  have r_lt : a % 729 < 729 := Nat.mod_lt _ (by decide)
  have r_3 : (a % 729) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd a (⟨243, rfl⟩ : (3:Nat) ∣ 729)]
    exact hg.2
  have hy18 : 18 ≤ y := by omega
  have hv1 : ∀ i, 1 ≤ fval a i := fun i => fval_pos a i
  have hv18 : ∀ i, i < 6 → fval a i ≤ 18 := fun i hi =>
    Nat.le_trans (fval_le_tmpl a i) (tmpl_le_18 hi)
  have h3c : ∀ i, 3 * fch a i + 1 = 2 ^ fval a i * a := fun i => three_fch hg i
  have hroot : ∀ i, Root (fch a i) := fun i => TreeHalf.root_fch ⟨hg, h5, ht⟩ i
  have hlift := lift_le hg
  unfold claimH
  have hbudget : ∀ i, i < 6 → 2 ^ (y - fval a i + 3) * fch a i + 18 ≤ 3 * 2 ^ y * a := by
    intro i hi
    have hid := TreeHalf.scale_identity (y := y) (by have := hv18 i hi; omega) (h3c i)
    have h32 := TreeHalf.thirtytwo_le (y := y) (v := fval a i) (by have := hv18 i hi; omega)
    rw [two_pow_add_three_mul', Nat.mul_assoc 3 (2 ^ y) a]
    omega
  apply assembleH hy18 (certH (a % 729) r_lt r_3)
    (S_rec (fun i => 2 ^ (y - fval a i + 3) * fch a i) hg h5 ht hbudget)
  intro i hi
  rw [fvalR_mod, childRes_eq hg i]
  have hv := hv18 i hi
  have hid := TreeHalf.scale_identity (y := y) (by omega) (h3c i)
  have h32 := TreeHalf.thirtytwo_le (y := y) (v := fval a i) (by omega)
  -- H(y - v + 1, c): bound 3 · 2^(y-v+1) c < 3 · 2^y a, moved up by S_mono
  have hH := ihH (y - fval a i + 1) (fch a i) (hroot i)
    (by rw [Nat.mul_assoc, TreeHalf.two_pow_succ_mul', Nat.mul_assoc 3 (2 ^ y) a]; omega)
  unfold claimH at hH
  have hmono : S (fch a i) (3 * 2 ^ (y - fval a i + 1) * fch a i)
      ≤ S (fch a i) (2 ^ (y - fval a i + 3) * fch a i) := by
    apply S_mono
    rw [Nat.mul_assoc, TreeHalf.two_pow_succ_mul', two_pow_add_three_mul']
    omega
  have hH' := Nat.le_trans hH (Nat.mul_le_mul_left _ hmono)
  -- F(y - v + 3, c): bound 2^(y-v+3) c < 3 · 2^y a — possibly an advanced index
  have hF := ihF (y - fval a i + 3) (fch a i) (hroot i)
    (by rw [two_pow_add_three_mul', Nat.mul_assoc 3 (2 ^ y) a]; omega)
  unfold claimF at hF
  exact childH_bound hy18 (hv1 i) hv (hlift i).1 (hlift i).2 hH' hF

/-! ## 5. Induction on the absolute bound -/

theorem base {y a : Nat} (hy : y ≤ 22) (ha : Root a) : claimF y a ∧ claimH y a := by
  obtain ⟨hg, _, _⟩ := ha
  have hb := base_bound (a % 729) (Nat.mod_lt _ (by decide)) y hy
  have hpow : 1 ≤ 2 ^ y := Nat.pow_pos (by decide)
  have hle1 : a ≤ 2 ^ y * a := by
    have := Nat.mul_le_mul_right a hpow
    omega
  have hle2 : a ≤ 3 * 2 ^ y * a := by
    have := Nat.mul_le_mul_right a (show 1 ≤ 3 * 2 ^ y by omega)
    omega
  have hS1 := S_pos hg hle1
  have hS2 := S_pos hg hle2
  constructor
  · unfold claimF
    have := Nat.mul_le_mul_left (8 ^ y * K) hS1
    omega
  · unfold claimH
    have := Nat.mul_le_mul_left (8 ^ y * K) hS2
    omega

/-- Every claim whose bound is at most `n`, by induction on `n`. -/
theorem claims_aux : ∀ n, ∀ y a, Root a →
    (2 ^ y * a ≤ n → claimF y a) ∧ (3 * 2 ^ y * a ≤ n → claimH y a) := by
  intro n
  induction n with
  | zero =>
    intro y a ha
    have ha5 : 0 < a := by have := ha.2.1; omega
    have hpos : 0 < 2 ^ y * a := Nat.mul_pos (Nat.pow_pos (by decide)) ha5
    have hpos3 : 0 < 3 * 2 ^ y * a := Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) ha5
    exact ⟨fun h => by omega, fun h => by omega⟩
  | succ n ih =>
    intro y a ha
    constructor
    · intro hbound
      rcases Nat.lt_or_ge (2 ^ y * a) (n + 1) with hlt | hge
      · exact (ih y a ha).1 (by omega)
      · by_cases h22 : y ≤ 22
        · exact (base h22 ha).1
        · apply stepF (by omega) ha
          · intro y' c hc hlt
            exact (ih y' c hc).1 (by omega)
          · intro y' c hc hlt
            exact (ih y' c hc).2 (by omega)
    · intro hbound
      rcases Nat.lt_or_ge (3 * 2 ^ y * a) (n + 1) with hlt | hge
      · exact (ih y a ha).2 (by omega)
      · by_cases h22 : y ≤ 22
        · exact (base h22 ha).2
        · apply stepH (by omega) ha
          · intro y' c hc hlt
            exact (ih y' c hc).1 (by omega)
          · intro y' c hc hlt
            exact (ih y' c hc).2 (by omega)

/-- **Both claims hold for every root at every scale.** -/
theorem claims (y a : Nat) (ha : Root a) : claimF y a ∧ claimH y a :=
  ⟨(claims_aux (2 ^ y * a) y a ha).1 (Nat.le_refl _),
   (claims_aux (3 * 2 ^ y * a) y a ha).2 (Nat.le_refl _)⟩

/-! ## 6. The exponent `7/10` -/

theorem A_five_pos : 1 ≤ A 5 := by decide

theorem K_ten : K ^ 10 = 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide

theorem thirteen_pow (y : Nat) : 128 ^ y * 1073741824 ^ y ≤ 137858491849 ^ y := by
  rw [← Nat.mul_pow]
  exact Nat.pow_le_pow_left (by decide) y

/-- **At least `N ^ (7/10) / c` integers up to `N` reach `1`.** -/
theorem count_ten {N : Nat} (hN : 1 ≤ N) :
    N ^ 7 < 1280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * reachesOneUpToCount N ^ 10 := by
  have hc1 : 1 ≤ reachesOneUpToCount N := by
    have h := TreeHalf.count_mono hN
    have h1 : reachesOneUpToCount 1 = 1 := by decide
    omega
  rcases Nat.lt_or_ge N 10 with hsmall | hbig
  · have : 1 ≤ reachesOneUpToCount N ^ 10 := Nat.pow_pos hc1
    have : N ^ 7 < 10000000 := by
      have : N ^ 7 ≤ 9 ^ 7 := Nat.pow_le_pow_left (by omega) 7
      omega
    omega
  obtain ⟨y, hy1, hy2⟩ := TreeHalf.exists_bracket_ten N hbig
  have hcl := (claims y 5 TreeHalf.root_five).1
  unfold claimF at hcl
  have hA := A_five_pos
  have hS : S 5 (2 ^ y * 5) ≤ reachesOneUpToCount N := by
    apply Nat.le_trans (S_five_le_count (2 ^ y * 5))
    apply TreeHalf.count_mono
    omega
  have h1 : 13 ^ y ≤ 8 ^ y * K * reachesOneUpToCount N := by
    have h5 : 5 % 729 = 5 := rfl
    rw [h5] at hcl
    have : 1 * 13 ^ y ≤ A 5 * 13 ^ y := Nat.mul_le_mul_right _ hA
    have := Nat.mul_le_mul_left (8 ^ y * K) hS
    omega
  have h2 : (13 ^ y) ^ 10 ≤ (8 ^ y * K * reachesOneUpToCount N) ^ 10 := Nat.pow_le_pow_left h1 10
  have hL : (13 ^ y) ^ 10 = 137858491849 ^ y := by
    rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
  have hR : (8 ^ y * K * reachesOneUpToCount N) ^ 10
      = 1073741824 ^ y * (K ^ 10 * reachesOneUpToCount N ^ 10) := by
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm y 10, Nat.pow_mul,
      show (8:Nat) ^ 10 = 1073741824 from rfl, Nat.mul_assoc]
  rw [hL, hR, K_ten] at h2
  have h3 := Nat.le_trans (thirteen_pow y) h2
  have h4 : 1073741824 ^ y * 128 ^ y
      ≤ 1073741824 ^ y * (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * reachesOneUpToCount N ^ 10) := by
    rw [Nat.mul_comm (1073741824 ^ y) (128 ^ y)]
    exact h3
  have h5 : 128 ^ y ≤ 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * reachesOneUpToCount N ^ 10 :=
    Nat.le_of_mul_le_mul_left h4 (Nat.pow_pos (by decide))
  have hN7 : N ^ 7 < (20 * 2 ^ y) ^ 7 := Nat.pow_lt_pow_left hy2 (by decide)
  have h20 : (20 * 2 ^ y) ^ 7 = 1280000000 * 128 ^ y := by
    rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm y 7, Nat.pow_mul]
  rw [h20] at hN7
  omega

end TreeSevenTenths
end Collatz
