import Collatz.Exploration.BalancedResidue
import Collatz.Exploration.BandClock
import Collatz.Core.Reach

/-! Arbitrarily long ordinary Collatz prefixes in [n,6n]. The start depends on
the horizon. This excludes uniform band clocks, never asserts an infinite floor. -/
namespace Collatz.Exploration.SixBandPrefixes
open BalancedResidue

/-- Split the modulus at any earlier accelerated time. -/
theorem power_split {j K : Nat} (hj : j ≤ K) : 2^j*2^(K-j) = (2:Nat)^K := by
  rw [← Nat.pow_add]
  congr 1
  omega

def slope (K r j : Nat) : Nat := 3^oddCount r j*2^(K-j)

/-- The exact affine trace of a large representative at an earlier time. -/
theorem class_trace {j K : Nat} (hj : j ≤ K) (m r : Nat) :
    acceleratedOrbit j (2^K*m+r) = slope K r j*m+acceleratedOrbit j r := by
  rw [← power_split hj, Nat.mul_assoc, Congruence.accOrbit_pow_two_mul_add]
  simp only [slope, Nat.mul_assoc]

theorem slope_bounds {K r j : Nat} (h : Safe K r) (hj : j ≤ K) :
    2^K ≤ slope K r j ∧ slope K r j < 3*2^K := by
  obtain ⟨hl,hu⟩ := h.1 j hj
  have hp : 0 < (2:Nat)^(K-j) := Nat.pow_pos (by decide)
  have hlo := Nat.mul_le_mul_right (2^(K-j)) hl
  have hhi := Nat.mul_lt_mul_of_pos_right hu hp
  rw [power_split hj] at hlo
  simp only [Nat.mul_assoc, power_split hj] at hhi
  exact ⟨hlo,hhi⟩

/-- Away from time zero, an odd power of three cannot equal an even power of two. -/
theorem slope_strict_lower {K r j : Nat} (h : Safe K r) (hj : j ≤ K)
    (hpos : 0 < j) : 2^K < slope K r j := by
  have hlow := (h.1 j hj).1
  have hodd : (3^oddCount r j)%2 = 1 := by simp [Nat.pow_mod]
  have heven : ((2:Nat)^j)%2 = 0 := Arith.two_pow_even hpos
  have hs : 2^j < 3^oddCount r j := by omega
  have hp : 0 < (2:Nat)^(K-j) := Nat.pow_pos (by decide)
  have hm := Nat.mul_lt_mul_of_pos_right hs hp
  rw [power_split hj] at hm
  exact hm

theorem slope_before_odd {K r j : Nat} (h : Safe K r) (hj : j < K)
    (ho : acceleratedOrbit j r % 2 = 1) : slope K r j < 2*2^K := by
  have hs := h.2 j hj ho
  have hp : 0 < (2:Nat)^(K-j) := Nat.pow_pos (by decide)
  have hm := Nat.mul_lt_mul_of_pos_right hs hp
  simpa only [slope, Nat.mul_assoc, power_split (Nat.le_of_lt hj)] using hm

/-- An integer coefficient gap absorbs a bounded affine offset at large scale. -/
theorem gap_upper {a b c m : Nat} (hab : a < b) (hc : c < m) : a*m+c < b*m := by
  have hm := Nat.mul_le_mul_right m (show a+1 ≤ b by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem gap_lower {a b r m : Nat} (hab : b < a) (hr : r ≤ m) : b*m+r ≤ a*m := by
  have hm := Nat.mul_le_mul_right m (show b+1 ≤ a by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem acc_step_growth (n : Nat) : acceleratedStep n+1 ≤ 4*(n+1) := by
  unfold acceleratedStep
  split <;> omega

/-- A coarse value bound, used only to choose a large source representative. -/
theorem acc_growth_bound (k r : Nat) : acceleratedOrbit k r+1 ≤ 4^k*(r+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [acceleratedOrbit_succ_step]
    have hstep := acc_step_growth (acceleratedOrbit k r)
    have hm := Nat.mul_le_mul_left 4 ih
    have hp : (4:Nat)^(k+1)*(r+1) = 4*(4^k*(r+1)) := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [hp]
    exact Nat.le_trans hstep hm

theorem acc_prefix_bound {j K : Nat} (hj : j ≤ K) (r : Nat) :
    acceleratedOrbit j r < 4^K*(r+1) := by
  have h0 := acc_growth_bound j r
  have hp : (4:Nat)^j ≤ 4^K := Nat.pow_le_pow_right (by decide) hj
  have hm := Nat.mul_le_mul_right (r+1) hp
  omega

/-- Transfer bounded accelerated states and bounded odd peaks to an ordinary prefix. -/
theorem ordinary_coverage (K b u n : Nat)
    (ha : ∀ j, j ≤ K → b ≤ acceleratedOrbit j n ∧ acceleratedOrbit j n ≤ u)
    (hp : ∀ j, j < K → acceleratedOrbit j n % 2 = 1 →
      3*acceleratedOrbit j n+1 ≤ u) :
    ∀ k, k ≤ K → b ≤ orbit k n ∧ orbit k n ≤ u := by
  induction K generalizing n with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst k
    exact ha 0 (by decide)
  | succ K ih =>
    have ha0 := ha 0 (by omega)
    change b ≤ n ∧ n ≤ u at ha0
    have htail : ∀ j, j ≤ K →
        b ≤ acceleratedOrbit j (acceleratedStep n) ∧ acceleratedOrbit j (acceleratedStep n) ≤ u := by
      intro j hj
      exact ha (j+1) (by omega)
    have ptail : ∀ j, j < K → acceleratedOrbit j (acceleratedStep n)%2 = 1 →
        3*acceleratedOrbit j (acceleratedStep n)+1 ≤ u := by
      intro j hj ho
      exact hp (j+1) (by omega) ho
    have hi := ih (acceleratedStep n) htail ptail
    intro k hk
    by_cases hk0 : k = 0
    · subst k; exact ha0
    · rcases Arith.mod_two_eq_zero_or_one n with he | ho
      · have hstep := Reach.accStep_eq_step_of_even he
        have hv := hi (k-1) (by omega)
        have heq : k = (k-1)+1 := by omega
        rw [heq, orbit_succ_steps, ← hstep]
        exact hv
      · have hn : 0 < n := by omega
        have hstep := Reach.step_odd hn ho
        by_cases hk1 : k = 1
        · subst k
          have hpeak := hp 0 (by omega) ho
          change 3*n+1 ≤ u at hpeak
          simp only [orbit, hstep]
          omega
        · have hv := hi (k-2) (by omega)
          have heq : k = (k-2)+1+1 := by omega
          rw [heq, orbit_succ_steps, orbit_succ_steps,
            ← Reach.accStep_eq_step_step_of_odd hn ho]
          exact hv

/-- All sufficiently large members of a balanced residue class have the desired prefix. -/
theorem large_class_prefix {K r m : Nat} (hr : r < 2^K) (hs : Safe K r)
    (hm : r+6*(4^K*(r+1))+1 ≤ m) :
    ∀ k, k ≤ K → 2^K*m+r ≤ orbit k (2^K*m+r) ∧
      orbit k (2^K*m+r) ≤ 6*(2^K*m+r) := by
  let n := 2^K*m+r
  have ha : ∀ j, j ≤ K → n ≤ acceleratedOrbit j n ∧ acceleratedOrbit j n ≤ 6*n := by
    intro j hj
    have hb := acc_prefix_bound hj r
    have hsl := slope_bounds hs hj
    have ht := class_trace hj m r
    change acceleratedOrbit j n = _ at ht
    refine ⟨?_,?_⟩
    · by_cases hz : j = 0
      · subst j; exact Nat.le_refl n
      · have hl := gap_lower (slope_strict_lower hs hj (by omega)) (show r ≤ m by omega)
        rw [ht]
        exact Nat.le_trans hl (Nat.le_add_right _ _)
    · have hu := gap_upper hsl.2 (show acceleratedOrbit j r < m by omega)
      rw [ht]
      dsimp [n]
      have hmul : 3*(2^K*m) ≤ 6*(2^K*m+r) := by omega
      have hh : slope K r j*m+acceleratedOrbit j r < 3*(2^K*m) := by
        simpa only [Nat.mul_assoc] using hu
      omega
  have hp : ∀ j, j < K → acceleratedOrbit j n%2 = 1 → 3*acceleratedOrbit j n+1 ≤ 6*n := by
    intro j hj ho
    have hv := vector_class K m r hr
    have hb := bit_of_vector hv hj
    have hslope := slope_before_odd hs hj (hb.symm.trans ho)
    have hraw := Nat.mul_lt_mul_of_pos_left hslope (show 0 < 3 by decide)
    have hcoef : 3*slope K r j < 6*2^K := by simpa only [← Nat.mul_assoc, Nat.reduceMul] using hraw
    have hc := acc_prefix_bound (Nat.le_of_lt hj) r
    have hu := gap_upper hcoef (show 3*acceleratedOrbit j r+1 < m by omega)
    have ht := class_trace (Nat.le_of_lt hj) m r
    change acceleratedOrbit j n = _ at ht
    rw [ht]
    dsimp [n]
    have heq : 3*(slope K r j*m+acceleratedOrbit j r)+1 =
        (3*slope K r j)*m+(3*acceleratedOrbit j r+1) := by
      simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
    rw [heq]
    have hh : (3*slope K r j)*m+(3*acceleratedOrbit j r+1) < 6*(2^K*m) := by
      simpa only [Nat.mul_assoc] using hu
    omega
  exact ordinary_coverage K n (6*n) n ha hp

/-- Horizons and size thresholds are arbitrary, but their witnesses may differ. -/
theorem arbitrarily_long_prefixes (K N : Nat) :
    ∃ n, N < n ∧ 1 < n ∧ ∀ k, k ≤ K → n ≤ orbit k n ∧ orbit k n ≤ 6*n := by
  obtain ⟨r,hr,hs⟩ := exists_safe K
  let m := N+r+6*(4^K*(r+1))+2
  let n := 2^K*m+r
  have hp : 0 < (2:Nat)^K := Nat.pow_pos (by decide)
  have hlarge : m ≤ 2^K*m := Nat.le_mul_of_pos_left m hp
  have hmn : m ≤ n := Nat.le_trans hlarge (Nat.le_add_right _ _)
  refine ⟨n, Nat.lt_of_lt_of_le ?_ hmn, Nat.lt_of_lt_of_le ?_ hmn,
    large_class_prefix hr hs (by dsimp [m]; omega)⟩ <;> dsimp [m] <;> omega

/-- Each finite horizon has an entire large arithmetic progression of witnesses. -/
theorem exists_class (K : Nat) :
    ∃ r M, r < 2^K ∧ ∀ m, M ≤ m → ∀ k, k ≤ K →
      2^K*m+r ≤ orbit k (2^K*m+r) ∧ orbit k (2^K*m+r) ≤ 6*(2^K*m+r) := by
  obtain ⟨r,hr,hs⟩ := exists_safe K
  exact ⟨r,r+6*(4^K*(r+1))+1,hr,fun m hm => large_class_prefix hr hs hm⟩

/-- The obstruction persists at every rational threshold at least six. -/
theorem no_clock_at_least_six (P Q K : Nat) (hP : 6*Q ≤ P) :
    ¬ BandClock.ExitClock P Q K := by
  intro hc
  obtain ⟨n,_,hn,hbounds⟩ := arbitrarily_long_prefixes K 0
  apply BandClock.no_band_through (b := n) (n := n) hc hn
  intro k hk
  obtain ⟨hl,hu⟩ := hbounds k hk
  have hm := Nat.mul_le_mul_left Q hu
  have hp := Nat.mul_le_mul_right n hP
  have heq : Q*(6*n) = (6*Q)*n := by ac_rfl
  rw [heq] at hm
  exact ⟨hl,Nat.le_trans hm hp⟩

theorem no_six_band_clock (K : Nat) : ¬ BandClock.ExitClock 6 1 K := by
  intro hc
  obtain ⟨n,_,hn,hbounds⟩ := arbitrarily_long_prefixes K 0
  apply BandClock.no_band_through (b := n) (n := n) hc hn
  intro k hk
  simpa using hbounds k hk

end Collatz.Exploration.SixBandPrefixes
