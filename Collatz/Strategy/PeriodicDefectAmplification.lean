import Collatz.Strategy.PeriodicDefectTransport

/-! A finite transfer-weight certificate for exponential error amplification.
Expanding modular ranges are essential. No convergence claim is made. -/

namespace Collatz.PeriodicDefectAmplification
open Collatz.Sum PeriodicRigidity PeriodicDefectMinimum PeriodicDefectTransport

theorem period_of_dvd {g : Nat → Nat} {L M : Nat}
    (hp : HasPeriod g L) (hd : L ∣ M) : HasPeriod g M := by
  obtain ⟨q,hq⟩ := hd
  intro n
  rw [hq,Nat.mul_comm L q]
  exact period_mul hp n q

def adjoint (w : Nat → Nat) (n : Nat) : Nat :=
  w (2*n) + if n%3=2 then 3*w ((2*n-1)/3) else 0

theorem adjoint_period {L : Nat} {w : Nat → Nat} (hp : HasPeriod w L) :
    HasPeriod (adjoint w) (3*L) := by
  intro n
  unfold adjoint
  have hm : (n+3*L)%3=n%3 := by omega
  have he : 2*(n+3*L)=2*n+6*L := by omega
  rw [hm,he,period_mul hp _ 6]
  by_cases h : n%3=2
  · rw [if_pos h,if_pos h]
    have hd : (2*n+6*L-1)/3=(2*n-1)/3+2*L := by omega
    rw [hd,period_mul hp _ 2]
  · simp [h]

/-- Duality between pullback of an error and transfer of its weight. -/
theorem weighted_pull {M : Nat} (h3 : M%3=0) {g w : Nat → Nat}
    (hg : HasPeriod g M) (hw : HasPeriod w (M/3)) :
    sumRange (2*M) (fun n => w n * pull g n) =
      sumRange M (fun n => adjoint w n * g n) := by
  have hM : M=3*(M/3) := by omega
  have he (i : Nat) : pull g (2*i)=g i := by simp [pull,acceleratedStep]
  have ho (i : Nat) : pull g (2*i+1)=g (3*i+2) := by
    unfold pull acceleratedStep
    rw [if_neg (by omega : ¬(2*i+1)%2=0)]
    congr 1
    omega
  have hp : HasPeriod (fun i => w (2*i+1)*g (3*i+2)) (M/3) := by
    intro i
    change w (2*(i+M/3)+1)*g (3*(i+M/3)+2) = _
    rw [show 2*(i+M/3)+1=(2*i+1)+2*(M/3) by omega,
      show 3*(i+M/3)+2=(3*i+2)+M by omega,period_mul hw _ 2,hg]
  have hs : sumRange M (fun i => w (2*i+1)*g (3*i+2)) =
      3*sumRange (M/3) (fun i => w (2*i+1)*g (3*i+2)) := by
    conv => lhs; rw [hM]
    exact sum_period_three hp
  have ht : sumRange M (fun n => if n%3=2 then w ((2*n-1)/3)*g n else 0) =
      sumRange (M/3) (fun i => w (2*i+1)*g (3*i+2)) := by
    change classMass M 2 (fun n => w ((2*n-1)/3)*g n) = _
    conv => lhs; rw [hM]
    rw [class_two]
    apply sumRange_congr
    intro i _
    rw [show (2*(3*i+2)-1)/3=2*i+1 by omega]
  rw [sum_even_odd]
  simp only [he,ho]
  rw [hs,← ht,← sumRange_const_mul,← sumRange_add]
  apply sumRange_congr
  intro n _
  unfold adjoint
  by_cases hn : n%3=2 <;>
    simp only [hn,if_true,if_false,Nat.add_mul,Nat.mul_assoc,
      Nat.mul_zero,Nat.add_zero]

def weights : Nat → Nat → Nat
  | 0, n => if n%3=0 then 0 else 1
  | k+1, n => adjoint (weights k) n

theorem weights_period (k : Nat) : HasPeriod (weights k) (3^(k+1)) := by
  induction k with
  | zero => intro n; simp [weights]
  | succ k ih =>
    have he : 3^(k+1+1)=3*(3^(k+1)) := Nat.pow_succ'
    rw [he]
    exact adjoint_period ih

/-- An actual finite table, not an unbounded test, suffices. -/
theorem bound_of_table (b A : Nat)
    (table : ∀ r : Fin (3^(b+1)),
      A*(if r.val%3=0 then 0 else 1) ≤ weights b r.val) (n : Nat) :
    A*(if n%3=0 then 0 else 1) ≤ weights b n := by
  have h := table ⟨n%(3^(b+1)),Nat.mod_lt n (Nat.pow_pos (by decide))⟩
  have hd : 3 ∣ 3^(b+1) := ⟨3^b,Nat.pow_succ'⟩
  have hm : n%(3^(b+1))%3=n%3 := Nat.mod_mod_of_dvd n hd
  rw [period_mod (weights_period b) n]
  simpa only [hm] using h

theorem pulls_comm (k : Nat) (g : Nat → Nat) : pulls k (pull g)=pulls (k+1) g := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg pull ih

/-- A fixed ternary certificate controls observables of unbounded compatible period. -/
theorem weighted_iterate (k : Nat) {M : Nat} {g : Nat → Nat}
    (hp : HasPeriod g M) (hd : 3^(k+1) ∣ M) :
    coreTower M g k = sumRange M (fun n => weights k n * g n) := by
  induction k generalizing M g with
  | zero =>
    unfold coreTower coreMass
    simp only [pulls,Nat.pow_zero,Nat.one_mul,weights]
    apply sumRange_congr
    intro n _
    split <;> simp
  | succ k ih =>
    obtain ⟨q,hq⟩ := hd
    have hp3 : 3^(k+1+1)=3*(3^(k+1)) := Nat.pow_succ'
    have hquot : M/3=3^(k+1)*q := by
      rw [hq,hp3,Nat.mul_assoc,Nat.mul_div_right] <;> omega
    have hd' : 3^(k+1) ∣ 2*M := by
      refine ⟨6*q,?_⟩
      rw [hq,hp3]
      calc
        2*(3*3^(k+1)*q) = 3^(k+1)*((2*3)*q) := by ac_rfl
        _ = _ := rfl
    have hi := ih (pull_period hp) hd'
    have he : 2^(k+1)*M=2^k*(2*M) := by rw [Nat.pow_succ]; ac_rfl
    unfold coreTower at hi ⊢
    rw [he,← pulls_comm,hi]
    have hM3 : M%3=0 := by rw [hq,hp3,Nat.mul_assoc]; omega
    exact weighted_pull hM3 hp
      (period_of_dvd (weights_period k) ⟨q,hquot⟩)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- Exhaustive finite arithmetic checked by Lean's kernel. -/
theorem four_certificate : ∀ r : Fin 243,
    4*(if r.val%3=0 then 0 else 1) ≤ weights 4 r.val := by decide

theorem four_weight_bound (n : Nat) :
    4*(if n%3=0 then 0 else 1) ≤ weights 4 n :=
  bound_of_table 4 4 four_certificate n

/-- The coefficient four is optimal for this four-step pointwise certificate. -/
theorem four_coefficient_optimal (A : Nat)
    (h : ∀ n, A*(if n%3=0 then 0 else 1) ≤ weights 4 n) : A ≤ 4 := by
  have h4 := h 4
  simpa [weights,adjoint] using h4

/-- A three-step certificate of this form cannot give strict amplification. -/
theorem three_coefficient_le_one (A : Nat)
    (h : ∀ n, A*(if n%3=0 then 0 else 1) ≤ weights 3 n) : A ≤ 1 := by
  have h7 := h 7
  simpa [weights,adjoint] using h7

theorem four_growth_compatible {M : Nat} {g : Nat → Nat}
    (hp : HasPeriod g M) (hd : 243 ∣ M) :
    4*coreMass M g ≤ coreTower M g 4 := by
  rw [weighted_iterate 4 hp hd]
  unfold coreMass
  rw [← sumRange_const_mul]
  apply sumRange_le
  intro n _
  have h := Nat.mul_le_mul_right (g n) (four_weight_bound n)
  by_cases hn : n%3=0 <;> simp_all

theorem sum_repeat {M : Nat} {g : Nat → Nat} (hp : HasPeriod g M) (q : Nat) :
    sumRange (q*M) g=q*sumRange M g := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul,sumRange_split,ih]
    have hs : sumRange M (fun i => g (q*M+i))=sumRange M g := by
      apply sumRange_congr
      intro i _
      rw [Nat.add_comm]
      exact period_mul hp i q
    rw [hs,Nat.succ_mul]

theorem core_period {M : Nat} (h3 : M%3=0) {g : Nat → Nat}
    (hp : HasPeriod g M) : HasPeriod (fun n => if n%3=0 then 0 else g n) M := by
  intro n
  have hm : (n+M)%3=n%3 := by omega
  change (if (n+M)%3=0 then 0 else g (n+M)) = _
  rw [hm,hp n]

theorem core_repeat {M : Nat} (h3 : M%3=0) {g : Nat → Nat}
    (hp : HasPeriod g M) (q : Nat) : coreMass (q*M) g=q*coreMass M g :=
  sum_repeat (core_period h3 hp) q

theorem coreTower_repeat {M : Nat} (h3 : M%3=0) {g : Nat → Nat}
    (hp : HasPeriod g M) (q k : Nat) : coreTower (q*M) g k=q*coreTower M g k := by
  unfold coreTower
  have he : 2^k*(q*M)=q*(2^k*M) := by ac_rfl
  rw [he]
  exact core_repeat (by simp [Nat.mul_mod,h3]) (pulls_period hp k) q

/-- Reusable certificate compiler. Checking only 3^(b+1) transfer weights
proves a b-step amplification bound at EVERY positive ternary-divisible period.
The proof enlarges the period temporarily, then cancels the repetition factor. -/
theorem growth_of_certificate (b A : Nat)
    (certificate : ∀ n, A*(if n%3=0 then 0 else 1) ≤ weights b n)
    {M : Nat} (h3 : M%3=0) {g : Nat → Nat} (hp : HasPeriod g M) :
    A*coreMass M g ≤ coreTower M g b := by
  have hbig : HasPeriod g (3^b*M) := period_of_dvd hp (Nat.dvd_mul_left M (3^b))
  have hd : 3^(b+1) ∣ 3^b*M := by
    refine ⟨M/3,?_⟩
    rw [Nat.pow_succ]
    have hm : M=3*(M/3) := by omega
    calc
      3^b*M = 3^b*(3*(M/3)) := congrArg (fun x => 3^b*x) hm
      _ = _ := by ac_rfl
  have hl : A*coreMass (3^b*M) g ≤ coreTower (3^b*M) g b := by
    rw [weighted_iterate b hbig hd]
    unfold coreMass
    rw [← sumRange_const_mul]
    apply sumRange_le
    intro n _
    have hn := Nat.mul_le_mul_right (g n) (certificate n)
    by_cases h : n%3=0 <;> simp_all
  rw [core_repeat h3 hp,coreTower_repeat h3 hp] at hl
  have hre : A*(3^b*coreMass M g)=3^b*(A*coreMass M g) := by ac_rfl
  rw [hre] at hl
  by_cases h : A*coreMass M g ≤ coreTower M g b
  · exact h
  · have hc := Nat.mul_lt_mul_of_pos_left (show coreTower M g b < A*coreMass M g by omega)
      (show 0 < 3^b from Nat.pow_pos (by decide : 0<(3:Nat)))
    omega

theorem four_growth {M : Nat} (h3 : M%3=0) {g : Nat → Nat}
    (hp : HasPeriod g M) : 4*coreMass M g ≤ coreTower M g 4 :=
  growth_of_certificate 4 4 four_weight_bound h3 hp

theorem pulls_add (a b : Nat) (g : Nat → Nat) :
    pulls a (pulls b g)=pulls (a+b) g := by
  induction a with
  | zero => simp [pulls]
  | succ a ih =>
    simp only [pulls,Nat.succ_add]
    exact congrArg pull ih

theorem coreTower_add (M : Nat) (g : Nat → Nat) (a b : Nat) :
    coreTower (2^b*M) (pulls b g) a=coreTower M g (a+b) := by
  unfold coreTower
  rw [pulls_add,Nat.pow_add,Nat.mul_assoc]

theorem iterated_growth (b A : Nat)
    (certificate : ∀ n, A*(if n%3=0 then 0 else 1) ≤ weights b n)
    {M : Nat} (h3 : M%3=0) {g : Nat → Nat} (hp : HasPeriod g M) (k : Nat) :
    A^k*coreMass M g ≤ coreTower M g (b*k) := by
  induction k with
  | zero => simp [coreTower,pulls]
  | succ k ih =>
    have hnext := growth_of_certificate b A certificate
      (by simp [Nat.mul_mod,h3] : (2^(b*k)*M)%3=0) (pulls_period hp (b*k))
    rw [coreTower_add] at hnext
    have hm := Nat.mul_le_mul_left A ih
    have he : A^(k+1)*coreMass M g=A*(A^k*coreMass M g) := by
      rw [Nat.pow_succ]; ac_rfl
    rw [he,show b*(k+1)=b+b*k by rw [Nat.mul_succ,Nat.add_comm]]
    exact Nat.le_trans hm hnext

/-- Public finite-certificate interface: one ternary table yields an infinite
family of bounds, uniformly over every ternary-divisible period and every scale. -/
theorem finite_certificate_amplifies (b A : Nat)
    (table : ∀ r : Fin (3^(b+1)),
      A*(if r.val%3=0 then 0 else 1) ≤ weights b r.val)
    {M : Nat} (h3 : M%3=0) {g : Nat → Nat} (hp : HasPeriod g M) (k : Nat) :
    A^k*coreMass M g ≤ coreTower M g (b*k) :=
  iterated_growth b A (bound_of_table b A table) h3 hp k

/-- A finite table also controls defects of actual pulled-back Boolean labels. -/
theorem defect_growth_of_table (b A : Nat)
    (table : ∀ r : Fin (3^(b+1)),
      A*(if r.val%3=0 then 0 else 1) ≤ weights b r.val)
    {m : Nat} (h3 : m%3=0) {f : Nat → Bool}
    (hp : HasPeriod f m) (k : Nat) :
    A^k*coreDefects m f ≤ defectTower m f (b*k) := by
  have hl := finite_certificate_amplifies b A table (by omega : (2*m)%3=0)
    (error_period hp) k
  rw [defectTower_eq_massTower]
  apply Nat.le_trans hl
  unfold coreTower massTower coreMass
  apply sumRange_le
  intro n _
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

/-- Uniform exponential amplification for the original Boolean defect counts. -/
theorem defect_exponential_growth {m : Nat} (h3 : m%3=0) {f : Nat → Bool}
    (hp : HasPeriod f m) (k : Nat) :
    4^k*coreDefects m f ≤ defectTower m f (4*k) :=
  defect_growth_of_table 4 4 four_certificate h3 hp k

/-- A constant tower or an exponential lower bound; no intermediate regime. -/
theorem defect_dichotomy {m : Nat} (hm : 0<m) (h3 : m%3=0)
    {f : Nat → Bool} (hp : HasPeriod f m) :
    (∀ k, defectTower m f k=defectCount m f) ∨
      (∀ k, 4^k ≤ defectTower m f (4*k)) := by
  by_cases hz : coreDefects m f=0
  · left
    have hs := (core_zero_iff (by omega : 0<2*m) (by omega : (2*m)%3=0)
      (error_period hp)).mp hz
    intro k
    rw [defectTower_eq_massTower]
    exact mass_constant_of_supported (by omega) (error_period hp) hs k
  · right
    intro k
    have hl := Nat.mul_le_mul_left (4^k) (show 1≤coreDefects m f by omega)
    exact Nat.le_trans (by simpa using hl) (defect_exponential_growth h3 hp k)

/-- The complementary case is exact doubling, by the pre-existing
mass-conservation theorem. This is not a novelty claim. -/
theorem massTower_exact_doubling {M : Nat} (hM : 0<M) (h3 : M%3≠0)
    {g : Nat → Nat} (hp : HasPeriod g M) (k : Nat) :
    massTower M g k=2^k*sumRange M g := by
  have hn : ∀ j, (2^j*M)%3≠0 := by
    intro j
    induction j with
    | zero => simpa using h3
    | succ j ih =>
      rw [show 2^(j+1)*M=2*(2^j*M) by rw [Nat.pow_succ]; ac_rfl]
      omega
  induction k with
  | zero => simp [massTower,pulls]
  | succ k ih =>
    have he : 2^(k+1)*M=2*(2^k*M) := by rw [Nat.pow_succ]; ac_rfl
    have hh := mass_conservation (Nat.mul_pos (Nat.pow_pos (by decide)) hM)
      (hn k) (pulls_period hp k)
    change sumRange (2*(2^k*M)) (pull (pulls k g)) = _ at hh
    unfold massTower
    rw [he,pulls,hh,sum_repeat (pulls_period hp k) 2]
    change 2*massTower M g k=2^(k+1)*sumRange M g
    rw [ih,Nat.pow_succ]
    ac_rfl

theorem defect_exact_doubling {m : Nat} (hm : 0<m) (h3 : m%3≠0)
    {f : Nat → Bool} (hp : HasPeriod f m) (k : Nat) :
    defectTower m f k=2^k*defectCount m f := by
  rw [defectTower_eq_massTower]
  exact massTower_exact_doubling (by omega) (by omega) (error_period hp) k

/-- Constant-or-exponential behavior holds at every positive period. -/
theorem defect_dichotomy_all {m : Nat} (hm : 0<m)
    {f : Nat → Bool} (hp : HasPeriod f m) :
    (∀ k, defectTower m f k=defectCount m f) ∨
      (∀ k, 4^k ≤ defectTower m f (4*k)) := by
  by_cases h3 : m%3=0
  · exact defect_dichotomy hm h3 hp
  · by_cases hz : defectCount m f=0
    · left
      intro k
      rw [defect_exact_doubling hm h3 hp,hz,Nat.mul_zero]
    · right
      intro k
      rw [defect_exact_doubling hm h3 hp]
      have hl := Nat.mul_le_mul_left (2^(4*k)) (show 1≤defectCount m f by omega)
      have he : 4^k ≤ 2^(4*k) := by
        rw [Nat.pow_mul]
        exact Nat.pow_le_pow_left (by decide : 4≤2^4) k
      exact Nat.le_trans he (by simpa using hl)

end Collatz.PeriodicDefectAmplification
