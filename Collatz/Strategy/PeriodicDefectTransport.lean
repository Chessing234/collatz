import Collatz.Strategy.PeriodicDefectMinimum

/-!
Transport of periodic errors under pullback by the accelerated Collatz map.
The mass identities below concern expanding residue ranges, not individual
infinite integer orbits. They do not assert convergence or historical novelty.
-/

namespace Collatz.PeriodicDefectTransport
open Collatz.Sum PeriodicRigidity PeriodicDefectMinimum

def pull (g : Nat → Nat) (n : Nat) : Nat := g (acceleratedStep n)

def coreMass (M : Nat) (g : Nat → Nat) : Nat :=
  sumRange M (fun n => if n % 3 = 0 then 0 else g n)

def classMass (M r : Nat) (g : Nat → Nat) : Nat :=
  sumRange M (fun n => if n % 3 = r then g n else 0)

theorem pull_period {M : Nat} {g : Nat → Nat} (hp : HasPeriod g M) :
    HasPeriod (pull g) (2*M) := by
  intro n
  unfold pull
  rw [step_add_even]
  split
  · exact hp _
  · exact period_mul hp _ 3

theorem sum_triples (L : Nat) (g : Nat → Nat) :
    sumRange (3*L) g = sumRange L (fun i => g (3*i)) +
      sumRange L (fun i => g (3*i+1)) + sumRange L (fun i => g (3*i+2)) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [show 3*(L+1) = ((3*L+1)+1)+1 by omega]
    simp only [sumRange_succ]
    rw [ih]
    omega

theorem class_one (L : Nat) (g : Nat → Nat) :
    classMass (3*L) 1 g = sumRange L (fun i => g (3*i+1)) := by
  unfold classMass
  rw [sum_triples]
  simp [sumRange_const]

theorem class_two (L : Nat) (g : Nat → Nat) :
    classMass (3*L) 2 g = sumRange L (fun i => g (3*i+2)) := by
  unfold classMass
  rw [sum_triples]
  simp [sumRange_const]

theorem core_split (M : Nat) (g : Nat → Nat) :
    coreMass M g = classMass M 1 g + classMass M 2 g := by
  unfold coreMass classMass
  rw [← sumRange_add]
  apply sumRange_congr
  intro n _
  have : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases this with h|h|h <;> simp [h]

theorem sum_period_three {L : Nat} {h : Nat → Nat} (hp : HasPeriod h L) :
    sumRange (3*L) h = 3*sumRange L h := by
  rw [show 3*L=L+2*L by omega, sumRange_split, sumRange_two_mul]
  have h1 : sumRange L (fun i => h (L+i)) = sumRange L h :=
    sumRange_congr (fun i _ => by simpa [Nat.add_comm] using hp i)
  have h2 : sumRange L (fun i => h (L+(L+i))) = sumRange L h :=
    sumRange_congr (fun i _ => by
      rw [show L+(L+i)=i+2*L by omega]
      exact period_mul hp i 2)
  rw [h1,h2]
  omega

theorem odd_mass {M : Nat} (h3 : M%3=0) {g : Nat → Nat}
    (hp : HasPeriod g M) :
    sumRange M (fun i => g (3*i+2)) = 3*classMass M 2 g := by
  have hM : M=3*(M/3) := by omega
  have hq : HasPeriod (fun i => g (3*i+2)) (M/3) := by
    intro i
    change g (3*(i+M/3)+2) = g (3*i+2)
    have he : 3*(i+M/3)+2 = (3*i+2)+M := by omega
    rw [he, hp]
  rw [hM, sum_period_three hq, class_two]

/-- Exact multiplicity formula: targets 2 mod 3 have three extra predecessors. -/
theorem mass_pull {M : Nat} (h3 : M%3=0) {g : Nat → Nat}
    (hp : HasPeriod g M) :
    sumRange (2*M) (pull g) = sumRange M g + 3*classMass M 2 g := by
  rw [sum_even_odd]
  have he (n : Nat) : pull g (2*n) = g n := by simp [pull, acceleratedStep]
  have ho (n : Nat) : pull g (2*n+1) = g (3*n+2) := by
    unfold pull acceleratedStep
    rw [if_neg (by omega : ¬ (2*n+1)%2=0)]
    congr 1
    omega
  simp only [he,ho]
  rw [odd_mass h3 hp]

theorem core_pull_ge (M : Nat) (g : Nat → Nat) :
    coreMass M g ≤ coreMass (2*M) (pull g) := by
  unfold coreMass
  rw [sum_even_odd]
  have he : sumRange M (fun i => if (2*i)%3=0 then 0 else pull g (2*i)) =
      sumRange M (fun i => if i%3=0 then 0 else g i) := by
    apply sumRange_congr
    intro i _
    have hs : pull g (2*i)=g i := by simp [pull,acceleratedStep]
    rw [hs]
    have hi : (2*i)%3=0 ↔ i%3=0 := by omega
    simp only [hi]
  rw [he]
  omega

theorem class_two_pull_ge (M : Nat) (g : Nat → Nat) :
    classMass M 1 g ≤ classMass (2*M) 2 (pull g) := by
  unfold classMass
  rw [sum_even_odd]
  have he : sumRange M (fun i => if (2*i)%3=2 then pull g (2*i) else 0) =
      sumRange M (fun i => if i%3=1 then g i else 0) := by
    apply sumRange_congr
    intro i _
    have hs : pull g (2*i)=g i := by simp [pull,acceleratedStep]
    rw [hs]
    have hi : (2*i)%3=2 ↔ i%3=1 := by omega
    simp only [hi]
  rw [he]
  omega

/-- Every unit-modulo-three error contributes at least three additional
copies within two pullbacks. -/
theorem two_step_growth {M : Nat} (h3 : M%3=0) {g : Nat → Nat}
    (hp : HasPeriod g M) :
    sumRange M g + 3*coreMass M g ≤ sumRange (4*M) (pull (pull g)) := by
  rw [show 4*M=2*(2*M) by omega,
    mass_pull (by omega : (2*M)%3=0) (pull_period hp), mass_pull h3 hp]
  have hl := class_two_pull_ge M g
  rw [core_split]
  omega

def pulls : Nat → (Nat → Nat) → Nat → Nat
  | 0, g => g
  | k+1, g => pull (pulls k g)

def massTower (M : Nat) (g : Nat → Nat) (k : Nat) : Nat :=
  sumRange (2^k*M) (pulls k g)

def coreTower (M : Nat) (g : Nat → Nat) (k : Nat) : Nat :=
  coreMass (2^k*M) (pulls k g)

theorem pulls_period {M : Nat} {g : Nat → Nat} (hp : HasPeriod g M) (k : Nat) :
    HasPeriod (pulls k g) (2^k*M) := by
  induction k with
  | zero => simpa [pulls] using hp
  | succ k ih =>
    have he : 2^(k+1)*M = 2*(2^k*M) := by rw [Nat.pow_succ]; ac_rfl
    rw [he]
    exact pull_period ih

theorem coreTower_step (M : Nat) (g : Nat → Nat) (k : Nat) :
    coreTower M g k ≤ coreTower M g (k+1) := by
  have he : 2^(k+1)*M = 2*(2^k*M) := by rw [Nat.pow_succ]; ac_rfl
  simpa [coreTower,pulls,he] using core_pull_ge (2^k*M) (pulls k g)

theorem coreTower_ge (M : Nat) (g : Nat → Nat) (k : Nat) :
    coreMass M g ≤ coreTower M g k := by
  induction k with
  | zero => simp [coreTower,pulls]
  | succ k ih => exact Nat.le_trans ih (coreTower_step M g k)

theorem massTower_two {M : Nat} (h3 : M%3=0) {g : Nat → Nat}
    (hp : HasPeriod g M) (k : Nat) :
    massTower M g k + 3*coreTower M g k ≤ massTower M g (k+2) := by
  have h3' : (2^k*M)%3=0 := by simp [Nat.mul_mod,h3]
  have he : 2^(k+2)*M=4*(2^k*M) := by
    rw [Nat.pow_add]; simp only [show (2:Nat)^2=4 by decide]; ac_rfl
  simpa [massTower,coreTower,pulls,he] using
    two_step_growth h3' (pulls_period hp k)

/-- A uniform quantitative obstruction to bounded pullback mass. -/
theorem linear_growth {M : Nat} (h3 : M%3=0) {g : Nat → Nat}
    (hp : HasPeriod g M) (k : Nat) :
    sumRange M g + 3*k*coreMass M g ≤ massTower M g (2*k) := by
  induction k with
  | zero => simp [massTower,pulls]
  | succ k ih =>
    have hs := massTower_two h3 hp (2*k)
    have hc := Nat.mul_le_mul_left 3 (coreTower_ge M g (2*k))
    have he : 3*(k+1)*coreMass M g=3*k*coreMass M g+3*coreMass M g := by
      rw [Nat.mul_add,Nat.add_mul]
    rw [show 2*(k+1)=2*k+2 by omega,he]
    omega

theorem core_zero_iff {M : Nat} (hM : 0<M) (h3 : M%3=0)
    {g : Nat → Nat} (hp : HasPeriod g M) :
    coreMass M g=0 ↔ ∀ n, n%3 ≠ 0 → g n=0 := by
  constructor
  · intro hz n hn
    have hmod : n%M%3=n%3 := Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero h3)
    have hbound := le_sumRange (fun i => if i%3=0 then 0 else g i)
      (Nat.mod_lt n hM)
    rw [if_neg (by omega : n%M%3 ≠ 0)] at hbound
    change g (n%M) ≤ coreMass M g at hbound
    rw [period_mod hp n]
    omega
  · intro hz
    unfold coreMass
    have he : sumRange M (fun n => if n%3=0 then 0 else g n) =
        sumRange M (fun _ => 0) := by
      apply sumRange_congr
      intro n _
      split
      · rfl
      · exact hz n (by assumption)
    rw [he,sumRange_const,Nat.mul_zero]

theorem step_core {n : Nat} (hn : n%3 ≠ 0) : acceleratedStep n%3 ≠ 0 := by
  unfold acceleratedStep
  split <;> omega

theorem supported_pull {g : Nat → Nat} (hz : ∀ n, n%3 ≠ 0 → g n=0) :
    ∀ n, n%3 ≠ 0 → pull g n=0 := by
  intro n hn
  exact hz _ (step_core hn)

theorem supported_pulls {g : Nat → Nat} (hz : ∀ n, n%3 ≠ 0 → g n=0) (k : Nat) :
    ∀ n, n%3 ≠ 0 → pulls k g n=0 := by
  induction k with
  | zero => exact hz
  | succ k ih => exact supported_pull ih

theorem mass_constant_of_supported {M : Nat} (h3 : M%3=0)
    {g : Nat → Nat} (hp : HasPeriod g M)
    (hz : ∀ n, n%3 ≠ 0 → g n=0) (k : Nat) :
    massTower M g k = sumRange M g := by
  induction k with
  | zero => simp [massTower,pulls]
  | succ k ih =>
    have he : 2^(k+1)*M = 2*(2^k*M) := by rw [Nat.pow_succ]; ac_rfl
    have hz' : classMass (2^k*M) 2 (pulls k g)=0 := by
      unfold classMass
      have hh : sumRange (2^k*M) (fun n => if n%3=2 then pulls k g n else 0) =
          sumRange (2^k*M) (fun _ => 0) := by
        apply sumRange_congr
        intro n _
        split
        · exact supported_pulls hz k n (by omega)
        · rfl
      rw [hh,sumRange_const,Nat.mul_zero]
    unfold massTower
    rw [he,pulls,mass_pull (by simp [Nat.mul_mod,h3]) (pulls_period hp k),hz']
    simpa [massTower] using ih

/-- Boundedness at all scales is detected exactly by the two-step plateau. -/
theorem bounded_iff_supported {M : Nat} (hM : 0<M) (h3 : M%3=0)
    {g : Nat → Nat} (hp : HasPeriod g M) :
    (∃ B, ∀ k, massTower M g k ≤ B) ↔ ∀ n, n%3 ≠ 0 → g n=0 := by
  constructor
  · rintro ⟨B,hB⟩
    apply (core_zero_iff hM h3 hp).mp
    have hl := linear_growth h3 hp (B+1)
    have hb := hB (2*(B+1))
    by_cases hz : coreMass M g=0
    · exact hz
    · have hm := Nat.mul_le_mul_left (3*(B+1)) (show 1≤coreMass M g by omega)
      omega
  · intro hz
    exact ⟨sumRange M g,fun k => Nat.le_of_eq (mass_constant_of_supported h3 hp hz k)⟩

theorem plateau_iff_supported {M : Nat} (hM : 0<M) (h3 : M%3=0)
    {g : Nat → Nat} (hp : HasPeriod g M) :
    massTower M g 2 = sumRange M g ↔ ∀ n, n%3 ≠ 0 → g n=0 := by
  constructor
  · intro he
    apply (core_zero_iff hM h3 hp).mp
    have hl := linear_growth h3 hp 1
    simp only [Nat.mul_one,show 2*1=2 by decide] at hl
    omega
  · intro hz
    exact mass_constant_of_supported h3 hp hz 2

/-! Specialization to actual Collatz label defects. -/

def errorWeight (f : Nat → Bool) (n : Nat) : Nat :=
  if f (acceleratedStep n)=f n then 0 else 1

def labelPulls : Nat → (Nat → Bool) → Nat → Bool
  | 0, f => f
  | k+1, f => fun n => labelPulls k f (acceleratedStep n)

def defectTower (m : Nat) (f : Nat → Bool) (k : Nat) : Nat :=
  defectCount (2^k*m) (labelPulls k f)

def coreDefects (m : Nat) (f : Nat → Bool) : Nat := coreMass (2*m) (errorWeight f)

theorem error_period {m : Nat} {f : Nat → Bool} (hp : HasPeriod f m) :
    HasPeriod (errorWeight f) (2*m) := by
  intro n
  have hd := defect_period hp n
  unfold Defect at hd
  unfold errorWeight
  by_cases h : f (acceleratedStep n)=f n
  · have h' : f (acceleratedStep (n+2*m))=f (n+2*m) := by
      apply Classical.byContradiction
      intro hh
      change f (acceleratedStep (n+2*m)) ≠ f (n+2*m) at hh
      rw [hd] at hh
      exact hh h
    simp [h,h']
  · have h' : f (acceleratedStep (n+2*m)) ≠ f (n+2*m) := by rwa [hd]
    simp [h,h']

theorem labelPulls_orbit (k : Nat) (f : Nat → Bool) (n : Nat) :
    labelPulls k f n=f (acceleratedOrbit k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => exact ih (acceleratedStep n)

theorem labelPulls_period {m : Nat} {f : Nat → Bool}
    (hp : HasPeriod f m) (k : Nat) : HasPeriod (labelPulls k f) (2^k*m) := by
  induction k with
  | zero => simpa [labelPulls] using hp
  | succ k ih =>
    intro n
    have he : 2^(k+1)*m=2*(2^k*m) := by rw [Nat.pow_succ]; ac_rfl
    simp only [labelPulls,he,step_add_even]
    split
    · exact ih _
    · exact period_mul ih _ 3

theorem error_pulls (k : Nat) (f : Nat → Bool) :
    errorWeight (labelPulls k f)=pulls k (errorWeight f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext n
    change errorWeight (labelPulls k f) (acceleratedStep n) =
      pulls k (errorWeight f) (acceleratedStep n)
    rw [ih]

theorem defectTower_eq_massTower (m : Nat) (f : Nat → Bool) (k : Nat) :
    defectTower m f k=massTower (2*m) (errorWeight f) k := by
  unfold defectTower defectCount massTower
  change sumRange (2*(2^k*m)) (errorWeight (labelPulls k f)) = _
  rw [error_pulls]
  congr 1
  ac_rfl

/-- The one-step defect transport identity, including its exact correction. -/
theorem defect_one_step {m : Nat} (h3 : m%3=0) {f : Nat → Bool}
    (hp : HasPeriod f m) :
    defectTower m f 1 = defectCount m f +
      3*classMass (2*m) 2 (errorWeight f) := by
  rw [defectTower_eq_massTower]
  exact mass_pull (by omega) (error_period hp)

/-- Quantitative error amplification in the actual expanding modular graphs. -/
theorem defect_linear_growth {m : Nat} (h3 : m%3=0) {f : Nat → Bool}
    (hp : HasPeriod f m) (k : Nat) :
    defectCount m f + 3*k*coreDefects m f ≤ defectTower m f (2*k) := by
  rw [defectTower_eq_massTower]
  exact linear_growth (by omega) (error_period hp) k

/-- A two-scale test characterizes bounded error counts at every scale. -/
theorem defect_plateau_iff_bounded {m : Nat} (hm : 0<m) (h3 : m%3=0)
    {f : Nat → Bool} (hp : HasPeriod f m) :
    defectTower m f 2=defectCount m f ↔ ∃ B, ∀ k, defectTower m f k ≤ B := by
  simp only [defectTower_eq_massTower]
  exact (plateau_iff_supported (by omega) (by omega) (error_period hp)).trans
    (bounded_iff_supported (by omega) (by omega) (error_period hp)).symm

/-- The bounded regime is precisely absence of defects at inputs prime to 3. -/
theorem defect_bounded_iff_core_invariant {m : Nat} (hm : 0<m) (h3 : m%3=0)
    {f : Nat → Bool} (hp : HasPeriod f m) :
    (∃ B, ∀ k, defectTower m f k ≤ B) ↔
      ∀ n, n%3 ≠ 0 → f (acceleratedStep n)=f n := by
  simp only [defectTower_eq_massTower]
  rw [bounded_iff_supported (by omega) (by omega) (error_period hp)]
  simp [errorWeight]

/-- If the first two pullbacks produce no growth, no later pullback does. -/
theorem defect_plateau_forever {m : Nat} (hm : 0<m) (h3 : m%3=0)
    {f : Nat → Bool} (hp : HasPeriod f m)
    (he : defectTower m f 2=defectCount m f) (k : Nat) :
    defectTower m f k=defectCount m f := by
  rw [defectTower_eq_massTower] at he ⊢
  exact mass_constant_of_supported (by omega) (error_period hp)
    ((plateau_iff_supported (by omega) (by omega) (error_period hp)).mp he) k

end Collatz.PeriodicDefectTransport
