import Collatz.Strategy.PeriodicDefectTransport

/-!
An explicit four-branch proof of uniform error amplification.
PeriodicDefectTransport supplies the definitions and the stable/linear-growth
results. The branch embedding below is independent
of the finite transfer-weight certificate in PeriodicDefectAmplification.
This is modular error propagation, not a proof of integer convergence.
-/
namespace Collatz.PeriodicBranchEmbedding
open Collatz.Sum PeriodicRigidity PeriodicDefectMinimum PeriodicDefectTransport TreeStochastic

theorem branch0 (q : Nat) : acceleratedOrbit 4 (16*q) = q := by
  simp only [acceleratedOrbit, acceleratedStep]
  repeat first | split | omega

theorem branch4 (q : Nat) : acceleratedOrbit 4 (16*q+4) = 3*q+1 := by
  simp only [acceleratedOrbit, acceleratedStep]
  repeat first | split | omega

theorem branch5 (q : Nat) : acceleratedOrbit 4 (16*q+5) = 3*q+1 := by
  simp only [acceleratedOrbit, acceleratedStep]
  repeat first | split | omega

theorem branch8 (q : Nat) : acceleratedOrbit 4 (16*q+8) = 3*q+2 := by
  simp only [acceleratedOrbit, acceleratedStep]
  repeat first | split | omega

theorem branch10 (q : Nat) : acceleratedOrbit 4 (16*q+10) = 3*q+2 := by
  simp only [acceleratedOrbit, acceleratedStep]
  repeat first | split | omega

/-- Select a one-odd-step inverse branch that remains prime to three. -/
theorem choose_branch {v : Nat} (hv : v%3 ≠ 0) :
    ∃ q r b : Nat, 0 < r ∧ r < 16 ∧ (q+r)%3 ≠ 0 ∧
      3*q+b=v ∧ 0 < b ∧ b ≤ 2 ∧
      ∀ t : Nat, acceleratedOrbit 4 (16*t+r)=3*t+b := by
  have hv9 : v%9=1 ∨ v%9=2 ∨ v%9=4 ∨ v%9=5 ∨ v%9=7 ∨ v%9=8 := by omega
  rcases hv9 with h|h|h|h|h|h
  · exact ⟨v/3,4,1,by omega,by omega,by omega,by omega,by omega,by omega,branch4⟩
  · exact ⟨v/3,8,2,by omega,by omega,by omega,by omega,by omega,by omega,branch8⟩
  · exact ⟨v/3,4,1,by omega,by omega,by omega,by omega,by omega,by omega,branch4⟩
  · exact ⟨v/3,10,2,by omega,by omega,by omega,by omega,by omega,by omega,branch10⟩
  · exact ⟨v/3,5,1,by omega,by omega,by omega,by omega,by omega,by omega,branch5⟩
  · exact ⟨v/3,8,2,by omega,by omega,by omega,by omega,by omega,by omega,branch8⟩

/-- Four distinct core preimages with explicit range and residue bounds. -/
theorem four_preimages {P v : Nat} (hP : 0 < P) (h9 : P%9=0)
    (hvP : v<P) (hv3 : v%3≠0) :
    ∃ a b c d : Nat,
      a<16*P ∧ b<16*P ∧ c<16*P ∧ d<16*P ∧
      a≠b ∧ a≠c ∧ a≠d ∧ b≠c ∧ b≠d ∧ c≠d ∧
      a%3≠0 ∧ b%3≠0 ∧ c%3≠0 ∧ d%3≠0 ∧
      acceleratedOrbit 4 a %P=v ∧ acceleratedOrbit 4 b %P=v ∧
      acceleratedOrbit 4 c %P=v ∧ acceleratedOrbit 4 d %P=v := by
  obtain ⟨q,r,s,hr0,hr16,hqr,hqv,hs0,hs2,hbranch⟩ := choose_branch hv3
  refine ⟨16*v,16*q+r,16*(q+P/3)+r,16*(q+2*(P/3))+r,
    by omega,by omega,by omega,by omega,
    by omega,by omega,by omega,by omega,by omega,by omega,
    by omega,by omega,by omega,by omega,?_,?_,?_,?_⟩
  · rw [branch0,Nat.mod_eq_of_lt hvP]
  · rw [hbranch,hqv,Nat.mod_eq_of_lt hvP]
  · rw [hbranch,show 3*(q+P/3)+s=v+P by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hvP]
  · rw [hbranch,show 3*(q+2*(P/3))+s=v+2*P by omega]
    simp [Nat.add_mod,Nat.mod_eq_of_lt hvP]

theorem four_le_count {N a b c d : Nat} (Q : Nat → Prop) [DecidablePred Q]
    (ha : a<N) (hb : b<N) (hc : c<N) (hd : d<N)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (hqa : Q a) (hqb : Q b) (hqc : Q c) (hqd : Q d) :
    4 ≤ sumRange N (fun n => if Q n then 1 else 0) := by
  let w := fun n => (if n=a then 1 else 0) + (if n=b then 1 else 0) +
    (if n=c then 1 else 0) + (if n=d then 1 else 0)
  have hw : sumRange N w = 4 := by
    dsimp [w]
    rw [sumRange_add,sumRange_add,sumRange_add,
      sumRange_single (fun _ => 1) ha,sumRange_single (fun _ => 1) hb,
      sumRange_single (fun _ => 1) hc,sumRange_single (fun _ => 1) hd]
  rw [← hw]
  apply sumRange_le
  intro n _
  dsimp [w]
  by_cases hna : n=a
  · subst n; simp_all
  by_cases hnb : n=b
  · subst n; simp_all
  by_cases hnc : n=c
  · subst n; simp_all
  by_cases hnd : n=d
  · subst n; simp_all
  simp [hna,hnb,hnc,hnd]

theorem weighted_fibers (N P : Nat) (Q : Nat → Prop) [DecidablePred Q]
    (F w : Nat → Nat) (hF : ∀ n, n<N → F n<P) :
    sumRange N (fun n => if Q n then w (F n) else 0) =
      sumRange P (fun v => w v * sumRange N (fun n => if Q n ∧ F n=v then 1 else 0)) := by
  calc
    _ = sumRange N (fun n => sumRange P (fun v => if Q n ∧ F n=v then w v else 0)) := by
      apply sumRange_congr
      intro n hn
      by_cases hq : Q n
      · rw [if_pos hq]
        have hpoint : ∀ v, (if Q n ∧ F n=v then w v else 0) =
            (if v=F n then w v else 0) := by intro v; simp [hq,eq_comm]
        rw [sumRange_congr (fun v _ => hpoint v),sumRange_single w (hF n hn)]
      · simp [hq,sumRange_const]
    _ = sumRange P (fun v => sumRange N (fun n => if Q n ∧ F n=v then w v else 0)) :=
      sumRange_comm N P _
    _ = _ := by
      apply sumRange_congr
      intro v _
      rw [← sumRange_const_mul]
      apply sumRange_congr
      intro n _
      split <;> simp_all

theorem fourfold_nine {P : Nat} (hP : 0<P) (h9 : P%9=0)
    {w : Nat → Nat} (hp : HasPeriod w P) :
    4 * coreMass P w ≤ coreMass (16*P) (pulls 4 w) := by
  have hperiod : coreMass (16*P) (pulls 4 w) =
      sumRange (16*P) (fun n => if n%3≠0 then w (acceleratedOrbit 4 n %P) else 0) := by
    apply sumRange_congr
    intro n _
    change (if n%3=0 then 0 else w (acceleratedOrbit 4 n)) = _
    rw [period_mod hp (acceleratedOrbit 4 n)]
    by_cases h : n%3=0 <;> simp [h]
  rw [hperiod,weighted_fibers (16*P) P (fun n => n%3≠0)
    (fun n => acceleratedOrbit 4 n %P) w (fun n _ => Nat.mod_lt _ hP)]
  unfold coreMass
  rw [← sumRange_const_mul]
  apply sumRange_le
  intro v hv
  by_cases hv3 : v%3=0
  · simp [hv3]
  · rw [if_neg hv3]
    obtain ⟨a,b,c,d,ha,hb,hc,hd,hab,hac,had,hbc,hbd,hcd,
      ha3,hb3,hc3,hd3,haT,hbT,hcT,hdT⟩ := four_preimages hP h9 hv hv3
    have hcount := four_le_count (fun n => n%3≠0 ∧ acceleratedOrbit 4 n %P=v)
      ha hb hc hd hab hac had hbc hbd hcd ⟨ha3,haT⟩ ⟨hb3,hbT⟩ ⟨hc3,hcT⟩ ⟨hd3,hdT⟩
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (w v) hcount

theorem sum_period_mul {P : Nat} {w : Nat → Nat} (hp : HasPeriod w P) (q : Nat) :
    sumRange (q*P) w = q * sumRange P w := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul,sumRange_split,ih]
    have hs : sumRange P (fun n => w (q*P+n)) = sumRange P w := by
      apply sumRange_congr
      intro n _
      simpa [Nat.add_comm] using period_mul hp n q
    rw [hs]
    rw [Nat.succ_mul]

theorem core_scale {P : Nat} (h3 : P%3=0) {w : Nat → Nat}
    (hp : HasPeriod w P) (q : Nat) : coreMass (q*P) w = q * coreMass P w := by
  apply sum_period_mul
  intro n
  simp [Nat.add_mod,h3,hp n]

/-- The fourfold lower bound holds at every positive period divisible by 3. -/
theorem core_fourfold {P : Nat} (hP : 0<P) (h3 : P%3=0)
    {w : Nat → Nat} (hp : HasPeriod w P) :
    4 * coreMass P w ≤ coreMass (16*P) (pulls 4 w) := by
  have hp9 : HasPeriod w (9*P) := fun n => period_mul hp n 9
  have hh := fourfold_nine (by omega : 0<9*P) (by omega : (9*P)%9=0) hp9
  have hp4 : HasPeriod (pulls 4 w) (16*P) := by simpa using pulls_period hp 4
  have h34 : (16*P)%3=0 := by omega
  rw [core_scale h3 hp 9,show 16*(9*P)=9*(16*P) by omega,core_scale h34 hp4 9] at hh
  omega

theorem pulls_add (a b : Nat) (g : Nat → Nat) :
    pulls a (pulls b g)=pulls (a+b) g := by
  induction a with
  | zero => simp [pulls]
  | succ a ih => simpa [pulls,Nat.succ_add] using congrArg pull ih

/-- Uniform exponential amplification, with unbounded depth and period. -/
theorem core_exponential {P : Nat} (hP : 0<P) (h3 : P%3=0)
    {w : Nat → Nat} (hp : HasPeriod w P) (j : Nat) :
    4^j * coreMass P w ≤ coreTower P w (4*j) := by
  induction j with
  | zero => simp [coreTower,pulls]
  | succ j ih =>
    have hp' := pulls_period hp (4*j)
    have hP' : 0 < 2^(4*j)*P := Nat.mul_pos (Nat.pow_pos (by decide)) hP
    have h3' : (2^(4*j)*P)%3=0 := by simp [Nat.mul_mod,h3]
    have hh := core_fourfold hP' h3' hp'
    have hbound := Nat.le_trans (Nat.mul_le_mul_left 4 ih) hh
    rw [pulls_add] at hbound
    have hidx : 4+4*j=4*(j+1) := by omega
    have hmod : 16*(2^(4*j)*P)=2^(4*(j+1))*P := by
      rw [show 4*(j+1)=4+4*j by omega,Nat.pow_add]
      simp [Nat.mul_assoc]
    rw [hidx,hmod] at hbound
    simpa [coreTower,Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hbound

theorem core_le_mass (P : Nat) (w : Nat → Nat) : coreMass P w ≤ sumRange P w := by
  apply sumRange_le
  intro n _
  split <;> omega

/-- The weight theorem applies to actual invariance defects of any Boolean label. -/
theorem defect_exponential {m : Nat} (hm : 0<m) (h3 : m%3=0)
    {f : Nat → Bool} (hp : HasPeriod f m) (j : Nat) :
    4^j * coreDefects m f ≤ defectTower m f (4*j) := by
  rw [defectTower_eq_massTower]
  exact Nat.le_trans (core_exponential (by omega) (by omega) (error_period hp) j)
    (core_le_mass _ _)

/-- A periodic observation has exactly stable error counts, or exponentially
growing counts. The alternatives describe finite modular errors, not orbits. -/
theorem defect_dichotomy {m : Nat} (hm : 0<m) (h3 : m%3=0)
    {f : Nat → Bool} (hp : HasPeriod f m) :
    (∀ k, defectTower m f k=defectCount m f) ∨
      (∀ j, 4^j ≤ defectTower m f (4*j)) := by
  by_cases hz : coreDefects m f=0
  · left
    have hs := (core_zero_iff (by omega : 0<2*m) (by omega) (error_period hp)).mp hz
    intro k
    rw [defectTower_eq_massTower]
    exact mass_constant_of_supported (by omega) (error_period hp) hs k
  · right
    intro j
    have hpos : 1 ≤ coreDefects m f := by omega
    have hh := Nat.mul_le_mul_left (4^j) hpos
    simpa using Nat.le_trans hh (defect_exponential hm h3 hp j)

/-- Two pullbacks distinguish the stable regime from a quantitatively
exponential one. Counts use the prescribed periods, not least periods. -/
theorem two_step_test {m : Nat} (hm : 0<m) (h3 : m%3=0)
    {f : Nat → Bool} (hp : HasPeriod f m) :
    (defectTower m f 2=defectCount m f ∧
      ∀ k, defectTower m f k=defectCount m f) ∨
    (defectCount m f < defectTower m f 2 ∧
      ∀ j, 4^j ≤ defectTower m f (4*j)) := by
  by_cases he : defectTower m f 2=defectCount m f
  · exact Or.inl ⟨he,defect_plateau_forever hm h3 hp he⟩
  · have hle := defect_linear_growth h3 hp 1
    simp only [Nat.mul_one] at hle
    have hlt : defectCount m f < defectTower m f 2 := by omega
    rcases defect_dichotomy hm h3 hp with hs|hg
    · exact False.elim (he (hs 2))
    · exact Or.inr ⟨hlt,hg⟩

set_option maxRecDepth 4096 in
/-- Sharp for arbitrary nonnegative periodic weights. It is not claimed sharp
after the extra restriction that the weight be a label's defect indicator. -/
theorem transfer_sharp :
    coreMass 9 (fun n => if n%9=7 then 1 else 0)=1 ∧
    coreTower 9 (fun n => if n%9=7 then 1 else 0) 3=1 ∧
    coreTower 9 (fun n => if n%9=7 then 1 else 0) 4=4 := by decide

/-- Four is the best universal four-step coefficient for periodic weights. -/
theorem fourfold_optimal (A : Nat)
    (h : ∀ (P : Nat), 0<P → P%3=0 → ∀ (w : Nat → Nat),
      HasPeriod w P → A * coreMass P w ≤ coreTower P w 4) : A ≤ 4 := by
  have hp : HasPeriod (fun n => if n%9=7 then 1 else 0) 9 := by
    intro n
    simp
  have hh := h 9 (by decide) (by decide) _ hp
  rw [transfer_sharp.1,transfer_sharp.2.2,Nat.mul_one] at hh
  exact hh

/-- No universal three-step coefficient greater than one is possible. -/
theorem three_steps_insufficient (A : Nat)
    (h : ∀ (P : Nat), 0<P → P%3=0 → ∀ (w : Nat → Nat),
      HasPeriod w P → A * coreMass P w ≤ coreTower P w 3) : A ≤ 1 := by
  have hp : HasPeriod (fun n => if n%9=7 then 1 else 0) 9 := by
    intro n
    simp
  have hh := h 9 (by decide) (by decide) _ hp
  rw [transfer_sharp.1,transfer_sharp.2.1,Nat.mul_one] at hh
  exact hh

end Collatz.PeriodicBranchEmbedding
