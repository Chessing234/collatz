import Collatz.Strategy.RealizableBound

/-!
A twelve-step rational phase certificate for a uniform linear Beatty ceiling.
This is a bound on heavy words; it makes no universal descent claim.
-/
namespace Collatz.BeattyBlockPotential
open RealizableBound

/-- Advance the power-of-two phase without logarithms. -/
def nextPhase (x y : Nat) : Nat := if 4*y ≤ 3*x then 4*y else 2*y

/-- Horner accumulator after `k` phase steps, starting from `c`. -/
def phaseRun : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, c => c
  | k+1, x, y, c => phaseRun k (3*x) (nextPhase x y) (3*c+y)

theorem phaseRun_linear (k x y c : Nat) :
    phaseRun k x y c = 3^k*c + phaseRun k x y 0 := by
  induction k generalizing x y c with
  | zero => simp [phaseRun]
  | succ k ih =>
    rw [phaseRun, phaseRun, ih, ih (3*x) (nextPhase x y) (3*0+y)]
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [Nat.mul_add, Arith.three_pow_succ]
    have h : 3^k*(3*c) = (3*3^k)*c := by
      rw [← Nat.mul_assoc, Nat.mul_comm (3^k) 3]
    rw [h]
    omega

theorem nextPhase_fexp (a : Nat) :
    nextPhase (3^a) (2^fexp a) = 2^fexp (a+1) := by
  have h2 : 2^(fexp a+2) = 4*2^fexp a := by
    rw [Nat.pow_add]
    omega
  rw [fexp, h2, Arith.three_pow_succ]
  unfold nextPhase
  split <;> simp only [Nat.pow_add] <;> omega

theorem phaseRun_bcap (k a : Nat) :
    phaseRun k (3^a) (2^fexp a) (Bcap a) = Bcap (a+k) := by
  induction k generalizing a with
  | zero => simp [phaseRun]
  | succ k ih =>
    rw [phaseRun, nextPhase_fexp]
    have h3 : 3*3^a = 3^(a+1) := (Arith.three_pow_succ a).symm
    rw [h3, ← Bcap_succ, ih]
    congr 1
    omega

theorem phaseRun_scaled_step {k P Q R S x y : Nat}
    (h : nextPhase (P*x) (Q*y) = S*y) :
    phaseRun (k+1) (P*x) (Q*y) (R*y) =
      phaseRun k ((3*P)*x) (S*y) ((3*R+Q)*y) := by
  rw [phaseRun, h, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.add_mul]

/-- The phase numerator after `k` steps; its denominator is `3^k*x`. -/
def phaseY : Nat → Nat → Nat → Nat
  | 0, _, y => y
  | k+1, x, y => phaseY k (3*x) (nextPhase x y)

theorem nextPhase_range {x y : Nat} (hlo : x<2*y) (hhi : y≤x) :
    3*x < 2*nextPhase x y ∧ nextPhase x y ≤ 3*x := by
  unfold nextPhase
  split <;> omega

theorem phaseY_range (k : Nat) {x y : Nat} (hlo : x<2*y) (hhi : y≤x) :
    3^k*x < 2*phaseY k x y ∧ phaseY k x y ≤ 3^k*x := by
  induction k generalizing x y with
  | zero => simpa [phaseY] using And.intro hlo hhi
  | succ k ih =>
    have hn := nextPhase_range hlo hhi
    have hh := ih hn.1 hn.2
    have hp : 3^k*(3*x) = 3^(k+1)*x := by
      rw [Arith.three_pow_succ, ← Nat.mul_assoc, Nat.mul_comm (3^k) 3]
    simpa only [phaseY, hp] using hh

/-- Concatenation of arbitrary phase blocks. -/
theorem phaseRun_add (u v x y c : Nat) :
    phaseRun (u+v) x y c =
      phaseRun v (3^u*x) (phaseY u x y) (phaseRun u x y c) := by
  induction u generalizing x y c with
  | zero => simp [phaseRun, phaseY]
  | succ u ih =>
    rw [show u+1+v = (u+v)+1 by omega, phaseRun, ih]
    have hp : 3^u*(3*x) = 3^(u+1)*x := by
      rw [Arith.three_pow_succ, ← Nat.mul_assoc, Nat.mul_comm (3^u) 3]
    rw [hp]
    rfl

-- BEGIN GENERATED PHASE CERTIFICATE
private theorem phase_interval_0 (x y : Nat)
    (hl : 1*x < 2*y) (hh : 4096*y ≤ 2187*x) :
    phaseRun 12 x y 0 < 1594323*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 16*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (16*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 128*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (128*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 1024*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (1024*y) = 4096*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (4096*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 32768*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (32768*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 262144*y := by
    unfold nextPhase
    split <;> omega
  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by
    rw [phaseRun_scaled_step e0, phaseRun_scaled_step e1, phaseRun_scaled_step e2, phaseRun_scaled_step e3, phaseRun_scaled_step e4, phaseRun_scaled_step e5, phaseRun_scaled_step e6, phaseRun_scaled_step e7, phaseRun_scaled_step e8, phaseRun_scaled_step e9, phaseRun_scaled_step e10]
    simp only [phaseRun]
    omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_interval_1 (x y : Nat)
    (hl : 2187*x < 4096*y) (hh : 16*y ≤ 9*x) :
    phaseRun 12 x y 0 < 1594323*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 16*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (16*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 128*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (128*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 1024*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (1024*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 32768*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (32768*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 262144*y := by
    unfold nextPhase
    split <;> omega
  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by
    rw [phaseRun_scaled_step e0, phaseRun_scaled_step e1, phaseRun_scaled_step e2, phaseRun_scaled_step e3, phaseRun_scaled_step e4, phaseRun_scaled_step e5, phaseRun_scaled_step e6, phaseRun_scaled_step e7, phaseRun_scaled_step e8, phaseRun_scaled_step e9, phaseRun_scaled_step e10]
    simp only [phaseRun]
    omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_interval_2 (x y : Nat)
    (hl : 9*x < 16*y) (hh : 32768*y ≤ 19683*x) :
    phaseRun 12 x y 0 < 1594323*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 128*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (128*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 1024*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (1024*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 32768*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (32768*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 262144*y := by
    unfold nextPhase
    split <;> omega
  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by
    rw [phaseRun_scaled_step e0, phaseRun_scaled_step e1, phaseRun_scaled_step e2, phaseRun_scaled_step e3, phaseRun_scaled_step e4, phaseRun_scaled_step e5, phaseRun_scaled_step e6, phaseRun_scaled_step e7, phaseRun_scaled_step e8, phaseRun_scaled_step e9, phaseRun_scaled_step e10]
    simp only [phaseRun]
    omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_interval_3 (x y : Nat)
    (hl : 19683*x < 32768*y) (hh : 128*y ≤ 81*x) :
    phaseRun 12 x y 0 < 1594323*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 128*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (128*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 1024*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (1024*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 262144*y := by
    unfold nextPhase
    split <;> omega
  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by
    rw [phaseRun_scaled_step e0, phaseRun_scaled_step e1, phaseRun_scaled_step e2, phaseRun_scaled_step e3, phaseRun_scaled_step e4, phaseRun_scaled_step e5, phaseRun_scaled_step e6, phaseRun_scaled_step e7, phaseRun_scaled_step e8, phaseRun_scaled_step e9, phaseRun_scaled_step e10]
    simp only [phaseRun]
    omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_interval_4 (x y : Nat)
    (hl : 81*x < 128*y) (hh : 262144*y ≤ 177147*x) :
    phaseRun 12 x y 0 < 1594323*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 1024*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (1024*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 262144*y := by
    unfold nextPhase
    split <;> omega
  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by
    rw [phaseRun_scaled_step e0, phaseRun_scaled_step e1, phaseRun_scaled_step e2, phaseRun_scaled_step e3, phaseRun_scaled_step e4, phaseRun_scaled_step e5, phaseRun_scaled_step e6, phaseRun_scaled_step e7, phaseRun_scaled_step e8, phaseRun_scaled_step e9, phaseRun_scaled_step e10]
    simp only [phaseRun]
    omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_interval_5 (x y : Nat)
    (hl : 177147*x < 262144*y) (hh : 1024*y ≤ 729*x) :
    phaseRun 12 x y 0 < 1594323*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 1024*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (1024*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by
    rw [phaseRun_scaled_step e0, phaseRun_scaled_step e1, phaseRun_scaled_step e2, phaseRun_scaled_step e3, phaseRun_scaled_step e4, phaseRun_scaled_step e5, phaseRun_scaled_step e6, phaseRun_scaled_step e7, phaseRun_scaled_step e8, phaseRun_scaled_step e9, phaseRun_scaled_step e10]
    simp only [phaseRun]
    omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_interval_6 (x y : Nat)
    (hl : 729*x < 1024*y) (hh : 4*y ≤ 3*x) :
    phaseRun 12 x y 0 < 1594323*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 512*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (512*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by
    rw [phaseRun_scaled_step e0, phaseRun_scaled_step e1, phaseRun_scaled_step e2, phaseRun_scaled_step e3, phaseRun_scaled_step e4, phaseRun_scaled_step e5, phaseRun_scaled_step e6, phaseRun_scaled_step e7, phaseRun_scaled_step e8, phaseRun_scaled_step e9, phaseRun_scaled_step e10]
    simp only [phaseRun]
    omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_interval_7 (x y : Nat)
    (hl : 3*x < 4*y) (hh : 8192*y ≤ 6561*x) :
    phaseRun 12 x y 0 < 1594323*x := by
  have e0 : nextPhase (1*x) (1*y) = 2*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (2*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 512*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (512*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by
    rw [phaseRun_scaled_step e0, phaseRun_scaled_step e1, phaseRun_scaled_step e2, phaseRun_scaled_step e3, phaseRun_scaled_step e4, phaseRun_scaled_step e5, phaseRun_scaled_step e6, phaseRun_scaled_step e7, phaseRun_scaled_step e8, phaseRun_scaled_step e9, phaseRun_scaled_step e10]
    simp only [phaseRun]
    omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_interval_8 (x y : Nat)
    (hl : 6561*x < 8192*y) (hh : 32*y ≤ 27*x) :
    phaseRun 12 x y 0 < 1594323*x := by
  have e0 : nextPhase (1*x) (1*y) = 2*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (2*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 512*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (512*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 4096*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (4096*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by
    rw [phaseRun_scaled_step e0, phaseRun_scaled_step e1, phaseRun_scaled_step e2, phaseRun_scaled_step e3, phaseRun_scaled_step e4, phaseRun_scaled_step e5, phaseRun_scaled_step e6, phaseRun_scaled_step e7, phaseRun_scaled_step e8, phaseRun_scaled_step e9, phaseRun_scaled_step e10]
    simp only [phaseRun]
    omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_interval_9 (x y : Nat)
    (hl : 27*x < 32*y) (hh : 65536*y ≤ 59049*x) :
    phaseRun 12 x y 0 < 1594323*x := by
  have e0 : nextPhase (1*x) (1*y) = 2*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (2*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 16*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (16*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 512*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (512*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 4096*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (4096*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by
    rw [phaseRun_scaled_step e0, phaseRun_scaled_step e1, phaseRun_scaled_step e2, phaseRun_scaled_step e3, phaseRun_scaled_step e4, phaseRun_scaled_step e5, phaseRun_scaled_step e6, phaseRun_scaled_step e7, phaseRun_scaled_step e8, phaseRun_scaled_step e9, phaseRun_scaled_step e10]
    simp only [phaseRun]
    omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_interval_10 (x y : Nat)
    (hl : 59049*x < 65536*y) (hh : 256*y ≤ 243*x) :
    phaseRun 12 x y 0 < 1594323*x := by
  have e0 : nextPhase (1*x) (1*y) = 2*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (2*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 16*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (16*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 512*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (512*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 4096*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (4096*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 32768*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (32768*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by
    rw [phaseRun_scaled_step e0, phaseRun_scaled_step e1, phaseRun_scaled_step e2, phaseRun_scaled_step e3, phaseRun_scaled_step e4, phaseRun_scaled_step e5, phaseRun_scaled_step e6, phaseRun_scaled_step e7, phaseRun_scaled_step e8, phaseRun_scaled_step e9, phaseRun_scaled_step e10]
    simp only [phaseRun]
    omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_interval_11 (x y : Nat)
    (hl : 243*x < 256*y) (hh : 1*y ≤ 1*x) :
    phaseRun 12 x y 0 < 1594323*x := by
  have e0 : nextPhase (1*x) (1*y) = 2*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (2*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 16*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (16*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 128*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (128*y) = 512*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (512*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 4096*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (4096*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 32768*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (32768*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  have hc : phaseRun 12 (1*x) (1*y) (0*y) < 1594323*x := by
    rw [phaseRun_scaled_step e0, phaseRun_scaled_step e1, phaseRun_scaled_step e2, phaseRun_scaled_step e3, phaseRun_scaled_step e4, phaseRun_scaled_step e5, phaseRun_scaled_step e6, phaseRun_scaled_step e7, phaseRun_scaled_step e8, phaseRun_scaled_step e9, phaseRun_scaled_step e10]
    simp only [phaseRun]
    omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_prefix_interval_0 (x y : Nat)
    (hl : 1*x < 2*y) (hh : 4096*y ≤ 2187*x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 16*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (16*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 128*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (128*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 1024*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (1024*y) = 4096*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (4096*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 32768*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (32768*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 262144*y := by
    unfold nextPhase
    split <;> omega
  intro k
  have hk := k.isLt
  have cases : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 ∨ k.val=9 ∨ k.val=10 ∨ k.val=11 := by omega
  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by
    rcases cases with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    all_goals repeat first
      | rw [phaseRun_scaled_step e0]
      | rw [phaseRun_scaled_step e1]
      | rw [phaseRun_scaled_step e2]
      | rw [phaseRun_scaled_step e3]
      | rw [phaseRun_scaled_step e4]
      | rw [phaseRun_scaled_step e5]
      | rw [phaseRun_scaled_step e6]
      | rw [phaseRun_scaled_step e7]
      | rw [phaseRun_scaled_step e8]
      | rw [phaseRun_scaled_step e9]
      | rw [phaseRun_scaled_step e10]
    all_goals simp only [phaseRun]
    all_goals omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_prefix_interval_1 (x y : Nat)
    (hl : 2187*x < 4096*y) (hh : 16*y ≤ 9*x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 16*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (16*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 128*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (128*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 1024*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (1024*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 32768*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (32768*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 262144*y := by
    unfold nextPhase
    split <;> omega
  intro k
  have hk := k.isLt
  have cases : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 ∨ k.val=9 ∨ k.val=10 ∨ k.val=11 := by omega
  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by
    rcases cases with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    all_goals repeat first
      | rw [phaseRun_scaled_step e0]
      | rw [phaseRun_scaled_step e1]
      | rw [phaseRun_scaled_step e2]
      | rw [phaseRun_scaled_step e3]
      | rw [phaseRun_scaled_step e4]
      | rw [phaseRun_scaled_step e5]
      | rw [phaseRun_scaled_step e6]
      | rw [phaseRun_scaled_step e7]
      | rw [phaseRun_scaled_step e8]
      | rw [phaseRun_scaled_step e9]
      | rw [phaseRun_scaled_step e10]
    all_goals simp only [phaseRun]
    all_goals omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_prefix_interval_2 (x y : Nat)
    (hl : 9*x < 16*y) (hh : 32768*y ≤ 19683*x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 128*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (128*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 1024*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (1024*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 32768*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (32768*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 262144*y := by
    unfold nextPhase
    split <;> omega
  intro k
  have hk := k.isLt
  have cases : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 ∨ k.val=9 ∨ k.val=10 ∨ k.val=11 := by omega
  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by
    rcases cases with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    all_goals repeat first
      | rw [phaseRun_scaled_step e0]
      | rw [phaseRun_scaled_step e1]
      | rw [phaseRun_scaled_step e2]
      | rw [phaseRun_scaled_step e3]
      | rw [phaseRun_scaled_step e4]
      | rw [phaseRun_scaled_step e5]
      | rw [phaseRun_scaled_step e6]
      | rw [phaseRun_scaled_step e7]
      | rw [phaseRun_scaled_step e8]
      | rw [phaseRun_scaled_step e9]
      | rw [phaseRun_scaled_step e10]
    all_goals simp only [phaseRun]
    all_goals omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_prefix_interval_3 (x y : Nat)
    (hl : 19683*x < 32768*y) (hh : 128*y ≤ 81*x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 128*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (128*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 1024*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (1024*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 262144*y := by
    unfold nextPhase
    split <;> omega
  intro k
  have hk := k.isLt
  have cases : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 ∨ k.val=9 ∨ k.val=10 ∨ k.val=11 := by omega
  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by
    rcases cases with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    all_goals repeat first
      | rw [phaseRun_scaled_step e0]
      | rw [phaseRun_scaled_step e1]
      | rw [phaseRun_scaled_step e2]
      | rw [phaseRun_scaled_step e3]
      | rw [phaseRun_scaled_step e4]
      | rw [phaseRun_scaled_step e5]
      | rw [phaseRun_scaled_step e6]
      | rw [phaseRun_scaled_step e7]
      | rw [phaseRun_scaled_step e8]
      | rw [phaseRun_scaled_step e9]
      | rw [phaseRun_scaled_step e10]
    all_goals simp only [phaseRun]
    all_goals omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_prefix_interval_4 (x y : Nat)
    (hl : 81*x < 128*y) (hh : 262144*y ≤ 177147*x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 1024*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (1024*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 262144*y := by
    unfold nextPhase
    split <;> omega
  intro k
  have hk := k.isLt
  have cases : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 ∨ k.val=9 ∨ k.val=10 ∨ k.val=11 := by omega
  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by
    rcases cases with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    all_goals repeat first
      | rw [phaseRun_scaled_step e0]
      | rw [phaseRun_scaled_step e1]
      | rw [phaseRun_scaled_step e2]
      | rw [phaseRun_scaled_step e3]
      | rw [phaseRun_scaled_step e4]
      | rw [phaseRun_scaled_step e5]
      | rw [phaseRun_scaled_step e6]
      | rw [phaseRun_scaled_step e7]
      | rw [phaseRun_scaled_step e8]
      | rw [phaseRun_scaled_step e9]
      | rw [phaseRun_scaled_step e10]
    all_goals simp only [phaseRun]
    all_goals omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_prefix_interval_5 (x y : Nat)
    (hl : 177147*x < 262144*y) (hh : 1024*y ≤ 729*x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 1024*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (1024*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  intro k
  have hk := k.isLt
  have cases : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 ∨ k.val=9 ∨ k.val=10 ∨ k.val=11 := by omega
  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by
    rcases cases with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    all_goals repeat first
      | rw [phaseRun_scaled_step e0]
      | rw [phaseRun_scaled_step e1]
      | rw [phaseRun_scaled_step e2]
      | rw [phaseRun_scaled_step e3]
      | rw [phaseRun_scaled_step e4]
      | rw [phaseRun_scaled_step e5]
      | rw [phaseRun_scaled_step e6]
      | rw [phaseRun_scaled_step e7]
      | rw [phaseRun_scaled_step e8]
      | rw [phaseRun_scaled_step e9]
      | rw [phaseRun_scaled_step e10]
    all_goals simp only [phaseRun]
    all_goals omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_prefix_interval_6 (x y : Nat)
    (hl : 729*x < 1024*y) (hh : 4*y ≤ 3*x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  have e0 : nextPhase (1*x) (1*y) = 4*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (4*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 512*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (512*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  intro k
  have hk := k.isLt
  have cases : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 ∨ k.val=9 ∨ k.val=10 ∨ k.val=11 := by omega
  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by
    rcases cases with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    all_goals repeat first
      | rw [phaseRun_scaled_step e0]
      | rw [phaseRun_scaled_step e1]
      | rw [phaseRun_scaled_step e2]
      | rw [phaseRun_scaled_step e3]
      | rw [phaseRun_scaled_step e4]
      | rw [phaseRun_scaled_step e5]
      | rw [phaseRun_scaled_step e6]
      | rw [phaseRun_scaled_step e7]
      | rw [phaseRun_scaled_step e8]
      | rw [phaseRun_scaled_step e9]
      | rw [phaseRun_scaled_step e10]
    all_goals simp only [phaseRun]
    all_goals omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_prefix_interval_7 (x y : Nat)
    (hl : 3*x < 4*y) (hh : 8192*y ≤ 6561*x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  have e0 : nextPhase (1*x) (1*y) = 2*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (2*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 512*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (512*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 8192*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (8192*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  intro k
  have hk := k.isLt
  have cases : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 ∨ k.val=9 ∨ k.val=10 ∨ k.val=11 := by omega
  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by
    rcases cases with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    all_goals repeat first
      | rw [phaseRun_scaled_step e0]
      | rw [phaseRun_scaled_step e1]
      | rw [phaseRun_scaled_step e2]
      | rw [phaseRun_scaled_step e3]
      | rw [phaseRun_scaled_step e4]
      | rw [phaseRun_scaled_step e5]
      | rw [phaseRun_scaled_step e6]
      | rw [phaseRun_scaled_step e7]
      | rw [phaseRun_scaled_step e8]
      | rw [phaseRun_scaled_step e9]
      | rw [phaseRun_scaled_step e10]
    all_goals simp only [phaseRun]
    all_goals omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_prefix_interval_8 (x y : Nat)
    (hl : 6561*x < 8192*y) (hh : 32*y ≤ 27*x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  have e0 : nextPhase (1*x) (1*y) = 2*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (2*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 32*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (32*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 512*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (512*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 4096*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (4096*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  intro k
  have hk := k.isLt
  have cases : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 ∨ k.val=9 ∨ k.val=10 ∨ k.val=11 := by omega
  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by
    rcases cases with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    all_goals repeat first
      | rw [phaseRun_scaled_step e0]
      | rw [phaseRun_scaled_step e1]
      | rw [phaseRun_scaled_step e2]
      | rw [phaseRun_scaled_step e3]
      | rw [phaseRun_scaled_step e4]
      | rw [phaseRun_scaled_step e5]
      | rw [phaseRun_scaled_step e6]
      | rw [phaseRun_scaled_step e7]
      | rw [phaseRun_scaled_step e8]
      | rw [phaseRun_scaled_step e9]
      | rw [phaseRun_scaled_step e10]
    all_goals simp only [phaseRun]
    all_goals omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_prefix_interval_9 (x y : Nat)
    (hl : 27*x < 32*y) (hh : 65536*y ≤ 59049*x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  have e0 : nextPhase (1*x) (1*y) = 2*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (2*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 16*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (16*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 512*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (512*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 4096*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (4096*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 65536*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (65536*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  intro k
  have hk := k.isLt
  have cases : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 ∨ k.val=9 ∨ k.val=10 ∨ k.val=11 := by omega
  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by
    rcases cases with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    all_goals repeat first
      | rw [phaseRun_scaled_step e0]
      | rw [phaseRun_scaled_step e1]
      | rw [phaseRun_scaled_step e2]
      | rw [phaseRun_scaled_step e3]
      | rw [phaseRun_scaled_step e4]
      | rw [phaseRun_scaled_step e5]
      | rw [phaseRun_scaled_step e6]
      | rw [phaseRun_scaled_step e7]
      | rw [phaseRun_scaled_step e8]
      | rw [phaseRun_scaled_step e9]
      | rw [phaseRun_scaled_step e10]
    all_goals simp only [phaseRun]
    all_goals omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_prefix_interval_10 (x y : Nat)
    (hl : 59049*x < 65536*y) (hh : 256*y ≤ 243*x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  have e0 : nextPhase (1*x) (1*y) = 2*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (2*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 16*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (16*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 256*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (256*y) = 512*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (512*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 4096*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (4096*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 32768*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (32768*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  intro k
  have hk := k.isLt
  have cases : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 ∨ k.val=9 ∨ k.val=10 ∨ k.val=11 := by omega
  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by
    rcases cases with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    all_goals repeat first
      | rw [phaseRun_scaled_step e0]
      | rw [phaseRun_scaled_step e1]
      | rw [phaseRun_scaled_step e2]
      | rw [phaseRun_scaled_step e3]
      | rw [phaseRun_scaled_step e4]
      | rw [phaseRun_scaled_step e5]
      | rw [phaseRun_scaled_step e6]
      | rw [phaseRun_scaled_step e7]
      | rw [phaseRun_scaled_step e8]
      | rw [phaseRun_scaled_step e9]
      | rw [phaseRun_scaled_step e10]
    all_goals simp only [phaseRun]
    all_goals omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

private theorem phase_prefix_interval_11 (x y : Nat)
    (hl : 243*x < 256*y) (hh : 1*y ≤ 1*x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  have e0 : nextPhase (1*x) (1*y) = 2*y := by
    unfold nextPhase
    split <;> omega
  have e1 : nextPhase (3*x) (2*y) = 8*y := by
    unfold nextPhase
    split <;> omega
  have e2 : nextPhase (9*x) (8*y) = 16*y := by
    unfold nextPhase
    split <;> omega
  have e3 : nextPhase (27*x) (16*y) = 64*y := by
    unfold nextPhase
    split <;> omega
  have e4 : nextPhase (81*x) (64*y) = 128*y := by
    unfold nextPhase
    split <;> omega
  have e5 : nextPhase (243*x) (128*y) = 512*y := by
    unfold nextPhase
    split <;> omega
  have e6 : nextPhase (729*x) (512*y) = 2048*y := by
    unfold nextPhase
    split <;> omega
  have e7 : nextPhase (2187*x) (2048*y) = 4096*y := by
    unfold nextPhase
    split <;> omega
  have e8 : nextPhase (6561*x) (4096*y) = 16384*y := by
    unfold nextPhase
    split <;> omega
  have e9 : nextPhase (19683*x) (16384*y) = 32768*y := by
    unfold nextPhase
    split <;> omega
  have e10 : nextPhase (59049*x) (32768*y) = 131072*y := by
    unfold nextPhase
    split <;> omega
  intro k
  have hk := k.isLt
  have cases : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 ∨ k.val=6 ∨ k.val=7 ∨ k.val=8 ∨ k.val=9 ∨ k.val=10 ∨ k.val=11 := by omega
  have hc : 108*phaseRun k.val (1*x) (1*y) (0*y) ≤ (27*k.val+11)*3^k.val*x := by
    rcases cases with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals rw [hk]
    all_goals repeat first
      | rw [phaseRun_scaled_step e0]
      | rw [phaseRun_scaled_step e1]
      | rw [phaseRun_scaled_step e2]
      | rw [phaseRun_scaled_step e3]
      | rw [phaseRun_scaled_step e4]
      | rw [phaseRun_scaled_step e5]
      | rw [phaseRun_scaled_step e6]
      | rw [phaseRun_scaled_step e7]
      | rw [phaseRun_scaled_step e8]
      | rw [phaseRun_scaled_step e9]
      | rw [phaseRun_scaled_step e10]
    all_goals simp only [phaseRun]
    all_goals omega
  simpa only [Nat.one_mul, Nat.zero_mul] using hc

/-- Every phase has strictly less than nine units of mass in twelve steps.
All phase branches are discharged by exact integer linear arithmetic. -/
theorem phase_twelve_bound (x y : Nat) (hlo : x < 2*y) (hhi : y ≤ x) :
    phaseRun 12 x y 0 < 3*3^12*x := by
  by_cases h0 : 4096*y ≤ 2187*x
  · exact phase_interval_0 x y (by omega) h0
  by_cases h1 : 16*y ≤ 9*x
  · exact phase_interval_1 x y (by omega) h1
  by_cases h2 : 32768*y ≤ 19683*x
  · exact phase_interval_2 x y (by omega) h2
  by_cases h3 : 128*y ≤ 81*x
  · exact phase_interval_3 x y (by omega) h3
  by_cases h4 : 262144*y ≤ 177147*x
  · exact phase_interval_4 x y (by omega) h4
  by_cases h5 : 1024*y ≤ 729*x
  · exact phase_interval_5 x y (by omega) h5
  by_cases h6 : 4*y ≤ 3*x
  · exact phase_interval_6 x y (by omega) h6
  by_cases h7 : 8192*y ≤ 6561*x
  · exact phase_interval_7 x y (by omega) h7
  by_cases h8 : 32*y ≤ 27*x
  · exact phase_interval_8 x y (by omega) h8
  by_cases h9 : 65536*y ≤ 59049*x
  · exact phase_interval_9 x y (by omega) h9
  by_cases h10 : 256*y ≤ 243*x
  · exact phase_interval_10 x y (by omega) h10
  exact phase_interval_11 x y (by omega) (by omega)

/-- The same optimal intercept controls every phase for the initial block. -/
theorem phase_initial_bound (x y : Nat) (hlo : x<2*y) (hhi : y≤x) :
    ∀ k : Fin 12, 108*phaseRun k.val x y 0 ≤ (27*k.val+11)*3^k.val*x := by
  by_cases h0 : 4096*y ≤ 2187*x
  · exact phase_prefix_interval_0 x y (by omega) h0
  by_cases h1 : 16*y ≤ 9*x
  · exact phase_prefix_interval_1 x y (by omega) h1
  by_cases h2 : 32768*y ≤ 19683*x
  · exact phase_prefix_interval_2 x y (by omega) h2
  by_cases h3 : 128*y ≤ 81*x
  · exact phase_prefix_interval_3 x y (by omega) h3
  by_cases h4 : 262144*y ≤ 177147*x
  · exact phase_prefix_interval_4 x y (by omega) h4
  by_cases h5 : 1024*y ≤ 729*x
  · exact phase_prefix_interval_5 x y (by omega) h5
  by_cases h6 : 4*y ≤ 3*x
  · exact phase_prefix_interval_6 x y (by omega) h6
  by_cases h7 : 8192*y ≤ 6561*x
  · exact phase_prefix_interval_7 x y (by omega) h7
  by_cases h8 : 32*y ≤ 27*x
  · exact phase_prefix_interval_8 x y (by omega) h8
  by_cases h9 : 65536*y ≤ 59049*x
  · exact phase_prefix_interval_9 x y (by omega) h9
  by_cases h10 : 256*y ≤ 243*x
  · exact phase_prefix_interval_10 x y (by omega) h10
  exact phase_prefix_interval_11 x y (by omega) (by omega)

-- END GENERATED PHASE CERTIFICATE

private theorem phase_block_algebra (n p x : Nat) :
    108*(p*(1594323*x)) + (27*n+11)*p*(531441*x) =
      (27*(n+12)+11)*(531441*p)*x := by
  have h1 : 108*(p*(1594323*x)) = 172186884*(p*x) := by
    calc 108*(p*(1594323*x)) = (108*1594323)*(p*x) := by ac_rfl
      _ = 172186884*(p*x) := rfl
  have h2 : (27*n+11)*p*(531441*x) = (531441*(27*n+11))*(p*x) := by ac_rfl
  have h3 : (27*(n+12)+11)*(531441*p)*x =
      (531441*(27*(n+12)+11))*(p*x) := by ac_rfl
  rw [h1,h2,h3,← Nat.add_mul]
  have he : 172186884+531441*(27*n+11) = 531441*(27*(n+12)+11) := by omega
  rw [he]

/-- Uniform bound for every initial phase and every horizon. The finite
phase certificate controls an infinite family, with no orbit sampling. -/
theorem phase_global_bound (k x y : Nat) (hlo : x<2*y) (hhi : y≤x) :
    108*phaseRun k x y 0 ≤ (27*k+11)*3^k*x := by
  induction k using Nat.strongRecOn generalizing x y with
  | ind k ih =>
    by_cases hs : k<12
    · exact phase_initial_bound x y hlo hhi ⟨k,hs⟩
    · let n := k-12
      have hn : n<k := by dsimp [n]; omega
      have hk : n+12=k := by dsimp [n]; omega
      have hp12 : (3:Nat)^12 = 531441 := by decide
      have hrange := phaseY_range 12 hlo hhi
      rw [hp12] at hrange
      have hi := ih n hn (531441*x) (phaseY 12 x y) hrange.1 hrange.2
      have hb := Nat.le_of_lt (phase_twelve_bound x y hlo hhi)
      rw [hp12] at hb
      have he : phaseRun k x y 0 =
          3^n*phaseRun 12 x y 0 + phaseRun n (531441*x) (phaseY 12 x y) 0 := by
        have hh := phaseRun_add 12 n x y 0
        rw [phaseRun_linear n (3^12*x) (phaseY 12 x y) (phaseRun 12 x y 0)] at hh
        rw [show 12+n=k by omega, hp12] at hh
        exact hh
      have hp : 3^k = 531441*3^n := by
        calc 3^k = 3^(n+12) := congrArg (fun t => 3^t) hk.symm
          _ = 3^n*3^12 := Nat.pow_add _ _ _
          _ = 531441*3^n := by rw [hp12, Nat.mul_comm]
      calc 108*phaseRun k x y 0
          = 108*(3^n*phaseRun 12 x y 0) +
              108*phaseRun n (531441*x) (phaseY 12 x y) 0 := by rw [he,Nat.mul_add]
        _ ≤ 108*(3^n*(1594323*x)) + (27*n+11)*3^n*(531441*x) :=
          Nat.add_le_add (Nat.mul_le_mul_left 108 (Nat.mul_le_mul_left (3^n) hb)) hi
        _ = (27*(n+12)+11)*(531441*3^n)*x := phase_block_algebra n (3^n) x
        _ = (27*k+11)*3^k*x := by rw [hk,hp]

/-- A translation-uniform bound for every window of the Beatty accumulator. -/
theorem bcap_window_bound (a k : Nat) :
    108*Bcap (a+k) ≤ 108*(3^k*Bcap a) + (27*k+11)*3^(a+k) := by
  have hlo := lt_fexp a
  rw [Arith.two_pow_succ] at hlo
  have hh := phase_global_bound k (3^a) (2^fexp a) hlo (fexp_le a)
  have he := phaseRun_bcap k a
  rw [phaseRun_linear] at he
  have hp : (27*k+11)*3^k*3^a = (27*k+11)*3^(a+k) := by
    rw [Nat.pow_add]
    ac_rfl
  rw [hp] at hh
  rw [← he, Nat.mul_add]
  exact Nat.add_le_add_left hh _

/-- Every consecutive block of twelve odd-step indices gains less than
three units in the normalized accumulator. -/
theorem bcap_block_strict (a : Nat) :
    Bcap (a+12) < 531441*Bcap a + 1594323*3^a := by
  have hlo := lt_fexp a
  rw [Arith.two_pow_succ] at hlo
  have h := phase_twelve_bound (3^a) (2^fexp a) hlo (fexp_le a)
  have he := phaseRun_bcap 12 a
  rw [phaseRun_linear] at he
  have hp : (3:Nat)^12 = 531441 := by decide
  rw [hp] at h he
  omega

private theorem initial_bound : ∀ a : Fin 12,
    108*Bcap a.val ≤ (27*a.val+11)*3^a.val := by decide

private theorem initial_eq : ∀ a : Fin 12,
    108*Bcap a.val = (27*a.val+11)*3^a.val ↔ a.val=3 := by decide

private theorem block_algebra (a p : Nat) :
    531441*((27*a+11)*p) + 172186884*p =
      (27*(a+12)+11)*(531441*p) := by
  have h : 27*(a+12)+11 = (27*a+11)+324 := by omega
  rw [h, Nat.add_mul (27*a+11) 324 (531441*p)]
  have h1 : (27*a+11)*(531441*p) = 531441*((27*a+11)*p) :=
    Nat.mul_left_comm _ _ _
  have h2 : 324*(531441*p) = 172186884*p := by rw [← Nat.mul_assoc]
  rw [h1, h2]

/-- A uniform closed form for the exact Beatty ceiling.
The intercept is attained at `a=3` and is optimal for this slope. -/
theorem bcap_linear_bound (a : Nat) :
    108*Bcap a ≤ (27*a+11)*3^a := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases hs : a<12
    · exact initial_bound ⟨a,hs⟩
    · have heq : a = (a-12)+12 := by omega
      have hb := bcap_block_strict (a-12)
      have hi := ih (a-12) (by omega)
      have hm := Nat.mul_lt_mul_of_pos_left hb (show 0<108 by decide)
      have hmi := Nat.mul_le_mul_left 531441 hi
      have hp : 3^a = 531441*3^(a-12) := by
        have hn : (3:Nat)^12 = 531441 := by decide
        calc 3^a = 3^((a-12)+12) := congrArg (fun t => 3^t) heq
          _ = 3^(a-12)*3^12 := Nat.pow_add _ _ _
          _ = 531441*3^(a-12) := by rw [hn, Nat.mul_comm]
      have ha := block_algebra (a-12) (3^(a-12))
      rw [← heq, ← hp] at ha
      rw [← heq] at hm
      rw [Nat.mul_add] at hm
      have h1 : 108*(531441*Bcap (a-12)) = 531441*(108*Bcap (a-12)) :=
        Nat.mul_left_comm _ _ _
      have h2 : 108*(1594323*3^(a-12)) = 172186884*3^(a-12) := by
        rw [← Nat.mul_assoc]
      rw [h1,h2] at hm
      omega

/-- The inequality is strict past the initial twelve indices. -/
theorem bcap_linear_strict {a : Nat} (ha : 12≤a) :
    108*Bcap a < (27*a+11)*3^a := by
  have heq : a = (a-12)+12 := by omega
  have hb := bcap_block_strict (a-12)
  have hi := bcap_linear_bound (a-12)
  have hm := Nat.mul_lt_mul_of_pos_left hb (show 0<108 by decide)
  have hmi := Nat.mul_le_mul_left 531441 hi
  have hp : 3^a = 531441*3^(a-12) := by
    have hn : (3:Nat)^12 = 531441 := by decide
    calc 3^a = 3^((a-12)+12) := congrArg (fun t => 3^t) heq
      _ = 3^(a-12)*3^12 := Nat.pow_add _ _ _
      _ = 531441*3^(a-12) := by rw [hn, Nat.mul_comm]
  have halg := block_algebra (a-12) (3^(a-12))
  rw [← heq, ← hp] at halg
  rw [← heq] at hm
  rw [Nat.mul_add] at hm
  have h1 : 108*(531441*Bcap (a-12)) = 531441*(108*Bcap (a-12)) :=
    Nat.mul_left_comm _ _ _
  have h2 : 108*(1594323*3^(a-12)) = 172186884*3^(a-12) := by
    rw [← Nat.mul_assoc]
  rw [h1,h2] at hm
  omega

theorem bcap_linear_eq_iff (a : Nat) :
    108*Bcap a = (27*a+11)*3^a ↔ a=3 := by
  by_cases hs : a<12
  · exact initial_eq ⟨a,hs⟩
  · have h := bcap_linear_strict (by omega : 12≤a)
    omega

theorem bcap_three_sharp : 108*Bcap 3 = (27*3+11)*3^3 := by decide

theorem intercept_optimal {b : Nat}
    (h : ∀ a : Nat, 108*Bcap a ≤ (27*a+b)*3^a) : 11≤b := by
  have h3 := h 3
  have hB : Bcap 3 = 23 := by decide
  rw [hB] at h3
  omega

end Collatz.BeattyBlockPotential
