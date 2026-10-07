import Collatz.Exploration.ElevenHalvesArithmetic.Part20

/-! Generated residue-and-affine certificates for the inclusive ratio-11/2 band.
Every branch and arithmetic conclusion is independently checked by Lean. -/
namespace Collatz.Exploration.ElevenHalvesArithmetic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

theorem impossible_trace
    (b x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : Nat) (hb : 1 < b)
    (h0 : b ≤ x0 ∧ 2*x0 ≤ 11*b)
    (h1 : b ≤ x1 ∧ 2*x1 ≤ 11*b)
    (h2 : b ≤ x2 ∧ 2*x2 ≤ 11*b)
    (h3 : b ≤ x3 ∧ 2*x3 ≤ 11*b)
    (h4 : b ≤ x4 ∧ 2*x4 ≤ 11*b)
    (h5 : b ≤ x5 ∧ 2*x5 ≤ 11*b)
    (h6 : b ≤ x6 ∧ 2*x6 ≤ 11*b)
    (h7 : b ≤ x7 ∧ 2*x7 ≤ 11*b)
    (h8 : b ≤ x8 ∧ 2*x8 ≤ 11*b)
    (h9 : b ≤ x9 ∧ 2*x9 ≤ 11*b)
    (h10 : b ≤ x10 ∧ 2*x10 ≤ 11*b)
    (h11 : b ≤ x11 ∧ 2*x11 ≤ 11*b)
    (h12 : b ≤ x12 ∧ 2*x12 ≤ 11*b)
    (h13 : b ≤ x13 ∧ 2*x13 ≤ 11*b)
    (h14 : b ≤ x14 ∧ 2*x14 ≤ 11*b)
    (h15 : b ≤ x15 ∧ 2*x15 ≤ 11*b)
    (h16 : b ≤ x16 ∧ 2*x16 ≤ 11*b)
    (h17 : b ≤ x17 ∧ 2*x17 ≤ 11*b)
    (h18 : b ≤ x18 ∧ 2*x18 ≤ 11*b)
    (h19 : b ≤ x19 ∧ 2*x19 ≤ 11*b)
    (h20 : b ≤ x20 ∧ 2*x20 ≤ 11*b)
    (h21 : b ≤ x21 ∧ 2*x21 ≤ 11*b)
    (h22 : b ≤ x22 ∧ 2*x22 ≤ 11*b)
    (h23 : b ≤ x23 ∧ 2*x23 ≤ 11*b)
    (h24 : b ≤ x24 ∧ 2*x24 ≤ 11*b)
    (h25 : b ≤ x25 ∧ 2*x25 ≤ 11*b)
    (h26 : b ≤ x26 ∧ 2*x26 ≤ 11*b)
    (h27 : b ≤ x27 ∧ 2*x27 ≤ 11*b)
    (h28 : b ≤ x28 ∧ 2*x28 ≤ 11*b)
    (h29 : b ≤ x29 ∧ 2*x29 ≤ 11*b)
    (h30 : b ≤ x30 ∧ 2*x30 ≤ 11*b)
    (r0 : (2*x1 = x0 ∧ x0%2 = 0) ∨ (x1 = 3*x0+1 ∧ x0%2 = 1))
    (r1 : (2*x2 = x1 ∧ x1%2 = 0) ∨ (x2 = 3*x1+1 ∧ x1%2 = 1))
    (r2 : (2*x3 = x2 ∧ x2%2 = 0) ∨ (x3 = 3*x2+1 ∧ x2%2 = 1))
    (r3 : (2*x4 = x3 ∧ x3%2 = 0) ∨ (x4 = 3*x3+1 ∧ x3%2 = 1))
    (r4 : (2*x5 = x4 ∧ x4%2 = 0) ∨ (x5 = 3*x4+1 ∧ x4%2 = 1))
    (r5 : (2*x6 = x5 ∧ x5%2 = 0) ∨ (x6 = 3*x5+1 ∧ x5%2 = 1))
    (r6 : (2*x7 = x6 ∧ x6%2 = 0) ∨ (x7 = 3*x6+1 ∧ x6%2 = 1))
    (r7 : (2*x8 = x7 ∧ x7%2 = 0) ∨ (x8 = 3*x7+1 ∧ x7%2 = 1))
    (r8 : (2*x9 = x8 ∧ x8%2 = 0) ∨ (x9 = 3*x8+1 ∧ x8%2 = 1))
    (r9 : (2*x10 = x9 ∧ x9%2 = 0) ∨ (x10 = 3*x9+1 ∧ x9%2 = 1))
    (r10 : (2*x11 = x10 ∧ x10%2 = 0) ∨ (x11 = 3*x10+1 ∧ x10%2 = 1))
    (r11 : (2*x12 = x11 ∧ x11%2 = 0) ∨ (x12 = 3*x11+1 ∧ x11%2 = 1))
    (r12 : (2*x13 = x12 ∧ x12%2 = 0) ∨ (x13 = 3*x12+1 ∧ x12%2 = 1))
    (r13 : (2*x14 = x13 ∧ x13%2 = 0) ∨ (x14 = 3*x13+1 ∧ x13%2 = 1))
    (r14 : (2*x15 = x14 ∧ x14%2 = 0) ∨ (x15 = 3*x14+1 ∧ x14%2 = 1))
    (r15 : (2*x16 = x15 ∧ x15%2 = 0) ∨ (x16 = 3*x15+1 ∧ x15%2 = 1))
    (r16 : (2*x17 = x16 ∧ x16%2 = 0) ∨ (x17 = 3*x16+1 ∧ x16%2 = 1))
    (r17 : (2*x18 = x17 ∧ x17%2 = 0) ∨ (x18 = 3*x17+1 ∧ x17%2 = 1))
    (r18 : (2*x19 = x18 ∧ x18%2 = 0) ∨ (x19 = 3*x18+1 ∧ x18%2 = 1))
    (r19 : (2*x20 = x19 ∧ x19%2 = 0) ∨ (x20 = 3*x19+1 ∧ x19%2 = 1))
    (r20 : (2*x21 = x20 ∧ x20%2 = 0) ∨ (x21 = 3*x20+1 ∧ x20%2 = 1))
    (r21 : (2*x22 = x21 ∧ x21%2 = 0) ∨ (x22 = 3*x21+1 ∧ x21%2 = 1))
    (r22 : (2*x23 = x22 ∧ x22%2 = 0) ∨ (x23 = 3*x22+1 ∧ x22%2 = 1))
    (r23 : (2*x24 = x23 ∧ x23%2 = 0) ∨ (x24 = 3*x23+1 ∧ x23%2 = 1))
    (r24 : (2*x25 = x24 ∧ x24%2 = 0) ∨ (x25 = 3*x24+1 ∧ x24%2 = 1))
    (r25 : (2*x26 = x25 ∧ x25%2 = 0) ∨ (x26 = 3*x25+1 ∧ x25%2 = 1))
    (r26 : (2*x27 = x26 ∧ x26%2 = 0) ∨ (x27 = 3*x26+1 ∧ x26%2 = 1))
    (r27 : (2*x28 = x27 ∧ x27%2 = 0) ∨ (x28 = 3*x27+1 ∧ x27%2 = 1))
    (r28 : (2*x29 = x28 ∧ x28%2 = 0) ∨ (x29 = 3*x28+1 ∧ x28%2 = 1))
    (r29 : (2*x30 = x29 ∧ x29%2 = 0) ∨ (x30 = 3*x29+1 ∧ x29%2 = 1))
    : False := by
  revert r29 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 r18 r17 r16 r15 r14 r13 r12 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0
  intro r0
  rcases r0 with r0 | r0
  · -- branch 0 at time 0
    intro r1
    rcases r1 with r1 | r1
    · -- branch 0 at time 1
      intro r2
      rcases r2 with r2 | r2
      · -- branch 0 at time 2
        exact False.elim (exclude_000 x0 x1 x2 x3 b hb h0 h3 r0 r1 r2)
      · -- branch 1 at time 2
        intro r3
        rcases r3 with r3 | r3
        · -- branch 0 at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- branch 0 at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- branch 0 at time 5
              exact False.elim (exclude_001000 x0 x1 x2 x3 x4 x5 x6 b hb h0 h6 r0 r1 r2 r3 r4 r5)
            · -- branch 1 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  exact False.elim (exclude_00100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
                · -- branch 1 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        exact False.elim (exclude_00100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb h0 h11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                      · -- branch 1 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            exact False.elim (exclude_0010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb h0 h13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                          · -- branch 1 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  exact False.elim (exclude_0010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb h0 h16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                                · -- branch 1 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      exact False.elim (exclude_001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb h0 h18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                    · -- branch 1 at time 17
                                      exact False.elim (exclude_001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb h5 h18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                  · -- branch 1 at time 16
                                    exact False.elim (exclude_00100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                              · -- branch 1 at time 14
                                exact False.elim (exclude_001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb h2 h15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                            · -- branch 1 at time 13
                              exact False.elim (exclude_00100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                        · -- branch 1 at time 11
                          exact False.elim (exclude_001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                    · -- branch 1 at time 9
                      exact False.elim (exclude_0010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb h5 h10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                  · -- branch 1 at time 8
                    exact False.elim (exclude_001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8)
              · -- branch 1 at time 6
                exact False.elim (exclude_0010011 x0 x1 x2 x3 x4 x5 x6 x7 b hb r0 r1 r2 r3 r4 r5 r6)
          · -- branch 1 at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- branch 0 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  exact False.elim (exclude_00101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
                · -- branch 1 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        exact False.elim (exclude_00101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb h0 h11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                      · -- branch 1 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            exact False.elim (exclude_0010100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb h0 h13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                          · -- branch 1 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  exact False.elim (exclude_0010100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb h0 h16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                                · -- branch 1 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      exact False.elim (exclude_001010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb h0 h18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                    · -- branch 1 at time 17
                                      intro r18
                                      rcases r18 with r18 | r18
                                      · -- branch 0 at time 18
                                        intro r19
                                        rcases r19 with r19 | r19
                                        · -- branch 0 at time 19
                                          intro r20
                                          rcases r20 with r20 | r20
                                          · -- branch 0 at time 20
                                            exact False.elim (exclude_001010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 b hb h0 h21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20)
                                          · -- branch 1 at time 20
                                            intro r21
                                            rcases r21 with r21 | r21
                                            · -- branch 0 at time 21
                                              intro r22
                                              rcases r22 with r22 | r22
                                              · -- branch 0 at time 22
                                                exact False.elim (exclude_00101001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 b hb h5 h23 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22)
                                              · -- branch 1 at time 22
                                                exact False.elim (exclude_00101001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 b hb h10 h23 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22)
                                            · -- branch 1 at time 21
                                              exact False.elim (exclude_0010100100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21)
                                        · -- branch 1 at time 19
                                          exact False.elim (exclude_00101001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 b hb h2 h20 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19)
                                      · -- branch 1 at time 18
                                        exact False.elim (exclude_0010100100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                  · -- branch 1 at time 16
                                    exact False.elim (exclude_00101001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                              · -- branch 1 at time 14
                                exact False.elim (exclude_001010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb h2 h15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                            · -- branch 1 at time 13
                              exact False.elim (exclude_00101001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                        · -- branch 1 at time 11
                          exact False.elim (exclude_001010010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                    · -- branch 1 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            exact False.elim (exclude_0010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb h0 h13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                          · -- branch 1 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  exact False.elim (exclude_0010100101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb h0 h16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                                · -- branch 1 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      exact False.elim (exclude_001010010100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb h0 h18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                    · -- branch 1 at time 17
                                      intro r18
                                      rcases r18 with r18 | r18
                                      · -- branch 0 at time 18
                                        intro r19
                                        rcases r19 with r19 | r19
                                        · -- branch 0 at time 19
                                          intro r20
                                          rcases r20 with r20 | r20
                                          · -- branch 0 at time 20
                                            exact False.elim (exclude_001010010100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 b hb h0 h21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20)
                                          · -- branch 1 at time 20
                                            intro r21
                                            rcases r21 with r21 | r21
                                            · -- branch 0 at time 21
                                              intro r22
                                              rcases r22 with r22 | r22
                                              · -- branch 0 at time 22
                                                exact False.elim (exclude_00101001010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 b hb h5 h23 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22)
                                              · -- branch 1 at time 22
                                                intro r23
                                                rcases r23 with r23 | r23
                                                · -- branch 0 at time 23
                                                  intro r24
                                                  rcases r24 with r24 | r24
                                                  · -- branch 0 at time 24
                                                    intro r25
                                                    rcases r25 with r25 | r25
                                                    · -- branch 0 at time 25
                                                      exact False.elim (exclude_00101001010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 b hb h0 h26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25)
                                                    · -- branch 1 at time 25
                                                      intro r26
                                                      rcases r26 with r26 | r26
                                                      · -- branch 0 at time 26
                                                        intro r27
                                                        rcases r27 with r27 | r27
                                                        · -- branch 0 at time 27
                                                          exact False.elim (exclude_0010100101001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 b hb h10 h28 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27)
                                                        · -- branch 1 at time 27
                                                          exact False.elim (exclude_0010100101001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 b hb h15 h28 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27)
                                                      · -- branch 1 at time 26
                                                        exact False.elim (exclude_001010010100100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26)
                                                  · -- branch 1 at time 24
                                                    exact False.elim (exclude_0010100101001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 b hb h2 h25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24)
                                                · -- branch 1 at time 23
                                                  exact False.elim (exclude_001010010100100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23)
                                            · -- branch 1 at time 21
                                              exact False.elim (exclude_0010100101001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21)
                                        · -- branch 1 at time 19
                                          exact False.elim (exclude_00101001010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 b hb h2 h20 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19)
                                      · -- branch 1 at time 18
                                        exact False.elim (exclude_0010100101001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                  · -- branch 1 at time 16
                                    exact False.elim (exclude_00101001010010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                              · -- branch 1 at time 14
                                exact False.elim (exclude_001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb h2 h15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                            · -- branch 1 at time 13
                              exact False.elim (exclude_00101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                        · -- branch 1 at time 11
                          exact False.elim (exclude_001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb h2 h12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                      · -- branch 1 at time 10
                        exact False.elim (exclude_00101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                  · -- branch 1 at time 8
                    exact False.elim (exclude_001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8)
              · -- branch 1 at time 6
                exact False.elim (exclude_0010101 x0 x1 x2 x3 x4 x5 x6 x7 b hb h2 h7 r0 r1 r2 r3 r4 r5 r6)
            · -- branch 1 at time 5
              exact False.elim (exclude_001011 x0 x1 x2 x3 x4 x5 x6 b hb r0 r1 r2 r3 r4 r5)
        · -- branch 1 at time 3
          exact False.elim (exclude_0011 x0 x1 x2 x3 x4 b hb r0 r1 r2 r3)
    · -- branch 1 at time 1
      intro r2
      rcases r2 with r2 | r2
      · -- branch 0 at time 2
        intro r3
        rcases r3 with r3 | r3
        · -- branch 0 at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- branch 0 at time 4
            exact False.elim (exclude_01000 x0 x1 x2 x3 x4 x5 b hb h2 h5 r0 r1 r2 r3 r4)
          · -- branch 1 at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- branch 0 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  exact False.elim (exclude_01001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb h0 h8 r0 r1 r2 r3 r4 r5 r6 r7)
                · -- branch 1 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      exact False.elim (exclude_0100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb h2 h10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                    · -- branch 1 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            exact False.elim (exclude_0100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb h0 h13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                          · -- branch 1 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                exact False.elim (exclude_010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb h2 h15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                              · -- branch 1 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      exact False.elim (exclude_010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb h0 h18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                    · -- branch 1 at time 17
                                      intro r18
                                      rcases r18 with r18 | r18
                                      · -- branch 0 at time 18
                                        intro r19
                                        rcases r19 with r19 | r19
                                        · -- branch 0 at time 19
                                          exact False.elim (exclude_01001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 b hb h2 h20 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19)
                                        · -- branch 1 at time 19
                                          exact False.elim (exclude_01001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 b hb h7 h20 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19)
                                      · -- branch 1 at time 18
                                        exact False.elim (exclude_0100100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                  · -- branch 1 at time 16
                                    exact False.elim (exclude_01001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb h4 h17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                                · -- branch 1 at time 15
                                  exact False.elim (exclude_0100100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                            · -- branch 1 at time 13
                              exact False.elim (exclude_01001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                        · -- branch 1 at time 11
                          exact False.elim (exclude_010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb h7 h12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                      · -- branch 1 at time 10
                        exact False.elim (exclude_01001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                  · -- branch 1 at time 8
                    exact False.elim (exclude_010010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8)
              · -- branch 1 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      exact False.elim (exclude_0100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb h2 h10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                    · -- branch 1 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            exact False.elim (exclude_0100101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb h0 h13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                          · -- branch 1 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                exact False.elim (exclude_010010100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb h2 h15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                              · -- branch 1 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      exact False.elim (exclude_010010100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb h0 h18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                    · -- branch 1 at time 17
                                      intro r18
                                      rcases r18 with r18 | r18
                                      · -- branch 0 at time 18
                                        intro r19
                                        rcases r19 with r19 | r19
                                        · -- branch 0 at time 19
                                          exact False.elim (exclude_01001010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 b hb h2 h20 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19)
                                        · -- branch 1 at time 19
                                          intro r20
                                          rcases r20 with r20 | r20
                                          · -- branch 0 at time 20
                                            intro r21
                                            rcases r21 with r21 | r21
                                            · -- branch 0 at time 21
                                              intro r22
                                              rcases r22 with r22 | r22
                                              · -- branch 0 at time 22
                                                exact False.elim (exclude_01001010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 b hb h2 h23 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22)
                                              · -- branch 1 at time 22
                                                intro r23
                                                rcases r23 with r23 | r23
                                                · -- branch 0 at time 23
                                                  intro r24
                                                  rcases r24 with r24 | r24
                                                  · -- branch 0 at time 24
                                                    exact False.elim (exclude_0100101001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 b hb h7 h25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24)
                                                  · -- branch 1 at time 24
                                                    exact False.elim (exclude_0100101001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 b hb h12 h25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24)
                                                · -- branch 1 at time 23
                                                  exact False.elim (exclude_010010100100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23)
                                            · -- branch 1 at time 21
                                              exact False.elim (exclude_0100101001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 b hb h4 h22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21)
                                          · -- branch 1 at time 20
                                            exact False.elim (exclude_010010100100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20)
                                      · -- branch 1 at time 18
                                        exact False.elim (exclude_0100101001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                  · -- branch 1 at time 16
                                    exact False.elim (exclude_01001010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb h4 h17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                                · -- branch 1 at time 15
                                  exact False.elim (exclude_0100101001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                            · -- branch 1 at time 13
                              exact False.elim (exclude_01001010010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                        · -- branch 1 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                exact False.elim (exclude_010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb h2 h15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                              · -- branch 1 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      exact False.elim (exclude_010010100101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb h0 h18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                    · -- branch 1 at time 17
                                      intro r18
                                      rcases r18 with r18 | r18
                                      · -- branch 0 at time 18
                                        intro r19
                                        rcases r19 with r19 | r19
                                        · -- branch 0 at time 19
                                          exact False.elim (exclude_01001010010100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 b hb h2 h20 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19)
                                        · -- branch 1 at time 19
                                          intro r20
                                          rcases r20 with r20 | r20
                                          · -- branch 0 at time 20
                                            intro r21
                                            rcases r21 with r21 | r21
                                            · -- branch 0 at time 21
                                              intro r22
                                              rcases r22 with r22 | r22
                                              · -- branch 0 at time 22
                                                exact False.elim (exclude_01001010010100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 b hb h2 h23 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22)
                                              · -- branch 1 at time 22
                                                intro r23
                                                rcases r23 with r23 | r23
                                                · -- branch 0 at time 23
                                                  intro r24
                                                  rcases r24 with r24 | r24
                                                  · -- branch 0 at time 24
                                                    exact False.elim (exclude_0100101001010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 b hb h7 h25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24)
                                                  · -- branch 1 at time 24
                                                    intro r25
                                                    rcases r25 with r25 | r25
                                                    · -- branch 0 at time 25
                                                      intro r26
                                                      rcases r26 with r26 | r26
                                                      · -- branch 0 at time 26
                                                        intro r27
                                                        rcases r27 with r27 | r27
                                                        · -- branch 0 at time 27
                                                          exact False.elim (exclude_0100101001010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 b hb h2 h28 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27)
                                                        · -- branch 1 at time 27
                                                          intro r28
                                                          rcases r28 with r28 | r28
                                                          · -- branch 0 at time 28
                                                            intro r29
                                                            rcases r29 with r29 | r29
                                                            · -- branch 0 at time 29
                                                              exact False.elim (exclude_010010100101001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 b hb h12 h30 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29)
                                                            · -- branch 1 at time 29
                                                              exact False.elim (exclude_010010100101001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 b hb h17 h30 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29)
                                                          · -- branch 1 at time 28
                                                            exact False.elim (exclude_01001010010100100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28)
                                                      · -- branch 1 at time 26
                                                        exact False.elim (exclude_010010100101001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 b hb h4 h27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26)
                                                    · -- branch 1 at time 25
                                                      exact False.elim (exclude_01001010010100100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25)
                                                · -- branch 1 at time 23
                                                  exact False.elim (exclude_010010100101001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23)
                                            · -- branch 1 at time 21
                                              exact False.elim (exclude_0100101001010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 b hb h4 h22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21)
                                          · -- branch 1 at time 20
                                            exact False.elim (exclude_010010100101001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20)
                                      · -- branch 1 at time 18
                                        exact False.elim (exclude_0100101001010010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                  · -- branch 1 at time 16
                                    exact False.elim (exclude_01001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb h4 h17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                                · -- branch 1 at time 15
                                  exact False.elim (exclude_0100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                            · -- branch 1 at time 13
                              exact False.elim (exclude_01001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb h1 h14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                          · -- branch 1 at time 12
                            exact False.elim (exclude_0100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                      · -- branch 1 at time 10
                        exact False.elim (exclude_01001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                  · -- branch 1 at time 8
                    exact False.elim (exclude_010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb h4 h9 r0 r1 r2 r3 r4 r5 r6 r7 r8)
                · -- branch 1 at time 7
                  exact False.elim (exclude_01001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb r0 r1 r2 r3 r4 r5 r6 r7)
            · -- branch 1 at time 5
              exact False.elim (exclude_010011 x0 x1 x2 x3 x4 x5 x6 b hb r0 r1 r2 r3 r4 r5)
        · -- branch 1 at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- branch 0 at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- branch 0 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                exact False.elim (exclude_0101000 x0 x1 x2 x3 x4 x5 x6 x7 b hb h4 h7 r0 r1 r2 r3 r4 r5 r6)
              · -- branch 1 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      exact False.elim (exclude_0101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb h2 h10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                    · -- branch 1 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          exact False.elim (exclude_010100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb h4 h12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                        · -- branch 1 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                exact False.elim (exclude_010100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb h2 h15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                              · -- branch 1 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    exact False.elim (exclude_01010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb h4 h17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                                  · -- branch 1 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      intro r18
                                      rcases r18 with r18 | r18
                                      · -- branch 0 at time 18
                                        intro r19
                                        rcases r19 with r19 | r19
                                        · -- branch 0 at time 19
                                          exact False.elim (exclude_01010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 b hb h2 h20 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19)
                                        · -- branch 1 at time 19
                                          intro r20
                                          rcases r20 with r20 | r20
                                          · -- branch 0 at time 20
                                            intro r21
                                            rcases r21 with r21 | r21
                                            · -- branch 0 at time 21
                                              exact False.elim (exclude_0101001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 b hb h4 h22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21)
                                            · -- branch 1 at time 21
                                              exact False.elim (exclude_0101001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 b hb h9 h22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21)
                                          · -- branch 1 at time 20
                                            exact False.elim (exclude_010100100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20)
                                      · -- branch 1 at time 18
                                        exact False.elim (exclude_0101001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb h1 h19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                    · -- branch 1 at time 17
                                      exact False.elim (exclude_010100100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                · -- branch 1 at time 15
                                  exact False.elim (exclude_0101001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                            · -- branch 1 at time 13
                              exact False.elim (exclude_01010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb h1 h14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                          · -- branch 1 at time 12
                            exact False.elim (exclude_0101001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                      · -- branch 1 at time 10
                        exact False.elim (exclude_01010010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                  · -- branch 1 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          exact False.elim (exclude_010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb h4 h12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                        · -- branch 1 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                exact False.elim (exclude_010100101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb h2 h15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                              · -- branch 1 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    exact False.elim (exclude_01010010100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb h4 h17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                                  · -- branch 1 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      intro r18
                                      rcases r18 with r18 | r18
                                      · -- branch 0 at time 18
                                        intro r19
                                        rcases r19 with r19 | r19
                                        · -- branch 0 at time 19
                                          exact False.elim (exclude_01010010100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 b hb h2 h20 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19)
                                        · -- branch 1 at time 19
                                          intro r20
                                          rcases r20 with r20 | r20
                                          · -- branch 0 at time 20
                                            intro r21
                                            rcases r21 with r21 | r21
                                            · -- branch 0 at time 21
                                              exact False.elim (exclude_0101001010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 b hb h4 h22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21)
                                            · -- branch 1 at time 21
                                              intro r22
                                              rcases r22 with r22 | r22
                                              · -- branch 0 at time 22
                                                intro r23
                                                rcases r23 with r23 | r23
                                                · -- branch 0 at time 23
                                                  intro r24
                                                  rcases r24 with r24 | r24
                                                  · -- branch 0 at time 24
                                                    exact False.elim (exclude_0101001010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 b hb h4 h25 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24)
                                                  · -- branch 1 at time 24
                                                    intro r25
                                                    rcases r25 with r25 | r25
                                                    · -- branch 0 at time 25
                                                      intro r26
                                                      rcases r26 with r26 | r26
                                                      · -- branch 0 at time 26
                                                        exact False.elim (exclude_010100101001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 b hb h9 h27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26)
                                                      · -- branch 1 at time 26
                                                        exact False.elim (exclude_010100101001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 b hb h14 h27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26)
                                                    · -- branch 1 at time 25
                                                      exact False.elim (exclude_01010010100100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25)
                                                · -- branch 1 at time 23
                                                  exact False.elim (exclude_010100101001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 b hb h1 h24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23)
                                              · -- branch 1 at time 22
                                                exact False.elim (exclude_01010010100100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22)
                                          · -- branch 1 at time 20
                                            exact False.elim (exclude_010100101001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20)
                                      · -- branch 1 at time 18
                                        exact False.elim (exclude_0101001010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb h1 h19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                    · -- branch 1 at time 17
                                      exact False.elim (exclude_010100101001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                · -- branch 1 at time 15
                                  exact False.elim (exclude_0101001010010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                            · -- branch 1 at time 13
                              exact False.elim (exclude_01010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb h1 h14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                          · -- branch 1 at time 12
                            exact False.elim (exclude_0101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                      · -- branch 1 at time 10
                        exact False.elim (exclude_01010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb h1 h11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                    · -- branch 1 at time 9
                      exact False.elim (exclude_0101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                · -- branch 1 at time 7
                  exact False.elim (exclude_01010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb r0 r1 r2 r3 r4 r5 r6 r7)
            · -- branch 1 at time 5
              exact False.elim (exclude_010101 x0 x1 x2 x3 x4 x5 x6 b hb h1 h6 r0 r1 r2 r3 r4 r5)
          · -- branch 1 at time 4
            exact False.elim (exclude_01011 x0 x1 x2 x3 x4 x5 b hb r0 r1 r2 r3 r4)
      · -- branch 1 at time 2
        exact False.elim (exclude_011 x0 x1 x2 x3 b hb r0 r1 r2)
  · -- branch 1 at time 0
    intro r1
    rcases r1 with r1 | r1
    · -- branch 0 at time 1
      intro r2
      rcases r2 with r2 | r2
      · -- branch 0 at time 2
        intro r3
        rcases r3 with r3 | r3
        · -- branch 0 at time 3
          exact False.elim (exclude_1000 x0 x1 x2 x3 x4 b hb h1 h4 r0 r1 r2 r3)
        · -- branch 1 at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- branch 0 at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- branch 0 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                exact False.elim (exclude_1001000 x0 x1 x2 x3 x4 x5 x6 x7 b hb h1 h7 r0 r1 r2 r3 r4 r5 r6)
              · -- branch 1 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    exact False.elim (exclude_100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb h1 h9 r0 r1 r2 r3 r4 r5 r6 r7 r8)
                  · -- branch 1 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          exact False.elim (exclude_100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb h1 h12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                        · -- branch 1 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              exact False.elim (exclude_10010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb h1 h14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                            · -- branch 1 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    exact False.elim (exclude_10010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb h1 h17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                                  · -- branch 1 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      intro r18
                                      rcases r18 with r18 | r18
                                      · -- branch 0 at time 18
                                        exact False.elim (exclude_1001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb h1 h19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                      · -- branch 1 at time 18
                                        exact False.elim (exclude_1001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb h6 h19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                    · -- branch 1 at time 17
                                      exact False.elim (exclude_100100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                · -- branch 1 at time 15
                                  exact False.elim (exclude_1001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb h3 h16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                              · -- branch 1 at time 14
                                exact False.elim (exclude_100100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                          · -- branch 1 at time 12
                            exact False.elim (exclude_1001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                      · -- branch 1 at time 10
                        exact False.elim (exclude_10010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb h6 h11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                    · -- branch 1 at time 9
                      exact False.elim (exclude_1001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                · -- branch 1 at time 7
                  exact False.elim (exclude_10010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb r0 r1 r2 r3 r4 r5 r6 r7)
            · -- branch 1 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    exact False.elim (exclude_100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb h1 h9 r0 r1 r2 r3 r4 r5 r6 r7 r8)
                  · -- branch 1 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          exact False.elim (exclude_100101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb h1 h12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                        · -- branch 1 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              exact False.elim (exclude_10010100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb h1 h14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                            · -- branch 1 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    exact False.elim (exclude_10010100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb h1 h17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                                  · -- branch 1 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      intro r18
                                      rcases r18 with r18 | r18
                                      · -- branch 0 at time 18
                                        exact False.elim (exclude_1001010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb h1 h19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                      · -- branch 1 at time 18
                                        intro r19
                                        rcases r19 with r19 | r19
                                        · -- branch 0 at time 19
                                          intro r20
                                          rcases r20 with r20 | r20
                                          · -- branch 0 at time 20
                                            intro r21
                                            rcases r21 with r21 | r21
                                            · -- branch 0 at time 21
                                              exact False.elim (exclude_1001010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 b hb h1 h22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21)
                                            · -- branch 1 at time 21
                                              intro r22
                                              rcases r22 with r22 | r22
                                              · -- branch 0 at time 22
                                                intro r23
                                                rcases r23 with r23 | r23
                                                · -- branch 0 at time 23
                                                  exact False.elim (exclude_100101001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 b hb h6 h24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23)
                                                · -- branch 1 at time 23
                                                  exact False.elim (exclude_100101001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 b hb h11 h24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23)
                                              · -- branch 1 at time 22
                                                exact False.elim (exclude_10010100100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22)
                                          · -- branch 1 at time 20
                                            exact False.elim (exclude_100101001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 b hb h3 h21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20)
                                        · -- branch 1 at time 19
                                          exact False.elim (exclude_10010100100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19)
                                    · -- branch 1 at time 17
                                      exact False.elim (exclude_100101001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                · -- branch 1 at time 15
                                  exact False.elim (exclude_1001010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb h3 h16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                              · -- branch 1 at time 14
                                exact False.elim (exclude_100101001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                          · -- branch 1 at time 12
                            exact False.elim (exclude_1001010010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                      · -- branch 1 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              exact False.elim (exclude_10010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb h1 h14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                            · -- branch 1 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    exact False.elim (exclude_10010100101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb h1 h17 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                                  · -- branch 1 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      intro r18
                                      rcases r18 with r18 | r18
                                      · -- branch 0 at time 18
                                        exact False.elim (exclude_1001010010100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb h1 h19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                      · -- branch 1 at time 18
                                        intro r19
                                        rcases r19 with r19 | r19
                                        · -- branch 0 at time 19
                                          intro r20
                                          rcases r20 with r20 | r20
                                          · -- branch 0 at time 20
                                            intro r21
                                            rcases r21 with r21 | r21
                                            · -- branch 0 at time 21
                                              exact False.elim (exclude_1001010010100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 b hb h1 h22 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21)
                                            · -- branch 1 at time 21
                                              intro r22
                                              rcases r22 with r22 | r22
                                              · -- branch 0 at time 22
                                                intro r23
                                                rcases r23 with r23 | r23
                                                · -- branch 0 at time 23
                                                  exact False.elim (exclude_100101001010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 b hb h6 h24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23)
                                                · -- branch 1 at time 23
                                                  intro r24
                                                  rcases r24 with r24 | r24
                                                  · -- branch 0 at time 24
                                                    intro r25
                                                    rcases r25 with r25 | r25
                                                    · -- branch 0 at time 25
                                                      intro r26
                                                      rcases r26 with r26 | r26
                                                      · -- branch 0 at time 26
                                                        exact False.elim (exclude_100101001010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 b hb h1 h27 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26)
                                                      · -- branch 1 at time 26
                                                        intro r27
                                                        rcases r27 with r27 | r27
                                                        · -- branch 0 at time 27
                                                          intro r28
                                                          rcases r28 with r28 | r28
                                                          · -- branch 0 at time 28
                                                            exact False.elim (exclude_10010100101001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 b hb h11 h29 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28)
                                                          · -- branch 1 at time 28
                                                            exact False.elim (exclude_10010100101001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 b hb h16 h29 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28)
                                                        · -- branch 1 at time 27
                                                          exact False.elim (exclude_1001010010100100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27)
                                                    · -- branch 1 at time 25
                                                      exact False.elim (exclude_10010100101001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 b hb h3 h26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25)
                                                  · -- branch 1 at time 24
                                                    exact False.elim (exclude_1001010010100100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24)
                                              · -- branch 1 at time 22
                                                exact False.elim (exclude_10010100101001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22)
                                          · -- branch 1 at time 20
                                            exact False.elim (exclude_100101001010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 b hb h3 h21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20)
                                        · -- branch 1 at time 19
                                          exact False.elim (exclude_10010100101001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19)
                                    · -- branch 1 at time 17
                                      exact False.elim (exclude_100101001010010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                · -- branch 1 at time 15
                                  exact False.elim (exclude_1001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb h3 h16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                              · -- branch 1 at time 14
                                exact False.elim (exclude_100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                          · -- branch 1 at time 12
                            exact False.elim (exclude_1001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb h0 h13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                        · -- branch 1 at time 11
                          exact False.elim (exclude_100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                    · -- branch 1 at time 9
                      exact False.elim (exclude_1001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                · -- branch 1 at time 7
                  exact False.elim (exclude_10010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 b hb h3 h8 r0 r1 r2 r3 r4 r5 r6 r7)
              · -- branch 1 at time 6
                exact False.elim (exclude_1001011 x0 x1 x2 x3 x4 x5 x6 x7 b hb r0 r1 r2 r3 r4 r5 r6)
          · -- branch 1 at time 4
            exact False.elim (exclude_10011 x0 x1 x2 x3 x4 x5 b hb r0 r1 r2 r3 r4)
      · -- branch 1 at time 2
        intro r3
        rcases r3 with r3 | r3
        · -- branch 0 at time 3
          intro r4
          rcases r4 with r4 | r4
          · -- branch 0 at time 4
            intro r5
            rcases r5 with r5 | r5
            · -- branch 0 at time 5
              exact False.elim (exclude_101000 x0 x1 x2 x3 x4 x5 x6 b hb h3 h6 r0 r1 r2 r3 r4 r5)
            · -- branch 1 at time 5
              intro r6
              rcases r6 with r6 | r6
              · -- branch 0 at time 6
                intro r7
                rcases r7 with r7 | r7
                · -- branch 0 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    exact False.elim (exclude_101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb h1 h9 r0 r1 r2 r3 r4 r5 r6 r7 r8)
                  · -- branch 1 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        exact False.elim (exclude_10100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb h3 h11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                      · -- branch 1 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              exact False.elim (exclude_10100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb h1 h14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                            · -- branch 1 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  exact False.elim (exclude_1010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb h3 h16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                                · -- branch 1 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      intro r18
                                      rcases r18 with r18 | r18
                                      · -- branch 0 at time 18
                                        exact False.elim (exclude_1010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb h1 h19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                      · -- branch 1 at time 18
                                        intro r19
                                        rcases r19 with r19 | r19
                                        · -- branch 0 at time 19
                                          intro r20
                                          rcases r20 with r20 | r20
                                          · -- branch 0 at time 20
                                            exact False.elim (exclude_101001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 b hb h3 h21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20)
                                          · -- branch 1 at time 20
                                            exact False.elim (exclude_101001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 b hb h8 h21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20)
                                        · -- branch 1 at time 19
                                          exact False.elim (exclude_10100100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19)
                                    · -- branch 1 at time 17
                                      exact False.elim (exclude_101001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb h0 h18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                  · -- branch 1 at time 16
                                    exact False.elim (exclude_10100100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                              · -- branch 1 at time 14
                                exact False.elim (exclude_101001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                          · -- branch 1 at time 12
                            exact False.elim (exclude_1010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb h0 h13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                        · -- branch 1 at time 11
                          exact False.elim (exclude_101001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                    · -- branch 1 at time 9
                      exact False.elim (exclude_1010010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                · -- branch 1 at time 7
                  intro r8
                  rcases r8 with r8 | r8
                  · -- branch 0 at time 8
                    intro r9
                    rcases r9 with r9 | r9
                    · -- branch 0 at time 9
                      intro r10
                      rcases r10 with r10 | r10
                      · -- branch 0 at time 10
                        exact False.elim (exclude_10100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b hb h3 h11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
                      · -- branch 1 at time 10
                        intro r11
                        rcases r11 with r11 | r11
                        · -- branch 0 at time 11
                          intro r12
                          rcases r12 with r12 | r12
                          · -- branch 0 at time 12
                            intro r13
                            rcases r13 with r13 | r13
                            · -- branch 0 at time 13
                              exact False.elim (exclude_10100101001000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 b hb h1 h14 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13)
                            · -- branch 1 at time 13
                              intro r14
                              rcases r14 with r14 | r14
                              · -- branch 0 at time 14
                                intro r15
                                rcases r15 with r15 | r15
                                · -- branch 0 at time 15
                                  exact False.elim (exclude_1010010100100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 b hb h3 h16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
                                · -- branch 1 at time 15
                                  intro r16
                                  rcases r16 with r16 | r16
                                  · -- branch 0 at time 16
                                    intro r17
                                    rcases r17 with r17 | r17
                                    · -- branch 0 at time 17
                                      intro r18
                                      rcases r18 with r18 | r18
                                      · -- branch 0 at time 18
                                        exact False.elim (exclude_1010010100100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b hb h1 h19 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18)
                                      · -- branch 1 at time 18
                                        intro r19
                                        rcases r19 with r19 | r19
                                        · -- branch 0 at time 19
                                          intro r20
                                          rcases r20 with r20 | r20
                                          · -- branch 0 at time 20
                                            exact False.elim (exclude_101001010010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 b hb h3 h21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20)
                                          · -- branch 1 at time 20
                                            intro r21
                                            rcases r21 with r21 | r21
                                            · -- branch 0 at time 21
                                              intro r22
                                              rcases r22 with r22 | r22
                                              · -- branch 0 at time 22
                                                intro r23
                                                rcases r23 with r23 | r23
                                                · -- branch 0 at time 23
                                                  exact False.elim (exclude_101001010010010100101000 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 b hb h3 h24 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23)
                                                · -- branch 1 at time 23
                                                  intro r24
                                                  rcases r24 with r24 | r24
                                                  · -- branch 0 at time 24
                                                    intro r25
                                                    rcases r25 with r25 | r25
                                                    · -- branch 0 at time 25
                                                      exact False.elim (exclude_10100101001001010010100100 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 b hb h8 h26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25)
                                                    · -- branch 1 at time 25
                                                      exact False.elim (exclude_10100101001001010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 b hb h13 h26 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25)
                                                  · -- branch 1 at time 24
                                                    exact False.elim (exclude_1010010100100101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24)
                                              · -- branch 1 at time 22
                                                exact False.elim (exclude_10100101001001010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 b hb h0 h23 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22)
                                            · -- branch 1 at time 21
                                              exact False.elim (exclude_1010010100100101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21)
                                        · -- branch 1 at time 19
                                          exact False.elim (exclude_10100101001001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19)
                                    · -- branch 1 at time 17
                                      exact False.elim (exclude_101001010010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 b hb h0 h18 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17)
                                  · -- branch 1 at time 16
                                    exact False.elim (exclude_10100101001001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16)
                              · -- branch 1 at time 14
                                exact False.elim (exclude_101001010010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14)
                          · -- branch 1 at time 12
                            exact False.elim (exclude_1010010100101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b hb h0 h13 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
                        · -- branch 1 at time 11
                          exact False.elim (exclude_101001010011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
                    · -- branch 1 at time 9
                      exact False.elim (exclude_1010010101 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b hb h0 h10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
                  · -- branch 1 at time 8
                    exact False.elim (exclude_101001011 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 b hb r0 r1 r2 r3 r4 r5 r6 r7 r8)
              · -- branch 1 at time 6
                exact False.elim (exclude_1010011 x0 x1 x2 x3 x4 x5 x6 x7 b hb r0 r1 r2 r3 r4 r5 r6)
          · -- branch 1 at time 4
            exact False.elim (exclude_10101 x0 x1 x2 x3 x4 x5 b hb h0 h5 r0 r1 r2 r3 r4)
        · -- branch 1 at time 3
          exact False.elim (exclude_1011 x0 x1 x2 x3 x4 b hb r0 r1 r2 r3)
    · -- branch 1 at time 1
      exact False.elim (exclude_11 x0 x1 x2 b hb r0 r1)

end Collatz.Exploration.ElevenHalvesArithmetic
