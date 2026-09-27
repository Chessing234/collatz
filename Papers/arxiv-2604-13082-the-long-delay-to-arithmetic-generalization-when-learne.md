# arxiv-2604-13082-the-long-delay-to-arithmetic-generalization-when-learne

Citation: Laura Gomezjurado Gonzalez, "The Long Delay to Arithmetic Generalization: When Learned Representations Outrun Behavior", arXiv:2604.13082 [2026].

Authors: Laura Gomezjurado Gonzalez

arXiv: [2604.13082](https://arxiv.org/abs/2604.13082)

Year: 2026

Classification: verification

Abstract:

Grokking in transformers trained on algorithmic tasks is characterized by a long delay between training-set fit and abrupt generalization, but the source of that delay remains poorly understood. In encoder-decoder arithmetic models, we argue that this delay reflects limited access to already learned structure rather than failure to acquire that structure in the first place. We study one-step Collatz prediction and find that the encoder organizes parity and residue structure within the first few thousand training steps, while output accuracy remains near chance for tens of thousands more. Causal interventions support the decoder bottleneck hypothesis. Transplanting a trained encoder into a fresh model accelerates grokking by 2.75 times, while transplanting a trained decoder actively hurts. Freezing a converged encoder and retraining only the decoder eliminates the plateau entirely and yie

Lean file: `Collatz/Papers/Arxiv2604_13082.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-b (2026-09-15)
