# arxiv-2511-10811-transformers-know-more-than-they-can-tell-learning-the-colla

Citation: François Charton and Ashvni Narayanan, "Transformers know more than they can tell -- Learning the Collatz sequence", arXiv:2511.10811 [2025].

Authors: François Charton, Ashvni Narayanan

arXiv: [2511.10811](https://arxiv.org/abs/2511.10811)

Year: 2025

Classification: density

Abstract:

We investigate transformer prediction of long Collatz steps, a complex arithmetic function that maps odd integers to their distant successors in the Collatz sequence ( $u_{n+1}=u_n/2$ if $u_n$ is even, $u_{n+1}=(3u_n+1)/2$ if $u_n$ is odd). Model accuracy varies with the base used to encode input and output. It can be as high as $99.7\%$ for bases $24$ and $32$, and as low as $37$ and $25\%$ for bases $11$ and $3$. Yet, all models, no matter the base, follow a common learning pattern. As training proceeds, they learn a sequence of classes of inputs that share the same residual modulo $2^p$. Models achieve near-perfect accuracy on these classes, and less than $1\%$ for all other inputs. This maps to a mathematical property of Collatz sequences: the length of the loops involved in the computation of a long Collatz step can be deduced from the binary representation of its input. The learning pattern reflects the model learning to predict inputs associated with increasing loop lengths. An 

Lean file: `Collatz/Papers/Arxiv2511_10811.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
