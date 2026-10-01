# Comparison of the Lean read-back with the paper

**Status: `agent-source-comparison-not-human-review`.** A separate agent compared the [blind Lean read-back](LEAN_READBACK.md) with the retained [manuscript snapshot](source-manuscript.tex), the [published arXiv v1 paper](https://arxiv.org/html/2609.28635v1), and the [paper-to-Lean mapping](paper-mapping.json). The read-back was produced from Lean sources without consulting the manuscript. This comparison finds the main statement consistent with Theorem 1 under the conventions explained below. It is an agent's mathematical assessment, not human certification or a Lean-checked theorem of semantic equivalence.

The [machine-readable record](paper-comparison.json) preserves input hashes and explicitly records `human_review_completed: false`. The retained development manuscript is not asserted byte-identical to the published arXiv source.

## Main theorem and definitions

| Paper item | Read-back of the formal artifact | Assessment |
|---|---|---|
| Theorem 1, equation (1.1), `thm:main` | `QuantumChannelContinuity.theorem_one`: the punctured two-sided order-one limit of `regularizedRenyi` equals `regularizedRelative` | Same limit assertion, including infinite divergence; no extra support or finiteness premise |
| State definitions, equations (1.2)–(1.3) | `stateRelative` and `stateRenyi` use normalized positive density operators and logarithms converted to bits | Same formulas and support/zero-overlap conventions at the relevant orders |
| Stabilization, equation (1.4) | Pure unit vectors with the reference a copy of the input space; reference dimension grows with block length | Same stated optimization scope, with tensor factor order reversed as explained below |
| Regularization, equation (1.5) | Supremum of normalized divergences over positive block lengths | Same supremum definition; two additional formal statements establish the normalized block limits |

The paper's two channels share an input space and an output space; it does not require input dimension to equal output dimension. The formal hypotheses likewise permit different dimensions. `Qudit` and `Nontrivial` give nonzero finite-dimensional complex Hilbert spaces, the usual setting for normalized quantum states and channels.

### Tensor factor order and the reference

The paper applies $\mathrm{id}_R\otimes N$ to an input on $R\otimes A$, with $R\simeq A$. Lean applies $N\otimes\mathrm{id}_A$ to an input on $A\otimes A$. These presentations are related by the canonical unitary swap $S_{X,Y}:X\otimes Y\to Y\otimes X$:

$$
S_{B,A}(N\otimes\mathrm{id}_A)(\rho)S_{B,A}^{\dagger}
=(\mathrm{id}_A\otimes N)
  (S_{A,A}\rho S_{A,A}^{\dagger}).
$$

Swapping is a bijection on unit-vector inputs. Relative entropy and sandwiched Rényi divergence are invariant under simultaneous unitary conjugation: spectral functions conjugate with the unitary, traces are unchanged, and support inclusion and zero overlap are preserved. This explains the factor-order difference as an ordinary mathematical identification. This document does not supply a new Lean proof of that identification.

Both definitions literally optimize over pure inputs with a reference of the input dimension. The paper also explains their equivalence to a more general ancillary-state presentation. Our comparison uses its explicit pure-input definition; it does not independently certify that purification-and-compression argument. Lean's associated tensor powers and terminal one-dimensional factor similarly agree with ordinary tensor powers under canonical unit and associativity identifications.

### Values, infinities, and order one

The formal state divergences use extended reals and explicitly handle support mismatch and zero quasi-entropy. Channel and regularized divergences use `ENNReal`, $[0,+\infty]$. The conversion `EReal.toENNReal` would clip a negative value to zero. The formal library has nonnegativity propositions for normalized relative entropy and the relevant Rényi orders $p\ge\tfrac12$, $p\ne1$, so this conversion changes no relevant divergence value.

Negative spectral powers vanish on the kernel, consistent with the paper's support convention. The formal scalar logarithm assigns a totalized value at zero; explicit support tests ensure singular states and infinite divergences are handled separately. No invertibility, finite-divergence, or support-inclusion hypothesis is added to the main theorem or the two block-limit identities. Convergence to $+\infty$ means eventual exceedance of every finite bound.

The paper defines Rényi divergence for $p\ge\tfrac12$, excluding $1$. Lean totalizes it at all real orders and assigns zero at order one, as explained in the read-back. The main statement uses the punctured filter `𝓝[≠] 1`, so that assigned value is irrelevant. A sufficiently small punctured neighborhood of one lies in the paper's admissible order domain. The statement concerns the two-sided limit, not continuity of the totalized function at its assigned value.

### Block limits are separate statements

`blockRenyi_tendsto_regularized` identifies the positive-block supremum with the limit of normalized block divergences for every fixed $p\ge\tfrac12$, $p\ne1$. `blockRelative_tendsto_regularized` provides the relative-entropy instance. Both allow infinite values. Thus the formalization addresses both equalities in equation (1.5), rather than assuming the limit characterization in its definitions. The totalized zero-block term is irrelevant to convergence at infinity. These statements do not assert a general interchange of order and block limits.

## Supporting scope and remaining review

The mapping's declaration names and file locators exist. Its supporting Schatten entry correctly records a restricted version: the paper's Lemma 3 covers every $p>1$, while the mapped formal estimates require $1<p\le2$. This range suffices for the order-one limit, since the relevant orders can eventually be chosen below two. It does **not** justify claiming the entire paper lemma for $p>2$ has been formalized. The mapped block-scaling statement supplies the normalization when treating an $n$-use block as one channel.

The fixed-dilation filter entry records a nonnegative threshold range, containing the paper's threshold range. The relative-entropy and Rényi testing entries record their positivity and finiteness conditions. These supporting locators were checked at the declaration level; this comparison did not re-audit their proofs or the dependency graph.

The later application corollaries—channel discrimination, subchannel AEP, exponential subchannel approximation, and the sharp testing threshold—remain outside the declared formalization scope. The [mapping](paper-mapping.json) makes that exclusion explicit.

A human mathematical reviewer should still confirm the definition identifications, singular-state conventions, and sufficiency of the restricted supporting estimates, and assess the manuscript's proof and later applications separately. No human review has been completed by this workflow. Comparator and Nanoda verify formal statements and proof terms within their documented scope; their acceptance does not by itself establish correspondence to the paper. This comparison introduces no new claim about build success or proof verification.
