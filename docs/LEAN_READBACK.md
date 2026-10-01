# Lean declaration read-back

**Status: `agent-readback-not-human-review`.** This is an independent translation of Lean definitions and proposition statements. It is not a human review or a comparison with a manuscript. No claim of manuscript faithfulness is made.

Only Lean source/dependency files, `lakefile.toml`, and `lean-toolchain` were used. Declaration-name searches located the relevant sources; implementation comments and docstrings were excluded when interpreting them. The manuscript, README, `formalization.yaml`, paper links, and previous prose audit reports were not consulted. This read-back does not audit the proof dependency graph or certify compilation. The exact files examined and their SHA-256 hashes are recorded in [`lean-readback.json`](lean-readback.json).

## Mathematical objects and conventions

`QuantumState.Qudit H` makes $H$ a finite-dimensional complex inner-product space, with its norm and completeness. `Nontrivial H` additionally excludes the zero vector space; equivalently its complex dimension is positive. The same conditions apply to $K$, whose dimension can differ from that of $H$.

`QuantumChannel.CPTP H K` is a complex-linear map from operators on $H$ to operators on $K$. It preserves positivity at every finite matrix amplification and preserves the trace of every operator. `QuantumChannelContinuity.DensityState H` is a positive semidefinite operator $\rho$ with $\operatorname{Tr}\rho=1$. No positive-definiteness assumption is imposed.

For such states define

$$
 Q_\alpha(\rho,\sigma)
 =\operatorname{Re}\operatorname{Tr}
 \left(\sigma^{(1-\alpha)/(2\alpha)}\rho
       \sigma^{(1-\alpha)/(2\alpha)}\right)^\alpha.
$$

These are the `CFC.rpow` spectral powers. On a zero eigenvalue the scalar convention is $0^t=0$ for $t\ne0$ and $0^0=1$; negative powers therefore use zero on the kernel. `CFC.log` uses the scalar convention $\ln 0=0$. The separate infinity tests below are consequently essential. `suppLE ρ σ` is literally $\ker\sigma\subseteq\ker\rho$, equivalent for these states to $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$.

For the relevant orders $\alpha\ge\tfrac12,\ \alpha\ne1$, `QuantumChannelContinuity.stateRenyi` is the extended-real quantity

$$
 \widetilde D_\alpha(\rho\Vert\sigma)=
 \begin{cases}
 +\infty,&\alpha>1\text{ and }\operatorname{supp}\rho\not\subseteq\operatorname{supp}\sigma,\\
 +\infty,&\alpha<1\text{ and }Q_\alpha(\rho,\sigma)=0,\\
 \dfrac{\log_2 Q_\alpha(\rho,\sigma)}{\alpha-1},&\text{otherwise}.
 \end{cases}
$$

In the dependency's lower-order infinity test there is also a condition $\rho\ne0$, automatic for `DensityState`. There is no support-inclusion requirement below $1$ when the quasi-entropy is nonzero. `QuantumChannelContinuity.stateRelative` is

$$
 D(\rho\Vert\sigma)=
 \begin{cases}
 \dfrac{\operatorname{Re}\operatorname{Tr}\rho(\ln\rho-\ln\sigma)}{\ln2},
     &\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma,\\
 +\infty,&\text{otherwise}.
 \end{cases}
$$

The definitions multiply the dependency's natural-log expressions by $1/\ln2$: all displayed divergences are in bits. Trace normalization eliminates the dependency formulas' division by $\operatorname{Re}\operatorname{Tr}\rho$.

`PureInput A` is a vector $\psi\in A$ with $\lVert\psi\rVert=1$, and its density operator is $|\psi\rangle\langle\psi|$. For a channel $E:H\to K$, `amplifiedOutput E` applies $E\otimes\mathrm{id}_H$ to a state on $H\otimes H$, giving a state on $K\otimes H$. Thus the reference is a second copy of the input space. The channel definitions are precisely

$$
 \widetilde D_\alpha^{\mathrm{ch}}(N\Vert M)
 =\sup_{\substack{\psi\in H\otimes H\\\lVert\psi\rVert=1}}
 \widetilde D_\alpha\bigl((N\otimes\mathrm{id}_H)(\psi\psi^*)
                  \Vert(M\otimes\mathrm{id}_H)(\psi\psi^*)\bigr),
$$

and $D^{\mathrm{ch}}$ is the same supremum with $D$. These are `channelRenyi` and `channelRelative`. Formally each state value first undergoes `EReal.toENNReal`, which preserves $+\infty$ and clips a finite negative value to zero. The source proves nonnegativity for the relevant Rényi orders and for relative entropy, so clipping changes none of these values. Channel, block, and regularized values lie in `ℝ≥0∞`, namely $[0,+\infty]$.

Define $H_0=K_0=\mathbb C$ (formally `EuclideanSpace ℂ (Fin 1)`), $H_{n+1}=H\otimes H_n$, and $K_{n+1}=K\otimes K_n$. `TensorPower` uses this association and terminal one-dimensional factor. `channelPower N 0` is the identity on that factor and `channelPower N (n+1)` is $N\otimes N_n$; under the usual unit identifications this is $N^{\otimes n}$. Then

$$
 B_\alpha(n)=\widetilde D_\alpha^{\mathrm{ch}}(N_n\Vert M_n),\qquad
 B(n)=D^{\mathrm{ch}}(N_n\Vert M_n),
$$

are `blockRenyi` and `blockRelative`. At each length $n$, the pure input is on $H_n\otimes H_n$, the reference dimension is $(\dim H)^n$, and the two output states are on $K_n\otimes H_n$. The definitions of `regularizedRenyi` and `regularizedRelative` are

$$
 R_\alpha=\sup_{n\ge1}\frac{B_\alpha(n)}n,\qquad
 R=\sup_{n\ge1}\frac{B(n)}n.
$$

`BlockInput H` is a dependent pair $(n,\psi)$ with $n\in\mathbb N$, $n>0$, and a unit vector $\psi\in H_n\otimes H_n$. `inputRenyi` and `inputRelative` are the corresponding output-state divergences divided by $n$. The stated source identities express $R_\alpha$ and $R$ as suprema over all such pairs.

## The three declarations

1. **`QuantumChannelContinuity.theorem_one`** (`QuantumChannelContinuity/Main.lean`): for every $H,K$ as above and every pair of CPTP channels $N,M:H\to K$,

   $$
   \lim_{\substack{\alpha\to1\\\alpha\ne1}}R_\alpha=R
   \quad\text{in }[0,+\infty].
   $$

   Its Lean source filter is `𝓝[≠] (1 : ℝ)`, the punctured **two-sided** real neighborhood filter, and its target is `𝓝 (regularizedRelative N M)`. The declaration has no finite-divergence or support hypothesis and no explicit order restriction on the source filter. A sufficiently small neighborhood of $1$ already lies above $1/2$. It includes $R=+\infty$; in that case every finite bound is eventually exceeded from both sides.

2. **`QuantumChannelContinuity.blockRenyi_tendsto_regularized`** (`QuantumChannelContinuity/RegularizationLimits.lean`): for every such pair $N,M$ and every fixed real $p\ge\tfrac12$ with $p\ne1$,

   $$
   \lim_{n\to\infty}\frac{B_p(n)}n
      =R_p=\sup_{n\ge1}\frac{B_p(n)}n
   \quad\text{in }[0,+\infty].
   $$

   The source is natural-number `atTop`. The endpoint $p=1/2$ is included. The statement allows infinite values and has no support or finiteness hypothesis.

3. **`QuantumChannelContinuity.blockRelative_tendsto_regularized`** (the same file): for every such pair $N,M$,

   $$
   \lim_{n\to\infty}\frac{B(n)}n
      =R=\sup_{n\ge1}\frac{B(n)}n
   \quad\text{in }[0,+\infty].
   $$

   Its source is also natural-number `atTop`; there is no support or finiteness hypothesis.

## Points for later human comparison

- The regularized quantities are defined as **suprema** over positive block lengths; the latter two theorems identify these suprema with limits. The sequence expressions also have a totalized $n=0$ value, irrelevant to `atTop`.
- Stabilization uses pure vectors and exactly a copy of the input space at every block length. The definitions do not literally quantify over arbitrary ancillary spaces or mixed input states. Any comparison using those alternative presentations must account for their equivalence separately.
- The state Rényi definition is a total function of every real order. Unfolding its definition at $\alpha=1$, both strict inequality infinity tests are false and the factor $1/(\alpha-1)$ is totalized to zero, so `stateRenyi 1` and `regularizedRenyi 1` evaluate to zero. This is a definition-level observation, not a separately checked Lean theorem in this review. The first theorem is a punctured limit, not continuity of that total function at its assigned value.
- All limits use the extended nonnegative-real topology, including convergence to $+\infty$. The statements provide no quantitative rate, uniformity in the channels or order, or joint limit assertion.
- The first theorem concerns the order limit **after** forming the block supremum. The two sequence theorems concern fixed-order block limits; their statements alone are not a general theorem interchanging two limits.

The companion JSON records this review's method, these exact declaration names, mathematical descriptions, and input-file hashes. Its status remains `agent-readback-not-human-review`.
