# GKKP26 artifacts

Artifacts for **[Overcoming the Randomness-Utility Trade-off in Answering Differentially Private Linear Queries](https://arxiv.org/abs/2609.02880)** by Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, and Pasin Manurangsi (2026).

## Open the artifacts

| Artifact | Open in your browser | Correspondence to the paper |
| --- | --- | --- |
| Lean proof | **[Open the interactive Lean viewer](https://live.lean-lang.org/#project=MathlibDemo&url=https%3A%2F%2Fraw.githubusercontent.com%2FsurendraGh%2FGKKP26_artifacts%2Frefs%2Fheads%2Fmain%2FProof.lean)** | The rounding and counting guarantees underlying **[Theorem 3.7](https://arxiv.org/html/2609.02880v1#S3.Thmtheorem7)**, developed in [Lemma 3.3](https://arxiv.org/html/2609.02880v1#S3.Thmtheorem3) through [Lemma 3.6](https://arxiv.org/html/2609.02880v1#S3.Thmtheorem6). |
| 3D visualizer | **[Open the interactive visualizer](https://raw.githack.com/surendraGh/GKKP26_artifacts/main/visualizer.html)** | **[Algorithm 1](https://arxiv.org/html/2609.02880v1#alg1)** in **Section 3.2**, illustrating the partition in **[Theorem 3.7](https://arxiv.org/html/2609.02880v1#S3.Thmtheorem7)** for dimension $d=3$. |

Theorem and algorithm numbers refer to [arXiv v1, Section 3.2: Explicit Construction for the $\ell_\infty$-norm](https://arxiv.org/html/2609.02880v1#S3.SS2).

## Explore the Lean proof

The viewer loads [Proof.lean](Proof.lean) into Lean Web's latest Mathlib environment. Allow the file and dependencies to load, then place the cursor inside a proof to inspect its goals and hypotheses in the **Infoview** panel.

The main declaration is `Rounding2.f_round_is_rounding_scheme`. For every positive dimension $d$ and integer $1 \le \ell \le d$, it establishes:

- Rounding changes each coordinate by at most $1$.
- Every closed $\ell_\infty$ ball of radius $1/\ell$ has at most $(\ell+1)^{8\lceil d/\ell\rceil}$ distinct rounded outputs.

These are the rounding and secludedness properties used in Theorem 3.7, with an explicit bound in place of the paper's asymptotic notation.

If the direct link does not load the file, copy [the raw proof](https://raw.githubusercontent.com/surendraGh/GKKP26_artifacts/main/Proof.lean) into [Lean Web](https://live.lean-lang.org/) with the latest Mathlib project selected.

## Explore the visualizer

The visualizer displays Algorithm 1's three-dimensional partition over $[-2,2]^3$. Use the controls to isolate partition cells, inspect slices, or move a query point and observe its selected shift and rounded output.

The browser link serves [visualizer.html](visualizer.html) through [raw.githack.com](https://raw.githack.com/); the service may show a confirmation page before opening it. Alternatively, download `visualizer.html` and open it locally in a browser. Internet access is needed for its JavaScript and styling dependencies.

## Paper

Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, and Pasin Manurangsi.  
*Overcoming the Randomness-Utility Trade-off in Answering Differentially Private Linear Queries.*  
arXiv:2609.02880, 2026. **[Abstract](https://arxiv.org/abs/2609.02880)** · **[HTML](https://arxiv.org/html/2609.02880v1)** · **[PDF](https://arxiv.org/pdf/2609.02880v1)**

This README was written by codex
