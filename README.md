# QFTT-WESH

**Core paper and experimental data** for the framework:

> **"Quantum Field Theory of Time — The Weak Entanglement Symmetry Hypothesis" — L. Casagrande (2026).**

[Read the paper](paper/QFTT_WESH_core.pdf) · [N² scaling](experiments/3.3-3.4/fig_3-3_collision.png) · [cos²θ angular law](experiments/3.5/fig_3-5_angular_scaling.png)

This work addresses the frozen-time problem of canonical quantum gravity. Physical time is promoted to a local quantum field operator T̂(x), subject to superposition and objective collapse, with dynamics constructed from first principles. An endogenously dissipative master equation in an auxiliary, non-observable label *s* generates physical time through

    dt/ds = Γ[ρ] ≥ 0.

Complete positivity, finite-range locality, CPT symmetry, and a pre-geometric WESH–Noether conservation principle single out a unique GKSL structure with:

- a **quadratic local dissipator** D[T̂²(x)],
- a **bilocal difference channel** L_xy = T̂²(x) − T̂²(y), gated by a Rényi-2 entanglement functional,
- a **finite-range kernel** γ(x,y) defined via the symmetric pre-geometric proximity relation N_ξ, without background metric input.

The framework has **no free dimensionless parameters**.

---

## Falsifiable signatures

The construction yields two quantitative predictions:

- **Collective stability:** τ_coh ∝ N², a quadratic scaling of coherence time with system size under inverse bilocal couplings, in contrast with standard decoherence where τ_coh remains flat or degrades with N.

- **Angular law:** Γ(θ) = Γ̄(1 + ε cos²θ), a state-dependent cos²θ modulation of the parity decay rate, with factorized state/geometry contributions and a predicted **sign reversal** between GHZ (ε > 0) and W-state (ε < 0) preparations.

---

## Experimental tests (Section 3)

Both predictions have been tested through classical simulations and quantum hardware experiments.

### Numerical evidence

Pre-asymptotic collision model simulations (N = 2–16) yield an effective scaling γ(N) ∝ N^{−1.804}, consistent with an approach towards the predicted N^{−2} behaviour. A matched local baseline returns α = −1.00, validating the sensitivity of the extraction method.

### Hardware evidence (IBM Eagle + Rigetti Ankaa-3)

Experiments on **IBM Eagle** (127-qubit) and **Rigetti Ankaa-3** (82-qubit), totaling over **3 × 10⁶ shots**, show trends consistent with the predicted signatures:

- cos²θ angular dependence of the decay rate (R² = 0.947 at N = 3),
- W-state anti-modulation consistent with state-dependent behaviour,
- a gate-matched GHZ vs Fake-GHZ control separating entanglement from circuit overhead (Γ_PROD/Γ_GHZ ≈ 2.6),
- cross-platform countercheck across distinct hardware stacks.

---

## Repository layout

    QFTT-WESH-1/
    ├── paper/
    │   ├── main.tex                 # LaTeX source (targeting CQG)
    │   └── QFTT_WESH_core.pdf      # Compiled paper
    ├── figures/
    │   ├── Picture1.png  …  Picture13.png
    ├── experiments/
    │   ├── 3.1/                     # WESH vs standard decoherence (CPU)
    │   ├── 3.2/                     # Collective stability scaling
    │   ├── 3.3-3.4/                 # Collision model vs local baseline
    │   ├── 3.5/                     # Angular law — IBM Eagle
    │   ├── 3.6/                     # Fake-GHZ gate-matched control
    │   ├── 3.7-3.8/                 # GHZ vs PRODUCT distributions (21σ)
    │   └── 3.9/                     # Cross-platform — Rigetti Ankaa-3
    └── README.md

---

## Experiments

| Folder | Figure(s) | Description |
|:-------|:----------|:------------|
| `3.1/` | Fig. 3.1 | WESH vs standard local decoherence: purity and coherence scaling (CPU simulations, N = 3–9) |
| `3.2/` | Fig. 3.2 | Robustness of collective protection under different noise channels and coupling profiles (N = 2–16) |
| `3.3-3.4/` | Figs. 3.3–3.4 | Pre-asymptotic rate scaling: collision model (α ≈ −1.80) vs local baseline (α = −1.00) |
| `3.5/` | Fig. 3.5 | IBM Eagle: cos²θ angular dependence, mini-scaling, and W-state control |
| `3.6/` | Fig. 3.6 | Fake-GHZ control: gate-matched separation of entanglement from circuit overhead |
| `3.7-3.8/` | Figs. 3.7–3.8 | GHZ vs PRODUCT parity distributions, ECDFs, violin plots (21σ significance) |
| `3.9/` | Fig. 3.9 | Cross-platform countercheck on Rigetti Ankaa-3 (N = 3–6, 400k shots) |

Each folder is self-contained: running the analysis script regenerates the corresponding plots from the included data. Hardware access is **not** required — all QPU results are provided as CSV/JSON files.

---

## Reproducing figures

    cd experiments/3.5/
    python analyze_3.5_angular_scaling.py

Requires Python 3.x with `numpy`, `pandas`, `matplotlib`, `scipy`.

---

## Acknowledgments

This work was developed with the assistance of artificial intelligence tools in a cross-inferencing multi-AI workflow. The primary tools employed were those of OpenAI, Anthropic, and Google. The conceptual framework, methodology, research direction, and verification of every output remained with the author.

---

## Citation

    @article{Casagrande2026QFTT,
      author  = {Casagrande, Luca},
      title   = {Quantum Field Theory of Time: The Weak Entanglement Symmetry Hypothesis},
      year    = {2026}
    }

---

## License

This work is released under the [MIT License](https://opensource.org/licenses/MIT).
