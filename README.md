# LTFP-Lean

A Lean 4 library formalizing Francis Bach (2024),
*Learning Theory from First Principles* (MIT Press), built on
[Mathlib](https://github.com/leanprover-community/mathlib4) and the
[`auto-res/lean-rademacher`](https://github.com/auto-res/lean-rademacher)
kernel (vendored as `LTFP/Foundations`).

The library covers the book chapter-by-chapter — supervised-learning
foundations, linear least squares, ERM, optimization, local averaging,
kernels, sparse methods, neural networks, ensembles, online / bandits,
overparameterized regimes, structured prediction, probabilistic models,
and statistical lower bounds. A sibling `LTFP/MathlibExt/` subdirectory
collects Mathlib-style extension modules (total-variation distance,
sub-exponential class, Le Cam's two-point method, DGL adversary,
subgradient of `|·|`, L-smoothness, RKHS scaffolding, ramp-function UAT
building blocks, etc.) covering theorems Mathlib does not yet have.

Several of these modules are being upstreamed: see open draft PRs at
`leanprover-community/mathlib4` ([#39164](https://github.com/leanprover-community/mathlib4/pull/39164),
[#39165](https://github.com/leanprover-community/mathlib4/pull/39165),
[#39166](https://github.com/leanprover-community/mathlib4/pull/39166),
[#39167](https://github.com/leanprover-community/mathlib4/pull/39167),
[#39168](https://github.com/leanprover-community/mathlib4/pull/39168)).

## Status

- Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
- Mathlib: tracks `master` (pinned by `lake-manifest.json`)
- `lake build` exits 0
- No `sorry`, no `admit`

## Layout

```
LTFP/
├── Foundations/                   vendored from auto-res/lean-rademacher
├── Ch01_Preliminaries/            §1.1 LinAlg, §1.1.5 DiffCalc, §1.2 Concentration
├── Ch02_SupervisedLearning/       §2.2 Risk, Bayes predictor; §2.3 ERM; §2.4 Consistency
├── Ch03_LinearLeastSquares/       §3.3 OLS, §3.5 Fixed design, §3.6 Ridge
├── Ch04_ERM/                      §4.x risk decomposition, approximation/estimation
├── Ch05_Optimization/             §5 gradient descent, SGD, convex
├── Ch06_LocalAveraging/           §6 kNN, partition, kernel estimators
├── Ch07_Kernels/                  §7 RKHS, KRR
├── Ch08_Sparse/                   §8 Lasso, ℓ¹
├── Ch09_NeuralNetworks/           §9 single-hidden / multilayer / NTK anchors
├── Ch10_Ensemble/                 §10 boosting, bagging
├── Ch11_OnlineBandits/            §11 online learning, UCB, ETC
├── Ch12_Overparameterized/        §12 double descent, min-norm
├── Ch13_StructuredPrediction/     §13 multiclass, surrogates
├── Ch14_Probabilistic/            §14 log-likelihoods, PAC-Bayes
├── Ch15_LowerBounds/              §15 statistical lower bounds, Le Cam
└── MathlibExt/                    Mathlib-quality extension modules
    ├── Probability/{TotalVariation,Distance/Pinsker,Adversary,LeCam,DonskerVaradhan,Moments/SubExponential}.lean
    ├── Analysis/{Smoothness,Subgradient/L1,InnerProductSpace/RKHS}.lean
    ├── Topology/UAT.lean
    ├── MatrixAnalysis/Lieb.lean
    └── Calculus/GradientFlow.lean
```

## Build

```
git clone https://github.com/allenhaozhu/LTFP-Lean.git
cd LTFP-Lean
lake exe cache get          # fetches Mathlib oleans (5-10 min cold)
lake build                  # ~3 min after cache
```

The chapter hubs (`LTFP/Ch<NN>_*.lean`) re-export every file in the
chapter directory; the top-level `LTFP.lean` re-exports every chapter
hub plus `LTFP.Foundations` and `LTFP.MathlibExt`. So
`import LTFP` gives you the whole library.

## License

MIT. See `LICENSE`. The vendored `LTFP/Foundations` kernel originates
from [`auto-res/lean-rademacher`](https://github.com/auto-res/lean-rademacher)
and is redistributed unchanged under the same license.

## Citation

If you use this library in academic work, please cite the underlying
textbook:

```bibtex
@book{bach2024ltfp,
  author    = {Bach, Francis},
  title     = {Learning Theory from First Principles},
  publisher = {MIT Press},
  year      = {2024},
}
```

A companion description of the library itself is in preparation; see
the [JMLR MLOSS paper draft](https://github.com/allenhaozhu/LTFP-Lean/releases)
once released.

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md).
