/-
Umbrella file for the `LTFP.MathlibExt` namespace.

This collects Mathlib-quality extension modules developed inside LTFP-Lean
that are candidates for an upstream pull request.  Each module follows
Mathlib coding conventions (full docstrings, namespaced declarations,
no `sorry`).
-/

import LTFP.MathlibExt.Analysis.Smoothness
import LTFP.MathlibExt.Analysis.Subgradient.L1
import LTFP.MathlibExt.Analysis.Subgradient.SumRule
import LTFP.MathlibExt.Analysis.InnerProductSpace.RKHS
import LTFP.MathlibExt.Calculus.FunctionMovementAlongCurve
import LTFP.MathlibExt.Calculus.GradientFlow
import LTFP.MathlibExt.Calculus.GradientFlowMovementBound
import LTFP.MathlibExt.Calculus.GradientFlowRandomInit
import LTFP.MathlibExt.Calculus.ParameterMovementBoundedDeriv
import LTFP.MathlibExt.Probability.Adversary
import LTFP.MathlibExt.Probability.TotalVariation
import LTFP.MathlibExt.Probability.Distance.Bhattacharyya
import LTFP.MathlibExt.Probability.Distance.Pinsker
import LTFP.MathlibExt.Probability.Distributions.GaussianObservationKernelMean
import LTFP.MathlibExt.Probability.Distributions.JointPriorObservationSndMean
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussian
import LTFP.MathlibExt.Probability.DonskerVaradhan
import LTFP.MathlibExt.Probability.FunctionClassConcentration
import LTFP.MathlibExt.Probability.KullbackLeibler
import LTFP.MathlibExt.Probability.Moments.SubExponential
import LTFP.MathlibExt.Probability.LeCam
import LTFP.MathlibExt.Probability.LinearClassSampleCover
import LTFP.MathlibExt.Probability.LinearClassSampleCoverCard
import LTFP.MathlibExt.Probability.LinearizedRiskLipschitz
import LTFP.MathlibExt.Probability.LinearizedRiskSampleCover
import LTFP.MathlibExt.MatrixAnalysis.Lieb
import LTFP.MathlibExt.MatrixAnalysis.OperatorAntitoneScalarBridge
import LTFP.MathlibExt.MatrixAnalysis.OperatorConcaveScalarBridge
import LTFP.MathlibExt.MatrixAnalysis.OperatorConvexScalarBridge
import LTFP.MathlibExt.MatrixAnalysis.OperatorMonotoneScalarBridge
import LTFP.MathlibExt.Topology.UAT
