/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.Wedge
import ScaleSpaceCore.ReceptiveField
import ScaleSpaceCore.BoostBracket
import ScaleSpaceCore.BoostBracketConcrete
import ScaleSpaceCore.PowerSumSymmetry
import ScaleSpaceCore.CausalCone
import ScaleSpaceCore.CausalData
import ScaleSpaceCore.PolyaFrequencyClass
import ScaleSpaceCore.L1Operators
import ScaleSpaceCore.BochnerConvolution
import ScaleSpaceCore.LaplaceUniqueness
import ScaleSpaceCore.TailInverse
import ScaleSpaceCore.Transform
import ScaleSpaceCore.Transport
import ScaleSpaceCore.Family
import ScaleSpaceCore.L1Continuity
import ScaleSpaceCore.Construction
import ScaleSpaceCore.SDProfile
import ScaleSpaceCore.SDProfileCone
import ScaleSpaceCore.BrownianDensity
import ScaleSpaceCore.GaussianKernel
import ScaleSpaceCore.BridgeExponents
import ScaleSpaceCore.Cin
import ScaleSpaceCore.CinRays
import ScaleSpaceCore.SelfDecomposable
import ScaleSpaceCore.DilationInvariance
import ScaleSpaceCore.TransformBridge
import ScaleSpaceCore.TransformUniqueness
import ScaleSpaceCore.Exponent
import ScaleSpaceCore.Representation
import ScaleSpaceCore.Nonvanishing
import ScaleSpaceCore.Pairing
import ScaleSpaceCore.Cascade
import ScaleSpaceCore.Additivity
import ScaleSpaceCore.Transmittance
import ScaleSpaceCore.Covariance
import ScaleSpaceCore.DilationAtom
import ScaleSpaceCore.Rigidity
import ScaleSpaceCore.Gauge
import ScaleSpaceCore.Truncation
import ScaleSpaceCore.NullArray
import ScaleSpaceCore.Tightness
import ScaleSpaceCore.LevyExtraction
import ScaleSpaceCore.Increments
import ScaleSpaceCore.GaugeLevy
import ScaleSpaceCore.LineInterfaces
import ScaleSpaceCore.SDExponents
import ScaleSpaceCore.DilationDecrease
import ScaleSpaceCore.AntitoneDensity
import ScaleSpaceCore.AnalysisDirection
import ScaleSpaceCore.MainConstruction
import ScaleSpaceCore.MainAnalysis
import ScaleSpaceCore.L1OperatorsSpace
import ScaleSpaceCore.BochnerConvolutionSpace
import ScaleSpaceCore.L1OperatorsEuclidean
import ScaleSpaceCore.L1ContinuitySpace
import ScaleSpaceCore.FourierPairingSpace
import ScaleSpaceCore.GammaMeasure
import ScaleSpaceCore.ConvPow
import ScaleSpaceCore.PosSemidefSum
import ScaleSpaceCore.LaplaceLaw
import ScaleSpaceCore.ExpIntegral

/-! # The shared scale-space core

The article-independent definitions and operator algebra: everything more than one article
in this line needs, proved from Mathlib alone. Nothing here rests on a cited interface, so a
consumer's `#print axioms` gains nothing by depending on it.
-/
