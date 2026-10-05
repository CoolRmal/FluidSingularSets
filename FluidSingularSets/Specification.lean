-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Topology.MetricSpace.Snowflaking

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.MetricSpace.Snowflaking

/-!
# Local suitable weak solutions for singular-set refinements

The solution and regularity definitions are adapted from the CKN comparator.
They are restated here using Mathlib alone for independent auditing. Space-time has
ordinary coordinates for the Navier–Stokes equations and the parabolic metric
only where that metric is mathematically relevant.
-/

@[expose] public section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Gradient InnerProductSpace NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKNChallenge

/-! ## Local weak Navier–Stokes solutions -/

/-- Three-dimensional Euclidean space. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The usual notation for a Hilbert-valued `L²` space. -/
local notation "L²(" α ", " E ")" => Lp E 2 (volume : Measure α)

/-! ### Test functions and spatial differential operators -/

/-- Smooth compactly supported `Y`-valued functions supported in `Ω`. -/
def testFunctions
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ω : Set X) : Set (X → Y) :=
  {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω}

local notation "Dₓ" g:arg z:arg =>
  fderiv ℝ (fun x : ℝ³ ↦ g (x, Prod.snd z)) (Prod.fst z)
local notation "∂ₜ" g:arg z:arg =>
  fderiv ℝ (fun t : ℝ ↦ g (Prod.fst z, t)) (Prod.snd z) 1
local notation "∇ₓ" g:arg z:arg =>
  gradient (fun x : ℝ³ ↦ g (x, Prod.snd z)) (Prod.fst z)
local notation "divₓ" g:arg z:arg =>
  LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap (Dₓ g z))
local notation "Δₓ" g:arg z:arg =>
  Laplacian.laplacian (fun x : ℝ³ ↦ g (x, Prod.snd z)) (Prod.fst z)
local notation "⟪" A ", " B "⟫ₕₛ" =>
  LinearMap.trace ℝ ℝ³
    (ContinuousLinearMap.toLinearMap (ContinuousLinearMap.adjoint A ∘L B))
local infixr:100 " ⊗ᵣ " => InnerProductSpace.rankOne ℝ

/-- `Du` is the weak derivative of `u` on `U` for the ambient measure. The
definition is coordinate-free for real Hilbert spaces equipped with a measure.
For the Euclidean spaces and volume used below, almost-everywhere
uniqueness on open sets follows from Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/
structure HasWeakDerivativeOn
    {X Y : Type*}
    [MeasureSpace X]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (u : X → Y) (Du : X → (X →L[ℝ] Y)) : Prop where
  functionLocallyIntegrable : LocallyIntegrableOn u U volume
  derivativeLocallyIntegrable : LocallyIntegrableOn Du U volume
  integral_eq : ∀ φ ∈ testFunctions ℝ U, ∀ v (y' : Y →L[ℝ] ℝ),
    ∫ x in U, φ x * y' (Du x v) ∂volume =
      -∫ x in U, ⟪∇ φ x, v⟫_ℝ * y' (u x) ∂volume

/-! ### The solution class -/

/-- The fields of the Navier–Stokes system together with a chosen global weak
spatial gradient of the velocity. -/
structure NSEData (Ω : Set ℝ³) (I : Set ℝ) where
  isOpenSpace : IsOpen Ω
  isOpenTime : IsOpen I
  ordConnectedTime : OrdConnected I
  u : ℝ³ × ℝ → ℝ³
  Dxu : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)
  p : ℝ³ × ℝ → ℝ
  f : ℝ³ × ℝ → ℝ³
  weakDerivative :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakDerivativeOn Ω (fun x ↦ u (x, t)) (fun x ↦ Dxu (x, t))

/-- `U ⋐ Ω` means that the closure of `U` is compact and contained in `Ω`. -/
def IsCompactlyContained
    {X : Type*} [TopologicalSpace X] (U Ω : Set X) : Prop :=
  IsCompact (closure U) ∧ closure U ⊆ Ω

local infix:50 " ⋐ " => IsCompactlyContained

/-- The energy-class bounds on a fixed space-time product set `U × J`. -/
structure HasEnergyRegularityOn
    {Ω : Set ℝ³} {I : Set ℝ} (data : NSEData Ω I) (q : ℝ≥0)
    (U : Set ℝ³) (J : Set ℝ) : Prop where
  velocityTimeBound :
    essSup (fun t ↦ eLpNorm (fun x ↦ data.u (x, t)) 2
      (volume.restrict U)) (volume.restrict J) < ∞
  velocityMemLp : MemLp data.u 2 (volume.restrict (U ×ˢ J))
  gradientMemLp : MemLp data.Dxu 2 (volume.restrict (U ×ˢ J))
  pressureMemLp : MemLp data.p (3 / 2) (volume.restrict (U ×ˢ J))
  forceMemLp : MemLp data.f q (volume.restrict (U ×ˢ J))

/-- The incompressibility and momentum equations in distributional form. -/
structure SolvesDistributionalNSE
    {Ω : Set ℝ³} {I : Set ℝ} (data : NSEData Ω I) : Prop where
  incompressible : ∀ ψ ∈ testFunctions ℝ (Ω ×ˢ I),
    ∫ z in Ω ×ˢ I, ⟪data.u z, ∇ₓ ψ z⟫_ℝ = 0
  momentum : ∀ φ ∈ testFunctions ℝ³ (Ω ×ˢ I),
    ∫ z in Ω ×ˢ I,
      ⟪data.u z, ∂ₜ φ z⟫_ℝ
        + ⟪data.u z ⊗ᵣ data.u z, Dₓ φ z⟫ₕₛ
        - ⟪data.Dxu z, Dₓ φ z⟫ₕₛ
        + data.p z * divₓ φ z
        + ⟪data.f z, φ z⟫_ℝ = 0

/-- The local energy inequality for nonnegative test functions. -/
def SatisfiesLocalEnergyInequality
    {Ω : Set ℝ³} {I : Set ℝ} (data : NSEData Ω I) : Prop :=
  ∀ ψ ∈ testFunctions ℝ (Ω ×ˢ I), (∀ z, 0 ≤ ψ z) →
    2 * ∫ z in Ω ×ˢ I, ⟪data.Dxu z, data.Dxu z⟫ₕₛ * ψ z ≤
      ∫ z in Ω ×ˢ I,
        ‖data.u z‖ ^ 2 * (∂ₜ ψ z + Δₓ ψ z)
          + (‖data.u z‖ ^ 2 + 2 * data.p z) * ⟪data.u z, ∇ₓ ψ z⟫_ℝ
          + 2 * ⟪data.f z, data.u z⟫_ℝ * ψ z

/-- A local suitable weak solution: finite-energy data satisfying the
distributional Navier–Stokes equations and the local energy inequality. -/
structure LocalWeakNSESolution
    (Ω : Set ℝ³) (I : Set ℝ) (q : ℝ≥0)
    extends NSEData Ω I where
  energyRegularity : ∀ (U : Set ℝ³) (J : Set ℝ),
    IsOpen U ∧ U ⋐ Ω ∧ OrdConnected J ∧ J ⋐ I →
      HasEnergyRegularityOn toNSEData q U J
  equations : SolvesDistributionalNSE toNSEData
  energyInequality : SatisfiesLocalEnergyInequality toNSEData

/-! ## Parabolic geometry and regularity -/

/-- `ℝ` equipped with the metric `dist s t = |s - t|^(1/2)`, used to define
the parabolic Hausdorff dimension. -/
abbrev Rpar :=
  Metric.Snowflaking ℝ (1 / 2 : ℝ) (by norm_num) (by norm_num)

instance : MeasurableSpace Rpar := borel Rpar
instance : BorelSpace Rpar := ⟨rfl⟩

/-- Hausdorff measure for the parabolic metric, written in ordinary
space-time coordinates. -/
def parabolicHausdorffMeasure (d : ℝ) : Measure (ℝ³ × ℝ) :=
  Measure.map
    ((Homeomorph.refl ℝ³).prodCongr
      (Metric.Snowflaking.homeomorph : Rpar ≃ₜ ℝ)).toMeasurableEquiv
    (Measure.hausdorffMeasure d : Measure (ℝ³ × Rpar))

/-- The backward cylinder `Qᵣ(z₀) = Bᵣ(x₀) × (t₀-r²,t₀]`, with optional top
centre `z₀ = (x₀,t₀)` defaulting to the origin. -/
abbrev Q (r : ℝ) (z₀ : ℝ³ × ℝ := 0) : Set (ℝ³ × ℝ) :=
  Metric.ball z₀.1 r ×ˢ Ioc (z₀.2 - r ^ 2) z₀.2

/-- The Hölder norm of an almost-everywhere equivalence class: the infimum,
over all representatives, of the supremum norm plus Hölder seminorm. -/
def aeHolderNormOn
    {X Y : Type*} [PseudoEMetricSpace X] [MeasureSpace X]
    [SeminormedAddCommGroup Y]
    (U : Set X) (g : X → Y) (γ : ℝ≥0) : ℝ≥0∞ :=
  ⨅ (w : X → Y) (_ : w =ᵐ[volume.restrict U] g),
    (⨆ x : U, ‖w x‖ₑ) + eHolderNorm γ (U.domRestrict w)

/-- Local Hölder regularity at a point, for arbitrary metric-measure spaces. -/
def IsHolderRegularPoint
    {X Y : Type*} [PseudoEMetricSpace X] [MeasureSpace X]
    [SeminormedAddCommGroup Y]
    (u : X → Y) (x₀ : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
    ∃ γ : ℝ≥0, 0 < γ ∧ γ ≤ 1 ∧ aeHolderNormOn U u γ < ∞

/-- The points of `Ω` where `u` has no local Hölder representative. Ordinary
space-time Hölder regularity is used here; on bounded cylinders it is
equivalent to parabolic Hölder regularity after halving the exponent. -/
def singularSet
    (Ω : Set ℝ³) (I : Set ℝ) (u : ℝ³ × ℝ → ℝ³) : Set (ℝ³ × ℝ) :=
  {z ∈ Ω ×ˢ I | ¬IsHolderRegularPoint u z}

end CKNChallenge

namespace FluidSingularSets

/-- Three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Time equipped with square-root distance. -/
abbrev ParabolicTime := CKNChallenge.Rpar

instance : MeasurableSpace ParabolicTime := borel ParabolicTime
instance : BorelSpace ParabolicTime := ⟨rfl⟩

/-- Ordinary coordinates, with the parabolic metric used after lifting the time coordinate. -/
abbrev SpaceTime := Space × ℝ

/-- The product metric here is `max ‖x-y‖ |t-s|^(1/2)`. -/
abbrev ParabolicSpaceTime := Space × ParabolicTime

/-- Passage from ordinary space-time coordinates to parabolic metric coordinates. -/
def toParabolic : SpaceTime → ParabolicSpaceTime :=
  fun z ↦ (z.1, Metric.Snowflaking.toSnowflaking z.2)

/-- The small-radius gauge `r(log(1/r))²`, extended constantly after `exp(-2)`.
The value at zero is zero, and the value at infinite diameter is infinite. The extension does
not affect the Hausdorff measure because the construction only uses arbitrarily small covers. -/
def logSquaredGauge (d : ℝ≥0∞) : ℝ≥0∞ :=
  if d = ∞ then ∞ else
    ENNReal.ofReal (if d.toReal ≤ Real.exp (-2) then
      d.toReal * (Real.log (1 / d.toReal)) ^ 2 else 4 * Real.exp (-2))

/-- Hausdorff measure for the logarithmic gauge and parabolic diameter.
This uses Mathlib's metric Hausdorff measure constructor on the lifted set. -/
def logSquaredHausdorffMeasure (E : Set SpaceTime) : ℝ≥0∞ :=
  (Measure.mkMetric logSquaredGauge : Measure ParabolicSpaceTime) (toParabolic '' E)

/-- Parabolic covering number, using arbitrary centers and closed radius-`r` balls.
The value is extended nonnegative so noncoverable sets retain the value infinity. -/
def parabolicCoveringNumber (E : Set SpaceTime) (r : ℝ≥0) : ℕ∞ :=
  Metric.externalCoveringNumber r (toParabolic '' E)

/-- Upper parabolic box dimension is the infimum of nonnegative exponents `s` such that
`N(E,r) ≤ C r^(-s)` for all sufficiently small positive radii and some finite positive `C`.
For bounded sets this agrees with the usual logarithmic `limsup` definition. The infimum of
an empty set of exponents is infinity; the empty set has dimension zero. -/
def upperParabolicBoxDimension (E : Set SpaceTime) : ℝ≥0∞ :=
  ⨅ (s : ℝ) (_ : 0 ≤ s)
    (_ : ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r < r₀ →
        (parabolicCoveringNumber E r.toNNReal).toENNReal ≤
          ENNReal.ofReal (C * r ^ (-s))), ENNReal.ofReal s


open Finset


/-- `logIterate n x` applies the real logarithm successively `n` times to `x`.
The zero-th iterate is `x`. Real logarithm uses Mathlib's total extension. -/
def logIterate : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => Real.log (logIterate n x)

/-- Radius times the product of the squares of the first `k` successive logarithms,
extended using `max 1` in each factor. Zero diameter has value zero and infinite diameter
has infinite value. For `k = 0` this is the ordinary linear gauge. -/
def iteratedLogGauge (k : ℕ) (d : ℝ≥0∞) : ℝ≥0∞ :=
  if d = ∞ then ∞ else
    ENNReal.ofReal (d.toReal *
      ∏ i ∈ range k, (max 1 (logIterate (i + 1) (1 / d.toReal))) ^ 2)

/-- Hausdorff measure for the finite successive logarithmic gauge family in the
parabolic metric, applied to the lifted set of ordinary space-time coordinates. -/
def iteratedLogHausdorffMeasure (k : ℕ) (E : Set SpaceTime) : ℝ≥0∞ :=
  (MeasureTheory.Measure.mkMetric (iteratedLogGauge k) :
    MeasureTheory.Measure ParabolicSpaceTime) (toParabolic '' E)

end FluidSingularSets
