-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallNativeEnergyRhs

/-!
# Literal native error families for projected energy

The actual right hand side, multiplied by a backward cutoff, splits into its
five native signed error families. The derivative remains that of the original
compact time test; the backward cutoff derivative belongs on the energy side.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual signed time error, retaining only the original test derivative. -/
def fullBallNativeTimeError
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) (θ χ : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2 *
    φ z.1 ^ 6 * deriv θ z.2 * χ z.2

/-- The actual signed spatial Laplacian error. -/
def fullBallNativeLaplacianError
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) (η : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2 *
    spatialLaplacian (fun x ↦ φ x ^ 6) z.1 * η z.2

/-- The actual signed convection flux with its literal sixth-cutoff gradient. -/
def fullBallNativeConvectionError
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) (η : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  η z.2 * vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2 *
    ∑ j : Fin 3, u z j * spatialDeriv (fun x ↦ φ x ^ 6) j z.1

/-- The actual mean-canceling projected pressure pairing. -/
def fullBallNativePressureError
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) (η : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  (p z - fullBallProjectedMomentumPressure u D p z.2 z.1) *
    fullBallProjectedPressureTest u D p a b c (fun x ↦ φ x ^ 6) η z

/-- The actual nine signed harmonic Hessian cross terms. -/
def fullBallNativeHarmonicError
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) (η : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, η z.2 * φ z.1 ^ 6 * u z j *
    fullBallProjectedHarmonicDerivativeAmbient u D p a b c z i j *
      fullBallProjectedVelocityAmbient u D p a b c z i

/-- The genuine native cutoff RHS is exactly the five signed error families. -/
theorem fullBallNativeProjectedRhsDensity_mul_cutoff_eq
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (χ : ℝ → ℝ)
    (z : ParabolicPoint) (hz : z.1 ∈ fullBallCompactInterior ρ) :
    fullBallNativeProjectedRhsDensity u D p a b c (fullBallSeparatedCutoffTest φ θ) z *
        χ z.2 =
      fullBallNativeTimeError u D p a b c φ θ χ z +
      fullBallNativeLaplacianError u D p a b c φ (fun t ↦ θ t * χ t) z +
      fullBallNativeConvectionError u D p a b c φ (fun t ↦ θ t * χ t) z +
      2 * fullBallNativePressureError u D p a b c φ (fun t ↦ θ t * χ t) z +
      2 * fullBallNativeHarmonicError u D p a b c φ (fun t ↦ θ t * χ t) z := by
  have he := fullBallProjectedRhsDensity_separated_cutoff ρ u D p a b c hφ hθ
    ((⟨z.1, hz⟩, z.2) : fullBallCompactInterior ρ × ℝ)
  change fullBallNativeProjectedRhsDensity u D p a b c
    (fullBallSeparatedCutoffTest φ θ) z = _ at he
  rw [he]
  simp only [fullBallNativeTimeError, fullBallNativeLaplacianError,
    fullBallNativeConvectionError, fullBallNativePressureError,
    fullBallNativeHarmonicError, fullBallProjectedPressureTest, Fin.sum_univ_three, Prod.mk.eta]
  ring

end FluidSingularSets
