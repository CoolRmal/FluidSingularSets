-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SmoothProjectedDivergence

/-!
# Actual momentum testing with a smooth spatial correction

The product of a genuine smooth vector correction with an actual compact scalar
test is an admissible vector momentum test. Its density is exactly the literal
harmonic-correction polynomial, with its true spatial and time derivatives.
The original suitable momentum equation therefore annihilates that polynomial.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal vector correction test. -/
def smoothCorrectionTest (H : Vec3 × ℝ → Vec3) (ψ : Vec3 × ℝ → ℝ)
    (z : Vec3 × ℝ) : Vec3 := fun i ↦ H z i * ψ z

/-- The actual smooth correction test is supported on the genuine scalar test. -/
theorem smoothCorrectionTest_tsupport
    (H : Vec3 × ℝ → Vec3) (ψ : Vec3 × ℝ → ℝ) :
    tsupport (smoothCorrectionTest H ψ) ⊆ tsupport ψ := by
  apply closure_minimal
  · intro z hz
    apply subset_tsupport ψ
    intro hψ
    apply hz
    funext i
    simp [smoothCorrectionTest, hψ]
  · exact isClosed_tsupport ψ

/-- Multiplication by a genuine smooth correction gives an admissible vector test. -/
theorem smoothCorrectionTest_mem
    {Ω : Set Vec3} {I : Set ℝ} {H : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    smoothCorrectionTest H ψ ∈ spaceTimeTestFunction (V := Vec3) Ω I := by
  refine ⟨?_, ?_, (smoothCorrectionTest_tsupport H ψ).trans hψ.2.2⟩
  · apply contDiff_pi.mpr
    intro i
    exact ((contDiff_apply ℝ ℝ i).comp hH).mul hψ.1
  · apply HasCompactSupport.of_support_subset_isCompact hψ.2.1.isCompact
    exact (subset_tsupport _).trans (smoothCorrectionTest_tsupport H ψ)

/-- The actual time product rule of the correction test. -/
theorem smoothCorrectionTest_timePartial
    {H : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin 3) (z : Vec3 × ℝ) :
    timePartial (fun w ↦ smoothCorrectionTest H ψ w i) z =
      timePartial (fun w ↦ H w i) z * ψ z + H z i * timePartial ψ z :=
  CKN.Core.Step3.timePartial_mul_full ((contDiff_apply ℝ ℝ i).comp hH) hψ z

/-- The actual spatial product rule of the correction test. -/
theorem smoothCorrectionTest_spatialPartial
    {H : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (fun w ↦ smoothCorrectionTest H ψ w i) j z =
      spatialPartial (fun w ↦ H w i) j z * ψ z + H z i * spatialPartial ψ j z :=
  CKN.Core.Step3.spatialPartial_mul_full ((contDiff_apply ℝ ℝ i).comp hH) hψ j z

/-- The genuine correction-test momentum density is its exact tested polynomial. -/
theorem smoothCorrectionTest_momentum_density
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) {H : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : Vec3 × ℝ) :
    frameMomentumDensity u Du p (fun _ ↦ 0) (smoothCorrectionTest H ψ) z =
      harmonicCorrectionMomentumPolynomial (u z) (H z)
        (fun i ↦ timePartial (fun w ↦ H w i) z) (fun j ↦ spatialPartial ψ j z)
        (Du z) (fun i j ↦ spatialPartial (fun w ↦ H w i) j z)
        (p z) (ψ z) (timePartial ψ z) := by
  unfold frameMomentumDensity
  simp only [smoothCorrectionTest_timePartial hH hψ,
    smoothCorrectionTest_spatialPartial hH hψ]
  simp only [harmonicCorrectionMomentumPolynomial, smoothCorrectionTest, Pi.zero_apply,
    Fin.sum_univ_three]
  ring

/-- Actual unforced suitable momentum annihilates the genuine smooth-correction polynomial. -/
theorem suitable_smooth_correction_momentum_pairing
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {H : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    Integrable (fun z : Vec3 × ℝ ↦
      harmonicCorrectionMomentumPolynomial (u z) (H z)
        (fun i ↦ timePartial (fun w ↦ H w i) z) (fun j ↦ spatialPartial ψ j z)
        (Du z) (fun i j ↦ spatialPartial (fun w ↦ H w i) j z)
        (p z) (ψ z) (timePartial ψ z)) volume ∧
      (∫ z : Vec3 × ℝ,
        harmonicCorrectionMomentumPolynomial (u z) (H z)
          (fun i ↦ timePartial (fun w ↦ H w i) z) (fun j ↦ spatialPartial ψ j z)
          (Du z) (fun i j ↦ spatialPartial (fun w ↦ H w i) j z)
          (p z) (ψ z) (timePartial ψ z)) = 0 := by
  have hw := suitable_global_momentum hsol (smoothCorrectionTest_mem hH hψ)
  have hae := ae_of_all (volume : Measure (Vec3 × ℝ))
    (smoothCorrectionTest_momentum_density u Du p hH hψ.1)
  exact ⟨hw.1.congr hae, (integral_congr_ae hae).symm.trans hw.2⟩

end FluidSingularSets
