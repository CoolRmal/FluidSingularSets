-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesNonlinearPressure
public import FluidSingularSets.LocalHarmonicDerivatives

/-!
# Genuine pressure Poisson identities

The actual variational pressure solves its literal scalar Poisson equation
against every compact smooth test. The genuine nonlinear tensor supplies the
quadratic source. The actual weak gradient of a divergence-free velocity
supplies a harmonic viscous pressure.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The genuine variational pressure gives the actual Laplacian pairing. -/
theorem unitBallStokesPressure_laplacian_pairing
    (F : StokesEnergyForce (vec3Ball 0 1)) (ψ : WeakTestFunction (vec3Ball 0 1)) :
    Integrable (fun x ↦ (unitBallStokesPressure F :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x * spatialLaplacian ψ.toFun x)
      (volume.restrict (vec3Ball 0 1)) ∧
    (∫ x in vec3Ball 0 1, (unitBallStokesPressure F :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x * spatialLaplacian ψ.toFun x) =
        -F (stokesEnergyTest (stokesScalarGradientTest ψ)) := by
  obtain ⟨hi, hp⟩ := unitBallStokesPressure_test F (stokesScalarGradientTest ψ)
  change Integrable (fun x ↦ (unitBallStokesPressure F :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x * spatialLaplacian ψ.toFun x)
      (volume.restrict (vec3Ball 0 1)) at hi
  change inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace (vec3Ball 0 1))
      (stokesEnergyTest (stokesScalarGradientTest ψ)) -
      (∫ x in vec3Ball 0 1, (unitBallStokesPressure F :
        Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x * spatialLaplacian ψ.toFun x) =
          F (stokesEnergyTest (stokesScalarGradientTest ψ)) at hp
  rw [stokesEnergySolution_inner_gradientTest] at hp
  exact ⟨hi, by linarith⟩

/-- The constructed tensor pressure has the literal distributional quadratic source. -/
theorem unitBallTensorPressure_poisson (T : StokesGradientL2 (vec3Ball 0 1))
    (ψ : WeakTestFunction (vec3Ball 0 1)) :
    Integrable (fun x ↦ ∑ ij : Fin 3 × Fin 3,
      T x ij * mixedSecond ψ.toFun ij.1 ij.2 x) (volume.restrict (vec3Ball 0 1)) ∧
    (∫ x in vec3Ball 0 1, (unitBallStokesPressure (stokesTensorForce T) :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x * spatialLaplacian ψ.toFun x) =
        -(∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
          T x ij * mixedSecond ψ.toFun ij.1 ij.2 x) := by
  obtain ⟨hi, hp⟩ := stokesTensorForce_compactTest T (stokesScalarGradientTest ψ)
  change Integrable (fun x ↦ ∑ ij : Fin 3 × Fin 3,
    T x ij * mixedSecond ψ.toFun ij.1 ij.2 x) (volume.restrict (vec3Ball 0 1)) at hi
  change stokesTensorForce T (stokesEnergyTest (stokesScalarGradientTest ψ)) =
    ∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
      T x ij * mixedSecond ψ.toFun ij.1 ij.2 x at hp
  exact ⟨hi, (unitBallStokesPressure_laplacian_pairing _ ψ).2.trans
    (congrArg Neg.neg hp)⟩

/-- The actual velocity product is the source of the genuine nonlinear pressure. -/
theorem unitBallNonlinearPressure_poisson (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict (vec3Ball 0 1)))
    (ψ : WeakTestFunction (vec3Ball 0 1)) :
    Integrable (fun x ↦ ∑ ij : Fin 3 × Fin 3,
      (u x ij.1 * u x ij.2) * mixedSecond ψ.toFun ij.1 ij.2 x)
        (volume.restrict (vec3Ball 0 1)) ∧
    (∫ x in vec3Ball 0 1, (unitBallNonlinearPressure u hu :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x * spatialLaplacian ψ.toFun x) =
        -(∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
          (u x ij.1 * u x ij.2) * mixedSecond ψ.toFun ij.1 ij.2 x) := by
  obtain ⟨hi, hp⟩ := stokesConvectiveTensorL2_compactTest u hu (stokesScalarGradientTest ψ)
  change Integrable (fun x ↦ ∑ ij : Fin 3 × Fin 3,
    (u x ij.1 * u x ij.2) * mixedSecond ψ.toFun ij.1 ij.2 x)
      (volume.restrict (vec3Ball 0 1)) at hi
  change stokesTensorForce (stokesConvectiveTensorL2 u hu)
      (stokesEnergyTest (stokesScalarGradientTest ψ)) =
    ∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
      (u x ij.1 * u x ij.2) * mixedSecond ψ.toFun ij.1 ij.2 x at hp
  exact ⟨hi, (unitBallStokesPressure_laplacian_pairing _ ψ).2.trans
    (congrArg Neg.neg hp)⟩

private theorem weakTest_mul_memLp_two {U : Set Vec3} {f : Vec3 → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (ψ : WeakTestFunction U) :
    Integrable (fun x ↦ f x * ψ x) (volume.restrict U) := by
  have hψ : MemLp ψ.toFun 2 (volume.restrict U) :=
    (ψ.contDiff.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport).mono_measure
      Measure.restrict_le_self
  exact hf.integrable_mul hψ

/-- Actual weak derivatives and weak divergence make the Hessian pairing zero. -/
theorem weakGradient_hessian_pairing_zero {U : Set Vec3}
    (u : Vec3 → Vec3) (D : Vec3 → Fin 3 → Vec3)
    (hu : MemLp u 2 (volume.restrict U)) (hD : MemLp D 2 (volume.restrict U))
    (hgrad : ∀ i : Fin 3, HasWeakGradientOn U (fun x ↦ u x i) (fun x ↦ D x i))
    (hdiv : ∀ ψ : WeakTestFunction U,
      (∫ x in U, ∑ i : Fin 3, u x i * spatialDeriv ψ.toFun i x) = 0)
    (ψ : WeakTestFunction U) :
    (∫ x in U, ∑ ij : Fin 3 × Fin 3,
      D x ij.2 ij.1 * mixedSecond ψ.toFun ij.1 ij.2 x) = 0 := by
  let A : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j x ↦
    u x i * spatialDeriv (mixedSecond ψ.toFun j i) j x
  let B : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j x ↦
    D x i j * mixedSecond ψ.toFun j i x
  have hA (i j : Fin 3) : Integrable (A i j) (volume.restrict U) :=
    weakTest_mul_memLp_two (memLp_pi_iff.mp hu i)
      (stokesWeakTestDerivative (stokesWeakTestDerivative (stokesWeakTestDerivative ψ i) j) j)
  have hB (i j : Fin 3) : Integrable (B i j) (volume.restrict U) :=
    weakTest_mul_memLp_two (memLp_pi_iff.mp (memLp_pi_iff.mp hD i) j)
      (stokesWeakTestDerivative (stokesWeakTestDerivative ψ i) j)
  have hp (i j : Fin 3) : (∫ x in U, B i j x) = -(∫ x in U, A i j x) := by
    let η := stokesWeakTestDerivative (stokesWeakTestDerivative ψ i) j
    have hw := hgrad i j η.toFun η.contDiff η.hasCompactSupport η.tsupport_subset
    change (∫ x in U, A i j x) = -(∫ x in U, B i j x) at hw
    linarith
  have halg (x : Vec3) : (∑ i : Fin 3, ∑ j : Fin 3, A i j x) =
      ∑ i : Fin 3, u x i * spatialDeriv (spatialLaplacian ψ.toFun) i x := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum]
    change u x i * spatialLaplacian (spatialDeriv ψ.toFun i) x = _
    rw [spatialLaplacian_spatialDeriv_commute ψ.contDiff]
  calc
    _ = ∑ j : Fin 3, ∑ i : Fin 3, ∫ x in U, B i j x := by
      rw [integral_finsetSum Finset.univ (fun ij _ ↦ hB ij.2 ij.1), Fintype.sum_prod_type]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x in U, B i j x := Finset.sum_comm
    _ = -(∑ i : Fin 3, ∑ j : Fin 3, ∫ x in U, A i j x) := by
      simp_rw [hp, Finset.sum_neg_distrib]
    _ = -(∫ x in U, ∑ i : Fin 3, ∑ j : Fin 3, A i j x) := by
      congr 1
      rw [integral_finsetSum Finset.univ (fun i _ ↦
        integrable_finsetSum _ fun j _ ↦ hA i j)]
      simp_rw [integral_finsetSum Finset.univ (fun j _ ↦ hA _ j)]
    _ = -(∫ x in U, ∑ i : Fin 3,
        u x i * spatialDeriv (spatialLaplacian ψ.toFun) i x) := by
      congr 1
      exact integral_congr_ae (ae_of_all _ halg)
    _ = 0 := by
      have hz := hdiv (stokesWeakTestLaplacian ψ)
      change (∫ x in U, ∑ i : Fin 3,
        u x i * spatialDeriv (spatialLaplacian ψ.toFun) i x) = 0 at hz
      exact neg_eq_zero.mpr hz

/-- The actual viscous source of a weakly divergence-free velocity gives a harmonic pressure. -/
theorem unitBallRawViscousPressure_weaklyHarmonic
    (u : Vec3 → Vec3) (D : Vec3 → Fin 3 → Vec3)
    (hu : MemLp u 2 (volume.restrict (vec3Ball 0 1)))
    (hD : MemLp D 2 (volume.restrict (vec3Ball 0 1)))
    (hgrad : ∀ i : Fin 3, HasWeakGradientOn (vec3Ball 0 1)
      (fun x ↦ u x i) (fun x ↦ D x i))
    (hdiv : ∀ ψ : WeakTestFunction (vec3Ball 0 1),
      (∫ x in vec3Ball 0 1, ∑ i : Fin 3, u x i * spatialDeriv ψ.toFun i x) = 0) :
    WeaklyHarmonicOn (vec3Ball 0 1) (unitBallRawViscousPressure D hD :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) := by
  intro ψ hψ hcompact hsub
  let φ : WeakTestFunction (vec3Ball 0 1) := ⟨ψ, hψ, hcompact, hsub⟩
  have hp := (unitBallTensorPressure_poisson (-stokesRawGradientL2 D hD) φ).2
  have hae : (fun x ↦ ∑ ij : Fin 3 × Fin 3,
      (-stokesRawGradientL2 D hD) x ij * mixedSecond ψ ij.1 ij.2 x) =ᵐ[
        volume.restrict (vec3Ball 0 1)]
      (fun x ↦ -(∑ ij : Fin 3 × Fin 3, D x ij.2 ij.1 * mixedSecond ψ ij.1 ij.2 x)) := by
    filter_upwards [Lp.coeFn_neg (stokesRawGradientL2 D hD),
      (stokesRawGradientMatrix_memLp D hD).coeFn_toLp] with x hx hy
    change stokesRawGradientL2 D hD x = stokesRawGradientMatrix D x at hy
    rw [hx]
    change (∑ ij : Fin 3 × Fin 3,
      (-(stokesRawGradientL2 D hD x)) ij * mixedSecond ψ ij.1 ij.2 x) = _
    rw [hy]
    simp only [PiLp.neg_apply, neg_mul, Finset.sum_neg_distrib, stokesRawGradientMatrix]
  have hzero := weakGradient_hessian_pairing_zero u D hu hD hgrad hdiv φ
  rw [integral_congr_ae hae, integral_neg, hzero, neg_zero, neg_zero] at hp
  exact hp

/-- Actual equal distributional Poisson sources have a genuinely harmonic difference. -/
theorem weaklyHarmonicOn_sub_of_laplacian_pairings_eq {U : Set Vec3}
    {p q : Vec3 → ℝ} (hp : MemLp p 2 (volume.restrict U))
    (hq : MemLp q 2 (volume.restrict U))
    (heq : ∀ ψ : WeakTestFunction U,
      (∫ x in U, p x * spatialLaplacian ψ.toFun x) =
        ∫ x in U, q x * spatialLaplacian ψ.toFun x) :
    WeaklyHarmonicOn U (p - q) := by
  intro ψ hψ hcompact hsub
  let φ : WeakTestFunction U := ⟨ψ, hψ, hcompact, hsub⟩
  have hip := weakTest_mul_memLp_two hp (stokesWeakTestLaplacian φ)
  have hiq := weakTest_mul_memLp_two hq (stokesWeakTestLaplacian φ)
  have he := heq φ
  change (∫ x in U, p x * spatialLaplacian ψ x) =
    ∫ x in U, q x * spatialLaplacian ψ x at he
  calc
    _ = ∫ x in U, p x * spatialLaplacian ψ x - q x * spatialLaplacian ψ x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by simp only [Pi.sub_apply]; ring
    _ = (∫ x in U, p x * spatialLaplacian ψ x) -
        (∫ x in U, q x * spatialLaplacian ψ x) := integral_sub hip hiq
    _ = 0 := sub_eq_zero.mpr he

end FluidSingularSets
