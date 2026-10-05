-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallStokesPressure
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Actual convective and viscous Stokes pressures

Spatial `L⁴` velocity data produce the true `L²` convective tensor. The already
constructed bounded mean-zero Stokes pressure operator yields its nonlinear
pressure and the pressure of the actual negative velocity gradient. The signs
correspond respectively to `-div (u ⊗ u)` and `+div Du`. Their quantitative
bounds and literal compact-test Stokes equations use only the genuine input data.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The true rank-one tensor in the Hilbert matrix norm, with derivative index first. -/
def stokesOuterProduct (a b : Vec3) : StokesGradientMatrix :=
  WithLp.toLp 2 (fun ij ↦ a ij.1 * b ij.2)

@[simp]
theorem stokesOuterProduct_apply (a b : Vec3) (ij : Fin 3 × Fin 3) :
    stokesOuterProduct a b ij = a ij.1 * b ij.2 := rfl

/-- The actual tensor operation is continuous. -/
theorem stokesOuterProduct_continuous : Continuous stokesOuterProduct.uncurry := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin 3 ↦ ℝ)).comp
  apply continuous_pi
  intro ij
  exact ((continuous_apply ij.1).comp continuous_fst).mul
    ((continuous_apply ij.2).comp continuous_snd)

/-- Sup-norm vector data control the true nine-component Hilbert tensor norm. -/
theorem stokesOuterProduct_norm_le (a b : Vec3) :
    ‖stokesOuterProduct a b‖ ≤ 3 * ‖a‖ * ‖b‖ := by
  have hsq : ‖stokesOuterProduct a b‖ ^ 2 ≤ 9 * (‖a‖ * ‖b‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ij : Fin 3 × Fin 3, (‖a‖ * ‖b‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro ij _
        rw [stokesOuterProduct_apply, norm_mul]
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul (norm_le_pi_norm a ij.1) (norm_le_pi_norm b ij.2)
            (norm_nonneg _) (norm_nonneg _)) 2
      _ = _ := by norm_num
  apply le_of_sq_le_sq _ (by positivity)
  convert hsq using 1
  ring

private theorem stokesHolderFourFourTwo : ENNReal.HolderTriple 4 4 2 := by
  have h : Real.HolderTriple 4 4 2 := by
    rw [Real.holderTriple_iff]
    norm_num
  simpa only [ENNReal.ofReal_ofNat] using h.ennrealOfReal

/-- Actual spatial `L⁴` velocity gives a genuine `L²` convective tensor. -/
theorem stokesConvectiveTensor_memLp {U : Set Vec3} (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict U)) :
    MemLp (fun x ↦ stokesOuterProduct (u x) (u x)) 2 (volume.restrict U) := by
  let : ENNReal.HolderTriple 4 4 2 := stokesHolderFourFourTwo
  apply hu.of_bilin stokesOuterProduct 3 hu stokesOuterProduct_continuous
  exact ae_of_all _ (fun x ↦ by exact_mod_cast stokesOuterProduct_norm_le (u x) (u x))

/-- The actual convective tensor as a genuine spatial `L²` equivalence class. -/
def stokesConvectiveTensorL2 {U : Set Vec3} (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict U)) : StokesGradientL2 U :=
  (stokesConvectiveTensor_memLp u hu).toLp (fun x ↦ stokesOuterProduct (u x) (u x))

/-- Genuine Hölder control of the actual convective tensor seminorm. -/
theorem stokesConvectiveTensor_eLpNorm_le {U : Set Vec3} (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict U)) :
    eLpNorm (fun x ↦ stokesOuterProduct (u x) (u x)) 2 (volume.restrict U) ≤
      3 * eLpNorm u 4 (volume.restrict U) ^ 2 := by
  let : ENNReal.HolderTriple 4 4 2 := stokesHolderFourFourTwo
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
    (p := 4) (q := 4) (r := 2) stokesOuterProduct 3 stokesOuterProduct_continuous
    hu.aestronglyMeasurable hu.aestronglyMeasurable
    (ae_of_all _ (fun x ↦ stokesOuterProduct_norm_le (u x) (u x)))
  simpa only [ENNReal.coe_ofNat, pow_two, mul_assoc] using h

/-- The actual convective tensor has a finite quantitative spatial `L²` norm. -/
theorem stokesConvectiveTensorL2_norm_le {U : Set Vec3} (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict U)) :
    ‖stokesConvectiveTensorL2 u hu‖ ≤
      3 * (eLpNorm u 4 (volume.restrict U)).toReal ^ 2 := by
  rw [stokesConvectiveTensorL2, Lp.norm_toLp]
  have h := ENNReal.toReal_mono (by finiteness [hu]) (stokesConvectiveTensor_eLpNorm_le u hu)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_pow] using h

/-- Actual tensor force pairing on every genuine compact smooth vector test. -/
theorem stokesTensorForce_compactTest {U : Set Vec3} (T : StokesGradientL2 U)
    (φ : StokesVectorTest U) :
    Integrable (fun x ↦ ∑ ij : Fin 3 × Fin 3,
      T x ij * (φ ij.2).partialDeriv ij.1 x) (volume.restrict U) ∧
    stokesTensorForce T (stokesEnergyTest φ) =
      ∫ x in U, ∑ ij : Fin 3 × Fin 3, T x ij * (φ ij.2).partialDeriv ij.1 x := by
  have hae : (fun x ↦ inner ℝ (T x) (stokesTestGradientL2 φ x))
      =ᵐ[volume.restrict U] (fun x ↦ ∑ ij : Fin 3 × Fin 3,
        T x ij * (φ ij.2).partialDeriv ij.1 x) := by
    filter_upwards [(stokesTestGradient_memLp φ).coeFn_toLp] with x hx
    change stokesTestGradientL2 φ x = stokesTestGradient φ x at hx
    rw [hx, PiLp.inner_apply]
    simp only [Real.inner_apply]
    rfl
  refine ⟨(L2.integrable_inner (𝕜 := ℝ) T (stokesTestGradientL2 φ)).congr hae, ?_⟩
  change inner ℝ T (stokesTestGradientL2 φ) = _
  rw [L2.inner_def, integral_congr_ae hae]

/-- The convective tensor pairs with tests through the actual velocity product. -/
theorem stokesConvectiveTensorL2_compactTest {U : Set Vec3} (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict U)) (φ : StokesVectorTest U) :
    Integrable (fun x ↦ ∑ ij : Fin 3 × Fin 3,
      (u x ij.1 * u x ij.2) * (φ ij.2).partialDeriv ij.1 x) (volume.restrict U) ∧
    stokesTensorForce (stokesConvectiveTensorL2 u hu) (stokesEnergyTest φ) =
      ∫ x in U, ∑ ij : Fin 3 × Fin 3,
        (u x ij.1 * u x ij.2) * (φ ij.2).partialDeriv ij.1 x := by
  have hae : (fun x ↦ ∑ ij : Fin 3 × Fin 3,
      stokesConvectiveTensorL2 u hu x ij * (φ ij.2).partialDeriv ij.1 x)
      =ᵐ[volume.restrict U] (fun x ↦ ∑ ij : Fin 3 × Fin 3,
        (u x ij.1 * u x ij.2) * (φ ij.2).partialDeriv ij.1 x) := by
    filter_upwards [(stokesConvectiveTensor_memLp u hu).coeFn_toLp] with x hx
    change stokesConvectiveTensorL2 u hu x = stokesOuterProduct (u x) (u x) at hx
    rw [hx]
    rfl
  obtain ⟨hprod, hpair⟩ := stokesTensorForce_compactTest (stokesConvectiveTensorL2 u hu) φ
  exact ⟨hprod.congr hae, hpair.trans (integral_congr_ae hae)⟩

/-- The actual mean-zero nonlinear pressure, with force `-div (u ⊗ u)`. -/
def unitBallNonlinearPressure (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict (vec3Ball 0 1))) : unitBallMeanZeroL2 :=
  unitBallStokesPressure (stokesTensorForce (stokesConvectiveTensorL2 u hu))

/-- The actual mean-zero viscous pressure, with force `+div D`. -/
def unitBallViscousPressure (D : StokesGradientL2 (vec3Ball 0 1)) : unitBallMeanZeroL2 :=
  unitBallStokesPressure (stokesTensorForce (-D))

/-- The actual CKN derivative array, transposed to the derivative-first Hilbert convention. -/
def stokesRawGradientMatrix (D : Vec3 → Fin 3 → Vec3) (x : Vec3) : StokesGradientMatrix :=
  WithLp.toLp 2 (fun ij ↦ D x ij.2 ij.1)

/-- The raw CKN convention converts exactly to the true compact-test gradient. -/
theorem stokesRawGradientMatrix_test {U : Set Vec3} (φ : StokesVectorTest U) (x : Vec3) :
    stokesRawGradientMatrix (fun y j i ↦ (φ j).partialDeriv i y) x =
      stokesTestGradient φ x := rfl

/-- Genuine square-integrable derivative data give the actual Hilbert matrix class. -/
theorem stokesRawGradientMatrix_memLp {U : Set Vec3} (D : Vec3 → Fin 3 → Vec3)
    (hD : MemLp D 2 (volume.restrict U)) :
    MemLp (stokesRawGradientMatrix D) 2 (volume.restrict U) := by
  apply MemLp.of_eval_piLp
  intro ij
  exact memLp_pi_iff.mp (memLp_pi_iff.mp hD ij.2) ij.1

/-- The actual raw velocity derivative array as a genuine Hilbert `L²` class. -/
def stokesRawGradientL2 {U : Set Vec3} (D : Vec3 → Fin 3 → Vec3)
    (hD : MemLp D 2 (volume.restrict U)) : StokesGradientL2 U :=
  (stokesRawGradientMatrix_memLp D hD).toLp (stokesRawGradientMatrix D)

/-- The raw derivative array controls its genuine Hilbert matrix norm. -/
theorem stokesRawGradientMatrix_norm_le (D : Vec3 → Fin 3 → Vec3) (x : Vec3) :
    ‖stokesRawGradientMatrix D x‖ ≤ 3 * ‖D x‖ := by
  have hsq : ‖stokesRawGradientMatrix D x‖ ^ 2 ≤ 9 * ‖D x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ij : Fin 3 × Fin 3, ‖D x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro ij _
        exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm (D x ij.2) ij.1).trans
          (norm_le_pi_norm (D x) ij.2)) 2
      _ = _ := by norm_num
  apply le_of_sq_le_sq _ (by positivity)
  convert hsq using 1
  ring

/-- Quantitative genuine conversion from raw derivative data to Hilbert `L²`. -/
theorem stokesRawGradientL2_norm_le {U : Set Vec3} (D : Vec3 → Fin 3 → Vec3)
    (hD : MemLp D 2 (volume.restrict U)) :
    ‖stokesRawGradientL2 D hD‖ ≤ 3 * (eLpNorm D 2 (volume.restrict U)).toReal := by
  rw [stokesRawGradientL2, Lp.norm_toLp]
  have h : eLpNorm (stokesRawGradientMatrix D) 2 (volume.restrict U) ≤
      (3 : ℝ≥0) • eLpNorm D 2 (volume.restrict U) := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (stokesRawGradientMatrix_memLp D hD).aestronglyMeasurable
    exact ae_of_all _ (fun x ↦ by exact_mod_cast stokesRawGradientMatrix_norm_le D x)
  have ht := ENNReal.toReal_mono (by
    simp only [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_ofNat]
    exact ENNReal.mul_ne_top (by norm_num) hD.eLpNorm_ne_top) h
  simpa only [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_ofNat,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat] using ht

/-- The actual viscous pressure of a genuine raw square-integrable velocity derivative. -/
def unitBallRawViscousPressure (D : Vec3 → Fin 3 → Vec3)
    (hD : MemLp D 2 (volume.restrict (vec3Ball 0 1))) : unitBallMeanZeroL2 :=
  unitBallViscousPressure (stokesRawGradientL2 D hD)

/-- The nonlinear pressure is controlled by the actual convective tensor norm. -/
theorem unitBallNonlinearPressure_norm_tensor (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict (vec3Ball 0 1))) :
    ‖unitBallNonlinearPressure u hu‖ ≤ 4 * ‖stokesConvectiveTensorL2 u hu‖ :=
  (unitBallStokesPressure_norm _).trans
    (mul_le_mul_of_nonneg_left (stokesTensorForce_norm_le _) (by norm_num))

/-- The nonlinear pressure has the genuine quadratic spatial `L⁴` bound. -/
theorem unitBallNonlinearPressure_norm (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict (vec3Ball 0 1))) :
    ‖unitBallNonlinearPressure u hu‖ ≤
      12 * (eLpNorm u 4 (volume.restrict (vec3Ball 0 1))).toReal ^ 2 := by
  calc
    _ ≤ 4 * ‖stokesConvectiveTensorL2 u hu‖ := unitBallNonlinearPressure_norm_tensor u hu
    _ ≤ 4 * (3 * (eLpNorm u 4 (volume.restrict (vec3Ball 0 1))).toReal ^ 2) :=
      mul_le_mul_of_nonneg_left (stokesConvectiveTensorL2_norm_le u hu) (by norm_num)
    _ = _ := by ring

/-- The viscous pressure is controlled by the actual spatial gradient norm. -/
theorem unitBallViscousPressure_norm (D : StokesGradientL2 (vec3Ball 0 1)) :
    ‖unitBallViscousPressure D‖ ≤ 4 * ‖D‖ := by
  have h := (unitBallStokesPressure_norm (stokesTensorForce (-D))).trans
    (mul_le_mul_of_nonneg_left (stokesTensorForce_norm_le (-D)) (by norm_num))
  simpa only [unitBallViscousPressure, norm_neg] using h

/-- The genuine viscous pressure bound in the original CKN derivative-array norm. -/
theorem unitBallRawViscousPressure_norm (D : Vec3 → Fin 3 → Vec3)
    (hD : MemLp D 2 (volume.restrict (vec3Ball 0 1))) :
    ‖unitBallRawViscousPressure D hD‖ ≤
      12 * (eLpNorm D 2 (volume.restrict (vec3Ball 0 1))).toReal := by
  calc
    _ ≤ 4 * ‖stokesRawGradientL2 D hD‖ := unitBallViscousPressure_norm _
    _ ≤ 4 * (3 * (eLpNorm D 2 (volume.restrict (vec3Ball 0 1))).toReal) :=
      mul_le_mul_of_nonneg_left (stokesRawGradientL2_norm_le D hD) (by norm_num)
    _ = _ := by ring

/-- The nonlinear pressure has literal zero mean on the actual unit ball. -/
theorem unitBallNonlinearPressure_integral_zero (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict (vec3Ball 0 1))) :
    (∫ x in vec3Ball 0 1, (unitBallNonlinearPressure u hu :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x) = 0 :=
  unitBallStokesPressure_integral_zero _

/-- The viscous pressure has literal zero mean on the actual unit ball. -/
theorem unitBallViscousPressure_integral_zero (D : StokesGradientL2 (vec3Ball 0 1)) :
    (∫ x in vec3Ball 0 1, (unitBallViscousPressure D :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x) = 0 :=
  unitBallStokesPressure_integral_zero _

/-- The recovered tensor-source Stokes problem has a fully literal weak test equation. -/
theorem unitBallTensorPressure_compactTest (T : StokesGradientL2 (vec3Ball 0 1))
    (φ : StokesVectorTest (vec3Ball 0 1)) :
    Integrable (fun x ↦ (unitBallStokesPressure (stokesTensorForce T) :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x * ∑ i : Fin 3, (φ i).partialDeriv i x)
      (volume.restrict (vec3Ball 0 1)) ∧
    (∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
      (stokesEnergySolution (stokesTensorForce T)).val.val x ij *
        (φ ij.2).partialDeriv ij.1 x) -
      (∫ x in vec3Ball 0 1, (unitBallStokesPressure (stokesTensorForce T) :
        Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x *
          ∑ i : Fin 3, (φ i).partialDeriv i x) =
      ∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
        T x ij * (φ ij.2).partialDeriv ij.1 x := by
  obtain ⟨hprod, hweak⟩ := unitBallStokesPressure_test (stokesTensorForce T) φ
  have he := (stokesTensorForce_compactTest
    (stokesEnergySolution (stokesTensorForce T)).val.val φ).2
  change inner ℝ (stokesEnergySolution (stokesTensorForce T) :
    stokesGradientEnergySpace (vec3Ball 0 1)) (stokesEnergyTest φ) = _ at he
  rw [he, (stokesTensorForce_compactTest T φ).2] at hweak
  exact ⟨hprod, hweak⟩

/-- The nonlinear pressure satisfies the actual convective weak Stokes equation. -/
theorem unitBallNonlinearPressure_compactTest (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict (vec3Ball 0 1)))
    (φ : StokesVectorTest (vec3Ball 0 1)) :
    Integrable (fun x ↦ (unitBallNonlinearPressure u hu :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x * ∑ i : Fin 3, (φ i).partialDeriv i x)
      (volume.restrict (vec3Ball 0 1)) ∧
    (∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
      (stokesEnergySolution (stokesTensorForce (stokesConvectiveTensorL2 u hu))).val.val x ij *
        (φ ij.2).partialDeriv ij.1 x) -
      (∫ x in vec3Ball 0 1, (unitBallNonlinearPressure u hu :
        Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x *
          ∑ i : Fin 3, (φ i).partialDeriv i x) =
      ∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
        (u x ij.1 * u x ij.2) * (φ ij.2).partialDeriv ij.1 x := by
  obtain ⟨hprod, hweak⟩ := unitBallTensorPressure_compactTest
    (stokesConvectiveTensorL2 u hu) φ
  have hconv := (stokesConvectiveTensorL2_compactTest u hu φ).2
  rw [← (stokesTensorForce_compactTest (stokesConvectiveTensorL2 u hu) φ).2, hconv] at hweak
  exact ⟨hprod, hweak⟩

/-- The viscous pressure satisfies the actual signed gradient-source weak Stokes equation. -/
theorem unitBallViscousPressure_compactTest (D : StokesGradientL2 (vec3Ball 0 1))
    (φ : StokesVectorTest (vec3Ball 0 1)) :
    Integrable (fun x ↦ (unitBallViscousPressure D :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x * ∑ i : Fin 3, (φ i).partialDeriv i x)
      (volume.restrict (vec3Ball 0 1)) ∧
    (∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
      (stokesEnergySolution (stokesTensorForce (-D))).val.val x ij *
        (φ ij.2).partialDeriv ij.1 x) -
      (∫ x in vec3Ball 0 1, (unitBallViscousPressure D :
        Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x *
          ∑ i : Fin 3, (φ i).partialDeriv i x) =
      -(∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
        D x ij * (φ ij.2).partialDeriv ij.1 x) := by
  obtain ⟨hprod, hweak⟩ := unitBallTensorPressure_compactTest (-D) φ
  have hneg : (∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
      (-D) x ij * (φ ij.2).partialDeriv ij.1 x) =
      -(∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
        D x ij * (φ ij.2).partialDeriv ij.1 x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_neg D] with x hx
    rw [hx]
    simp only [Pi.neg_apply, PiLp.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [hneg] at hweak
  exact ⟨hprod, hweak⟩

/-- The genuine raw-gradient pressure solves the fully literal viscous weak Stokes equation. -/
theorem unitBallRawViscousPressure_compactTest (D : Vec3 → Fin 3 → Vec3)
    (hD : MemLp D 2 (volume.restrict (vec3Ball 0 1)))
    (φ : StokesVectorTest (vec3Ball 0 1)) :
    Integrable (fun x ↦ (unitBallRawViscousPressure D hD :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x * ∑ i : Fin 3, (φ i).partialDeriv i x)
      (volume.restrict (vec3Ball 0 1)) ∧
    (∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
      (stokesEnergySolution (stokesTensorForce (-stokesRawGradientL2 D hD))).val.val x ij *
        (φ ij.2).partialDeriv ij.1 x) -
      (∫ x in vec3Ball 0 1, (unitBallRawViscousPressure D hD :
        Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x *
          ∑ i : Fin 3, (φ i).partialDeriv i x) =
      -(∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
        D x ij.2 ij.1 * (φ ij.2).partialDeriv ij.1 x) := by
  obtain ⟨hprod, hweak⟩ := unitBallViscousPressure_compactTest (stokesRawGradientL2 D hD) φ
  have heq : (∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
      stokesRawGradientL2 D hD x ij * (φ ij.2).partialDeriv ij.1 x) =
      ∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
        D x ij.2 ij.1 * (φ ij.2).partialDeriv ij.1 x := by
    apply integral_congr_ae
    filter_upwards [(stokesRawGradientMatrix_memLp D hD).coeFn_toLp] with x hx
    change stokesRawGradientL2 D hD x = stokesRawGradientMatrix D x at hx
    rw [hx]
    rfl
  rw [heq] at hweak
  exact ⟨hprod, hweak⟩

end FluidSingularSets
