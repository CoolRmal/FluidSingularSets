-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallHarmonicOperators

/-!
# Actual pressure values and Hessians on every compact interior

The true full-ball pressure representative has a quantitative value bound on
any smaller ball. Its values and its literal second derivatives define bounded
linear operators on arbitrary compact interiors.
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

local instance fullBallValuesForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance fullBallValuesForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The actual harmonic value coefficient at an arbitrary boundary margin. -/
def fullBallHarmonicValueConstant (ρ : ℝ) : ℝ :=
  weakHarmonicInteriorSupConstant * ((1 - ρ) ^ 2)⁻¹

/-- The margin-dependent value constant is nonnegative. -/
theorem fullBallHarmonicValueConstant_nonneg {ρ : ℝ} (hρ : ρ < 1) :
    0 ≤ fullBallHarmonicValueConstant ρ := by
  have h : 0 < 1 - ρ := sub_pos.mpr hρ
  exact mul_nonneg weakHarmonicInteriorSupConstant_nonneg (by positivity)

/-- True translated Weyl representatives give the value of the actual full-ball representative. -/
theorem fullBallHarmonic_representative_value_bound {h H : Vec3 → ℝ}
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) h)
    (hH : ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 1))
    (hae : h =ᵐ[volume.restrict (vec3Ball 0 1)] H)
    {ρ : ℝ} (hρ : ρ < 1) {x : Vec3} (hx : x ∈ vec3Ball 0 ρ) :
    |H x| ≤ fullBallHarmonicValueConstant ρ *
      lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) := by
  let R := 1 - ρ
  have hR : 0 < R := sub_pos.mpr hρ
  have hsub : vec3Ball x R ⊆ vec3Ball 0 1 := by
    intro y hy
    rw [mem_vec3Ball] at hx hy ⊢
    have ht := vec3EuclideanNorm_add_le (y - x) x
    rw [sub_add_cancel] at ht
    norm_num only [sub_zero] at hx ⊢
    dsimp [R] at hy
    linarith
  have hm := hmem.mono_measure (Measure.restrict_mono_set volume hsub)
  have hw := localWeaklyHarmonicOn_restrict hsub hweak
  rw [← euclideanBall_eq_vec3Ball hR] at hm hw
  obtain ⟨G, hG, hGa, hGval, _hGgrad⟩ := weakly_harmonic_interior_smooth hR hm hw
  rw [euclideanBall_eq_vec3Ball (by positivity : 0 < R / 2)] at hG hGa hGval
  have hs : vec3Ball x (R / 2) ⊆ vec3Ball 0 1 :=
    (vec3Ball_mono (by linarith : R / 2 ≤ R)).trans hsub
  have hHa : h =ᵐ[volume.restrict (vec3Ball x (R / 2))] H :=
    ae_restrict_of_ae_restrict_of_subset hs hae
  have he := Measure.eqOn_open_of_ae_eq (hHa.symm.trans hGa)
    (isOpen_vec3Ball x (R / 2)) (hH.continuousOn.mono hs) hG.continuousOn
  have hxc : x ∈ vec3Ball x (R / 2) := by
    rw [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
    positivity
  rw [he hxc]
  have hv := hGval x hxc
  rw [euclideanBall_eq_vec3Ball hR] at hv
  have hn : lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball x R)) ≤
      lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) := by
    change (eLpNorm h _ _).toReal ≤ (eLpNorm h _ _).toReal
    exact ENNReal.toReal_mono hmem.eLpNorm_ne_top
      (eLpNorm_mono_measure h (Measure.restrict_mono_set volume hsub))
  exact hv.trans (mul_le_mul_of_nonneg_left hn (fullBallHarmonicValueConstant_nonneg hρ))

/-- The true force-to-value coefficient with its genuine boundary margin. -/
def fullBallHarmonicForceValueCoefficient (ρ : ℝ) : ℝ :=
  fullBallHarmonicValueConstant ρ *
    (4 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ))

/-- The true force-to-value coefficient is nonnegative. -/
theorem fullBallHarmonicForceValueCoefficient_nonneg {ρ : ℝ} (hρ : ρ < 1) :
    0 ≤ fullBallHarmonicForceValueCoefficient ρ :=
  mul_nonneg (fullBallHarmonicValueConstant_nonneg hρ)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg ENNReal.toReal_nonneg _))

/-- The true force-to-Hessian coefficient at the prescribed boundary margin. -/
def fullBallHarmonicForceHessianCoefficient (ρ : ℝ) : ℝ :=
  3 * fullBallHarmonicHessianConstant ρ *
    (4 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ))

/-- The true Hessian coefficient is nonnegative. -/
theorem fullBallHarmonicForceHessianCoefficient_nonneg {ρ : ℝ} (hρ : ρ < 1) :
    0 ≤ fullBallHarmonicForceHessianCoefficient ρ :=
  mul_nonneg (mul_nonneg (by norm_num) (fullBallHarmonicHessianConstant_nonneg hρ))
    (mul_nonneg (by norm_num) (Real.rpow_nonneg ENNReal.toReal_nonneg _))

variable (K : Set Vec3) [CompactSpace K] (hK : K ⊆ vec3Ball 0 1)

/-- The actual continuous pressure values on a compact interior. -/
def fullBallHarmonicValueMap (F : unitBallGradientFreeForce) : C(K, ℝ) where
  toFun := fun x ↦ unitBallFullHarmonicForcePressureRepresentative F x.1
  continuous_toFun := continuousOn_iff_continuous_domRestrict.mp
    ((unitBallFullHarmonicForcePressureRepresentative_contDiff F).continuousOn.mono hK)

omit [CompactSpace K] in
/-- The actual pressure values preserve force addition. -/
theorem fullBallHarmonicValueMap_add (F G : unitBallGradientFreeForce) :
    fullBallHarmonicValueMap K hK (F + G) =
      fullBallHarmonicValueMap K hK F + fullBallHarmonicValueMap K hK G := by
  ext x
  exact unitBallFullHarmonicForcePressureRepresentative_add F G (hK x.property)

omit [CompactSpace K] in
/-- The actual pressure values preserve real force scaling. -/
theorem fullBallHarmonicValueMap_smul (c : ℝ) (F : unitBallGradientFreeForce) :
    fullBallHarmonicValueMap K hK (c • F) = c • fullBallHarmonicValueMap K hK F := by
  ext x
  exact unitBallFullHarmonicForcePressureRepresentative_smul c F (hK x.property)

/-- The genuine pressure values satisfy the actual margin-dependent force bound. -/
theorem fullBallHarmonicValueMap_norm_le {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) (F : unitBallGradientFreeForce) :
    ‖fullBallHarmonicValueMap K hK F‖ ≤ fullBallHarmonicForceValueCoefficient ρ * ‖F‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (fullBallHarmonicForceValueCoefficient_nonneg hρ) (norm_nonneg F))).mpr
  intro x
  rw [Real.norm_eq_abs]
  have hb := fullBallHarmonic_representative_value_bound
    (unitBallPressureFunction_memLp_threeHalves F.1)
    (unitBallStokesPressure_weaklyHarmonic F.1 F.property)
    (unitBallFullHarmonicForcePressureRepresentative_contDiff F)
    (unitBallFullHarmonicForcePressureRepresentative_ae F) hρ (hKρ x.property)
  apply hb.trans
  have hl := mul_le_mul_of_nonneg_left (unitBallPressureFunction_lpNorm_threeHalves_le F.1)
    (fullBallHarmonicValueConstant_nonneg hρ)
  simpa only [fullBallHarmonicForceValueCoefficient, unitBallGradientFreeForce_norm_coe,
    mul_assoc] using hl

/-- A genuine bounded linear pressure-values operator on each compact interior. -/
def fullBallHarmonicValues {ρ : ℝ} (hρ : ρ < 1) (hKρ : K ⊆ vec3Ball 0 ρ) :
    unitBallGradientFreeForce →L[ℝ] C(K, ℝ) :=
  ({ toFun := fullBallHarmonicValueMap K hK
     map_add' := fullBallHarmonicValueMap_add K hK
     map_smul' := fullBallHarmonicValueMap_smul K hK } :
       unitBallGradientFreeForce →ₗ[ℝ] C(K, ℝ)).mkContinuous
    (fullBallHarmonicForceValueCoefficient ρ) (fullBallHarmonicValueMap_norm_le K hK hρ hKρ)

/-- The literal derivative-first Hilbert Hessian of the full-ball pressure. -/
def fullBallHarmonicHessianMatrix (F : unitBallGradientFreeForce) (x : Vec3) :
    StokesGradientMatrix :=
  WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 ↦
    mixedSecond (unitBallFullHarmonicForcePressureRepresentative F) ij.1 ij.2 x)

/-- The literal continuous full-ball Hessian on an arbitrary compact interior. -/
def fullBallHarmonicHessianMap (F : unitBallGradientFreeForce) : C(K, StokesGradientMatrix) where
  toFun := fun x ↦ fullBallHarmonicHessianMatrix F x.1
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin 3 ↦ ℝ)).comp
    apply continuous_pi
    intro ij
    have hp := contDiffOn_spatialDeriv_of_two (isOpen_vec3Ball 0 1)
      (unitBallFullHarmonicForcePressureRepresentative_contDiff F) ij.2
    have hd := hp.continuousOn_fderiv_of_isOpen (isOpen_vec3Ball 0 1) (by norm_num)
    exact continuousOn_iff_continuous_domRestrict.mp
      ((hd.clm_apply (g := fun _ ↦ basisVec ij.1) continuousOn_const).mono hK)

omit [CompactSpace K] in
/-- True full-ball pressure linearity gives actual Hessian additivity. -/
theorem fullBallHarmonicHessianMap_add (F G : unitBallGradientFreeForce) :
    fullBallHarmonicHessianMap K hK (F + G) =
      fullBallHarmonicHessianMap K hK F + fullBallHarmonicHessianMap K hK G := by
  ext x ij
  change mixedSecond (unitBallFullHarmonicForcePressureRepresentative (F + G)) ij.1 ij.2 x.1 =
    mixedSecond (unitBallFullHarmonicForcePressureRepresentative F) ij.1 ij.2 x.1 +
      mixedSecond (unitBallFullHarmonicForcePressureRepresentative G) ij.1 ij.2 x.1
  exact (mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball 0 1)
    (unitBallFullHarmonicForcePressureRepresentative_add F G) ij.1 ij.2 (hK x.property)).trans
    (mixedSecond_add_eqOn (isOpen_vec3Ball 0 1)
      (unitBallFullHarmonicForcePressureRepresentative_contDiff F)
      (unitBallFullHarmonicForcePressureRepresentative_contDiff G) ij.1 ij.2 (hK x.property))

omit [CompactSpace K] in
/-- True full-ball pressure linearity gives actual Hessian scaling. -/
theorem fullBallHarmonicHessianMap_smul (c : ℝ) (F : unitBallGradientFreeForce) :
    fullBallHarmonicHessianMap K hK (c • F) = c • fullBallHarmonicHessianMap K hK F := by
  ext x ij
  change mixedSecond (unitBallFullHarmonicForcePressureRepresentative (c • F)) ij.1 ij.2 x.1 =
    c * mixedSecond (unitBallFullHarmonicForcePressureRepresentative F) ij.1 ij.2 x.1
  exact (mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball 0 1)
    (unitBallFullHarmonicForcePressureRepresentative_smul c F) ij.1 ij.2 (hK x.property)).trans
    (mixedSecond_smul_eqOn (isOpen_vec3Ball 0 1)
      (unitBallFullHarmonicForcePressureRepresentative_contDiff F) c ij.1 ij.2 (hK x.property))

/-- The actual Hilbert Hessian norm satisfies the true margin-dependent force bound. -/
theorem fullBallHarmonicHessianMap_norm_le {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) (F : unitBallGradientFreeForce) :
    ‖fullBallHarmonicHessianMap K hK F‖ ≤ fullBallHarmonicForceHessianCoefficient ρ * ‖F‖ := by
  let B := fullBallHarmonicHessianConstant ρ *
    lpNorm (unitBallPressureFunction F.1) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball 0 1))
  have hB : 0 ≤ B := mul_nonneg (fullBallHarmonicHessianConstant_nonneg hρ) lpNorm_nonneg
  have hl : 3 * B ≤ fullBallHarmonicForceHessianCoefficient ρ * ‖F‖ := by
    have ht := mul_le_mul_of_nonneg_left (unitBallPressureFunction_lpNorm_threeHalves_le F.1)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (fullBallHarmonicHessianConstant_nonneg hρ))
    simpa only [B, fullBallHarmonicForceHessianCoefficient, unitBallGradientFreeForce_norm_coe,
      mul_assoc] using ht
  apply (ContinuousMap.norm_le _
    (mul_nonneg (fullBallHarmonicForceHessianCoefficient_nonneg hρ) (norm_nonneg F))).mpr
  intro x
  have he (ij : Fin 3 × Fin 3) : ‖fullBallHarmonicHessianMatrix F x.1 ij‖ ≤ B := by
    exact fullBallHarmonic_representative_hessian_bound
      (unitBallPressureFunction_memLp_threeHalves F.1)
      (unitBallStokesPressure_weaklyHarmonic F.1 F.property)
      (unitBallFullHarmonicForcePressureRepresentative_contDiff F)
      (unitBallFullHarmonicForcePressureRepresentative_ae F) hρ (hKρ x.property) ij.1 ij.2
  have hs : ‖fullBallHarmonicHessianMatrix F x.1‖ ^ 2 ≤ 9 * B ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ij : Fin 3 × Fin 3, B ^ 2 := by
        apply Finset.sum_le_sum
        intro ij _
        exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (he ij)
      _ = _ := by norm_num
  have hn : ‖fullBallHarmonicHessianMatrix F x.1‖ ≤ 3 * B := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hB)).mp
    nlinarith
  exact hn.trans hl

/-- The actual bounded linear pressure Hessian on any compact interior. -/
def fullBallHarmonicHessian {ρ : ℝ} (hρ : ρ < 1) (hKρ : K ⊆ vec3Ball 0 ρ) :
    unitBallGradientFreeForce →L[ℝ] C(K, StokesGradientMatrix) :=
  ({ toFun := fullBallHarmonicHessianMap K hK
     map_add' := fullBallHarmonicHessianMap_add K hK
     map_smul' := fullBallHarmonicHessianMap_smul K hK } :
       unitBallGradientFreeForce →ₗ[ℝ] C(K, StokesGradientMatrix)).mkContinuous
    (fullBallHarmonicForceHessianCoefficient ρ)
    (fullBallHarmonicHessianMap_norm_le K hK hρ hKρ)

/-- The actual full-ball gradient, extended by the genuine orthogonal force projection. -/
def fullBallHarmonicGradientExtended {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) : StokesEnergyForce (vec3Ball 0 1) →L[ℝ] C(K, Vec3) :=
  (fullBallHarmonicGradient K hK hρ hKρ).comp unitBallGradientFreeForceProjection

/-- Actual pressure values extended by the genuine orthogonal force projection. -/
def fullBallHarmonicValuesExtended {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) : StokesEnergyForce (vec3Ball 0 1) →L[ℝ] C(K, ℝ) :=
  (fullBallHarmonicValues K hK hρ hKρ).comp unitBallGradientFreeForceProjection

/-- The actual full-ball Hessian, extended by the genuine orthogonal force projection. -/
def fullBallHarmonicHessianExtended {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] C(K, StokesGradientMatrix) :=
  (fullBallHarmonicHessian K hK hρ hKρ).comp unitBallGradientFreeForceProjection

/-- The extended actual gradient obeys the same genuine margin bound. -/
theorem fullBallHarmonicGradientExtended_norm_le {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖fullBallHarmonicGradientExtended K hK hρ hKρ F‖ ≤
      fullBallHarmonicForceGradientCoefficient ρ * ‖F‖ :=
  (fullBallHarmonicGradientMap_norm_le K hK hρ hKρ _).trans
    (mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F)
      (fullBallHarmonicForceGradientCoefficient_nonneg hρ))

/-- Extended actual pressure values obey the same genuine margin bound. -/
theorem fullBallHarmonicValuesExtended_norm_le {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖fullBallHarmonicValuesExtended K hK hρ hKρ F‖ ≤
      fullBallHarmonicForceValueCoefficient ρ * ‖F‖ :=
  (fullBallHarmonicValueMap_norm_le K hK hρ hKρ _).trans
    (mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F)
      (fullBallHarmonicForceValueCoefficient_nonneg hρ))

/-- The extended actual Hessian obeys the same genuine margin bound. -/
theorem fullBallHarmonicHessianExtended_norm_le {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖fullBallHarmonicHessianExtended K hK hρ hKρ F‖ ≤
      fullBallHarmonicForceHessianCoefficient ρ * ‖F‖ :=
  (fullBallHarmonicHessianMap_norm_le K hK hρ hKρ _).trans
    (mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F)
      (fullBallHarmonicForceHessianCoefficient_nonneg hρ))

/-- The actual extended gradient operator has the quantitative margin bound. -/
theorem fullBallHarmonicGradientExtended_opNorm_le {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) :
    ‖fullBallHarmonicGradientExtended K hK hρ hKρ‖ ≤
      fullBallHarmonicForceGradientCoefficient ρ :=
  ContinuousLinearMap.opNorm_le_bound _ (fullBallHarmonicForceGradientCoefficient_nonneg hρ)
    (fullBallHarmonicGradientExtended_norm_le K hK hρ hKρ)

/-- The actual extended value operator has the quantitative margin bound. -/
theorem fullBallHarmonicValuesExtended_opNorm_le {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) :
    ‖fullBallHarmonicValuesExtended K hK hρ hKρ‖ ≤ fullBallHarmonicForceValueCoefficient ρ :=
  ContinuousLinearMap.opNorm_le_bound _ (fullBallHarmonicForceValueCoefficient_nonneg hρ)
    (fullBallHarmonicValuesExtended_norm_le K hK hρ hKρ)

/-- The actual extended Hessian operator has the quantitative margin bound. -/
theorem fullBallHarmonicHessianExtended_opNorm_le {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) :
    ‖fullBallHarmonicHessianExtended K hK hρ hKρ‖ ≤
      fullBallHarmonicForceHessianCoefficient ρ :=
  ContinuousLinearMap.opNorm_le_bound _ (fullBallHarmonicForceHessianCoefficient_nonneg hρ)
    (fullBallHarmonicHessianExtended_norm_le K hK hρ hKρ)

/-- The actual extended gradient fixes every genuine gradient-annihilating force. -/
theorem fullBallHarmonicGradientExtended_of_gradientFree {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) (F : unitBallGradientFreeForce) :
    fullBallHarmonicGradientExtended K hK hρ hKρ F.1 =
      fullBallHarmonicGradient K hK hρ hKρ F := by
  simp only [fullBallHarmonicGradientExtended, ContinuousLinearMap.comp_apply,
    unitBallGradientFreeForceProjection_of_gradientFree]

/-- Actual extended values fix every genuine gradient-annihilating force. -/
theorem fullBallHarmonicValuesExtended_of_gradientFree {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) (F : unitBallGradientFreeForce) :
    fullBallHarmonicValuesExtended K hK hρ hKρ F.1 = fullBallHarmonicValues K hK hρ hKρ F := by
  simp only [fullBallHarmonicValuesExtended, ContinuousLinearMap.comp_apply,
    unitBallGradientFreeForceProjection_of_gradientFree]

/-- The actual extended Hessian fixes every genuine gradient-annihilating force. -/
theorem fullBallHarmonicHessianExtended_of_gradientFree {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) (F : unitBallGradientFreeForce) :
    fullBallHarmonicHessianExtended K hK hρ hKρ F.1 =
      fullBallHarmonicHessian K hK hρ hKρ F := by
  simp only [fullBallHarmonicHessianExtended, ContinuousLinearMap.comp_apply,
    unitBallGradientFreeForceProjection_of_gradientFree]

/-- Actual pressure values obey the mean-value bound on every genuine interior ball. -/
theorem fullBallHarmonicValues_sub_le {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) (F : unitBallGradientFreeForce) (x y : K) :
    ‖fullBallHarmonicValues K hK hρ hKρ F x - fullBallHarmonicValues K hK hρ hKρ F y‖ ≤
      (3 * fullBallHarmonicForceGradientCoefficient ρ) * ‖F‖ * ‖x.1 - y.1‖ := by
  have hd := (unitBallFullHarmonicForcePressureRepresentative_contDiff F).differentiableOn
    (by norm_num)
  have hb (z : Vec3) (hz : z ∈ vec3Ball 0 ρ) :
      vec3EuclideanNorm (classicalGradient (unitBallFullHarmonicForcePressureRepresentative F) z) ≤
        fullBallHarmonicForceGradientCoefficient ρ * ‖F‖ := by
    have ht := fullBallHarmonic_representative_gradient_bound
      (unitBallPressureFunction_memLp_threeHalves F.1)
      (unitBallStokesPressure_weaklyHarmonic F.1 F.property)
      (unitBallFullHarmonicForcePressureRepresentative_contDiff F)
      (unitBallFullHarmonicForcePressureRepresentative_ae F) hρ hz
    apply ht.trans
    have hl := mul_le_mul_of_nonneg_left (unitBallPressureFunction_lpNorm_threeHalves_le F.1)
      (fullBallHarmonicGradientConstant_nonneg hρ)
    simpa only [fullBallHarmonicForceGradientCoefficient, unitBallGradientFreeForce_norm_coe,
      mul_assoc] using hl
  have hderiv : ∀ z ∈ vec3Ball 0 ρ,
      ‖fderiv ℝ (unitBallFullHarmonicForcePressureRepresentative F) z‖ ≤
        (3 * fullBallHarmonicForceGradientCoefficient ρ) * ‖F‖ := by
    intro z hz
    apply (fderiv_norm_le_three_euclidean_classicalGradient z).trans
    have ht := mul_le_mul_of_nonneg_left (hb z hz) (by norm_num : (0 : ℝ) ≤ 3)
    simpa only [mul_assoc] using ht
  have hconv : Convex ℝ (vec3Ball (0 : Vec3) ρ) := by
    rw [← euclideanBall_eq_vec3Ball hρpos]
    exact convex_euclideanBall hρpos
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ (hd z ((vec3Ball_mono hρ.le) hz)).differentiableAt
      ((isOpen_vec3Ball 0 1).mem_nhds ((vec3Ball_mono hρ.le) hz)))
    hderiv hconv (hKρ y.property) (hKρ x.property)

/-- The true dual evaluation kernel of actual full-ball pressure values. -/
def fullBallHarmonicValueKernel {ρ : ℝ} (hρ : ρ < 1) (hKρ : K ⊆ vec3Ball 0 ρ) (x : K) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x).comp (fullBallHarmonicValuesExtended K hK hρ hKρ)

/-- The true gradient estimate controls the evaluation kernel in operator norm. -/
theorem fullBallHarmonicValueKernel_sub_norm_le {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) (x y : K) :
    ‖fullBallHarmonicValueKernel K hK hρ hKρ x - fullBallHarmonicValueKernel K hK hρ hKρ y‖ ≤
      (3 * fullBallHarmonicForceGradientCoefficient ρ) * ‖x.1 - y.1‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (by norm_num) (fullBallHarmonicForceGradientCoefficient_nonneg hρ))
      (norm_nonneg _))
  intro F
  have ht := fullBallHarmonicValues_sub_le K hK hρpos hρ hKρ
    (unitBallGradientFreeForceProjection F) x y
  change ‖fullBallHarmonicValues K hK hρ hKρ (unitBallGradientFreeForceProjection F) x -
    fullBallHarmonicValues K hK hρ hKρ (unitBallGradientFreeForceProjection F) y‖ ≤ _
  apply ht.trans
  calc
    _ ≤ (3 * fullBallHarmonicForceGradientCoefficient ρ) * ‖F‖ * ‖x.1 - y.1‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F)
          (mul_nonneg (by norm_num) (fullBallHarmonicForceGradientCoefficient_nonneg hρ)))
        (norm_nonneg _)
    _ = _ := by ring

/-- Actual pressure evaluation is continuous in the energy-force dual norm. -/
theorem fullBallHarmonicValueKernel_continuous {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) : Continuous (fullBallHarmonicValueKernel K hK hρ hKρ) := by
  have hl : LipschitzWith (Real.toNNReal (3 * fullBallHarmonicForceGradientCoefficient ρ))
      (fullBallHarmonicValueKernel K hK hρ hKρ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Subtype.dist_eq, dist_eq_norm,
      Real.coe_toNNReal _ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
        (fullBallHarmonicForceGradientCoefficient_nonneg hρ))] using
      fullBallHarmonicValueKernel_sub_norm_le K hK hρpos hρ hKρ x y
  exact hl.continuous

end FluidSingularSets
