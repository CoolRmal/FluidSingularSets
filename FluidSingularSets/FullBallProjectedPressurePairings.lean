-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallPressureMeanPairings
public import FluidSingularSets.FullBallProjectedSixControl
public import FluidSingularSets.ProjectedViscousMixedPairing

/-!
# Actual pressure pairing bounds at every interior projection radius

The actual original-interval projected velocity gives literal cutoff pressure
pairings. Genuine full-ball Stokes source bounds control the convective term
by the weighted corrected energy and the viscous term by the original velocity
mixed norm and gradient energy. Constants retain the true boundary margin.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance fullBallPressurePairingsSpaceSecondCountable : SecondCountableTopology Vec3 :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → ℝ))

/-- A finite positive viscous pairing coefficient retaining the actual boundary margin. -/
def fullBallViscousMixedPairingCoefficient (ρ L : ℝ) : ℝ≥0∞ :=
  1 + 12 * ENNReal.ofReal (6 * L) * fullBallProjectedVelocitySliceCoefficient ρ *
    volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ)

theorem fullBallViscousMixedPairingCoefficient_ne_top (ρ L : ℝ) :
    fullBallViscousMixedPairingCoefficient ρ L ≠ ⊤ := by
  unfold fullBallViscousMixedPairingCoefficient
  have hv : volume (vec3Ball (0 : Vec3) 1) ≠ ⊤ := volume_vec3Ball_lt_top.ne
  finiteness [fullBallProjectedVelocitySliceCoefficient_ne_top ρ, hv]

theorem fullBallViscousMixedPairingCoefficient_pos (ρ L : ℝ) :
    0 < fullBallViscousMixedPairingCoefficient ρ L := by
  exact zero_lt_one.trans_le (le_add_right le_rfl)

section LocalBox

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3}

/-- The actual cubed-cutoff velocity on the unchanged local interval. -/
def fullBallProjectedCutoffVelocity (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) (a b c : ℝ)
    (φ : Vec3 → ℝ) (z : ParabolicPoint) : Vec3 :=
  φ z.1 ^ 3 • fullBallProjectedVelocityAmbient u D p a b c z

/-- The literal sixth-cutoff viscous pressure test component. -/
def fullBallProjectedPressureCutoffComponent (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) (a b c : ℝ)
    (φ : Vec3 → ℝ) (θ : ℝ → ℝ) (i : Fin 3) (z : ParabolicPoint) : ℝ :=
  θ z.2 * fullBallProjectedVelocityAmbient u D p a b c z i *
    spatialDeriv (fun x ↦ φ x ^ (6 : ℕ)) i z.1

/-- The actual pressure test factors through the true cubed-cutoff velocity. -/
theorem fullBallProjectedPressureCutoffComponent_eq_weighted
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (θ : ℝ → ℝ) (i : Fin 3) (z : ParabolicPoint) :
    fullBallProjectedPressureCutoffComponent u D p a b c φ θ i z =
      (6 * θ z.2 * φ z.1 ^ 2 * spatialDeriv φ i z.1) *
        fullBallProjectedCutoffVelocity u D p a b c φ z i := by
  simp only [fullBallProjectedPressureCutoffComponent, fullBallProjectedCutoffVelocity,
    spatialDeriv_cutoff_sixth hφ, Pi.smul_apply, smul_eq_mul]
  ring

/-- The literal weighted projected energy supremum on the original local interval. -/
def fullBallProjectedCutoffSliceEnergy
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (B : Set Vec3) (φ : Vec3 → ℝ) : ℝ≥0∞ :=
  essSup (fun t ↦ ∫⁻ x in B,
    ‖fullBallProjectedCutoffVelocity u D p a b c φ (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo a b))

/-- Genuine original suitable data give true weighted joint measurability. -/
theorem fullBallProjectedCutoffVelocity_aestronglyMeasurable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    AEStronglyMeasurable (fullBallProjectedCutoffVelocity u D p a b c φ)
      ((volume.restrict B).prod (volume.restrict (Ioo a b))) := by
  have hV : AEStronglyMeasurable (fullBallProjectedVelocityAmbient u D p a b c)
      ((volume.restrict B).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact (fullBallProjectedVelocityAmbient_joint_memLp_two
      hsol hbox hab hc hρ hρone hBK).1.aestronglyMeasurable
  exact ((hφ.pow 3).continuous.comp continuous_fst).aestronglyMeasurable.smul hV

/-- Genuine weak suitable slices give actual weighted spatial L² membership. -/
theorem fullBallProjectedCutoffVelocity_slices_memLp_two
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), MemLp
      (fun x ↦ fullBallProjectedCutoffVelocity u D p a b c φ (x, t)) 2
        (volume.restrict B) := by
  filter_upwards [fullBallProjectedVelocityAmbient_weak_gradient_slices_ae
    u D p a b c hsol hbox hρ hρone hB hBK] with t ht
  apply ht.1.of_le
    ((hφ.pow 3).continuous.aestronglyMeasurable.smul ht.1.aestronglyMeasurable)
  exact ae_of_all _ fun x ↦ projected_cutoff_power_norm_le _ (hb x).1 (hb x).2 3

/-- Actual weighted energy is bounded by the true full-ball suitable source energy. -/
theorem fullBallProjectedCutoffSliceEnergy_le_source
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    fullBallProjectedCutoffSliceEnergy u D p a b c B φ ≤
      fullBallProjectedVelocitySliceCoefficient ρ ^ 2 *
        essSup (fun t ↦ ∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
          (volume.restrict (Ioo a b)) := by
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫⁻ x in B, ‖fullBallProjectedCutoffVelocity u D p a b c φ (x, t)‖ₑ ^ (2 : ℝ)) ≤
        fullBallProjectedVelocitySliceCoefficient ρ ^ 2 *
          ∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ) := by
    filter_upwards [fullBallProjectedVelocityAmbient_slice_norm_le_source_ae
      hsol hbox hab hc hρ hρone hB hBK,
      fullBallProjectedCutoffVelocity_slices_memLp_two hsol hbox hρ hρone hB hBK hφ hb,
      slice_memLp_ae_of_sws hsol hbox] with t hvt hwt hut
    have hW := eLpNorm_mono_ae (p := 2) hwt.aestronglyMeasurable
      (ae_of_all _ fun x ↦ projected_cutoff_power_norm_le
        (fullBallProjectedVelocityAmbient u D p a b c (x, t)) (hb x).1 (hb x).2 3)
    have hWEq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0))
      (by norm_num) hwt.aestronglyMeasurable
    have hUEq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0))
      (by norm_num) hut.1.aestronglyMeasurable
    norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at hWEq hUEq
    have hs : ‖unitBallVelocityCurve u t‖ₑ ^ 2 =
        ∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ) := by
      rw [unitBallVelocityCurve, actualSliceLp_enorm u t hut.1]
      simpa only [ENNReal.rpow_ofNat] using hUEq
    have hh := pow_le_pow_left' (hW.trans hvt) 2
    rw [mul_pow, hWEq, hs] at hh
    simpa only [ENNReal.rpow_ofNat] using hh
  exact (essSup_mono_ae hpoint).trans_eq ENNReal.essSup_const_mul

/-- Actual suitable S1 makes the literal weighted corrected energy finite. -/
theorem fullBallProjectedCutoffSliceEnergy_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    fullBallProjectedCutoffSliceEnergy u D p a b c B φ < ⊤ :=
  (fullBallProjectedCutoffSliceEnergy_le_source
    hsol hbox hab hc hρ hρone hB hBK hφ hb).trans_lt
      (ENNReal.mul_lt_top (ENNReal.pow_ne_top
        (fullBallProjectedVelocitySliceCoefficient_ne_top ρ)).lt_top
          (hsol.toData.essSup_sliceEnergy_lt_top hbox))

/-- The actual weighted class has its true square-root weighted-energy time bound. -/
theorem fullBallProjectedCutoffVelocity_curve_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    MemLp (actualSliceLp (μ := volume.restrict B) (p := 2)
      (fullBallProjectedCutoffVelocity u D p a b c φ)) ⊤ (volume.restrict (Ioo a b)) ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2)
      (fullBallProjectedCutoffVelocity u D p a b c φ)) ⊤ (volume.restrict (Ioo a b)) ≤
        fullBallProjectedCutoffSliceEnergy u D p a b c B φ ^ (1 / 2 : ℝ) := by
  have hj := fullBallProjectedCutoffVelocity_aestronglyMeasurable
    hsol hbox hab hc hρ hρone hBK hφ
  exact ⟨actualSliceLp_memLp_top_of_sliceEnergy hj
    (fullBallProjectedCutoffSliceEnergy_lt_top hsol hbox hab hc hρ hρone hB hBK hφ hb),
    actualSliceLp_eLpNorm_top_le_sliceEnergy hj⟩

/-- A true scalar cutoff test dominated by the weighted velocity has genuine mixed data. -/
theorem fullBallProjectedCutoffScalar_curve_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {G : ParabolicPoint → ℝ} (hG : AEStronglyMeasurable G
      ((volume.restrict B).prod (volume.restrict (Ioo a b))))
    {C : ℝ} (hbound : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ᵐ x ∂volume.restrict B,
      ‖G (x, t)‖ ≤ C * ‖fullBallProjectedCutoffVelocity u D p a b c φ (x, t)‖) :
    ProjectedEnergySliceData (volume.restrict B) (volume.restrict (Ioo a b)) ⊤ G ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2) G) ⊤
      (volume.restrict (Ioo a b)) ≤ ENNReal.ofReal C *
        fullBallProjectedCutoffSliceEnergy u D p a b c B φ ^ (1 / 2 : ℝ) := by
  have hs := fullBallProjectedCutoffVelocity_slices_memLp_two (c := c)
    hsol hbox hρ hρone hB hBK hφ hb
  have hw := fullBallProjectedCutoffVelocity_curve_data
    hsol hbox hab hc hρ hρone hB hBK hφ hb
  have hd := projectedEnergySliceData_top_of_velocity_bound hG hs hw.1 hbound
  have hnorm : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ‖actualSliceLp (μ := volume.restrict B) (p := 2) G t‖ₑ ≤ ENNReal.ofReal C *
        ‖actualSliceLp (μ := volume.restrict B) (p := 2)
          (fullBallProjectedCutoffVelocity u D p a b c φ) t‖ₑ := by
    filter_upwards [hd.slices, hs, hbound] with t hgt hwt hbt
    rw [actualSliceLp_enorm G t hgt,
      actualSliceLp_enorm (fullBallProjectedCutoffVelocity u D p a b c φ) t hwt]
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hgt.aestronglyMeasurable hbt 2
  exact ⟨hd, (eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' ⊤
    hd.classMemLp.aestronglyMeasurable hnorm).trans (mul_le_mul' le_rfl hw.2)⟩

/-- Actual suitability gives the pressure test genuine time L² spatial L² data. -/
theorem fullBallProjectedPressureCutoffComponent_curve_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3) :
    (∀ᵐ t ∂volume.restrict (Ioo a b), MemLp
      (fun x ↦ fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t)) 2
        (volume.restrict B)) ∧
    MemLp (actualSliceLp (μ := volume.restrict B) (p := 2)
      (fullBallProjectedPressureCutoffComponent u D p a b c φ θ i)) 2
        (volume.restrict (Ioo a b)) ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2)
      (fullBallProjectedPressureCutoffComponent u D p a b c φ θ i)) 2
        (volume.restrict (Ioo a b)) ≤
      ENNReal.ofReal (6 * L) * fullBallProjectedVelocitySliceCoefficient ρ *
        eLpNorm (unitBallVelocityCurve u) 2 (volume.restrict (Ioo a b)) := by
  let G := fullBallProjectedPressureCutoffComponent u D p a b c φ θ i
  let A : Vec3 × ℝ → ℝ := fun z ↦ 6 * θ z.2 * φ z.1 ^ 5 * spatialDeriv φ i z.1
  have hA : Continuous A :=
    ((continuous_const.mul (hθ.comp continuous_snd)).mul
      ((hφ.pow 5).continuous.comp continuous_fst)).mul
        ((contDiff_spatialDeriv_smooth hφ i).continuous.comp continuous_fst)
  have heq : G = fun z ↦ A z * fullBallProjectedVelocityAmbient u D p a b c z i := by
    funext z
    simp only [G, fullBallProjectedPressureCutoffComponent, spatialDeriv_cutoff_sixth hφ, A]
    ring
  have hAb (z : ParabolicPoint) : ‖A z‖ ≤ 6 * L := by
    have hg : ‖spatialDeriv φ i z.1‖ ≤ L :=
      (norm_le_pi_norm (classicalGradient φ z.1) i).trans (hgrad z.1)
    have hp : ‖φ z.1 ^ 5‖ ≤ 1 := by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (hb z.1).1]
      exact pow_le_one₀ (hb z.1).1 (hb z.1).2
    calc
      ‖A z‖ = 6 * ‖θ z.2‖ * ‖φ z.1 ^ 5‖ * ‖spatialDeriv φ i z.1‖ := by
        simp only [A, norm_mul, Real.norm_ofNat]
      _ ≤ 6 * 1 * 1 * L := by gcongr; exact hθb z.2
      _ = 6 * L := by ring
  have hV : AEStronglyMeasurable (fullBallProjectedVelocityAmbient u D p a b c)
      ((volume.restrict B).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact (fullBallProjectedVelocityAmbient_joint_memLp_two
      hsol hbox hab hc hρ hρone hBK).1.aestronglyMeasurable
  have hGj : AEStronglyMeasurable G
      ((volume.restrict B).prod (volume.restrict (Ioo a b))) := by
    rw [heq]
    exact hA.aestronglyMeasurable.mul ((continuous_apply i).comp_aestronglyMeasurable hV)
  have hGb (z : ParabolicPoint) : ‖G z‖ ≤ 6 * L *
      ‖fullBallProjectedVelocityAmbient u D p a b c z‖ := by
    rw [heq, norm_mul]
    exact mul_le_mul (hAb z) (norm_le_pi_norm _ i) (norm_nonneg _) (by positivity)
  have hGs : ∀ᵐ t ∂volume.restrict (Ioo a b),
      MemLp (fun x ↦ G (x, t)) 2 (volume.restrict B) := by
    filter_upwards [fullBallProjectedVelocityAmbient_weak_gradient_slices_ae
      u D p a b c hsol hbox hρ hρone hB hBK, hGj.prodMk_right] with t ht hgt
    exact ht.1.of_le_mul hgt (ae_of_all _ fun x ↦ hGb (x, t))
  have hcap : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ‖actualSliceLp (μ := volume.restrict B) (p := 2) G t‖ₑ ≤
        (ENNReal.ofReal (6 * L) * fullBallProjectedVelocitySliceCoefficient ρ) *
          ‖unitBallVelocityCurve u t‖ₑ := by
    filter_upwards [hGs, fullBallProjectedVelocityAmbient_slice_norm_le_source_ae
      hsol hbox hab hc hρ hρone hB hBK] with t hgt hvt
    rw [actualSliceLp_enorm G t hgt]
    exact (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hgt.aestronglyMeasurable
      (ae_of_all _ fun x ↦ hGb (x, t)) 2).trans
        ((mul_le_mul' le_rfl hvt).trans_eq (mul_assoc _ _ _).symm)
  have hnorm := eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' 2
    (aestronglyMeasurable_actualSliceLp hGj (by norm_num)) hcap
  have hGc : MemLp (actualSliceLp (μ := volume.restrict B) (p := 2) G) 2
      (volume.restrict (Ioo a b)) := hnorm.trans_lt
    (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (fullBallProjectedVelocitySliceCoefficient_ne_top ρ).lt_top)
      (suitable_velocityCurve_memLp_localBox hsol hbox).eLpNorm_lt_top)
  exact ⟨hGs, hGc, hnorm⟩

/-- The actual viscous pressure pairing has no corrected-velocity energy supremum term. -/
theorem suitable_fullBall_viscous_mixed_pairing_bound_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3) :
    Integrable (fun t ↦ ∫ x in B, (unitBallViscousPressureCurve D t).val x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t))
        (volume.restrict (Ioo a b)) ∧
    ‖∫ t in Ioo a b, ∫ x in B, (unitBallViscousPressureCurve D t).val x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t)‖ₑ ≤
      12 * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ))
        ^ (1 / 2 : ℝ) * ENNReal.ofReal (6 * L) * fullBallProjectedVelocitySliceCoefficient ρ *
          volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ) *
            (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
              (volume.restrict (vec3Ball 0 1)) ^ 2) ^ (1 / 2 : ℝ) := by
  have hG := fullBallProjectedPressureCutoffComponent_curve_data
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb i
  have hB1 := hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  have hDn := hsol.toData.aestronglyMeasurable_gradient hbox
  have hD : AEStronglyMeasurable D
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hDn
  have hDs : ∀ᵐ t ∂volume.restrict (Ioo a b),
      MemLp (fun x ↦ D (x, t)) 2 (volume.restrict (vec3Ball 0 1)) := by
    filter_upwards [slice_memLp_ae_of_sws hsol hbox] with t ht
    exact ht.2
  have hfin : (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ D (x, t)) 2
      (volume.restrict (vec3Ball 0 1)) ^ 2) < ⊤ := by
    rw [lintegral_spatial_two_sq_eq hDn]
    exact (lintegral_mono (fun _ ↦ le_add_left le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)
  have hP := unitBallViscousPressureCurve_memLp_two_of_gradient_moment hD hDs hfin
  have hPv : MemLp (fun t ↦ (unitBallViscousPressureCurve D t).val) 2
      (volume.restrict (Ioo a b)) :=
    hP.continuousLinearMap_comp unitBallMeanZeroL2.toSubmodule.subtypeL
  have hPeq : eLpNorm (fun t ↦ (unitBallViscousPressureCurve D t).val) 2
      (volume.restrict (Ioo a b)) =
      eLpNorm (unitBallViscousPressureCurve D) 2 (volume.restrict (Ioo a b)) :=
    eLpNorm_congr_norm_ae hPv.aestronglyMeasurable hP.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ rfl)
  have hpbound := unitBallViscousPressureCurve_eLpNorm_two_le_gradient_moment hD hDs
  rw [lintegral_spatial_two_sq_eq hDn] at hpbound
  change eLpNorm (unitBallViscousPressureCurve D) 2 (volume.restrict (Ioo a b)) ≤
    12 * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ))
      ^ (1 / 2 : ℝ) at hpbound
  have hh := pressureCurve_pairing_restrict_two_two_integrable_and_bound
    (Measure.restrict_mono_set volume hB1) hPv hG.1 hG.2.1
  rw [hPeq] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hgb := hG.2.2.trans (mul_le_mul' le_rfl
    (localBox_velocityCurve_two_le_six_moment_sqrt hsol hbox))
  exact (mul_le_mul' hpbound hgb).trans_eq (by ring)

/-- Actual suitable viscous pressure is absorbed by original gradient and endpoint cost alone. -/
theorem suitable_fullBall_viscous_mixed_pairing_young_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1)
    (i : Fin 3) {δ : ℝ} (hδ : 0 < δ) :
    ‖∫ t in Ioo a b, ∫ x in B, (unitBallViscousPressureCurve D t).val x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t)‖ₑ ≤
      ENNReal.ofReal δ * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b,
        ‖D z‖ₑ ^ (2 : ℝ)) +
      fullBallViscousMixedPairingCoefficient ρ L ^ 2 / (4 * ENNReal.ofReal δ) *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2) := by
  let E : ℝ≥0∞ := ∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ)
  let X : ℝ≥0∞ := ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
    (volume.restrict (vec3Ball 0 1)) ^ 2
  let A : ℝ≥0∞ := 12 * ENNReal.ofReal (6 * L) * fullBallProjectedVelocitySliceCoefficient ρ *
    volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ)
  have hh := (suitable_fullBall_viscous_mixed_pairing_bound_localBox
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb i).2
  have hbnd : ‖∫ t in Ioo a b, ∫ x in B, (unitBallViscousPressureCurve D t).val x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t)‖ₑ ≤
      fullBallViscousMixedPairingCoefficient ρ L * E ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ A * E ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := hh.trans_eq (by dsimp [A, E, X]; ring)
      _ ≤ _ := mul_le_mul' (mul_le_mul' (le_add_left le_rfl) le_rfl) le_rfl
  exact hbnd.trans (ennreal_viscous_mixed_young
    (fullBallViscousMixedPairingCoefficient_ne_top ρ L)
    (fullBallViscousMixedPairingCoefficient_pos ρ L) hδ)

/-- Actual smooth pressure tests have genuine weighted mixed classes without extra data. -/
theorem fullBallProjectedPressureCutoffComponent_top_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3) :
    ProjectedEnergySliceData (volume.restrict B)
      (volume.restrict (Ioo a b)) ⊤
      (fullBallProjectedPressureCutoffComponent u D p a b c φ θ i) ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2)
      (fullBallProjectedPressureCutoffComponent u D p a b c φ θ i)) ⊤
        (volume.restrict (Ioo a b)) ≤
      ENNReal.ofReal (6 * L) *
        fullBallProjectedCutoffSliceEnergy u D p a b c B φ ^ (1 / 2 : ℝ) := by
  let A : Vec3 × ℝ → ℝ := fun z ↦ 6 * θ z.2 * φ z.1 ^ 2 * spatialDeriv φ i z.1
  have hA : Continuous A :=
    ((continuous_const.mul (hθ.comp continuous_snd)).mul
      ((hφ.pow 2).continuous.comp continuous_fst)).mul
        ((contDiff_spatialDeriv_smooth hφ i).continuous.comp continuous_fst)
  have heq : fullBallProjectedPressureCutoffComponent u D p a b c φ θ i =
      fun z ↦ A z * fullBallProjectedCutoffVelocity u D p a b c φ z i := by
    funext z
    simp only [fullBallProjectedPressureCutoffComponent, spatialDeriv_cutoff_sixth hφ,
      A, fullBallProjectedCutoffVelocity, Pi.smul_apply, smul_eq_mul]
    ring
  have hAb (z : ParabolicPoint) : ‖A z‖ ≤ 6 * L := by
    have hg : ‖spatialDeriv φ i z.1‖ ≤ L :=
      (norm_le_pi_norm (classicalGradient φ z.1) i).trans (hgrad z.1)
    have hp : ‖φ z.1 ^ 2‖ ≤ 1 := by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (hb z.1).1]
      exact pow_le_one₀ (hb z.1).1 (hb z.1).2
    calc
      ‖A z‖ = 6 * ‖θ z.2‖ * ‖φ z.1 ^ 2‖ * ‖spatialDeriv φ i z.1‖ := by
        simp only [A, norm_mul, Real.norm_ofNat]
      _ ≤ 6 * 1 * 1 * L := by gcongr; exact hθb z.2
      _ = 6 * L := by ring
  have hW := fullBallProjectedCutoffVelocity_aestronglyMeasurable
    hsol hbox hab hc hρ hρone hBK hφ
  have hm : AEStronglyMeasurable
      (fullBallProjectedPressureCutoffComponent u D p a b c φ θ i)
      ((volume.restrict B).prod (volume.restrict (Ioo a b))) := by
    rw [heq]
    exact hA.aestronglyMeasurable.mul
      ((continuous_apply i).comp_aestronglyMeasurable hW)
  apply fullBallProjectedCutoffScalar_curve_data
    hsol hbox hab hc hρ hρone hB hBK hφ hb hm
  exact ae_of_all _ fun t ↦ ae_of_all _ fun x ↦ by
    rw [heq, norm_mul]
    exact mul_le_mul (hAb (x, t)) (norm_le_pi_norm _ i)
      (norm_nonneg _) (by positivity)

/-- Original suitable full-ball weak gradients give genuine spatial L⁶ on the same ball. -/
theorem suitable_fullBall_source_memLp_six_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      MemLp (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) := by
  have hw := ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht hwt
  exact fullUnitBallH1Vector_memLp_six ht.1 ht.2 hwt

/-- A genuine time L¹ pressure class pairs with the actual weighted full-ball cutoff test. -/
theorem suitable_fullBall_pressure_cutoff_component_one_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3)
    {P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball 0 1))}
    (hP : MemLp P 1 (volume.restrict (Ioo a b))) :
    Integrable (fun t ↦ ∫ x in B, P t x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t))
        (volume.restrict (Ioo a b)) ∧
    ‖∫ t in Ioo a b, ∫ x in B, P t x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t)‖ₑ ≤
        eLpNorm P 1 (volume.restrict (Ioo a b)) * ENNReal.ofReal (6 * L) *
          fullBallProjectedCutoffSliceEnergy u D p a b c B φ ^ (1 / 2 : ℝ) := by
  have hB1 := hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  have hG := fullBallProjectedPressureCutoffComponent_top_data
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb i
  have hh := pressureCurve_pairing_restrict_one_top_integrable_and_bound
    (Measure.restrict_mono_set volume hB1) hP hG.1.slices hG.1.classMemLp
  exact ⟨hh.1, hh.2.trans ((mul_le_mul' le_rfl hG.2).trans_eq (by ring))⟩

/-- Actual same-ball suitability supplies the true convective pressure weighted pairing bound. -/
theorem suitable_fullBall_convective_pressure_cutoff_component_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3) :
    Integrable (fun t ↦ ∫ x in B, (unitBallConvectivePressureCurve u t).val x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t))
        (volume.restrict (Ioo a b)) ∧
    ‖∫ t in Ioo a b, ∫ x in B, (unitBallConvectivePressureCurve u t).val x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t)‖ₑ ≤
      12 * volume (vec3Ball (0 : Vec3) 1) ^ (1 / 6 : ℝ) *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2) * ENNReal.ofReal (6 * L) *
            fullBallProjectedCutoffSliceEnergy u D p a b c B φ ^ (1 / 2 : ℝ) := by
  let ν := volume.restrict (Ioo a b)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioo])
  have hP : MemLp (unitBallConvectivePressureCurve u) 1 ν :=
    ((suitable_convectiveTensorCurve_memLp_localBox hsol hbox).continuousLinearMap_comp
      unitBallTensorPressureL).mono_exponent (by norm_num)
  have hPv : MemLp (fun t ↦ (unitBallConvectivePressureCurve u t).val) 1 ν :=
    hP.continuousLinearMap_comp unitBallMeanZeroL2.toSubmodule.subtypeL
  have hPeq : eLpNorm (fun t ↦ (unitBallConvectivePressureCurve u t).val) 1 ν =
      eLpNorm (unitBallConvectivePressureCurve u) 1 ν :=
    eLpNorm_congr_norm_ae hPv.aestronglyMeasurable hP.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ rfl)
  have hh := suitable_fullBall_pressure_cutoff_component_one_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb i hPv
  have hu : AEStronglyMeasurable u ((volume.restrict (vec3Ball 0 1)).prod ν) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hsol.toData.aestronglyMeasurable_velocity hbox
  have hpn := unitBallConvectivePressureCurve_eLpNorm_one_le_six_moment hu
    (suitable_fullBall_source_memLp_six_ae hsol hbox)
  rw [hPeq] at hh
  exact ⟨hh.1, hh.2.trans (mul_le_mul' (mul_le_mul' hpn le_rfl) le_rfl)⟩

end LocalBox

end FluidSingularSets
