-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallPressureMeanPairings

/-!
# Actual pressure tests depending jointly on space and time

The common divergence and projected-pressure identities apply to the genuine
spatial slice of every joint smooth compact test. Thus arbitrary time-dependent
spatial pressure means cancel also for backward heat-kernel tests.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal genuine spatial weak test at one time of a joint compact smooth test. -/
def fullBallJointSpatialTest {B : Set Vec3} (ψ : Vec3 × ℝ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : ∀ z ∈ tsupport ψ, z.1 ∈ B) (t : ℝ) : WeakTestFunction B where
  toFun := fun x ↦ ψ (x, t)
  contDiff := hψ.comp (contDiff_id.prodMk contDiff_const)
  hasCompactSupport := HasCompactSupport.intro (hcψ.image continuous_fst) fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx ⟨(x, t), h, rfl⟩
  tsupport_subset := fun x hx ↦ hsψ (x, t)
    ((tsupport_comp_subset_preimage ψ (continuous_id.prodMk continuous_const)) hx)

/-- The true joint-test projected velocity flux, with an arbitrary scalar time multiplier. -/
def fullBallJointProjectedPressureTest
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ) (χ : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  χ z.2 * ∑ i : Fin 3, fullBallProjectedVelocityAmbient u D p a b c z i *
    spatialPartial ψ i z

section LocalBox

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3}

/-- Common suitable divergence cancels every actual joint-test spatial flux. -/
theorem fullBallJointProjectedPressureTest_spatial_integral_zero_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : ∀ z ∈ tsupport ψ, z.1 ∈ B) (χ : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫ x in B, fullBallJointProjectedPressureTest u D p a b c ψ χ (x, t)) = 0 := by
  filter_upwards [fullBallProjectedVelocityAmbient_divergenceFree_slices_ae
    u D p a b c hsol hbox hρ hρone hB hBK] with t ht
  change (∫ x in B, χ t * ∑ i : Fin 3,
    fullBallProjectedVelocityAmbient u D p a b c (x, t) i * spatialPartial ψ i (x, t)) = 0
  rw [integral_const_mul]
  have hz := ht (fullBallJointSpatialTest ψ hψ hcψ hsψ t)
  change (∫ x in B, ∑ i : Fin 3,
    fullBallProjectedVelocityAmbient u D p a b c (x, t) i * spatialPartial ψ i (x, t)) = 0 at hz
  rw [hz, mul_zero]

/-- The actual joint pressure test belongs to spatial L² on one full suitable time set. -/
theorem fullBallJointProjectedPressureTest_memLp_two_slices_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : ∀ z ∈ tsupport ψ, z.1 ∈ B) (χ : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      MemLp (fun x ↦ fullBallJointProjectedPressureTest u D p a b c ψ χ (x, t)) 2
        (volume.restrict B) := by
  filter_upwards [fullBallProjectedVelocityAmbient_weak_gradient_slices_ae
    u D p a b c hsol hbox hρ hρone hB hBK] with t ht
  let φ := fullBallJointSpatialTest ψ hψ hcψ hsψ t
  have hd (i : Fin 3) : MemLp (fun x ↦ spatialPartial ψ i (x, t)) ⊤ (volume.restrict B) :=
    ((stokesWeakTestDerivative φ i).contDiff.continuous.memLp_of_hasCompactSupport
      (stokesWeakTestDerivative φ i).hasCompactSupport).restrict B
  exact (memLp_finsetSum Finset.univ (fun i _ ↦ (ht.1.eval i).mul (hd i))).const_mul (χ t)

/-- Genuine joint-test pressure pairings equal the actual two Stokes oscillation pairings.
Both subtracted spatial means may depend arbitrarily on time. -/
theorem suitable_fullBall_joint_pressure_pairing_eq_centered_stokes_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : ∀ z ∈ tsupport ψ, z.1 ∈ B) (χ m₁ m₂ : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫ x in B, (p (x, t) - fullBallProjectedMomentumPressure u D p t x) *
        fullBallJointProjectedPressureTest u D p a b c ψ χ (x, t)) =
      (∫ x in B, ((unitBallConvectivePressureCurve u t).val x - m₁ t) *
        fullBallJointProjectedPressureTest u D p a b c ψ χ (x, t)) +
      (∫ x in B, ((unitBallViscousPressureCurve D t).val x - m₂ t) *
        fullBallJointProjectedPressureTest u D p a b c ψ χ (x, t)) := by
  have hB1 := hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr
    ((measure_mono hB1).trans_lt volume_vec3Ball_lt_top).ne
  filter_upwards [suitable_fullBall_projected_pressure_identification_ae_localBox hsol hbox,
    fullBallJointProjectedPressureTest_memLp_two_slices_ae
      (c := c) hsol hbox hρ hρone hB hBK hψ hcψ hsψ χ,
    fullBallJointProjectedPressureTest_spatial_integral_zero_ae
      (c := c) hsol hbox hρ hρone hB hBK hψ hcψ hsψ χ] with t hp ht hz
  let G : Vec3 → ℝ := fun x ↦ fullBallJointProjectedPressureTest u D p a b c ψ χ (x, t)
  let m : ℝ := average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t)) + m₁ t + m₂ t
  have hP1 := (((Lp.memLp (unitBallConvectivePressureCurve u t).val).mono_measure
    (Measure.restrict_mono_set volume hB1)).sub (memLp_const (m₁ t))).integrable_mul ht
  have hP2 := (((Lp.memLp (unitBallViscousPressureCurve D t).val).mono_measure
    (Measure.restrict_mono_set volume hB1)).sub (memLp_const (m₂ t))).integrable_mul ht
  change Integrable (fun x ↦ ((unitBallConvectivePressureCurve u t).val x - m₁ t) * G x)
    (volume.restrict B) at hP1
  change Integrable (fun x ↦ ((unitBallViscousPressureCurve D t).val x - m₂ t) * G x)
    (volume.restrict B) at hP2
  have hm : Integrable (fun x ↦ m * G x) (volume.restrict B) :=
    (ht.integrable (by norm_num)).const_mul m
  calc
    _ = ∫ x in B, (((unitBallConvectivePressureCurve u t).val x - m₁ t) +
        ((unitBallViscousPressureCurve D t).val x - m₂ t) + m) * G x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hB1 hp] with x hx
      change (p (x, t) - fullBallProjectedMomentumPressure u D p t x) * G x = _
      rw [hx]
      dsimp only [m]
      ring
    _ = _ := by
      simp_rw [add_mul]
      have hmean : (∫ x in B, m * G x) = 0 := by
        calc
          _ = m * ∫ x in B, G x := integral_const_mul _ _
          _ = 0 := by simpa only [mul_zero] using congrArg (fun r : ℝ ↦ m * r) hz
      exact (integral_add (hP1.add hP2) hm).trans
        ((congrArg₂ (fun r s : ℝ ↦ r + s) (integral_add hP1 hP2) hmean).trans (add_zero _))

/-- The genuine time-integrated joint pressure pairing has the same centered Stokes form. -/
theorem suitable_fullBall_joint_pressure_iterated_pairing_eq_centered_stokes
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : ∀ z ∈ tsupport ψ, z.1 ∈ B) (χ m₁ m₂ : ℝ → ℝ) :
    (∫ t in Ioo a b, ∫ x in B, (p (x, t) - fullBallProjectedMomentumPressure u D p t x) *
      fullBallJointProjectedPressureTest u D p a b c ψ χ (x, t)) =
    ∫ t in Ioo a b,
      (∫ x in B, ((unitBallConvectivePressureCurve u t).val x - m₁ t) *
        fullBallJointProjectedPressureTest u D p a b c ψ χ (x, t)) +
      (∫ x in B, ((unitBallViscousPressureCurve D t).val x - m₂ t) *
        fullBallJointProjectedPressureTest u D p a b c ψ χ (x, t)) :=
  integral_congr_ae (suitable_fullBall_joint_pressure_pairing_eq_centered_stokes_ae
    hsol hbox hρ hρone hB hBK hψ hcψ hsψ χ m₁ m₂)

end LocalBox

end FluidSingularSets
