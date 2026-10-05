module

public import FluidSingularSets.CKNBridge
public import CKN.Setting.ScalingInvariance
public import CKN.ClassEquivalence.MainTheorems
public import Mathlib.Tactic

/-!
# Epsilon regularity at arbitrary scales

Parabolic scaling transports open neighborhoods, null sets, and Hölder representatives.
This makes the imported unit-cylinder epsilon criterion usable at arbitrary centers.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

noncomputable section

namespace FluidSingularSets

/-- The affine space-time scaling map as a homeomorphism for the parabolic topology. -/
def parabolicScalingHomeomorph (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint) :
    ParabolicPoint ≃ₜ ParabolicPoint :=
  parabolicHomeomorph.trans ((CKN.scalingHomeomorph r hr z₀).trans
    parabolicHomeomorph.symm)

@[simp] theorem parabolicScalingHomeomorph_apply (r : ℝ) (hr : 0 < r)
    (z₀ z : ParabolicPoint) :
    parabolicScalingHomeomorph r hr z₀ z = CKN.scalingParabolic r z₀ z := rfl

/-- Positive parabolic scaling multiplies the parabolic distance by the spatial scale. -/
theorem parabolicDist_scaling {r : ℝ} (hr : 0 < r) (z₀ z w : ParabolicPoint) :
    parabolicDist (CKN.scalingParabolic r z₀ z) (CKN.scalingParabolic r z₀ w) =
      r * parabolicDist z w := by
  have htime : z₀.2 + r ^ 2 * z.2 - (z₀.2 + r ^ 2 * w.2) =
      r ^ 2 * (z.2 - w.2) := by ring
  change max (vec3EuclideanNorm ((z₀.1 + r • z.1) - (z₀.1 + r • w.1)))
    (Real.sqrt |z₀.2 + r ^ 2 * z.2 - (z₀.2 + r ^ 2 * w.2)|) =
      r * max (vec3EuclideanNorm (z.1 - w.1)) (Real.sqrt |z.2 - w.2|)
  rw [add_sub_add_left_eq_sub, ← smul_sub, vec3EuclideanNorm_smul, abs_of_pos hr,
    htime, abs_mul, abs_of_nonneg (sq_nonneg r), Real.sqrt_mul (sq_nonneg r),
    Real.sqrt_sq_eq_abs, abs_of_pos hr]
  exact (mul_max_of_nonneg _ _ hr.le).symm

/-- The scaling homeomorphism changes space-time volume by the homogeneous factor `r⁻⁵`. -/
theorem map_volume_parabolicScalingHomeomorph {r : ℝ} (hr : 0 < r)
    (z₀ : ParabolicPoint) :
    Measure.map (parabolicScalingHomeomorph r hr z₀) volume =
      ENNReal.ofReal (r⁻¹ ^ 5) • (volume : Measure ParabolicPoint) :=
  CKN.map_scalingParabolic r hr z₀

/-- An almost-everywhere rescaled velocity representative gives a representative of the
original velocity on the image neighborhood. -/
theorem ae_eq_unscale_velocity {r : ℝ} (hr : 0 < r) (z₀ : ParabolicPoint)
    {N : Set ParabolicPoint} (hN : MeasurableSet N) {u w : ParabolicPoint → Vec3}
    (hae : w =ᵐ[volume.restrict N] CKN.rescaleVelocity r z₀ u) :
    (fun z ↦ r⁻¹ • w ((parabolicScalingHomeomorph r hr z₀).symm z)) =ᵐ[
      volume.restrict (parabolicScalingHomeomorph r hr z₀ '' N)] u := by
  let H := parabolicScalingHomeomorph r hr z₀
  have hImage : MeasurableSet (H '' N) := H.measurableEmbedding.measurableSet_image.2 hN
  have hmap : Measure.map H (volume.restrict N) =
      ENNReal.ofReal (r⁻¹ ^ 5) • volume.restrict (H '' N) := by
    calc
      _ = Measure.map H (volume.restrict (H ⁻¹' (H '' N))) := by
        rw [H.preimage_image N]
      _ = (Measure.map H volume).restrict (H '' N) :=
        (Measure.restrict_map H.measurable hImage).symm
      _ = _ := by
        rw [map_volume_parabolicScalingHomeomorph hr z₀, Measure.restrict_smul]
  have haemap : (fun z ↦ r⁻¹ • w (H.symm z)) =ᵐ[Measure.map H (volume.restrict N)] u := by
    apply H.measurableEmbedding.ae_map_iff.2
    filter_upwards [hae] with z hz
    rw [H.symm_apply_apply, hz]
    change r⁻¹ • (r • u (H z)) = u (H z)
    simp [smul_smul, hr.ne']
  rw [hmap] at haemap
  exact (ae_ennreal_smul_measure_iff
    (ENNReal.ofReal_ne_zero_iff.2 (pow_pos (inv_pos.2 hr) 5))).1 haemap

/-- An inverse scaling transports the complete bounded parabolic Hölder representative. -/
theorem parabolicHolderVecOn_unscale {r : ℝ} (hr : 0 < r) (z₀ : ParabolicPoint)
    {N : Set ParabolicPoint} {w : ParabolicPoint → Vec3} {γ : ℝ}
    (hw : CKN.ParabolicHolderVecOn N w γ) :
    CKN.ParabolicHolderVecOn (parabolicScalingHomeomorph r hr z₀ '' N)
      (fun z ↦ r⁻¹ • w ((parabolicScalingHomeomorph r hr z₀).symm z)) γ := by
  let H := parabolicScalingHomeomorph r hr z₀
  obtain ⟨B, K, hB, hK, hsup, hholder⟩ := hw
  refine ⟨r⁻¹ * B, r⁻¹ * K * (r⁻¹) ^ γ,
    mul_nonneg (inv_nonneg.2 hr.le) hB,
    mul_nonneg (mul_nonneg (inv_nonneg.2 hr.le) hK)
      (Real.rpow_nonneg (inv_nonneg.2 hr.le) γ), ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change vec3EuclideanNorm (r⁻¹ • w (H.symm (H z))) ≤ r⁻¹ * B
    rw [H.symm_apply_apply, vec3EuclideanNorm_smul, abs_inv, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hsup z hz) (inv_nonneg.2 hr.le)
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨v, hv, rfl⟩
    change vec3EuclideanNorm (r⁻¹ • w (H.symm (H z)) - r⁻¹ • w (H.symm (H v))) ≤
      (r⁻¹ * K * (r⁻¹) ^ γ) * parabolicDist (H z) (H v) ^ γ
    rw [H.symm_apply_apply, H.symm_apply_apply]
    have hdist : parabolicDist z v = r⁻¹ * parabolicDist (H z) (H v) := by
      change parabolicDist z v = r⁻¹ *
        parabolicDist (CKN.scalingParabolic r z₀ z) (CKN.scalingParabolic r z₀ v)
      rw [parabolicDist_scaling hr]
      simp [hr.ne']
    calc
      vec3EuclideanNorm (r⁻¹ • w z - r⁻¹ • w v) =
          r⁻¹ * vec3EuclideanNorm (w z - w v) := by
        rw [← smul_sub, vec3EuclideanNorm_smul, abs_inv, abs_of_pos hr]
      _ ≤ r⁻¹ * (K * parabolicDist z v ^ γ) :=
        mul_le_mul_of_nonneg_left (hholder z hz v hv) (inv_nonneg.2 hr.le)
      _ = (r⁻¹ * K * (r⁻¹) ^ γ) * parabolicDist (H z) (H v) ^ γ := by
        rw [hdist, Real.mul_rpow (inv_nonneg.2 hr.le)
          (by rw [← dist_eq_parabolicDist]; exact dist_nonneg)]
        ring

/-- Local CKN regularity of the rescaled velocity implies local CKN regularity of the
original velocity at the corresponding physical point. -/
theorem isRegularPoint_of_rescaled {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {r : ℝ} (hr : 0 < r) (z₀ z : ParabolicPoint)
    (hreg : CKN.IsRegularPoint (CKN.rescaledSpace r z₀.1 Ω)
      (CKN.rescaledTime r z₀.2 I) (CKN.rescaleVelocity r z₀ u) z) :
    CKN.IsRegularPoint Ω I u (CKN.scalingParabolic r z₀ z) := by
  let H := parabolicScalingHomeomorph r hr z₀
  obtain ⟨hz, N, hNopen, hzN, hNdom, γ, hγ, hγle, w, hae, hholder⟩ := hreg
  rw [CKN.rescaledSpaceTimeSet_eq_preimage] at hz hNdom
  refine ⟨hz, H '' N, H.isOpenMap N hNopen, ⟨z, hzN, rfl⟩, ?_,
    γ, hγ, hγle, (fun a ↦ r⁻¹ • w (H.symm a)), ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact hNdom ha
  · exact ae_eq_unscale_velocity hr z₀ hNopen.measurableSet hae
  · exact parabolicHolderVecOn_unscale hr z₀ hholder

/-- The scaling homeomorphism carries the unit cylinder to the physical cylinder. -/
theorem scalingHomeomorph_image_unitCylinder {r : ℝ} (hr : 0 < r)
    (z₀ : ParabolicPoint) :
    parabolicScalingHomeomorph r hr z₀ '' parabolicCylinder 0 0 1 =
      parabolicCylinder z₀.1 z₀.2 r := by
  change (parabolicTranslate z₀.1 z₀.2 ∘ parabolicScale r) ''
    parabolicCylinder 0 0 1 = _
  rw [Set.image_comp]
  simpa using CKN.Foundation.Parabolic.Integration.parabolicCylinder_rescale_image
    hr z₀.1 z₀.2 1

/-- Containment of the closed physical cylinder supplies the unit-domain hypothesis. -/
theorem closure_unitCylinder_subset_rescaled {Ω : Set Vec3} {I : Set ℝ}
    {r : ℝ} (hr : 0 < r) (z₀ : ParabolicPoint)
    (hdom : closure (parabolicCylinder z₀.1 z₀.2 r) ⊆ CKN.spaceTimeSet Ω I) :
    closure (parabolicCylinder 0 0 1) ⊆
      CKN.spaceTimeSet (CKN.rescaledSpace r z₀.1 Ω) (CKN.rescaledTime r z₀.2 I) := by
  rw [CKN.rescaledSpaceTimeSet_eq_preimage]
  intro z hz
  apply hdom
  rw [← scalingHomeomorph_image_unitCylinder hr z₀,
    ← (parabolicScalingHomeomorph r hr z₀).image_closure]
  exact ⟨z, hz, rfl⟩

/-- The integral appearing in the unit epsilon criterion after scaling a physical cylinder. -/
def scaledUnitL3Charge (q r : ℝ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) : ℝ≥0∞ :=
  ∫⁻ z in parabolicCylinder 0 0 1,
    ENNReal.ofReal (vec3EuclideanNorm (CKN.rescaleVelocity r z₀ u z)) ^ (3 : ℝ) +
      ENNReal.ofReal |CKN.rescalePressure r z₀ p z| ^ (3 / 2 : ℝ) +
      ENNReal.ofReal (vec3EuclideanNorm (CKN.rescaleForce r z₀ f z)) ^ q

/-- The imported unit epsilon theorem gives regularity on every interior scaled half-cylinder,
with a threshold depending only on the force exponent. -/
theorem epsilonRegularityL3_at_scale (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      CKN.IsSuitableWeakSolution Ω I q u Du p f → ∀ {r : ℝ}, 0 < r →
      ∀ z₀ : ParabolicPoint,
      closure (parabolicCylinder z₀.1 z₀.2 r) ⊆ CKN.spaceTimeSet Ω I →
      scaledUnitL3Charge q r z₀ u p f ≤ ENNReal.ofReal ε →
      ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
        CKN.IsRegularPoint Ω I u (CKN.scalingParabolic r z₀ z) := by
  obtain ⟨ε, γ, C₄, hε, _, _, _, hunit⟩ := CKN.epsilonRegularityL3 q hq
  refine ⟨ε, hε, ?_⟩
  intro Ω I u Du p f hsol r hr z₀ hdom hsmall z hz
  have hscaled := CKN.isSuitableWeakSolutionIntegrable_rescale
    (CKN.isSuitableWeakSolution_iff_integrable.1 hsol) z₀ hr
  have hscaledStatement := CKN.isSuitableWeakSolution_iff_integrable.2 hscaled
  obtain ⟨_, _, _, hreg⟩ := hunit _ _ _ _ _ _ hscaledStatement
    (closure_unitCylinder_subset_rescaled hr z₀ hdom) hsmall
  exact isRegularPoint_of_rescaled hr z₀ z (hreg z hz)

/-- Change of variables for an arbitrary nonnegative density on the scaled unit cylinder. -/
theorem lintegral_unitCylinder_comp_scaling {r : ℝ} (hr : 0 < r)
    (z₀ : ParabolicPoint) (F : ParabolicPoint → ℝ≥0∞) :
    (∫⁻ z in parabolicCylinder 0 0 1, F (CKN.scalingParabolic r z₀ z)) =
      ENNReal.ofReal (r⁻¹ ^ 5) * ∫⁻ z in parabolicCylinder z₀.1 z₀.2 r, F z := by
  let H := parabolicScalingHomeomorph r hr z₀
  let N := parabolicCylinder 0 0 1
  have hN : MeasurableSet N := by
    exact measurableSet_parabolicCylinder _ _ _
  have hImage : MeasurableSet (H '' N) := H.measurableEmbedding.measurableSet_image.2 hN
  have hmap : Measure.map H (volume.restrict N) =
      ENNReal.ofReal (r⁻¹ ^ 5) • volume.restrict (parabolicCylinder z₀.1 z₀.2 r) := by
    calc
      _ = Measure.map H (volume.restrict (H ⁻¹' (H '' N))) := by rw [H.preimage_image N]
      _ = (Measure.map H volume).restrict (H '' N) :=
        (Measure.restrict_map H.measurable hImage).symm
      _ = _ := by
        rw [map_volume_parabolicScalingHomeomorph hr z₀, Measure.restrict_smul,
          scalingHomeomorph_image_unitCylinder hr z₀]
  calc
    _ = ∫⁻ z, F z ∂Measure.map H (volume.restrict N) :=
      (H.measurableEmbedding.lintegral_map F).symm
    _ = _ := by rw [hmap, lintegral_smul_measure]; rfl

/-- Both velocity cubed and pressure to the power `3/2` scale by the same third power. -/
theorem rescaled_l3_density {r : ℝ} (hr : 0 < r) (z₀ z : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) :
    ENNReal.ofReal (vec3EuclideanNorm (CKN.rescaleVelocity r z₀ u z)) ^ (3 : ℝ) +
      ENNReal.ofReal |CKN.rescalePressure r z₀ p z| ^ (3 / 2 : ℝ) =
    ENNReal.ofReal (r ^ 3) *
      (ENNReal.ofReal (vec3EuclideanNorm (u (CKN.scalingParabolic r z₀ z))) ^ (3 : ℝ) +
        ENNReal.ofReal |p (CKN.scalingParabolic r z₀ z)| ^ (3 / 2 : ℝ)) := by
  have hv : ENNReal.ofReal
      (vec3EuclideanNorm (CKN.rescaleVelocity r z₀ u z)) ^ (3 : ℝ) =
      ENNReal.ofReal (r ^ 3) *
        ENNReal.ofReal (vec3EuclideanNorm (u (CKN.scalingParabolic r z₀ z))) ^ (3 : ℝ) := by
    change ENNReal.ofReal (vec3EuclideanNorm (r • u (CKN.scalingParabolic r z₀ z))) ^
      (3 : ℝ) = _
    rw [vec3EuclideanNorm_smul, abs_of_pos hr, ENNReal.ofReal_mul hr.le,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_pow hr.le]
    norm_num
  have hp : ENNReal.ofReal |CKN.rescalePressure r z₀ p z| ^ (3 / 2 : ℝ) =
      ENNReal.ofReal (r ^ 3) *
        ENNReal.ofReal |p (CKN.scalingParabolic r z₀ z)| ^ (3 / 2 : ℝ) := by
    change ENNReal.ofReal |r ^ 2 * p (CKN.scalingParabolic r z₀ z)| ^ (3 / 2 : ℝ) = _
    rw [abs_mul, abs_of_nonneg (sq_nonneg r), ENNReal.ofReal_mul (sq_nonneg r),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_pow hr.le,
      ENNReal.ofReal_pow hr.le]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hv, hp, mul_add]

/-- For zero force, the rescaled unit charge is exactly the physical dimensionless cubic
velocity-pressure charge. This identity does not require any integrability assumption. -/
theorem scaledUnitL3Charge_zero_force {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (z₀ : ParabolicPoint) (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) :
    scaledUnitL3Charge q r z₀ u p (fun _ ↦ 0) =
      ENNReal.ofReal (r⁻¹ ^ 2) * ∫⁻ z in parabolicCylinder z₀.1 z₀.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) := by
  have hcoef : ENNReal.ofReal (r ^ 3) * ENNReal.ofReal (r⁻¹ ^ 5) =
      ENNReal.ofReal (r⁻¹ ^ 2) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hr.le 3)]
    congr 1
    field_simp [hr.ne']
  unfold scaledUnitL3Charge
  simp only [CKN.rescaleForce, smul_zero, vec3EuclideanNorm_zero, ENNReal.ofReal_zero,
    ENNReal.zero_rpow_of_pos hq, add_zero]
  simp_rw [rescaled_l3_density hr z₀]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hchange := lintegral_unitCylinder_comp_scaling hr z₀
    (fun z ↦ ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
      ENNReal.ofReal |p z| ^ (3 / 2 : ℝ))
  rw [hchange, ← mul_assoc, hcoef]

/-- Raising the top of the backward cylinder makes its original center an interior point. -/
def shiftedCylinderTop (z : ParabolicPoint) (r : ℝ) : ParabolicPoint :=
  (z.1, z.2 + r ^ 2 / 8)

@[simp] theorem scaling_shiftedCylinderTop (z : ParabolicPoint) (r : ℝ) :
    CKN.scalingParabolic r (shiftedCylinderTop z r) ((0 : Vec3), (-1 / 8 : ℝ)) = z := by
  cases z with
  | mk x t =>
    apply Prod.ext
    · simp [CKN.scalingParabolic, parabolicTranslate, parabolicScale, shiftedCylinderTop]
    · change t + r ^ 2 / 8 + r ^ 2 * (-1 / 8) = t
      ring

/-- The fixed reference point used for the shifted cylinder lies strictly inside the
half-cylinder where CKN supplies a full open regular neighborhood. -/
theorem shifted_referencePoint_mem_halfCylinder :
    ((0 : Vec3), (-1 / 8 : ℝ)) ∈
      vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0 := by
  constructor
  · change vec3EuclideanNorm (0 - 0) < 1 / 2
    rw [sub_zero, vec3EuclideanNorm_zero]
    norm_num
  · norm_num

/-- Arbitrary-scale epsilon regularity for unforced suitable weak solutions, with the point
of interest strictly inside a time-shifted backward cylinder. -/
theorem epsilonRegularityL3_unforced_shifted (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ},
      CKN.IsSuitableWeakSolution Ω I q u Du p (fun _ ↦ 0) →
      ∀ (z : ParabolicPoint) {r : ℝ}, 0 < r →
      closure (parabolicCylinder z.1 (z.2 + r ^ 2 / 8) r) ⊆ CKN.spaceTimeSet Ω I →
      ENNReal.ofReal (r⁻¹ ^ 2) *
        (∫⁻ a in parabolicCylinder z.1 (z.2 + r ^ 2 / 8) r,
          ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
            ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)) ≤ ENNReal.ofReal ε →
      CKN.IsRegularPoint Ω I u z := by
  obtain ⟨ε, hε, hcriterion⟩ := epsilonRegularityL3_at_scale q hq
  refine ⟨ε, hε, ?_⟩
  intro Ω I u Du p hsol z r hr hdom hsmall
  have hcharge : scaledUnitL3Charge q r (shiftedCylinderTop z r) u p (fun _ ↦ 0) ≤
      ENNReal.ofReal ε := by
    rw [scaledUnitL3Charge_zero_force (by linarith : 0 < q) hr]
    exact hsmall
  have hreg := hcriterion hsol hr (shiftedCylinderTop z r) hdom hcharge
    ((0 : Vec3), (-1 / 8 : ℝ)) shifted_referencePoint_mem_halfCylinder
  simpa only [scaling_shiftedCylinderTop] using hreg

/-- The cubic velocity-pressure integral agrees in the raw CKN and independent Euclidean
coordinates, at every center and radius. -/
theorem velocity_pressure_integral_transport
    (u : SpaceTime → Space) (p : SpaceTime → ℝ) (z₀ : ParabolicPoint) (r : ℝ) :
    (∫⁻ z in parabolicCylinder z₀.1 z₀.2 r,
      ENNReal.ofReal (vec3EuclideanNorm (CKNChallenge.pullVelocity u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |CKNChallenge.pullScalar p z| ^ (3 / 2 : ℝ)) =
    ∫⁻ z in CKNChallenge.Q r (CKNChallenge.parabolicToEuclideanHomeomorph z₀),
      ‖u z‖ₑ ^ (3 : ℝ) + ‖p z‖ₑ ^ (3 / 2 : ℝ) := by
  let H := CKNChallenge.parabolicToEuclideanHomeomorph
  have hpre : H ⁻¹' CKNChallenge.Q r (H z₀) = parabolicCylinder z₀.1 z₀.2 r := by
    change CKNChallenge.rawSpaceTimeToEuclidean ⁻¹'
      CKNChallenge.Q r (H z₀) = _
    rw [CKNChallenge.rawSpaceTime_preimage_Q]
    change parabolicCylinder
      (CKNChallenge.rawToEuclidean.symm (CKNChallenge.rawToEuclidean z₀.1)) z₀.2 r = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have hmp := CKNChallenge.parabolicToEuclidean_measurePreserving.restrict_preimage_emb
    H.measurableEmbedding (CKNChallenge.Q r (H z₀))
  have hchange := hmp.lintegral_comp_emb H.measurableEmbedding
    (fun z ↦ ‖u z‖ₑ ^ (3 : ℝ) + ‖p z‖ₑ ^ (3 / 2 : ℝ))
  rw [hpre] at hchange
  calc
    _ = ∫⁻ z in parabolicCylinder z₀.1 z₀.2 r,
        ‖u (H z)‖ₑ ^ (3 : ℝ) + ‖p (H z)‖ₑ ^ (3 / 2 : ℝ) := by
      apply lintegral_congr
      intro z
      simp only [CKNChallenge.pullVelocity, CKNChallenge.pullScalar,
        CKNChallenge.vec3EuclideanNorm_rawToEuclidean_symm, Real.norm_eq_abs,
        ← ofReal_norm]
      rfl
    _ = _ := hchange

/-- Epsilon smallness of the physical shifted-cylinder charge gives the independently
specified local Hölder regularity predicate, for every center and scale. -/
theorem holderRegularityL3_unforced_shifted (q : ℝ≥0) (hq : 5 / 2 < (q : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {Ω : Set Space} {I : Set ℝ}
      (sol : CKNChallenge.LocalWeakNSESolution Ω I q), (∀ z, sol.f z = 0) →
      ∀ (z : SpaceTime) {r : ℝ}, 0 < r →
      closure (CKNChallenge.Q r (z.1, z.2 + r ^ 2 / 8)) ⊆ Ω ×ˢ I →
      ENNReal.ofReal (r⁻¹ ^ 2) *
        (∫⁻ a in CKNChallenge.Q r (z.1, z.2 + r ^ 2 / 8),
          ‖sol.u a‖ₑ ^ (3 : ℝ) + ‖sol.p a‖ₑ ^ (3 / 2 : ℝ)) ≤ ENNReal.ofReal ε →
      CKNChallenge.IsHolderRegularPoint sol.u z := by
  obtain ⟨ε, hε, hcriterion⟩ := epsilonRegularityL3_unforced_shifted (q : ℝ) hq
  refine ⟨ε, hε, ?_⟩
  intro Ω I sol hf z r hr hdom hsmall
  let ζ := CKNChallenge.parabolicToEuclideanHomeomorph.symm z
  have hζ : CKNChallenge.parabolicToEuclideanHomeomorph ζ = z :=
    CKNChallenge.parabolicToEuclideanHomeomorph.apply_symm_apply z
  have htop : CKNChallenge.parabolicToEuclideanHomeomorph (shiftedCylinderTop ζ r) =
      (z.1, z.2 + r ^ 2 / 8) := by
    apply Prod.ext
    · change CKNChallenge.rawToEuclidean ζ.1 = z.1
      exact congrArg Prod.fst hζ
    · change ζ.2 + r ^ 2 / 8 = z.2 + r ^ 2 / 8
      exact congrArg (fun t ↦ t + r ^ 2 / 8) (congrArg Prod.snd hζ)
  have hrawdom : closure (parabolicCylinder ζ.1 (ζ.2 + r ^ 2 / 8) r) ⊆
      CKN.spaceTimeSet (CKNChallenge.rawSpace Ω) I := by
    intro a ha
    have haphys := (CKNChallenge.mem_closure_cylinder_iff_mem_closure_Q hr
      (shiftedCylinderTop ζ r) a).1 ha
    have htop' : (CKNChallenge.rawToEuclidean ζ.1, ζ.2 + r ^ 2 / 8) =
        (z.1, z.2 + r ^ 2 / 8) := htop
    change CKNChallenge.rawSpaceTimeToEuclidean a ∈
      closure (CKNChallenge.Q r (CKNChallenge.rawToEuclidean ζ.1, ζ.2 + r ^ 2 / 8))
      at haphys
    rw [htop'] at haphys
    exact hdom haphys
  have hrawsmall : ENNReal.ofReal (r⁻¹ ^ 2) *
      (∫⁻ a in parabolicCylinder ζ.1 (ζ.2 + r ^ 2 / 8) r,
        ENNReal.ofReal (vec3EuclideanNorm (CKNChallenge.pullVelocity sol.u a)) ^ (3 : ℝ) +
          ENNReal.ofReal |CKNChallenge.pullScalar sol.p a| ^ (3 / 2 : ℝ)) ≤
        ENNReal.ofReal ε := by
    calc
      _ = ENNReal.ofReal (r⁻¹ ^ 2) *
          ∫⁻ a in CKNChallenge.Q r
              (CKNChallenge.parabolicToEuclideanHomeomorph (shiftedCylinderTop ζ r)),
            ‖sol.u a‖ₑ ^ (3 : ℝ) + ‖sol.p a‖ₑ ^ (3 / 2 : ℝ) :=
        congrArg (fun a ↦ ENNReal.ofReal (r⁻¹ ^ 2) * a)
          (velocity_pressure_integral_transport sol.u sol.p (shiftedCylinderTop ζ r) r)
      _ ≤ ENNReal.ofReal ε := by rw [htop]; exact hsmall
  have hraw := CKNChallenge.rawSuitableWeakSolution hq sol
  have hforce : CKNChallenge.pullVelocity sol.f = fun _ ↦ 0 := by
    funext a
    simp [CKNChallenge.pullVelocity, hf]
  rw [hforce] at hraw
  have hreg := hcriterion hraw ζ hr hrawdom hrawsmall
  have hnew := CKNChallenge.isHolderRegularPoint_of_rawRegular hreg
  rwa [hζ] at hnew

/-- The positive epsilon threshold becomes a strict charge lower bound at every singular
point, whenever the shifted cylinder is contained in the solution domain. -/
theorem singular_shifted_l3_charge_lower_bound (q : ℝ≥0) (hq : 5 / 2 < (q : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {Ω : Set Space} {I : Set ℝ}
      (sol : CKNChallenge.LocalWeakNSESolution Ω I q), (∀ z, sol.f z = 0) →
      ∀ (z : SpaceTime), ¬CKNChallenge.IsHolderRegularPoint sol.u z →
      ∀ {r : ℝ}, 0 < r →
      closure (CKNChallenge.Q r (z.1, z.2 + r ^ 2 / 8)) ⊆ Ω ×ˢ I →
      ENNReal.ofReal ε < ENNReal.ofReal (r⁻¹ ^ 2) *
        ∫⁻ a in CKNChallenge.Q r (z.1, z.2 + r ^ 2 / 8),
          ‖sol.u a‖ₑ ^ (3 : ℝ) + ‖sol.p a‖ₑ ^ (3 / 2 : ℝ) := by
  obtain ⟨ε, hε, hcriterion⟩ := holderRegularityL3_unforced_shifted q hq
  refine ⟨ε, hε, ?_⟩
  intro Ω I sol hf z hsing r hr hdom
  by_contra hcharge
  exact hsing (hcriterion sol hf z hr hdom (le_of_not_gt hcharge))

/-- A symmetric parabolic cylinder in the physical Euclidean coordinates. -/
def symmetricL3Cylinder (z : SpaceTime) (r : ℝ) : Set SpaceTime :=
  Metric.ball z.1 r ×ˢ Ioo (z.2 - r ^ 2) (z.2 + r ^ 2)

/-- The time-shifted backward cylinder lies inside the symmetric cylinder of the same radius. -/
theorem shiftedCylinder_subset_symmetric (z : SpaceTime) {r : ℝ} (hr : 0 < r) :
    CKNChallenge.Q r (z.1, z.2 + r ^ 2 / 8) ⊆ symmetricL3Cylinder z r := by
  rintro a ⟨hx, htlow, hthigh⟩
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  refine ⟨hx, ?_, ?_⟩ <;> dsimp at * <;> nlinarith [hr2]

/-- The singular-point charge lower bound also holds on symmetric cylinders. -/
theorem singular_symmetric_l3_charge_lower_bound (q : ℝ≥0) (hq : 5 / 2 < (q : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {Ω : Set Space} {I : Set ℝ}
      (sol : CKNChallenge.LocalWeakNSESolution Ω I q), (∀ z, sol.f z = 0) →
      ∀ (z : SpaceTime), ¬CKNChallenge.IsHolderRegularPoint sol.u z →
      ∀ {r : ℝ}, 0 < r → closure (symmetricL3Cylinder z r) ⊆ Ω ×ˢ I →
      ENNReal.ofReal ε < ENNReal.ofReal (r⁻¹ ^ 2) *
        ∫⁻ a in symmetricL3Cylinder z r,
          ‖sol.u a‖ₑ ^ (3 : ℝ) + ‖sol.p a‖ₑ ^ (3 / 2 : ℝ) := by
  obtain ⟨ε, hε, hcriterion⟩ := singular_shifted_l3_charge_lower_bound q hq
  refine ⟨ε, hε, ?_⟩
  intro Ω I sol hf z hsing r hr hdom
  have hsub := shiftedCylinder_subset_symmetric z hr
  exact (hcriterion sol hf z hsing hr ((closure_mono hsub).trans hdom)).trans_le
    (mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) bot_le)

/-- At radii at most one, the closure of a symmetric cylinder lies in the ordinary closed
space-time ball of its spatial radius. -/
theorem closure_symmetricCylinder_subset_closedBall (z : SpaceTime) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    closure (symmetricL3Cylinder z r) ⊆ Metric.closedBall z r := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  rintro a ⟨hx, htlow, hthigh⟩
  rw [Metric.mem_closedBall, Prod.dist_eq]
  apply max_le
  · exact (Metric.mem_ball.1 hx).le
  · have ht : |a.2 - z.2| ≤ r ^ 2 := abs_le.2 ⟨by linarith, by linarith⟩
    rw [Real.dist_eq]
    exact ht.trans (by nlinarith)

/-- Every interior point has a positive radius on which all closed symmetric cylinders
remain inside the open solution domain. -/
theorem exists_symmetricCylinder_domain_radius {Ω : Set Space} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) {z : SpaceTime} (hz : z ∈ Ω ×ˢ I) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      closure (symmetricL3Cylinder z r) ⊆ Ω ×ˢ I := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hΩ.prod hI) z hz
  refine ⟨min 1 (δ / 2), lt_min (by norm_num) (by positivity), ?_⟩
  intro r hr hrR
  have hr1 : r ≤ 1 := hrR.trans (min_le_left _ _)
  have hrδ : r < δ := lt_of_le_of_lt (hrR.trans (min_le_right _ _)) (by linarith)
  exact ((closure_symmetricCylinder_subset_closedBall z hr hr1).trans
    (Metric.closedBall_subset_ball hrδ)).trans hball

/-- Every singular point of an unforced suitable weak solution has uniformly positive
dimensionless velocity-pressure charge at every sufficiently small scale. -/
theorem singular_symmetric_l3_charge_eventually (q : ℝ≥0) (hq : 5 / 2 < (q : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {Ω : Set Space} {I : Set ℝ}
      (sol : CKNChallenge.LocalWeakNSESolution Ω I q), (∀ z, sol.f z = 0) →
      ∀ z ∈ CKNChallenge.singularSet Ω I sol.u,
      ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
        ENNReal.ofReal ε < ENNReal.ofReal (r⁻¹ ^ 2) *
          ∫⁻ a in symmetricL3Cylinder z r,
            ‖sol.u a‖ₑ ^ (3 : ℝ) + ‖sol.p a‖ₑ ^ (3 / 2 : ℝ) := by
  obtain ⟨ε, hε, hcriterion⟩ := singular_symmetric_l3_charge_lower_bound q hq
  refine ⟨ε, hε, ?_⟩
  intro Ω I sol hf z hz
  obtain ⟨hzdom, hzsing⟩ := hz
  obtain ⟨R, hR, hdom⟩ := exists_symmetricCylinder_domain_radius
    sol.isOpenSpace sol.isOpenTime hzdom
  exact ⟨R, hR, fun r hr hrR ↦ hcriterion sol hf z hzsing hr (hdom r hr hrR)⟩

end FluidSingularSets
