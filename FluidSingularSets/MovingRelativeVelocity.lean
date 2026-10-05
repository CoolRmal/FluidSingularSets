-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.NormalizedWeightedCutoff
public import FluidSingularSets.AcceleratedData

/-!
# Actual mixed velocity control in a moving cylinder

Volume-preserving spatial translation and restriction transfer the genuine
normalized-weight Sobolev-Poincaré estimate to the actual relative velocity.
This estimate uses suitability on the original fixed box.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Core.Step4 CKN.Leray
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Translation preserves the spatial seminorm on the exact translated set,
including for a function before a measurable representative is selected. -/
theorem eLpNorm_spatialTranslation_restrict
    {E : Type*} [NormedAddCommGroup E] (a : Vec3) (B : Set Vec3)
    (v : Vec3 → E) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ v (a + x)) p (volume.restrict B) =
      eLpNorm v p (volume.restrict ((fun x ↦ a + x) '' B)) := by
  have hmap := (spatialTranslation_restrict_measurePreserving a B).map_eq
  have hemb : MeasurableEmbedding (fun x : Vec3 ↦ a + x) :=
    (Homeomorph.addLeft a).measurableEmbedding
  rw [← hmap]
  exact hemb.eLpNorm_map_measure.symm

/-- Translating and restricting a relative velocity slice increases no mixed
spatial seminorm when the translated set lies in the source ball. -/
theorem accelerated_relativeVelocity_slice_eLpNorm_le
    (X m : ℝ → Vec3) (u : ParabolicPoint → Vec3) (B A : Set Vec3) (t : ℝ)
    (hspace : (fun x : Vec3 ↦ X t + x) '' B ⊆ A) :
    eLpNorm (fun x ↦ vec3EuclideanNorm (acceleratedVelocity X m u (x, t))) 6
      (volume.restrict B) ≤
        eLpNorm (fun x ↦ vec3EuclideanNorm (u (x, t) - m t)) 6 (volume.restrict A) := by
  change eLpNorm (fun x ↦ vec3EuclideanNorm (u (X t + x, t) - m t)) 6 _ ≤ _
  have htrans := eLpNorm_spatialTranslation_restrict (X t) B
    (fun x : Vec3 ↦ vec3EuclideanNorm (u (x, t) - m t)) 6
  exact htrans.trans_le (eLpNorm_mono_measure _ (Measure.restrict_mono hspace le_rfl))

/-- Actual suitability and the normalized weighted mean control the moving
relative velocity by the original integrated weak-gradient energy. -/
theorem suitable_moving_relativeVelocity_mixed_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (J J₀ : Set ℝ)
    (hbox : localBox Ω I (vec3Ball x₀ (2 * R)) J₀)
    (hJ : MeasurableSet J) (htime : J ⊆ J₀)
    (X m : ℝ → Vec3) (S : Set Vec3)
    (hspace : ∀ t ∈ J, (fun x : Vec3 ↦ X t + x) '' S ⊆ vec3Ball x₀ (2 * R))
    (hmean : ∀ᵐ t ∂volume.restrict J,
      m t = fun i ↦ weightedVelocityMean (vec3Ball x₀ R)
        (normalizedWeightedCutoff x₀ hR) u i t) :
    (∫⁻ t in J, eLpNorm (fun x ↦
      vec3EuclideanNorm (acceleratedVelocity X m u (x, t))) 6
        (volume.restrict S) ^ (2 : ℝ)) ≤
      weightedVelocityEuclideanPoincareConstant 64 ^ (2 : ℝ) *
        ∫⁻ z in spaceTimeSet (vec3Ball x₀ (2 * R)) J₀, ‖D z‖ₑ ^ (2 : ℝ) := by
  have hfixed := suitable_normalizedWeightedCutoff_mixed_sobolevPoincare hsol x₀ hR J₀ hbox
  have hrestrict := lintegral_mono_set (μ := (volume : Measure ℝ))
    (f := fun t : ℝ ↦ eLpNorm (fun x ↦ vec3EuclideanNorm (fun i : Fin 3 ↦
      u (x, t) i - weightedVelocityMean (vec3Ball x₀ R)
        (normalizedWeightedCutoff x₀ hR) u i t)) 6
          (volume.restrict (vec3Ball x₀ (2 * R))) ^ (2 : ℝ)) htime
  apply le_trans (lintegral_mono_ae ?_) (hrestrict.trans hfixed)
  filter_upwards [hmean, ae_restrict_mem hJ] with t ht htJ
  have hslice := accelerated_relativeVelocity_slice_eLpNorm_le X m u S
    (vec3Ball x₀ (2 * R)) t (hspace t htJ)
  rw [ht] at hslice
  convert ENNReal.rpow_le_rpow hslice (by norm_num : 0 ≤ (2 : ℝ)) using 1

/-- Actual local energy gives the finite squared-gradient moment on a fixed box. -/
theorem suitable_box_gradient_memLp_two
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (hbox : localBox Ω I B J) :
    MemLp D 2 (volume.restrict (spaceTimeSet B J)) := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (hsol.toData.aestronglyMeasurable_gradient hbox)]
  simp only [ENNReal.toReal_ofNat]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  exact ((lintegral_mono fun _ ↦ le_add_of_nonneg_left (by positivity)).trans_lt
    (hsol.toData.energy_lintegral_lt_top hbox)).ne

/-- The genuine charge is integrable once its actual local moments are given. -/
theorem meanMotionCharge_integrable_of_moments
    {Q : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    {D : ParabolicPoint → Fin 3 → Vec3} {Dp : ParabolicPoint → Vec3}
    (hu : MemLp u (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict Q))
    (hD : MemLp D 2 (volume.restrict Q))
    (hDp : MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict Q)) :
    IntegrableOn (fun w ↦ ‖D w‖ ^ (2 : ℝ) + ‖u w‖ ^ (10 / 3 : ℝ) +
      ‖Dp w‖ ^ (5 / 4 : ℝ)) Q := by
  have huInt : Integrable (fun w ↦ ‖u w‖ ^ (10 / 3 : ℝ)) (volume.restrict Q) := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 10 / 3)] using
      hu.integrable_norm_rpow (by norm_num) ENNReal.ofReal_ne_top
  have hDInt : Integrable (fun w ↦ ‖D w‖ ^ (2 : ℝ)) (volume.restrict Q) := by
    simpa only [ENNReal.toReal_ofNat] using hD.integrable_norm_rpow (by norm_num) (by norm_num)
  have hDpInt : Integrable (fun w ↦ ‖Dp w‖ ^ (5 / 4 : ℝ)) (volume.restrict Q) := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 5 / 4)] using
      hDp.integrable_norm_rpow (by norm_num) ENNReal.ofReal_ne_top
  exact (hDInt.add huInt).add hDpInt

/-- The extended gradient energy is bounded by the finite actual real charge. -/
theorem gradient_lintegral_le_meanMotionCharge
    {Q : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    {D : ParabolicPoint → Fin 3 → Vec3} {Dp : ParabolicPoint → Vec3}
    (hu : MemLp u (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict Q))
    (hD : MemLp D 2 (volume.restrict Q))
    (hDp : MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict Q)) :
    (∫⁻ w in Q, ‖D w‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal (meanMotionCharge Q u D Dp) := by
  unfold meanMotionCharge
  rw [ofReal_integral_eq_lintegral_ofReal
    (meanMotionCharge_integrable_of_moments hu hD hDp)
    (Eventually.of_forall fun _ ↦ by positivity)]
  apply lintegral_mono
  intro w
  dsimp only
  rw [← ofReal_norm (D w), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hu0 := Real.rpow_nonneg (norm_nonneg (u w)) (10 / 3 : ℝ)
  have hp0 := Real.rpow_nonneg (norm_nonneg (Dp w)) (5 / 4 : ℝ)
  linarith

/-- The scale-invariant squared `L²_t L⁶_x` cost of the actual relative velocity. -/
def movingRelativeVelocityCost (X m : ℝ → Vec3) (u : ParabolicPoint → Vec3)
    (r : ℝ) (J : Set ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r)⁻¹ *
    ∫⁻ t in J, eLpNorm (fun x ↦
      vec3EuclideanNorm (acceleratedVelocity X m u (x, t))) 6
        (volume.restrict (vec3Ball 0 r)) ^ (2 : ℝ)

/-- The normalized moving cost is controlled by the genuine three-term real
charge. The pressure-gradient moment here is the local input constructed from
suitability by `PressureGradientFiveFourths` and `MeanMotionBound`. -/
theorem suitable_moving_relativeVelocity_cost_le_charge
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x₀ : Vec3) {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (J J₀ : Set ℝ)
    (hbox : localBox Ω I (vec3Ball x₀ (2 * R)) J₀)
    (hJ : MeasurableSet J) (htime : J ⊆ J₀)
    (X m : ℝ → Vec3)
    (hspace : ∀ t ∈ J, (fun x : Vec3 ↦ X t + x) '' vec3Ball 0 r ⊆
      vec3Ball x₀ (2 * R))
    (hmean : ∀ᵐ t ∂volume.restrict J,
      m t = fun i ↦ weightedVelocityMean (vec3Ball x₀ R)
        (normalizedWeightedCutoff x₀ hR) u i t)
    {Dp : ParabolicPoint → Vec3}
    (hDp : MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball x₀ (2 * R)) J₀))) :
    movingRelativeVelocityCost X m u r J ≤
      weightedVelocityEuclideanPoincareConstant 64 ^ (2 : ℝ) *
        ENNReal.ofReal (meanMotionCharge (spaceTimeSet (vec3Ball x₀ (2 * R)) J₀)
          u D Dp / r) := by
  have hu : MemLp u (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball x₀ (2 * R)) J₀)) :=
    MemLp.of_eval fun i ↦ velocity_component_memLp_tenThirds_on_ballBox_of_data
      hsol.toData hbox (by positivity : 0 < 2 * R) (Subset.refl _) i
  have henergy := gradient_lintegral_le_meanMotionCharge hu
    (suitable_box_gradient_memLp_two hsol hbox) hDp
  have hmix := suitable_moving_relativeVelocity_mixed_bound hsol x₀ hR J J₀
    hbox hJ htime X m (vec3Ball 0 r) hspace hmean
  unfold movingRelativeVelocityCost
  calc
    _ ≤ (ENNReal.ofReal r)⁻¹ *
        (weightedVelocityEuclideanPoincareConstant 64 ^ (2 : ℝ) *
          ENNReal.ofReal (meanMotionCharge (spaceTimeSet (vec3Ball x₀ (2 * R)) J₀)
            u D Dp)) := mul_le_mul_right (hmix.trans (mul_le_mul_right henergy _)) _
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos hr, div_eq_mul_inv]
      ac_rfl

/-- At the moving scale `r=c R^(25/23)`, a genuine charge budget
`ε R^(25/23)` gives the radius-independent normalized smallness `C² ε/c`. -/
theorem suitable_moving_relativeVelocity_endpoint_cost_le
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x₀ : Vec3) {R c ε : ℝ} (hR : 0 < R) (hc : 0 < c) (J J₀ : Set ℝ)
    (hbox : localBox Ω I (vec3Ball x₀ (2 * R)) J₀)
    (hJ : MeasurableSet J) (htime : J ⊆ J₀)
    (X m : ℝ → Vec3)
    (hspace : ∀ t ∈ J, (fun x : Vec3 ↦ X t + x) ''
      vec3Ball 0 (c * R ^ (25 / 23 : ℝ)) ⊆ vec3Ball x₀ (2 * R))
    (hmean : ∀ᵐ t ∂volume.restrict J,
      m t = fun i ↦ weightedVelocityMean (vec3Ball x₀ R)
        (normalizedWeightedCutoff x₀ hR) u i t)
    {Dp : ParabolicPoint → Vec3}
    (hDp : MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball x₀ (2 * R)) J₀)))
    (hsmall : meanMotionCharge (spaceTimeSet (vec3Ball x₀ (2 * R)) J₀) u D Dp ≤
      ε * R ^ (25 / 23 : ℝ)) :
    movingRelativeVelocityCost X m u (c * R ^ (25 / 23 : ℝ)) J ≤
      weightedVelocityEuclideanPoincareConstant 64 ^ (2 : ℝ) * ENNReal.ofReal (ε / c) := by
  have hscale : 0 < R ^ (25 / 23 : ℝ) := Real.rpow_pos_of_pos hR _
  have hr : 0 < c * R ^ (25 / 23 : ℝ) := mul_pos hc hscale
  apply (suitable_moving_relativeVelocity_cost_le_charge hsol x₀ hR hr J J₀
    hbox hJ htime X m hspace hmean hDp).trans
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (ε * R ^ (25 / 23 : ℝ)) / (c * R ^ (25 / 23 : ℝ)) :=
      div_le_div_of_nonneg_right hsmall hr.le
    _ = ε / c := by field_simp [hc.ne', hscale.ne']

end FluidSingularSets
