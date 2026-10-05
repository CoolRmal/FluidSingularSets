-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.MixedVelocityDecay
public import FluidSingularSets.ActivityMeasurability

/-!
# Symmetric-window mixed-gradient decay

A fixed shift of the upper time face places the small symmetric cylinder inside
the time window of the pressure decomposition. The larger mixed-gradient window
is still contained in the symmetric inner cylinder.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- A small symmetric time interval lies in the shifted backward mean window. -/
theorem symmetricTimeWindow_subset_shiftedMeanWindow
    {t R s : ℝ} (_hR : 0 < R) (hs : 0 < s) (hsR : s ≤ R / 4) :
    Ioo (t - s ^ 2) (t + s ^ 2) ⊆
      Ioc (t + R ^ 2 / 16 - (R / 2) ^ 2) (t + R ^ 2 / 16) := by
  have hsSq : s ^ 2 ≤ R ^ 2 / 16 := by nlinarith only [hsR, hs, _hR]
  intro τ hτ
  constructor <;> nlinarith only [hτ.1, hτ.2, hsSq, sq_pos_of_pos _hR]

/-- The shifted backward gradient window stays inside the symmetric inner window. -/
theorem shiftedGradientWindow_subset_symmetricTimeWindow
    {t R : ℝ} (_hR : 0 < R) :
    Ioc (t + R ^ 2 / 16 - R ^ 2) (t + R ^ 2 / 16) ⊆
      Ioo (t - R ^ 2) (t + R ^ 2) := by
  intro τ hτ
  constructor <;> nlinarith only [hτ.1, hτ.2, sq_pos_of_pos _hR]

/-- For a nonnegative integrable product function, the real iterated integral
has exactly the expected extended-real representation. -/
theorem timeWindowIntegral_ofReal
    {U : Set Vec3} {J : Set ℝ} {f : ParabolicPoint → ℝ}
    (hf : Integrable f ((volume.restrict U).prod (volume.restrict J)))
    (hpos : ∀ w, 0 ≤ f w) :
    ENNReal.ofReal (∫ s in J, ∫ x in U, f (x, s)) =
      ∫⁻ s in J, ∫⁻ x in U, ENNReal.ofReal (f (x, s)) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf.integral_prod_right
    (Eventually.of_forall (fun s ↦ integral_nonneg (fun x ↦ hpos (x, s))))]
  apply lintegral_congr_ae
  filter_upwards [hf.prod_left_ae] with s hs
  exact ofReal_integral_eq_lintegral_ofReal hs
    (Eventually.of_forall (fun x ↦ hpos (x, s)))

/-- The actual suitable-solution clauses make the critical array mixed mass
measurable and finite on every interior backward cylinder. -/
theorem suitableMixedGradientCylinderData
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hsub : closure (parabolicCylinder z.1 z.2 R) ⊆ spaceTimeSet Ω I) :
    AEStronglyMeasurable Du (volume.restrict (parabolicCylinder z.1 z.2 R)) ∧
      (∫⁻ t in Ioc (z.2 - R ^ 2) z.2,
        eLpNorm (fun x ↦ Du (x, t)) (12 / 7)
          (volume.restrict (vec3Ball z.1 R)) ^ (2 : ℝ)) < ⊤ := by
  let B := vec3Ball z.1 R
  let T := Ioc (z.2 - R ^ 2) z.2
  obtain ⟨U, J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hR hsub
  obtain ⟨-, hD, -, -, -, henergy, -, -, -⟩ := hsol.2.2.2.2.2.1 U J hbox
  have hDcyl : AEStronglyMeasurable Du (volume.restrict (B ×ˢ T)) :=
    hD.mono_measure (Measure.restrict_mono hcyl le_rfl)
  refine ⟨hDcyl, ?_⟩
  rw [← arrayMixedGradientIntegral_eq_eLpNorm Du B T hDcyl]
  apply (arrayMixedGradientIntegral_le_dissipation Du B T hDcyl).trans_lt
  apply ENNReal.mul_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) volume_vec3Ball_lt_top.ne
  · calc
      _ ≤ ∫⁻ a in U ×ˢ J, ‖Du a‖ₑ ^ (2 : ℝ) := lintegral_mono_set hcyl
      _ < ⊤ := (lintegral_mono fun _ ↦ le_add_left le_rfl).trans_lt henergy

/-- The proved suitable velocity decay is an ordinary real inequality: all
extended masses and the mixed-gradient source are genuinely finite. -/
theorem suitableVelocityTimeWindowMixedMassDecay_real
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r ≤ ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 (4 * ρ)) ⊆ spaceTimeSet Ω I)
    {J : Set ℝ} (hJ : J ⊆ Ioc (z.2 - ρ ^ 2) z.2) :
    (∫ s in J, ∫ x in vec3Ball z.1 r,
      vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ)) ≤
      4 * criticalVectorCubicOscillationConstant.toReal *
        (timeSliceEnergyEssSup z.1 z.2 (2 * ρ)
          (fun w ↦ vec3EuclideanNorm (u w))).toReal ^ (1 / 2 : ℝ) *
        (∫⁻ s in Ioc (z.2 - (2 * ρ) ^ 2) z.2,
          eLpNorm (fun x ↦ Du (x, s)) (12 / 7)
            (volume.restrict (vec3Ball z.1 (2 * ρ))) ^ (2 : ℝ)).toReal +
      4 * (r / ρ) ^ (3 : ℕ) * ∫ s in Ioc (z.2 - ρ ^ 2) z.2,
        ∫ x in vec3Ball z.1 ρ, vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ) := by
  let B := vec3Ball z.1 ρ
  let T := Ioc (z.2 - ρ ^ 2) z.2
  have hsubρ : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono hρ.le (by linarith only [hρ]))).trans hsub
  have hsub₂ : closure (parabolicCylinder z.1 z.2 (2 * ρ)) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono (by positivity)
      (by linarith only [hρ]))).trans hsub
  have hc : Integrable (fun w ↦ vec3EuclideanNorm (u w) ^ (3 : ℕ))
      ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    exact tsai_integrable_velocity_cube_on_cylinder hsol hρ hsubρ
  have hcsmall : Integrable (fun w ↦ vec3EuclideanNorm (u w) ^ (3 : ℕ))
      ((volume.restrict (vec3Ball z.1 r)).prod (volume.restrict J)) :=
    hc.mono_measure (Measure.prod_mono
      (Measure.restrict_mono (vec3Ball_mono hrρ) le_rfl)
      (Measure.restrict_mono hJ le_rfl))
  have hsmall : ENNReal.ofReal (∫ s in J, ∫ x in vec3Ball z.1 r,
      vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ)) =
      ∫⁻ s in J, ∫⁻ x in vec3Ball z.1 r,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ) := by
    apply (timeWindowIntegral_ofReal hcsmall
      (fun w ↦ pow_nonneg (vec3EuclideanNorm_nonneg (u w)) 3)).trans
    apply lintegral_congr
    intro s
    apply lintegral_congr
    intro x
    norm_num only [ENNReal.rpow_ofNat]
    exact ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3
  have hlarge : ENNReal.ofReal (∫ s in T, ∫ x in B,
      vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ)) =
      ∫⁻ s in T, ∫⁻ x in B,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ) := by
    apply (timeWindowIntegral_ofReal hc
      (fun w ↦ pow_nonneg (vec3EuclideanNorm_nonneg (u w)) 3)).trans
    apply lintegral_congr
    intro s
    apply lintegral_congr
    intro x
    norm_num only [ENNReal.rpow_ofNat]
    exact ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3
  have hE : timeSliceEnergyEssSup z.1 z.2 (2 * ρ)
      (fun w ↦ vec3EuclideanNorm (u w)) ≠ ⊤ :=
    (sws_timeSliceEnergyEssSup_lt_top hsol (by positivity) hsub₂).ne
  have hM := (suitableMixedGradientCylinderData hsol (by positivity) hsub₂).2.ne
  have hfinite :
      4 * criticalVectorCubicOscillationConstant *
        timeSliceEnergyEssSup z.1 z.2 (2 * ρ) (fun w ↦ vec3EuclideanNorm (u w)) ^
          (1 / 2 : ℝ) *
        (∫⁻ s in Ioc (z.2 - (2 * ρ) ^ 2) z.2,
          eLpNorm (fun x ↦ Du (x, s)) (12 / 7)
            (volume.restrict (vec3Ball z.1 (2 * ρ))) ^ (2 : ℝ)) +
      4 * ENNReal.ofReal ((r / ρ) ^ (3 : ℕ)) *
        (∫⁻ s in T, ∫⁻ x in B,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) ≠ ⊤ := by
    rw [← hlarge]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) criticalVectorCubicOscillationConstant_ne_top)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE)) hM,
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
          ENNReal.ofReal_ne_top⟩
  have hreal := ENNReal.toReal_mono hfinite
    (suitableVelocityTimeWindowMixedMassDecay hsol hρ hr hrρ hsub hJ)
  rw [← hsmall, ← hlarge, ENNReal.toReal_add] at hreal
  · simpa only [ENNReal.toReal_mul, ENNReal.toReal_rpow, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ integral_nonneg
        (fun _ ↦ pow_nonneg (vec3EuclideanNorm_nonneg _) 3))),
      ENNReal.toReal_ofReal (pow_nonneg (div_nonneg hr.le hρ.le) 3)] using hreal
  · exact (ENNReal.add_ne_top.mp hfinite).1
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top

end FluidSingularSets
