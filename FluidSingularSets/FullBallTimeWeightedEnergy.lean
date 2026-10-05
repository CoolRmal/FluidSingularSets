-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallProjectedTimeEnergy
public import FluidSingularSets.FullBallProjectedPressurePairings

/-!
# Genuine time-weighted corrected energy

The tested energy controls the actual field sqrt(θ) φ³V. Its literal Euclidean
slice energy agrees with the suitable tested energy and bounds the native L²
slice costs. Genuine suitable data provide finite energy and actual mixed classes.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The literal velocity controlled by the actual time-weighted sixth-cutoff energy. -/
def fullBallTimeWeightedProjectedVelocity
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) (θ : ℝ → ℝ)
    (z : ParabolicPoint) : Vec3 :=
  Real.sqrt (θ z.2) • fullBallProjectedCutoffVelocity u D p a b c φ z

/-- The true Euclidean energy supremum of that actual weighted field. -/
def fullBallTimeWeightedProjectedEnergySup
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (B : Set Vec3)
    (φ : Vec3 → ℝ) (θ : ℝ → ℝ) : ℝ≥0∞ :=
  essSup (fun t ↦ ∫⁻ x in B,
    ‖vec3EuclideanNorm (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t))‖ₑ ^
      (2 : ℝ)) (volume.restrict (Ioo a b))

/-- A time cutoff in the unit interval is bounded by its genuine square root. -/
theorem time_cutoff_le_sqrt {s : ℝ} (hs : 0 ≤ s) (hsone : s ≤ 1) :
    s ≤ Real.sqrt s := by
  apply (Real.le_sqrt hs hs).mpr
  nlinarith

/-- The actual time-weighted field is pointwise dominated by the spatially weighted field. -/
theorem fullBallTimeWeightedProjectedVelocity_norm_le
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) {θ : ℝ → ℝ}
    (hθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) (z : ParabolicPoint) :
    ‖fullBallTimeWeightedProjectedVelocity u D p a b c φ θ z‖ ≤
      ‖fullBallProjectedCutoffVelocity u D p a b c φ z‖ := by
  rw [fullBallTimeWeightedProjectedVelocity, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.sqrt_le_one.mpr (hθ z.2).2)

/-- The pressure's literal time factor is controlled by the tested weighted velocity. -/
theorem fullBallTimeWeightedProjectedVelocity_time_smul_norm_le
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) {θ : ℝ → ℝ}
    (hθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) (z : ParabolicPoint) :
    ‖θ z.2 • fullBallProjectedCutoffVelocity u D p a b c φ z‖ ≤
      ‖fullBallTimeWeightedProjectedVelocity u D p a b c φ θ z‖ := by
  simp only [fullBallTimeWeightedProjectedVelocity, norm_smul,
    Real.norm_of_nonneg (hθ z.2).1, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (time_cutoff_le_sqrt (hθ z.2).1 (hθ z.2).2) (norm_nonneg _)

/-- The genuine Euclidean square is exactly the literal sixth-cutoff tested energy. -/
theorem fullBallTimeWeightedProjectedVelocity_energy_eq
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {φ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hφ : ∀ x, 0 ≤ φ x) (hθ : ∀ t, 0 ≤ θ t)
    (x : fullBallCompactInterior ρ) (t : ℝ) :
    vec3EuclideanNorm (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x.1, t)) ^ 2 =
      fullBallProjectedEnergyDensity ρ u D p a b c
        (fun z ↦ φ z.1 ^ 6 * θ z.2) (x, t) := by
  simp only [fullBallTimeWeightedProjectedVelocity, fullBallProjectedCutoffVelocity,
    fullBallProjectedEnergyDensity, fullBallProjectedVelocityAmbient,
    vec3EuclideanNorm_smul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (pow_nonneg (hφ x.1) 3), mul_pow, Real.sq_sqrt (hθ t), ← pow_mul]
  ring

/-- The actual tested spatial energy equals the real weighted square integral at every time. -/
theorem fullBallTimeWeightedProjectedVelocity_integral_energy_eq
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {φ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hφ : ∀ x, 0 ≤ φ x) (hθ : ∀ t, 0 ≤ θ t) (t : ℝ) :
    (∫ x : fullBallCompactInterior ρ,
      vec3EuclideanNorm (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x.1, t)) ^ 2
        ∂(fullBallInteriorMeasure ρ)) =
      ∫ x, fullBallProjectedEnergyDensity ρ u D p a b c
        (fun z ↦ φ z.1 ^ 6 * θ z.2) (x, t) ∂(fullBallInteriorMeasure ρ) := by
  exact integral_congr_ae (ae_of_all _ fun x ↦
    fullBallTimeWeightedProjectedVelocity_energy_eq ρ u D p a b c hφ hθ x t)

/-- Actual compact tested energy equals the native spatial integral whenever
the genuine spatial cutoff is supported in that patch. -/
theorem fullBallTimeWeightedProjectedVelocity_tested_integral_eq
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {B : Set Vec3}
    {φ : Vec3 → ℝ} {θ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) (hθ : ∀ t, 0 ≤ θ t)
    (hs : tsupport φ ⊆ B) (hBK : B ⊆ fullBallCompactInterior ρ) (t : ℝ) :
    (∫ x, fullBallProjectedEnergyDensity ρ u D p a b c
      (fun z ↦ φ z.1 ^ 6 * θ z.2) (x, t) ∂(fullBallInteriorMeasure ρ)) =
      ∫ x in B, vec3EuclideanNorm
        (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t)) ^ 2 := by
  let F : Vec3 → ℝ := fun x ↦ vec3EuclideanNorm
    (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t)) ^ 2
  have hz (x : Vec3) (hx : x ∉ B) : F x = 0 := by
    have hxφ : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))
    simp only [F, fullBallTimeWeightedProjectedVelocity, fullBallProjectedCutoffVelocity,
      hxφ, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_smul, smul_zero,
      vec3EuclideanNorm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  calc
    _ = ∫ x : fullBallCompactInterior ρ, F x.1 ∂(fullBallInteriorMeasure ρ) :=
      (fullBallTimeWeightedProjectedVelocity_integral_energy_eq ρ u D p a b c hφ hθ t).symm
    _ = ∫ x in fullBallCompactInterior ρ, F x :=
      (fullBallInterior_measurePreserving ρ).integral_comp
        (MeasurableEmbedding.subtype_coe isClosed_closure.measurableSet) F
    _ = ∫ x, F x := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ hz x (fun h ↦ hx (hBK h)))
    _ = ∫ x in B, F x := (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm

section LocalBox

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3} {φ : Vec3 → ℝ} {θ : ℝ → ℝ}

/-- Genuine suitable source data give actual time-weighted joint measurability. -/
theorem fullBallTimeWeightedProjectedVelocity_aestronglyMeasurable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hθ : Continuous θ) :
    AEStronglyMeasurable (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ)
      ((volume.restrict B).prod (volume.restrict (Ioo a b))) :=
  (Real.continuous_sqrt.comp (hθ.comp continuous_snd)).aestronglyMeasurable.smul
    (fullBallProjectedCutoffVelocity_aestronglyMeasurable
      hsol hbox hab hc hρ hρone hBK hφ)

/-- Actual suitable spatial slices give true L² membership of the weighted field. -/
theorem fullBallTimeWeightedProjectedVelocity_slices_memLp_two
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), MemLp
      (fun x ↦ fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t)) 2
        (volume.restrict B) := by
  filter_upwards [fullBallProjectedCutoffVelocity_slices_memLp_two (c := c)
    hsol hbox hρ hρone hB hBK hφ hb] with t ht
  exact ht.const_smul (Real.sqrt (θ t))

/-- The actual bounded time and spatial cutoffs preserve true joint L² membership. -/
theorem fullBallTimeWeightedProjectedVelocity_joint_memLp_two
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hθ : Continuous θ) (hbθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) :
    MemLp (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ) 2
      ((volume.restrict B).prod (volume.restrict (Ioo a b))) := by
  have hV : MemLp (fullBallProjectedVelocityAmbient u D p a b c) 2
      ((volume.restrict B).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact (fullBallProjectedVelocityAmbient_joint_memLp_two
      hsol hbox hab hc hρ hρone hBK).1
  apply hV.of_le (fullBallTimeWeightedProjectedVelocity_aestronglyMeasurable
    hsol hbox hab hc hρ hρone hBK hφ hθ)
  filter_upwards [] with z
  exact (fullBallTimeWeightedProjectedVelocity_norm_le u D p a b c φ hbθ z).trans
      (projected_cutoff_power_norm_le
        (fullBallProjectedVelocityAmbient u D p a b c z) (hb z.1).1 (hb z.1).2 3)

/-- The actual Euclidean energy supremum is exactly that of the tested real energy. -/
theorem fullBallTimeWeightedProjectedEnergySup_eq_tested_energy
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hs : tsupport φ ⊆ B) (hθ : ∀ t, 0 ≤ θ t) :
    fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ =
      essSup (fun t ↦ ENNReal.ofReal (∫ x, fullBallProjectedEnergyDensity ρ u D p a b c
        (fun z ↦ φ z.1 ^ 6 * θ z.2) (x, t) ∂(fullBallInteriorMeasure ρ)))
          (volume.restrict (Ioo a b)) := by
  apply essSup_congr_ae
  filter_upwards [fullBallTimeWeightedProjectedVelocity_slices_memLp_two (c := c)
    hsol hbox hρ hρone hB hBK hφ hb] with t ht
  let W := fun x ↦ fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t)
  have hE : MemLp (fun x ↦ vec3EuclideanNorm (W x)) 2 (volume.restrict B) := by
    apply ht.of_le_mul (CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      ht.aestronglyMeasurable)
    exact ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)]
      exact (vec3EuclideanNorm_le_sqrt_three_mul_norm _).trans
        (mul_le_mul_of_nonneg_right (show Real.sqrt 3 ≤ 3 from by
          apply Real.sqrt_le_iff.mpr
          norm_num) (norm_nonneg _))
  have hi : Integrable (fun x ↦ vec3EuclideanNorm (W x) ^ 2) (volume.restrict B) := by
    have h := hE.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    simpa only [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)] using h
  rw [fullBallTimeWeightedProjectedVelocity_tested_integral_eq
    ρ u D p a b c (fun x ↦ (hb x).1) hθ hs hBK t,
    ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x ↦ sq_nonneg _)]
  apply lintegral_congr_ae
  exact ae_of_all _ fun x ↦ by
    simp only [W, ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _),
      ENNReal.rpow_ofNat, ← ofReal_norm, Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)]

/-- The genuine time-weighted Euclidean supremum is bounded in the correct direction. -/
theorem fullBallTimeWeightedProjectedEnergySup_le_spatial
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) :
    fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ≤
      9 * fullBallProjectedCutoffSliceEnergy u D p a b c B φ := by
  apply (essSup_mono_ae ?_).trans_eq ENNReal.essSup_const_mul
  filter_upwards [fullBallTimeWeightedProjectedVelocity_slices_memLp_two (c := c)
    hsol hbox hρ hρone hB hBK hφ hb] with t ht
  apply (lintegral_euclidean_velocity_sq_le_nine ht.aestronglyMeasurable).trans
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro x
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal
    (fullBallTimeWeightedProjectedVelocity_norm_le u D p a b c φ hθ (x, t))

/-- Actual suitable data make the time-weighted tested energy genuinely finite. -/
theorem fullBallTimeWeightedProjectedEnergySup_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) :
    fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ < ⊤ :=
  (fullBallTimeWeightedProjectedEnergySup_le_spatial
    hsol hbox hρ hρone hB hBK hφ hb hθ).trans_lt
      (ENNReal.mul_lt_top (by norm_num)
        (fullBallProjectedCutoffSliceEnergy_lt_top hsol hbox hab hc hρ hρone hB hBK hφ hb))

/-- Actual native L² slice costs are bounded by the genuine tested Euclidean energy. -/
theorem fullBallTimeWeightedProjectedVelocity_energy_bound_ae :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫⁻ x in B, ‖fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t)‖ₑ ^
        (2 : ℝ)) ≤ fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ := by
  filter_upwards [ENNReal.ae_le_essSup (fun t ↦ ∫⁻ x in B,
    ‖vec3EuclideanNorm (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t))‖ₑ ^
      (2 : ℝ))] with t ht
  apply le_trans (lintegral_mono fun x ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)) ht
  rw [← ofReal_norm, ← ofReal_norm, Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_le_vec3EuclideanNorm _)

/-- The actual time-weighted spatial-class curve has the tested energy square-root bound. -/
theorem fullBallTimeWeightedProjectedVelocity_curve_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hθ : Continuous θ) (hbθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) :
    MemLp (actualSliceLp (μ := volume.restrict B) (p := 2)
      (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ)) ⊤
        (volume.restrict (Ioo a b)) ∧
      eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2)
        (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ)) ⊤
          (volume.restrict (Ioo a b)) ≤
            fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ^ (1 / 2 : ℝ) := by
  have hj := fullBallTimeWeightedProjectedVelocity_aestronglyMeasurable
    hsol hbox hab hc hρ hρone hBK hφ hθ
  have he : essSup (fun t ↦ ∫⁻ x in B,
      ‖fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo a b)) ≤
      fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ :=
    essSup_le_of_ae_le _ fullBallTimeWeightedProjectedVelocity_energy_bound_ae
  refine ⟨actualSliceLp_memLp_top_of_sliceEnergy hj
    (he.trans_lt (fullBallTimeWeightedProjectedEnergySup_lt_top
      hsol hbox hab hc hρ hρone hB hBK hφ hb hbθ)), ?_⟩
  exact (actualSliceLp_eLpNorm_top_le_sliceEnergy hj).trans
    (ENNReal.rpow_le_rpow he (by norm_num))

/-- Genuine domination by Wθ gives true scalar mixed data and the exact Mθ bound. -/
theorem fullBallTimeWeightedProjectedScalar_curve_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hθ : Continuous θ) (hbθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1)
    {G : ParabolicPoint → ℝ} (hG : AEStronglyMeasurable G
      ((volume.restrict B).prod (volume.restrict (Ioo a b))))
    {C : ℝ} (hbound : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ᵐ x ∂volume.restrict B,
      ‖G (x, t)‖ ≤ C * ‖fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t)‖) :
    ProjectedEnergySliceData (volume.restrict B) (volume.restrict (Ioo a b)) ⊤ G ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2) G) ⊤
      (volume.restrict (Ioo a b)) ≤ ENNReal.ofReal C *
        fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ^ (1 / 2 : ℝ) := by
  have hs := fullBallTimeWeightedProjectedVelocity_slices_memLp_two (c := c) (θ := θ)
    hsol hbox hρ hρone hB hBK hφ hb
  have hw := fullBallTimeWeightedProjectedVelocity_curve_data
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hbθ
  have hd := projectedEnergySliceData_top_of_velocity_bound hG hs hw.1 hbound
  have hnorm : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ‖actualSliceLp (μ := volume.restrict B) (p := 2) G t‖ₑ ≤ ENNReal.ofReal C *
        ‖actualSliceLp (μ := volume.restrict B) (p := 2)
          (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ) t‖ₑ := by
    filter_upwards [hd.slices, hs, hbound] with t hgt hwt hbt
    rw [actualSliceLp_enorm G t hgt,
      actualSliceLp_enorm (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ) t hwt]
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hgt.aestronglyMeasurable hbt 2
  exact ⟨hd, (eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' ⊤
    hd.classMemLp.aestronglyMeasurable hnorm).trans (mul_le_mul' le_rfl hw.2)⟩

end LocalBox

end FluidSingularSets
