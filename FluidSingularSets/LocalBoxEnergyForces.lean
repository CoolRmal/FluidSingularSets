-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalBoxPressureEnergy
public import FluidSingularSets.StokesForceCurves
public import CKN.Setting.SobolevPoincareBallWeak
public import CKN.Setting.SobolevPoincareConstantFinite

/-!
# Full local-ball energy-force curves

The true weak Sobolev–Poincaré theorem on the full ball removes the doubled
spatial carrier from the source classes of the energy-dual momentum equation.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance localBoxEnergyForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance localBoxEnergyForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The actual spatial mean is controlled by the true slice energy norm. -/
theorem enorm_average_le_energy
    {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) {f : A → ℝ} (hf : AEStronglyMeasurable f μ) :
    ‖average μ f‖ₑ ≤ (μ univ)⁻¹ * (eLpNorm f 2 μ * (μ univ) ^ (1 / 2 : ℝ)) := by
  have htop : μ univ ≠ ∞ := measure_ne_top μ univ
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (by constructor <;> norm_num : (2 : ℝ).HolderConjugate 2)
    hf.enorm (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at hholder
  have hnorm := eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num) hf
  norm_num only [ENNReal.toReal_ofNat] at hnorm
  have havg : ‖average μ f‖ₑ = (μ univ)⁻¹ * ‖∫ x, f x ∂μ‖ₑ := by
    rw [average_eq, smul_eq_mul, enorm_mul, Real.enorm_eq_ofReal,
      ENNReal.ofReal_inv_of_pos, measureReal_def, ENNReal.ofReal_toReal htop]
    · exact ENNReal.toReal_pos hμ htop
    · positivity
  rw [havg]
  exact mul_le_mul_right ((enorm_integral_le_lintegral_enorm f).trans
    (hholder.trans_eq (by rw [← hnorm]))) _

/-- A finite coefficient for the full unit-ball spatial mean. -/
def fullUnitBallMeanCoefficient : ℝ≥0∞ :=
  (volume (vec3Ball (0 : Vec3) 1))⁻¹ *
    volume (vec3Ball (0 : Vec3) 1) ^ (1 / 2 : ℝ) *
      volume (vec3Ball (0 : Vec3) 1) ^ (1 / 6 : ℝ)

theorem fullUnitBallMeanCoefficient_ne_top : fullUnitBallMeanCoefficient ≠ ∞ := by
  unfold fullUnitBallMeanCoefficient
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr (volume_vec3Ball_pos (by norm_num : (0 : ℝ) < 1)).ne'
    · exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) volume_vec3Ball_lt_top.ne).ne
  · exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) volume_vec3Ball_lt_top.ne).ne

/-- An explicit finite full-ball weak Sobolev coefficient. -/
def fullUnitBallH1Coefficient : ℝ≥0∞ :=
  3 * (sobolevPoincareL6Constant + fullUnitBallMeanCoefficient)

theorem fullUnitBallH1Coefficient_ne_top : fullUnitBallH1Coefficient ≠ ∞ :=
  ENNReal.mul_ne_top (by norm_num)
    (ENNReal.add_ne_top.mpr ⟨sobolevPoincareL6Constant_ne_top,
      fullUnitBallMeanCoefficient_ne_top⟩)

private theorem fullBall_eLpNorm_vector_six_le_sum {μ : Measure Vec3}
    {u : Vec3 → Vec3} (hu : AEStronglyMeasurable u μ) :
    eLpNorm u 6 μ ≤ ∑ j : Fin 3, eLpNorm (fun x ↦ u x j) 6 μ := by
  calc
    _ ≤ eLpNorm (fun x ↦ ∑ j : Fin 3, ‖u x j‖) 6 μ := by
      apply eLpNorm_mono_ae hu
      exact ae_of_all _ (fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]
        apply (pi_norm_le_iff_of_nonneg
          (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))).mpr
        intro j
        exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j))
    _ = eLpNorm (∑ j : Fin 3, fun x ↦ ‖u x j‖) 6 μ := rfl
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x ↦ ‖u x j‖) 6 μ :=
      eLpNorm_sum_le (by norm_num)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact eLpNorm_norm _ ((continuous_apply j).comp_aestronglyMeasurable hu)

/-- Actual energy-class weak velocity gradients control the entire unit ball. -/
theorem fullUnitBallH1Vector_sobolev
    {u : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3}
    (hu : MemLp u 2 (volume.restrict (vec3Ball 0 1)))
    (hD : MemLp D 2 (volume.restrict (vec3Ball 0 1)))
    (hw : ∀ j : Fin 3, HasWeakGradientOn (vec3Ball 0 1)
      (fun x ↦ u x j) (fun x ↦ D x j)) :
    eLpNorm u 6 (volume.restrict (vec3Ball 0 1)) ≤ fullUnitBallH1Coefficient *
      (eLpNorm D 2 (volume.restrict (vec3Ball 0 1)) +
        eLpNorm u 2 (volume.restrict (vec3Ball 0 1))) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball 0 1)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have hμ : μ univ ≠ 0 := by
    simp only [μ, Measure.restrict_apply_univ]
    exact (volume_vec3Ball_pos (by norm_num : (0 : ℝ) < 1)).ne'
  have hcomp (j : Fin 3) : eLpNorm (fun x ↦ u x j) 6 μ ≤
      (sobolevPoincareL6Constant + fullUnitBallMeanCoefficient) *
        (eLpNorm D 2 μ + eLpNorm u 2 μ) := by
    have hB : euclideanBall (0 : Vec3) 1 = vec3Ball 0 1 :=
      euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1)
    let v : H1Function (euclideanBall 0 1) :=
      { toFun := fun x ↦ u x j
        grad := fun x ↦ D x j
        memL2 := by simpa only [MemL2On, MemLpOn, hB] using hu.eval j
        gradMemL2 := fun i ↦ by
          simpa only [MemLpOn, hB] using (hD.eval j).eval i
        hasWeakGradient := by
          simpa only [hB] using hw j }
    have hs := sobolevPoincare_L6_ball_weak (0 : Vec3) (by norm_num : (0 : ℝ) < 1) v
    simp only [lpNormOn, weakGradientLpNormOn, hB] at hs
    change eLpNorm (fun x ↦ u x j - average μ (fun y ↦ u y j)) 6 μ ≤
      sobolevPoincareL6Constant * eLpNorm (fun x ↦ D x j) 2 μ at hs
    have hg : eLpNorm (fun x ↦ D x j) 2 μ ≤ eLpNorm D 2 μ :=
      eLpNorm_mono_ae ((hD.eval j).aestronglyMeasurable)
        (ae_of_all _ (fun x ↦ norm_le_pi_norm (D x) j))
    have hv : eLpNorm (fun x ↦ u x j) 2 μ ≤ eLpNorm u 2 μ :=
      eLpNorm_mono_ae ((hu.eval j).aestronglyMeasurable)
        (ae_of_all _ (fun x ↦ norm_le_pi_norm (u x) j))
    have hmean : eLpNorm (fun _ : Vec3 ↦ average μ (fun y ↦ u y j)) 6 μ ≤
        fullUnitBallMeanCoefficient * eLpNorm u 2 μ := by
      rw [eLpNorm_const' _ (by norm_num : (6 : ℝ≥0∞) ≠ 0) (by norm_num),
        ENNReal.toReal_ofNat]
      have ha := enorm_average_le_energy hμ (hu.eval j).aestronglyMeasurable
      apply (mul_le_mul_left ha _).trans
      calc
        _ ≤ ((μ univ)⁻¹ * (eLpNorm u 2 μ * (μ univ) ^ (1 / 2 : ℝ))) *
            (μ univ) ^ (1 / 6 : ℝ) := by gcongr
        _ = _ := by
          simp only [μ, Measure.restrict_apply_univ, fullUnitBallMeanCoefficient]
          ring
    have hid : (fun x ↦ u x j) =
        (fun x ↦ u x j - average μ (fun y ↦ u y j)) +
          (fun _ ↦ average μ (fun y ↦ u y j)) := by
      funext x
      simp only [Pi.add_apply, sub_add_cancel]
    calc
      _ ≤ eLpNorm (fun x ↦ u x j - average μ (fun y ↦ u y j)) 6 μ +
          eLpNorm (fun _ : Vec3 ↦ average μ (fun y ↦ u y j)) 6 μ := by
        conv_lhs => rw [hid]
        exact eLpNorm_add_le (by norm_num)
      _ ≤ sobolevPoincareL6Constant * eLpNorm D 2 μ +
          fullUnitBallMeanCoefficient * eLpNorm u 2 μ :=
        add_le_add (hs.trans (mul_le_mul_right hg _)) hmean
      _ ≤ _ := by
        calc
          _ ≤ sobolevPoincareL6Constant * (eLpNorm D 2 μ + eLpNorm u 2 μ) +
              fullUnitBallMeanCoefficient * (eLpNorm D 2 μ + eLpNorm u 2 μ) :=
            add_le_add (mul_le_mul_right le_self_add _)
              (mul_le_mul_right le_add_self _)
          _ = _ := by ring
  calc
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x ↦ u x j) 6 μ :=
      fullBall_eLpNorm_vector_six_le_sum hu.aestronglyMeasurable
    _ ≤ ∑ _j : Fin 3, (sobolevPoincareL6Constant + fullUnitBallMeanCoefficient) *
        (eLpNorm D 2 μ + eLpNorm u 2 μ) := Finset.sum_le_sum fun j _ ↦ hcomp j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat, fullUnitBallH1Coefficient, μ, mul_assoc]

/-- The full-ball genuine weak Sobolev bound supplies spatial `L⁶` membership. -/
theorem fullUnitBallH1Vector_memLp_six
    {u : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3}
    (hu : MemLp u 2 (volume.restrict (vec3Ball 0 1)))
    (hD : MemLp D 2 (volume.restrict (vec3Ball 0 1)))
    (hw : ∀ j : Fin 3, HasWeakGradientOn (vec3Ball 0 1)
      (fun x ↦ u x j) (fun x ↦ D x j)) :
    MemLp u 6 (volume.restrict (vec3Ball 0 1)) :=
  (fullUnitBallH1Vector_sobolev hu hD hw).trans_lt (ENNReal.mul_lt_top
    fullUnitBallH1Coefficient_ne_top.lt_top (ENNReal.add_lt_top.mpr
      ⟨hD.eLpNorm_lt_top, hu.eLpNorm_lt_top⟩))

/-- Interpolation on the full ball retains the exact energy time exponent. -/
theorem fullUnitBallH1Vector_four_pow_energy {u : Vec3 → Vec3}
    {D : Vec3 → Fin 3 → Vec3} {M : ℝ≥0∞}
    (hu : MemLp u 2 (volume.restrict (vec3Ball 0 1)))
    (hD : MemLp D 2 (volume.restrict (vec3Ball 0 1)))
    (hw : ∀ j : Fin 3, HasWeakGradientOn (vec3Ball 0 1)
      (fun x ↦ u x j) (fun x ↦ D x j))
    (hM : eLpNorm u 2 (volume.restrict (vec3Ball 0 1)) ^ 2 ≤ M) :
    eLpNorm u 4 (volume.restrict (vec3Ball 0 1)) ^ (8 / 3 : ℝ) ≤
      2 * fullUnitBallH1Coefficient ^ 2 * M ^ (1 / 3 : ℝ) *
        (eLpNorm D 2 (volume.restrict (vec3Ball 0 1)) ^ 2 + M) := by
  have hui := hu
  have hU : eLpNorm u 2 (volume.restrict (vec3Ball 0 1)) ≤
      eLpNorm u 2 (volume.restrict (vec3Ball 0 1)) :=
    le_rfl
  have hfactor : eLpNorm u 2 (volume.restrict (vec3Ball 0 1)) ^ (2 / 3 : ℝ) ≤
      M ^ (1 / 3 : ℝ) := by
    have h := ENNReal.rpow_le_rpow hM (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul] at h
    norm_num only [show (2 : ℝ) * (1 / 3) = 2 / 3 by norm_num] at h
    exact (ENNReal.rpow_le_rpow hU (by norm_num)).trans h
  have hadd : (eLpNorm D 2 (volume.restrict (vec3Ball 0 1)) +
      eLpNorm u 2 (volume.restrict (vec3Ball 0 1))) ^ 2 ≤
      2 * (eLpNorm D 2 (volume.restrict (vec3Ball 0 1)) ^ 2 + M) := by
    have h := ENNReal.rpow_add_le_mul_rpow_add_rpow
      (eLpNorm D 2 (volume.restrict (vec3Ball 0 1)))
      (eLpNorm u 2 (volume.restrict (vec3Ball 0 1)))
      (by norm_num : (1 : ℝ) ≤ 2)
    norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one,
      ENNReal.rpow_ofNat] at h
    exact h.trans (mul_le_mul_right (add_le_add le_rfl hM) 2)
  have hsquare := pow_le_pow_left' (fullUnitBallH1Vector_sobolev hu hD hw) 2
  rw [mul_pow] at hsquare
  calc
    _ ≤ eLpNorm u 2 (volume.restrict (vec3Ball 0 1)) ^ (2 / 3 : ℝ) *
        eLpNorm u 6 (volume.restrict (vec3Ball 0 1)) ^ 2 :=
      eLpNorm_interpolate_four_pow hui.aestronglyMeasurable
    _ ≤ M ^ (1 / 3 : ℝ) * (fullUnitBallH1Coefficient ^ 2 *
        (2 * (eLpNorm D 2 (volume.restrict (vec3Ball 0 1)) ^ 2 + M))) :=
      mul_le_mul' hfactor (hsquare.trans (mul_le_mul_right hadd _))
    _ = _ := by ring


section Suitable

variable {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
  {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- Actual S1 energy gives both joint quadratic classes on the full local ball. -/
theorem suitable_joint_two_localBox (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp u 2 (volume.restrict (vec3Ball 0 1 ×ˢ J)) ∧
      MemLp Du 2 (volume.restrict (vec3Ball 0 1 ×ˢ J)) := by
  have hu : MemLp u 2 (volume.restrict (vec3Ball 0 1 ×ˢ J)) := by
    apply memLp_iff.mpr
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      (hsol.toData.aestronglyMeasurable_velocity hbox)).mpr
    rw [ENNReal.toReal_ofNat]
    exact (lintegral_mono (fun _ ↦ le_add_right le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)
  have hD : MemLp Du 2 (volume.restrict (vec3Ball 0 1 ×ˢ J)) := by
    apply memLp_iff.mpr
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      (hsol.toData.aestronglyMeasurable_gradient hbox)).mpr
    rw [ENNReal.toReal_ofNat]
    exact (lintegral_mono (fun _ ↦ le_add_left le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)
  exact ⟨hu, hD⟩
/-- Actual suitability gives full-ball spatial quartic slices. -/
theorem suitable_unitBall_memLp_four_ae_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    ∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ u (x, t)) 4 (volume.restrict (vec3Ball 0 1)) := by
  have hw : ∀ᵐ t ∂volume.restrict J, ∀ j : Fin 3,
      HasWeakGradientOn (vec3Ball 0 1)
        (fun x ↦ u (x, t) j) (fun x ↦ Du (x, t) j) :=
    ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht hwt
  exact memLp_four_of_two_six
    ht.1
    (fullUnitBallH1Vector_memLp_six ht.1 ht.2 hwt)

/-- The actual S1 slice energy controls time `L^{8/3}` of the spatial `L⁴` norm. -/
theorem suitable_unitBall_four_time_moment_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    (∫⁻ t in J, eLpNorm (fun x ↦ u (x, t)) 4
      (volume.restrict (vec3Ball 0 1)) ^ (8 / 3 : ℝ)) ≤
      2 * fullUnitBallH1Coefficient ^ 2 *
        (essSup (fun t ↦ ∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
          (volume.restrict J)) ^ (1 / 3 : ℝ) *
        ((∫⁻ z in vec3Ball 0 1 ×ˢ J, ‖Du z‖ₑ ^ (2 : ℝ)) +
          (essSup (fun t ↦ ∫⁻ x in vec3Ball 0 1,
            ‖u (x, t)‖ₑ ^ (2 : ℝ)) (volume.restrict J)) * volume J) := by
  let M := essSup (fun t ↦ ∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
    (volume.restrict J)
  have hMfin : M < ∞ := hsol.toData.essSup_sliceEnergy_lt_top hbox
  have hw : ∀ᵐ t ∂volume.restrict J, ∀ j : Fin 3,
      HasWeakGradientOn (vec3Ball 0 1)
        (fun x ↦ u (x, t) j) (fun x ↦ Du (x, t) j) :=
    ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x ↦ u (x, t)) 4 (volume.restrict (vec3Ball 0 1)) ^ (8 / 3 : ℝ) ≤
        2 * fullUnitBallH1Coefficient ^ 2 * M ^ (1 / 3 : ℝ) *
          (eLpNorm (fun x ↦ Du (x, t)) 2
            (volume.restrict (vec3Ball 0 1)) ^ 2 + M) := by
    filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw,
      ENNReal.ae_le_essSup (μ := volume.restrict J)
        (fun t ↦ ∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))] with t ht hwt hMt
    apply fullUnitBallH1Vector_four_pow_energy ht.1 ht.2 hwt
    have heq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0))
      (by norm_num) ht.1.aestronglyMeasurable
    norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at heq
    exact heq.trans_le (by simpa only [M, ENNReal.rpow_ofNat] using hMt)
  calc
    _ ≤ ∫⁻ t in J, 2 * fullUnitBallH1Coefficient ^ 2 * M ^ (1 / 3 : ℝ) *
        (eLpNorm (fun x ↦ Du (x, t)) 2
          (volume.restrict (vec3Ball 0 1)) ^ 2 + M) :=
      lintegral_mono_ae hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by
          exact ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by norm_num)
              (ENNReal.pow_ne_top fullUnitBallH1Coefficient_ne_top))
            (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hMfin.ne).ne),
        lintegral_add_right _ measurable_const, lintegral_const,
        lintegral_spatial_two_sq_eq (hsol.toData.aestronglyMeasurable_gradient hbox)]
      simp only [M, Measure.restrict_apply_univ, mul_assoc, ENNReal.rpow_ofNat]

/-- The genuine suitable-data bound is finite, so this anisotropic moment is finite. -/
theorem suitable_unitBall_four_time_moment_lt_top_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    (∫⁻ t in J, eLpNorm (fun x ↦ u (x, t)) 4
      (volume.restrict (vec3Ball 0 1)) ^ (8 / 3 : ℝ)) < ∞ := by
  apply (suitable_unitBall_four_time_moment_localBox hsol hbox).trans_lt
  have hM := hsol.toData.essSup_sliceEnergy_lt_top hbox
  have hD : (∫⁻ z in vec3Ball 0 1 ×ˢ J, ‖Du z‖ₑ ^ (2 : ℝ)) < ∞ :=
    (lintegral_mono (fun _ ↦ le_add_left le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)
  have hJ : volume J < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top fullUnitBallH1Coefficient_ne_top)))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne))
    (ENNReal.add_lt_top.mpr ⟨hD,
      ENNReal.mul_lt_top hM hJ⟩)

/-- Actual full-ball energy gives the genuine time velocity class. -/
theorem suitable_velocityCurve_memLp_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (unitBallVelocityCurve u) 2 (volume.restrict J) :=
  unitBall_actualSliceLp_memLp_two (suitable_joint_two_localBox hsol hbox).1

/-- Actual suitable energy data give a genuine time L² Hilbert-gradient curve. -/
theorem suitable_rawGradientCurve_memLp_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (unitBallRawGradientCurve Du) 2 (volume.restrict J) := by
  apply unitBall_actualSliceLp_memLp_two
  apply MemLp.of_eval_piLp
  intro ij
  exact (((suitable_joint_two_localBox hsol hbox).2.eval ij.2).eval ij.1)

/-- The actual suitable convection tensor gives a genuine time L^{4/3} spatial L² curve. -/
theorem suitable_convectiveTensorCurve_memLp_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (unitBallConvectiveTensorCurve u) (ENNReal.ofReal (4 / 3 : ℝ))
      (volume.restrict J) := by
  have hu := (suitable_joint_two_localBox hsol hbox).1.aestronglyMeasurable
  have huProd : AEStronglyMeasurable u
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict,
      ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hu
  have hT : AEStronglyMeasurable (fun z : Vec3 × ℝ ↦ stokesOuterProduct (u z) (u z))
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict J)) :=
    stokesOuterProduct_continuous.comp_aestronglyMeasurable (huProd.prodMk huProd)
  apply memLp_iff.mpr
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_pos.mpr (by norm_num)).ne' ENNReal.ofReal_ne_top
    (aestronglyMeasurable_actualSliceLp hT (by norm_num))).mpr
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      ‖unitBallConvectiveTensorCurve u t‖ₑ ^ (4 / 3 : ℝ) ≤
        (3 : ℝ≥0∞) ^ (4 / 3 : ℝ) * eLpNorm (fun x ↦ u (x, t)) 4
          (volume.restrict (vec3Ball 0 1)) ^ (8 / 3 : ℝ) := by
    filter_upwards [suitable_unitBall_memLp_four_ae_localBox hsol hbox] with t ht
    have h := ENNReal.rpow_le_rpow (unitBallConvectiveTensorCurve_enorm_le u t ht)
      (by norm_num : (0 : ℝ) ≤ 4 / 3)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_ofNat,
      ← ENNReal.rpow_mul] at h
    norm_num only [show (2 : ℝ) * (4 / 3) = 8 / 3 by norm_num] at h
    exact h
  calc
    _ ≤ ∫⁻ t in J, (3 : ℝ≥0∞) ^ (4 / 3 : ℝ) * eLpNorm (fun x ↦ u (x, t)) 4
        (volume.restrict (vec3Ball 0 1)) ^ (8 / 3 : ℝ) := lintegral_mono_ae hpoint
    _ = (3 : ℝ≥0∞) ^ (4 / 3 : ℝ) * ∫⁻ t in J, eLpNorm (fun x ↦ u (x, t)) 4
        (volume.restrict (vec3Ball 0 1)) ^ (8 / 3 : ℝ) :=
      lintegral_const_mul' _ _
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num)).ne
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num))
      (suitable_unitBall_four_time_moment_lt_top_localBox hsol hbox)

/-- The true velocity vector force is time L². -/
theorem suitable_velocityForceCurve_memLp_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (unitBallVelocityForceCurve u) 2 (volume.restrict J) := by
  change MemLp (fun t ↦ stokesVectorForceL (vec3Ball 0 1) (unitBallVelocityCurve u t))
    2 (volume.restrict J)
  exact (suitable_velocityCurve_memLp_localBox hsol hbox).continuousLinearMap_comp
    (stokesVectorForceL (vec3Ball 0 1))

/-- The true nonlinear convection force is time L^{4/3}. -/
theorem suitable_convectiveForceCurve_memLp_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (unitBallConvectiveForceCurve u) (ENNReal.ofReal (4 / 3 : ℝ))
      (volume.restrict J) := by
  change MemLp (fun t ↦ stokesTensorForceL (vec3Ball 0 1) (unitBallConvectiveTensorCurve u t))
    (ENNReal.ofReal (4 / 3 : ℝ)) (volume.restrict J)
  exact (suitable_convectiveTensorCurve_memLp_localBox hsol hbox).continuousLinearMap_comp
    (stokesTensorForceL (vec3Ball 0 1))

/-- The true viscosity force is time L². -/
theorem suitable_viscousForceCurve_memLp_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (unitBallViscousForceCurve Du) 2 (volume.restrict J) := by
  change MemLp (fun t ↦ stokesTensorForceL (vec3Ball 0 1) (-unitBallRawGradientCurve Du t))
    2 (volume.restrict J)
  exact (suitable_rawGradientCurve_memLp_localBox hsol hbox).neg.continuousLinearMap_comp
    (stokesTensorForceL (vec3Ball 0 1))

/-- The actual velocity, convection, and viscosity forces are genuinely Bochner integrable. -/
theorem suitable_energyForceCurves_integrable_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    IntegrableOn (unitBallVelocityForceCurve u) J volume ∧
      IntegrableOn (unitBallConvectiveForceCurve u) J volume ∧
      IntegrableOn (unitBallViscousForceCurve Du) J volume := by
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr
    ((measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top).ne
  exact ⟨(suitable_velocityForceCurve_memLp_localBox hsol hbox).integrable (by norm_num),
    (suitable_convectiveForceCurve_memLp_localBox hsol hbox).integrable (by norm_num),
    (suitable_viscousForceCurve_memLp_localBox hsol hbox).integrable (by norm_num)⟩

/-- The actual force classes retain all literal compact-test pairings on the
original full ball and time interval. -/
theorem suitable_energyForceCurves_compactTests_ae_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    ∀ᵐ t ∂volume.restrict J, ∀ φ : StokesVectorTest (vec3Ball 0 1),
      unitBallVelocityForceCurve u t (stokesEnergyTest φ) =
          (∫ x in vec3Ball 0 1, ∑ i : Fin 3, u (x, t) i * φ i x) ∧
        unitBallConvectiveForceCurve u t (stokesEnergyTest φ) =
          (∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
            (u (x, t) ij.1 * u (x, t) ij.2) * (φ ij.2).partialDeriv ij.1 x) ∧
        unitBallViscousForceCurve Du t (stokesEnergyTest φ) =
          -(∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
            Du (x, t) ij.2 ij.1 * (φ ij.2).partialDeriv ij.1 x) := by
  filter_upwards [suitable_unitBall_memLp_four_ae_localBox hsol hbox,
    slice_memLp_ae_of_sws hsol hbox] with t ht hL2
  intro φ
  exact ⟨(unitBallVelocityForceCurve_compactTest u t hL2.1 φ).2,
    (unitBallConvectiveForceCurve_compactTest u t ht φ).2,
    (unitBallViscousForceCurve_compactTest Du t hL2.2 φ).2⟩

end Suitable

end FluidSingularSets
