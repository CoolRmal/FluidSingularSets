-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallProjectedData
public import FluidSingularSets.FullBallProjectedGradientControl
public import FluidSingularSets.TruncatedCylinderExhaustion
public import FluidSingularSets.FullBallCylinderCaccioppoli
public import FluidSingularSets.ProjectedRadiusInterpolation
public import CKN.Main.TheoremB
public import CKN.Foundation.Parabolic.BallDisplays
public import CKN.Statements.SpatialGradientSq

/-!
# Genuine vanishing gradient correction at shrinking cylinders

The actual harmonic correction has a joint essential bound derived from
suitable slice energy. Its normalized coordinate-gradient mass therefore
vanishes at the fourth radius power. Original and projected gradient masses
are compared using their literal pointwise derivative identity.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Native backward-cylinder volume has the actual fifth radius power. -/
theorem volume_centered_backwardCylinder {r : ℝ} (hr : 0 ≤ r) :
    volume (vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) 0 : Set ParabolicPoint) =
      ENNReal.ofReal ((Real.pi * 4 / 3) * r ^ 5) := by
  change (volume : Measure Vec3).prod (volume : Measure ℝ)
    (vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) 0) = _
  rw [Measure.prod_prod, volume_vec3Ball_zero, Real.volume_Ioo]
  simp only [sub_neg_eq_add, zero_add, ← ENNReal.ofReal_pow hr]
  rw [← ENNReal.ofReal_mul (pow_nonneg hr 3),
    ← ENNReal.ofReal_mul (by positivity [Real.pi_pos] : 0 ≤ r ^ 3 * (Real.pi * 4 / 3))]
  congr 1
  ring

/-- The true suitable harmonic derivative contributes only a vanishing fourth-order mass. -/
theorem suitable_fullBall_harmonic_normalized_gradient_le_fourth
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      (ENNReal.ofReal r)⁻¹ *
        (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) 0,
          ENNReal.ofReal (projectedGradientSquare
            (fullBallProjectedHarmonicDerivativeAmbient u D p (-1) 0 (-(1 / 2)) z))) ≤
        ENNReal.ofReal (C * r ^ 4) := by
  let F := fullBallProjectedHarmonicDerivativeAmbient u D p (-1) 0 (-(1 / 2))
  let μ : Measure ParabolicPoint :=
    volume.restrict (fullBallCompactInterior (1 / 2) ×ˢ Ioo (-1 : ℝ) 0)
  have hF : MemLp F ⊤ μ := (fullBallProjected_correction_ambient_joint_memLp_top
    hsol hbox (by norm_num) (by constructor <;> norm_num)
      (ρ := 1 / 2) (by norm_num) (by norm_num)).2
  let L : ℝ := (eLpNorm F ⊤ μ).toReal
  let C : ℝ := 9 * L ^ 2 * (Real.pi * 4 / 3)
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hae : ∀ᵐ z : ParabolicPoint ∂μ, ‖F z‖ₑ ≤ ENNReal.ofReal L := by
    have hh : ∀ᵐ z : ParabolicPoint ∂μ, ‖F z‖ₑ ≤ eLpNorm F ⊤ μ := by
      rw [eLpNorm_exponent_top hF.aestronglyMeasurable]
      exact ae_le_eLpNormEssSup
    simpa only [L, ENNReal.ofReal_toReal hF.eLpNorm_ne_top] using hh
  have hden : ∀ᵐ z : ParabolicPoint ∂μ,
      ENNReal.ofReal (projectedGradientSquare (F z)) ≤ ENNReal.ofReal (9 * L ^ 2) := by
    filter_upwards [hae] with z hz
    calc
      _ ≤ 9 * ‖F z‖ₑ ^ (2 : ℕ) := by
        simpa only [ENNReal.rpow_ofNat] using projectedGradientSquare_enorm_le_nine (F z)
      _ ≤ 9 * ENNReal.ofReal L ^ (2 : ℕ) :=
        mul_le_mul' le_rfl (pow_le_pow_left₀ (by positivity) hz 2)
      _ = _ := by rw [← ENNReal.ofReal_pow hL, ENNReal.ofReal_mul (by norm_num)]; norm_num
  refine ⟨C, by dsimp only [C]; positivity [Real.pi_pos], ?_⟩
  intro r hr hrquarter
  let A : Set ParabolicPoint := vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) 0
  have hsub : A ⊆ fullBallCompactInterior (1 / 2) ×ˢ Ioo (-1 : ℝ) 0 := by
    intro z hz
    refine ⟨subset_closure (vec3Ball_mono (by linarith : r ≤ (1 / 2 : ℝ)) hz.1),
      ?_, hz.2.2⟩
    nlinarith [hz.2.1]
  have hmass : (∫⁻ z : ParabolicPoint in A, ENNReal.ofReal (projectedGradientSquare (F z))) ≤
      ENNReal.ofReal (9 * L ^ 2) * volume A := by
    calc
      _ ≤ ∫⁻ _z : ParabolicPoint in A, ENNReal.ofReal (9 * L ^ 2) :=
        lintegral_mono_ae (hden.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub)))
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  calc
    _ ≤ (ENNReal.ofReal r)⁻¹ * (ENNReal.ofReal (9 * L ^ 2) * volume A) :=
      mul_le_mul' le_rfl hmass
    _ = _ := by
      rw [← ENNReal.ofReal_inv_of_pos hr, show volume A =
        ENNReal.ofReal ((Real.pi * 4 / 3) * r ^ 5) from volume_centered_backwardCylinder hr.le,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 9 * L ^ 2),
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
      congr 1
      dsimp only [C]
      field_simp [hr.ne']

/-- The genuine derivative identity compares original and projected coordinate masses. -/
theorem fullBall_original_coordinate_mass_le_projected_and_harmonic
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c r : ℝ)
    (hH : AEMeasurable (fun z : ParabolicPoint ↦ ENNReal.ofReal
      (projectedGradientSquare
        (fullBallProjectedHarmonicDerivativeAmbient u D p a b c z)))
      (volume.restrict (vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) 0))) :
    coordinateCylinderMass D r ≤
      2 * (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) 0,
        ENNReal.ofReal (projectedGradientSquare
          (fullBallProjectedVelocityDerivativeAmbient u D p a b c z))) +
      2 * (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) 0,
        ENNReal.ofReal (projectedGradientSquare
          (fullBallProjectedHarmonicDerivativeAmbient u D p a b c z))) := by
  have hp (z : ParabolicPoint) : ENNReal.ofReal (projectedGradientSquare (D z)) ≤
      2 * ENNReal.ofReal (projectedGradientSquare
        (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) +
      2 * ENNReal.ofReal (projectedGradientSquare
        (fullBallProjectedHarmonicDerivativeAmbient u D p a b c z)) := by
    have hs := projectedGradientSquare_sub_le_two
      (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)
      (fullBallProjectedHarmonicDerivativeAmbient u D p a b c z)
    rw [fullBallProjectedVelocityDerivativeAmbient_sub_harmonic] at hs
    have hh := ENNReal.ofReal_le_ofReal hs
    rw [ENNReal.ofReal_add
      (mul_nonneg (by norm_num) (projectedGradientSquare_nonneg _))
      (mul_nonneg (by norm_num) (projectedGradientSquare_nonneg _)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hh
    simpa only [ENNReal.ofReal_ofNat] using hh
  calc
    _ ≤ ∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) 0,
        2 * ENNReal.ofReal (projectedGradientSquare
          (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) +
        2 * ENNReal.ofReal (projectedGradientSquare
          (fullBallProjectedHarmonicDerivativeAmbient u D p a b c z)) := lintegral_mono hp
    _ = _ := by
      rw [lintegral_add_right' _ (hH.const_mul 2),
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]

/-- The exact original CKN density is the literal coordinate mass, including its terminal slice. -/
theorem normalized_original_gradient_eq_coordinate_mass
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3) (r : ℝ) :
    (ENNReal.ofReal r)⁻¹ * (∫⁻ z in parabolicCylinder 0 0 r,
      ENNReal.ofReal (spatialGradientSq u D z)) =
        (ENNReal.ofReal r)⁻¹ * coordinateCylinderMass D r := by
  congr 1
  simpa only [coordinateCylinderMass, parabolicCylinder, zero_sub, spatialGradientSq,
    projectedGradientSquare] using (lintegral_cylinder_Ioo_eq_Ioc (vec3Ball 0 r)
      (-(r ^ 2)) 0 (fun z ↦ ENNReal.ofReal (projectedGradientSquare (D z)))).symm

/-- Actual suitability transfers small projected energy to the original gradient limsup. -/
theorem suitable_fullBall_original_gradient_limsup_le_projected_bound
    {Ω : Set Vec3} {I : Set ℝ} {q K : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0)) (hK : 0 ≤ K)
    (hE : ∀ᶠ r : ℝ in 𝓝[>] 0,
      fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 (-(1 / 2)) r 0 ≤
        ENNReal.ofReal K) :
    limsup (fun r : ℝ ↦ (ENNReal.ofReal r)⁻¹ *
      (∫⁻ z in parabolicCylinder 0 0 r, ENNReal.ofReal (spatialGradientSq u D z)))
        (𝓝[>] (0 : ℝ)) ≤ ENNReal.ofReal (2 * K) := by
  obtain ⟨C, hC, hCb⟩ := suitable_fullBall_harmonic_normalized_gradient_le_fourth hsol hbox
  have hmajor : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (2 * K + 2 * C * r ^ 4))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (2 * K))) := by
    have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
      continuous_id.tendsto 0 |>.mono_left inf_le_left
    have ht : Tendsto (fun r : ℝ ↦ 2 * K + 2 * C * r ^ 4)
        (𝓝[>] 0) (𝓝 (2 * K + 2 * C * 0 ^ 4)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul (hid.pow 4))
    simpa using ENNReal.tendsto_ofReal ht
  have hle : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (ENNReal.ofReal r)⁻¹ * (∫⁻ z in parabolicCylinder 0 0 r,
        ENNReal.ofReal (spatialGradientSq u D z)) ≤
          ENNReal.ofReal (2 * K + 2 * C * r ^ 4) := by
    filter_upwards [self_mem_nhdsWithin, hE,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono inf_le_left]
        with r hr hEr hrq
    change 0 < r at hr
    let A : Set ParabolicPoint := vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) 0
    have hsub : A ⊆ fullBallCompactInterior (1 / 2) ×ˢ Ioo (-1 : ℝ) 0 := by
      intro z hz
      refine ⟨subset_closure (vec3Ball_mono (by linarith : r ≤ (1 / 2 : ℝ)) hz.1),
        ?_, hz.2.2⟩
      nlinarith [hz.2.1]
    have hH := (fullBallProjected_correction_ambient_joint_memLp_top
      (c := -(1 / 2)) hsol hbox (by norm_num) (by constructor <;> norm_num)
        (ρ := 1 / 2) (by norm_num) (by norm_num)).2
    have hm := hH.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume hsub)
    have hc : Continuous (fun W : Fin 3 → Vec3 ↦
        ENNReal.ofReal (projectedGradientSquare W)) := by
      unfold projectedGradientSquare
      exact ENNReal.continuous_ofReal.comp (by fun_prop)
    have hHm := (hc.comp_aestronglyMeasurable hm).aemeasurable
    have hmass := fullBall_original_coordinate_mass_le_projected_and_harmonic
      u D p (-1) 0 (-(1 / 2)) r hHm
    have hDle : (ENNReal.ofReal r)⁻¹ *
        (∫⁻ z : ParabolicPoint in A, ENNReal.ofReal (projectedGradientSquare
          (fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 (-(1 / 2)) z))) ≤
        ENNReal.ofReal K := by
      rw [fullBallNormalizedProjectedIterationEnergy,
        fullBallProjectedIterationDissipation, zero_sub,
        ENNReal.ofReal_inv_of_pos hr] at hEr
      exact (mul_le_mul' le_rfl le_add_self).trans hEr
    calc
      _ = (ENNReal.ofReal r)⁻¹ * coordinateCylinderMass D r :=
        normalized_original_gradient_eq_coordinate_mass u D r
      _ ≤ (ENNReal.ofReal r)⁻¹ *
          (2 * (∫⁻ z : ParabolicPoint in A, ENNReal.ofReal (projectedGradientSquare
            (fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 (-(1 / 2)) z))) +
            2 * (∫⁻ z : ParabolicPoint in A, ENNReal.ofReal (projectedGradientSquare
              (fullBallProjectedHarmonicDerivativeAmbient u D p (-1) 0 (-(1 / 2)) z)))) :=
        mul_le_mul' le_rfl hmass
      _ = 2 * ((ENNReal.ofReal r)⁻¹ *
          (∫⁻ z : ParabolicPoint in A, ENNReal.ofReal (projectedGradientSquare
            (fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 (-(1 / 2)) z)))) +
            2 * ((ENNReal.ofReal r)⁻¹ *
              (∫⁻ z : ParabolicPoint in A, ENNReal.ofReal (projectedGradientSquare
                (fullBallProjectedHarmonicDerivativeAmbient u D p (-1) 0 (-(1 / 2)) z)))) :=
        by ring
      _ ≤ 2 * ENNReal.ofReal K + 2 * ENNReal.ofReal (C * r ^ 4) :=
        add_le_add (mul_le_mul' le_rfl hDle) (mul_le_mul' le_rfl (hCb r hr hrq.le))
      _ = _ := by
        rw [show 2 * K + 2 * C * r ^ 4 = 2 * K + 2 * (C * r ^ 4) by ring,
          ENNReal.ofReal_add (mul_nonneg (by norm_num) hK)
            (by positivity : 0 ≤ 2 * (C * r ^ 4)),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num only [ENNReal.ofReal_ofNat]
  exact (limsup_le_limsup hle).trans_eq hmajor.limsup_eq

end FluidSingularSets
