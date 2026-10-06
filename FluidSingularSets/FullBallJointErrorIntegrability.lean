-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallJointEnergyErrors

/-!
# Genuine joint integrability of every projected-energy error

Actual suitable velocity classes, harmonic correction bounds, and smooth test
derivative bounds give joint integrability of the heat, convection, and Hessian
errors. The true projected RHS then supplies pressure-flux integrability.
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

private theorem fullBall_joint_field_top_of_bound (ρ a b : ℝ)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) {C : ℝ} (hC : ∀ z, ‖F z‖ ≤ C) :
    MemLp (fun z : fullBallCompactInterior ρ × ℝ ↦ F (z.1.1, z.2)) ⊤
      ((fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) :=
  MemLp.of_bound (hF.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    continuous_snd)).aestronglyMeasurable C (ae_of_all _ fun z ↦ hC (z.1.1, z.2))

/-- All four literal error families of every genuine joint test are jointly integrable. -/
theorem suitable_fullBall_joint_errors_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z) (hsupp : tsupport ψ ⊆ fullBallCompactInterior ρ ×ˢ Ioo a b)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    Integrable (fullBallJointHeatError u D p a b c ψ χ) volume ∧
      Integrable (fullBallJointConvectionError u D p a b c ψ χ) volume ∧
      Integrable (fullBallJointPressureError u D p a b c ψ χ) volume ∧
      Integrable (fullBallJointHarmonicError u D p a b c ψ χ) volume := by
  let μ := fullBallInteriorMeasure ρ
  let ν := volume.restrict (Ioo a b)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by
    simp only [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  let r : ℝ≥0∞ := ENNReal.ofReal (3 / 2 : ℝ)
  let : ENNReal.HolderTriple 3 3 r := by
    have h : Real.HolderTriple 3 3 (3 / 2 : ℝ) := by constructor <;> norm_num
    simpa [r] using h.ennrealOfReal
  let : ENNReal.HolderTriple r 3 1 := by
    have h : Real.HolderTriple (3 / 2 : ℝ) 3 1 := by constructor <;> norm_num
    simpa [r] using h.ennrealOfReal
  let U : fullBallCompactInterior ρ × ℝ → Vec3 := fun z ↦ u (z.1.1, z.2)
  let H : fullBallCompactInterior ρ × ℝ → Vec3 := fun z ↦
    fullBallProjectedHarmonicGradientAmbient u D p a b c (z.1.1, z.2)
  let V : fullBallCompactInterior ρ × ℝ → Vec3 := fun z ↦ U z + H z
  let B : fullBallCompactInterior ρ × ℝ → Fin 3 → Vec3 := fun z ↦
    fullBallProjectedHarmonicDerivativeAmbient u D p a b c (z.1.1, z.2)
  obtain ⟨hU, _hD, _hp⟩ := fullBallProjected_memLp hsol hbox hab hρ hρone
  obtain ⟨hH, hB⟩ := fullBallProjected_correction_joint_memLp_top
    hsol hbox hab hc hρ hρone
  have hVi (i : Fin 3) : MemLp (fun z ↦ V z i) 3 (μ.prod ν) :=
    (memLp_pi_iff.mp hU i).add ((memLp_pi_iff.mp hH i).mono_exponent le_top)
  have hVV (i : Fin 3) : MemLp (fun z ↦ V z i * V z i) r (μ.prod ν) :=
    (hVi i).mul (hVi i)
  have hΨ : MemLp (fun z : fullBallCompactInterior ρ × ℝ ↦ ψ (z.1.1, z.2)) ⊤
      (μ.prod ν) := by
    obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction hψ
    exact fullBall_joint_field_top_of_bound ρ a b hψ.1.continuous hC
  have hτ : MemLp (fun z : fullBallCompactInterior ρ × ℝ ↦ timePartial ψ (z.1.1, z.2)) ⊤
      (μ.prod ν) := by
    obtain ⟨C, hC⟩ := exists_bound_timePartial_of_mem_spaceTimeTestFunction hψ
    exact fullBall_joint_field_top_of_bound ρ a b (contDiff_timePartial hψ.1).continuous hC
  have hΛ : MemLp (fun z : fullBallCompactInterior ρ × ℝ ↦
      ∑ j, spatialSecondPartial ψ j j (z.1.1, z.2)) ⊤ (μ.prod ν) := by
    apply memLp_finsetSum
    intro j _
    obtain ⟨C, hC⟩ := exists_bound_spatialSecondPartial_of_mem_spaceTimeTestFunction hψ j j
    exact fullBall_joint_field_top_of_bound ρ a b
      (spatialPartial_contDiff (spatialPartial_contDiff hψ.1 j) j).continuous hC
  have hG (i : Fin 3) : MemLp (fun z : fullBallCompactInterior ρ × ℝ ↦
      spatialPartial ψ i (z.1.1, z.2)) ⊤ (μ.prod ν) := by
    obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hψ i
    exact fullBall_joint_field_top_of_bound ρ a b (spatialPartial_contDiff hψ.1 i).continuous hC
  have hχtop : MemLp (fun z : fullBallCompactInterior ρ × ℝ ↦ χ z.2) ⊤ (μ.prod ν) :=
    MemLp.of_bound (hχ.comp continuous_snd).aestronglyMeasurable 1
      (ae_of_all _ fun z ↦ hbχ z.2)
  have hheat (i : Fin 3) : Integrable (fun z : fullBallCompactInterior ρ × ℝ ↦
      (V z i * V z i) *
        (timePartial ψ (z.1.1, z.2) + ∑ j, spatialSecondPartial ψ j j (z.1.1, z.2)) *
          χ z.2) (μ.prod ν) :=
    (((hVV i).mul (r := r) (hτ.add hΛ)).mul (r := r) hχtop).integrable (by norm_num [r])
  have hconv (i j : Fin 3) : Integrable (fun z : fullBallCompactInterior ρ × ℝ ↦
      (V z i * V z i) * U z j * spatialPartial ψ j (z.1.1, z.2) * χ z.2) (μ.prod ν) :=
    ((((hVV i).mul (r := 1) (memLp_pi_iff.mp hU j)).mul (r := 1) (hG j)).mul
      (r := 1) hχtop).integrable (by norm_num)
  have hharm (i j : Fin 3) : Integrable (fun z : fullBallCompactInterior ρ × ℝ ↦
      (U z j * B z i j) * V z i * ψ (z.1.1, z.2) * χ z.2) (μ.prod ν) :=
    (((((memLp_pi_iff.mp hU j).mul (r := 3) (hB i j)).mul (r := r) (hVi i)).mul
      (r := r) hΨ).mul (r := r) hχtop).integrable (by norm_num [r])
  have hnorm (z : fullBallCompactInterior ρ × ℝ) :
      vec3EuclideanNorm (V z) ^ 2 = ∑ i : Fin 3, V z i * V z i := by
    rw [vec3EuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)]
    simp only [pow_two]
  have hHE : Integrable (fun z : fullBallCompactInterior ρ × ℝ ↦
      fullBallJointHeatError u D p a b c ψ χ (z.1.1, z.2)) (μ.prod ν) := by
    convert integrable_finsetSum Finset.univ (fun i _ ↦ hheat i) using 1
    funext z
    change vec3EuclideanNorm (V z) ^ 2 * _ * _ = _
    rw [hnorm]
    simp only [Fin.sum_univ_three]
    ring
  have hCE : Integrable (fun z : fullBallCompactInterior ρ × ℝ ↦
      fullBallJointConvectionError u D p a b c ψ χ (z.1.1, z.2)) (μ.prod ν) := by
    convert integrable_finsetSum Finset.univ (fun i _ ↦
      integrable_finsetSum Finset.univ (fun j _ ↦ hconv i j)) using 1
    funext z
    change vec3EuclideanNorm (V z) ^ 2 * _ * _ = _
    rw [hnorm]
    simp only [U, Fin.sum_univ_three]
    ring
  have hBE : Integrable (fun z : fullBallCompactInterior ρ × ℝ ↦
      fullBallJointHarmonicError u D p a b c ψ χ (z.1.1, z.2)) (μ.prod ν) := by
    convert integrable_finsetSum Finset.univ (fun i _ ↦
      integrable_finsetSum Finset.univ (fun j _ ↦ hharm i j)) using 1
    funext z
    simp only [fullBallJointHarmonicError, U, B, V, H,
      fullBallProjectedVelocityAmbient, Fin.sum_univ_three, Pi.add_apply]
    ring
  have transfer (F : ParabolicPoint → ℝ)
      (hF : Integrable (fun z : fullBallCompactInterior ρ × ℝ ↦ F (z.1.1, z.2)) (μ.prod ν))
      (hz : ∀ z, z ∉ tsupport ψ → F z = 0) : Integrable F volume := by
    have hi : IntegrableOn F (fullBallCompactInterior ρ ×ˢ Ioo a b) volume :=
      memLp_one_iff_integrable.mp ((memLp_fullBallInterior_product_ambient_iff
        ρ F 1 (Ioo a b)).mpr (memLp_one_iff_integrable.mpr hF))
    exact hi.integrable_of_forall_notMem_eq_zero fun z h ↦ hz z (fun h' ↦ h (hsupp h'))
  have hHE' : Integrable (fullBallJointHeatError u D p a b c ψ χ) volume :=
    transfer _ hHE fun z hz ↦ (fullBallJointEnergyErrors_zero_off_tsupport
      u D p a b c ψ χ z hz).1
  have hCE' : Integrable (fullBallJointConvectionError u D p a b c ψ χ) volume :=
    transfer _ hCE fun z hz ↦ (fullBallJointEnergyErrors_zero_off_tsupport
      u D p a b c ψ χ z hz).2.1
  have hBE' : Integrable (fullBallJointHarmonicError u D p a b c ψ χ) volume :=
    transfer _ hBE fun z hz ↦ (fullBallJointEnergyErrors_zero_off_tsupport
      u D p a b c ψ χ z hz).2.2.2
  have hR := suitable_fullBall_native_projected_rhs_integrable
    hρ hρone hsol hbox hab hc hψ hnψ hsupp
  have hRχ : Integrable (fun z : ParabolicPoint ↦
      fullBallNativeProjectedRhsDensity u D p a b c ψ z * χ z.2) volume :=
    hR.mul_bdd (hχ.comp continuous_snd_parabolicPoint).aestronglyMeasurable
      (ae_of_all _ fun z ↦ hbχ z.2)
  have hPE : Integrable (fullBallJointPressureError u D p a b c ψ χ) volume := by
    have hi := (((hRχ.sub hHE').sub hCE').sub (hBE'.const_mul 2)).const_mul (1 / 2 : ℝ)
    apply hi.congr
    exact ae_of_all _ fun z ↦ by
      change (1 / 2) * (((fullBallNativeProjectedRhsDensity u D p a b c ψ z * χ z.2 -
        fullBallJointHeatError u D p a b c ψ χ z) -
        fullBallJointConvectionError u D p a b c ψ χ z) -
        2 * fullBallJointHarmonicError u D p a b c ψ χ z) =
          fullBallJointPressureError u D p a b c ψ χ z
      have he := fullBallNativeProjectedRhsDensity_joint_errors_eq u D p a b c ψ χ z
      linarith
  exact ⟨hHE', hCE', hPE, hBE'⟩

end FluidSingularSets
