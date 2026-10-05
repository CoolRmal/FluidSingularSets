-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesPressureCurves
public import FluidSingularSets.StokesVectorForceLinear
public import FluidSingularSets.SliceLpMoments

/-!
# Actual time-integrable energy forces

The true suitable velocity, convective tensor, and derivative slices give
genuine L², L^{4/3}, and L² curves into their spatial L² spaces. The constructed
continuous force maps yield actual Bochner-integrable energy-dual sources,
with the physical convection and viscosity signs. At every good slice their
pairings are the literal suitable-solution test integrals.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

-- Pin the canonical operator-space instance before generalized Bochner integrals.
local instance (U : Set Vec3) : NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance (U : Set Vec3) : NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

private theorem energyForce_ball_eq {r : ℝ} (hr : 0 < r) :
    euclideanBall (0 : Vec3) r = vec3Ball 0 r := by
  ext x
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr, mem_vec3Ball]
  simp only [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/-- The genuine spatial L² velocity class at each time. -/
def unitBallVelocityCurve (u : ParabolicPoint → Vec3) (t : ℝ) :
    Lp Vec3 2 (volume.restrict (vec3Ball 0 1)) :=
  actualSliceLp (μ := volume.restrict (vec3Ball 0 1)) (p := 2) u t

/-- The genuine spatial L² class of the actual convective tensor. -/
def unitBallConvectiveTensorCurve (u : ParabolicPoint → Vec3) (t : ℝ) :
    StokesGradientL2 (vec3Ball 0 1) :=
  actualSliceLp (μ := volume.restrict (vec3Ball 0 1)) (p := 2)
    (fun z : Vec3 × ℝ ↦ stokesOuterProduct (u z) (u z)) t

/-- The actual derivative array in the derivative-first spatial Hilbert matrix convention. -/
def unitBallRawGradientCurve (D : ParabolicPoint → Fin 3 → Vec3) (t : ℝ) :
    StokesGradientL2 (vec3Ball 0 1) :=
  actualSliceLp (μ := volume.restrict (vec3Ball 0 1)) (p := 2)
    (fun z : Vec3 × ℝ ↦ stokesRawGradientMatrix (fun x ↦ D (x, z.2)) z.1) t

/-- The actual velocity vector force on the completed test energy space. -/
def unitBallVelocityForceCurve (u : ParabolicPoint → Vec3) (t : ℝ) :
    StokesEnergyForce (vec3Ball 0 1) :=
  stokesVectorForceL (vec3Ball 0 1) (unitBallVelocityCurve u t)

/-- The actual convection force `-div (u ⊗ u)`. -/
def unitBallConvectiveForceCurve (u : ParabolicPoint → Vec3) (t : ℝ) :
    StokesEnergyForce (vec3Ball 0 1) :=
  stokesTensorForceL (vec3Ball 0 1) (unitBallConvectiveTensorCurve u t)

/-- The actual viscosity force `+div Du`. -/
def unitBallViscousForceCurve (D : ParabolicPoint → Fin 3 → Vec3) (t : ℝ) :
    StokesEnergyForce (vec3Ball 0 1) :=
  stokesTensorForceL (vec3Ball 0 1) (-unitBallRawGradientCurve D t)

/-- The nonlinear pressure curve is exactly the projection of the true convection force. -/
theorem unitBallConvectivePressureCurve_eq_projection (u : ParabolicPoint → Vec3) (t : ℝ) :
    unitBallConvectivePressureCurve u t = unitBallStokesPressureL
      (unitBallConvectiveForceCurve u t) := rfl

/-- The viscous pressure curve is exactly the projection of the true viscosity force. -/
theorem unitBallViscousPressureCurve_eq_projection (D : ParabolicPoint → Fin 3 → Vec3) (t : ℝ) :
    unitBallViscousPressureCurve D t = unitBallStokesPressureL
      (unitBallViscousForceCurve D t) := rfl

/-- Every joint L² field has a genuine time L² curve of its actual spatial L² classes. -/
theorem unitBall_actualSliceLp_memLp_two {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {F : ParabolicPoint → E} {J : Set ℝ}
    (hF : MemLp F 2 (volume.restrict (vec3Ball 0 1 ×ˢ J))) :
    MemLp (actualSliceLp (μ := volume.restrict (vec3Ball 0 1)) (p := 2) F)
      2 (volume.restrict J) := by
  have hprod : MemLp F 2 ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hF
  exact actualSliceLp_memLp_of_prod_memLp hprod (by norm_num)

/-- At every good velocity slice the tensor is its genuine actual `toLp` class. -/
theorem unitBallConvectiveTensorCurve_eq (u : ParabolicPoint → Vec3) (t : ℝ)
    (ht : MemLp (fun x ↦ u (x, t)) 4 (volume.restrict (vec3Ball 0 1))) :
    unitBallConvectiveTensorCurve u t = stokesConvectiveTensorL2 (fun x ↦ u (x, t)) ht := by
  unfold unitBallConvectiveTensorCurve actualSliceLp
  rw [dite_eq_left (stokesConvectiveTensor_memLp (fun x ↦ u (x, t)) ht)]
  rfl

/-- At every good derivative slice the curve is its genuine transposed gradient class. -/
theorem unitBallRawGradientCurve_eq (D : ParabolicPoint → Fin 3 → Vec3) (t : ℝ)
    (ht : MemLp (fun x ↦ D (x, t)) 2 (volume.restrict (vec3Ball 0 1))) :
    unitBallRawGradientCurve D t = stokesRawGradientL2 (fun x ↦ D (x, t)) ht := by
  unfold unitBallRawGradientCurve actualSliceLp
  rw [dite_eq_left (stokesRawGradientMatrix_memLp (fun x ↦ D (x, t)) ht)]
  rfl

/-- The true convective tensor norm satisfies genuine spatial Hölder control. -/
theorem unitBallConvectiveTensorCurve_enorm_le (u : ParabolicPoint → Vec3) (t : ℝ)
    (ht : MemLp (fun x ↦ u (x, t)) 4 (volume.restrict (vec3Ball 0 1))) :
    ‖unitBallConvectiveTensorCurve u t‖ₑ ≤
      3 * eLpNorm (fun x ↦ u (x, t)) 4 (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  rw [unitBallConvectiveTensorCurve_eq u t ht, stokesConvectiveTensorL2, Lp.enorm_toLp]
  exact stokesConvectiveTensor_eLpNorm_le (fun x ↦ u (x, t)) ht

/-- At every actual L² velocity slice the true vector-force pairing is the raw test integral. -/
theorem unitBallVelocityForceCurve_compactTest (u : ParabolicPoint → Vec3) (t : ℝ)
    (ht : MemLp (fun x ↦ u (x, t)) 2 (volume.restrict (vec3Ball 0 1)))
    (φ : StokesVectorTest (vec3Ball 0 1)) :
    Integrable (fun x ↦ ∑ i : Fin 3, u (x, t) i * φ i x)
        (volume.restrict (vec3Ball 0 1)) ∧
      unitBallVelocityForceCurve u t (stokesEnergyTest φ) =
        ∫ x in vec3Ball 0 1, ∑ i : Fin 3, u (x, t) i * φ i x := by
  have hae : (fun x ↦ ∑ i : Fin 3, unitBallVelocityCurve u t x i * φ i x)
      =ᵐ[volume.restrict (vec3Ball 0 1)] (fun x ↦ ∑ i : Fin 3, u (x, t) i * φ i x) := by
    filter_upwards [actualSliceLp_ae u t ht] with x hx
    change unitBallVelocityCurve u t x = u (x, t) at hx
    rw [hx]
  refine ⟨(integrable_finsetSum Finset.univ
    (fun i _ ↦ stokesVectorForce_testProduct_integrable (unitBallVelocityCurve u t) φ i)).congr
      hae, ?_⟩
  change stokesVectorForceL (vec3Ball 0 1) (unitBallVelocityCurve u t) (stokesEnergyTest φ) = _
  rw [stokesVectorForceL_apply, stokesVectorForce_test (isOpen_vec3Ball 0 1).measurableSet
    volume_vec3Ball_lt_top.ne]
  exact integral_congr_ae hae

/-- At every actual L⁴ velocity slice the force is the true quadratic convection pairing. -/
theorem unitBallConvectiveForceCurve_compactTest (u : ParabolicPoint → Vec3) (t : ℝ)
    (ht : MemLp (fun x ↦ u (x, t)) 4 (volume.restrict (vec3Ball 0 1)))
    (φ : StokesVectorTest (vec3Ball 0 1)) :
    Integrable (fun x ↦ ∑ ij : Fin 3 × Fin 3,
      (u (x, t) ij.1 * u (x, t) ij.2) * (φ ij.2).partialDeriv ij.1 x)
        (volume.restrict (vec3Ball 0 1)) ∧
      unitBallConvectiveForceCurve u t (stokesEnergyTest φ) =
        ∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
          (u (x, t) ij.1 * u (x, t) ij.2) * (φ ij.2).partialDeriv ij.1 x := by
  unfold unitBallConvectiveForceCurve
  rw [unitBallConvectiveTensorCurve_eq u t ht, stokesTensorForceL_apply]
  exact stokesConvectiveTensorL2_compactTest (fun x ↦ u (x, t)) ht φ

/-- At every actual L² derivative slice the viscosity force has the true negative pairing. -/
theorem unitBallViscousForceCurve_compactTest (D : ParabolicPoint → Fin 3 → Vec3) (t : ℝ)
    (ht : MemLp (fun x ↦ D (x, t)) 2 (volume.restrict (vec3Ball 0 1)))
    (φ : StokesVectorTest (vec3Ball 0 1)) :
    Integrable (fun x ↦ ∑ ij : Fin 3 × Fin 3,
      D (x, t) ij.2 ij.1 * (φ ij.2).partialDeriv ij.1 x)
        (volume.restrict (vec3Ball 0 1)) ∧
      unitBallViscousForceCurve D t (stokesEnergyTest φ) =
        -(∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
          D (x, t) ij.2 ij.1 * (φ ij.2).partialDeriv ij.1 x) := by
  have hae : (fun x ↦ ∑ ij : Fin 3 × Fin 3,
      stokesRawGradientL2 (fun y ↦ D (y, t)) ht x ij * (φ ij.2).partialDeriv ij.1 x)
      =ᵐ[volume.restrict (vec3Ball 0 1)] (fun x ↦ ∑ ij : Fin 3 × Fin 3,
        D (x, t) ij.2 ij.1 * (φ ij.2).partialDeriv ij.1 x) := by
    filter_upwards [(stokesRawGradientMatrix_memLp (fun x ↦ D (x, t)) ht).coeFn_toLp]
      with x hx
    change stokesRawGradientL2 (fun y ↦ D (y, t)) ht x =
      stokesRawGradientMatrix (fun y ↦ D (y, t)) x at hx
    rw [hx]
    rfl
  obtain ⟨hprod, hpair⟩ :=
    stokesTensorForce_compactTest (stokesRawGradientL2 (fun x ↦ D (x, t)) ht) φ
  refine ⟨hprod.congr hae, ?_⟩
  unfold unitBallViscousForceCurve
  rw [unitBallRawGradientCurve_eq D t ht, map_neg, neg_apply, stokesTensorForceL_apply,
    hpair, integral_congr_ae hae]

section Suitable

variable {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
  {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

private theorem suitable_joint_two (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    MemLp u 2 (volume.restrict (vec3Ball 0 1 ×ˢ J)) ∧
      MemLp Du 2 (volume.restrict (vec3Ball 0 1 ×ˢ J)) := by
  have hsub : vec3Ball (0 : Vec3) 1 ×ˢ J ⊆ euclideanBall 0 2 ×ˢ J :=
    Set.prod_mono
      (by rw [energyForce_ball_eq (by norm_num : (0 : ℝ) < 2)];
          exact vec3Ball_mono (by norm_num)) Subset.rfl
  have hu : MemLp u 2 (volume.restrict (euclideanBall 0 2 ×ˢ J)) := by
    apply memLp_iff.mpr
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      (hsol.toData.aestronglyMeasurable_velocity hbox)).mpr
    rw [ENNReal.toReal_ofNat]
    exact (lintegral_mono (fun _ ↦ le_add_right le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)
  have hD : MemLp Du 2 (volume.restrict (euclideanBall 0 2 ×ˢ J)) := by
    apply memLp_iff.mpr
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      (hsol.toData.aestronglyMeasurable_gradient hbox)).mpr
    rw [ENNReal.toReal_ofNat]
    exact (lintegral_mono (fun _ ↦ le_add_left le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)
  exact ⟨hu.mono_measure (Measure.restrict_mono hsub le_rfl),
    hD.mono_measure (Measure.restrict_mono hsub le_rfl)⟩

/-- Actual suitable energy data give a genuine time L² velocity-class curve. -/
theorem suitable_velocityCurve_memLp
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    MemLp (unitBallVelocityCurve u) 2 (volume.restrict J) :=
  unitBall_actualSliceLp_memLp_two (suitable_joint_two hsol hbox).1

/-- Actual suitable energy data give a genuine time L² Hilbert-gradient curve. -/
theorem suitable_rawGradientCurve_memLp
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    MemLp (unitBallRawGradientCurve Du) 2 (volume.restrict J) := by
  apply unitBall_actualSliceLp_memLp_two
  apply MemLp.of_eval_piLp
  intro ij
  exact (((suitable_joint_two hsol hbox).2.eval ij.2).eval ij.1)

/-- The actual suitable convection tensor gives a genuine time L^{4/3} spatial L² curve. -/
theorem suitable_convectiveTensorCurve_memLp
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    MemLp (unitBallConvectiveTensorCurve u) (ENNReal.ofReal (4 / 3 : ℝ))
      (volume.restrict J) := by
  have hu := (suitable_joint_two hsol hbox).1.aestronglyMeasurable
  have huProd : AEStronglyMeasurable u
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
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
          (volume.restrict (euclideanBall 0 1)) ^ (8 / 3 : ℝ) := by
    filter_upwards [suitable_unitBall_memLp_four_ae hsol hbox] with t ht
    rw [energyForce_ball_eq (by norm_num : (0 : ℝ) < 1)] at ht ⊢
    have h := ENNReal.rpow_le_rpow (unitBallConvectiveTensorCurve_enorm_le u t ht)
      (by norm_num : (0 : ℝ) ≤ 4 / 3)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_ofNat,
      ← ENNReal.rpow_mul] at h
    norm_num only [show (2 : ℝ) * (4 / 3) = 8 / 3 by norm_num] at h
    exact h
  calc
    _ ≤ ∫⁻ t in J, (3 : ℝ≥0∞) ^ (4 / 3 : ℝ) * eLpNorm (fun x ↦ u (x, t)) 4
        (volume.restrict (euclideanBall 0 1)) ^ (8 / 3 : ℝ) := lintegral_mono_ae hpoint
    _ = (3 : ℝ≥0∞) ^ (4 / 3 : ℝ) * ∫⁻ t in J, eLpNorm (fun x ↦ u (x, t)) 4
        (volume.restrict (euclideanBall 0 1)) ^ (8 / 3 : ℝ) :=
      lintegral_const_mul' _ _
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num)).ne
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num))
      (suitable_unitBall_four_time_moment_lt_top hsol hbox)

/-- The true velocity vector force is time L². -/
theorem suitable_velocityForceCurve_memLp
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    MemLp (unitBallVelocityForceCurve u) 2 (volume.restrict J) := by
  change MemLp (fun t ↦ stokesVectorForceL (vec3Ball 0 1) (unitBallVelocityCurve u t))
    2 (volume.restrict J)
  exact (suitable_velocityCurve_memLp hsol hbox).continuousLinearMap_comp
    (stokesVectorForceL (vec3Ball 0 1))

/-- The true nonlinear convection force is time L^{4/3}. -/
theorem suitable_convectiveForceCurve_memLp
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    MemLp (unitBallConvectiveForceCurve u) (ENNReal.ofReal (4 / 3 : ℝ))
      (volume.restrict J) := by
  change MemLp (fun t ↦ stokesTensorForceL (vec3Ball 0 1) (unitBallConvectiveTensorCurve u t))
    (ENNReal.ofReal (4 / 3 : ℝ)) (volume.restrict J)
  exact (suitable_convectiveTensorCurve_memLp hsol hbox).continuousLinearMap_comp
    (stokesTensorForceL (vec3Ball 0 1))

/-- The true viscosity force is time L². -/
theorem suitable_viscousForceCurve_memLp
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    MemLp (unitBallViscousForceCurve Du) 2 (volume.restrict J) := by
  change MemLp (fun t ↦ stokesTensorForceL (vec3Ball 0 1) (-unitBallRawGradientCurve Du t))
    2 (volume.restrict J)
  exact (suitable_rawGradientCurve_memLp hsol hbox).neg.continuousLinearMap_comp
    (stokesTensorForceL (vec3Ball 0 1))

/-- The actual velocity, convection, and viscosity forces are genuinely Bochner integrable. -/
theorem suitable_energyForceCurves_integrable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    IntegrableOn (unitBallVelocityForceCurve u) J volume ∧
      IntegrableOn (unitBallConvectiveForceCurve u) J volume ∧
      IntegrableOn (unitBallViscousForceCurve Du) J volume := by
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr
    ((measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top).ne
  exact ⟨(suitable_velocityForceCurve_memLp hsol hbox).integrable (by norm_num),
    (suitable_convectiveForceCurve_memLp hsol hbox).integrable (by norm_num),
    (suitable_viscousForceCurve_memLp hsol hbox).integrable (by norm_num)⟩

/-- Almost every actual suitable slice gives all three literal compact-test force pairings. -/
theorem suitable_energyForceCurves_compactTests_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    ∀ᵐ t ∂volume.restrict J, ∀ φ : StokesVectorTest (vec3Ball 0 1),
      unitBallVelocityForceCurve u t (stokesEnergyTest φ) =
          (∫ x in vec3Ball 0 1, ∑ i : Fin 3, u (x, t) i * φ i x) ∧
        unitBallConvectiveForceCurve u t (stokesEnergyTest φ) =
          (∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
            (u (x, t) ij.1 * u (x, t) ij.2) * (φ ij.2).partialDeriv ij.1 x) ∧
        unitBallViscousForceCurve Du t (stokesEnergyTest φ) =
          -(∫ x in vec3Ball 0 1, ∑ ij : Fin 3 × Fin 3,
            Du (x, t) ij.2 ij.1 * (φ ij.2).partialDeriv ij.1 x) := by
  have hsub : vec3Ball (0 : Vec3) 1 ⊆ euclideanBall 0 2 := by
    rw [energyForce_ball_eq (by norm_num : (0 : ℝ) < 2)]
    exact vec3Ball_mono (by norm_num)
  filter_upwards [suitable_unitBall_memLp_four_ae hsol hbox,
    slice_memLp_ae_of_sws hsol hbox] with t ht hL2
  rw [energyForce_ball_eq (by norm_num : (0 : ℝ) < 1)] at ht
  intro φ
  exact ⟨(unitBallVelocityForceCurve_compactTest u t
      (hL2.1.mono_measure (Measure.restrict_mono hsub le_rfl)) φ).2,
    (unitBallConvectiveForceCurve_compactTest u t ht φ).2,
    (unitBallViscousForceCurve_compactTest Du t
      (hL2.2.mono_measure (Measure.restrict_mono hsub le_rfl)) φ).2⟩

end Suitable

end FluidSingularSets
