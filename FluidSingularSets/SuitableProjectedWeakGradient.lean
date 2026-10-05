-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedCutoffMixedEnergy
public import FluidSingularSets.SuitableProjectedLocalEnergy
public import FluidSingularSets.SuitableViscousPressureHarmonic

/-!
# Actual weak spatial gradient of the projected velocity

The continuous harmonic correction and its canonical Hessian are the gradient
and Hessian of the same genuine pressure representative at every time. Their
actual spatial weak-gradient identity therefore follows from the proved C²
pressure regularity, before using the suitable weak solution's own gradients.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance projectedWeakForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance projectedWeakForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The actual harmonic potential of the recovered force primitive, with the physical sign. -/
def suitableProjectedHarmonicPotential
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ t : ℝ) : Vec3 → ℝ :=
  harmonicSpatialPressureRepresentative
    (-averagedTimePrimitive (unitBallVelocityForceCurve u)
      (unitBallMomentumForceCurve u D p) (t₀ - 4) (t₀ + 4) t₀ t)

/-- An ambient representative of the actual compact-interior harmonic correction. -/
def suitableProjectedHarmonicGradientAmbient
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) (z : ParabolicPoint) : Vec3 :=
  classicalGradient (suitableProjectedHarmonicPotential u D p t₀ z.2) z.1

/-- Its literal ambient Hessian in the original component/derivative index order. -/
def suitableProjectedHarmonicDerivativeAmbient
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) (z : ParabolicPoint) : Fin 3 → Vec3 :=
  fun i j ↦ mixedSecond (suitableProjectedHarmonicPotential u D p t₀ z.2) j i z.1

/-- The actual projected velocity represented on ambient spatial coordinates. -/
def suitableProjectedVelocityAmbient
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) (z : ParabolicPoint) : Vec3 :=
  u z + suitableProjectedHarmonicGradientAmbient u D p t₀ z

/-- The actual proposed gradient is the original gradient plus the true harmonic Hessian. -/
def suitableProjectedVelocityDerivativeAmbient
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) (z : ParabolicPoint) : Fin 3 → Vec3 :=
  D z + suitableProjectedHarmonicDerivativeAmbient u D p t₀ z

variable (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
  (p : ParabolicPoint → ℝ) (t₀ : ℝ)

/-- The ambient gradient equals the frozen actual continuous time representative everywhere. -/
theorem suitableProjectedHarmonicGradientAmbient_eq_compact
    (x : unitBallPressureCompactInterior) (t : ℝ) :
    suitableProjectedHarmonicGradientAmbient u D p t₀ (x.1, t) =
      suitableProjectedHarmonicGradient u D p t₀ (x, t) := by
  change unitBallHarmonicForceGradientExtended
      (-averagedTimePrimitive (unitBallVelocityForceCurve u)
        (unitBallMomentumForceCurve u D p) (t₀ - 4) (t₀ + 4) t₀ t) x =
    (-unitBallHarmonicForceGradientExtended
      (averagedTimePrimitive (unitBallVelocityForceCurve u)
        (unitBallMomentumForceCurve u D p) (t₀ - 4) (t₀ + 4) t₀ t)) x
  rw [map_neg]

/-- The ambient Hessian equals the frozen actual spatial correction derivative everywhere. -/
theorem suitableProjectedHarmonicDerivativeAmbient_eq_compact
    (x : unitBallPressureCompactInterior) (t : ℝ) (i j : Fin 3) :
    suitableProjectedHarmonicDerivativeAmbient u D p t₀ (x.1, t) i j =
      suitableProjectedHarmonicDerivative u D p t₀ (x, t) i j := rfl

/-- The actual recovered potential has genuine C² regularity on the quarter ball at every time. -/
theorem suitableProjectedHarmonicPotential_contDiff (t : ℝ) :
    ContDiffOn ℝ (2 : ℕ∞) (suitableProjectedHarmonicPotential u D p t₀ t)
      (vec3Ball 0 (1 / 4)) :=
  unitBallHarmonicForcePressureRepresentative_contDiff _

/-- The frozen correction's actual Hessian is its true spatial weak gradient at every time. -/
theorem suitableProjectedHarmonicGradientAmbient_hasWeakGradient
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (t : ℝ) (i : Fin 3) :
    HasWeakGradientOn B
      (fun x ↦ suitableProjectedHarmonicGradientAmbient u D p t₀ (x, t) i)
      (fun x ↦ suitableProjectedHarmonicDerivativeAmbient u D p t₀ (x, t) i) := by
  have hquarter : B ⊆ vec3Ball 0 (1 / 4) := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  exact (hasWeakGradientOn_gradient_of_contDiffOn_two (isOpen_vec3Ball _ _)
    (suitableProjectedHarmonicPotential_contDiff u D p t₀ t) i).mono hB hquarter

/-- Pulling back by the genuine compact inclusion preserves ambient Lᵖ membership exactly. -/
theorem memLp_harmonicInterior_ambient_iff {E : Type*} [NormedAddCommGroup E]
    (v : Vec3 → E) (P : ℝ≥0∞) :
    MemLp v P (volume.restrict unitBallPressureCompactInterior) ↔
      MemLp (fun x : unitBallPressureCompactInterior ↦ v x.1) P harmonicInteriorMeasure := by
  have he : MeasurableEmbedding (Subtype.val : unitBallPressureCompactInterior → Vec3) :=
    MeasurableEmbedding.subtype_coe isClosed_closure.measurableSet
  rw [← harmonicInterior_measurePreserving.map_eq]
  exact he.memLp_map_measure_iff

/-- Every actual harmonic correction slice belongs to spatial L² on the compact interior. -/
theorem suitableProjectedHarmonicGradientAmbient_memLp_two (t : ℝ) :
    MemLp (fun x ↦ suitableProjectedHarmonicGradientAmbient u D p t₀ (x, t)) 2
      (volume.restrict unitBallPressureCompactInterior) := by
  apply (memLp_harmonicInterior_ambient_iff _ _).mpr
  have heq : (fun x : unitBallPressureCompactInterior ↦
      suitableProjectedHarmonicGradientAmbient u D p t₀ (x.1, t)) =
      unitBallHarmonicTimePrimitive u D p t₀ t := by
    funext x
    exact suitableProjectedHarmonicGradientAmbient_eq_compact u D p t₀ x t
  rw [heq]
  exact (unitBallHarmonicTimePrimitive u D p t₀ t).memLp harmonicInteriorMeasure ℝ

/-- Every actual harmonic Hessian slice belongs to spatial L² on the compact interior. -/
theorem suitableProjectedHarmonicDerivativeAmbient_memLp_two (t : ℝ) :
    MemLp (fun x ↦ suitableProjectedHarmonicDerivativeAmbient u D p t₀ (x, t)) 2
      (volume.restrict unitBallPressureCompactInterior) := by
  apply memLp_pi_iff.mpr
  intro i
  apply memLp_pi_iff.mpr
  intro j
  apply (memLp_harmonicInterior_ambient_iff _ _).mpr
  have hm := (harmonicCompactHessianOperator
    (-averagedTimePrimitive (unitBallVelocityForceCurve u)
      (unitBallMomentumForceCurve u D p) (t₀ - 4) (t₀ + 4) t₀ t)).memLp
      (p := 2) harmonicInteriorMeasure ℝ
  exact hm.eval_piLp (j, i)

/-- Adding genuine L² weak gradients preserves the literal compact-test identity. -/
theorem hasWeakGradientOn_add_of_memLp_two {B : Set Vec3}
    {v w : Vec3 → ℝ} {A C : Vec3 → Vec3}
    (hv : MemLp v 2 (volume.restrict B)) (hw : MemLp w 2 (volume.restrict B))
    (hA : MemLp A 2 (volume.restrict B)) (hC : MemLp C 2 (volume.restrict B))
    (hdv : HasWeakGradientOn B v A) (hdw : HasWeakGradientOn B w C) :
    HasWeakGradientOn B (fun x ↦ v x + w x) (fun x ↦ A x + C x) := by
  intro i ψ hψ hc hs
  have hmψ : MemLp ψ 2 (volume.restrict B) :=
    (hψ.continuous.memLp_of_hasCompactSupport hc).restrict B
  have hmdψ : MemLp (fun x ↦ (fderiv ℝ ψ x) (basisVec i)) 2
      (volume.restrict B) :=
    (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict B
  have h1 : Integrable (fun x ↦ v x * (fderiv ℝ ψ x) (basisVec i))
      (volume.restrict B) := hv.integrable_mul hmdψ
  have h2 : Integrable (fun x ↦ w x * (fderiv ℝ ψ x) (basisVec i))
      (volume.restrict B) := hw.integrable_mul hmdψ
  have h3 : Integrable (fun x ↦ A x i * ψ x) (volume.restrict B) :=
    (hA.eval i).integrable_mul hmψ
  have h4 : Integrable (fun x ↦ C x i * ψ x) (volume.restrict B) :=
    (hC.eval i).integrable_mul hmψ
  simp only [Pi.add_apply, add_mul]
  rw [integral_add h1 h2, integral_add h3 h4,
    hdv i ψ hψ hc hs, hdw i ψ hψ hc hs]
  ring

/-- The actual harmonic correction is weakly divergence-free on every inner open set. -/
theorem suitableProjectedHarmonicGradientAmbient_divergenceFree
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (t : ℝ) (ψ : WeakTestFunction B) :
    (∫ x in B, ∑ i : Fin 3,
      suitableProjectedHarmonicGradientAmbient u D p t₀ (x, t) i *
        spatialDeriv ψ.toFun i x) = 0 := by
  have hquarter : B ⊆ vec3Ball 0 (1 / 4) := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  exact classicalGradient_weakly_divergenceFree_of_weaklyHarmonic hB
    ((suitableProjectedHarmonicPotential_contDiff u D p t₀ t).mono hquarter
      |>.of_le (by norm_num))
    (localWeaklyHarmonicOn_restrict hquarter
      (unitBallHarmonicForcePressureRepresentative_weaklyHarmonic _))
    ψ.toFun ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset

/-- Actual suitability supplies the projected velocity's genuine L² and weak-gradient slices. -/
theorem suitableProjectedVelocityAmbient_weak_gradient_slices_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      MemLp (fun x ↦ suitableProjectedVelocityAmbient u D p t₀ (x, t)) 2
        (volume.restrict B) ∧
      MemLp (fun x ↦ suitableProjectedVelocityDerivativeAmbient u D p t₀ (x, t)) 2
        (volume.restrict B) ∧
      ∀ i : Fin 3, HasWeakGradientOn B
        (fun x ↦ suitableProjectedVelocityAmbient u D p t₀ (x, t) i)
        (fun x ↦ suitableProjectedVelocityDerivativeAmbient u D p t₀ (x, t) i) := by
  have hB1 : B ⊆ vec3Ball 0 1 := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  have hbox := suitableProjected_unitBall_localBox hdom
  have hw := ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht hwt
  have hu := ht.1.mono_measure (Measure.restrict_mono_set volume hB1)
  have hD := ht.2.mono_measure (Measure.restrict_mono_set volume hB1)
  have hH := (suitableProjectedHarmonicGradientAmbient_memLp_two u D p t₀ t).mono_measure
    (Measure.restrict_mono_set volume hBK)
  have hDH := (suitableProjectedHarmonicDerivativeAmbient_memLp_two u D p t₀ t).mono_measure
    (Measure.restrict_mono_set volume hBK)
  refine ⟨hu.add hH, hD.add hDH, ?_⟩
  intro i
  exact hasWeakGradientOn_add_of_memLp_two (hu.eval i) (hH.eval i)
    (hD.eval i) (hDH.eval i) ((hwt i).mono hB hB1)
    (suitableProjectedHarmonicGradientAmbient_hasWeakGradient u D p t₀ hB hBK t i)

/-- The true projected velocity remains weakly divergence-free on one common full time set. -/
theorem suitableProjectedVelocityAmbient_divergenceFree_slices_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)), ∀ ψ : WeakTestFunction B,
      (∫ x in B, ∑ i : Fin 3, suitableProjectedVelocityAmbient u D p t₀ (x, t) i *
        spatialDeriv ψ.toFun i x) = 0 := by
  have hB1 : B ⊆ vec3Ball 0 1 := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  have hbox := suitableProjected_unitBall_localBox hdom
  have hboxB : localBox Ω I B (Ioo (t₀ - 4) (t₀ + 4)) :=
    ⟨hB, hbox.2.1.of_isClosed_subset isClosed_closure (closure_mono hB1),
      (closure_mono hB1).trans hbox.2.2.1, hbox.2.2.2⟩
  filter_upwards [suitable_divergenceFree_slices_ae_localBox hsol hboxB,
    slice_memLp_ae_of_sws hsol hboxB] with t hdiv ht ψ
  have hH := (suitableProjectedHarmonicGradientAmbient_memLp_two u D p t₀ t).mono_measure
    (Measure.restrict_mono_set volume hBK)
  have hψd (i : Fin 3) : MemLp (spatialDeriv ψ.toFun i) 2 (volume.restrict B) :=
    ((stokesWeakTestDerivative ψ i).contDiff.continuous.memLp_of_hasCompactSupport
      (stokesWeakTestDerivative ψ i).hasCompactSupport).restrict B
  have hu (i : Fin 3) : Integrable (fun x ↦ u (x, t) i * spatialDeriv ψ.toFun i x)
      (volume.restrict B) := (ht.1.eval i).integrable_mul (hψd i)
  have hh (i : Fin 3) : Integrable (fun x ↦
      suitableProjectedHarmonicGradientAmbient u D p t₀ (x, t) i *
        spatialDeriv ψ.toFun i x) (volume.restrict B) :=
    (hH.eval i).integrable_mul (hψd i)
  have hus : Integrable (fun x ↦ ∑ i : Fin 3, u (x, t) i * spatialDeriv ψ.toFun i x)
      (volume.restrict B) := integrable_finsetSum _ (fun i _ ↦ hu i)
  have hhs : Integrable (fun x ↦ ∑ i : Fin 3,
      suitableProjectedHarmonicGradientAmbient u D p t₀ (x, t) i *
        spatialDeriv ψ.toFun i x) (volume.restrict B) :=
    integrable_finsetSum _ (fun i _ ↦ hh i)
  simp only [suitableProjectedVelocityAmbient, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [integral_add hus hhs, hdiv ψ,
    suitableProjectedHarmonicGradientAmbient_divergenceFree u D p t₀ hB hBK t ψ]
  simp

/-- Genuine inclusion of the compact product preserves actual joint Lᵖ membership. -/
theorem memLp_harmonicInterior_product_ambient_iff {E : Type*} [NormedAddCommGroup E]
    (v : ParabolicPoint → E) (P : ℝ≥0∞) (J : Set ℝ) :
    MemLp v P (volume.restrict (unitBallPressureCompactInterior ×ˢ J)) ↔
      MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦ v (z.1.1, z.2)) P
        (harmonicInteriorMeasure.prod (volume.restrict J)) := by
  have he : MeasurableEmbedding
      (fun z : unitBallPressureCompactInterior × ℝ ↦ (z.1.1, z.2)) :=
    (MeasurableEmbedding.subtype_coe isClosed_closure.measurableSet).prodMap
      (MeasurableEmbedding.id : MeasurableEmbedding (id : ℝ → ℝ))
  rw [volume_parabolicPoint_eq_prod, ← Measure.prod_restrict,
    ← (harmonicInterior_product_measurePreserving J).map_eq]
  exact he.memLp_map_measure_iff

/-- Suitability supplies the genuine ambient joint L² harmonic correction and Hessian. -/
theorem suitableProjectedHarmonicAmbient_joint_memLp_two
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    MemLp (suitableProjectedHarmonicGradientAmbient u D p t₀) 2
      (volume.restrict (unitBallPressureCompactInterior ×ˢ Ioo (t₀ - 4) (t₀ + 4))) ∧
    MemLp (suitableProjectedHarmonicDerivativeAmbient u D p t₀) 2
      (volume.restrict (unitBallPressureCompactInterior ×ˢ Ioo (t₀ - 4) (t₀ + 4))) := by
  let J := Ioo (t₀ - 4) (t₀ + 4)
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr (by
    dsimp [J]
    simp only [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top)
  have hd := suitable_harmonicInterior_correction_memLp_top hsol hdom
  constructor
  · apply (memLp_harmonicInterior_product_ambient_iff _ _ _).mpr
    have heq : (fun z : unitBallPressureCompactInterior × ℝ ↦
        suitableProjectedHarmonicGradientAmbient u D p t₀ (z.1.1, z.2)) =
        suitableProjectedHarmonicGradient u D p t₀ := by
      funext z
      exact suitableProjectedHarmonicGradientAmbient_eq_compact u D p t₀ z.1 z.2
    rw [heq]
    exact hd.1.mono_exponent le_top
  · apply memLp_pi_iff.mpr
    intro i
    apply memLp_pi_iff.mpr
    intro j
    apply (memLp_harmonicInterior_product_ambient_iff _ _ _).mpr
    exact (hd.2 i j).mono_exponent le_top

/-- The actual projected velocity and its actual gradient have genuine joint finite energy. -/
theorem suitableProjectedVelocityAmbient_joint_memLp_two
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hBK : B ⊆ unitBallPressureCompactInterior) :
    MemLp (suitableProjectedVelocityAmbient u D p t₀) 2
      (volume.restrict (B ×ˢ Ioo (t₀ - 4) (t₀ + 4))) ∧
    MemLp (suitableProjectedVelocityDerivativeAmbient u D p t₀) 2
      (volume.restrict (B ×ˢ Ioo (t₀ - 4) (t₀ + 4))) := by
  let J := Ioo (t₀ - 4) (t₀ + 4)
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr (by
    dsimp [J]
    simp only [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top)
  have hu := suitable_harmonicInterior_memLp hsol hdom
  have hH := suitableProjectedHarmonicAmbient_joint_memLp_two u D p t₀ hsol hdom
  have hu2 : MemLp u 2 (volume.restrict (unitBallPressureCompactInterior ×ˢ J)) :=
    (memLp_harmonicInterior_product_ambient_iff _ _ _).mpr
      (hu.1.mono_exponent (by norm_num))
  have hD2 : MemLp D 2 (volume.restrict (unitBallPressureCompactInterior ×ˢ J)) :=
    (memLp_harmonicInterior_product_ambient_iff _ _ _).mpr hu.2.1
  have hsub : B ×ˢ J ⊆ unitBallPressureCompactInterior ×ˢ J := prod_mono hBK le_rfl
  exact ⟨(hu2.add hH.1).mono_measure (Measure.restrict_mono_set volume hsub),
    (hD2.add hH.2).mono_measure (Measure.restrict_mono_set volume hsub)⟩

/-- The genuine projected field satisfies the weighted mixed Sobolev estimate from suitability. -/
theorem suitableProjectedVelocityAmbient_integrated_cutoff_sobolev
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ B) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    (∫⁻ t in Ioo (t₀ - 4) (t₀ + 4),
      eLpNorm (fun x ↦ φ x ^ 3 • suitableProjectedVelocityAmbient u D p t₀ (x, t)) 6
        (volume.restrict B) ^ (2 : ℝ)) ≤
      2 * (3 * localSobolevConstant) ^ 2 *
        ((∫⁻ z : ParabolicPoint in B ×ˢ Ioo (t₀ - 4) (t₀ + 4),
          ‖φ z.1 ^ 3 • suitableProjectedVelocityDerivativeAmbient u D p t₀ z‖ₑ ^
            (2 : ℝ)) +
        ENNReal.ofReal (3 * L + 32) ^ 2 *
          ∫⁻ z : ParabolicPoint in B ×ˢ Ioo (t₀ - 4) (t₀ + 4),
            ‖φ z.1 ^ 2 • suitableProjectedVelocityAmbient u D p t₀ z‖ₑ ^ (2 : ℝ)) := by
  have hunit : tsupport φ ⊆ euclideanBall 0 1 := by
    rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1)]
    exact fun x hx ↦ vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK (hs hx)))
  have hj := suitableProjectedVelocityAmbient_joint_memLp_two u D p t₀ hsol hdom hBK
  exact integrated_cutoff_cube_vector_sobolev hB hj.1.aestronglyMeasurable
    hj.2.aestronglyMeasurable
    (suitableProjectedVelocityAmbient_weak_gradient_slices_ae u D p t₀ hsol hdom hB hBK)
    hφ hc hs hunit hb hL hgrad

set_option maxHeartbeats 3000000 in
/-- The actual projected cubed-cutoff mixed moment is finite without extra energy premises. -/
theorem suitableProjectedVelocityAmbient_integrated_cutoff_sobolev_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ B) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    (∫⁻ t in Ioo (t₀ - 4) (t₀ + 4),
      eLpNorm (fun x ↦ φ x ^ 3 • suitableProjectedVelocityAmbient u D p t₀ (x, t)) 6
        (volume.restrict B) ^ (2 : ℝ)) < ∞ := by
  have hj := suitableProjectedVelocityAmbient_joint_memLp_two u D p t₀ hsol hdom hBK
  have hVE : (∫⁻ z : ParabolicPoint in B ×ˢ Ioo (t₀ - 4) (t₀ + 4),
      ‖suitableProjectedVelocityAmbient u D p t₀ z‖ₑ ^ (2 : ℝ)) < ∞ := by
    simpa only [ENNReal.toReal_ofNat] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2)
        (by norm_num) (by norm_num) hj.1.eLpNorm_lt_top)
  have hDE : (∫⁻ z : ParabolicPoint in B ×ˢ Ioo (t₀ - 4) (t₀ + 4),
      ‖suitableProjectedVelocityDerivativeAmbient u D p t₀ z‖ₑ ^ (2 : ℝ)) < ∞ := by
    simpa only [ENNReal.toReal_ofNat] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2)
        (by norm_num) (by norm_num) hj.2.eLpNorm_lt_top)
  have hDw : (∫⁻ z : ParabolicPoint in B ×ˢ Ioo (t₀ - 4) (t₀ + 4),
      ‖φ z.1 ^ 3 • suitableProjectedVelocityDerivativeAmbient u D p t₀ z‖ₑ ^
        (2 : ℝ)) < ∞ :=
    (lintegral_mono (fun z ↦ ENNReal.rpow_le_rpow
      (cutoff_power_smul_enorm_le (suitableProjectedVelocityDerivativeAmbient u D p t₀ z)
        (hb z.1).1 (hb z.1).2 3) (by norm_num))).trans_lt hDE
  have hVw : (∫⁻ z : ParabolicPoint in B ×ˢ Ioo (t₀ - 4) (t₀ + 4),
      ‖φ z.1 ^ 2 • suitableProjectedVelocityAmbient u D p t₀ z‖ₑ ^ (2 : ℝ)) < ∞ :=
    (lintegral_mono (fun z ↦ ENNReal.rpow_le_rpow
      (cutoff_power_smul_enorm_le (suitableProjectedVelocityAmbient u D p t₀ z)
        (hb z.1).1 (hb z.1).2 2) (by norm_num))).trans_lt hVE
  apply (suitableProjectedVelocityAmbient_integrated_cutoff_sobolev u D p t₀ hsol hdom
    hB hBK hφ hc hs hb hL hgrad).trans_lt
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr cutoff_mixed_sobolev_coefficient_ne_top)
    (ENNReal.add_lt_top.mpr ⟨hDw, ENNReal.mul_lt_top (by finiteness) hVw⟩)

end FluidSingularSets
