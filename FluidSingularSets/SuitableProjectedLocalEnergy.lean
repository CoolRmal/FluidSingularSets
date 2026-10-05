-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SuitableHarmonicSmoothApprox
public import FluidSingularSets.HarmonicHessianSmoothApprox
public import FluidSingularSets.SmoothProjectedLocalEnergy
public import FluidSingularSets.ProjectedEnergyStrongLimit
public import FluidSingularSets.MixedWeightedVelocity
public import FluidSingularSets.JointTopSliceClasses

/-!
# Projected local energy for the genuine suitable harmonic correction

The jointly smooth force approximants retain their true harmonic structure.
The pressure term is passed to the limit in its spatial `L²`, time `L¹` class,
paired with the actual bounded-in-time spatial velocity class.
-/

@[expose] public section

open MeasureTheory Set Filter CKN TopologicalSpace
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance suitableProjectedForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance suitableProjectedForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance suitableProjectedSpaceSecondCountable : SecondCountableTopology Vec3 :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → ℝ))

/-- The actual spatial Lebesgue measure on the compact pressure interior. -/
def harmonicInteriorMeasure : Measure unitBallPressureCompactInterior :=
  (volume.restrict unitBallPressureCompactInterior).comap Subtype.val

instance harmonicInteriorMeasure_isFiniteMeasure : IsFiniteMeasure harmonicInteriorMeasure := by
  let : IsFiniteMeasure (volume.restrict unitBallPressureCompactInterior) :=
    isFiniteMeasure_restrict.mpr
      ((isCompact_closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16)).measure_lt_top.ne)
  unfold harmonicInteriorMeasure
  infer_instance

/-- The subtype inclusion carries the real compact interior volume to the
ambient spatial Lebesgue measure restricted to that interior. -/
theorem harmonicInterior_measurePreserving :
    MeasurePreserving (Subtype.val : unitBallPressureCompactInterior → Vec3)
      harmonicInteriorMeasure (volume.restrict unitBallPressureCompactInterior) := by
  have hs : MeasurableSet unitBallPressureCompactInterior := isClosed_closure.measurableSet
  have h := measurePreserving_subtype_coe
    (μa := volume.restrict unitBallPressureCompactInterior) hs
  simpa only [harmonicInteriorMeasure, Measure.restrict_restrict hs, inter_self] using h

/-- Product integration over the true compact interior is native Lebesgue
integration restricted to that same spatial set and time interval. -/
theorem harmonicInterior_product_measurePreserving (J : Set ℝ) :
    MeasurePreserving (fun z : unitBallPressureCompactInterior × ℝ ↦ (z.1.1, z.2))
      (harmonicInteriorMeasure.prod (volume.restrict J))
      ((volume.restrict unitBallPressureCompactInterior).prod (volume.restrict J)) := by
  have hs : MeasurableSet unitBallPressureCompactInterior := isClosed_closure.measurableSet
  let : IsFiniteMeasure ((volume.restrict unitBallPressureCompactInterior).comap
      (Subtype.val : unitBallPressureCompactInterior → Vec3)) :=
    harmonicInteriorMeasure_isFiniteMeasure
  have hp := (measurePreserving_subtype_coe
    (μa := volume.restrict unitBallPressureCompactInterior) hs).prod
    (MeasurePreserving.id (volume.restrict J))
  change MeasurePreserving
    (Prod.map (Subtype.val : unitBallPressureCompactInterior → Vec3) (id : ℝ → ℝ)) _ _
  simpa only [harmonicInteriorMeasure, Measure.restrict_restrict hs, inter_self] using hp

/-- The actual volume identity for a compactly supported energy density. -/
theorem integral_harmonicInterior_product_eq_integral
    {J : Set ℝ} (F : Vec3 × ℝ → ℝ)
    (hF : ∀ z, z ∉ unitBallPressureCompactInterior ×ˢ J → F z = 0) :
    (∫ z : unitBallPressureCompactInterior × ℝ, F (z.1.1, z.2)
      ∂harmonicInteriorMeasure.prod (volume.restrict J)) = ∫ z : Vec3 × ℝ, F z := by
  have hs : MeasurableSet unitBallPressureCompactInterior := isClosed_closure.measurableSet
  have he : MeasurableEmbedding
      (fun z : unitBallPressureCompactInterior × ℝ ↦ (z.1.1, z.2)) :=
    (MeasurableEmbedding.subtype_coe hs).prodMap
      (MeasurableEmbedding.id : MeasurableEmbedding (id : ℝ → ℝ))
  have h := (harmonicInterior_product_measurePreserving J).integral_comp he F
  rw [h, Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hF

/-- The real spatial derivative of each smooth correction is the corresponding
entry of its smoothed pressure Hessian, in the velocity-gradient index order. -/
theorem unitBallJointHarmonicApproxGradient_spatialPartial
    (fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)) (n : ℕ)
    (z : Vec3 × ℝ) (i j : Fin 3) :
    spatialPartial (fun w ↦ unitBallJointHarmonicApproxGradient fs n w i) j z =
      mixedSecond (harmonicSpatialSmoothPressure (-fs n z.2)
        (suitableHarmonicSmoothRadius_pos n)) j i z.1 := by
  simp_rw [spatialPartial, unitBallJointHarmonicApproxGradient,
    harmonicJointSmoothGradient_apply]
  rfl

/-- The source domain contains a genuine local velocity box covering the entire
closed time interval used for the harmonic primitive. -/
theorem suitableProjected_unitBall_localBox
    {Ω : Set Vec3} {I : Set ℝ} {t₀ : ℝ}
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    localBox Ω I (vec3Ball 0 1) (Ioo (t₀ - 4) (t₀ + 4)) := by
  have hb := CKN.Core.Endgame.localBox_of_parabolic_ball
    (z₀ := ((0, t₀) : ParabolicPoint)) (by norm_num : (0 : ℝ) < 2)
    ((Metric.ball_subset_ball (by norm_num : (2 : ℝ) * 2 ≤ 8)).trans hdom)
  have hB : localBox Ω I (vec3Ball 0 2) (Ioo (t₀ - 4) (t₀ + 4)) := by
    simpa only [Prod.fst, Prod.snd, show (2 : ℝ) ^ 2 = 4 by norm_num] using hb
  have hsub : vec3Ball (0 : Vec3) 1 ⊆ vec3Ball 0 2 := vec3Ball_mono (by norm_num)
  refine ⟨isOpen_vec3Ball 0 1, ?_, ?_, hB.2.2.2⟩
  · exact hB.2.1.of_isClosed_subset isClosed_closure (closure_mono hsub)
  · exact (closure_mono hsub).trans hB.2.2.1

/-- Actual suitability supplies all three joint exponents on the true compact
pressure interior, without any integrability premise for the projected fields. -/
theorem suitable_harmonicInterior_memLp
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦ u (z.1.1, z.2)) 3
      (harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) ∧
      MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦ Du (z.1.1, z.2)) 2
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) ∧
      MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦ p (z.1.1, z.2))
        (ENNReal.ofReal (3 / 2 : ℝ))
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) := by
  let J := Ioo (t₀ - 4) (t₀ + 4)
  let S : Set ParabolicPoint := unitBallPressureCompactInterior ×ˢ Icc (t₀ - 4) (t₀ + 4)
  have hbox := suitableProjected_unitBall_localBox hdom
  have hS : IsCompact S := parabolicHomeomorph.isCompact_preimage.mpr
    ((isCompact_closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16)).prod isCompact_Icc)
  have hSdom : S ⊆ spaceTimeSet Ω I := by
    intro z hz
    refine ⟨hbox.2.2.1 (subset_closure ?_), hbox.2.2.2.2.2 ?_⟩
    · exact vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
        (unitBallPressureCompactInterior_subset_eighth hz.1)
    · rw [closure_Ioo (by linarith : t₀ - 4 ≠ t₀ + 4)]
      exact hz.2
  have hu : MemLp u 3 (volume.restrict S) := by
    simpa using velocity_memLp_three_on_compact_of_data hsol.toData hS hSdom
  have hd := gradient_memLp_two_on_compact_of_data hsol.toData hS hSdom
  have hp := pressure_memLp_threeHalves_on_compact_of_data hsol.toData hS hSdom
  have hsub : unitBallPressureCompactInterior ×ˢ J ⊆ S :=
    prod_mono le_rfl Ioo_subset_Icc_self
  have hUP : MemLp (fun z : Vec3 × ℝ ↦ u z) 3
      ((volume.restrict unitBallPressureCompactInterior).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict,
      ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hu.mono_measure (Measure.restrict_mono_set volume hsub)
  have hDP : MemLp (fun z : Vec3 × ℝ ↦ Du z) 2
      ((volume.restrict unitBallPressureCompactInterior).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict,
      ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hd.mono_measure (Measure.restrict_mono_set volume hsub)
  have hPP : MemLp (fun z : Vec3 × ℝ ↦ p z) (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume.restrict unitBallPressureCompactInterior).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict,
      ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hp.mono_measure (Measure.restrict_mono_set volume hsub)
  exact ⟨hUP.comp_measurePreserving (harmonicInterior_product_measurePreserving J),
    hDP.comp_measurePreserving (harmonicInterior_product_measurePreserving J),
    hPP.comp_measurePreserving (harmonicInterior_product_measurePreserving J)⟩

/-- The original suitable slice-energy bound gives the true compact-interior
velocity class in time `L∞`, including its genuine good spatial slices. -/
theorem suitable_harmonicInterior_velocity_slice_data
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    (∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      MemLp (fun x : unitBallPressureCompactInterior ↦ u (x.1, t)) 2
        harmonicInteriorMeasure) ∧
      MemLp (actualSliceLp (μ := harmonicInteriorMeasure) (p := 2)
        (fun z : unitBallPressureCompactInterior × ℝ ↦ u (z.1.1, z.2))) ⊤
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) := by
  let J := Ioo (t₀ - 4) (t₀ + 4)
  have hbox := suitableProjected_unitBall_localBox hdom
  have hsub : unitBallPressureCompactInterior ⊆ vec3Ball (0 : Vec3) 1 :=
    fun x hx ↦ vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth hx)
  refine ⟨?_, ?_⟩
  · filter_upwards [slice_memLp_ae_of_sws hsol hbox] with t ht
    exact (ht.1.mono_measure (Measure.restrict_mono_set volume hsub)).comp_measurePreserving
      harmonicInterior_measurePreserving
  · have hmeas := (suitable_harmonicInterior_memLp hsol hdom).1.aestronglyMeasurable
    apply actualSliceLp_memLp_top_of_sliceEnergy hmeas
    apply lt_of_le_of_lt _ (hsol.toData.essSup_sliceEnergy_lt_top hbox)
    refine essSup_mono_ae (ae_of_all _ fun t ↦ ?_)
    ·
      let ft : Vec3 → ℝ≥0∞ := fun x ↦ ‖u ((x, t) : ParabolicPoint)‖ₑ ^ (2 : ℝ)
      have hs : MeasurableSet unitBallPressureCompactInterior := isClosed_closure.measurableSet
      have hm : (volume.restrict unitBallPressureCompactInterior).restrict
          unitBallPressureCompactInterior = volume.restrict unitBallPressureCompactInterior := by
        rw [Measure.restrict_restrict hs, inter_self]
      change (∫⁻ x : unitBallPressureCompactInterior, ft x.1
        ∂(volume.restrict unitBallPressureCompactInterior).comap Subtype.val) ≤
          ∫⁻ x in vec3Ball 0 1, ft x
      calc
        _ = ∫⁻ x in unitBallPressureCompactInterior, ft x
            ∂volume.restrict unitBallPressureCompactInterior := lintegral_subtype_comap hs ft
        _ = ∫⁻ x in unitBallPressureCompactInterior, ft x :=
          congrArg (fun ρ : Measure Vec3 ↦ ∫⁻ x, ft x ∂ρ) hm
        _ ≤ _ := lintegral_mono_set hsub

/-- Evaluation of a genuine continuous spatial field gives exactly its actual
conditional spatial `L²` class. -/
theorem actualSliceLp_continuousMap_field
    {K T : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] [MeasurableSpace T]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure K} [IsFiniteMeasure μ] (F : T → C(K, E)) (t : T) :
    actualSliceLp (μ := μ) (p := 2) (fun z : K × T ↦ F z.2 z.1) t =
      ContinuousMap.toLp 2 μ ℝ (F t) := by
  have ht : MemLp (fun x ↦ F t x) 2 μ := (F t).memLp μ ℝ
  apply Lp.ext
  exact (actualSliceLp_ae (fun z : K × T ↦ F z.2 z.1) t ht).trans
    (ContinuousMap.coeFn_toLp μ (F t)).symm

/-- A genuine time `L¹` continuous spatial field has its actual mixed
pressure-class data. -/
theorem projectedEnergySliceData_one_continuousMap
    {K T : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    [MeasurableSpace T] {μ : Measure K} [IsFiniteMeasure μ]
    {ν : Measure T} [SFinite ν] {F : T → C(K, ℝ)} (hF : MemLp F 1 ν) :
    ProjectedEnergySliceData μ ν 1 (fun z : K × T ↦ F z.2 z.1) := by
  have hFs : AEStronglyMeasurable (fun z : K × T ↦ F z.2) (μ.prod ν) :=
    hF.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hx : AEStronglyMeasurable (fun z : K × T ↦ z.1) (μ.prod ν) :=
    measurable_fst.aestronglyMeasurable
  refine ⟨?_, ae_of_all _ fun t ↦ (F t).memLp μ ℝ, ?_⟩
  · exact continuous_eval.comp_aestronglyMeasurable (hFs.prodMk hx)
  · have h := hF.continuousLinearMap_comp (ContinuousMap.toLp 2 μ ℝ)
    convert h using 1
    funext t
    exact actualSliceLp_continuousMap_field (μ := μ) F t

/-- Genuine strong time `L¹` continuous-field convergence gives the strong
actual spatial pressure-class convergence required by the energy limit. -/
theorem projectedEnergySliceStrong_one_continuousMap
    {K T : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    [MeasurableSpace T] {μ : Measure K} [IsFiniteMeasure μ]
    {ν : Measure T} [SFinite ν] {F : T → C(K, ℝ)} {Fs : ℕ → T → C(K, ℝ)}
    (hF : MemLp F 1 ν) (hFs : ∀ n, MemLp (Fs n) 1 ν)
    (hconv : Tendsto (fun n ↦ eLpNorm (Fs n - F) 1 ν) atTop (𝓝 0)) :
    ProjectedEnergySliceStrong μ ν 1 (fun z : K × T ↦ F z.2 z.1)
      (fun n z ↦ Fs n z.2 z.1) := by
  refine ⟨projectedEnergySliceData_one_continuousMap hF,
    fun n ↦ projectedEnergySliceData_one_continuousMap (hFs n), ?_⟩
  have hc : Tendsto (fun n ↦ eLpNorm (F - Fs n) 1 ν) atTop (𝓝 0) := by
    convert hconv using 1
    funext n
    exact eLpNorm_sub_comm _ _ _ _
  have h := tendsto_eLpNorm_operator_sub (ContinuousMap.toLp 2 μ ℝ) hF hFs hc
  have heq : actualSliceLp (μ := μ) (p := 2) (fun z : K × T ↦ F z.2 z.1) =
      fun t ↦ ContinuousMap.toLp 2 μ ℝ (F t) :=
    funext (actualSliceLp_continuousMap_field (μ := μ) F)
  have heqs (n : ℕ) : actualSliceLp (μ := μ) (p := 2)
      (fun z : K × T ↦ Fs n z.2 z.1) = fun t ↦ ContinuousMap.toLp 2 μ ℝ (Fs n t) :=
    funext (actualSliceLp_continuousMap_field (μ := μ) (Fs n))
  simp only [heq, heqs]
  convert h using 1
  funext n
  exact eLpNorm_sub_comm _ _ _ _

/-- A genuine time class of continuous spatial fields gives the joint field
class, by the literal pointwise bound by its actual uniform spatial norm. -/
theorem memLp_continuousMap_field
    {K T E : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure K} [IsFiniteMeasure μ] {ν : Measure T} [SFinite ν]
    {F : T → C(K, E)} {P : ℝ≥0∞} (hF : MemLp F P ν) :
    MemLp (fun z : K × T ↦ F z.2 z.1) P (μ.prod ν) := by
  have hFs := hF.aestronglyMeasurable.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_snd (μ := μ))
  have hx : AEStronglyMeasurable (fun z : K × T ↦ z.1) (μ.prod ν) :=
    measurable_fst.aestronglyMeasurable
  have hm := continuous_eval.comp_aestronglyMeasurable (hFs.prodMk hx)
  exact (hF.comp_snd μ).of_le hm (ae_of_all _ fun z ↦ (F z.2).norm_coe_le_norm z.1)

/-- The literal harmonic gradient representative on the compact interior. -/
def suitableProjectedHarmonicGradient
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) : unitBallPressureCompactInterior × ℝ → Vec3 :=
  fun z ↦ unitBallHarmonicTimePrimitive u Du p t₀ z.2 z.1

/-- The actual harmonic Hessian, in the same component/derivative order as `Du`. -/
def suitableProjectedHarmonicDerivative
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) :
    unitBallPressureCompactInterior × ℝ → Fin 3 → Vec3 :=
  fun z i j ↦ harmonicCompactHessianOperator
    (-averagedTimePrimitive (unitBallVelocityForceCurve u)
      (unitBallMomentumForceCurve u Du p) (t₀ - 4) (t₀ + 4) t₀ z.2) z.1 (j, i)

/-- Actual suitable slice energy and the recovered force primitive give true
joint uniform bounds for both the harmonic correction and its spatial derivative. -/
theorem suitable_harmonicInterior_correction_memLp_top
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    MemLp (suitableProjectedHarmonicGradient u Du p t₀) ⊤
      (harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) ∧
      (∀ i j, MemLp (fun z ↦ suitableProjectedHarmonicDerivative u Du p t₀ z i j) ⊤
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))))) := by
  refine ⟨memLp_continuousMap_field (suitable_harmonicTimePrimitive_memLp_top hsol hdom), ?_⟩
  have hbox := suitableProjected_unitBall_localBox hdom
  have hM := (suitable_velocityForceCurve_memLp_top hsol hbox).ae_eq
    (suitable_unitBall_velocityForce_ae_primitive hsol hdom)
  have hB := memLp_continuousMap_field (μ := harmonicInteriorMeasure)
    (hM.neg.continuousLinearMap_comp harmonicCompactHessianOperator)
  intro i j
  exact hB.eval_piLp (j, i)

/-- Actual suitable momentum and its genuine smooth derivative approximation
give the exact strong mixed pressure data on the compact interior. -/
theorem suitable_harmonicInterior_pressure_sliceStrong
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {gs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hgs : ∀ n, MemLp (gs n) 1 volume)
    (hconv : Tendsto (fun n ↦ eLpNorm
      ((Ioo (t₀ - 4) (t₀ + 4)).indicator (unitBallMomentumForceCurve u Du p) - gs n)
      1 volume) atTop (𝓝 0)) :
    ProjectedEnergySliceStrong harmonicInteriorMeasure
      (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) 1
      (fun z : unitBallPressureCompactInterior × ℝ ↦
        harmonicCompactPressureValues (-unitBallMomentumForceCurve u Du p z.2) z.1)
      (fun n z ↦ unitBallJointHarmonicApproxPressure gs n (z.1.1, z.2)) := by
  let J := Ioo (t₀ - 4) (t₀ + 4)
  let g := unitBallMomentumForceCurve u Du p
  let F : ℝ → C(unitBallPressureCompactInterior, ℝ) :=
    fun t ↦ harmonicCompactPressureValues (-g t)
  let Fs : ℕ → ℝ → C(unitBallPressureCompactInterior, ℝ) := fun n t ↦
    harmonicSmoothCompactPressureValues (suitableHarmonicSmoothRadius_pos n)
      (suitableHarmonicSmoothRadius_le n) (-gs n t)
  obtain ⟨_, hg⟩ := suitable_unitBall_momentumForces_integrable hsol hdom
  have hg₀ : MemLp (J.indicator g) 1 volume :=
    memLp_one_iff_integrable.mpr (hg.integrable_indicator measurableSet_Ioo)
  have hneg : Tendsto (fun n ↦ eLpNorm
      ((fun t ↦ -gs n t) - fun t ↦ -(J.indicator g t)) 1 volume) atTop (𝓝 0) := by
    convert hconv using 1
    funext n
    congr 1
    funext t
    simp only [Pi.sub_apply]
    abel
  have hglobal := harmonicSmoothCompactPressureValues_strong_one
    suitableHarmonicSmoothRadius_tendsto suitableHarmonicSmoothRadius_pos
    suitableHarmonicSmoothRadius_le hg₀.neg (fun n ↦ (hgs n).neg) hneg
  have hlocal : Tendsto (fun n ↦ eLpNorm (Fs n - F) 1 (volume.restrict J)) atTop (𝓝 0) := by
    have hrestr : Tendsto (fun n ↦ eLpNorm (fun t ↦ Fs n t -
        harmonicCompactPressureValues (-(J.indicator g t))) 1 (volume.restrict J))
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglobal
        (fun _ ↦ zero_le) (fun _ ↦ eLpNorm_mono_measure _ Measure.restrict_le_self)
    convert hrestr using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [Fs, F, Pi.sub_apply, J, indicator_of_mem ht]
  have hF : MemLp F 1 (volume.restrict J) :=
    (memLp_one_iff_integrable.mpr hg).neg.continuousLinearMap_comp harmonicCompactPressureValues
  have hFs (n : ℕ) : MemLp (Fs n) 1 (volume.restrict J) :=
    ((hgs n).mono_measure Measure.restrict_le_self).neg.continuousLinearMap_comp
      (harmonicSmoothCompactPressureValues (suitableHarmonicSmoothRadius_pos n)
        (suitableHarmonicSmoothRadius_le n))
  have h := projectedEnergySliceStrong_one_continuousMap
    (μ := harmonicInteriorMeasure) hF hFs hlocal
  convert h using 1
  ext n z
  exact (harmonicSmoothCompactPressureValues_apply
    (suitableHarmonicSmoothRadius_pos n) (suitableHarmonicSmoothRadius_le n)
    (-gs n z.2) z.1).trans
      (harmonicJointSmoothPressure_apply (suitableHarmonicSmoothRadius_pos n)
        (fun t ↦ -gs n t) (z.1.1, z.2)).symm

/-- Every actual constructed smooth correction satisfies the original
suitable projected energy inequality for compact tests inside its harmonic region. -/
theorem suitable_unitBall_joint_smooth_projected_energy
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {gs fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hsm : ∀ n, ContDiff ℝ ∞ (gs n) ∧ ContDiff ℝ ∞ (fs n) ∧
      (∀ t, HasDerivAt (fs n) (gs n t) t))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z)
    (hsupp : ∀ z ∈ tsupport ψ, z.1 ∈ vec3Ball 0 (1 / 12)) (n : ℕ) :
    Integrable (fun z : Vec3 × ℝ ↦ projectedEnergyDeficitPolynomial
      (u z) (unitBallJointHarmonicApproxGradient fs n z)
      (fun j ↦ spatialPartial ψ j z) (Du z)
      (fun i j ↦ spatialPartial (fun w ↦ unitBallJointHarmonicApproxGradient fs n w i) j z)
      (p z - unitBallJointHarmonicApproxPressure gs n z) (ψ z) (timePartial ψ z)
      (∑ j, spatialSecondPartial ψ j j z)) volume ∧
      (∫ z : Vec3 × ℝ, projectedEnergyDeficitPolynomial
        (u z) (unitBallJointHarmonicApproxGradient fs n z)
        (fun j ↦ spatialPartial ψ j z) (Du z)
        (fun i j ↦ spatialPartial
          (fun w ↦ unitBallJointHarmonicApproxGradient fs n w i) j z)
        (p z - unitBallJointHarmonicApproxPressure gs n z) (ψ z) (timePartial ψ z)
        (∑ j, spatialSecondPartial ψ j j z)) ≤ 0 := by
  apply suitable_smooth_projected_local_energy hsol
    (harmonicJointSmoothGradient_contDiff _ (hsm n).2.1.neg)
    (harmonicJointSmoothPressure_contDiff _ (hsm n).1.neg) hψ hnψ
  · intro i z hz
    exact harmonicJointSmoothGradient_spatialSecondPartial _
      (suitableHarmonicSmoothRadius_le n) _ i z (hsupp z hz)
  · intro z hz
    exact harmonicJointSmoothGradient_divergence _
      (suitableHarmonicSmoothRadius_le n) _ z (hsupp z hz)
  · intro i z _
    exact harmonicJointSmoothGradient_timePartial _ (fun t ↦ ((hsm n).2.2 t).neg) z i

/-- Uniform convergence of actual continuous fields on a compact domain has a
genuine nonnegative scalar error sequence, given by the true uniform norm. -/
theorem exists_uniform_error_sequence
    {K E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] {f : K → E} {fs : ℕ → K → E}
    (hf : Continuous f) (hfs : ∀ n, Continuous (fs n))
    (hconv : TendstoUniformly fs f atTop) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ Tendsto C atTop (𝓝 0) ∧
      ∀ n x, ‖fs n x - f x‖ ≤ C n := by
  let F : C(K, E) := ⟨f, hf⟩
  let Fs : ℕ → C(K, E) := fun n ↦ ⟨fs n, hfs n⟩
  refine ⟨fun n ↦ ‖Fs n - F‖, fun n ↦ norm_nonneg _, ?_, ?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp hconv) (ε / 2) (by positivity)] with n hn
    have hb : ‖Fs n - F‖ ≤ ε / 2 := (ContinuousMap.norm_le _ (by positivity)).mpr
      fun x ↦ by
        change ‖fs n x - f x‖ ≤ ε / 2
        rw [norm_sub_rev]
        have hx := hn x
        rw [dist_eq_norm] at hx
        exact hx.le
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      (show ‖Fs n - F‖ < ε by linarith)
  · intro n x
    exact (Fs n - F).norm_coe_le_norm x

/-- A continuous spatial correction preserves the actual good velocity slices
and their genuine time `L∞` spatial `L²` class. -/
theorem actual_velocity_slice_data_add_continuousMap
    {K T E : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] [MeasurableSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure K} [IsFiniteMeasure μ] {ν : Measure T}
    {U : K × T → E} {H : T → C(K, E)}
    (hUs : ∀ᵐ t ∂ν, MemLp (fun x ↦ U (x, t)) 2 μ)
    (hUc : MemLp (actualSliceLp (μ := μ) (p := 2) U) ⊤ ν)
    (hH : MemLp H ⊤ ν) :
    (∀ᵐ t ∂ν, MemLp (fun x ↦ U (x, t) + H t x) 2 μ) ∧
      MemLp (actualSliceLp (μ := μ) (p := 2)
        (fun z : K × T ↦ U z + H z.2 z.1)) ⊤ ν := by
  have hHs (t : T) : MemLp (fun x ↦ H t x) 2 μ := (H t).memLp μ ℝ
  refine ⟨hUs.mono fun t ht ↦ ht.add (hHs t), ?_⟩
  have hh := hH.continuousLinearMap_comp (ContinuousMap.toLp 2 μ ℝ)
  apply (hUc.add hh).ae_eq
  filter_upwards [hUs] with t ht
  apply Lp.ext
  have hsum := actualSliceLp_ae (fun z : K × T ↦ U z + H z.2 z.1) t
    (ht.add (hHs t))
  exact ((Lp.coeFn_add _ _).trans
    ((actualSliceLp_ae U t ht).add (ContinuousMap.coeFn_toLp μ (H t)))).trans hsum.symm

/-- Actual continuity on a closed finite interval gives every finite-measure
time class on its open interior, including the true essential supremum. -/
theorem continuous_memLp_restrict_Ioo
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) (a b : ℝ) (P : ℝ≥0∞) :
    MemLp f P (volume.restrict (Ioo a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C
    ((ae_restrict_mem measurableSet_Ioo).mono fun t ht ↦ hC t (Ioo_subset_Icc_self ht))

/-- A genuinely bounded measurable difference transfers actual uniform
membership from the limit field to each approximating field. -/
theorem memLp_top_of_uniform_difference
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {μ : Measure A} [IsFiniteMeasure μ] {f g : A → E} (hf : MemLp f ⊤ μ)
    (hg : AEStronglyMeasurable g μ) {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖g x - f x‖ ≤ C) : MemLp g ⊤ μ := by
  have hd : MemLp (g - f) ⊤ μ :=
    MemLp.of_bound (hg.sub hf.aestronglyMeasurable) C hbound
  convert hd.add hf using 1
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, sub_add_cancel]

/-- The literal derivative of the actual jointly smooth harmonic approximation. -/
def unitBallJointHarmonicApproxDerivative
    (fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)) (n : ℕ)
    (z : unitBallPressureCompactInterior × ℝ) : Fin 3 → Vec3 :=
  fun i j ↦ spatialPartial (fun w ↦ unitBallJointHarmonicApproxGradient fs n w i) j
    (z.1.1, z.2)

/-- Actual force-space convergence gives uniform errors for the correction and
its true Hessian, and hence genuine joint uniform classes of every approximant. -/
theorem suitable_harmonicInterior_uniform_approximations
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hfs : ∀ n, ContDiff ℝ ∞ (fs n))
    (hforce : TendstoUniformly fs
      (averagedTimePrimitive (unitBallVelocityForceCurve u)
        (unitBallMomentumForceCurve u Du p) (t₀ - 4) (t₀ + 4) t₀) atTop)
    (hfield : TendstoUniformly
      (fun n (z : unitBallPressureCompactInterior × Icc (t₀ - 4) (t₀ + 4)) ↦
        unitBallJointHarmonicApproxGradient fs n (z.1.1, z.2.1))
      (fun z ↦ unitBallHarmonicTimePrimitive u Du p t₀ z.2.1 z.1) atTop) :
    ∃ CH CB : ℕ → ℝ,
      (∀ n, 0 ≤ CH n) ∧ Tendsto CH atTop (𝓝 0) ∧
      (∀ n, 0 ≤ CB n) ∧ Tendsto CB atTop (𝓝 0) ∧
      (∀ n t, t ∈ Icc (t₀ - 4) (t₀ + 4) → ∀ x : unitBallPressureCompactInterior,
        ‖unitBallJointHarmonicApproxGradient fs n (x.1, t) -
          suitableProjectedHarmonicGradient u Du p t₀ (x, t)‖ ≤ CH n) ∧
      (∀ n t, t ∈ Icc (t₀ - 4) (t₀ + 4) → ∀ x : unitBallPressureCompactInterior,
        ∀ i j, ‖unitBallJointHarmonicApproxDerivative fs n (x, t) i j -
          suitableProjectedHarmonicDerivative u Du p t₀ (x, t) i j‖ ≤ CB n) ∧
      (∀ n, MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦
        unitBallJointHarmonicApproxGradient fs n (z.1.1, z.2)) ⊤
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))))) ∧
      (∀ n i j, MemLp (fun z ↦ unitBallJointHarmonicApproxDerivative fs n z i j) ⊤
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))))) := by
  let J := Ioo (t₀ - 4) (t₀ + 4)
  let T := Icc (t₀ - 4) (t₀ + 4)
  let M := averagedTimePrimitive (unitBallVelocityForceCurve u)
    (unitBallMomentumForceCurve u Du p) (t₀ - 4) (t₀ + 4) t₀
  obtain ⟨_, hg⟩ := suitable_unitBall_momentumForces_integrable hsol hdom
  have hM : Continuous M := averagedTimePrimitive_continuous hg
  have hH : Continuous (unitBallHarmonicTimePrimitive u Du p t₀) :=
    (unitBallHarmonicForceGradientExtended.continuous.comp hM).neg
  have hHjoint : Continuous (fun z : unitBallPressureCompactInterior × T ↦
      unitBallHarmonicTimePrimitive u Du p t₀ z.2.1 z.1) :=
    continuous_eval.comp ((hH.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      continuous_fst)
  have hHn (n : ℕ) : Continuous (unitBallJointHarmonicApproxGradient fs n) :=
    (harmonicJointSmoothGradient_contDiff _ (hfs n).neg).continuous
  obtain ⟨CH, hCH, hCHzero, hCHbound⟩ := exists_uniform_error_sequence hHjoint
    (fun n ↦ (hHn n).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))) hfield
  have hnegative : TendstoUniformly (fun n (t : T) ↦ -fs n t.1)
      (fun t : T ↦ -M t.1) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp hforce) ε hε] with n hn t
    simpa only [dist_neg_neg] using hn t.1
  have hBuniform := harmonicSmoothCompactHessian_tendstoUniformly
    suitableHarmonicSmoothRadius_tendsto suitableHarmonicSmoothRadius_pos
    suitableHarmonicSmoothRadius_le (hM.comp continuous_subtype_val).neg hnegative
  obtain ⟨CB, hCB, hCBzero, hCBbound⟩ := exists_uniform_error_sequence
    (harmonicCompactHessianOperator.continuous.comp (hM.comp continuous_subtype_val).neg)
    (fun n ↦ (harmonicSmoothCompactHessian (suitableHarmonicSmoothRadius_pos n)
      (suitableHarmonicSmoothRadius_le n)).continuous.comp
        ((hfs n).continuous.comp continuous_subtype_val).neg) hBuniform
  have hbH (n : ℕ) (t : ℝ) (ht : t ∈ T) (x : unitBallPressureCompactInterior) :
      ‖unitBallJointHarmonicApproxGradient fs n (x.1, t) -
        suitableProjectedHarmonicGradient u Du p t₀ (x, t)‖ ≤ CH n :=
    hCHbound n (x, ⟨t, ht⟩)
  have hbB (n : ℕ) (t : ℝ) (ht : t ∈ T) (x : unitBallPressureCompactInterior)
      (i j : Fin 3) : ‖unitBallJointHarmonicApproxDerivative fs n (x, t) i j -
        suitableProjectedHarmonicDerivative u Du p t₀ (x, t) i j‖ ≤ CB n := by
    rw [unitBallJointHarmonicApproxDerivative,
      unitBallJointHarmonicApproxGradient_spatialPartial]
    have he := (harmonicSmoothCompactHessian_apply (suitableHarmonicSmoothRadius_pos n)
      (suitableHarmonicSmoothRadius_le n) (-fs n t) x j i).symm
    rw [he]
    exact ((PiLp.norm_apply_le _ (j, i)).trans
      ((harmonicSmoothCompactHessian (suitableHarmonicSmoothRadius_pos n)
        (suitableHarmonicSmoothRadius_le n) (-fs n t) -
        harmonicCompactHessianOperator (-M t)).norm_coe_le_norm x)).trans
      (hCBbound n ⟨t, ht⟩)
  have htime : ∀ᵐ z : unitBallPressureCompactInterior × ℝ
      ∂harmonicInteriorMeasure.prod (volume.restrict J), z.2 ∈ J :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioo)).mpr
      (ae_of_all _ fun _ ↦ ae_restrict_mem measurableSet_Ioo)
  obtain ⟨hHtop, hBtop⟩ := suitable_harmonicInterior_correction_memLp_top hsol hdom
  refine ⟨CH, CB, hCH, hCHzero, hCB, hCBzero, hbH, hbB, ?_, ?_⟩
  · intro n
    apply memLp_top_of_uniform_difference hHtop
      ((hHn n).comp ((continuous_subtype_val.comp continuous_fst).prodMk
        continuous_snd)).aestronglyMeasurable
    exact htime.mono fun z hz ↦ hbH n z.2 (Ioo_subset_Icc_self hz) z.1
  · intro n i j
    have hc := (spatialPartial_contDiff ((contDiff_apply ℝ ℝ i).comp
      (harmonicJointSmoothGradient_contDiff (suitableHarmonicSmoothRadius_pos n)
        (hfs n).neg)) j).continuous
    apply memLp_top_of_uniform_difference (hBtop i j)
      (hc.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        continuous_snd)).aestronglyMeasurable
    exact htime.mono fun z hz ↦ hbB n z.2 (Ioo_subset_Icc_self hz) z.1 i j

/-- Addition of true spatial classes agrees with the actual conditional class
on every common good slice. -/
theorem actual_velocity_slice_data_add
    {K T E : Type*} [MeasurableSpace K] [MeasurableSpace T]
    [NormedAddCommGroup E] {μ : Measure K} {ν : Measure T}
    {U H : K × T → E}
    (hUs : ∀ᵐ t ∂ν, MemLp (fun x ↦ U (x, t)) 2 μ)
    (hHs : ∀ᵐ t ∂ν, MemLp (fun x ↦ H (x, t)) 2 μ)
    (hUc : MemLp (actualSliceLp (μ := μ) (p := 2) U) ⊤ ν)
    (hHc : MemLp (actualSliceLp (μ := μ) (p := 2) H) ⊤ ν) :
    (∀ᵐ t ∂ν, MemLp (fun x ↦ U (x, t) + H (x, t)) 2 μ) ∧
      MemLp (actualSliceLp (μ := μ) (p := 2) (U + H)) ⊤ ν := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hUs, hHs] with t ht hht
    exact ht.add hht
  · apply (hUc.add hHc).ae_eq
    filter_upwards [hUs, hHs] with t ht hht
    apply Lp.ext
    have hsum := actualSliceLp_ae (U + H) t (ht.add hht)
    exact ((Lp.coeFn_add _ _).trans
      ((actualSliceLp_ae U t ht).add (actualSliceLp_ae H t hht))).trans hsum.symm

/-- The literal projected deficit vanishes away from the actual test support. -/
theorem projectedEnergyDeficitPolynomial_zero_off_tsupport
    (U H : Vec3 × ℝ → Vec3) (D B : Vec3 × ℝ → Fin 3 → Vec3)
    (P ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) (hz : z ∉ tsupport ψ) :
    projectedEnergyDeficitPolynomial (U z) (H z) (fun j ↦ spatialPartial ψ j z)
      (D z) (B z) (P z) (ψ z) (timePartial ψ z)
      (∑ j, spatialSecondPartial ψ j j z) = 0 := by
  have hψ := image_eq_zero_of_notMem_tsupport hz
  have hτ := timePartial_eq_zero_off_tsupport hz
  have hG (j : Fin 3) := spatialPartial_eq_zero_off_tsupport hz j
  have hΛ (j : Fin 3) := spatialSecondPartial_eq_zero_off_tsupport hz j j
  simp only [projectedEnergyDeficitPolynomial, hψ, hτ, hG, hΛ, Finset.sum_const_zero,
    add_zero, mul_zero, sub_zero]

/-- The literal ordinary-coordinate density of a smooth projected test. -/
def unitBallSmoothProjectedEnergyDensity
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (gs fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1))
    (ψ : Vec3 × ℝ → ℝ) (n : ℕ) (z : Vec3 × ℝ) : ℝ :=
  projectedEnergyDeficitPolynomial (u ((z.1, z.2) : ParabolicPoint))
    (unitBallJointHarmonicApproxGradient fs n z) (fun j ↦ spatialPartial ψ j z)
    (Du ((z.1, z.2) : ParabolicPoint))
    (fun i j ↦ spatialPartial (fun w ↦ unitBallJointHarmonicApproxGradient fs n w i) j z)
    (p ((z.1, z.2) : ParabolicPoint) - unitBallJointHarmonicApproxPressure gs n z)
    (ψ z) (timePartial ψ z) (∑ j, spatialSecondPartial ψ j j z)

/-- The genuine smooth projected inequality is also the true compact-product
inequality whenever the actual test is supported in that product. -/
theorem suitable_unitBall_joint_smooth_projected_energy_compact
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {J : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {gs fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hsm : ∀ n, ContDiff ℝ ∞ (gs n) ∧ ContDiff ℝ ∞ (fs n) ∧
      (∀ t, HasDerivAt (fs n) (gs n t) t))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z)
    (hsupp : tsupport ψ ⊆ unitBallPressureCompactInterior ×ˢ J) (n : ℕ) :
    (∫ z : unitBallPressureCompactInterior × ℝ,
      unitBallSmoothProjectedEnergyDensity u Du p gs fs ψ n (z.1.1, z.2)
      ∂harmonicInteriorMeasure.prod (volume.restrict J)) ≤ 0 := by
  have hregion : ∀ z ∈ tsupport ψ, z.1 ∈ vec3Ball 0 (1 / 12) := by
    intro z hz
    have hx := (hsupp hz).1
    rw [unitBallPressureCompactInterior,
      closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16)] at hx
    change vec3EuclideanNorm (z.1 - 0) ≤ 1 / 16 at hx
    change vec3EuclideanNorm (z.1 - 0) < 1 / 12
    linarith
  have hineq := (suitable_unitBall_joint_smooth_projected_energy hsol hsm hψ hnψ
    hregion n).2
  let F := unitBallSmoothProjectedEnergyDensity u Du p gs fs ψ n
  have heq := integral_harmonicInterior_product_eq_integral (J := J) F (by
    intro z hz
    exact projectedEnergyDeficitPolynomial_zero_off_tsupport
      (fun w ↦ u ((w.1, w.2) : ParabolicPoint))
      (unitBallJointHarmonicApproxGradient fs n)
      (fun w ↦ Du ((w.1, w.2) : ParabolicPoint))
      (fun w i j ↦ spatialPartial
        (fun v ↦ unitBallJointHarmonicApproxGradient fs n v i) j w)
      (fun w ↦ p ((w.1, w.2) : ParabolicPoint) - unitBallJointHarmonicApproxPressure gs n w)
      ψ z (fun h ↦ hz (hsupp h)))
  rw [heq]
  exact hineq

/-- The true tested-velocity difference depends only on the correction
difference, with an explicit finite-dimensional bound. -/
theorem projectedTestedVelocity_sub_norm_le (U H H' G : Vec3) :
    ‖(∑ i : Fin 3, (U i + H' i) * G i) -
      (∑ i : Fin 3, (U i + H i) * G i)‖ ≤ 3 * ‖H' - H‖ * ‖G‖ := by
  have heq : (∑ i : Fin 3, (U i + H' i) * G i) -
      (∑ i : Fin 3, (U i + H i) * G i) = ∑ i : Fin 3, (H' - H) i * G i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  exact vec3_coordinate_pairing_norm_le (H' - H) G

/-- The literal projected density with the genuine continuous harmonic
gradient, actual canonical Hessian, and actual momentum-derivative pressure. -/
def suitableProjectedLocalEnergyDensity
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) (ψ : Vec3 × ℝ → ℝ)
    (z : unitBallPressureCompactInterior × ℝ) : ℝ :=
  projectedEnergyDeficitPolynomial (u (z.1.1, z.2))
    (suitableProjectedHarmonicGradient u Du p t₀ z)
    (fun j ↦ spatialPartial ψ j (z.1.1, z.2)) (Du (z.1.1, z.2))
    (suitableProjectedHarmonicDerivative u Du p t₀ z)
    (p (z.1.1, z.2) -
      harmonicCompactPressureValues (-unitBallMomentumForceCurve u Du p z.2) z.1)
    (ψ (z.1.1, z.2)) (timePartial ψ (z.1.1, z.2))
    (∑ j, spatialSecondPartial ψ j j (z.1.1, z.2))

set_option maxHeartbeats 1000000 in
/-- The actual unforced suitable solution satisfies projected local energy for
its genuine nonsmooth harmonic correction. Every approximation class and limit
is derived from suitability; the theorem has only the original solution and
the actual nonnegative compact test as analytic hypotheses. -/
theorem suitable_projected_local_energy
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z)
    (hsupp : tsupport ψ ⊆
      unitBallPressureCompactInterior ×ˢ Ioo (t₀ - 4) (t₀ + 4)) :
    Integrable (suitableProjectedLocalEnergyDensity u Du p t₀ ψ)
      (harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) ∧
      (∫ z, suitableProjectedLocalEnergyDensity u Du p t₀ ψ z
        ∂harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) ≤ 0 := by
  let J := Ioo (t₀ - 4) (t₀ + 4)
  let T := Icc (t₀ - 4) (t₀ + 4)
  let μ := harmonicInteriorMeasure
  let ν := volume.restrict J
  let U : unitBallPressureCompactInterior × ℝ → Vec3 := fun z ↦ u (z.1.1, z.2)
  let D : unitBallPressureCompactInterior × ℝ → Fin 3 → Vec3 := fun z ↦ Du (z.1.1, z.2)
  let P : unitBallPressureCompactInterior × ℝ → ℝ := fun z ↦ p (z.1.1, z.2)
  let H := suitableProjectedHarmonicGradient u Du p t₀
  let B := suitableProjectedHarmonicDerivative u Du p t₀
  let Q : unitBallPressureCompactInterior × ℝ → ℝ := fun z ↦
    harmonicCompactPressureValues (-unitBallMomentumForceCurve u Du p z.2) z.1
  let G : unitBallPressureCompactInterior × ℝ → Vec3 :=
    fun z j ↦ spatialPartial ψ j (z.1.1, z.2)
  let Ψ : unitBallPressureCompactInterior × ℝ → ℝ := fun z ↦ ψ (z.1.1, z.2)
  let τ : unitBallPressureCompactInterior × ℝ → ℝ := fun z ↦ timePartial ψ (z.1.1, z.2)
  let Λ : unitBallPressureCompactInterior × ℝ → ℝ :=
    fun z ↦ ∑ j, spatialSecondPartial ψ j j (z.1.1, z.2)
  obtain ⟨gs, fs, hsm, _hAE, hconv, hforce, _hbound, hjoint, hfield, _hpressure⟩ :=
    exists_suitable_unitBall_harmonic_joint_smooth_sequence hsol hdom
  let Hs : ℕ → unitBallPressureCompactInterior × ℝ → Vec3 :=
    fun n z ↦ unitBallJointHarmonicApproxGradient fs n (z.1.1, z.2)
  let Bs := unitBallJointHarmonicApproxDerivative fs
  let Qs : ℕ → unitBallPressureCompactInterior × ℝ → ℝ :=
    fun n z ↦ unitBallJointHarmonicApproxPressure gs n (z.1.1, z.2)
  obtain ⟨CH, CB, hCH, hCHzero, hCB, hCBzero, hHb, hBb, hHs, hBs⟩ :=
    suitable_harmonicInterior_uniform_approximations hsol hdom
      (fun n ↦ (hsm n).2.1) hforce hfield
  obtain ⟨hU, hD, hP⟩ := suitable_harmonicInterior_memLp hsol hdom
  obtain ⟨hH, hB⟩ := suitable_harmonicInterior_correction_memLp_top hsol hdom
  have ht : ∀ᵐ z : unitBallPressureCompactInterior × ℝ ∂μ.prod ν, z.2 ∈ J :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioo)).mpr
      (ae_of_all _ fun _ ↦ ae_restrict_mem measurableSet_Ioo)
  have hHbAE (n : ℕ) : ∀ᵐ z ∂μ.prod ν, ‖Hs n z - H z‖ ≤ CH n :=
    ht.mono fun z hz ↦ hHb n z.2 (Ioo_subset_Icc_self hz) z.1
  have hBbAE (n : ℕ) (i j : Fin 3) :
      ∀ᵐ z ∂μ.prod ν, ‖Bs n z i j - B z i j‖ ≤ CB n :=
    ht.mono fun z hz ↦ hBb n z.2 (Ioo_subset_Icc_self hz) z.1 i j
  have hV (i : Fin 3) : MemLp (fun z ↦ U z i + H z i) 3 (μ.prod ν) :=
    (memLp_pi_iff.mp hU i).add ((memLp_pi_iff.mp hH i).mono_exponent le_top)
  have hVs (n : ℕ) (i : Fin 3) : MemLp (fun z ↦ U z i + Hs n z i) 3 (μ.prod ν) :=
    (memLp_pi_iff.mp hU i).add ((memLp_pi_iff.mp (hHs n) i).mono_exponent le_top)
  have hW (i j : Fin 3) : MemLp (fun z ↦ D z i j + B z i j) 2 (μ.prod ν) :=
    (memLp_pi_iff.mp (memLp_pi_iff.mp hD i) j).add ((hB i j).mono_exponent le_top)
  have hWs (n : ℕ) (i j : Fin 3) :
      MemLp (fun z ↦ D z i j + Bs n z i j) 2 (μ.prod ν) :=
    (memLp_pi_iff.mp (memLp_pi_iff.mp hD i) j).add ((hBs n i j).mono_exponent le_top)
  have hVc (i : Fin 3) : Tendsto (fun n ↦ eLpNorm
      (fun z ↦ (U z i + Hs n z i) - (U z i + H z i)) 3 (μ.prod ν)) atTop (𝓝 0) := by
    have hc := tendsto_eLpNorm_sub_of_uniform_bound (p := 3) (by norm_num) (by norm_num)
      (memLp_pi_iff.mp hH i).aestronglyMeasurable
      (fun n ↦ (memLp_pi_iff.mp (hHs n) i).aestronglyMeasurable) hCH hCHzero
      (fun n ↦ (hHbAE n).mono fun z hz ↦ (norm_le_pi_norm (Hs n z - H z) i).trans hz)
    convert hc using 1
    funext n
    congr 1
    ext z
    simp only [Pi.sub_apply]
    ring
  have hWc (i j : Fin 3) : Tendsto (fun n ↦ eLpNorm
      (fun z ↦ (D z i j + Bs n z i j) - (D z i j + B z i j)) 2 (μ.prod ν))
      atTop (𝓝 0) := by
    have hc := tendsto_eLpNorm_sub_of_uniform_bound (p := 2) (by norm_num) (by norm_num)
      (hB i j).aestronglyMeasurable (fun n ↦ (hBs n i j).aestronglyMeasurable)
      hCB hCBzero (fun n ↦ hBbAE n i j)
    convert hc using 1
    funext n
    congr 1
    ext z
    simp only [Pi.sub_apply]
    ring
  have hBc (i j : Fin 3) : Tendsto (fun n ↦ eLpNorm
      (fun z ↦ Bs n z i j - B z i j) ⊤ (μ.prod ν)) atTop (𝓝 0) :=
    tendsto_eLpNorm_top_sub_of_uniform_bound (hB i j).aestronglyMeasurable
      (fun n ↦ (hBs n i j).aestronglyMeasurable) hCBzero (fun n ↦ hBbAE n i j)
  have hGcont : Continuous (fun z : Vec3 × ℝ ↦ fun j ↦ spatialPartial ψ j z) :=
    continuous_pi fun j ↦ (spatialPartial_contDiff hψ.1 j).continuous
  let GK : C(unitBallPressureCompactInterior × T, Vec3) :=
    ⟨fun z ↦ G (z.1, z.2.1), hGcont.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))⟩
  have hGb (t : ℝ) (ht : t ∈ T) (x : unitBallPressureCompactInterior) :
      ‖G (x, t)‖ ≤ ‖GK‖ := GK.norm_coe_le_norm (x, ⟨t, ht⟩)
  have hG : MemLp G ⊤ (μ.prod ν) := MemLp.of_bound
    (hGcont.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      continuous_snd)).aestronglyMeasurable ‖GK‖
    (ht.mono fun z hz ↦ hGb z.2 (Ioo_subset_Icc_self hz) z.1)
  have hΨ : MemLp Ψ ⊤ (μ.prod ν) := by
    obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction hψ
    exact MemLp.of_bound
      (hψ.1.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        continuous_snd)).aestronglyMeasurable C (ae_of_all _ fun z ↦ hC (z.1.1, z.2))
  have hτ : MemLp τ ⊤ (μ.prod ν) := by
    obtain ⟨C, hC⟩ := exists_bound_timePartial_of_mem_spaceTimeTestFunction hψ
    exact MemLp.of_bound
      ((contDiff_timePartial hψ.1).continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable
      C (ae_of_all _ fun z ↦ hC (z.1.1, z.2))
  have hΛ : MemLp Λ ⊤ (μ.prod ν) := by
    apply memLp_finsetSum
    intro i _
    obtain ⟨C, hC⟩ := exists_bound_spatialSecondPartial_of_mem_spaceTimeTestFunction hψ i i
    exact MemLp.of_bound
      ((spatialPartial_contDiff (spatialPartial_contDiff hψ.1 i) i).continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable
      C (ae_of_all _ fun z ↦ hC (z.1.1, z.2))
  obtain ⟨hUslices, hUclass⟩ := suitable_harmonicInterior_velocity_slice_data hsol hdom
  obtain ⟨hHslices, hHclass⟩ := actualSliceLp_memLp_top_of_joint_memLp_top hH
  have hVslice := actual_velocity_slice_data_add hUslices hHslices hUclass hHclass
  have hVnslice (n : ℕ) := actual_velocity_slice_data_add hUslices
    (actualSliceLp_memLp_top_of_joint_memLp_top (hHs n)).1 hUclass
    (actualSliceLp_memLp_top_of_joint_memLp_top (hHs n)).2
  have hGN : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖G (x, t)‖ ≤ ‖GK‖ :=
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht ↦
      ae_of_all _ fun x ↦ hGb t (Ioo_subset_Icc_self ht) x
  have hA : ProjectedEnergySliceData μ ν ⊤ (projectedTestedVelocity U H G) :=
    projectedEnergySliceData_top_tested_velocity
      (hU.aestronglyMeasurable.add hH.aestronglyMeasurable) hG.aestronglyMeasurable
      hVslice.1 hVslice.2 hGN
  have hAs (n : ℕ) :
      ProjectedEnergySliceData μ ν ⊤ (projectedTestedVelocity U (Hs n) G) :=
    projectedEnergySliceData_top_tested_velocity
      (hU.aestronglyMeasurable.add (hHs n).aestronglyMeasurable) hG.aestronglyMeasurable
      (hVnslice n).1 (hVnslice n).2 hGN
  have hAzero : Tendsto (fun n ↦ 3 * CH n * ‖GK‖) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (tendsto_const_nhds.mul hCHzero).mul tendsto_const_nhds
  have hAstrong : ProjectedEnergySliceStrong μ ν ⊤
      (projectedTestedVelocity U H G) (fun n ↦ projectedTestedVelocity U (Hs n) G) := by
    apply projectedEnergySliceStrong_top_of_uniform_bound hA hAs
      (fun n ↦ mul_nonneg (mul_nonneg (by norm_num) (hCH n)) (norm_nonneg _)) hAzero
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    apply ae_of_all
    intro x
    apply (projectedTestedVelocity_sub_norm_le (U (x, t)) (H (x, t))
      (Hs n (x, t)) (G (x, t))).trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hHb n t (Ioo_subset_Icc_self ht) x) (by norm_num))
      (hGb t (Ioo_subset_Icc_self ht) x) (norm_nonneg _)
      (mul_nonneg (by norm_num) (hCH n))
  have hQ := suitable_harmonicInterior_pressure_sliceStrong hsol hdom
    (fun n ↦ (hsm n).2.2.2.2.1) hconv
  have hLEI : ∀ᶠ n in atTop, (∫ z, projectedEnergyDeficitPolynomial (U z) (Hs n z)
      (G z) (D z) (Bs n z) (P z - Qs n z) (Ψ z) (τ z) (Λ z) ∂μ.prod ν) ≤ 0 :=
    Eventually.of_forall fun n ↦ suitable_unitBall_joint_smooth_projected_energy_compact
      hsol (fun n ↦ ⟨(hsm n).1, (hsm n).2.1, (hsm n).2.2.2.2.2⟩) hψ hnψ hsupp n
  exact projectedEnergy_inequality_of_strongLp (memLp_pi_iff.mp hU) hV hW hB hP
    hVs hWs hBs (memLp_pi_iff.mp hG) hΨ hτ hΛ hVc hWc hBc hQ hAstrong hLEI

end FluidSingularSets
