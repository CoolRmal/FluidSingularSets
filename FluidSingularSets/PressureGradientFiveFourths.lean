-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import CKN.ClassEquivalence.VelocityTenThirds
public import CKN.Core.Step4.WeakGradientGluingTSuitableSelection
public import CKN.Core.Step4.WeakGradientGluingTSuitableIdentification
public import CKN.Core.Step4.WeakGradientGluingTRemainderMajorant
public import CKN.Core.Step4.WeakGradientGluingTFixedSelection
public import CKN.Core.Step4.PressureGradientHGCloserCellsMeans
public import CKN.Leray.RieszPressurePackageAgreement

/-!
# Pressure gradients at the box-dimension exponent

The actual local energy class gives velocity in `L^(10/3)` and its spatial
weak gradient in `L²`. Hölder therefore puts their product in `L^(5/4)`.
The concrete cutoff pressure decomposition and unconditional Riesz bounds
transfer this exponent to the pressure gradient.

The analytic operators and suitable-solution estimates reused here are the
proved CKN results of Scott Armstrong and Vlad Vicol, under Apache 2.0.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Core.Step4 CKN.Leray
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Every actual suitable velocity component has the local energy exponent. -/
theorem suitable_velocity_component_memLp_tenThirds
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (i : Fin 3) :
    MemLp (fun w ↦ u w i) (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
  obtain ⟨Ω', J, hbox, hQsub⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hcenter : z.1 ∈ vec3Ball z.1 ρ := by
    simpa only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero] using hρ
  have htop : z.2 ∈ Ioc (z.2 - ρ ^ 2) z.2 :=
    ⟨by nlinarith [sq_pos_of_pos hρ], le_rfl⟩
  have hball : vec3Ball z.1 ρ ⊆ Ω' := fun x hx ↦ (hQsub (a := (x, z.2)) ⟨hx, htop⟩).1
  have htime : Ioc (z.2 - ρ ^ 2) z.2 ⊆ J := fun t ht ↦ (hQsub (a := (z.1, t)) ⟨hcenter, ht⟩).2
  exact (velocity_component_memLp_tenThirds_on_ballBox_of_data hsol.toData
    hbox hρ hball i).mono_measure (Measure.restrict_mono_set volume (prod_mono le_rfl htime))

/-- The genuine velocity-gradient product has precisely the `5/4` exponent. -/
theorem suitable_velocity_gradient_product_memLp_fiveFourths
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (i j k : Fin 3) :
    MemLp (fun w ↦ Du w i j * u w k) (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
  let : ENNReal.HolderTriple 2 (ENNReal.ofReal (10 / 3 : ℝ))
      (ENNReal.ofReal (5 / 4 : ℝ)) := by
    have h : Real.HolderTriple 2 (10 / 3 : ℝ) (5 / 4 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    simpa only [ENNReal.ofReal_ofNat] using h.ennrealOfReal
  have hcompact : IsCompact (closure (parabolicCylinder z.1 z.2 ρ)) := by
    rw [closure_parabolicCylinder hρ]
    have hx := isCompact_closure_vec3Ball (x := z.1) hρ
    rw [closure_vec3Ball hρ] at hx
    have hp := hx.prod (isCompact_Icc : IsCompact (Icc (z.2 - ρ ^ 2) z.2))
    exact parabolicHomeomorph.isCompact_preimage.mpr hp
  have hDu := gradient_memLp_two_on_compact_of_data hsol.toData hcompact hsub
  have hlocal := hDu.mono_measure (Measure.restrict_mono_set volume subset_closure)
  exact ((hlocal.eval i).eval j).mul
    (suitable_velocity_component_memLp_tenThirds hsol hρ hsub k)

/-- The localized quadratic tensor belongs to `L^(5/3)`. -/
theorem suitable_quadratic_tensor_memLp_fiveThirds
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (i j : Fin 3) :
    MemLp (fun w ↦ u w i * u w j) (ENNReal.ofReal (5 / 3 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
  let : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3 : ℝ))
      (ENNReal.ofReal (10 / 3 : ℝ)) (ENNReal.ofReal (5 / 3 : ℝ)) := by
    exact (show Real.HolderTriple (10 / 3 : ℝ) (10 / 3 : ℝ) (5 / 3 : ℝ) by
      rw [Real.holderTriple_iff]; norm_num).ennrealOfReal
  exact (suitable_velocity_component_memLp_tenThirds hsol hρ hsub i).mul
    (suitable_velocity_component_memLp_tenThirds hsol hρ hsub j)

/-- The exact ball and backward window are an admissible local energy box. -/
theorem pressure_localBox_of_closed_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    localBox Ω I (vec3Ball z.1 ρ) (Ioc (z.2 - ρ ^ 2) z.2) := by
  have hcl : closure (Ioc (z.2 - ρ ^ 2) z.2) ⊆ Icc (z.2 - ρ ^ 2) z.2 :=
    closure_minimal Ioc_subset_Icc_self isClosed_Icc
  rw [closure_parabolicCylinder hρ] at hsub
  refine ⟨isOpen_vec3Ball _ _, isCompact_closure_vec3Ball hρ, ?_,
    ordConnected_Ioc, isCompact_Icc.of_isClosed_subset isClosed_closure hcl, ?_⟩
  · intro y hy
    rw [closure_vec3Ball hρ] at hy
    exact (hsub (a := (y, z.2)) ⟨hy, by linarith only [sq_nonneg ρ], le_rfl⟩).1
  · intro t ht
    exact (hsub (a := (z.1, t)) ⟨by
      simpa only [Set.mem_ofPred_eq, sub_self, vec3EuclideanNorm_zero] using hρ.le,
      hcl ht⟩).2

/-- Suitability puts the genuine centred cutoff divergence source in global
space-time `L^(5/4)` after extending it by zero outside its fixed cylinder. -/
theorem suitable_centred_cutoff_source_memLp_fiveFourths
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (i : Fin 3) :
    let η := mollifiedBallCutoff z.1 hρ
    let c := sourceSliceCentredMean z.1 ρ u
    let V := sourceMorreyCutoffVCentredTensorSpacetime η (spatialDeriv η) u Du c
    MemLp ((parabolicCylinder z.1 z.2 ρ).indicator (fun w ↦ V w i))
      (ENNReal.ofReal (5 / 4 : ℝ)) volume := by
  dsimp only
  let Q := parabolicCylinder z.1 z.2 ρ
  let B := vec3Ball z.1 ρ
  let J := Ioc (z.2 - ρ ^ 2) z.2
  let η := mollifiedBallCutoff z.1 hρ
  let c := sourceSliceCentredMean z.1 ρ u
  let : IsFiniteMeasure (volume.restrict Q) :=
    isFiniteMeasure_restrict.mpr Integration.volume_parabolicCylinder_lt_top.ne
  let : ENNReal.HolderTriple 2 (ENNReal.ofReal (10 / 3 : ℝ))
      (ENNReal.ofReal (5 / 4 : ℝ)) := by
    have h : Real.HolderTriple 2 (10 / 3 : ℝ) (5 / 4 : ℝ) := by
      rw [Real.holderTriple_iff]; norm_num
    simpa only [ENNReal.ofReal_ofNat] using h.ennrealOfReal
  let : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3 : ℝ))
      (ENNReal.ofReal (10 / 3 : ℝ)) (ENNReal.ofReal (5 / 3 : ℝ)) := by
    exact (show Real.HolderTriple (10 / 3 : ℝ) (10 / 3 : ℝ) (5 / 3 : ℝ) by
      rw [Real.holderTriple_iff]; norm_num).ennrealOfReal
  have hbox := pressure_localBox_of_closed_cylinder hρ hsub
  obtain ⟨C, _hC, hmeanBound⟩ := pressure_source_mean_ae_bounded_of_sws hsol hbox
  have hprod : (volume : Measure ParabolicPoint).restrict Q =
      (volume.restrict B).prod (volume.restrict J) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
    rfl
  have hmeanBoundProd : ∀ᵐ w ∂volume.restrict Q, ∀ j : Fin 3, |c w.2 j| ≤ C := by
    rw [hprod]
    exact (Measure.quasiMeasurePreserving_snd (μ := volume.restrict B)).ae hmeanBound
  have hc (j : Fin 3) : MemLp (fun w : ParabolicPoint ↦ c w.2 j) ∞
      (volume.restrict Q) := by
    have hm := (pressure_source_mean_aemeasurable_of_sws hsol hbox j).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := volume.restrict B))
    have hm' : AEStronglyMeasurable (fun w : ParabolicPoint ↦ c w.2 j)
        (volume.restrict Q) := by rw [hprod]; exact hm.aestronglyMeasurable
    apply MemLp.of_bound hm' C
    filter_upwards [hmeanBoundProd] with w hw
    simpa only [Real.norm_eq_abs] using hw j
  have hη : MemLp (fun w : ParabolicPoint ↦ η w.1) ∞ (volume.restrict Q) := by
    apply MemLp.of_bound
      ((mollifiedBallCutoff_smooth z.1 hρ).continuous.measurable.comp
        measurable_fst).aestronglyMeasurable 1
    exact Eventually.of_forall fun w ↦ by
      change |mollifiedBallCutoff z.1 hρ w.1| ≤ 1
      rw [abs_of_nonneg (mollifiedBallCutoff_nonneg z.1 hρ w.1)]
      exact mollifiedBallCutoff_le_one z.1 hρ w.1
  have hdη (j : Fin 3) : MemLp (fun w : ParabolicPoint ↦ spatialDeriv η j w.1) ∞
      (volume.restrict Q) := by
    have hm : Measurable (spatialDeriv η j) :=
      (contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth z.1 hρ) j).continuous.measurable
    apply MemLp.of_bound
      (hm.comp measurable_fst).aestronglyMeasurable (cutoffGradientConstant / ρ)
    exact Eventually.of_forall fun w ↦ by
      change |spatialDeriv η j w.1| ≤ cutoffGradientConstant / ρ
      exact (abs_apply_le_vecEuclideanNorm (classicalGradient η w.1) j).trans
        (mollifiedBallCutoff_gradient_bound z.1 hρ w.1)
  have hu (j : Fin 3) := suitable_velocity_component_memLp_tenThirds hsol hρ hsub j
  have hcompact : IsCompact (closure Q) := by
    rw [closure_parabolicCylinder hρ]
    have hx := isCompact_closure_vec3Ball (x := z.1) hρ
    rw [closure_vec3Ball hρ] at hx
    have hp := hx.prod (isCompact_Icc : IsCompact (Icc (z.2 - ρ ^ 2) z.2))
    exact parabolicHomeomorph.isCompact_preimage.mpr hp
  have hDu := (gradient_memLp_two_on_compact_of_data hsol.toData hcompact hsub).mono_measure
    (Measure.restrict_mono_set volume subset_closure)
  have hw (j : Fin 3) : MemLp (fun w ↦ u w j - c w.2 j)
      (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict Q) :=
    (hu j).sub ((hc j).mono_exponent le_top)
  apply (memLp_indicator_iff_restrict (measurableSet_parabolicCylinder _ _ _)).mpr
  change MemLp (fun w : ParabolicPoint ↦ ∑ j,
      (η w.1 * Du w i j * (u w j - c w.2 j) +
        spatialDeriv η j w.1 * u w i * (u w j - c w.2 j)))
    (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict Q)
  have hterm (j : Fin 3) : MemLp (fun w : ParabolicPoint ↦
      η w.1 * Du w i j * (u w j - c w.2 j) +
        spatialDeriv η j w.1 * u w i * (u w j - c w.2 j))
      (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict Q) := by
    have hderiv : MemLp _ (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict Q) :=
      ((hDu.eval i).eval j).mul (hw j)
    have hquadratic : MemLp _ (ENNReal.ofReal (5 / 3 : ℝ)) (volume.restrict Q) :=
      (hu i).mul (hw j)
    have hmain : MemLp _ (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict Q) :=
      hη.mul hderiv
    have hcut : MemLp _ (ENNReal.ofReal (5 / 3 : ℝ)) (volume.restrict Q) :=
      (hdη j).mul hquadratic
    have hcut' := hcut.mono_exponent
      (by norm_num : ENNReal.ofReal (5 / 4 : ℝ) ≤ ENNReal.ofReal (5 / 3 : ℝ))
    convert hmain.add hcut' using 1
    funext w
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  convert memLp_finsetSum' Finset.univ (fun j _ ↦ hterm j) using 1
  funext w
  simp only [Finset.sum_apply]

/-- The CKN gradient extension and the signed all-exponent pressure operator
are the same bounded operator at their common exponent. -/
theorem gradient_riesz_eq_neg_pressure_operator
    (j i : Fin 3) {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume) :
    rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) G =ᵐ[volume]
        fun x ↦ -rieszPressureOperator (6 / 5) (by norm_num) j i (hG.toLp G) x := by
  let : Fact (1 ≤ ENNReal.ofReal (6 / 5 : ℝ)) := ⟨by norm_num⟩
  let A := lpExtensionCore (by norm_num : ENNReal.ofReal (6 / 5 : ℝ) ≠ ∞)
    (rieszSecondGradientExtensionInput (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i))
  let B := -rieszPressureOperator (6 / 5) (by norm_num) j i
  have hclosed : IsClosed {v | A v = B v} := isClosed_eq A.continuous B.continuous
  have hdense := (MeasureTheory.Lp.dense_hasCompactSupport_contDiff
    (F := ℝ) (p := ENNReal.ofReal (6 / 5 : ℝ)) (μ := (volume : Measure Vec3))
    ENNReal.ofReal_ne_top).denseRange_val
  have heq : A (hG.toLp G) = B (hG.toLp G) := by
    apply isClosed_property hdense hclosed
    rintro ⟨v, g, hvg, hgc, hg⟩
    have hgp : MemLp g (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
      hg.continuous.memLp_of_hasCompactSupport hgc
    have hg₂ : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
    have hv : v = hgp.toLp g := Lp.ext (hvg.trans hgp.coeFn_toLp.symm)
    change A v = B v
    rw [hv]
    apply Lp.ext
    have hleft := lpExtensionRepresentative_ae_eq_core (by norm_num)
      (rieszSecondGradientExtensionInput (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i)) hgp
    have hraw := rieszSecondGradientExtensionOperator_ae_raw (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) hgp hg₂
    have hright := rieszPressureOperator_ae_eq_negRaw (6 / 5) (by norm_num) j i g hgp hg₂
    have hneg := Lp.coeFn_neg (rieszPressureOperator (6 / 5) (by norm_num) j i (hgp.toLp g))
    filter_upwards [hleft, hraw, hright, hneg] with x hl hr hp hn
    dsimp [A, B] at hl ⊢
    rw [← hl]
    change rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) g x = _
    rw [hr]
    change _ = (-rieszPressureOperator (6 / 5) (by norm_num) j i (hgp.toLp g)) x
    rw [hn, Pi.neg_apply, hp, neg_neg]
  have hleft := lpExtensionRepresentative_ae_eq_core (by norm_num)
    (rieszSecondGradientExtensionInput (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i)) hG
  have hright := (Lp.ext_iff.mp heq).trans
    (Lp.coeFn_neg (rieszPressureOperator (6 / 5) (by norm_num) j i (hG.toLp G)))
  exact hleft.trans hright

/-- A tensor with one active entry embeds a scalar source into the pressure API. -/
def singlePressureTensor (j i : Fin 3) (G : Vec3 × ℝ → ℝ) :
    Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
  fun a b ↦ if a = j ∧ b = i then G else 0

private theorem singlePressureTensor_memLp
    (j i : Fin 3) {G : Vec3 × ℝ → ℝ} {r : ℝ≥0∞} (hG : MemLp G r volume) :
    ∀ a b, MemLp (singlePressureTensor j i G a b) r volume := by
  intro a b
  by_cases h : a = j ∧ b = i
  · simpa [singlePressureTensor, h] using hG
  · simp [singlePressureTensor, h]

private theorem singlePressureTensor_spacetime_eq_component
    (r : ℝ) (hr : 1 < r) (j i : Fin 3) {G : Vec3 × ℝ → ℝ}
    (hG : MemLp G (ENNReal.ofReal r) volume) :
    rieszPressureSpaceTime r hr (singlePressureTensor j i G)
      (singlePressureTensor_memLp j i hG) =
        rieszPressureSpaceTimeComponentRepresentative r hr j i (hG.toLp G) := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  have hinput (a b : Fin 3) :
      (singlePressureTensor_memLp j i hG a b).toLp (singlePressureTensor j i G a b) =
        if a = j ∧ b = i then hG.toLp G else 0 := by
    by_cases h : a = j ∧ b = i
    · simp [singlePressureTensor, h]
    · simp [singlePressureTensor, h, MemLp.toLp_zero]
  have hclass : rieszPressureSpaceTimeClass r hr
      (rieszPressureSpaceTimeTensorToLp r hr (singlePressureTensor j i G)
        (singlePressureTensor_memLp j i hG)) =
        rieszPressureSpaceTimeComponent r hr j i (hG.toLp G) := by
    unfold rieszPressureSpaceTimeClass rieszPressureSpaceTimeTensorToLp
    simp_rw [hinput]
    simp only [apply_ite, map_zero, ite_and]
    simp
  exact congrArg (fun v : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ↦
    (Lp.aestronglyMeasurable v).aemeasurable.mk v) hclass

/-- Completed space-time Riesz representatives at `5/4` and `6/5` agree on
sources in both spaces, without an `L²` premise. -/
theorem pressure_component_spacetime_ae_eq_fiveFourths_sixFifths
    (j i : Fin 3) {G : Vec3 × ℝ → ℝ}
    (hG₅ : MemLp G (ENNReal.ofReal (5 / 4 : ℝ)) volume)
    (hG₆ : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume) :
    rieszPressureSpaceTimeComponentRepresentative (5 / 4) (by norm_num) j i (hG₅.toLp G)
      =ᵐ[volume]
        rieszPressureSpaceTimeComponentRepresentative (6 / 5) (by norm_num) j i
          (hG₆.toLp G) := by
  have h := rieszPressureSpaceTime_ae_eq_of_memLp_common
    (5 / 4) (by norm_num) (6 / 5) (by norm_num) (singlePressureTensor j i G)
      (singlePressureTensor_memLp j i hG₅) (singlePressureTensor_memLp j i hG₆)
  rw [singlePressureTensor_spacetime_eq_component,
    singlePressureTensor_spacetime_eq_component] at h
  exact h

/-- The existing jointly measurable `6/5` gradient representative inherits
`5/4` integrability from its source and the unconditional all-exponent operator. -/
theorem gradient_riesz_spacetime_memLp_fiveFourths
    (j i : Fin 3) {G T : Vec3 × ℝ → ℝ}
    (hG₅ : MemLp G (ENNReal.ofReal (5 / 4 : ℝ)) volume)
    (hG₆ : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hT : Measurable T)
    (hTs : ∀ᵐ s ∂volume, (fun y ↦ T (y, s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i) (fun y ↦ G (y, s))) :
    MemLp T (ENNReal.ofReal (5 / 4 : ℝ)) volume := by
  let P₅ := rieszPressureSpaceTimeComponentRepresentative (5 / 4) (by norm_num) j i
    (hG₅.toLp G)
  let P₆ := rieszPressureSpaceTimeComponentRepresentative (6 / 5) (by norm_num) j i
    (hG₆.toLp G)
  have hPm : Measurable P₆ :=
    rieszPressureSpaceTimeComponentRepresentative_measurable _ _ _ _ _
  have hPmem : MemLp P₅ (ENNReal.ofReal (5 / 4 : ℝ)) volume := by
    apply (Lp.memLp (rieszPressureSpaceTimeComponent (5 / 4) (by norm_num) j i
      (hG₅.toLp G))).ae_eq
    exact (Lp.aestronglyMeasurable _).aemeasurable.ae_eq_mk
  have hP56 : P₅ =ᵐ[volume] P₆ :=
    pressure_component_spacetime_ae_eq_fiveFourths_sixFifths j i hG₅ hG₆
  have hT6 : T =ᵐ[volume] fun w ↦ -P₆ w := by
    apply ae_eq_of_ae_time_sections hT hPm.neg
    filter_upwards [hTs, rieszPressureSpaceTimeComponent_slice_ae_eq
      (6 / 5) (by norm_num) j i hG₆] with s ht hp
    obtain ⟨hGs, hps⟩ := hp
    have hgrad := gradient_riesz_eq_neg_pressure_operator j i hGs
    exact ht.trans (hgrad.trans hps.symm.neg)
  exact hPmem.neg.ae_eq ((hT6.trans hP56.symm.neg).symm)

/-- The localized actual force also belongs to `L^(5/4)`. -/
theorem suitable_cutoff_force_memLp_fiveFourths
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (i : Fin 3) :
    MemLp ((parabolicCylinder z.1 z.2 ρ).indicator
      (fun w ↦ mollifiedBallCutoff z.1 hρ w.1 * f w i))
      (ENNReal.ofReal (5 / 4 : ℝ)) volume := by
  let Q := parabolicCylinder z.1 z.2 ρ
  let : IsFiniteMeasure (volume.restrict Q) :=
    isFiniteMeasure_restrict.mpr Integration.volume_parabolicCylinder_lt_top.ne
  have hfq : MemLp f (ENNReal.ofReal q) (volume.restrict Q) :=
    hsol.toData.memLp_force (pressure_localBox_of_closed_cylinder hρ hsub)
  have hf := (hfq.eval i).mono_exponent
      (ENNReal.ofReal_le_ofReal (by linarith only [hsol.2.2.2.1] : (5 / 4 : ℝ) ≤ q))
  have hη : MemLp (fun w : ParabolicPoint ↦ mollifiedBallCutoff z.1 hρ w.1) ∞
      (volume.restrict Q) := by
    apply MemLp.of_bound
      ((mollifiedBallCutoff_smooth z.1 hρ).continuous.measurable.comp
        measurable_fst).aestronglyMeasurable 1
    exact Eventually.of_forall fun w ↦ by
      change |mollifiedBallCutoff z.1 hρ w.1| ≤ 1
      rw [abs_of_nonneg (mollifiedBallCutoff_nonneg z.1 hρ w.1)]
      exact mollifiedBallCutoff_le_one z.1 hρ w.1
  exact (memLp_indicator_iff_restrict (measurableSet_parabolicCylinder _ _ _)).mpr
    (hη.mul hf)

private theorem indicator_memLp_sixFifths_of_fiveFourths
    {Q : Set ParabolicPoint} (hQ : MeasurableSet Q) (hfin : volume Q < ∞)
    {F : ParabolicPoint → ℝ}
    (hF : MemLp (Q.indicator F) (ENNReal.ofReal (5 / 4 : ℝ)) volume) :
    MemLp (Q.indicator F) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  let : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.mpr hfin.ne
  exact (memLp_indicator_iff_restrict hQ).mpr
    (((memLp_indicator_iff_restrict hQ).mp hF).mono_exponent (by norm_num))

/-- A finite time moment of a slice majorant gives the corresponding genuine
space-time norm on every finite-volume spatial box. -/
theorem memLp_threeHalves_of_slice_majorant
    {B : Set Vec3} {J : Set ℝ} (hB : volume B < ∞)
    {H : ParabolicPoint → ℝ} (hH : Measurable H) {M : ℝ → ℝ≥0∞}
    (hM : AEMeasurable M (volume.restrict J))
    (hmoment : (∫⁻ s in J, M s ^ (3 / 2 : ℝ)) < ∞)
    (hbound : ∀ᵐ s ∂volume.restrict J, ∀ᵐ y ∂volume.restrict B,
      ‖H (y, s)‖ₑ ≤ M s) :
    MemLp H (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (B ×ˢ J)) := by
  have hprod : (volume : Measure ParabolicPoint).restrict (B ×ˢ J) =
      (volume.restrict B).prod (volume.restrict J) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hf : AEStronglyMeasurable H ((volume.restrict B).prod (volume.restrict J)) := by
    rw [← hprod]
    exact hH.aestronglyMeasurable
  have hpower : (∫⁻ w in B ×ˢ J, ‖H w‖ₑ ^ (3 / 2 : ℝ)) < ∞ := by
    rw [hprod, lintegral_prod_symm _ (hf.aemeasurable.enorm.pow_const _)]
    have hle : (∫⁻ s in J, ∫⁻ y in B, ‖H (y, s)‖ₑ ^ (3 / 2 : ℝ)) ≤
        ∫⁻ s in J, volume B * M s ^ (3 / 2 : ℝ) := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with s hs
      calc
        (∫⁻ y in B, ‖H (y, s)‖ₑ ^ (3 / 2 : ℝ)) ≤ ∫⁻ _y in B, M s ^ (3 / 2 : ℝ) :=
          lintegral_mono_ae (hs.mono fun y hy ↦ ENNReal.rpow_le_rpow hy (by norm_num))
        _ = volume B * M s ^ (3 / 2 : ℝ) := by
          rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
    have hfinite : (∫⁻ s in J, volume B * M s ^ (3 / 2 : ℝ)) < ∞ := by
      rw [lintegral_const_mul'' _ (hM.pow_const _)]
      exact ENNReal.mul_lt_top hB hmoment
    exact hle.trans_lt hfinite
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num) ENNReal.ofReal_ne_top hH.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hpower.ne

/-- Actual suitability gives one measurable spatial weak pressure gradient
in `L^(5/4)` on an interior symmetric cylinder. The conclusion uses the
pressure supplied by the solution, with no pressure-gradient premise. -/
theorem exists_suitable_pressure_gradient_memLp_fiveFourths
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R)
    (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ))
        (volume.restrict (vec3Ball z₀.1 (R / 2) ×ˢ
          Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4))) ∧
      ∀ᵐ s ∂volume.restrict (Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4)),
        ∀ i : Fin 3,
          LocallyIntegrableOn (fun y ↦ Dp (y, s) i) (vec3Ball z₀.1 (R / 2)) volume ∧
          HasWeakPartialDerivOn (vec3Ball z₀.1 (R / 2)) i
            (fun y ↦ p (y, s)) (fun y ↦ Dp (y, s) i) := by
  let z : ParabolicPoint := (z₀.1, z₀.2 + R ^ 2 / 4)
  let Q := parabolicCylinder z.1 z.2 R
  let J := Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4)
  let J₀ := Ioc (z.2 - R ^ 2) z.2
  let B := vec3Ball z₀.1 (R / 2)
  let η := mollifiedBallCutoff z₀.1 hR
  let V := sourceMorreyCutoffVCentredTensorSpacetime η (spatialDeriv η) u Du
    (sourceSliceCentredMean z₀.1 R u)
  have hsub : closure Q ⊆ spaceTimeSet Ω I :=
    (closure_fixed_pressure_cylinder_subset_doubled_ball z₀ hR).trans hdom
  have hJ : J ⊆ J₀ := by
    intro s hs
    exact ⟨by dsimp [J, J₀, z] at *; nlinarith only [hs.1, sq_pos_of_pos hR], hs.2.le⟩
  obtain ⟨Dp, T, Tforce, H, hDp, hT, hTf, hH, hweak, hTs, hTfs, hdecomp, hHs⟩ :=
    exists_measurable_fixed_pressure_decomposition_of_sws hsol z₀ hR hdom
  have hTmem (j i : Fin 3) : MemLp (T j i) (ENNReal.ofReal (5 / 4 : ℝ)) volume := by
    have hV₅ := suitable_centred_cutoff_source_memLp_fiveFourths hsol hR hsub j
    have hV₆ := indicator_memLp_sixFifths_of_fiveFourths
      (measurableSet_parabolicCylinder _ _ _) Integration.volume_parabolicCylinder_lt_top hV₅
    exact gradient_riesz_spacetime_memLp_fiveFourths j i hV₅ hV₆ (hT j i) (hTs j i)
  have hFmem (j i : Fin 3) : MemLp (Tforce j i) (ENNReal.ofReal (5 / 4 : ℝ)) volume := by
    have hF₅ := suitable_cutoff_force_memLp_fiveFourths hsol hR hsub j
    have hF₆ := indicator_memLp_sixFifths_of_fiveFourths
      (measurableSet_parabolicCylinder _ _ _) Integration.volume_parabolicCylinder_lt_top hF₅
    exact gradient_riesz_spacetime_memLp_fiveFourths j i hF₅ hF₆ (hTf j i) (hTfs j i)
  obtain ⟨M, hM, hmoment, hMb⟩ := fixed_remainder_temporal_majorant_of_sws
    hsol.2.2.2.1 hsol hR hsub
  have hHmem (i : Fin 3) : MemLp (H i) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (B ×ˢ J)) := by
    apply memLp_threeHalves_of_slice_majorant Integration.volume_vec3Ball_lt_top (hH i)
      (hM.mono_measure (Measure.restrict_mono_set volume hJ))
      ((lintegral_mono_set hJ).trans_lt hmoment)
    filter_upwards [hHs, ae_restrict_of_ae_restrict_of_subset hJ hMb] with s hs hm
    filter_upwards [hs i, ae_restrict_mem (vec3Ball_measurable _ _)] with y hy hyB
    rw [hy]
    exact hm i y hyB
  let : IsFiniteMeasure (volume.restrict (B ×ˢ J)) := by
    apply isFiniteMeasure_restrict.mpr
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact (ENNReal.mul_lt_top Integration.volume_vec3Ball_lt_top
      (by simp only [J, Real.volume_Ioo, ENNReal.ofReal_lt_top])).ne
  have hDpmem : MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict (B ×ˢ J)) := by
    rw [memLp_pi_iff]
    intro i
    have ht : MemLp (∑ j : Fin 3, T j i) (ENNReal.ofReal (5 / 4 : ℝ))
        (volume.restrict (B ×ˢ J)) := memLp_finsetSum' Finset.univ (fun j _ ↦
      (hTmem j i).mono_measure Measure.restrict_le_self)
    have hf : MemLp (∑ j : Fin 3, Tforce j i) (ENNReal.ofReal (5 / 4 : ℝ))
        (volume.restrict (B ×ˢ J)) := memLp_finsetSum' Finset.univ (fun j _ ↦
      (hFmem j i).mono_measure Measure.restrict_le_self)
    have hh := (hHmem i).mono_exponent (by norm_num :
      ENNReal.ofReal (5 / 4 : ℝ) ≤ ENNReal.ofReal (3 / 2 : ℝ))
    apply ((ht.neg.add hh).add hf).ae_eq
    exact Eventually.of_forall fun w ↦ by
      simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply]
      exact (hdecomp i w).symm
  exact ⟨Dp, hDp, hDpmem, hweak⟩

/-- The same actual pressure gradient is integrable at the box exponent on
the usual backward cylinder, and differentiates the supplied pressure there. -/
theorem exists_suitable_pressure_gradient_memLp_fiveFourths_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) {r : ℝ} (hr : 0 < r)
    (hdom : Metric.ball z₀ (4 * r) ⊆ spaceTimeSet Ω I) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ))
        (volume.restrict (parabolicCylinder z₀.1 z₀.2 r)) ∧
      ∀ᵐ s ∂volume.restrict (Ioc (z₀.2 - r ^ 2) z₀.2), ∀ i : Fin 3,
        LocallyIntegrableOn (fun y ↦ Dp (y, s) i) (vec3Ball z₀.1 r) volume ∧
        HasWeakPartialDerivOn (vec3Ball z₀.1 r) i
          (fun y ↦ p (y, s)) (fun y ↦ Dp (y, s) i) := by
  have hR : 0 < 2 * r := by positivity
  have hdom' : Metric.ball z₀ (2 * (2 * r)) ⊆ spaceTimeSet Ω I := by
    rw [show 2 * (2 * r) = 4 * r by ring]
    exact hdom
  obtain ⟨Dp, hDp, hmem, hweak⟩ :=
    exists_suitable_pressure_gradient_memLp_fiveFourths hsol z₀ hR hdom'
  have hhalf : 2 * r / 2 = r := by ring
  have hquarter : (2 * r) ^ 2 / 4 = r ^ 2 := by ring
  rw [hhalf, hquarter] at hmem hweak
  have htime : Ioc (z₀.2 - r ^ 2) z₀.2 ⊆
      Ioo (z₀.2 - r ^ 2) (z₀.2 + r ^ 2) := by
    intro s hs
    exact ⟨hs.1, by nlinarith only [hs.2, sq_pos_of_pos hr]⟩
  exact ⟨Dp, hDp,
    hmem.mono_measure (Measure.restrict_mono_set volume (prod_mono le_rfl htime)),
    ae_restrict_of_ae_restrict_of_subset htime hweak⟩

end FluidSingularSets
