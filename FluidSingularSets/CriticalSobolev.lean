-- Copyright (c) 2026 Scott Armstrong, Vlad Vicol, and FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import CKN.Foundation.Sobolev.Inequalities.H1

/-!
# The critical mixed-gradient Sobolev estimate

The cutoff argument of CKN `Inequalities/Smooth.lean` is adapted to the critical
exponent `12/7`, whose Sobolev conjugate in dimension three is `4`. The weak
representative proof adapts CKN `Inequalities/H1.lean`, using general-exponent
mollifier convergence and Fatou.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Convolution

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

open CKN

private theorem norm_le_vecEuclideanNorm {d : ℕ} (x : Vec d) :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖x i‖₊) ≤
      ⟨vecEuclideanNorm x, vecEuclideanNorm_nonneg x⟩ := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast abs_apply_le_vecEuclideanNorm x i
  exact_mod_cast hnn

private theorem classicalGradient_mul
    {f g : Vec 3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    classicalGradient (fun x => f x * g x) =
      fun x => f x • classicalGradient g x + g x • classicalGradient f x := by
  funext x i
  rw [classicalGradient_apply]
  have h := congrArg (fun L : Vec 3 →L[ℝ] ℝ => L (basisVec i))
    (fderiv_mul (hf x) (hg x))
  have hfun : (fun y => f y * g y) = f * g := by
    funext y
    rfl
  rw [hfun]
  simpa [Pi.mul_apply, smul_eq_mul, classicalGradient_apply, add_comm] using h

private theorem fderiv_norm_le_three_classicalGradient
    {f : Vec 3 → ℝ} (x : Vec 3) :
    ‖fderiv ℝ f x‖ ≤ 3 * ‖classicalGradient f x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  calc
    ‖(fderiv ℝ f x) z‖ =
        ‖∑ i : Fin 3, z i • (fderiv ℝ f x) (basisVec i)‖ := by
          have hz : z = ∑ i : Fin 3, z i • basisVec i :=
            (sum_smul_basisVec z).symm
          rw [hz, map_sum]
          simp [Pi.smul_apply, smul_eq_mul]
    _ ≤ ∑ i : Fin 3, ‖z i • (fderiv ℝ f x) (basisVec i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖z‖ * ‖classicalGradient f x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      have hz : |z i| ≤ ‖z‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
      have hg : |(fderiv ℝ f x) (basisVec i)| ≤ ‖classicalGradient f x‖ := by
        simpa only [classicalGradient_apply, Real.norm_eq_abs] using
          norm_le_pi_norm (classicalGradient f x) i
      exact mul_le_mul hz hg (abs_nonneg _) (norm_nonneg _)
    _ = 3 * ‖classicalGradient f x‖ * ‖z‖ := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

private theorem canonicalBallCutoff_gradient_norm_bound
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) (x : Vec 3) :
    ‖classicalGradient (canonicalBallCutoff x₀ r (2 * r)) x‖ ≤ 32 / r := by
  calc
    ‖classicalGradient (canonicalBallCutoff x₀ r (2 * r)) x‖ ≤
        vecEuclideanNorm (classicalGradient
          (canonicalBallCutoff x₀ r (2 * r)) x) :=
      norm_le_vecEuclideanNorm _
    _ ≤ 32 / ((2 * r) - r) := canonicalBallCutoff_gradient_bound (le_of_lt hr)
      (by linarith only [hr]) x
    _ = 32 / r := by ring_nf

/-- Fixed constant for the critical mixed-gradient Sobolev exponent in dimension three. -/
noncomputable def criticalSobolevConstant : ℝ≥0∞ :=
  ((3 : NNReal) : ℝ≥0∞) *
    (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
      (12 / 7 : ℝ) : ℝ≥0∞)

private theorem smooth_cutoff_gradient_bound
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) (u : Vec 3 → ℝ)
    (hu : ContDiff ℝ 1 u) :
    eLpNorm (fun x =>
        canonicalBallCutoff x₀ r (2 * r) x • classicalGradient u x) (12 / 7) volume ≤
      eLpNorm ((euclideanBall x₀ (2 * r)).indicator (classicalGradient u)) (12 / 7) volume := by
  let η : Vec 3 → ℝ := canonicalBallCutoff x₀ r (2 * r)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    canonicalBallCutoff_smooth x₀ (le_of_lt hr) (by linarith only [hr])
  have houter : MeasurableSet (euclideanBall x₀ (2 * r)) := by
    change MeasurableSet {x | euclideanSqDist x x₀ < (2 * r) ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const).measurableSet
  have hgrad : AEStronglyMeasurable (classicalGradient u) volume := by
    have hcont : Continuous (classicalGradient u) := by
      apply continuous_pi
      intro i
      simpa only [classicalGradient_apply] using
        (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hcont.aestronglyMeasurable
  apply eLpNorm_mono_ae
    (f := fun x => η x • classicalGradient u x)
    (g := (euclideanBall x₀ (2 * r)).indicator (classicalGradient u))
    (hη.continuous.aestronglyMeasurable.smul hgrad)
  filter_upwards [] with x
  by_cases hx : x ∈ euclideanBall x₀ (2 * r)
  · rw [indicator_of_mem hx]
    rw [norm_smul]
    have hη0 : 0 ≤ η x := canonicalBallCutoff_nonneg x₀ r (2 * r) x
    have hη1 : η x ≤ 1 := canonicalBallCutoff_le_one x₀ r (2 * r) x
    simpa [abs_of_nonneg hη0] using
      (mul_le_mul_of_nonneg_right hη1 (norm_nonneg (classicalGradient u x)))
  · simp only [Set.indicator, hx, ite_false]
    have hxt : x ∉ tsupport η := by
      intro hxt
      exact hx (canonicalBallCutoff_tsupport_subset_outer (le_of_lt hr)
        (by linarith only [hr]) hxt)
    rw [show η x = 0 by exact image_eq_zero_of_notMem_tsupport hxt]
    simp

private theorem smooth_cutoff_u_gradient_bound
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) (u : Vec 3 → ℝ)
    (hu : ContDiff ℝ 1 u) :
    eLpNorm (fun x => u x •
        classicalGradient (canonicalBallCutoff x₀ r (2 * r)) x) (12 / 7) volume ≤
      Real.toNNReal (32 / r) •
        eLpNorm ((euclideanBall x₀ (2 * r)).indicator u) (12 / 7) volume := by
  let η : Vec 3 → ℝ := canonicalBallCutoff x₀ r (2 * r)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    canonicalBallCutoff_smooth x₀ (le_of_lt hr) (by linarith only [hr])
  have hgradη : AEStronglyMeasurable (classicalGradient η) volume := by
    have hcont : Continuous (classicalGradient η) := by
      apply continuous_pi
      intro i
      simpa only [classicalGradient_apply] using
        (hη.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hcont.aestronglyMeasurable
  have huMeas : AEStronglyMeasurable u volume :=
    hu.continuous.aestronglyMeasurable
  refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (f := fun x => u x • classicalGradient η x)
    (g := (euclideanBall x₀ (2 * r)).indicator u)
    (huMeas.smul hgradη) ?_ (12 / 7)
  filter_upwards [] with x
  by_cases hx : x ∈ euclideanBall x₀ (2 * r)
  · rw [indicator_of_mem hx]
    have hgrad := canonicalBallCutoff_gradient_norm_bound (x₀ := x₀) hr x
    have hpoint : ‖u x • classicalGradient η x‖ ≤
        (32 / r) * ‖u x‖ := by
      rw [norm_smul]
      simpa [η, mul_comm] using
        (mul_le_mul_of_nonneg_left hgrad (norm_nonneg (u x)))
    have hscale : (Real.toNNReal (32 / r) : ℝ) = 32 / r := by
      exact Real.coe_toNNReal (32 / r) (by positivity)
    rw [← NNReal.coe_le_coe]
    simpa [hscale] using hpoint
  · simp only [Set.indicator, hx, ite_false]
    have hxt : x ∉ tsupport η := by
      intro hxt
      exact hx (canonicalBallCutoff_tsupport_subset_outer (le_of_lt hr)
        (by linarith only [hr]) hxt)
    have hzero : classicalGradient η x = 0 := by
      funext i
      rw [classicalGradient_apply, fderiv_of_notMem_tsupport ℝ hxt]
      simp
    simp [hzero]

/-- A localized critical Sobolev estimate for smooth functions. The cutoff is supported
inside the larger ball; the lower-order term can then be removed by Poincaré. -/
theorem smoothCriticalSobolevBall
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) {u : Vec 3 → ℝ}
    (hu : ContDiff ℝ 1 u) :
    lpNormOn 4 (euclideanBall x₀ r) u ≤
      criticalSobolevConstant *
        (gradientLpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) u +
          (Real.toNNReal (32 / r) : ℝ≥0∞) *
            lpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) u) := by
  let η : Vec 3 → ℝ := canonicalBallCutoff x₀ r (2 * r)
  let v : Vec 3 → ℝ := fun x => η x * u x
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    canonicalBallCutoff_smooth x₀ (le_of_lt hr) (by linarith only [hr])
  have hηC : HasCompactSupport η :=
    canonicalBallCutoff_hasCompactSupport (le_of_lt hr) (by linarith only [hr])
  have hv : ContDiff ℝ 1 v := by
    exact (hη.of_le (by norm_num)).mul hu
  have hvC : HasCompactSupport v := hηC.mul_right (f' := u)
  have hglobal :
      eLpNorm v 4 volume ≤
          (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
            (12 / 7 : ℝ) : ℝ≥0∞) *
          eLpNorm (fderiv ℝ v) (12 / 7) volume := by
    simpa using
      (MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
        (volume : Measure (Vec 3)) hv hvC
          (by exact_mod_cast (by norm_num : (1 : ℝ) ≤ 12 / 7) :
            (1 : NNReal) ≤ 12 / 7)
          (by norm_num : 0 < Module.finrank ℝ (Vec 3))
          (by norm_num : ((4 : NNReal) : ℝ)⁻¹ =
            ((12 / 7 : NNReal) : ℝ)⁻¹ - ((Module.finrank ℝ (Vec 3) : ℝ)⁻¹)))
  have hderiv :
      eLpNorm (fderiv ℝ v) (12 / 7) volume ≤
        (3 : NNReal) • eLpNorm (classicalGradient v) (12 / 7) volume := by
    refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (f := fderiv ℝ v) (g := classicalGradient v)
      (hv.continuous_fderiv (by norm_num)).aestronglyMeasurable ?_ (12 / 7)
    exact Filter.Eventually.of_forall (fun x => by
      exact_mod_cast fderiv_norm_le_three_classicalGradient (f := v) x)
  have hgrad :
      eLpNorm (classicalGradient v) (12 / 7) volume ≤
        eLpNorm ((euclideanBall x₀ (2 * r)).indicator (classicalGradient u)) (12 / 7) volume +
          Real.toNNReal (32 / r) •
            eLpNorm ((euclideanBall x₀ (2 * r)).indicator u) (12 / 7) volume := by
    rw [show classicalGradient v =
      (fun x => η x • classicalGradient u x + u x • classicalGradient η x) by
        simpa [v, η] using classicalGradient_mul (f := η) (g := u)
          (hη.differentiable (by norm_num)) (hu.differentiable (by norm_num))
          ]
    calc
      eLpNorm (fun x => η x • classicalGradient u x +
          u x • classicalGradient η x) (12 / 7) volume ≤
          eLpNorm (fun x => η x • classicalGradient u x) (12 / 7) volume +
            eLpNorm (fun x => u x • classicalGradient η x) (12 / 7) volume :=
        eLpNorm_add_le (by
          rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
          norm_num)
      _ ≤ eLpNorm ((euclideanBall x₀ (2 * r)).indicator (classicalGradient u)) (12 / 7) volume +
          Real.toNNReal (32 / r) •
            eLpNorm ((euclideanBall x₀ (2 * r)).indicator u) (12 / 7) volume := by
        exact add_le_add (smooth_cutoff_gradient_bound hr u hu)
          (smooth_cutoff_u_gradient_bound hr u hu)
  have houter : MeasurableSet (euclideanBall x₀ (2 * r)) := by
    change MeasurableSet {x | euclideanSqDist x x₀ < (2 * r) ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const).measurableSet
  have hin : MeasurableSet (euclideanBall x₀ r) := by
    change MeasurableSet {x | euclideanSqDist x x₀ < r ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const).measurableSet
  have hvInner :
      eLpNorm u 4 (volume.restrict (euclideanBall x₀ r)) ≤ eLpNorm v 4 volume := by
    calc
      eLpNorm u 4 (volume.restrict (euclideanBall x₀ r)) =
          eLpNorm v 4 (volume.restrict (euclideanBall x₀ r)) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem hin] with x hx
        simp [v, η, canonicalBallCutoff_eq_one_on_inner
          (x₀ := x₀) (r := r) (R := 2 * r) (x := x)
          (le_of_lt hr) (by linarith only [hr]) hx]
      _ ≤ eLpNorm v 4 volume := eLpNorm_mono_measure v Measure.restrict_le_self
  calc
    lpNormOn 4 (euclideanBall x₀ r) u ≤ eLpNorm v 4 volume := hvInner
    _ ≤ (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
          (12 / 7 : ℝ) : ℝ≥0∞) *
          eLpNorm (fderiv ℝ v) (12 / 7) volume := hglobal
    _ ≤ (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
          (12 / 7 : ℝ) : ℝ≥0∞) *
          (((3 : NNReal) : ℝ≥0∞) * eLpNorm (classicalGradient v) (12 / 7) volume) := by
      gcongr
      simpa [ENNReal.smul_def, smul_eq_mul] using hderiv
    _ ≤ criticalSobolevConstant *
          (gradientLpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) u +
            (Real.toNNReal (32 / r) : ℝ≥0∞) *
              lpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) u) := by
      rw [criticalSobolevConstant]
      rw [eLpNorm_indicator_eq_eLpNorm_restrict houter] at hgrad
      rw [eLpNorm_indicator_eq_eLpNorm_restrict houter] at hgrad
      simpa [gradientLpNormOn, lpNormOn, ENNReal.smul_def, smul_eq_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hgrad
          (show 0 ≤ ((3 : NNReal) : ℝ≥0∞) *
            (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
              (12 / 7 : ℝ) : ℝ≥0∞) by positivity))


private theorem criticalExponent_one_le : (1 : ℝ≥0∞) ≤ 12 / 7 := by
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num

private theorem memLp_mul_cutoff_le
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {p : ENNReal} {f : Vec d → ℝ} (hf : MemLp f p (volume.restrict U))
    {η : Vec d → ℝ} (hηMeas : Measurable η) (hηU : tsupport η ⊆ U)
    {c : ℝ} (hη : ∀ x, ‖η x‖ ≤ c) :
    MemLp (fun x => η x * f x) p volume := by
  have hmeas : AEStronglyMeasurable (fun x => η x * f x) (volume.restrict U) := by
    exact (hηMeas.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  have hmul : MemLp (fun x => η x * f x) p (volume.restrict U) := by
    apply MemLp.of_le_mul hf hmeas
    filter_upwards [] with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hη x) (norm_nonneg (f x))
  have hglob : MemLp (U.indicator (fun x => η x * f x)) p volume :=
    (memLp_indicator_iff_restrict hU).2 hmul
  have heq : U.indicator (fun x => η x * f x) = (fun x => η x * f x) := by
    funext x
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx]
    · have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport (fun hxt => hx (hηU hxt))
      simp [hη0]
  rw [heq] at hglob
  exact hglob
private theorem fderiv_component_tsupport_subset
    {d : ℕ} {η : Vec d → ℝ} (i : Fin d) :
    tsupport (fun x => (fderiv ℝ η x) (basisVec i)) ⊆ tsupport η := by
  apply closure_minimal
  · intro x hx
    by_contra hxt
    have hηzero : η =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := η)).isOpen_compl.eventually_mem hxt |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    have hderivzero := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hηzero
    have hzero : (fderiv ℝ η x) (basisVec i) = 0 := by
      rw [hderivzero]
      simp
    exact hx hzero
  · exact isClosed_tsupport (f := η)
private theorem eLpNorm_pi_le_sum
    {f : Vec 3 → Vec 3} {μ : Measure (Vec 3)}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (12 / 7) μ ≤ ∑ i : Fin 3, eLpNorm (fun x => f x i) (12 / 7) μ := by
  have hpoint : ∀ x, ‖f x‖ ≤ ∑ i : Fin 3, ‖f x i‖ := by
    intro x
    rw [Pi.norm_def]
    have hsup : Finset.univ.sup (fun i => ‖f x i‖₊) ≤
        ∑ i : Fin 3, ‖f x i‖₊ := by
      apply Finset.sup_le
      intro i hi
      have hnonneg : ∀ j : Fin 3, j ∈ Finset.univ → 0 ≤ ‖f x j‖₊ := by
        intro j hj
        exact bot_le
      simpa only [Finset.sum_filter, Finset.mem_univ, ite_true] using
        (Finset.single_le_sum hnonneg (Finset.mem_univ i))
    exact_mod_cast hsup
  calc
    eLpNorm f (12 / 7) μ ≤ eLpNorm (fun x => ∑ i : Fin 3, ‖f x i‖) (12 / 7) μ := by
      apply eLpNorm_mono_ae hf
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
        (fun i _ => norm_nonneg (f x i)))]
      exact hpoint x
    _ = eLpNorm (∑ i : Fin 3, (fun x => ‖f x i‖)) (12 / 7) μ := by rfl
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => ‖f x i‖) (12 / 7) μ := by
      simpa using (eLpNorm_sum_le (p := (12 / 7 : ENNReal)) (s := Finset.univ)
        (f := fun i : Fin 3 => (fun x => ‖f x i‖)) criticalExponent_one_le)
    _ = ∑ i : Fin 3, eLpNorm (fun x => f x i) (12 / 7) μ := by
      congr 1
      funext i
      have hfi : AEStronglyMeasurable (fun x => f x i) μ := by
        simpa only [ContinuousLinearMap.proj_apply] using
          (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hf
      rw [eLpNorm_norm _ hfi]
private theorem tendsto_sum_zero_of_fin_three
    {f : Fin 3 → ℕ → ℝ≥0∞}
    (hf : ∀ i, Tendsto (f i) atTop (nhds 0)) :
    Tendsto (fun n => ∑ i : Fin 3, f i n) atTop (nhds 0) := by
  simpa using tendsto_finsetSum Finset.univ (fun i hi => hf i)

/-- Local critical Sobolev control for a representative with a weak gradient. -/
theorem weakCriticalSobolevBall
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    {u : Vec 3 → ℝ} {Du : Vec 3 → Vec 3}
    (hu : MemLp u (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))))
    (hDu : MemLp Du (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))))
    (hweakInput : HasWeakGradientOn (euclideanBall x₀ (2 * r)) u Du) :
    lpNormOn 4 (euclideanBall x₀ r) u ≤
      criticalSobolevConstant *
        (weakGradientLpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) Du +
          (Real.toNNReal (32 / r) : ℝ≥0∞) *
            lpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) u) := by
  have hDu_i (i : Fin 3) : MemLp (fun x ↦ Du x i) (12 / 7)
      (volume.restrict (euclideanBall x₀ (2 * r))) := (memLp_pi_iff).1 hDu i
  let U : Set (Vec 3) := euclideanBall x₀ (2 * r)
  let inner : Set (Vec 3) := euclideanBall x₀ r
  let η : Vec 3 → ℝ := canonicalBallCutoff x₀ r (2 * r)
  let v : Vec 3 → ℝ := fun x => η x * u x
  let G : Vec 3 → Vec 3 := fun x => η x • Du x +
    u x • classicalGradient η x
  have hUopen : IsOpen U := by
    change IsOpen {x | euclideanSqDist x x₀ < (2 * r) ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hinnerMeas : MeasurableSet inner := by
    change MeasurableSet {x | euclideanSqDist x x₀ < r ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const).measurableSet
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := by
    exact canonicalBallCutoff_smooth x₀ (le_of_lt hr) (by linarith only [hr])
  have hηMeas : Measurable η := hη.continuous.measurable
  have hηSupport : HasCompactSupport η := by
    exact canonicalBallCutoff_hasCompactSupport (le_of_lt hr) (by linarith only [hr])
  have hηU : tsupport η ⊆ U := by
    exact canonicalBallCutoff_tsupport_subset_outer (le_of_lt hr) (by linarith only [hr])
  have hηBound : ∀ x, ‖η x‖ ≤ (1 : ℝ) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (canonicalBallCutoff_nonneg x₀ r (2 * r) x)]
    exact canonicalBallCutoff_le_one x₀ r (2 * r) x
  have hgradη : ∀ x, ‖classicalGradient η x‖ ≤ 32 / r := by
    intro x
    calc
      ‖classicalGradient η x‖ ≤
          vecEuclideanNorm (classicalGradient η x) := pi_norm_le_vecEuclideanNorm _
      _ ≤ 32 / ((2 * r) - r) := canonicalBallCutoff_gradient_bound
        (le_of_lt hr) (by linarith only [hr]) x
      _ = 32 / r := by ring_nf
  have hgradηMeas (i : Fin 3) :
      Measurable (fun x => (classicalGradient η x) i) := by
    simpa only [classicalGradient_apply] using
      (hη.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.measurable
  have hgradηSupport (i : Fin 3) :
      tsupport (fun x => (classicalGradient η x) i) ⊆ U := by
    exact (fderiv_component_tsupport_subset i).trans hηU
  have hgradηBound (i : Fin 3) :
      ∀ x, ‖(classicalGradient η x) i‖ ≤ 32 / r := by
    intro x
    exact (norm_le_pi_norm (classicalGradient η x) i).trans (hgradη x)
  have huLoc : LocallyIntegrableOn u U volume := by
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      (hu.locallyIntegrable criticalExponent_one_le)
  have hgradLoc (i : Fin 3) :
      LocallyIntegrableOn (fun x => Du x i) U volume := by
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hDu_i i).locallyIntegrable criticalExponent_one_le)
  have hweak : HasWeakGradientOn Set.univ v G := by
    exact HasWeakGradientOn.mul_smooth_zeroExtend hUopen huLoc hgradLoc hweakInput
      hη hηSupport hηU
  have hvSupport : HasCompactSupport v := by
    exact hηSupport.mul_right (f' := u)
  have hv : MemLp v (12 / 7) volume := by
    exact memLp_mul_cutoff_le hUmeas hu hηMeas hηU hηBound
  have hG_i (i : Fin 3) : MemLp (fun x => G x i) (12 / 7) volume := by
    have hηg : MemLp (fun x => η x * Du x i) (12 / 7) volume :=
      memLp_mul_cutoff_le hUmeas (hDu_i i) hηMeas hηU hηBound
    have hηd : MemLp (fun x => (classicalGradient η x) i * u x) (12 / 7) volume :=
      memLp_mul_cutoff_le hUmeas hu (hgradηMeas i) (hgradηSupport i) (hgradηBound i)
    convert hηg.add hηd using 1
    · ext x
      simp [G, Pi.smul_apply, smul_eq_mul, classicalGradient_apply,
        mul_comm, Pi.add_apply]
  have hG : MemLp G (12 / 7) volume := (memLp_pi_iff).2 hG_i
  have hgOuter : MemLp Du (12 / 7) (volume.restrict U) := by
    apply (memLp_pi_iff).2
    intro i
    exact memLpOn_mono subset_rfl (hDu_i i)
  have huOuter : MemLp u (12 / 7) (volume.restrict U) := hu
  have hGbound :
      eLpNorm G (12 / 7) volume ≤
        weakGradientLpNormOn (12 / 7) U Du +
          (Real.toNNReal (32 / r) : ℝ≥0∞) * lpNormOn (12 / 7) U u := by
    let A : Vec 3 → Vec 3 := fun x => η x • Du x
    let B : Vec 3 → Vec 3 := fun x => u x • classicalGradient η x
    have hA_i (i : Fin 3) : MemLp (fun x => A x i) (12 / 7) volume := by
      simpa [A, Pi.smul_apply, smul_eq_mul] using
        (memLp_mul_cutoff_le hUmeas (hDu_i i) hηMeas hηU hηBound)
    have hB_i (i : Fin 3) : MemLp (fun x => B x i) (12 / 7) volume := by
      simpa [B, Pi.smul_apply, smul_eq_mul, mul_comm] using
        (memLp_mul_cutoff_le hUmeas hu (hgradηMeas i) (hgradηSupport i)
          (hgradηBound i))
    have hA : MemLp A (12 / 7) volume := (memLp_pi_iff).2 hA_i
    have hB : MemLp B (12 / 7) volume := (memLp_pi_iff).2 hB_i
    have hA_bound : eLpNorm A (12 / 7) volume ≤ eLpNorm (U.indicator Du) (12 / 7) volume := by
      apply eLpNorm_mono_ae hA.aestronglyMeasurable
      filter_upwards [] with x
      by_cases hx : x ∈ U
      · simp only [Set.indicator_of_mem hx]
        rw [norm_smul]
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right (hηBound x) (norm_nonneg (Du x)))
      · have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport (fun hxt => hx (hηU hxt))
        simp [A, hη0]
    have hB_bound : eLpNorm B (12 / 7) volume ≤
        (Real.toNNReal (32 / r) : ℝ≥0∞) • eLpNorm (U.indicator u) (12 / 7) volume := by
      refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' hB.aestronglyMeasurable ?_ (12 / 7)
      filter_upwards [] with x
      by_cases hx : x ∈ U
      · simp only [Set.indicator_of_mem hx]
        simp only [enorm_eq_nnnorm]
        rw [← ENNReal.coe_mul]
        have hpoint : ‖B x‖₊ ≤
          Real.toNNReal (32 / r) * ‖u x‖₊ := by
          rw [nnnorm_smul]
          have hgradη' : ‖classicalGradient η x‖₊ ≤ Real.toNNReal (32 / r) := by
            rw [← NNReal.coe_le_coe]
            have hscale : (Real.toNNReal (32 / r) : ℝ) = 32 / r := by
              exact Real.coe_toNNReal (32 / r) (by positivity)
            simpa [hscale] using hgradη x
          calc
            ‖u x‖₊ * ‖classicalGradient η x‖₊ ≤
                ‖u x‖₊ * Real.toNNReal (32 / r) :=
              mul_le_mul_of_nonneg_left hgradη' bot_le
            _ = Real.toNNReal (32 / r) * ‖u x‖₊ := by ac_rfl
        exact_mod_cast hpoint
      · have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport (fun hxt => hx (hηU hxt))
        have hgradη0 : classicalGradient η x = 0 := by
          funext i
          rw [classicalGradient_apply, fderiv_of_notMem_tsupport ℝ
            (fun hxt => hx (hηU hxt))]
          simp
        simp [B, hgradη0, hx]
    have houterIndicatorG : eLpNorm (U.indicator Du) (12 / 7) volume =
        weakGradientLpNormOn (12 / 7) U Du := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hUmeas]
      rfl
    have houterIndicatorU : eLpNorm (U.indicator u) (12 / 7) volume = lpNormOn (12 / 7) U u := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hUmeas]
      rfl
    rw [show G = A + B by rfl]
    calc
      eLpNorm (A + B) (12 / 7) volume ≤ eLpNorm A (12 / 7) volume + eLpNorm B (12 / 7) volume :=
        eLpNorm_add_le criticalExponent_one_le
      _ ≤ eLpNorm (U.indicator Du) (12 / 7) volume +
          (Real.toNNReal (32 / r) : ℝ≥0∞) • eLpNorm (U.indicator u) (12 / 7) volume :=
        add_le_add hA_bound hB_bound
      _ = weakGradientLpNormOn (12 / 7) U Du +
          (Real.toNNReal (32 / r) : ℝ≥0∞) * lpNormOn (12 / 7) U u := by
        rw [houterIndicatorG, houterIndicatorU]
        simp [smul_eq_mul]
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hε : Tendsto ε atTop (nhds 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hvApprox := tendsto_eLpNorm_sub_zero_mollify (p := (12 / 7 : ENNReal))
    criticalExponent_one_le (by finiteness) hv hε hεpos
  have hGApprox (i : Fin 3) := tendsto_eLpNorm_sub_zero_mollify (p := (12 / 7 : ENNReal))
    criticalExponent_one_le (by finiteness) (hG_i i) hε hεpos
  have hderiv (n : ℕ) (i : Fin 3) (x : Vec 3) :
      (fderiv ℝ (mollify v (ε n) (hεpos n)) x) (basisVec i) =
        mollify (fun y => G y i) (ε n) (hεpos n) x := by
    exact fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ
      (hv.locallyIntegrable criticalExponent_one_le)
      ((hG_i i).locallyIntegrable criticalExponent_one_le)
      (hweak i) (hεpos n) (by simp)
  let D : ℕ → Vec 3 → Vec 3 := fun n x => classicalGradient
    (mollify v (ε n) (hεpos n)) x
  have hD_i (n : ℕ) (i : Fin 3) :
      (fun x => D n x i) = mollify (fun y => G y i) (ε n) (hεpos n) := by
    funext x
    exact hderiv n i x
  have hDmem (n : ℕ) (i : Fin 3) : MemLp (fun x => D n x i) (12 / 7) volume := by
    rw [hD_i]
    have hconv := young_convolution_nonneg_integral_one_of_aemeasurable
      (p := (12 / 7 : ENNReal)) criticalExponent_one_le (by finiteness)
      (mollifier_nonneg (hεpos n))
      ((mollifier_contDiff (hεpos n) (n := 0)).continuous.integrable_of_hasCompactSupport
        (mollifier_hasCompactSupport (hεpos n)))
      (mollifier_integral_one (hεpos n))
      (mollifier_contDiff (hεpos n) (n := 0)).continuous.measurable
      (hG_i i).aestronglyMeasurable.aemeasurable
    rw [memLp_iff]
    simpa only [mollify] using hconv.trans_lt (hG_i i)
  have hDmemVec (n : ℕ) : MemLp (D n) (12 / 7) volume := (memLp_pi_iff).2 (hDmem n)
  have hDerr : Tendsto (fun n => eLpNorm (D n - G) (12 / 7) volume) atTop (nhds 0) := by
    have hle : ∀ n, eLpNorm (D n - G) (12 / 7) volume ≤
        ∑ i : Fin 3, eLpNorm (fun x => mollify (fun y => G y i)
          (ε n) (hεpos n) x - G x i) (12 / 7) volume := by
      intro n
      have hmeas : AEStronglyMeasurable (D n - G) volume :=
        (hDmemVec n).sub hG |>.aestronglyMeasurable
      calc
        eLpNorm (D n - G) (12 / 7) volume ≤
            ∑ i : Fin 3, eLpNorm (fun x => (D n - G) x i) (12 / 7) volume :=
          eLpNorm_pi_le_sum hmeas
        _ = _ := by
          congr 1
          funext i
          apply eLpNorm_congr_ae
          filter_upwards [] with x
          simp only [Pi.sub_apply]
          rw [show D n x i = mollify (fun y => G y i) (ε n) (hεpos n) x by
            exact congrFun (hD_i n i) x]
    have hsum : Tendsto (fun n => ∑ i : Fin 3, eLpNorm (fun x => mollify
        (fun y => G y i) (ε n) (hεpos n) x - G x i) (12 / 7) volume) atTop (nhds 0) := by
      apply tendsto_sum_zero_of_fin_three
      intro i
      exact hGApprox i
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall hle)
  obtain ⟨ns, hns_mono, hns_ae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (μ := (volume : Measure (Vec 3)))
      (p := (12 / 7 : ENNReal)) (by norm_num) hvApprox).exists_seq_tendsto_ae
  have hinner_v : eLpNorm v 4 (volume.restrict inner) =
      lpNormOn 4 inner u := by
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hinnerMeas] with x hx
    simp only [v, η]
    rw [canonicalBallCutoff_eq_one_on_inner (x₀ := x₀) (r := r) (R := 2 * r)
      (le_of_lt hr) (by linarith only [hr]) hx]
    simp
  have hliminf : lpNormOn 4 inner u ≤
      atTop.liminf (fun k => eLpNorm (mollify v (ε (ns k)) (hεpos (ns k)))
        4 (volume.restrict inner)) := by
    rw [← hinner_v]
    apply MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm
    · intro k
      exact (mollify_contDiff (hεpos (ns k))
        (hv.locallyIntegrable criticalExponent_one_le)
        (n := 0)).continuous.aestronglyMeasurable.restrict
    · exact hv.aestronglyMeasurable.restrict
    · rw [ae_restrict_iff' hinnerMeas]
      filter_upwards [hns_ae] with x hx hxin
      exact hx
  let A : ℝ≥0∞ := weakGradientLpNormOn (12 / 7) U Du +
    (Real.toNNReal (32 / r) : ℝ≥0∞) * lpNormOn (12 / 7) U u
  have hvBound : eLpNorm v (12 / 7) volume ≤ lpNormOn (12 / 7) U u := by
    calc
      eLpNorm v (12 / 7) volume ≤ eLpNorm (U.indicator u) (12 / 7) volume := by
        apply eLpNorm_mono_ae hv.aestronglyMeasurable
        filter_upwards [] with x
        by_cases hx : x ∈ U
        · simp only [Set.indicator_of_mem hx]
          rw [norm_mul]
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right (hηBound x) (norm_nonneg (u x)))
        · have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport
            (fun hxt => hx (hηU hxt))
          simp [v, hη0]
      _ = lpNormOn (12 / 7) U u := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hUmeas]
        rfl
  have hDnBound (n : ℕ) :
      eLpNorm (D n) (12 / 7) volume ≤ A + eLpNorm (D n - G) (12 / 7) volume := by
    calc
      eLpNorm (D n) (12 / 7) volume = eLpNorm ((D n - G) + G) (12 / 7) volume := by
        congr 1
        funext x
        simp only [Pi.sub_apply, Pi.add_apply]
        abel
      _ ≤ eLpNorm (D n - G) (12 / 7) volume + eLpNorm G (12 / 7) volume := by
        exact eLpNorm_add_le (p := (12 / 7 : ENNReal)) criticalExponent_one_le
      _ ≤ eLpNorm (D n - G) (12 / 7) volume + A := by
        have hGbound' : eLpNorm G (12 / 7) volume ≤ A := by
          simpa [A] using hGbound
        exact add_le_add_right hGbound' _
      _ = A + eLpNorm (D n - G) (12 / 7) volume := by ac_rfl
  have hboundEventually : ∀ δ : ℝ≥0∞, δ ≠ ∞ → 0 < δ →
      ∀ᶠ k in atTop, eLpNorm (mollify v (ε (ns k)) (hεpos (ns k))) 4
        (volume.restrict inner) ≤ criticalSobolevConstant * (A + δ) := by
    intro δ hδtop hδpos
    have hgradSmall : ∀ᶠ k in atTop, eLpNorm (D (ns k) - G) (12 / 7) volume ≤ δ :=
      (ENNReal.tendsto_nhds_zero.1 (hDerr.comp (hns_mono.tendsto_atTop)) δ hδpos)
    filter_upwards [hgradSmall] with k hgrad
    let m : Vec 3 → ℝ := mollify v (ε (ns k)) (hεpos (ns k))
    have hm : ContDiff ℝ 1 m := by
      exact mollify_contDiff (hεpos (ns k))
        (hv.locallyIntegrable criticalExponent_one_le) (n := 1)
    have hmSupport : HasCompactSupport m := by
      change HasCompactSupport
        (mollifier (ε (ns k)) (hεpos (ns k)) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, volume] v)
      exact (mollifier_hasCompactSupport (hεpos (ns k))).convolution
        (ContinuousLinearMap.lsmul ℝ ℝ) hvSupport
    have hglobal : eLpNorm m 4 volume ≤
        (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
          (12 / 7 : ℝ) : ℝ≥0∞) * eLpNorm (fderiv ℝ m) (12 / 7) volume := by
      simpa using
        (MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
          (volume : Measure (Vec 3)) hm hmSupport
          (by exact_mod_cast (by norm_num : (1 : ℝ) ≤ 12 / 7) :
            (1 : NNReal) ≤ 12 / 7)
          (by norm_num : 0 < Module.finrank ℝ (Vec 3))
          (by norm_num : ((4 : NNReal) : ℝ)⁻¹ =
            ((12 / 7 : NNReal) : ℝ)⁻¹ - ((Module.finrank ℝ (Vec 3) : ℝ)⁻¹)))
    have hderivBound : eLpNorm (fderiv ℝ m) (12 / 7) volume ≤
        (3 : NNReal) • eLpNorm (D (ns k)) (12 / 7) volume := by
      refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
        (hm.continuous_fderiv (by norm_num)).aestronglyMeasurable ?_ (12 / 7)
      exact Filter.Eventually.of_forall (fun x => by
        simp only [enorm_eq_nnnorm]
        rw [← ENNReal.coe_mul]
        have hpoint : ‖fderiv ℝ m x‖₊ ≤
            (3 : NNReal) * ‖D (ns k) x‖₊ := by
          exact_mod_cast fderiv_norm_le_three_classicalGradient x
        exact_mod_cast hpoint)
    change eLpNorm m 4 (volume.restrict inner) ≤ _
    change eLpNorm (mollify v (ε (ns k)) (hεpos (ns k))) 4
        (volume.restrict inner) ≤ _
    calc
      eLpNorm m 4 (volume.restrict inner) ≤ eLpNorm m 4 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ
          (volume : Measure (Vec 3)) (12 / 7 : ℝ) : ℝ≥0∞) *
          eLpNorm (fderiv ℝ m) (12 / 7) volume := hglobal
      _ ≤ (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ
          (volume : Measure (Vec 3)) (12 / 7 : ℝ) : ℝ≥0∞) *
          ((3 : NNReal) • eLpNorm (D (ns k)) (12 / 7) volume) := by
        gcongr
      _ = criticalSobolevConstant * eLpNorm (D (ns k)) (12 / 7) volume := by
        rw [criticalSobolevConstant]
        simp [ENNReal.smul_def, smul_eq_mul]
        ring
      _ ≤ criticalSobolevConstant * (A + δ) := by
        gcongr
        exact (hDnBound (ns k)).trans (add_le_add_right hgrad A)
  have hfinal : lpNormOn 4 inner u ≤ criticalSobolevConstant * A := by
    apply ENNReal.le_of_forall_pos_le_add
    intro δ hδ _
    have hCtop : criticalSobolevConstant ≠ ∞ := by
      unfold criticalSobolevConstant
      finiteness
    have hqtop : criticalSobolevConstant + 1 ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨hCtop, ENNReal.one_ne_top⟩
    have hδ' : δ / (criticalSobolevConstant + 1) ≠ ∞ := by
      exact ENNReal.div_ne_top (by finiteness) (by positivity)
    have hδpos : 0 < δ / (criticalSobolevConstant + 1) := by
      exact ENNReal.div_pos (by exact_mod_cast hδ.ne') (by finiteness)
    have hlim := hboundEventually (δ / (criticalSobolevConstant + 1)) hδ' hδpos
    have hle : atTop.liminf (fun k => eLpNorm (mollify v (ε (ns k))
        (hεpos (ns k))) 4 (volume.restrict inner)) ≤
        criticalSobolevConstant * (A + δ / (criticalSobolevConstant + 1)) := by
      exact liminf_le_of_frequently_le' hlim.frequently
    refine hliminf.trans (hle.trans ?_)
    calc
      criticalSobolevConstant * (A + δ / (criticalSobolevConstant + 1)) =
          criticalSobolevConstant * A +
            criticalSobolevConstant * (δ / (criticalSobolevConstant + 1)) := by
        rw [mul_add]
      _ ≤ criticalSobolevConstant * A + δ := by
        apply add_le_add_right
        calc
          criticalSobolevConstant * (δ / (criticalSobolevConstant + 1)) ≤
              (criticalSobolevConstant + 1) * (δ / (criticalSobolevConstant + 1)) := by
            exact mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right (by norm_num)) (by positivity)
          _ = δ := by
            exact ENNReal.mul_div_cancel (by positivity) (by finiteness)
  simpa [A, inner, U, weakGradientLpNormOn] using hfinal

end FluidSingularSets
