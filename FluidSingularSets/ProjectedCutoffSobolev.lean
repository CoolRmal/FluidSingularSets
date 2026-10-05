-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedCutoffConvection
public import CKN.Foundation.Sobolev.Inequalities.H1

/-!
# Actual weak Sobolev control of the cutoff corrected velocity

Multiplication by a smooth compact cutoff gives a genuine global weak gradient.
The existing weak Sobolev theorem then bounds the actual cutoff L⁶ norm by the
weighted gradient and the cutoff derivative term.
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

/-- A bounded smooth factor supported in the actual domain gives a global Lᵖ product. -/
theorem memLp_supported_scalar_product {U : Set Vec3} (hU : MeasurableSet U)
    {p : ℝ≥0∞} {u η : Vec3 → ℝ} (hu : MemLp u p (volume.restrict U))
    (hη : Measurable η) (hs : tsupport η ⊆ U) {C : ℝ}
    (hb : ∀ x, ‖η x‖ ≤ C) : MemLp (fun x ↦ η x * u x) p volume := by
  have hm : MemLp (fun x ↦ η x * u x) p (volume.restrict U) := by
    apply MemLp.of_le_mul (c := C) hu
      (hη.aestronglyMeasurable.mul hu.aestronglyMeasurable)
    filter_upwards [] with x
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
  have hi := (memLp_indicator_iff_restrict hU).2 hm
  have heq : U.indicator (fun x ↦ η x * u x) = (fun x ↦ η x * u x) := by
    funext x
    by_cases hx : x ∈ U
    · exact indicator_of_mem hx _
    · have hz : η x = 0 := image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht))
      simp only [indicator_of_notMem hx, hz, zero_mul]
  rwa [heq] at hi

/-- Each true cutoff gradient component is supported where the cutoff is supported. -/
theorem classicalGradient_component_tsupport_subset {η : Vec3 → ℝ} (i : Fin 3) :
    tsupport (fun x ↦ classicalGradient η x i) ⊆ tsupport η := by
  apply closure_minimal
  · intro x hx
    by_contra hxt
    have hz : η =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := η)).isOpen_compl.eventually_mem hxt |>.mono
        (fun _ hy ↦ image_eq_zero_of_notMem_tsupport hy)
    have hd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hz
    apply hx
    change classicalGradient η x i = 0
    rw [classicalGradient_apply, hd]
    simp
  · exact isClosed_tsupport η

/-- The global weak gradient of the true cutoff product belongs to L². -/
theorem cutoff_product_gradient_memLp {U : Set Vec3} (hU : MeasurableSet U)
    {u η : Vec3 → ℝ} {g : Vec3 → Vec3}
    (hu : MemLp u 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hs : tsupport η ⊆ U)
    {C L : ℝ} (hb : ∀ x, ‖η x‖ ≤ C) (hgrad : ∀ x, ‖classicalGradient η x‖ ≤ L) :
    MemLp (fun x ↦ η x • g x + u x • classicalGradient η x) 2 volume := by
  have ha : MemLp (fun x ↦ η x • g x) 2 volume := by
    apply memLp_pi_iff.mpr
    intro i
    exact memLp_supported_scalar_product hU (hg.eval i) hη.continuous.measurable hs hb
  have hb' : MemLp (fun x ↦ u x • classicalGradient η x) 2 volume := by
    apply memLp_pi_iff.mpr
    intro i
    have hm := memLp_supported_scalar_product hU hu
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const).measurable
      ((classicalGradient_component_tsupport_subset i).trans hs)
      (fun x ↦ (norm_le_pi_norm (classicalGradient η x) i).trans (hgrad x))
    simpa only [classicalGradient_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hm
  exact ha.add hb'

/-- A compact product supported in the unit ball has the actual global weak Sobolev bound. -/
theorem cutoff_product_sobolev_six {U : Set Vec3} (hU : IsOpen U)
    {u η : Vec3 → ℝ} {g : Vec3 → Vec3}
    (hu : MemLp u 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hw : HasWeakGradientOn U u g) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U)
    (hunit : tsupport η ⊆ euclideanBall 0 1)
    {C L : ℝ} (hb : ∀ x, ‖η x‖ ≤ C) (hgrad : ∀ x, ‖classicalGradient η x‖ ≤ L) :
    eLpNorm (fun x ↦ η x * u x) 6 volume ≤ localSobolevConstant *
      (eLpNorm (fun x ↦ η x • g x) 2 volume +
        eLpNorm (fun x ↦ u x • classicalGradient η x) 2 volume +
        32 * eLpNorm (fun x ↦ η x * u x) 2 volume) := by
  have hv := memLp_supported_scalar_product hU.measurableSet hu
    hη.continuous.measurable hs hb
  have hG := cutoff_product_gradient_memLp hU.measurableSet hu hg hη hs hb hgrad
  have hglobal := hw.mul_smooth_zeroExtend hU
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hu.locallyIntegrable (by norm_num)))
    (fun i ↦ locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hg.eval i).locallyIntegrable (by norm_num))) hη hc hs
  let v : H1Function (euclideanBall (0 : Vec3) (2 * 1)) := {
    toFun := fun x ↦ η x * u x
    grad := fun x ↦ η x • g x + u x • classicalGradient η x
    memL2 := hv.restrict _
    gradMemL2 := fun i ↦ (hG.eval i).restrict _
    hasWeakGradient := hglobal.mono (isOpen_euclideanBall _ _) (subset_univ _) }
  have hSob := h1SobolevBall (x₀ := (0 : Vec3)) (r := 1) (by norm_num) v
  have heq : (euclideanBall (0 : Vec3) 1).indicator (fun x ↦ η x * u x) =
      (fun x ↦ η x * u x) := by
    funext x
    by_cases hx : x ∈ euclideanBall (0 : Vec3) 1
    · exact indicator_of_mem hx _
    · have hz : η x = 0 := image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hunit ht))
      simp only [indicator_of_notMem hx, hz, zero_mul]
  have hnorm : eLpNorm (fun x ↦ η x * u x) 6 volume =
      lpNormOn 6 (euclideanBall (0 : Vec3) 1) v.toFun := by
    rw [← heq, eLpNorm_indicator_eq_eLpNorm_restrict (isOpen_euclideanBall _ _).measurableSet]
    rfl
  rw [hnorm]
  apply hSob.trans
  apply mul_le_mul' (le_refl _)
  change eLpNorm v.grad 2 (volume.restrict (euclideanBall 0 (2 * 1))) +
    (Real.toNNReal (32 / 1) : ℝ≥0∞) *
      eLpNorm v.toFun 2 (volume.restrict (euclideanBall 0 (2 * 1))) ≤ _
  calc
    _ ≤ eLpNorm v.grad 2 volume + 32 * eLpNorm v.toFun 2 volume := by
      norm_num only [div_one, Real.toNNReal_ofNat, ENNReal.coe_ofNat]
      exact add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self)
        (mul_le_mul' (le_refl _) (eLpNorm_mono_measure _ Measure.restrict_le_self))
    _ ≤ _ := by
      apply add_le_add _ (le_refl _)
      let A : Vec3 → Vec3 := fun x ↦ η x • g x
      let B : Vec3 → Vec3 := fun x ↦ u x • classicalGradient η x
      rw [show v.grad = A + B by rfl]
      exact eLpNorm_add_le (by norm_num)

/-- The literal derivative of the cubed cutoff is the true weighted gradient. -/
theorem classicalGradient_cutoff_cube {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec3) :
    classicalGradient (fun y ↦ φ y ^ (3 : ℕ)) x =
      (3 * φ x ^ 2) • classicalGradient φ x := by
  ext i
  simp only [classicalGradient_apply, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_fun_pow 3 (hφ.differentiable (by simp)).differentiableAt]
  simp only [Nat.cast_ofNat, nsmul_eq_mul, Nat.reduceSub,
    smul_apply, smul_eq_mul]

/-- Positive integer powers do not enlarge the actual cutoff support. -/
theorem cutoff_pow_tsupport_subset {φ : Vec3 → ℝ} {n : ℕ} (hn : n ≠ 0) :
    tsupport (fun x ↦ φ x ^ n) ⊆ tsupport φ := by
  apply closure_mono
  intro x hx hz
  exact hx (by simp only [hz, zero_pow hn])

/-- The cubed cutoff velocity has genuine L⁶ control by the weighted gradient and L² term. -/
theorem cutoff_cube_sobolev_six {U : Set Vec3} (hU : IsOpen U)
    {u φ : Vec3 → ℝ} {g : Vec3 → Vec3}
    (hu : MemLp u 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hw : HasWeakGradientOn U u g) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hunit : tsupport φ ⊆ euclideanBall 0 1)
    (hφb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {L : ℝ} (hL : 0 ≤ L)
    (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    eLpNorm (fun x ↦ φ x ^ 3 * u x) 6 volume ≤ localSobolevConstant *
      (eLpNorm (fun x ↦ φ x ^ 3 • g x) 2 volume +
        ENNReal.ofReal (3 * L + 32) * eLpNorm (fun x ↦ φ x ^ 2 * u x) 2 volume) := by
  have hs3 := cutoff_pow_tsupport_subset (φ := φ) (by norm_num : (3 : ℕ) ≠ 0)
  have hs2 := cutoff_pow_tsupport_subset (φ := φ) (by norm_num : (2 : ℕ) ≠ 0)
  have hc3 : HasCompactSupport (fun x ↦ φ x ^ 3) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hs3
  have hpow (n : ℕ) (x : Vec3) : ‖φ x ^ n‖ ≤ 1 := by
    simp only [norm_pow, Real.norm_eq_abs, abs_of_nonneg (hφb x).1]
    exact pow_le_one₀ (hφb x).1 (hφb x).2
  have hd3 : ∀ x, ‖classicalGradient (fun y ↦ φ y ^ 3) x‖ ≤ 3 * L := by
    intro x
    rw [classicalGradient_cutoff_cube hφ, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 3 * φ x ^ 2)]
    calc
      _ ≤ (3 * 1) * L := by
        gcongr
        exact pow_le_one₀ (hφb x).1 (hφb x).2
        exact hgrad x
      _ = _ := by ring
  have hSob := cutoff_product_sobolev_six hU hu hg hw (hφ.pow 3) hc3
    (hs3.trans hs) (hs3.trans hunit) (hpow 3) hd3
  have hv2 := memLp_supported_scalar_product hU.measurableSet hu
    (hφ.pow 2).continuous.measurable (hs2.trans hs) (hpow 2)
  have hv3 := memLp_supported_scalar_product hU.measurableSet hu
    (hφ.pow 3).continuous.measurable (hs3.trans hs) (hpow 3)
  have hBu : MemLp (fun x ↦ u x • classicalGradient (fun y ↦ φ y ^ 3) x) 2 volume := by
    apply memLp_pi_iff.mpr
    intro i
    have hm := memLp_supported_scalar_product hU.measurableSet hu
      (((hφ.pow 3).continuous_fderiv (by simp)).clm_apply continuous_const).measurable
      ((classicalGradient_component_tsupport_subset i).trans (hs3.trans hs))
      (fun x ↦ (norm_le_pi_norm _ i).trans (hd3 x))
    simpa only [classicalGradient_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hm
  have hBn : eLpNorm (fun x ↦ u x • classicalGradient (fun y ↦ φ y ^ 3) x) 2 volume ≤
      ENNReal.ofReal (3 * L) * eLpNorm (fun x ↦ φ x ^ 2 * u x) 2 volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul hBu.aestronglyMeasurable
    filter_upwards [] with x
    have h3 : ‖3 * φ x ^ 2‖ = 3 * φ x ^ 2 := Real.norm_of_nonneg (by positivity)
    have h2 : ‖φ x ^ 2‖ = φ x ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    rw [classicalGradient_cutoff_cube hφ, norm_smul, norm_smul, h3, norm_mul, h2]
    calc
      _ ≤ ‖u x‖ * ((3 * φ x ^ 2) * L) := by gcongr; exact hgrad x
      _ = _ := by ring
  have hvn : eLpNorm (fun x ↦ φ x ^ 3 * u x) 2 volume ≤
      eLpNorm (fun x ↦ φ x ^ 2 * u x) 2 volume := by
    apply eLpNorm_mono_ae hv3.aestronglyMeasurable
    filter_upwards [] with x
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (hφb x).1]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    calc
      φ x ^ 3 = φ x * φ x ^ 2 := by ring
      _ ≤ 1 * φ x ^ 2 := mul_le_mul_of_nonneg_right (hφb x).2 (sq_nonneg _)
      _ = _ := one_mul _
  apply hSob.trans
  apply mul_le_mul' (le_refl _)
  rw [add_assoc]
  apply add_le_add (le_refl _)
  calc
    _ ≤ ENNReal.ofReal (3 * L) * eLpNorm (fun x ↦ φ x ^ 2 * u x) 2 volume +
        32 * eLpNorm (fun x ↦ φ x ^ 2 * u x) 2 volume :=
      add_le_add hBn (mul_le_mul' (le_refl _) hvn)
    _ = _ := by
      rw [← add_mul, ENNReal.ofReal_add (by positivity) (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]

/-- Restriction preserves the actual norm of any product whose factor is supported in the set. -/
theorem eLpNorm_supported_smul_restrict {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Vec3} (hU : MeasurableSet U) {η : Vec3 → ℝ} (hs : tsupport η ⊆ U)
    (u : Vec3 → E) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ η x • u x) p volume =
      eLpNorm (fun x ↦ η x • u x) p (volume.restrict U) := by
  have heq : U.indicator (fun x ↦ η x • u x) = (fun x ↦ η x • u x) := by
    funext x
    by_cases hx : x ∈ U
    · exact indicator_of_mem hx _
    · have hz : η x = 0 := image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht))
      simp only [indicator_of_notMem hx, hz, zero_smul]
  calc
    _ = eLpNorm (U.indicator (fun x ↦ η x • u x)) p volume := by rw [heq]
    _ = _ := eLpNorm_indicator_eq_eLpNorm_restrict hU

/-- The coordinate supremum norm gives true vector Lᵖ control by the coordinate norms. -/
theorem eLpNorm_vec3_le_sum_components {μ : Measure Vec3} {v : Vec3 → Vec3}
    (hv : AEStronglyMeasurable v μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm v p μ ≤ ∑ i : Fin 3, eLpNorm (fun x ↦ v x i) p μ := by
  have hn (x : Vec3) : ‖v x‖ ≤ ∑ i : Fin 3, ‖v x i‖ := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))).mpr
    intro i
    exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
  calc
    _ ≤ eLpNorm (fun x ↦ ∑ i : Fin 3, ‖v x i‖) p μ := by
      apply eLpNorm_mono_ae hv
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]
      exact hn x
    _ = eLpNorm (∑ i : Fin 3, (fun x ↦ ‖v x i‖)) p μ := rfl
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x ↦ ‖v x i‖) p μ := by
      simpa using eLpNorm_sum_le (f := fun i : Fin 3 ↦ (fun x ↦ ‖v x i‖))
        (s := Finset.univ) (μ := μ) hp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact eLpNorm_norm _ ((continuous_apply i).comp_aestronglyMeasurable hv)

/-- The actual vector corrected velocity satisfies the cubed-cutoff Sobolev estimate. -/
theorem cutoff_cube_vector_sobolev_six {U : Set Vec3} (hU : IsOpen U)
    {v : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3} {φ : Vec3 → ℝ}
    (hv : MemLp v 2 (volume.restrict U)) (hD : MemLp D 2 (volume.restrict U))
    (hw : ∀ i : Fin 3, HasWeakGradientOn U (fun x ↦ v x i) (fun x ↦ D x i))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hunit : tsupport φ ⊆ euclideanBall 0 1) (hφb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    eLpNorm (fun x ↦ φ x ^ 3 • v x) 6 volume ≤ (3 * localSobolevConstant) *
      (eLpNorm (fun x ↦ φ x ^ 3 • D x) 2 volume +
        ENNReal.ofReal (3 * L + 32) * eLpNorm (fun x ↦ φ x ^ 2 • v x) 2 volume) := by
  have hs3 := (cutoff_pow_tsupport_subset (φ := φ) (by norm_num : (3 : ℕ) ≠ 0)).trans hs
  have hs2 := (cutoff_pow_tsupport_subset (φ := φ) (by norm_num : (2 : ℕ) ≠ 0)).trans hs
  have hp (n : ℕ) (x : Vec3) : ‖φ x ^ n‖ ≤ 1 := by
    simp only [norm_pow, Real.norm_eq_abs, abs_of_nonneg (hφb x).1]
    exact pow_le_one₀ (hφb x).1 (hφb x).2
  have hv3 : MemLp (fun x ↦ φ x ^ 3 • v x) 2 volume := by
    apply memLp_pi_iff.mpr
    intro i
    exact memLp_supported_scalar_product hU.measurableSet (hv.eval i)
      (hφ.pow 3).continuous.measurable hs3 (hp 3)
  have hv2 : MemLp (fun x ↦ φ x ^ 2 • v x) 2 volume := by
    apply memLp_pi_iff.mpr
    intro i
    exact memLp_supported_scalar_product hU.measurableSet (hv.eval i)
      (hφ.pow 2).continuous.measurable hs2 (hp 2)
  have hD3 : MemLp (fun x ↦ φ x ^ 3 • D x) 2 volume := by
    apply memLp_pi_iff.mpr
    intro i
    apply memLp_pi_iff.mpr
    intro j
    exact memLp_supported_scalar_product hU.measurableSet ((hD.eval i).eval j)
      (hφ.pow 3).continuous.measurable hs3 (hp 3)
  have hi (i : Fin 3) : eLpNorm (fun x ↦ φ x ^ 3 * v x i) 6 volume ≤
      localSobolevConstant * (eLpNorm (fun x ↦ φ x ^ 3 • D x) 2 volume +
        ENNReal.ofReal (3 * L + 32) * eLpNorm (fun x ↦ φ x ^ 2 • v x) 2 volume) := by
    apply (cutoff_cube_sobolev_six hU (hv.eval i) (hD.eval i) (hw i)
      hφ hc hs hunit hφb hL hgrad).trans
    apply mul_le_mul' (le_refl _)
    apply add_le_add
    · exact eLpNorm_mono_ae (hD3.eval i).aestronglyMeasurable
        (ae_of_all _ (fun x ↦ norm_le_pi_norm (φ x ^ 3 • D x) i))
    · apply mul_le_mul' (le_refl _)
      exact eLpNorm_mono_ae (hv2.eval i).aestronglyMeasurable
        (ae_of_all _ (fun x ↦ norm_le_pi_norm (φ x ^ 2 • v x) i))
  apply (eLpNorm_vec3_le_sum_components hv3.aestronglyMeasurable (by norm_num)).trans
  calc
    _ ≤ ∑ _i : Fin 3, localSobolevConstant *
        (eLpNorm (fun x ↦ φ x ^ 3 • D x) 2 volume +
          ENNReal.ofReal (3 * L + 32) * eLpNorm (fun x ↦ φ x ^ 2 • v x) 2 volume) :=
      Finset.sum_le_sum (fun i _ ↦ hi i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring

/-- Squaring the true vector Sobolev bound gives actual weighted energy moments. -/
theorem cutoff_cube_vector_sobolev_six_squared {U : Set Vec3} (hU : IsOpen U)
    {v : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3} {φ : Vec3 → ℝ}
    (hv : MemLp v 2 (volume.restrict U)) (hD : MemLp D 2 (volume.restrict U))
    (hw : ∀ i : Fin 3, HasWeakGradientOn U (fun x ↦ v x i) (fun x ↦ D x i))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hunit : tsupport φ ⊆ euclideanBall 0 1) (hφb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    eLpNorm (fun x ↦ φ x ^ 3 • v x) 6 (volume.restrict U) ^ (2 : ℝ) ≤
      2 * (3 * localSobolevConstant) ^ 2 *
        ((∫⁻ x in U, ‖φ x ^ 3 • D x‖ₑ ^ (2 : ℝ)) +
          ENNReal.ofReal (3 * L + 32) ^ 2 * ∫⁻ x in U, ‖φ x ^ 2 • v x‖ₑ ^ (2 : ℝ)) := by
  have hs3 := (cutoff_pow_tsupport_subset (φ := φ) (by norm_num : (3 : ℕ) ≠ 0)).trans hs
  have hs2 := (cutoff_pow_tsupport_subset (φ := φ) (by norm_num : (2 : ℕ) ≠ 0)).trans hs
  have h6 := cutoff_cube_vector_sobolev_six hU hv hD hw hφ hc hs hunit hφb hL hgrad
  rw [eLpNorm_supported_smul_restrict hU.measurableSet hs3 v 6,
    eLpNorm_supported_smul_restrict hU.measurableSet hs3 D 2,
    eLpNorm_supported_smul_restrict hU.measurableSet hs2 v 2] at h6
  have hdmeas : AEStronglyMeasurable (fun x ↦ φ x ^ 3 • D x) (volume.restrict U) :=
    (hφ.pow 3).continuous.aestronglyMeasurable.smul hD.aestronglyMeasurable
  have hvmeas : AEStronglyMeasurable (fun x ↦ φ x ^ 2 • v x) (volume.restrict U) :=
    (hφ.pow 2).continuous.aestronglyMeasurable.smul hv.aestronglyMeasurable
  have hdEq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hdmeas
  have hvEq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hvmeas
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at hdEq hvEq
  have hadd := ENNReal.rpow_add_le_mul_rpow_add_rpow
    (eLpNorm (fun x ↦ φ x ^ 3 • D x) 2 (volume.restrict U))
    (ENNReal.ofReal (3 * L + 32) *
      eLpNorm (fun x ↦ φ x ^ 2 • v x) 2 (volume.restrict U))
    (by norm_num : (1 : ℝ) ≤ 2)
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_ofNat, mul_pow] at hadd
  rw [hdEq, hvEq] at hadd
  have hsq := pow_le_pow_left' h6 2
  rw [mul_pow] at hsq
  norm_num only [ENNReal.rpow_ofNat]
  exact (hsq.trans (mul_le_mul' (le_refl _) hadd)).trans_eq (by ring)

/-- Actual suitable weak solutions supply the weighted cutoff estimate on one full time set. -/
theorem suitable_cutoff_cube_sobolev_squared_ae
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    {U : Set Vec3} (hU : IsOpen U) (hbox : localBox Ω I U J) {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hunit : tsupport φ ⊆ euclideanBall 0 1) (hφb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x ↦ φ x ^ 3 • u (x, t)) 6 (volume.restrict U) ^ (2 : ℝ) ≤
        2 * (3 * localSobolevConstant) ^ 2 *
          ((∫⁻ x in U, ‖φ x ^ 3 • D (x, t)‖ₑ ^ (2 : ℝ)) +
            ENNReal.ofReal (3 * L + 32) ^ 2 *
              ∫⁻ x in U, ‖φ x ^ 2 • u (x, t)‖ₑ ^ (2 : ℝ)) := by
  have hw := ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht hwt
  exact cutoff_cube_vector_sobolev_six_squared hU ht.1 ht.2 hwt
    hφ hc hs hunit hφb hL hgrad

end FluidSingularSets
