-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.HarmonicJointSmoothApprox
public import FluidSingularSets.UnitBallHarmonicForceHessian
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Genuine uniformly bounded harmonic Hessian approximations

The true smooth pressure Hessians define bounded force operators, with one
bound for every sufficiently small smoothing radius. The actual fixed-force
Hessian limit consequently also holds uniformly on compact force trajectories.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance harmonicHessianSmoothForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance harmonicHessianSmoothForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The derivative-first Hessian kernel of the genuine smooth pressure operator. -/
def harmonicSpatialSmoothHessianKernel {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) :
    Vec3 → StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ :=
  fun x ↦ (fderiv ℝ (harmonicSpatialSmoothGradientKernel hε j) x) (basisVec i)

theorem harmonicSpatialSmoothHessianKernel_contDiff {ε : ℝ} (hε : 0 < ε)
    (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (harmonicSpatialSmoothHessianKernel hε i j) := by
  have h := (harmonicSpatialSmoothGradientKernel_contDiff hε j).contDiff_fderiv_apply
    (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)
  exact h.comp (contDiff_id.prodMk contDiff_const)

/-- Operator differentiation evaluates to the literal scalar Hessian. -/
theorem harmonicSpatialSmoothHessianKernel_apply {ε : ℝ} (hε : 0 < ε)
    (i j : Fin 3) (x : Vec3) (F : StokesEnergyForce (vec3Ball 0 1)) :
    harmonicSpatialSmoothHessianKernel hε i j x F =
      mixedSecond (harmonicSpatialSmoothPressure F hε) i j x := by
  let ev := ContinuousLinearMap.apply ℝ ℝ F
  have heq : spatialDeriv (harmonicSpatialSmoothPressure F hε) j =
      fun y ↦ ev (harmonicSpatialSmoothGradientKernel hε j y) := by
    funext y
    exact (harmonicSpatialSmoothGradientKernel_apply hε j y F).symm
  have hd := ev.hasFDerivAt.comp x
    ((harmonicSpatialSmoothGradientKernel_contDiff hε j).differentiable
      (by simp) x).hasFDerivAt
  change _ = (fderiv ℝ (spatialDeriv (harmonicSpatialSmoothPressure F hε) j) x) (basisVec i)
  rw [heq]
  change _ = (fderiv ℝ (ev ∘ harmonicSpatialSmoothGradientKernel hε j) x) (basisVec i)
  rw [hd.fderiv]
  rfl

private theorem harmonicHessian_compact_inner (x : unitBallPressureCompactInterior) :
    x.1 ∈ vec3Ball 0 (1 / 8) := by
  have hx := x.property
  change x.1 ∈ closure (vec3Ball 0 (1 / 16)) at hx
  rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16)] at hx
  change vec3EuclideanNorm (x.1 - 0) ≤ 1 / 16 at hx
  exact hx.trans_lt (by norm_num)

private theorem harmonicHessian_compact_ball_inner (x : unitBallPressureCompactInterior)
    {ε : ℝ} (hsmall : ε ≤ 1 / 100) : Metric.ball x.1 ε ⊆ vec3Ball 0 (1 / 8) := by
  intro y hy
  have hx := x.property
  change x.1 ∈ closure (vec3Ball 0 (1 / 16)) at hx
  rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16)] at hx
  change vec3EuclideanNorm (x.1 - 0) ≤ 1 / 16 at hx
  have hn := euclideanNorm_le_three_mul_space_norm (y - x.1)
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have he : vec3EuclideanNorm (y - x.1) ≤ 3 * ε :=
    hn.trans (mul_le_mul_of_nonneg_left hy.le (by norm_num))
  have ht := vec3EuclideanNorm_add_le (y - x.1) x.1
  rw [sub_add_cancel] at ht
  rw [mem_vec3Ball]
  norm_num only [sub_zero] at hx ⊢
  linarith

/-- True convolution and the interior harmonic estimate bound every actual smooth Hessian. -/
theorem harmonicSpatialSmoothPressure_mixedSecond_bound
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 100) (x : unitBallPressureCompactInterior) (i j : Fin 3) :
    |mixedSecond (harmonicSpatialSmoothPressure F hε) i j x.1| ≤
      3 * unitBallPressureHessianConstant * ‖F‖ := by
  let g := mixedSecond (harmonicSpatialCutoffPressure F) i j
  let M := unitBallPressureHessianConstant * ‖F‖
  have hj := (harmonicSpatialCutoffPressure_contDiff F).contDiff_fderiv_apply
    (m := (1 : ℕ∞)) (n := (2 : ℕ∞)) (by norm_num)
  have hfirst : ContDiff ℝ (1 : ℕ∞)
      (spatialDeriv (harmonicSpatialCutoffPressure F) j) :=
    hj.comp (contDiff_id.prodMk contDiff_const)
  have hg : Continuous g :=
    (hfirst.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hb : |g x.1| ≤ M :=
    harmonicSpatialCutoffPressure_mixedSecond_bound F x.1 (harmonicHessian_compact_inner x) i j
  have hlocal : ∀ y ∈ Metric.ball x.1 ε, dist (g y) (g x.1) ≤ 2 * M := by
    intro y hy
    have hyb := harmonicSpatialCutoffPressure_mixedSecond_bound F y
      (harmonicHessian_compact_ball_inner x hsmall hy) i j
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by simpa only [Real.norm_eq_abs] using
      (show |g y| + |g x.1| ≤ 2 * M by dsimp [g, M] at *; linarith))
  have hm := (standardMollifier (d := 3) ε hε).dist_normed_convolution_le
    (μ := volume) hg.aestronglyMeasurable (x₀ := x.1) (ε := 2 * M) hlocal
  have ht := norm_add_le (mollify g ε hε x.1 - g x.1) (g x.1)
  simp only [sub_add_cancel] at ht
  rw [harmonicSpatialSmoothPressure_mixedSecond]
  change |mollify g ε hε x.1| ≤ _
  have hm' : dist (mollify g ε hε x.1) (g x.1) ≤ 2 * M := by
    simpa only [mollify, mollifier, dist_comm] using hm
  rw [dist_eq_norm, Real.norm_eq_abs] at hm'
  simp only [Real.norm_eq_abs] at ht
  dsimp [M] at *
  linarith

/-- The actual restricted Hessian of the canonical force pressure. -/
def harmonicCompactHessian (F : StokesEnergyForce (vec3Ball 0 1)) :
    C(unitBallPressureCompactInterior, StokesGradientMatrix) where
  toFun x := unitBallHarmonicForceHessianExtended F
    ⟨x.1, closure_mono (vec3Ball_mono (by norm_num : (1 / 16 : ℝ) ≤ 1 / 10))
      x.property⟩
  continuous_toFun := by
    apply (unitBallHarmonicForceHessianExtended F).continuous.comp
    exact continuous_subtype_val.subtype_mk _

/-- The smooth Hessian matrix is an actual compact continuous field. -/
def smoothCompactHessianMap {ε : ℝ} (hε : 0 < ε)
    (F : StokesEnergyForce (vec3Ball 0 1)) :
    C(unitBallPressureCompactInterior, StokesGradientMatrix) where
  toFun x := WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 ↦
    harmonicSpatialSmoothHessianKernel hε ij.1 ij.2 x.1 F)
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin 3 ↦ ℝ)).comp
    apply continuous_pi
    intro ij
    exact ((harmonicSpatialSmoothHessianKernel_contDiff hε ij.1 ij.2).continuous.comp
      continuous_subtype_val).clm_apply continuous_const

private theorem hilbertHessian_norm_le {A : StokesGradientMatrix} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ ij, ‖A ij‖ ≤ M) : ‖A‖ ≤ 3 * M := by
  have hsq : ‖A‖ ^ 2 ≤ 9 * M ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ij : Fin 3 × Fin 3, M ^ 2 := by
        apply Finset.sum_le_sum
        intro ij _
        exact (sq_le_sq₀ (norm_nonneg _) hM).mpr (hb ij)
      _ = _ := by
        norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hM)).mp
  nlinarith [hsq]

/-- One genuine force norm bound holds uniformly for all the smoothing radii. -/
theorem smoothCompactHessianMap_norm_le {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 100) (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖smoothCompactHessianMap hε F‖ ≤ 9 * unitBallPressureHessianConstant * ‖F‖ := by
  have hc := unitBallPressureHessianConstant_nonneg
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  apply (hilbertHessian_norm_le
    (M := 3 * unitBallPressureHessianConstant * ‖F‖)
    (by positivity) (fun ij ↦ ?_)).trans_eq (by ring)
  change |harmonicSpatialSmoothHessianKernel hε ij.1 ij.2 x.1 F| ≤ _
  rw [harmonicSpatialSmoothHessianKernel_apply]
  exact harmonicSpatialSmoothPressure_mixedSecond_bound F hε hsmall x ij.1 ij.2

/-- The actual smoothed Hessian is a genuine bounded linear force operator. -/
def harmonicSmoothCompactHessian {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 100) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ]
      C(unitBallPressureCompactInterior, StokesGradientMatrix) :=
  ({ toFun := smoothCompactHessianMap hε
     map_add' := fun F G ↦ by
       ext x ij
       exact (harmonicSpatialSmoothHessianKernel hε ij.1 ij.2 x.1).map_add F G
     map_smul' := fun c F ↦ by
       ext x ij
       exact (harmonicSpatialSmoothHessianKernel hε ij.1 ij.2 x.1).map_smul c F } :
    StokesEnergyForce (vec3Ball 0 1) →ₗ[ℝ]
      C(unitBallPressureCompactInterior, StokesGradientMatrix))
    |>.mkContinuous (9 * unitBallPressureHessianConstant)
      (smoothCompactHessianMap_norm_le hε hsmall)

theorem harmonicSmoothCompactHessian_opNorm_le {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 100) :
    ‖harmonicSmoothCompactHessian hε hsmall‖ ≤ 9 * unitBallPressureHessianConstant := by
  unfold harmonicSmoothCompactHessian
  exact LinearMap.mkContinuous_norm_le _
    (mul_nonneg (by norm_num) unitBallPressureHessianConstant_nonneg) _

/-- Restriction to the smaller compact test interior is an actual continuous map. -/
def pressureCompactHessianInclusion : C(unitBallPressureCompactInterior,
    unitBallPressureHessianCompactInterior) where
  toFun x := ⟨x.1, closure_mono (vec3Ball_mono
    (by norm_num : (1 / 16 : ℝ) ≤ 1 / 10)) x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The canonical restricted Hessian is a genuine bounded force operator. -/
def harmonicCompactHessianOperator : StokesEnergyForce (vec3Ball 0 1) →L[ℝ]
    C(unitBallPressureCompactInterior, StokesGradientMatrix) :=
  (ContinuousMap.compCLM ℝ StokesGradientMatrix pressureCompactHessianInclusion).comp
    unitBallHarmonicForceHessianExtended

@[simp]
theorem harmonicCompactHessianOperator_apply (F : StokesEnergyForce (vec3Ball 0 1))
    (x : unitBallPressureCompactInterior) (i j : Fin 3) :
    harmonicCompactHessianOperator F x (i, j) =
      mixedSecond (harmonicSpatialPressureRepresentative F) i j x.1 := rfl

@[simp]
theorem harmonicSmoothCompactHessian_apply {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 100) (F : StokesEnergyForce (vec3Ball 0 1))
    (x : unitBallPressureCompactInterior) (i j : Fin 3) :
    harmonicSmoothCompactHessian hε hsmall F x (i, j) =
      mixedSecond (harmonicSpatialSmoothPressure F hε) i j x.1 :=
  harmonicSpatialSmoothHessianKernel_apply hε i j x.1 F

/-- The true compact Hessian operator converges on each genuine force. -/
theorem harmonicSmoothCompactHessian_tendsto
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ 1 / 100) (F : StokesEnergyForce (vec3Ball 0 1)) :
    Tendsto (fun n ↦ harmonicSmoothCompactHessian (hpos n) (hsmall n) F)
      atTop (𝓝 (harmonicCompactHessianOperator F)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have he (ij : Fin 3 × Fin 3) : ∀ᶠ n in atTop,
      ∀ x : unitBallPressureCompactInterior,
        |mixedSecond (harmonicSpatialSmoothPressure F (hpos n)) ij.1 ij.2 x.1 -
          mixedSecond (harmonicSpatialPressureRepresentative F) ij.1 ij.2 x.1| < δ / 6 := by
    have ht := (harmonicSpatialSmoothPressure_mixedSecond_tendstoUniformly
      F ij.1 ij.2 hε hpos).comp (Subtype.val : unitBallPressureCompactInterior → Vec3)
    have heq : (fun x : unitBallPressureCompactInterior ↦
        mixedSecond (harmonicSpatialCutoffPressure F) ij.1 ij.2 x.1) =
        fun x ↦ mixedSecond (harmonicSpatialPressureRepresentative F) ij.1 ij.2 x.1 := by
      funext x
      exact mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 8))
        (harmonicSpatialCutoffPressure_eqOn F) ij.1 ij.2 (harmonicHessian_compact_inner x)
    change TendstoUniformly (fun n (x : unitBallPressureCompactInterior) ↦
      mixedSecond (harmonicSpatialSmoothPressure F (hpos n)) ij.1 ij.2 x.1)
      (fun x ↦ mixedSecond (harmonicSpatialCutoffPressure F) ij.1 ij.2 x.1) atTop at ht
    rw [heq] at ht
    have hd := Metric.tendstoUniformly_iff.mp ht (δ / 6) (by positivity)
    exact hd.mono fun n hn x ↦ by
      have hh := hn x
      rw [dist_comm] at hh
      simpa only [dist_eq_norm, Real.norm_eq_abs] using hh
  filter_upwards [Filter.eventually_all.mpr he] with n hn
  have hb : ‖harmonicSmoothCompactHessian (hpos n) (hsmall n) F -
      harmonicCompactHessianOperator F‖ ≤ δ / 2 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    apply (hilbertHessian_norm_le (M := δ / 6) (by positivity) (fun ij ↦ ?_)).trans_eq (by ring)
    change |harmonicSpatialSmoothHessianKernel (hpos n) ij.1 ij.2 x.1 F -
      mixedSecond (harmonicSpatialPressureRepresentative F) ij.1 ij.2 x.1| ≤ _
    rw [harmonicSpatialSmoothHessianKernel_apply]
    exact (hn ij x).le
  simpa only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] using
    hb.trans_lt (half_lt_self hδ)

/-- Actual bounded linear operators converge uniformly on every continuous compact trajectory. -/
theorem tendstoUniformly_operator_on_compact_domain
    {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : E →L[ℝ] F} {Ls : ℕ → E →L[ℝ] F} {C : ℝ}
    (hLs : ∀ n, ‖Ls n‖ ≤ C)
    (hpoint : ∀ x, Tendsto (fun n ↦ Ls n x) atTop (𝓝 (L x)))
    {f : K → E} (hf : Continuous f) :
    TendstoUniformly (fun n x ↦ Ls n (f x)) (fun x ↦ L (f x)) atTop := by
  have hC : 0 ≤ C := (norm_nonneg (Ls 0)).trans (hLs 0)
  have hlip (n : ℕ) : LipschitzWith (Real.toNNReal C) (Ls n) := by
    apply (Ls n).lipschitzWith.weaken
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hC]
    exact hLs n
  have heq := (LipschitzWith.uniformEquicontinuous
    (fun n x ↦ Ls n x) (Real.toNNReal C) hlip).equicontinuous
  have heqf : Equicontinuous (fun n x ↦ Ls n (f x)) := by
    rw [equicontinuous_iff_continuous]
    exact (equicontinuous_iff_continuous.mp heq).comp hf
  have ht := (heqf.tendsto_uniformFun_iff_pi atTop (fun x ↦ L (f x))).mpr
    (tendsto_pi_nhds.mpr fun x ↦ hpoint (f x))
  exact UniformFun.tendsto_iff_tendstoUniformly.mp ht

/-- Uniformly approximated compact input trajectories retain the true uniform operator limit. -/
theorem tendstoUniformly_moving_operator_on_compact_domain
    {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : E →L[ℝ] F} {Ls : ℕ → E →L[ℝ] F} {C : ℝ}
    (hLs : ∀ n, ‖Ls n‖ ≤ C)
    (hpoint : ∀ x, Tendsto (fun n ↦ Ls n x) atTop (𝓝 (L x)))
    {f : K → E} {fs : ℕ → K → E} (hf : Continuous f)
    (hfs : TendstoUniformly fs f atTop) :
    TendstoUniformly (fun n x ↦ Ls n (fs n x)) (fun x ↦ L (f x)) atTop := by
  have hC : 0 ≤ C := (norm_nonneg (Ls 0)).trans (hLs 0)
  have hD : 0 < C + 1 := by linarith
  have hfixed := tendstoUniformly_operator_on_compact_domain hLs hpoint hf
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [Metric.tendstoUniformly_iff.mp hfixed (δ / 2) (by positivity),
    Metric.tendstoUniformly_iff.mp hfs (δ / (2 * (C + 1))) (by positivity)]
    with n hn hs x
  have hb : dist (Ls n (fs n x)) (Ls n (f x)) ≤ (C + 1) * dist (fs n x) (f x) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((Ls n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (by linarith [hLs n]) (norm_nonneg _))
  have hsmall : dist (Ls n (fs n x)) (Ls n (f x)) < δ / 2 := by
    have h := mul_lt_mul_of_pos_left (hs x) hD
    have he : (C + 1) * (δ / (2 * (C + 1))) = δ / 2 := by field_simp
    rw [he, dist_comm] at h
    exact hb.trans_lt h
  calc
    dist (L (f x)) (Ls n (fs n x)) ≤
        dist (L (f x)) (Ls n (f x)) + dist (Ls n (f x)) (Ls n (fs n x)) :=
      dist_triangle _ _ _
    _ < δ := by rw [dist_comm] at hsmall; linarith [hn x]

/-- The genuine smooth Hessians converge uniformly along moving compact force trajectories. -/
theorem harmonicSmoothCompactHessian_tendstoUniformly
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ 1 / 100)
    {f : K → StokesEnergyForce (vec3Ball 0 1)}
    {fs : ℕ → K → StokesEnergyForce (vec3Ball 0 1)} (hf : Continuous f)
    (hfs : TendstoUniformly fs f atTop) :
    TendstoUniformly
      (fun n x ↦ harmonicSmoothCompactHessian (hpos n) (hsmall n) (fs n x))
      (fun x ↦ harmonicCompactHessianOperator (f x)) atTop :=
  tendstoUniformly_moving_operator_on_compact_domain
    (fun n ↦ harmonicSmoothCompactHessian_opNorm_le (hpos n) (hsmall n))
    (harmonicSmoothCompactHessian_tendsto hε hpos hsmall) hf hfs

end FluidSingularSets
