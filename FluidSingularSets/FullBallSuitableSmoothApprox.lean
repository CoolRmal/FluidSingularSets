-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallJointSmoothApprox
public import FluidSingularSets.FullBallSmoothLimits
public import FluidSingularSets.FullBallProjectedData

/-!
# Actual suitable force approximations on arbitrary compact interior balls

The genuine force primitive on the original time interval is smoothed in time,
then passed through actual spatial pressure kernels. The resulting fields retain
joint smoothness, harmonicity and the time-gradient identity, while their values
and Hessians converge uniformly and their pressures converge strongly in time L¹.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance fullBallSuitableApproxForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance fullBallSuitableApproxForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- A spatial scale within half the available margin, tending genuinely to zero. -/
def fullBallSuitableSmoothRadius (ρ σ : ℝ) (n : ℕ) : ℝ :=
  (σ - ρ) / (12 * ((n : ℝ) + 1))

theorem fullBallSuitableSmoothRadius_pos {ρ σ : ℝ} (hρσ : ρ < σ) (n : ℕ) :
    0 < fullBallSuitableSmoothRadius ρ σ n := by
  unfold fullBallSuitableSmoothRadius
  positivity

theorem fullBallSuitableSmoothRadius_le {ρ σ : ℝ} (hρσ : ρ < σ) (n : ℕ) :
    fullBallSuitableSmoothRadius ρ σ n ≤ (σ - ρ) / 12 := by
  unfold fullBallSuitableSmoothRadius
  apply div_le_div_of_nonneg_left (sub_nonneg.mpr hρσ.le) (by norm_num)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem fullBallSuitableSmoothRadius_le_six {ρ σ : ℝ} (hρσ : ρ < σ) (n : ℕ) :
    fullBallSuitableSmoothRadius ρ σ n ≤ (σ - ρ) / 6 := by
  have h := fullBallSuitableSmoothRadius_le hρσ n
  linarith

theorem fullBallSuitableSmoothRadius_tendsto (ρ σ : ℝ) :
    Tendsto (fullBallSuitableSmoothRadius ρ σ) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((σ - ρ) / 12)
  convert h using 1
  · funext n
    simp only [fullBallSuitableSmoothRadius, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  · simp

/-- Strong time approximation commutes with the genuine compact spatial pressure operators. -/
theorem fullBallSmoothCompactValue_strong_one
    (ρ σ θ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) (hσθ : σ < θ) (hθ : θ < 1)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ (σ - ρ) / 6)
    {g : ℝ → StokesEnergyForce (vec3Ball 0 1)}
    {gs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hg : MemLp g 1 volume) (hgs : ∀ n, MemLp (gs n) 1 volume)
    (hconv : Tendsto (fun n ↦ eLpNorm (gs n - g) 1 volume) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun t ↦
      fullBallSmoothCompactValue ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n) (gs n t) -
      fullBallCompactValueOperator ρ σ hρ hρσ (hσθ.trans hθ) (g t)) 1 volume)
      atTop (𝓝 0) :=
  tendsto_eLpNorm_moving_operator_curve_one
    (fun n ↦ fullBallSmoothCompactValue_opNorm_le ρ σ θ hρ hρσ hσθ hθ
      (hpos n) (hsmall n))
    (fullBallSmoothCompactValue_tendsto ρ σ θ hρ hρσ hσθ hθ hε hpos hsmall)
    hg hgs hconv

/-- A genuine source suitable solution supplies the actual full-ball smooth force
sequence, with common force bounds, exact differential identities and actual limits. -/
theorem exists_suitable_fullBall_joint_smooth_sequence_localBox
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ σ θ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρσ : ρ < σ) (hσθ : σ < θ) (hθ : θ < 1) :
    ∃ gs fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1),
      (∀ n, ContDiff ℝ ∞ (gs n) ∧ ContDiff ℝ ∞ (fs n) ∧
        HasCompactSupport (gs n) ∧ tsupport (gs n) ⊆ meanApproxTimeSet a b ∧
        MemLp (gs n) 1 volume ∧ (∀ t, HasDerivAt (fs n) (gs n t) t)) ∧
      unitBallVelocityForceCurve u =ᵐ[volume.restrict (Ioo a b)]
        localBoxForcePrimitive u D p a b c ∧
      Tendsto (fun n ↦ eLpNorm
        ((Ioo a b).indicator (unitBallMomentumForceCurve u D p) - gs n)
        1 volume) atTop (𝓝 0) ∧
      TendstoUniformly fs (localBoxForcePrimitive u D p a b c) atTop ∧
      (∃ C : ℝ, 0 < C ∧ ∀ n t, t ∈ Icc a b → ‖fs n t‖ ≤ C) ∧
      (∀ n, ContDiff ℝ ∞ (fullBallJointSmoothGradient σ θ (hρ.trans hρσ) hσθ hθ
          (fullBallSuitableSmoothRadius_pos hρσ n) (fun t ↦ -fs n t)) ∧
        ContDiff ℝ ∞ (fullBallJointSmoothPressure σ θ (hρ.trans hρσ) hσθ hθ
          (fullBallSuitableSmoothRadius_pos hρσ n) (fun t ↦ -gs n t)) ∧
        (∀ z i, timePartial (fun w ↦ fullBallJointSmoothGradient σ θ (hρ.trans hρσ)
            hσθ hθ (fullBallSuitableSmoothRadius_pos hρσ n) (fun t ↦ -fs n t) w i) z =
          spatialPartial (fullBallJointSmoothPressure σ θ (hρ.trans hρσ) hσθ hθ
            (fullBallSuitableSmoothRadius_pos hρσ n) (fun t ↦ -gs n t)) i z) ∧
        (∀ z, z.1 ∈ fullBallCompactInterior ρ →
          (∑ i : Fin 3, spatialPartial (fun w ↦ fullBallJointSmoothGradient σ θ
            (hρ.trans hρσ) hσθ hθ (fullBallSuitableSmoothRadius_pos hρσ n)
            (fun t ↦ -fs n t) w i) i z) = 0) ∧
        (∀ z i, z.1 ∈ fullBallCompactInterior ρ →
          (∑ j : Fin 3, spatialSecondPartial (fun w ↦ fullBallJointSmoothGradient σ θ
            (hρ.trans hρσ) hσθ hθ (fullBallSuitableSmoothRadius_pos hρσ n)
            (fun t ↦ -fs n t) w i) j j z) = 0)) ∧
      TendstoUniformly (fun n (t : Icc a b) ↦
        fullBallSmoothCompactGradient ρ σ θ hρ hρσ hσθ hθ
          (fullBallSuitableSmoothRadius_pos hρσ n)
          (fullBallSuitableSmoothRadius_le_six hρσ n) (-fs n t.1))
        (fun t ↦ fullBallProjectedGradientCompact u D p a b c hρ
          (hρσ.trans (hσθ.trans hθ)) t.1) atTop ∧
      TendstoUniformly (fun n (t : Icc a b) ↦
        fullBallSmoothCompactHessian ρ σ θ hρ hρσ hσθ hθ
          (fullBallSuitableSmoothRadius_pos hρσ n)
          (fullBallSuitableSmoothRadius_le_six hρσ n) (-fs n t.1))
        (fun t ↦ fullBallProjectedHessianCompact u D p a b c hρ
          (hρσ.trans (hσθ.trans hθ)) t.1) atTop ∧
      Tendsto (fun n ↦ eLpNorm (fun t ↦
        fullBallSmoothCompactValue ρ σ θ hρ hρσ hσθ hθ
          (fullBallSuitableSmoothRadius_pos hρσ n)
          (fullBallSuitableSmoothRadius_le_six hρσ n) (-gs n t) -
        fullBallCompactValueOperator ρ σ hρ hρσ (hσθ.trans hθ)
          (-((Ioo a b).indicator (unitBallMomentumForceCurve u D p) t))) 1 volume)
        atTop (𝓝 0) := by
  obtain ⟨gs, fs, hsm, hAE, hconv, hunif, C, hC, hbound⟩ :=
    exists_suitable_unitBall_force_smooth_sequence_localBox hsol hbox hab hc
  obtain ⟨_, hg⟩ := suitable_unitBall_momentumForces_integrable_localBox hsol hbox
  have hg₀ : Integrable ((Ioo a b).indicator (unitBallMomentumForceCurve u D p)) volume :=
    hg.integrable_indicator measurableSet_Ioo
  have hM : Continuous (localBoxForcePrimitive u D p a b c) :=
    continuous_const.add (hg₀.continuous_primitive c)
  have hneg : TendstoUniformly (fun n t ↦ -fs n t)
      (fun t ↦ -localBoxForcePrimitive u D p a b c t) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro δ hδ
    filter_upwards [Metric.tendstoUniformly_iff.mp hunif δ hδ] with n hn t
    simpa only [dist_neg_neg] using hn t
  have hnegconv : Tendsto (fun n ↦ eLpNorm
      ((fun t ↦ -gs n t) - fun t ↦
        -((Ioo a b).indicator (unitBallMomentumForceCurve u D p) t))
      1 volume) atTop (𝓝 0) := by
    convert hconv using 1
    funext n
    congr 1
    funext t
    simp only [Pi.sub_apply]
    abel
  refine ⟨gs, fs, hsm, hAE, hconv, hunif, ⟨C, hC, hbound⟩, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨fullBallJointSmoothGradient_contDiff _ _ _ _ _ _ (hsm n).2.1.neg,
      fullBallJointSmoothPressure_contDiff _ _ _ _ _ _ (hsm n).1.neg, ?_, ?_, ?_⟩
    · intro z i
      exact fullBallJointSmoothGradient_timePartial _ _ _ _ _ _
        (fun t ↦ ((hsm n).2.2.2.2.2 t).neg) z i
    · intro z hz
      apply fullBallJointSmoothGradient_divergence σ θ (hρ.trans hρσ) hσθ hθ
        (ρ := (ρ + σ) / 2) (by linarith) _ (by
          have h := fullBallSuitableSmoothRadius_le hρσ n
          linarith) _ z
      exact fullBallCompactInterior_subset hρ (by linarith) hz
    · intro z i hz
      apply fullBallJointSmoothGradient_spatialSecondPartial σ θ (hρ.trans hρσ) hσθ hθ
        (ρ := (ρ + σ) / 2) (by linarith) _ (by
          have h := fullBallSuitableSmoothRadius_le hρσ n
          linarith) _ i z
      exact fullBallCompactInterior_subset hρ (by linarith) hz
  · have h := fullBallSmoothCompactGradient_tendstoUniformly ρ σ θ hρ hρσ hσθ hθ
      (fullBallSuitableSmoothRadius_tendsto ρ σ) (fullBallSuitableSmoothRadius_pos hρσ)
      (fullBallSuitableSmoothRadius_le_six hρσ) (hM.neg.comp continuous_subtype_val)
      (hneg.comp (Subtype.val : Icc a b → ℝ))
    exact h
  · have h := fullBallSmoothCompactHessian_tendstoUniformly ρ σ θ hρ hρσ hσθ hθ
      (fullBallSuitableSmoothRadius_tendsto ρ σ) (fullBallSuitableSmoothRadius_pos hρσ)
      (fullBallSuitableSmoothRadius_le_six hρσ) (hM.neg.comp continuous_subtype_val)
      (hneg.comp (Subtype.val : Icc a b → ℝ))
    exact h
  · exact fullBallSmoothCompactValue_strong_one ρ σ θ hρ hρσ hσθ hθ
      (fullBallSuitableSmoothRadius_tendsto ρ σ) (fullBallSuitableSmoothRadius_pos hρσ)
      (fullBallSuitableSmoothRadius_le_six hρσ) (memLp_one_iff_integrable.mpr hg₀).neg
      (fun n ↦ (hsm n).2.2.2.2.1.neg) hnegconv

end FluidSingularSets
