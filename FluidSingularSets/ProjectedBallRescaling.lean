-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallStokesPressureProjection
public import CKN.Setting.ScalingInvariance

/-!
# Genuine rescaling of arbitrary projection balls

Actual suitable solutions and their compact local boxes pull back under the
true parabolic homeomorphism. In particular, projection on any physical ball
can be analyzed using the native unit ball, with the original interval mapped
exactly by the true time scaling.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- Genuine compact local boxes pull back by the actual parabolic homeomorphism. -/
theorem localBox_rescaled_preimages {μ : ℝ} (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω B : Set Vec3} {I J : Set ℝ} (hbox : localBox Ω I B J) :
    localBox (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I)
      (rescaledSpace μ z₀.1 B) (rescaledTime μ z₀.2 J) := by
  rcases hbox with ⟨hB, hBc, hBΩ, hJ, hJc, hJI⟩
  let eΩ := scalingSpaceHomeomorph μ hμ z₀.1
  let eI := scalingTimeHomeomorph μ hμ z₀.2
  have heΩ : scalingSpace μ z₀.1 = eΩ := by
    funext y
    simp [scalingSpace, eΩ, scalingSpaceHomeomorph]
  have heI : scalingTime μ z₀.2 = eI := by
    funext t
    simp [scalingTime, eI, scalingTimeHomeomorph, smul_eq_mul]
  have hBc' : closure (rescaledSpace μ z₀.1 B) = eΩ ⁻¹' closure B := by
    rw [rescaledSpace, heΩ, ← eΩ.preimage_closure]
  have hJc' : closure (rescaledTime μ z₀.2 J) = eI ⁻¹' closure J := by
    rw [rescaledTime, heI, ← eI.preimage_closure]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hB.preimage eΩ.continuous
  · rw [hBc']
    exact eΩ.isCompact_preimage.mpr hBc
  · rw [hBc']
    exact fun y hy ↦ hBΩ hy
  · exact hJ.preimage_mono (by
      intro s t hst
      change z₀.2 + μ ^ 2 * s ≤ z₀.2 + μ ^ 2 * t
      simpa only [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hst (sq_nonneg μ)) z₀.2)
  · rw [hJc']
    exact eI.isCompact_preimage.mpr hJc
  · rw [hJc']
    exact fun t ht ↦ hJI ht

/-- The actual physical spatial ball pulls back to its literal native radius. -/
theorem rescaledSpace_vec3Ball (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) (R : ℝ) :
    rescaledSpace μ x₀ (vec3Ball x₀ R) = vec3Ball 0 (R / μ) := by
  ext y
  simp only [rescaledSpace, mem_preimage, mem_vec3Ball, scalingSpace,
    add_sub_cancel_left, sub_zero, vec3EuclideanNorm_smul, abs_of_pos hμ]
  rw [lt_div_iff₀ hμ, mul_comm]

/-- Rescaling the actual projection ball by its radius gives exactly the native unit ball. -/
theorem rescaledSpace_projectionBall {μ : ℝ} (hμ : 0 < μ) (x₀ : Vec3) :
    rescaledSpace μ x₀ (vec3Ball x₀ μ) = vec3Ball 0 1 := by
  rw [rescaledSpace_vec3Ball μ hμ x₀ μ, div_self hμ.ne']

/-- The actual original interval has the literal rescaled endpoints. -/
theorem rescaledTime_Ioo (μ : ℝ) (hμ : 0 < μ) (t₀ a b : ℝ) :
    rescaledTime μ t₀ (Ioo a b) = Ioo ((a - t₀) / μ ^ 2) ((b - t₀) / μ ^ 2) := by
  ext t
  simp only [rescaledTime, mem_preimage, mem_Ioo, scalingTime]
  rw [div_lt_iff₀ (sq_pos_of_pos hμ), lt_div_iff₀ (sq_pos_of_pos hμ)]
  constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> nlinarith

/-- A genuine physical projection box gives the true native unit-ball local box. -/
theorem localBox_rescaled_projectionBall {μ : ℝ} (hμ : 0 < μ)
    (z₀ : ParabolicPoint) {Ω : Set Vec3} {I : Set ℝ} {a b : ℝ}
    (hbox : localBox Ω I (vec3Ball z₀.1 μ) (Ioo a b)) :
    localBox (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I)
      (vec3Ball 0 1) (Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2)) := by
  simpa only [rescaledSpace_projectionBall hμ, rescaledTime_Ioo μ hμ] using
    localBox_rescaled_preimages hμ z₀ hbox

/-- The genuine parabolic rescaling retains ordinary unforced suitable solutions. -/
theorem suitable_unforced_rescale
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (z₀ : ParabolicPoint) {μ : ℝ} (hμ : 0 < μ) :
    IsSuitableWeakSolutionIntegrable (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) q
      (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
      (rescalePressure μ z₀ p) (fun _ ↦ 0) := by
  have he : rescaleForce μ z₀ (fun _ ↦ (0 : Vec3)) = (fun _ ↦ 0) := by
    funext w
    change μ ^ 3 • (0 : Vec3) = 0
    exact smul_zero _
  have hs := isSuitableWeakSolutionIntegrable_rescale hsol z₀ hμ
  rw [he] at hs
  exact hs

end FluidSingularSets
