module

public import FluidSingularSets.ActualEnergyControl

/-!
# Dissipation controlled by the actual velocity-pressure charge

These companion Caccioppoli estimates control the gradient mass in backward
cylinders with any admissible terminal time. The time flexibility is used when
comparing adjacent-grid cells with the symmetric activity at a singular center.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- The actual unforced CKN solution class satisfies a squared inner energy estimate,
with no assumed energy-decay or regularity conclusion. -/
theorem unforced_half_beta_sq_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hdom : closure (parabolicCylinder z.1 z.2 ρ) ⊆ CKN.spaceTimeSet Ω I) :
    CKN.beta u Du z (ρ / 2) ^ 2 ≤
      24 * CKN.Core.Endgame.startGammaConstant ^ 2 *
        (CKN.gamma u z ρ ^ 2 + CKN.gamma u z ρ ^ 3 + CKN.delta p z ρ ^ 3) := by
  have hg := CKN.gamma_nonneg u z hρ.le
  have hd := CKN.delta_nonneg p z hρ.le
  have hα := CKN.alpha_nonneg u z (by positivity : 0 ≤ ρ / 2)
  have hβ := CKN.beta_nonneg u Du z (by positivity : 0 ≤ ρ / 2)
  have hq : 0 < q := lt_trans (by norm_num : (0 : ℝ) < 5 / 2) hsol.2.2.2.1
  have hlambda : CKN.lambda q (fun _ ↦ 0) z ρ = 0 := by
    simp [CKN.lambda, vec3EuclideanNorm_zero, hq.ne', hq]
  have hratio : (ρ / 2) / ρ = (1 / 2 : ℝ) := by field_simp
  have hcacc := CKN.Core.Endgame.caccioppoli_gamma_display_fixed hsol hρ
    (by positivity : 0 < ρ / 2) le_rfl hdom
  rw [hratio, hlambda] at hcacc
  norm_num at hcacc
  have hbound : CKN.beta u Du z (ρ / 2) ≤ CKN.Core.Endgame.startGammaConstant *
      (CKN.gamma u z ρ / 2 + 2 * CKN.gamma u z ρ ^ (3 / 2 : ℝ) +
        2 * CKN.delta p z ρ * CKN.gamma u z ρ ^ (1 / 2 : ℝ)) := by
    nlinarith only [hcacc, hα]
  calc
    _ ≤ (CKN.Core.Endgame.startGammaConstant *
        (CKN.gamma u z ρ / 2 + 2 * CKN.gamma u z ρ ^ (3 / 2 : ℝ) +
          2 * CKN.delta p z ρ * CKN.gamma u z ρ ^ (1 / 2 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ hβ hbound 2
    _ = CKN.Core.Endgame.startGammaConstant ^ 2 *
        (CKN.gamma u z ρ / 2 + 2 * CKN.gamma u z ρ ^ (3 / 2 : ℝ) +
          2 * CKN.delta p z ρ * CKN.gamma u z ρ ^ (1 / 2 : ℝ)) ^ 2 := by ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (half_gamma_display_sq_le hg hd)
        (sq_nonneg CKN.Core.Endgame.startGammaConstant)
      nlinarith only [h]

/-- Both shifted backward cubic quantities are controlled by the actual symmetric charge. -/
theorem backward_half_gamma_delta_cubes_le_charge
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} (τ : ℝ) {r : ℝ} (hr : 0 < r)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ CKN.spaceTimeSet Ω I)
    (hsub : parabolicCylinder z.1 τ (r / 2) ⊆ rawSymmetricL3Cylinder z r) :
    CKN.gamma u (z.1, τ) (r / 2) ^ 3 +
      CKN.delta p (z.1, τ) (r / 2) ^ 3 ≤
        8 * rawSymmetricL3Activity u p z r := by
  let M := ∫⁻ a in rawSymmetricL3Cylinder z r,
    ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
      ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)
  have hfinite : M < ⊤ := raw_symmetric_velocity_pressure_integral_lt_top hsol hr hdom
  have hvel : (∫⁻ a in parabolicCylinder z.1 (z.1, τ).2 (r / 2),
      ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ)) ≤ M := by
    calc
      _ ≤ ∫⁻ a in rawSymmetricL3Cylinder z r,
          ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) := lintegral_mono_set hsub
      _ ≤ M := lintegral_mono fun _ ↦ le_add_of_nonneg_right bot_le
  have hpress : (∫⁻ a in parabolicCylinder z.1 (z.1, τ).2 (r / 2),
      ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)) ≤ M := by
    calc
      _ ≤ ∫⁻ a in rawSymmetricL3Cylinder z r,
          ENNReal.ofReal |p a| ^ (3 / 2 : ℝ) := lintegral_mono_set hsub
      _ ≤ M := lintegral_mono fun _ ↦ le_add_of_nonneg_left bot_le
  have hvelreal := ENNReal.toReal_mono hfinite.ne hvel
  have hpressreal := ENNReal.toReal_mono hfinite.ne hpress
  have hscale : (r / 2) ^ (-2 : ℝ) = 4 * r⁻¹ ^ 2 := by
    norm_num [Real.rpow_neg, Real.rpow_ofNat]
    field_simp
    ring
  have hγ : CKN.gamma u (z.1, τ) (r / 2) ^ 3 ≤
      4 * rawSymmetricL3Activity u p z r := by
    calc
      _ = (r / 2) ^ (-2 : ℝ) *
          (∫⁻ a in parabolicCylinder z.1 (z.1, τ).2 (r / 2),
            ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ)).toReal :=
        CKN.gamma_cube_eq u (z.1, τ) (r / 2) (by positivity)
      _ = 4 * r⁻¹ ^ 2 *
          (∫⁻ a in parabolicCylinder z.1 (z.1, τ).2 (r / 2),
            ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ)).toReal := by rw [hscale]
      _ ≤ 4 * r⁻¹ ^ 2 * M.toReal :=
        mul_le_mul_of_nonneg_left hvelreal (by positivity)
      _ = _ := by unfold rawSymmetricL3Activity; dsimp [M]; ring
  have hδ : CKN.delta p (z.1, τ) (r / 2) ^ 3 ≤
      4 * rawSymmetricL3Activity u p z r := by
    calc
      _ = (r / 2) ^ (-2 : ℝ) *
          (∫⁻ a in parabolicCylinder z.1 (z.1, τ).2 (r / 2),
            ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)).toReal :=
        CKN.delta_cube_eq p (z.1, τ) (r / 2) (by positivity)
      _ = 4 * r⁻¹ ^ 2 *
          (∫⁻ a in parabolicCylinder z.1 (z.1, τ).2 (r / 2),
            ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)).toReal := by rw [hscale]
      _ ≤ 4 * r⁻¹ ^ 2 * M.toReal :=
        mul_le_mul_of_nonneg_left hpressreal (by positivity)
      _ = _ := by unfold rawSymmetricL3Activity; dsimp [M]; ring
  linarith only [hγ, hδ]

/-- The inner squared energy is controlled by the actual symmetric charge. -/
theorem unforced_backward_half_beta_sq_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} (τ : ℝ) {r : ℝ} (hr : 0 < r)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ CKN.spaceTimeSet Ω I)
    (hsub : parabolicCylinder z.1 τ (r / 2) ⊆ rawSymmetricL3Cylinder z r) :
    CKN.beta u Du (z.1, τ) (r / 4) ^ 2 ≤
      192 * CKN.Core.Endgame.startGammaConstant ^ 2 *
        (rawSymmetricL3Activity u p z r ^ (2 / 3 : ℝ) + rawSymmetricL3Activity u p z r) := by
  let G := rawSymmetricL3Activity u p z r
  have hG : 0 ≤ G := rawSymmetricL3Activity_nonneg _ _ _ _
  have hγ := CKN.gamma_nonneg u (z.1, τ) (by positivity : 0 ≤ r / 2)
  have hδ := CKN.delta_nonneg p (z.1, τ) (by positivity : 0 ≤ r / 2)
  have hcubes := backward_half_gamma_delta_cubes_le_charge hsol τ hr hdom hsub
  have hγcube : CKN.gamma u (z.1, τ) (r / 2) ^ 3 ≤ 8 * G :=
    (le_add_of_nonneg_right (pow_nonneg hδ 3)).trans hcubes
  have hγsq := square_le_twoThirds_of_cube_le hγ (by positivity : 0 ≤ 8 * G) hγcube
  rw [eight_mul_twoThirds hG] at hγsq
  have houter := (closure_mono hsub).trans hdom
  have hβsq := unforced_half_beta_sq_bound (z := (z.1, τ)) hsol
    (by positivity : 0 < r / 2) houter
  have hquarter : (r / 2) / 2 = r / 4 := by ring
  rw [hquarter] at hβsq
  calc
    _ ≤ 24 * CKN.Core.Endgame.startGammaConstant ^ 2 *
        (CKN.gamma u (z.1, τ) (r / 2) ^ 2 +
          CKN.gamma u (z.1, τ) (r / 2) ^ 3 +
          CKN.delta p (z.1, τ) (r / 2) ^ 3) := hβsq
    _ ≤ 24 * CKN.Core.Endgame.startGammaConstant ^ 2 * (4 * G ^ (2 / 3 : ℝ) + 8 * G) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith only [hγsq, hcubes]
    _ ≤ _ := by
      have hpow : 0 ≤ G ^ (2 / 3 : ℝ) := Real.rpow_nonneg hG _
      nlinarith [sq_nonneg CKN.Core.Endgame.startGammaConstant]

/-- The actual integrated gradient mass in the inner backward cylinder is controlled
by the symmetric charge, with no dissipation estimate assumed. -/
theorem unforced_backward_half_gradient_mass_le_charge
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} (τ : ℝ) {r : ℝ} (hr : 0 < r)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ CKN.spaceTimeSet Ω I)
    (hsub : parabolicCylinder z.1 τ (r / 2) ⊆ rawSymmetricL3Cylinder z r) :
    (∫⁻ a in parabolicCylinder z.1 τ (r / 4), ENNReal.ofReal (CKN.spatialGradientSq u Du a)) ≤
      ENNReal.ofReal (48 * CKN.Core.Endgame.startGammaConstant ^ 2 * r *
        (rawSymmetricL3Activity u p z r ^ (2 / 3 : ℝ) + rawSymmetricL3Activity u p z r)) := by
  have hinner : parabolicCylinder z.1 τ (r / 4) ⊆ parabolicCylinder z.1 τ (r / 2) := by
    rintro a ⟨hx, hlow, hhigh⟩
    refine ⟨vec3Ball_mono (by linarith : r / 4 ≤ r / 2) hx, ?_, hhigh⟩
    nlinarith [sq_pos_of_pos hr]
  have hinnerdom := (closure_mono (hinner.trans hsub)).trans hdom
  rw [CKN.sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq hsol (z.1, τ)
    (by positivity : 0 < r / 4) hinnerdom]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (r / 4) * (192 * CKN.Core.Endgame.startGammaConstant ^ 2 *
        (rawSymmetricL3Activity u p z r ^ (2 / 3 : ℝ) + rawSymmetricL3Activity u p z r)) :=
      mul_le_mul_of_nonneg_left
        (unforced_backward_half_beta_sq_bound hsol τ hr hdom hsub) (by positivity)
    _ = _ := by ring

/-- The array norm used by the mixed-gradient trace is bounded by the actual
Dirichlet density used by the local energy inequality. -/
theorem array_norm_sq_le_spatialGradientSq (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    ‖Du z‖ ^ 2 ≤ CKN.spatialGradientSq u Du z := by
  have hS : 0 ≤ CKN.spatialGradientSq u Du z := by
    unfold CKN.spatialGradientSq
    exact Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg _))
  have hterm (i j : Fin 3) : (Du z i j) ^ 2 ≤ CKN.spatialGradientSq u Du z := by
    unfold CKN.spatialGradientSq
    exact (Finset.single_le_sum (fun l _ ↦ sq_nonneg (Du z i l)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum
        (fun l _ ↦ Finset.sum_nonneg (fun m _ ↦ sq_nonneg (Du z l m))) (Finset.mem_univ i))
  have hn : ‖Du z‖ ≤ Real.sqrt (CKN.spatialGradientSq u Du z) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro j
    simpa only [Real.norm_eq_abs] using Real.abs_le_sqrt (hterm i j)
  calc
    _ ≤ Real.sqrt (CKN.spatialGradientSq u Du z) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := Real.sq_sqrt hS

/-- The same pointwise comparison in the extended-real form used by the trace. -/
theorem array_enorm_sq_le_spatialGradientSq (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    ‖Du z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (CKN.spatialGradientSq u Du z) := by
  rw [ENNReal.rpow_ofNat, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (array_norm_sq_le_spatialGradientSq u Du z)

end FluidSingularSets
