-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesNonlinearPressure
public import FluidSingularSets.SliceLpMeasurable
public import FluidSingularSets.UnitBallPressureProjection
public import CKN.Foundation.Sobolev.Inequalities.H1
public import CKN.ClassEquivalence.VelocityTenThirds
public import CKN.Pressure.SliceIntegrability

/-!
# Actual spatial interpolation for the time integrability of Stokes pressures

The `L²` and genuine weak Sobolev `L⁶` slice bounds imply `L⁴` interpolation.
The exponent `8 / 3` makes its spatial `L⁶` factor quadratic, allowing actual
finite-energy suitable data to control the convective pressure in time `L^{4/3}`.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

private theorem unitBall_subset_double :
    euclideanBall (0 : Vec3) 1 ⊆ euclideanBall 0 2 := by
  intro x hx
  change euclideanSqDist x 0 < (2 : ℝ) ^ 2
  change euclideanSqDist x 0 < (1 : ℝ) ^ 2 at hx
  norm_num at hx ⊢
  exact hx.trans (by norm_num)

private theorem stokesLocalSobolevConstant_ne_top : localSobolevConstant ≠ ∞ := by
  unfold localSobolevConstant
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top

/-- Genuine `L²`/`L⁶` interpolation of any strongly measurable spatial velocity. -/
theorem eLpNorm_interpolate_four {μ : Measure Vec3} {u : Vec3 → Vec3}
    (hu : AEStronglyMeasurable u μ) :
    eLpNorm u 4 μ ≤ eLpNorm u 2 μ ^ (1 / 4 : ℝ) * eLpNorm u 6 μ ^ (3 / 4 : ℝ) := by
  let a : Vec3 → ℝ := fun x ↦ ‖u x‖ ^ (1 / 4 : ℝ)
  let b : Vec3 → ℝ := fun x ↦ ‖u x‖ ^ (3 / 4 : ℝ)
  have ha : AEStronglyMeasurable a μ := by
    exact (Real.continuous_rpow_const (q := (1 / 4 : ℝ)) (by norm_num)).comp_aestronglyMeasurable
      hu.norm
  have hb : AEStronglyMeasurable b μ := by
    exact (Real.continuous_rpow_const (q := (3 / 4 : ℝ)) (by norm_num)).comp_aestronglyMeasurable
      hu.norm
  let : ENNReal.HolderTriple 8 8 4 := by
    have h : Real.HolderTriple 8 8 4 := by rw [Real.holderTriple_iff]; norm_num
    simpa only [ENNReal.ofReal_ofNat] using h.ennrealOfReal
  have hholder : eLpNorm (fun x ↦ a x * b x) 4 μ ≤ eLpNorm a 8 μ * eLpNorm b 8 μ := by
    simpa only [ENNReal.coe_one, one_mul] using
      eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 8) (q := 8) (r := 4)
        (fun x y : ℝ ↦ x * y) 1 continuous_mul ha hb
        (ae_of_all _ (fun x ↦ by simp only [norm_mul, NNReal.coe_one, one_mul, le_refl]))
  have hprod : (fun x ↦ a x * b x) = fun x ↦ ‖u x‖ := by
    funext x
    change ‖u x‖ ^ (1 / 4 : ℝ) * ‖u x‖ ^ (3 / 4 : ℝ) = ‖u x‖
    by_cases hz : ‖u x‖ = 0
    · simp only [hz, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0),
        Real.zero_rpow (by norm_num : (3 / 4 : ℝ) ≠ 0), mul_zero]
    · rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))]
      norm_num
  have hquarter : ENNReal.ofReal (1 / 4 : ℝ) = (4 : ℝ≥0∞)⁻¹ := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hthreeQuarter : ENNReal.ofReal (3 / 4 : ℝ) = 3 * (4 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp only [ENNReal.ofReal_ofNat, div_eq_mul_inv]
  have h82 : (8 : ℝ≥0∞) * 4⁻¹ = 2 := by
    rw [show (8 : ℝ≥0∞) = 2 * 4 by norm_num, mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  have h86 : (8 : ℝ≥0∞) * (3 * 4⁻¹) = 6 := by
    rw [mul_left_comm, h82]
    norm_num
  have hpow2 : eLpNorm a 8 μ = eLpNorm u 2 μ ^ (1 / 4 : ℝ) := by
    have h := eLpNorm_norm_rpow u hu (by norm_num : (0 : ℝ) < 1 / 4) (p := 8)
    rw [hquarter, h82] at h
    exact h
  have hpow6 : eLpNorm b 8 μ = eLpNorm u 6 μ ^ (3 / 4 : ℝ) := by
    have h := eLpNorm_norm_rpow u hu (by norm_num : (0 : ℝ) < 3 / 4) (p := 8)
    rw [hthreeQuarter, h86] at h
    exact h
  rw [hprod, hpow2, hpow6, eLpNorm_norm u hu] at hholder
  exact hholder

/-- The actual two finite slice norms imply genuine spatial `L⁴` membership. -/
theorem memLp_four_of_two_six {μ : Measure Vec3} {u : Vec3 → Vec3}
    (hu2 : MemLp u 2 μ) (hu6 : MemLp u 6 μ) : MemLp u 4 μ := by
  apply memLp_iff.mpr
  exact (eLpNorm_interpolate_four hu2.aestronglyMeasurable).trans_lt (by finiteness [hu2, hu6])

/-- The exact exponent controlling time `L^{8/3}` of the actual spatial `L⁴` norm. -/
theorem eLpNorm_interpolate_four_pow {μ : Measure Vec3} {u : Vec3 → Vec3}
    (hu : AEStronglyMeasurable u μ) :
    eLpNorm u 4 μ ^ (8 / 3 : ℝ) ≤
      eLpNorm u 2 μ ^ (2 / 3 : ℝ) * eLpNorm u 6 μ ^ (2 : ℕ) := by
  have h := ENNReal.rpow_le_rpow (eLpNorm_interpolate_four hu) (by norm_num : (0 : ℝ) ≤ 8 / 3)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at h
  norm_num only [show (1 / 4 : ℝ) * (8 / 3) = 2 / 3 by norm_num,
    show (3 / 4 : ℝ) * (8 / 3) = 2 by norm_num, ENNReal.rpow_ofNat] at h
  exact h

private theorem eLpNorm_vector_six_le_sum {μ : Measure Vec3} {u : Vec3 → Vec3}
    (hu : AEStronglyMeasurable u μ) :
    eLpNorm u 6 μ ≤ ∑ j : Fin 3, eLpNorm (fun x ↦ u x j) 6 μ := by
  calc
    _ ≤ eLpNorm (fun x ↦ ∑ j : Fin 3, ‖u x j‖) 6 μ := by
      apply eLpNorm_mono_ae hu
      exact ae_of_all _ (fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]
        apply (pi_norm_le_iff_of_nonneg
          (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))).mpr
        intro j
        exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j))
    _ = eLpNorm (∑ j : Fin 3, fun x ↦ ‖u x j‖) 6 μ := rfl
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x ↦ ‖u x j‖) 6 μ :=
      eLpNorm_sum_le (by norm_num)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact eLpNorm_norm _ ((continuous_apply j).comp_aestronglyMeasurable hu)

/-- The actual weak-gradient slice on the double ball gives true vector `L⁶` control. -/
theorem unitBallH1Vector_sobolev {u : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3}
    (hu : MemLp u 2 (volume.restrict (euclideanBall 0 2)))
    (hD : MemLp D 2 (volume.restrict (euclideanBall 0 2)))
    (hw : ∀ j : Fin 3, HasWeakGradientOn (euclideanBall 0 2)
      (fun x ↦ u x j) (fun x ↦ D x j)) :
    eLpNorm u 6 (volume.restrict (euclideanBall 0 1)) ≤
      3 * localSobolevConstant *
        (eLpNorm D 2 (volume.restrict (euclideanBall 0 2)) +
          32 * eLpNorm u 2 (volume.restrict (euclideanBall 0 2))) := by
  have hcomp (j : Fin 3) : eLpNorm (fun x ↦ u x j) 6
      (volume.restrict (euclideanBall 0 1)) ≤ localSobolevConstant *
        (eLpNorm D 2 (volume.restrict (euclideanBall 0 2)) +
          32 * eLpNorm u 2 (volume.restrict (euclideanBall 0 2))) := by
    let v : H1Function (euclideanBall 0 (2 * 1)) :=
      { toFun := fun x ↦ u x j
        grad := fun x ↦ D x j
        memL2 := by simpa only [mul_one] using hu.eval j
        gradMemL2 := fun i ↦ by simpa only [mul_one] using (hD.eval j).eval i
        hasWeakGradient := by simpa only [mul_one] using hw j }
    have hs := h1SobolevBall (x₀ := (0 : Vec3)) (r := 1) (by norm_num) v
    have hg : eLpNorm (fun x ↦ D x j) 2 (volume.restrict (euclideanBall 0 2)) ≤
        eLpNorm D 2 (volume.restrict (euclideanBall 0 2)) :=
      eLpNorm_mono_ae ((hD.eval j).aestronglyMeasurable)
        (ae_of_all _ (fun x ↦ norm_le_pi_norm (D x) j))
    have hv : eLpNorm (fun x ↦ u x j) 2 (volume.restrict (euclideanBall 0 2)) ≤
        eLpNorm u 2 (volume.restrict (euclideanBall 0 2)) :=
      eLpNorm_mono_ae ((hu.eval j).aestronglyMeasurable)
        (ae_of_all _ (fun x ↦ norm_le_pi_norm (u x) j))
    norm_num only [mul_one, div_one, Real.toNNReal_ofNat, ENNReal.coe_ofNat] at hs
    change eLpNorm (fun x ↦ u x j) 6 (volume.restrict (euclideanBall 0 1)) ≤
      localSobolevConstant *
        (eLpNorm (fun x ↦ D x j) 2 (volume.restrict (euclideanBall 0 2)) +
          32 * eLpNorm (fun x ↦ u x j) 2 (volume.restrict (euclideanBall 0 2))) at hs
    exact hs.trans (mul_le_mul_right (add_le_add hg (mul_le_mul_right hv 32)) _)
  have hmeas : AEStronglyMeasurable u (volume.restrict (euclideanBall 0 1)) :=
    hu.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono unitBall_subset_double le_rfl)
  calc
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x ↦ u x j) 6 (volume.restrict (euclideanBall 0 1)) :=
      eLpNorm_vector_six_le_sum hmeas
    _ ≤ ∑ _j : Fin 3, localSobolevConstant *
        (eLpNorm D 2 (volume.restrict (euclideanBall 0 2)) +
          32 * eLpNorm u 2 (volume.restrict (euclideanBall 0 2))) :=
      Finset.sum_le_sum (fun j _ ↦ hcomp j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat, mul_assoc]

/-- Actual `H¹` velocity data give a genuine spatial `L⁶` slice on the unit ball. -/
theorem unitBallH1Vector_memLp_six {u : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3}
    (hu : MemLp u 2 (volume.restrict (euclideanBall 0 2)))
    (hD : MemLp D 2 (volume.restrict (euclideanBall 0 2)))
    (hw : ∀ j : Fin 3, HasWeakGradientOn (euclideanBall 0 2)
      (fun x ↦ u x j) (fun x ↦ D x j)) :
    MemLp u 6 (volume.restrict (euclideanBall 0 1)) := by
  apply memLp_iff.mpr
  exact (unitBallH1Vector_sobolev hu hD hw).trans_lt (by
    unfold localSobolevConstant
    finiteness [hu, hD])

/-- The true spatial interpolation bound with the actual outer slice energy. -/
theorem unitBallH1Vector_four_pow_energy {u : Vec3 → Vec3}
    {D : Vec3 → Fin 3 → Vec3} {M : ℝ≥0∞}
    (hu : MemLp u 2 (volume.restrict (euclideanBall 0 2)))
    (hD : MemLp D 2 (volume.restrict (euclideanBall 0 2)))
    (hw : ∀ j : Fin 3, HasWeakGradientOn (euclideanBall 0 2)
      (fun x ↦ u x j) (fun x ↦ D x j))
    (hM : eLpNorm u 2 (volume.restrict (euclideanBall 0 2)) ^ 2 ≤ M) :
    eLpNorm u 4 (volume.restrict (euclideanBall 0 1)) ^ (8 / 3 : ℝ) ≤
      2 * (3 * localSobolevConstant) ^ 2 * M ^ (1 / 3 : ℝ) *
        (eLpNorm D 2 (volume.restrict (euclideanBall 0 2)) ^ 2 + 1024 * M) := by
  have hui := hu.mono_measure (Measure.restrict_mono unitBall_subset_double le_rfl)
  have hU : eLpNorm u 2 (volume.restrict (euclideanBall 0 1)) ≤
      eLpNorm u 2 (volume.restrict (euclideanBall 0 2)) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono unitBall_subset_double le_rfl)
  have hfactor : eLpNorm u 2 (volume.restrict (euclideanBall 0 1)) ^ (2 / 3 : ℝ) ≤
      M ^ (1 / 3 : ℝ) := by
    have h := ENNReal.rpow_le_rpow hM (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul] at h
    norm_num only [show (2 : ℝ) * (1 / 3) = 2 / 3 by norm_num] at h
    exact (ENNReal.rpow_le_rpow hU (by norm_num)).trans h
  have hadd : (eLpNorm D 2 (volume.restrict (euclideanBall 0 2)) +
      32 * eLpNorm u 2 (volume.restrict (euclideanBall 0 2))) ^ 2 ≤
      2 * (eLpNorm D 2 (volume.restrict (euclideanBall 0 2)) ^ 2 + 1024 * M) := by
    have h := ENNReal.rpow_add_le_mul_rpow_add_rpow
      (eLpNorm D 2 (volume.restrict (euclideanBall 0 2)))
      (32 * eLpNorm u 2 (volume.restrict (euclideanBall 0 2)))
      (by norm_num : (1 : ℝ) ≤ 2)
    norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one,
      ENNReal.rpow_ofNat, mul_pow, show (32 : ℝ≥0∞) ^ 2 = 1024 by norm_num] at h
    exact h.trans (mul_le_mul_right (add_le_add le_rfl (mul_le_mul_right hM 1024)) 2)
  have hsquare := pow_le_pow_left' (unitBallH1Vector_sobolev hu hD hw) 2
  rw [mul_pow] at hsquare
  calc
    _ ≤ eLpNorm u 2 (volume.restrict (euclideanBall 0 1)) ^ (2 / 3 : ℝ) *
        eLpNorm u 6 (volume.restrict (euclideanBall 0 1)) ^ 2 :=
      eLpNorm_interpolate_four_pow hui.aestronglyMeasurable
    _ ≤ M ^ (1 / 3 : ℝ) * ((3 * localSobolevConstant) ^ 2 *
        (2 * (eLpNorm D 2 (volume.restrict (euclideanBall 0 2)) ^ 2 + 1024 * M))) :=
      mul_le_mul' hfactor (hsquare.trans (mul_le_mul_right hadd _))
    _ = _ := by ring

/-- Fubini identifies the true joint square moment with spatial slice norms. -/
theorem lintegral_spatial_two_sq_eq {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → E}
    (hF : AEStronglyMeasurable F (volume.restrict (B ×ˢ J))) :
    (∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 2 (volume.restrict B) ^ 2) =
      ∫⁻ z in B ×ˢ J, ‖F z‖ₑ ^ (2 : ℝ) := by
  have hprod : AEStronglyMeasurable F
      ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hF
  rw [show (volume : Measure ParabolicPoint).restrict (B ×ˢ J) =
    (volume.restrict B).prod (volume.restrict J) by
    rw [Measure.prod_restrict, CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod],
    lintegral_prod_symm _ (hprod.enorm.pow_const (2 : ℝ))]
  apply lintegral_congr_ae
  filter_upwards [hprod.prodMk_right] with t ht
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ht]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul]
  norm_num

section Suitable

variable {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
  {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- Actual suitability supplies spatial `L⁴` slices without extra regularity. -/
theorem suitable_unitBall_memLp_four_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    ∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ u (x, t)) 4 (volume.restrict (euclideanBall 0 1)) := by
  have hw : ∀ᵐ t ∂volume.restrict J, ∀ j : Fin 3,
      HasWeakGradientOn (euclideanBall 0 2)
        (fun x ↦ u (x, t) j) (fun x ↦ Du (x, t) j) :=
    ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht hwt
  exact memLp_four_of_two_six
    (ht.1.mono_measure (Measure.restrict_mono unitBall_subset_double le_rfl))
    (unitBallH1Vector_memLp_six ht.1 ht.2 hwt)

/-- The actual S1 slice energy controls time `L^{8/3}` of the spatial `L⁴` norm. -/
theorem suitable_unitBall_four_time_moment
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    (∫⁻ t in J, eLpNorm (fun x ↦ u (x, t)) 4
      (volume.restrict (euclideanBall 0 1)) ^ (8 / 3 : ℝ)) ≤
      2 * (3 * localSobolevConstant) ^ 2 *
        (essSup (fun t ↦ ∫⁻ x in euclideanBall 0 2, ‖u (x, t)‖ₑ ^ (2 : ℝ))
          (volume.restrict J)) ^ (1 / 3 : ℝ) *
        ((∫⁻ z in euclideanBall 0 2 ×ˢ J, ‖Du z‖ₑ ^ (2 : ℝ)) +
          1024 * (essSup (fun t ↦ ∫⁻ x in euclideanBall 0 2,
            ‖u (x, t)‖ₑ ^ (2 : ℝ)) (volume.restrict J)) * volume J) := by
  let M := essSup (fun t ↦ ∫⁻ x in euclideanBall 0 2, ‖u (x, t)‖ₑ ^ (2 : ℝ))
    (volume.restrict J)
  have hMfin : M < ∞ := hsol.toData.essSup_sliceEnergy_lt_top hbox
  have hw : ∀ᵐ t ∂volume.restrict J, ∀ j : Fin 3,
      HasWeakGradientOn (euclideanBall 0 2)
        (fun x ↦ u (x, t) j) (fun x ↦ Du (x, t) j) :=
    ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x ↦ u (x, t)) 4 (volume.restrict (euclideanBall 0 1)) ^ (8 / 3 : ℝ) ≤
        2 * (3 * localSobolevConstant) ^ 2 * M ^ (1 / 3 : ℝ) *
          (eLpNorm (fun x ↦ Du (x, t)) 2
            (volume.restrict (euclideanBall 0 2)) ^ 2 + 1024 * M) := by
    filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw,
      ENNReal.ae_le_essSup (μ := volume.restrict J)
        (fun t ↦ ∫⁻ x in euclideanBall 0 2, ‖u (x, t)‖ₑ ^ (2 : ℝ))] with t ht hwt hMt
    apply unitBallH1Vector_four_pow_energy ht.1 ht.2 hwt
    have heq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0))
      (by norm_num) ht.1.aestronglyMeasurable
    norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at heq
    exact heq.trans_le (by simpa only [M, ENNReal.rpow_ofNat] using hMt)
  calc
    _ ≤ ∫⁻ t in J, 2 * (3 * localSobolevConstant) ^ 2 * M ^ (1 / 3 : ℝ) *
        (eLpNorm (fun x ↦ Du (x, t)) 2
          (volume.restrict (euclideanBall 0 2)) ^ 2 + 1024 * M) :=
      lintegral_mono_ae hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by
          exact ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by norm_num)
              (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by norm_num)
                stokesLocalSobolevConstant_ne_top)))
            (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hMfin.ne).ne),
        lintegral_add_right _ measurable_const, lintegral_const,
        lintegral_spatial_two_sq_eq (hsol.toData.aestronglyMeasurable_gradient hbox)]
      simp only [M, Measure.restrict_apply_univ, mul_assoc, ENNReal.rpow_ofNat]

/-- The genuine suitable-data bound is finite, so this anisotropic moment is finite. -/
theorem suitable_unitBall_four_time_moment_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    (∫⁻ t in J, eLpNorm (fun x ↦ u (x, t)) 4
      (volume.restrict (euclideanBall 0 1)) ^ (8 / 3 : ℝ)) < ∞ := by
  apply (suitable_unitBall_four_time_moment hsol hbox).trans_lt
  have hM := hsol.toData.essSup_sliceEnergy_lt_top hbox
  have hD : (∫⁻ z in euclideanBall 0 2 ×ˢ J, ‖Du z‖ₑ ^ (2 : ℝ)) < ∞ :=
    (lintegral_mono (fun _ ↦ le_add_left le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)
  have hJ : volume J < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by norm_num)
          stokesLocalSobolevConstant_ne_top))))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne))
    (ENNReal.add_lt_top.mpr ⟨hD,
      ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hM) hJ⟩)

end Suitable

end FluidSingularSets
