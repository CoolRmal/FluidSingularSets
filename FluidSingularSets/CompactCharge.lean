module

public import CKN.ClassEquivalence.VelocityTenThirds
public import CKN.ClassEquivalence.MainTheorems
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Actual compact interior charge finiteness

The componentwise spatial-time Sobolev theorem gives velocity power `10/3` on each
ball box. The existing finite cover of a compact interior set retains that exponent.
The gradient power two and pressure power `3/2` follow directly from CKN's data clauses.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- For a positive finite exponent, the standard `MemLp` condition is equivalent to
finiteness of the literal extended-norm power integral. -/
theorem memLp_ofReal_iff_lintegral_enorm_rpow_lt_top
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {v : α → E} {t : ℝ} (ht : 0 < t)
    (hv : AEStronglyMeasurable v μ) :
    MemLp v (ENNReal.ofReal t) μ ↔ (∫⁻ z, ‖v z‖ₑ ^ t ∂μ) < ⊤ := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ne_of_gt (ENNReal.ofReal_pos.2 ht)) ENNReal.ofReal_ne_top hv,
    ENNReal.toReal_ofReal ht.le]

/-- Suitable solution data imply actual `L^(10/3)` velocity on every compact interior set.
The finite cover uses the already proved componentwise ball-box Sobolev estimate. -/
theorem velocity_memLp_tenThirds_on_compact_of_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ CKN.spaceTimeSet Ω I) :
    MemLp u (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict K) := by
  obtain ⟨Ω', J, n, c, rad, hbox, hradpos, hradsub, hcov⟩ :=
    CKN.exists_localBox_ball_cover_of_data hdata hK hKsub
  have hmeas :=
    (CKN.velocity_memLp_two_on_compact_of_data hdata hK hKsub).aestronglyMeasurable
  apply (memLp_ofReal_iff_lintegral_enorm_rpow_lt_top (by norm_num) hmeas).2
  have hlocal (m : Fin n) :
      (∫⁻ z in CKN.spaceTimeSet (vec3Ball (c m) (rad m)) J,
        ‖u z‖ₑ ^ (10 / 3 : ℝ)) < ⊤ := by
    have hpi : MemLp u (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (CKN.spaceTimeSet (vec3Ball (c m) (rad m)) J)) :=
      memLp_pi_iff.2 (fun i ↦ CKN.velocity_component_memLp_tenThirds_on_ballBox_of_data
        hdata hbox (hradpos m) (hradsub m) i)
    exact (memLp_ofReal_iff_lintegral_enorm_rpow_lt_top
      (by norm_num) hpi.aestronglyMeasurable).1 hpi
  calc
    _ ≤ ∫⁻ z in ⋃ m : Fin n, CKN.spaceTimeSet (vec3Ball (c m) (rad m)) J,
        ‖u z‖ₑ ^ (10 / 3 : ℝ) := lintegral_mono_set hcov
    _ ≤ ∑' m : Fin n, ∫⁻ z in CKN.spaceTimeSet (vec3Ball (c m) (rad m)) J,
        ‖u z‖ₑ ^ (10 / 3 : ℝ) := lintegral_iUnion_le _ _
    _ = ∑ m : Fin n, ∫⁻ z in CKN.spaceTimeSet (vec3Ball (c m) (rad m)) J,
        ‖u z‖ₑ ^ (10 / 3 : ℝ) := tsum_fintype _
    _ < ⊤ := ENNReal.sum_lt_top.2 (fun m _ ↦ hlocal m)

/-- The actual velocity, pressure and gradient charges are finite on every compact
interior set, using only the suitable solution's local data clauses. -/
theorem compact_velocity_pressure_gradient_charges_of_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ CKN.spaceTimeSet Ω I) :
    (∫⁻ z in K, ‖u z‖ₑ ^ (10 / 3 : ℝ)) < ⊤ ∧
      (∫⁻ z in K, ‖p z‖ₑ ^ (3 / 2 : ℝ)) < ⊤ ∧
        (∫⁻ z in K, ‖Du z‖ₑ ^ (2 : ℕ)) < ⊤ := by
  have hu := velocity_memLp_tenThirds_on_compact_of_data hdata hK hKsub
  have hp := CKN.pressure_memLp_threeHalves_on_compact_of_data hdata hK hKsub
  have hDu := CKN.gradient_memLp_two_on_compact_of_data hdata hK hKsub
  refine ⟨(memLp_ofReal_iff_lintegral_enorm_rpow_lt_top
    (by norm_num) hu.aestronglyMeasurable).1 hu,
    (memLp_ofReal_iff_lintegral_enorm_rpow_lt_top
      (by norm_num) hp.aestronglyMeasurable).1 hp, ?_⟩
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    hDu.eLpNorm_lt_top
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h

/-- The local data needed for charge finiteness are contained in the actual suitable
weak solution class carrying CKN's integral identities. -/
theorem compact_velocity_pressure_gradient_charges
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ CKN.spaceTimeSet Ω I) :
    (∫⁻ z in K, ‖u z‖ₑ ^ (10 / 3 : ℝ)) < ⊤ ∧
      (∫⁻ z in K, ‖p z‖ₑ ^ (3 / 2 : ℝ)) < ⊤ ∧
        (∫⁻ z in K, ‖Du z‖ₑ ^ (2 : ℕ)) < ⊤ :=
  compact_velocity_pressure_gradient_charges_of_data
    ⟨hsol.1, hsol.2.1, hsol.2.2.1, hsol.2.2.2.1, hsol.2.2.2.2.1, hsol.2.2.2.2.2.1⟩
    hK hKsub

/-- The physical Euclidean velocity norm has the same compact `10/3` finiteness.
The raw coordinate norm is compared with the Euclidean norm by CKN's explicit bound. -/
theorem compact_euclidean_velocity_tenThirds_charge_of_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ CKN.spaceTimeSet Ω I) :
    (∫⁻ z in K, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ)) < ⊤ := by
  let A := ENNReal.ofReal (Real.sqrt 3 ^ (10 / 3 : ℝ))
  have hA : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hnorm (v : Vec3) : ENNReal.ofReal (vec3EuclideanNorm v) ≤
      ENNReal.ofReal (Real.sqrt 3) * ‖v‖ₑ := by
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (vec3EuclideanNorm_le_sqrt_three_mul_norm v)
  have hpow (z : ParabolicPoint) :
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ) ≤
        A * ‖u z‖ₑ ^ (10 / 3 : ℝ) := by
    have h := ENNReal.rpow_le_rpow (hnorm (u z)) (by norm_num : (0 : ℝ) ≤ 10 / 3)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 10 / 3),
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num)] at h
    exact h
  have hu := (compact_velocity_pressure_gradient_charges_of_data hdata hK hKsub).1
  calc
    _ ≤ ∫⁻ z in K, A * ‖u z‖ₑ ^ (10 / 3 : ℝ) := lintegral_mono hpow
    _ = A * ∫⁻ z in K, ‖u z‖ₑ ^ (10 / 3 : ℝ) := lintegral_const_mul' A _ hA
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hA) hu

/-- The actual pressure and array-gradient density measures are finite on every
compact interior set. The density convention allows zero mass without extra choices. -/
theorem compact_pressure_gradient_measures_finite
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ CKN.spaceTimeSet Ω I) :
    IsFiniteMeasure ((volume.restrict K).withDensity (fun z ↦ ‖p z‖ₑ ^ (3 / 2 : ℝ))) ∧
      IsFiniteMeasure ((volume.restrict K).withDensity (fun z ↦ ‖Du z‖ₑ ^ (2 : ℕ))) := by
  have hcharge := compact_velocity_pressure_gradient_charges hsol hK hKsub
  exact ⟨isFiniteMeasure_withDensity hcharge.2.1.ne,
    isFiniteMeasure_withDensity hcharge.2.2.ne⟩

end FluidSingularSets
