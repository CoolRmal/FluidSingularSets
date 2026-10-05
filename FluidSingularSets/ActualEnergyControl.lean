module

public import FluidSingularSets.RealCharge
public import CKN.Core.Endgame.StartCaccioppoli
public import CKN.Setting.SliceNormBounds
public import CKN.Setting.ScalingQuantityNonneg

/-!
# Energy control by the actual cubic velocity-pressure charge

The imported solution-level Caccioppoli estimate controls the energy at an inner radius.
Its cubic velocity and pressure terms are bounded by the combined charge on an outer
symmetric cylinder. The time shift makes the backward energy window cover the symmetric
window used in the mixed decay estimate.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

noncomputable section

namespace FluidSingularSets

/-- The symmetric cylinder in the raw CKN coordinates. -/
def rawSymmetricL3Cylinder (z : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  vec3Ball z.1 r ×ˢ Ioo (z.2 - r ^ 2) (z.2 + r ^ 2)

/-- The real symmetric cubic velocity-pressure activity in raw CKN coordinates. -/
def rawSymmetricL3Activity (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ :=
  r⁻¹ ^ 2 * (∫⁻ a in rawSymmetricL3Cylinder z r,
    ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
      ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)).toReal

/-- The raw symmetric activity is nonnegative at every radius. -/
theorem rawSymmetricL3Activity_nonneg (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) (z : ParabolicPoint) (r : ℝ) :
    0 ≤ rawSymmetricL3Activity u p z r :=
  mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg

/-- The extended normalized charge is the `ofReal` of raw activity when its mass is finite. -/
theorem ofReal_rawSymmetricL3Activity (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) (z : ParabolicPoint) (r : ℝ)
    (hfinite : (∫⁻ a in rawSymmetricL3Cylinder z r,
      ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
        ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)) ≠ ⊤) :
    ENNReal.ofReal (rawSymmetricL3Activity u p z r) = ENNReal.ofReal (r⁻¹ ^ 2) *
      ∫⁻ a in rawSymmetricL3Cylinder z r,
        ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
          ENNReal.ofReal |p a| ^ (3 / 2 : ℝ) := by
  rw [rawSymmetricL3Activity, ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_toReal hfinite]

/-- The coordinate homeomorphism identifies the two symmetric cylinders. -/
theorem rawSpaceTime_preimage_symmetricCylinder (z : ParabolicPoint) (r : ℝ) :
    CKNChallenge.parabolicToEuclideanHomeomorph ⁻¹'
      symmetricL3Cylinder (CKNChallenge.parabolicToEuclideanHomeomorph z) r =
        rawSymmetricL3Cylinder z r := by
  ext a
  change (dist (CKNChallenge.rawToEuclidean a.1) (CKNChallenge.rawToEuclidean z.1) < r ∧
    a.2 ∈ Ioo (z.2 - r ^ 2) (z.2 + r ^ 2)) ↔
      (vec3EuclideanNorm (a.1 - z.1) < r ∧ a.2 ∈ Ioo (z.2 - r ^ 2) (z.2 + r ^ 2))
  have hnorm : dist (CKNChallenge.rawToEuclidean a.1)
      (CKNChallenge.rawToEuclidean z.1) = vec3EuclideanNorm (a.1 - z.1) := by
    rw [dist_eq_norm, vec3EuclideanNorm_eq_l2]
    change ‖CKNChallenge.rawToEuclidean a.1 - CKNChallenge.rawToEuclidean z.1‖ =
      ‖CKNChallenge.rawToEuclidean (a.1 - z.1)‖
    rw [map_sub]
  rw [hnorm]

/-- The actual physical and raw symmetric activities agree under the coordinate pullback. -/
theorem rawSymmetricL3Activity_pull_eq (u : SpaceTime → Space) (p : SpaceTime → ℝ)
    (z : ParabolicPoint) (r : ℝ) :
    rawSymmetricL3Activity (CKNChallenge.pullVelocity u) (CKNChallenge.pullScalar p) z r =
      symmetricL3Activity u p (CKNChallenge.parabolicToEuclideanHomeomorph z) r := by
  let H := CKNChallenge.parabolicToEuclideanHomeomorph
  have hmp := CKNChallenge.parabolicToEuclidean_measurePreserving.restrict_preimage_emb
    H.measurableEmbedding (symmetricL3Cylinder (H z) r)
  have hchange := hmp.lintegral_comp_emb H.measurableEmbedding
    (fun a ↦ ‖u a‖ₑ ^ (3 : ℝ) + ‖p a‖ₑ ^ (3 / 2 : ℝ))
  rw [rawSpaceTime_preimage_symmetricCylinder] at hchange
  have hmass : (∫⁻ a in rawSymmetricL3Cylinder z r,
      ENNReal.ofReal (vec3EuclideanNorm (CKNChallenge.pullVelocity u a)) ^ (3 : ℝ) +
        ENNReal.ofReal |CKNChallenge.pullScalar p a| ^ (3 / 2 : ℝ)) =
      ∫⁻ a in symmetricL3Cylinder (H z) r,
        ‖u a‖ₑ ^ (3 : ℝ) + ‖p a‖ₑ ^ (3 / 2 : ℝ) := by
    calc
      _ = ∫⁻ a in rawSymmetricL3Cylinder z r,
          ‖u (H a)‖ₑ ^ (3 : ℝ) + ‖p (H a)‖ₑ ^ (3 / 2 : ℝ) := by
        apply lintegral_congr
        intro a
        simp only [CKNChallenge.pullVelocity, CKNChallenge.pullScalar,
          CKNChallenge.vec3EuclideanNorm_rawToEuclidean_symm, Real.norm_eq_abs,
          ← ofReal_norm]
        rfl
      _ = _ := hchange
  unfold rawSymmetricL3Activity
  rw [symmetricL3Activity_eq, hmass]

/-- Closure containment is preserved by the raw-to-physical homeomorphism. -/
theorem closure_rawSymmetricL3Cylinder (z : ParabolicPoint) (r : ℝ) :
    closure (rawSymmetricL3Cylinder z r) =
      CKNChallenge.parabolicToEuclideanHomeomorph ⁻¹'
        closure (symmetricL3Cylinder (CKNChallenge.parabolicToEuclideanHomeomorph z) r) := by
  rw [← rawSpaceTime_preimage_symmetricCylinder]
  exact (CKNChallenge.parabolicToEuclideanHomeomorph.preimage_closure _).symm

/-- The raw symmetric charge is finite for every actual solution when its closure is in the
solution domain. -/
theorem raw_symmetric_velocity_pressure_integral_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ CKN.spaceTimeSet Ω I) :
    (∫⁻ a in rawSymmetricL3Cylinder z r,
      ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
        ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)) < ⊤ := by
  let H := CKNChallenge.parabolicToEuclideanHomeomorph
  have hphys := two_backward_closure_subset_symmetric (H z) hr
  have hleft : closure (parabolicCylinder z.1 z.2 r) ⊆ CKN.spaceTimeSet Ω I := by
    intro a ha
    have hpa := (CKNChallenge.mem_closure_cylinder_iff_mem_closure_Q hr z a).1 ha
    apply hdom
    rw [closure_rawSymmetricL3Cylinder]
    exact hphys.1 hpa
  have hright : closure (parabolicCylinder z.1 (z.2 + r ^ 2) r) ⊆
      CKN.spaceTimeSet Ω I := by
    intro a ha
    have hpa := (CKNChallenge.mem_closure_cylinder_iff_mem_closure_Q hr
      (z.1, z.2 + r ^ 2) a).1 ha
    apply hdom
    rw [closure_rawSymmetricL3Cylinder]
    exact hphys.2 hpa
  have hcover : rawSymmetricL3Cylinder z r ⊆ parabolicCylinder z.1 z.2 r ∪
      parabolicCylinder z.1 (z.2 + r ^ 2) r := by
    rintro a ⟨hx, hlow, hhigh⟩
    by_cases ht : a.2 ≤ z.2
    · exact Or.inl ⟨hx, hlow, ht⟩
    · refine Or.inr ⟨hx, ?_, hhigh.le⟩
      linarith
  calc
    _ ≤ ∫⁻ a in parabolicCylinder z.1 z.2 r ∪
        parabolicCylinder z.1 (z.2 + r ^ 2) r,
        ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
          ENNReal.ofReal |p a| ^ (3 / 2 : ℝ) := lintegral_mono_set hcover
    _ ≤ (∫⁻ a in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
          ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)) +
        ∫⁻ a in parabolicCylinder z.1 (z.2 + r ^ 2) r,
          ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
            ENNReal.ofReal |p a| ^ (3 / 2 : ℝ) := lintegral_union_le _ _ _
    _ < ⊤ := ENNReal.add_lt_top.2
      ⟨raw_velocity_pressure_integral_lt_top hsol hr hleft,
        raw_velocity_pressure_integral_lt_top (z := (z.1, z.2 + r ^ 2)) hsol hr hright⟩

/-- The backward-cylinder top used for the inner energy window. -/
def energyShiftedTop (z : ParabolicPoint) (r : ℝ) : ParabolicPoint :=
  (z.1, z.2 + (r / 512) ^ 2 / 16)

/-- The shifted outer cylinder of radius `r/2` stays in the symmetric cylinder of radius `r`. -/
theorem energyShiftedOuter_subset_symmetric (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    parabolicCylinder z.1 (energyShiftedTop z r).2 (r / 2) ⊆
      rawSymmetricL3Cylinder z r := by
  rintro a ⟨hx, hlow, hhigh⟩
  have hspace : a.1 ∈ vec3Ball z.1 r := (vec3Ball_mono (by linarith : r / 2 ≤ r)) hx
  refine ⟨hspace, ?_, ?_⟩ <;> dsimp [energyShiftedTop] at * <;>
    nlinarith [sq_pos_of_pos hr]

/-- The closure of the shifted outer cylinder remains in the symmetric closure. -/
theorem energyShiftedOuter_closure_subset_symmetric (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) :
    closure (parabolicCylinder z.1 (energyShiftedTop z r).2 (r / 2)) ⊆
      closure (rawSymmetricL3Cylinder z r) :=
  closure_mono (energyShiftedOuter_subset_symmetric z hr)

/-- The weighted cubic product is bounded by the sum of the two cubes. -/
theorem sq_mul_le_sum_cubes {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 * b ≤ a ^ 3 + b ^ 3 := by
  by_cases hab : a ≤ b
  · calc
      a ^ 2 * b ≤ b ^ 2 * b :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2) hb
      _ = b ^ 3 := by ring
      _ ≤ a ^ 3 + b ^ 3 := le_add_of_nonneg_left (pow_nonneg ha 3)
  · calc
      a ^ 2 * b ≤ a ^ 2 * a := mul_le_mul_of_nonneg_left (le_of_not_ge hab) (sq_nonneg a)
      _ = a ^ 3 := by ring
      _ ≤ a ^ 3 + b ^ 3 := le_add_of_nonneg_right (pow_nonneg hb 3)

/-- Squaring the half-radius gamma display costs only an absolute coefficient. -/
theorem half_gamma_display_sq_le {g d : ℝ} (hg : 0 ≤ g) (hd : 0 ≤ d) :
    (g / 2 + 2 * g ^ (3 / 2 : ℝ) + 2 * d * g ^ (1 / 2 : ℝ)) ^ 2 ≤
      24 * (g ^ 2 + g ^ 3 + d ^ 3) := by
  have hthreehalf : (g ^ (3 / 2 : ℝ)) ^ 2 = g ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hg]
    norm_num
  have hhalf : (g ^ (1 / 2 : ℝ)) ^ 2 = g := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hg]
    norm_num
  have hcauchy : (g / 2 + 2 * g ^ (3 / 2 : ℝ) + 2 * d * g ^ (1 / 2 : ℝ)) ^ 2 ≤
      3 * ((g / 2) ^ 2 + (2 * g ^ (3 / 2 : ℝ)) ^ 2 +
        (2 * d * g ^ (1 / 2 : ℝ)) ^ 2) := by
    nlinarith [sq_nonneg (g / 2 - 2 * g ^ (3 / 2 : ℝ)),
      sq_nonneg (g / 2 - 2 * d * g ^ (1 / 2 : ℝ)),
      sq_nonneg (2 * g ^ (3 / 2 : ℝ) - 2 * d * g ^ (1 / 2 : ℝ))]
  have hprod := sq_mul_le_sum_cubes hd hg
  have hsqproduct : (2 * d * g ^ (1 / 2 : ℝ)) ^ 2 = 4 * d ^ 2 * g := by
    calc
      _ = 4 * d ^ 2 * (g ^ (1 / 2 : ℝ)) ^ 2 := by ring
      _ = _ := by rw [hhalf]
  rw [hsqproduct] at hcauchy
  nlinarith [sq_nonneg g, pow_nonneg hg 3, pow_nonneg hd 3]

/-- A nonnegative number squared is bounded by the two-thirds power of any upper bound
for its cube. -/
theorem square_le_twoThirds_of_cube_le {a G : ℝ} (ha : 0 ≤ a) (_hG : 0 ≤ G)
    (hcube : a ^ 3 ≤ G) : a ^ 2 ≤ G ^ (2 / 3 : ℝ) := by
  have h := Real.rpow_le_rpow (pow_nonneg ha 3) hcube (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have heq : (a ^ 3) ^ (2 / 3 : ℝ) = a ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  rwa [heq] at h

/-- The actual unforced CKN solution class satisfies a squared inner energy estimate,
with no assumed energy-decay or regularity conclusion. -/
theorem unforced_half_alpha_sq_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hdom : closure (parabolicCylinder z.1 z.2 ρ) ⊆ CKN.spaceTimeSet Ω I) :
    CKN.alpha u z (ρ / 2) ^ 2 ≤
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
  have hbound : CKN.alpha u z (ρ / 2) ≤ CKN.Core.Endgame.startGammaConstant *
      (CKN.gamma u z ρ / 2 + 2 * CKN.gamma u z ρ ^ (3 / 2 : ℝ) +
        2 * CKN.delta p z ρ * CKN.gamma u z ρ ^ (1 / 2 : ℝ)) := by
    nlinarith only [hcacc, hβ]
  calc
    _ ≤ (CKN.Core.Endgame.startGammaConstant *
        (CKN.gamma u z ρ / 2 + 2 * CKN.gamma u z ρ ^ (3 / 2 : ℝ) +
          2 * CKN.delta p z ρ * CKN.gamma u z ρ ^ (1 / 2 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ hα hbound 2
    _ = CKN.Core.Endgame.startGammaConstant ^ 2 *
        (CKN.gamma u z ρ / 2 + 2 * CKN.gamma u z ρ ^ (3 / 2 : ℝ) +
          2 * CKN.delta p z ρ * CKN.gamma u z ρ ^ (1 / 2 : ℝ)) ^ 2 := by ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (half_gamma_display_sq_le hg hd)
        (sq_nonneg CKN.Core.Endgame.startGammaConstant)
      nlinarith only [h]

/-- Both shifted backward cubic quantities are controlled by the actual symmetric charge. -/
theorem energyShifted_gamma_delta_cubes_le_charge
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ CKN.spaceTimeSet Ω I) :
    CKN.gamma u (energyShiftedTop z r) (r / 2) ^ 3 +
      CKN.delta p (energyShiftedTop z r) (r / 2) ^ 3 ≤
        8 * rawSymmetricL3Activity u p z r := by
  let M := ∫⁻ a in rawSymmetricL3Cylinder z r,
    ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
      ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)
  have hfinite : M < ⊤ := raw_symmetric_velocity_pressure_integral_lt_top hsol hr hdom
  have hsub := energyShiftedOuter_subset_symmetric z hr
  have hvel : (∫⁻ a in parabolicCylinder z.1 (energyShiftedTop z r).2 (r / 2),
      ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ)) ≤ M := by
    calc
      _ ≤ ∫⁻ a in rawSymmetricL3Cylinder z r,
          ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) := lintegral_mono_set hsub
      _ ≤ M := lintegral_mono fun _ ↦ le_add_of_nonneg_right bot_le
  have hpress : (∫⁻ a in parabolicCylinder z.1 (energyShiftedTop z r).2 (r / 2),
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
  have hγ : CKN.gamma u (energyShiftedTop z r) (r / 2) ^ 3 ≤
      4 * rawSymmetricL3Activity u p z r := by
    calc
      _ = (r / 2) ^ (-2 : ℝ) *
          (∫⁻ a in parabolicCylinder z.1 (energyShiftedTop z r).2 (r / 2),
            ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ)).toReal :=
        CKN.gamma_cube_eq u (energyShiftedTop z r) (r / 2) (by positivity)
      _ = 4 * r⁻¹ ^ 2 *
          (∫⁻ a in parabolicCylinder z.1 (energyShiftedTop z r).2 (r / 2),
            ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ)).toReal := by rw [hscale]
      _ ≤ 4 * r⁻¹ ^ 2 * M.toReal :=
        mul_le_mul_of_nonneg_left hvelreal (by positivity)
      _ = _ := by unfold rawSymmetricL3Activity; dsimp [M]; ring
  have hδ : CKN.delta p (energyShiftedTop z r) (r / 2) ^ 3 ≤
      4 * rawSymmetricL3Activity u p z r := by
    calc
      _ = (r / 2) ^ (-2 : ℝ) *
          (∫⁻ a in parabolicCylinder z.1 (energyShiftedTop z r).2 (r / 2),
            ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)).toReal :=
        CKN.delta_cube_eq p (energyShiftedTop z r) (r / 2) (by positivity)
      _ = 4 * r⁻¹ ^ 2 *
          (∫⁻ a in parabolicCylinder z.1 (energyShiftedTop z r).2 (r / 2),
            ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)).toReal := by rw [hscale]
      _ ≤ 4 * r⁻¹ ^ 2 * M.toReal :=
        mul_le_mul_of_nonneg_left hpressreal (by positivity)
      _ = _ := by unfold rawSymmetricL3Activity; dsimp [M]; ring
  linarith only [hγ, hδ]

/-- The factor eight in the cubic comparison becomes four at the two-thirds power. -/
theorem eight_mul_twoThirds {G : ℝ} (hG : 0 ≤ G) :
    (8 * G) ^ (2 / 3 : ℝ) = 4 * G ^ (2 / 3 : ℝ) := by
  have h8 : (8 : ℝ) ^ (2 / 3 : ℝ) = 4 := by
    calc
      _ = ((2 : ℝ) ^ 3) ^ (2 / 3 : ℝ) := by norm_num
      _ = (2 : ℝ) ^ ((3 : ℝ) * (2 / 3)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ = 4 := by norm_num
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hG, h8]

/-- The inner squared energy is controlled by the actual symmetric charge. -/
theorem unforced_shifted_alpha_sq_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ CKN.spaceTimeSet Ω I) :
    CKN.alpha u (energyShiftedTop z r) (r / 4) ^ 2 ≤
      192 * CKN.Core.Endgame.startGammaConstant ^ 2 *
        (rawSymmetricL3Activity u p z r ^ (2 / 3 : ℝ) + rawSymmetricL3Activity u p z r) := by
  let G := rawSymmetricL3Activity u p z r
  have hG : 0 ≤ G := rawSymmetricL3Activity_nonneg _ _ _ _
  have hγ := CKN.gamma_nonneg u (energyShiftedTop z r) (by positivity : 0 ≤ r / 2)
  have hδ := CKN.delta_nonneg p (energyShiftedTop z r) (by positivity : 0 ≤ r / 2)
  have hcubes := energyShifted_gamma_delta_cubes_le_charge hsol hr hdom
  have hγcube : CKN.gamma u (energyShiftedTop z r) (r / 2) ^ 3 ≤ 8 * G :=
    (le_add_of_nonneg_right (pow_nonneg hδ 3)).trans hcubes
  have hγsq := square_le_twoThirds_of_cube_le hγ (by positivity : 0 ≤ 8 * G) hγcube
  rw [eight_mul_twoThirds hG] at hγsq
  have houter := (energyShiftedOuter_closure_subset_symmetric z hr).trans hdom
  have hα := unforced_half_alpha_sq_bound (z := energyShiftedTop z r) hsol
    (by positivity : 0 < r / 2) houter
  have hquarter : (r / 2) / 2 = r / 4 := by ring
  rw [hquarter] at hα
  calc
    _ ≤ 24 * CKN.Core.Endgame.startGammaConstant ^ 2 *
        (CKN.gamma u (energyShiftedTop z r) (r / 2) ^ 2 +
          CKN.gamma u (energyShiftedTop z r) (r / 2) ^ 3 +
          CKN.delta p (energyShiftedTop z r) (r / 2) ^ 3) := hα
    _ ≤ 24 * CKN.Core.Endgame.startGammaConstant ^ 2 * (4 * G ^ (2 / 3 : ℝ) + 8 * G) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith only [hγsq, hcubes]
    _ ≤ _ := by
      have hpow : 0 ≤ G ^ (2 / 3 : ℝ) := Real.rpow_nonneg hG _
      nlinarith [sq_nonneg CKN.Core.Endgame.startGammaConstant]

/-- A universal positive coefficient for the shifted energy estimate. -/
def energyChargeConstant : ℝ := 1 + 48 * CKN.Core.Endgame.startGammaConstant ^ 2

/-- The energy-charge coefficient is strictly positive. -/
theorem energyChargeConstant_pos : 0 < energyChargeConstant := by
  unfold energyChargeConstant
  positivity

/-- The actual shifted time-slice energy at radius `r/512` is controlled by the symmetric
charge at radius `r`. This supplies the energy input for the mixed pressure-velocity decay. -/
theorem unforced_shifted_energy_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ CKN.spaceTimeSet Ω I) :
    timeSliceEnergyEssSup z.1 (energyShiftedTop z r).2 (r / 512)
        (fun a ↦ vec3EuclideanNorm (u a)) ≤
      ENNReal.ofReal (energyChargeConstant * r *
        (rawSymmetricL3Activity u p z r ^ (2 / 3 : ℝ) + rawSymmetricL3Activity u p z r)) := by
  have hG := rawSymmetricL3Activity_nonneg u p z r
  have hsum : 0 ≤ rawSymmetricL3Activity u p z r ^ (2 / 3 : ℝ) +
      rawSymmetricL3Activity u p z r := add_nonneg (Real.rpow_nonneg hG _) hG
  have houter := (energyShiftedOuter_closure_subset_symmetric z hr).trans hdom
  have houterfin := CKN.sws_timeSliceEnergyEssSup_lt_top
    (z := energyShiftedTop z r) hsol (by positivity : 0 < r / 2) houter
  have hinnermono := timeSliceEnergyEssSup_mono_radius (x := z.1)
    (t := (energyShiftedTop z r).2) (by positivity : 0 ≤ r / 4)
    (by linarith : r / 4 ≤ r / 2) (fun a ↦ vec3EuclideanNorm (u a))
  have hinnerfin := (hinnermono.trans_lt houterfin).ne
  have hα := unforced_shifted_alpha_sq_bound hsol hr hdom
  have hreal : (r / 4) * CKN.alpha u (energyShiftedTop z r) (r / 4) ^ 2 ≤
      energyChargeConstant * r *
        (rawSymmetricL3Activity u p z r ^ (2 / 3 : ℝ) + rawSymmetricL3Activity u p z r) := by
    calc
      _ ≤ (r / 4) * (192 * CKN.Core.Endgame.startGammaConstant ^ 2 *
          (rawSymmetricL3Activity u p z r ^ (2 / 3 : ℝ) + rawSymmetricL3Activity u p z r)) :=
        mul_le_mul_of_nonneg_left hα (by positivity)
      _ = 48 * CKN.Core.Endgame.startGammaConstant ^ 2 * r *
          (rawSymmetricL3Activity u p z r ^ (2 / 3 : ℝ) + rawSymmetricL3Activity u p z r) := by
        ring
      _ ≤ _ := by
        have hC : 48 * CKN.Core.Endgame.startGammaConstant ^ 2 ≤ energyChargeConstant := by
          unfold energyChargeConstant
          linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hr.le) hsum
  calc
    _ ≤ timeSliceEnergyEssSup z.1 (energyShiftedTop z r).2 (r / 4)
        (fun a ↦ vec3EuclideanNorm (u a)) :=
      timeSliceEnergyEssSup_mono_radius (by positivity : 0 ≤ r / 512)
        (by linarith : r / 512 ≤ r / 4) _
    _ = ENNReal.ofReal ((r / 4) * CKN.alpha u (energyShiftedTop z r) (r / 4) ^ 2) :=
      CKN.timeSliceEnergyEssSup_eq_ofReal_alpha_sq u (energyShiftedTop z r)
        (by positivity : 0 < r / 4) hinnerfin
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end FluidSingularSets
