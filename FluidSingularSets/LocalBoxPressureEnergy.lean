-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalBoxPressureForces
public import FluidSingularSets.ActualPressureCurve
public import FluidSingularSets.SliceLpMoments

/-!
# Pressure energy forces on arbitrary local boxes

Local weak Sobolev bounds and a finite spatial cover give the actual pressure
energy class on a full local carrier. The original time interval is retained.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance localBoxPressureEnergyForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

set_option maxHeartbeats 1000000 in
/-- Weak Sobolev gives the original pressure its local spatial energy class. -/
theorem raw_pressure_energy_dual_bound
    {x₀ : Vec3} {r t : ℝ} (hr : 0 < r) {p : ParabolicPoint → ℝ} {Dp : ParabolicPoint → Vec3}
    (hp : MemLp (fun x ↦ p (x, t)) (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (vec3Ball x₀ (2 * r))))
    (hDp : MemLp (fun x ↦ Dp (x, t)) (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (vec3Ball x₀ (2 * r))))
    (hweak : HasWeakGradientOn (vec3Ball x₀ (2 * r))
      (fun x ↦ p (x, t)) (fun x ↦ Dp (x, t))) :
    MemLp ((fun x ↦ p (x, t))) 2 (volume.restrict (vec3Ball x₀ r)) ∧
      eLpNorm ((fun x ↦ p (x, t))) 2 (volume.restrict (vec3Ball x₀ r)) ≤
        pressureEnergyDualCoefficient x₀ r *
          (eLpNorm (fun x ↦ Dp (x, t)) (ENNReal.ofReal (5 / 4 : ℝ))
            (volume.restrict (vec3Ball x₀ (2 * r))) +
          eLpNorm (fun x ↦ p (x, t)) (ENNReal.ofReal (5 / 4 : ℝ))
            (volume.restrict (vec3Ball x₀ (2 * r)))) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball x₀ (2 * r))
  let ν : Measure Vec3 := volume.restrict (vec3Ball x₀ r)
  let : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp only [μ, Measure.restrict_apply_univ]
    exact CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top
  let : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    simp only [ν, Measure.restrict_apply_univ]
    exact CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top
  have hdown : (6 / 5 : ℝ≥0∞) ≤ ENNReal.ofReal (5 / 4 : ℝ) := by
    have hsix : (6 / 5 : ℝ≥0∞) = ENNReal.ofReal (6 / 5 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [hsix]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hpdown := hp.mono_exponent hdown
  have hDpdown := hDp.mono_exponent hdown
  have hB := euclideanBall_eq_vec3Ball (x₀ := x₀) (by positivity : 0 < 2 * r)
  have hB₁ := euclideanBall_eq_vec3Ball (x₀ := x₀) hr
  have hs := weakPressureEnergySobolevBall (x₀ := x₀)
    (u := fun x ↦ p (x, t)) (Du := fun x ↦ Dp (x, t)) hr (by simpa only [hB] using hpdown)
    (by simpa only [hB] using hDpdown) (by simpa only [hB] using hweak)
  simp only [hB, hB₁, lpNormOn, weakGradientLpNormOn] at hs
  have hpeq := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hdown hp.aestronglyMeasurable
  have hDeq := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hdown hDp.aestronglyMeasurable
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_ofReal
    (by norm_num : (0 : ℝ) ≤ 5 / 4), Measure.restrict_apply_univ] at hpeq hDeq
  have hraw : eLpNorm (fun x ↦ p (x, t)) 2 ν ≤
      pressureEnergySobolevConstant *
        (1 + (Real.toNNReal (32 / r) : ℝ≥0∞)) *
          volume (vec3Ball x₀ (2 * r)) ^ (1 / 30 : ℝ) *
            (eLpNorm (fun x ↦ Dp (x, t)) (ENNReal.ofReal (5 / 4 : ℝ)) μ +
              eLpNorm (fun x ↦ p (x, t)) (ENNReal.ofReal (5 / 4 : ℝ)) μ) := by
    apply hs.trans
    calc
      _ ≤ pressureEnergySobolevConstant *
          (eLpNorm (fun x ↦ Dp (x, t)) (ENNReal.ofReal (5 / 4 : ℝ)) μ *
            volume (vec3Ball x₀ (2 * r)) ^ (1 / 30 : ℝ) +
          (Real.toNNReal (32 / r) : ℝ≥0∞) *
            (eLpNorm (fun x ↦ p (x, t)) (ENNReal.ofReal (5 / 4 : ℝ)) μ *
              volume (vec3Ball x₀ (2 * r)) ^ (1 / 30 : ℝ))) := by gcongr
      _ ≤ _ := by
        let a := eLpNorm (fun x ↦ Dp (x, t)) (ENNReal.ofReal (5 / 4 : ℝ)) μ
        let b := eLpNorm (fun x ↦ p (x, t)) (ENNReal.ofReal (5 / 4 : ℝ)) μ
        let k : ℝ≥0∞ := (Real.toNNReal (32 / r) : ℝ≥0∞)
        let w := volume (vec3Ball x₀ (2 * r)) ^ (1 / 30 : ℝ)
        have hadd : a + k * b ≤ (1 + k) * (a + b) := by
          calc
            _ ≤ (a + b) + k * (a + b) :=
              add_le_add le_self_add (mul_le_mul_of_nonneg_left le_add_self (by positivity))
            _ = _ := by ring
        convert mul_le_mul_of_nonneg_left hadd
          (by positivity : 0 ≤ pressureEnergySobolevConstant * w) using 1 <;> ring
  have hpinner : MemLp (fun x ↦ p (x, t)) 2 ν := by
    apply memLp_iff.mpr
    apply hraw.trans_lt
    apply ENNReal.mul_lt_top
    · apply ENNReal.mul_lt_top
      · exact ENNReal.mul_lt_top pressureEnergySobolevConstant_ne_top.lt_top (by finiteness)
      · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top.ne
    · exact ENNReal.add_lt_top.mpr ⟨hDp.eLpNorm_lt_top, hp.eLpNorm_lt_top⟩
  refine ⟨hpinner, ?_⟩
  apply hraw.trans
  unfold pressureEnergyDualCoefficient
  calc
    _ ≤ 2 * (pressureEnergySobolevConstant *
        (1 + (Real.toNNReal (32 / r) : ℝ≥0∞)) *
          volume (vec3Ball x₀ (2 * r)) ^ (1 / 30 : ℝ) *
            (eLpNorm (fun x ↦ Dp (x, t)) (ENNReal.ofReal (5 / 4 : ℝ)) μ +
              eLpNorm (fun x ↦ p (x, t)) (ENNReal.ofReal (5 / 4 : ℝ)) μ)) :=
      le_mul_of_one_le_left (by positivity) (by norm_num)
    _ = _ := by ring

/-- Actual joint moments control the raw spatial energy norm in time. -/
theorem raw_pressure_energy_dual_time_moment_lt_top
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) {J : Set ℝ}
    {p : ParabolicPoint → ℝ} {Dp : ParabolicPoint → Vec3}
    (hp : MemLp p (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (vec3Ball x₀ (2 * r) ×ˢ J)))
    (hDp : MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (vec3Ball x₀ (2 * r) ×ˢ J)))
    (hweak : ∀ᵐ t ∂volume.restrict J, HasWeakGradientOn (vec3Ball x₀ (2 * r))
      (fun x ↦ p (x, t)) (fun x ↦ Dp (x, t))) :
    (∀ᵐ t ∂volume.restrict J,
      MemLp ((fun x ↦ p (x, t))) 2 (volume.restrict (vec3Ball x₀ r))) ∧
    (∫⁻ t in J, eLpNorm ((fun x ↦ p (x, t))) 2
      (volume.restrict (vec3Ball x₀ r)) ^ (5 / 4 : ℝ)) < ∞ := by
  have hps := spatial_memLp_ae_of_joint_memLp (by norm_num : (0 : ℝ) < 5 / 4) hp
  have hDs := spatial_memLp_ae_of_joint_memLp (by norm_num : (0 : ℝ) < 5 / 4) hDp
  have hpt := lintegral_spatial_eLpNorm_rpow_lt_top (by norm_num : (0 : ℝ) < 5 / 4) hp
  have hDt := lintegral_spatial_eLpNorm_rpow_lt_top (by norm_num : (0 : ℝ) < 5 / 4) hDp
  have hb : ∀ᵐ t ∂volume.restrict J,
      MemLp ((fun x ↦ p (x, t))) 2 (volume.restrict (vec3Ball x₀ r)) ∧
      eLpNorm ((fun x ↦ p (x, t))) 2 (volume.restrict (vec3Ball x₀ r)) ≤
        pressureEnergyDualCoefficient x₀ r *
          (eLpNorm (fun x ↦ Dp (x, t)) (ENNReal.ofReal (5 / 4 : ℝ))
            (volume.restrict (vec3Ball x₀ (2 * r))) +
          eLpNorm (fun x ↦ p (x, t)) (ENNReal.ofReal (5 / 4 : ℝ))
            (volume.restrict (vec3Ball x₀ (2 * r)))) := by
    filter_upwards [hps, hDs, hweak] with t ht hDt hwt
    exact raw_pressure_energy_dual_bound hr ht hDt hwt
  refine ⟨hb.mono fun _ ht ↦ ht.1, ?_⟩
  let A : ℝ → ℝ≥0∞ := fun t ↦ eLpNorm (fun x ↦ Dp (x, t)) (ENNReal.ofReal (5 / 4 : ℝ))
    (volume.restrict (vec3Ball x₀ (2 * r)))
  let B : ℝ → ℝ≥0∞ := fun t ↦ eLpNorm (fun x ↦ p (x, t)) (ENNReal.ofReal (5 / 4 : ℝ))
    (volume.restrict (vec3Ball x₀ (2 * r)))
  let K : ℝ≥0∞ := pressureEnergyDualCoefficient x₀ r ^ (5 / 4 : ℝ) * 2 ^ (1 / 4 : ℝ)
  have hK : K ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (pressureEnergyDualCoefficient_ne_top x₀ r)).ne
    (by finiteness)
  have hle : (∫⁻ t in J, eLpNorm ((fun x ↦ p (x, t))) 2
      (volume.restrict (vec3Ball x₀ r)) ^ (5 / 4 : ℝ)) ≤
      K * ((∫⁻ t in J, A t ^ (5 / 4 : ℝ)) + ∫⁻ t in J, B t ^ (5 / 4 : ℝ)) := by
    calc
      _ ≤ ∫⁻ t in J, K * (A t ^ (5 / 4 : ℝ) + B t ^ (5 / 4 : ℝ)) := by
        apply lintegral_mono_ae
        filter_upwards [hb] with t ht
        calc
          _ ≤ (pressureEnergyDualCoefficient x₀ r * (A t + B t)) ^ (5 / 4 : ℝ) :=
            ENNReal.rpow_le_rpow ht.2 (by norm_num)
          _ = pressureEnergyDualCoefficient x₀ r ^ (5 / 4 : ℝ) *
              (A t + B t) ^ (5 / 4 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
          _ ≤ K * (A t ^ (5 / 4 : ℝ) + B t ^ (5 / 4 : ℝ)) := by
            have h := ENNReal.rpow_add_le_mul_rpow_add_rpow (A t) (B t)
              (by norm_num : (1 : ℝ) ≤ 5 / 4)
            norm_num only [show (5 / 4 : ℝ) - 1 = 1 / 4 by norm_num] at h
            exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by dsimp [K]; ring)
      _ = _ := by
        rw [lintegral_const_mul' K _ hK, lintegral_add_right']
        have hpm : AEMeasurable (fun w : Vec3 × ℝ ↦ p w)
            (volume.restrict (vec3Ball x₀ (2 * r) ×ˢ J)) := by
          rw [Measure.volume_eq_prod,
            ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
          exact hp.aestronglyMeasurable.aemeasurable
        exact (CKN.Core.Step4.origin_time_slice_norm_aemeasurable
          (by norm_num : (0 : ℝ) < 5 / 4) hpm).pow_const (5 / 4 : ℝ)
  exact hle.trans_lt (ENNReal.mul_lt_top hK.lt_top (ENNReal.add_lt_top.mpr ⟨hDt, hpt⟩))

/-- A finite measurable cover bounds the genuine spatial energy norm by the
sum of its patch norms. Overlaps are allowed and no partition is selected. -/
theorem memLp_two_of_finite_spatial_cover
    {A E ι : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    [Fintype ι] {μ : Measure A} {B : Set A} {V : ι → Set A} {f : A → E}
    (hB : MeasurableSet B) (hV : ∀ k, MeasurableSet (V k))
    (hcover : B ⊆ ⋃ k, V k) (hf : AEStronglyMeasurable f (μ.restrict B))
    (hfs : ∀ k, MemLp f 2 (μ.restrict (V k))) :
    MemLp f 2 (μ.restrict B) ∧
      eLpNorm f 2 (μ.restrict B) ≤ ∑ k, eLpNorm f 2 (μ.restrict (V k)) := by
  classical
  let F : ι → A → E := fun k ↦ (V k).indicator f
  have hF (k : ι) : MemLp (F k) 2 μ :=
    (memLp_indicator_iff_restrict (hV k)).mpr (hfs k)
  have hsum : MemLp (fun x ↦ ∑ k, ‖F k x‖) 2 μ :=
    memLp_finsetSum Finset.univ (fun k _ ↦ (hF k).norm)
  have hmajor : ∀ᵐ x ∂μ.restrict B, ‖f x‖ ≤ ‖∑ k, ‖F k x‖‖ := by
    filter_upwards [ae_restrict_mem hB] with x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover hx)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ ↦ norm_nonneg (F k x))]
    have heq : ‖f x‖ = ‖F k x‖ := by simp only [F, indicator_of_mem hk]
    rw [heq]
    exact Finset.single_le_sum (fun k _ ↦ norm_nonneg (F k x)) (Finset.mem_univ k)
  refine ⟨(hsum.mono_measure Measure.restrict_le_self).of_le hf hmajor, ?_⟩
  calc
    _ ≤ eLpNorm (fun x ↦ ∑ k, ‖F k x‖) 2 (μ.restrict B) := eLpNorm_mono_ae hf hmajor
    _ ≤ ∑ k, eLpNorm (fun x ↦ ‖F k x‖) 2 (μ.restrict B) := by
      have heq : (fun x ↦ ∑ k, ‖F k x‖) = ∑ k, fun x ↦ ‖F k x‖ := by
        funext x
        simp only [Finset.sum_apply]
      rw [heq]
      exact eLpNorm_sum_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ ∑ k, eLpNorm (fun x ↦ ‖F k x‖) 2 μ :=
      Finset.sum_le_sum fun k _ ↦ eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [eLpNorm_norm _ (hF k).aestronglyMeasurable]
      exact eLpNorm_indicator_eq_eLpNorm_restrict (hV k)

/-- Genuine patch energy-class curves combine across a finite spatial cover. -/
theorem pressure_energy_curve_of_finite_spatial_cover
    {ι : Type*} [Fintype ι] {B : Set Vec3} {V : ι → Set Vec3} {J : Set ℝ}
    [IsFiniteMeasure ((volume : Measure Vec3).restrict B)]
    {F : Vec3 × ℝ → ℝ} (hB : MeasurableSet B) (hV : ∀ k, MeasurableSet (V k))
    (hcover : B ⊆ ⋃ k, V k)
    (hF : AEStronglyMeasurable F ((volume.restrict B).prod (volume.restrict J)))
    (hgood : ∀ k, ∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ F (x, t)) 2 (volume.restrict (V k)))
    (hclasses : ∀ k, MemLp
      (actualSliceLp (μ := volume.restrict (V k)) (p := 2) F)
      (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict J)) :
    (∀ᵐ t ∂volume.restrict J, MemLp (fun x ↦ F (x, t)) 2 (volume.restrict B)) ∧
    MemLp (actualSliceLp (μ := volume.restrict B) (p := 2) F)
      (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict J) := by
  classical
  let C (k : ι) := actualSliceLp (μ := volume.restrict (V k)) (p := 2) F
  have hbound : ∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ F (x, t)) 2 (volume.restrict B) ∧
        eLpNorm (fun x ↦ F (x, t)) 2 (volume.restrict B) ≤
          ∑ k, ‖C k t‖ₑ := by
    filter_upwards [hF.prodMk_right, ae_all_iff.mpr hgood] with t ht hgt
    have hc := memLp_two_of_finite_spatial_cover hB hV hcover ht hgt
    refine ⟨hc.1, hc.2.trans_eq ?_⟩
    apply Finset.sum_congr rfl
    intro k _
    exact (actualSliceLp_enorm F t (hgt k)).symm
  let S : ℝ → ℝ := fun t ↦ ∑ k, ‖C k t‖
  have hS : MemLp S (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict J) :=
    memLp_finsetSum Finset.univ (fun k _ ↦ (hclasses k).norm)
  refine ⟨hbound.mono fun _ ht ↦ ht.1, ?_⟩
  apply hS.of_le_enorm (aestronglyMeasurable_actualSliceLp hF (by norm_num))
  filter_upwards [hbound] with t ht
  rw [actualSliceLp_enorm F t ht.1]
  apply ht.2.trans_eq
  dsimp [S]
  rw [Real.enorm_eq_ofReal (Finset.sum_nonneg fun k _ ↦ norm_nonneg (C k t)),
    ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ norm_nonneg (C k t))]
  apply Finset.sum_congr rfl
  intro k _
  exact (ofReal_norm (C k t)).symm

set_option maxHeartbeats 1000000 in
/-- Original suitability gives the full local carrier a spatial `L²` pressure
class and its genuine `5/4` time class, with the time interval unchanged. -/
theorem suitable_pressure_energy_curve_localBox
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I B J) :
    (∀ᵐ t ∂volume.restrict J, MemLp (fun x ↦ p (x, t)) 2 (volume.restrict B)) ∧
    MemLp (actualSliceLp (μ := volume.restrict B) (p := 2)
      (fun z : Vec3 × ℝ ↦ p z)) (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict J) := by
  classical
  obtain ⟨W, _δ, _hδ, hW, hBW, hWc, hWΩ, _hballs⟩ :=
    exists_open_between_of_isCompact hbox.2.1 hsol.1 hbox.2.2.1
  have hWbox : localBox Ω I W J := ⟨hW, hWc, hWΩ, hbox.2.2.2⟩
  obtain ⟨Dp, _hDpm, hDp, hDw⟩ :=
    exists_suitable_pressure_gradient_memLp_localBox hsol hWbox
  let K : Set ParabolicPoint := closure W ×ˢ closure J
  have hK : IsCompact K := parabolicHomeomorph.isCompact_preimage.mpr
    (hWc.prod hbox.2.2.2.2.1)
  let : IsFiniteMeasure (volume.restrict (spaceTimeSet W J)) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono (Set.prod_mono subset_closure subset_closure)).trans_lt
        hK.measure_lt_top).ne
  have hp : MemLp p (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (spaceTimeSet W J)) :=
    (hsol.toData.memLp_pressure hWbox).mono_exponent (by norm_num)
  choose R hR hRW using fun x : closure B ↦ exists_vec3Ball_subset_of_isOpen hW (hBW x.2)
  let V (x : closure B) := vec3Ball x.1 (R x / 2)
  have hcover : closure B ⊆ ⋃ x : closure B, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_vec3Ball_self (div_pos (hR ⟨x, hx⟩) (by norm_num))⟩
  obtain ⟨s, hs⟩ := hbox.2.1.elim_finite_subcover V (fun _ ↦ isOpen_vec3Ball _ _) hcover
  let T (k : s) := vec3Ball k.1.1 (R k.1)
  have hT (k : s) : T k ×ˢ J ⊆ spaceTimeSet W J := prod_mono (hRW k.1) Subset.rfl
  have hpT (k : s) : MemLp p (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (T k ×ˢ J)) :=
    hp.mono_measure (Measure.restrict_mono_set volume (hT k))
  have hDpT (k : s) : MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (T k ×ˢ J)) :=
    hDp.mono_measure (Measure.restrict_mono_set volume (hT k))
  have hweakT (k : s) : ∀ᵐ t ∂volume.restrict J,
      HasWeakGradientOn (T k) (fun x ↦ p (x, t)) (fun x ↦ Dp (x, t)) := by
    filter_upwards [hDw] with t ht
    exact fun i ↦ (ht i).2.restrict (isOpen_vec3Ball _ _) (hRW k.1)
  have hpatch (k : s) := raw_pressure_energy_dual_time_moment_lt_top
    (x₀ := k.1.1) (r := R k.1 / 2) (div_pos (hR k.1) (by norm_num)) (J := J)
    (by simpa only [show 2 * (R k.1 / 2) = R k.1 by ring] using hpT k)
    (by simpa only [show 2 * (R k.1 / 2) = R k.1 by ring] using hDpT k)
    (by simpa only [show 2 * (R k.1 / 2) = R k.1 by ring] using hweakT k)
  have hclass (k : s) : MemLp
      (actualSliceLp (μ := volume.restrict (V k.1)) (p := 2) (fun z : Vec3 × ℝ ↦ p z))
      (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict J) := by
    have hsub : V k.1 ×ˢ J ⊆ spaceTimeSet W J :=
      prod_mono ((vec3Ball_mono (by have := hR k.1; linarith)).trans
        (hRW k.1)) Subset.rfl
    have hm : AEStronglyMeasurable (fun z : Vec3 × ℝ ↦ p z)
        ((volume.restrict (V k.1)).prod (volume.restrict J)) := by
      rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
      exact hp.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume hsub)
    apply actualSliceLp_memLp_of_mixed_moment hm (by norm_num)
      (by norm_num) ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 5 / 4)] using (hpatch k).2
  let : IsFiniteMeasure ((volume : Measure Vec3).restrict B) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top).ne
  have hpB : AEStronglyMeasurable (fun z : Vec3 × ℝ ↦ p z)
      ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact (hsol.toData.memLp_pressure hbox).aestronglyMeasurable
  apply pressure_energy_curve_of_finite_spatial_cover hbox.1.measurableSet
    (fun k : s ↦ (isOpen_vec3Ball _ _).measurableSet) (V := fun k : s ↦ V k.1) ?_ hpB
    (fun k ↦ (hpatch k).1) hclass
  intro x hx
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hs (subset_closure hx))
  obtain ⟨hks, hxk⟩ := mem_iUnion.mp hk
  exact mem_iUnion.mpr ⟨⟨k, hks⟩, hxk⟩

/-- Actual pressure on a full local ball has its centered spatial energy class
and finite `5/4` time moment without enlarging the time interval. -/
theorem suitable_centered_pressure_energy_dual_localBox
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ} {x₀ : Vec3} {r : ℝ} (hr : 0 < r)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball x₀ r) J) :
    (∀ᵐ t ∂volume.restrict J,
      MemLp (centeredPressureSlice p x₀ r t) 2 (volume.restrict (vec3Ball x₀ r))) ∧
    (∫⁻ t in J, eLpNorm (centeredPressureSlice p x₀ r t) 2
      (volume.restrict (vec3Ball x₀ r)) ^ (5 / 4 : ℝ)) < ∞ := by
  obtain ⟨hgood, hclass⟩ := suitable_pressure_energy_curve_localBox hsol hbox
  let μ : Measure Vec3 := volume.restrict (vec3Ball x₀ r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have hμpos : μ univ ≠ 0 := by
    simp only [μ, Measure.restrict_apply_univ]
    exact (volume_vec3Ball_pos hr).ne'
  have hmc := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (by norm_num) ENNReal.ofReal_ne_top hclass.eLpNorm_lt_top
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 5 / 4)] at hmc
  have hraw : (∫⁻ t in J, eLpNorm (fun x ↦ p (x, t)) 2 μ ^ (5 / 4 : ℝ)) < ∞ := by
    convert hmc using 1
    apply lintegral_congr_ae
    filter_upwards [hgood] with t ht
    rw [actualSliceLp_enorm (fun z : Vec3 × ℝ ↦ p z) t ht]
  have hbound : ∀ᵐ t ∂volume.restrict J,
      MemLp (centeredPressureSlice p x₀ r t) 2 μ ∧
        eLpNorm (centeredPressureSlice p x₀ r t) 2 μ ≤
          2 * eLpNorm (fun x ↦ p (x, t)) 2 μ := by
    filter_upwards [hgood] with t ht
    refine ⟨ht.sub (memLp_const _), ?_⟩
    have hh := centered_eLpNorm_le_two hμpos ht.aestronglyMeasurable
      (by constructor <;> norm_num : (2 : ℝ).HolderConjugate 2)
    rw [show centeredPressureSlice p x₀ r t =
      (fun x ↦ p (x, t) - average μ (fun y ↦ p (y, t))) by rfl]
    simpa only [ENNReal.ofReal_ofNat] using hh
  refine ⟨hbound.mono fun _ ht ↦ ht.1, ?_⟩
  calc
    _ ≤ ∫⁻ t in J, 2 ^ (5 / 4 : ℝ) *
        eLpNorm (fun x ↦ p (x, t)) 2 μ ^ (5 / 4 : ℝ) := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with t ht
      exact (ENNReal.rpow_le_rpow ht.2 (by norm_num)).trans_eq
        (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num))
    _ = 2 ^ (5 / 4 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ p (x, t)) 2 μ ^ (5 / 4 : ℝ)) :=
      lintegral_const_mul' _ _ (by finiteness)
    _ < ∞ := ENNReal.mul_lt_top (by finiteness) hraw

/-- The genuine pressure energy force has its actual `5/4` time class on any
local ball with the original time interval. -/
theorem suitable_pressure_energy_force_memLp_localBox
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ} {x₀ : Vec3} {r : ℝ} (hr : 0 < r)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball x₀ r) J) :
    MemLp (pressureEnergyForce p x₀ r) (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict J) :=
  memLp_pressureEnergyForce_of_time_moment (hsol.toData.memLp_pressure hbox).aestronglyMeasurable
    (suitable_centered_pressure_energy_dual_localBox hr hsol hbox).2

/-- The actual unit-ball mean-zero pressure curve has its genuine time class
on every original suitable local time interval. -/
theorem suitable_unitBall_actual_pressure_curve_memLp_localBox
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (unitBallActualPressureCurve p) (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict J) :=
  memLp_unitBallActualPressureCurve_of_time_moment
    (hsol.toData.memLp_pressure hbox).aestronglyMeasurable
    (suitable_centered_pressure_energy_dual_localBox (by norm_num) hsol hbox).2

end FluidSingularSets
