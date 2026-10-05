-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesTestPoincare
public import CKN.Foundation.Sobolev.WeakDerivative
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Actual zero-boundary velocities represented by Stokes energy gradients

The genuine compact smooth function submodule supplies linear gradient and velocity
maps. The proved test Poincare inequality extends the velocity map uniquely
along the dense gradient map to the actual energy completion. Genuine compact
test integration by parts passes to this extension by continuity.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Actual smooth compact function arrays form a genuine linear submodule. -/
def stokesCompactSmoothSubmodule (U : Set Vec3) : Submodule ℝ (Fin 3 → Vec3 → ℝ) where
  carrier f := ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j) ∧ HasCompactSupport (f j) ∧ tsupport (f j) ⊆ U
  zero_mem' := by
    intro j
    exact ⟨contDiff_const, HasCompactSupport.zero, by simp only [Pi.zero_apply,
      tsupport_zero, empty_subset]⟩
  add_mem' := by
    intro f g hf hg j
    exact ⟨(hf j).1.add (hg j).1, (hf j).2.1.add (hg j).2.1,
      (tsupport_add (f j) (g j)).trans (union_subset (hf j).2.2 (hg j).2.2)⟩
  smul_mem' := by
    intro c f hf j
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 ↦ c * f j x) ∧
      HasCompactSupport (fun x : Vec3 ↦ c * f j x) ∧
        tsupport (fun x : Vec3 ↦ c * f j x) ⊆ U
    refine ⟨contDiff_const.mul (hf j).1, ?_, ?_⟩
    · exact (hf j).2.1.mul_left (f := fun _ : Vec3 ↦ c)
    · exact (tsupport_mul_subset_right (f := fun _ : Vec3 ↦ c) (g := f j)).trans (hf j).2.2

/-- The actual linear source of compact smooth vector tests. -/
abbrev StokesSmoothTestSpace (U : Set Vec3) := stokesCompactSmoothSubmodule U

theorem stokesSmooth_component_contDiff {U : Set Vec3} (φ : StokesSmoothTestSpace U)
    (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (φ.val j) := (φ.property j).1

theorem stokesSmooth_component_compact {U : Set Vec3} (φ : StokesSmoothTestSpace U)
    (j : Fin 3) : HasCompactSupport (φ.val j) := (φ.property j).2.1

/-- Actual compact smooth functions represent genuine CKN tests. -/
def stokesSmoothToWeak {U : Set Vec3} (φ : StokesSmoothTestSpace U) :
    StokesVectorTest U := fun j ↦
  { toFun := φ.val j
    contDiff := stokesSmooth_component_contDiff φ j
    hasCompactSupport := stokesSmooth_component_compact φ j
    tsupport_subset := (φ.property j).2.2 }

/-- Every original genuine test belongs to the constructed linear smooth test space. -/
def stokesWeakToSmooth {U : Set Vec3} (φ : StokesVectorTest U) : StokesSmoothTestSpace U :=
  ⟨fun j ↦ φ j, fun j ↦ ⟨(φ j).contDiff, (φ j).hasCompactSupport, (φ j).tsupport_subset⟩⟩

theorem stokesSmoothToWeak_stokesWeakToSmooth {U : Set Vec3}
    (φ : StokesVectorTest U) :
    stokesSmoothToWeak (stokesWeakToSmooth φ) = φ := by
  funext j
  rfl

/-- The true spatial gradient respects addition of genuine smooth tests. -/
theorem stokesSmooth_gradient_add {U : Set Vec3}
    (φ ψ : StokesSmoothTestSpace U) :
    stokesTestGradient (stokesSmoothToWeak (φ + ψ)) =
      stokesTestGradient (stokesSmoothToWeak φ) + stokesTestGradient (stokesSmoothToWeak ψ) := by
  funext x
  ext ij
  change (fderiv ℝ (φ.val ij.2 + ψ.val ij.2) x) (basisVec ij.1) = _
  rw [fderiv_add
    ((stokesSmooth_component_contDiff φ ij.2).differentiable (by simp)).differentiableAt
    ((stokesSmooth_component_contDiff ψ ij.2).differentiable (by simp)).differentiableAt]
  rfl

/-- The true spatial gradient respects scalar multiplication of genuine smooth tests. -/
theorem stokesSmooth_gradient_smul {U : Set Vec3}
    (c : ℝ) (φ : StokesSmoothTestSpace U) :
    stokesTestGradient (stokesSmoothToWeak (c • φ)) =
      c • stokesTestGradient (stokesSmoothToWeak φ) := by
  funext x
  ext ij
  change (fderiv ℝ (c • φ.val ij.2) x) (basisVec ij.1) = _
  rw [fderiv_const_smul
    ((stokesSmooth_component_contDiff φ ij.2).differentiable (by simp)).differentiableAt]
  rfl

/-- The original compact-test gradient is a genuine linear map into actual `L²`. -/
def stokesSmoothGradient (U : Set Vec3) :
    StokesSmoothTestSpace U →ₗ[ℝ] StokesGradientL2 U where
  toFun φ := stokesTestGradientL2 (stokesSmoothToWeak φ)
  map_add' φ ψ := by
    apply Lp.ext
    filter_upwards [(stokesTestGradient_memLp (stokesSmoothToWeak (φ + ψ))).coeFn_toLp,
      (stokesTestGradient_memLp (stokesSmoothToWeak φ)).coeFn_toLp,
      (stokesTestGradient_memLp (stokesSmoothToWeak ψ)).coeFn_toLp,
      Lp.coeFn_add (stokesTestGradientL2 (stokesSmoothToWeak φ))
        (stokesTestGradientL2 (stokesSmoothToWeak ψ))] with x ha hφ hψ hadd
    change stokesTestGradientL2 (stokesSmoothToWeak (φ + ψ)) x = _ at ha
    change stokesTestGradientL2 (stokesSmoothToWeak φ) x = _ at hφ
    change stokesTestGradientL2 (stokesSmoothToWeak ψ) x = _ at hψ
    rw [ha, hadd]
    simp only [Pi.add_apply]
    rw [hφ, hψ]
    exact congrFun (stokesSmooth_gradient_add φ ψ) x
  map_smul' c φ := by
    apply Lp.ext
    filter_upwards [(stokesTestGradient_memLp (stokesSmoothToWeak (c • φ))).coeFn_toLp,
      (stokesTestGradient_memLp (stokesSmoothToWeak φ)).coeFn_toLp,
      Lp.coeFn_smul c (stokesTestGradientL2 (stokesSmoothToWeak φ))] with x ha hφ hsmul
    change stokesTestGradientL2 (stokesSmoothToWeak (c • φ)) x = _ at ha
    change stokesTestGradientL2 (stokesSmoothToWeak φ) x = _ at hφ
    rw [ha]
    simp only [RingHom.id_apply]
    rw [hsmul]
    simp only [Pi.smul_apply]
    rw [hφ]
    exact congrFun (stokesSmooth_gradient_smul c φ) x

/-- The original compact-test velocity is a genuine linear map into actual `L²`. -/
def stokesSmoothVelocity (U : Set Vec3) :
    StokesSmoothTestSpace U →ₗ[ℝ] Lp Vec3 2 (volume.restrict U) where
  toFun φ := stokesTestVelocityL2 (stokesSmoothToWeak φ)
  map_add' φ ψ := by
    have h : stokesTestVelocity (stokesSmoothToWeak (φ + ψ)) =
        stokesTestVelocity (stokesSmoothToWeak φ) +
          stokesTestVelocity (stokesSmoothToWeak ψ) := rfl
    apply Lp.ext
    filter_upwards [(stokesTestVelocity_memLp (stokesSmoothToWeak (φ + ψ))).coeFn_toLp,
      (stokesTestVelocity_memLp (stokesSmoothToWeak φ)).coeFn_toLp,
      (stokesTestVelocity_memLp (stokesSmoothToWeak ψ)).coeFn_toLp,
      Lp.coeFn_add (stokesTestVelocityL2 (stokesSmoothToWeak φ))
        (stokesTestVelocityL2 (stokesSmoothToWeak ψ))] with x ha hφ hψ hadd
    change stokesTestVelocityL2 (stokesSmoothToWeak (φ + ψ)) x = _ at ha
    change stokesTestVelocityL2 (stokesSmoothToWeak φ) x = _ at hφ
    change stokesTestVelocityL2 (stokesSmoothToWeak ψ) x = _ at hψ
    rw [ha, hadd]
    simp only [Pi.add_apply]
    rw [hφ, hψ]
    exact congrFun h x
  map_smul' c φ := by
    have h : stokesTestVelocity (stokesSmoothToWeak (c • φ)) =
        c • stokesTestVelocity (stokesSmoothToWeak φ) := rfl
    apply Lp.ext
    filter_upwards [(stokesTestVelocity_memLp (stokesSmoothToWeak (c • φ))).coeFn_toLp,
      (stokesTestVelocity_memLp (stokesSmoothToWeak φ)).coeFn_toLp,
      Lp.coeFn_smul c (stokesTestVelocityL2 (stokesSmoothToWeak φ))] with x ha hφ hsmul
    change stokesTestVelocityL2 (stokesSmoothToWeak (c • φ)) x = _ at ha
    change stokesTestVelocityL2 (stokesSmoothToWeak φ) x = _ at hφ
    rw [ha]
    simp only [RingHom.id_apply]
    rw [hsmul]
    simp only [Pi.smul_apply]
    rw [hφ]
    exact congrFun h x

/-- The gradient is valued in the actual zero-boundary energy completion. -/
def stokesSmoothEnergy (U : Set Vec3) :
    StokesSmoothTestSpace U →ₗ[ℝ] stokesGradientEnergySpace U :=
  (stokesSmoothGradient U).codRestrict _ (fun φ ↦
    stokesTestGradientL2_mem (stokesSmoothToWeak φ))

/-- The smooth gradient range is exactly the span used to define the energy completion. -/
theorem stokesSmoothGradient_range (U : Set Vec3) :
    (stokesSmoothGradient U).range =
      Submodule.span ℝ (range (stokesTestGradientL2 (U := U))) := by
  apply le_antisymm
  · rintro g ⟨φ, rfl⟩
    exact Submodule.subset_span ⟨stokesSmoothToWeak φ, rfl⟩
  · apply Submodule.span_le.mpr
    rintro g ⟨φ, rfl⟩
    exact ⟨stokesWeakToSmooth φ, by
      change stokesTestGradientL2 (stokesSmoothToWeak (stokesWeakToSmooth φ)) = _
      rw [stokesSmoothToWeak_stokesWeakToSmooth]⟩

/-- The actual smooth test gradients are dense in the genuine energy completion. -/
theorem stokesSmoothEnergy_dense (U : Set Vec3) :
    DenseRange (stokesSmoothEnergy U) := by
  intro v
  rw [closure_subtype]
  have himage : Subtype.val '' range (stokesSmoothEnergy U) = range (stokesSmoothGradient U) := by
    ext g
    constructor
    · rintro ⟨v, ⟨φ, rfl⟩, rfl⟩
      exact ⟨φ, rfl⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨stokesSmoothEnergy U φ, ⟨φ, rfl⟩, rfl⟩
  rw [himage]
  have hmem := v.property
  change v.val ∈ closure
    (Submodule.span ℝ (range (stokesTestGradientL2 (U := U))) :
      Set (StokesGradientL2 U)) at hmem
  rw [← stokesSmoothGradient_range U] at hmem
  exact hmem

/-- Actual test Poincare controls the velocity by its genuine dense energy image. -/
theorem stokesSmoothVelocity_norm_le {U : Set Vec3}
    (hU : MeasurableSet U) (hvol : volume U ≠ ∞) (φ : StokesSmoothTestSpace U) :
    ‖stokesSmoothVelocity U φ‖ ≤ (stokesTestPoincareConstant U).toReal *
      ‖stokesSmoothEnergy U φ‖ :=
  stokesTestVelocityL2_norm_le hU hvol (stokesSmoothToWeak φ)

/-- The genuine zero-boundary velocity reconstructed from its actual energy gradient. -/
def stokesEnergyVelocity (U : Set Vec3) :
    stokesGradientEnergySpace U →L[ℝ] Lp Vec3 2 (volume.restrict U) :=
  (stokesSmoothVelocity U).extendOfNorm (stokesSmoothEnergy U)

/-- The reconstruction agrees with every actual compactly supported smooth vector test. -/
theorem stokesEnergyVelocity_test {U : Set Vec3}
    (hU : MeasurableSet U) (hvol : volume U ≠ ∞) (φ : StokesVectorTest U) :
    stokesEnergyVelocity U (stokesEnergyTest φ) = stokesTestVelocityL2 φ := by
  have h := LinearMap.extendOfNorm_eq (f := stokesSmoothVelocity U)
    (e := stokesSmoothEnergy U) (stokesSmoothEnergy_dense U)
    ⟨_, stokesSmoothVelocity_norm_le hU hvol⟩ (stokesWeakToSmooth φ)
  have he : stokesSmoothEnergy U (stokesWeakToSmooth φ) = stokesEnergyTest φ := by
    apply Subtype.ext
    change stokesTestGradientL2 (stokesSmoothToWeak (stokesWeakToSmooth φ)) = _
    rw [stokesSmoothToWeak_stokesWeakToSmooth]
    rfl
  have hf : stokesSmoothVelocity U (stokesWeakToSmooth φ) = stokesTestVelocityL2 φ := by
    change stokesTestVelocityL2 (stokesSmoothToWeak (stokesWeakToSmooth φ)) = _
    rw [stokesSmoothToWeak_stokesWeakToSmooth]
  change stokesEnergyVelocity U (stokesSmoothEnergy U (stokesWeakToSmooth φ)) =
    stokesSmoothVelocity U (stokesWeakToSmooth φ) at h
  rw [he, hf] at h
  exact h

/-- The actual velocity reconstruction retains the genuine finite Poincare bound. -/
theorem stokesEnergyVelocity_norm_le {U : Set Vec3}
    (hU : MeasurableSet U) (hvol : volume U ≠ ∞) (v : stokesGradientEnergySpace U) :
    ‖stokesEnergyVelocity U v‖ ≤ (stokesTestPoincareConstant U).toReal * ‖v‖ :=
  LinearMap.norm_extendOfNorm_apply_le (stokesSmoothEnergy_dense U) _
    (stokesSmoothVelocity_norm_le hU hvol) v

/-- The genuine finite Poincare bound also controls the reconstruction operator norm. -/
theorem stokesEnergyVelocity_opNorm_le {U : Set Vec3}
    (hU : MeasurableSet U) (hvol : volume U ≠ ∞) :
    ‖stokesEnergyVelocity U‖ ≤ (stokesTestPoincareConstant U).toReal :=
  (stokesEnergyVelocity U).opNorm_le_bound ENNReal.toReal_nonneg
    (stokesEnergyVelocity_norm_le hU hvol)

/-- The scalar `L²` class of a genuine compact test. -/
def stokesScalarTestL2 {U : Set Vec3} (ψ : WeakTestFunction U) :
    Lp ℝ 2 (volume.restrict U) :=
  (((ψ.contDiff.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport).mono_measure
    Measure.restrict_le_self : MemLp ψ.toFun 2 (volume.restrict U))).toLp ψ.toFun

/-- The scalar `L²` class of the genuine derivative of a compact test. -/
def stokesScalarTestDerivativeL2 {U : Set Vec3} (ψ : WeakTestFunction U) (i : Fin 3) :
    Lp ℝ 2 (volume.restrict U) :=
  ((((ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i))).mono_measure
      Measure.restrict_le_self : MemLp (ψ.partialDeriv i) 2 (volume.restrict U)).toLp
        (ψ.partialDeriv i)

/-- A genuine velocity coordinate, continuously extracted in actual `L²`. -/
def stokesVelocityComponent (U : Set Vec3) (j : Fin 3) :
    Lp Vec3 2 (volume.restrict U) →L[ℝ] Lp ℝ 2 (volume.restrict U) :=
  (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).compLpL 2 (volume.restrict U)

/-- A genuine matrix coordinate, continuously extracted from the energy space. -/
def stokesGradientComponent (U : Set Vec3) (i j : Fin 3) :
    stokesGradientEnergySpace U →L[ℝ] Lp ℝ 2 (volume.restrict U) :=
  ((PiLp.proj 2 (fun _ : Fin 3 × Fin 3 ↦ ℝ) (i, j) : StokesGradientMatrix →L[ℝ] ℝ).compLpL
    2 (volume.restrict U)).comp (stokesGradientEnergySpace U).toSubmodule.subtypeL

/-- The scalar test pairing is the actual integral of the velocity coordinate. -/
theorem stokesVelocityComponent_pair {U : Set Vec3} (j : Fin 3)
    (f : Lp Vec3 2 (volume.restrict U)) (ψ : WeakTestFunction U) :
    inner ℝ (stokesScalarTestL2 ψ) (stokesVelocityComponent U j f) =
      ∫ x in U, f x j * ψ x := by
  rw [L2.inner_def]
  have hc := (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).coeFn_compLpL
    (p := 2) (μ := volume.restrict U) f
  have hψ := (((ψ.contDiff.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport).mono_measure
    Measure.restrict_le_self : MemLp ψ.toFun 2 (volume.restrict U))).coeFn_toLp
  apply integral_congr_ae
  filter_upwards [hc, hψ] with x hx hψx
  change stokesScalarTestL2 ψ x = ψ x at hψx
  rw [hψx, Real.inner_apply]
  have hcx : stokesVelocityComponent U j f x = f x j := hx
  rw [hcx]
  exact mul_comm _ _

/-- The derivative-test pairing is the actual integral of the velocity coordinate. -/
theorem stokesVelocityComponent_derivative_pair {U : Set Vec3} (i j : Fin 3)
    (f : Lp Vec3 2 (volume.restrict U)) (ψ : WeakTestFunction U) :
    inner ℝ (stokesScalarTestDerivativeL2 ψ i) (stokesVelocityComponent U j f) =
      ∫ x in U, f x j * ψ.partialDeriv i x := by
  rw [L2.inner_def]
  have hc := (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).coeFn_compLpL
    (p := 2) (μ := volume.restrict U) f
  have hcψ : Continuous (ψ.partialDeriv i) :=
    (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hkψ : HasCompactSupport (ψ.partialDeriv i) :=
    ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hψ := ((hcψ.memLp_of_hasCompactSupport hkψ).mono_measure
    Measure.restrict_le_self : MemLp (ψ.partialDeriv i) 2 (volume.restrict U)).coeFn_toLp
  apply integral_congr_ae
  filter_upwards [hc, hψ] with x hx hψx
  change stokesScalarTestDerivativeL2 ψ i x = ψ.partialDeriv i x at hψx
  rw [hψx, Real.inner_apply]
  have hcx : stokesVelocityComponent U j f x = f x j := hx
  rw [hcx]
  exact mul_comm _ _

/-- The compact-test pairing is the actual integral of the energy matrix coordinate. -/
theorem stokesGradientComponent_pair {U : Set Vec3} (i j : Fin 3)
    (v : stokesGradientEnergySpace U) (ψ : WeakTestFunction U) :
    inner ℝ (stokesScalarTestL2 ψ) (stokesGradientComponent U i j v) =
      ∫ x in U, v.val x (i, j) * ψ x := by
  rw [L2.inner_def]
  have hc := (PiLp.proj 2 (fun _ : Fin 3 × Fin 3 ↦ ℝ) (i, j) :
    StokesGradientMatrix →L[ℝ] ℝ).coeFn_compLpL
      (p := 2) (μ := volume.restrict U) v.val
  have hψ := (((ψ.contDiff.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport).mono_measure
    Measure.restrict_le_self : MemLp ψ.toFun 2 (volume.restrict U))).coeFn_toLp
  apply integral_congr_ae
  filter_upwards [hc, hψ] with x hx hψx
  change stokesScalarTestL2 ψ x = ψ x at hψx
  rw [hψx, Real.inner_apply]
  have hcx : stokesGradientComponent U i j v x = v.val x (i, j) := hx
  rw [hcx]
  exact mul_comm _ _

/-- The reconstructed velocity has the actual given energy matrix as its weak gradient,
as a genuine compact-test integration by parts identity. -/
theorem stokesEnergyVelocity_integral_ibp {U : Set Vec3}
    (hU : MeasurableSet U) (hvol : volume U ≠ ∞) (v : stokesGradientEnergySpace U)
    (i j : Fin 3) (ψ : WeakTestFunction U) :
    (∫ x in U, stokesEnergyVelocity U v x j * ψ.partialDeriv i x) =
      -(∫ x in U, v.val x (i, j) * ψ x) := by
  let L : stokesGradientEnergySpace U →L[ℝ] ℝ :=
    ((innerSL ℝ (stokesScalarTestDerivativeL2 ψ i)).comp
      (stokesVelocityComponent U j)).comp (stokesEnergyVelocity U)
  let R : stokesGradientEnergySpace U →L[ℝ] ℝ :=
    (innerSL ℝ (stokesScalarTestL2 ψ)).comp (stokesGradientComponent U i j)
  have h : L v = -R v := by
    refine (stokesSmoothEnergy_dense U).induction_on (p := fun w ↦ L w = -R w) v
      (isClosed_eq L.continuous R.continuous.neg) ?_
    intro φ
    change inner ℝ (stokesScalarTestDerivativeL2 ψ i)
      (stokesVelocityComponent U j
        (stokesEnergyVelocity U (stokesEnergyTest (stokesSmoothToWeak φ)))) =
      -inner ℝ (stokesScalarTestL2 ψ)
        (stokesGradientComponent U i j (stokesEnergyTest (stokesSmoothToWeak φ)))
    rw [stokesEnergyVelocity_test hU hvol, stokesVelocityComponent_derivative_pair,
      stokesGradientComponent_pair]
    have hv := (stokesTestVelocity_memLp (stokesSmoothToWeak φ)).coeFn_toLp
    have hg := (stokesTestGradient_memLp (stokesSmoothToWeak φ)).coeFn_toLp
    have heqV : (∫ x in U, stokesTestVelocityL2 (stokesSmoothToWeak φ) x j *
        ψ.partialDeriv i x) = ∫ x in U, φ.val j x * ψ.partialDeriv i x := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      change stokesTestVelocityL2 (stokesSmoothToWeak φ) x = _ at hx
      rw [hx]
      rfl
    have heqG : (∫ x in U, (stokesEnergyTest (stokesSmoothToWeak φ)).val x
        (i, j) * ψ x) = ∫ x in U, (stokesSmoothToWeak φ j).partialDeriv i x *
          ψ x := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      change stokesTestGradientL2 (stokesSmoothToWeak φ) x = _ at hx
      rw [show (stokesEnergyTest (stokesSmoothToWeak φ)).val =
        stokesTestGradientL2 (stokesSmoothToWeak φ) from rfl, hx]
      rfl
    rw [heqV, heqG]
    exact HasWeakPartialDerivOn.of_contDiff ((stokesSmooth_component_contDiff φ j).of_le (by simp))
      ψ.toFun ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset
  change inner ℝ (stokesScalarTestDerivativeL2 ψ i)
    (stokesVelocityComponent U j (stokesEnergyVelocity U v)) =
      -inner ℝ (stokesScalarTestL2 ψ) (stokesGradientComponent U i j v) at h
  simpa only [stokesVelocityComponent_derivative_pair, stokesGradientComponent_pair] using h

/-- Every component of the actual reconstructed velocity has the genuine energy
matrix as its spatial weak gradient. -/
theorem stokesEnergyVelocity_hasWeakGradient {U : Set Vec3}
    (hU : MeasurableSet U) (hvol : volume U ≠ ∞) (v : stokesGradientEnergySpace U)
    (j : Fin 3) :
    HasWeakGradientOn U (fun x ↦ stokesEnergyVelocity U v x j)
      (fun x i ↦ v.val x (i, j)) := by
  intro i
  apply hasWeakPartialDerivOn_iff_forall_testFunction.mpr
  exact stokesEnergyVelocity_integral_ibp hU hvol v i j

end FluidSingularSets
