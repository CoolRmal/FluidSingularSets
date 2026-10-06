-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallEndpointAbsorption
public import FluidSingularSets.FullBallProjectedPressurePairings
public import FluidSingularSets.CanonicalBallCutoffSecondBounds
public import FluidSingularSets.FullBallCanonicalCaccioppoli

/-!
# Genuine fixed bounds for the endpoint projected energy coefficients

The actual native Stokes pairing, harmonic Hessian, and corrected velocity
coefficients have universal reciprocal radius-gap bounds. This module derives
their precise powers directly from the proved operators and the actual
canonical cutoff budgets. The original mixed velocity source polynomial is
preserved by the scalar absorption theorem.
-/

@[expose] public section

open CKN MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A genuine universal coefficient for the actual viscous pressure pairing. -/
def fullBallFixedViscousPairingConstant : ℝ :=
  1 + 18432 * fullBallFixedProjectedSliceConstant *
    (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 3 : ℝ)

theorem fullBallFixedViscousPairingConstant_nonneg :
    0 ≤ fullBallFixedViscousPairingConstant := by
  unfold fullBallFixedViscousPairingConstant
  positivity [fullBallFixedProjectedSliceConstant_nonneg]

/-- A genuine universal coefficient for the square-root pressure and harmonic terms. -/
def fullBallFixedEndpointPressureConstant : ℝ :=
  13824 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ) +
    1152 * fullBallFixedHarmonicHessianConstant *
      (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ)

theorem fullBallFixedEndpointPressureConstant_nonneg :
    0 ≤ fullBallFixedEndpointPressureConstant := by
  unfold fullBallFixedEndpointPressureConstant
  positivity [fullBallFixedHarmonicHessianConstant_nonneg]

/-- A true radius-independent convection coefficient on the original time interval. -/
def fullBallFixedEndpointConvectionConstant (a b : ℝ) : ℝ :=
  5184 * (8 * fullBallFixedProjectedSliceConstant) ^ (1 / 3 : ℝ) *
    (volume (Ioo a b)).toReal ^ (1 / 4 : ℝ)

theorem fullBallFixedEndpointConvectionConstant_nonneg (a b : ℝ) :
    0 ≤ fullBallFixedEndpointConvectionConstant a b := by
  unfold fullBallFixedEndpointConvectionConstant
  positivity [fullBallFixedProjectedSliceConstant_nonneg]

/-- The actual time/diffusion/viscous quadratic source has a fixed finite coefficient. -/
def fullBallFixedEndpointQuadraticConstant (T₀ Λ₀ δ : ℝ) : ℝ :=
  576 * (T₀ + Λ₀) * fullBallFixedProjectedSquareConstant +
    (3 / 2 : ℝ) * fullBallFixedViscousPairingConstant ^ 2 / δ

theorem fullBallFixedEndpointQuadraticConstant_nonneg {T₀ Λ₀ δ : ℝ}
    (hT₀ : 0 ≤ T₀) (hΛ₀ : 0 ≤ Λ₀) (hδ : 0 < δ) :
    0 ≤ fullBallFixedEndpointQuadraticConstant T₀ Λ₀ δ := by
  unfold fullBallFixedEndpointQuadraticConstant
  positivity [fullBallFixedProjectedSquareConstant_nonneg]

/-- The native viscous pairing coefficient has its literal real operator value. -/
theorem fullBallViscousMixedPairingCoefficient_toReal {ρ L : ℝ} (hL : 0 ≤ L) :
    (fullBallViscousMixedPairingCoefficient ρ L).toReal =
      1 + 72 * L * (fullBallProjectedVelocitySliceCoefficient ρ).toReal *
        (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 3 : ℝ) := by
  have hv : volume (vec3Ball (0 : Vec3) 1) ≠ ⊤ := volume_vec3Ball_lt_top.ne
  have hterm : 12 * ENNReal.ofReal (6 * L) * fullBallProjectedVelocitySliceCoefficient ρ *
      volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ) ≠ ⊤ := by
    finiteness [fullBallProjectedVelocitySliceCoefficient_ne_top ρ]
  unfold fullBallViscousMixedPairingCoefficient
  rw [ENNReal.toReal_add ENNReal.one_ne_top hterm]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 6 * L), ← ENNReal.toReal_rpow]
  ring

/-- Genuine native viscous pairing at the midpoint costs the reciprocal fourth gap power. -/
theorem fullBallViscousMixedPairingCoefficient_midpoint_le_gap {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1) :
    (fullBallViscousMixedPairingCoefficient ((r + R) / 2) (32 / (R - r))).toReal ≤
      fullBallFixedViscousPairingConstant / (R - r) ^ 4 := by
  have hd : 0 < R - r := sub_pos.mpr hrR
  have hd1 : R - r ≤ 1 := by linarith
  rw [fullBallViscousMixedPairingCoefficient_toReal (by positivity)]
  have hpow : (R - r) ^ (4 : ℕ) ≤ 1 := pow_le_one₀ hd.le hd1
  calc
    _ ≤ 1 + 72 * (32 / (R - r)) *
        (8 * fullBallFixedProjectedSliceConstant / (R - r) ^ 3) *
        (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 3 : ℝ) := by
      gcongr
      exact fullBallProjectedVelocitySliceCoefficient_midpoint_le_gap hr hrR hR
    _ ≤ fullBallFixedViscousPairingConstant / (R - r) ^ 4 := by
      apply (le_div_iff₀ (pow_pos hd 4)).mpr
      unfold fullBallFixedViscousPairingConstant
      have he : (1 + 72 * (32 / (R - r)) *
          (8 * fullBallFixedProjectedSliceConstant / (R - r) ^ 3) *
          (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 3 : ℝ)) * (R - r) ^ 4 =
          (R - r) ^ 4 + 18432 * fullBallFixedProjectedSliceConstant *
            (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 3 : ℝ) := by
        field_simp
        ring
      rw [he]
      linarith

/-- The actual midpoint convection coefficient keeps the genuine time-length factor. -/
theorem fullBall_endpoint_convectionTimeCoefficient_midpoint_le_gap {r R a b : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1) :
    162 * (32 / (R - r)) *
      (fullBallProjectedVelocitySliceCoefficient ((r + R) / 2)).toReal ^ (1 / 3 : ℝ) *
      (volume (Ioo a b)).toReal ^ (1 / 4 : ℝ) ≤
      fullBallFixedEndpointConvectionConstant a b / (R - r) ^ 2 := by
  apply (mul_le_mul_of_nonneg_right
    (fullBall_endpoint_convectionCoefficient_midpoint_le_gap hr hrR hR)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)).trans_eq
  unfold fullBallFixedEndpointConvectionConstant
  ring

/-- The true midpoint pressure/Hessian square-root coefficient costs the sixth gap power. -/
theorem fullBall_endpoint_pressureCoefficient_midpoint_le_gap {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1) :
    432 * (32 / (R - r)) * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ) +
      18 * fullBallProjectedHarmonicHessianVelocityConstant ((r + R) / 2) *
        (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ) ≤
      fullBallFixedEndpointPressureConstant / (R - r) ^ 6 := by
  have hd : 0 < R - r := sub_pos.mpr hrR
  have hd1 : R - r ≤ 1 := by linarith
  have h₁ := endpoint_reciprocal_gap_power_le hd hd1
    (by positivity : 0 ≤ 13824 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ))
    (by norm_num : (1 : ℕ) ≤ 6)
  have hH := fullBallProjectedHarmonicHessianVelocityConstant_midpoint_le_gap hr hrR hR
  calc
    _ ≤ 13824 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ) / (R - r) +
        18 * (64 * fullBallFixedHarmonicHessianConstant / (R - r) ^ 6) *
          (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ) := by
      have hv : 0 ≤ (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ) :=
        Real.rpow_nonneg ENNReal.toReal_nonneg _
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH
        (by norm_num : (0 : ℝ) ≤ 18)) hv
      convert add_le_add le_rfl hh using 1; ring
    _ ≤ 13824 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ) / (R - r) ^ 6 +
        18 * (64 * fullBallFixedHarmonicHessianConstant / (R - r) ^ 6) *
          (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ) := by
      exact add_le_add (by simpa only [pow_one] using h₁) le_rfl
    _ = _ := by unfold fullBallFixedEndpointPressureConstant; ring

/-- The actual quadratic midpoint cost is bounded from the true time and Laplacian budgets. -/
theorem fullBall_endpoint_quadraticCoefficient_midpoint_le_gap {r R T Λ T₀ Λ₀ δ : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1)
    (hT₀ : 0 ≤ T₀) (hΛ₀ : 0 ≤ Λ₀) (hδ : 0 < δ)
    (hT : T ≤ T₀ / (R - r) ^ 2) (hΛ : Λ ≤ Λ₀ / (R - r) ^ 2) :
    9 * (T + Λ) * (fullBallProjectedVelocitySquareCoefficient ((r + R) / 2)).toReal +
      (3 / 2 : ℝ) *
        (fullBallViscousMixedPairingCoefficient ((r + R) / 2) (32 / (R - r))).toReal ^ 2 / δ ≤
      fullBallFixedEndpointQuadraticConstant T₀ Λ₀ δ / (R - r) ^ 8 := by
  have hd : 0 < R - r := sub_pos.mpr hrR
  have hC := fullBallProjectedVelocitySquareCoefficient_midpoint_le_gap hr hrR hR
  have hV := pow_le_pow_left₀ ENNReal.toReal_nonneg
    (fullBallViscousMixedPairingCoefficient_midpoint_le_gap hr hrR hR) 2
  have hTΛ : T + Λ ≤ (T₀ + Λ₀) / (R - r) ^ 2 := by
    calc
      _ ≤ T₀ / (R - r) ^ 2 + Λ₀ / (R - r) ^ 2 := add_le_add hT hΛ
      _ = _ := by ring
  calc
    _ ≤ 9 * ((T₀ + Λ₀) / (R - r) ^ 2) *
        (64 * fullBallFixedProjectedSquareConstant / (R - r) ^ 6) +
        (3 / 2 : ℝ) * (fullBallFixedViscousPairingConstant / (R - r) ^ 4) ^ 2 / δ := by
      have ht := mul_le_mul (mul_le_mul_of_nonneg_left hTΛ (by norm_num)) hC
        ENNReal.toReal_nonneg (by positivity : 0 ≤ 9 * ((T₀ + Λ₀) / (R - r) ^ 2))
      exact add_le_add ht (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hV (by norm_num)) hδ.le)
    _ = _ := by
      unfold fullBallFixedEndpointQuadraticConstant
      field_simp
      ring

/-- The exact native quadratic cost has the proved midpoint coefficient bound. -/
theorem fullBallEndpointQuadraticCost_midpoint_le_gap {r R T Λ T₀ Λ₀ δ : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1)
    (hT₀ : 0 ≤ T₀) (hΛ₀ : 0 ≤ Λ₀) (hδ : 0 < δ)
    (hT : T ≤ T₀ / (R - r) ^ 2) (hΛ : Λ ≤ Λ₀ / (R - r) ^ 2) :
    fullBallEndpointQuadraticCost ((r + R) / 2) (32 / (R - r)) Λ T δ ≤
      fullBallFixedEndpointQuadraticConstant T₀ Λ₀ δ / (R - r) ^ 8 :=
  fullBall_endpoint_quadraticCoefficient_midpoint_le_gap hr hrR hR hT₀ hΛ₀ hδ hT hΛ

/-- The actual canonical twice-midpoint quadratic coefficient has an eighth-gap bound. -/
theorem fullBallEndpointQuadraticCost_canonical_le_gap {r δ : ℝ}
    (hr : 0 ≤ r) (hrone : r < 1) (hδ : 0 < δ) :
    fullBallEndpointQuadraticCost (((r + 1) / 2 + 1) / 2) (64 / (1 - r))
      (4 * canonicalBallCutoffSixthLaplacianConstant / (1 - r) ^ 2) (32 / (1 - r)) δ ≤
      256 * fullBallFixedEndpointQuadraticConstant
        16 canonicalBallCutoffSixthLaplacianConstant δ / (1 - r) ^ 8 := by
  let R : ℝ := (r + 1) / 2
  have hR : 0 ≤ R := by dsimp only [R]; linarith
  have hRone : R < 1 := by dsimp only [R]; linarith
  have hd : 0 < 1 - R := sub_pos.mpr hRone
  have hd1 : 1 - R ≤ 1 := by linarith
  have heL : 64 / (1 - r) = 32 / (1 - R) := by dsimp only [R]; field_simp; ring
  have heT : 32 / (1 - r) = 16 / (1 - R) := by dsimp only [R]; field_simp; ring
  have hT : 32 / (1 - r) ≤ 16 / (1 - R) ^ 2 := by
    rw [heT]
    simpa only [pow_one] using endpoint_reciprocal_gap_power_le hd hd1
      (by norm_num : (0 : ℝ) ≤ 16) (by norm_num : (1 : ℕ) ≤ 2)
  have hΛ : 4 * canonicalBallCutoffSixthLaplacianConstant / (1 - r) ^ 2 ≤
      canonicalBallCutoffSixthLaplacianConstant / (1 - R) ^ 2 := by
    apply le_of_eq
    dsimp only [R]
    field_simp
    ring
  rw [heL]
  calc
    _ ≤ fullBallFixedEndpointQuadraticConstant
        16 canonicalBallCutoffSixthLaplacianConstant δ / (1 - R) ^ 8 :=
      fullBallEndpointQuadraticCost_midpoint_le_gap hR hRone le_rfl (by norm_num)
        canonicalBallCutoffSixthLaplacianConstant_nonneg hδ hT hΛ
    _ = _ := by dsimp only [R]; field_simp; ring

/-- The actual twice-midpoint convection cost has a reciprocal squared-gap bound. -/
theorem fullBallEndpointConvectionCost_canonical_le_gap {r a b : ℝ}
    (hr : 0 ≤ r) (hrone : r < 1) :
    fullBallEndpointConvectionCost (((r + 1) / 2 + 1) / 2) (64 / (1 - r)) a b ≤
      4 * fullBallFixedEndpointConvectionConstant a b / (1 - r) ^ 2 := by
  let R : ℝ := (r + 1) / 2
  have hR : 0 ≤ R := by dsimp only [R]; linarith
  have hRone : R < 1 := by dsimp only [R]; linarith
  have heL : 64 / (1 - r) = 32 / (1 - R) := by dsimp only [R]; field_simp; ring
  rw [heL]
  calc
    _ ≤ fullBallFixedEndpointConvectionConstant a b / (1 - R) ^ 2 :=
      fullBall_endpoint_convectionTimeCoefficient_midpoint_le_gap hR hRone le_rfl
    _ = _ := by dsimp only [R]; field_simp; ring

/-- The actual twice-midpoint pressure/Hessian cost has a reciprocal sixth-gap bound. -/
theorem fullBallEndpointPressureCost_canonical_le_gap {r : ℝ}
    (hr : 0 ≤ r) (hrone : r < 1) :
    fullBallEndpointPressureCost (((r + 1) / 2 + 1) / 2) (64 / (1 - r)) ≤
      64 * fullBallFixedEndpointPressureConstant / (1 - r) ^ 6 := by
  let R : ℝ := (r + 1) / 2
  have hR : 0 ≤ R := by dsimp only [R]; linarith
  have hRone : R < 1 := by dsimp only [R]; linarith
  have heL : 64 / (1 - r) = 32 / (1 - R) := by dsimp only [R]; field_simp; ring
  rw [heL]
  calc
    _ ≤ fullBallFixedEndpointPressureConstant / (1 - R) ^ 6 :=
      fullBall_endpoint_pressureCoefficient_midpoint_le_gap hR hRone le_rfl
    _ = _ := by dsimp only [R]; field_simp; ring

/-- The genuine twice-midpoint tested connector source costs the sixth gap power. -/
theorem fullBall_endpoint_connectorSource_canonical_le_gap {r : ℝ}
    (hr : 0 ≤ r) (hrone : r < 1) :
    (fullBallProjectedVelocitySliceCoefficient (((r + 1) / 2 + 1) / 2)).toReal ^ 2 ≤
      4096 * fullBallFixedProjectedSliceConstant ^ 2 / (1 - r) ^ 6 := by
  let R : ℝ := (r + 1) / 2
  have hR : 0 ≤ R := by dsimp only [R]; linarith
  have hRone : R < 1 := by dsimp only [R]; linarith
  calc
    _ ≤ 64 * fullBallFixedProjectedSliceConstant ^ 2 / (1 - R) ^ 6 :=
      fullBall_endpoint_connectorSource_midpoint_le_gap hR hRone le_rfl
    _ = _ := by dsimp only [R]; field_simp; ring

/-- The actual twice-midpoint harmonic-gradient source costs the twelfth gap power. -/
theorem fullBallProjectedHarmonicSquareCoefficient_canonical_le_gap {r : ℝ}
    (hr : 0 ≤ r) (hrone : r < 1) :
    (fullBallProjectedHarmonicSquareCoefficient (((r + 1) / 2 + 1) / 2)).toReal ≤
      16777216 * fullBallFixedHarmonicSquareConstant / (1 - r) ^ 12 := by
  let R : ℝ := (r + 1) / 2
  have hR : 0 ≤ R := by dsimp only [R]; linarith
  have hRone : R < 1 := by dsimp only [R]; linarith
  calc
    _ ≤ 4096 * fullBallFixedHarmonicSquareConstant / (1 - R) ^ 12 :=
      fullBallProjectedHarmonicSquareCoefficient_midpoint_le_gap hR hRone le_rfl
    _ = _ := by dsimp only [R]; field_simp; ring

/-- A genuine radius-independent constant for the whole actual canonical forcing polynomial. -/
def fullBallCanonicalEndpointForcingConstant (δ a b : ℝ) : ℝ :=
  fullBallEndpointAbsorptionConstant
    (256 * fullBallFixedEndpointQuadraticConstant
      16 canonicalBallCutoffSixthLaplacianConstant δ)
    (4 * fullBallFixedEndpointConvectionConstant a b)
    (64 * fullBallFixedEndpointPressureConstant)
    (4096 * fullBallFixedProjectedSliceConstant ^ 2) +
      301989888 * fullBallFixedHarmonicSquareConstant

theorem fullBallCanonicalEndpointForcingConstant_nonneg {δ a b : ℝ} (hδ : 0 < δ) :
    0 ≤ fullBallCanonicalEndpointForcingConstant δ a b := by
  unfold fullBallCanonicalEndpointForcingConstant
  apply add_nonneg
  · exact fullBallEndpointAbsorptionConstant_nonneg
      (mul_nonneg (by norm_num) (fullBallFixedEndpointQuadraticConstant_nonneg
        (by norm_num) canonicalBallCutoffSixthLaplacianConstant_nonneg hδ)) (by positivity)
  · exact mul_nonneg (by norm_num) fullBallFixedHarmonicSquareConstant_nonneg

/-- The literal actual canonical original-gradient source polynomial has the twelfth gap bound. -/
theorem fullBall_canonical_endpoint_forcing_le_gap {r δ a b X : ℝ}
    (hr : 0 ≤ r) (hrone : r < 1) (hδ : 0 < δ) (hX : 0 ≤ X) :
    let ρ := ((r + 1) / 2 + 1) / 2
    let L := 64 / (1 - r)
    let c₀ := fullBallEndpointQuadraticCost ρ L
      (4 * canonicalBallCutoffSixthLaplacianConstant / (1 - r) ^ 2) (32 / (1 - r)) δ
    let c₁ := fullBallEndpointConvectionCost ρ L a b
    let c₂ := fullBallEndpointPressureCost ρ L
    (4 * c₀ + 2 * (fullBallProjectedVelocitySliceCoefficient ρ).toReal ^ 2 +
      18 * (fullBallProjectedHarmonicSquareCoefficient ρ).toReal) * X +
        32 * c₂ ^ 2 * X ^ 2 + 131072 * c₁ ^ 6 * X ^ 4 ≤
      fullBallCanonicalEndpointForcingConstant δ a b / (1 - r) ^ 12 *
        (X + X ^ 2 + X ^ 4) := by
  dsimp only
  let ρ : ℝ := ((r + 1) / 2 + 1) / 2
  let L : ℝ := 64 / (1 - r)
  let K₀ := 256 * fullBallFixedEndpointQuadraticConstant
    16 canonicalBallCutoffSixthLaplacianConstant δ
  let K₁ := 4 * fullBallFixedEndpointConvectionConstant a b
  let K₂ := 64 * fullBallFixedEndpointPressureConstant
  let KS := 4096 * fullBallFixedProjectedSliceConstant ^ 2
  let KH := 16777216 * fullBallFixedHarmonicSquareConstant
  have hd : 0 < 1 - r := sub_pos.mpr hrone
  have hd1 : 1 - r ≤ 1 := by linarith
  have hρone : ρ < 1 := by dsimp only [ρ]; linarith
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hK₀ : 0 ≤ K₀ := mul_nonneg (by norm_num)
    (fullBallFixedEndpointQuadraticConstant_nonneg
      (by norm_num) canonicalBallCutoffSixthLaplacianConstant_nonneg hδ)
  have hKS : 0 ≤ KS := by dsimp only [KS]; positivity
  have hKH : 0 ≤ KH := mul_nonneg (by norm_num) fullBallFixedHarmonicSquareConstant_nonneg
  have hc₀ := (fullBallEndpointQuadraticCost_canonical_le_gap hr hrone hδ).trans
    (endpoint_reciprocal_gap_power_le hd hd1 hK₀ (by norm_num : (8 : ℕ) ≤ 12))
  have hκ := (fullBall_endpoint_connectorSource_canonical_le_gap hr hrone).trans
    (endpoint_reciprocal_gap_power_le hd hd1 hKS (by norm_num : (6 : ℕ) ≤ 12))
  have hH := fullBallProjectedHarmonicSquareCoefficient_canonical_le_gap hr hrone
  have hc₁nonneg : 0 ≤ fullBallEndpointConvectionCost ρ L a b := by
    unfold fullBallEndpointConvectionCost
    positivity
  have hc₂nonneg : 0 ≤ fullBallEndpointPressureCost ρ L := by
    unfold fullBallEndpointPressureCost
    positivity [fullBallProjectedHarmonicHessianVelocityConstant_nonneg hρone]
  have hc₁ := pow_le_pow_left₀ hc₁nonneg
    (fullBallEndpointConvectionCost_canonical_le_gap hr hrone) 6
  have hc₂ := pow_le_pow_left₀ hc₂nonneg
    (fullBallEndpointPressureCost_canonical_le_gap hr hrone) 2
  rw [div_pow, ← pow_mul] at hc₁ hc₂
  have hc : 4 * fullBallEndpointQuadraticCost ρ L
      (4 * canonicalBallCutoffSixthLaplacianConstant / (1 - r) ^ 2) (32 / (1 - r)) δ +
      2 * (fullBallProjectedVelocitySliceCoefficient ρ).toReal ^ 2 +
      18 * (fullBallProjectedHarmonicSquareCoefficient ρ).toReal ≤
        (4 * K₀ + 2 * KS + 18 * KH) / (1 - r) ^ 12 := by
    calc
      _ ≤ 4 * (K₀ / (1 - r) ^ 12) + 2 * (KS / (1 - r) ^ 12) +
          18 * (KH / (1 - r) ^ 12) := by linarith
      _ = _ := by ring
  have hP₁ : X ≤ X + X ^ 2 + X ^ 4 := by nlinarith [sq_nonneg X, sq_nonneg (X ^ 2)]
  have hP₂ : X ^ 2 ≤ X + X ^ 2 + X ^ 4 := by nlinarith [sq_nonneg (X ^ 2)]
  have hP₄ : X ^ 4 ≤ X + X ^ 2 + X ^ 4 := by nlinarith [sq_nonneg X]
  calc
    _ ≤ (4 * K₀ + 2 * KS + 18 * KH) / (1 - r) ^ 12 * X +
        32 * (K₂ ^ 2 / (1 - r) ^ 12) * X ^ 2 +
        131072 * (K₁ ^ 6 / (1 - r) ^ 12) * X ^ 4 := by gcongr
    _ ≤ (4 * K₀ + 2 * KS + 18 * KH) / (1 - r) ^ 12 * (X + X ^ 2 + X ^ 4) +
        32 * (K₂ ^ 2 / (1 - r) ^ 12) * (X + X ^ 2 + X ^ 4) +
        131072 * (K₁ ^ 6 / (1 - r) ^ 12) * (X + X ^ 2 + X ^ 4) := by gcongr
    _ = _ := by
      dsimp only [K₀, K₁, K₂, KS, KH, fullBallCanonicalEndpointForcingConstant,
        fullBallEndpointAbsorptionConstant]
      ring

/-- The three literal canonical source coefficients satisfy the actual twelfth-gap bound. -/
theorem fullBall_canonical_source_polynomial_le_gap12 {r X : ℝ}
    (hr : 0 ≤ r) (hrone : r < 1) (hX : 0 ≤ X) :
    fullBallCanonicalLinearSourceCoefficient r * X +
      fullBallCanonicalQuadraticSourceCoefficient r * X ^ 2 +
      fullBallCanonicalFourthSourceCoefficient r * X ^ 4 ≤
        fullBallCanonicalEndpointForcingConstant (1 / 32) (-1) 0 / (1 - r) ^ 12 *
          (X + X ^ 2 + X ^ 4) := by
  have h := fullBall_canonical_endpoint_forcing_le_gap hr hrone
    (by norm_num : (0 : ℝ) < 1 / 32) hX (a := -1) (b := 0)
  have heρ : ((r + 1) / 2 + 1) / 2 = fullBallCanonicalPressureRadius r := by
    unfold fullBallCanonicalPressureRadius
    ring
  dsimp only at h
  simpa only [heρ, fullBallCanonicalLinearSourceCoefficient,
    fullBallCanonicalQuadraticSourceCoefficient, fullBallCanonicalFourthSourceCoefficient] using h

/-- Actual suitable data imply the terminal-independent truncated twelfth-gap estimate. -/
theorem suitable_fullBall_canonical_truncated_gap12
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0))
    {r δ : ℝ} (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) (hδ : 0 < δ) :
    let X := (∫⁻ t in Ioo (-1 : ℝ) 0, eLpNorm (fun x ↦ u (x, t)) 6
      (volume.restrict (vec3Ball 0 1)) ^ 2).toReal
    (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) (-δ),
      ENNReal.ofReal (projectedGradientSquare (D z))) < ⊤ ∧
    (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) (-δ),
      ENNReal.ofReal (projectedGradientSquare (D z))).toReal ≤
        (3 / 4) * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 0,
          ENNReal.ofReal (projectedGradientSquare (D z))).toReal +
        fullBallCanonicalEndpointForcingConstant (1 / 32) (-1) 0 / (1 - r) ^ 12 *
          (X + X ^ 2 + X ^ 4) := by
  have h := suitable_fullBall_canonical_truncated_caccioppoli hsol hbox hr hrone hδ
  dsimp only at h ⊢
  refine ⟨h.1, h.2.trans ?_⟩
  have hs := fullBall_canonical_source_polynomial_le_gap12
    (by linarith : 0 ≤ r) hrone (X := (∫⁻ t in Ioo (-1 : ℝ) 0,
      eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2).toReal)
    ENNReal.toReal_nonneg
  calc
    _ = (3 / 4) * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 0,
        ENNReal.ofReal (projectedGradientSquare (D z))).toReal +
      (fullBallCanonicalLinearSourceCoefficient r *
        (∫⁻ t in Ioo (-1 : ℝ) 0, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2).toReal +
      fullBallCanonicalQuadraticSourceCoefficient r *
        (∫⁻ t in Ioo (-1 : ℝ) 0, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2).toReal ^ 2 +
      fullBallCanonicalFourthSourceCoefficient r *
        (∫⁻ t in Ioo (-1 : ℝ) 0, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2).toReal ^ 4) := by ring
    _ ≤ _ := add_le_add le_rfl hs

end FluidSingularSets
