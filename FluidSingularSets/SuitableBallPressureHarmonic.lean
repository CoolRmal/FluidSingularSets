-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallHarmonicPressureDecay
public import FluidSingularSets.SuitableViscousPressureHarmonic
public import FluidSingularSets.StokesPressureMixedBounds

/-!
# Actual suitable spatial pressure slices

The suitable weak equations give one common full-measure time set for every
compact divergence test. Together with actual local Sobolev slice data, this
proves harmonicity of the genuine ball Stokes velocity and viscous pressures.
No spatial regularity or pressure harmonicity assumption is added to suitability.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Genuine local H¹ vector data have finite spatial L⁶ on the inner ball. -/
theorem ballH1Vector_memLp_six (x : Vec3) {r : ℝ} (hr : 0 < r)
    {u : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3}
    (hu : MemLp u 2 (volume.restrict (euclideanBall x (2 * r))))
    (hD : MemLp D 2 (volume.restrict (euclideanBall x (2 * r))))
    (hw : ∀ j : Fin 3, HasWeakGradientOn (euclideanBall x (2 * r))
      (fun y ↦ u y j) (fun y ↦ D y j)) :
    MemLp u 6 (volume.restrict (vec3Ball x r)) := by
  rw [← euclideanBall_eq_vec3Ball hr]
  apply MemLp.of_eval
  intro j
  let v : H1Function (euclideanBall x (2 * r)) :=
    { toFun := fun y ↦ u y j
      grad := fun y ↦ D y j
      memL2 := hu.eval j
      gradMemL2 := fun i ↦ (hD.eval j).eval i
      hasWeakGradient := hw j }
  have hs := h1SobolevBall hr v
  change eLpNorm (fun y ↦ u y j) 6 (volume.restrict (euclideanBall x r)) ≤
    localSobolevConstant *
      (eLpNorm (fun y ↦ D y j) 2 (volume.restrict (euclideanBall x (2 * r))) +
        (Real.toNNReal (32 / r) : ℝ≥0∞) *
          eLpNorm (fun y ↦ u y j) 2 (volume.restrict (euclideanBall x (2 * r)))) at hs
  apply memLp_iff.mpr
  exact hs.trans_lt (by
    unfold localSobolevConstant
    finiteness [hu.eval j, hD.eval j])

/-- Actual suitable slice data give finite L⁶ on every interior inner spatial ball. -/
theorem suitable_ball_memLp_six_ae
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x : Vec3) {r : ℝ} (hr : 0 < r)
    (hbox : localBox Ω I (euclideanBall x (2 * r)) J) :
    ∀ᵐ t ∂volume.restrict J,
      MemLp (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball x r)) := by
  have hw : ∀ᵐ t ∂volume.restrict J, ∀ j : Fin 3,
      HasWeakGradientOn (euclideanBall x (2 * r))
        (fun y ↦ u (y, t) j) (fun y ↦ D (y, t) j) :=
    ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht hwt
  exact ballH1Vector_memLp_six x hr ht.1 ht.2 hwt

/-- Suitable divergence gives all actual compact spatial tests on one full-measure time set. -/
theorem suitable_ball_divergenceFree_slices_ae
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x : Vec3) (r : ℝ) (hbox : localBox Ω I (vec3Ball x r) J) :
    ∀ᵐ t ∂volume.restrict J,
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x r →
          (∫ y in vec3Ball x r, ∑ i : Fin 3,
            u (y, t) i * spatialDeriv ψ i y) = 0 := by
  filter_upwards [suitable_divergenceFree_slices_ae_localBox hsol hbox]
    with t ht ψ hψ hψc hψB
  exact ht ⟨ψ, hψ, hψc, hψB⟩

/-- The actual suitable derivative pressure is weakly harmonic almost every time. -/
theorem suitable_ballRawViscousPressure_weaklyHarmonic_ae
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x : Vec3) {r : ℝ} (hr : 0 < r) (hbox : localBox Ω I (vec3Ball x r) J) :
    ∀ᵐ t ∂volume.restrict J,
      ∀ hD : MemLp (fun y ↦ D (y, t)) 2 (volume.restrict (vec3Ball x r)),
        WeaklyHarmonicOn (vec3Ball x r)
          (ballRawViscousPressure x hr (fun y ↦ D (y, t)) hD : Vec3 → ℝ) := by
  have hw : ∀ᵐ t ∂volume.restrict J, ∀ j : Fin 3,
      HasWeakGradientOn (vec3Ball x r)
        (fun y ↦ u (y, t) j) (fun y ↦ D (y, t) j) :=
    ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw,
    suitable_ball_divergenceFree_slices_ae hsol x r hbox] with t ht hwt hdiv hD
  exact ballRawViscousPressure_weaklyHarmonic x hr
    (fun y ↦ u (y, t)) (fun y ↦ D (y, t)) ht.1 hD hwt
    (fun ψ ↦ hdiv ψ.toFun ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset)

/-- The actual physical viscous-pressure curve is harmonic at almost every suitable time. -/
theorem suitable_ballViscousPressureCurve_weaklyHarmonic_ae
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x : Vec3) {r : ℝ} (hr : 0 < r) (hbox : localBox Ω I (vec3Ball x r) J) :
    ∀ᵐ t ∂volume.restrict J,
      WeaklyHarmonicOn (vec3Ball x r) (ballViscousPressureCurve x hr D t : Vec3 → ℝ) := by
  filter_upwards [slice_memLp_ae_of_sws hsol hbox,
    suitable_ballRawViscousPressure_weaklyHarmonic_ae hsol x hr hbox] with t ht hH
  rw [ballViscousPressureCurve_eq x hr D t ht.2]
  exact hH ht.2

/-- The actual suitable large and local convective-pressure curves differ harmonically. -/
theorem suitable_ballConvectivePressureCurve_local_difference_weaklyHarmonic_ae
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x : Vec3) {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R)
    (hbox : localBox Ω I (euclideanBall x (2 * R)) J) :
    ∀ᵐ t ∂volume.restrict J, WeaklyHarmonicOn (vec3Ball x r)
      (fun y ↦ ballConvectivePressureCurve x hR u t y -
        ballConvectivePressureCurve x hr u t y) := by
  filter_upwards [suitable_ball_memLp_four_ae hsol x hR hbox] with t ht
  rw [ballConvectivePressureCurve_eq x hR u t ht,
    ballConvectivePressureCurve_eq x hr u t
      (ht.mono_measure (Measure.restrict_mono (vec3Ball_mono hrR) le_rfl))]
  exact ballNonlinearPressure_local_difference_weaklyHarmonic x hR hr hrR
    (fun y ↦ u (y, t)) ht

/-- The true suitable viscous pressure has actual relative-radius centered L² decay. -/
theorem suitable_ballViscousPressureCurve_centered_decay_ae
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x : Vec3) {r : ℝ} (hr : 0 < r) (hbox : localBox Ω I (vec3Ball x r) J)
    {s ρ : ℝ} (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1) :
    ∀ᵐ t ∂volume.restrict J,
      let P := ballViscousPressureCurve x hr D t
      eLpNorm (fun y ↦ P y - average (volume.restrict (vec3Ball x (r * s))) P) 2
          (volume.restrict (vec3Ball x (r * s))) ≤
        fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ) *
          eLpNorm P 2 (volume.restrict (vec3Ball x r)) := by
  filter_upwards [suitable_ballViscousPressureCurve_weaklyHarmonic_ae hsol x hr hbox]
    with t ht
  exact ballHarmonic_centered_eLpNorm_two_decay x hr
    (Lp.memLp (ballViscousPressureCurve x hr D t)) ht hs hsρ hρ

/-- Actual suitable convective pressure has local decay with the true endpoint velocity source. -/
theorem suitable_ballConvectivePressureCurve_centered_local_decay_ae
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x : Vec3) {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R)
    (hbox : localBox Ω I (euclideanBall x (2 * R)) J)
    {s ρ : ℝ} (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1) :
    ∀ᵐ t ∂volume.restrict J,
      let P := ballConvectivePressureCurve x hR u t
      let A := 12 * volume (vec3Ball x r) ^ (1 / 6 : ℝ) *
        eLpNorm (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball x r)) ^ 2
      eLpNorm (fun y ↦ P y - average (volume.restrict (vec3Ball x (r * s))) P) 2
          (volume.restrict (vec3Ball x (r * s))) ≤
        2 * A + fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ) *
          (eLpNorm P 2 (volume.restrict (vec3Ball x r)) + A) := by
  filter_upwards [suitable_ball_memLp_four_ae hsol x hR hbox,
    suitable_ball_memLp_six_ae hsol x hR hbox] with t ht4 ht6
  dsimp only
  rw [ballConvectivePressureCurve_eq x hR u t ht4]
  exact ballNonlinearPressure_centered_local_decay_velocity_source x hR hr hrR
    (fun y ↦ u (y, t)) ht4
    (ht6.mono_measure (Measure.restrict_mono (vec3Ball_mono hrR) le_rfl)) hs hsρ hρ

end FluidSingularSets
