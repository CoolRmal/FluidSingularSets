-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.MovingRelativeVelocity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Genuine continuity of mixed costs under terminal-time shifts

A finite nonnegative time density has a continuous sliding interval integral.
Localizing to a fixed open buffer proves the same fact from actual local
measurability and integrability. In particular a strict moving mixed-norm
bound persists for small positive shifts of the terminal time.
-/

@[expose] public section

open MeasureTheory Set Filter intervalIntegral
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The sliding integral of a genuinely finite nonnegative time density is continuous. -/
theorem continuous_sliding_lintegral {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g volume) (hfin : (∫⁻ t, g t) ≠ ∞)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Continuous (fun s : ℝ ↦ ∫⁻ t in Ioo (s - ℓ) s, g t) := by
  have hreal := integrable_toReal_of_lintegral_ne_top hg hfin
  have hP := hreal.continuous_primitive 0
  have heq (s : ℝ) :
      (∫⁻ t in Ioo (s - ℓ) s, g t) =
        ENNReal.ofReal ((∫ t in (0 : ℝ)..s, (g t).toReal) -
          ∫ t in (0 : ℝ)..(s - ℓ), (g t).toReal) := by
    have hlocal : (∫⁻ t in Ioo (s - ℓ) s, g t) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral _ _)
    rw [integral_interval_sub_left hreal.intervalIntegrable hreal.intervalIntegrable,
      integral_of_le (sub_le_self s hℓ), integral_Ioc_eq_integral_Ioo,
      integral_toReal hg.restrict (ae_restrict_of_ae (ae_lt_top' hg hfin)),
      ENNReal.ofReal_toReal hlocal]
  have hshift : Continuous (fun s : ℝ ↦ s - ℓ) := continuous_id.sub continuous_const
  have hcont := ENNReal.continuous_ofReal.comp (hP.sub (hP.comp hshift))
  exact hcont.congr (fun s ↦ (heq s).symm)

/-- A sliding integral is continuous at every terminal time strictly inside a
fixed buffer on which the actual density is measurable and finite. -/
theorem continuousAt_sliding_lintegral_of_buffer {g : ℝ → ℝ≥0∞}
    {a b s₀ ℓ : ℝ} (hℓ : 0 ≤ ℓ) (ha : a < s₀ - ℓ) (hb : s₀ < b)
    (hg : AEMeasurable g (volume.restrict (Ioo a b)))
    (hfin : (∫⁻ t in Ioo a b, g t) ≠ ∞) :
    ContinuousAt (fun s : ℝ ↦ ∫⁻ t in Ioo (s - ℓ) s, g t) s₀ := by
  let G := (Ioo a b).indicator g
  have hG : AEMeasurable G volume :=
    (aemeasurable_indicator_iff measurableSet_Ioo).mpr hg
  have hGfin : (∫⁻ t, G t) ≠ ∞ := by
    simpa only [G, lintegral_indicator measurableSet_Ioo] using hfin
  have hcont := (continuous_sliding_lintegral hG hGfin hℓ).continuousAt (x := s₀)
  have heq : (fun s : ℝ ↦ ∫⁻ t in Ioo (s - ℓ) s, g t) =ᶠ[𝓝 s₀]
      (fun s : ℝ ↦ ∫⁻ t in Ioo (s - ℓ) s, G t) := by
    have hshift : ContinuousAt (fun s : ℝ ↦ s - ℓ) s₀ :=
      continuousAt_id.sub continuousAt_const
    have hleft := hshift.tendsto.eventually (eventually_gt_nhds ha)
    filter_upwards [hleft, eventually_lt_nhds hb] with s hsleft hsright
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have htbuf : t ∈ Ioo a b := ⟨hsleft.trans ht.1, ht.2.trans hsright⟩
    exact (indicator_of_mem htbuf g).symm
  exact hcont.congr_of_eventuallyEq heq

/-- A strict integral bound persists under all sufficiently small terminal shifts. -/
theorem eventually_sliding_lintegral_lt_of_buffer {g : ℝ → ℝ≥0∞}
    {a b s₀ ℓ : ℝ} {ε : ℝ≥0∞}
    (hℓ : 0 ≤ ℓ) (ha : a < s₀ - ℓ) (hb : s₀ < b)
    (hg : AEMeasurable g (volume.restrict (Ioo a b)))
    (hfin : (∫⁻ t in Ioo a b, g t) ≠ ∞)
    (hsmall : (∫⁻ t in Ioo (s₀ - ℓ) s₀, g t) < ε) :
    ∀ᶠ s : ℝ in 𝓝 s₀, (∫⁻ t in Ioo (s - ℓ) s, g t) < ε :=
  (continuousAt_sliding_lintegral_of_buffer hℓ ha hb hg hfin).tendsto.eventually
    (eventually_lt_nhds hsmall)

/-- The literal moving mixed velocity cost is continuous in the terminal time
from genuine local measurability and a finite slice-density integral. -/
theorem continuousAt_movingRelativeVelocityCost_shift
    (X m : ℝ → Vec3) (u : ParabolicPoint → Vec3) {r a b s₀ : ℝ}
    (hr : 0 < r) (ha : a < s₀ - r ^ 2) (hb : s₀ < b)
    (hg : AEMeasurable (fun t ↦ eLpNorm (fun x ↦
      vec3EuclideanNorm (acceleratedVelocity X m u (x, t))) 6
        (volume.restrict (vec3Ball 0 r)) ^ (2 : ℝ)) (volume.restrict (Ioo a b)))
    (hfin : (∫⁻ t in Ioo a b, eLpNorm (fun x ↦
      vec3EuclideanNorm (acceleratedVelocity X m u (x, t))) 6
        (volume.restrict (vec3Ball 0 r)) ^ (2 : ℝ)) ≠ ∞) :
    ContinuousAt (fun s ↦ movingRelativeVelocityCost X m u r (Ioo (s - r ^ 2) s)) s₀ := by
  exact (ENNReal.continuous_const_mul
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hr)))).continuousAt.comp
      (continuousAt_sliding_lintegral_of_buffer (sq_nonneg r) ha hb hg hfin)

/-- A strict actual moving mixed cost bound survives sufficiently small terminal shifts. -/
theorem eventually_movingRelativeVelocityCost_shift_lt
    (X m : ℝ → Vec3) (u : ParabolicPoint → Vec3) {r a b s₀ : ℝ} {κ : ℝ≥0∞}
    (hr : 0 < r) (ha : a < s₀ - r ^ 2) (hb : s₀ < b)
    (hg : AEMeasurable (fun t ↦ eLpNorm (fun x ↦
      vec3EuclideanNorm (acceleratedVelocity X m u (x, t))) 6
        (volume.restrict (vec3Ball 0 r)) ^ (2 : ℝ)) (volume.restrict (Ioo a b)))
    (hfin : (∫⁻ t in Ioo a b, eLpNorm (fun x ↦
      vec3EuclideanNorm (acceleratedVelocity X m u (x, t))) 6
        (volume.restrict (vec3Ball 0 r)) ^ (2 : ℝ)) ≠ ∞)
    (hsmall : movingRelativeVelocityCost X m u r (Ioo (s₀ - r ^ 2) s₀) < κ) :
    ∀ᶠ s : ℝ in 𝓝 s₀, movingRelativeVelocityCost X m u r (Ioo (s - r ^ 2) s) < κ :=
  (continuousAt_movingRelativeVelocityCost_shift X m u hr ha hb hg hfin).tendsto.eventually
    (eventually_lt_nhds hsmall)

end FluidSingularSets
