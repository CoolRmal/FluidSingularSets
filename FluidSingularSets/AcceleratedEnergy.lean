-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.AcceleratedFrame
public import FluidSingularSets.AcceleratedEnergyAlgebra
public import CKN.ClassEquivalence.MomentumIntegrand
public import CKN.Core.Step3.LocalizedEquationBasics
public import CKN.Setting.Energy.AELocalEnergy

/-!
# The actual local energy inequality in an accelerating frame

The first analytic bridge integrates the actual almost-everywhere spatial weak
gradient over time. Compact-test integrability is obtained from the suitable
solution's energy data before any integral identity is used.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The almost-everywhere spatial weak gradient of an actual suitable solution
gives a genuine joint space-time integration-by-parts identity. -/
theorem suitable_joint_spatial_integration_by_parts
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {χ : Vec3 × ℝ → ℝ} (hχ : χ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (i j : Fin 3) :
    Integrable (fun z : Vec3 × ℝ ↦ u z i * spatialPartial χ j z) volume ∧
      Integrable (fun z : Vec3 × ℝ ↦ Du z i j * χ z) volume ∧
        (∫ z : Vec3 × ℝ, u z i * spatialPartial χ j z) =
          -(∫ z : Vec3 × ℝ, Du z i j * χ z) := by
  have hdata := hsol.toData
  have hK : IsCompact (tsupport (show ParabolicPoint → ℝ from χ)) :=
    isCompact_tsupport_parabolic hχ.2.1
  have hKsub := tsupport_parabolic_subset_spaceTimeSet hχ
  have huK := velocity_component_integrableOn_compact_of_data hdata hK hKsub i
  have hDK := gradient_entry_integrableOn_compact_of_data hdata hK hKsub i j
  have hχcont : Continuous (show ParabolicPoint → ℝ from χ) :=
    hχ.1.continuous.comp continuous_parabolicPoint_to_prod
  have hdχcont : Continuous (fun z : ParabolicPoint ↦ spatialPartial χ j z) :=
    (spatialPartial_contDiff hχ.1 j).continuous.comp continuous_parabolicPoint_to_prod
  have huχK : IntegrableOn (fun z : ParabolicPoint ↦ u z i * spatialPartial χ j z)
      (tsupport (show ParabolicPoint → ℝ from χ)) volume := by
    simpa only [smul_eq_mul] using huK.smul_continuousOn hdχcont.continuousOn hK
  have hDχK : IntegrableOn (fun z : ParabolicPoint ↦ Du z i j * χ z)
      (tsupport (show ParabolicPoint → ℝ from χ)) volume := by
    simpa only [smul_eq_mul] using hDK.smul_continuousOn hχcont.continuousOn hK
  have huSupp : Function.support
      (fun z : ParabolicPoint ↦ u z i * spatialPartial χ j z) ⊆
        tsupport (show ParabolicPoint → ℝ from χ) := by
    rw [tsupport_parabolic_eq]
    intro z hz
    by_contra hcon
    apply hz
    change u z i * spatialPartial (show ParabolicPoint → ℝ from χ) j z = 0
    exact mul_eq_zero_of_right _ (spatialPartial_eq_zero_off_tsupport hcon j)
  have hDSupp : Function.support (fun z : ParabolicPoint ↦ Du z i j * χ z) ⊆
      tsupport (show ParabolicPoint → ℝ from χ) := by
    intro z hz
    by_contra hcon
    apply hz
    change Du z i j * (show ParabolicPoint → ℝ from χ) z = 0
    exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hcon)
  have huχ : Integrable (fun z : Vec3 × ℝ ↦ u z i * spatialPartial χ j z) volume :=
    (integrableOn_iff_integrable_of_support_subset huSupp).mp huχK
  have hDχ : Integrable (fun z : Vec3 × ℝ ↦ Du z i j * χ z) volume :=
    (integrableOn_iff_integrable_of_support_subset hDSupp).mp hDχK
  obtain ⟨B, J, hbox, hKbox⟩ := caccioppoli_localBox_of_compact_subset hsol.1 hsol.2.1
    hsol.2.2.1 hK hKsub
  have hsupport : tsupport χ ⊆ B ×ˢ J := by
    rw [tsupport_parabolic_eq] at hKbox
    exact hKbox
  have hJmeas : MeasurableSet J := hbox.2.2.2.1.measurableSet
  have hsliceSmooth (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 ↦ χ (x, t)) :=
    hχ.1.comp (contDiff_id.prodMk contDiff_const)
  have hsliceCompact (t : ℝ) : HasCompactSupport (fun x : Vec3 ↦ χ (x, t)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hχ.2.1.isCompact.image continuous_fst)
    intro x hx
    exact ⟨(x, t), subset_tsupport χ hx, rfl⟩
  have hsliceSupport (t : ℝ) : tsupport (fun x : Vec3 ↦ χ (x, t)) ⊆ B := by
    intro x hx
    exact (hsupport (tsupport_comp_subset_preimage (f := fun y : Vec3 ↦ (y, t)) χ
      (continuous_id.prodMk continuous_const) hx)).1
  have hgrad := hdata.hasWeakGradientOn_slice hbox i
  have hgrad' : ∀ᵐ t ∂volume, t ∈ J →
      HasWeakGradientOn B (fun x ↦ u (x, t) i) (fun x ↦ Du (x, t) i) :=
    (ae_restrict_iff' hJmeas).mp hgrad
  have hslice : ∀ᵐ t ∂volume,
      (∫ x : Vec3, u (x, t) i * spatialPartial χ j (x, t)) =
        -(∫ x : Vec3, Du (x, t) i j * χ (x, t)) := by
    filter_upwards [hgrad'] with t ht
    by_cases htJ : t ∈ J
    · have hw := (ht htJ) j (fun x : Vec3 ↦ χ (x, t))
        (hsliceSmooth t) (hsliceCompact t) (hsliceSupport t)
      have huoff (x : Vec3) (hx : x ∉ B) :
          u (x, t) i * spatialPartial χ j (x, t) = 0 := by
        rw [spatialPartial_eq_zero_off_tsupport (fun hmem ↦ hx (hsupport hmem).1) j,
          mul_zero]
      have hDoff (x : Vec3) (hx : x ∉ B) : Du (x, t) i j * χ (x, t) = 0 := by
        rw [image_eq_zero_of_notMem_tsupport (fun hmem ↦ hx (hsupport hmem).1), mul_zero]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero huoff,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero hDoff]
      exact hw
    · have huoff (x : Vec3) : u (x, t) i * spatialPartial χ j (x, t) = 0 := by
        rw [spatialPartial_eq_zero_off_tsupport (fun hmem ↦ htJ (hsupport hmem).2) j,
          mul_zero]
      have hDoff (x : Vec3) : Du (x, t) i j * χ (x, t) = 0 := by
        rw [image_eq_zero_of_notMem_tsupport (fun hmem ↦ htJ (hsupport hmem).2), mul_zero]
      simp only [huoff, hDoff, integral_zero, neg_zero]
  refine ⟨huχ, hDχ, ?_⟩
  calc
    _ = ∫ t : ℝ, ∫ x : Vec3, u (x, t) i * spatialPartial χ j (x, t) :=
      integral_prod_symm _ huχ
    _ = ∫ t : ℝ, -(∫ x : Vec3, Du (x, t) i j * χ (x, t)) := integral_congr_ae hslice
    _ = -(∫ t : ℝ, ∫ x : Vec3, Du (x, t) i j * χ (x, t)) := integral_neg _
    _ = _ := congrArg Neg.neg (integral_prod_symm _ hDχ).symm

/-- The genuine weak-gradient integration-by-parts identity transports to the
moving frame and admits a smooth time-dependent mean as a multiplier. -/
theorem suitable_accelerated_gradient_component_pairing
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (htube : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) B J)
    (i j : Fin 3) :
    Integrable (fun z : Vec3 × ℝ ↦ u (acceleratedFrameMap X z) i * m z.2 i *
        spatialSecondPartial ψ j j z) volume ∧
      Integrable (fun z : Vec3 × ℝ ↦ Du (acceleratedFrameMap X z) i j * m z.2 i *
        spatialPartial ψ j z) volume ∧
        (∫ z : Vec3 × ℝ, u (acceleratedFrameMap X z) i * m z.2 i *
          spatialSecondPartial ψ j j z) =
          -(∫ z : Vec3 × ℝ, Du (acceleratedFrameMap X z) i j * m z.2 i *
            spatialPartial ψ j z) := by
  let Ψ := acceleratedTestPullback X ψ
  have hΨ : Ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I :=
    acceleratedTestPullback_mem_spaceTimeTest hX hψ htube
  have hdΨ : (fun w : Vec3 × ℝ ↦ spatialPartial Ψ j w) ∈
      spaceTimeTestFunction (V := ℝ) Ω I :=
    ⟨spatialPartial_contDiff hΨ.1 j, hasCompactSupport_spatialPartial hΨ.2.1 j,
      (tsupport_spatialPartial_subset j).trans hΨ.2.2⟩
  let χ : Vec3 × ℝ → ℝ := fun w ↦ spatialPartial Ψ j w * m w.2 i
  have hχ : χ ∈ spaceTimeTestFunction (V := ℝ) Ω I :=
    spaceTimeTestFunction_mul_smooth hdΨ
      (((contDiff_apply ℝ ℝ i).comp hm).comp contDiff_snd)
  obtain ⟨hL, hR, hEq⟩ := suitable_joint_spatial_integration_by_parts hsol hχ i j
  have hχderiv (z : ParabolicPoint) : spatialPartial χ j (acceleratedFrameMap X z) =
      spatialSecondPartial ψ j j z * m z.2 i := by
    calc
      _ = spatialSecondPartial Ψ j j (acceleratedFrameMap X z) * m z.2 i :=
        spatialPartial_mul_time (χ := fun t ↦ m t i) (spatialPartial_contDiff hΨ.1 j) j
          ((acceleratedFrameMap X z).1, (acceleratedFrameMap X z).2)
      _ = _ := congrArg (fun b : ℝ ↦ b * m z.2 i)
        (accelerated_spatialSecondPartial_pullback X hψ.1 j j z)
  have hχvalue (z : ParabolicPoint) : χ (acceleratedFrameMap X z) =
      spatialPartial ψ j z * m z.2 i := by
    exact congrArg (fun b : ℝ ↦ b * m z.2 i)
      (accelerated_spatialPartial_pullback X hψ.1 j z)
  have hleft : (fun z : Vec3 × ℝ ↦ u (acceleratedFrameMap X z) i * m z.2 i *
      spatialSecondPartial ψ j j z) =
      (fun z : Vec3 × ℝ ↦ u z i * spatialPartial χ j z) ∘ acceleratedFrameMapProd X := by
    funext z
    change _ = u (acceleratedFrameMap X z) i * spatialPartial χ j (acceleratedFrameMap X z)
    rw [hχderiv]
    ring
  have hright : (fun z : Vec3 × ℝ ↦ Du (acceleratedFrameMap X z) i j * m z.2 i *
      spatialPartial ψ j z) =
      (fun z : Vec3 × ℝ ↦ Du z i j * χ z) ∘ acceleratedFrameMapProd X := by
    funext z
    change _ = Du (acceleratedFrameMap X z) i j * χ (acceleratedFrameMap X z)
    rw [hχvalue]
    ring
  have hMP := acceleratedFrameMapProd_measurePreserving X hX.continuous.measurable
  have hEmb := (acceleratedFrameHomeomorph X hX.continuous).measurableEmbedding
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact hMP.integrable_comp_of_integrable hL
  · rw [hright]
    exact hMP.integrable_comp_of_integrable hR
  · rw [hleft, hright]
    exact (hMP.integral_comp hEmb _).trans
      (hEq.trans (congrArg Neg.neg (hMP.integral_comp hEmb _).symm))

/-- The actual mean-gradient and mean-Laplacian correction integrals cancel,
including integrability of each correction separately. -/
theorem suitable_accelerated_gradient_pairing
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (htube : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) B J) :
    Integrable (fun z : Vec3 × ℝ ↦
        (∑ i, u (acceleratedFrameMap X z) i * m z.2 i) *
          ∑ j, spatialSecondPartial ψ j j z) volume ∧
      Integrable (fun z : Vec3 × ℝ ↦
        ∑ i, ∑ j, Du (acceleratedFrameMap X z) i j * m z.2 i * spatialPartial ψ j z)
          volume ∧
        (∫ z : Vec3 × ℝ, (∑ i, u (acceleratedFrameMap X z) i * m z.2 i) *
          ∑ j, spatialSecondPartial ψ j j z) =
          -(∫ z : Vec3 × ℝ, ∑ i, ∑ j, Du (acceleratedFrameMap X z) i j * m z.2 i *
            spatialPartial ψ j z) := by
  let L : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j z ↦
    u (acceleratedFrameMap X z) i * m z.2 i * spatialSecondPartial ψ j j z
  let R : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j z ↦
    Du (acceleratedFrameMap X z) i j * m z.2 i * spatialPartial ψ j z
  have hL (i j : Fin 3) : Integrable (L i j) volume :=
    (suitable_accelerated_gradient_component_pairing hsol hX hm htube hψ i j).1
  have hR (i j : Fin 3) : Integrable (R i j) volume :=
    (suitable_accelerated_gradient_component_pairing hsol hX hm htube hψ i j).2.1
  have hEq (i j : Fin 3) : (∫ z, L i j z) = -(∫ z, R i j z) :=
    (suitable_accelerated_gradient_component_pairing hsol hX hm htube hψ i j).2.2
  have hfun : (fun z : Vec3 × ℝ ↦ (∑ i, u (acceleratedFrameMap X z) i * m z.2 i) *
      ∑ j, spatialSecondPartial ψ j j z) = fun z ↦ ∑ i, ∑ j, L i j z := by
    funext z
    simp only [L, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have hsumL (i : Fin 3) : Integrable (fun z ↦ ∑ j, L i j z) volume :=
    integrable_finsetSum _ (fun j _ ↦ hL i j)
  have hsumR (i : Fin 3) : Integrable (fun z ↦ ∑ j, R i j z) volume :=
    integrable_finsetSum _ (fun j _ ↦ hR i j)
  rw [hfun]
  refine ⟨integrable_finsetSum _ (fun i _ ↦ hsumL i),
    integrable_finsetSum _ (fun i _ ↦ hsumR i), ?_⟩
  change (∫ z : Vec3 × ℝ, ∑ i, ∑ j, L i j z) = -(∫ z, ∑ i, ∑ j, R i j z)
  rw [integral_finsetSum _ (fun i _ ↦ hsumL i),
    integral_finsetSum _ (fun i _ ↦ hsumR i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ ↦ hL i j),
    integral_finsetSum _ (fun j _ ↦ hR i j), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ hEq i j

/-- The actual moving-coordinate divergence equation also cancels every
smooth time-weighted convection pairing. -/
theorem suitable_accelerated_time_weighted_divergence
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (htube : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) B J)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) :
    Integrable (fun z : Vec3 × ℝ ↦ θ z.2 *
      ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z) volume ∧
      ∫ z : Vec3 × ℝ, θ z.2 *
        ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z = 0 := by
  have htest := spaceTimeTestFunction_mul_smooth hψ (hθ.comp contDiff_snd)
  have hderiv (i : Fin 3) (z : ParabolicPoint) :
      spatialPartial (fun w : Vec3 × ℝ ↦ ψ w * θ w.2) i z =
        spatialPartial ψ i z * θ z.2 :=
    spatialPartial_mul_time (χ := θ) hψ.1 i (z.1, z.2)
  have hfun : (fun z : Vec3 × ℝ ↦ θ z.2 *
      ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z) =
      fun z : Vec3 × ℝ ↦ ∑ i, acceleratedVelocity X m u z i *
        spatialPartial (fun w : Vec3 × ℝ ↦ ψ w * θ w.2) i z := by
    funext z
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hderiv]
    ring
  rw [hfun]
  exact suitable_accelerated_global_divergence hsol hX hm htube htest

/-- Testing the genuine transformed divergence equation against the affine
acceleration potential times a scalar test gives the remaining acceleration
cancellation needed in the relative energy inequality. -/
theorem suitable_accelerated_affine_velocity_pairing
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m a : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (htube : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) B J) :
    Integrable (fun z : Vec3 × ℝ ↦ (∑ i : Fin 3, a z.2 i * z.1 i) *
        ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z) volume ∧
      Integrable (fun z : Vec3 × ℝ ↦
        (∑ i, acceleratedVelocity X m u z i * a z.2 i) * ψ z) volume ∧
        (∫ z : Vec3 × ℝ, (∑ i : Fin 3, a z.2 i * z.1 i) *
          ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z) =
          -(∫ z : Vec3 × ℝ, (∑ i, acceleratedVelocity X m u z i * a z.2 i) * ψ z) := by
  let A : Vec3 × ℝ → ℝ := fun z ↦ ∑ i : Fin 3, a z.2 i * z.1 i
  let D : Vec3 × ℝ → ℝ :=
    fun z ↦ ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z
  let V : Vec3 × ℝ → ℝ :=
    fun z ↦ (∑ i, acceleratedVelocity X m u z i * a z.2 i) * ψ z
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := by dsimp [A]; fun_prop
  obtain ⟨hD, hDzero⟩ := suitable_accelerated_global_divergence hsol hX hm htube hψ
  have hADK : IntegrableOn (fun z : ParabolicPoint ↦ D z * A z)
      (tsupport (show ParabolicPoint → ℝ from ψ)) volume := by
    have hDK : IntegrableOn (show ParabolicPoint → ℝ from D)
        (tsupport (show ParabolicPoint → ℝ from ψ)) volume := hD.integrableOn
    have hAcont : Continuous (show ParabolicPoint → ℝ from A) :=
      hA.continuous.comp continuous_parabolicPoint_to_prod
    simpa only [smul_eq_mul] using hDK.smul_continuousOn hAcont.continuousOn
      (isCompact_tsupport_parabolic hψ.2.1)
  have hsupport : Function.support (fun z : ParabolicPoint ↦ D z * A z) ⊆
      tsupport (show ParabolicPoint → ℝ from ψ) := by
    rw [tsupport_parabolic_eq]
    intro z hz
    by_contra hcon
    have hDz : D z = 0 := Finset.sum_eq_zero fun i _ ↦ by
      rw [spatialPartial_eq_zero_off_tsupport hcon i, mul_zero]
    exact hz (mul_eq_zero_of_left hDz _)
  have hAD : Integrable (fun z : Vec3 × ℝ ↦ A z * D z) volume := by
    have h := (integrableOn_iff_integrable_of_support_subset hsupport).mp hADK
    exact h.congr (Eventually.of_forall fun z ↦ mul_comm (D z) (A z))
  have htest := spaceTimeTestFunction_mul_smooth hψ hA
  have hderiv (i : Fin 3) (z : ParabolicPoint) :
      spatialPartial (fun w : Vec3 × ℝ ↦ ψ w * A w) i z =
        spatialPartial ψ i z * A z + ψ z * a z.2 i := by
    calc
      _ = spatialPartial ψ i z * A z + ψ z * spatialPartial A i z :=
        CKN.Core.Step3.spatialPartial_mul_full hψ.1 hA i (z.1, z.2)
      _ = _ := congrArg (fun b : ℝ ↦ spatialPartial ψ i z * A z + ψ z * b)
        (accelerated_affine_pressure_spatialPartial a i z)
  have hfun : (fun z : Vec3 × ℝ ↦ ∑ i, acceleratedVelocity X m u z i *
      spatialPartial (fun w : Vec3 × ℝ ↦ ψ w * A w) i z) =
      fun z : Vec3 × ℝ ↦ A z * D z + V z := by
    funext z
    have hd (i : Fin 3) := hderiv i z
    simp only [hd, D, V, Fin.sum_univ_three]
    ring
  obtain ⟨hnew, hnew_zero⟩ := suitable_accelerated_global_divergence hsol hX hm htube htest
  rw [hfun] at hnew hnew_zero
  have hV : Integrable V volume := by
    have h := hnew.sub hAD
    convert h using 1
    funext z
    change V z = (A z * D z + V z) - A z * D z
    ring
  rw [integral_add (f := fun z ↦ A z * D z) (g := V) hAD hV] at hnew_zero
  exact ⟨hAD, hV, eq_neg_of_add_eq_zero_left hnew_zero⟩

/-- The square of the Euclidean length of a smooth mean is smooth even at
zeros of that mean: it is the finite sum of the squares of its components. -/
theorem frame_mean_square_contDiff
    {m : ℝ → Vec3} (hm : ContDiff ℝ (⊤ : ℕ∞) m) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ vec3EuclideanNorm (m t) ^ 2) := by
  have heq : (fun t ↦ vec3EuclideanNorm (m t) ^ 2) =
      fun t ↦ ∑ i : Fin 3, m t i ^ 2 := by
    funext t
    exact CKN.Foundation.Heat.vec3EuclideanNorm_sq (m t)
  rw [heq]
  fun_prop

/-- The mean-square time derivative is twice its acceleration pairing. -/
theorem frame_mean_square_hasDerivAt
    {m : ℝ → Vec3} {a : Vec3} {t : ℝ} (hma : HasDerivAt m a t) :
    HasDerivAt (fun s ↦ vec3EuclideanNorm (m s) ^ 2)
      (2 * ∑ i : Fin 3, m t i * a i) t := by
  have heq : (fun s ↦ vec3EuclideanNorm (m s) ^ 2) =
      fun s ↦ ∑ i : Fin 3, m s i ^ 2 := by
    funext s
    exact CKN.Foundation.Heat.vec3EuclideanNorm_sq (m s)
  have hi (i : Fin 3) : HasDerivAt (fun s ↦ m s i ^ 2) (2 * m t i * a i) t := by
    simpa using (hasDerivAt_pi.mp hma i).fun_pow 2
  rw [heq]
  convert HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i) using 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Integration by parts supplies the exact mean-square time correction in
the accelerated local energy identity. -/
theorem frame_mean_square_time_pairing
    {m a : ℝ → Vec3} (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hma : ∀ t, HasDerivAt m (a t) t)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) :
    Integrable (fun z : Vec3 × ℝ ↦ vec3EuclideanNorm (m z.2) ^ 2 * timePartial ψ z)
        volume ∧
      Integrable (fun z : Vec3 × ℝ ↦ (∑ i : Fin 3, m z.2 i * a z.2 i) * ψ z) volume ∧
        (∫ z : Vec3 × ℝ, vec3EuclideanNorm (m z.2) ^ 2 * timePartial ψ z) =
          -2 * (∫ z : Vec3 × ℝ, (∑ i : Fin 3, m z.2 i * a z.2 i) * ψ z) := by
  let F : Vec3 × ℝ → ℝ := fun z ↦ vec3EuclideanNorm (m z.2) ^ 2
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (frame_mean_square_contDiff hm).comp contDiff_snd
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ ↦ ∑ i : Fin 3, m z.2 i * a z.2 i) := by fun_prop
  have hI : Integrable (fun z : Vec3 × ℝ ↦ F z * timePartial ψ z) volume :=
    (hF.continuous.mul (contDiff_timePartial hψ).continuous)
      |>.integrable_of_hasCompactSupport (hasCompactSupport_timePartial hcψ).mul_left
  have hJ : Integrable (fun z : Vec3 × ℝ ↦
      (∑ i : Fin 3, m z.2 i * a z.2 i) * ψ z) volume :=
    (hA.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  have hderiv (z : ParabolicPoint) : timePartial F z =
      2 * ∑ i : Fin 3, m z.2 i * a z.2 i := by
    change deriv (fun t ↦ vec3EuclideanNorm (m t) ^ 2) z.2 = _
    exact (frame_mean_square_hasDerivAt (hma z.2)).deriv
  refine ⟨hI, hJ, ?_⟩
  calc
    _ = -(∫ z : Vec3 × ℝ, timePartial F z * ψ z) :=
      integral_mul_timePartial_eq_neg_timePartial_mul hF hψ hcψ
    _ = -(∫ z : Vec3 × ℝ, 2 * ((∑ i : Fin 3, m z.2 i * a z.2 i) * ψ z)) := by
      apply congrArg Neg.neg
      apply integral_congr_ae
      filter_upwards [] with z
      change timePartial (show ParabolicPoint → ℝ from F) z * ψ z = _
      exact (congrArg (fun b : ℝ ↦ b * ψ z) (hderiv z)).trans (by ring)
    _ = _ := by rw [integral_const_mul]; ring

/-- Every smooth time coefficient pairs to zero with the spatial Laplacian
of a compact test, with genuine integrability supplied by compactness. -/
theorem frame_time_coefficient_laplacian_pairing
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) :
    Integrable (fun z : Vec3 × ℝ ↦ θ z.2 * ∑ j, spatialSecondPartial ψ j j z) volume ∧
      ∫ z : Vec3 × ℝ, θ z.2 * ∑ j, spatialSecondPartial ψ j j z = 0 := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ ↦ θ z.2) :=
    hθ.comp contDiff_snd
  have hi (j : Fin 3) : Integrable (fun z : Vec3 × ℝ ↦
      θ z.2 * spatialSecondPartial ψ j j z) volume :=
    (hF.continuous.mul (spatialPartial_contDiff (spatialPartial_contDiff hψ j) j).continuous)
      |>.integrable_of_hasCompactSupport
        (hasCompactSupport_spatialSecondPartial hcψ j j).mul_left
  have heq (j : Fin 3) :
      (∫ z : Vec3 × ℝ, θ z.2 * spatialSecondPartial ψ j j z) = 0 := by
    have h := integral_mul_spatialPartial_eq_neg_spatialPartial_mul hF
      (spatialPartial_contDiff hψ j) (hasCompactSupport_spatialPartial hcψ j) j
    have hzero (z : ParabolicPoint) : spatialPartial (fun w : Vec3 × ℝ ↦ θ w.2) j z =
        0 := by simp [spatialPartial]
    calc
      _ = -(∫ z : Vec3 × ℝ, spatialPartial (fun w : Vec3 × ℝ ↦ θ w.2) j z *
          spatialPartial ψ j z) := h
      _ = 0 := by
        have hz : (∫ z : Vec3 × ℝ, spatialPartial (fun w : Vec3 × ℝ ↦ θ w.2) j z *
            spatialPartial ψ j z) = 0 :=
          integral_eq_zero_of_ae (Eventually.of_forall fun z ↦ mul_eq_zero_of_left (hzero z) _)
        exact (congrArg Neg.neg hz).trans (neg_zero : -(0 : ℝ) = 0)
  have hfun : (fun z : Vec3 × ℝ ↦ θ z.2 * ∑ j, spatialSecondPartial ψ j j z) =
      fun z : Vec3 × ℝ ↦ ∑ j, θ z.2 * spatialSecondPartial ψ j j z := by
    funext z
    exact Finset.mul_sum _ _ _
  rw [hfun]
  refine ⟨integrable_finsetSum _ (fun j _ ↦ hi j), ?_⟩
  rw [integral_finsetSum _ (fun j _ ↦ hi j)]
  exact Finset.sum_eq_zero fun j _ ↦ heq j

/-- The original momentum test giving the relative kinetic energy identity. -/
def acceleratedRelativeTest (X m : ℝ → Vec3) (ψ : Vec3 × ℝ → ℝ) :
    Vec3 × ℝ → Vec3 := fun w ↦ acceleratedTestPullback X ψ w • m w.2

/-- The relative-energy momentum test is a genuine compact smooth test on
the original solution domain. -/
theorem acceleratedRelativeTest_mem_spaceTimeTest
    {Ω B : Set Vec3} {I J : Set ℝ} {X m : ℝ → Vec3}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (htube : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) B J) :
    acceleratedRelativeTest X m ψ ∈ spaceTimeTestFunction (V := Vec3) Ω I := by
  have hΨ := acceleratedTestPullback_mem_spaceTimeTest hX hψ htube
  refine ⟨hΨ.1.smul (hm.comp contDiff_snd), hΨ.2.1.smul_right, ?_⟩
  exact (tsupport_smul_subset_left _ _).trans hΨ.2.2

/-- The abstract relative momentum polynomial is exactly the genuine CKN
momentum density under the smooth accelerated chain rule. -/
theorem accelerated_relative_momentum_density
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    {X m a : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hXm : ∀ t, HasDerivAt X (m t) t) (hma : ∀ t, HasDerivAt m (a t) t)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : ParabolicPoint) :
    frameMomentumDensity u Du p f (acceleratedRelativeTest X m ψ)
        (acceleratedFrameMap X z) =
      frameRelativeMomentumPolynomial (u (acceleratedFrameMap X z)) (m z.2) (a z.2)
        (f (acceleratedFrameMap X z)) (fun j ↦ spatialPartial ψ j z)
        (Du (acceleratedFrameMap X z)) (p (acceleratedFrameMap X z)) (ψ z)
        (timePartial ψ z) := by
  let Ψ := acceleratedTestPullback X ψ
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ := hψ.comp (acceleratedFrameMapProd_contDiff hX).2
  have hmi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ m t i) :=
    (contDiff_apply ℝ ℝ i).comp hm
  have hdi (i : Fin 3) (t : ℝ) : deriv (fun s ↦ m s i) t = a t i :=
    (hasDerivAt_pi.mp (hma t) i).deriv
  have hvalue : Ψ (acceleratedFrameMap X z) = ψ z := by
    simp [Ψ, acceleratedTestPullback, acceleratedFrameMapProd, acceleratedFrameMap]
  have hs (i j : Fin 3) :
      spatialPartial (fun w ↦ acceleratedRelativeTest X m ψ w i) j
          (acceleratedFrameMap X z) = spatialPartial ψ j z * m z.2 i := by
    calc
      _ = spatialPartial Ψ j (acceleratedFrameMap X z) * m z.2 i :=
        spatialPartial_mul_time (χ := fun t ↦ m t i) hΨ j
          ((acceleratedFrameMap X z).1, (acceleratedFrameMap X z).2)
      _ = _ := congrArg (fun b : ℝ ↦ b * m z.2 i)
        (accelerated_spatialPartial_pullback X hψ j z)
  have ht (i : Fin 3) :
      timePartial (fun w ↦ acceleratedRelativeTest X m ψ w i) (acceleratedFrameMap X z) =
        (timePartial ψ z - ∑ j : Fin 3, m z.2 j * spatialPartial ψ j z) * m z.2 i +
          ψ z * a z.2 i := by
    have h := timePartial_mul_time (χ := fun t ↦ m t i) hΨ (hmi i)
      ((acceleratedFrameMap X z).1, (acceleratedFrameMap X z).2)
    change timePartial (fun w : Vec3 × ℝ ↦ Ψ w * m w.2 i) (acceleratedFrameMap X z) = _
    calc
      _ = timePartial Ψ (acceleratedFrameMap X z) * m z.2 i +
          Ψ (acceleratedFrameMap X z) * deriv (fun s ↦ m s i) z.2 := h
      _ = timePartial Ψ (acceleratedFrameMap X z) * m z.2 i +
          Ψ (acceleratedFrameMap X z) * a z.2 i :=
        congrArg (fun b : ℝ ↦ timePartial Ψ (acceleratedFrameMap X z) * m z.2 i +
          Ψ (acceleratedFrameMap X z) * b) (hdi i z.2)
      _ = _ := by
        rw [hvalue]
        exact congrArg (fun b : ℝ ↦ b * m z.2 i + ψ z * a z.2 i)
          (accelerated_timePartial_pullback hψ (z.1, z.2) (hXm z.2))
  have hv (i : Fin 3) :
      acceleratedRelativeTest X m ψ (acceleratedFrameMap X z) i = ψ z * m z.2 i := by
    exact congrArg (fun b : ℝ ↦ b * m z.2 i) hvalue
  simp only [frameMomentumDensity, frameRelativeMomentumPolynomial, ht, hs, hv]
  simp only [Fin.sum_univ_three]
  ring

/-- The exact actual energy-density correction in the smooth accelerating
frame, expressed using the genuine original momentum density. -/
theorem accelerated_relative_energy_density
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    {X m a : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hXm : ∀ t, HasDerivAt X (m t) t) (hma : ∀ t, HasDerivAt m (a t) t)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : ParabolicPoint) :
    localEnergyRhs (acceleratedVelocity X m u) (acceleratedPressure X a p)
        (acceleratedForce X f) ψ (z.1, z.2) -
      localEnergyRhs u p f (acceleratedTestPullback X ψ)
        ((acceleratedFrameMap X z).1, (acceleratedFrameMap X z).2) =
      2 * frameMomentumDensity u Du p f (acceleratedRelativeTest X m ψ)
          (acceleratedFrameMap X z) +
        vec3EuclideanNorm (m z.2) ^ 2 * (timePartial ψ z +
          (∑ j, spatialSecondPartial ψ j j z) +
            ∑ j, acceleratedVelocity X m u z j * spatialPartial ψ j z) +
          2 * (∑ i, u (acceleratedFrameMap X z) i * a z.2 i) * ψ z -
            2 * (∑ i, ∑ j, Du (acceleratedFrameMap X z) i j * m z.2 i *
              spatialPartial ψ j z) -
              2 * (∑ i, u (acceleratedFrameMap X z) i * m z.2 i) *
                (∑ j, spatialSecondPartial ψ j j z) +
                2 * (∑ i : Fin 3, a z.2 i * z.1 i) *
                  ∑ j, acceleratedVelocity X m u z j * spatialPartial ψ j z := by
  let Ψ := acceleratedTestPullback X ψ
  have hs (j : Fin 3) : spatialPartial Ψ j (acceleratedFrameMap X z) =
      spatialPartial ψ j z := accelerated_spatialPartial_pullback X hψ j z
  have hss (j : Fin 3) : spatialSecondPartial Ψ j j (acceleratedFrameMap X z) =
      spatialSecondPartial ψ j j z := accelerated_spatialSecondPartial_pullback X hψ j j z
  have ht : timePartial Ψ (acceleratedFrameMap X z) =
      timePartial ψ z - ∑ j : Fin 3, m z.2 j * spatialPartial ψ j z :=
    accelerated_timePartial_pullback hψ (z.1, z.2) (hXm z.2)
  have hvalue : Ψ (acceleratedFrameMap X z) = ψ z := by
    simp [Ψ, acceleratedTestPullback, acceleratedFrameMapProd, acceleratedFrameMap]
  have hsource : localEnergyRhs u p f Ψ
      ((acceleratedFrameMap X z).1, (acceleratedFrameMap X z).2) =
      frameEnergyPolynomial (u (acceleratedFrameMap X z)) (f (acceleratedFrameMap X z))
        (fun j ↦ spatialPartial ψ j z) (p (acceleratedFrameMap X z)) (ψ z)
        (timePartial ψ z - ∑ j : Fin 3, m z.2 j * spatialPartial ψ j z)
        (∑ j, spatialSecondPartial ψ j j z) := by
    unfold localEnergyRhs frameEnergyPolynomial timePartialProd spatialPartialProd
      spatialSecondPartialProd
    simp only [Prod.eta]
    simp only [hs, hss, ht, hvalue]
  have h := accelerated_relative_energy_expansion (u (acceleratedFrameMap X z)) (m z.2)
    (a z.2) (f (acceleratedFrameMap X z)) (fun j ↦ spatialPartial ψ j z) z.1
    (Du (acceleratedFrameMap X z)) (p (acceleratedFrameMap X z)) (ψ z) (timePartial ψ z)
    (∑ j, spatialSecondPartial ψ j j z)
  rw [hsource]
  rw [← accelerated_relative_momentum_density u Du p f hX hm hXm hma hψ z] at h
  exact h

/-- An actual suitable local energy inequality is a genuine global compact
test inequality, with integrability of both densities established first. -/
theorem suitable_global_energy
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hψnonneg : ∀ z, 0 ≤ ψ z) :
    Integrable (fun z : Vec3 × ℝ ↦ spatialGradientSq u Du z * ψ z) volume ∧
      Integrable (localEnergyRhs u p f ψ) volume ∧
        2 * (∫ z : Vec3 × ℝ, spatialGradientSq u Du z * ψ z) ≤
          ∫ z : Vec3 × ℝ, localEnergyRhs u p f ψ z := by
  obtain ⟨hGon, hEon, _⟩ := hsol.2.2.2.2.2.2.2.2 ψ hψ hψnonneg
  have hEon' : IntegrableOn (fun z : ParabolicPoint ↦ localEnergyRhs u p f ψ (z.1, z.2))
      (tsupport (show ParabolicPoint → ℝ from ψ)) volume := by
    simpa only [localEnergyRhs, timePartialProd, spatialPartialProd,
      spatialSecondPartialProd, Prod.eta] using hEon
  have hGsupport : Function.support (fun z : ParabolicPoint ↦
      spatialGradientSq u Du z * ψ z) ⊆ tsupport (show ParabolicPoint → ℝ from ψ) := by
    intro z hz
    by_contra hcon
    apply hz
    change spatialGradientSq u Du z * (show ParabolicPoint → ℝ from ψ) z = 0
    exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hcon)
  have hEsupport : Function.support
      (fun z : ParabolicPoint ↦ localEnergyRhs u p f ψ (z.1, z.2)) ⊆
        tsupport (show ParabolicPoint → ℝ from ψ) := by
    rw [tsupport_parabolic_eq]
    intro z hz
    by_contra hcon
    exact hz (localEnergyRhs_eq_zero_of_not_mem_tsupport_public hψ.1 hcon)
  have hG : Integrable (fun z : Vec3 × ℝ ↦ spatialGradientSq u Du z * ψ z) volume :=
    (integrableOn_iff_integrable_of_support_subset hGsupport).mp hGon
  have hE : Integrable (localEnergyRhs u p f ψ) volume :=
    (integrableOn_iff_integrable_of_support_subset hEsupport).mp hEon'
  have hGoff (z : ParabolicPoint) (hz : z ∉ spaceTimeSet Ω I) :
      spatialGradientSq u Du z * ψ z = 0 := by
    have hzψ : z ∉ tsupport (show ParabolicPoint → ℝ from ψ) := by
      rw [tsupport_parabolic_eq]
      exact fun hmem ↦ hz (hψ.2.2 hmem)
    change spatialGradientSq u Du z * (show ParabolicPoint → ℝ from ψ) z = 0
    exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hzψ)
  have hEoff (z : ParabolicPoint) (hz : z ∉ spaceTimeSet Ω I) :
      localEnergyRhs u p f ψ z = 0 :=
    localEnergyRhs_eq_zero_of_not_mem_tsupport_public hψ.1 (fun hmem ↦ hz (hψ.2.2 hmem))
  have hineq := suitableWeakSolution_energyInequality hsol hψ hψnonneg
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hGoff,
    setIntegral_eq_integral_of_forall_compl_eq_zero hEoff] at hineq
  exact ⟨hG, hE, hineq⟩

/-- All genuine relative-energy corrections cancel after integration. The
transformed energy density is integrable and has exactly the original
compact-test integral, including an arbitrary transformed force. -/
theorem suitable_accelerated_energy_rhs_integral
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m a : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hXm : ∀ t, HasDerivAt X (m t) t) (hma : ∀ t, HasDerivAt m (a t) t)
    (htube : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) B J)
    (hψnonneg : ∀ z, 0 ≤ ψ z) :
    Integrable (localEnergyRhs (acceleratedVelocity X m u) (acceleratedPressure X a p)
      (acceleratedForce X f) ψ) volume ∧
      (∫ z : Vec3 × ℝ, localEnergyRhs (acceleratedVelocity X m u)
        (acceleratedPressure X a p) (acceleratedForce X f) ψ z) =
        ∫ z : Vec3 × ℝ, localEnergyRhs u p f (acceleratedTestPullback X ψ) z := by
  let Ψ := acceleratedTestPullback X ψ
  have hΨ : Ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I :=
    acceleratedTestPullback_mem_spaceTimeTest hX hψ htube
  have hnΨ : ∀ z, 0 ≤ Ψ z := fun z ↦ hψnonneg _
  have hΦ := acceleratedRelativeTest_mem_spaceTimeTest hX hm htube hψ
  obtain ⟨_, hsource, _⟩ := suitable_global_energy hsol hΨ hnΨ
  obtain ⟨hsourceM, hsourceMzero⟩ := suitable_global_momentum hsol hΦ
  let S : Vec3 × ℝ → ℝ := fun z ↦ localEnergyRhs u p f Ψ (acceleratedFrameMapProd X z)
  let M : Vec3 × ℝ → ℝ := fun z ↦ frameMomentumDensity u Du p f
    (acceleratedRelativeTest X m ψ) (acceleratedFrameMap X z)
  let H : Vec3 × ℝ → ℝ := fun z ↦ vec3EuclideanNorm (m z.2) ^ 2 * timePartial ψ z
  let L : Vec3 × ℝ → ℝ := fun z ↦ vec3EuclideanNorm (m z.2) ^ 2 *
    ∑ j, spatialSecondPartial ψ j j z
  let C : Vec3 × ℝ → ℝ := fun z ↦ vec3EuclideanNorm (m z.2) ^ 2 *
    ∑ j, acceleratedVelocity X m u z j * spatialPartial ψ j z
  let K : Vec3 × ℝ → ℝ := fun z ↦ (∑ i, m z.2 i * a z.2 i) * ψ z
  let V : Vec3 × ℝ → ℝ := fun z ↦ (∑ i, acceleratedVelocity X m u z i * a z.2 i) * ψ z
  let D : Vec3 × ℝ → ℝ := fun z ↦
    ∑ i, ∑ j, Du (acceleratedFrameMap X z) i j * m z.2 i * spatialPartial ψ j z
  let U : Vec3 × ℝ → ℝ := fun z ↦ (∑ i, u (acceleratedFrameMap X z) i * m z.2 i) *
    ∑ j, spatialSecondPartial ψ j j z
  let P : Vec3 × ℝ → ℝ := fun z ↦ (∑ i : Fin 3, a z.2 i * z.1 i) *
    ∑ j, acceleratedVelocity X m u z j * spatialPartial ψ j z
  let R : Vec3 × ℝ → ℝ := fun z ↦
    2 * M z + H z + L z + C z + 2 * (V z + K z) - 2 * D z - 2 * U z + 2 * P z
  have hMP := acceleratedFrameMapProd_measurePreserving X hX.continuous.measurable
  have hEmb := (acceleratedFrameHomeomorph X hX.continuous).measurableEmbedding
  have hS : Integrable S volume := hMP.integrable_comp_of_integrable hsource
  have hM : Integrable M volume := hMP.integrable_comp_of_integrable hsourceM
  have hMzero : ∫ z, M z = 0 :=
    (hMP.integral_comp hEmb _).trans hsourceMzero
  obtain ⟨hH, hK, hHeq⟩ := frame_mean_square_time_pairing hm ha hma hψ.1 hψ.2.1
  obtain ⟨hL, hLzero⟩ :=
    frame_time_coefficient_laplacian_pairing (frame_mean_square_contDiff hm) hψ.1 hψ.2.1
  obtain ⟨hC, hCzero⟩ := suitable_accelerated_time_weighted_divergence hsol hX hm htube hψ
    (frame_mean_square_contDiff hm)
  obtain ⟨hP, hV, hPeq⟩ := suitable_accelerated_affine_velocity_pairing hsol hX hm ha htube hψ
  obtain ⟨hU, hD, hUeq⟩ := suitable_accelerated_gradient_pairing hsol hX hm htube hψ
  change Integrable H volume at hH
  change Integrable K volume at hK
  change Integrable L volume at hL
  change Integrable C volume at hC
  change Integrable P volume at hP
  change Integrable V volume at hV
  change Integrable U volume at hU
  change Integrable D volume at hD
  change (∫ z, H z) = -2 * (∫ z, K z) at hHeq
  change (∫ z, L z) = 0 at hLzero
  change (∫ z, C z) = 0 at hCzero
  change (∫ z, P z) = -(∫ z, V z) at hPeq
  change (∫ z, U z) = -(∫ z, D z) at hUeq
  have hfun : localEnergyRhs (acceleratedVelocity X m u) (acceleratedPressure X a p)
      (acceleratedForce X f) ψ = fun z : Vec3 × ℝ ↦ S z + R z := by
    funext z
    have h := accelerated_relative_energy_density u Du p f hX hm hXm hma hψ.1 z
    have hR : localEnergyRhs (acceleratedVelocity X m u) (acceleratedPressure X a p)
        (acceleratedForce X f) ψ z - S z = R z := by
      refine h.trans ?_
      dsimp only [R, M, H, L, C, K, V, D, U, P]
      simp only [acceleratedVelocity, Pi.sub_apply, Fin.sum_univ_three]
      ring
    linarith only [hR]
  have h0 : Integrable (fun z ↦ 2 * M z) volume := hM.const_mul 2
  have h1 : Integrable (fun z ↦ 2 * M z + H z) volume := h0.add hH
  have h2 : Integrable (fun z ↦ 2 * M z + H z + L z) volume := h1.add hL
  have h3 : Integrable (fun z ↦ 2 * M z + H z + L z + C z) volume := h2.add hC
  have hVK : Integrable (fun z ↦ 2 * (V z + K z)) volume := (hV.add hK).const_mul 2
  have h4 : Integrable (fun z ↦ 2 * M z + H z + L z + C z + 2 * (V z + K z)) volume :=
    h3.add hVK
  have hD2 : Integrable (fun z ↦ 2 * D z) volume := hD.const_mul 2
  have hU2 : Integrable (fun z ↦ 2 * U z) volume := hU.const_mul 2
  have hP2 : Integrable (fun z ↦ 2 * P z) volume := hP.const_mul 2
  have h5 : Integrable (fun z ↦
      2 * M z + H z + L z + C z + 2 * (V z + K z) - 2 * D z) volume := h4.sub hD2
  have h6 : Integrable (fun z ↦
      2 * M z + H z + L z + C z + 2 * (V z + K z) - 2 * D z - 2 * U z) volume :=
    h5.sub hU2
  have hRInt : Integrable R volume := h6.add hP2
  have hRformula : (∫ z, R z) = 2 * (∫ z, M z) + (∫ z, H z) + (∫ z, L z) +
      (∫ z, C z) + 2 * ((∫ z, V z) + (∫ z, K z)) - 2 * (∫ z, D z) -
        2 * (∫ z, U z) + 2 * (∫ z, P z) := by
    change (∫ z : Vec3 × ℝ,
      2 * M z + H z + L z + C z + 2 * (V z + K z) - 2 * D z - 2 * U z + 2 * P z) = _
    rw [integral_add
      (f := fun z ↦ 2 * M z + H z + L z + C z + 2 * (V z + K z) - 2 * D z - 2 * U z)
      (g := fun z ↦ 2 * P z) h6 hP2,
      integral_sub
        (f := fun z ↦ 2 * M z + H z + L z + C z + 2 * (V z + K z) - 2 * D z)
        (g := fun z ↦ 2 * U z) h5 hU2,
      integral_sub (f := fun z ↦ 2 * M z + H z + L z + C z + 2 * (V z + K z))
        (g := fun z ↦ 2 * D z) h4 hD2,
      integral_add (f := fun z ↦ 2 * M z + H z + L z + C z)
        (g := fun z ↦ 2 * (V z + K z)) h3 hVK,
      integral_add (f := fun z ↦ 2 * M z + H z + L z) (g := C) h2 hC,
      integral_add (f := fun z ↦ 2 * M z + H z) (g := L) h1 hL,
      integral_add (f := fun z ↦ 2 * M z) (g := H) h0 hH]
    simp only [integral_const_mul, integral_add (f := V) (g := K) hV hK]
  have hRzero : ∫ z, R z = 0 := by
    rw [hRformula, hMzero, hLzero, hCzero, hHeq, hUeq, hPeq]
    ring
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hS.add hRInt
  · rw [hfun, integral_add (f := S) (g := R) hS hRInt, hRzero, add_zero]
    exact hMP.integral_comp hEmb (localEnergyRhs u p f Ψ)

/-- The actual suitable local energy inequality is preserved by every smooth
accelerating frame with its affine acceleration pressure. No transformed
equation or transformed suitability is assumed. -/
theorem suitable_accelerated_local_energy
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m a : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hXm : ∀ t, HasDerivAt X (m t) t) (hma : ∀ t, HasDerivAt m (a t) t)
    (htube : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) B J)
    (hψnonneg : ∀ z, 0 ≤ ψ z) :
    IntegrableOn (fun z : ParabolicPoint ↦
        spatialGradientSq (acceleratedVelocity X m u) (acceleratedGradient X Du) z * ψ z)
      (tsupport (show ParabolicPoint → ℝ from ψ)) volume ∧
      IntegrableOn (fun z : ParabolicPoint ↦ localEnergyRhs (acceleratedVelocity X m u)
        (acceleratedPressure X a p) (acceleratedForce X f) ψ z)
        (tsupport (show ParabolicPoint → ℝ from ψ)) volume ∧
        2 * (∫ z in spaceTimeSet B J,
          spatialGradientSq (acceleratedVelocity X m u) (acceleratedGradient X Du) z * ψ z) ≤
          ∫ z in spaceTimeSet B J, localEnergyRhs (acceleratedVelocity X m u)
            (acceleratedPressure X a p) (acceleratedForce X f) ψ z := by
  let Ψ := acceleratedTestPullback X ψ
  have hΨ : Ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I :=
    acceleratedTestPullback_mem_spaceTimeTest hX hψ htube
  have hnΨ : ∀ z, 0 ≤ Ψ z := fun z ↦ hψnonneg _
  obtain ⟨hsourceG, _, hsourceIneq⟩ := suitable_global_energy hsol hΨ hnΨ
  obtain ⟨hE, hEq⟩ :=
    suitable_accelerated_energy_rhs_integral hsol hX hm ha hXm hma htube hψ hψnonneg
  have hGfun : (fun z : Vec3 × ℝ ↦
      spatialGradientSq (acceleratedVelocity X m u) (acceleratedGradient X Du) z * ψ z) =
      (fun w : Vec3 × ℝ ↦ spatialGradientSq u Du w * Ψ w) ∘ acceleratedFrameMapProd X := by
    funext z
    have hvalue : Ψ (acceleratedFrameMapProd X z) = ψ z := by
      simp [Ψ, acceleratedTestPullback, acceleratedFrameMapProd]
    change spatialGradientSq (acceleratedVelocity X m u) (acceleratedGradient X Du) z * ψ z =
      spatialGradientSq u Du (acceleratedFrameMap X z) * Ψ (acceleratedFrameMapProd X z)
    rw [hvalue]
    rfl
  have hMP := acceleratedFrameMapProd_measurePreserving X hX.continuous.measurable
  have hEmb := (acceleratedFrameHomeomorph X hX.continuous).measurableEmbedding
  have hG : Integrable (fun z : Vec3 × ℝ ↦
      spatialGradientSq (acceleratedVelocity X m u) (acceleratedGradient X Du) z * ψ z)
      volume := by
    rw [hGfun]
    exact hMP.integrable_comp_of_integrable hsourceG
  have hGEq : (∫ z : Vec3 × ℝ,
      spatialGradientSq (acceleratedVelocity X m u) (acceleratedGradient X Du) z * ψ z) =
      ∫ z : Vec3 × ℝ, spatialGradientSq u Du z * Ψ z := by
    rw [hGfun]
    exact hMP.integral_comp hEmb (fun z : Vec3 × ℝ ↦ spatialGradientSq u Du z * Ψ z)
  have hineq : 2 * (∫ z : Vec3 × ℝ,
      spatialGradientSq (acceleratedVelocity X m u) (acceleratedGradient X Du) z * ψ z) ≤
      ∫ z : Vec3 × ℝ, localEnergyRhs (acceleratedVelocity X m u)
        (acceleratedPressure X a p) (acceleratedForce X f) ψ z := by
    rw [hGEq, hEq]
    exact hsourceIneq
  refine ⟨hG.integrableOn, hE.integrableOn, ?_⟩
  have hGoff (z : ParabolicPoint) (hz : z ∉ spaceTimeSet B J) :
      spatialGradientSq (acceleratedVelocity X m u) (acceleratedGradient X Du) z * ψ z = 0 := by
    have hzψ : z ∉ tsupport (show ParabolicPoint → ℝ from ψ) := by
      rw [tsupport_parabolic_eq]
      exact fun hmem ↦ hz (hψ.2.2 hmem)
    change spatialGradientSq (acceleratedVelocity X m u) (acceleratedGradient X Du) z *
      (show ParabolicPoint → ℝ from ψ) z = 0
    exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hzψ)
  have hEoff (z : ParabolicPoint) (hz : z ∉ spaceTimeSet B J) :
      localEnergyRhs (acceleratedVelocity X m u) (acceleratedPressure X a p)
        (acceleratedForce X f) ψ z = 0 :=
    localEnergyRhs_eq_zero_of_not_mem_tsupport_public hψ.1 (fun hmem ↦ hz (hψ.2.2 hmem))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hGoff,
    setIntegral_eq_integral_of_forall_compl_eq_zero hEoff]
  exact hineq

end FluidSingularSets
