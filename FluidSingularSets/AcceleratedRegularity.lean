-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.AcceleratedData
public import FluidSingularSets.BoundedRegularity

@[expose] public section

open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A full open neighborhood with an actual essential velocity bound. -/
def HasLocalAEVelocityBound (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : Prop :=
  ∃ U : Set ParabolicPoint, IsOpen U ∧ z ∈ U ∧
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ w ∂volume.restrict U, vec3EuclideanNorm (u w) ≤ A

@[simp] theorem acceleratedParabolicHomeomorph_apply
    (X : ℝ → Vec3) (hX : Continuous X) (w : ParabolicPoint) :
    acceleratedParabolicHomeomorph X hX w = acceleratedFrameMap X w := rfl

/-- Essential boundedness transfers through the actual moving frame in both
directions. Continuity of the mean supplies its local bound; no modulus of
continuity is required. The neighborhoods are open on both sides of time. -/
theorem accelerated_local_ae_bound_iff
    {X m : ℝ → Vec3} (hX : Continuous X) (hm : Continuous m)
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint} :
    HasLocalAEVelocityBound (acceleratedVelocity X m u) z ↔
      HasLocalAEVelocityBound u (acceleratedFrameMap X z) := by
  let H := acceleratedParabolicHomeomorph X hX
  let M : ℝ := vec3EuclideanNorm (m z.2) + 1
  let V : Set ParabolicPoint := {w | vec3EuclideanNorm (m w.2) < M}
  have hV : IsOpen V := isOpen_lt
    ((CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp hm).comp
      continuous_snd_parabolicPoint)
    continuous_const
  have hzV : z ∈ V := by dsimp [V, M]; linarith
  have hM : 0 ≤ M := by dsimp [M]; linarith [vec3EuclideanNorm_nonneg (m z.2)]
  have hMP : MeasurePreserving H volume volume :=
    acceleratedFrameMap_measurePreserving X hX.measurable
  constructor
  · rintro ⟨U, hU, hzU, A, hA, hbound⟩
    let W := U ∩ V
    have hW : IsOpen W := hU.inter hV
    have hpre : H ⁻¹' (H '' W) = W := H.toEquiv.preimage_image W
    have hMPr : MeasurePreserving H (volume.restrict W) (volume.restrict (H '' W)) := by
      simpa only [hpre] using hMP.restrict_preimage_emb H.measurableEmbedding (H '' W)
    refine ⟨H '' W, H.isOpenMap _ hW, ⟨z, ⟨hzU, hzV⟩, rfl⟩,
      A + M, add_nonneg hA hM, ?_⟩
    rw [← hMPr.map_eq]
    apply H.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hbound,
      ae_restrict_mem hW.measurableSet] with w hw hwW
    have hmW : vec3EuclideanNorm (m w.2) ≤ M := hwW.2.le
    have heq : u (H w) = acceleratedVelocity X m u w + m w.2 := by
      simp [H, acceleratedVelocity]
    rw [heq]
    exact (vec3EuclideanNorm_add_le _ _).trans (add_le_add hw hmW)
  · rintro ⟨U, hU, hzU, A, hA, hbound⟩
    let W := H ⁻¹' U ∩ V
    have hW : IsOpen W := (hU.preimage H.continuous).inter hV
    have hMPr : MeasurePreserving H (volume.restrict (H ⁻¹' U))
        (volume.restrict U) := hMP.restrict_preimage_emb H.measurableEmbedding U
    have hbound' := hMPr.quasiMeasurePreserving.ae hbound
    refine ⟨W, hW, ⟨hzU, hzV⟩, A + M, add_nonneg hA hM, ?_⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hbound',
      ae_restrict_mem hW.measurableSet] with w hw hwW
    have hmW : vec3EuclideanNorm (m w.2) ≤ M := hwW.2.le
    exact (vec3EuclideanNorm_sub_le _ _).trans (add_le_add hw hmW)

/-- A raw CKN Hölder representative supplies a full local essential bound. -/
theorem regular_has_local_ae_velocity_bound
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3} {z : ParabolicPoint}
    (hreg : CKN.IsRegularPoint Ω I u z) : HasLocalAEVelocityBound u z := by
  obtain ⟨_, U, hU, hzU, _, _, _, _, w, hae, A, _, hA, _, hbound, _⟩ := hreg
  refine ⟨U, hU, hzU, A, hA, ?_⟩
  filter_upwards [hae, ae_restrict_mem hU.measurableSet] with y hy hyU
  rw [← hy]
  exact hbound y hyU

/-- Every full raw open neighborhood contains a closed backward CKN cylinder. -/
theorem exists_closure_raw_cylinder_subset_open
    {U : Set ParabolicPoint} {z : ParabolicPoint} (hU : IsOpen U) (hz : z ∈ U) :
    ∃ R : ℝ, 0 < R ∧ closure (parabolicCylinder z.1 z.2 R) ⊆ U := by
  let H := CKNChallenge.parabolicToEuclideanHomeomorph
  obtain ⟨R, hR, hsub⟩ := exists_closure_cylinder_subset_open
    (H.isOpenMap U hU) (show H z ∈ H '' U from ⟨z, hz, rfl⟩)
  refine ⟨R, hR, ?_⟩
  intro w hw
  have hmem : H w ∈ H '' U := hsub
    ((CKNChallenge.mem_closure_cylinder_iff_mem_closure_Q hR z w).mp hw)
  obtain ⟨y, hy, heq⟩ := hmem
  exact H.injective heq ▸ hy

/-- Actual unforced suitability converts a full local essential bound into
the CKN Hölder-representative regularity predicate. -/
theorem suitable_regular_of_local_ae_velocity_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} (hz : z ∈ spaceTimeSet Ω I)
    (hbound : HasLocalAEVelocityBound u z) : CKN.IsRegularPoint Ω I u z := by
  obtain ⟨U, hU, hzU, A, hA, hboundU⟩ := hbound
  obtain ⟨R, hR, hsub⟩ := exists_closure_raw_cylinder_subset_open
    (hU.inter (isOpen_spaceTimeSet Ω I hsol.1 hsol.2.1)) ⟨hzU, hz⟩
  exact suitable_regular_of_ae_bound hsol hR hA (hsub.trans inter_subset_right)
    (ae_restrict_of_ae_restrict_of_subset
      (subset_closure.trans (hsub.trans inter_subset_left)) hboundU)

/-- The two regularity conventions agree for actual suitable solutions at
their interior carrier points. -/
theorem suitable_regular_iff_local_ae_velocity_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} (hz : z ∈ spaceTimeSet Ω I) :
    CKN.IsRegularPoint Ω I u z ↔ HasLocalAEVelocityBound u z :=
  ⟨regular_has_local_ae_velocity_bound,
    suitable_regular_of_local_ae_velocity_bound hsol hz⟩

/-- An actual source solution is regular at the physical image of any native
point where the actual relative velocity is locally essentially bounded. -/
theorem suitable_regular_of_accelerated_local_ae_bound
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {X m : ℝ → Vec3} (hX : Continuous X) (hm : Continuous m)
    (htube : acceleratedFrameMap X '' spaceTimeSet B J ⊆ spaceTimeSet Ω I)
    {z : ParabolicPoint} (hz : z ∈ spaceTimeSet B J)
    (hbound : HasLocalAEVelocityBound (acceleratedVelocity X m u) z) :
    CKN.IsRegularPoint Ω I u (acceleratedFrameMap X z) :=
  suitable_regular_of_local_ae_velocity_bound hsol (htube ⟨z, hz, rfl⟩)
    ((accelerated_local_ae_bound_iff hX hm).mp hbound)

/-- Genuine source and relative suitability make regularity equivalent
across a continuous moving frame. Full open neighborhoods are used at the
native and physical points, including both sides of the time coordinate. -/
theorem suitable_accelerated_regular_iff
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {X m acc : ℝ → Vec3} (hX : Continuous X) (hm : Continuous m)
    (hrelative : IsSuitableWeakSolutionIntegrable B J q (acceleratedVelocity X m u)
      (acceleratedGradient X Du) (acceleratedPressure X acc p) (fun _ ↦ 0))
    (htube : acceleratedFrameMap X '' spaceTimeSet B J ⊆ spaceTimeSet Ω I)
    {z : ParabolicPoint} (hz : z ∈ spaceTimeSet B J) :
    CKN.IsRegularPoint Ω I u (acceleratedFrameMap X z) ↔
      CKN.IsRegularPoint B J (acceleratedVelocity X m u) z := by
  rw [suitable_regular_iff_local_ae_velocity_bound hsol (htube ⟨z, hz, rfl⟩),
    suitable_regular_iff_local_ae_velocity_bound hrelative hz]
  exact (accelerated_local_ae_bound_iff hX hm).symm

open CKNChallenge in
/-- The actual ordinary-coordinate source solution has the specified local
almost-everywhere Hölder representative at the physical image of a bounded
native-frame point. Only a continuous path and continuous mean are needed. -/
theorem suitable_holderRegular_of_accelerated_local_ae_bound
    {Ω : Set Space} {I : Set ℝ} {q : ℝ≥0} (hq : 5 / 2 < (q : ℝ))
    (sol : LocalWeakNSESolution Ω I q) (hforce : sol.f = fun _ ↦ 0)
    {B : Set Vec3} {J : Set ℝ} {X m : ℝ → Vec3}
    (hX : Continuous X) (hm : Continuous m)
    (htube : acceleratedFrameMap X '' spaceTimeSet B J ⊆ spaceTimeSet (rawSpace Ω) I)
    {z : ParabolicPoint} (hz : z ∈ spaceTimeSet B J)
    (hbound : HasLocalAEVelocityBound (acceleratedVelocity X m (pullVelocity sol.u)) z) :
    IsHolderRegularPoint sol.u (parabolicToEuclideanHomeomorph (acceleratedFrameMap X z)) := by
  have hraw : IsSuitableWeakSolutionIntegrable (rawSpace Ω) I (q : ℝ)
      (pullVelocity sol.u) (pullGradient sol.Dxu) (pullScalar sol.p) (fun _ ↦ 0) := by
    have h := CKN.isSuitableWeakSolution_iff_integrable.mp (rawSuitableWeakSolution hq sol)
    have hzero : pullVelocity (fun _ ↦ 0) = fun _ ↦ 0 := by
      funext w
      change rawToEuclidean.symm 0 = 0
      exact map_zero _
    rw [hforce, hzero] at h
    exact h
  exact isHolderRegularPoint_of_rawRegular
    (suitable_regular_of_accelerated_local_ae_bound hraw hX hm htube hz hbound)

end FluidSingularSets
