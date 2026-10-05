-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.AcceleratedData

/-!
# Moving-frame data for integrable acceleration

The affine acceleration pressure needs only the actual time `L^(3/2)` class.
Its spatial coordinates are bounded on each compact local box. Pulling back the
acceleration by the time projection and multiplying by these coordinates keeps
it in the required pressure class. The genuine zero-acceleration data therefore
supply all other clauses for an absolutely continuous moving mean.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A time-dependent actual `MemLp` field has the same class on a product with
a spatial set of finite volume. The time marginal is exactly scaled volume. -/
theorem accelerated_time_memLp_product {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {J : Set ℝ} (hB : volume B < ⊤)
    {a : ℝ → E} {b : ℝ≥0∞} (ha : MemLp a b (volume.restrict J)) :
    MemLp (fun z : ParabolicPoint ↦ a z.2) b
      (volume.restrict (spaceTimeSet B J)) := by
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hB.ne
  have hmpProd : MeasurePreserving (Prod.snd : Vec3 × ℝ → ℝ)
      ((volume.restrict B).prod (volume.restrict J))
      (volume B • volume.restrict J) := by
    refine ⟨measurable_snd, ?_⟩
    rw [Measure.map_snd_prod, Measure.restrict_apply_univ]
  have hmp : MeasurePreserving (fun z : ParabolicPoint ↦ z.2)
      (volume.restrict (spaceTimeSet B J)) (volume B • volume.restrict J) := by
    rw [spaceTimeSet, volume_parabolicPoint_eq_prod, ← Measure.prod_restrict]
    exact hmpProd
  exact (ha.smul_measure hB.ne).comp_measurePreserving hmp

/-- The actual affine pressure from an `L^(3/2)` acceleration has the required
joint pressure class on every spatially and temporally compact box. -/
theorem accelerated_affine_pressure_memLp
    {B : Set Vec3} {J : Set ℝ} (hB : IsOpen B) (hJ : MeasurableSet J)
    (hBc : IsCompact (closure B)) (hJc : IsCompact (closure J))
    {a : ℝ → Vec3} (ha : MemLp a (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict J)) :
    MemLp (fun z : ParabolicPoint ↦ ∑ i : Fin 3, a z.2 i * z.1 i)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet B J)) := by
  have hBvol : volume B < ⊤ := (measure_mono subset_closure).trans_lt hBc.measure_lt_top
  have hK : IsCompact (spaceTimeSet (closure B) (closure J)) :=
    accelerated_isCompact_product hBc hJc
  have hsub : spaceTimeSet B J ⊆ spaceTimeSet (closure B) (closure J) :=
    fun _ hz ↦ ⟨subset_closure hz.1, subset_closure hz.2⟩
  let : IsFiniteMeasure (volume.restrict (spaceTimeSet B J)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hsub).trans_lt hK.measure_lt_top).ne
  have hat := accelerated_time_memLp_product hBvol ha
  obtain ⟨C, hC⟩ := hBc.isBounded.exists_norm_le
  have hterm (i : Fin 3) : MemLp (fun z : ParabolicPoint ↦ a z.2 i * z.1 i)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet B J)) := by
    have hcoord : MemLp (fun z : ParabolicPoint ↦ z.1 i) ⊤
        (volume.restrict (spaceTimeSet B J)) := by
      apply MemLp.of_bound
        (((continuous_apply i).comp continuous_fst_parabolicPoint).aestronglyMeasurable) C
      filter_upwards [ae_restrict_mem (hB.measurableSet.prod hJ)] with z hz
      exact (norm_le_pi_norm z.1 i).trans (hC z.1 (subset_closure hz.1))
    exact ((memLp_pi_iff).1 hat i).mul hcoord
  simpa using memLp_finsetSum Finset.univ (fun i _ ↦ hterm i)


/-- The genuine affine pressure is locally `L^(3/2)` when the actual acceleration
has only that time class. No continuity of the acceleration is required. -/
theorem suitable_accelerated_pressure_memLp_of_acceleration
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m a : ℝ → Vec3} (hX : Continuous X) (hm : Continuous m)
    (ha : MemLp a (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict J))
    (hB : IsOpen B) (hJ : IsOpen J) (hJord : OrdConnected J)
    (htube : acceleratedFrameMap X '' spaceTimeSet B J ⊆ spaceTimeSet Ω I)
    {B' : Set Vec3} {J' : Set ℝ} (hbox : localBox B J B' J') :
    MemLp (acceleratedPressure X a p) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet B' J')) := by
  have hbase := suitable_accelerated_data hsol hX hm (continuous_const :
    Continuous (fun _ : ℝ ↦ (0 : Vec3))) hB hJ hJord htube
  have hppull : MemLp (fun z : ParabolicPoint ↦ p (acceleratedFrameMap X z))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet B' J')) := by
    have hp0 := hbase.memLp_pressure hbox
    have heq : acceleratedPressure X (fun _ : ℝ ↦ (0 : Vec3)) p =
        (fun z : ParabolicPoint ↦ p (acceleratedFrameMap X z)) := by
      funext z
      change p (acceleratedFrameMap X z) + ∑ i : Fin 3, (0 : ℝ) * z.1 i = _
      simp
    rw [heq] at hp0
    exact hp0
  have htime : J' ⊆ J := fun _ ht ↦ hbox.2.2.2.2.2 (subset_closure ht)
  have ha' := ha.mono_measure (Measure.restrict_mono htime le_rfl)
  have haffine := accelerated_affine_pressure_memLp hbox.1
    hbox.2.2.2.1.measurableSet hbox.2.1 hbox.2.2.2.2.1 ha'
  exact hppull.add haffine

/-- The entire actual moving-frame data predicate holds for an acceleration in
time `L^(3/2)`. An absolutely continuous mean with that derivative therefore
satisfies every data clause on its genuine tube without a smoothness shortcut. -/
theorem suitable_accelerated_data_of_acceleration_memLp
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m a : ℝ → Vec3} (hX : Continuous X) (hm : Continuous m)
    (ha : MemLp a (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict J))
    (hB : IsOpen B) (hJ : IsOpen J) (hJord : OrdConnected J)
    (htube : acceleratedFrameMap X '' spaceTimeSet B J ⊆ spaceTimeSet Ω I) :
    IsSuitableWeakSolutionData B J q (acceleratedVelocity X m u)
      (acceleratedGradient X Du) (acceleratedPressure X a p) (acceleratedForce X f) := by
  have hbase := suitable_accelerated_data hsol hX hm (continuous_const :
    Continuous (fun _ : ℝ ↦ (0 : Vec3))) hB hJ hJord htube
  refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1,
    hbase.2.2.2.2.1, ?_⟩
  intro B' J' hbox
  have hp := suitable_accelerated_pressure_memLp_of_acceleration
    hsol hX hm ha hB hJ hJord htube hbox
  exact ⟨hbase.aestronglyMeasurable_velocity hbox,
    hbase.aestronglyMeasurable_gradient hbox, hp.aestronglyMeasurable,
    hbase.aestronglyMeasurable_force hbox, hbase.essSup_sliceEnergy_lt_top hbox,
    hbase.energy_lintegral_lt_top hbox, hp, hbase.memLp_force hbox,
    hbase.hasWeakGradientOn_slice hbox⟩

end FluidSingularSets
