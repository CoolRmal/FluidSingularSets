-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.AcceleratedData
public import CKN.ClassEquivalence.VelocityTenThirds
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The continuous volume-preserving spatial translation associated to a path. -/
def acceleratedFrameContinuousMap (X : ℝ → Vec3) (hX : Continuous X) :
    C(Vec3 × ℝ, Vec3 × ℝ) :=
  ⟨acceleratedFrameMapProd X, (acceleratedFrameHomeomorph X hX).continuous⟩

/-- Uniform convergence of paths on compact time sets gives compact-open
convergence of their moving space-time translations. -/
theorem tendsto_acceleratedFrameContinuousMap
    {α : Type*} {l : Filter α} {Xs : α → ℝ → Vec3} {X : ℝ → Vec3}
    (hXs : ∀ n, Continuous (Xs n)) (hX : Continuous X)
    (hconv : ∀ T : Set ℝ, IsCompact T → TendstoUniformlyOn Xs X l T) :
    Tendsto (fun n ↦ acceleratedFrameContinuousMap (Xs n) (hXs n)) l
      (𝓝 (acceleratedFrameContinuousMap X hX)) := by
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (hconv (Prod.snd '' K) (hK.image continuous_snd)) ε hε] with n hn
  intro z hz
  have h := hn z.2 ⟨z, hz, rfl⟩
  simpa [acceleratedFrameContinuousMap, acceleratedFrameMapProd,
    Prod.dist_eq, dist_add_right] using h

/-- Strong global `L^p` continuity of moving translations is valid for every
finite exponent at least one, including rough measurable source fields. -/
theorem tendsto_eLpNorm_moving_translation
    {E : Type*} [NormedAddCommGroup E]
    {α : Type*} {l : Filter α} {Xs : α → ℝ → Vec3} {X : ℝ → Vec3}
    (hXs : ∀ n, Continuous (Xs n)) (hX : Continuous X)
    (hconv : ∀ T : Set ℝ, IsCompact T → TendstoUniformlyOn Xs X l T)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {g : Vec3 × ℝ → E} (hg : MemLp g p volume) :
    Tendsto (fun n ↦ eLpNorm
      ((g ∘ acceleratedFrameMapProd (Xs n)) - (g ∘ acceleratedFrameMapProd X)) p volume)
      l (𝓝 0) := by
  let maps := fun n ↦ acceleratedFrameContinuousMap (Xs n) (hXs n)
  let map₀ := acceleratedFrameContinuousMap X hX
  have hm : ∀ n, MeasurePreserving (maps n) volume volume := fun n ↦
    acceleratedFrameMapProd_measurePreserving (Xs n) (hXs n).measurable
  have hm₀ : MeasurePreserving map₀ volume volume :=
    acceleratedFrameMapProd_measurePreserving X hX.measurable
  have hmaps : Tendsto maps l (𝓝 map₀) :=
    tendsto_acceleratedFrameContinuousMap hXs hX hconv
  have hLp := (tendsto_const_nhds : Tendsto (fun _ : α ↦ hg.toLp g) l
    (𝓝 (hg.toLp g))).compMeasurePreservingLp hmaps hm hm₀ hp
  have hLp' : Tendsto
      (fun n ↦ (hg.comp_measurePreserving (hm n)).toLp (g ∘ maps n)) l
      (𝓝 ((hg.comp_measurePreserving hm₀).toLp (g ∘ map₀))) := hLp
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
    (fun n ↦ hg.comp_measurePreserving (hm n)) _
      (hg.comp_measurePreserving hm₀)).mp hLp'

/-- Local strong `L^p` convergence follows from one common measurable source
tube carrying finite `L^p` mass. Neither pointwise continuity nor an assumed
convergence property is required of the source field. -/
theorem tendsto_eLpNorm_moving_translation_local
    {E : Type*} [NormedAddCommGroup E]
    {α : Type*} {l : Filter α} {Xs : α → ℝ → Vec3} {X : ℝ → Vec3}
    (hXs : ∀ n, Continuous (Xs n)) (hX : Continuous X)
    (hconv : ∀ T : Set ℝ, IsCompact T → TendstoUniformlyOn Xs X l T)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {S K : Set (Vec3 × ℝ)} (hS : MeasurableSet S) (hK : MeasurableSet K)
    (himages : ∀ᶠ n in l, acceleratedFrameMapProd (Xs n) '' S ⊆ K)
    (himage : acceleratedFrameMapProd X '' S ⊆ K)
    {g : Vec3 × ℝ → E} (hg : MemLp g p (volume.restrict K)) :
    Tendsto (fun n ↦ eLpNorm
      ((g ∘ acceleratedFrameMapProd (Xs n)) - (g ∘ acceleratedFrameMapProd X)) p
        (volume.restrict S)) l (𝓝 0) := by
  have hgK : MemLp (K.indicator g) p volume := (memLp_indicator_iff_restrict hK).2 hg
  have hglobal := tendsto_eLpNorm_moving_translation hXs hX hconv hp hgK
  have hbound (n : α) (hn : acceleratedFrameMapProd (Xs n) '' S ⊆ K) : eLpNorm
      ((g ∘ acceleratedFrameMapProd (Xs n)) - (g ∘ acceleratedFrameMapProd X)) p
        (volume.restrict S) ≤ eLpNorm
      (((K.indicator g) ∘ acceleratedFrameMapProd (Xs n)) -
        ((K.indicator g) ∘ acceleratedFrameMapProd X)) p volume := by
    calc
      _ = eLpNorm (((K.indicator g) ∘ acceleratedFrameMapProd (Xs n)) -
          ((K.indicator g) ∘ acceleratedFrameMapProd X)) p (volume.restrict S) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem hS] with z hz
        simp only [Pi.sub_apply, Function.comp_apply,
          indicator_of_mem (hn ⟨z, hz, rfl⟩),
          indicator_of_mem (himage ⟨z, hz, rfl⟩)]
      _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hglobal
    (Eventually.of_forall (fun _ ↦ bot_le)) (himages.mono (fun n hn ↦ hbound n hn))

/-- Only convergence on the compact time interval containing the target tube
is needed. Clamping time outside that interval converts the local path
convergence to global compact-open convergence without changing the tube. -/
theorem tendsto_eLpNorm_moving_translation_on_time_interval
    {E : Type*} [NormedAddCommGroup E]
    {α : Type*} {l : Filter α} {Xs : α → ℝ → Vec3} {X : ℝ → Vec3}
    (hXs : ∀ n, Continuous (Xs n)) (hX : Continuous X)
    {a b : ℝ} (hab : a ≤ b) (hconv : TendstoUniformlyOn Xs X l (Icc a b))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {S K : Set (Vec3 × ℝ)} (hS : MeasurableSet S) (hK : MeasurableSet K)
    (hStime : ∀ z ∈ S, z.2 ∈ Icc a b)
    (himages : ∀ᶠ n in l, acceleratedFrameMapProd (Xs n) '' S ⊆ K)
    (himage : acceleratedFrameMapProd X '' S ⊆ K)
    {g : Vec3 × ℝ → E} (hg : MemLp g p (volume.restrict K)) :
    Tendsto (fun n ↦ eLpNorm
      ((g ∘ acceleratedFrameMapProd (Xs n)) - (g ∘ acceleratedFrameMapProd X)) p
        (volume.restrict S)) l (𝓝 0) := by
  let c : ℝ → ℝ := fun t ↦ projIcc a b hab t
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hcon : ∀ t ∈ Icc a b, c t = t := by
    intro t ht
    exact congrArg Subtype.val (projIcc_of_mem hab ht)
  let Ys := fun n ↦ Xs n ∘ c
  let Y := X ∘ c
  have hYs : ∀ n, Continuous (Ys n) := fun n ↦ (hXs n).comp hc
  have hY : Continuous Y := hX.comp hc
  have hYconv : ∀ T : Set ℝ, IsCompact T → TendstoUniformlyOn Ys Y l T := by
    intro T _
    exact (hconv.comp c).mono (fun t _ ↦ (projIcc a b hab t).property)
  have hYimages : ∀ᶠ n in l, acceleratedFrameMapProd (Ys n) '' S ⊆ K := by
    filter_upwards [himages] with n hn
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have heq : acceleratedFrameMapProd (Ys n) w = acceleratedFrameMapProd (Xs n) w := by
      simp only [acceleratedFrameMapProd, Ys, Function.comp_apply, hcon w.2 (hStime w hw)]
    rw [heq]
    exact hn ⟨w, hw, rfl⟩
  have hYimage : acceleratedFrameMapProd Y '' S ⊆ K := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have heq : acceleratedFrameMapProd Y w = acceleratedFrameMapProd X w := by
      simp only [acceleratedFrameMapProd, Y, Function.comp_apply, hcon w.2 (hStime w hw)]
    rw [heq]
    exact himage ⟨w, hw, rfl⟩
  have htend := tendsto_eLpNorm_moving_translation_local hYs hY hYconv hp hS hK
    hYimages hYimage hg
  apply htend.congr
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hS] with z hz
  simp only [Pi.sub_apply, Function.comp_apply, acceleratedFrameMapProd, Ys, Y,
    hcon z.2 (hStime z hz)]

/-- An actual suitable solution supplies strong composition limits for all fields
on a common compact interior tube. In particular the rough weak gradient and
pressure converge in their genuine energy and pressure spaces, and the velocity
converges in the cubic space needed by the local energy inequality. -/
theorem suitable_moving_fields_strongLp
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {α : Type*} {l : Filter α} {Xs : α → ℝ → Vec3} {X : ℝ → Vec3}
    (hXs : ∀ n, Continuous (Xs n)) (hX : Continuous X)
    {a b : ℝ} (hab : a ≤ b) (hconv : TendstoUniformlyOn Xs X l (Icc a b))
    {S K : Set ParabolicPoint} (hS : MeasurableSet S) (hK : IsCompact K)
    (hKdom : K ⊆ spaceTimeSet Ω I) (hStime : ∀ z ∈ S, z.2 ∈ Icc a b)
    (himages : ∀ᶠ n in l, acceleratedFrameMap (Xs n) '' S ⊆ K)
    (himage : acceleratedFrameMap X '' S ⊆ K) :
    Tendsto (fun n ↦ eLpNorm
      ((u ∘ acceleratedFrameMap (Xs n)) - (u ∘ acceleratedFrameMap X)) 2
        (volume.restrict S)) l (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        ((u ∘ acceleratedFrameMap (Xs n)) - (u ∘ acceleratedFrameMap X)) 3
          (volume.restrict S)) l (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        ((Du ∘ acceleratedFrameMap (Xs n)) - (Du ∘ acceleratedFrameMap X)) 2
          (volume.restrict S)) l (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        ((p ∘ acceleratedFrameMap (Xs n)) - (p ∘ acceleratedFrameMap X))
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict S)) l (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        ((f ∘ acceleratedFrameMap (Xs n)) - (f ∘ acceleratedFrameMap X))
          (ENNReal.ofReal q) (volume.restrict S)) l (𝓝 0) := by
  have hKm : MeasurableSet (show Set (Vec3 × ℝ) from K) :=
    (isCompact_prod_of_isCompact_parabolic hK).measurableSet
  have hu := velocity_memLp_two_on_compact_of_data hsol.toData hK hKdom
  have hu3 : MemLp u 3 (volume.restrict K) := by
    simpa using velocity_memLp_three_on_compact_of_data hsol.toData hK hKdom
  have hDu := gradient_memLp_two_on_compact_of_data hsol.toData hK hKdom
  have hp := pressure_memLp_threeHalves_on_compact_of_data hsol.toData hK hKdom
  have hf := force_memLp_on_compact_of_data hsol.toData hK hKdom
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [hsol.toData.five_halves_lt_exponent])⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact tendsto_eLpNorm_moving_translation_on_time_interval hXs hX hab hconv
      (by norm_num) hS hKm hStime himages himage hu
  · exact tendsto_eLpNorm_moving_translation_on_time_interval hXs hX hab hconv
      (by norm_num) hS hKm hStime himages himage hu3
  · exact tendsto_eLpNorm_moving_translation_on_time_interval hXs hX hab hconv
      (by norm_num) hS hKm hStime himages himage hDu
  · exact tendsto_eLpNorm_moving_translation_on_time_interval hXs hX hab hconv
      ENNReal.ofReal_ne_top hS hKm hStime himages himage hp
  · exact tendsto_eLpNorm_moving_translation_on_time_interval hXs hX hab hconv
      ENNReal.ofReal_ne_top hS hKm hStime himages himage hf

end FluidSingularSets
