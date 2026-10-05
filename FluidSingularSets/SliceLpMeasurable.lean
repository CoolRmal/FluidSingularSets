-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Measurability of actual spatial Lp slices

The class of a spatial slice is its genuine `toLp` class whenever that slice
belongs to Lp, and zero otherwise. Measurable distances to fixed Lp classes
prove strong measurability of this actual curve. In particular bounded local
Stokes operators may be applied to jointly measurable fields without assuming
measurability of their slice pressures.
-/

@[expose] public section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

open Classical

/-- Measurable distances to every fixed point characterize measurability in a
second-countable metric Borel space. -/
theorem measurable_of_all_dist {A E : Type*} [MeasurableSpace A]
    [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {f : A → E} (hf : ∀ y : E, Measurable (fun x ↦ dist (f x) y)) : Measurable f := by
  apply measurable_of_isOpen
  intro U hU
  let S : Set (Set E) := {V | ∃ y r, 0 < r ∧ V = Metric.ball y r ∧ V ⊆ U}
  have hSopen : ∀ V ∈ S, IsOpen V := by
    rintro V ⟨y, r, _, rfl, _⟩
    exact Metric.isOpen_ball
  have heq : sUnion S = U := by
    ext y
    constructor
    · rintro ⟨V, ⟨_, _, _, _, hVU⟩, hyV⟩
      exact hVU hyV
    · intro hy
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hy)
      exact ⟨Metric.ball y r, ⟨y, r, hr, rfl, hball⟩, Metric.mem_ball_self hr⟩
  obtain ⟨C, hCc, hCS, hCU⟩ := isOpen_sUnion_countable S hSopen
  rw [← heq, ← hCU, sUnion_eq_biUnion, preimage_iUnion₂]
  apply MeasurableSet.biUnion hCc
  intro V hVC
  obtain ⟨y, r, _, rfl, _⟩ := hCS hVC
  exact (hf y) measurableSet_Iio

section Slices

variable {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
  [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure A} [SFinite μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Lp class of a time slice, with zero at the non-Lp times. -/
def actualSliceLp (F : A × T → E) (t : T) : Lp E p μ :=
  if h : MemLp (fun x ↦ F (x, t)) p μ then h.toLp (fun x ↦ F (x, t)) else 0

omit [MeasurableSpace T] [MeasurableSpace E] [BorelSpace E] [SFinite μ] [Fact (1 ≤ p)] in
/-- Genuine slice agreement at every good time. -/
theorem actualSliceLp_ae (F : A × T → E) (t : T)
    (ht : MemLp (fun x ↦ F (x, t)) p μ) :
    actualSliceLp (μ := μ) (p := p) F t =ᵐ[μ] (fun x ↦ F (x, t)) := by
  rw [actualSliceLp, dite_eq_left ht]
  exact ht.coeFn_toLp

/-- The true finite-exponent slice seminorm is measurable in time. -/
theorem measurable_actualSlice_eLpNorm {F : A × T → E}
    (hF : StronglyMeasurable F) (hp : p ≠ ∞) :
    Measurable (fun t ↦ eLpNorm (fun x ↦ F (x, t)) p μ) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1)
    Fact.out)
  have hslice (t : T) : AEStronglyMeasurable (fun x ↦ F (x, t)) μ :=
    (hF.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have heq : (fun t ↦ eLpNorm (fun x ↦ F (x, t)) p μ) =
      fun t ↦ (∫⁻ x, ‖F (x, t)‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
    funext t
    exact eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (hslice t)
  rw [heq]
  exact (Measurable.lintegral_prod_left'
    (hF.measurable.enorm.pow_const p.toReal)).pow_const _

/-- The genuine set of finite-exponent Lp times is measurable. -/
theorem measurableSet_actualSlice_memLp {F : A × T → E}
    (hF : StronglyMeasurable F) (hp : p ≠ ∞) :
    MeasurableSet {t | MemLp (fun x ↦ F (x, t)) p μ} := by
  have heq : {t | MemLp (fun x ↦ F (x, t)) p μ} =
      {t | eLpNorm (fun x ↦ F (x, t)) p μ < ∞} := by
    rfl
  rw [heq]
  exact measurableSet_lt (measurable_actualSlice_eLpNorm hF hp) measurable_const

/-- Distances from actual slice classes to any fixed Lp class are measurable. -/
theorem measurable_actualSliceLp_dist {F : A × T → E}
    (hF : StronglyMeasurable F) (hp : p ≠ ∞) (v : Lp E p μ) :
    Measurable (fun t ↦ dist (actualSliceLp (μ := μ) (p := p) F t) v) := by
  have hdiff : StronglyMeasurable (fun z : A × T ↦ F z - v z.1) :=
    hF.sub ((Lp.stronglyMeasurable v).comp_measurable measurable_fst)
  have heq : (fun t ↦ dist (actualSliceLp (μ := μ) (p := p) F t) v) =
      fun t ↦ if MemLp (fun x ↦ F (x, t)) p μ then
        (eLpNorm (fun x ↦ F (x, t) - v x) p μ).toReal else ‖v‖ := by
    funext t
    by_cases ht : MemLp (fun x ↦ F (x, t)) p μ
    · rw [ite_eq_left ht, Lp.dist_def]
      congr 1
      apply eLpNorm_congr_ae
      exact (actualSliceLp_ae F t ht).sub EventuallyEq.rfl
    · simp [actualSliceLp, ht]
  rw [heq]
  exact ((measurable_actualSlice_eLpNorm hdiff hp).ennreal_toReal).ite
    (measurableSet_actualSlice_memLp hF hp) measurable_const

/-- The genuine conditional Lp-valued slice curve is strongly measurable. -/
theorem stronglyMeasurable_actualSliceLp [IsSeparable μ] [SecondCountableTopology E]
    {F : A × T → E} (hF : StronglyMeasurable F) (hp : p ≠ ∞) :
    StronglyMeasurable (actualSliceLp (μ := μ) (p := p) F) := by
  let : Fact (p ≠ ∞) := ⟨hp⟩
  let : MeasurableSpace (Lp E p μ) := borel (Lp E p μ)
  let : BorelSpace (Lp E p μ) := ⟨rfl⟩
  have hm : Measurable (actualSliceLp (μ := μ) (p := p) F) :=
    measurable_of_all_dist (measurable_actualSliceLp_dist hF hp)
  exact hm.stronglyMeasurable

omit [MeasurableSpace T] [MeasurableSpace E] [BorelSpace E] [SFinite μ] [Fact (1 ≤ p)] in
/-- The actual conditional slice class is unchanged by true spatial AE equality. -/
theorem actualSliceLp_eq_of_ae_eq (F G : A × T → E) (t : T)
    (h : (fun x ↦ F (x, t)) =ᵐ[μ] (fun x ↦ G (x, t))) :
    actualSliceLp (μ := μ) (p := p) F t = actualSliceLp (μ := μ) (p := p) G t := by
  by_cases hF : MemLp (fun x ↦ F (x, t)) p μ
  · have hG := (memLp_congr_ae h).mp hF
    rw [actualSliceLp, dite_eq_left hF, actualSliceLp, dite_eq_left hG]
    exact MemLp.toLp_congr hF hG h
  · have hG : ¬MemLp (fun x ↦ G (x, t)) p μ := fun hG ↦
      hF ((memLp_congr_ae h).mpr hG)
    simp only [actualSliceLp, dite_eq_right hF, dite_eq_right hG]

omit [MeasurableSpace E] [BorelSpace E] [Fact (1 ≤ p)] in
/-- Almost-everywhere joint equality gives almost-everywhere equality of the actual
spatial Lp classes, including their non-Lp branch. -/
theorem actualSliceLp_ae_eq_of_prod_ae_eq {ν : Measure T} [SFinite ν]
    (F G : A × T → E) (h : F =ᵐ[μ.prod ν] G) :
    actualSliceLp (μ := μ) (p := p) F =ᵐ[ν] actualSliceLp (μ := μ) (p := p) G := by
  have hs := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae h)
  filter_upwards [hs] with t ht
  exact actualSliceLp_eq_of_ae_eq F G t ht

/-- Genuine joint AE strong measurability also gives a strongly measurable
Lp-valued curve up to equality at almost every time. -/
theorem aestronglyMeasurable_actualSliceLp [IsSeparable μ] [SecondCountableTopology E]
    {ν : Measure T} [SFinite ν] {F : A × T → E}
    (hF : AEStronglyMeasurable F (μ.prod ν)) (hp : p ≠ ∞) :
    AEStronglyMeasurable (actualSliceLp (μ := μ) (p := p) F) ν := by
  have hm : AEStronglyMeasurable (actualSliceLp (μ := μ) (p := p) (hF.mk F)) ν :=
    (stronglyMeasurable_actualSliceLp (μ := μ) (p := p)
      hF.stronglyMeasurable_mk hp).aestronglyMeasurable
  exact hm.congr (actualSliceLp_ae_eq_of_prod_ae_eq F (hF.mk F) hF.ae_eq_mk).symm

end Slices

end FluidSingularSets
