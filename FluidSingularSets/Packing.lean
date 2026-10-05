-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Tactic.Linarith

/-!
# Packing estimates from a uniform measure charge

A disjoint family cannot have more members than its total available mass divided by the
mass required for one member. The covering-number application uses the standard maximal
separated set from Mathlib. Its charge assumption is explicit: this file supplies the
measure-theoretic reduction, not a Navier--Stokes regularity detector.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

set_option autoImplicit false

namespace FluidSingularSets

variable {X ι : Type*} [MeasurableSpace X]

/-- The total charge of a finite, disjoint measurable family is at most the ambient mass. -/
theorem card_mul_charge_le_measure (ν : Measure X) (P : Finset ι) (A : ι → Set X)
    (hdisjoint : (P : Set ι).PairwiseDisjoint A)
    (hmeasurable : ∀ i ∈ P, MeasurableSet (A i)) (charge : ℝ≥0∞)
    (hcharge : ∀ i ∈ P, charge ≤ ν (A i)) :
    (P.card : ℝ≥0∞) * charge ≤ ν Set.univ := by
  calc
    (P.card : ℝ≥0∞) * charge = ∑ i ∈ P, charge := by simp
    _ ≤ ∑ i ∈ P, ν (A i) := Finset.sum_le_sum hcharge
    _ = ν (⋃ i ∈ P, A i) := (measure_biUnion_finset hdisjoint hmeasurable).symm
    _ ≤ ν Set.univ := measure_mono (Set.subset_univ _)

/-- Dividing by a positive finite charge bounds the size of a disjoint measurable family. -/
theorem card_le_measure_div_charge (ν : Measure X) (P : Finset ι) (A : ι → Set X)
    (hdisjoint : (P : Set ι).PairwiseDisjoint A)
    (hmeasurable : ∀ i ∈ P, MeasurableSet (A i)) (charge : ℝ≥0∞)
    (hcharge_pos : charge ≠ 0) (hcharge_finite : charge ≠ ⊤)
    (hcharge : ∀ i ∈ P, charge ≤ ν (A i)) :
    (P.card : ℝ≥0∞) ≤ ν Set.univ / charge := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl hcharge_pos) (Or.inl hcharge_finite)).2
  exact card_mul_charge_le_measure ν P A hdisjoint hmeasurable charge hcharge

section Metric

variable [PseudoMetricSpace X] [BorelSpace X]

/-- Separated centers give a disjoint ball packing, whose uniform charge controls its size. -/
theorem card_mul_ball_charge_le_measure (ν : Measure X) (P : Finset X) (ε : ℝ≥0)
    (hseparated : Metric.IsSeparated (ε : ℝ≥0∞) (P : Set X)) (charge : ℝ≥0∞)
    (hcharge : ∀ x ∈ P, charge ≤ ν (Metric.ball x ((ε : ℝ) / 2))) :
    (P.card : ℝ≥0∞) * charge ≤ ν Set.univ := by
  apply card_mul_charge_le_measure ν P (fun x ↦ Metric.ball x ((ε : ℝ) / 2))
    ?_ (fun _ _ ↦ measurableSet_ball) charge hcharge
  intro x hx y hy hxy
  apply Metric.ball_disjoint_ball
  have hdist : (ε : ℝ) < dist x y := by
    simpa only [edist_dist, ENNReal.coe_lt_ofReal] using hseparated hx hy hxy
  linarith

/-- Finite ambient mass and a positive uniform ball charge rule out infinite packing numbers. -/
theorem packingNumber_ne_top_of_ball_charge (ν : Measure X) (A : Set X) (ε : ℝ≥0)
    (hν : ν Set.univ ≠ ⊤) (charge : ℝ≥0∞) (hcharge_pos : charge ≠ 0)
    (hcharge : ∀ x ∈ A, charge ≤ ν (Metric.ball x ((ε : ℝ) / 2))) :
    Metric.packingNumber ε A ≠ ⊤ := by
  classical
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hcharge_pos hν
  have hbound : Metric.packingNumber ε A ≤ (n : ℕ∞) := by
    unfold Metric.packingNumber
    refine iSup_le fun C ↦ iSup_le fun hCA ↦ iSup_le fun hCseparated ↦ ?_
    by_contra! hCn
    obtain ⟨D, hDC, hDcard⟩ := Set.exists_subset_encard_eq (le_of_lt hCn)
    have hDfinite : D.Finite := Set.encard_ne_top_iff.mp (hDcard ▸ by simp)
    let P := hDfinite.toFinset
    have hPD : (P : Set X) = D := hDfinite.coe_toFinset
    have hPn : P.card = n := by
      exact_mod_cast hDfinite.encard_eq_coe_toFinset_card.symm.trans hDcard
    have hPseparated : Metric.IsSeparated (ε : ℝ≥0∞) (P : Set X) :=
      hPD ▸ hCseparated.subset hDC
    have hPcharge : ∀ x ∈ P, charge ≤ ν (Metric.ball x ((ε : ℝ) / 2)) := by
      intro x hx
      exact hcharge x (hCA (hDC (hPD ▸ hx)))
    have hmass := card_mul_ball_charge_le_measure ν P ε hPseparated charge hPcharge
    rw [hPn] at hmass
    exact (not_le_of_gt hn) hmass
  exact ne_top_of_le_ne_top (by simp) hbound

/-- A maximal separated set transfers the ball charge estimate to external covering numbers.
The finiteness hypothesis concerns the packing number, so conversion to a natural number
does not discard an infinite covering number. -/
theorem externalCoveringNumber_le_measure_div_ball_charge (ν : Measure X) (A : Set X)
    (ε : ℝ≥0) (hpacking : Metric.packingNumber ε A ≠ ⊤) (charge : ℝ≥0∞)
    (hcharge_pos : charge ≠ 0) (hcharge_finite : charge ≠ ⊤)
    (hcharge : ∀ x ∈ A, charge ≤ ν (Metric.ball x ((ε : ℝ) / 2))) :
    Metric.externalCoveringNumber ε A ≠ ⊤ ∧
      ((Metric.externalCoveringNumber ε A).toNat : ℝ≥0∞) ≤ ν Set.univ / charge := by
  classical
  obtain ⟨C, hCA, hCfinite, hCseparated, hCcard⟩ :=
    Metric.exists_set_encard_eq_packingNumber hpacking
  let P := hCfinite.toFinset
  have hPC : (P : Set X) = C := hCfinite.coe_toFinset
  have hcover : Metric.externalCoveringNumber ε A ≤ (P.card : ℕ∞) := by
    calc
      Metric.externalCoveringNumber ε A ≤ Metric.packingNumber ε A :=
        (Metric.externalCoveringNumber_le_coveringNumber ε A).trans
          (Metric.coveringNumber_le_packingNumber ε A)
      _ = C.encard := hCcard.symm
      _ = (P.card : ℕ∞) := hCfinite.encard_eq_coe_toFinset_card
  refine ⟨ne_top_of_le_ne_top (by simp) hcover, ?_⟩
  have hcard : (P.card : ℝ≥0∞) ≤ ν Set.univ / charge := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hcharge_pos) (Or.inl hcharge_finite)).2
    apply card_mul_ball_charge_le_measure ν P ε (hPC ▸ hCseparated) charge
    intro x hx
    exact hcharge x (hCA (hPC ▸ hx))
  have hnat : ((Metric.externalCoveringNumber ε A).toNat : ℝ≥0∞) ≤ P.card := by
    exact_mod_cast ENat.toNat_le_of_le_natCast hcover
  exact hnat.trans hcard

/-- The external covering number is finite and is bounded by mass divided by ball charge. -/
theorem externalCoveringNumber_le_measure_div_ball_charge_of_finite_mass
    (ν : Measure X) (A : Set X) (ε : ℝ≥0) (hν : ν Set.univ ≠ ⊤)
    (charge : ℝ≥0∞) (hcharge_pos : charge ≠ 0) (hcharge_finite : charge ≠ ⊤)
    (hcharge : ∀ x ∈ A, charge ≤ ν (Metric.ball x ((ε : ℝ) / 2))) :
    Metric.externalCoveringNumber ε A ≠ ⊤ ∧
      ((Metric.externalCoveringNumber ε A).toNat : ℝ≥0∞) ≤ ν Set.univ / charge := by
  exact externalCoveringNumber_le_measure_div_ball_charge ν A ε
    (packingNumber_ne_top_of_ball_charge ν A ε hν charge hcharge_pos hcharge)
    charge hcharge_pos hcharge_finite hcharge

end Metric

end FluidSingularSets
