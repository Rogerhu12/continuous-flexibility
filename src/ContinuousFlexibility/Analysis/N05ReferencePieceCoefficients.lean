module

public import ContinuousFlexibility.Analysis.N05ReferenceInterface
public import ContinuousFlexibility.Analysis.N05ReferenceSWindow
public import ContinuousFlexibility.Radial.DeepTailPhysicalWeights
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Reference reciprocal coefficients on actual canonical pieces

The endpoint-exponent window costs one fixed coefficient power. The controlled
reference coordinates associate each point with an actual cell satisfying
that window, so reciprocal-jet bounds transfer to the piece index. The stronger
bounded-index helper remains available for explicit seed constructions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

/-- A bounded index window changes a fixed coefficient power by at most
another coefficient power, uniformly over the two indices. -/
theorem n05_radialE_power_index_window (A B : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ i n : ℕ,
      |(i : ℝ) - (n : ℝ)| ≤ B →
        radialE i ^ A ≤ C * radialE n ^ C := by
  obtain ⟨C, hC, hshift⟩ := Radial.physicalWeight_shift A hA ⌈B⌉₊
  refine ⟨C, hC, fun i n hwindow => ?_⟩
  have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  have hdiff : (i : ℝ) - (n : ℝ) ≤ B :=
    (le_abs_self _).trans hwindow
  have hiR : (i : ℝ) ≤ ((n + ⌈B⌉₊ : ℕ) : ℝ) := by
    push_cast
    linarith only [hdiff, hceil]
  have hi : i ≤ n + ⌈B⌉₊ := by exact_mod_cast hiR
  have hE : radialE i ≤ radialE (n + ⌈B⌉₊) :=
    Real.exp_le_exp.mpr (Radial.radialQ_monotone hi)
  exact (Real.rpow_le_rpow (Real.exp_pos _).le hE hA).trans (hshift n)

/-- Every actual piece inherits the reciprocal-jet coefficient bound from
a genuine reference cell meeting that point. Only its endpoint-exponent
window is used; no coefficient envelope for the pieces is assumed. -/
theorem n05_referenceInverseJet_piece_bound {D : ReferenceData}
    {S : PhysicalSpacesData} {G : NonlinearGeometryData S} {K : CanonicalData S}
    (hD : IsAccumulatingProfile D)
    (hcoordinates : N05ControlledReferenceCoordinates D S G K) (s : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
        |radialJet s (fun t => (D.w t)⁻¹) r| ≤
          C * radialE (D.cellIndex (K.cell m)) ^ A := by
  obtain ⟨bounds, hbounds⟩ := hD
  have hpositive : 0 < bounds s := hbounds.2.2.1 s
  have hjets := hbounds.2.2.2.2.2.2.2.2.2.1
  obtain ⟨B, hB, hassociation, _, _⟩ := hcoordinates.2
  obtain ⟨C, hC, hwindow⟩ :=
    n05_radialE_power_swindow (bounds s) B hpositive.le hB.le
  refine ⟨bounds s * C, C, mul_pos hpositive hC, hC, fun m r hr => ?_⟩
  obtain ⟨j, hrj, hindex⟩ := hassociation m r hr
  calc
    _ ≤ bounds s * radialE (D.cellIndex j) ^ (bounds s) := hjets j r hrj s
    _ ≤ bounds s * (C * radialE (D.cellIndex (K.cell m)) ^ C) :=
      mul_le_mul_of_nonneg_left
        (hwindow (D.cellIndex j) (D.cellIndex (K.cell m)) hindex) hpositive.le
    _ = _ := (mul_assoc _ _ _).symm

/-- The reciprocal profile weight has one uniform coefficient bound on
every actual canonical piece, indexed by the piece's prescribed cell. -/
theorem n05_referenceReciprocal_piece_bound {D : ReferenceData}
    {S : PhysicalSpacesData} {G : NonlinearGeometryData S} {K : CanonicalData S}
    (hD : IsAccumulatingProfile D)
    (hcoordinates : N05ControlledReferenceCoordinates D S G K) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
        (D.w r)⁻¹ ≤ C * radialE (D.cellIndex (K.cell m)) ^ A := by
  obtain ⟨C, A, hC, hA, hbound⟩ :=
    n05_referenceInverseJet_piece_bound hD hcoordinates 0
  refine ⟨C, A, hC, hA, fun m r hr => ?_⟩
  exact (le_abs_self _).trans (hbound m r hr)

end ContinuousFlexibility.Statements
