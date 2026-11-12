import ContinuousFlexibility.Analysis.N01CoefficientValueJets
import ContinuousFlexibility.Analysis.MaterialCellHeightTransport
import ContinuousFlexibility.Analysis.MaterialMixedFlatExtension
import ContinuousFlexibility.Scalar.WeightedReferenceBounds

/-!
# The actual N01 coefficient difference is flat at the ambient ends

The frozen N01 spatial bounds retain H^(3/4) at an actual cell sample.
The same-cell material comparison moves this factor to the evaluation
point, without changing its positive exponent. Material endpoint decay
then proves smooth flatness of the literal zero extension of the actual
current-minus-reference coefficient difference on the open annulus.
No statement is made about arbitrary totalized ambient coefficient values.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

def n01OriginalCoefficientDifference
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (i : Fin 3) : PolarPoint → ℝ :=
  fun p => canonicalCoefficientComponent i (originalCoefficients D S C z) p -
    canonicalCoefficientComponent i (originalCoefficients D S C (C.referenceState, 0)) p

def n01OriginalCoefficientDifferenceExtension
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (i : Fin 3) : PolarPoint → ℝ :=
  (annularOpen D).indicator (n01OriginalCoefficientDifference D S C z i)

theorem n01OriginalCoefficientDifference_point_weight_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ i a b (p : PolarPoint),
      a + b ≤ s → p ∈ annularOpen D → ∀ z ∈ stateNeighborhood S C base ε,
      |mixedDerivative a b (n01OriginalCoefficientDifference D S C z i) p| ≤
        K * T.H p.1 ^ (3 / 4 : ℝ) * T.E0 p.1 ^ A *
          (1 + pairGrading (stateGrading S) realGrading (s + loss)
            (z - (C.referenceState, 0))) := by
  obtain ⟨B, hB, hb⟩ := coefficientFamily_value_bound_of_n01 hN s
  obtain ⟨K, A, hK, hA, hweight⟩ :=
    materialCell_H_E0_rpow_same_cell hT hN.1.1 (3 / 4 : ℝ) hB.le
  have hsample : ∀ m, T.sample m ∈ D.cells m := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := hT
    exact hs
  refine ⟨B * K, A, mul_pos hB hK, hA, ?_⟩
  intro i a b p hab hp z hz
  obtain ⟨m, hm⟩ := RadialPartition.exists_cell hN.1.1.choose_spec.2.1 hp.1
  have hvalue := hb m i a b p hab hm z hz
  change |mixedDerivative a b (n01OriginalCoefficientDifference D S C z i) p| ≤ _ at hvalue
  let W : ℝ := 1 + pairGrading (stateGrading S) realGrading (s + loss)
    (z - (C.referenceState, 0))
  have hW : 0 ≤ W := add_nonneg zero_le_one (apply_nonneg _ _)
  calc
    _ ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B * W := hvalue
    _ = B * (T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B) * W := by ring
    _ ≤ B * (K * T.H p.1 ^ (3 / 4 : ℝ) * T.E0 p.1 ^ A) * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hweight m (T.sample m) p.1 (hsample m) hm) hB.le) hW
    _ = _ := by dsimp only [W]; ring

theorem n01OriginalCoefficientDifferenceExtension_smooth_flat
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (i : Fin 3) :
    ContDiff ℝ ∞ (n01OriginalCoefficientDifferenceExtension D S C z i) ∧
      ∀ n (p : PolarPoint), p.1 ∉ Ioo D.a D.b →
        iteratedFDeriv ℝ n (n01OriginalCoefficientDifferenceExtension D S C z i) p = 0 := by
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.2.1
  have hrefS : stateSector S C.referenceState := hN.2.2.1.stateSector
  have hf : ContDiffOn ℝ ∞ (n01OriginalCoefficientDifference D S C z i) (annularOpen D) :=
    (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hs i).sub
      (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN href hrefS i)
  have hbound (a b : ℕ) : ∃ K A : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      |mixedDerivative a b (n01OriginalCoefficientDifference D S C z i) p| ≤
        K * T.H p.1 ^ (3 / 4 : ℝ) * T.M p.1 ^ A := by
    obtain ⟨K, A, hK, _, hb⟩ := n01OriginalCoefficientDifference_point_weight_bound hT hN (a + b)
    have hE : ∀ A : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ioo D.a D.b,
        T.E0 r ^ A ≤ C * T.M r := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hE, _⟩ := hT
      exact hE
    obtain ⟨CE, hCE, he⟩ := hE A
    let W : ℝ := 1 + pairGrading (stateGrading S) realGrading (a + b + loss)
      (z - (C.referenceState, 0))
    have hW : 0 ≤ W := add_nonneg zero_le_one (apply_nonneg _ _)
    refine ⟨K * CE * W, 1, mul_nonneg (mul_nonneg hK.le hCE.le) hW, ?_⟩
    intro p hp
    have hH : 0 ≤ T.H p.1 ^ (3 / 4 : ℝ) :=
      Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.1.le _
    calc
      _ ≤ K * T.H p.1 ^ (3 / 4 : ℝ) * T.E0 p.1 ^ A * W := hb i a b p le_rfl hp z hz
      _ ≤ K * T.H p.1 ^ (3 / 4 : ℝ) * (CE * T.M p.1) * W :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (he p.1 hp.1) (mul_nonneg hK.le hH)) hW
      _ = (K * CE * W) * T.H p.1 ^ (3 / 4 : ℝ) * T.M p.1 ^ (1 : ℝ) := by
        rw [Real.rpow_one]
        ring
  exact smooth_annular_zero_extension_of_material_mixed_bounds hT
    (by norm_num : (0 : ℝ) < 3 / 4) hf hbound

theorem n01OriginalCoefficientDifferenceExtension_germ
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (i : Fin 3) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    n01OriginalCoefficientDifferenceExtension D S C z i =ᶠ[𝓝 p]
      n01OriginalCoefficientDifference D S C z i := by
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
  exact Set.indicator_of_mem hq _

end ContinuousFlexibility.Analysis
