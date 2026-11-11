import ContinuousFlexibility.Scalar.WeightedDecodedProductMap
import ContinuousFlexibility.Scalar.WeightedProductTower
import ContinuousFlexibility.Scalar.WeightedUniformTameGermOperations

/-!
# The actual product retains both input weights

The weighted product estimates already hold at the sum of the input weights.
Here that estimate is realized as a continuous bilinear map into the sum-weight
model. In particular, two fields of weight `3/8` give a source field of weight
`3/4`; no weight is discarded when the product is encoded.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ}
  {A B : SobolevModelData}

private theorem n08_sumWeightProduct_member (hT : IsMaterialData D T)
    (hA : IsSobolevModel D T γ A) (hinterp : HasInterpolation A.grading)
    (u : Fin 2 → A.Space) :
    HeightMember D T (2 * γ) (SobolevModelData.decodedProductFieldMultilinear A 1 u) := by
  rw [SobolevModelData.decodedProductFieldMultilinear_apply]
  exact heightMember_decodedProduct_sumWeight hT hA hinterp 1 u

private theorem n08_sumWeightProduct_productBound (hT : IsMaterialData D T)
    (hA : IsSobolevModel D T γ A) (hinterp : HasInterpolation A.grading) :
    ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Fin 2 → A.Space,
      physicalNorm T (2 * γ) s (SobolevModelData.decodedProductFieldMultilinear A 1 u) ≤
        C * ∏ i, A.grading t (u i) := by
  obtain ⟨base, loss, _, hproduct⟩ :=
    decodedProduct_sumWeight_physicalNorm_oneHigh hT hA hinterp
  intro s
  obtain ⟨C, hC, hCu⟩ := hproduct 1 s
  refine ⟨max base (s + loss), C * 2, by positivity, ?_⟩
  intro u
  rw [SobolevModelData.decodedProductFieldMultilinear_apply]
  have hsum := oneHigh_le_card_product
    (p := A.grading) (gradedSeminorm_monotone _ _) base (s + loss) u
  have hbound := (hCu u).trans (mul_le_mul_of_nonneg_left hsum hC)
  simpa only [Nat.cast_ofNat, Fintype.card_fin, mul_assoc] using hbound

/-- The same decoded multiplication, with its full sum-weight codomain. -/
def n08SumWeightProduct (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hB : IsSobolevModel D T (2 * γ) B) (hinterp : HasInterpolation A.grading) :
    A.Space [×2]→L[ℝ] B.Space :=
  SobolevModelData.liftContinuousMultilinear hB
    (SobolevModelData.decodedProductFieldMultilinear A 1)
    (n08_sumWeightProduct_member hT hA hinterp)
    (withSeminorms_graded (fun n => A.level n) A.bond)
    (n08_sumWeightProduct_productBound hT hA hinterp)

theorem n08SumWeightProduct_decode (hT : IsMaterialData D T)
    (hA : IsSobolevModel D T γ A) (hB : IsSobolevModel D T (2 * γ) B)
    (hinterp : HasInterpolation A.grading) (u : Fin 2 → A.Space) :
    B.decode (n08SumWeightProduct hT hA hB hinterp u) =
      fun p => A.decode (u 0) p * A.decode (u 1) p := by
  have h := SobolevModelData.decode_liftContinuousMultilinear hB
    (SobolevModelData.decodedProductFieldMultilinear A 1)
    (n08_sumWeightProduct_member hT hA hinterp)
    (withSeminorms_graded (fun n => A.level n) A.bond)
    (n08_sumWeightProduct_productBound hT hA hinterp) u
  apply h.trans
  rw [SobolevModelData.decodedProductFieldMultilinear_apply]
  funext p
  exact Fin.prod_univ_two (fun i : Fin 2 => A.decode (u i) p)

theorem n08SumWeightProduct_grading (hT : IsMaterialData D T)
    (hA : IsSobolevModel D T γ A) (hB : IsSobolevModel D T (2 * γ) B)
    (hinterp : HasInterpolation A.grading) (u : Fin 2 → A.Space) (s : ℕ) :
    B.grading s (n08SumWeightProduct hT hA hB hinterp u) =
      physicalNorm T (2 * γ) s (fun p => A.decode (u 0) p * A.decode (u 1) p) := by
  rw [sobolevGrading_eq_physicalNorm hB, n08SumWeightProduct_decode]

/-- A single fixed base and loss control every output order. -/
theorem n08SumWeightProduct_twoFactor (hT : IsMaterialData D T)
    (hA : IsSobolevModel D T γ A) (hB : IsSobolevModel D T (2 * γ) B)
    (hinterp : HasInterpolation A.grading) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x y : A.Space,
        B.grading s (bilinearJetValue (n08SumWeightProduct hT hA hB hinterp) x y) ≤
          C * (A.grading (s + loss) x * A.grading base y +
            A.grading base x * A.grading (s + loss) y) := by
  obtain ⟨base, loss, hbase, hproduct⟩ :=
    decodedProduct_sumWeight_physicalNorm_oneHigh hT hA hinterp
  refine ⟨base, loss, hbase, ?_⟩
  intro s _
  obtain ⟨C, hC, hCu⟩ := hproduct 1 s
  refine ⟨C, hC, fun x y => ?_⟩
  change B.grading s (n08SumWeightProduct hT hA hB hinterp ![x, y]) ≤ _
  rw [n08SumWeightProduct_grading]
  have hfield : (fun p => ∏ i : Fin 2, A.decode (![x, y] i) p) =
      fun p => A.decode x p * A.decode y p := by
    funext p
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h := hCu ![x, y]
  rw [hfield, oneHigh_fin_two] at h
  exact h

theorem n08SumWeightProduct_uniformTameGerm (hT : IsMaterialData D T)
    (hA : IsSobolevModel D T γ A) (hB : IsSobolevModel D T (2 * γ) B)
    (hinterp : HasInterpolation A.grading) (z0 : A.Space × A.Space) :
    UniformTameGerm (pairGrading A.grading A.grading) B.grading z0
      (fun z : A.Space × A.Space =>
        bilinearJetValue (n08SumWeightProduct hT hA hB hinterp) z.1 z.2) := by
  obtain ⟨base, loss, _, hbound⟩ := n08SumWeightProduct_twoFactor hT hA hB hinterp
  exact uniformTameGerm_bilinearMultilinear
    (n08SumWeightProduct hT hA hB hinterp) hbound
    (withSeminorms_graded (fun n => A.level n) A.bond) z0

end ContinuousFlexibility.Statements
