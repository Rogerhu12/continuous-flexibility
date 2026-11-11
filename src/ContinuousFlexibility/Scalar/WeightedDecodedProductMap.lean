import ContinuousFlexibility.Scalar.WeightedDecodedProduct
import ContinuousFlexibility.Scalar.WeightedMultilinearLift

/-!
# Continuous multilinear products with uniform tame estimates

The map is the actual pointwise product of the frozen decoders.  Its
multilinearity comes from multiplication of scalar functions; its continuity
comes from the proved physical estimates.  The one-high-factor estimate keeps
the same base and loss for every positive arity.
-/

noncomputable section

open scoped BigOperators

namespace ContinuousFlexibility.Analysis

/-- Monotonicity turns a one-high-factor expression into a product bound in
one higher seminorm.  This step is used only to prove continuity. -/
theorem oneHigh_le_card_product
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    (base high : ℕ) (u : ι → E) :
    (∑ i, p high (u i) * ∏ j ∈ Finset.univ.erase i, p base (u j)) ≤
      (Fintype.card ι : ℝ) * ∏ i, p (max base high) (u i) := by
  have hterm (i : ι) :
      p high (u i) * ∏ j ∈ Finset.univ.erase i, p base (u j) ≤
        ∏ j, p (max base high) (u j) := by
    calc
      _ ≤ p (max base high) (u i) *
          ∏ j ∈ Finset.univ.erase i, p (max base high) (u j) :=
        mul_le_mul (hp (le_max_right base high) (u i))
          (Finset.prod_le_prod₀ (fun j _ => apply_nonneg _ _)
            (fun j _ => hp (le_max_left base high) (u j)))
          (Finset.prod_nonneg (fun j _ => apply_nonneg _ _)) (apply_nonneg _ _)
      _ = _ := Finset.mul_prod_erase Finset.univ
        (fun j => p (max base high) (u j)) (Finset.mem_univ i)
  calc
    _ ≤ ∑ _i : ι, ∏ j, p (max base high) (u j) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements.SobolevModelData

open ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

/-- Pointwise multiplication of the actual decoders is algebraically
multilinear before any choice of an encoded output. -/
def decodedProductFieldMultilinear (A : SobolevModelData) (k : ℕ) :
    MultilinearMap ℝ (fun _ : Fin (k + 1) => A.Space) (PolarPoint → ℝ) :=
  (MultilinearMap.mkPiAlgebra ℝ (Fin (k + 1)) (PolarPoint → ℝ)).compLinearMap
    (fun _ => A.decode)

theorem decodedProductFieldMultilinear_apply
    (k : ℕ) (u : Fin (k + 1) → A.Space) :
    decodedProductFieldMultilinear A k u = fun p => ∏ i, A.decode (u i) p := by
  funext p
  simp only [decodedProductFieldMultilinear, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Finset.prod_apply]

private theorem decodedProductField_heightMember
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) (k : ℕ)
    (u : Fin (k + 1) → A.Space) :
    HeightMember D T γ (decodedProductFieldMultilinear A k u) := by
  rw [decodedProductFieldMultilinear_apply]
  exact heightMember_decodedProduct hT hA hinterp hγ k u

private theorem decodedProductField_productBound
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) (k : ℕ) :
    ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : Fin (k + 1) → A.Space,
        physicalNorm T γ s (decodedProductFieldMultilinear A k u) ≤
          C * ∏ i, A.grading t (u i) := by
  obtain ⟨base, loss, _, hprod⟩ := decodedProduct_physicalNorm_oneHigh hT hA hinterp hγ
  intro s
  obtain ⟨C, hC, hCu⟩ := hprod k s
  refine ⟨max base (s + loss), C * ((k + 1 : ℕ) : ℝ),
    mul_nonneg hC (Nat.cast_nonneg _), ?_⟩
  intro u
  rw [decodedProductFieldMultilinear_apply]
  have hsum :
      (∑ i, A.grading (s + loss) (u i) *
        ∏ j ∈ Finset.univ.erase i, A.grading base (u j)) ≤
      (Fintype.card (Fin (k + 1)) : ℝ) * ∏ i, A.grading (max base (s + loss)) (u i) :=
    oneHigh_le_card_product (p := A.grading)
      (gradedSeminorm_monotone (fun n => A.level n) A.bond) base (s + loss) u
  exact ((hCu u).trans (mul_le_mul_of_nonneg_left hsum hC)).trans_eq (by
    simp only [Fintype.card_fin]
    ring)

/-- The genuine continuous multilinear product on the prescribed weighted
Sobolev model, at every positive arity. -/
def decodedProductMap
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => A.Space) A.Space :=
  liftContinuousMultilinear (p := A.grading) hA (decodedProductFieldMultilinear A k)
    (decodedProductField_heightMember hT hA hinterp hγ k)
    (withSeminorms_graded (fun n => A.level n) A.bond)
    (decodedProductField_productBound hT hA hinterp hγ k)

theorem decode_decodedProductMap
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) (k : ℕ)
    (u : Fin (k + 1) → A.Space) :
    A.decode (decodedProductMap hT hA hinterp hγ k u) =
      fun p => ∏ i, A.decode (u i) p := by
  exact (decode_liftContinuousMultilinear (p := A.grading) hA
    (decodedProductFieldMultilinear A k)
    (decodedProductField_heightMember hT hA hinterp hγ k)
    (withSeminorms_graded (fun n => A.level n) A.bond)
    (decodedProductField_productBound hT hA hinterp hγ k) u).trans
      (decodedProductFieldMultilinear_apply k u)

theorem decodedProductMap_apply
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) (k : ℕ)
    (u : Fin (k + 1) → A.Space) :
    decodedProductMap hT hA hinterp hγ k u = decodedProduct hT hA hinterp hγ k u := by
  apply hA.2.2.2.2.2.1
  rw [decode_decodedProductMap, decode_decodedProduct]

/-- Continuity does not change the previously proved common base or loss. -/
theorem decodedProductMap_oneHigh
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ k s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : Fin (k + 1) → A.Space,
        A.grading s (decodedProductMap hT hA hinterp hγ k u) ≤
          C * ∑ i, A.grading (s + loss) (u i) *
            ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
  obtain ⟨base, loss, hbase, hprod⟩ := decodedProduct_oneHigh hT hA hinterp hγ
  refine ⟨base, loss, hbase, ?_⟩
  intro k s
  obtain ⟨C, hC, hCu⟩ := hprod k s
  refine ⟨C, hC, fun u => ?_⟩
  rw [decodedProductMap_apply]
  exact hCu u

theorem continuous_decodedProduct
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) (k : ℕ) :
    Continuous (decodedProduct hT hA hinterp hγ k) := by
  have heq : decodedProduct hT hA hinterp hγ k =
      fun u => decodedProductMap hT hA hinterp hγ k u :=
    funext (fun u => (decodedProductMap_apply hT hA hinterp hγ k u).symm)
  rw [heq]
  exact (decodedProductMap hT hA hinterp hγ k).cont

end ContinuousFlexibility.Statements.SobolevModelData
