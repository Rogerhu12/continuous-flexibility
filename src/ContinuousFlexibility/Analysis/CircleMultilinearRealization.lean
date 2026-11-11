import ContinuousFlexibility.Analysis.CircleNonlinearRealization
import ContinuousFlexibility.Analysis.SmoothDirectionsUniformBounds

/-!
# Continuous multilinear realization in the actual circle model

Scalar multilinear field identities lift through the injective decoder.
Continuity is proved in every projective coordinate using a continuous
seminorm product bound and the exact telescoping multilinear identity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

section MultilinearBounds

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_multilinear_sub_le_of_seminorm_bound {n : ℕ}
    (A : MultilinearMap ℝ (fun _ : Fin n => E) F)
    (p : Seminorm ℝ E) (B : ℝ)
    (hbound : ∀ v : Fin n → E, ‖A v‖ ≤ B * ∏ i, p (v i))
    (v w : Fin n → E) :
    ‖A w - A v‖ ≤ B * seminormMultilinearDifference p v w := by
  have heq : A w - A v = ∑ i : Fin n, A (multilinearDifferenceTuple v w i) := by
    change A w - A v = ∑ i : Fin n,
      A (fun j => if j < i then w j else if i = j then w j - v j else v j)
    simpa only [Finset.piecewise_univ, Finset.mem_univ, true_implies,
      multilinearDifferenceTuple] using A.map_sub_map_piecewise w v Finset.univ
  rw [heq]
  calc
    ‖∑ i : Fin n, A (multilinearDifferenceTuple v w i)‖ ≤
        ∑ i : Fin n, ‖A (multilinearDifferenceTuple v w i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, B * ∏ j : Fin n, p (multilinearDifferenceTuple v w i j) :=
      Finset.sum_le_sum (fun i hi => hbound _)
    _ = B * seminormMultilinearDifference p v w := (Finset.mul_sum _ _ _).symm

theorem continuous_multilinear_of_seminorm_bound
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {n : ℕ} (A : MultilinearMap ℝ (fun _ : Fin n => E) F)
    (p : Seminorm ℝ E) (hp : Continuous p) (B : ℝ)
    (hbound : ∀ v : Fin n → E, ‖A v‖ ≤ B * ∏ i, p (v i)) : Continuous A := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun w => B * seminormMultilinearDifference p v w) (𝓝 v) (𝓝 0) := by
    simpa only [seminormMultilinearDifference_self, mul_zero] using
      (continuous_const.mul (continuous_seminormMultilinearDifference p hp v)).tendsto v
  exact squeeze_zero (fun w => norm_nonneg _)
    (fun w => norm_multilinear_sub_le_of_seminorm_bound A p B hbound v w) hlim

end MultilinearBounds

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {T : MaterialData} {γ : ℝ} {S : CircleModelData} {n : ℕ}

def liftCircleMultilinear (hS : IsCircleModel T γ S)
    (A : MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hA : ∀ v, CircleMember T γ (A v)) :
    MultilinearMap ℝ (fun _ : Fin n => E) S.Space where
  toFun v := circleRealize hS (A v) (hA v)
  map_update_add' v i x y := by
    apply hS.2.2.2.2.2.1
    simp only [map_add, circleRealize_decode, A.map_update_add]
  map_update_smul' v i c x := by
    apply hS.2.2.2.2.2.1
    simp only [map_smul, circleRealize_decode, A.map_update_smul]

theorem liftCircleMultilinear_decode (hS : IsCircleModel T γ S)
    (A : MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hA : ∀ v, CircleMember T γ (A v)) (v : Fin n → E) :
    S.decode (liftCircleMultilinear hS A hA v) = A v :=
  circleRealize_decode hS (A v) (hA v)

theorem liftCircleMultilinear_continuous
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hS : IsCircleModel T γ S)
    (A : MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hA : ∀ v, CircleMember T γ (A v))
    (hbound : ∀ s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧
      ∀ v : Fin n → E, circleNorm T γ s (A v) ≤ B * ∏ i, p (v i)) :
    Continuous (liftCircleMultilinear hS A hA) := by
  let M := liftCircleMultilinear hS A hA
  have hcoordinate (s : ℕ) : Continuous (fun v => (M v).val s) := by
    obtain ⟨p, B, hp, hb⟩ := hbound s
    let Q := projectiveCoordinate (fun j => S.level j) S.bond s
    let L := Q.toLinearMap.compMultilinearMap M
    apply continuous_multilinear_of_seminorm_bound L p hp B
    intro v
    change ‖(M v).val s‖ ≤ _
    rw [hS.2.2.2.2.2.2.2, liftCircleMultilinear_decode]
    exact hb v
  apply continuous_iff_continuousAt.mpr
  intro v
  rw [ContinuousAt, tendsto_projectiveLimit_iff]
  exact fun s => (hcoordinate s).tendsto v

def liftCircleContinuousMultilinear
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hS : IsCircleModel T γ S)
    (A : MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hA : ∀ v, CircleMember T γ (A v))
    (hbound : ∀ s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧
      ∀ v : Fin n → E, circleNorm T γ s (A v) ≤ B * ∏ i, p (v i)) :
    E [×n]→L[ℝ] S.Space :=
  { liftCircleMultilinear hS A hA with
    cont := liftCircleMultilinear_continuous hS A hA hbound }

theorem liftCircleContinuousMultilinear_decode
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hS : IsCircleModel T γ S)
    (A : MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hA : ∀ v, CircleMember T γ (A v))
    (hbound : ∀ s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧
      ∀ v : Fin n → E, circleNorm T γ s (A v) ≤ B * ∏ i, p (v i))
    (v : Fin n → E) : S.decode (liftCircleContinuousMultilinear hS A hA hbound v) = A v :=
  liftCircleMultilinear_decode hS A hA v

end ContinuousFlexibility.Statements
