import ContinuousFlexibility.Analysis.CircleProductMixedBounds
import ContinuousFlexibility.Analysis.CircleMultilinearRealization
import ContinuousFlexibility.Analysis.TameMultilinearNormalization
import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Joint smooth tame multiplication in the actual circle model

The physical Leibniz estimate first gives a continuous bilinear map in
the supplied projective space. Global interpolation on the unit low
seminorm ball and homogeneous normalization give one high factor with
a fixed loss. The ordinary quadratic directional tower then proves
joint smooth tameness of actual pointwise multiplication.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem material_circle_power_upper
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D) (hγ : 0 < γ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m, T.H (T.sample m) ^ γ ≤ A := by
  obtain ⟨_, hbounds⟩ := hD
  have hs := materialSample_mem_radialCore hT hbounds.2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecay, _⟩ := hT
  obtain ⟨A, hA, hbound, _⟩ := hdecay 0 γ hγ
  refine ⟨A, hA.le, ?_⟩
  intro m
  simpa only [Real.rpow_zero, mul_one] using hbound (T.sample m) (hs m)

def circleProductFieldMultilinear (S : CircleModelData) :
    MultilinearMap ℝ (fun _ : Fin 2 => S.Space) (ℕ → ℝ → ℝ) :=
  (MultilinearMap.mkPiAlgebra ℝ (Fin 2) (ℕ → ℝ → ℝ)).compLinearMap
    (fun _ => S.decode)

theorem circleProductFieldMultilinear_apply (S : CircleModelData) (v : Fin 2 → S.Space) :
    circleProductFieldMultilinear S v =
      fun m θ => S.decode (v 0) m θ * S.decode (v 1) m θ := by
  change (∏ i : Fin 2, S.decode (v i)) = _
  rw [Fin.prod_univ_two]
  rfl

theorem circleProductFieldMultilinear_member
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (v : Fin 2 → S.Space) :
    CircleMember T γ (circleProductFieldMultilinear S v) := by
  rw [circleProductFieldMultilinear_apply,
    ← circleProductBilinear_decode hS hT hD hγ (v 0) (v 1)]
  exact hS.2.2.2.1 _

theorem circleProductFieldMultilinear_bound
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) :
    ∀ s, ∃ p : Seminorm ℝ S.Space, ∃ B : ℝ, Continuous p ∧
      ∀ v : Fin 2 → S.Space,
        circleNorm T γ s (circleProductFieldMultilinear S v) ≤ B * ∏ i, p (v i) := by
  obtain ⟨A, hA, hHA⟩ := material_circle_power_upper hT hD hγ
  have hw := material_circle_sample_weights_pos hT hD
  intro s
  obtain ⟨C, hC, hb⟩ := circleNorm_product_coarse_bound hS hw.1 hw.2 hA hHA s
  refine ⟨S.grading (s + 1), C,
    (withSeminorms_graded (fun i => S.level i) S.bond).continuous_seminorm _, ?_⟩
  intro v
  rw [circleProductFieldMultilinear_apply, Fin.prod_univ_two]
  simpa only [mul_assoc] using hb (v 0) (v 1)

def circleProductContinuousMultilinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) :
    S.Space [×2]→L[ℝ] S.Space :=
  liftCircleContinuousMultilinear hS (circleProductFieldMultilinear S)
    (circleProductFieldMultilinear_member hS hT hD hγ)
    (circleProductFieldMultilinear_bound hS hT hD hγ)

theorem circleProductContinuousMultilinear_eq
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (v : Fin 2 → S.Space) :
    circleProductContinuousMultilinear hS hT hD hγ v =
      circleProductBilinear hS hT hD hγ (v 0) (v 1) := by
  apply hS.2.2.2.2.2.1
  rw [circleProductContinuousMultilinear, liftCircleContinuousMultilinear_decode,
    circleProductFieldMultilinear_apply, circleProductBilinear_decode]

theorem circleProduct_grading_unit_growth
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) :
    ∃ base loss : ℕ, base ≤ loss ∧ ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : S.Space,
      S.grading base u ≤ 1 → S.grading base v ≤ 1 →
      S.grading s (circleProductBilinear hS hT hD hγ u v) ≤
        C * (1 + S.grading (s + loss) u + S.grading (s + loss) v) := by
  classical
  obtain ⟨A, hA, hHA⟩ := material_circle_power_upper hT hD hγ
  have hw := material_circle_sample_weights_pos hT hD
  obtain ⟨base, loss, hbl, hb⟩ :=
    circleNorm_product_unit_growth hS hw.1 hw.2 hA hHA hinterp
  choose C hC hbound using hb
  refine ⟨base, loss, hbl, ?_⟩
  intro s
  let K : ℝ := ∑ i ∈ Finset.range (s + 1), C i
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨K, hK, ?_⟩
  intro u v hu hv
  have hsize : 0 ≤ 1 + S.grading (s + loss) u + S.grading (s + loss) v := by
    positivity
  apply (circleGrading_le_iff_circleNorm hS s _
    (mul_nonneg hK hsize)).mpr
  intro i hi
  rw [circleProductBilinear_decode]
  have hCi : C i ≤ K := Finset.single_le_sum
    (f := C) (fun j _ => hC j) (Finset.mem_range.mpr (by omega))
  have hpu := gradedSeminorm_monotone (fun j => S.level j) S.bond
    (Nat.add_le_add_right hi loss) u
  have hpv := gradedSeminorm_monotone (fun j => S.level j) S.bond
    (Nat.add_le_add_right hi loss) v
  exact (hbound i u v hu hv).trans
    ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hpu) hpv) (hC i)).trans
      (mul_le_mul_of_nonneg_right hCi hsize))

private theorem multilinearTameSize_fin_two
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (low high : Seminorm ℝ E) (u v : E) :
    multilinearTameSize low high 2 1 ![u, v] =
      low u * low v + (high u * low v + high v * low u) := by
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simp [multilinearTameSize, Fin.prod_univ_two, Fin.sum_univ_two, h0, h1]

/-- The multiplication estimate has one high factor and a loss fixed
before the output order. It holds on the entire original circle space. -/
theorem circleProduct_oneHigh_bound
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) :
    ∃ base loss : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : S.Space,
      S.grading s (circleProductBilinear hS hT hD hγ u v) ≤
        C * (S.grading (s + loss) u * S.grading base v +
          S.grading base u * S.grading (s + loss) v) := by
  classical
  obtain ⟨base, loss, hbl, hb⟩ :=
    circleProduct_grading_unit_growth hS hT hD hγ hinterp
  let B := circleProductContinuousMultilinear hS hT hD hγ
  refine ⟨base, loss, ?_⟩
  intro s
  obtain ⟨C, hC, hc⟩ := hb s
  have hunit (v : Fin 2 → S.Space) (hv : ∀ i, S.grading base (v i) < 1) :
      S.grading s (B v) ≤ C * (1 + ∑ i, S.grading (s + loss) (v i)) := by
    rw [show B v = circleProductBilinear hS hT hD hγ (v 0) (v 1) from
      circleProductContinuousMultilinear_eq hS hT hD hγ v, Fin.sum_univ_two]
    simpa only [add_assoc] using hc (v 0) (v 1) (hv 0).le (hv 1).le
  have hnormalized := multilinear_bound_of_unitBall B (S.grading s)
    (S.grading base) (S.grading (s + loss)) hC hunit
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro u v
  have hn := hnormalized ![u, v]
  rw [circleProductContinuousMultilinear_eq, multilinearTameSize_fin_two] at hn
  have hlow : S.grading base u * S.grading base v ≤
      S.grading (s + loss) u * S.grading base v :=
    mul_le_mul_of_nonneg_right
      (gradedSeminorm_monotone (fun j => S.level j) S.bond (by omega) u)
      (apply_nonneg _ _)
  let R := S.grading (s + loss) u * S.grading base v +
    S.grading base u * S.grading (s + loss) v
  have hlowR : S.grading base u * S.grading base v ≤ R :=
    hlow.trans (le_add_of_nonneg_right (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  calc
    _ ≤ C * (S.grading base u * S.grading base v +
        (S.grading (s + loss) u * S.grading base v +
          S.grading (s + loss) v * S.grading base u)) := hn
    _ = C * (S.grading base u * S.grading base v + R) := by dsimp [R]; ring
    _ ≤ C * (R + R) := mul_le_mul_of_nonneg_left (add_le_add hlowR le_rfl) hC
    _ = 2 * C * R := by ring

def circleProductPairMultilinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) :
    (S.Space × S.Space) [×2]→L[ℝ] S.Space :=
  (circleProductContinuousMultilinear hS hT hD hγ).compContinuousLinearMap
    (fun i : Fin 2 => if i = 0 then ContinuousLinearMap.fst ℝ S.Space S.Space
      else ContinuousLinearMap.snd ℝ S.Space S.Space)

theorem circleProductPairMultilinear_apply
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (v : Fin 2 → S.Space × S.Space) :
    circleProductPairMultilinear hS hT hD hγ v =
      circleProductBilinear hS hT hD hγ (v 0).1 (v 1).2 := by
  rw [circleProductPairMultilinear, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    circleProductContinuousMultilinear_eq]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
    ContinuousLinearMap.fst_apply, ContinuousLinearMap.snd_apply]

theorem smoothTameOn_circleProduct
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) :
    SmoothTameOn (pairGrading S.grading S.grading) S.grading univ
      (fun z : S.Space × S.Space => circleProductBilinear hS hT hD hγ z.1 z.2) := by
  obtain ⟨base, loss, hb⟩ := circleProduct_oneHigh_bound hS hT hD hγ hinterp
  let B := circleProductPairMultilinear hS hT hD hγ
  have hB : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : S.Space × S.Space,
      S.grading s (bilinearJetValue B x y) ≤
        C * (pairGrading S.grading S.grading (s + loss) x *
            pairGrading S.grading S.grading base y +
          pairGrading S.grading S.grading base x *
            pairGrading S.grading S.grading (s + loss) y) := by
    intro s hs
    obtain ⟨C, hC, hc⟩ := hb s
    refine ⟨C, hC, ?_⟩
    intro x y
    have heq : bilinearJetValue B x y =
        circleProductBilinear hS hT hD hγ x.1 y.2 := by
      exact circleProductPairMultilinear_apply hS hT hD hγ ![x, y]
    rw [heq]
    apply (hc x.1 y.2).trans
    apply mul_le_mul_of_nonneg_left _ hC
    simp only [tamePairGrading_apply]
    apply add_le_add
    · exact mul_le_mul (le_add_of_nonneg_right (apply_nonneg _ _))
        (le_add_of_nonneg_left (apply_nonneg _ _)) (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
    · exact mul_le_mul (le_add_of_nonneg_right (apply_nonneg _ _))
        (le_add_of_nonneg_left (apply_nonneg _ _)) (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  apply smoothTameOn_congr (smoothTameOn_quadratic B hB)
  intro z hz
  exact circleProductPairMultilinear_apply hS hT hD hγ ![z, z]

end ContinuousFlexibility.Statements
