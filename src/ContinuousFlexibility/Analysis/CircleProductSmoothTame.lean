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
  let ha := material_circle_power_upper hT hD hγ
  let A : ℝ := ha.choose
  have hA : 0 ≤ A := ha.choose_spec.1
  have hHA := ha.choose_spec.2
  have hw := material_circle_sample_weights_pos hT hD
  intro s
  let hc := circleNorm_product_coarse_bound hS hw.1 hw.2 hA hHA s
  let C : ℝ := hc.choose
  have hb := hc.choose_spec.2
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
  have hdecode := liftCircleContinuousMultilinear_decode hS (circleProductFieldMultilinear S)
    (circleProductFieldMultilinear_member hS hT hD hγ)
    (circleProductFieldMultilinear_bound hS hT hD hγ) v
  exact hdecode.trans ((circleProductFieldMultilinear_apply S v).trans
    (circleProductBilinear_decode hS hT hD hγ (v 0) (v 1)).symm)

theorem circleProduct_grading_unit_growth
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) :
    ∃ base loss : ℕ, base ≤ loss ∧ ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : S.Space,
      S.grading base u ≤ 1 → S.grading base v ≤ 1 →
      S.grading s (circleProductBilinear hS hT hD hγ u v) ≤
        C * (1 + S.grading (s + loss) u + S.grading (s + loss) v) := by
  classical
  let ha := material_circle_power_upper hT hD hγ
  let A : ℝ := ha.choose
  have hA : 0 ≤ A := ha.choose_spec.1
  have hHA := ha.choose_spec.2
  have hw := material_circle_sample_weights_pos hT hD
  let hg := circleNorm_product_unit_growth hS hw.1 hw.2 hA hHA hinterp
  let base : ℕ := hg.choose
  let loss : ℕ := hg.choose_spec.choose
  have hbl : base ≤ loss := hg.choose_spec.choose_spec.1
  have hb := hg.choose_spec.choose_spec.2
  let C : ℕ → ℝ := fun s => (hb s).choose
  have hC (s : ℕ) : 0 ≤ C s := (hb s).choose_spec.1
  have hbound (s : ℕ) := (hb s).choose_spec.2
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

private theorem bilinear_oneHigh_of_unit_bound
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [ContinuousConstSMul ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (hp : Monotone p)
    (B : E [×2]→L[ℝ] F) {base loss : ℕ} (hbl : base ≤ loss)
    (hb : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin 2 → E,
      (∀ i, p base (v i) < 1) →
      q s (B v) ≤ C * (1 + ∑ i, p (s + loss) (v i))) :
    ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      q s (B ![u, v]) ≤
        C * (p (s + loss) u * p base v + p base u * p (s + loss) v) := by
  intro s
  obtain ⟨C, hC, hc⟩ := hb s
  have hnormalized := multilinear_bound_of_unitBall B (q s)
    (p base) (p (s + loss)) hC hc
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro u v
  have hn := hnormalized ![u, v]
  rw [multilinearTameSize_fin_two] at hn
  have hlow : p base u * p base v ≤ p (s + loss) u * p base v :=
    mul_le_mul_of_nonneg_right (hp (by omega) u) (apply_nonneg _ _)
  let R := p (s + loss) u * p base v + p base u * p (s + loss) v
  have hlowR : p base u * p base v ≤ R := hlow.trans
    (le_add_of_nonneg_right (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  calc
    _ ≤ C * (p base u * p base v +
        (p (s + loss) u * p base v + p (s + loss) v * p base u)) := hn
    _ = C * (p base u * p base v + R) := by dsimp [R]; ring
    _ ≤ C * (R + R) := mul_le_mul_of_nonneg_left (add_le_add hlowR le_rfl) hC
    _ = 2 * C * R := by ring

private theorem multilinear_pair_precomp_apply
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (B : E [×2]→L[ℝ] F) (v : Fin 2 → E × E) :
    B.compContinuousLinearMap
        (fun i : Fin 2 => if i = 0 then ContinuousLinearMap.fst ℝ E E
          else ContinuousLinearMap.snd ℝ E E) v = B ![(v 0).1, (v 1).2] := by
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem smoothTameOn_pair_of_multilinear_bound
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (B : E [×2]→L[ℝ] F) {base loss : ℕ}
    (hb : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      q s (B ![u, v]) ≤
        C * (p (s + loss) u * p base v + p base u * p (s + loss) v)) :
    SmoothTameOn (pairGrading p p) q univ (fun z : E × E => B ![z.1, z.2]) := by
  let A : (E × E) [×2]→L[ℝ] F := B.compContinuousLinearMap
    (fun i : Fin 2 => if i = 0 then ContinuousLinearMap.fst ℝ E E
      else ContinuousLinearMap.snd ℝ E E)
  have hA : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : E × E,
      q s (bilinearJetValue A x y) ≤
        C * (pairGrading p p (s + loss) x * pairGrading p p base y +
          pairGrading p p base x * pairGrading p p (s + loss) y) := by
    intro s hs
    obtain ⟨C, hC, hc⟩ := hb s
    refine ⟨C, hC, ?_⟩
    intro x y
    have heq : bilinearJetValue A x y = B ![x.1, y.2] :=
      multilinear_pair_precomp_apply B ![x, y]
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
  apply smoothTameOn_congr (smoothTameOn_quadratic A hA)
  intro z hz
  exact multilinear_pair_precomp_apply B ![z, z]

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
  let hg := circleProduct_grading_unit_growth hS hT hD hγ hinterp
  let base : ℕ := hg.choose
  let loss : ℕ := hg.choose_spec.choose
  have hbl : base ≤ loss := hg.choose_spec.choose_spec.1
  have hb := hg.choose_spec.choose_spec.2
  let B := circleProductContinuousMultilinear hS hT hD hγ
  have hunit : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin 2 → S.Space,
      (∀ i, S.grading base (v i) < 1) →
      S.grading s (B v) ≤ C * (1 + ∑ i, S.grading (s + loss) (v i)) := by
    intro s
    let C : ℝ := (hb s).choose
    have hC : 0 ≤ C := (hb s).choose_spec.1
    have hc := (hb s).choose_spec.2
    refine ⟨C, hC, ?_⟩
    intro v hv
    rw [show B v = circleProductBilinear hS hT hD hγ (v 0) (v 1) from
      circleProductContinuousMultilinear_eq hS hT hD hγ v, Fin.sum_univ_two]
    simpa only [add_assoc] using hc (v 0) (v 1) (hv 0).le (hv 1).le
  have hnormal := bilinear_oneHigh_of_unit_bound S.grading S.grading
    (gradedSeminorm_monotone (fun j => S.level j) S.bond) B hbl hunit
  refine ⟨base, loss, ?_⟩
  intro s
  refine ⟨(hnormal s).choose, (hnormal s).choose_spec.1, ?_⟩
  intro u v
  have heq := circleProductContinuousMultilinear_eq hS hT hD hγ ![u, v]
  exact heq ▸ (hnormal s).choose_spec.2 u v

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
  exact (multilinear_pair_precomp_apply
    (circleProductContinuousMultilinear hS hT hD hγ) v).trans
      (circleProductContinuousMultilinear_eq hS hT hD hγ ![(v 0).1, (v 1).2])

theorem smoothTameOn_circleProduct
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) :
    SmoothTameOn (pairGrading S.grading S.grading) S.grading univ
      (fun z : S.Space × S.Space => circleProductBilinear hS hT hD hγ z.1 z.2) := by
  let hg := circleProduct_oneHigh_bound hS hT hD hγ hinterp
  let base : ℕ := hg.choose
  let loss : ℕ := hg.choose_spec.choose
  have hb := hg.choose_spec.choose_spec
  let B := circleProductContinuousMultilinear hS hT hD hγ
  have hB : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : S.Space,
      S.grading s (B ![u, v]) ≤
        C * (S.grading (s + loss) u * S.grading base v +
          S.grading base u * S.grading (s + loss) v) := by
    intro s
    refine ⟨(hb s).choose, (hb s).choose_spec.1, ?_⟩
    intro u v
    have heq := circleProductContinuousMultilinear_eq hS hT hD hγ ![u, v]
    exact heq.symm ▸ (hb s).choose_spec.2 u v
  apply smoothTameOn_congr
    (smoothTameOn_pair_of_multilinear_bound S.grading S.grading B hB)
  intro z hz
  exact circleProductContinuousMultilinear_eq hS hT hD hγ ![z.1, z.2]

end ContinuousFlexibility.Statements
