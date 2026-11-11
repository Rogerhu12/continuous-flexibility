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

private theorem bilinear_field_seminorm_bound
    {E G : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : ∀ s, Continuous (p s))
    (N : ℕ → G → ℝ) (A : (Fin 2 → E) → G) (P : E → E → G)
    (heq : ∀ v : Fin 2 → E, A v = P (v 0) (v 1))
    (hb : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      N s (P u v) ≤ C * p (s + 1) u * p (s + 1) v) :
    ∀ s, ∃ q : Seminorm ℝ E, ∃ B : ℝ, Continuous q ∧
      ∀ v : Fin 2 → E, N s (A v) ≤ B * ∏ i, q (v i) := by
  intro s
  obtain ⟨C, hC, hc⟩ := hb s
  refine ⟨p (s + 1), C, hp (s + 1), ?_⟩
  intro v
  rw [heq, Fin.prod_univ_two]
  simpa only [mul_assoc] using hc (v 0) (v 1)

private theorem bilinear_unit_growth_of_finite_norms
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (hp : Monotone p)
    (N : ℕ → F → ℝ) (P : E → E → F) (R : ℕ → E → E → ℝ)
    (hq : ∀ s y C, 0 ≤ C → (q s y ≤ C ↔ ∀ i, i ≤ s → N i y ≤ C))
    (heq : ∀ s u v, N s (P u v) = R s u v)
    (hg : ∃ base loss : ℕ, base ≤ loss ∧ ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      p base u ≤ 1 → p base v ≤ 1 →
      R s u v ≤ C * (1 + p (s + loss) u + p (s + loss) v)) :
    ∃ base loss : ℕ, base ≤ loss ∧ ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      p base u ≤ 1 → p base v ≤ 1 →
      q s (P u v) ≤ C * (1 + p (s + loss) u + p (s + loss) v) := by
  classical
  obtain ⟨base, loss, hbl, hb⟩ := hg
  choose C hC hbound using hb
  refine ⟨base, loss, hbl, ?_⟩
  intro s
  let K : ℝ := ∑ i ∈ Finset.range (s + 1), C i
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨K, hK, ?_⟩
  intro u v hu hv
  have hsize : 0 ≤ 1 + p (s + loss) u + p (s + loss) v := by positivity
  apply (hq s (P u v) _ (mul_nonneg hK hsize)).mpr
  intro i hi
  rw [heq]
  have hCi : C i ≤ K := Finset.single_le_sum
    (f := C) (fun j _ => hC j) (Finset.mem_range.mpr (by omega))
  have hpu := hp (Nat.add_le_add_right hi loss) u
  have hpv := hp (Nat.add_le_add_right hi loss) v
  exact (hbound i u v hu hv).trans
    ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hpu) hpv) (hC i)).trans
      (mul_le_mul_of_nonneg_right hCi hsize))

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
  exact bilinear_field_seminorm_bound S.grading
    (fun s => (withSeminorms_graded (fun i => S.level i) S.bond).continuous_seminorm s)
    (circleNorm T γ) (circleProductFieldMultilinear S)
    (fun u v m θ => S.decode u m θ * S.decode v m θ)
    (circleProductFieldMultilinear_apply S)
    (circleNorm_product_coarse_bound hS hw.1 hw.2 hA hHA)

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
  exact bilinear_unit_growth_of_finite_norms S.grading S.grading
    (gradedSeminorm_monotone (fun j => S.level j) S.bond)
    (fun s y => circleNorm T γ s (S.decode y))
    (circleProductBilinear hS hT hD hγ)
    (fun s u v => circleNorm T γ s (fun m θ => S.decode u m θ * S.decode v m θ))
    (fun s y C hC => circleGrading_le_iff_circleNorm hS s y hC)
    (fun s u v => congrArg (circleNorm T γ s) (circleProductBilinear_decode hS hT hD hγ u v))
    (circleNorm_product_unit_growth hS hw.1 hw.2 hA hHA hinterp)

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
    change
      p (s + loss) x.1 * p base y.2 + p base x.1 * p (s + loss) y.2 ≤
        (p (s + loss) x.1 + p (s + loss) x.2) * (p base y.1 + p base y.2) +
          (p base x.1 + p base x.2) * (p (s + loss) y.1 + p (s + loss) y.2)
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

private theorem bilinear_function_oneHigh_of_unit_growth
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [ContinuousConstSMul ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (hp : Monotone p)
    (B : E [×2]→L[ℝ] F) (P : E → E → F)
    (heq : ∀ v : Fin 2 → E, B v = P (v 0) (v 1))
    (hg : ∃ base loss : ℕ, base ≤ loss ∧ ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      p base u ≤ 1 → p base v ≤ 1 →
      q s (P u v) ≤ C * (1 + p (s + loss) u + p (s + loss) v)) :
    ∃ base loss : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      q s (P u v) ≤ C * (p (s + loss) u * p base v + p base u * p (s + loss) v) := by
  obtain ⟨base, loss, hbl, hb⟩ := hg
  have hunit : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin 2 → E,
      (∀ i, p base (v i) < 1) → q s (B v) ≤ C * (1 + ∑ i, p (s + loss) (v i)) := by
    intro s
    obtain ⟨C, hC, hc⟩ := hb s
    refine ⟨C, hC, ?_⟩
    intro v hv
    rw [heq, Fin.sum_univ_two]
    simpa only [add_assoc] using hc (v 0) (v 1) (hv 0).le (hv 1).le
  have hn := bilinear_oneHigh_of_unit_bound p q hp B hbl hunit
  refine ⟨base, loss, ?_⟩
  intro s
  obtain ⟨C, hC, hc⟩ := hn s
  refine ⟨C, hC, ?_⟩
  intro u v
  have he : B ![u, v] = P u v := heq ![u, v]
  exact he ▸ hc u v

private theorem smoothTameOn_bilinear_function_of_bound
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (B : E [×2]→L[ℝ] F) (P : E → E → F)
    (heq : ∀ v : Fin 2 → E, B v = P (v 0) (v 1))
    (hg : ∃ base loss : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      q s (P u v) ≤ C * (p (s + loss) u * p base v + p base u * p (s + loss) v)) :
    SmoothTameOn (pairGrading p p) q univ (fun z : E × E => P z.1 z.2) := by
  obtain ⟨base, loss, hb⟩ := hg
  have hB : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      q s (B ![u, v]) ≤
        C * (p (s + loss) u * p base v + p base u * p (s + loss) v) := by
    intro s
    obtain ⟨C, hC, hc⟩ := hb s
    refine ⟨C, hC, ?_⟩
    intro u v
    have he : B ![u, v] = P u v := heq ![u, v]
    exact he.symm ▸ hc u v
  apply smoothTameOn_congr (smoothTameOn_pair_of_multilinear_bound p q B hB)
  intro z hz
  exact heq ![z.1, z.2]

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
  exact bilinear_function_oneHigh_of_unit_growth S.grading S.grading
    (gradedSeminorm_monotone (fun j => S.level j) S.bond)
    (circleProductContinuousMultilinear hS hT hD hγ)
    (circleProductBilinear hS hT hD hγ)
    (circleProductContinuousMultilinear_eq hS hT hD hγ)
    (circleProduct_grading_unit_growth hS hT hD hγ hinterp)

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
  exact smoothTameOn_bilinear_function_of_bound S.grading S.grading
    (circleProductContinuousMultilinear hS hT hD hγ)
    (circleProductBilinear hS hT hD hγ)
    (circleProductContinuousMultilinear_eq hS hT hD hγ)
    (circleProduct_oneHigh_bound hS hT hD hγ hinterp)

end ContinuousFlexibility.Statements
