import ContinuousFlexibility.Analysis.CircleCompositionJetModels

/-!
# Fixed-order and tame bounds for finite actual circle products

The number of factors is fixed before the output order. Coarse bounds
are used for projective continuity, while the second estimate retains
affine high-order growth on every low-seminorm box.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

private theorem grading_product_coarse_loss
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (product : E → E → E)
    (hbound : ∃ base loss : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      p s (product u v) ≤ C * (p (s + loss) u * p base v +
        p base u * p (s + loss) v)) :
    ∃ loss : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      p s (product u v) ≤ C * p (s + loss) u * p (s + loss) v := by
  obtain ⟨base, loss, hb⟩ := hbound
  refine ⟨base + loss, ?_⟩
  intro s
  obtain ⟨C, hC, hc⟩ := hb s
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro u v
  have hu0 := hp (show base ≤ s + (base + loss) by omega) u
  have hv0 := hp (show base ≤ s + (base + loss) by omega) v
  have hu1 := hp (show s + loss ≤ s + (base + loss) by omega) u
  have hv1 := hp (show s + loss ≤ s + (base + loss) by omega) v
  exact (hc u v).trans ((mul_le_mul_of_nonneg_left
    (add_le_add
      (mul_le_mul hu1 hv0 (apply_nonneg _ _) (apply_nonneg _ _))
      (mul_le_mul hu0 hv1 (apply_nonneg _ _) (apply_nonneg _ _))) hC).trans_eq (by ring))

private theorem grading_finiteProduct_coarse_bound
    {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (product : E → E → E)
    (finiteProduct : E → (ι → E) → Finset ι → E)
    (hempty : ∀ u v, finiteProduct u v ∅ = u)
    (hinsert : ∀ u v I i, i ∉ I → finiteProduct u v (insert i I) =
      product (v i) (finiteProduct u v I))
    (hbound : ∃ loss : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      p s (product u v) ≤ C * p (s + loss) u * p (s + loss) v) (I : Finset ι) :
    ∃ loss : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E) (v : ι → E),
      p s (finiteProduct u v I) ≤
        C * p (s + loss) u * ∏ i ∈ I, p (s + loss) (v i) := by
  classical
  obtain ⟨L, hproduct⟩ := hbound
  induction I using Finset.induction_on with
  | empty =>
      refine ⟨0, fun s => ⟨1, zero_le_one, ?_⟩⟩
      intro u v
      simp only [hempty, Finset.prod_empty, one_mul, mul_one,
        Nat.add_zero, le_refl]
  | @insert i I hi ih =>
      obtain ⟨loss, hb⟩ := ih
      refine ⟨L + loss, ?_⟩
      intro s
      obtain ⟨C0, hC0, hc0⟩ := hproduct s
      obtain ⟨C1, hC1, hc1⟩ := hb (s + L)
      refine ⟨C0 * C1, mul_nonneg hC0 hC1, ?_⟩
      intro u v
      rw [hinsert u v I i hi]
      have hprev : p (s + L) (finiteProduct u v I) ≤
          C1 * p (s + (L + loss)) u *
            ∏ j ∈ I, p (s + (L + loss)) (v j) := by
        simpa only [Nat.add_assoc] using hc1 u v
      have hvi : p (s + L) (v i) ≤ p (s + (L + loss)) (v i) :=
        hp (by omega) (v i)
      calc
        _ ≤ C0 * p (s + L) (v i) *
            p (s + L) (finiteProduct u v I) :=
          hc0 (v i) _
        _ ≤ C0 * p (s + (L + loss)) (v i) *
            (C1 * p (s + (L + loss)) u *
              ∏ j ∈ I, p (s + (L + loss)) (v j)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hvi hC0) hprev (apply_nonneg _ _)
            (mul_nonneg hC0 (apply_nonneg _ _))
        _ = _ := by rw [Finset.prod_insert hi]; ring

private theorem grading_finiteProduct_local_growth
    {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (product : E → E → E)
    (finiteProduct : E → (ι → E) → Finset ι → E)
    (hempty : ∀ u v, finiteProduct u v ∅ = u)
    (hinsert : ∀ u v I i, i ∉ I → finiteProduct u v (insert i I) =
      product (v i) (finiteProduct u v I))
    (hbound : ∃ base loss : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      p s (product u v) ≤ C * (p (s + loss) u * p base v +
        p base u * p (s + loss) v)) (I : Finset ι) :
    ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : E) (v : ι → E), p base u ≤ K → (∀ i ∈ I, p base (v i) ≤ K) →
        p s (finiteProduct u v I) ≤
          C * (1 + p (s + loss) u + ∑ i ∈ I, p (s + loss) (v i)) := by
  classical
  obtain ⟨b0, l0, hproduct⟩ := hbound
  induction I using Finset.induction_on with
  | empty =>
      refine ⟨0, 0, fun K hK s => ⟨1, zero_le_one, ?_⟩⟩
      intro u v hu hv
      simp only [hempty, Finset.sum_empty, one_mul, add_zero,
        Nat.add_zero]
      exact le_add_of_nonneg_left zero_le_one
  | @insert i I hi ih =>
      obtain ⟨bi, li, hb⟩ := ih
      let base : ℕ := max b0 (max bi (b0 + li))
      let loss : ℕ := l0 + li
      have hb0 : b0 ≤ base := le_max_left _ _
      have hbi : bi ≤ base := (le_max_left bi _).trans (le_max_right _ _)
      have hblo : b0 + li ≤ base := (le_max_right bi _).trans (le_max_right _ _)
      refine ⟨base, loss, ?_⟩
      intro K hK
      obtain ⟨CL, hCL, hcl⟩ := hb K hK b0
      let L : ℝ := CL * (1 + K + (I.card : ℝ) * K)
      have hL : 0 ≤ L := by dsimp [L]; positivity
      intro s
      obtain ⟨C0, hC0, hc0⟩ := hproduct s
      obtain ⟨C1, hC1, hc1⟩ := hb K hK (s + l0)
      refine ⟨C0 * (L + K * C1), mul_nonneg hC0 (add_nonneg hL (mul_nonneg hK hC1)), ?_⟩
      intro u v hu hv
      have hui : p bi u ≤ K := (hp hbi u).trans hu
      have hvi (j : ι) (hj : j ∈ I) : p bi (v j) ≤ K :=
        (hp hbi (v j)).trans (hv j (Finset.mem_insert_of_mem hj))
      have hlow : p b0 (finiteProduct u v I) ≤ L := by
        have hsum : (∑ j ∈ I, p (b0 + li) (v j)) ≤ (I.card : ℝ) * K := by
          calc
            _ ≤ ∑ _j ∈ I, K := Finset.sum_le_sum (fun j hj =>
              (hp hblo (v j)).trans (hv j (Finset.mem_insert_of_mem hj)))
            _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
        exact (hcl u v hui hvi).trans (mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add le_rfl ((hp hblo u).trans hu)) hsum) hCL)
      let R : ℝ := 1 + p (s + loss) u +
        ∑ j ∈ insert i I, p (s + loss) (v j)
      have hR : 0 ≤ R := by dsimp [R]; positivity
      have hrest : 1 + p (s + loss) u +
          ∑ j ∈ I, p (s + loss) (v j) ≤ R := by
        dsimp [R]
        rw [Finset.sum_insert hi]
        have hnonneg : 0 ≤ p (s + loss) (v i) := apply_nonneg _ _
        linarith
      have hhigh : p (s + l0) (finiteProduct u v I) ≤ C1 * R := by
        have h := hc1 u v hui hvi
        have h' : p (s + l0) (finiteProduct u v I) ≤
            C1 * (1 + p (s + loss) u +
              ∑ j ∈ I, p (s + loss) (v j)) := by
          simpa only [loss, Nat.add_assoc] using h
        exact h'.trans (mul_le_mul_of_nonneg_left hrest hC1)
      have hviHigh : p (s + l0) (v i) ≤ R := by
        have hsingle : p (s + loss) (v i) ≤
            ∑ j ∈ insert i I, p (s + loss) (v j) :=
          Finset.single_le_sum (f := fun j => p (s + loss) (v j))
            (fun j _ => apply_nonneg _ _) (Finset.mem_insert_self i I)
        exact (hp (show s + l0 ≤ s + loss by dsimp [loss]; omega) (v i)).trans
          (hsingle.trans (le_add_of_nonneg_left (by positivity)))
      have hviLow : p b0 (v i) ≤ K :=
        (hp hb0 (v i)).trans (hv i (Finset.mem_insert_self i I))
      rw [hinsert u v I i hi]
      calc
        _ ≤ C0 * (p (s + l0) (v i) *
              p b0 (finiteProduct u v I) +
            p b0 (v i) *
              p (s + l0) (finiteProduct u v I)) :=
          hc0 (v i) _
        _ ≤ C0 * (R * L + K * (C1 * R)) :=
          mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul hviHigh hlow (apply_nonneg _ _) hR)
            (mul_le_mul hviLow hhigh (apply_nonneg _ _) hK)) hC0
        _ = C0 * (L + K * C1) * R := by ring

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem circleProduct_grading_coarse_loss
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) :
    ∃ loss : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : S.Space,
      S.grading s (circleProductBilinear hS hT hD hγ u v) ≤
        C * S.grading (s + loss) u * S.grading (s + loss) v := by
  exact grading_product_coarse_loss S.grading
    (gradedSeminorm_monotone (fun i => S.level i) S.bond)
    (circleProductBilinear hS hT hD hγ)
    (circleProduct_oneHigh_bound hS hT hD hγ hinterp)

theorem circleFiniteProductWith_coarse_bound
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (I : Finset ι) :
    ∃ loss : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : S.Space) (v : ι → S.Space),
      S.grading s (circleFiniteProductWith hS hT hD hγ u v I) ≤
        C * S.grading (s + loss) u * ∏ i ∈ I, S.grading (s + loss) (v i) := by
  exact grading_finiteProduct_coarse_bound S.grading
    (gradedSeminorm_monotone (fun i => S.level i) S.bond)
    (circleProductBilinear hS hT hD hγ) (circleFiniteProductWith hS hT hD hγ)
    (circleFiniteProductWith_empty hS hT hD hγ)
    (circleFiniteProductWith_insert hS hT hD hγ)
    (circleProduct_grading_coarse_loss hS hT hD hγ hinterp) I

/- The low order and the loss precede the radius. -/
theorem circleFiniteProductWith_local_growth
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (I : Finset ι) :
    ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : S.Space) (v : ι → S.Space),
        S.grading base u ≤ K → (∀ i ∈ I, S.grading base (v i) ≤ K) →
        S.grading s (circleFiniteProductWith hS hT hD hγ u v I) ≤
          C * (1 + S.grading (s + loss) u + ∑ i ∈ I, S.grading (s + loss) (v i)) := by
  exact grading_finiteProduct_local_growth S.grading
    (gradedSeminorm_monotone (fun i => S.level i) S.bond)
    (circleProductBilinear hS hT hD hγ) (circleFiniteProductWith hS hT hD hγ)
    (circleFiniteProductWith_empty hS hT hD hγ)
    (circleFiniteProductWith_insert hS hT hD hγ)
    (circleProduct_oneHigh_bound hS hT hD hγ hinterp) I

end ContinuousFlexibility.Statements
