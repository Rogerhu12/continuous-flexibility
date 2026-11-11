import ContinuousFlexibility.Analysis.N01aReferenceCoarseningNorms

/-!
# Inverse, reciprocity and first-normal estimates after coarsening

The actual inverse function is unchanged. Only its norm constant increases;
the weak differential expression, border, row and physical equivalence are
identical for the two partitions.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

private theorem n01a_coarsened_inverse_constant {K C x : ℝ} (hK : 1 ≤ K) (hx : 0 ≤ x) :
    K * (C ^ 2 * x) ≤ (K * C) ^ 2 * x := by
  have hKsq : K ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
  have hc : K * C ^ 2 ≤ (K * C) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hKsq (sq_nonneg C)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc hx

namespace N01aReferenceCoarsening

variable {D E : ReferenceData} {σ : ℕ → ℕ} (h : N01aReferenceCoarsening D E σ)

theorem inverse_properties (hD : RadialPartition D) (hE : RadialPartition E)
    (hab : D.a ≤ D.b) {γ M₀ M₁ : ℝ} {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ReferenceInverseProperties E γ M₀ M₁ G := by
  obtain ⟨K, hK, hsrc, hout⟩ := h.exists_norm_comparison hD hE hab
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have habE : E.a ≤ E.b := by simpa only [h.a_eq, h.b_eq] using hab
  obtain ⟨hsolve, huniq, hlinear, C, hC, hbound⟩ := hG
  refine ⟨?_, ?_, ?_, K * C, mul_pos hKpos hC, ?_⟩
  · intro F hF
    exact (h.graph_iff hD hE hab γ M₀ M₁ (G F) F).mpr
      (hsolve F ((h.source_iff hD hE hab γ M₀ F).mp hF))
  · intro U F hUF
    exact (h.representative_iff (G F) U).mpr
      (huniq U F ((h.graph_iff hD hE hab γ M₀ M₁ U F).mp hUF))
  · intro F L hF hL c d
    exact (h.representative_iff _ _).mpr (hlinear F L
      ((h.source_iff hD hE hab γ M₀ F).mp hF)
      ((h.source_iff hD hE hab γ M₀ L).mp hL) c d)
  · intro F hF
    have hFD := (h.source_iff hD hE hab γ M₀ F).mp hF
    obtain ⟨aL, hU, hUF⟩ := hbound F hFD
    refine ⟨aL, (h.output_realization_iff hD hE hab γ M₁ aL (G F)).mpr hU, ?_⟩
    calc
      _ ≤ K * outputNormSquare D γ M₁ aL (G F) := (hout γ M₁ aL (G F) hU).2
      _ ≤ K * (C ^ 2 * sourceNormSquare D γ M₀ F) :=
        mul_le_mul_of_nonneg_left hUF hKpos.le
      _ ≤ K * (C ^ 2 * sourceNormSquare E γ M₀ F) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (hsrc γ M₀ F hFD.1 hFD.2.1).1 (sq_nonneg C)) hKpos.le
      _ ≤ _ := n01a_coarsened_inverse_constant hK
        (n01a_sourceNormSquare_nonneg habE γ M₀ F)

theorem bounded_inverse (hD : RadialPartition D) (hE : RadialPartition E)
    (hab : D.a ≤ D.b) {γ M₀ M₁ : ℝ}
    (hG : BoundedReferenceInverse D γ M₀ M₁) : BoundedReferenceInverse E γ M₀ M₁ := by
  obtain ⟨G, hG⟩ := hG
  exact ⟨G, h.inverse_properties hD hE hab hG⟩

theorem green_reciprocity (hD : RadialPartition D) (hE : RadialPartition E)
    (hab : D.a ≤ D.b) {γ M₀ M₁ : ℝ} (hR : ReferenceGreenReciprocity D γ M₀ M₁) :
    ReferenceGreenReciprocity E γ M₀ M₁ := by
  intro U V F L hUF hVL
  have hr := hR U V F L
    ((h.graph_iff hD hE hab γ M₀ M₁ U F).mp hUF)
    ((h.graph_iff hD hE hab γ M₀ M₁ V L).mp hVL)
  simpa only [h.core_eq, h.a_eq, h.b_eq] using hr

theorem first_normal_estimate (hD : RadialPartition D) (hE : RadialPartition E)
    (hab : D.a ≤ D.b) {γ M₀ M₁ : ℝ} {G : RadialSource → RadialUnknown}
    (hN : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    FirstNormalInverseEstimate E γ M₀ M₁ G := by
  obtain ⟨K, hK, hsrc, hout⟩ := h.exists_norm_comparison hD hE hab
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have habE : E.a ≤ E.b := by simpa only [h.a_eq, h.b_eq] using hab
  obtain ⟨C, hC, hN⟩ := hN
  refine ⟨K * C, mul_pos hKpos hC, ?_⟩
  intro F fθ hF hθ hfθ
  have hFD := (h.source_iff hD hE hab γ M₀ F).mp hF
  have hfθD := (h.source_iff hD hE hab γ M₀ (fθ, 0)).mp hfθ
  obtain ⟨ur, hur, hU, hbound⟩ := hN F fθ hFD ((h.angular_iff F.1 fθ).mp hθ) hfθD
  refine ⟨ur, (h.normal_iff (G F).1 ur).mpr hur,
    (h.output_realization_iff hD hE hab γ M₁ 0 (ur, 0)).mpr hU, ?_⟩
  calc
    _ ≤ K * outputNormSquare D γ M₁ 0 (ur, 0) := (hout γ M₁ 0 (ur, 0) hU).2
    _ ≤ K * (C ^ 2 * (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (fθ, 0))) :=
      mul_le_mul_of_nonneg_left hbound hKpos.le
    _ ≤ K * (C ^ 2 * (sourceNormSquare E γ M₀ F + sourceNormSquare E γ M₀ (fθ, 0))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (add_le_add (hsrc γ M₀ F hFD.1 hFD.2.1).1
          (hsrc γ M₀ (fθ, 0) hfθD.1 hfθD.2.1).1) (sq_nonneg C)) hKpos.le
    _ ≤ _ := n01a_coarsened_inverse_constant hK
      (add_nonneg (n01a_sourceNormSquare_nonneg habE γ M₀ F)
        (n01a_sourceNormSquare_nonneg habE γ M₀ (fθ, 0)))

end N01aReferenceCoarsening

end ContinuousFlexibility.Statements
