module

public import ContinuousFlexibility.Analysis.MaterialSampleWeightedConstraint
public import ContinuousFlexibility.Statements.Nonlinear

/-!
# One fixed material order for the full N01 flow prefactor

The positive N01 height factor cancels the inverse output height weight
after a bounded sample-index change. The remaining, arbitrarily large
`E0` power costs exactly one material order. Its exponent changes only
the numerical constant, not the derivative loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem materialSample_cancelled_height_prefactor_le_M
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (γ : ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ m n : ℕ,
      |(D.cellIndex m : ℝ) - D.cellIndex n| ≤ B →
      T.H (T.sample n) ^ (-γ) * T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ A ≤
        K * T.M (T.sample n) := by
  obtain ⟨KH, P, hKH, _, hshift⟩ :=
    materialSample_H_E0_rpow_of_index_sub_bound hT hD γ hA hB
  obtain ⟨KE, hKE, hE⟩ := materialSample_E0_rpow_le_M hT hD P
  obtain ⟨_, hgeom⟩ := hD
  refine ⟨KH * KE, mul_pos hKH hKE, fun m n hmn => ?_⟩
  have hH : 0 < T.H (T.sample n) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hgeom.2.1 n)).2.1
  have hcancel : T.H (T.sample n) ^ (-γ) * T.H (T.sample n) ^ γ = 1 := by
    rw [← Real.rpow_add hH, neg_add_cancel, Real.rpow_zero]
  calc
    _ = T.H (T.sample n) ^ (-γ) *
        (T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ A) := by ring
    _ ≤ T.H (T.sample n) ^ (-γ) *
        (KH * T.H (T.sample n) ^ γ * T.E0 (T.sample n) ^ P) :=
      mul_le_mul_of_nonneg_left (hshift m n hmn) (Real.rpow_nonneg hH.le _)
    _ = (T.H (T.sample n) ^ (-γ) * T.H (T.sample n) ^ γ) *
        (KH * T.E0 (T.sample n) ^ P) := by ring
    _ = KH * T.E0 (T.sample n) ^ P := by rw [hcancel, one_mul]
    _ ≤ KH * (KE * T.M (T.sample n)) := mul_le_mul_of_nonneg_left (hE n) hKH.le
    _ = _ := by ring

/-- The loss is the literal natural number one for every exponent `A`.
In particular, `A` may be the N01 constant depending on the jet order. -/
theorem N01Properties.flow_sample_prefactor_le_M
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ,
      T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
        T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ A ≤ K * T.M (T.sample m) := by
  obtain ⟨B, hB, hindex⟩ := hN.2.2.2.2.1
  obtain ⟨K, hK, hbound⟩ := materialSample_cancelled_height_prefactor_le_M
    hT hN.1.1 (3 / 4 : ℝ) hA hB.le
  exact ⟨K, hK, fun m => hbound (C.cell m) m (hindex m)⟩

end ContinuousFlexibility.Statements
