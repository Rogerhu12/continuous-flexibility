module

public import ContinuousFlexibility.Analysis.N08PhysicalLabelTests
public import ContinuousFlexibility.Analysis.N08TailHeightMultiplier

/-!
# Actual height cutoffs at the physical control components

The physical cells are obtained from the N01 mixed-flow tests. Their
cutoffs are fixed once, before any grading or control-label power. The
weight comparison pays that label power and leaves one inverse physical
envelope factor, including for the fixed reference height.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

private theorem n08_rpow_inverse_successor {M : ℝ} (hM : 0 < M) (N : ℝ) :
    M ^ N * (M ^ (N + 1))⁻¹ = M⁻¹ := by
  rw [Real.rpow_add hM, Real.rpow_one, mul_inv_rev]
  field_simp [(Real.rpow_pos_of_pos hM N).ne', hM.ne']

private theorem n08_reweight_localizations
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (M : ℕ → ℝ) (F : ℕ → E → E) (physical : ℕ → ℕ)
    (hM : ∀ m, 0 < M m)
    (hweight : ∀ a : ℝ, ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ m,
      M m ^ a ≤ C * M (physical m) ^ N)
    (htail : ∀ N : ℝ, ∃ l : ℕ, ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ m u,
      p s (F m u) ≤ K * (M m ^ N)⁻¹ * p (s + l) u) :
    ∀ s a : ℕ, ∃ b : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ m u,
      M m ^ a * p s (F (physical m) u) ≤ K * (M (physical m))⁻¹ * p b u := by
  intro s a
  obtain ⟨C, N, hC, _, hCb⟩ := hweight (a : ℝ)
  obtain ⟨l, hLb⟩ := htail (N + 1)
  obtain ⟨K, hK, hKb⟩ := hLb s
  refine ⟨s + l, C * K, mul_nonneg hC.le hK, fun m u => ?_⟩
  have hlabel : M m ^ a ≤ C * M (physical m) ^ N := by
    simpa only [Real.rpow_natCast] using hCb m
  calc
    _ ≤ (C * M (physical m) ^ N) *
        (K * (M (physical m) ^ (N + 1))⁻¹ * p (s + l) u) :=
      mul_le_mul hlabel (hKb (physical m) u) (apply_nonneg _ _)
        (mul_nonneg hC.le (Real.rpow_nonneg (hM (physical m)).le _))
    _ = (C * K) *
        (M (physical m) ^ N * (M (physical m) ^ (N + 1))⁻¹) * p (s + l) u := by ring
    _ = _ := by rw [n08_rpow_inverse_successor (hM (physical m))]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08_control_height_localizations
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    ∃ physical : ℕ → ℕ,
      ∃ F : ℕ → (S.height (3 / 4 : ℝ)).Space →L[ℝ] (S.height (3 / 4 : ℝ)).Space,
      (∃ K : ℝ, 0 < K ∧ ∀ m,
        T.H (T.sample (physical m)) ^ (33 : ℝ) ≤
          K * T.H (T.sample (C.cell m)) ^ (3 / 8 : ℝ)) ∧
      (∀ m (u : (S.height (3 / 4 : ℝ)).Space),
        ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ,
          (S.height (3 / 4 : ℝ)).decode (F m u) =ᶠ[𝓝 (r, θ)]
            (S.height (3 / 4 : ℝ)).decode u) ∧
      ∀ s a : ℕ, ∃ b : ℕ, ∃ K : ℝ, 0 ≤ K ∧
        ∀ m (u : (S.height (3 / 4 : ℝ)).Space),
          T.M (T.sample m) ^ a * (S.height (3 / 4 : ℝ)).grading s (F m u) ≤
            K * (T.M (T.sample (physical m)))⁻¹ * (S.height (3 / 4 : ℝ)).grading b u := by
  obtain ⟨physical, hcell, hH, hweight⟩ := n08_control_physical_cells hT hS hN
  obtain ⟨A, hA, hplatform⟩ := n08_referenceCell_layer_parameters hN.1.1
  let F (m : ℕ) : (S.height (3 / 4 : ℝ)).Space →L[ℝ] (S.height (3 / 4 : ℝ)).Space :=
    n08CellLayerMultiplier hT (hS.1 (3 / 4 : ℝ)) A (physical m)
  refine ⟨physical, F, hH, ?_, ?_⟩
  · intro m u r hr θ
    exact n08CellLayerMultiplier_decode_germ hT (hS.1 (3 / 4 : ℝ))
      (zero_lt_one.trans_le hA) (physical m) u (hplatform (physical m) r (hcell m hr))
  · exact n08_reweight_localizations (S.height (3 / 4 : ℝ)).grading
      (fun m => T.M (T.sample m))
      (fun m u => n08CellLayerMultiplier hT (hS.1 (3 / 4 : ℝ)) A m u) physical
      (fun m => zero_lt_one.trans_le (n08_material_sample_bounds hN.1.1 hT m).2)
      hweight
      (fun N => n08CellLayerMultiplier_tail_bound
        (W := S.height (3 / 4 : ℝ)) (γ := (3 / 4 : ℝ)) hN.1.1 hT
        (hS.1 (3 / 4 : ℝ)) hA N)

end ContinuousFlexibility.Statements
