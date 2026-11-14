module

public import ContinuousFlexibility.Analysis.N01ControlPlateauWeights
public import ContinuousFlexibility.Analysis.N01FlowSamplePrefactor

/-!
# Fixed material losses from return labels to local energy points

The pure material comparison costs three orders, uniformly in the
requested power. Combining it with the complete N01 sample prefactor
costs four orders, even when the N01 exponent depends on the output jet.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.controlPlateau_material_pow_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m t,
      t ∈ Icc
        (C.left m - endpointPlateauWidth D (C.left m) (C.right m))
        (C.right m + endpointPlateauWidth D (C.left m) (C.right m)) →
      T.M (T.sample m) ^ s ≤ K * T.M t ^ (s + 3) := by
  obtain ⟨K₁, hK₁, hsample⟩ := hN.actualCell_material_order_bound hS hT s
  obtain ⟨K₂, hK₂, hpoint⟩ := materialCell_plateau_sample_weight_bound hN.1.1 hT
    (le_refl (0 : ℝ)) (s + 1)
  obtain ⟨_, _, hcells⟩ := hN.actualCell_travel_lower_bound
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  refine ⟨K₁ * K₂, mul_pos hK₁ hK₂, fun m t ht => ?_⟩
  obtain ⟨_, j, hj, _⟩ := hcells m
  have hp := hpoint j (C.left m) (C.right m)
    (hcontrol.1 m).1 (hcontrol.1 m).2.1 (hcontrol.1 m).2.2 hj t ht
  simp only [neg_zero, Real.rpow_zero, one_mul, mul_one] at hp
  calc
    _ ≤ K₁ * T.M (T.sample j) ^ (s + 1) := hsample m j hj
    _ ≤ K₁ * (K₂ * T.M t ^ ((s + 1) + 2)) := mul_le_mul_of_nonneg_left hp hK₁.le
    _ = _ := by rw [Nat.add_assoc]; ring

/-- The exponent `A` is chosen after the fixed loss four. Its size only
changes the positive constant, including for `A = B(k,s)` from N01. -/
theorem N01Properties.flow_weighted_prefactor_on_plateau
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {A : ℝ} (hA : 0 ≤ A) (s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m t,
      t ∈ Icc
        (C.left m - endpointPlateauWidth D (C.left m) (C.right m))
        (C.right m + endpointPlateauWidth D (C.left m) (C.right m)) →
      T.H (T.sample m) ^ (-(3 / 4 : ℝ)) * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ A * T.M (T.sample m) ^ s ≤
          K * T.M t ^ (s + 4) := by
  obtain ⟨K₁, hK₁, hprefactor⟩ := hN.flow_sample_prefactor_le_M hT hA
  obtain ⟨K₂, hK₂, hpoint⟩ := hN.controlPlateau_material_pow_bound hS hT (s + 1)
  refine ⟨K₁ * K₂, mul_pos hK₁ hK₂, fun m t ht => ?_⟩
  have hm : 0 ≤ T.M (T.sample m) :=
    zero_le_one.trans (hT.2.1 _
      (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m)).2.2.2
  calc
    _ ≤ (K₁ * T.M (T.sample m)) * T.M (T.sample m) ^ s :=
      mul_le_mul_of_nonneg_right (hprefactor m) (pow_nonneg hm s)
    _ = K₁ * T.M (T.sample m) ^ (s + 1) := by rw [pow_succ]; ring
    _ ≤ K₁ * (K₂ * T.M t ^ ((s + 1) + 3)) := mul_le_mul_of_nonneg_left (hpoint m t ht) hK₁.le
    _ = _ := by rw [Nat.add_assoc]; ring

end ContinuousFlexibility.Statements
