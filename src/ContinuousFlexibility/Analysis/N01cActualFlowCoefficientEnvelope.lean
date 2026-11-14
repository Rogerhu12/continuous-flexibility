module

public import ContinuousFlexibility.Analysis.N01cActualFlowHeadBounds
public import ContinuousFlexibility.Analysis.N01cMaterialAbsorption

/-!
# High norms of the actual linear variation coefficient

The coefficient is the all-angle singleton forcing head of the same
trajectory. Global material absorption removes its small weight, while
retaining one requested-order aggregate and one fixed-order aggregate.
Its fixed low integral is controlled separately on the common domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem n01_ordinaryFlowCoefficient_highBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
      r ∈ Icc (C.left i) (C.right i) →
        0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
    (hhead : ∃ offset : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ u : OrdinaryFlowVariationInput D S C base ε 1,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ choice : FlowForcingChoice 1,
        u.factorNorm hS hT hA hB hpos s t choice 0 ≤
          B * T.H (T.sample (C.cell u.component)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell u.component)) ^ B *
            u.aggregate (s + offset) * u.aggregate offset) :
    ∃ offset : ℕ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ n, ∀ u : OrdinaryFlowVariationInput D S C base ε (n + 1),
      ∀ t ∈ Icc (0 : ℝ) 1,
        (u.data hS hT hA hB hpos).coefficientNorm s t ≤
          A * u.aggregate (s + offset) * u.aggregate offset := by
  let I := OrdinaryFlowVariationInput D S C base ε 1 × Icc (0 : ℝ) 1
  let F : ℕ → I → ℝ := fun s i =>
    i.1.factorNorm hS hT hA hB hpos s i.2 flowAngleForcingChoice 0
  let R : ℕ → I → ℝ := fun s i => i.1.aggregate s
  let H : I → ℝ := fun i => T.H (T.sample (C.cell i.1.component))
  let E : I → ℝ := fun i => T.E0 (T.sample (C.cell i.1.component))
  have hweight : ∀ A : ℝ, ∃ Q : ℝ, 0 < Q ∧ ∀ i : I,
      H i ^ (3 / 4 : ℝ) * E i ^ A ≤ Q := by
    intro A
    obtain ⟨Q, hQ, hb⟩ := materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) A
    exact ⟨Q, hQ, fun i => hb _ (materialSample_mem_radialCore
      hT hA.1.1.choose_spec.2.1 (C.cell i.1.component))⟩
  have hF : ∃ offset : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i : I,
      F s i ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
        R (s + offset) i * R offset i := by
    refine n01c_transport_offset_bounds _ _ hhead ?_
    intro offset s B hBpos hb i
    exact hb i.1 i.2 i.2.property flowAngleForcingChoice
  have hscalar := n01c_productEnvelope_absorb F R H E
    (fun s i => zero_le_one.trans (i.1.aggregate_one_le s)) hweight hF
  refine n01c_transport_offset_bounds _ _ hscalar ?_
  intro offset s A hApos hb n u t ht
  rw [u.coefficientNorm_eq_angleHead hS hT hA hB hpos]
  have hh := hb (u.angleInput, ⟨t, ht⟩)
  exact hh.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (u.angleInput_aggregate_le (s + offset)) hApos.le)
    (u.angleInput_aggregate_le offset)
    (zero_le_one.trans (u.angleInput.aggregate_one_le offset))
    (mul_nonneg hApos.le (zero_le_one.trans (u.aggregate_one_le (s + offset)))))

end ContinuousFlexibility.Blueprint
