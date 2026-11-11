import ContinuousFlexibility.Analysis.N01cActualFlowLowerBounds
import ContinuousFlexibility.Analysis.N01cActualFlowHeadBounds
import ContinuousFlexibility.Analysis.N01cFlowForcingFamilyEnvelope

/-!
# The actual positive variational forcing under strict induction

The input at lower parameter orders is the canonical genuine flow jet
already obtained in the induction. The resulting forcing estimate is
for the actual circle linear equation of the same finite plot.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem n01_ordinaryFlowForcing_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
      r ∈ Icc (C.left i) (C.right i) →
        0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (n : ℕ)
    (hIH : ∀ k, k < n + 1 → 0 < k →
      OrdinaryFlowAngularOrderBound hS hT hA hB hpos loss k)
    (hhead : ∃ offset : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ u : OrdinaryFlowVariationInput D S C base ε (n + 1),
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ choice : FlowForcingChoice (n + 1),
        u.factorNorm hS hT hA hB hpos s t choice 0 ≤
          B * T.H (T.sample (C.cell u.component)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell u.component)) ^ B *
            u.aggregate (s + offset) * u.aggregate offset) :
    ∃ offset : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ u : OrdinaryFlowVariationInput D S C base ε (n + 1),
      ∀ t ∈ Icc (0 : ℝ) 1,
        (u.data hS hT hA hB hpos).forcingNorm s t ≤
          B * T.H (T.sample (C.cell u.component)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell u.component)) ^ B *
            u.aggregate (s + offset) * u.aggregate offset ^ (2 * (n + 1) + 3) := by
  let I := OrdinaryFlowVariationInput D S C base ε (n + 1) × Icc (0 : ℝ) 1
  let F : ℕ → I → ℝ := fun s i =>
    (i.1.data hS hT hA hB hpos).forcingNorm s i.2
  let R : ℕ → I → ℝ := fun s i => i.1.aggregate s
  let H : I → ℝ := fun i => T.H (T.sample (C.cell i.1.component))
  let E : I → ℝ := fun i => T.E0 (T.sample (C.cell i.1.component))
  let f : ℕ → I → ∀ choice : FlowForcingChoice (n + 1), Fin (choice.1.length + 1) → ℝ :=
    fun s i choice j => i.1.factorNorm hS hT hA hB hpos s i.2 choice j
  have hh : ∃ o : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i : I, ∀ choice,
      f s i choice 0 ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
        R (s + o) i * R o i := by
    refine n01c_transport_offset_bounds _ _ hhead ?_
    intro o s B hBpos hb i choice
    exact hb i.1 i.2 i.2.property choice
  have hl : ∃ o : ℕ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ i : I,
      ∀ (choice : FlowForcingChoice (n + 1)) (j : Fin choice.1.length),
        f s i choice j.succ ≤ A * R (s + o) i := by
    refine n01c_transport_offset_bounds _ _
      (n01_ordinaryFlowLowerFactors_bounds hS hT hA hB hpos hE hIH) ?_
    intro o s A hApos hb i choice j
    exact hb i.1 i.2 choice j
  have hsample (i : I) :
      T.sample (C.cell i.1.component) ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell i.1.component)
  have hf := n01c_forcingFamily_envelope Real.pi (n + 1) F R H E f
    (fun i => (hT.2.1 _ (hsample i)).2.1.le)
    (fun i => hE _ (hsample i))
    (fun s i => i.1.aggregate_one_le s)
    (fun a b hab i => i.1.aggregate_mono hab)
    (fun s i choice j => circle_real_sobolevNorm_nonneg _ _)
    (fun s i => by
      simpa only [F, f, OrdinaryFlowVariationInput.data,
        OrdinaryFlowVariationInput.factorNorm, Nat.cast_one] using
        ordinaryFlowCircleVariationData_forcingNorm_le hS hT hA hB hpos
          i.1.component i.1.tower i.1.state i.1.mem i.1.plot n i.1.directions i.2 s)
    hh hl
  refine n01c_transport_offset_bounds _ _ hf ?_
  intro o s B hBpos hb u t ht
  exact hb (u, ⟨t, ht⟩)

end ContinuousFlexibility.Blueprint
