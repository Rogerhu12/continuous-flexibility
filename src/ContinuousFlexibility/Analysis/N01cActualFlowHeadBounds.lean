import ContinuousFlexibility.Analysis.N01cFlowVariationInput
import ContinuousFlexibility.Analysis.N01cActualFlowDefectBounds
import ContinuousFlexibility.Analysis.N01cFlowHeadEnvelope

/-!
# The actual forcing head on one common neighbourhood

The original speed bound and the proved zero-parameter derivative-defect
bound supply the two inputs to actual circle composition. The loss is
chosen before the spatial order, and every finite parameter plot shares
the same constants.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem n01_ordinaryFlowForcingHead_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base₀ loss d₀ : ℕ} {ε ε₀ : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
      r ∈ Icc (C.left i) (C.right i) →
        0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε)
    (hB₀ : N01PartB D S C base₀ ε₀)
    (hGs : ∀ z ∈ stateNeighborhood S C base₀ ε₀, ∀ i,
      ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C i (z, p)))
    (hQ : OrdinaryFlowZeroAngularGrowth hS hT hA hB₀ hGs loss d₀)
    (hsub : stateNeighborhood S C base ε ⊆ stateNeighborhood S C base₀ ε₀)
    (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M)
    (hgeometry : ∀ N, ∀ u : OrdinaryFlowVariationInput D S C base ε N, ∀ t : ℝ,
      (∀ θ, c ≤ deriv
        (ordinaryFlowFiniteAngle u.component u.state u.mem u.plot t) θ) ∧
      u.defectNorm hS hT hA hB hpos 3 t ≤ M) :
    ∀ N : ℕ, 0 < N → ∃ offset : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ u : OrdinaryFlowVariationInput D S C base ε N,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ ω : FlowForcingChoice N,
        u.factorNorm hS hT hA hB hpos s t ω 0 ≤
          B * T.H (T.sample (C.cell u.component)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell u.component)) ^ B *
            u.aggregate (s + offset) * u.aggregate offset := by
  intro N hN
  let I := OrdinaryFlowVariationInput D S C base ε N ×
    ((Icc (0 : ℝ) 1) × FlowForcingChoice N)
  let head : ℕ → I → ℝ := fun s i =>
    i.1.factorNorm hS hT hA hB hpos s i.2.1 i.2.2 0
  let outer : ℕ → I → ℝ := fun s i =>
    i.1.outerNorm hS hT hA hB hpos s i.2.1 i.2.2
  let defect : ℕ → I → ℝ := fun s i =>
    i.1.defectNorm hS hT hA hB hpos s i.2.1
  let R : ℕ → I → ℝ := fun s i => i.1.aggregate s
  let H : I → ℝ := fun i => T.H (T.sample (C.cell i.1.component))
  let E : I → ℝ := fun i => T.E0 (T.sample (C.cell i.1.component))
  have hsample (i : I) :
      T.sample (C.cell i.1.component) ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell i.1.component)
  have houter : ∃ o : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i : I,
      outer s i ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B * R (s + loss + o) i := by
    refine n01c_transport_offset_bounds _ _
      (n01_ordinaryFlowSpeedOuter_sobolev_bounds
        hS hT hA hε hB hpos hE hSpeed N hN) ?_
    intro o s B hBpos hbound i
    exact hbound i.1.component i.1.tower i.1.dimension i.1.state i.1.mem
      i.1.plot i.1.directions i.1.unit i.2.1 i.2.1.property i.2.2
  have hdefect : ∀ s : ℕ, ∃ Q : ℝ, 0 < Q ∧ ∀ i : I,
      defect s i ≤ Q * R (s + (1 + loss + d₀)) i := by
    refine n01c_transfer_positiveConstants _ _
      (ordinaryFlowFiniteDefectJet_sobolev_growth hS hT hA hB hpos
        hB₀ hGs loss d₀ hQ hsub) ?_
    intro s Q hQpos hbound i
    have hb := hbound i.1.component i.1.tower i.1.dimension i.1.state i.1.mem
      i.1.plot i.2.1
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ hQpos.le
    simpa only [Nat.add_assoc] using i.1.stateSize_le_aggregate (s + 1 + loss + d₀)
  have hhead := n01c_headComposition_envelope head outer defect R H E
    (circleLiftCompositionConstant Real.pi c M) loss (1 + loss + d₀)
    (fun i => (hT.2.1 _ (hsample i)).2.1.le)
    (fun i => hE _ (hsample i))
    (fun s i => i.1.aggregate_one_le s)
    (fun a b hab i => i.1.aggregate_mono hab)
    (fun s => zero_le_one.trans (circleLiftCompositionConstant_one_le Real.pi c M s))
    (fun s i => circle_real_sobolevNorm_nonneg _ _)
    (fun s i => ordinaryFlowForcingFactorJet_head_sobolev_le
      hS hT hA hB hpos i.1.component i.1.tower i.1.state i.1.mem i.1.plot
      i.1.directions i.2.1 i.2.2 s hc hM
      (hgeometry N i.1 i.2.1).1 (hgeometry N i.1 i.2.1).2)
    houter hdefect
  refine n01c_transport_offset_bounds _ _ hhead ?_
  intro offset s B hBpos hbound u t ht ω
  exact hbound (u, (⟨t, ht⟩, ω))

end ContinuousFlexibility.Blueprint
