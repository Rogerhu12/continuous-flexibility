import ContinuousFlexibility.Analysis.N01cCosineSpeedParameterBounds
import ContinuousFlexibility.Analysis.N01cFlowSlotBounds

/-! Finite prefixes of actual cosine-speed state derivatives, with one
additive loss chosen before the spatial order and unchanged low base. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

theorem n01c_materialOneHigh_mono
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p)
    (base : ℕ) {high high' : ℕ} (hh : high ≤ high')
    {B B' H E : ℝ} (hB : 0 ≤ B) (hBB' : B ≤ B') (hH : 0 ≤ H) (hE : 1 ≤ E)
    (γ : ℝ) (x : X) {k : ℕ} (v : Fin k → X) :
    B * H ^ γ * E ^ B * oneHighVariationWeight p base high x v ≤
      B' * H ^ γ * E ^ B' * oneHighVariationWeight p base high' x v := by
  have hB' := hB.trans hBB'
  have hHγ := Real.rpow_nonneg hH γ
  have hE' : 0 ≤ E := zero_le_one.trans hE
  have hC : B * H ^ γ * E ^ B ≤ B' * H ^ γ * E ^ B' :=
    mul_le_mul (mul_le_mul_of_nonneg_right hBB' hHγ)
      (Real.rpow_le_rpow_of_exponent_le hE hBB')
      (Real.rpow_nonneg hE' B) (mul_nonneg hB' hHγ)
  exact mul_le_mul hC (oneHighVariationWeight_mono hp le_rfl hh x v)
    (oneHighVariationWeight_nonneg p base high x v)
    (mul_nonneg (mul_nonneg hB' hHγ) (Real.rpow_nonneg hE' B'))

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- Every selected forcing speed factor has state and angle arity at
most K. One loss and one constant control all such arities at once. -/
theorem n01_componentCosineAngularStateJets_prefix_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε) :
    ∀ K : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ k : ℕ, k ≤ K → ∀ m b t θ, b ≤ s + K →
      t ∈ Icc (0 : ℝ) Real.pi → 0 < k + b →
      ∀ J : SmoothDirections (stateNeighborhood S C base ε)
        (fun z => iteratedDeriv b (fun η => componentCosineSpeed D S C m (z, (t, η))) θ),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss + d) (z - (C.referenceState, 0)) v := by
  let P : ℕ → ℕ → ℕ → ℝ → Prop := fun k s high B =>
    ∀ m b t θ, b ≤ s → t ∈ Icc (0 : ℝ) Real.pi → 0 < k + b →
      ∀ J : SmoothDirections (stateNeighborhood S C base ε)
        (fun z => iteratedDeriv b (fun η => componentCosineSpeed D S C m (z, (t, η))) θ),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base high (z - (C.referenceState, 0)) v
  exact n01c_finiteOrderPrefix P loss
    (fun k s high high' B B' hh hBpos hBB' hraw m b t θ hb ht hkb J z hz v => by
      have hsample := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
      exact (hraw m b t θ hb ht hkb J z hz v).trans
        (n01c_materialOneHigh_mono
          (pairGrading (stateGrading S) realGrading) (jointStateGrading_monotone S)
          base hh hBpos.le hBB' (hT.2.1 _ hsample).2.1.le (hE _ hsample)
          (3 / 4 : ℝ) (z - (C.referenceState, 0)) v))
    (n01_componentCosineAngularStateJets_bounds hS hT hA hε hB hE hSpeed)

end ContinuousFlexibility.Blueprint
