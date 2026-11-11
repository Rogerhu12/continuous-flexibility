import ContinuousFlexibility.Analysis.N01cActualFlowForcingEnvelope
import ContinuousFlexibility.Analysis.N01cActualFlowCoefficientEnvelope
import ContinuousFlexibility.Analysis.N01cFlowLinearFamilyEnvelope

/-!
# The actual positive variation on its original unit ball

The actual forcing estimate and the actual linear equation are now
combined. The polynomial degree depends only on the current state
order. No spatial derivative order enters the exponential constant.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem n01_ordinaryFlowVariation_unitBall_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
      r ∈ Icc (C.left i) (C.right i) →
        0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (Mlin : ℝ)
    (hlinear : ∀ n, ∀ u : OrdinaryFlowVariationInput D S C base ε (n + 1),
      (u.data hS hT hA hB hpos).coefficientSize 1 ≤ Mlin)
    (hcoefficient : ∃ offset : ℕ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ n, ∀ u : OrdinaryFlowVariationInput D S C base ε (n + 1),
      ∀ t ∈ Icc (0 : ℝ) 1,
        (u.data hS hT hA hB hpos).coefficientNorm s t ≤
          A * u.aggregate (s + offset) * u.aggregate offset)
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
    ∃ offset : ℕ, ∀ b : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ u : OrdinaryFlowVariationInput D S C base ε (n + 1),
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ : ℝ,
        |(u.data hS hT hA hB hpos).value t b (θ : AddCircle Real.pi)| ≤
          B * T.H (T.sample (C.cell u.component)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell u.component)) ^ B *
            u.aggregate (b + offset) * u.aggregate offset ^ (2 * (n + 1) + 5) := by
  let I := OrdinaryFlowVariationInput D S C base ε (n + 1)
  let V : I → CircleLinearVariationData Real.pi 0 1 := fun u => u.data hS hT hA hB hpos
  let R : ℕ → I → ℝ := fun s u => u.aggregate s
  let H : I → ℝ := fun u => T.H (T.sample (C.cell u.component))
  let E : I → ℝ := fun u => T.E0 (T.sample (C.cell u.component))
  have hcoef : ∃ offset : ℕ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ u : I, ∀ t ∈ Icc (0 : ℝ) 1,
        (V u).coefficientNorm s t ≤ A * R (s + offset) u * R offset u := by
    refine n01c_transport_offset_bounds _ _ hcoefficient ?_
    intro offset s A hApos hb u t ht
    exact hb n u t ht
  have hforcing :=
    n01_ordinaryFlowForcing_bounds hS hT hA hB hpos hE n hIH hhead
  have hsample (u : I) :
      T.sample (C.cell u.component) ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell u.component)
  have hraw := n01c_linearVariationFamily_angularEnvelope V R H E (2 * (n + 1) + 3)
    Mlin (fun u => (hT.2.1 _ (hsample u)).2.1.le) (fun u => hE _ (hsample u))
    (fun s u => u.aggregate_one_le s)
    (fun a b hab u => u.aggregate_mono hab) (hlinear n) hcoef hforcing
  refine n01c_transport_offset_bounds _ _ hraw ?_
  intro offset b B hBpos hb u t ht θ
  simpa only [Nat.add_assoc] using hb u t ht (θ : AddCircle Real.pi)

end ContinuousFlexibility.Blueprint
