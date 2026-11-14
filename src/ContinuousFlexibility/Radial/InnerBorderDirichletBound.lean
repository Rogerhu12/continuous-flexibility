module

public import ContinuousFlexibility.Radial.InnerProjectedInverseBound
public import ContinuousFlexibility.Radial.InnerLocalizedInverseBound

/-!
# The actual weighted bordered Dirichlet sum

The direct sum is made from restriction, a local operator, and zero
extension on the same physical Hilbert product. Only the central piece
receives the scalar. Separate local input and output bounds include
the actual coefficient loss and preserve a constant independent of
the number of cells.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped BigOperators

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
  (μ : Measure α) (sets : ι → Set α) (center : ι)
  (D : ι → InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ)

def innerBorderDirichletSum : InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ :=
  innerProjectedDirichletSum (innerBorderPieceProjection μ sets center) D

theorem innerBorderDirichletSum_weighted_bound
    (hmeas : ∀ i, MeasurableSet (sets i))
    (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))
    (W V : α → ℝ) (hW : Measurable W) (hV : Measurable V) (CW CV : ℝ)
    (hWC : ∀ x, |W x| ≤ CW) (hVC : ∀ x, |V x| ≤ CV)
    (u v : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hucenter : 1 ≤ u center) (hvcenter : 1 ≤ v center)
    (hlocalW : ∀ i x, x ∈ sets i → |W x| ≤ u i)
    (hlocalV : ∀ i x, x ∈ sets i → |V x| ≤ v i)
    {K : ℝ} (hK : 0 ≤ K) (hcost : ∀ i, u i * v i * ‖D i‖ ≤ K) :
    ‖innerBorderFieldMap μ (innerWeightMultiplier μ W hW CW hWC) ∘L
      innerBorderDirichletSum μ sets center D ∘L
        innerBorderFieldMap μ (innerWeightMultiplier μ V hV CV hVC)‖ ≤ K := by
  apply innerProjectedDirichletSum_weighted_bound
    (innerBorderPieceProjection μ sets center) D
    (innerBorderFieldMap μ (innerWeightMultiplier μ W hW CW hWC))
    (innerBorderFieldMap μ (innerWeightMultiplier μ V hV CV hVC)) u v hu hv
      (innerBorderPieceProjections_bessel μ sets center hmeas hdis)
  · intro i k hik F H
    exact innerBorderPieceProjections_orthogonal μ sets center hmeas hdis F H hik
  · exact innerBorderPieceProjection_contract μ sets center hmeas
  · exact innerBorderPieceProjection_weight_commute μ sets center hmeas W hW CW hWC
  · intro i F
    exact innerBorderPieceProjection_weight_bound μ sets center hmeas W hW CW hWC i
      (hu i) (fun hi => by simpa only [hi] using hucenter) (hlocalW i) F
  · intro i F
    rw [← innerBorderPieceProjection_weight_commute μ sets center hmeas V hV CV hVC]
    exact innerBorderPieceProjection_weight_bound μ sets center hmeas V hV CV hVC i
      (hv i) (fun hi => by simpa only [hi] using hvcenter) (hlocalV i) F
  · exact hK
  · exact hcost

/-- The localized coefficient multiplier occurs on the output exactly
once. Its local cost is loss_i * ratio_i² * norm(D_i). -/
theorem innerBorderDirichletSum_localized_cost
    (hmeas : ∀ i, MeasurableSet (sets i))
    (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))
    (W V : α → ℝ) (hW : Measurable W) (hV : Measurable V) (CW CV : ℝ)
    (hWC : ∀ x, |W x| ≤ CW) (hVC : ∀ x, |V x| ≤ CV)
    (loss ratio w : ι → ℝ)
    (hloss : ∀ i, 0 ≤ loss i) (hratio : ∀ i, 0 ≤ ratio i) (hw : ∀ i, 0 < w i)
    (hcenterW : 1 ≤ loss center * ratio center * w center)
    (hcenterV : 1 ≤ ratio center / w center)
    (hlocalW : ∀ i x, x ∈ sets i → |W x| ≤ loss i * ratio i * w i)
    (hlocalV : ∀ i x, x ∈ sets i → |V x| ≤ ratio i / w i)
    {K : ℝ} (hK : 0 ≤ K) (hcost : ∀ i, loss i * (ratio i ^ 2 * ‖D i‖) ≤ K) :
    ‖innerBorderFieldMap μ (innerWeightMultiplier μ W hW CW hWC) ∘L
      innerBorderDirichletSum μ sets center D ∘L
        innerBorderFieldMap μ (innerWeightMultiplier μ V hV CV hVC)‖ ≤ K := by
  apply innerBorderDirichletSum_weighted_bound μ sets center D hmeas hdis
    W V hW hV CW CV hWC hVC
      (fun i => loss i * ratio i * w i) (fun i => ratio i / w i)
        (fun i => mul_nonneg (mul_nonneg (hloss i) (hratio i)) (hw i).le)
        (fun i => div_nonneg (hratio i) (hw i).le)
        hcenterW hcenterV hlocalW hlocalV hK
  intro i
  have heq : (loss i * ratio i * w i) * (ratio i / w i) * ‖D i‖ =
      loss i * (ratio i ^ 2 * ‖D i‖) := by
    field_simp [(hw i).ne'] <;> ring
  rw [heq]
  exact hcost i

end ContinuousFlexibility.Radial
