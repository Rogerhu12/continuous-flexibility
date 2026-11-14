module

public import ContinuousFlexibility.Radial.DeepTailPoissonContinuity
public import ContinuousFlexibility.Radial.DeepTailEdgeCoordinates

/-!
# Choosing the actual Poisson basis continuously on fixed edges

Only joint continuity of the density on the closed physical edge is
needed. The split between its mass and resistance parts may depend on
the parameter; it is absent from the Poisson equation itself.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped NNReal
open ContinuousFlexibility.Statements

theorem continuousOn_tailFamilyDensity {P : Type*} [TopologicalSpace P]
    {p : P → ℝ → ℝ} {a b : ℝ}
    (hp : Continuous (fun z : P × Icc a b => p z.1 z.2)) (σ : P) :
    ContinuousOn (p σ) (Icc a b) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact hp.comp (continuous_const.prodMk continuous_id)

/-- Restrict the density's original joint continuity to any fixed closed
edge lying inside every member of the family. -/
theorem deepTailFamily_density_continuous_on_interval
    {P : Type*} [TopologicalSpace P] (family : P → DeepTailData) {a b : ℝ}
    (hp : ContinuousOn (fun z : P × ℝ => (family z.1).p z.2)
      {z | z.2 ∈ Ico (family z.1).entrance (family z.1).endpoint})
    (hsub : ∀ σ, Icc a b ⊆ Ico (family σ).entrance (family σ).endpoint) :
    Continuous (fun z : P × Icc a b => (family z.1).p z.2) := by
  exact hp.comp_continuous
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    (fun z => hsub z.1 z.2.property)

/-- A common bound for the actual Green contraction gives continuous
Poisson functions and continuous coefficients of their actual flux matrix. -/
theorem exists_continuous_tailPhysicalPoissonFamily
    {P : Type*} [TopologicalSpace P] {a b θ : ℝ}
    (p : P → ℝ → ℝ) (hab : a < b) (Λ η : P → ℝ)
    (hp : Continuous (fun z : P × Icc a b => p z.1 z.2))
    (hpos : ∀ σ x, x ∈ Icc a b → 0 < p σ x)
    (hΛcont : Continuous Λ) (hΛ : ∀ σ, 0 ≤ Λ σ)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) (hη : ∀ σ, η σ ≤ θ)
    (hsmall : ∀ σ,
      tailEdgeDiagonalSize
        ((tailResistanceChart_strictMono
          (tailClampedDensity_continuous hab.le (continuousOn_tailFamilyDensity hp σ))
          (tailClampedDensity_pos hab.le (hpos σ)) a) hab)
        (tailClampedEdgePotential hab.le (continuousOn_tailFamilyDensity hp σ) (hpos σ) (Λ σ)) ≤
        η σ) :
    ∃ B : ∀ σ, TailPhysicalPoissonData (p σ) a b (Λ σ) (η σ) hab.le,
      (∀ right, Continuous (fun σ => (B σ).onEdge right)) ∧
      Continuous (fun σ => (B σ).offDiagonal) ∧
      Continuous (fun σ => (B σ).leftDiagonal) ∧
      Continuous (fun σ => (B σ).rightDiagonal) := by
  let B (σ : P) : TailPhysicalPoissonData (p σ) a b (Λ σ) (η σ) hab.le :=
    Classical.choice (exists_tailPhysicalPoissonData hab (continuousOn_tailFamilyDensity hp σ)
      (hpos σ) (hΛ σ) ((hη σ).trans_lt hθ₁) (hsmall σ))
  let K : ℝ≥0 := ⟨θ, hθ₀⟩
  have hK : K < 1 := hθ₁
  have hdiag (σ : P) : (∫ t in a..b,
      tailPhysicalGreenWeight (p σ) a b hab.le (Λ σ) t t) ≤ K := by
    rw [tailPhysicalGreenWeight_diagonal_eq hab (continuousOn_tailFamilyDensity hp σ) (hpos σ)]
    exact (hsmall σ).trans (hη σ)
  have hB (right : Bool) : Continuous (fun σ => (B σ).onEdge right) :=
    continuous_tailPhysicalPoissonOn p hab Λ η hp hpos hΛcont hΛ B K hK hdiag right
  exact ⟨B, hB, continuous_tailPhysicalPoissonCoefficients p hab Λ η hp hpos hΛcont hΛ B hB⟩

end ContinuousFlexibility.Radial
