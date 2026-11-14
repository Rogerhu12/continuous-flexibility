module

public import ContinuousFlexibility.Analysis.N01LocalizedCoefficientBounds

/-!
# Actual original coefficient jets on a fixed radial strip

The existing localized N01 estimate already chooses its reference
compactness constant before the state. On the inner strip the fixed
clamp is exactly the identity, so locality transfers all its mixed jets
to the actual original coefficients without changing the loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def N01OriginalCoefficientStripBoundAtOrder
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε l u : ℝ) (s : ℕ) (A : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ Ioo l u ×ˢ (univ : Set ℝ),
        |mixedDerivative a b (canonicalCoefficientComponent i
          (originalCoefficients D S C z)) q| ≤
          A * (1 + pairGrading (stateGrading S) realGrading (s + loss)
            (z - (C.referenceState, 0)))

private theorem originalCoefficientStrip_bound_of_localized
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base loss s : ℕ} {ε l u ρ A : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (h : LocalizedOriginalCoefficientBoundAtOrder D S C base loss ε hlu hρ s A) :
    N01OriginalCoefficientStripBoundAtOrder D S C base loss ε l u s A := by
  intro z hz hs i a b hab q hq
  have he := mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ)
    (localizedOriginalCoefficient_eqOn D S C hlu hρ z i) a b hq
  exact (congrArg abs he).symm.trans_le (h z hz hs i a b hab q hq)

/-- The actual coefficient estimate has the original N01 neighborhood
and derivative loss. The cell and fixed strip only affect the numerical
constant, which precedes the state, angle, and derivative split. -/
theorem n01_originalCoefficient_strip_fixed_loss_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {l u ρ : ℝ} (hlu : l ≤ u) (hρ : 0 < ρ)
    (hphysical : Ioo (l - ρ) (u + ρ) ⊆ Ioo D.a D.b)
    (m : ℕ) (hcell : Ioo l u ⊆ D.cells m) (s : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
      N01OriginalCoefficientStripBoundAtOrder D S C base loss ε l u s A := by
  obtain ⟨A, hA, hbound⟩ := localizedOriginalCoefficient_fixed_loss_bound_of_n01
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hS hT hN hlu hρ hphysical m hcell s
  exact ⟨A, hA, originalCoefficientStrip_bound_of_localized hlu hρ hbound⟩

end ContinuousFlexibility.Analysis
