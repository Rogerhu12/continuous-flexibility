module

public import ContinuousFlexibility.Analysis.N01LocalizedCoefficientBounds
public import ContinuousFlexibility.Analysis.RootShiftMixedJets

/-!
# Actual N01 coefficient jets in either oriented root coordinate

The radial coordinate change has slope +1 or −1, so it preserves the
absolute values of every mixed jet. The fixed physical localization
therefore gives one coefficient sequence before the state, retaining
the original N01 loss without any new composition estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem contDiffOn_shiftedOriginalCoefficient_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {r σ R : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hphysical : Ioo (r - R) (r + R) ⊆ Ioo D.a D.b)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (i : Fin 3) :
    ContDiffOn ℝ ∞
      (fun q => canonicalCoefficientComponent i (originalCoefficients D S C z)
        (rootProfileShift r σ q)) (Ioo (-R) R ×ˢ (univ : Set ℝ)) := by
  have hshift : ContDiff ℝ ∞ (rootProfileShift r σ) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  intro q hq
  have hqphysical : rootProfileShift r σ q ∈ annularOpen D :=
    ⟨hphysical (rootProfileShift_mem_symmetric_interval hσ hq.1), mem_univ _⟩
  have hc := (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hsector i).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hqphysical)
  exact (hc.comp q hshift.contDiffAt).contDiffWithinAt

theorem shiftedOriginalCoefficient_fixed_loss_bound_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {r σ R : ℝ} (hσ : σ = 1 ∨ σ = -1) (hR : 0 < R)
    (hphysical : Ioo ((r - R) - R) ((r + R) + R) ⊆ Ioo D.a D.b)
    (m : ℕ) (hcell : Ioo (r - R) (r + R) ⊆ D.cells m) :
    ∃ A : ℕ → ℝ, (∀ s, 1 ≤ A s) ∧
      ∀ s : ℕ, ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
        |mixedDerivative a b
          (fun y => canonicalCoefficientComponent i (originalCoefficients D S C z)
            (rootProfileShift r σ y)) q| ≤
          A s * (1 + pairGrading (stateGrading S) realGrading (s + loss)
            (z - (C.referenceState, 0))) := by
  have hlu : r - R ≤ r + R := by linarith
  choose A hA hbound using
    (fun n => localizedOriginalCoefficient_fixed_loss_bound_of_n01
      hS hT hN hlu hR hphysical m hcell n)
  refine ⟨A, hA, ?_⟩
  intro s z hz hsector i a b hab q hq
  have hqphysical : rootProfileShift r σ q ∈
      Ioo (r - R) (r + R) ×ˢ (univ : Set ℝ) :=
    ⟨rootProfileShift_mem_symmetric_interval hσ hq.1, mem_univ _⟩
  have hjet := mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ)
    (localizedOriginalCoefficient_eqOn D S C hlu hR z i) a b hqphysical
  calc
    _ = |mixedDerivative a b (canonicalCoefficientComponent i (originalCoefficients D S C z))
        (rootProfileShift r σ q)| :=
      abs_mixedDerivative_rootProfileShift _ hσ a b q
    _ = |mixedDerivative a b (localizedOriginalCoefficient D S C hlu hR z i)
        (rootProfileShift r σ q)| := (congrArg abs hjet).symm
    _ ≤ _ := hbound s z hz hsector i a b hab (rootProfileShift r σ q) hqphysical

end ContinuousFlexibility.Analysis
