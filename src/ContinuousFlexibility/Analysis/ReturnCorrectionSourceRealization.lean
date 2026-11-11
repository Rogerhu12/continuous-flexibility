import ContinuousFlexibility.Analysis.ReturnOpticalCorrectionSource
import ContinuousFlexibility.Analysis.ReturnCorrectionSource

/-!
# Realization of the actual independent error in the physical source

The scalar differential error is already bilinear and has zero physical
source integral. Weighted height membership therefore lifts that same
field into the original source kernel. The realization is unique on the
common neighborhood and can be used by every later jet construction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

section SourceError

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
  (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
  (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
    χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
  (hdisc : ∀ z ∈ stateNeighborhood S C base ε, ∀ m p,
    p.1 ∈ tsupport (deriv (χ m)) →
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
  (hmember : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ ρ η,
    HeightMember D T (3 / 4 : ℝ) (returnCorrectionResidualErrorField D S C R χ z ρ η))

def returnCorrectionSourceError :
    AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source := by
  classical
  intro z
  exact if hz : z ∈ stateNeighborhood S C base ε ∧ stateSector S z.1 then
    liftPhysicalSourceBilinear hS
      (returnCorrectionResidualErrorBilinearOfCutoffs hN hS hT R hz.1 hz.2
        χ hχ hχrange hsupp hend (hdisc z hz.1))
      (fun ρ η => by
        rw [returnCorrectionResidualErrorBilinearOfCutoffs_apply]
        exact hmember z hz.1 hz.2 ρ η)
      (fun ρ η => by
        rw [returnCorrectionResidualErrorBilinearOfCutoffs_apply]
        exact hN.returnCorrectionResidualErrorField_sourceIntegral_of_cutoffs
          hS hT R hz.1 hz.2 χ hχ hχrange hsupp hend (hdisc z hz.1) ρ η)
    else 0

theorem returnCorrectionSourceError_decode
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (ρ : CircleSpace S) (η : HeightPair S) :
    physicalSourceDecode S
      (returnCorrectionSourceError hN hS hT R χ hχ hχrange hsupp hend hdisc hmember z ρ η) =
      returnCorrectionResidualErrorField D S C R χ z ρ η := by
  classical
  have hz' : z ∈ stateNeighborhood S C base ε ∧ stateSector S z.1 := ⟨hz, hs⟩
  simp only [returnCorrectionSourceError, dif_pos hz',
    liftPhysicalSourceBilinear_decode, returnCorrectionResidualErrorBilinearOfCutoffs_apply]

theorem returnCorrectionSourceError_eq_of_decode
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (ρ : CircleSpace S) (η : HeightPair S)
    (u : S.Source) (hu : physicalSourceDecode S u =
      returnCorrectionResidualErrorField D S C R χ z ρ η) :
    u = returnCorrectionSourceError hN hS hT R χ hχ hχrange hsupp hend hdisc hmember z ρ η := by
  apply physicalSourceDecode_injective hS
  exact hu.trans (returnCorrectionSourceError_decode hN hS hT R χ hχ hχrange
    hsupp hend hdisc hmember hz hs ρ η).symm

theorem returnCorrectionSourceError_grading_le_iff
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (ρ : CircleSpace S) (η : HeightPair S)
    (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    S.sourceGrading n
      (returnCorrectionSourceError hN hS hT R χ hχ hχrange hsupp hend hdisc hmember z ρ η) ≤ B ↔
      ∀ i ≤ n, physicalNorm T (3 / 4 : ℝ) i
        (returnCorrectionResidualErrorField D S C R χ z ρ η) ≤ B := by
  rw [sourceGrading_le_iff_physicalNorm hS n _ hB,
    returnCorrectionSourceError_decode hN hS hT R χ hχ hχrange hsupp hend hdisc hmember hz hs]

end SourceError

end ContinuousFlexibility.Statements
