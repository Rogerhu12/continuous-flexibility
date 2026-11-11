import ContinuousFlexibility.Radial.MatchedPhysicalSchur

/-!
# The single active scalar border

For modes other than two, the scalar input is zero. Precomposition by
the corresponding scalar gate removes an arbitrary extension of the
modal inverse on inadmissible scalar inputs. It leaves every actual
physical cell block and every admissible solution unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

def matchedModeScalarGate (D : ReferenceData) (active : Bool) :
    RadialModePair D →L[ℝ] RadialModePair D :=
  (ContinuousLinearMap.fst ℝ (RadialModeL2 D) ℝ).prod
    (if active then ContinuousLinearMap.snd ℝ (RadialModeL2 D) ℝ else 0)

theorem matchedModeScalarGate_apply (D : ReferenceData) (active : Bool) (F : RadialModePair D) :
    matchedModeScalarGate D active F = (F.1, if active then F.2 else 0) := by
  cases active <;> rfl

theorem matchedModeScalarGate_eq_self (D : ReferenceData) (active : Bool)
    (F : RadialModePair D) (hF : active = false → F.2 = 0) :
    matchedModeScalarGate D active F = F := by
  rw [matchedModeScalarGate_apply]
  apply Prod.ext
  · rfl
  · cases active with
    | false => exact (hF rfl).symm
    | true => rfl

theorem matchedModeScalarGate_sourceCell (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (active : Bool) (m : ℕ) (f : MatchedPhysicalL2 D) :
    matchedModeScalarGate D active (matchedPhysicalSourceCell D hD hP m f) =
      matchedPhysicalSourceCell D hD hP m f := by
  apply matchedModeScalarGate_eq_self
  intro _
  rfl

theorem matchedPhysicalCellBlock_scalarGate (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (active : Bool) (k m : ℕ) :
    matchedPhysicalCellBlock D hD hP (G ∘L matchedModeScalarGate D active) k m =
      matchedPhysicalCellBlock D hD hP G k m := by
  ext f
  rw [matchedPhysicalCellBlock_eq, matchedPhysicalCellBlock_eq]
  simp only [ContinuousLinearMap.comp_apply, matchedModeScalarGate_sourceCell]

theorem matchedPhysicalRawKernel_scalarGate_succ (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (active : Bool) (k m : ℕ) :
    matchedPhysicalRawKernel D hD hP (G ∘L matchedModeScalarGate D active) k (m + 1) =
      matchedPhysicalRawKernel D hD hP G k (m + 1) := by
  cases k with
  | zero =>
      change ‖(ContinuousLinearMap.snd ℝ (RadialModeL2 D) ℝ) ∘L
          (G ∘L matchedModeScalarGate D active) ∘L matchedPhysicalSourceCell D hD hP m‖ =
        ‖(ContinuousLinearMap.snd ℝ (RadialModeL2 D) ℝ) ∘L
          G ∘L matchedPhysicalSourceCell D hD hP m‖
      congr 1
      ext f
      simp only [ContinuousLinearMap.comp_apply, matchedModeScalarGate_sourceCell]
  | succ k =>
      exact congrArg norm (matchedPhysicalCellBlock_scalarGate D hD hP G active k m)

theorem matchedPhysicalRawKernel_scalarGate_false_zero (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D) (k : ℕ) :
    matchedPhysicalRawKernel D hD hP (G ∘L matchedModeScalarGate D false) k 0 = 0 := by
  cases k <;>
    simp [matchedPhysicalRawKernel, ContinuousLinearMap.comp_apply,
      matchedModeScalarGate_apply]

theorem matchedMode_scalarGate_apply_inverse (D : ReferenceData)
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (active : Bool) (F : RadialModePair D) (hF : active = false → F.2 = 0) :
    (G ∘L matchedModeScalarGate D active) F = G F := by
  rw [ContinuousLinearMap.comp_apply, matchedModeScalarGate_eq_self D active F hF]

end ContinuousFlexibility.Radial
