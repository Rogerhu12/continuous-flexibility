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
  rw [matchedPhysicalCellBlock_eq, matchedPhysicalCellBlock_eq]
  apply ContinuousLinearMap.ext
  intro f
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
      apply ContinuousLinearMap.ext
      intro f
      simp only [ContinuousLinearMap.comp_apply, matchedModeScalarGate_sourceCell]
  | succ k =>
      exact congrArg norm (matchedPhysicalCellBlock_scalarGate D hD hP G active k m)

theorem matchedPhysicalRawKernel_scalarGate_false_zero (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D) (k : ℕ) :
    matchedPhysicalRawKernel D hD hP (G ∘L matchedModeScalarGate D false) k 0 = 0 := by
  have hgate : matchedModeScalarGate D false (0, 1) = 0 := by
    rfl
  have hzero : (G ∘L matchedModeScalarGate D false) (0, 1) = 0 := by
    rw [ContinuousLinearMap.comp_apply, hgate, map_zero]
  cases k with
  | zero =>
      change ‖((G ∘L matchedModeScalarGate D false) (0, 1)).2‖ = 0
      rw [hzero]
      exact norm_zero
  | succ k =>
      change ‖matchedPhysicalOutputCell D hD hP k
        ((G ∘L matchedModeScalarGate D false) (0, 1))‖ = 0
      rw [hzero, map_zero, norm_zero]

theorem matchedMode_scalarGate_apply_inverse (D : ReferenceData)
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (active : Bool) (F : RadialModePair D) (hF : active = false → F.2 = 0) :
    (G ∘L matchedModeScalarGate D active) F = G F := by
  rw [ContinuousLinearMap.comp_apply, matchedModeScalarGate_eq_self D active F hF]

/-- The actual inverse has no output scalar on an admissible nonbordered
input. This is the scalar clause of its genuine graph, not an estimate. -/
theorem matchedMode_inverse_scalar_zero {D : ReferenceData} {j : ℕ}
    {G : RadialModePair D →L[ℝ] RadialModePair D}
    (hG : ModeInverseProperties D j G) (hj : j ≠ 2)
    (F : RadialModePair D) (hF : F.2 = 0) :
    (G F).2 = 0 := by
  have hrow := (hG.1 F (fun _ => hF)).2
  simp only [if_neg hj] at hrow
  exact hrow.1

theorem matchedMode_inverse_scalarGate_false_zero {D : ReferenceData} {j : ℕ}
    {G : RadialModePair D →L[ℝ] RadialModePair D}
    (hG : ModeInverseProperties D j G) (hj : j ≠ 2)
    (F : RadialModePair D) :
    ((G ∘L matchedModeScalarGate D false) F).2 = 0 := by
  change (G (matchedModeScalarGate D false F)).2 = 0
  exact matchedMode_inverse_scalar_zero hG hj (matchedModeScalarGate D false F) rfl

/-- The whole scalar output row of the actual gated raw kernel vanishes
outside frequency two, including all physical source cells. -/
theorem matchedPhysicalRawKernel_scalarGate_false_row_zero {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) {j : ℕ}
    {G : RadialModePair D →L[ℝ] RadialModePair D}
    (hG : ModeInverseProperties D j G) (hj : j ≠ 2) (m : ℕ) :
    matchedPhysicalRawKernel D hD hP (G ∘L matchedModeScalarGate D false) 0 m = 0 := by
  cases m with
  | zero =>
      change ‖((G ∘L matchedModeScalarGate D false) (0, 1)).2‖ = 0
      rw [matchedMode_inverse_scalarGate_false_zero hG hj, norm_zero]
  | succ m =>
      change ‖(ContinuousLinearMap.snd ℝ (RadialModeL2 D) ℝ) ∘L
        (G ∘L matchedModeScalarGate D false) ∘L matchedPhysicalSourceCell D hD hP m‖ = 0
      have he : (ContinuousLinearMap.snd ℝ (RadialModeL2 D) ℝ) ∘L
          (G ∘L matchedModeScalarGate D false) ∘L matchedPhysicalSourceCell D hD hP m = 0 := by
        apply ContinuousLinearMap.ext
        intro f
        exact matchedMode_inverse_scalarGate_false_zero hG hj _
      rw [he, norm_zero]

end ContinuousFlexibility.Radial
