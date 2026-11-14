module

public import ContinuousFlexibility.Analysis.N01cComponentSpeedPeriodicity
public import ContinuousFlexibility.Blueprint.N01c.Statements

/-!
# Actual angular jets under the cosine change of variable

The physical angular coordinate is unchanged. All angular derivatives of
the reference-subtracted speed acquire exactly one cosine velocity factor.
The reference speed has no angular dependence, so the same identity gives
every positive angular derivative needed for the flow's low geometry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint

theorem componentCosineSpeed_reference_angle
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (m : ℕ) (t θ : ℝ) :
    componentCosineSpeed D S C m ((C.referenceState, 0), (t, θ)) =
      componentCosineSpeed D S C m ((C.referenceState, 0), (t, 0)) := by
  have hC := hA.2.2.1
  have hr := rootCosinePath_mem_Icc (hC.1 m).2.1.le t
  have hq (η : ℝ) : (rootCosinePath (C.left m) (C.right m) t, η) ∈ annularOpen D :=
    ⟨⟨(hC.1 m).1.trans_le hr.1, hr.2.trans_lt (hC.1 m).2.2⟩, mem_univ _⟩
  obtain ⟨haθ, hbθ⟩ := normalizedSpeedFactor_reference hS hT hA hε hB (hq θ)
  obtain ⟨ha0, hb0⟩ := normalizedSpeedFactor_reference hS hT hA hε hB (hq 0)
  simp only [componentCosineSpeed, cosineRegularizedSpeed, haθ, hbθ, ha0, hb0]

theorem iteratedDeriv_componentCosineSpeed_difference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) Real.pi) (θ : ℝ) :
    iteratedDeriv n (fun η => componentCosineSpeed D S C m (z, (t, η)) -
      componentCosineSpeed D S C m ((C.referenceState, 0), (t, η))) θ =
      ((C.right m - C.left m) / 2 * Real.sin t) *
        characteristicSpeedFamily D S C 0 n
          (rootCosinePath (C.left m) (C.right m) t, θ) z := by
  have href := reference_mem_stateNeighborhood S C base hε
  have he : (fun η => componentCosineSpeed D S C m (z, (t, η)) -
      componentCosineSpeed D S C m ((C.referenceState, 0), (t, η))) =
      fun η => ((C.right m - C.left m) / 2 * Real.sin t) *
        (minusCharacteristicSpeed (originalCoefficients D S C z)
          (rootCosinePath (C.left m) (C.right m) t, η) -
          minusCharacteristicSpeed (originalCoefficients D S C (C.referenceState, 0))
            (rootCosinePath (C.left m) (C.right m) t, η)) := by
    funext η
    rw [componentCosineSpeed_eq_transformed hS hT hA hB hz m ht,
      componentCosineSpeed_eq_transformed hS hT hA hB href m ht]
    ring
  rw [he, iteratedDeriv_const_mul_field]
  rfl

theorem iteratedDeriv_componentCosineSpeed_positive
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m n : ℕ) (hn : 0 < n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) Real.pi) (θ : ℝ) :
    iteratedDeriv n (fun η => componentCosineSpeed D S C m (z, (t, η))) θ =
      ((C.right m - C.left m) / 2 * Real.sin t) *
        characteristicSpeedFamily D S C 0 n
          (rootCosinePath (C.left m) (C.right m) t, θ) z := by
  have he : (fun η => componentCosineSpeed D S C m (z, (t, η))) =
      fun η => componentCosineSpeed D S C m ((C.referenceState, 0), (t, 0)) +
        (componentCosineSpeed D S C m (z, (t, η)) -
          componentCosineSpeed D S C m ((C.referenceState, 0), (t, η))) := by
    funext η
    rw [componentCosineSpeed_reference_angle hS hT hA hε hB m t η]
    ring
  rw [he, iteratedDeriv_const_add hn]
  exact iteratedDeriv_componentCosineSpeed_difference hS hT hA hε hB hz m n ht θ

theorem iteratedDeriv_componentCosineSpeed_zero_of_sin_zero
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (z : AnnularState S × ℝ) (m n : ℕ) {t : ℝ} (ht : Real.sin t = 0) (θ : ℝ) :
    iteratedDeriv n (fun η => componentCosineSpeed D S C m (z, (t, η))) θ = 0 := by
  have he : (fun η => componentCosineSpeed D S C m (z, (t, η))) = (0 : ℝ → ℝ) := by
    funext η
    simp only [componentCosineSpeed, cosineRegularizedSpeed, ht, mul_zero,
      neg_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, Pi.zero_apply]
  rw [he, iteratedDeriv_const_zero]

end ContinuousFlexibility.Statements
