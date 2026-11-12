import ContinuousFlexibility.Analysis.N01cComponentCosineSpeed

/-!
# The actual cosine speed at every real time

The signed extension is expressed through the actual ordinary minus
speed and its actual normalized drift. The absolute sine keeps the
identity valid on both halves of every period. At a sine zero all terms
vanish, without evaluating an interior identity at a boundary point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem rootCosinePath_mem_Ioo_of_sin_ne_zero {l h t : ℝ}
    (hlh : l < h) (hs : Real.sin t ≠ 0) :
    rootCosinePath l h t ∈ Ioo l h := by
  have hc : 0 < (h - l) / 2 := div_pos (sub_pos.mpr hlh) (by norm_num)
  have hp : 0 < (rootCosinePath l h t - l) * (h - rootCosinePath l h t) := by
    rw [rootCosinePath_rootFactors]
    exact mul_pos (sq_pos_of_pos hc) (sq_pos_of_ne_zero hs)
  rcases mul_pos_iff.mp hp with hp | hp
  · exact ⟨sub_pos.mp hp.1, sub_pos.mp hp.2⟩
  · exact False.elim ((not_lt_of_ge
      (sub_nonneg.mpr (rootCosinePath_mem_Icc hlh.le t).1)) hp.1)

/-- The scalar root identity uses the absolute sine on the whole line. -/
theorem sqrt_comp_rootCosinePath_abs
    {f : ℝ → ℝ} {l h : ℝ} (hlh : l < h)
    (hl : f l = 0) (hh : f h = 0) (t : ℝ) :
    Real.sqrt (f (rootCosinePath l h t)) =
      (h - l) / 2 * |Real.sin t| *
        Real.sqrt (twoRootDivided f l h (rootCosinePath l h t)) := by
  have hc : 0 < (h - l) / 2 := div_pos (sub_pos.mpr hlh) (by norm_num)
  have he := twoRootDivided_mul_rootFactors hlh hl hh (rootCosinePath l h t)
  rw [rootCosinePath_rootFactors] at he
  have hf : f (rootCosinePath l h t) =
      ((h - l) / 2 * Real.sin t) ^ 2 *
        twoRootDivided f l h (rootCosinePath l h t) := by
    rw [← he]
    ring
  rw [hf, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_mul,
    abs_of_nonneg hc.le]

/-- A purely scalar identity isolates the sign correction in the drift. -/
theorem cosineRegularizedSpeed_eq_signed
    {E : Type*} {l h : ℝ} (hlh : l < h)
    (A B : E × (ℝ × ℝ) → ℝ) (Q : E × ℝ → ℝ)
    {x : E} (hl : Q (x, l) = 0) (hh : Q (x, h) = 0) (t θ : ℝ) :
    cosineRegularizedSpeed l h A B
        (fun p => twoRootDivided (fun r => Q (p.1, r)) l h p.2) (x, (t, θ)) =
      ((h - l) / 2 * |Real.sin t|) *
        (-A (x, (rootCosinePath l h t, θ)) -
          B (x, (rootCosinePath l h t, θ)) * Real.sqrt (Q (x, rootCosinePath l h t))) +
      ((h - l) / 2 * (|Real.sin t| - Real.sin t)) *
        A (x, (rootCosinePath l h t, θ)) := by
  rw [sqrt_comp_rootCosinePath_abs (f := fun r => Q (x, r)) hlh hl hh t]
  dsimp only [cosineRegularizedSpeed]
  rw [← sq_abs (Real.sin t)]
  ring

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- The same actual ordinary speed supplies every real-time state jet of
the signed cosine extension, with an explicit actual drift correction. -/
theorem componentCosineSpeed_eq_signed
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ) (t θ : ℝ) :
    componentCosineSpeed D S C m (z, (t, θ)) =
      ((C.right m - C.left m) / 2 * |Real.sin t|) *
        minusCharacteristicSpeed (originalCoefficients D S C z)
          (rootCosinePath (C.left m) (C.right m) t, θ) +
      ((C.right m - C.left m) / 2 * (|Real.sin t| - Real.sin t)) *
        normalizedSpeedFactor D S C 0 z
          (rootCosinePath (C.left m) (C.right m) t, θ) := by
  by_cases hs : Real.sin t = 0
  · simp only [componentCosineSpeed, cosineRegularizedSpeed, hs, abs_zero,
      sq, mul_zero, zero_mul, neg_zero, sub_zero, add_zero]
  · have hC := hA.2.2.1
    have hr := rootCosinePath_mem_Ioo_of_sin_ne_zero (hC.1 m).2.1 hs
    have hcore : (rootCosinePath (C.left m) (C.right m) t, θ) ∈ annularOpen D :=
      ⟨⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩, mem_univ _⟩
    rw [minusCharacteristicSpeed_normalized_factors hS hT hA hB hz hcore]
    have he := cosineRegularizedSpeed_eq_signed (hC.1 m).2.1
      (fun q : (AnnularState S × ℝ) × PolarPoint => normalizedSpeedFactor D S C 0 q.1 q.2)
      (fun q : (AnnularState S × ℝ) × PolarPoint => normalizedSpeedFactor D S C 1 q.1 q.2)
      (fun q : (AnnularState S × ℝ) × ℝ => componentOpticalSquare D S C m q.1 q.2)
      (componentOpticalSquare_boundary_zero hA m z (Or.inl rfl))
      (componentOpticalSquare_boundary_zero hA m z (Or.inr rfl)) t θ
    simpa only [componentCosineSpeed, componentOpticalSquare_eq_actual hA m z hr] using he

end ContinuousFlexibility.Statements
