import ContinuousFlexibility.Radial.ReferenceModerateCoefficients
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The actual optical radicand has a cell coefficient-power Lipschitz bound

The actual identity `F = -w' * r⁻¹ * w⁻¹` and the product rule express
`F'` using the already controlled physical coefficient generators. The
mean-value estimate first uses the open cell inclusion supplied by return
margins, then continuity extends the same constant to both endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped Topology ContDiff
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

/-- Both the actual optical radicand and its actual derivative have fixed
coefficient powers on the original reference cells. -/
theorem n05_referenceModerate_opticalRadicand {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ReferenceModerate D (fun r => -deriv D.w r / (r * D.w r)) ∧
      ReferenceModerate D (deriv (fun r => -deriv D.w r / (r * D.w r))) := by
  let F : ℝ → ℝ := fun r => -deriv D.w r / (r * D.w r)
  have hw : ContDiff ℝ ∞ D.w := hD.choose_spec.1.2.2.1.1
  have hu : ReferenceModerate D (deriv D.w) := by
    simpa only [iteratedDeriv_one] using referenceModerate_smooth_jet hD hw 1
  have hu' : ReferenceModerate D (deriv (deriv D.w)) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      referenceModerate_smooth_jet hD hw 2
  have hv : ReferenceModerate D (fun r : ℝ => r⁻¹) := by
    simpa only [iteratedDeriv_zero] using referenceModerate_reciprocal_radius_jet hD 0
  have hv' : ReferenceModerate D (deriv (fun r : ℝ => r⁻¹)) := by
    simpa only [iteratedDeriv_one] using referenceModerate_reciprocal_radius_jet hD 1
  have hz : ReferenceModerate D (fun r => (D.w r)⁻¹) := by
    simpa only [iteratedDeriv_zero] using referenceModerate_reciprocal_profile_jet hD 0
  have hz' : ReferenceModerate D (deriv (fun r => (D.w r)⁻¹)) := by
    simpa only [iteratedDeriv_one] using referenceModerate_reciprocal_profile_jet hD 1
  have heq : F = fun r => -(deriv D.w r * r⁻¹ * (D.w r)⁻¹) := by
    funext r
    dsimp only [F]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hF : ReferenceModerate D F := by
    rw [heq]
    simpa only [neg_one_mul] using
      (ReferenceModerate.const D (-1)).mul ((hu.mul hv).mul hz)
  let G : ℝ → ℝ := fun r =>
    -((deriv (deriv D.w) r * r⁻¹ + deriv D.w r * deriv (fun t : ℝ => t⁻¹) r) *
      (D.w r)⁻¹ + (deriv D.w r * r⁻¹) * deriv (fun t => (D.w t)⁻¹) r)
  have hG : ReferenceModerate D G := by
    have hfirst := ((hu'.mul hv).add (hu.mul hv')).mul hz
    have hsecond := (hu.mul hv).mul hz'
    simpa only [G, neg_one_mul] using
      (ReferenceModerate.const D (-1)).mul (hfirst.add hsecond)
  have hderiv (r : ℝ) (hr : r ∈ radialCore D) : deriv F r = G r := by
    have du := ((hu.1.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
    have dv := ((hv.1.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
    have dz := ((hz.1.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
    rw [heq]
    exact ((du.mul dv).mul dz).neg.deriv
  refine ⟨hF, ?_⟩
  obtain ⟨B, A, hB, hbound⟩ := hG.2
  refine ⟨((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hF.1).2,
    B, A, hB, fun m r hr => ?_⟩
  rw [hderiv r (hD.choose_spec.2.1.2.2.2.1 m hr)]
  exact hbound m r hr

/-- An actual interval carried by a reference cell has a Lipschitz
constant bounded by one fixed coefficient power. Its endpoints need only
belong to the physical core, not to the possibly nonclosed cell. -/
theorem n05_opticalRadicand_cell_lipschitz {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ (m : ℕ) (l b : ℝ),
      l < b → Ioo l b ⊆ D.cells m → Icc l b ⊆ radialCore D →
      ∃ P : ℝ≥0, 1 ≤ (P : ℝ) ∧
        (P : ℝ) = C * radialE (D.cellIndex m) ^ A ∧
        LipschitzOnWith P (fun r => -deriv D.w r / (r * D.w r)) (Icc l b) := by
  let F : ℝ → ℝ := fun r => -deriv D.w r / (r * D.w r)
  obtain ⟨hF, hder⟩ := n05_referenceModerate_opticalRadicand hD
  obtain ⟨B, A₀, hB, hbound⟩ := hder.2
  let C : ℝ := B + 1
  let A : ℝ := |A₀| + 1
  have hC : 0 < C := by dsimp only [C]; linarith only [hB]
  have hC1 : 1 ≤ C := by dsimp only [C]; linarith only [hB]
  have hA : 0 < A := by dsimp only [A]; positivity
  have hA₀ : A₀ ≤ A := by dsimp only [A]; linarith only [le_abs_self A₀]
  refine ⟨C, A, hC, hA, fun m l b hlb hcell hcore => ?_⟩
  let P : ℝ≥0 := ⟨C * Real.exp (A * radialQ (D.cellIndex m)),
    mul_nonneg hC.le (Real.exp_pos _).le⟩
  have hQ := radialQ_nonneg (D.cellIndex m)
  have hP : 1 ≤ (P : ℝ) := by
    have he := mul_le_mul hC1 (Real.one_le_exp (mul_nonneg hA.le hQ)) zero_le_one hC.le
    simpa only [one_mul] using he
  refine ⟨P, hP, ?_, ?_⟩
  · change C * Real.exp (A * radialQ (D.cellIndex m)) =
      C * radialE (D.cellIndex m) ^ A
    rw [radialE, ← Real.exp_mul]
    congr 1
    congr 1
    ring
  · have hpoint (r : ℝ) (hr : r ∈ Ioo l b) : |deriv F r| ≤ (P : ℝ) := by
      calc
        _ ≤ B * Real.exp (A₀ * radialQ (D.cellIndex m)) := hbound m r (hcell hr)
        _ ≤ C * Real.exp (A * radialQ (D.cellIndex m)) :=
          mul_le_mul (by dsimp only [C]; linarith)
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA₀ hQ))
            (Real.exp_pos _).le hC.le
        _ = _ := rfl
    have hLip : LipschitzOnWith P F (Ioo l b) := by
      apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
        (fun r hr => (hF.1.contDiffAt (isOpen_Ioo.mem_nhds
          (hcore (Ioo_subset_Icc_self hr)))).differentiableAt (by simp))
        _ (convex_Ioo l b)
      intro r hr
      change ‖deriv F r‖ ≤ (P : ℝ)
      simpa only [Real.norm_eq_abs] using hpoint r hr
    have hcont : ContinuousOn F (closure (Ioo l b)) := by
      rw [closure_Ioo hlb.ne]
      exact hF.1.continuousOn.mono hcore
    simpa only [closure_Ioo hlb.ne] using LipschitzOnWith.closure hcont hLip

end ContinuousFlexibility.Statements
