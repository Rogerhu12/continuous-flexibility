import ContinuousFlexibility.Analysis.N05ReferenceEndpointWeights

/-!
# The actual endpoint weight in reference cell coordinates

The error in the cubic endpoint exponent is absorbed by one material
envelope, in both directions. The exponent is arbitrary and the material
loss does not grow with it; only the multiplicative constant changes.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

/-- On every actual reference cell, replacing the prescribed material
endpoint weight by the discrete cubic exponential costs one power of `M`.
The two inequalities are proved from the same logarithmic estimate. -/
theorem n05_materialH_reference_exponential_comparison
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (γ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m r, r ∈ D.cells m →
      T.H r ^ γ ≤ K * T.M r * Real.exp (-γ * radialS (D.cellIndex m)) ∧
      Real.exp (-γ * radialS (D.cellIndex m)) ≤ K * T.M r * T.H r ^ γ := by
  obtain ⟨C, hC, hlog⟩ := n05_material_reference_logH_bound hD hT
  let A : ℝ := |γ| * C
  have hA : 0 ≤ A := mul_nonneg (abs_nonneg _) hC.le
  obtain ⟨B, hB, hcoef⟩ := referenceCellCoefficient_le_materialM hD hT hA
  obtain ⟨bounds, hbounds⟩ := hD
  refine ⟨B * Real.exp A, mul_pos hB (Real.exp_pos _), fun m r hrm => ?_⟩
  have hr : r ∈ Ioo D.a D.b := hbounds.2.1.2.2.2.1 m hrm
  have hH : 0 < T.H r := (hT.2.1 r hr).2.1
  have hscaled : |γ * (Real.log (T.H r) + radialS (D.cellIndex m))| ≤
      A * (radialQ (D.cellIndex m) + 1) := by
    rw [abs_mul]
    simpa only [A, mul_assoc] using
      mul_le_mul_of_nonneg_left (hlog m r hrm) (abs_nonneg γ)
  have hupper : γ * Real.log (T.H r) ≤
      A * (radialQ (D.cellIndex m) + 1) - γ * radialS (D.cellIndex m) := by
    linarith only [(abs_le.mp hscaled).2]
  have hlower : -γ * radialS (D.cellIndex m) ≤
      A * (radialQ (D.cellIndex m) + 1) + γ * Real.log (T.H r) := by
    linarith only [(abs_le.mp hscaled).1]
  have hpow : T.H r ^ γ = Real.exp (γ * Real.log (T.H r)) := by
    rw [Real.rpow_def_of_pos hH]
    congr 1
    ring
  have hfactor : Real.exp (A * (radialQ (D.cellIndex m) + 1)) =
      Real.exp A * radialE (D.cellIndex m) ^ A := by
    simp only [radialE, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  constructor
  · calc
      T.H r ^ γ = Real.exp (γ * Real.log (T.H r)) := hpow
      _ ≤ Real.exp (A * (radialQ (D.cellIndex m) + 1) -
          γ * radialS (D.cellIndex m)) := Real.exp_le_exp.mpr hupper
      _ = (Real.exp A * radialE (D.cellIndex m) ^ A) *
          Real.exp (-γ * radialS (D.cellIndex m)) := by
        rw [sub_eq_add_neg, Real.exp_add, hfactor]
        congr 2
        ring
      _ ≤ (Real.exp A * (B * T.M r)) *
          Real.exp (-γ * radialS (D.cellIndex m)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hcoef m r hrm) (Real.exp_pos _).le)
          (Real.exp_pos _).le
      _ = (B * Real.exp A) * T.M r *
          Real.exp (-γ * radialS (D.cellIndex m)) := by ring
  · calc
      Real.exp (-γ * radialS (D.cellIndex m)) ≤
          Real.exp (A * (radialQ (D.cellIndex m) + 1) +
            γ * Real.log (T.H r)) := Real.exp_le_exp.mpr hlower
      _ = (Real.exp A * radialE (D.cellIndex m) ^ A) * T.H r ^ γ := by
        rw [Real.exp_add, hfactor, hpow]
      _ ≤ (Real.exp A * (B * T.M r)) * T.H r ^ γ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hcoef m r hrm) (Real.exp_pos _).le)
          (Real.rpow_pos_of_pos hH γ).le
      _ = (B * Real.exp A) * T.M r * T.H r ^ γ := by ring

end ContinuousFlexibility.Statements
