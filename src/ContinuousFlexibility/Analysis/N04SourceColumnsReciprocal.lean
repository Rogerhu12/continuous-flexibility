import ContinuousFlexibility.Analysis.N04SourceColumnsScalarData
import ContinuousFlexibility.Analysis.AbsoluteReciprocalJetBounds

/-!
# Reciprocal current jets from a material lower bound

The true scalar derivative formula converts a bound for the reciprocal
value into every outer derivative envelope. Scalar composition then
produces the complete reference-difference tower on one neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

/-- An absolute reciprocal-value envelope controls all mixed scalar outer jets.
No upper bound or sign choice for the nonzero input is used. -/
theorem n04SourceColumns_inverse_abs_outer_envelope
    (C P : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P) (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ E t : ℝ, 1 ≤ E → t ≠ 0 → |t⁻¹| ≤ C * E ^ P →
      ∀ a b : ℕ, a + b ≤ N →
        ‖iteratedFDeriv ℝ a (iteratedDeriv b (fun u : ℝ => u⁻¹)) t‖ ≤ B * E ^ B := by
  have hpack := coefficientEnvelope_pack
    ((N.factorial : ℝ) * (1 + C) ^ (N + 1)) (P * (N + 1 : ℕ))
  refine ⟨hpack.choose, hpack.choose_spec.1, ?_⟩
  intro E t hE ht hinv a b hab
  let M : ℝ := (1 + C) * E ^ P
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le
    (le_add_of_nonneg_right hC) (Real.one_le_rpow hE hP)
  have hiabs : |t|⁻¹ ≤ C * E ^ P := by simpa only [abs_inv] using hinv
  have hiM : |t|⁻¹ ≤ M := hiabs.trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
      (Real.rpow_nonneg (zero_le_one.trans hE) P))
  have ht' : 0 < |t| := abs_pos.mpr ht
  have hformula := norm_iteratedFDeriv_one_div_le ht' (le_rfl : |t| ≤ |t|) (a + b)
  have hscalar : ‖iteratedFDeriv ℝ a (iteratedDeriv b (fun u : ℝ => u⁻¹)) t‖ ≤
      ((a + b).factorial : ℝ) * (|t|⁻¹) ^ (a + b + 1) := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      circle_iteratedDeriv_iteratedDeriv, one_div, absoluteReciprocalJetBound,
      inv_pow, Nat.add_comm] using hformula
  have hfact : ((a + b).factorial : ℝ) ≤ (N.factorial : ℝ) :=
    Nat.cast_le.mpr (Nat.factorial_le hab)
  have hpow : (|t|⁻¹) ^ (a + b + 1) ≤ M ^ (N + 1) :=
    (pow_le_pow_left₀ (inv_pos.mpr ht').le hiM _).trans
      (pow_le_pow_right₀ hM (Nat.add_le_add_right hab 1))
  have hmain : ‖iteratedFDeriv ℝ a (iteratedDeriv b (fun u : ℝ => u⁻¹)) t‖ ≤
      (N.factorial : ℝ) * M ^ (N + 1) := hscalar.trans
    (mul_le_mul hfact hpow (pow_nonneg (inv_pos.mpr ht').le _) (Nat.cast_nonneg _))
  have hMp : M ^ (N + 1) = (1 + C) ^ (N + 1) * E ^ (P * (N + 1 : ℕ)) := by
    dsimp only [M]
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE) P (N + 1)]
  exact hmain.trans (by
    simpa only [hMp, mul_assoc] using hpack.choose_spec.2 E hE)

/-- Positive-input specialization of the absolute reciprocal estimate. -/
theorem n04SourceColumns_inverse_outer_envelope
    (C P : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P) (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ E t : ℝ, 1 ≤ E → 0 < t → t⁻¹ ≤ C * E ^ P →
      ∀ a b : ℕ, a + b ≤ N →
        ‖iteratedFDeriv ℝ a (iteratedDeriv b (fun u : ℝ => u⁻¹)) t‖ ≤ B * E ^ B := by
  obtain ⟨B, hB, hb⟩ := n04SourceColumns_inverse_abs_outer_envelope C P hC hP N
  refine ⟨B, hB, fun E t hE ht hi a b hab => ?_⟩
  exact hb E t hE ht.ne' (by simpa only [abs_of_pos (inv_pos.mpr ht)] using hi)
    a b hab

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- Positivity and a uniform material bound on the reciprocal value are
the only current reciprocal inputs. Every reciprocal derivative is derived. -/
theorem CurrentJetDataOn.sourceColumns_inv_of_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {cell : ℕ → ℕ} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : HasInterpolation (parameterGrading S))
    (hf : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (h₀ : N04SourceReferenceData T cell f₀)
    (hi₀ : N04SourceReferenceData T cell (fun m q => (f₀ m q)⁻¹))
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (C P : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hbound : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m q, q ∈ unitStrip →
      0 < f z m q ∧ (f z m q)⁻¹ ≤ C * T.E0 (T.sample (cell m)) ^ P) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      CurrentJetDataOn S T cell (fun _ => True) base' ε'
        (fun z m q => (f z m q)⁻¹) (fun m q => (f₀ m q)⁻¹) := by
  have hg : ContDiffOn ℝ ∞ (fun t : ℝ => t⁻¹) (Ioi (0 : ℝ)) :=
    contDiffOn_id.inv (fun t ht => ht.ne')
  apply CurrentJetDataOn.sourceColumns_scalarComp hD hT hI hf h₀
    (fun t : ℝ => t⁻¹) (Ioi (0 : ℝ)) isOpen_Ioi hg hi₀ hε hE
    (fun z hz m q hq => (hbound z hz m q hq).1)
  intro N
  have ho := n04SourceColumns_inverse_outer_envelope C P hC hP N
  refine ⟨ho.choose, ho.choose_spec.1, ?_⟩
  intro m q hq z hz a b hab
  exact ho.choose_spec.2 (T.E0 (T.sample (cell m))) (f z m q) (hE m)
    (hbound z hz m q hq).1 (hbound z hz m q hq).2 a b hab

end ContinuousFlexibility.Analysis
