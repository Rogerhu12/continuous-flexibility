module

public import ContinuousFlexibility.Analysis.N06LeftColumnJets
public import ContinuousFlexibility.Analysis.N06CompactCoefficientDifference

/-!
# Linear smallness of the genuine left-column difference

The physical cutoff is the original S.chiLeft. Its derivative has one
fixed compact support. The exact flux-jet formula and the proved N01
coefficient estimate give a bound for every angular derivative through
a fixed order. No current chart or final operator bound is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

private theorem n06_cutoff_weight_bounded {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) {J : Set ℝ} (hJ : IsCompact J) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ J,
      |deriv (deriv χ) r| + 2 * |deriv χ r| ≤ M := by
  have hχ' : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hχ'' : ContDiff ℝ ∞ (deriv (deriv χ)) :=
    (contDiff_infty_iff_deriv.mp hχ').2
  have hc : Continuous (fun r => |deriv (deriv χ) r| + 2 * |deriv χ r|) :=
    hχ''.continuous.abs.add (continuous_const.mul hχ'.continuous.abs)
  obtain ⟨M, hM⟩ := hJ.bddAbove_image hc.continuousOn
  exact ⟨|M|, abs_nonneg M,
    fun r hr => (hM ⟨r, hr, rfl⟩).trans (le_abs_self M)⟩

private theorem n06_cutoff_three_term_bound {a₀ a₁ b₁ c₁ c₂ δ M : ℝ}
    (hδ : 0 ≤ δ) (h₀ : |a₀| ≤ δ) (h₁ : |a₁| ≤ δ) (h₂ : |b₁| ≤ δ)
    (hM : |c₂| + 2 * |c₁| ≤ M) :
    |c₂ * a₀ + c₁ * a₁ + c₁ * b₁| ≤ M * δ := by
  calc
    _ ≤ |c₂ * a₀| + |c₁ * a₁| + |c₁ * b₁| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |c₂| * |a₀| + |c₁| * |a₁| + |c₁| * |b₁| := by
      rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |c₂| * δ + |c₁| * δ + |c₁| * δ :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left h₀ (abs_nonneg c₂))
        (mul_le_mul_of_nonneg_left h₁ (abs_nonneg c₁)))
        (mul_le_mul_of_nonneg_left h₂ (abs_nonneg c₁))
    _ = (|c₂| + 2 * |c₁|) * δ := by ring
    _ ≤ M * δ := mul_le_mul_of_nonneg_right hM hδ

private theorem n06_compact_cutoff_family_bound
    {Z : Type*} (J : Set ℝ) (U : Set PolarPoint) (χ : ℝ → ℝ) (b : ℕ)
    (family : Fin 3 → ℕ → ℕ → PolarPoint → Z → ℝ)
    (field : Z → PolarPoint → ℝ) (size : Z → ℝ) (Ad₁ Ad₂ Ad₃ : Z → Prop)
    (hsize : ∀ z, 0 ≤ size z)
    (hweight : ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ J,
      |deriv (deriv χ) r| + 2 * |deriv χ r| ≤ M)
    (hcoeff : ∃ B : ℝ, 0 ≤ B ∧ ∀ i a k (p : PolarPoint),
      a + k ≤ b + 1 → p.1 ∈ J → ∀ z, Ad₁ z → Ad₃ z →
        |family i a k p z| ≤ B * size z)
    (hformula : ∀ z, Ad₁ z → Ad₂ z → ∀ j, j ≤ b → ∀ p ∈ U,
      mixedDerivative 0 j (field z) p =
        deriv (deriv χ) p.1 * family 0 0 j p z +
          deriv χ p.1 * family 0 1 j p z +
          deriv χ p.1 * family 1 0 (j + 1) p z)
    (hzero : ∀ z, ∀ r, r ∉ J → ∀ θ, field z (r, θ) = 0) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z, Ad₁ z → Ad₂ z → Ad₃ z →
      ∀ j, j ≤ b → ∀ p ∈ U, |mixedDerivative 0 j (field z) p| ≤ Q * size z := by
  obtain ⟨M, hM, hw⟩ := hweight
  obtain ⟨B, hB, hc⟩ := hcoeff
  refine ⟨M * B, mul_nonneg hM hB, ?_⟩
  intro z hz₁ hz₂ hz₃ j hj p hp
  by_cases hpJ : p.1 ∈ J
  · have h₀ := hc 0 0 j p (by omega) hpJ z hz₁ hz₃
    have h₁ := hc 0 1 j p (by omega) hpJ z hz₁ hz₃
    have h₂ := hc 1 0 (j + 1) p (by omega) hpJ z hz₁ hz₃
    exact (congrArg abs (hformula z hz₁ hz₂ j hj p hp)).trans_le
      ((n06_cutoff_three_term_bound (mul_nonneg hB (hsize z))
        h₀ h₁ h₂ (hw p.1 hpJ)).trans_eq (mul_assoc M B (size z)).symm)
  · have he : (fun θ => field z (p.1, θ)) = (fun _ : ℝ => 0) :=
      funext (hzero z p.1 hpJ)
    have hjzero : |mixedDerivative 0 j (field z) p| = 0 := by
      change |iteratedDeriv j (fun θ => field z (p.1, θ)) p.2| = 0
      exact (congrArg (fun f : ℝ → ℝ => |iteratedDeriv j f p.2|) he).trans
        (by simp only [iteratedDeriv_fun_const_zero, abs_zero])
    exact hjzero.trans_le (mul_nonneg (mul_nonneg hM hB) (hsize z))

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

theorem n06_leftColumnDifference_zero_off_cutoff
    (hS : IsPhysicalSpaces D T S) (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ r, r ∉ J → deriv S.chiLeft r = 0)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hp : p.1 ∉ J) :
    n06LeftColumnDifference D S L z p = 0 := by
  have hz : n06CurrentLeftColumn S L z p = 0 :=
    n06_divergence_radial_cutoff_zero (L.coefficients z) hS.2.2.1.1 hJ hzero hp
  have hr : n06CurrentLeftColumn S L (C.referenceState, 0) p = 0 :=
    n06_divergence_radial_cutoff_zero (L.coefficients (C.referenceState, 0))
      hS.2.2.1.1 hJ hzero hp
  have href : n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft) p = 0 :=
    (n06_currentLeftColumn_reference hS h01 h03 p).symm.trans hr
  exact (congrArg₂ (fun a b : ℝ => a - b) hz href).trans (sub_self 0)

def N06LeftColumnAngularDifferenceBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (base loss : ℕ) (ε : ℝ) (b : ℕ) (Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
    z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S base (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ j, j ≤ b → ∀ p ∈ annularOpen D,
      |mixedDerivative 0 j (n06LeftColumnDifference D S L z) p| ≤
        Q * (stateGrading S (max base (b + 1 + loss)) (z.1 - C.referenceState) + |z.2|)

/-- Every requested physical angular jet is linearly small in the one
fixed original seminorm max base (b+1+loss). -/
theorem n06_leftColumnDifference_finiteAngular_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε) (b : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06LeftColumnAngularDifferenceBound D S C L base loss ε b Q := by
  obtain ⟨J, hJ, hJD, _hpos, hzero⟩ := hS.2.2.1.2.2
  exact n06_compact_cutoff_family_bound
    (Z := AnnularState S × ℝ) J (annularOpen D) S.chiLeft b
    (coefficientFamily D S C) (n06LeftColumnDifference D S L)
    (fun z => stateGrading S (max base (b + 1 + loss))
      (z.1 - C.referenceState) + |z.2|)
    (fun z => z ∈ stateNeighborhood S C base ε) (fun z => stateSector S z.1)
    (fun z => stateGrading S base (z.1 - C.referenceState) + |z.2| ≤ 1)
    (fun z => add_nonneg
      (apply_nonneg (stateGrading S (max base (b + 1 + loss))) (z.1 - C.referenceState))
      (abs_nonneg z.2))
    (n06_cutoff_weight_bounded hS.2.2.1.1 hJ)
    (n06_N01_compactCoefficientDifference_bound hT h01 hJ hJD (b + 1))
    (fun z hz hs j _hj p hp => n06_leftColumnDifference_angularJet hT hS h01 h03 hz hs j hp)
    (fun z r hr θ => n06_leftColumnDifference_zero_off_cutoff
      hS h01 h03 hJ.isClosed hzero z (p := (r, θ)) hr)

end ContinuousFlexibility.Statements
