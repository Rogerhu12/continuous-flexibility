module

public import ContinuousFlexibility.Analysis.InverseChartFieldJetBounds
public import ContinuousFlexibility.Analysis.PositiveChartJacobianJets
public import ContinuousFlexibility.Analysis.PointwiseJacobianReciprocalJets
public import ContinuousFlexibility.Analysis.PlanarInverseJacobianMaterialJets

/-!
# Actual inverse fields from physical coefficient, chart, and height jets

The inverse derivative tower and reciprocal Jacobian tower are derived
from the actual forward chart and a lower bound on its determinant.
The nine primitive fields then feed the existing transformed-field
polynomial estimate. All losses and low orders precede component
constants; no inverse or transformed-field jet estimate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem contDiffOn_coordinatePrimitiveJetField_of_fields
    {U : Set PolarPoint} (hU : IsOpen U)
    {C : SymmetricCoefficients} {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    (hC : ∀ i : Fin 3, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i C) U)
    (hF : ContDiffOn ℝ ∞ F U) (hh : ContDiffOn ℝ ∞ h U)
    (hJ : ∀ q ∈ U, planeJacobian F q ≠ 0) :
    ∀ i : Fin 9, ContDiffOn ℝ ∞ (coordinatePrimitiveJetField C F h i) U := by
  have hD (v : PolarPoint) : ContDiffOn ℝ ∞ (fun q => fderiv ℝ F q v) U := by
    intro q hq
    exact (((hF.contDiffAt (hU.mem_nhds hq)).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const).contDiffWithinAt
  have he (i : Fin 4) : ContDiffOn ℝ ∞ (coordinateChartDerivativeField F i) U := by
    fin_cases i
    · simpa [coordinateChartDerivativeField] using (hD (1, 0)).fst
    · simpa [coordinateChartDerivativeField] using (hD (0, 1)).fst
    · simpa [coordinateChartDerivativeField] using (hD (1, 0)).snd
    · simpa [coordinateChartDerivativeField] using (hD (0, 1)).snd
  have hR : ContDiffOn ℝ ∞ (fun q => |planeJacobian F q|⁻¹) U := by
    intro q hq
    have hs := (contDiffAt_absoluteReciprocal (hJ q hq)).comp q
      (contDiffAt_planeJacobian (hF.contDiffAt (hU.mem_nhds hq)))
    simpa only [Function.comp_def] using hs.contDiffWithinAt
  intro i
  fin_cases i
  · simpa [coordinatePrimitiveJetField, canonicalCoefficientComponent] using hC 0
  · simpa [coordinatePrimitiveJetField, canonicalCoefficientComponent] using hC 1
  · simpa [coordinatePrimitiveJetField, canonicalCoefficientComponent] using hC 2
  · simpa [coordinatePrimitiveJetField] using he 0
  · simpa [coordinatePrimitiveJetField] using he 1
  · simpa [coordinatePrimitiveJetField] using he 2
  · simpa [coordinatePrimitiveJetField] using he 3
  · simpa [coordinatePrimitiveJetField] using hh
  · simpa [coordinatePrimitiveJetField] using hR

private theorem physicalJetEnvelope_mono
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    {k l : ℕ} (hkl : k ≤ l) (z : E) :
    A * (1 + p k z) ≤ B * (1 + p l z) :=
  mul_le_mul hAB (add_le_add (le_refl (1 : ℝ)) (hp hkl z))
    (add_nonneg zero_le_one (apply_nonneg _ _)) (hA.trans hAB)

def InverseFieldsFromPhysicalJetsEstimate
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (low inputLoss outLoss : ℕ)
    (A : ℕ → ℝ) (κ : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z : E, p low z ≤ 1 →
    ∀ C : SymmetricCoefficients, ∀ F G : PolarPoint → PolarPoint,
    ∀ h : PolarPoint → ℝ, ∀ U : Set PolarPoint, IsOpen U →
      (∀ i : Fin 3, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i C) U) →
      ContDiffOn ℝ ∞ F U → ContDiffOn ℝ ∞ h U →
      (∀ q ∈ U, planeJacobian F q ≠ 0) →
    ∀ x : PolarPoint, G x ∈ U → ContDiffAt ℝ ∞ G x →
      F ∘ G =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint) →
      G ∘ F =ᶠ[𝓝 (G x)] (id : PolarPoint → PolarPoint) →
      κ ≤ |planeJacobian F (G x)| →
      (∀ i : Fin 3, PointwiseMaterialJetBound p inputLoss A z
        (canonicalCoefficientComponent i C) (G x)) →
      PointwiseMaterialJetBound p inputLoss A z h (G x) →
      (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n F (G x)‖ ≤
        A n * (1 + p (n + inputLoss) z)) →
    ∀ n : ℕ,
      ‖iteratedFDeriv ℝ n (inverseChartPotential C F G h) x‖ ≤
        B n * (1 + p (n + outLoss) z) ∧
      ∀ i : Fin 3, ‖iteratedFDeriv ℝ n
        (canonicalCoefficientComponent i (inverseChartPrincipalCoefficients C F G h)) x‖ ≤
          B n * (1 + p (n + outLoss) z)

theorem inverseFields_from_physicalJets_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∀ κ : ℝ, 0 < κ →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        InverseFieldsFromPhysicalJetsEstimate p low inputLoss outLoss A κ B := by
  obtain ⟨baseR, lossR, hreciprocal⟩ :=
    absolutePlaneJacobian_positiveJets_at_fixed_loss_bound hp hI inputLoss
  obtain ⟨baseI, lossI, hinverse⟩ :=
    planarInverse_positiveJets_of_jacobian_fixed_loss hp hI inputLoss
  let midLoss := max (inputLoss + 1) (max lossR lossI)
  have hlA : inputLoss ≤ midLoss := (Nat.le_succ inputLoss).trans (le_max_left _ _)
  have hlD : inputLoss + 1 ≤ midLoss := le_max_left _ _
  have hlR : lossR ≤ midLoss := (le_max_left _ _).trans (le_max_right _ _)
  have hlI : lossI ≤ midLoss := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨baseQ, lossQ, hphysical⟩ :=
    inverseChartFieldsOn_fixed_loss_material_bound hp hI midLoss
  refine ⟨max baseR (max baseI baseQ), lossQ, ?_⟩
  intro A hA κ hκ
  have hApos (n : ℕ) : 0 < A n := zero_lt_one.trans_le (hA n)
  obtain ⟨R, hR, hRbound⟩ := hreciprocal A hApos κ hκ
  obtain ⟨I, hIpos, hIbound⟩ := hinverse A hA κ hκ
  let M (n : ℕ) : ℝ := 1 + A n + A (n + 1) + R n + I n
  have hM (n : ℕ) : 1 ≤ M n := by
    dsimp only [M]
    linarith [hApos n, hApos (n + 1), hR n, hIpos n]
  have hAM (n : ℕ) : A n ≤ M n := by
    dsimp only [M]
    linarith [hApos (n + 1), hR n, hIpos n]
  have hDM (n : ℕ) : A (n + 1) ≤ M n := by
    dsimp only [M]
    linarith [hApos n, hR n, hIpos n]
  have hRM (n : ℕ) : R n ≤ M n := by
    dsimp only [M]
    linarith [hApos n, hApos (n + 1), hIpos n]
  have hIM (n : ℕ) : I n ≤ M n := by
    dsimp only [M]
    linarith [hApos n, hApos (n + 1), hR n]
  obtain ⟨B, hB, hbound⟩ := hphysical M hM
  refine ⟨B, hB, ?_⟩
  intro z hz C F G h U hU hC hF hh hJ x hx hG hFG hGF hκx hCjets hhjets hFjets
  have hzR : p baseR z ≤ 1 := (hp (le_max_left _ _) z).trans hz
  have hzI : p baseI z ≤ 1 :=
    (hp ((le_max_left _ _).trans (le_max_right _ _)) z).trans hz
  have hzQ : p baseQ z ≤ 1 :=
    (hp ((le_max_right _ _).trans (le_max_right _ _)) z).trans hz
  have hFx : ContDiffAt ℝ ∞ F (G x) := hF.contDiffAt (hU.mem_nhds hx)
  have hRjets := hRbound z hzR F (G x) hFx hκx hFjets
  have hIjets := hIbound z hzI F G x hFx hG hFG hGF hκx hFjets
  have hfields := contDiffOn_coordinatePrimitiveJetField_of_fields hU hC hF hh hJ
  have hcoef (i : Fin 3) (n : ℕ) :
      ‖iteratedFDeriv ℝ n (canonicalCoefficientComponent i C) (G x)‖ ≤
        M n * (1 + p (n + midLoss) z) :=
    (hCjets i n).trans (physicalJetEnvelope_mono hp (hApos n).le (hAM n)
      (Nat.add_le_add_left hlA n) z)
  have hheight (n : ℕ) : ‖iteratedFDeriv ℝ n h (G x)‖ ≤
      M n * (1 + p (n + midLoss) z) :=
    (hhjets n).trans (physicalJetEnvelope_mono hp (hApos n).le (hAM n)
      (Nat.add_le_add_left hlA n) z)
  have hentry (i : Fin 4) (n : ℕ) :
      ‖iteratedFDeriv ℝ n (coordinateChartDerivativeField F i) (G x)‖ ≤
        M n * (1 + p (n + midLoss) z) :=
    ((coordinateChartDerivativeField_norm_le_positiveJet_at hFx i n).trans
      (hFjets (n + 1) (by omega))).trans
        (physicalJetEnvelope_mono hp (hApos (n + 1)).le (hDM n) (by omega) z)
  have hrecip (n : ℕ) : ‖iteratedFDeriv ℝ n (fun y => |planeJacobian F y|⁻¹) (G x)‖ ≤
      M n * (1 + p (n + midLoss) z) :=
    (hRjets n).trans (physicalJetEnvelope_mono hp (hR n).le (hRM n)
      (Nat.add_le_add_left hlR n) z)
  have hprimitive (i : Fin 9) (n : ℕ) :
      ‖iteratedFDeriv ℝ n (coordinatePrimitiveJetField C F h i) (G x)‖ ≤
        M n * (1 + p (n + midLoss) z) := by
    fin_cases i
    · simpa [coordinatePrimitiveJetField, canonicalCoefficientComponent] using hcoef 0 n
    · simpa [coordinatePrimitiveJetField, canonicalCoefficientComponent] using hcoef 1 n
    · simpa [coordinatePrimitiveJetField, canonicalCoefficientComponent] using hcoef 2 n
    · simpa [coordinatePrimitiveJetField] using hentry 0 n
    · simpa [coordinatePrimitiveJetField] using hentry 1 n
    · simpa [coordinatePrimitiveJetField] using hentry 2 n
    · simpa [coordinatePrimitiveJetField] using hentry 3 n
    · simpa [coordinatePrimitiveJetField] using hheight n
    · simpa [coordinatePrimitiveJetField] using hrecip n
  have hmixed (i : Fin 9) (a b : ℕ) :
      |mixedDerivative a b (coordinatePrimitiveJetField C F h i) (G x)| ≤
        M (a + b) * (1 + p (a + b + midLoss) z) :=
    (abs_mixedDerivative_le_norm_iteratedFDeriv hU (hfields i) a b hx).trans
      (hprimitive i (a + b))
  have hinner (n : ℕ) (hn : 1 ≤ n) : ‖iteratedFDeriv ℝ n G x‖ ≤
      M n * (1 + p (n + midLoss) z) :=
    (hIjets n hn).trans (physicalJetEnvelope_mono hp (hIpos n).le (hIM n)
      (Nat.add_le_add_left hlI n) z)
  intro n
  have he := hbound z hzQ 1 le_rfl C F G h U hU hfields x hx hG
    (fun i a b => by simpa only [Real.one_rpow, mul_one] using hmixed i a b)
    (fun k hk => by simpa only [Real.one_rpow, mul_one] using hinner k hk) n
  simpa only [Real.one_rpow, mul_one] using he

end ContinuousFlexibility.Analysis
