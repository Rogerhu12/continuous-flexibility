module

public import ContinuousFlexibility.Analysis.CoordinateFieldJetBounds
public import ContinuousFlexibility.Analysis.CoordinateCompositionMaterialBounds
public import ContinuousFlexibility.Analysis.CylinderMixedJetNorms

/-!
# Fixed-loss bounds after the actual inverse coordinate map

The physical potential and density estimates are composed with the
actual function used as inverse chart. Only its positive-order actual
Fréchet jets enter the composition theorem. The value estimate uses the
outer field directly, so no bound on the angular lift itself is needed.

Both low orders and both derivative losses are selected before the
output order. The hypotheses concern the nine actual primitive fields
and the actual inverse jets; no canonical potential or principal
coefficient estimate is an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem coordinateFieldEnvelope_mono
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {C D W : ℝ} (hW : 1 ≤ W) (hC : 0 ≤ C) (hCD : C ≤ D)
    {s t : ℕ} (hst : s ≤ t) (z : E) :
    C * W ^ C * (1 + p s z) ≤ D * W ^ D * (1 + p t z) := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hD : 0 ≤ D := hC.trans hCD
  exact mul_le_mul
    (mul_le_mul hCD (Real.rpow_le_rpow_of_exponent_le hW hCD)
      (Real.rpow_nonneg hW0 _) hD)
    (add_le_add (le_refl (1 : ℝ)) ((hp hst) z))
    (add_nonneg zero_le_one (apply_nonneg _ _))
    (mul_nonneg hD (Real.rpow_nonneg hW0 _))

private theorem inverseChartCoefficient_component_comp
    (A : SymmetricCoefficients) (F G : PolarPoint → PolarPoint)
    (h : PolarPoint → ℝ) (i : Fin 3) :
    canonicalCoefficientComponent i (inverseChartPrincipalCoefficients A F G h) =
      (canonicalCoefficientComponent i (coordinatePrincipalDensity A F h)) ∘ G := by
  unfold canonicalCoefficientComponent
  split_ifs <;> funext q <;>
    simp only [Function.comp_apply, inverseChartPrincipalCoefficients]

/-- The same inverse-map estimate applies when the physical primitives
are smooth only on an explicit open domain containing the image point. -/
theorem inverseChartFieldsOn_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ C : ℕ → ℝ, (∀ k, 1 ≤ C k) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ A : SymmetricCoefficients, ∀ F G : PolarPoint → PolarPoint,
      ∀ h : PolarPoint → ℝ, ∀ U : Set PolarPoint, IsOpen U →
        (∀ i, ContDiffOn ℝ ∞ (coordinatePrimitiveJetField A F h i) U) →
      ∀ x : PolarPoint, G x ∈ U → ContDiffAt ℝ ∞ G x →
        (∀ i a b,
          |mixedDerivative a b (coordinatePrimitiveJetField A F h i) (G x)| ≤
            C (a + b) * W ^ (C (a + b)) * (1 + p (a + b + inputLoss) z)) →
        (∀ k : ℕ, 1 ≤ k → ‖iteratedFDeriv ℝ k G x‖ ≤
          C k * W ^ (C k) * (1 + p (k + inputLoss) z)) →
      ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n (inverseChartPotential A F G h) x‖ ≤
          B n * W ^ (B n) * (1 + p (n + loss) z) ∧
        ∀ i : Fin 3, ‖iteratedFDeriv ℝ n
          (canonicalCoefficientComponent i (inverseChartPrincipalCoefficients A F G h)) x‖ ≤
            B n * W ^ (B n) * (1 + p (n + loss) z) := by
  classical
  obtain ⟨baseP, lossP, hphysical⟩ :=
    coordinatePhysicalFieldsOn_fixed_loss_material_bound hp hI inputLoss
  let midLoss : ℕ := max inputLoss lossP
  obtain ⟨baseQ, lossQ, hcomposition⟩ :=
    coordinateComposition_fixed_loss_material_bound
      (X := PolarPoint) (Y := PolarPoint) (Z := ℝ) hp hI midLoss
  refine ⟨max baseP baseQ, max lossP lossQ, ?_⟩
  intro C hC
  obtain ⟨P, hP, hPb⟩ := hphysical C hC
  let R : ℕ → ℝ := fun k => max 1 (max (C k) (P k))
  have hR (k : ℕ) : 1 ≤ R k := le_max_left _ _
  have hCR (k : ℕ) : C k ≤ R k :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hPR (k : ℕ) : P k ≤ R k :=
    (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨Q, hQ, hQb⟩ := hcomposition R hR
  let B : ℕ → ℝ := fun n => 1 + max (P n) (Q (n - 1))
  have hB (n : ℕ) : 0 < B n := by
    have hmax := le_max_left (P n) (Q (n - 1))
    dsimp only [B]
    linarith [hP n]
  have hPB (n : ℕ) : P n ≤ B n := by
    have hmax := le_max_left (P n) (Q (n - 1))
    dsimp only [B]
    linarith
  have hQB (n : ℕ) : Q n ≤ B (n + 1) := by
    have hi : n + 1 - 1 = n := by omega
    have hmax := le_max_right (P (n + 1)) (Q n)
    dsimp only [B]
    rw [hi]
    linarith
  refine ⟨B, hB, ?_⟩
  intro z hz W hW A F G h U hU hfields x hx hG hraw hGjets n
  have hzP : p baseP z ≤ 1 := ((hp (le_max_left _ _)) z).trans hz
  have hzQ : p baseQ z ≤ 1 := ((hp (le_max_right _ _)) z).trans hz
  have hphysicalJets := hPb z hzP W hW A F h U hU hfields (G x) hx hraw
  have hsmooth := contDiffOn_coordinatePhysicalFields hU A F h hfields
  have hinner (k : ℕ) (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ k G x‖ ≤
        R k * W ^ (R k) * (1 + p (k + midLoss) z) :=
    (hGjets k hk).trans
      (coordinateFieldEnvelope_mono hp hW (zero_le_one.trans (hC k)) (hCR k)
        (Nat.add_le_add_left (le_max_left inputLoss lossP) k) z)
  have hcomposed (f : PolarPoint → ℝ) (hf : ContDiffAt ℝ ∞ f (G x))
      (hfb : ∀ k : ℕ, ‖iteratedFDeriv ℝ k f (G x)‖ ≤
        P k * W ^ (P k) * (1 + p (k + lossP) z)) :
      ∀ k : ℕ, ‖iteratedFDeriv ℝ k (f ∘ G) x‖ ≤
        B k * W ^ (B k) * (1 + p (k + max lossP lossQ) z) := by
    intro k
    cases k with
    | zero =>
      have hv := (hfb 0).trans
        (coordinateFieldEnvelope_mono hp hW (hP 0).le (hPB 0)
          (Nat.add_le_add_left (le_max_left lossP lossQ) 0) z)
      simpa only [norm_iteratedFDeriv_zero, Function.comp_apply] using hv
    | succ k =>
      have houter (j : ℕ) (_ : 1 ≤ j) :
          ‖iteratedFDeriv ℝ j f (G x)‖ ≤
            R j * W ^ (R j) * (1 + p (j + midLoss) z) :=
        (hfb j).trans
          (coordinateFieldEnvelope_mono hp hW (hP j).le (hPR j)
            (Nat.add_le_add_left (le_max_right inputLoss lossP) j) z)
      exact (hQb z hzQ W hW f G x hf hG houter hinner k).trans
        (coordinateFieldEnvelope_mono hp hW (hQ k).le (hQB k)
          (Nat.add_le_add_left (le_max_right lossP lossQ) (k + 1)) z)
  constructor
  · have hb := hcomposed
      (fun q => h q * divergenceOperator A h q / |planeJacobian F q|)
      (hsmooth.1.contDiffAt (hU.mem_nhds hx)) (fun k => (hphysicalJets k).1) n
    unfold inverseChartPotential
    simpa only [Function.comp_def] using hb
  · intro i
    rw [inverseChartCoefficient_component_comp A F G h i]
    exact hcomposed (canonicalCoefficientComponent i (coordinatePrincipalDensity A F h))
      ((hsmooth.2 i).contDiffAt (hU.mem_nhds hx)) (fun k => (hphysicalJets k).2 i) n

/-- The actual transformed fields have one common base and fixed loss.
The inverse map is differentiated as a genuine function, with no
zeroth-order inverse-coordinate bound among the inputs. -/
theorem inverseChartFields_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ C : ℕ → ℝ, (∀ k, 1 ≤ C k) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ A : SymmetricCoefficients, ∀ F G : PolarPoint → PolarPoint,
      ∀ h : PolarPoint → ℝ,
        (∀ i, ContDiff ℝ ∞ (coordinatePrimitiveJetField A F h i)) →
      ∀ x : PolarPoint, ContDiffAt ℝ ∞ G x →
        (∀ i a b,
          |mixedDerivative a b (coordinatePrimitiveJetField A F h i) (G x)| ≤
            C (a + b) * W ^ (C (a + b)) * (1 + p (a + b + inputLoss) z)) →
        (∀ k : ℕ, 1 ≤ k → ‖iteratedFDeriv ℝ k G x‖ ≤
          C k * W ^ (C k) * (1 + p (k + inputLoss) z)) →
      ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n (inverseChartPotential A F G h) x‖ ≤
          B n * W ^ (B n) * (1 + p (n + loss) z) ∧
        ∀ i : Fin 3, ‖iteratedFDeriv ℝ n
          (canonicalCoefficientComponent i (inverseChartPrincipalCoefficients A F G h)) x‖ ≤
            B n * W ^ (B n) * (1 + p (n + loss) z) := by
  obtain ⟨base, loss, hbound⟩ := inverseChartFieldsOn_fixed_loss_material_bound hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro C hC
  obtain ⟨B, hB, hb⟩ := hbound C hC
  refine ⟨B, hB, ?_⟩
  intro z hz W hW A F G h hfields x hG hraw hGjets n
  exact hb z hz W hW A F G h univ isOpen_univ
    (fun i => (hfields i).contDiffOn) x (mem_univ (G x)) hG hraw hGjets n

/-- On actual open source and target domains the same constants bound
every mixed jet of the explicit canonical fields. The inverse-map
smoothness and image hypotheses are genuine map properties. -/
theorem inverseChartFields_mixed_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ C : ℕ → ℝ, (∀ k, 1 ≤ C k) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ A : SymmetricCoefficients, ∀ F G : PolarPoint → PolarPoint,
      ∀ h : PolarPoint → ℝ, ∀ U V : Set PolarPoint, IsOpen U → IsOpen V →
        (∀ i, ContDiffOn ℝ ∞ (coordinatePrimitiveJetField A F h i) U) →
        ContDiffOn ℝ ∞ G V → MapsTo G V U →
        (∀ x ∈ V, ∀ i a b,
          |mixedDerivative a b (coordinatePrimitiveJetField A F h i) (G x)| ≤
            C (a + b) * W ^ (C (a + b)) * (1 + p (a + b + inputLoss) z)) →
        (∀ x ∈ V, ∀ k : ℕ, 1 ≤ k → ‖iteratedFDeriv ℝ k G x‖ ≤
          C k * W ^ (C k) * (1 + p (k + inputLoss) z)) →
      ∀ a b : ℕ, ∀ x ∈ V,
        |mixedDerivative a b (inverseChartPotential A F G h) x| ≤
          B (a + b) * W ^ (B (a + b)) * (1 + p (a + b + loss) z) ∧
        ∀ i : Fin 3, |mixedDerivative a b
          (canonicalCoefficientComponent i (inverseChartPrincipalCoefficients A F G h)) x| ≤
            B (a + b) * W ^ (B (a + b)) * (1 + p (a + b + loss) z) := by
  obtain ⟨base, loss, hbound⟩ := inverseChartFieldsOn_fixed_loss_material_bound hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro C hC
  obtain ⟨B, hB, hb⟩ := hbound C hC
  refine ⟨B, hB, ?_⟩
  intro z hz W hW A F G h U V hU hV hfields hG hmaps hraw hGjets a b x hx
  have hsmooth := contDiffOn_coordinatePhysicalFields hU A F h hfields
  have hpotential : ContDiffOn ℝ ∞ (inverseChartPotential A F G h) V := by
    unfold inverseChartPotential
    simpa only [Function.comp_def] using
      hsmooth.1.comp hG hmaps
  have hcoefficient (i : Fin 3) : ContDiffOn ℝ ∞
      (canonicalCoefficientComponent i (inverseChartPrincipalCoefficients A F G h)) V := by
    rw [inverseChartCoefficient_component_comp A F G h i]
    exact (hsmooth.2 i).comp hG hmaps
  have hjet := hb z hz W hW A F G h U hU hfields x (hmaps hx)
    (hG.contDiffAt (hV.mem_nhds hx)) (hraw x hx) (hGjets x hx) (a + b)
  exact ⟨(abs_mixedDerivative_le_norm_iteratedFDeriv hV hpotential a b hx).trans hjet.1,
    fun i => (abs_mixedDerivative_le_norm_iteratedFDeriv hV (hcoefficient i) a b hx).trans
      (hjet.2 i)⟩

end ContinuousFlexibility.Analysis
