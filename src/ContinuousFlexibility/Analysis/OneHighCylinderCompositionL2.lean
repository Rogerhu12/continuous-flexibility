module

public import ContinuousFlexibility.Analysis.OneHighCylinderCompositionJets
public import ContinuousFlexibility.Analysis.OneHighL2Domination

/-!
# Finite-energy pure derivatives of actual smooth compositions

The finite chain-rule majorant proves output L² membership as well as its
norm bound. The final scalar and multivariable estimates instantiate every
product premise with the actual one-high derivative-product theorem.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal BigOperators ContDiff

variable {P : ℝ} [Fact (0 < P)] {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Select either one of the two genuine coordinate derivative towers. -/
def cylinderPureDerivative (f : ℝ × AddCircle P → E) (radial : Bool) (k : ℕ) :
    ℝ × AddCircle P → E :=
  if radial then cylinderRadialJet f k else cylinderAngularJet f k

theorem continuous_cylinderPureDerivative {f : ℝ × AddCircle P → E}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P))))
    (radial : Bool) (k : ℕ) : Continuous (cylinderPureDerivative f radial k) := by
  cases radial
  · exact continuous_cylinderAngularJet hf k
  · exact continuous_cylinderRadialJet hf k

@[simp] theorem cylinderPureDerivative_zero (f : ℝ × AddCircle P → E) (radial : Bool) :
    cylinderPureDerivative f radial 0 = f := by
  cases radial <;> simp [cylinderPureDerivative]

/-- The L² form of the actual finite Faà di Bruno expansion. No membership
of the output derivative is assumed. -/
theorem cylinder_composition_pure_l2_of_product_bounds
    (u : CylinderSmoothJet P E) (Φ : E → ℝ)
    (hΦ : ∀ p, ContDiffAt ℝ ∞ Φ (u.jet 0 0 p))
    {k : ℕ} (hk : 0 < k) (radial : Bool) {B : ℕ → ℝ}
    (hB0 : ∀ n, 0 ≤ B n)
    (hB : ∀ p n, 1 ≤ n → n ≤ k →
      ‖iteratedFDeriv ℝ n Φ (u.jet 0 0 p)‖ ≤ B n)
    (A : OrderedFinpartition k → ℝ)
    (hprod : ∀ c : OrderedFinpartition k,
      MemLp (fun p => ∏ j,
        ‖u.jet (if radial then c.partSize j else 0)
          (if radial then 0 else c.partSize j) p‖) 2 (cylinderPhysicalMeasure P) ∧
      (eLpNorm (fun p => ∏ j,
        ‖u.jet (if radial then c.partSize j else 0)
          (if radial then 0 else c.partSize j) p‖) 2 (cylinderPhysicalMeasure P)).toReal ≤ A c) :
    MemLp (cylinderPureDerivative (cylinderComposition u Φ) radial k)
        2 (cylinderPhysicalMeasure P) ∧
      (eLpNorm (cylinderPureDerivative (cylinderComposition u Φ) radial k)
        2 (cylinderPhysicalMeasure P)).toReal ≤
      ∑ c : OrderedFinpartition k, B c.length * A c := by
  classical
  let J (c : OrderedFinpartition k) (p : ℝ × AddCircle P) : ℝ :=
    ∏ j, ‖u.jet (if radial then c.partSize j else 0)
      (if radial then 0 else c.partSize j) p‖
  have hpoint (p : ℝ × AddCircle P) :
      ‖cylinderPureDerivative (cylinderComposition u Φ) radial k p‖ ≤
        ∑ c : OrderedFinpartition k, B c.length * ‖J c p‖ := by
    cases radial
    · simpa [cylinderPureDerivative, J, norm_prod] using cylinder_composition_angular_pointwise u Φ hΦ hk hB p
    · simpa [cylinderPureDerivative, J, norm_prod] using cylinder_composition_radial_pointwise u Φ hΦ hk hB p
  have hD := oneHigh_l2_finite_domination
    (continuous_cylinderPureDerivative (cylinderComposition_contDiff_lift u Φ hΦ)
      radial k).aestronglyMeasurable J (fun c => (hprod c).1)
    (fun c => B c.length) (fun c => hB0 c.length) (Eventually.of_forall hpoint)
  refine ⟨hD.1, hD.2.trans ?_⟩
  exact Finset.sum_le_sum fun c _ =>
    mul_le_mul_of_nonneg_left (hprod c).2 (hB0 c.length)

end ContinuousFlexibility.Analysis
