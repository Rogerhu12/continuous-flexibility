import ContinuousFlexibility.Analysis.RootCoefficientFactorization
import ContinuousFlexibility.Analysis.MixedSimpleDivisionBounds
import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization
import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace

/-!
# Actual fixed-loss division of the root coefficient discriminant

A single state-independent radial clamp extends the actual factor.
The auxiliary numerator is r times that extension, so it agrees with
the original coefficient discriminant on the inner strip. Its mixed
jets there are therefore the original coefficient jets, and the first
Taylor integral gives a true loss of one, including at the root circle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Conditions concern the original profile, height, and their actual
derivatives throughout one fixed outer strip. -/
def RootCoefficientStripConditions (wref g w : ℝ → ℝ) (z : PolarPoint → ℝ)
    (r σ R : ℝ) : Prop :=
  ∀ p ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ),
    0 < (rootProfileShift r σ p).1 ∧
    0 < wref (rootProfileShift r σ p).1 ∧ 0 < g p.1 ∧
    0 < polarDiscriminant w z (rootProfileShift r σ p) ∧
    0 < heightQ (profileEnergy w (rootProfileShift r σ p))
      (heightRadial z (rootProfileShift r σ p))
      (angularPartial (heightAngular z) (rootProfileShift r σ p)) ∧
    w (rootProfileShift r σ p).1 = wref (rootProfileShift r σ p).1 ∧
    -deriv w (rootProfileShift r σ p).1 = p.1 * g p.1

/-- The numerator and factor below are constructed from the actual
fields. No globally smooth extension or inverse is supplied as input. -/
theorem exists_rootCoefficient_factor_extension
    {wref g w : ℝ → ℝ} {z : PolarPoint → ℝ}
    (hwref : ContDiff ℝ ∞ wref) (hg : ContDiff ℝ ∞ g)
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    {r σ R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions wref g w z r σ R) :
    ∃ F G : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧ ContDiff ℝ ∞ G ∧
      (∀ p : PolarPoint, F p = p.1 * G p) ∧
      EqOn F (rootCoefficientDiscriminant w z r σ)
        (Ioo (-R) R ×ˢ (univ : Set ℝ)) ∧
      EqOn G (rootCoefficientRadialFactor wref g w z r σ)
        (Ioo (-R) R ×ˢ (univ : Set ℝ)) := by
  let H := rootCoefficientRadialFactor wref g w z r σ
  have hH : ContDiffOn ℝ ∞ H (Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ)) := by
    intro p hp
    obtain ⟨hrp, hwp, hgp, hDp, hQp, _, _⟩ := hstrip p hp
    exact (contDiffAt_rootCoefficientRadialFactor
      hwref hg hw hz hrp hwp hgp hDp hQp).contDiffWithinAt
  have hab : -R ≤ R := neg_le_self hR.le
  let G := circleFlowLocalizedSpeed H hab hR
  have hG : ContDiff ℝ ∞ G := contDiff_circleFlowLocalizedSpeed hab hR hH
  let F : PolarPoint → ℝ := fun p => p.1 * G p
  have hF : ContDiff ℝ ∞ F := contDiff_fst.mul hG
  have hGeq : EqOn G H (Ioo (-R) R ×ˢ (univ : Set ℝ)) := by
    intro p hp
    exact circleFlowLocalizedSpeed_eq hab hR ⟨hp.1.1.le, hp.1.2.le⟩ p.2
  refine ⟨F, G, hF, hG, fun _ => rfl, ?_, hGeq⟩
  intro p hp
  have hpouter : p ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hp.1.1, hp.1.2]
  obtain ⟨hrp, hwp, hgp, hDp, hQp, hweq, hdivide⟩ := hstrip p hpouter
  change p.1 * G p = _
  rw [hGeq hp]
  exact (rootCoefficientDiscriminant_factorization
    (hw.differentiable (by simp) _) hrp hwp hgp hDp hQp.ne' hweq hdivide).symm

/-- An actual mixed numerator bound on the inner strip gives the factor
bound with exactly one additional radial derivative. -/
theorem abs_mixedDerivative_rootCoefficientRadialFactor_le
    {wref g w : ℝ → ℝ} {z : PolarPoint → ℝ}
    (hwref : ContDiff ℝ ∞ wref) (hg : ContDiff ℝ ∞ g)
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    {r σ R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions wref g w z r σ R)
    (a b : ℕ) {p : PolarPoint}
    (hp : p ∈ Ioo (-R) R ×ˢ (univ : Set ℝ)) {M : ℝ}
    (hbound : ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
      |mixedDerivative (a + 1) b (rootCoefficientDiscriminant w z r σ) q| ≤ M) :
    |mixedDerivative a b (rootCoefficientRadialFactor wref g w z r σ) p| ≤ M := by
  obtain ⟨F, G, hF, hG, hfactor, hFeq, hGeq⟩ :=
    exists_rootCoefficient_factor_extension hwref hg hw hz hR hstrip
  have hFjet := mixedDerivative_eqOn_of_isOpen
    (isOpen_Ioo.prod isOpen_univ) hFeq (a + 1) b
  have hGjet := mixedDerivative_eqOn_of_isOpen
    (isOpen_Ioo.prod isOpen_univ) hGeq a b
  rw [← hGjet hp]
  apply abs_mixedDerivative_smoothRadialFactor_le hF hG hfactor a b
  intro t ht
  have htp : (t * p.1, p.2) ∈ Ioo (-R) R ×ˢ (univ : Set ℝ) :=
    ⟨mul_radial_mem_symmetric_strip hR hp.1 ht, mem_univ _⟩
  rw [hFjet htp]
  exact hbound _ htp

end ContinuousFlexibility.Analysis
