module

public import ContinuousFlexibility.Analysis.N07aSampleLinearJets
public import ContinuousFlexibility.Analysis.N07aCanonicalRepresentationPairing

/-!
# Bounded open coefficients supplied by the actual source-linear estimates

Every fixed input gives the same original scalar function and its actual
mixed jets. Pointwise estimates on the open piece imply precisely the
boundedness required to form its genuine L² classes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {U : Set E} {w : ℕ → ℕ → ℝ} {low loss : ℕ}
  {f : E → F → ℕ → PolarPoint → ℝ}

def N07aSampleLinearJetBounds.openCoefficient
    (hf : N07aSampleLinearJetBounds T K p q U (canonicalOpen S K) w low loss f)
    (hw : ∀ c m, 0 ≤ w c m)
    (hfs : ∀ z ∈ U, ∀ u m, ContDiffOn ℝ ∞ (f z u m) (canonicalOpen S K m))
    (hfp : ∀ z ∈ U, ∀ u m y, y ∈ canonicalOpen S K m →
      f z u m (y + (0, Real.pi)) = f z u m y)
    (z : E) (hz : z ∈ U) (u : F) (m : ℕ) : N07aCanonicalOpenCoefficient S K m where
  value := f z u m
  smooth := hfs z hz u m
  periodic := hfp z hz u m
  bounded := by
    intro a b
    obtain ⟨e, _, he0, heb⟩ := hf a b 0
    refine ⟨e m * w 0 m *
      (q (0 + (a + b) + loss) u + (1 + p (0 + (a + b) + loss) z) * q low u),
      mul_nonneg (mul_nonneg (he0 m) (hw 0 m))
        (add_nonneg (apply_nonneg _ _)
          (mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _))), ?_⟩
    exact (n07a_canonicalOpen_ae (S := S) (K := K) (m := m)).mono
      (fun y hy => heb z hz u m y hy)

theorem N07aSampleLinearJetBounds.openCoefficient_value
    (hf : N07aSampleLinearJetBounds T K p q U (canonicalOpen S K) w low loss f)
    (hw : ∀ c m, 0 ≤ w c m)
    (hfs : ∀ z ∈ U, ∀ u m, ContDiffOn ℝ ∞ (f z u m) (canonicalOpen S K m))
    (hfp : ∀ z ∈ U, ∀ u m y, y ∈ canonicalOpen S K m →
      f z u m (y + (0, Real.pi)) = f z u m y)
    (z : E) (hz : z ∈ U) (u : F) (m : ℕ) :
    (hf.openCoefficient hw hfs hfp z hz u m).value = f z u m := rfl

end ContinuousFlexibility.Analysis
