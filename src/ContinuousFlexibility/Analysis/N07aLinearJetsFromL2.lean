module

public import ContinuousFlexibility.Analysis.N07aCanonicalMixedPointwise
public import ContinuousFlexibility.Analysis.N07aSampleLinearJets
public import ContinuousFlexibility.Analysis.N07aModeBudgetMaterial

/-!
# The actual L² bounds give source-linear pointwise jets at fixed loss

The only added derivative cost is two, uniformly over all mixed and
material orders. The complete strip constant remains a subpower envelope.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

theorem n07a_sampleLinearJetBounds_of_mixed_L2
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hinterval : ∀ m, K.left m < K.right m)
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q)
    (U : Set E) (w : ℕ → ℕ → ℝ) (hw : ∀ c m, 0 ≤ w c m)
    (low loss : ℕ) (f : E → F → ℕ → PolarPoint → ℝ)
    (hfs : ∀ z ∈ U, ∀ u m, ContDiffOn ℝ ∞ (f z u m) (canonicalOpen S K m))
    (hfp : ∀ z ∈ U, ∀ u m x, x ∈ canonicalOpen S K m →
      f z u m (x + (0, Real.pi)) = f z u m x)
    (hL2 : ∀ a b c : ℕ, ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ u m,
          eLpNorm (mixedDerivative a b (f z u m)) 2 (canonicalMeasure S K m) ≤
            ENNReal.ofReal (e m * w c m *
              (q (c + (a + b) + loss) u +
                (1 + p (c + (a + b) + loss) z) * q low u))) :
    N07aSampleLinearJetBounds T K p q U (canonicalOpen S K) w low (loss + 2) f := by
  classical
  choose e he he0 heb using hL2
  let A : ℕ → ℝ := fun m => (1 + 2 * (K.right m - K.left m)⁻¹) *
    Real.sqrt (Real.pi * (K.right m - K.left m))
  have hA : N07aSampleSubpower T K A :=
    N07aSampleSubpower.mul hD hT
      ((N07aSampleSubpower.const hD hT 1).add
        (N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT 2)
          (n07a_canonicalLengthInverse_subpower hD hT href)))
      (n07a_canonicalModeNormalization_subpower hD hT href)
  have hA0 (m : ℕ) : 0 ≤ A m :=
    mul_nonneg (add_nonneg zero_le_one (mul_nonneg (by norm_num)
      (inv_nonneg.mpr (sub_pos.mpr (hinterval m)).le))) (Real.sqrt_nonneg _)
  intro a b c
  let E₀ := fun m => e a b c m + e (a + 1) b c m +
    e a (b + 1) c m + e (a + 1) (b + 1) c m
  have hE : N07aSampleSubpower T K E₀ :=
    (((he a b c).add (he (a + 1) b c)).add (he a (b + 1) c)).add
      (he (a + 1) (b + 1) c)
  have hE0 (m : ℕ) : 0 ≤ E₀ m :=
    add_nonneg (add_nonneg (add_nonneg (he0 a b c m) (he0 (a + 1) b c m))
      (he0 a (b + 1) c m)) (he0 (a + 1) (b + 1) c m)
  refine ⟨fun m => A m * E₀ m, N07aSampleSubpower.mul hD hT hA hE,
    fun m => mul_nonneg (hA0 m) (hE0 m), ?_⟩
  intro z hz u m x hx
  let B := q (c + (a + b) + (loss + 2)) u +
    (1 + p (c + (a + b) + (loss + 2)) z) * q low u
  have hbound (ar an : ℕ) (horder : ar + an ≤ a + b + 2) :
      (eLpNorm (mixedDerivative ar an (f z u m)) 2 (canonicalMeasure S K m)).toReal ≤
        e ar an c m * w c m * B := by
    have h := heb ar an c z hz u m
    have hP : 0 ≤ q (c + (ar + an) + loss) u +
        (1 + p (c + (ar + an) + loss) z) * q low u :=
      add_nonneg (apply_nonneg _ _)
        (mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _))
    apply (ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (mul_nonneg (he0 ar an c m) (hw c m)) hP) h).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (he0 ar an c m) (hw c m))
    exact add_le_add (hq (by omega) u)
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl (hp (by omega) z)) (apply_nonneg _ _))
  have hmem (ar an : ℕ) :
      MemLp (mixedDerivative ar an (f z u m)) 2 (canonicalMeasure S K m) :=
    memLp_iff.mpr (lt_of_le_of_lt (heb ar an c z hz u m) ENNReal.ofReal_lt_top)
  have hpoint := n07a_canonicalOpen_mixed_pointwise_L2 (hinterval m)
    (hfs z hz u m) (hfp z hz u m) hmem a b hx
  have hsum := add_le_add (add_le_add (add_le_add
    (hbound a b (by omega)) (hbound (a + 1) b (by omega)))
    (hbound a (b + 1) (by omega))) (hbound (a + 1) (b + 1) (by omega))
  exact (hpoint.trans (mul_le_mul_of_nonneg_left hsum (hA0 m))).trans_eq
    (by dsimp only [A, E₀, B]; ring)

end ContinuousFlexibility.Analysis
