module

public import ContinuousFlexibility.Analysis.N07aLinearJetCoefficient
public import ContinuousFlexibility.Analysis.N07aCanonicalJetNormBounds

/-!
# The actual source-linear field has mixed L² terminal bounds

Subtraction keeps a single fixed loss. The open representative and the
exact rectangle measure then give the terminal mixed-jet L² estimates,
with the complete square-root length factor retained in the sampled
envelope.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff BigOperators ENNReal

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {U : Set E} {w : ℕ → ℕ → ℝ} {low d d' : ℕ}
  {f g : E → F → ℕ → PolarPoint → ℝ}

theorem N07aSampleLinearJetBounds.loss_mono
    (hp : Monotone p) (hq : Monotone q) (hw : ∀ c m, 0 ≤ w c m)
    (hdd : d ≤ d')
    (hf : N07aSampleLinearJetBounds T K p q U (canonicalOpen S K) w low d f) :
    N07aSampleLinearJetBounds T K p q U (canonicalOpen S K) w low d' f := by
  intro a b c
  obtain ⟨e, he, he0, heb⟩ := hf a b c
  refine ⟨e, he, he0, fun z hz u m y hy => (heb z hz u m y hy).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (he0 m) (hw c m))
  have horder : c + (a + b) + d ≤ c + (a + b) + d' := Nat.add_le_add_left hdd _
  exact add_le_add (hq horder u)
    (mul_le_mul_of_nonneg_right (add_le_add le_rfl (hp horder z)) (apply_nonneg _ _))

theorem N07aSampleLinearJetBounds.sub
    (hf : N07aSampleLinearJetBounds T K p q U (canonicalOpen S K) w low d f)
    (hg : N07aSampleLinearJetBounds T K p q U (canonicalOpen S K) w low d g)
    (hfs : ∀ z ∈ U, ∀ u m, ContDiffOn ℝ ∞ (f z u m) (canonicalOpen S K m))
    (hgs : ∀ z ∈ U, ∀ u m, ContDiffOn ℝ ∞ (g z u m) (canonicalOpen S K m)) :
    N07aSampleLinearJetBounds T K p q U (canonicalOpen S K) w low d
      (fun z u m y => f z u m y - g z u m y) := by
  intro a b c
  obtain ⟨e, he, he0, heb⟩ := hf a b c
  obtain ⟨e', he', he0', heb'⟩ := hg a b c
  refine ⟨fun m => e m + e' m, he.add he', fun m => add_nonneg (he0 m) (he0' m), ?_⟩
  intro z hz u m y hy
  have hfun : (fun y => f z u m y - g z u m y) =
      fun y => f z u m y + (-1 : ℝ) * g z u m y := by funext y; ring
  have hjet : mixedDerivative a b (fun y => f z u m y - g z u m y) y =
      mixedDerivative a b (f z u m) y - mixedDerivative a b (g z u m) y := by
    rw [hfun, n07a_mixedDerivative_add_on (isOpen_Ioo.prod isOpen_univ)
      (hfs z hz u m) (contDiffOn_const.mul (hgs z hz u m)) a b hy,
      spaces_mixedDerivative_const_mul, neg_one_mul, ← sub_eq_add_neg]
  exact (congrArg abs hjet).le.trans ((abs_sub _ _).trans
    ((add_le_add (heb z hz u m y hy) (heb' z hz u m y hy)).trans_eq (by ring)))

theorem n07a_sampleLinearJet_mixed_eLpNorm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : ∀ m, K.left m < K.right m)
    (hlen : N07aSampleSubpower T K (fun m => Real.sqrt (Real.pi * (K.right m - K.left m))))
    (hw : ∀ c m, 0 ≤ w c m)
    (hf : N07aSampleLinearJetBounds T K p q U (canonicalOpen S K) w low d f)
    (hfs : ∀ z ∈ U, ∀ u m, ContDiffOn ℝ ∞ (f z u m) (canonicalOpen S K m))
    (hfp : ∀ z ∈ U, ∀ u m y, y ∈ canonicalOpen S K m →
      f z u m (y + (0, Real.pi)) = f z u m y) :
    ∀ a b c : ℕ, ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ z ∈ U, ∀ u m,
        eLpNorm (mixedDerivative a b (f z u m)) 2 (canonicalMeasure S K m) ≤
          ENNReal.ofReal (e m * w c m * (q (c + (a + b) + d) u +
            (1 + p (c + (a + b) + d) z) * q low u)) := by
  intro a b c
  obtain ⟨e, he, he0, heb⟩ := hf a b c
  refine ⟨fun m => Real.sqrt (Real.pi * (K.right m - K.left m)) * e m,
    N07aSampleSubpower.mul hD hT hlen he,
    fun m => mul_nonneg (Real.sqrt_nonneg _) (he0 m), fun z hz u m => ?_⟩
  let χ := hf.openCoefficient hw hfs hfp z hz u m
  let B : ℝ := q (c + (a + b) + d) u + (1 + p (c + (a + b) + d) z) * q low u
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hbound : ∀ᵐ y ∂canonicalMeasure S K m, |(χ.jet a b).value y| ≤ e m * w c m * B :=
    (n07a_canonicalOpen_ae (S := S) (K := K) (m := m)).mono
      (fun y hy => heb z hz u m y hy)
  have hn := (χ.jet a b).toLp_norm_le (hI m)
    (mul_nonneg (mul_nonneg (he0 m) (hw c m)) hB) hbound
  have hjet : ((χ.jet a b).toLp : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      mixedDerivative a b (f z u m) := (χ.jet a b).toLp_ae
  calc
    eLpNorm (mixedDerivative a b (f z u m)) 2 (canonicalMeasure S K m) =
        ENNReal.ofReal ‖(χ.jet a b).toLp‖ :=
      (eLpNorm_congr_ae hjet).symm.trans (by rw [← Lp.enorm_def, ← ofReal_norm])
    _ ≤ ENNReal.ofReal (Real.sqrt (Real.pi * (K.right m - K.left m)) *
        (e m * w c m * B)) := ENNReal.ofReal_le_ofReal hn
    _ = _ := congrArg ENNReal.ofReal (by dsimp only [B]; ring)

end ContinuousFlexibility.Analysis
