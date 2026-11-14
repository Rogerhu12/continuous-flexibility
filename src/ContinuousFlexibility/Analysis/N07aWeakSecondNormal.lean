module

public import ContinuousFlexibility.Analysis.N07aWeakNormalEquation

/-!
# The second normal derivative of a rough canonical solution

The first derivatives and the angular derivative of the radial jet are
enough to recover a second normal derivative from the actual divergence
equation. The proof stays in L² throughout: it differentiates the angular
flux, subtracts the mixed flux, and multiplies by the reciprocal leading
coefficient using the weak product rule.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

/-- A first-order coefficient bound on the actual canonical measure. -/
def N07aCanonicalC1Bound (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ)
    (χ : PolarPoint → ℝ) (A : ℝ) : Prop :=
  ∀ᵐ p ∂canonicalMeasure S K m,
    |χ p| + |mixedDerivative 1 0 χ p| + |mixedDerivative 0 1 χ p| ≤ A

theorem N07aCanonicalC1Bound.value {χ : PolarPoint → ℝ} {A : ℝ}
    (h : N07aCanonicalC1Bound S K m χ A) :
    ∀ᵐ p ∂canonicalMeasure S K m, |χ p| ≤ A := by
  filter_upwards [h] with p hp
  linarith [abs_nonneg (mixedDerivative 1 0 χ p),
    abs_nonneg (mixedDerivative 0 1 χ p)]

theorem N07aCanonicalC1Bound.first {χ : PolarPoint → ℝ} {A : ℝ}
    (h : N07aCanonicalC1Bound S K m χ A) (j : Fin 2) :
    ∀ᵐ p ∂canonicalMeasure S K m,
      |mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ p| ≤ A := by
  filter_upwards [h] with p hp
  fin_cases j <;> simp [n07aFirstOrder] <;>
    linarith [abs_nonneg (χ p), abs_nonneg (mixedDerivative 1 0 χ p),
      abs_nonneg (mixedDerivative 0 1 χ p)]

def n07aC1Multiplier (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ) (A : ℝ)
    (hA : N07aCanonicalC1Bound S K m χ A) :
    CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m :=
  n07aCanonicalMultiplier χ hχ.continuous.aestronglyMeasurable A hA.value

def n07aC1DerivativeMultiplier (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ) (A : ℝ)
    (hA : N07aCanonicalC1Bound S K m χ A) (j : Fin 2) :
    CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m :=
  n07aCanonicalMultiplier (mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2 χ)
    (contDiff_mixedDerivative hχ _ _).continuous.aestronglyMeasurable A (hA.first j)

theorem n07aC1Multiplier_ae (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ) (A : ℝ)
    (hA : N07aCanonicalC1Bound S K m χ A) (u : CanonicalL2 S K m) :
    (n07aC1Multiplier χ hχ A hA u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => χ p * u p :=
  n07aCanonicalMultiplier_ae χ _ A hA.value u

theorem n07aC1Multiplier_norm_le (χ : PolarPoint → ℝ) (hχ : ContDiff ℝ ∞ χ) (A : ℝ)
    (hA : N07aCanonicalC1Bound S K m χ A) (u : CanonicalL2 S K m) :
    ‖n07aC1Multiplier χ hχ A hA u‖ ≤ A * ‖u‖ :=
  n07aCanonicalMultiplier_norm_le χ _ A hA.value u

theorem n07aC1DerivativeMultiplier_norm_le (χ : PolarPoint → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (A : ℝ) (hA : N07aCanonicalC1Bound S K m χ A)
    (j : Fin 2) (u : CanonicalL2 S K m) :
    ‖n07aC1DerivativeMultiplier χ hχ A hA j u‖ ≤ A * ‖u‖ :=
  n07aCanonicalMultiplier_norm_le _ _ A (hA.first j) u

theorem n07aC1Multiplier_weak_product {χ : PolarPoint → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχp : Function.Periodic χ (0, Real.pi))
    (A : ℝ) (hA : N07aCanonicalC1Bound S K m χ A) (j : Fin 2)
    {u du : CanonicalL2 S K m}
    (h : N07aWeakCanonicalMixedDerivative S K m u du
      (n07aFirstOrder j).1 (n07aFirstOrder j).2) :
    N07aWeakCanonicalMixedDerivative S K m (n07aC1Multiplier χ hχ A hA u)
      (n07aC1Multiplier χ hχ A hA du + n07aC1DerivativeMultiplier χ hχ A hA j u)
      (n07aFirstOrder j).1 (n07aFirstOrder j).2 :=
  n07a_weakCanonical_first_product hχ hχp j A A hA.value (hA.first j) h

theorem n07aC1Multiplier_inverse {a χ : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ a) (hχ : ContDiff ℝ ∞ χ) (A B : ℝ)
    (hA : N07aCanonicalC1Bound S K m a A)
    (hB : N07aCanonicalC1Bound S K m χ B)
    (hinv : ∀ᵐ p ∂canonicalMeasure S K m, χ p * a p = 1)
    (u : CanonicalL2 S K m) :
    n07aC1Multiplier χ hχ B hB (n07aC1Multiplier a ha A hA u) = u := by
  apply Lp.ext
  filter_upwards [n07aC1Multiplier_ae χ hχ B hB (n07aC1Multiplier a ha A hA u),
    n07aC1Multiplier_ae a ha A hA u, hinv] with p hχa ha' hi
  rw [hχa, ha', ← mul_assoc, hi, one_mul]

/-- The actual L² right-hand side obtained by differentiating the angular
flux, subtracting the mixed flux and applying the reciprocal coefficient. -/
def n07aCanonicalSecondNormalRhs
    (a b c χ : PolarPoint → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : ContDiff ℝ ∞ c) (hχ : ContDiff ℝ ∞ χ) (A : ℝ)
    (haA : N07aCanonicalC1Bound S K m a A)
    (hbA : N07aCanonicalC1Bound S K m b A)
    (hcA : N07aCanonicalC1Bound S K m c A)
    (hχA : N07aCanonicalC1Bound S K m χ A)
    (F ur uθ urθ uθθ : CanonicalL2 S K m) : CanonicalL2 S K m :=
  n07aC1Multiplier χ hχ A hχA
    (F - ((n07aC1Multiplier b hb A hbA urθ +
        n07aC1DerivativeMultiplier b hb A hbA 1 ur) +
      (n07aC1Multiplier c hc A hcA uθθ +
        n07aC1DerivativeMultiplier c hc A hcA 1 uθ)) -
      (n07aC1Multiplier b hb A hbA urθ +
        n07aC1DerivativeMultiplier b hb A hbA 0 uθ)) +
    n07aC1DerivativeMultiplier χ hχ A hχA 0 (n07aC1Multiplier a ha A haA ur)

/-- Quantitative recovery of the second normal derivative. The source is
the original right-hand side of the flux equation. Angular differentiability
of the corrected source is not substituted for its normal regularity. -/
theorem n07a_weakCanonical_secondNormal
    (a b c χ : PolarPoint → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : ContDiff ℝ ∞ c) (hχ : ContDiff ℝ ∞ χ)
    (hbp : Function.Periodic b (0, Real.pi))
    (hcp : Function.Periodic c (0, Real.pi))
    (hχp : Function.Periodic χ (0, Real.pi))
    (A : ℝ) (hA : 1 ≤ A)
    (haA : N07aCanonicalC1Bound S K m a A)
    (hbA : N07aCanonicalC1Bound S K m b A)
    (hcA : N07aCanonicalC1Bound S K m c A)
    (hχA : N07aCanonicalC1Bound S K m χ A)
    (hinv : ∀ᵐ p ∂canonicalMeasure S K m, χ p * a p = 1)
    {u ur uθ urθ uθθ F : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1)
    (hflux : N07aCanonicalFluxEquation S K m F
      (n07aC1Multiplier a ha A haA ur + n07aC1Multiplier b hb A hbA uθ)
      (n07aC1Multiplier b hb A hbA ur + n07aC1Multiplier c hc A hcA uθ)) :
    let urr := n07aCanonicalSecondNormalRhs a b c χ ha hb hc hχ A haA hbA hcA hχA
      F ur uθ urθ uθθ;
      N07aWeakCanonicalMixedDerivative S K m ur urr 1 0 ∧
      N07aWeakCanonicalMixedDerivative S K m u urr 2 0 ∧
      ‖urr‖ ≤ 2 * A ^ 2 * (‖F‖ + ‖ur‖ + ‖uθ‖ + ‖urθ‖ + ‖uθθ‖) := by
  let Ma := n07aC1Multiplier a ha A haA
  let Mb := n07aC1Multiplier b hb A hbA
  let Mc := n07aC1Multiplier c hc A hcA
  let Mi := n07aC1Multiplier χ hχ A hχA
  let Dbθ := n07aC1DerivativeMultiplier b hb A hbA 1
  let Dcθ := n07aC1DerivativeMultiplier c hc A hcA 1
  let Dbr := n07aC1DerivativeMultiplier b hb A hbA 0
  let Dir := n07aC1DerivativeMultiplier χ hχ A hχA 0
  have hbθ : N07aWeakCanonicalMixedDerivative S K m (Mb ur)
      (Mb urθ + Dbθ ur) 0 1 :=
    n07aC1Multiplier_weak_product hb hbp A hbA 1 hrθ
  have hcθ : N07aWeakCanonicalMixedDerivative S K m (Mc uθ)
      (Mc uθθ + Dcθ uθ) 0 1 :=
    n07aC1Multiplier_weak_product hc hcp A hcA 1 hθθ
  let dqθ := (Mb urθ + Dbθ ur) + (Mc uθθ + Dcθ uθ)
  have hqr : N07aWeakCanonicalMixedDerivative S K m
      (Ma ur + Mb uθ) (F - dqθ) 1 0 :=
    n07a_weakCanonical_normalFlux hflux (hbθ.add hcθ)
  have hbr : N07aWeakCanonicalMixedDerivative S K m (Mb uθ)
      (Mb urθ + Dbr uθ) 1 0 :=
    n07aC1Multiplier_weak_product hb hbp A hbA 0
      (n07a_weakCanonical_crossDerivative hr hθ hrθ)
  let dv := F - dqθ - (Mb urθ + Dbr uθ)
  have hma : N07aWeakCanonicalMixedDerivative S K m (Ma ur) dv 1 0 := by
    simpa only [add_sub_cancel_right] using hqr.sub hbr
  let urr := Mi dv + Dir (Ma ur)
  have hurr : N07aWeakCanonicalMixedDerivative S K m ur urr 1 0 := by
    have hprod := n07aC1Multiplier_weak_product hχ hχp A hχA 0 hma
    rw [n07aC1Multiplier_inverse ha hχ A A haA hχA hinv] at hprod
    exact hprod
  refine ⟨hurr, ?_, ?_⟩
  · exact hr.comp hurr
  have hnonneg : 0 ≤ A := le_trans zero_le_one hA
  have hdq : ‖dqθ‖ ≤ A * (‖urθ‖ + ‖ur‖ + ‖uθθ‖ + ‖uθ‖) := by
    calc
      _ ≤ (‖Mb urθ‖ + ‖Dbθ ur‖) + (‖Mc uθθ‖ + ‖Dcθ uθ‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ ≤ (A * ‖urθ‖ + A * ‖ur‖) + (A * ‖uθθ‖ + A * ‖uθ‖) :=
        add_le_add
          (add_le_add (n07aC1Multiplier_norm_le b hb A hbA urθ)
            (n07aC1DerivativeMultiplier_norm_le b hb A hbA 1 ur))
          (add_le_add (n07aC1Multiplier_norm_le c hc A hcA uθθ)
            (n07aC1DerivativeMultiplier_norm_le c hc A hcA 1 uθ))
      _ = _ := by ring
  have hdbr : ‖Mb urθ + Dbr uθ‖ ≤ A * (‖urθ‖ + ‖uθ‖) := by
    calc
      _ ≤ ‖Mb urθ‖ + ‖Dbr uθ‖ := norm_add_le _ _
      _ ≤ A * ‖urθ‖ + A * ‖uθ‖ :=
        add_le_add (n07aC1Multiplier_norm_le b hb A hbA urθ)
          (n07aC1DerivativeMultiplier_norm_le b hb A hbA 0 uθ)
      _ = _ := by ring
  have hdv : ‖dv‖ ≤ ‖F‖ + A * (‖urθ‖ + ‖ur‖ + ‖uθθ‖ + ‖uθ‖) +
      A * (‖urθ‖ + ‖uθ‖) := by
    calc
      _ ≤ ‖F - dqθ‖ + ‖Mb urθ + Dbr uθ‖ := norm_sub_le _ _
      _ ≤ (‖F‖ + ‖dqθ‖) + ‖Mb urθ + Dbr uθ‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add le_rfl hdq) hdbr
  have hMa : ‖Ma ur‖ ≤ A * ‖ur‖ := n07aC1Multiplier_norm_le a ha A haA ur
  calc
    ‖urr‖ ≤ ‖Mi dv‖ + ‖Dir (Ma ur)‖ := norm_add_le _ _
    _ ≤ A * ‖dv‖ + A * ‖Ma ur‖ :=
      add_le_add (n07aC1Multiplier_norm_le χ hχ A hχA dv)
        (n07aC1DerivativeMultiplier_norm_le χ hχ A hχA 0 (Ma ur))
    _ ≤ A * (‖F‖ + A * (‖urθ‖ + ‖ur‖ + ‖uθθ‖ + ‖uθ‖) +
        A * (‖urθ‖ + ‖uθ‖)) + A * (A * ‖ur‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hdv hnonneg)
        (mul_le_mul_of_nonneg_left hMa hnonneg)
    _ ≤ _ := by
      have hAF : A * ‖F‖ ≤ A ^ 2 * ‖F‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg F)
        nlinarith
      nlinarith [mul_nonneg (sq_nonneg A) (norm_nonneg F),
        mul_nonneg (sq_nonneg A) (norm_nonneg uθθ)]

end ContinuousFlexibility.Analysis
