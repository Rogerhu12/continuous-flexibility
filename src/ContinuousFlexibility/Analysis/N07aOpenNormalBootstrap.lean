import ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficients
import ContinuousFlexibility.Analysis.N07aWeakNormalBootstrap

/-!
# Weak normal bootstrap for the actual open-piece coefficients

The original divergence equation and a reciprocal leading coefficient
recover the second weak normal derivative. The bounded interior jet
algebra then recovers every mixed order, including the potential term.
Neither the unknown nor the coefficients are presumed smooth across a
piece endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem N07aCanonicalOpenCoefficient.mul_inverse
    (a ρ : N07aCanonicalOpenCoefficient S K m)
    (hinv : ∀ᵐ p ∂canonicalMeasure S K m, ρ.value p * a.value p = 1)
    (u : CanonicalL2 S K m) : ρ.mul (a.mul u) = u := by
  apply Lp.ext
  filter_upwards [ρ.mul_ae (a.mul u), a.mul_ae u, hinv] with p hρ ha hi
  rw [hρ, ha, ← mul_assoc, hi, one_mul]

def n07aOpenSecondNormalRhs (a b c ρ : N07aCanonicalOpenCoefficient S K m)
    (F ur uθ urθ uθθ : CanonicalL2 S K m) : CanonicalL2 S K m :=
  ρ.mul (F - ((b.mul urθ + (b.jet 0 1).mul ur) +
      (c.mul uθθ + (c.jet 0 1).mul uθ)) -
        (b.mul urθ + (b.jet 1 0).mul uθ)) + (ρ.jet 1 0).mul (a.mul ur)

theorem n07a_openWeak_secondNormal
    (a b c ρ : N07aCanonicalOpenCoefficient S K m)
    (hinv : ∀ᵐ p ∂canonicalMeasure S K m, ρ.value p * a.value p = 1)
    {u ur uθ urθ uθθ F : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1)
    (hflux : N07aCanonicalFluxEquation S K m F
      (a.mul ur + b.mul uθ) (b.mul ur + c.mul uθ)) :
    N07aWeakCanonicalMixedDerivative S K m ur
      (n07aOpenSecondNormalRhs a b c ρ F ur uθ urθ uθθ) 1 0 ∧
    N07aWeakCanonicalMixedDerivative S K m u
      (n07aOpenSecondNormalRhs a b c ρ F ur uθ urθ uθθ) 2 0 := by
  have hbθ : N07aWeakCanonicalMixedDerivative S K m (b.mul ur)
      (b.mul urθ + (b.jet 0 1).mul ur) 0 1 := b.first_product 1 hrθ
  have hcθ : N07aWeakCanonicalMixedDerivative S K m (c.mul uθ)
      (c.mul uθθ + (c.jet 0 1).mul uθ) 0 1 := c.first_product 1 hθθ
  let dqθ := (b.mul urθ + (b.jet 0 1).mul ur) +
    (c.mul uθθ + (c.jet 0 1).mul uθ)
  have hqr : N07aWeakCanonicalMixedDerivative S K m
      (a.mul ur + b.mul uθ) (F - dqθ) 1 0 :=
    n07a_weakCanonical_normalFlux hflux (hbθ.add hcθ)
  have hbr : N07aWeakCanonicalMixedDerivative S K m (b.mul uθ)
      (b.mul urθ + (b.jet 1 0).mul uθ) 1 0 :=
    b.first_product 0 (n07a_weakCanonical_crossDerivative hr hθ hrθ)
  let dv := F - dqθ - (b.mul urθ + (b.jet 1 0).mul uθ)
  have hma : N07aWeakCanonicalMixedDerivative S K m (a.mul ur) dv 1 0 := by
    simpa only [add_sub_cancel_right] using hqr.sub hbr
  have hurr : N07aWeakCanonicalMixedDerivative S K m ur
      (n07aOpenSecondNormalRhs a b c ρ F ur uθ urθ uθθ) 1 0 := by
    have hp := ρ.first_product 0 hma
    rw [a.mul_inverse ρ hinv] at hp
    exact hp
  exact ⟨hurr, hr.comp hurr⟩

theorem n07aOpenSecondNormalRhs_normalRegular (n : ℕ)
    (a b c ρ : N07aCanonicalOpenCoefficient S K m)
    {u ur uθ urθ uθθ F : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1)
    (hu : N07aCanonicalNormalRegular S K m u (n + 1))
    (hF : N07aCanonicalNormalRegular S K m F n) :
    N07aCanonicalNormalRegular S K m
      (n07aOpenSecondNormalRhs a b c ρ F ur uθ urθ uθθ) n := by
  have hur : N07aCanonicalNormalRegular S K m ur n := hu.derivative hr
  have huθ : N07aCanonicalNormalRegular S K m uθ n :=
    (hu.mono (Nat.le_succ n)).derivative hθ
  have hurθ : N07aCanonicalNormalRegular S K m urθ n := hu.derivative (hr.comp hrθ)
  have huθθ : N07aCanonicalNormalRegular S K m uθθ n :=
    (hu.mono (Nat.le_succ n)).derivative (hθ.comp hθθ)
  unfold n07aOpenSecondNormalRhs
  have hdq := ((b.normalRegular n _ hurθ).add ((b.jet 0 1).normalRegular n _ hur)).add
    ((c.normalRegular n _ huθθ).add ((c.jet 0 1).normalRegular n _ huθ))
  have hdv := (hF.sub hdq).sub
    ((b.normalRegular n _ hurθ).add ((b.jet 1 0).normalRegular n _ huθ))
  exact (ρ.normalRegular n _ hdv).add
    ((ρ.jet 1 0).normalRegular n _ (a.normalRegular n _ hur))

/-- All genuine weak mixed orders from angular regularity, a first normal
jet, and the original source. The potential is bootstrapped with the unknown. -/
theorem n07a_openWeak_divergenceBootstrap
    (a b c ρ q : N07aCanonicalOpenCoefficient S K m)
    (hinv : ∀ᵐ p ∂canonicalMeasure S K m, ρ.value p * a.value p = 1)
    {u ur uθ urθ uθθ F : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1)
    (hbase : N07aCanonicalNormalRegular S K m u 1)
    (hF : ∀ n, N07aCanonicalNormalRegular S K m F n)
    (hflux : N07aCanonicalFluxEquation S K m (F - q.mul u)
      (a.mul ur + b.mul uθ) (b.mul ur + c.mul uθ)) :
    ∀ n, N07aCanonicalNormalRegular S K m u n := by
  have hsecond := (n07a_openWeak_secondNormal a b c ρ hinv hr hθ hrθ hθθ hflux).2
  apply Nat.twoStepInduction
  · exact hbase.mono (Nat.zero_le _)
  · exact hbase
  · intro n _ hn
    apply n07aCanonicalNormalRegular_of_second hbase hsecond
    apply n07aOpenSecondNormalRhs_normalRegular n a b c ρ hr hθ hrθ hθθ hn
    exact (hF n).sub (q.normalRegular n _ (hn.mono (Nat.le_succ n)))

end ContinuousFlexibility.Analysis
