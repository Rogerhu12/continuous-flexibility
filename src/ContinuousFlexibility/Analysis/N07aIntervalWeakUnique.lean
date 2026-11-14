module

public import ContinuousFlexibility.Analysis.N07aCanonicalUnitModes

/-!
# Uniqueness and scalar normalization of actual interval derivatives

Weak derivatives are determined as L² classes by compact interior tests.
The normalization statements distinguish pointwise scalar multiplication
from scalar multiplication of the prescribed L² quotient.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

theorem n07a_intervalWeakDerivative_unique {u : ℝ → ℝ} {d e : N07aIntervalL2}
    (hd : HasIntervalWeakDerivative 0 1 u d)
    (he : HasIntervalWeakDerivative 0 1 u e) : d = e := by
  have hdloc : LocallyIntegrableOn (d : ℝ → ℝ) (Ioo (0 : ℝ) 1) :=
    IntegrableOn.locallyIntegrableOn ((Lp.memLp d).integrable (by norm_num))
  have heloc : LocallyIntegrableOn (e : ℝ → ℝ) (Ioo (0 : ℝ) 1) :=
    IntegrableOn.locallyIntegrableOn ((Lp.memLp e).integrable (by norm_num))
  have hz : ∀ᵐ x ∂volume, x ∈ Ioo (0 : ℝ) 1 → d x - e x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hdloc.sub heloc)
    intro φ hφ hc hs
    have hid := interval_integrable_mul_test hdloc hφ.continuous hc hs
    have hie := interval_integrable_mul_test heloc hφ.continuous hc hs
    have hdφ := hd φ hφ hc hs
    have heφ := he φ hφ hc hs
    simp only [Pi.sub_apply, smul_eq_mul]
    have hswap : (fun x => φ x * (d x - e x)) = fun x => d x * φ x - e x * φ x := by
      funext x
      ring
    rw [hswap, integral_sub hid hie]
    linarith only [hdφ, heφ]
  apply Lp.ext
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mpr hz] with x hx
  exact sub_eq_zero.mp hx

theorem n07a_intervalWeakDerivative_const_mul {u d : ℝ → ℝ}
    (hd : HasIntervalWeakDerivative 0 1 u d) (c : ℝ) :
    HasIntervalWeakDerivative 0 1 (fun x => c * u x) (fun x => c * d x) := by
  intro φ hφ hc hs
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hd φ hφ hc hs]
  ring

theorem n07a_intervalWeakDerivative_smul {u d : N07aIntervalL2}
    (hd : HasIntervalWeakDerivative 0 1 u d) (c : ℝ) :
    HasIntervalWeakDerivative 0 1 ((c • u : N07aIntervalL2) : ℝ → ℝ)
      ((c • d : N07aIntervalL2) : ℝ → ℝ) := by
  apply n07a_intervalWeakDerivative_congr (Lp.coeFn_smul c u).symm (Lp.coeFn_smul c d).symm
  exact n07a_intervalWeakDerivative_const_mul hd c

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07aCanonicalUnitMode_firstNormal_class (hm : K.left m < K.right m)
    {u d : CanonicalL2 S K m}
    (hd : N07aWeakCanonicalMixedDerivative S K m u d 1 0) (n : ℕ) :
    HasIntervalWeakDerivative 0 1 (n07aCanonicalUnitMode hm u n)
      (((K.right m - K.left m) • n07aCanonicalUnitMode hm d n : N07aIntervalL2) : ℝ → ℝ) := by
  apply n07a_intervalWeakDerivative_congr (EventuallyEq.refl _ _)
    (Lp.coeFn_smul (K.right m - K.left m) (n07aCanonicalUnitMode hm d n)).symm
  exact n07aCanonicalUnitMode_firstNormal hm hd n

theorem n07aCanonicalUnitMode_secondNormal_class (hm : K.left m < K.right m)
    {ur urr : CanonicalL2 S K m}
    (hd : N07aWeakCanonicalMixedDerivative S K m ur urr 1 0) (n : ℕ) :
    HasIntervalWeakDerivative 0 1
      (((K.right m - K.left m) • n07aCanonicalUnitMode hm ur n : N07aIntervalL2) : ℝ → ℝ)
      (((K.right m - K.left m) ^ 2 • n07aCanonicalUnitMode hm urr n : N07aIntervalL2) : ℝ → ℝ) := by
  have h := n07a_intervalWeakDerivative_smul (n07aCanonicalUnitMode_firstNormal_class hm hd n)
    (K.right m - K.left m)
  simpa only [smul_smul, ← pow_two] using h

end ContinuousFlexibility.Analysis
