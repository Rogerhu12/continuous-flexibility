module

public import ContinuousFlexibility.Analysis.N07aAngularEven
public import ContinuousFlexibility.Analysis.N07aCanonicalWeakJets

/-!
# Even compact tests separate the actual even canonical L² classes

Reflection preserves the prescribed half-period measure. Averaging a
canonical test with its reflection therefore preserves its pairing with
an even L² class. The already proved full test separation then applies.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonicalTest_even {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) :
    CanonicalTest S K m (spacesCylinderEvenFunction φ) := by
  obtain ⟨hs, hp, J, hJ, hJU, hz⟩ := hφ
  refine ⟨spacesCylinderEvenFunction_contDiff hs,
    spacesCylinderEvenFunction_periodic hp, J, hJ, hJU, ?_⟩
  intro r hr θ
  simp only [spacesCylinderEvenFunction, hz r hr θ, hz r hr (Real.pi - θ),
    add_zero, mul_zero]

theorem n07a_canonicalTest_even_reflect {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) (r θ : ℝ) :
    spacesCylinderEvenFunction φ (r, -θ) = spacesCylinderEvenFunction φ (r, θ) := by
  have hp := spacesCylinderEvenFunction_periodic hφ.2.1 (r, -θ)
  have hr := spacesCylinderEvenFunction_reflection φ (r, θ)
  have he : (r, -θ) + (0, Real.pi) = (r, Real.pi - θ) := by
    apply Prod.ext
    · simp only [Prod.fst_add, add_zero]
    · simp only [Prod.snd_add]
      ring
  rw [he] at hp
  exact hp.symm.trans hr

theorem n07a_canonical_even_pairing {u : CanonicalL2 S K m}
    (hu : n07aAngularReflection m u = u) {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) :
    (∫ p, u p * spacesCylinderEvenFunction φ p ∂canonicalMeasure S K m) =
      ∫ p, u p * φ p ∂canonicalMeasure S K m := by
  have hpres := n07aAngularReflection_preserving (S := S) (K := K) m
  have href := (n07aAngularReflection_fixed_iff m u).mp hu
  have hφLp := n07a_canonicalTest_memLp hφ
  have hφmap : MemLp φ 2 (Measure.map cylinderAngularReflection (canonicalMeasure S K m)) := by
    rw [hpres.map_eq]
    exact hφLp
  have hφref := hφmap.comp_of_map hpres.measurable.aemeasurable
  have hprod := (Lp.memLp u).integrable_mul hφLp
  have hprodref := (Lp.memLp u).integrable_mul hφref
  have hFm : AEStronglyMeasurable (fun p => u p * φ p)
      (Measure.map cylinderAngularReflection (canonicalMeasure S K m)) := by
    rw [hpres.map_eq]
    exact hprod.aestronglyMeasurable
  have hmap := integral_map hpres.measurable.aemeasurable hFm
  rw [hpres.map_eq] at hmap
  have hr : (∫ p, u p * φ (p.1, Real.pi - p.2) ∂canonicalMeasure S K m) =
      ∫ p, u p * φ p ∂canonicalMeasure S K m := by
    calc
      _ = ∫ p, u (cylinderAngularReflection p) * φ (cylinderAngularReflection p)
          ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [href] with p hp
        exact congrArg (· * φ (p.1, Real.pi - p.2)) hp.symm
      _ = _ := hmap.symm
  calc
    _ = ∫ p, (1 / 2 : ℝ) * (u p * φ p + u p * φ (p.1, Real.pi - p.2))
        ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [spacesCylinderEvenFunction]
      ring
    _ = (1 / 2 : ℝ) * ((∫ p, u p * φ p ∂canonicalMeasure S K m) +
        ∫ p, u p * φ (p.1, Real.pi - p.2) ∂canonicalMeasure S K m) := by
      rw [integral_const_mul]
      exact congrArg ((1 / 2 : ℝ) * ·) (integral_add hprod hprodref)
    _ = _ := by rw [hr]; ring

/-- No Fourier coefficient or density assumption is added: the actual even
canonical classes are determined by their compact even test pairings. -/
theorem n07a_canonical_even_test_separation (hm : K.left m < K.right m)
    {u v : CanonicalL2 S K m}
    (hu : n07aAngularReflection m u = u) (hv : n07aAngularReflection m v = v)
    (heq : ∀ φ, CanonicalTest S K m φ →
      (∀ r θ, φ (r, -θ) = φ (r, θ)) →
      (∫ p, u p * φ p ∂canonicalMeasure S K m) =
        ∫ p, v p * φ p ∂canonicalMeasure S K m) : u = v := by
  have hpair (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ) :
      (∫ p, u p * φ p ∂canonicalMeasure S K m) =
        ∫ p, v p * φ p ∂canonicalMeasure S K m :=
    (n07a_canonical_even_pairing hu hφ).symm.trans
      ((heq _ (n07a_canonicalTest_even hφ) (n07a_canonicalTest_even_reflect hφ)).trans
        (n07a_canonical_even_pairing hv hφ))
  apply n07aAngularWeak_unique m hm (f := u) (k := 0)
  · intro φ hφ
    simp only [pow_zero, one_mul, spaces_mixedDerivative_zero]
  · intro φ hφ
    simpa only [pow_zero, one_mul, spaces_mixedDerivative_zero] using (hpair φ hφ).symm

end ContinuousFlexibility.Analysis
