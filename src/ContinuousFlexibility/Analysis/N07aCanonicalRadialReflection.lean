module

public import ContinuousFlexibility.Analysis.N07aAngularEven
public import ContinuousFlexibility.Analysis.N07aCanonicalWeakJets

/-!
# Radial weak derivatives retain the actual angular reflection

Reflection is transferred through the original compact test identity and
the measure-preserving change of angular variable. No pointwise derivative
of the L² representative is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonicalTest_reflected {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) :
    CanonicalTest S K m (fun p => φ (p.1, Real.pi - p.2)) := by
  obtain ⟨hs, hp, J, hJ, hJU, hz⟩ := hφ
  refine ⟨hs.comp (contDiff_fst.prodMk (contDiff_const.sub contDiff_snd)),
    ?_, J, hJ, hJU, ?_⟩
  · rintro ⟨r, θ⟩
    have hper : φ (r, -θ + Real.pi) = φ (r, -θ) := by
      simpa only [Prod.mk_add_mk, add_zero] using hp (r, -θ)
    simp only [Prod.mk_add_mk, add_zero]
    rw [show Real.pi - (θ + Real.pi) = -θ by ring,
      show Real.pi - θ = -θ + Real.pi by ring, hper]
  · intro r hr θ
    exact hz r hr (Real.pi - θ)

theorem n07aCanonicalReflection_pairing (u : CanonicalL2 S K m) (φ : PolarPoint → ℝ)
    (hφ : MemLp φ 2 (canonicalMeasure S K m)) :
    (∫ p, n07aAngularReflection m u p * φ p ∂canonicalMeasure S K m) =
      ∫ p, u p * φ (p.1, Real.pi - p.2) ∂canonicalMeasure S K m := by
  have hpres := n07aAngularReflection_preserving (S := S) (K := K) m
  have hφmap : MemLp φ 2 (Measure.map cylinderAngularReflection (canonicalMeasure S K m)) := by
    rw [hpres.map_eq]
    exact hφ
  have hφref := hφmap.comp_of_map hpres.measurable.aemeasurable
  let H : PolarPoint → ℝ := fun p => u p * φ (cylinderAngularReflection p)
  have hH : Integrable H (canonicalMeasure S K m) := (Lp.memLp u).integrable_mul hφref
  have hHm : AEStronglyMeasurable H
      (Measure.map cylinderAngularReflection (canonicalMeasure S K m)) := by
    rw [hpres.map_eq]
    exact hH.aestronglyMeasurable
  have hmap := integral_map hpres.measurable.aemeasurable hHm
  rw [hpres.map_eq] at hmap
  calc
    _ = ∫ p, u (p.1, Real.pi - p.2) * φ p ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      exact (n07aAngularReflection_ae m u).mono fun p hp => congrArg (· * φ p) hp
    _ = ∫ p, H (cylinderAngularReflection p) ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        simp only [H, cylinderAngularReflection, sub_sub_cancel]
    _ = _ := hmap.symm

theorem n07a_weakCanonical_radial_reflection (hm : K.left m < K.right m)
    {u d : CanonicalL2 S K m} {a : ℕ}
    (hu : n07aAngularReflection m u = u)
    (hd : N07aWeakCanonicalMixedDerivative S K m u d a 0) :
    n07aAngularReflection m d = d := by
  have hzero : WeakCanonicalAngularDerivative S K m d (n07aAngularReflection m d) 0 := by
    intro φ hφ
    rw [pow_zero, one_mul, spaces_mixedDerivative_zero]
    let ψ := fun p : PolarPoint => φ (p.1, Real.pi - p.2)
    have hψ : CanonicalTest S K m ψ := n07a_canonicalTest_reflected hφ
    have hder : mixedDerivative a 0 ψ = fun p => mixedDerivative a 0 φ (p.1, Real.pi - p.2) := by
      funext p
      simp only [ψ, spaces_mixedDerivative_reflection, pow_zero, one_mul]
    have hp := n07aCanonicalReflection_pairing u (mixedDerivative a 0 φ)
      (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hφ a 0))
    rw [hu] at hp
    calc
      _ = ∫ p, d p * ψ p ∂canonicalMeasure S K m :=
        n07aCanonicalReflection_pairing d φ (n07a_canonicalTest_memLp hφ)
      _ = (-1 : ℝ) ^ (a + 0) * ∫ p, u p * mixedDerivative a 0 ψ p
          ∂canonicalMeasure S K m := hd ψ hψ
      _ = (-1 : ℝ) ^ (a + 0) * ∫ p, u p * mixedDerivative a 0 φ p
          ∂canonicalMeasure S K m := by rw [hder, ← hp]
      _ = _ := (hd φ hφ).symm
  exact n07aAngularWeak_unique m hm hzero
    ((n07a_weakCanonicalMixed_zero_radial_iff d d 0).mp (n07a_weakCanonicalMixed_refl d))

end ContinuousFlexibility.Analysis
