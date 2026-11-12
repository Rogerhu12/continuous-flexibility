import ContinuousFlexibility.Analysis.N07aOpenStripPointwiseL2
import ContinuousFlexibility.Analysis.N07aCanonicalGreenPairing

/-!
# Pointwise mixed jets from the actual mixed L² jets
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonicalOpen_mixed_pointwise_L2
    (hm : K.left m < K.right m) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hper : ∀ x ∈ canonicalOpen S K m, f (x + (0, Real.pi)) = f x)
    (hmem : ∀ a b, MemLp (mixedDerivative a b f) 2 (canonicalMeasure S K m))
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    |mixedDerivative a b f p| ≤ (1 + 2 * (K.right m - K.left m)⁻¹) *
      Real.sqrt (Real.pi * (K.right m - K.left m)) *
        ((eLpNorm (mixedDerivative a b f) 2 (canonicalMeasure S K m)).toReal +
          (eLpNorm (mixedDerivative (a + 1) b f) 2 (canonicalMeasure S K m)).toReal +
          (eLpNorm (mixedDerivative a (b + 1) f) 2 (canonicalMeasure S K m)).toReal +
          (eLpNorm (mixedDerivative (a + 1) (b + 1) f) 2
            (canonicalMeasure S K m)).toReal) := by
  let g := mixedDerivative a b f
  have hU : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hg : ContDiffOn ℝ ∞ g (canonicalOpen S K m) := contDiffOn_mixedDerivative hU hf a b
  have hgr : EqOn (radialPartial g) (mixedDerivative (a + 1) b f)
      (canonicalOpen S K m) := fun _ hq => n07a_radialPartial_mixedDerivative_on hU hf a b hq
  have hgt : EqOn (angularPartial g) (mixedDerivative a (b + 1) f)
      (canonicalOpen S K m) := by
    intro q hq
    rw [n07a_open_angularPartial_eq hg hq,
      n07a_mixedDerivative_mixedDerivative_on hU hf 0 1 a b hq]
    simp only [Nat.zero_add, Nat.add_comm 1 b]
  have hgrt : EqOn (radialPartial (angularPartial g))
      (mixedDerivative (a + 1) (b + 1) f) (canonicalOpen S K m) := by
    intro q hq
    have hθg : ContDiffOn ℝ ∞ (angularPartial g) (canonicalOpen S K m) :=
      (hg.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    rw [n07a_open_radialPartial_eq hθg hq,
      n07a_mixedDerivative_eqOn hU hgt 1 0 hq,
      n07a_mixedDerivative_mixedDerivative_on hU hf 1 0 a (b + 1) hq]
    simp only [Nat.zero_add, Nat.add_comm 1 a]
  have hr : radialPartial g =ᵐ[canonicalMeasure S K m] mixedDerivative (a + 1) b f :=
    n07a_canonicalOpen_ae.mono (fun _ hq => hgr hq)
  have ht : angularPartial g =ᵐ[canonicalMeasure S K m] mixedDerivative a (b + 1) f :=
    n07a_canonicalOpen_ae.mono (fun _ hq => hgt hq)
  have hrt : radialPartial (angularPartial g) =ᵐ[canonicalMeasure S K m]
      mixedDerivative (a + 1) (b + 1) f :=
    n07a_canonicalOpen_ae.mono (fun _ hq => hgrt hq)
  have hgp : ∀ x ∈ Ioo (K.left m) (K.right m),
      Function.Periodic (fun θ => g (x, θ)) Real.pi := by
    intro x hx θ
    simpa only [Prod.mk_add_mk, add_zero] using
      n07a_mixedDerivative_periodic_on hper a b (x, θ) ⟨hx, mem_univ _⟩
  have h := n07a_canonicalOpen_pointwise_L2 hm hg hgp (hmem a b)
    ((memLp_congr_ae hr).mpr (hmem (a + 1) b))
    ((memLp_congr_ae ht).mpr (hmem a (b + 1)))
    ((memLp_congr_ae hrt).mpr (hmem (a + 1) (b + 1))) hp
  rw [eLpNorm_congr_ae hr, eLpNorm_congr_ae ht, eLpNorm_congr_ae hrt] at h
  exact h

end ContinuousFlexibility.Analysis
