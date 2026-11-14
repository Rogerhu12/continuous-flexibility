module

public import ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficients

/-!
# Genuine physical interior coefficients on a compact inner strip

Interior smoothness on the actual annulus supplies bounded jets on every
strictly smaller closed radial interval. This constructs the open
coefficient record from the real function, without extending it across
an endpoint or assuming a regularity statement about a solution.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {D : ReferenceData} {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

def n07aInteriorCoefficient {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hfp : ∀ p ∈ annularOpen D, f (p + (0, Real.pi)) = f p)
    (hinner : Icc (K.left m) (K.right m) ⊆ Ioo D.a D.b) :
    N07aCanonicalOpenCoefficient S K m where
  value := f
  smooth := hf.mono fun _ hp => ⟨hinner (Ioo_subset_Icc_self hp.1), mem_univ _⟩
  periodic := fun _ hp => hfp _ ⟨hinner (Ioo_subset_Icc_self hp.1), mem_univ _⟩
  bounded := by
    intro a b
    let Q := Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi
    have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
    have hQsub : Q ⊆ annularOpen D := fun _ hp => ⟨hinner hp.1, mem_univ _⟩
    have hd := contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hf a b
    obtain ⟨B, hB⟩ := hQ.bddAbove_image (hd.continuousOn.abs.mono hQsub)
    refine ⟨max 0 B, le_max_left _ _, ?_⟩
    have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
        p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
    filter_upwards [hmem] with p hp
    exact (hB ⟨p, ⟨Ioo_subset_Icc_self hp.1, Ioc_subset_Icc_self hp.2⟩, rfl⟩).trans
      (le_max_right _ _)

@[simp] theorem n07aInteriorCoefficient_value {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hfp : ∀ p ∈ annularOpen D, f (p + (0, Real.pi)) = f p)
    (hinner : Icc (K.left m) (K.right m) ⊆ Ioo D.a D.b) :
    (n07aInteriorCoefficient (S := S) hf hfp hinner).value = f := rfl

/-- The inverse is the actual reciprocal function on the same physical
strip; its bounded jets follow from interior nonvanishing and compactness. -/
def n07aInteriorReciprocal {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hfp : ∀ p ∈ annularOpen D, f (p + (0, Real.pi)) = f p)
    (hne : ∀ p ∈ annularOpen D, f p ≠ 0)
    (hinner : Icc (K.left m) (K.right m) ⊆ Ioo D.a D.b) :
    N07aCanonicalOpenCoefficient S K m :=
  n07aInteriorCoefficient (hf.inv hne)
    (fun p hp => congrArg Inv.inv (hfp p hp)) hinner

theorem n07aInteriorReciprocal_mul_value {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hfp : ∀ p ∈ annularOpen D, f (p + (0, Real.pi)) = f p)
    (hne : ∀ p ∈ annularOpen D, f p ≠ 0)
    (hinner : Icc (K.left m) (K.right m) ⊆ Ioo D.a D.b) :
    ∀ᵐ p ∂canonicalMeasure S K m,
      (n07aInteriorReciprocal (S := S) hf hfp hne hinner).value p *
        (n07aInteriorCoefficient (S := S) hf hfp hinner).value p = 1 := by
  filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
  exact inv_mul_cancel₀ (hne p ⟨hinner (Ioo_subset_Icc_self hp.1), mem_univ _⟩)

end ContinuousFlexibility.Analysis
