module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.CylinderTestPairing
public import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets

/-!+# Mixed weak derivatives on the actual canonical pieces

The normal bootstrap uses the same L² representatives and compact radial
tests as the frozen angular graph.  Testing, linear combinations and
composition of derivatives are established before any smooth
representative of the solution is chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

/-- Compact radial support of a canonical test survives every actual
mixed derivative. -/
theorem n07a_canonicalTest_mixedDerivative {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) (a b : ℕ) :
    CanonicalTest S K m (mixedDerivative a b φ) := by
  obtain ⟨hφs, hφp, J, hJ, hJU, hzero⟩ := hφ
  refine ⟨contDiff_mixedDerivative hφs a b, ?_, J, hJ, hJU, ?_⟩
  · have hper (r : ℝ) : Function.Periodic (fun θ => φ (r, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hφp (r, θ)
    rintro ⟨r, θ⟩
    simpa only [Prod.mk_add_mk, add_zero] using
      mixedDerivative_angular_periodic hper a b r θ
  · intro r hr θ
    have hnear : ∀ᶠ t : ℝ in 𝓝 r, t ∉ J := hJ.isClosed.isOpen_compl.mem_nhds hr
    have he : (fun t => iteratedDeriv b (fun u => φ (t, u)) θ) =ᶠ[𝓝 r]
        (0 : ℝ → ℝ) := by
      filter_upwards [hnear] with t ht
      have hz : (fun u => φ (t, u)) = (0 : ℝ → ℝ) := funext (hzero t ht)
      simp only [hz, iteratedDeriv_const_zero, Pi.zero_apply]
    simpa only [mixedDerivative, iteratedDeriv_const_zero, Pi.zero_apply] using
      he.iteratedDeriv_eq a

theorem n07a_canonicalTest_mul {φ χ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) (hχ : ContDiff ℝ ∞ χ)
    (hχp : Function.Periodic χ (0, Real.pi)) :
    CanonicalTest S K m (fun p => χ p * φ p) := by
  obtain ⟨hφs, hφp, J, hJ, hJU, hzero⟩ := hφ
  refine ⟨hχ.mul hφs, hχp.mul hφp, J, hJ, hJU, ?_⟩
  intro r hr θ
  simp only [hzero r hr θ, mul_zero]

theorem n07a_canonicalMeasure_finite (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) : IsFiniteMeasure (canonicalMeasure S K m) := by
  constructor
  rw [canonicalMeasure, Measure.restrict_apply_univ]
  exact ((Metric.isBounded_Ioo (K.left m) (K.right m)).prod
    (Metric.isBounded_Ioc (0 : ℝ) Real.pi)).measure_lt_top

theorem n07a_canonicalTest_memLp {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S K m φ) : MemLp φ 2 (canonicalMeasure S K m) := by
  let := n07a_canonicalMeasure_finite S K m
  let Q : Set PolarPoint := Icc (K.left m) (K.right m) ×ˢ Icc 0 Real.pi
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  obtain ⟨A, hA⟩ := hQ.bddAbove_image hφ.1.continuous.norm.continuousOn
  apply MemLp.of_bound hφ.1.continuous.aestronglyMeasurable A
  have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc 0 Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hmem] with p hp
  exact hA ⟨p, ⟨Ioo_subset_Icc_self hp.1, Ioc_subset_Icc_self hp.2⟩, rfl⟩

/-- Evaluation against a canonical test in the prescribed L² space. -/
def n07aCanonicalTestPairing (φ : PolarPoint → ℝ)
    (hφ : MemLp φ 2 (canonicalMeasure S K m)) : CanonicalL2 S K m →L[ℝ] ℝ :=
  innerSL ℝ (hφ.toLp φ)

theorem n07aCanonicalTestPairing_apply (φ : PolarPoint → ℝ)
    (hφ : MemLp φ 2 (canonicalMeasure S K m)) (u : CanonicalL2 S K m) :
    n07aCanonicalTestPairing φ hφ u = ∫ p, u p * φ p ∂canonicalMeasure S K m := by
  change ⟪hφ.toLp φ, u⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hφ] with p hp
  rw [hp]
  simp only [RCLike.inner_apply, conj_trivial]

/-- The actual mixed weak derivative on a fixed canonical piece.  Its
zero-radial case is exactly `WeakCanonicalAngularDerivative`. -/
def N07aWeakCanonicalMixedDerivative (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (f g : CanonicalL2 S K m) (a b : ℕ) : Prop :=
  ∀ φ, CanonicalTest S K m φ →
    (∫ p, g p * φ p ∂canonicalMeasure S K m) =
      (-1 : ℝ) ^ (a + b) *
        ∫ p, f p * mixedDerivative a b φ p ∂canonicalMeasure S K m

theorem n07a_weakCanonicalMixed_zero_radial_iff (f g : CanonicalL2 S K m) (b : ℕ) :
    N07aWeakCanonicalMixedDerivative S K m f g 0 b ↔
      WeakCanonicalAngularDerivative S K m f g b := by
  simp only [N07aWeakCanonicalMixedDerivative, WeakCanonicalAngularDerivative, zero_add]

theorem n07a_weakCanonicalMixed_refl (f : CanonicalL2 S K m) :
    N07aWeakCanonicalMixedDerivative S K m f f 0 0 := by
  intro φ hφ
  simp only [mixedDerivative, iteratedDeriv_zero, zero_add, pow_zero, one_mul]

theorem n07a_weakCanonicalMixed_pairing_iff
    (f g : CanonicalL2 S K m) (a b : ℕ) :
    N07aWeakCanonicalMixedDerivative S K m f g a b ↔
      ∀ φ, ∀ hφ : CanonicalTest S K m φ,
        n07aCanonicalTestPairing φ (n07a_canonicalTest_memLp hφ) g =
          (-1 : ℝ) ^ (a + b) * n07aCanonicalTestPairing (mixedDerivative a b φ)
            (n07a_canonicalTest_memLp (n07a_canonicalTest_mixedDerivative hφ a b)) f := by
  simp only [N07aWeakCanonicalMixedDerivative, n07aCanonicalTestPairing_apply]

theorem N07aWeakCanonicalMixedDerivative.add {f g u v : CanonicalL2 S K m} {a b : ℕ}
    (hfg : N07aWeakCanonicalMixedDerivative S K m f g a b)
    (huv : N07aWeakCanonicalMixedDerivative S K m u v a b) :
    N07aWeakCanonicalMixedDerivative S K m (f + u) (g + v) a b := by
  rw [n07a_weakCanonicalMixed_pairing_iff] at hfg huv ⊢
  intro φ hφ
  rw [map_add, map_add, hfg φ hφ, huv φ hφ, mul_add]

theorem N07aWeakCanonicalMixedDerivative.smul {f g : CanonicalL2 S K m} {a b : ℕ}
    (hfg : N07aWeakCanonicalMixedDerivative S K m f g a b) (c : ℝ) :
    N07aWeakCanonicalMixedDerivative S K m (c • f) (c • g) a b := by
  rw [n07a_weakCanonicalMixed_pairing_iff] at hfg ⊢
  intro φ hφ
  rw [map_smul, map_smul, hfg φ hφ]
  simp only [smul_eq_mul]
  ring

theorem n07a_weakCanonicalMixed_zero (a b : ℕ) :
    N07aWeakCanonicalMixedDerivative S K m 0 0 a b := by
  rw [n07a_weakCanonicalMixed_pairing_iff]
  intro φ hφ
  rw [map_zero, map_zero, mul_zero]

/-- Ordinary mixed derivatives add their orders on the smooth test
function; this does not presuppose smoothness of a weak solution. -/
theorem n07a_mixedDerivative_mixedDerivative {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (a b c d : ℕ) :
    mixedDerivative a b (mixedDerivative c d φ) = mixedDerivative (a + c) (b + d) φ := by
  induction c generalizing a with
  | zero =>
    induction d generalizing b with
    | zero => rw [spaces_mixedDerivative_zero, Nat.add_zero, Nat.add_zero]
    | succ d ih =>
      rw [← angularPartial_mixedDerivative hφ 0 d]
      have he : mixedDerivative a b (angularPartial (mixedDerivative 0 d φ)) =
          mixedDerivative a (b + 1) (mixedDerivative 0 d φ) :=
        funext (fun p => mixedDerivative_angularPartial isOpen_univ
          (contDiff_mixedDerivative hφ 0 d).contDiffOn a b (mem_univ p))
      rw [he, ih]
      congr 1
      omega
  | succ c ih =>
    rw [← radialPartial_mixedDerivative hφ c d]
    have he : mixedDerivative a b (radialPartial (mixedDerivative c d φ)) =
        mixedDerivative (a + 1) b (mixedDerivative c d φ) :=
      funext (fun p => mixedDerivative_radialPartial isOpen_univ
        (contDiff_mixedDerivative hφ c d).contDiffOn a b (mem_univ p))
    rw [he, ih]
    congr 1
    omega

/-- Composition of weak derivatives is justified by differentiating the
test functions, which remain in the same test space. -/
theorem N07aWeakCanonicalMixedDerivative.comp
    {f g h : CanonicalL2 S K m} {a b c d : ℕ}
    (hfg : N07aWeakCanonicalMixedDerivative S K m f g a b)
    (hgh : N07aWeakCanonicalMixedDerivative S K m g h c d) :
    N07aWeakCanonicalMixedDerivative S K m f h (a + c) (b + d) := by
  intro φ hφ
  rw [hgh φ hφ, hfg (mixedDerivative c d φ)
    (n07a_canonicalTest_mixedDerivative hφ c d),
    n07a_mixedDerivative_mixedDerivative hφ.1]
  rw [← mul_assoc, ← pow_add]
  congr 2
  omega

end ContinuousFlexibility.Analysis
