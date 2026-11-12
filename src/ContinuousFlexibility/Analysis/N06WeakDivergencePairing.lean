import ContinuousFlexibility.Analysis.N06WeakFiniteCalculus

/-!
# The genuine symmetric divergence pairing for an actual weak H2 row

The two first and three second fields satisfy actual distributional
partial identities. Twice applying those identities, with coefficients
smooth only on the open strip, gives the original symmetric divergence
operator on every original test.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def n06WeakDivergenceExpression (L : SymmetricCoefficients)
    (Ur Ut Urr Urt Utt : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  (L.a p * Urr p + radialPartial L.a p * Ur p) +
    (L.b p * Urt p + angularPartial L.b p * Ur p) +
    (L.b p * Urt p + radialPartial L.b p * Ut p) +
    (L.c p * Utt p + angularPartial L.c p * Ut p)

private theorem n06_integral_four {μ : Measure PolarPoint}
    {f g h j : PolarPoint → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) (hj : Integrable j μ) :
    (∫ p, f p + g p + h p + j p ∂μ) =
      (∫ p, f p ∂μ) + (∫ p, g p ∂μ) + (∫ p, h p ∂μ) + ∫ p, j p ∂μ := by
  have hfg : Integrable (fun p => f p + g p) μ := hf.add hg
  have hfgh : Integrable (fun p => f p + g p + h p) μ := hfg.add hh
  calc
    _ = (∫ p, f p + g p + h p ∂μ) + ∫ p, j p ∂μ := integral_add hfgh hj
    _ = ((∫ p, f p + g p ∂μ) + ∫ p, h p ∂μ) + ∫ p, j p ∂μ :=
      congrArg (fun z : ℝ => z + ∫ p, j p ∂μ) (integral_add hfg hh)
    _ = _ := congrArg (fun z : ℝ => (z + ∫ p, h p ∂μ) + ∫ p, j p ∂μ)
      (integral_add hf hg)

private theorem n06_integrable_weak_product_test
    {f g a da φ : PolarPoint → ℝ}
    (hf : MemLp f 2 (cylinderWindowMeasure 0))
    (hg : MemLp g 2 (cylinderWindowMeasure 0)) (hφ : n06UnitCanonicalTest φ)
    (ha : ContDiffOn ℝ ∞ a (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hda : ContDiffOn ℝ ∞ da (Ioo (0 : ℝ) 1 ×ˢ univ)) :
    Integrable (fun p => (a p * g p + da p * f p) * φ p) (cylinderWindowMeasure 0) := by
  have hI := (n06_unit_integrable_mul_local_test hg hφ ha).add
    (n06_unit_integrable_mul_local_test hf hφ hda)
  apply hI.congr
  filter_upwards with p
  change g p * (a p * φ p) + f p * (da p * φ p) = (a p * g p + da p * f p) * φ p
  ring

/-- The formal operator in the test is the actual `divergenceOperator`.
The right side uses the actual weak fields, with no smooth source assumption. -/
theorem n06_unit_weak_divergence_pairing
    {U Ur Ut Urr Urt Utt φ : PolarPoint → ℝ}
    (hrow : N06UnitWeakH2Row U Ur Ut Urr Urt Utt)
    (L : SymmetricCoefficients)
    (ha : ContDiffOn ℝ ∞ L.a (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ L.b (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hc : ContDiffOn ℝ ∞ L.c (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hpa : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), L.a (p + (0, Real.pi)) = L.a p)
    (hpb : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), L.b (p + (0, Real.pi)) = L.b p)
    (hpc : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), L.c (p + (0, Real.pi)) = L.c p)
    (hφ : n06UnitCanonicalTest φ) :
    (∫ p, U p * divergenceOperator L φ p ∂cylinderWindowMeasure 0) =
      ∫ p, n06WeakDivergenceExpression L Ur Ut Urr Urt Utt p * φ p
        ∂cylinderWindowMeasure 0 := by
  let F₁ := radialPartial (fun p => L.a p * radialPartial φ p)
  let F₂ := radialPartial (fun p => L.b p * angularPartial φ p)
  let F₃ := angularPartial (fun p => L.b p * radialPartial φ p)
  let F₄ := angularPartial (fun p => L.c p * angularPartial φ p)
  let Q₁ : PolarPoint → ℝ := fun p => L.a p * Urr p + radialPartial L.a p * Ur p
  let Q₂ : PolarPoint → ℝ := fun p => L.b p * Urt p + angularPartial L.b p * Ur p
  let Q₃ : PolarPoint → ℝ := fun p => L.b p * Urt p + radialPartial L.b p * Ut p
  let Q₄ : PolarPoint → ℝ := fun p => L.c p * Utt p + angularPartial L.c p * Ut p
  have hT₁ := hφ.n06_radialPartial.n06_mul_left_of_contDiffOn ha hpa
  have hT₂ := hφ.n06_angularPartial.n06_mul_left_of_contDiffOn hb hpb
  have hT₃ := hφ.n06_radialPartial.n06_mul_left_of_contDiffOn hb hpb
  have hT₄ := hφ.n06_angularPartial.n06_mul_left_of_contDiffOn hc hpc
  have hF₁ : Integrable (fun p => U p * F₁ p) (cylinderWindowMeasure 0) :=
    hrow.value_memLp.integrable_mul hT₁.n06_radialPartial.n06_memLp
  have hF₂ : Integrable (fun p => U p * F₂ p) (cylinderWindowMeasure 0) :=
    hrow.value_memLp.integrable_mul hT₂.n06_radialPartial.n06_memLp
  have hF₃ : Integrable (fun p => U p * F₃ p) (cylinderWindowMeasure 0) :=
    hrow.value_memLp.integrable_mul hT₃.n06_angularPartial.n06_memLp
  have hF₄ : Integrable (fun p => U p * F₄ p) (cylinderWindowMeasure 0) :=
    hrow.value_memLp.integrable_mul hT₄.n06_angularPartial.n06_memLp
  have hQ₁ : Integrable (fun p => Q₁ p * φ p) (cylinderWindowMeasure 0) :=
    n06_integrable_weak_product_test hrow.radial_memLp hrow.radial_radial_memLp hφ ha
      (scalar_contDiffOn_radialPartial (isOpen_Ioo.prod isOpen_univ) ha)
  have hQ₂ : Integrable (fun p => Q₂ p * φ p) (cylinderWindowMeasure 0) :=
    n06_integrable_weak_product_test hrow.radial_memLp hrow.radial_angular_memLp hφ hb
      (scalar_contDiffOn_angularPartial (isOpen_Ioo.prod isOpen_univ) hb)
  have hQ₃ : Integrable (fun p => Q₃ p * φ p) (cylinderWindowMeasure 0) :=
    n06_integrable_weak_product_test hrow.angular_memLp hrow.radial_angular_memLp hφ hb
      (scalar_contDiffOn_radialPartial (isOpen_Ioo.prod isOpen_univ) hb)
  have hQ₄ : Integrable (fun p => Q₄ p * φ p) (cylinderWindowMeasure 0) :=
    n06_integrable_weak_product_test hrow.angular_memLp hrow.angular_angular_memLp hφ hc
      (scalar_contDiffOn_angularPartial (isOpen_Ioo.prod isOpen_univ) hc)
  have hswap (f a ψ : PolarPoint → ℝ) :
      (∫ p, f p * (a p * ψ p) ∂cylinderWindowMeasure 0) =
        ∫ p, (a p * f p) * ψ p ∂cylinderWindowMeasure 0 := by
    apply integral_congr_ae
    filter_upwards with p
    ring
  have h₁ : (∫ p, U p * F₁ p ∂cylinderWindowMeasure 0) =
      ∫ p, Q₁ p * φ p ∂cylinderWindowMeasure 0 := by
    have hfirst := hrow.radial _ hT₁
    rw [hswap Ur L.a (radialPartial φ)] at hfirst
    have hsecond := n06_unit_weak_radial_product_pairing hrow.radial_radial
      hrow.radial_memLp hrow.radial_radial_memLp ha hpa hφ
    change (∫ p, Q₁ p * φ p ∂cylinderWindowMeasure 0) = _ at hsecond
    change (∫ p, (L.a p * Ur p) * radialPartial φ p ∂cylinderWindowMeasure 0) =
      -(∫ p, U p * F₁ p ∂cylinderWindowMeasure 0) at hfirst
    linarith only [hfirst, hsecond]
  have h₂ : (∫ p, U p * F₂ p ∂cylinderWindowMeasure 0) =
      ∫ p, Q₂ p * φ p ∂cylinderWindowMeasure 0 := by
    have hfirst := hrow.radial _ hT₂
    rw [hswap Ur L.b (angularPartial φ)] at hfirst
    have hsecond := n06_unit_weak_angular_product_pairing hrow.radial_angular
      hrow.radial_memLp hrow.radial_angular_memLp hb hpb hφ
    change (∫ p, Q₂ p * φ p ∂cylinderWindowMeasure 0) = _ at hsecond
    change (∫ p, (L.b p * Ur p) * angularPartial φ p ∂cylinderWindowMeasure 0) =
      -(∫ p, U p * F₂ p ∂cylinderWindowMeasure 0) at hfirst
    linarith only [hfirst, hsecond]
  have h₃ : (∫ p, U p * F₃ p ∂cylinderWindowMeasure 0) =
      ∫ p, Q₃ p * φ p ∂cylinderWindowMeasure 0 := by
    have hfirst := hrow.angular _ hT₃
    rw [hswap Ut L.b (radialPartial φ)] at hfirst
    have hsecond := n06_unit_weak_radial_product_pairing hrow.angular_radial
      hrow.angular_memLp hrow.radial_angular_memLp hb hpb hφ
    change (∫ p, Q₃ p * φ p ∂cylinderWindowMeasure 0) = _ at hsecond
    change (∫ p, (L.b p * Ut p) * radialPartial φ p ∂cylinderWindowMeasure 0) =
      -(∫ p, U p * F₃ p ∂cylinderWindowMeasure 0) at hfirst
    linarith only [hfirst, hsecond]
  have h₄ : (∫ p, U p * F₄ p ∂cylinderWindowMeasure 0) =
      ∫ p, Q₄ p * φ p ∂cylinderWindowMeasure 0 := by
    have hfirst := hrow.angular _ hT₄
    rw [hswap Ut L.c (angularPartial φ)] at hfirst
    have hsecond := n06_unit_weak_angular_product_pairing hrow.angular_angular
      hrow.angular_memLp hrow.angular_angular_memLp hc hpc hφ
    change (∫ p, Q₄ p * φ p ∂cylinderWindowMeasure 0) = _ at hsecond
    change (∫ p, (L.c p * Ut p) * angularPartial φ p ∂cylinderWindowMeasure 0) =
      -(∫ p, U p * F₄ p ∂cylinderWindowMeasure 0) at hfirst
    linarith only [hfirst, hsecond]
  have hoperator : divergenceOperator L φ = fun p => F₁ p + F₂ p + F₃ p + F₄ p := by
    funext p
    change radialPartial (fun q => L.a q * radialPartial φ q + L.b q * angularPartial φ q) p +
      angularPartial (fun q => L.b q * radialPartial φ q + L.c q * angularPartial φ q) p = _
    rw [radialPartial_add (hT₁.1.differentiable (by simp) p)
      (hT₂.1.differentiable (by simp) p),
      angularPartial_add (hT₃.1.differentiable (by simp) p)
        (hT₄.1.differentiable (by simp) p)]
    dsimp only [F₁, F₂, F₃, F₄]
    ring
  calc
    _ = ∫ p, U p * F₁ p + U p * F₂ p + U p * F₃ p + U p * F₄ p
        ∂cylinderWindowMeasure 0 := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hoperator]
      ring
    _ = (∫ p, U p * F₁ p ∂cylinderWindowMeasure 0) +
        (∫ p, U p * F₂ p ∂cylinderWindowMeasure 0) +
        (∫ p, U p * F₃ p ∂cylinderWindowMeasure 0) +
        ∫ p, U p * F₄ p ∂cylinderWindowMeasure 0 := n06_integral_four hF₁ hF₂ hF₃ hF₄
    _ = (∫ p, Q₁ p * φ p ∂cylinderWindowMeasure 0) +
        (∫ p, Q₂ p * φ p ∂cylinderWindowMeasure 0) +
        (∫ p, Q₃ p * φ p ∂cylinderWindowMeasure 0) +
        ∫ p, Q₄ p * φ p ∂cylinderWindowMeasure 0 := by rw [h₁, h₂, h₃, h₄]
    _ = ∫ p, Q₁ p * φ p + Q₂ p * φ p + Q₃ p * φ p + Q₄ p * φ p
        ∂cylinderWindowMeasure 0 := (n06_integral_four hQ₁ hQ₂ hQ₃ hQ₄).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      dsimp only [n06WeakDivergenceExpression, Q₁, Q₂, Q₃, Q₄]
      ring

end ContinuousFlexibility.Analysis
