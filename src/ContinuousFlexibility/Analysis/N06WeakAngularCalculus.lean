import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Analysis.SpacesCylinderIntegration
import ContinuousFlexibility.Scalar.WeightedDifferentiationSupport

/-!
# Angular calculus on the actual canonical weak graph

The test class is stable under actual mixed derivatives and multiplication
by smooth periodic coefficients. These facts give composition of weak
angular derivatives, including successive first derivatives of the stored
jets. The product rule below applies to arbitrary canonical L2 functions;
only the multiplier and the test are smooth.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

theorem CanonicalTest.n06_mixedDerivative
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) (a b : ℕ) :
    CanonicalTest S K m (mixedDerivative a b φ) := by
  obtain ⟨J, hJ, hJK, hzero⟩ := hφ.2.2
  refine ⟨contDiff_mixedDerivative hφ.1 a b, ?_, J, hJ, hJK, ?_⟩
  · have hp (r : ℝ) : Function.Periodic (fun θ => φ (r, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hφ.2.1 (r, θ)
    intro p
    change mixedDerivative a b φ (p.1 + 0, p.2 + Real.pi) = mixedDerivative a b φ p
    rw [add_zero]
    exact mixedDerivative_angular_periodic hp a b p.1 p.2
  · intro r hr θ
    have hnear : ∀ᶠ s : ℝ in 𝓝 r, s ∉ J := hJ.isClosed.isOpen_compl.mem_nhds hr
    have he : (fun s : ℝ => iteratedDeriv b (fun t : ℝ => φ (s, t)) θ) =ᶠ[𝓝 r]
        (0 : ℝ → ℝ) := by
      filter_upwards [hnear] with s hs
      have hz : (fun t : ℝ => φ (s, t)) = (0 : ℝ → ℝ) :=
        funext (hzero s hs)
      simp only [hz, iteratedDeriv_const_zero, Pi.zero_apply]
    simpa only [mixedDerivative, iteratedDeriv_const_zero, Pi.zero_apply] using
      he.iteratedDeriv_eq a

theorem n06_mixedAngular_one_eq_angularPartial {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : mixedDerivative 0 1 φ = angularPartial φ := by
  have h := angularPartial_mixedDerivative hφ 0 0
  simpa only [spaces_mixedDerivative_zero, Nat.zero_add] using h.symm

theorem CanonicalTest.n06_angularPartial
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    CanonicalTest S K m (angularPartial φ) := by
  rw [← n06_mixedAngular_one_eq_angularPartial hφ.1]
  exact hφ.n06_mixedDerivative 0 1

theorem CanonicalTest.n06_zero_of_not_mem
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ)
    {p : PolarPoint} (hp : p ∉ canonicalOpen S K m) : φ p = 0 := by
  obtain ⟨J, _, hJK, hzero⟩ := hφ.2.2
  have hpJ : p.1 ∉ J := fun h => hp ⟨hJK h, mem_univ p.2⟩
  exact hzero p.1 hpJ p.2

theorem CanonicalTest.n06_eventually_zero_of_not_mem
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ)
    {p : PolarPoint} (hp : p ∉ canonicalOpen S K m) :
    φ =ᶠ[𝓝 p] (0 : PolarPoint → ℝ) := by
  obtain ⟨J, hJ, hJK, hzero⟩ := hφ.2.2
  have hpJ : p.1 ∉ J := fun h => hp ⟨hJK h, mem_univ p.2⟩
  have hnear : ∀ᶠ r : ℝ in 𝓝 p.1, r ∉ J := hJ.isClosed.isOpen_compl.mem_nhds hpJ
  filter_upwards [(continuous_fst.tendsto p).eventually hnear] with q hq
  exact hzero q.1 hq q.2

/-- A coefficient only needs to be smooth inside the strip: the compact
radial support of the test makes the product zero near every exterior point. -/
theorem CanonicalTest.n06_contDiff_mul_left
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ a : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m)) :
    ContDiff ℝ ∞ (fun p => a p * φ p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ canonicalOpen S K m
  · exact (ha.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).mul hφ.1.contDiffAt
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hφ.n06_eventually_zero_of_not_mem hp] with q hq
    change a q * φ q = 0
    change φ q = 0 at hq
    rw [hq, mul_zero]

theorem CanonicalTest.n06_mul_left_of_contDiffOn
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ a : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m))
    (hp : ∀ p ∈ canonicalOpen S K m, a (p + (0, Real.pi)) = a p) :
    CanonicalTest S K m (fun p => a p * φ p) := by
  obtain ⟨J, hJ, hJK, hzero⟩ := hφ.2.2
  refine ⟨hφ.n06_contDiff_mul_left ha, ?_, J, hJ, hJK, ?_⟩
  · intro p
    change a (p + (0, Real.pi)) * φ (p + (0, Real.pi)) = a p * φ p
    rw [hφ.2.1 p]
    by_cases hpU : p ∈ canonicalOpen S K m
    · rw [hp p hpU]
    · rw [hφ.n06_zero_of_not_mem hpU, mul_zero, mul_zero]
  · intro r hr θ
    change a (r, θ) * φ (r, θ) = 0
    rw [hzero r hr θ, mul_zero]

theorem CanonicalTest.n06_mul_left
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ a : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ)
    (ha : ContDiff ℝ ∞ a) (hp : Function.Periodic a (0, Real.pi)) :
    CanonicalTest S K m (fun p => a p * φ p) :=
  hφ.n06_mul_left_of_contDiffOn ha.contDiffOn (fun p _ => hp p)

private theorem n06_iteratedDeriv_iterated (f : ℝ → ℝ) (j k : ℕ) :
    iteratedDeriv j (iteratedDeriv k f) = iteratedDeriv (j + k) f := by
  induction j with
  | zero => simp only [iteratedDeriv_zero, Nat.zero_add]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih, Nat.succ_add, iteratedDeriv_succ]

/-- Composition here is literal composition of totalized one-variable
derivatives, so no extra regularity assumption is needed for the identity. -/
theorem n06_mixedAngular_comp (φ : PolarPoint → ℝ) (j k : ℕ) :
    mixedDerivative 0 j (mixedDerivative 0 k φ) = mixedDerivative 0 (j + k) φ := by
  funext p
  simp only [mixedDerivative, iteratedDeriv_zero]
  exact congrFun (n06_iteratedDeriv_iterated (fun θ => φ (p.1, θ)) j k) p.2

theorem n06_weakCanonicalAngularDerivative_one_iff
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {f g : CanonicalL2 S K m} :
    WeakCanonicalAngularDerivative S K m f g 1 ↔
      ∀ φ, CanonicalTest S K m φ →
        (∫ p, g p * φ p ∂canonicalMeasure S K m) =
          -(∫ p, f p * angularPartial φ p ∂canonicalMeasure S K m) := by
  constructor
  · intro h φ hφ
    simpa only [pow_one, neg_one_mul, n06_mixedAngular_one_eq_angularPartial hφ.1]
      using h φ hφ
  · intro h φ hφ
    simpa only [pow_one, neg_one_mul, n06_mixedAngular_one_eq_angularPartial hφ.1]
      using h φ hφ

/-- Successive weak differentiations add their orders. -/
theorem WeakCanonicalAngularDerivative.n06_trans
    {S : PhysicalSpacesData} {K : CanonicalData S} {m j k : ℕ}
    {f g h : CanonicalL2 S K m}
    (hfg : WeakCanonicalAngularDerivative S K m f g j)
    (hgh : WeakCanonicalAngularDerivative S K m g h k) :
    WeakCanonicalAngularDerivative S K m f h (j + k) := by
  intro φ hφ
  rw [hgh φ hφ, hfg _ (hφ.n06_mixedDerivative 0 k), n06_mixedAngular_comp, pow_add]
  ring

/-- If two stored jets have orders j and j+k relative to the same zeroth
field, the latter is the kth weak derivative of the former. -/
theorem WeakCanonicalAngularDerivative.n06_between
    {S : PhysicalSpacesData} {K : CanonicalData S} {m j k : ℕ}
    {f g h : CanonicalL2 S K m}
    (hfg : WeakCanonicalAngularDerivative S K m f g j)
    (hfh : WeakCanonicalAngularDerivative S K m f h (j + k)) :
    WeakCanonicalAngularDerivative S K m g h k := by
  intro φ hφ
  rw [hfh φ hφ, hfg _ (hφ.n06_mixedDerivative 0 k), n06_mixedAngular_comp, pow_add]
  ring

theorem WeakCanonicalAngularDerivative.n06_successive
    {S : PhysicalSpacesData} {K : CanonicalData S} {m j : ℕ}
    {f g h : CanonicalL2 S K m}
    (hfg : WeakCanonicalAngularDerivative S K m f g j)
    (hfh : WeakCanonicalAngularDerivative S K m f h (j + 1)) :
    WeakCanonicalAngularDerivative S K m g h 1 := hfg.n06_between hfh

/-- A continuous field is square-integrable on each actual finite
canonical cylinder, irrespective of its behavior off that cylinder. -/
theorem n06_memLp_canonical_of_continuous
    {S : PhysicalSpacesData} {K : CanonicalData S} (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : Continuous φ) :
    MemLp φ 2 (canonicalMeasure S K m) := by
  let Q : Set PolarPoint := Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hsubset : Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi ⊆ Q :=
    Set.prod_mono Ioo_subset_Icc_self Ioc_subset_Icc_self
  letI : IsFiniteMeasure (canonicalMeasure S K m) := ⟨by
    rw [canonicalMeasure, Measure.restrict_apply_univ]
    exact (measure_mono hsubset).trans_lt hQ.measure_lt_top⟩
  obtain ⟨M, hM⟩ := hQ.bddAbove_image hφ.norm.continuousOn
  apply MemLp.of_bound hφ.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  exact hM ⟨p, hsubset hp, rfl⟩

theorem CanonicalTest.n06_memLp
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    MemLp φ 2 (canonicalMeasure S K m) :=
  n06_memLp_canonical_of_continuous m hφ.1.continuous

theorem n06_integrable_canonical_mul_continuous
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (f : CanonicalL2 S K m) {φ : PolarPoint → ℝ} (hφ : Continuous φ) :
    Integrable (fun p => f p * φ p) (canonicalMeasure S K m) :=
  (Lp.memLp f).integrable_mul (n06_memLp_canonical_of_continuous m hφ)

/-- The genuine product rule with a coefficient controlled only inside
the canonical strip. The weak fields remain arbitrary actual L2 elements. -/
theorem n06_weakCanonicalAngularDerivative_mul_of_contDiffOn
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {f g F G : CanonicalL2 S K m} {a : PolarPoint → ℝ}
    (hfg : WeakCanonicalAngularDerivative S K m f g 1)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m))
    (hp : ∀ p ∈ canonicalOpen S K m, a (p + (0, Real.pi)) = a p)
    (hF : (F : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] fun p => a p * f p)
    (hG : (G : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => a p * g p + angularPartial a p * f p) :
    WeakCanonicalAngularDerivative S K m F G 1 := by
  apply n06_weakCanonicalAngularDerivative_one_iff.mpr
  intro φ hφ
  have hU : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have haθ : ContDiffOn ℝ ∞ (angularPartial a) (canonicalOpen S K m) :=
    scalar_contDiffOn_angularPartial hU ha
  have hga := n06_integrable_canonical_mul_continuous g (hφ.n06_contDiff_mul_left ha).continuous
  have hfaθ := n06_integrable_canonical_mul_continuous f (hφ.n06_contDiff_mul_left haθ).continuous
  have hfa := n06_integrable_canonical_mul_continuous f
    ((hφ.n06_angularPartial).n06_contDiff_mul_left ha).continuous
  have hderivInt :
      (∫ p, f p * angularPartial (fun q => a q * φ q) p ∂canonicalMeasure S K m) =
        (∫ p, f p * (angularPartial a p * φ p) ∂canonicalMeasure S K m) +
          ∫ p, f p * (a p * angularPartial φ p) ∂canonicalMeasure S K m := by
    calc
      _ = ∫ p, f p * (angularPartial a p * φ p + a p * angularPartial φ p)
          ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hpU
        have hpOpen : p ∈ canonicalOpen S K m := ⟨hpU.1, mem_univ p.2⟩
        exact congrArg (fun v => f p * v)
          (angularPartial_mul ((ha.contDiffAt (hU.mem_nhds hpOpen)).differentiableAt (by simp))
            (hφ.1.differentiable (by simp) p))
      _ = _ := by
        simp_rw [mul_add]
        exact integral_add hfaθ hfa
  have htest := n06_weakCanonicalAngularDerivative_one_iff.mp hfg
    (fun p => a p * φ p) (hφ.n06_mul_left_of_contDiffOn ha hp)
  rw [hderivInt] at htest
  have hleft :
      (∫ p, G p * φ p ∂canonicalMeasure S K m) =
        (∫ p, g p * (a p * φ p) ∂canonicalMeasure S K m) +
          ∫ p, f p * (angularPartial a p * φ p) ∂canonicalMeasure S K m := by
    calc
      _ = ∫ p, (g p * (a p * φ p) + f p * (angularPartial a p * φ p))
          ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hG] with p hGp
        rw [hGp]
        ring
      _ = _ := integral_add hga hfaθ
  have hright :
      (∫ p, F p * angularPartial φ p ∂canonicalMeasure S K m) =
        ∫ p, f p * (a p * angularPartial φ p) ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [hF] with p hFp
    rw [hFp]
    ring
  rw [hleft, hright]
  linarith only [htest]

/-- The globally smooth form is an immediate specialization of the
strip-local product rule; no regularity is imposed on the weak fields. -/
theorem n06_weakCanonicalAngularDerivative_mul_of_ae
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {f g F G : CanonicalL2 S K m} {a : PolarPoint → ℝ}
    (hfg : WeakCanonicalAngularDerivative S K m f g 1)
    (ha : ContDiff ℝ ∞ a) (hp : Function.Periodic a (0, Real.pi))
    (hF : (F : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] fun p => a p * f p)
    (hG : (G : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => a p * g p + angularPartial a p * f p) :
    WeakCanonicalAngularDerivative S K m F G 1 :=
  n06_weakCanonicalAngularDerivative_mul_of_contDiffOn hfg ha.contDiffOn
    (fun p _ => hp p) hF hG

/-- A measurable coefficient bounded on the actual cylinder multiplies
an arbitrary canonical L2 field into the same L2 space. -/
theorem n06_canonicalMemLp_bounded_mul
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {a : PolarPoint → ℝ} {C : ℝ}
    (ha : AEStronglyMeasurable a (canonicalMeasure S K m))
    (hC : ∀ᵐ p ∂canonicalMeasure S K m, |a p| ≤ C) (f : CanonicalL2 S K m) :
    MemLp (fun p => a p * f p) 2 (canonicalMeasure S K m) := by
  apply (Lp.memLp f).of_le_mul (c := C) (ha.mul (Lp.aestronglyMeasurable f))
  filter_upwards [hC] with p hp
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

/-- The product rule packaged directly for the L2 elements produced by
the actual coefficient fields and their first weak product jet. -/
theorem n06_weakCanonicalAngularDerivative_mul_toLp
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {f g : CanonicalL2 S K m} {a : PolarPoint → ℝ}
    (hfg : WeakCanonicalAngularDerivative S K m f g 1)
    (ha : ContDiff ℝ ∞ a) (hp : Function.Periodic a (0, Real.pi))
    (hF : MemLp (fun p => a p * f p) 2 (canonicalMeasure S K m))
    (hG : MemLp (fun p => a p * g p + angularPartial a p * f p) 2
      (canonicalMeasure S K m)) :
    WeakCanonicalAngularDerivative S K m (hF.toLp _) (hG.toLp _) 1 :=
  n06_weakCanonicalAngularDerivative_mul_of_ae hfg ha hp hF.coeFn_toLp hG.coeFn_toLp

theorem n06_weakCanonicalAngularDerivative_mul_toLp_of_contDiffOn
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {f g : CanonicalL2 S K m} {a : PolarPoint → ℝ}
    (hfg : WeakCanonicalAngularDerivative S K m f g 1)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m))
    (hp : ∀ p ∈ canonicalOpen S K m, a (p + (0, Real.pi)) = a p)
    (hF : MemLp (fun p => a p * f p) 2 (canonicalMeasure S K m))
    (hG : MemLp (fun p => a p * g p + angularPartial a p * f p) 2
      (canonicalMeasure S K m)) :
    WeakCanonicalAngularDerivative S K m (hF.toLp _) (hG.toLp _) 1 :=
  n06_weakCanonicalAngularDerivative_mul_of_contDiffOn hfg ha hp hF.coeFn_toLp hG.coeFn_toLp

end ContinuousFlexibility.Statements
