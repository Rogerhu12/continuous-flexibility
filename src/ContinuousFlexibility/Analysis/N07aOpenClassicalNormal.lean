module

public import ContinuousFlexibility.Analysis.N07aOpenNormalBootstrap
public import ContinuousFlexibility.Analysis.N07aCanonicalSmoothJets
public import ContinuousFlexibility.Analysis.N07aNormalExpansionExact

/-!
# The classical normal equation of the actual weak solution

The genuine open-piece weak divergence equation determines the classical
second normal derivative of its smooth representative. The six coefficients
below are the actual algebraic expressions in the divergence coefficients;
the source is the original source, with the potential retained separately.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff BigOperators Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonical_periodicOn_eqOn_of_ae_eq {f g : PolarPoint → ℝ}
    (hf : ContinuousOn f (canonicalOpen S K m))
    (hg : ContinuousOn g (canonicalOpen S K m))
    (hfp : ∀ p ∈ canonicalOpen S K m, f (p + (0, Real.pi)) = f p)
    (hgp : ∀ p ∈ canonicalOpen S K m, g (p + (0, Real.pi)) = g p)
    (hae : f =ᵐ[canonicalMeasure S K m] g) : EqOn f g (canonicalOpen S K m) := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  rw [canonicalMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict] at hae
  have hrows := Measure.ae_ae_of_ae_prod hae
  have hmem : ∀ᵐ r ∂(volume.restrict (Ioo (K.left m) (K.right m))),
      r ∈ Ioo (K.left m) (K.right m) := ae_restrict_mem measurableSet_Ioo
  intro p hp
  have hpoint : ∀ᵐ r ∂(volume.restrict (Ioo (K.left m) (K.right m))),
      f (r, p.2) = g (r, p.2) := by
    filter_upwards [hrows, hmem] with r hr hri
    have hfr : Continuous (fun θ => f (r, θ)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ => ⟨hri, mem_univ _⟩)
    have hgr : Continuous (fun θ => g (r, θ)) :=
      hg.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ => ⟨hri, mem_univ _⟩)
    have hfp' : Function.Periodic (fun θ => f (r, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hfp (r, θ) ⟨hri, mem_univ _⟩
    have hgp' : Function.Periodic (fun θ => g (r, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hgp (r, θ) ⟨hri, mem_univ _⟩
    exact congrFun (angle_periodic_eq_of_ae_eq hfr hgr hfp' hgp' hr) p.2
  exact Measure.eqOn_open_of_ae_eq hpoint isOpen_Ioo
    (hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => ⟨hr, mem_univ _⟩))
    (hg.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => ⟨hr, mem_univ _⟩)) hp.1

def n07aOpenNormalCoefficients (a b c ρ q : N07aCanonicalOpenCoefficient S K m) :
    Fin 6 → PolarPoint → ℝ :=
  ![fun p => -2 * ρ.value p * b.value p,
    fun p => -ρ.value p * c.value p,
    fun p => (ρ.jet 1 0).value p * a.value p - ρ.value p * (b.jet 0 1).value p,
    fun p => -ρ.value p * ((b.jet 1 0).value p + (c.jet 0 1).value p),
    fun p => -ρ.value p * q.value p,
    ρ.value]

theorem n07aOpenNormalCoefficients_smooth
    (a b c ρ q : N07aCanonicalOpenCoefficient S K m) (i : Fin 6) :
    ContDiffOn ℝ ∞ (n07aOpenNormalCoefficients a b c ρ q i) (canonicalOpen S K m) := by
  fin_cases i
  · exact (contDiffOn_const.mul ρ.smooth).mul b.smooth
  · exact ρ.smooth.neg.mul c.smooth
  · exact ((ρ.jet 1 0).smooth.mul a.smooth).sub (ρ.smooth.mul (b.jet 0 1).smooth)
  · exact ρ.smooth.neg.mul ((b.jet 1 0).smooth.add (c.jet 0 1).smooth)
  · exact ρ.smooth.neg.mul q.smooth
  · exact ρ.smooth

theorem n07aOpenNormalCoefficients_periodic
    (a b c ρ q : N07aCanonicalOpenCoefficient S K m) (i : Fin 6)
    (p : PolarPoint) (hp : p ∈ canonicalOpen S K m) :
    n07aOpenNormalCoefficients a b c ρ q i (p + (0, Real.pi)) =
      n07aOpenNormalCoefficients a b c ρ q i p := by
  fin_cases i <;> simp [n07aOpenNormalCoefficients, a.periodic p hp, b.periodic p hp,
    c.periodic p hp, ρ.periodic p hp, q.periodic p hp,
    (ρ.jet 1 0).periodic p hp, (b.jet 0 1).periodic p hp,
    (b.jet 1 0).periodic p hp, (c.jet 0 1).periodic p hp]

private theorem n07aCanonical_add_ae {u v : CanonicalL2 S K m} {f g : PolarPoint → ℝ}
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f)
    (hv : (v : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] g) :
    (u + v : CanonicalL2 S K m) =ᵐ[canonicalMeasure S K m] fun p => f p + g p :=
  (Lp.coeFn_add u v).trans (hu.add hv)

private theorem n07aCanonical_sub_ae {u v : CanonicalL2 S K m} {f g : PolarPoint → ℝ}
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f)
    (hv : (v : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] g) :
    (u - v : CanonicalL2 S K m) =ᵐ[canonicalMeasure S K m] fun p => f p - g p :=
  (Lp.coeFn_sub u v).trans (hu.sub hv)

private theorem n07aCanonical_mul_ae (χ : N07aCanonicalOpenCoefficient S K m)
    {u : CanonicalL2 S K m} {f : PolarPoint → ℝ}
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f) :
    (χ.mul u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] fun p => χ.value p * f p := by
  filter_upwards [χ.mul_ae u, hu] with p hp hpu
  exact hp.trans (congrArg (χ.value p * ·) hpu)

/-- The same weak source and solution give the actual classical normal
equation, including every coefficient derivative and the potential term. -/
theorem n07a_openWeak_classicalNormal (hm : K.left m < K.right m)
    (a b c ρ q : N07aCanonicalOpenCoefficient S K m)
    (hinv : ∀ᵐ p ∂canonicalMeasure S K m, ρ.value p * a.value p = 1)
    (u F : n07aCanonicalSmoothSpace S K m)
    {ur uθ urθ uθθ : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u.val ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u.val uθ 0 1)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1)
    (hflux : N07aCanonicalFluxEquation S K m (F.val - q.mul u.val)
      (a.mul ur + b.mul uθ) (b.mul ur + c.mul uθ)) :
    EqOn (mixedDerivative 2 0 (n07aCanonicalSmoothDecode hm u))
      (n07aNormalRhs (n07aOpenNormalCoefficients a b c ρ q)
        (n07aCanonicalSmoothDecode hm u) (n07aCanonicalSmoothDecode hm F))
      (canonicalOpen S K m) := by
  let v := n07aCanonicalSmoothDecode hm u
  let f := n07aCanonicalSmoothDecode hm F
  have hv := n07aCanonicalSmoothRepresentative_properties hm u
  have hf := n07aCanonicalSmoothRepresentative_properties hm F
  have hre := (n07aCanonicalSmoothDecode_mixed_ae hm 1 0 u ur hr).symm
  have hθe := (n07aCanonicalSmoothDecode_mixed_ae hm 0 1 u uθ hθ).symm
  have hrθe := (n07aCanonicalSmoothDecode_mixed_ae hm 1 1 u urθ (hr.comp hrθ)).symm
  have hθθe := (n07aCanonicalSmoothDecode_mixed_ae hm 0 2 u uθθ (hθ.comp hθθ)).symm
  have hsecond := (n07a_openWeak_secondNormal a b c ρ hinv hr hθ hrθ hθθ hflux).2
  have hsecondae := n07aCanonicalSmoothDecode_mixed_ae hm 2 0 u _ hsecond
  have hsource := n07aCanonical_sub_ae hf.2.2.1.symm
    (n07aCanonical_mul_ae q hv.2.2.1.symm)
  have hangular := n07aCanonical_add_ae
    (n07aCanonical_add_ae (n07aCanonical_mul_ae b hrθe)
      (n07aCanonical_mul_ae (b.jet 0 1) hre))
    (n07aCanonical_add_ae (n07aCanonical_mul_ae c hθθe)
      (n07aCanonical_mul_ae (c.jet 0 1) hθe))
  have hcross := n07aCanonical_add_ae (n07aCanonical_mul_ae b hrθe)
    (n07aCanonical_mul_ae (b.jet 1 0) hθe)
  have hrhs := n07aCanonical_add_ae
    (n07aCanonical_mul_ae ρ (n07aCanonical_sub_ae
      (n07aCanonical_sub_ae hsource hangular) hcross))
    (n07aCanonical_mul_ae (ρ.jet 1 0) (n07aCanonical_mul_ae a hre))
  have heqae : mixedDerivative 2 0 v =ᵐ[canonicalMeasure S K m]
      n07aNormalRhs (n07aOpenNormalCoefficients a b c ρ q) v f := by
    filter_upwards [hsecondae, hrhs] with p hp hpr
    change mixedDerivative 2 0 v p = _ at hp
    refine hp.trans (hpr.trans ?_)
    simp [n07aNormalRhs, n07aOpenNormalCoefficients, n07aNormalShift,
      Fin.sum_univ_succ, spaces_mixedDerivative_zero, v, f,
      n07aCanonicalSmoothDecode]
    ring
  have hU : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  apply n07a_canonical_periodicOn_eqOn_of_ae_eq
    (contDiffOn_mixedDerivative hU hv.1 2 0).continuousOn
  · exact ((ContDiffOn.sum fun i _ =>
      (n07aOpenNormalCoefficients_smooth a b c ρ q i.castSucc).mul
        (contDiffOn_mixedDerivative hU hv.1 _ _)).add
          ((n07aOpenNormalCoefficients_smooth a b c ρ q 5).mul hf.1)).continuousOn
  · exact n07a_mixedDerivative_periodic_on (fun p _ => hv.2.1 p) 2 0
  · intro p hp
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _
      exact congrArg₂ (· * ·) (n07aOpenNormalCoefficients_periodic a b c ρ q i.castSucc p hp)
        (n07a_mixedDerivative_periodic_on (fun z _ => hv.2.1 z) _ _ p hp)
    · exact congrArg₂ (· * ·) (n07aOpenNormalCoefficients_periodic a b c ρ q 5 p hp)
        (hf.2.1 p)
  · exact heqae

/-- Starting with the original weak unknown, the first normal/angular
jets and a smooth weak source give representatives with the exact finite
normal expansion. No classical derivative of the unknown is an input. -/
theorem n07a_openWeak_exists_smoothExpansion (hm : K.left m < K.right m)
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
    ∃ v f : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ v (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ f (canonicalOpen S K m) ∧
      Function.Periodic v (0, Real.pi) ∧ Function.Periodic f (0, Real.pi) ∧
      v =ᵐ[canonicalMeasure S K m] u ∧ f =ᵐ[canonicalMeasure S K m] F ∧
      (∀ i j, EqOn (mixedDerivative i j v)
        (n07aNormalTermsValue (n07aOpenNormalCoefficients a b c ρ q) v f
          (n07aNormalExpansion i j)) (canonicalOpen S K m)) ∧
      (∀ i j w, N07aWeakCanonicalMixedDerivative S K m u w i j →
        mixedDerivative i j v =ᵐ[canonicalMeasure S K m] w) := by
  let u' : n07aCanonicalSmoothSpace S K m := ⟨u,
    n07a_openWeak_divergenceBootstrap a b c ρ q hinv hr hθ hrθ hθθ hbase hF hflux⟩
  let F' : n07aCanonicalSmoothSpace S K m := ⟨F, hF⟩
  have hu := n07aCanonicalSmoothRepresentative_properties hm u'
  have hf := n07aCanonicalSmoothRepresentative_properties hm F'
  refine ⟨n07aCanonicalSmoothDecode hm u', n07aCanonicalSmoothDecode hm F',
    hu.1, hf.1, hu.2.1, hf.2.1, hu.2.2.1, hf.2.2.1, ?_, ?_⟩
  · intro i j p hp
    exact n07a_normalExpansion_exact (isOpen_Ioo.prod isOpen_univ)
      (n07aOpenNormalCoefficients_smooth a b c ρ q) hu.1 hf.1
      (n07a_openWeak_classicalNormal hm a b c ρ q hinv u' F' hr hθ hrθ hθθ hflux)
      i j hp
  · intro i j w hw
    exact n07aCanonicalSmoothDecode_mixed_ae hm i j u' w hw

end ContinuousFlexibility.Analysis
