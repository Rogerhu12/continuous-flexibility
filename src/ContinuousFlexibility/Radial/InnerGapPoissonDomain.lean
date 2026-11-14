module

public import ContinuousFlexibility.Radial.InnerRadialH1Density
public import ContinuousFlexibility.Radial.InnerRadialAffineLift
public import ContinuousFlexibility.Radial.InnerGapPoissonL2

/-!
# The actual gap Poisson columns in the common physical domain

The Poisson value and its normalized derivative are realized together
in the same physical measure. Subtracting the fixed affine endpoint
lift gives a smooth zero-endpoint field, so the cutoff density theorem
places it in the actual H¹ closure. The canonical trace is therefore
the prescribed boundary vector.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

section PoissonDomain

variable (D : ReferenceData) (hw : Continuous D.w)
  {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
  (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
  (p : Fin 2 → ℝ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))

def innerGapPoissonH1Unit (i : Fin 2) : InnerRadialH1Pair D :=
  (innerRadialIntervalToLp D hw ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (p i) (hp i).continuous.continuousOn,
   innerRadialIntervalToLp D hw ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapGradientField (p i))
    (innerGapGradientField_continuous (hp i)).continuousOn)

theorem innerGapPoissonH1Unit_value_ae (i : Fin 2) :
    ((innerGapPoissonH1Unit D hw ha hcore hpos p hp i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (p i) :=
  innerRadialIntervalToLp_ae D hw ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (p i) (hp i).continuous.continuousOn

theorem innerGapPoissonH1Unit_gradient_ae (i : Fin 2) :
    ((innerGapPoissonH1Unit D hw ha hcore hpos p hp i).2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField (p i)) :=
  innerRadialIntervalToLp_ae D hw ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapGradientField (p i))
    (innerGapGradientField_continuous (hp i)).continuousOn

/-- The actual two-column value/gradient map. -/
def innerGapPoissonH1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] InnerRadialH1Pair D := by
  let L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] InnerRadialH1Pair D :=
    { toFun := fun ξ => ξ 0 • innerGapPoissonH1Unit D hw ha hcore hpos p hp 0 +
        ξ 1 • innerGapPoissonH1Unit D hw ha hcore hpos p hp 1
      map_add' := by
        intro ξ η
        simp only [PiLp.add_apply, add_smul]
        abel
      map_smul' := by
        intro c ξ
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, smul_add] }
  exact ⟨L, L.continuous_of_finiteDimensional⟩

theorem innerGapPoissonH1_apply (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerGapPoissonH1 D hw ha hcore hpos p hp ξ =
      ξ 0 • innerGapPoissonH1Unit D hw ha hcore hpos p hp 0 +
        ξ 1 • innerGapPoissonH1Unit D hw ha hcore hpos p hp 1 := rfl

theorem innerGapPoissonH1_value_ae (ξ : EuclideanSpace ℝ (Fin 2)) :
    ((innerGapPoissonH1 D hw ha hcore hpos p hp ξ).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapPoisson p ξ) := by
  simp only [innerGapPoissonH1_apply, Prod.fst_add, Prod.smul_fst]
  filter_upwards [Lp.coeFn_add
    (ξ 0 • (innerGapPoissonH1Unit D hw ha hcore hpos p hp 0).1)
    (ξ 1 • (innerGapPoissonH1Unit D hw ha hcore hpos p hp 1).1),
    Lp.coeFn_smul (ξ 0) (innerGapPoissonH1Unit D hw ha hcore hpos p hp 0).1,
    Lp.coeFn_smul (ξ 1) (innerGapPoissonH1Unit D hw ha hcore hpos p hp 1).1,
    innerGapPoissonH1Unit_value_ae D hw ha hcore hpos p hp 0,
    innerGapPoissonH1Unit_value_ae D hw ha hcore hpos p hp 1] with r hadd hs₀ hs₁ h₀ h₁
  rw [hadd, Pi.add_apply, hs₀, hs₁, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    h₀, h₁]
  by_cases hr : r ∈ Ioo a b
  · simp only [indicator_of_mem hr, innerGapPoisson_two]
  · simp only [indicator_of_notMem hr, mul_zero, zero_add]

theorem innerGapPoissonH1_gradient_ae (ξ : EuclideanSpace ℝ (Fin 2)) :
    ((innerGapPoissonH1 D hw ha hcore hpos p hp ξ).2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField (innerGapPoisson p ξ)) := by
  simp only [innerGapPoissonH1_apply, Prod.snd_add, Prod.smul_snd]
  filter_upwards [Lp.coeFn_add
    (ξ 0 • (innerGapPoissonH1Unit D hw ha hcore hpos p hp 0).2)
    (ξ 1 • (innerGapPoissonH1Unit D hw ha hcore hpos p hp 1).2),
    Lp.coeFn_smul (ξ 0) (innerGapPoissonH1Unit D hw ha hcore hpos p hp 0).2,
    Lp.coeFn_smul (ξ 1) (innerGapPoissonH1Unit D hw ha hcore hpos p hp 1).2,
    innerGapPoissonH1Unit_gradient_ae D hw ha hcore hpos p hp 0,
    innerGapPoissonH1Unit_gradient_ae D hw ha hcore hpos p hp 1] with r hadd hs₀ hs₁ h₀ h₁
  rw [hadd, Pi.add_apply, hs₀, hs₁, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    h₀, h₁]
  by_cases hr : r ∈ Ioo a b
  · simp only [indicator_of_mem hr, innerGapGradientField, innerGapPoisson_deriv p hp,
      Fin.sum_univ_two]
    ring
  · simp only [indicator_of_notMem hr, mul_zero, zero_add]

/-- The value coordinate is the very same physical Poisson operator
whose Hilbert adjoint and quantitative estimate were already proved. -/
theorem innerGapPoissonH1_value (ξ : EuclideanSpace ℝ (Fin 2)) :
    (innerGapPoissonH1 D hw ha hcore hpos p hp ξ).1 =
      innerGapPoissonL2 D hw ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp ξ := by
  apply Lp.ext
  exact (innerGapPoissonH1_value_ae D hw ha hcore hpos p hp ξ).trans
    (innerGapPoissonL2_ae D hw ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp ξ).symm

theorem innerGapPoissonH1Unit_sub_affine (hab : a < b)
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0) (i : Fin 2) :
    innerGapPoissonH1Unit D hw ha hcore hpos p hp i -
      innerRadialAffineUnitPair D hw ha hcore hpos i ∈ innerRadialH1Zero D a b := by
  let h : ℝ → ℝ := innerIntervalAffineLift a b (innerEndpointValues i)
  have hh : ContDiff ℝ ∞ h := innerIntervalAffineLift_contDiff a b (innerEndpointValues i)
  let φ : ℝ → ℝ := fun r => p i r - h r
  have hφ : ContDiff ℝ ∞ φ := (hp i).sub hh
  have hpa : p i a = innerEndpointValues i 0 := by
    simpa only [innerGapEndpoint_zero, innerEndpointValues] using hb 0 i
  have hpb : p i b = innerEndpointValues i 1 := by
    simpa only [innerGapEndpoint_one, innerEndpointValues] using hb 1 i
  have hends := innerIntervalAffineLift_endpoints hab (innerEndpointValues i)
  have hφa : φ a = 0 := by
    dsimp only [φ, h]
    rw [hpa, hends.1, sub_self]
  have hφb : φ b = 0 := by
    dsimp only [φ, h]
    rw [hpb, hends.2, sub_self]
  apply innerRadialH1Zero_of_smooth_zero_endpoints D hw hab ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
    (fun _ _ => hφ.contDiffAt) hφa hφb
  · filter_upwards [Lp.coeFn_sub
      (innerGapPoissonH1Unit D hw ha hcore hpos p hp i).1
      (innerRadialAffineUnitPair D hw ha hcore hpos i).1,
      innerGapPoissonH1Unit_value_ae D hw ha hcore hpos p hp i,
      innerRadialAffineUnitPair_value_ae D hw ha hcore hpos i] with r hsub hP hA
    rw [hsub, Pi.sub_apply, hP, hA]
    by_cases hr : r ∈ Ioo a b
    · simp only [indicator_of_mem hr, φ, h]
    · simp only [indicator_of_notMem hr, sub_self]
  · filter_upwards [Lp.coeFn_sub
      (innerGapPoissonH1Unit D hw ha hcore hpos p hp i).2
      (innerRadialAffineUnitPair D hw ha hcore hpos i).2,
      innerGapPoissonH1Unit_gradient_ae D hw ha hcore hpos p hp i,
      innerRadialAffineUnitPair_gradient_ae D hw ha hcore hpos i] with r hsub hP hA
    rw [hsub, Pi.sub_apply, hP, hA]
    by_cases hr : r ∈ Ioo a b
    · have hdφ : deriv φ r = deriv (p i) r - deriv h r :=
        (((hp i).differentiable (by simp) r).hasDerivAt.fun_sub
          (hh.differentiable (by simp) r).hasDerivAt).deriv
      simp only [indicator_of_mem hr, innerGapGradientField, hdφ]
      dsimp only [h]
      ring
    · simp only [indicator_of_notMem hr, sub_self]

/-- The same Poisson pair and the fixed physical affine lift differ
by an element of the actual zero-endpoint closure. -/
theorem innerGapPoissonH1_sub_affine (hab : a < b)
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerGapPoissonH1 D hw ha hcore hpos p hp ξ -
      innerRadialAffineLift D hw ha hcore hpos (fun i => ξ i) ∈ innerRadialH1Zero D a b := by
  let P₀ := innerGapPoissonH1Unit D hw ha hcore hpos p hp 0
  let P₁ := innerGapPoissonH1Unit D hw ha hcore hpos p hp 1
  let A₀ := innerRadialAffineUnitPair D hw ha hcore hpos 0
  let A₁ := innerRadialAffineUnitPair D hw ha hcore hpos 1
  have h₀ : P₀ - A₀ ∈ innerRadialH1Zero D a b :=
    innerGapPoissonH1Unit_sub_affine D hw ha hcore hpos p hp hab hb 0
  have h₁ : P₁ - A₁ ∈ innerRadialH1Zero D a b :=
    innerGapPoissonH1Unit_sub_affine D hw ha hcore hpos p hp hab hb 1
  have he : ξ 0 • P₀ + ξ 1 • P₁ - (ξ 0 • A₀ + ξ 1 • A₁) =
      ξ 0 • (P₀ - A₀) + ξ 1 • (P₁ - A₁) := by
    simp only [smul_sub]
    abel
  rw [innerGapPoissonH1_apply, innerRadialAffineLift_apply, he]
  exact (innerRadialH1Zero D a b).add_mem
    ((innerRadialH1Zero D a b).smul_mem (ξ 0) h₀)
    ((innerRadialH1Zero D a b).smul_mem (ξ 1) h₁)

/-- The actual trace, recovered from physical pairings, is the
prescribed Euclidean boundary vector. -/
theorem innerGapPoissonH1_domain_trace (hab : a < b)
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerGapPoissonH1 D hw ha hcore hpos p hp ξ ∈
        innerRadialH1Domain D hw ha hcore hpos ∧
      innerRadialH1Trace D hw ha hcore hpos
        (innerGapPoissonH1 D hw ha hcore hpos p hp ξ) = fun i => ξ i :=
  (innerRadialH1Domain_trace_iff D hw hab ha hcore hpos _ _).mpr
    (innerGapPoissonH1_sub_affine D hw ha hcore hpos p hp hab hb ξ)

end PoissonDomain

end ContinuousFlexibility.Radial
