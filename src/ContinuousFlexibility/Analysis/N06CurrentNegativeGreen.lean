module

public import ContinuousFlexibility.Analysis.N06CurrentTestTensorGreen

/-!
# Finite negative Green against actual current physical tests

The finite canonical field has genuine C1 radial modes, AC first radial
derivatives, and L2 second radial derivatives. The actual transformed test
has only the open smoothness and the closed Lipschitz traces derived from
N04. Combining the radial and angular tensor identities proves the finite
negative principal Green identity with the true two endpoint terms.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- The actual transformed test's negative principal expression is L2
on the original piece. This uses only actual forward-chart jet bounds. -/
theorem n06_currentHeight_negativePrincipal_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) :
    MemLp (n06NegativePrincipalTest (canonicalHeight S K z m φ))
      2 (canonicalMeasure S K m) := by
  obtain ⟨hrr, htt⟩ := n06_current_canonicalHeight_second_memLp h04 hz hs m hφ
  exact hrr.sub (n06_canonical_radialWeight_mul_memLp continuous_id htt)

/-- One actual H2 mode satisfies negative Green against the actual
current physical test, without zero endpoint values or a smooth inverse
chart at the boundary. -/
theorem N06CurrentHeightTestTraces.tensor_negative_green
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi))
    {v e : ℝ → ℝ} (hC : ContDiff ℝ 1 v)
    (hAC : AbsolutelyContinuousOnInterval (deriv v) (K.left m) (K.right m))
    (hv : MemLp v 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hv₂ : MemLp (deriv (deriv v)) 2
      (volume.restrict (Ioo (K.left m) (K.right m))))
    (he : ContDiff ℝ ∞ e) (hep : Function.Periodic e Real.pi) :
    (∫ p, (deriv (deriv v) p.1 * e p.2 -
        (p.1 * v p.1) * iteratedDeriv 2 e p.2) * canonicalHeight S K z m φ p
          ∂canonicalMeasure S K m) -
      (∫ p, (v p.1 * e p.2) *
        n06NegativePrincipalTest (canonicalHeight S K z m φ) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi, e θ *
        ((P.value (K.right m, θ) * deriv v (K.right m) -
          v (K.right m) * P.radial (K.right m, θ)) -
        (P.value (K.left m, θ) * deriv v (K.left m) -
          v (K.left m) * P.radial (K.left m, θ))) := by
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  obtain ⟨hrr, htt⟩ := n06_current_canonicalHeight_second_memLp h04 hz hs m hφ
  have hyv : MemLp (fun y => y * v y) 2
      (volume.restrict (Ioo (K.left m) (K.right m))) :=
    n06_interval_memLp_mul_continuous hv continuous_id
  have hA : Integrable (fun p : PolarPoint =>
      (deriv (deriv v) p.1 * e p.2) * canonicalHeight S K z m φ p)
      (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp hv₂ he.continuous).integrable_mul hW
  have hB : Integrable (fun p : PolarPoint =>
      ((p.1 * v p.1) * iteratedDeriv 2 e p.2) * canonicalHeight S K z m φ p)
      (canonicalMeasure S K m) := (n06_canonical_tensor_memLp hyv
        (circleFourier_contDiff_iteratedDeriv he 2).continuous).integrable_mul hW
  have hCint : Integrable (fun p : PolarPoint => (v p.1 * e p.2) *
      radialPartial (radialPartial (canonicalHeight S K z m φ)) p)
      (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp hv he.continuous).integrable_mul hrr
  have hDint : Integrable (fun p : PolarPoint => ((p.1 * v p.1) * e p.2) *
      angularPartial (angularPartial (canonicalHeight S K z m φ)) p)
      (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp hyv he.continuous).integrable_mul htt
  have hleft :
      (∫ p, (deriv (deriv v) p.1 * e p.2 - (p.1 * v p.1) * iteratedDeriv 2 e p.2) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m) =
      (∫ p, (deriv (deriv v) p.1 * e p.2) * canonicalHeight S K z m φ p
        ∂canonicalMeasure S K m) -
      ∫ p, ((p.1 * v p.1) * iteratedDeriv 2 e p.2) * canonicalHeight S K z m φ p
        ∂canonicalMeasure S K m := by
    rw [← integral_sub hA hB]
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hright :
      (∫ p, (v p.1 * e p.2) * n06NegativePrincipalTest (canonicalHeight S K z m φ) p
        ∂canonicalMeasure S K m) =
      (∫ p, (v p.1 * e p.2) * radialPartial (radialPartial (canonicalHeight S K z m φ)) p
        ∂canonicalMeasure S K m) -
      ∫ p, ((p.1 * v p.1) * e p.2) *
        angularPartial (angularPartial (canonicalHeight S K z m φ)) p
          ∂canonicalMeasure S K m := by
    rw [← integral_sub hCint hDint]
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [n06NegativePrincipalTest]
    ring
  have hr := P.tensor_radial_green h04 hz hs hφ hC hAC hv hv₂ he.continuous
  have ht := n06_currentHeight_tensor_angular_green h04 hz hs hφ hφp hyv he hep
  rw [hleft, hright]
  linarith only [hr, ht]

/-- The finite negative principal Green identity uses the same canonical
half-period measure and the actual test traces at both radial endpoints.
The angular truncation is arbitrary, not necessarily an initial segment. -/
theorem N06CurrentHeightTestTraces.finite_negative_green
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi))
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hC : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s,
      AbsolutelyContinuousOnInterval (deriv (v i)) (K.left m) (K.right m))
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2
      (volume.restrict (Ioo (K.left m) (K.right m)))) :
    (∫ p, (n06FiniteMixedField s v 2 0 p - p.1 * n06FiniteMixedField s v 0 2 p) *
      canonicalHeight S K z m φ p ∂canonicalMeasure S K m) -
      (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p *
        n06NegativePrincipalTest (canonicalHeight S K z m φ) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        (P.value (K.right m, θ) * n06FiniteMixedField s v 1 0 (K.right m, θ) -
          r11bFiniteSynthesis s v referenceAngularBasis (K.right m, θ) * P.radial (K.right m, θ)) -
        (P.value (K.left m, θ) * n06FiniteMixedField s v 1 0 (K.left m, θ) -
          r11bFiniteSynthesis s v referenceAngularBasis (K.left m, θ) * P.radial (K.left m, θ)) := by
  let Q (i : ℕ) (p : PolarPoint) : ℝ :=
    deriv (deriv (v i)) p.1 * referenceAngularBasis i p.2 -
      (p.1 * v i p.1) * iteratedDeriv 2 (referenceAngularBasis i) p.2
  let U (i : ℕ) (p : PolarPoint) : ℝ := v i p.1 * referenceAngularBasis i p.2
  let B (i : ℕ) (θ : ℝ) : ℝ := referenceAngularBasis i θ *
    ((P.value (K.right m, θ) * deriv (v i) (K.right m) -
      v i (K.right m) * P.radial (K.right m, θ)) -
    (P.value (K.left m, θ) * deriv (v i) (K.left m) -
      v i (K.left m) * P.radial (K.left m, θ)))
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  have hPW := n06_currentHeight_negativePrincipal_memLp h04 hz hs hφ (m := m)
  have hQ (i : ℕ) (hi : i ∈ s) : MemLp (Q i) 2 (canonicalMeasure S K m) := by
    exact (n06_canonical_tensor_memLp (hv₂ i hi)
      (contDiff_referenceAngularBasis i).continuous).sub
      (n06_canonical_tensor_memLp
        (n06_interval_memLp_mul_continuous (hv i hi) continuous_id)
        (circleFourier_contDiff_iteratedDeriv (contDiff_referenceAngularBasis i) 2).continuous)
  have hI (i : ℕ) (hi : i ∈ s) : Integrable
      (fun p => Q i p * canonicalHeight S K z m φ p) (canonicalMeasure S K m) :=
    (hQ i hi).integrable_mul hW
  have hJ (i : ℕ) (hi : i ∈ s) : Integrable
      (fun p => U i p * n06NegativePrincipalTest (canonicalHeight S K z m φ) p)
        (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp (hv i hi)
      (contDiff_referenceAngularBasis i).continuous).integrable_mul hPW
  have hB (i : ℕ) : IntervalIntegrable (B i) volume 0 Real.pi := by
    have hvalr : Continuous (fun θ => P.value (K.right m, θ)) :=
      P.value_lipschitz.continuous.comp (continuous_const.prodMk continuous_id)
    have hvall : Continuous (fun θ => P.value (K.left m, θ)) :=
      P.value_lipschitz.continuous.comp (continuous_const.prodMk continuous_id)
    have hradr : Continuous (fun θ => P.radial (K.right m, θ)) :=
      P.radial_lipschitz.continuous.comp (continuous_const.prodMk continuous_id)
    have hradl : Continuous (fun θ => P.radial (K.left m, θ)) :=
      P.radial_lipschitz.continuous.comp (continuous_const.prodMk continuous_id)
    exact ((contDiff_referenceAngularBasis i).continuous.mul
      (((hvalr.mul continuous_const).sub (continuous_const.mul hradr)).sub
        ((hvall.mul continuous_const).sub (continuous_const.mul hradl)))).intervalIntegrable _ _
  have hQpoint (p : PolarPoint) :
      n06FiniteMixedField s v 2 0 p - p.1 * n06FiniteMixedField s v 0 2 p =
        ∑ i ∈ s, Q i p := by
    simp only [n06FiniteMixedField, r11bFiniteSynthesis, iteratedDeriv_succ,
      iteratedDeriv_zero, Q]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hBpoint (θ : ℝ) : (∑ i ∈ s, B i θ) =
      (P.value (K.right m, θ) * n06FiniteMixedField s v 1 0 (K.right m, θ) -
        r11bFiniteSynthesis s v referenceAngularBasis (K.right m, θ) * P.radial (K.right m, θ)) -
      (P.value (K.left m, θ) * n06FiniteMixedField s v 1 0 (K.left m, θ) -
        r11bFiniteSynthesis s v referenceAngularBasis (K.left m, θ) * P.radial (K.left m, θ)) := by
    simp only [B, n06FiniteMixedField, r11bFiniteSynthesis, iteratedDeriv_one,
      iteratedDeriv_zero, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hleft :
      (∫ p, (n06FiniteMixedField s v 2 0 p - p.1 * n06FiniteMixedField s v 0 2 p) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m) =
      ∑ i ∈ s, ∫ p, Q i p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m := by
    simp_rw [hQpoint, Finset.sum_mul]
    exact integral_finsetSum s hI
  have hright :
      (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p *
        n06NegativePrincipalTest (canonicalHeight S K z m φ) p ∂canonicalMeasure S K m) =
      ∑ i ∈ s, ∫ p, U i p * n06NegativePrincipalTest (canonicalHeight S K z m φ) p
        ∂canonicalMeasure S K m := by
    simp only [r11bFiniteSynthesis, Finset.sum_mul]
    exact integral_finsetSum s hJ
  rw [hleft, hright, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ i ∈ s, ∫ θ in (0 : ℝ)..Real.pi, B i θ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact P.tensor_negative_green h04 hz hs hφ hφp (hC i hi) (hAC i hi)
        (hv i hi) (hv₂ i hi) (contDiff_referenceAngularBasis i)
        (referenceAngularBasis_periodic i)
    _ = ∫ θ in (0 : ℝ)..Real.pi, ∑ i ∈ s, B i θ :=
      (intervalIntegral.integral_finsetSum (fun i _ => hB i)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact hBpoint θ

end ContinuousFlexibility.Statements
