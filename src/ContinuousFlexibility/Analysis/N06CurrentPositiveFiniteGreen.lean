module

public import ContinuousFlexibility.Analysis.N06CurrentPositiveGreen
public import ContinuousFlexibility.Analysis.N06UnitWeakGraphData
public import ContinuousFlexibility.Analysis.N06CutTransmissionJets

/-!
# Finite positive Green with the actual modal forcing

The genuine modal equation supplies the radial flux derivative in L2.
The tensor Green identity then sums over an arbitrary finite mode set,
with its actual forcing synthesis and both weighted endpoint Wronskians.
The final theorem uses the existing weak graph package and its original
modal ODE; no smooth radial source or new operator is introduced.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The actual modal ODE determines an L2 radial flux derivative from
the original L2 value and forcing, with no extra derivative hypothesis. -/
theorem n06_positive_modal_flux_memLp
    {l r j : ℝ} {a c V v f : ℝ → ℝ}
    (hc : Continuous c) (hV : Continuous V)
    (hv : MemLp v 2 (volume.restrict (Ioo l r)))
    (hf : MemLp f 2 (volume.restrict (Ioo l r)))
    (hode : ∀ᵐ y ∂volume.restrict (Ioo l r),
      -deriv (fun t => a t * deriv v t) y + j ^ 2 * c y * v y + V y * v y = f y) :
    MemLp (deriv (fun t => a t * deriv v t)) 2 (volume.restrict (Ioo l r)) := by
  have hrest : MemLp (fun y => j ^ 2 * (c y * v y) + V y * v y - f y)
      2 (volume.restrict (Ioo l r)) :=
    (((n06_interval_memLp_mul_continuous hv hc).const_mul (j ^ 2)).add
      (n06_interval_memLp_mul_continuous hv hV)).sub hf
  apply (memLp_congr_ae ?_).mpr hrest
  filter_upwards [hode] with y hy
  change deriv (fun t => a t * deriv v t) y =
    j ^ 2 * (c y * v y) + V y * v y - f y
  linear_combination -hy

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- Summing the genuine modal equations gives the finite positive Green
identity with its actual L2 forcing. Both endpoint derivatives are the
ordinary derivatives of the same finite C1 reconstruction. -/
theorem N06CurrentHeightTestTraces.finite_positive_green
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi))
    {a c V : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V)
    (s : Finset ℕ) (v f : ℕ → ℝ → ℝ)
    (hC : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s,
      AbsolutelyContinuousOnInterval (deriv (v i)) (K.left m) (K.right m))
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hf : ∀ i ∈ s, MemLp (f i) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hode : ∀ i ∈ s, ∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)),
      -deriv (fun t => a t * deriv (v i) t) y +
        (((2 * i : ℕ) : ℝ)) ^ 2 * c y * v i y + V y * v i y = f i y) :
    (∫ p, r11bFiniteSynthesis s f referenceAngularBasis p * canonicalHeight S K z m φ p
      ∂canonicalMeasure S K m) -
      (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p *
        n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        a (K.left m) * (P.value (K.left m, θ) *
          radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.left m, θ) -
            r11bFiniteSynthesis s v referenceAngularBasis (K.left m, θ) * P.radial (K.left m, θ)) -
        a (K.right m) * (P.value (K.right m, θ) *
          radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.right m, θ) -
            r11bFiniteSynthesis s v referenceAngularBasis (K.right m, θ) * P.radial (K.right m, θ)) := by
  let Q (i : ℕ) (p : PolarPoint) : ℝ :=
    -deriv (fun t => a t * deriv (v i) t) p.1 * referenceAngularBasis i p.2 -
      (c p.1 * v i p.1) * iteratedDeriv 2 (referenceAngularBasis i) p.2 +
        (V p.1 * v i p.1) * referenceAngularBasis i p.2
  let U (i : ℕ) (p : PolarPoint) : ℝ := v i p.1 * referenceAngularBasis i p.2
  let B (i : ℕ) (θ : ℝ) : ℝ := referenceAngularBasis i θ *
    (a (K.left m) * (P.value (K.left m, θ) * deriv (v i) (K.left m) -
      v i (K.left m) * P.radial (K.left m, θ)) -
    a (K.right m) * (P.value (K.right m, θ) * deriv (v i) (K.right m) -
      v i (K.right m) * P.radial (K.right m, θ)))
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  have hPW := n06_currentHeight_positiveOperator_memLp h04 hz hs hφ ha hc hV (m := m)
  have hflux (i : ℕ) (hi : i ∈ s) :=
    n06_positive_modal_flux_memLp hc hV (hv i hi) (hf i hi) (hode i hi)
  have hQeq (i : ℕ) (hi : i ∈ s) : Q i =ᵐ[canonicalMeasure S K m]
      (fun p : PolarPoint => f i p.1 * referenceAngularBasis i p.2) := by
    have hp : ∀ᵐ p : PolarPoint ∂canonicalMeasure S K m,
        -deriv (fun t => a t * deriv (v i) t) p.1 +
          (((2 * i : ℕ) : ℝ)) ^ 2 * c p.1 * v i p.1 + V p.1 * v i p.1 = f i p.1 := by
      rw [n06_canonicalMeasure_eq_radial_prod]
      exact Measure.quasiMeasurePreserving_fst.ae (hode i hi)
    filter_upwards [hp] with p hp
    dsimp only [Q]
    simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one, iteratedDeriv_zero, deriv_deriv_referenceAngularBasis]
    linear_combination (referenceAngularBasis i p.2) * hp
  have hI (i : ℕ) (hi : i ∈ s) : Integrable
      (fun p => (f i p.1 * referenceAngularBasis i p.2) * canonicalHeight S K z m φ p)
        (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp (hf i hi)
      (contDiff_referenceAngularBasis i).continuous).integrable_mul hW
  have hJ (i : ℕ) (hi : i ∈ s) : Integrable
      (fun p => U i p * n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p)
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
      ((continuous_const.mul ((hvall.mul continuous_const).sub (continuous_const.mul hradl))).sub
        (continuous_const.mul ((hvalr.mul continuous_const).sub
          (continuous_const.mul hradr))))).intervalIntegrable _ _
  have he : ∀ i ∈ s, ContDiff ℝ 1 (referenceAngularBasis i) :=
    fun i _ => (contDiff_referenceAngularBasis i).of_le (by simp)
  have hBpoint (θ : ℝ) : (∑ i ∈ s, B i θ) =
      a (K.left m) * (P.value (K.left m, θ) *
        radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.left m, θ) -
          r11bFiniteSynthesis s v referenceAngularBasis (K.left m, θ) * P.radial (K.left m, θ)) -
      a (K.right m) * (P.value (K.right m, θ) *
        radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.right m, θ) -
          r11bFiniteSynthesis s v referenceAngularBasis (K.right m, θ) * P.radial (K.right m, θ)) := by
    rw [n06_radialPartial_finiteSynthesis_one s v referenceAngularBasis hC he]
    simp only [B, r11bFiniteSynthesis, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hleft :
      (∫ p, r11bFiniteSynthesis s f referenceAngularBasis p * canonicalHeight S K z m φ p
        ∂canonicalMeasure S K m) =
      ∑ i ∈ s, ∫ p, (f i p.1 * referenceAngularBasis i p.2) * canonicalHeight S K z m φ p
        ∂canonicalMeasure S K m := by
    simp only [r11bFiniteSynthesis, Finset.sum_mul]
    exact integral_finsetSum s hI
  have hright :
      (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p *
        n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
          ∂canonicalMeasure S K m) =
      ∑ i ∈ s, ∫ p, U i p * n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
        ∂canonicalMeasure S K m := by
    simp only [r11bFiniteSynthesis, Finset.sum_mul]
    exact integral_finsetSum s hJ
  rw [hleft, hright, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ i ∈ s, ∫ θ in (0 : ℝ)..Real.pi, B i θ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hg := P.tensor_positive_green h04 hz hs hφ hφp ha hc hV
        (hC i hi) (hAC i hi) (hv i hi) (hflux i hi)
        (contDiff_referenceAngularBasis i) (referenceAngularBasis_periodic i)
      have hforce : (∫ p, Q i p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m) =
          ∫ p, (f i p.1 * referenceAngularBasis i p.2) * canonicalHeight S K z m φ p
            ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hQeq i hi] with p hp
        rw [hp]
      change (∫ p, Q i p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m) -
        (∫ p, U i p * n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
          ∂canonicalMeasure S K m) = ∫ θ in (0 : ℝ)..Real.pi, B i θ at hg
      rw [hforce] at hg
      exact hg
    _ = ∫ θ in (0 : ℝ)..Real.pi, ∑ i ∈ s, B i θ :=
      (intervalIntegral.integral_finsetSum (fun i _ => hB i)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact hBpoint θ

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The existing actual weak graph package supplies every hypothesis of
finite positive Green, including the forcing and flux derivative. Its
chosen modes remain the same H2 representatives used by the graph limits. -/
theorem N06UnitWeakGraphData.current_positive_finite_green
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {Kc : CanonicalData S}
    {base loss b m : ℕ} {ε κ : ℝ} {z : AnnularState S × ℝ}
    {a c V : ℝ → ℝ} {φ : PolarPoint → ℝ}
    {U F : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m)}
    (P : N06UnitWeakGraphData a c V U F κ)
    (Q : N06CurrentHeightTestTraces S Kc z m φ)
    (hl : Kc.left m = 0) (hr : Kc.right m = 1)
    (h04 : N04Properties D T S C L Kc base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi))
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V) (s : Finset ℕ) :
    (∫ p, r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis p *
      canonicalHeight S Kc z m φ p ∂canonicalMeasure S Kc m) -
      (∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p *
        n06UnitReferenceTestOperator a c V (canonicalHeight S Kc z m φ) p
          ∂canonicalMeasure S Kc m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        a 0 * (Q.value (0, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (0, θ) -
            r11bFiniteSynthesis s P.modes referenceAngularBasis (0, θ) * Q.radial (0, θ)) -
        a 1 * (Q.value (1, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (1, θ) -
            r11bFiniteSynthesis s P.modes referenceAngularBasis (1, θ) * Q.radial (1, θ)) := by
  have hC : ∀ i ∈ s, ContDiff ℝ 1 (P.modes i) := fun i _ => (P.representative i).contDiffOne
  have hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (deriv (P.modes i))
      (Kc.left m) (Kc.right m) := by
    intro i _
    simpa only [hl, hr] using (P.representative i).firstAC
  have hv : ∀ i ∈ s, MemLp (P.modes i) 2
      (volume.restrict (Ioo (Kc.left m) (Kc.right m))) := by
    intro i _
    simpa only [hl, hr] using (P.representative i).memLp
  have hf : ∀ i ∈ s, MemLp (n06HalfCosineCoefficient (F 0) i) 2
      (volume.restrict (Ioo (Kc.left m) (Kc.right m))) := by
    intro i _
    exact (n06_canonical_angularCoefficient_memLp (F 0)
      (memLp_angleMeasure_of_continuous (contDiff_referenceAngularBasis i).continuous)).const_mul
        Real.pi⁻¹
  have hode : ∀ i ∈ s, ∀ᵐ y ∂volume.restrict (Ioo (Kc.left m) (Kc.right m)),
      -deriv (fun t => a t * deriv (P.modes i) t) y +
        (((2 * i : ℕ) : ℝ)) ^ 2 * c y * P.modes i y + V y * P.modes i y =
          n06HalfCosineCoefficient (F 0) i y := by
    intro i _
    simpa only [hl, hr] using (P.representative i).ode
  simpa only [hl, hr] using Q.finite_positive_green h04 hz hs hφ hφp ha hc hV s
    P.modes (n06HalfCosineCoefficient (F 0)) hC hAC hv hf hode

end ContinuousFlexibility.Analysis
