module

public import ContinuousFlexibility.Analysis.N06WeakCubicPairing
public import ContinuousFlexibility.Analysis.N06CubicMultiplierSymmetry
public import ContinuousFlexibility.Analysis.N06CanonicalCosineCutoff
public import ContinuousFlexibility.Analysis.N06WeakCylinderGraph
public import ContinuousFlexibility.Analysis.N06GraphCauchy
public import ContinuousFlexibility.Radial.R11bWeakNormalLimit

/-!
# The actual cubic distributional equation after strong graph completion

The finite identity is passed through the original L2 pairings. The test
on the left is the actual divergence of the original compact radial test;
the five tests on the right are the same cubic multipliers times that
test. The canonical theorem obtains convergence of the original value
from its already proved cosine truncation and the same mode representatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem n06_integral_graph_pairing_sum {μ : Measure PolarPoint}
    (X M : Fin 5 → PolarPoint → ℝ) (φ : PolarPoint → ℝ)
    (hI : ∀ i, Integrable (fun p => X i p * (M i p * φ p)) μ) :
    (∫ p, (∑ i : Fin 5, M i p * X i p) * φ p ∂μ) =
      ∑ i : Fin 5, ∫ p, X i p * (M i p * φ p) ∂μ := by
  calc
    _ = ∫ p, ∑ i : Fin 5, X i p * (M i p * φ p) ∂μ := by
      apply integral_congr_ae
      filter_upwards with p
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := integral_finsetSum Finset.univ (fun i _ => hI i)

/-- Passing the actual finite pairing to strong L2 limits gives the genuine
cubic divergence distribution, with exactly the five original multipliers. -/
theorem n06_weak_cubic_pairing_of_finite_limits
    {μ : Measure PolarPoint} (hμ : μ = cylinderWindowMeasure 0)
    (U : Lp ℝ 2 μ) (G : Fin 5 → Lp ℝ 2 μ) (v : ℕ → ℝ → ℝ)
    (hC₁ : ∀ i, ContDiff ℝ 1 (v i))
    (hAC : ∀ i, AbsolutelyContinuousOnInterval (deriv (v i)) 0 1)
    (hv : ∀ i, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : ∀ i, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : ∀ i, MemLp (deriv (deriv (v i))) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hUN : ∀ N, MemLp (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) 2 μ)
    (hGN : ∀ N i, MemLp (n06WeakFiniteGraphFields (Finset.range (N + 1)) v 0 i) 2 μ)
    (hUlim : Tendsto (fun N => (hUN N).toLp
      (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis)) atTop (𝓝 U))
    (hGlim : ∀ i, Tendsto (fun N => (hGN N i).toLp
      (n06WeakFiniteGraphFields (Finset.range (N + 1)) v 0 i)) atTop (𝓝 (G i)))
    {A B C φ : PolarPoint → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ B (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hC : ContDiffOn ℝ ∞ C (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hpA : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), A (p + (0, Real.pi)) = A p)
    (hpB : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), B (p + (0, Real.pi)) = B p)
    (hpC : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), C (p + (0, Real.pi)) = C p)
    (hφ : n06UnitCanonicalTest φ) :
    (∫ p, U p *
      divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p ∂μ) =
      ∫ p, (∑ i : Fin 5,
        n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C i p * G i p) * φ p ∂μ := by
  subst μ
  let M := n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C
  let L := n06CubicCoefficients (fun q => cylinderWeight q.1) A B C
  have hd : ContDiff ℝ ∞ cylinderWeight := by
    change ContDiff ℝ ∞ (fun r : ℝ => r * (1 - r))
    exact contDiff_id.mul (contDiff_const.sub contDiff_id)
  have he : ContDiff ℝ ∞ (fun r : ℝ => 1 - 2 * r) :=
    contDiff_const.sub (contDiff_const.mul contDiff_id)
  have hpos (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) : 0 < cylinderWeight r :=
    mul_pos hr.1 (sub_pos.mpr hr.2)
  have hM (i : Fin 5) : ContDiffOn ℝ ∞ (M i) (Ioo (0 : ℝ) 1 ×ˢ univ) :=
    n06CubicGraphMultipliers_contDiffOn_strip hd.contDiffOn he.contDiffOn hpos hA hB hC i
  have htestM (i : Fin 5) : MemLp (fun p => M i p * φ p) 2 (cylinderWindowMeasure 0) :=
    continuous_memLp_cylinderWindow (hφ.n06_contDiff_mul_left (hM i)).continuous 0
  have hd₃ : ContDiff ℝ ∞ (fun p : PolarPoint => cylinderWeight p.1 ^ 3) :=
    (hd.comp contDiff_fst).pow 3
  have htestL : MemLp (divergenceOperator L φ) 2 (cylinderWindowMeasure 0) :=
    continuous_memLp_cylinderWindow
      (n06_unit_divergence_test_contDiff L (hd₃.contDiffOn.mul hA)
        (hd₃.contDiffOn.mul hB) (hd₃.contDiffOn.mul hC) hφ).continuous 0
  have hleft : Tendsto (fun N => ∫ p,
      r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis p *
        divergenceOperator L φ p ∂cylinderWindowMeasure 0) atTop
      (𝓝 (∫ p, U p * divergenceOperator L φ p ∂cylinderWindowMeasure 0)) :=
    r11b_tendsto_integral_mul_of_L2_tendsto hUN (Lp.memLp U) htestL
      (by simpa only [Lp.toLp_coeFn] using hUlim)
  have hright (i : Fin 5) : Tendsto (fun N => ∫ p,
      n06WeakFiniteGraphFields (Finset.range (N + 1)) v 0 i p * (M i p * φ p)
        ∂cylinderWindowMeasure 0) atTop
      (𝓝 (∫ p, G i p * (M i p * φ p) ∂cylinderWindowMeasure 0)) :=
    r11b_tendsto_integral_mul_of_L2_tendsto (fun N => hGN N i) (Lp.memLp (G i)) (htestM i)
      (by simpa only [Lp.toLp_coeFn] using hGlim i)
  have hseq : (fun N => ∫ p,
      r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis p *
        divergenceOperator L φ p ∂cylinderWindowMeasure 0) =
      fun N => ∑ i : Fin 5, ∫ p,
        n06WeakFiniteGraphFields (Finset.range (N + 1)) v 0 i p * (M i p * φ p)
          ∂cylinderWindowMeasure 0 := by
    funext N
    exact (n06_finite_weak_cubic_pairing (Finset.range (N + 1)) v
      (fun i _ => hC₁ i) (fun i _ => hAC i) (fun i _ => hv i)
      (fun i _ => hv₁ i) (fun i _ => hv₂ i) hA hB hC hpA hpB hpC hφ).trans
        (n06_integral_graph_pairing_sum _ M φ
          (fun i => (hGN N i).integrable_mul (htestM i)))
  rw [hseq] at hleft
  have heq := tendsto_nhds_unique hleft
    (tendsto_finsetSum Finset.univ (fun i _ => hright i))
  exact heq.trans (n06_integral_graph_pairing_sum
    (fun i => (G i : PolarPoint → ℝ)) M φ
      (fun i => (Lp.memLp (G i)).integrable_mul (htestM i))).symm

/-- The original canonical weak row itself supplies convergence of the
value cutoff. Only the genuine graph limits and the same AE mode
representatives from graph completion are used. -/
theorem n06_canonical_weak_cubic_pairing_of_graph_limits
    {S : PhysicalSpacesData} {K : CanonicalData S} {m b : ℕ}
    (hl : K.left m = 0) (hr : K.right m = 1)
    (U : Fin (b + 1) → CanonicalL2 S K m)
    (hUeven : (fun p : PolarPoint => U 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U 0 : PolarPoint → ℝ))
    (hUjets : ∀ k, WeakCanonicalAngularDerivative S K m (U 0) (U k) k.val)
    (v : ℕ → ℝ → ℝ)
    (hC₁ : ∀ i, ContDiff ℝ 1 (v i))
    (hAC : ∀ i, AbsolutelyContinuousOnInterval (deriv (v i)) 0 1)
    (hv : ∀ i, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : ∀ i, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : ∀ i, MemLp (deriv (deriv (v i))) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hveq : ∀ i, n06HalfCosineCoefficient (U 0) i =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] v i)
    (hGN : ∀ N i, MemLp (n06WeakFiniteGraphFields (Finset.range (N + 1)) v 0 i) 2
      (canonicalMeasure S K m))
    (G : Fin 5 → CanonicalL2 S K m)
    (hGlim : ∀ i, Tendsto (fun N => (hGN N i).toLp
      (n06WeakFiniteGraphFields (Finset.range (N + 1)) v 0 i)) atTop (𝓝 (G i)))
    {A B C φ : PolarPoint → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ B (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hC : ContDiffOn ℝ ∞ C (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hpA : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), A (p + (0, Real.pi)) = A p)
    (hpB : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), B (p + (0, Real.pi)) = B p)
    (hpC : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), C (p + (0, Real.pi)) = C p)
    (hφ : CanonicalTest S K m φ) :
    (∫ p, U 0 p *
      divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p
        ∂canonicalMeasure S K m) =
      ∫ p, (∑ i : Fin 5,
        n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C i p * G i p) * φ p
          ∂canonicalMeasure S K m := by
  have hμ := n06_canonical_unit_measure_eq_window hl hr
  obtain ⟨hUC, hUlim⟩ := n06_canonicalCosineCut_jetRow_tendsto U hUeven hUjets
  let hUN (N : ℕ) : MemLp
      (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) 2
        (canonicalMeasure S K m) :=
    (congrArg (fun ν : Measure PolarPoint => MemLp
      (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) 2 ν) hμ).mpr
        (n06_weak_finiteSynthesis_memLp _ v referenceAngularBasis
          (fun i _ => hv i) (fun i _ => (contDiff_referenceAngularBasis i).continuous))
  have hclass (N : ℕ) :
      (hUN N).toLp (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) =
        (hUC N 0).toLp (mixedDerivative 0 (0 : Fin (b + 1)).val
          (n06CylinderCosineCut N (U 0))) := by
    have hae : n06CylinderCosineCut N (U 0) =ᵐ[canonicalMeasure S K m]
        r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis :=
      (congrArg (fun ν : Measure PolarPoint =>
        n06CylinderCosineCut N (U 0) =ᵐ[ν]
          r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) hμ).mpr
        (n06_weak_finiteSynthesis_congr_ae (Finset.range (N + 1))
          (n06HalfCosineCoefficient (U 0)) v referenceAngularBasis (fun i _ => hveq i))
    apply (hUN N).toLp_congr (hUC N 0)
    simpa only [Fin.val_zero, spaces_mixedDerivative_zero] using hae.symm
  have hlim : Tendsto (fun N => (hUN N).toLp
      (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis)) atTop (𝓝 (U 0)) :=
    (n06_tendsto_component_of_sum_sq_errors hUlim (0 : Fin (b + 1))).congr'
      (Eventually.of_forall (fun N => (hclass N).symm))
  exact n06_weak_cubic_pairing_of_finite_limits hμ (U 0) G v hC₁ hAC hv hv₁ hv₂ hUN hGN
    hlim hGlim hA hB hC hpA hpB hpC ((n06_unitCanonicalTest_iff hl hr φ).mpr hφ)

end ContinuousFlexibility.Analysis
