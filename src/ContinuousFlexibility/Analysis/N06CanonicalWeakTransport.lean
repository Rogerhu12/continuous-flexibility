module

public import ContinuousFlexibility.Analysis.N06CanonicalTestOperator
public import ContinuousFlexibility.Analysis.N06HalfPhysicalPairing

/-!
# Actual physical weak pairings in the original canonical measure

The transported compact test is used in the physical equation. The actual
height and source changes of variables give the canonical equation, with
the type sign and the physical angular normalization retained. The input
height may be any weak L2 representative; no smooth approximation of that
height is assumed. The physical remainder and forcing can include the
original three scalar columns before this change of variables.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {φ : PolarPoint → ℝ}

theorem n06CanonicalTestPullback_source_operator
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n06CanonicalTestPullback S K z m φ)) p =
      (if K.positive m then -1 else (1 : ℝ)) * canonicalOperator S K L z m φ p := by
  have he := n06CanonicalTestPullback_operator (L := L) (φ := φ) hK hz hs hp
  cases hm : K.positive m <;>
    simp only [hm, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at he ⊢ <;>
    linarith only [he]

/-- The actual forcing paired with the transported physical test gives
its canonical source paired with the original test. -/
theorem n06_physicalMean_test_source
    (hK : N04PartA D S C K base ε) (hab : D.a ≤ D.b)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (f : PolarPoint → ℝ)
    (hperiod : Function.Periodic
      (fun p => f p * n06CanonicalTestPullback S K z m φ p) (0, Real.pi))
    (hint : IntegrableOn (fun p => f p * n06CanonicalTestPullback S K z m φ p)
      (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      f (r, θ) * n06CanonicalTestPullback S K z m φ (r, θ))) =
      Real.pi⁻¹ * ∫ p, canonicalSource S K z m f p * φ p ∂canonicalMeasure S K m := by
  have hflip : (fun p => n06CanonicalTestPullback S K z m φ p * f p) =
      (fun p => f p * n06CanonicalTestPullback S K z m φ p) :=
    funext (fun p => mul_comm _ _)
  have hmean := n06_physicalMean_pairing_eq_canonical hK hab hz hs m
    (n06CanonicalTestPullback S K z m φ) f
    (by rw [hflip]; exact hperiod) (by rw [hflip]; exact hint)
    (fun p hp => by rw [n06CanonicalTestPullback_eq_zero_of_not_mem hp, zero_mul])
  have hswap := congrArg (fun H : PolarPoint → ℝ =>
    ∫ r in D.a..D.b, radialAngularMean (fun θ => H (r, θ))) hflip
  refine hswap.symm.trans (hmean.trans ?_)
  apply congrArg (fun t : ℝ => Real.pi⁻¹ * t)
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  rw [n06CanonicalTestPullback_canonicalHeight hK hz hs ⟨hp.1, mem_univ _⟩]
  exact mul_comm _ _

/-- The physical differential pairing observes the original canonical
L2 height and exactly the signed canonical test operator. -/
theorem n06_physicalMean_test_operator
    (hK : N04PartA D S C K base ε) (hab : D.a ≤ D.b)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) (w : PolarPoint → ℝ) (W : CanonicalL2 S K m)
    (hW : (W : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] canonicalHeight S K z m w)
    (hperiod : Function.Periodic (fun p => w p *
      divergenceOperator (L.coefficients z) (n06CanonicalTestPullback S K z m φ) p)
        (0, Real.pi))
    (hint : IntegrableOn (fun p => w p *
      divergenceOperator (L.coefficients z) (n06CanonicalTestPullback S K z m φ) p)
        (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => w (r, θ) *
      divergenceOperator (L.coefficients z) (n06CanonicalTestPullback S K z m φ) (r, θ))) =
      Real.pi⁻¹ * ((if K.positive m then -1 else (1 : ℝ)) *
        ∫ p, W p * canonicalOperator S K L z m φ p ∂canonicalMeasure S K m) := by
  have hmean := n06_physicalMean_pairing_eq_canonical hK hab hz hs m w
    (divergenceOperator (L.coefficients z) (n06CanonicalTestPullback S K z m φ))
    hperiod hint (fun p hp => by
      rw [n06CanonicalTestPullback_divergence_zero_of_not_mem hK hz hs hφ _ hp, mul_zero])
  refine hmean.trans ?_
  apply congrArg (fun t : ℝ => Real.pi⁻¹ * t)
  calc
    _ = ∫ p, (if K.positive m then -1 else (1 : ℝ)) *
        (W p * canonicalOperator S K L z m φ p) ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      filter_upwards [hW, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hWp hp
      rw [← hWp, n06CanonicalTestPullback_source_operator hK hz hs ⟨hp.1, mem_univ _⟩]
      ring
    _ = _ := by rw [integral_const_mul]

/-- A true physical weak equation for the remainder and its corrected
forcing becomes the original canonical weak equation. Its only analytic
pairing hypotheses are the actual physical integrability used by Fubini. -/
theorem n06_canonicalWeakPairing_of_physical
    (hK : N04PartA D S C K base ε) (hab : D.a ≤ D.b)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) (w g : PolarPoint → ℝ) (W : CanonicalL2 S K m)
    (hW : (W : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] canonicalHeight S K z m w)
    (hperiodL : Function.Periodic (fun p => w p *
      divergenceOperator (L.coefficients z) (n06CanonicalTestPullback S K z m φ) p)
        (0, Real.pi))
    (hintL : IntegrableOn (fun p => w p *
      divergenceOperator (L.coefficients z) (n06CanonicalTestPullback S K z m φ) p)
        (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi))
    (hperiodR : Function.Periodic
      (fun p => g p * n06CanonicalTestPullback S K z m φ p) (0, Real.pi))
    (hintR : IntegrableOn (fun p => g p * n06CanonicalTestPullback S K z m φ p)
      (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi))
    (hweak : (∫ r in D.a..D.b, radialAngularMean (fun θ => w (r, θ) *
      divergenceOperator (L.coefficients z) (n06CanonicalTestPullback S K z m φ) (r, θ))) =
        ∫ r in D.a..D.b, radialAngularMean (fun θ =>
          g (r, θ) * n06CanonicalTestPullback S K z m φ (r, θ))) :
    (∫ p, W p * canonicalOperator S K L z m φ p ∂canonicalMeasure S K m) =
      ∫ p, ((if K.positive m then -1 else (1 : ℝ)) * canonicalSource S K z m g p) * φ p
        ∂canonicalMeasure S K m := by
  have hleft := n06_physicalMean_test_operator hK hab hz hs hφ w W hW hperiodL hintL
  have hright := n06_physicalMean_test_source hK hab hz hs g hperiodR hintR
  have he : (if K.positive m then -1 else (1 : ℝ)) *
      (∫ p, W p * canonicalOperator S K L z m φ p ∂canonicalMeasure S K m) =
        ∫ p, canonicalSource S K z m g p * φ p ∂canonicalMeasure S K m :=
    mul_left_cancel₀ (inv_ne_zero Real.pi_ne_zero) (hleft.symm.trans (hweak.trans hright))
  have hsign : (∫ p, W p * canonicalOperator S K L z m φ p ∂canonicalMeasure S K m) =
      (if K.positive m then -1 else (1 : ℝ)) *
        ∫ p, canonicalSource S K z m g p * φ p ∂canonicalMeasure S K m := by
    cases hm : K.positive m <;>
      simp only [hm, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at he ⊢ <;>
      linarith only [he]
  refine hsign.trans ?_
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  ring

/-- The physical left-height correction stays its actual source column
under the change of coordinates, with no implicit redistribution. -/
theorem n06_canonicalSource_sub_smul (f g : PolarPoint → ℝ) (aL : ℝ) (p : PolarPoint) :
    canonicalSource S K z m (fun q => f q - aL * g q) p =
      canonicalSource S K z m f p - aL * canonicalSource S K z m g p := by
  simp only [canonicalSource, div_eq_mul_inv]
  ring

end ContinuousFlexibility.Analysis
