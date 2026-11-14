module

public import ContinuousFlexibility.Analysis.N05CanonicalAngularColumns

/-!
# Physical weak angular identities on the actual smooth canonical core

Canonical smooth single-cell jets are transported without parity averaging.
Their fixed physical representatives agree almost everywhere with the
ordinary derivatives of the genuine radial transport. Physical L² pairings
then identify their full-period weak angular jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open scoped ContDiff Topology

theorem n05_sourceWeakJet_congr_ae {D : ReferenceData} (hab : D.a ≤ D.b)
    {u d u' d' : PolarPoint → ℝ} {j : ℕ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (huu' : u =ᵐ[radialPhysicalMeasure D] u')
    (hdd' : d =ᵐ[radialPhysicalMeasure D] d')
    (hw : n05_weakReferenceAngularJet D u d j) :
    n05_weakReferenceAngularJet D u' d' j := by
  have hu' := MemLp.ae_eq huu' hu
  have hd' := MemLp.ae_eq hdd' hd
  intro φ hφ
  have hφLp : MemLp φ 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp hφ.1.continuous
  have hφjLp : MemLp (mixedDerivative 0 j φ) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (contDiff_mixedDerivative hφ.1 0 j).continuous
  have hl := r11b_integral_angularMean_congr_ae hab
    (hd'.integrable_mul hφLp) (hd.integrable_mul hφLp)
    (hdd'.symm.mul (Filter.EventuallyEq.rfl))
  have hr := r11b_integral_angularMean_congr_ae hab
    (hu'.integrable_mul hφjLp) (hu.integrable_mul hφjLp)
    (huu'.symm.mul (Filter.EventuallyEq.rfl))
  simp only [Pi.mul_apply] at hl hr
  rw [hl, hr]
  exact hw φ hφ

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include h hcoordinates in
/-- The actual single-cell jet source has its genuine smooth transport
representative, with the same sample multiplier at every angular order. -/
theorem n05CanonicalJetSource_smooth_single_ae (γ t : ℝ) (m s : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) (j : Fin (s + 1)) :
    n05CanonicalJetSource T S C K γ t s j
        (n05CanonicalSmoothSingleRaw S K m s hφ.1) =ᵐ[radialPhysicalMeasure D]
      (fun p => n05CanonicalSampleWeight T S K γ t m *
        n05CanonicalAngularTransport S C K m (mixedDerivative 0 j.val φ) p) := by
  classical
  let F : CanonicalSequence S K := Pi.single m (n05CanonicalSmoothJet S K m hφ.1 j.val)
  have he : (fun k => n05CanonicalSampleWeight T S K γ t k •
      n05CanonicalAngularColumn S K s j (n05CanonicalSmoothSingleRaw S K m s hφ.1) k) =
        n05CanonicalSampleWeight T S K γ t m • F := by
    funext k
    rw [n05CanonicalAngularColumn_apply]
    by_cases hkm : k = m
    · subst k
      simp only [n05CanonicalSmoothSingleRaw_self, Pi.smul_apply, F, Pi.single_eq_same]
    · simp only [n05CanonicalSmoothSingleRaw_ne S K m s hφ.1 hkm, smul_zero,
        Pi.smul_apply, F, Pi.single_eq_of_ne hkm]
  have hscaled : n05CanonicalAngularLift S C K
      (n05CanonicalSampleWeight T S K γ t m • F) =ᵐ[radialPhysicalMeasure D]
        (fun p => n05CanonicalSampleWeight T S K γ t m * n05CanonicalAngularLift S C K F p) := by
    simpa only [zero_smul, add_zero, zero_mul] using
      n05CanonicalAngularLift_linear_combination_ae h hcoordinates F F
        (n05CanonicalSampleWeight T S K γ t m) 0
  unfold n05CanonicalJetSource n05CanonicalAngularSource
  rw [he]
  filter_upwards [hscaled,
    n05CanonicalAngularLift_smooth_single_ae h hcoordinates m hφ.1 hφ.2.1 j.val]
    with p hp hq
  exact hp.trans (congrArg (fun x : ℝ => n05CanonicalSampleWeight T S K γ t m * x) hq)

include h hcoordinates in
theorem n05CanonicalJetSource_smooth_single_weak (hab : D.a ≤ D.b)
    (γ t : ℝ) (m s : ℕ) {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ)
    (j : Fin (s + 1)) :
    n05_weakReferenceAngularJet D
      (n05CanonicalJetSource T S C K γ t s 0 (n05CanonicalSmoothSingleRaw S K m s hφ.1))
      (n05CanonicalJetSource T S C K γ t s j (n05CanonicalSmoothSingleRaw S K m s hφ.1))
      j.val := by
  have hzero : mixedDerivative 0 0 φ = φ := by
    funext p
    simp only [mixedDerivative, iteratedDeriv_zero, Prod.eta]
  have h0 : n05CanonicalJetSource T S C K γ t s 0
      (n05CanonicalSmoothSingleRaw S K m s hφ.1) =ᵐ[radialPhysicalMeasure D]
        (fun p => n05CanonicalSampleWeight T S K γ t m *
          n05CanonicalAngularTransport S C K m φ p) := by
    simpa only [Fin.val_zero, hzero] using
      n05CanonicalJetSource_smooth_single_ae h hcoordinates γ t m s hφ 0
  have hj := n05CanonicalJetSource_smooth_single_ae h hcoordinates γ t m s hφ j
  have ht := n05CanonicalAngularTransport_test h hcoordinates m hφ
  have hu : MemLp (n05CanonicalAngularTransport S C K m φ) 2
      (radialPhysicalMeasure D) := r11b_continuous_memLp ht.1.continuous
  have hd : MemLp (n05CanonicalAngularTransport S C K m (mixedDerivative 0 j.val φ)) 2
      (radialPhysicalMeasure D) := by
    have he : mixedDerivative 0 j.val (n05CanonicalAngularTransport S C K m φ) =
        n05CanonicalAngularTransport S C K m (mixedDerivative 0 j.val φ) :=
      funext (n05CanonicalAngularTransport_angular S C K m φ j.val)
    rw [← he]
    exact r11b_continuous_memLp (contDiff_mixedDerivative ht.1 0 j.val).continuous
  exact n05_sourceWeakJet_congr_ae hab
    (hu.const_mul (n05CanonicalSampleWeight T S K γ t m))
    (hd.const_mul (n05CanonicalSampleWeight T S K γ t m)) h0.symm hj.symm
    (n05_weakReferenceAngularJet_const_mul
      (n05CanonicalAngularTransport_weak h hcoordinates m hφ j.val)
        (n05CanonicalSampleWeight T S K γ t m))

end ContinuousFlexibility.Statements
