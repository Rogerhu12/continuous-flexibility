import ContinuousFlexibility.Analysis.N06PrimitiveC1Green
import ContinuousFlexibility.Analysis.N06PrimitiveModeRegularity
import ContinuousFlexibility.Analysis.N06CompactCanonicalTraces
import ContinuousFlexibility.Analysis.N06CanonicalTestSeparation
import ContinuousFlexibility.Analysis.N06ReferenceUnitEquation

/-!
# The actual reference forcing of a finite height on its original interval

The H2 modes determine their actual L2 flux residuals.  Closed Green,
applied to transported compact canonical tests, identifies their finite
synthesis with the complete original forcing.  The original compatibility
column is retained, and no finite support of the unmodified source is
assumed.  The leading reference coefficient needs only a C1 representative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial CanonicalGeometry
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The literal flux residual of one chosen H2 representative. -/
def n06PrimitiveModalForcing (a c V : ℝ → ℝ) (v : ℕ → ℝ → ℝ)
    (i : ℕ) (y : ℝ) : ℝ :=
  -deriv (fun t => a t * deriv (v i) t) y +
    (((2 * i : ℕ) : ℝ)) ^ 2 * c y * v i y + V y * v i y

theorem n06_primitiveModalForcing_memLp {l r : ℝ} (hlr : l ≤ r)
    {a c V : ℝ → ℝ} {v : ℕ → ℝ → ℝ} (i : ℕ)
    (ha : ContDiff ℝ 1 a) (hc : Continuous c) (hV : Continuous V)
    (hAC : AbsolutelyContinuousOnInterval (deriv (v i)) l r)
    (hv : MemLp (v i) 2 (volume.restrict (Ioo l r)))
    (hv₁ : MemLp (deriv (v i)) 2 (volume.restrict (Ioo l r)))
    (hv₂ : MemLp (deriv (deriv (v i))) 2 (volume.restrict (Ioo l r))) :
    MemLp (n06PrimitiveModalForcing a c V v i) 2 (volume.restrict (Ioo l r)) := by
  have hdiff : ∀ᵐ y ∂volume.restrict (Ioo l r),
      DifferentiableAt ℝ (deriv (v i)) y := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hAC.ae_differentiableAt] with y hy hylr
    apply hy
    simpa only [uIcc_of_le hlr] using mem_Icc_of_Ioo hylr
  have he : deriv (fun t => a t * deriv (v i) t)
      =ᵐ[volume.restrict (Ioo l r)]
        (fun y => deriv a y * deriv (v i) y + a y * deriv (deriv (v i)) y) := by
    filter_upwards [hdiff] with y hy
    exact ((ha.differentiable_one y).hasDerivAt.fun_mul hy.hasDerivAt).deriv
  have hflux : MemLp (deriv (fun t => a t * deriv (v i) t)) 2
      (volume.restrict (Ioo l r)) :=
    (memLp_congr_ae he).mpr
      ((n06_interval_memLp_mul_continuous hv₁ (ha.continuous_deriv le_rfl)).add
        (n06_interval_memLp_mul_continuous hv₂ ha.continuous))
  have hf := (hflux.neg.add
    ((n06_interval_memLp_mul_continuous hv hc).const_mul ((((2 * i : ℕ) : ℝ)) ^ 2))).add
      (n06_interval_memLp_mul_continuous hv hV)
  convert hf using 1 <;> funext y <;>
    simp only [n06PrimitiveModalForcing, Pi.add_apply, Pi.neg_apply] <;> ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  {a c pot : ℝ → ℝ}

/-- The true closed Green formula becomes the compact reference weak
equation because the transported test has zero true endpoint traces. -/
theorem n06_positive_finite_reference_weak_C1
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (ha : ContDiff ℝ 1 a) (hc : Continuous c) (hpot : Continuous pot)
    (s : Finset ℕ) (v f : ℕ → ℝ → ℝ)
    (hC : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (deriv (v i)) (K.left m) (K.right m))
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hf : ∀ i ∈ s, MemLp (f i) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hode : ∀ i ∈ s, ∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)),
      -deriv (fun t => a t * deriv (v i) t) y +
        (((2 * i : ℕ) : ℝ)) ^ 2 * c y * v i y + pot y * v i y = f i y)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p *
      n06UnitReferenceTestOperator a c pot φ p ∂canonicalMeasure S K m) =
      ∫ p, r11bFiniteSynthesis s f referenceAngularBasis p * φ p
        ∂canonicalMeasure S K m := by
  let Φ := n06CanonicalTestPullback S K z m φ
  have hΦ := n06_canonicalTest_transport h04 hz hs hφ
  obtain ⟨Q⟩ := n06_currentHeightTest_exists_traces h04 hz hs m hΦ.1.1
  have htrace := Q.compactPullback_closed h04 hz hs hφ
  have hg := Q.finite_positive_green_C1 h04 hz hs hΦ.1.1 hΦ.2.1
    ha hc hpot s v f hC hAC hv hf hode
  have hvalue :
      (∫ p, r11bFiniteSynthesis s f referenceAngularBasis p *
        canonicalHeight S K z m Φ p ∂canonicalMeasure S K m) =
      ∫ p, r11bFiniteSynthesis s f referenceAngularBasis p * φ p
        ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    rw [(n06CanonicalTestPullback_height_germ h04 hz hs
      (φ := φ) ⟨hp.1, mem_univ _⟩).eq_of_nhds]
  have hoperator :
      (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p *
        n06UnitReferenceTestOperator a c pot (canonicalHeight S K z m Φ) p
          ∂canonicalMeasure S K m) =
      ∫ p, r11bFiniteSynthesis s v referenceAngularBasis p *
        n06UnitReferenceTestOperator a c pot φ p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    rw [n06UnitReferenceTestOperator_input_congr_germ a c pot
      (n06CanonicalTestPullback_height_germ h04 hz hs (φ := φ) ⟨hp.1, mem_univ _⟩)]
  have hzero (y : ℝ) (hy : y ∈ Icc (K.left m) (K.right m))
      (hyo : y ∉ Ioo (K.left m) (K.right m)) (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
      Q.value (y, θ) = 0 ∧ Q.radial (y, θ) = 0 := by
    rw [htrace.1 ⟨hy, hθ⟩, htrace.2 ⟨hy, hθ⟩]
    exact hφ.n06_value_radial_zero_of_not_mem hyo θ
  have hboundary :
      (∫ θ in (0 : ℝ)..Real.pi,
        a (K.left m) * (Q.value (K.left m, θ) *
          radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.left m, θ) -
            r11bFiniteSynthesis s v referenceAngularBasis (K.left m, θ) *
              Q.radial (K.left m, θ)) -
        a (K.right m) * (Q.value (K.right m, θ) *
          radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.right m, θ) -
            r11bFiniteSynthesis s v referenceAngularBasis (K.right m, θ) *
              Q.radial (K.right m, θ))) = 0 := by
    calc
      _ = ∫ _θ in (0 : ℝ)..Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        have ht : θ ∈ Icc (0 : ℝ) Real.pi := by
          simpa only [uIcc_of_le Real.pi_pos.le] using hθ
        have hlr := (h04.1.referenceBounds m).2.1.le
        have h₀ := hzero (K.left m) ⟨le_rfl, hlr⟩ (by simp) θ ht
        have h₁ := hzero (K.right m) ⟨hlr, le_rfl⟩ (by simp) θ ht
        simp only [h₀.1, h₀.2, h₁.1, h₁.2, zero_mul, mul_zero, sub_self, sub_zero]
      _ = 0 := by simp
  rw [hvalue, hoperator, hboundary] at hg
  exact (sub_eq_zero.mp hg).symm

/-- Separation identifies the full L2 forcing from the actual finite
height and its reference equation, retaining all scalar columns. -/
theorem n06_positive_forcing_eq_finite_C1
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (ha : ContDiff ℝ 1 a) (hc : Continuous c) (hpot : Continuous pot)
    (U : CanonicalL2 S K m) {F : PolarPoint → ℝ}
    (hF : MemLp F 2 (canonicalMeasure S K m))
    (s : Finset ℕ) (v f : ℕ → ℝ → ℝ)
    (hC : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (deriv (v i)) (K.left m) (K.right m))
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hf : ∀ i ∈ s, MemLp (f i) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hode : ∀ i ∈ s, ∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)),
      -deriv (fun t => a t * deriv (v i) t) y +
        (((2 * i : ℕ) : ℝ)) ^ 2 * c y * v i y + pot y * v i y = f i y)
    (hvalue : (U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s v referenceAngularBasis)
    (hweak : ∀ φ, CanonicalTest S K m φ →
      (∫ p, U p * n06UnitReferenceTestOperator a c pot φ p ∂canonicalMeasure S K m) =
        ∫ p, F p * φ p ∂canonicalMeasure S K m) :
    F =ᵐ[canonicalMeasure S K m] r11bFiniteSynthesis s f referenceAngularBasis := by
  have hsf : MemLp (r11bFiniteSynthesis s f referenceAngularBasis) 2
      (canonicalMeasure S K m) := by
    unfold r11bFiniteSynthesis
    exact memLp_finsetSum s (fun i hi => n06_canonical_tensor_memLp
      (hf i hi) (contDiff_referenceAngularBasis i).continuous)
  let G : CanonicalL2 S K m := hsf.toLp (r11bFiniteSynthesis s f referenceAngularBasis)
  let F₀ : CanonicalL2 S K m := hF.toLp F
  have hG := hsf.coeFn_toLp
  have hF₀ := hF.coeFn_toLp
  have he : F₀ = G := by
    apply n06_canonicalL2_test_ext
    intro φ hφ
    calc
      (∫ p, F₀ p * φ p ∂canonicalMeasure S K m) =
          ∫ p, F p * φ p ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hF₀] with p hp
        rw [hp]
      _ = ∫ p, U p * n06UnitReferenceTestOperator a c pot φ p
          ∂canonicalMeasure S K m := (hweak φ hφ).symm
      _ = ∫ p, r11bFiniteSynthesis s v referenceAngularBasis p *
          n06UnitReferenceTestOperator a c pot φ p ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hvalue] with p hp
        rw [hp]
      _ = ∫ p, r11bFiniteSynthesis s f referenceAngularBasis p * φ p
          ∂canonicalMeasure S K m :=
        n06_positive_finite_reference_weak_C1 h04 hz hs ha hc hpot s v f
          hC hAC hv hf hode hφ
      _ = ∫ p, G p * φ p ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hG] with p hp
        rw [hp]
  have he_ae : (F₀ : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      (G : PolarPoint → ℝ) :=
    Eventually.of_forall fun p => congrArg (fun v : CanonicalL2 S K m => v p) he
  exact hF₀.symm.trans (he_ae.trans hG)

variable {Vol : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K Vol b}

theorem n06N05_primitive_referenceForcing_memLp
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (u : B.Space) (m : ℕ) :
    MemLp (n06ReferenceCanonicalForcing D S C K u.val.1
      (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m) 2 (canonicalMeasure S K m) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hi (i : Fin 3) : MemLp (canonicalSource S K (C.referenceState, 0) m
      (n06ReferenceScalarField D S i)) 2 (canonicalMeasure S K m) :=
    n06_current_canonicalSource_memLp h04 hz hs m
      (n06_referenceScalarField_contDiff h01.1.1 hT hS h01.1.2.2.2.1 i).continuous.continuousOn
  unfold n06ReferenceCanonicalForcing
  exact ((((Lp.memLp (Vol.forget (3 / 4 : ℝ) 0 b u.val.2 m)).neg.add
    ((hi 0).const_mul u.val.1.2.1)).add ((hi 1).const_mul u.val.1.2.2.1)).add
      ((hi 2).const_mul u.val.1.2.2.2))

theorem n06N05_primitive_positive_finite_referenceForcing
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (u : B.Space) (hm : K.positive m = true)
    (ha : ContDiff ℝ 1 a) (hc : Continuous c) (hpot : Continuous pot)
    (hcd : ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ c y)
    (hea : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun p => a p.1) (canonicalOpen S K m))
    (heb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun p => c p.1) (canonicalOpen S K m))
    (hepot : EqOn (K.potential (C.referenceState, 0) m)
      (fun p => pot p.1) (canonicalOpen S K m))
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hC : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (deriv (v i)) (K.left m) (K.right m))
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hvalue : (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s v referenceAngularBasis) :
    n06ReferenceCanonicalForcing D S C K u.val.1
      (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s (n06PrimitiveModalForcing a c pot v) referenceAngularBasis := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hf (i : ℕ) (hi : i ∈ s) := n06_primitiveModalForcing_memLp
    (h04.1.referenceBounds m).2.1.le i ha hc hpot (hAC i hi) (hv i hi) (hv₁ i hi) (hv₂ i hi)
  apply n06_positive_forcing_eq_finite_C1 h04 hz hs ha hc hpot (u.val.1.1 m)
    (n06N05_primitive_referenceForcing_memLp hT hS h u m) s v
    (n06PrimitiveModalForcing a c pot v) hC hAC hv hf
    (fun _ _ => Eventually.of_forall fun _ => rfl) hvalue
  intro ψ hψ
  exact n06N05_positive_unitWeakPairing h01.1.1 h01.1.2.2.2.1 hS h03
    (n06_N04_qualitative_parts h04).1 (n06_N04_qualitative_parts h04).2 h.2
    h01.2.2.1 hz hs u hm hea heb hec hepot hcd hψ

end ContinuousFlexibility.Analysis
