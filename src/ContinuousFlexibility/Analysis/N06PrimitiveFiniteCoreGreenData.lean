module

public import ContinuousFlexibility.Analysis.N06PrimitiveReferenceRepresentatives
public import ContinuousFlexibility.Analysis.N06PrimitivePositiveFiniteGreen
public import ContinuousFlexibility.Analysis.N06PrimitiveNegativeFiniteGreen
public import ContinuousFlexibility.Analysis.N06PrimitiveFiniteBoundaryMatching
public import ContinuousFlexibility.Analysis.N06PrimitiveFiniteGreenRelation
public import ContinuousFlexibility.Analysis.N06FiniteHeightModes

/-!
# Actual finite Green data on the original primitive atlas

The original graph supplies genuine H2 representatives on every original
interval. One common finite set reconstructs all its height fields. The
reference coefficient representatives, actual principal source pairing,
and original negative equation give the two local Green formulas. The
primitive shared first jets and actual moving-cut law cancel their true
boundary terms. No coordinate replacement or unit interval is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial CanonicalGeometry
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem n06_primitive_reference_c_representative_differentiable
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    (href : ReferenceJets D T S C L K) {m : ℕ} (hlen : K.left m < K.right m)
    {c : ℝ → ℝ}
    (hec : EqOn (K.coefficients (C.referenceState, 0) m).c (fun p => c p.1)
      (canonicalOpen S K m)) :
    ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ c y := by
  intro y hy
  have hc : ContDiffOn ℝ ∞ (K.coefficients (C.referenceState, 0) m).c
      (canonicalOpen S K m) := (n07aReferenceOpenCoefficient href m hlen 2).smooth
  have hp : (y, (0 : ℝ)) ∈ canonicalOpen S K m := ⟨hy, mem_univ _⟩
  have hd := (hc.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt
    (by simp)
  have hline : DifferentiableAt ℝ (fun r : ℝ => (r, (0 : ℝ))) y :=
    differentiableAt_id.prodMk (differentiableAt_const 0)
  have he : (fun r : ℝ => (K.coefficients (C.referenceState, 0) m).c (r, 0))
      =ᶠ[𝓝 y] c := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with r hr
    exact hec ⟨hr, mem_univ _⟩
  exact (hd.comp y hline).congr_of_eventuallyEq he.symm

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {Vol : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K Vol b} {z : AnnularState S × ℝ}

private theorem n06N05_primitive_finiteCore_pieceGreen
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (a c pot : ℕ → ℝ → ℝ)
    (ha : ∀ m, ContDiff ℝ 1 (a m)) (hc : ∀ m, Continuous (c m))
    (hpot : ∀ m, Continuous (pot m))
    (hea : ∀ m, EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun p => a m p.1) (canonicalOpen S K m))
    (heb : ∀ m, EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : ∀ m, EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun p => c m p.1) (canonicalOpen S K m))
    (hepot : ∀ m, EqOn (K.potential (C.referenceState, 0) m)
      (fun p => pot m p.1) (canonicalOpen S K m))
    (hcd : ∀ m, ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ (c m) y)
    (u : B.Space) (hu : u ∈ n06CanonicalGraphFiniteAngularCore B)
    (G Fcur : CanonicalSequence S K)
    (hsource : ∀ m, (Fcur m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CurrentRelativeSourceField D S C L K z u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) G m)
    (hweak : ∀ m, K.positive m = true → ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, G m p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u.val.1.1 m p * divergenceOperator
          (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
            (K.dividedDifference z m).a (K.dividedDifference z m).b
            (K.dividedDifference z m).c) ψ p ∂canonicalMeasure S K m)
    (hnegative : ∀ m, K.positive m ≠ true → G m = 0) :
    ∃ s : Finset ℕ, ∃ v : ℕ → ℕ → ℝ → ℝ,
      (∀ m i, ContDiff ℝ 1 (v m i)) ∧
      (∀ m i, n06HalfCosineCoefficient (u.val.1.1 m) i
        =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v m i) ∧
      (∀ m, (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        r11bFiniteSynthesis s (v m) referenceAngularBasis) ∧
      (∀ m, ContDiff ℝ 1 (r11bFiniteSynthesis s (v m) referenceAngularBasis)) ∧
      ∀ φ, RadialTest D φ →
        ∀ Q : ∀ m, N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ),
          ∀ m,
            (∫ p, n06CurrentRemainderSource D S C L K z u.val.1 Fcur m p *
              canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
            (∫ p, r11bFiniteSynthesis s (v m) referenceAngularBasis p * canonicalSource S K z m
              (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
                ∂canonicalMeasure S K m) =
            ∫ θ in (0 : ℝ)..Real.pi,
              (if K.positive m = true then a m (K.right m) else 1) *
                ((Q m).value (K.right m, θ) *
                    radialPartial (r11bFiniteSynthesis s (v m) referenceAngularBasis) (K.right m, θ) -
                  r11bFiniteSynthesis s (v m) referenceAngularBasis (K.right m, θ) *
                    (Q m).radial (K.right m, θ)) -
              (if K.positive m = true then a m (K.left m) else 1) *
                ((Q m).value (K.left m, θ) *
                    radialPartial (r11bFiniteSynthesis s (v m) referenceAngularBasis) (K.left m, θ) -
                  r11bFiniteSynthesis s (v m) referenceAngularBasis (K.left m, θ) *
                    (Q m).radial (K.left m, θ)) := by
  classical
  have hpos (m : ℕ) (hm : K.positive m = true) :=
    n06N05_primitive_positive_modes_regular hS h href hprincipal u m hm
  choose vp hvp using hpos
  have hex (m : ℕ) (hm : K.positive m = false) :
      ∃ Gn : CanonicalL2 S K m,
        (Gn : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          n06NegativePrincipalForcing D S C K u.val.1
            (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m ∧
        Nonempty (N06NegativeGraphApproximation (u.val.1.1 m) Gn) :=
    n06N05_negative_graphApproximation hT hS h u m hm
  choose Gn hGn hPn using hex
  let Pneg (m : ℕ) (hm : K.positive m = false) :
      N06NegativeGraphApproximation (u.val.1.1 m) (Gn m hm) := Classical.choice (hPn m hm)
  let v (m : ℕ) : ℕ → ℝ → ℝ :=
    if hm : K.positive m = true then vp m hm
    else (Pneg m (Bool.eq_false_of_not_eq_true hm)).modes
  have hregular (m i : ℕ) : ContDiff ℝ 1 (v m i) := by
    by_cases hm : K.positive m = true
    · simpa only [v, dif_pos hm] using (hvp m hm i).2.1
    · simpa only [v, dif_neg hm] using
        (Pneg m (Bool.eq_false_of_not_eq_true hm)).contDiff i
  have hmode (m i : ℕ) : n06HalfCosineCoefficient (u.val.1.1 m) i
      =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v m i := by
    by_cases hm : K.positive m = true
    · simpa only [v, dif_pos hm] using (hvp m hm i).1
    · simpa only [v, dif_neg hm] using
        (Pneg m (Bool.eq_false_of_not_eq_true hm)).coefficient i
  obtain ⟨s, hvalue⟩ := n06CanonicalGraphFiniteAngularCore_actual_modes u hu v hmode
  refine ⟨s, v, hregular, hmode, hvalue, ?_, ?_⟩
  · intro m
    exact n06_contDiff_one_finiteSynthesis s (v m) referenceAngularBasis
      (fun i _ => hregular m i)
      (fun i _ => (contDiff_referenceAngularBasis i).of_le (by simp))
  · intro φ hφ Q m
    by_cases hm : K.positive m = true
    · have hv : (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          r11bFiniteSynthesis s (vp m hm) referenceAngularBasis := by
        simpa only [v, dif_pos hm] using hvalue m
      have he := n06N05_primitive_positive_finite_relative_green hT hS h href hcur
        hz hs u hm (ha m) (hc m) (hpot m) (hcd m) (hea m) (heb m) (hec m) (hepot m)
        s (vp m hm) (fun i _ => (hvp m hm i).2.1)
        (fun i _ => (hvp m hm i).2.2.1) (fun i _ => (hvp m hm i).2.2.2.1)
        (fun i _ => (hvp m hm i).2.2.2.2.1) (fun i _ => (hvp m hm i).2.2.2.2.2)
        hv G Fcur (hsource m) (hweak m hm) hφ (Q m)
      simpa only [v, dif_pos hm, if_pos hm] using he
    · have hn : K.positive m = false := Bool.eq_false_of_not_eq_true hm
      have hv : (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          r11bFiniteSynthesis s (Pneg m hn).modes referenceAngularBasis := by
        simpa only [v, dif_neg hm] using hvalue m
      have he := n06N05_primitive_negative_finite_relative_green hT hS h hz hs u m hn
        (Pneg m hn) (hGn m hn) s hv G Fcur (hsource m) (hnegative m hm) hφ (Q m)
      simpa only [v, dif_neg hm, if_neg hm, one_mul] using he

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial CanonicalGeometry
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- All actual finite Green data follow from the same original N05
graph and primitive geometry. The only source premises are the already
constructed principal pairing, its negative zero, and full source identity. -/
theorem n06N05_primitive_finiteCore_greenData
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {Vol : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K Vol b} {z : AnnularState S × ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hradial : ReferenceRadial S C K)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (htransmission : TransmissionGeometry D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : B.Space) (hu : u ∈ n06CanonicalGraphFiniteAngularCore B)
    (G Fcur : CanonicalSequence S K)
    (hsource : ∀ m, (Fcur m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CurrentRelativeSourceField D S C L K z u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) G m)
    (hweak : ∀ m, K.positive m = true → ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, G m p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u.val.1.1 m p * divergenceOperator
          (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
            (K.dividedDifference z m).a (K.dividedDifference z m).b
            (K.dividedDifference z m).c) ψ p ∂canonicalMeasure S K m)
    (hnegative : ∀ m, K.positive m ≠ true → G m = 0) :
    ∀ φ, RadialTest D φ →
      Nonempty (N06CurrentFiniteGreenData D S C L K z u.val.1 Fcur φ) := by
  classical
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hrepresentatives (m : ℕ) := n06_primitiveReference_coefficients_representatives
    href hprincipal m (h04.1.referenceBounds m).2.1
  choose a c pot ha hc hpot hea heb hec hepot using hrepresentatives
  have hcd (m : ℕ) : ∀ y ∈ Ioo (K.left m) (K.right m),
      DifferentiableAt ℝ (c m) y :=
    n06_primitive_reference_c_representative_differentiable href
      (h04.1.referenceBounds m).2.1 (hec m)
  obtain ⟨s, v, hv, hmode, hvalue, hregular, hgreen⟩ :=
    n06N05_primitive_finiteCore_pieceGreen hT hS h href hcur hprincipal hz hs
      a c pot ha hc hpot hea heb hec hepot hcd u hu G Fcur hsource hweak hnegative
  obtain ⟨reverse, J⟩ := n06_exists_atlasTransmissionJets_of_primitive
    h01 h04 htransmission hz hs
  intro φ hφ
  have havg : ContDiff ℝ ∞ (n06_radialTestAverage φ) :=
    (n06_radialTestAverage_test hφ).1
  let Q (m : ℕ) : N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ) :=
    Classical.choice (n06_currentHeightTest_exists_traces h04 hz hs m havg)
  refine ⟨{
    test := Q
    value := fun m => r11bFiniteSynthesis s (v m) referenceAngularBasis
    radialCoefficient := fun m y => if K.positive m = true then a m y else 1
    reverse := reverse
    regular := hregular
    represents := hvalue
    endpointCircles := J.endpointInverseRadius h01.2.2.2.1 h04 hz hs
    green := hgreen φ hφ Q
    matching := ?_
  }⟩
  intro ml mr hjoin θ hθ
  exact n06N05_primitive_finite_atlas_orientedMatching hT hS h hradial hz hs a
    (fun m _ => (ha m).continuous) (fun m _ => hea m) (fun m _ => heb m)
    (fun m _ => n06_primitive_current_principal_smooth h01 h04 href hcur hz hs m)
    reverse J u s v (fun m n _ => hv m n) (fun m n _ => hmode m n)
    havg Q ml mr hjoin hθ

end ContinuousFlexibility.Statements
