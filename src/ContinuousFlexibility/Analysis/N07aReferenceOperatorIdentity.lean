module

public import ContinuousFlexibility.Analysis.N07aReferenceCanonicalEquation
public import ContinuousFlexibility.Analysis.N07aPerturbedCanonicalEquation
public import ContinuousFlexibility.Analysis.N07aAngularEvenTestSeparation

/-!
# The actual perturbed operator equals the reference source at the reference state

Both frozen graphs are expressed in the same physical coordinates and the
same canonical functions. Genuine even test separation identifies their
source classes, so this is an equality of the actual operators rather than
an additional reference normalization assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B}

theorem n07a_volume_forget_reflection (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {s : ℕ} (F : V.level γ t s) (m : ℕ) :
    n07aAngularReflection m (V.forget γ t s F m) = V.forget γ t s F m := by
  have hgraph : F.val ∈ canonicalVolumeGraph S K s := by
    rw [← hV.1 γ t s]
    exact F.property
  have hfix := (n07aAngularReflection_fixed_iff m (F.val m 0)).mpr (hgraph.1 m)
  rw [hV.2.2.2 γ t s F m, map_smul, hfix]

theorem n07a_referenceOperator_distribution
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (h06 : N06Properties D S C K L V b B P base ε)
    (u : B.Space) (m : ℕ) (hm : K.left m < K.right m) :
    N07aCanonicalDistributionEquation S K m (K.coefficients (C.referenceState, 0) m)
      (u.val.1.1 m) (n07aReferenceCanonicalRhs hJ m hm u.val.1
        (V.forget (3 / 4 : ℝ) 0 b (P.operator (C.referenceState, 0) u))) := by
  have hz := n07a_reference_mem_stateNeighborhood h01
  have hs := h01.2.2.1.stateSector
  exact n07a_perturbedCanonical_distribution_of_coefficients hab h04 hz hs hS.2.2.1.1
    ((h06.2 _ hz hs).1 u)
    (n07aReferenceOpenCoefficient hJ m hm 0)
    (n07aReferenceOpenCoefficient hJ m hm 1)
    (n07aReferenceOpenCoefficient hJ m hm 2)
    (N07aCanonicalOpenCoefficient.constMul (if K.positive m then -1 else (1 : ℝ))
      (n07aReferenceOpenCoefficient hJ m hm 4))
    (n07aReferenceScalarOpenCoefficient hJ m hm)
    rfl rfl rfl rfl (fun _ => rfl)

theorem n07a_referenceOperator_eq_source
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε) (u : B.Space) :
    P.operator (C.referenceState, 0) u = u.val.2 := by
  have hV := h05.2.1
  apply hV.2.2.1 (3 / 4 : ℝ) 0 b
  funext m
  have hm := (h04.1.referenceBounds m).2.1
  apply n07a_canonical_even_test_separation hm
    (n07a_volume_forget_reflection hV (P.operator (C.referenceState, 0) u) m)
    (n07a_volume_forget_reflection hV u.val.2 m)
  intro W hW hWeven
  have hrel : ReferenceCanonicalRelation D T S C K V B.weakExponent
      B.sourceMaterial B.outputMaterial B.lossMaterial u.val.1
        (V.forget (3 / 4 : ℝ) 0 b u.val.2) :=
    (h05.2.2.2.2.2.2.1 u.val).mp u.property
  have hreference := n07a_referenceCanonical_distribution_even
    hab hS hT h01 h02 h03 h04 hJ hrel hm hW hWeven
  have hcurrent := n07a_referenceOperator_distribution hab hS h01 h04 hJ h06 u m hm W hW
  have he := hcurrent.symm.trans hreference
  simp only [n07aReferenceCanonicalRhs] at he
  rw [← n07aCanonicalTestPairing_apply W (n07a_canonicalTest_memLp hW),
    ← n07aCanonicalTestPairing_apply W (n07a_canonicalTest_memLp hW)] at he
  simp only [map_sub, map_smul, smul_eq_mul] at he
  have hcancel := sub_left_inj.mp he
  have hcancel := sub_left_inj.mp hcancel
  have hcancel := sub_left_inj.mp hcancel
  have hcancel := sub_left_inj.mp hcancel
  simpa only [n07aCanonicalTestPairing_apply] using hcancel

theorem n07a_referenceRelative_eq_zero
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (F : V.level (3 / 4 : ℝ) 0 b) : P.relative (C.referenceState, 0) F = 0 := by
  have hz := n07a_reference_mem_stateNeighborhood h01
  have hs := h01.2.2.1.stateSector
  rw [(h06.2 _ hz hs).2.1 F,
    n07a_referenceOperator_eq_source hab hS hT h01 h02 h03 h04 hJ h05 h06,
    h05.2.2.2.2.2.2.2.1 F, sub_self]

theorem n07a_referenceDomain_distribution
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (u : B.Space) (m : ℕ) (hm : K.left m < K.right m) :
    N07aCanonicalDistributionEquation S K m (K.coefficients (C.referenceState, 0) m)
      (u.val.1.1 m) (n07aReferenceCanonicalRhs hJ m hm u.val.1
        (V.forget (3 / 4 : ℝ) 0 b u.val.2)) := by
  simpa only [n07a_referenceOperator_eq_source hab hS hT h01 h02 h03 h04 hJ h05 h06] using
    n07a_referenceOperator_distribution hab hS h01 h04 hJ h06 u m hm

end ContinuousFlexibility.Analysis
