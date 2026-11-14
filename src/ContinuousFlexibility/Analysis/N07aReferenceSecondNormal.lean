module

public import ContinuousFlexibility.Analysis.N07aReferenceFiniteJets
public import ContinuousFlexibility.Analysis.N07aReferenceOpenCoefficients
public import ContinuousFlexibility.Analysis.N07aOpenDistributionFlux
public import ContinuousFlexibility.Analysis.N07aOpenNormalBootstrap

/-!
# Actual second normal derivatives of the reference inverse

N05 supplies the four finite jets. The original canonical distribution
equation and the genuine reciprocal leading coefficient then recover an
L² second derivative on the entire open canonical piece.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S} {m : ℕ}

theorem n07a_reference_secondNormal_of_fourJets
    (hJ : ReferenceJets D T S C L K) (hP : ReferencePrincipal T S C K)
    (hm : K.left m < K.right m) {u ur uθ urθ uθθ G : CanonicalL2 S K m}
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1)
    (heq : N07aCanonicalDistributionEquation S K m (K.coefficients (C.referenceState, 0) m) u G) :
    ∃ urr : CanonicalL2 S K m,
      N07aWeakCanonicalMixedDerivative S K m ur urr 1 0 ∧
      N07aWeakCanonicalMixedDerivative S K m u urr 2 0 := by
  let a := n07aReferenceOpenCoefficient hJ m hm 0
  let b := n07aReferenceOpenCoefficient hJ m hm 1
  let c := n07aReferenceOpenCoefficient hJ m hm 2
  let ρ := n07aReferenceOpenCoefficient hJ m hm 3
  have hi : ∀ᵐ p ∂canonicalMeasure S K m, ρ.value p * a.value p = 1 := by
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    change ((K.coefficients (C.referenceState, 0) m).a p)⁻¹ *
      (K.coefficients (C.referenceState, 0) m).a p = 1
    exact inv_mul_cancel₀ (hP.1 m p hp).1.ne'
  have heq' : N07aCanonicalDistributionEquation S K m ⟨a.value, b.value, c.value⟩ u G := heq
  have hflux := n07a_openDistribution_flux a b c hr hθ heq'
  exact ⟨n07aOpenSecondNormalRhs a b c ρ G ur uθ urθ uθθ,
    n07a_openWeak_secondNormal a b c ρ hi hr hθ hrθ hθθ hflux⟩

variable {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}

local instance n07aReferenceSecondLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _

local instance n07aReferenceSecondLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _

local instance n07aReferenceSecondUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance

local instance n07aReferenceSecondUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance

local instance n07aReferenceSecondGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _

local instance n07aReferenceSecondGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

def n07aReferenceInverseField (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    CanonicalL2 S K m := (B.inverse F).val.1.1 m

theorem n07a_referenceInverse_secondNormal
    (h05 : N05Properties D T S C K V b B)
    (hJ : ReferenceJets D T S C L K) (hP : ReferencePrincipal T S C K)
    (F : V.level (3 / 4 : ℝ) 0 b) (hm : K.left m < K.right m)
    (G : CanonicalL2 S K m)
    (heq : N07aCanonicalDistributionEquation S K m (K.coefficients (C.referenceState, 0) m)
      (n07aReferenceInverseField (B := B) F m) G) :
    ∃ ur urr : CanonicalL2 S K m,
      N07aWeakCanonicalMixedDerivative S K m (n07aReferenceInverseField (B := B) F m) ur 1 0 ∧
      N07aWeakCanonicalMixedDerivative S K m ur urr 1 0 ∧
      N07aWeakCanonicalMixedDerivative S K m (n07aReferenceInverseField (B := B) F m) urr 2 0 := by
  obtain ⟨ur, uθ, urθ, uθθ, hr, hθ, hrθ, hθθ⟩ := n07a_referenceInverse_finiteJets h05 F m
  obtain ⟨urr, hurr, hurr₂⟩ := n07a_reference_secondNormal_of_fourJets hJ hP hm hr hθ hrθ hθθ heq
  exact ⟨ur, urr, hr, hurr, hurr₂⟩

end ContinuousFlexibility.Analysis
