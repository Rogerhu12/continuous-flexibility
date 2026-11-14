module

public import ContinuousFlexibility.Analysis.N07aForwardCoefficients
public import ContinuousFlexibility.Analysis.N07aMaterialDecay
public import ContinuousFlexibility.Analysis.N07aProfileCoefficient
public import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace
public import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# The actual controlled profile difference in a physical height space

The q=0 coefficient slice and the genuine N01 bounds imply weighted
membership of the profile difference. This uses no support assumption on
the closure of the distinguished control's support.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

local instance n07aProfileHeightInst1 (S : PhysicalSpacesData) : AddCommGroup (AnnularState S) := inferInstance
local instance n07aProfileHeightInst2 (S : PhysicalSpacesData) : Module ℝ (AnnularState S) := inferInstance
local instance n07aProfileHeightInst3 (S : PhysicalSpacesData) : AddGroup (AnnularState S) :=
  (inferInstance : AddCommGroup (AnnularState S)).toAddGroup
local instance n07aProfileHeightInst4 (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (inferInstance : Module ℝ (AnnularState S)).toSMul
local instance n07aProfileHeightInst5 (S : PhysicalSpacesData) : Sub (AnnularState S) :=
  (inferInstance : AddCommGroup (AnnularState S)).toSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n07a_stateProfile_reference (href : referenceStateConditions D S C) :
    stateProfile D S C C.referenceState = D.w := by
  funext r
  simp only [stateProfile, stateKappa, href.2.2.1, href.2.2.2.1,
    map_zero, Pi.zero_apply, angularMean, intervalIntegral.integral_zero,
    mul_zero, zero_mul, tsum_zero, add_zero, Real.exp_zero, mul_one]

def n07aProfileDifferenceField (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (x : AnnularState S) (p : PolarPoint) : ℝ := by
  classical
  exact if p ∈ annularOpen D then
    stateProfile D S C x p.1 - stateProfile D S C C.referenceState p.1 else 0

theorem n07aProfileDifferenceField_eqOn (x : AnnularState S) :
    EqOn (n07aProfileDifferenceField D S C x)
      (fun p : PolarPoint =>
        stateProfile D S C x p.1 - stateProfile D S C C.referenceState p.1)
      (annularOpen D) := by
  classical
  intro p hp
  simp only [n07aProfileDifferenceField, ite_eq_left hp]

/-- The genuine N01 coefficients place the actual profile variation in
every physical height space with exponent strictly below 3/64. -/
theorem n07aProfileDifferenceField_heightMember
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {γ : ℝ} (hγ : γ < 3 / 64) (x : AnnularState S)
    (hx : (x, 0) ∈ stateNeighborhood S C base ε) :
    HeightMember D T γ (n07aProfileDifferenceField D S C x) := by
  classical
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hglobal : ContDiff ℝ ∞ (fun p : PolarPoint =>
      stateProfile D S C x p.1 - stateProfile D S C C.referenceState p.1) :=
    ((contDiff_stateProfile_of_n01 hS hT h01 x).comp contDiff_fst).sub
      ((contDiff_stateProfile_of_n01 hS hT h01 C.referenceState).comp contDiff_fst)
  have hf : ContDiffOn ℝ ∞ (n07aProfileDifferenceField D S C x) (annularOpen D) :=
    hglobal.contDiffOn.congr (fun _ hp => n07aProfileDifferenceField_eqOn x hp)
  refine ⟨hf, ?_, ?_, ?_, ?_⟩
  · intro r θ
    simp only [n07aProfileDifferenceField, annularOpen, Set.mem_prod,
      Set.mem_univ, and_true]
  · intro p
    simp only [n07aProfileDifferenceField, annularOpen, Set.mem_prod,
      Prod.fst_add, add_zero, Set.mem_univ, and_true]
  · intro p hp
    simp only [n07aProfileDifferenceField, ite_eq_right hp]
  · intro a b c
    let bound := n07a_coefficientFamily_decay_bound hT h01 (a + b)
    let K : ℝ := bound.choose
    have hK : 0 < K := bound.choose_spec.1
    have hKb := bound.choose_spec.2
    let B : ℝ := K * (1 + n07aRawParameterSize S
      (a + b + loss) ((x, 0) - (C.referenceState, 0)))
    have hB : 0 ≤ B := mul_nonneg hK.le (by
      unfold n07aRawParameterSize
      positivity)
    apply n07a_weightedPhysicalJet_memLp_of_decay hT hγ hf a b c hB
    intro j hj p hp
    rw [mixedDerivative_eqOn_of_isOpen hU (n07aProfileDifferenceField_eqOn x) j b hp,
      ← n07a_coefficientFamily_profile_slice hS hT h01 j b p x]
    exact (hKb 0 j b p (Nat.add_le_add_right hj b) hp (x, 0) hx).trans_eq (by
      dsimp only [B]
      ring)

/-- The element is chosen through the actual frozen Sobolev decoder. -/
def n07aProfileDifferenceHeight
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {γ : ℝ} (hγ : γ < 3 / 64) (x : AnnularState S)
    (hx : (x, 0) ∈ stateNeighborhood S C base ε) : (S.height γ).Space :=
  SobolevModelData.liftHeight (hS.1 γ) (n07aProfileDifferenceField D S C x)
    (n07aProfileDifferenceField_heightMember hS hT h01 hγ x hx)

theorem n07aProfileDifferenceHeight_decode
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {γ : ℝ} (hγ : γ < 3 / 64) (x : AnnularState S)
    (hx : (x, 0) ∈ stateNeighborhood S C base ε) :
    (S.height γ).decode (n07aProfileDifferenceHeight hS hT h01 hγ x hx) =
      n07aProfileDifferenceField D S C x :=
  SobolevModelData.decode_liftHeight (hS.1 γ) _ _

theorem n07aProfileDifferenceHeight_decode_on
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {γ : ℝ} (hγ : γ < 3 / 64) (x : AnnularState S)
    (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (S.height γ).decode (n07aProfileDifferenceHeight hS hT h01 hγ x hx) p =
      stateProfile D S C x p.1 - D.w p.1 := by
  rw [n07aProfileDifferenceHeight_decode,
    n07aProfileDifferenceField_eqOn x hp, n07a_stateProfile_reference h01.2.2.1]

end ContinuousFlexibility.Analysis
