module

public import ContinuousFlexibility.Analysis.N07aMixedAngularProduct
public import ContinuousFlexibility.Scalar.WeightedScalarOperator

/-!
# The actual divergence operator for mixed coefficient weights

The coefficient perturbations carry a small positive weight. The unknown
retains weight three quarters. The odd coefficient is the angular
derivative of its actual even primitive, and the free left endpoint
constant is included through the common radial derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n07aMixedNormalCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 ≤ γ)
    (a b : (S.height γ).Space) : ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  (n07aMixedHeightMultiplyCLM hT hS hγ scalarBeta a).comp
      (scalarCommonRadialCLM hD hT hS) +
    (n07aMixedAngularJetCLM hT hS hγ scalarBeta b).comp
      (scalarCommonProjectionCLM S)

def n07aMixedAngularCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 ≤ γ)
    (b c : (S.height γ).Space) : ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  (n07aMixedHeightMultiplyCLM hT hS hγ scalarBeta
      (SobolevModelData.angularSecondCLM hT (hS.1 γ) b)).comp
        (scalarCommonRadialCLM hD hT hS) +
    (n07aMixedAngularJetCLM hT hS hγ scalarBeta b).comp
      (scalarCommonRadialCLM hD hT hS) +
    (n07aMixedHeightMultiplyCLM hT hS hγ scalarBeta c).comp
      ((SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta)).comp
        (scalarCommonProjectionCLM S)) +
    (n07aMixedAngularJetCLM hT hS hγ scalarBeta c).comp
      (scalarCommonProjectionCLM S)

def n07aMixedCoefficientOperatorCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 ≤ γ)
    (a b c : (S.height γ).Space) : ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  (SobolevModelData.radialCLM hT (hS.1 scalarBeta)).comp
      (n07aMixedNormalCLM hD hT hS hγ a b) +
    n07aMixedAngularCLM hD hT hS hγ b c

theorem n07aMixedNormalCLM_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 < γ)
    (a b : (S.height γ).Space) (u : ScalarCommonHeight S) :
    (S.height scalarBeta).decode (n07aMixedNormalCLM hD hT hS hγ.le a b u) =
      fun p => (S.height γ).decode a p * radialPartial (scalarCommonHeightDecode S u) p +
        angularPartial ((S.height γ).decode b) p * angularPartial (scalarCommonHeightDecode S u) p := by
  have hθ : angularPartial (scalarCommonHeightDecode S u) =
      angularPartial ((S.height scalarBeta).decode u.1) :=
    scalarCommonHeightDecode_angularPartial hT hS u
  have hR : (S.height scalarBeta).decode (scalarCommonRadialCLM hD hT hS u) =
      radialPartial (scalarCommonHeightDecode S u) := decode_scalarCommonRadialCLM hD hT hS u
  have hP : scalarCommonProjectionCLM S u = u.1 := by
    exact congrFun (ContinuousLinearMap.coe_fst' (R := ℝ) (M₁ := ScalarHeightSpace S) (M₂ := ℝ)) u
  funext p
  simp only [n07aMixedNormalCLM, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_add, Pi.add_apply,
    n07aMixedHeightMultiplyCLM_decode,
    n07aMixedAngularJetCLM_decode hT hS hγ scalarBeta_pos, hR, hP, hθ]

theorem n07aMixedAngularCLM_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 < γ)
    (b c : (S.height γ).Space) (u : ScalarCommonHeight S) :
    (S.height scalarBeta).decode (n07aMixedAngularCLM hD hT hS hγ.le b c u) =
      angularPartial (fun p =>
        angularPartial ((S.height γ).decode b) p * radialPartial (scalarCommonHeightDecode S u) p +
          (S.height γ).decode c p * angularPartial (scalarCommonHeightDecode S u) p) := by
  have hb := (heightMember_contDiff_and_flatJets hT hγ ((hS.1 γ).2.2.2.1 b)).1
  have hc := (heightMember_contDiff_and_flatJets hT hγ ((hS.1 γ).2.2.2.1 c)).1
  have hu : ContDiff ℝ ∞ (scalarCommonHeightDecode S u) := scalarCommonHeightDecode_contDiff hT hS u
  have hbθ : ContDiff ℝ ∞ (angularPartial ((S.height γ).decode b)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_angularPartial hb.contDiffAt (by simp)
  have hur : ContDiff ℝ ∞ (radialPartial (scalarCommonHeightDecode S u)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_radialPartial hu.contDiffAt (by simp)
  have huθ : ContDiff ℝ ∞ (angularPartial (scalarCommonHeightDecode S u)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_angularPartial hu.contDiffAt (by simp)
  have hθ : angularPartial (scalarCommonHeightDecode S u) =
      angularPartial ((S.height scalarBeta).decode u.1) :=
    scalarCommonHeightDecode_angularPartial hT hS u
  have hR : (S.height scalarBeta).decode (scalarCommonRadialCLM hD hT hS u) =
      radialPartial (scalarCommonHeightDecode S u) := decode_scalarCommonRadialCLM hD hT hS u
  have hP : scalarCommonProjectionCLM S u = u.1 := by
    exact congrFun (ContinuousLinearMap.coe_fst' (R := ℝ) (M₁ := ScalarHeightSpace S) (M₂ := ℝ)) u
  funext p
  rw [angularPartial_add ((hbθ.mul hur).differentiable (by simp) p)
    ((hc.mul huθ).differentiable (by simp) p),
    angularPartial_mul (hbθ.differentiable (by simp) p) (hur.differentiable (by simp) p),
    angularPartial_mul (hc.differentiable (by simp) p) (huθ.differentiable (by simp) p)]
  simp only [n07aMixedAngularCLM, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_add, Pi.add_apply,
    n07aMixedHeightMultiplyCLM_decode,
    n07aMixedAngularJetCLM_decode hT hS hγ scalarBeta_pos,
    SobolevModelData.decode_angularSecondCLM, hR, hP, hθ]
  ring

theorem n07aMixedCoefficientOperatorCLM_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 < γ)
    (a b c : (S.height γ).Space) (u : ScalarCommonHeight S) :
    (S.height scalarBeta).decode
        (n07aMixedCoefficientOperatorCLM hD hT hS hγ.le a b c u) =
      symmetricDivergence ((S.height γ).decode a)
        (angularPartial ((S.height γ).decode b)) ((S.height γ).decode c)
        (scalarCommonHeightDecode S u) := by
  simp only [n07aMixedCoefficientOperatorCLM, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_add,
    SobolevModelData.decode_radialCLM,
    n07aMixedNormalCLM_decode hD hT hS hγ,
    n07aMixedAngularCLM_decode hD hT hS hγ]
  rfl

end ContinuousFlexibility.Analysis
