import ContinuousFlexibility.Analysis.N08ScalarProfileAlgebra
import ContinuousFlexibility.Scalar.WeightedOddHeightGerms
import ContinuousFlexibility.Scalar.WeightedHeightGerms

/-!
# Actual uniform towers for the controlled scalar formula

The proof is finite algebra in the actual spaces. Its common base and loss
do not depend on the derivative order. The profile perturbation is allowed
to have a weaker positive weight than the height and source spaces.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {γ : ℝ}
variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {x0 : X}
  {m : X → (S.height γ).Space} {f : X → ScalarHeightSpace S}
  {x : X → ScalarWeightedState S}

theorem UniformTameGerm.n08ProfileWAct
    (hm : UniformTameGerm p (S.height γ).grading x0 m)
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun y => n08ProfileWAct hD hT hS hγ (m y) (f y)) :=
  (hf.add (hm.n08MixedWeightAction hf hT hS hγ hp ht) hp ht).scalarReferenceW
    hD hT hS hp ht

theorem UniformTameGerm.n08ProfileEnergyAct
    (hm : UniformTameGerm p (S.height γ).grading x0 m)
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun y => n08ProfileEnergyAct hD hT hS hγ (m y) (f y)) :=
  hf.add (hm.n08ProfileWAct (hm.n08ProfileWAct hf hD hT hS hγ hp ht)
    hD hT hS hγ hp ht) hp ht

theorem UniformTameGerm.n08ProfileWDerivAct
    (hm : UniformTameGerm p (S.height γ).grading x0 m)
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun y => n08ProfileWDerivAct hD hT hS hγ (m y) (f y)) := by
  have hmd := hm.postcompose hp ht (SobolevModelData.radialCLM hT (hS.1 γ))
    (SobolevModelData.radialCLM_isTame hT (hS.1 γ))
  exact ((hf.add (hm.n08MixedWeightAction hf hT hS hγ hp ht) hp ht).scalarReferenceWDeriv
    hD hT hS hp ht).add
      ((hmd.n08MixedWeightAction hf hT hS hγ hp ht).scalarReferenceW hD hT hS hp ht) hp ht

theorem UniformTameGerm.n08ProfileDiscriminant
    (hm : UniformTameGerm p (S.height γ).grading x0 m)
    (hx : UniformTameGerm p (scalarStateGrading S) x0 x)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun y => n08ProfileDiscriminant hD hT hS hγ (m y) (x y)) := by
  have hq := hx.postcompose hp ht (scalarStateQProjection S) (scalarStateQProjection_isTame S)
  have ha := hx.postcompose hp ht (scalarStateRadialCLM hD hT hS)
    (scalarStateRadialCLM_isTame hD hT hS)
  have hc := hx.postcompose hp ht (scalarStateAngularPrimitiveCLM hD hT hS)
    (scalarStateAngularPrimitiveCLM_isTame hD hT hS)
  have hqa := hq.scalarHeightSMul ha hS hp ht
  have hqc := hq.scalarHeightSMul hc hS hp ht
  exact ((hm.n08ProfileWAct hqa hD hT hS hγ hp ht).const_smul hp ht (-2)).sub
    (hqa.scalarHeightMul hqa hT hS hp ht) hp ht |>.sub
      (hm.n08ProfileEnergyAct (hqc.scalarHeightAngularMul hqc hT hS hp ht)
        hD hT hS hγ hp ht) hp ht

theorem UniformTameGerm.n08ProfileNumerator
    (hm : UniformTameGerm p (S.height γ).grading x0 m)
    (hx : UniformTameGerm p (scalarStateGrading S) x0 x)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun y => n08ProfileNumerator hD hT hS hγ (m y) (x y)) := by
  have ha := hx.postcompose hp ht (scalarStateRadialCLM hD hT hS)
    (scalarStateRadialCLM_isTame hD hT hS)
  have hb := hx.postcompose hp ht (scalarStateRadialSecondCLM hD hT hS)
    (scalarStateRadialSecondCLM_isTame hD hT hS)
  have hc := hx.postcompose hp ht (scalarStateAngularPrimitiveCLM hD hT hS)
    (scalarStateAngularPrimitiveCLM_isTame hD hT hS)
  have hd := hx.postcompose hp ht (scalarStateAngularRadialPrimitiveCLM hD hT hS)
    (scalarStateAngularRadialPrimitiveCLM_isTame hD hT hS)
  have he := hx.postcompose hp ht (scalarStateAngularSecondCLM hD hT hS)
    (scalarStateAngularSecondCLM_isTame hD hT hS)
  have hq := hx.postcompose hp ht (scalarStateQProjection S) (scalarStateQProjection_isTame S)
  have hfirst := (hm.n08ProfileWDerivAct (ha.add he hp ht) hD hT hS hγ hp ht).add
    (hm.n08ProfileWAct hb hD hT hS hγ hp ht) hp ht
  have hquad := ((ha.add (hm.n08ProfileEnergyAct he hD hT hS hγ hp ht) hp ht).scalarHeightMul
    hb hT hS hp ht).sub
      ((hm.n08ProfileEnergyAct (hd.scalarHeightAngularMul hd hT hS hp ht)
        hD hT hS hγ hp ht).scalarReferenceRadius hD hT hS hp ht) hp ht
  have hlast := hm.n08ProfileWAct
    (hm.n08ProfileWDerivAct ((hc.scalarHeightAngularMul hc hT hS hp ht).sub
      (ha.scalarHeightMul he hT hS hp ht) hp ht) hD hT hS hγ hp ht) hD hT hS hγ hp ht
  exact hfirst.add (hq.scalarHeightSMul (hquad.add hlast hp ht) hS hp ht) hp ht

theorem n08ProfileDiscriminant_zero_of_q
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ)
    (m : (S.height γ).Space) (x : ScalarWeightedState S) (hq : x.2 = 0) :
    n08ProfileDiscriminant hD hT hS hγ m x = 0 := by
  have hw0 : n08ProfileWAct hD hT hS hγ m 0 = 0 := by
    rw [n08ProfileWAct, n08MixedWeightAction_zero_right, add_zero]
    exact (scalarReferenceWCLM hD hT hS).map_zero
  have he0 : n08ProfileEnergyAct hD hT hS hγ m 0 = 0 := by
    rw [n08ProfileEnergyAct, hw0, hw0, add_zero]
  simp only [n08ProfileDiscriminant, scalarStateRadialHeight, scalarStateAngularSquare,
    scalarStateAngularPrimitive, hq, zero_smul, scalarHeightAngularMul_zero_left,
    scalarHeightMul_zero_left, hw0, he0, smul_zero, sub_zero]

theorem UniformTameGerm.n08ProfileResidual
    (hm : UniformTameGerm p (S.height γ).grading x0 m)
    (hx : UniformTameGerm p (scalarStateGrading S) x0 x)
    (hqx0 : (x x0).2 = 0)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun y => n08ProfileResidual hD hT hS hγ (m y) (x y)) := by
  have hd := hm.n08ProfileDiscriminant hx hD hT hS hγ hp ht
  have hz := n08ProfileDiscriminant_zero_of_q hD hT hS hγ (m x0) (x x0) hqx0
  exact (hd.scalarHeightPower hz hT hS (-(3 / 2) : ℝ) hp ht).scalarHeightUnitalAct
    (hm.n08ProfileNumerator hx hD hT hS hγ hp ht) hT hS hp ht

end ContinuousFlexibility.Statements
