module

public import ContinuousFlexibility.Analysis.N01SingleComponentFlow
public import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations

/-!
# The same cutoff interpolation with a varying physical radius

Only the selected circle component is changed. Its affine lift is the
actual interpolation used in the corrected flow, with the supplied
cutoff evaluated at the variable radius. Positivity follows from the
original return-chart identities and the cutoff range.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01SingleComponentInterpolationStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

private theorem singleComponentInterpolation_product_field
    (m : ℕ) (c : ℝ) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hfm : ∀ θ, f m θ = g θ) :
    (fun i θ => circleSingletonField m c i θ * f i θ) =
      circleSingleComponentField m (fun θ => c * g θ) := by
  funext i θ
  by_cases hi : i = m
  · subst i
    simp only [circleSingletonField, circleSingleComponentField, eq_self_iff_true, ite_true]
    exact congrArg (fun y : ℝ => c * y) (hfm θ)
  · simp only [circleSingletonField, circleSingleComponentField, if_neg hi, zero_mul]

private theorem singleComponentInterpolation_affineLift
    (m : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    circleAffineLift (fun _ => 0)
      (circleSingleComponentField m (fun θ => c * (f θ - θ))) 1 m =
        returnInterpolation c f := by
  funext θ
  simp only [circleAffineLift, circleSingleComponentField, eq_self_iff_true, ite_true,
    one_mul, add_zero, returnInterpolation_apply]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (χ : ℕ → ℝ → ℝ)

def N01Properties.singleComponentInterpolationCircle
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ) : CircleSpace S :=
  circleProductBilinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (circleSingletonLinear (hS.2.1 (3 / 4 : ℝ)) m (χ m x.2))
    (hN.returnCorrectionInitialCircle hS hT x.1)

theorem N01Properties.singleComponentInterpolationCircle_decode
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε) :
    (S.circle (3 / 4 : ℝ)).decode
        (hN.singleComponentInterpolationCircle hS hT χ m x) =
      circleSingleComponentField m (fun θ =>
        χ m x.2 * (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m θ - θ)) := by
  let u : CircleSpace S := circleSingletonLinear (hS.2.1 (3 / 4 : ℝ)) m (χ m x.2)
  let v : CircleSpace S := hN.returnCorrectionInitialCircle hS hT x.1
  have hprod : (S.circle (3 / 4 : ℝ)).decode
      (hN.singleComponentInterpolationCircle hS hT χ m x) =
        fun i θ => (S.circle (3 / 4 : ℝ)).decode u i θ *
          (S.circle (3 / 4 : ℝ)).decode v i θ :=
    circleProductBilinear_decode (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) u v
  have hu : (S.circle (3 / 4 : ℝ)).decode u = circleSingletonField m (χ m x.2) :=
    circleSingletonLinear_decode (hS.2.1 (3 / 4 : ℝ)) m (χ m x.2)
  have hv (θ : ℝ) : (S.circle (3 / 4 : ℝ)).decode v m θ =
      returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m θ - θ :=
    hN.returnCorrectionInitialCircle_decode hS hT x.1 hx m θ
  have hfield := congrArg
    (fun f : ℕ → ℝ → ℝ => fun i θ => f i θ * (S.circle (3 / 4 : ℝ)).decode v i θ) hu
  exact hprod.trans (hfield.trans
    (singleComponentInterpolation_product_field m (χ m x.2)
      ((S.circle (3 / 4 : ℝ)).decode v)
      (fun θ => returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m θ - θ) hv))

theorem N01Properties.singleComponentInterpolationCircle_lift
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε) :
    circleAffineLift (fun _ => 0)
        ((S.circle (3 / 4 : ℝ)).decode
          (hN.singleComponentInterpolationCircle hS hT χ m x)) 1 m =
      returnInterpolation (χ m x.2)
        (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m) := by
  exact (congrArg (fun e : ℕ → ℝ → ℝ => circleAffineLift (fun _ => 0) e 1 m)
    (hN.singleComponentInterpolationCircle_decode hS hT χ m x hx)).trans
      (singleComponentInterpolation_affineLift m (χ m x.2)
        (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m))

theorem N01Properties.singleComponentInterpolationCircle_positive
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Icc (C.left m) (C.right m)) :
    hN.singleComponentInterpolationCircle hS hT χ m x ∈
      circlePositiveLiftDomain (S.circle (3 / 4 : ℝ)) := by
  apply (circlePositiveLiftDomain_iff (hS.2.1 (3 / 4 : ℝ)) (fun _ => 0) _).mpr
  intro i θ
  by_cases hi : i = m
  · subst i
    rw [hN.singleComponentInterpolationCircle_lift hS hT χ m x hx]
    have hk := hN.returnCorrectionInitialMap_deriv_pos
      (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x.1) m θ
    rw [(returnInterpolation_hasDerivAt (χ := χ m x.2)
      (differentiableAt_of_deriv_ne_zero hk.ne').hasDerivAt).deriv]
    exact returnInterpolation_deriv_pos (hχrange m x.2 hr).1 (hχrange m x.2 hr).2 hk
  · have heq : circleAffineLift (fun _ => 0)
        ((S.circle (3 / 4 : ℝ)).decode
          (hN.singleComponentInterpolationCircle hS hT χ m x)) 1 i =
          (fun t : ℝ => t) := by
      funext t
      rw [hN.singleComponentInterpolationCircle_decode hS hT χ m x hx]
      simp only [circleAffineLift, circleSingleComponentField, if_neg hi, one_mul, add_zero]
    rw [heq, deriv_id'']
    exact zero_lt_one

def N01Properties.singleComponentInterpolationTower
    (hχ : ∀ m, ContDiff ℝ ∞ (χ m)) (m : ℕ) (l h : ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ Ioo l h)
      (hN.singleComponentInterpolationCircle hS hT χ m) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo : IsOpen (Ioo l h))
  let F : ((StateDirections S × ℝ) × ℝ) →L[ℝ] StateDirections S × ℝ :=
    ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) ℝ
  let G : ((StateDirections S × ℝ) × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) ℝ
  let J := (hN.smoothTameOn_returnCorrectionInitialCircle hS hT).choose.compLinear F hU
    (fun x hx => hx.1)
  let K := (smoothDirectionsOfContDiffOn isOpen_Ioo
    ((hχ m).contDiffOn (s := Ioo l h))).compLinear G hU (fun x hx => hx.2)
  exact circleProductDirections hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (circleSingletonDirections hH m K) J

def N01Properties.singleComponentInterpolationInverseCircle
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ) : CircleSpace S :=
  circlePositiveInversePerturbation (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun _ => 0) (hN.singleComponentInterpolationCircle hS hT χ m x)

theorem N01Properties.singleComponentInterpolationInverseCircle_decode
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        (hN.singleComponentInterpolationInverseCircle hS hT χ m x) m θ =
      Function.invFun (returnInterpolation (χ m x.2)
        (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m)) θ - θ := by
  have hd : (S.circle (3 / 4 : ℝ)).decode
      (hN.singleComponentInterpolationInverseCircle hS hT χ m x) m θ =
        circleAffineInverse (fun _ => 0)
          (hN.singleComponentInterpolationCircle hS hT χ m x) m θ - (θ - 0) :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
      (circlePositiveInversePerturbation_decode
        (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun _ => 0)
        (hN.singleComponentInterpolationCircle hS hT χ m x)
        (hN.singleComponentInterpolationCircle_positive hS hT χ hχrange m x hx hr))
  have heq : circleAffineInverse (fun _ => 0)
      (hN.singleComponentInterpolationCircle hS hT χ m x) m θ =
      Function.invFun (returnInterpolation (χ m x.2)
        (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m)) θ :=
    congrArg (fun f : ℝ → ℝ => Function.invFun f θ)
      (hN.singleComponentInterpolationCircle_lift hS hT χ m x hx)
  exact hd.trans (congrArg₂ (fun a b : ℝ => a - b) heq (sub_zero θ))

def N01Properties.singleComponentInterpolationInverseTower
    (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ Ioo l h)
      (hN.singleComponentInterpolationInverseCircle hS hT χ m) :=
  circleInversePerturbationDirections (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ => 0)
    (hN.singleComponentInterpolationTower hS hT χ hχ m l h)
    (fun x hx => hN.singleComponentInterpolationCircle_positive hS hT χ hχrange m x hx.1
      ⟨(hl.trans hx.2.1).le, (hx.2.2.trans hh).le⟩)

end ContinuousFlexibility.Statements
