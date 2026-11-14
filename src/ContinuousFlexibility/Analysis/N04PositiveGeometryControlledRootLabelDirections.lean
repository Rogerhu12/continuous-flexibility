import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsRoot
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-!
# Genuine angular towers of the actual inverse-root slope

The inverse label is the decoded inverse circle plus the identity. This
gives its literal slope and every angular derivative, including the
reference constant at angular order zero. Positive parameter jets are
exactly the corresponding jets of the inverse-label displacement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04ControlledRootLabelDirectionsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

private theorem controlled_rootLabel_slope_add_identity
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (θ : ℝ) :
    iteratedDeriv n (deriv (fun α => f α + α)) θ =
      iteratedDeriv (n + 1) f θ + if n = 0 then 1 else 0 := by
  rw [← iteratedDeriv_succ']
  have hadd : iteratedDeriv (n + 1) (fun α => f α + α) θ =
      iteratedDeriv (n + 1) f θ + iteratedDeriv (n + 1) (id : ℝ → ℝ) θ :=
    iteratedDeriv_fun_add (f := f) (g := fun α : ℝ => α) (n := n + 1)
      (hf.contDiffAt.of_le (by simp)) contDiffAt_id
  have hid : iteratedDeriv (n + 1) (id : ℝ → ℝ) θ = if n = 0 then 1 else 0 := by
    rw [iteratedDeriv_id, if_neg (Nat.succ_ne_zero n)]
    by_cases hn : n = 0
    · subst n
      norm_num
    · rw [if_neg (by omega : n + 1 ≠ 1), if_neg hn]
  exact hadd.trans (congrArg (fun t : ℝ => iteratedDeriv (n + 1) f θ + t) hid)

/-- Every angular jet of the actual inverse-label displacement has its
original parameter tower, obtained by continuous circle evaluation. -/
def n04PositiveGeometry_rootInverseDefect_angularDirections
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (side : Bool) (m b : ℕ) (θ : ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε) (fun x =>
      iteratedDeriv b (fun α =>
        Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side) α - α) θ) :=
  (circleDecodedAngularDirections (hS.2.1 (3 / 4 : ℝ))
    (n04PositiveGeometry_rootInverseCircle_directions hT hS hN side) b m θ).congrOn
      (fun x hx => congrArg (fun f : ℝ → ℝ => iteratedDeriv b f θ)
        (funext (fun α => n04PositiveGeometry_rootInverseCircle_decode hT hS hN hx side m α)))

/-- The constant term in the actual inverse-root slope is retained. -/
theorem n04PositiveGeometry_rootInverseDerivative_angular_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {x : StateDirections S × ℝ} (hx : x ∈ sectorNeighborhood S base ε ε)
    (side : Bool) (m b : ℕ) (θ : ℝ) :
    iteratedDeriv b
        (deriv (Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side))) θ =
      iteratedDeriv (b + 1) (fun α =>
        Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side) α - α) θ +
        if b = 0 then 1 else 0 := by
  let f : ℝ → ℝ := (S.circle (3 / 4 : ℝ)).decode
    (n04PositiveGeometry_rootInverseCircle hT hS hN side x) m
  have hf : ContDiff ℝ ∞ f := by
    simpa only [iteratedDeriv_zero] using circleDecoded_iteratedDeriv_contDiff
      (hS.2.1 (3 / 4 : ℝ)) (n04PositiveGeometry_rootInverseCircle hT hS hN side x) m 0
  have hdefect : f = (fun α =>
      Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side) α - α) :=
    funext (fun α => n04PositiveGeometry_rootInverseCircle_decode hT hS hN hx side m α)
  have hfull : Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side) =
      (fun α => f α + α) := by
    funext α
    exact (sub_add_cancel _ α).symm.trans
      (congrArg (fun t : ℝ => t + α) (congrFun hdefect α).symm)
  calc
    _ = iteratedDeriv b (deriv (fun α => f α + α)) θ :=
      congrArg (fun g : ℝ → ℝ => iteratedDeriv b (deriv g) θ) hfull
    _ = iteratedDeriv (b + 1) f θ + if b = 0 then 1 else 0 :=
      controlled_rootLabel_slope_add_identity hf b θ
    _ = _ := congrArg (fun g : ℝ → ℝ =>
      iteratedDeriv (b + 1) g θ + if b = 0 then 1 else 0) hdefect

/-- A tower for the actual inverse slope and any angular derivative. -/
def n04PositiveGeometry_rootInverseDerivative_angularDirections
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (side : Bool) (m b : ℕ) (θ : ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε) (fun x =>
      iteratedDeriv b
        (deriv (Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side))) θ) :=
  (smoothDirectionsAdd
    (n04PositiveGeometry_rootInverseDefect_angularDirections hT hS hN side m (b + 1) θ)
    (smoothDirections_constant (isOpen_sectorNeighborhood S base ε ε)
      (if b = 0 then (1 : ℝ) else 0))).congrOn
        (fun x hx => (n04PositiveGeometry_rootInverseDerivative_angular_eq
          hT hS hN hx side m b θ).symm)

/-- Uniqueness identifies every positive jet of the literal slope with
the corresponding positive jet of its decoded displacement. -/
theorem n04PositiveGeometry_rootInverseDerivative_positive_jet_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (side : Bool) (m b : ℕ) (θ : ℝ)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (fun x =>
      iteratedDeriv b
        (deriv (Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side))) θ))
    (K : SmoothDirections (sectorNeighborhood S base ε ε) (fun x =>
      iteratedDeriv (b + 1) (fun α =>
        Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side) α - α) θ))
    {k : ℕ} (hk : 0 < k) {x : StateDirections S × ℝ}
    (hx : x ∈ sectorNeighborhood S base ε ε) (v : Fin k → (StateDirections S × ℝ)) :
    J.D k x v = K.D k x v := by
  let K' := K.congrOn (fun y hy => (eq_sub_iff_add_eq).mpr
    (n04PositiveGeometry_rootInverseDerivative_angular_eq hT hS hN hy side m b θ).symm)
  exact (smoothDirections_D_sub_constant J K' hk hx v).symm

end ContinuousFlexibility.Analysis
