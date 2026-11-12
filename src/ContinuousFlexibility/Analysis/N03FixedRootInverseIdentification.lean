import ContinuousFlexibility.Analysis.N03FixedRootFlowIdentification
import ContinuousFlexibility.Analysis.N03RootReanchoring
import ContinuousFlexibility.Analysis.RootRescaledInverseSample
import ContinuousFlexibility.Analysis.N01RootLabels

/-!
# Actual inverse footpoints throughout the fixed root band

Agreement for every initial angle identifies the chosen inverse at every
point of the entire band. No continuity limit, angle neighborhood, or
state-dependent radius is used. The actual endpoint reanchoring keeps
the right-root travel offset and the original scale δ exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Full forward agreement identifies inverse values without a local
inverse continuity assumption. -/
theorem invFun_reanchored_eq_of_full_agreement
    {f g H : ℝ → ℝ} {y J : ℝ}
    (hH : Function.Bijective H) (hg : Function.Injective g)
    (hmatch : ∀ u, g (H u) = f u) (hright : g J = y) :
    H (Function.invFun f y) = J := by
  have hf : Function.Injective f := by
    intro u v huv
    exact hH.1 (hg ((hmatch u).trans (huv.trans (hmatch v).symm)))
  have hHright := Function.rightInverse_invFun hH.2 J
  have hvalue : f (Function.invFun H J) = y :=
    (hmatch _).symm.trans ((congrArg g hHright).trans hright)
  have hchosen : Function.invFun f y = Function.invFun H J := by
    rw [← hvalue]
    exact Function.leftInverse_invFun hf _
  exact (congrArg H hchosen).trans hHright

theorem n03_controlledInverse_eq_storedRootFootpoint_on_band
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {R δ η : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R)
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations
      (rootRescaledField
        (localizedRootDrift D S C (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z)
        (localizedRootSpeed D S C g (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z) δ) Θ)
    (hmatch : RootStoredFlowAgreementOn C L z m rightEnd δ η Θ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) η) (θ : ℝ) :
    let r := n01ComponentRoot C m rightEnd
    let σ := n01ComponentRootOrientation rightEnd
    L.minusFlow z m r (Function.invFun (L.minusFlow z m (r + σ * (δ * x))) θ) =
      rootRescaledInverseSample Θ ((-σ) * Real.sqrt δ) (x, θ) := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  have hJ := rootRescaledInverseSample_regular hregular.1 hregular.2
    hperiod.1 hperiod.2 hΘ ((-σ) * Real.sqrt δ)
  have hH := (n03_rootReturn_bijective_and_continuous_invFun
    hS hT hN hL hA hB hz hs m rightEnd).1
  have hinj : Function.Injective
      (fun u => Θ (x, ((-σ) * Real.sqrt δ) * x ^ (3 / 2 : ℝ)) 1 u) :=
    (strictMono_of_deriv_pos (fun u =>
      n04Flow_angular_deriv_pos (contDiff_rootRescaledField hregular.1 hregular.2 δ)
        (rootRescaledField_periodic hperiod.1 hperiod.2 δ) hΘ
        ⟨zero_le_one, le_rfl⟩ (x, ((-σ) * Real.sqrt δ) * x ^ (3 / 2 : ℝ)) u)).injective
  exact invFun_reanchored_eq_of_full_agreement hH hinj
    (fun u => hmatch u x hx) (hJ.2.1 (x, θ))

/-- The exact angular label of the actual stored footpoint on the whole
fixed closed band. The right offset remains minus the total travel. -/
theorem n03_rootScaledInverseCoordinate_eq_storedFootpoint_on_band
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {R δ η : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R)
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations
      (rootRescaledField
        (localizedRootDrift D S C (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z)
        (localizedRootSpeed D S C g (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z) δ) Θ)
    (hmatch : RootStoredFlowAgreementOn C L z m rightEnd δ η Θ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) η) (θ : ℝ) :
    let r := n01ComponentRoot C m rightEnd
    let σ := n01ComponentRootOrientation rightEnd
    rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
        (x, (-σ) * x ^ (3 / 2 : ℝ), θ) =
      stateLeftChart S z.1 m
          (Function.invFun (L.minusFlow z m (r + σ * (δ * x))) θ) -
        if rightEnd then C.travel m else 0 := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  have hlabel (ι : ℝ) : n01RootLabel S C z m rightEnd (L.minusFlow z m r ι) =
      stateLeftChart S z.1 m ι - if rightEnd then C.travel m else 0 := by
    cases rightEnd
    · change stateLeftChart S z.1 m (L.minusFlow z m (C.left m) ι) =
        stateLeftChart S z.1 m ι - 0
      rw [(hL.2.2.2.2.1 z hz hs m ι).1, sub_zero]
    · exact (hL.2.2.2.2.1 z hz hs m ι).2.2.2.1
  have he := n03_controlledInverse_eq_storedRootFootpoint_on_band
    hS hT hN hL hA hB hz hs m rightEnd hg hR hstrip hΘ hmatch hx θ
  rw [rootScaledInverseCoordinate_eq_signed_sample, ← he]
  exact hlabel _

end ContinuousFlexibility.Analysis
