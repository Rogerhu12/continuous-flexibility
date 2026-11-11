import ContinuousFlexibility.Analysis.N01ReturnChartLineVariation
import ContinuousFlexibility.Analysis.SectorParameterGeometry
import ContinuousFlexibility.Analysis.ProjectiveJets

/-!
# The N02 chart derivative in the actual circle topology

The genuine sector tower gives a derivative in every projective level.
Continuous point evaluations identify that derivative with the scalar
return variation already obtained from the actual inverse flow. Thus the
N02 identity holds for the full circle-valued difference quotient.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

local instance n02ProjectiveChartVariationStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem SmoothDirections.hasProjectiveLineDerivAt_self
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {U : Set E} {f : E → F} (J : SmoothDirections U f)
    (x : E) (hx : x ∈ U) (v : E) :
    HasProjectiveLineDerivAt f (J.D 1 x (Fin.cons v Fin.elim0)) x v := by
  apply (J.derivative 0 x hx Fin.elim0 v).congr_germ
  filter_upwards [J.open_domain.mem_nhds hx] with y hy
  exact (J.zero y hy).symm

def circlePointEvaluationCLM {T : MaterialData} {γ : ℝ} {B : CircleModelData}
    (hB : IsCircleModel T γ B) (m : ℕ) (θ : ℝ) : B.Space →L[ℝ] ℝ :=
  { (LinearMap.proj θ).comp ((LinearMap.proj m).comp B.decode) with
    cont := (continuous_apply θ).comp ((continuous_apply m).comp hB.2.2.1) }

theorem circlePointEvaluationCLM_apply {T : MaterialData} {γ : ℝ} {B : CircleModelData}
    (hB : IsCircleModel T γ B) (m : ℕ) (θ : ℝ) (u : B.Space) :
    circlePointEvaluationCLM hB m θ u = B.decode u m θ := rfl

def sectorParameterOfState {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (hRef : stateSector S C.referenceState) (z : AnnularState S × ℝ)
    (hz : stateSector S z.1) : StateDirections S × ℝ :=
  (⟨z.1 - C.referenceState, (stateSectorSubmodule S).sub_mem hz hRef⟩, z.2)

theorem lift_sectorParameterOfState {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (hRef : stateSector S C.referenceState)
    (z : AnnularState S × ℝ) (hz : stateSector S z.1) :
    liftSectorParameter S C (sectorParameterOfState C hRef z hz) = z := by
  apply Prod.ext
  · change C.referenceState + (z.1 - C.referenceState) = z.1
    abel
  · rfl

theorem sectorParameterOfState_mem {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (hRef : stateSector S C.referenceState)
    {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hz : stateSector S z.1) (hmem : z ∈ stateNeighborhood S C base ε) :
    sectorParameterOfState C hRef z hz ∈ sectorNeighborhood S base ε ε :=
  hmem

def chartSectorDirection (S : PhysicalSpacesData) (w : CircleSpace S)
    (hw : IsOddCircle S w) : StateDirections S :=
  ⟨(0, (0, (0, w))), by
    constructor
    · intro m θ φ
      simp only [map_zero, Pi.zero_apply]
    · exact hw⟩

def chartParameterDirection (S : PhysicalSpacesData) (w : CircleSpace S)
    (hw : IsOddCircle S w) : StateDirections S × ℝ := (chartSectorDirection S w hw, 0)

theorem liftSectorParameter_chart_line (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (y : StateDirections S × ℝ)
    (w : CircleSpace S) (hw : IsOddCircle S w) (t : ℝ) :
    liftSectorParameter S C (y + t • chartParameterDirection S w hw) =
      ((liftSectorParameter S C y).1 + t • (0, (0, (0, w))), y.2) := by
  change (C.referenceState + (y.1.val + t • ((0, (0, (0, w))) : AnnularState S)),
    y.2 + t * 0) =
      ((C.referenceState + y.1.val) + t • ((0, (0, (0, w))) : AnnularState S), y.2)
  rw [add_assoc, mul_zero, add_zero]

theorem N01Properties.hasProjectiveLineDerivAt_returnResidual_chartDirection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (f : AnnularState S × ℝ → CircleSpace S)
    (J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun y => f (liftSectorParameter S C y)))
    (hdecode : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m θ,
      (S.circle (3 / 4 : ℝ)).decode (f z) m θ = returnResidualField S C z m θ)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1)
    (w v out : CircleSpace S) (hv : IsOddCircle S v)
    (hw : ∀ m θ, (S.circle (3 / 4 : ℝ)).decode w m θ =
      (S.circle (3 / 4 : ℝ)).decode v m (stateLeftChart S z.1 m θ))
    (hout : ∀ m θ, (S.circle (3 / 4 : ℝ)).decode out m θ =
      circleRotationDifference S C v m θ + circleChartError S C z (f z) v m θ) :
    HasProjectiveLineDerivAt (fun x => f (x, z.2)) out
      z.1 (0, (0, (0, w))) := by
  have hwodd := chartIncrement_isOdd S z w v hsector hv hw
  let y := sectorParameterOfState C hN.2.2.1.stateSector z hsector
  let d := chartParameterDirection S w hwodd
  have hy : y ∈ sectorNeighborhood S base ε ε :=
    sectorParameterOfState_mem C hN.2.2.1.stateSector hsector hz
  have hylift : liftSectorParameter S C y = z :=
    lift_sectorParameterOfState C hN.2.2.1.stateSector z hsector
  let q := J.D 1 y (Fin.cons d Fin.elim0)
  have hfull : HasProjectiveLineDerivAt (fun x => f (x, z.2)) q
      z.1 (0, (0, (0, w))) := by
    have hd := J.hasProjectiveLineDerivAt_self y hy d
    change HasProjectiveCurveDerivAt
      (fun t : ℝ => f (liftSectorParameter S C (y + t • d))) q 0 at hd
    change HasProjectiveCurveDerivAt
      (fun t : ℝ => f (z.1 + t • (0, (0, (0, w))), z.2)) q 0
    have heq : (fun t : ℝ => f (liftSectorParameter S C (y + t • d))) =
        (fun t : ℝ => f (z.1 + t • (0, (0, (0, w))), z.2)) := by
      funext t
      rw [show liftSectorParameter S C (y + t • d) =
        ((liftSectorParameter S C y).1 + t • (0, (0, (0, w))), y.2) from
          liftSectorParameter_chart_line S C y w hwodd t, hylift]
      rfl
    exact heq ▸ hd
  have hq : q = out := by
    apply (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
    funext m θ
    have hd : HasDerivAt (fun t : ℝ => (S.circle (3 / 4 : ℝ)).decode
        (f (z.1 + t • (0, (0, (0, w))), z.2)) m θ)
        ((S.circle (3 / 4 : ℝ)).decode q m θ) 0 := by
      apply hasDerivAt_iff_tendsto_slope_zero.mpr
      exact hfull.clm_comp (circlePointEvaluationCLM (hS.2.1 (3 / 4 : ℝ)) m θ)
    have hraw : HasDerivAt (fun t : ℝ => returnResidualField S C
        (z.1 + t • (0, (0, (0, w))), z.2) m θ)
        ((S.circle (3 / 4 : ℝ)).decode q m θ) 0 := by
      apply hd.congr_of_eventuallyEq
      filter_upwards [stateChartLine_eventually_mem S C hz w] with t ht
      rw [← stateChartLine_eq_add_smul]
      exact (hdecode (stateChartLine S z w t) ht
        (stateChartLine_sector S z w hsector hwodd t) m θ).symm
    exact (hraw.unique (hN.hasDerivAt_returnResidual_chartDirection hS hT hz hsector
      w v (f z) hv hw (hdecode z hz hsector) m θ)).trans (hout m θ).symm
  exact hq ▸ hfull

end ContinuousFlexibility.Statements
