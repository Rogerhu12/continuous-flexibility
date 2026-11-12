import ContinuousFlexibility.Analysis.N04ActualTravelStripTower
import ContinuousFlexibility.Analysis.N01CharacteristicJointGrowth
import ContinuousFlexibility.Analysis.N01ReturnVelocitySpatialTower
import ContinuousFlexibility.Analysis.N01FlowJointRegularity

/-!
# The actual corrected minus speed on the same physical strips

The stored N03 flow and the literal corrected flow solve two displayed
ODEs. Their equality and actual slice surjectivity identify the speeds
at every interior point. The original speed tower plus the genuine
residual velocity tower is therefore a tower of the stored coefficient
speed itself. No new flow, inverse or positive corrected-gap assumption
is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

local instance n04ActualMinusSpeedStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hfield : N04bFieldRegularity D S C L base ε)
  (χ : ℕ → ℝ → ℝ)
  (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hflow : L.minusFlow = returnCorrectedMinusFlow S C χ)

include hN hS hT hfield hχ hχrange hflow in
/-- Derivative uniqueness on the same flow identifies the actual speed.
The initial angle is obtained from the stored flow's true slice map. -/
theorem NonlinearPropertiesThrough03.n04_actualMinusSpeed_eq_corrected
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    minusCharacteristicSpeed (L.coefficients z) p =
      returnCorrectedMinusSpeed D S C χ z m p := by
  have hΦ := n04b_actualMinusFlow_regular hN hS hT hfield hz hs m
  obtain ⟨θ, hθ⟩ := hΦ.surjective Real.pi_ne_zero
    (show p.1 ∈ Icc (C.left m) (C.right m) from ⟨hp.1.le, hp.2.le⟩) p.2
  have hstored := (hN.2.2.2.2.2.1 z hz hs m θ).2.2.1 p.1 hp
  have hcorrected := hN.1.1.returnCorrectedMinusFlow_hasDerivAt_of_physical
    hS hT hz hs χ m p.1 θ hp
    ((hχ m).differentiable (by simp) p.1)
    (hχrange m p.1 ⟨hp.1.le, hp.2.le⟩)
  have hcorrected' : HasDerivAt (fun r => L.minusFlow z m r θ)
      (returnCorrectedMinusSpeed D S C χ z m (p.1, L.minusFlow z m p.1 θ)) p.1 := by
    simpa only [hflow] using hcorrected
  simpa only [hθ, Prod.mk.eta] using hstored.unique hcorrected'

include hN hS hT hfield hχ hχrange hflow in
/-- The correction is the actual N02 residual, in the original circle
space, evaluated through the same flow and interpolation inverses. -/
theorem NonlinearPropertiesThrough03.n04_actualMinusSpeed_eq_original_add_residual
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    minusCharacteristicSpeed (L.coefficients z) p =
      minusCharacteristicSpeed (originalCoefficients D S C z) p +
        returnCorrectionVelocityLinear D S C χ z m p (R.residual z) := by
  rw [hN.n04_actualMinusSpeed_eq_corrected hS hT hfield χ hχ hχrange hflow hz hs m hp,
    returnCorrectionVelocityLinear_at_actual hN.1.1 hN.1.2 χ hz hs m p]
  ring

/-- One genuine joint tower of the stored speed is fixed before any
parameter or spatial derivative order. The real component hosts and
interior strip endpoints are the same supplied construction data. -/
def NonlinearPropertiesThrough03.n04ActualMinusSpeed_stripJointTower
    (hcoeff : L.coefficients = returnCorrectedCoefficients D S C χ)
    (hdiscFull : ∀ z ∈ stateNeighborhood S C base ε, ∀ m (p : PolarPoint),
      p.1 ∈ tsupport (deriv (χ m)) →
        0 < (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    (m : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        minusCharacteristicSpeed (L.coefficients (liftSectorParameter S C x.1)) x.2) := by
  have hphysical (k : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (l k) (h k)) :
      p.1 ∈ Ioo (C.left k) (C.right k) :=
    ⟨(hl k).trans hp.1, hp.2.trans (hh k)⟩
  have hapos : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ (k : ℕ) (p : PolarPoint),
      p.1 ∈ Ioo (l k) (h k) →
        0 < (originalCoefficients D S C (liftSectorParameter S C z)).a p := by
    intro z hz k p hp
    have hr := hphysical k p hp
    have hbounds := hN.1.1.2.2.2.1.1 k
    exact hN.1.1.originalRadialCoefficient_pos
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hN.1.1.2.2.1.liftSectorParameter_sector z)
      ⟨⟨hbounds.1.trans hr.1, hr.2.trans hbounds.2.2⟩, mem_univ _⟩
  have hdpos : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ (k : ℕ) (p : PolarPoint),
      p.1 ∈ Ioo (l k) (h k) →
        0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C z)).a p *
            (originalCoefficients D S C (liftSectorParameter S C z)).c p := by
    intro z hz k p hp
    exact hN.1.1.n04_originalDiscriminant_of_preservedCorrection hfield χ hcoeff hdiscFull
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hN.1.1.2.2.1.liftSectorParameter_sector z) k (hphysical k p hp)
  let J := hN.1.1.minusCharacteristicSpeed_stripTower hS hT j hcell l h hl hh hapos hdpos m
  let K := hN.1.1.returnCorrectionVelocity_actual_parameterSpatialTower
    hS hT χ hχrange hχ m (l m) (h m) (hl m) (hh m)
    (fun z hz p hp => hdpos z hz m p hp) hN.1.2
  apply (smoothDirectionsAdd J K).congrOn
  intro x hx
  exact (hN.n04_actualMinusSpeed_eq_original_add_residual
    hS hT hfield χ hχ hχrange hflow
    (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
    (hN.1.1.2.2.1.liftSectorParameter_sector x.1) m (hphysical m x.2 hx.2.1)).symm

end ContinuousFlexibility.Statements
