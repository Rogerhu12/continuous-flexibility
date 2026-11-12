import ContinuousFlexibility.Analysis.N04MinusFirstIntegralStripTower
import ContinuousFlexibility.Analysis.N04bActualTravelChart
import ContinuousFlexibility.Analysis.ReturnCorrectionPatching
import ContinuousFlexibility.Analysis.TameProductDirections
import ContinuousFlexibility.Analysis.SolveNewtonBridge

/-!
# Joint towers of the stored travel chart on real physical strips

The retained cutoff-support discriminant and the actual corrected field
give the original discriminant throughout a negative component. The
first-integral tower therefore applies on every interior strip. Its
reflection and two fixed linear combinations are the very same stored
travel chart; neither a new inverse nor a new coordinate family is chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

local instance n04ActualTravelStripStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hfield : N04bFieldRegularity D S C L base ε)
  (χ : ℕ → ℝ → ℝ)
  (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hcoeff : L.coefficients = returnCorrectedCoefficients D S C χ)
  (hflow : L.minusFlow = returnCorrectedMinusFlow S C χ)
  (hdiscFull : ∀ z ∈ stateNeighborhood S C base ε, ∀ m (p : PolarPoint),
    p.1 ∈ tsupport (deriv (χ m)) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hN hfield hcoeff hdiscFull in
/-- The actual patch is original where its own cutoff derivative vanishes;
on its support the already-retained construction supplies positivity. -/
theorem N01Properties.n04_originalDiscriminant_of_preservedCorrection
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p := by
  by_cases hzero : deriv (χ m) p.1 = 0
  · have he := returnCorrectedCoefficients_eq_original_at_of_deriv_zero
      hN.2.2.2.1.2.2.1 χ z m p hp hzero
    have hd := hfield.negative_discriminant z hz hs m p ⟨hp, mem_univ _⟩
    rw [hcoeff, he.1, he.2, returnCorrectedCoefficients_a] at hd
    exact hd
  · exact hdiscFull z hz m p (subset_tsupport _ hzero)

/-- One joint state/radius/angle tower of the stored minus first integral. -/
def N01Properties.n04ActualMinusFirstIntegral_stripJointTower
    (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint => n04bMinusFirstIntegral
        (fun q => L.minusFlow (liftSectorParameter S C x.1) m q.1 q.2)
        (stateLeftChart S (liftSectorParameter S C x.1).1 m) x.2) := by
  have hdisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ p : PolarPoint,
      p.1 ∈ Ioo l h →
        0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C z)).a p *
            (originalCoefficients D S C (liftSectorParameter S C z)).c p := by
    intro z hz p hp
    exact hN.n04_originalDiscriminant_of_preservedCorrection hfield χ hcoeff hdiscFull
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hN.2.2.1.liftSectorParameter_sector z) m
      ⟨hl.trans hp.1, hp.2.trans hh⟩
  let J := hN.n04MinusFirstIntegral_stripJointTower hS hT χ hχrange hχ m l h hl hh hdisc
  apply J.congrOn
  intro x hx
  simp only [hflow]

/-- Reflection and fixed linear combinations of that one tower give the
literal stored travel chart, before any derivative order is specified. -/
def N01Properties.n04ActualTravelChart_stripJointTower
    (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        n04bActualTravelChart S C L (liftSectorParameter S C x.1) m x.2) := by
  let V : (StateDirections S × ℝ) × PolarPoint → ℝ := fun x =>
    n04bMinusFirstIntegral
      (fun q => L.minusFlow (liftSectorParameter S C x.1) m q.1 q.2)
      (stateLeftChart S (liftSectorParameter S C x.1).1 m) x.2
  let J : SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ)) V :=
    hN.n04ActualMinusFirstIntegral_stripJointTower hS hT hfield χ hχ hχrange
      hcoeff hflow hdiscFull m l h hl hh
  let R : PolarPoint →L[ℝ] PolarPoint :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-ContinuousLinearMap.snd ℝ ℝ ℝ)
  let P : ((StateDirections S × ℝ) × PolarPoint) →L[ℝ]
      (StateDirections S × ℝ) × PolarPoint :=
    (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) PolarPoint).prod
      (R.comp (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) PolarPoint))
  let K := J.compLinear P J.open_domain (fun x hx => by
    change (x.1, (x.2.1, -x.2.2)) ∈
      sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ)
    exact ⟨hx.1, hx.2.1, mem_univ _⟩)
  let A : PolarPoint →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)
  let B : PolarPoint →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ)
  apply (solveSmoothDirectionsPostcomp (smoothDirectionsProd J K) (A.prod B)).congrOn
  intro x hx
  change ((1 / 2 : ℝ) * (V x + V (x.1, (x.2.1, -x.2.2))),
      (1 / 2 : ℝ) * (V x - V (x.1, (x.2.1, -x.2.2)))) =
    ((1 / 2 : ℝ) * (V x - -V (x.1, (x.2.1, -x.2.2))),
      (1 / 2 : ℝ) * (-V (x.1, (x.2.1, -x.2.2)) + V x))
  congr 1 <;> ring

end ContinuousFlexibility.Statements
