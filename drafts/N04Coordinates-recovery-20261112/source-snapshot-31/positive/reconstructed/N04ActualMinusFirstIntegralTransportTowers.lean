import ContinuousFlexibility.Analysis.N04ActualMinusSpeedStripTower
import ContinuousFlexibility.Analysis.JointMixedTransportCalculus
import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# Three-index transport for the actual first-integral tower

The state, radial and angular derivatives all belong to the two already
constructed joint towers. The stored N03 ODE supplies their actual PDE.
The existing joint Leibniz theorem then reduces positive radial order
to lower radial orders of the same inverse-flow first integral.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

local instance n04ActualTransportMixedStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hfield : N04bFieldRegularity D S C L base ε)
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hcoeff : L.coefficients = returnCorrectedCoefficients D S C χ)
  (hflow : L.minusFlow = returnCorrectedMinusFlow S C χ)
  (hdiscFull : ∀ z ∈ stateNeighborhood S C base ε, ∀ m (p : PolarPoint),
    p.1 ∈ tsupport (deriv (χ m)) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
  (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)

/-- Every term on the right has first-integral radial order at most `a`.
No parameter or spatial order changes either of the actual towers. -/
theorem NonlinearPropertiesThrough03.n04ActualMinusFirstIntegral_jointMixed_radial_succ
    (m n a b : ℕ) (x w : StateDirections S × ℝ)
    (hx : x ∈ sectorNeighborhood S base ε ε) {p : PolarPoint}
    (hp : p ∈ Ioo (l m) (h m) ×ˢ (univ : Set ℝ)) :
    let J := hN.1.1.n04ActualMinusFirstIntegral_stripJointTower
      hS hT hfield χ hχ hχrange hcoeff hflow hdiscFull m (l m) (h m) (hl m) (hh m)
    let K := hN.n04ActualMinusSpeed_stripJointTower
      hS hT hfield χ hχ hχrange hflow hcoeff hdiscFull j hcell l h hl hh m
    jointMixedDiagonal J n (a + 1) b x w p =
      -(∑ q ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        ∑ k ∈ Finset.range (n + 1),
          (b.choose q : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ) *
            jointMixedDiagonal K k i q x w p *
              jointMixedDiagonal J (n - k) (a - i) (b - q + 1) x w p) := by
  let J := hN.1.1.n04ActualMinusFirstIntegral_stripJointTower
    hS hT hfield χ hχ hχrange hcoeff hflow hdiscFull m (l m) (h m) (hl m) (hh m)
  let K := hN.n04ActualMinusSpeed_stripJointTower
    hS hT hfield χ hχ hχrange hflow hcoeff hdiscFull j hcell l h hl hh m
  have htransport : ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ q ∈ Ioo (l m) (h m) ×ˢ (univ : Set ℝ),
      radialPartial (n04bMinusFirstIntegral
        (fun r => L.minusFlow (liftSectorParameter S C z) m r.1 r.2)
        (stateLeftChart S (liftSectorParameter S C z).1 m)) q =
      -(minusCharacteristicSpeed (L.coefficients (liftSectorParameter S C z)) q *
        angularPartial (n04bMinusFirstIntegral
          (fun r => L.minusFlow (liftSectorParameter S C z) m r.1 r.2)
          (stateLeftChart S (liftSectorParameter S C z).1 m)) q) := by
    intro z hz q hq
    have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
    have hs := hN.1.1.2.2.1.liftSectorParameter_sector z
    have hq' : q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
      ⟨⟨(hl m).trans hq.1.1, hq.1.2.trans (hh m)⟩, mem_univ _⟩
    have hΦ := n04b_actualMinusFlow_regular hN hS hT hfield hz' hs m
    have hleft := stateLeftChart_contDiff S (liftSectorParameter S C z) m
      (hS.2.1 (3 / 4 : ℝ))
    have he := n04b_minusFirstIntegral_transport
      (d := n04bCharacteristicDrift (L.coefficients (liftSectorParameter S C z)))
      (v := n04bCharacteristicHalfGap (L.coefficients (liftSectorParameter S C z)))
      hΦ Real.pi_ne_zero hleft
      (fun r hr θ => (hN.2.2.2.2.2.1 _ hz' hs m θ).2.2.1 r hr) hq'
    simpa only [n04bCharacteristicDrift, n04bCharacteristicHalfGap,
      minusCharacteristicSpeed, neg_mul] using he
  exact jointMixedDiagonal_transport J K (sectorNeighborhood_isOpen S base ε ε)
    (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex S base ε ε).prod
      ((convex_Ioo (l m) (h m)).prod convex_univ)) htransport n a b x w hx hp

end ContinuousFlexibility.Statements
