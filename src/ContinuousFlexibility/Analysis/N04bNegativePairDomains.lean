import ContinuousFlexibility.Analysis.N04bNegativePairGeometry
import ContinuousFlexibility.Analysis.CharacteristicPrincipalDensity

/-!
# Domain fields of a constructed negative root piece

The existing moving-domain lemmas supply openness, nonemptiness and
symmetry. The physical component supplies annular containment and its
negative type. These facts assemble exactly the domain fields required by
CanonicalGeometry, with one Bool parameter for both halves.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

/-- Lift periodicity of the actual first integrals gives travel-chart
equivariance; the difference coordinate is invariant. -/
theorem n04b_characteristicTravelChart_periodic
    (period : ℝ) {U V : PolarPoint → ℝ} {p : PolarPoint}
    (hU : U (p + (0, period)) = U p + period)
    (hV : V (p + (0, period)) = V p + period) :
    characteristicTravelChart U V (p + (0, period)) =
      characteristicTravelChart U V p + (0, period) := by
  apply Prod.ext <;>
    simp only [characteristicTravelChart, hU, hV, Prod.fst_add, Prod.snd_add] <;>
    ring

/-- Reflection interchanges the two characteristic families and negates
their first integrals, preserving travel and negating the angular coordinate. -/
theorem n04b_travelChart_reflection_of_firstIntegrals
    {U V : PolarPoint → ℝ} {p : PolarPoint}
    (hU : U (p.1, -p.2) = -V p)
    (hV : V (p.1, -p.2) = -U p) :
    characteristicTravelChart U V (p.1, -p.2) =
      ((characteristicTravelChart U V p).1,
        -(characteristicTravelChart U V p).2) := by
  apply Prod.ext <;> simp only [characteristicTravelChart, hU, hV] <;> ring

theorem n04b_continuousOn_characteristicTravelChart
    {Ω : Set PolarPoint} {U V : PolarPoint → ℝ}
    (hU : ContinuousOn U Ω) (hV : ContinuousOn V Ω) :
    ContinuousOn (characteristicTravelChart U V) Ω :=
  (continuousOn_const.mul (hV.sub hU)).prodMk
    (continuousOn_const.mul (hU.add hV))

/-- Actual half-domains inherit all qualitative domain properties from
the genuine travel chart on the full physical component. -/
theorem n04b_negativeHalfDomain_properties
    {a b T : ℝ} {F : PolarPoint → PolarPoint} (hT : 0 < T)
    (hF : BijOn F (Ioo a b ×ˢ (univ : Set ℝ))
      (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (hCont : ContinuousOn F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hPeriod : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F (p + (0, Real.pi)) = F p + (0, Real.pi))
    (hReflect : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F (p.1, -p.2) = ((F p).1, -(F p).2))
    (side : Bool) :
    let Ω := n04bTravelHalfDomain (Ioo a b ×ˢ (univ : Set ℝ)) F T side
    IsOpen Ω ∧ Ω.Nonempty ∧ Ω ⊆ Ioo a b ×ˢ (univ : Set ℝ) ∧
      (∀ p : PolarPoint, p + (0, Real.pi) ∈ Ω ↔ p ∈ Ω) ∧
      (∀ p : PolarPoint, (p.1, -p.2) ∈ Ω ↔ p ∈ Ω) := by
  have hp : ∀ p : PolarPoint,
      p + (0, Real.pi) ∈ Ioo a b ×ˢ (univ : Set ℝ) ↔
        p ∈ Ioo a b ×ˢ (univ : Set ℝ) := by
    intro p
    simp
  have hr : ∀ p : PolarPoint,
      (p.1, -p.2) ∈ Ioo a b ×ˢ (univ : Set ℝ) ↔
        p ∈ Ioo a b ×ˢ (univ : Set ℝ) := by
    intro p
    simp
  refine ⟨n04b_isOpen_travelHalf (isOpen_Ioo.prod isOpen_univ) hCont side,
    n04b_travelHalfDomain_nonempty hT hF side, ?_,
    n04b_travelHalfDomain_periodic Real.pi hp hPeriod side,
    n04b_travelHalfDomain_reflection hr hReflect side⟩
  intro p hp
  exact (mem_n04bTravelDomain.mp hp).1

/-- This is the full domain-field tuple of CanonicalGeometry for a
constructed negative piece. No domain-field tuple is assumed. -/
theorem n04b_constructedNegative_domain_fields
    {S : PhysicalSpacesData} (D : ReferenceData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (i : ℕ)
    {a b T : ℝ} {F : PolarPoint → PolarPoint} (hT : 0 < T) (side : Bool)
    (hF : BijOn F (Ioo a b ×ˢ (univ : Set ℝ))
      (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (hCont : ContinuousOn F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hPeriod : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F (p + (0, Real.pi)) = F p + (0, Real.pi))
    (hReflect : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      F (p.1, -p.2) = ((F p).1, -(F p).2))
    (hDomain : physicalPieceOpen S K z i =
      n04bTravelHalfDomain (Ioo a b ×ˢ (univ : Set ℝ)) F T side)
    (hNegative : K.positive i = false)
    (hAnnular : Ioo a b ×ˢ (univ : Set ℝ) ⊆ annularOpen D)
    (hSign : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), deriv D.w p.1 < 0) :
    let Ω := physicalPieceOpen S K z i
    IsOpen Ω ∧ Ω.Nonempty ∧ Ω ⊆ annularOpen D ∧
      (∀ p : PolarPoint, p + (0, Real.pi) ∈ Ω ↔ p ∈ Ω) ∧
      (∀ p : PolarPoint, (p.1, -p.2) ∈ Ω ↔ p ∈ Ω) ∧
      (K.positive i = true → Ω = referencePhysicalPieceOpen S K i) ∧
      (∀ p ∈ Ω, K.positive i = true → 0 < deriv D.w p.1) ∧
      (∀ p ∈ Ω, K.positive i = false → deriv D.w p.1 < 0) := by
  have h := n04b_negativeHalfDomain_properties hT hF hCont hPeriod hReflect side
  dsimp only
  rw [hDomain]
  refine ⟨h.1, h.2.1, fun p hp => hAnnular (h.2.2.1 hp),
    h.2.2.2.1, h.2.2.2.2, ?_, ?_, ?_⟩
  · intro hpos
    simp [hNegative] at hpos
  · intro p hp hpos
    simp [hNegative] at hpos
  · intro p hp _
    exact hSign p (h.2.2.1 hp)

end ContinuousFlexibility.Analysis
