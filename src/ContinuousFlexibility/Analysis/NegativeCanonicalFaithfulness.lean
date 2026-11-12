import ContinuousFlexibility.Analysis.PreconnectedOperatorFaithfulness
import ContinuousFlexibility.Analysis.EffectiveRadialCoefficient
import ContinuousFlexibility.Analysis.CanonicalDomainConnected
import ContinuousFlexibility.Analysis.N01CoefficientValueJets

/-!
# The stored operator equals the actual smooth field on each negative half

The reverse-coordinate action first recovers the original positive radial
coefficient. The actual current piece is preconnected and contains a true
reflection-axis point. The pointwise operator classification therefore
recovers all three stored coefficients, without assuming regularity of the
stored mixed or angular field. The paired halves have canonical left
endpoint zero, so their smooth comparison discriminant is strictly positive.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Positivity uses only the actual N01 value inequalities. -/
theorem n01_originalRadialCoefficient_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    0 < (originalCoefficients D S C z).a p := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hwref : 0 < D.w p.1 := hD.1.2.2.2.2.1 p.1 hp.1
  have hlow := hN.2.2.2.2.2.2.2.2.2.1 z hz hsector p hp
  have hw : 0 < stateProfile D S C z.1 p.1 :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hwref).trans_le
      ((le_div_iff₀ hwref).mp hlow.1)
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) :=
    (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) hw).trans_le
      ((le_div_iff₀ hw).mp hlow.2.2.1)
  have hdisc : 0 < polarDiscriminant (stateProfile D S C z.1)
      (stateHeight D S C z) p :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hlow.2.2.2.2.1
  exact mul_pos hQ (inverseDThreeHalves_pos _ hdisc)

/-- Any negative current piece whose canonical radius is positive in
the interior has faithful stored coefficients. The only regularity and
positivity inputs concern the actual original radial coefficient. -/
theorem negativeCanonicalClosedCoefficients_eq_stored
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hN03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (hm : K.positive m = false)
    (hleft : 0 ≤ K.left m)
    (hOriginal : ∀ p ∈ physicalPieceOpen S K z m,
      DifferentiableAt ℝ (originalCoefficients D S C z).a p)
    (hpositive : ∀ p ∈ physicalPieceOpen S K z m,
      0 < (originalCoefficients D S C z).a p) :
    ∀ p ∈ physicalPieceOpen S K z m,
      (L.coefficients z).a p = (negativeCanonicalClosedCoefficients S K z m).a p ∧
      (L.coefficients z).b p = (negativeCanonicalClosedCoefficients S K z m).b p ∧
      (L.coefficients z).c p = (negativeCanonicalClosedCoefficients S K z m).c p := by
  have hLaeq : (L.coefficients z).a = (originalCoefficients D S C z).a :=
    funext (hN03.1 z hz hsector)
  have hLa (p : PolarPoint) (hp : p ∈ physicalPieceOpen S K z m) :
      DifferentiableAt ℝ (L.coefficients z).a p := by
    rw [hLaeq]
    exact hOriginal p hp
  have hregular (p : PolarPoint) (hp : p ∈ physicalPieceOpen S K z m) :=
    negativeCanonicalClosedCoefficients_contDiffAt hA hz hsector m (subset_closure hp)
  have hBa0 (p : PolarPoint) (hp : p ∈ physicalPieceOpen S K z m) :
      (negativeCanonicalClosedCoefficients S K z m).a p ≠ 0 := by
    rw [negativeCanonicalClosedCoefficients_radial_eq_original
      hA hB hN03 hz hsector m hm hp (hOriginal p hp)]
    exact (hpositive p hp).ne'
  have hdisc (p : PolarPoint) (hp : p ∈ physicalPieceOpen S K z m) :
      0 < (negativeCanonicalClosedCoefficients S K z m).b p ^ 2 -
        (negativeCanonicalClosedCoefficients S K z m).a p *
          (negativeCanonicalClosedCoefficients S K z m).c p := by
    have hFp := (hA.charts z hz hsector m).1 hp
    have hξ : 0 < (K.chart z m p).1 := hleft.trans_lt hFp.1.1
    have hh : 0 < K.height z m p :=
      ((hA.charts z hz hsector m).2.2.2.2.2.2.2 p hp).1
    have he := negativeCanonicalClosedCoefficients_determinant
      hA hz hsector m (subset_closure hp)
    have hquot : 0 < (K.chart z m p).1 / K.height z m p ^ 4 :=
      div_pos hξ (pow_pos hh 4)
    rw [neg_div] at he
    linarith only [he, hquot]
  exact coefficients_eq_on_of_preconnected_operator_action
    (canonicalPhysicalPiece_isPreconnected hA hz hsector m) hLa
    (fun p hp => (hregular p hp).1.differentiableAt (by simp))
    (fun p hp => (hregular p hp).2.1.differentiableAt (by simp))
    (fun p hp => (hregular p hp).2.2.differentiableAt (by simp))
    hBa0 hdisc (canonicalPhysicalPiece_exists_zero_mixedCoefficient hA hN03 hz hsector m)
    (fun p hp u hu => negativeCanonicalClosedOperator_of_parts
      hA hB hz hsector m hm u hu.contDiffOn hp)

/-- Both paired negative halves are faithful under precisely the actual
N01/N03 and canonical hypotheses. One Bool parameter treats both sides. -/
theorem negativeCutPair_coefficients_eq_closed
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (side : Bool) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    ∀ p ∈ physicalPieceOpen S K z i,
      (L.coefficients z).a p = (negativeCanonicalClosedCoefficients S K z i).a p ∧
      (L.coefficients z).b p = (negativeCanonicalClosedCoefficients S K z i).b p ∧
      (L.coefficients z).c p = (negativeCanonicalClosedCoefficients S K z i).c p := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  obtain ⟨hnegL, hnegR, _, _, _, _, hleftL, hleftR, _, _⟩ := hB.1.1 m
  have hm : K.positive i = false := by
    cases side with
    | false => exact hnegL
    | true => exact hnegR
  have hleft : 0 ≤ K.left i := by
    cases side <;> simp only [i, Bool.false_eq_true, ↓reduceIte, hleftL, hleftR, le_refl]
  have hOriginal : ContDiffOn ℝ ∞ (originalCoefficients D S C z).a (annularOpen D) :=
    contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hsector 0
  exact negativeCanonicalClosedCoefficients_eq_stored hA hB hN03 hz hsector i hm hleft
    (fun p hp => ((hOriginal p ((hA.domains z hz hsector i).2.2.1 hp)).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        ((hA.domains z hz hsector i).2.2.1 hp))).differentiableAt (by simp))
    (fun p hp => n01_originalRadialCoefficient_pos hN01 hz hsector
      ((hA.domains z hz hsector i).2.2.1 hp))

end ContinuousFlexibility.Analysis
