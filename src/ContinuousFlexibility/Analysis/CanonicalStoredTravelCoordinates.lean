module

public import ContinuousFlexibility.Analysis.CanonicalStoredSliceBijection

/-!
# Recovering the actual negative chart from stored characteristic footpoints

The two genuine first integrals determine the angular coordinate and the
Airy radial travel by elementary linear algebra. The right half measures
radial travel backwards from the full N01 travel. The footpoints here are
those of the original stored N03 flow, whose slice bijectivity was proved
from the existing canonical geometry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The two glued values recover both actual chart components on either
open half. Only disjointness of the two physical domains is used here. -/
theorem canonicalCutPair_chartValues_of_gluedIntegrals
    {S : PhysicalSpacesData} {K : CanonicalData S} {z : AnnularState S × ℝ}
    (m : ℕ) (side : Bool)
    (hdisjoint : Disjoint (physicalPieceOpen S K z (K.cutPair m).1)
      (physicalPieceOpen S K z (K.cutPair m).2))
    {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K z
      (if side then (K.cutPair m).2 else (K.cutPair m).1)) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let V := canonicalGluedAiryIntegral S K z m 1 p
    let U := canonicalGluedAiryIntegral S K z m (-1) p
    (K.chart z i p).2 = (V + U) / 2 ∧
      airyTravelPrimitive (K.chart z i p).1 =
        if side then 2 * airyTravelPrimitive (K.cutRadius m) - (V - U) / 2
        else (V - U) / 2 := by
  classical
  cases side with
  | false =>
      have hm : canonicalGluedAiryIntegral S K z m 1 p =
          (K.chart z (K.cutPair m).1 p).2 +
            (1 : ℝ) * airyTravelPrimitive (K.chart z (K.cutPair m).1 p).1 := by
        change canonicalGluedAiryIntegral S K z m 1 p =
          airyFirstIntegral (K.chart z (K.cutPair m).1) 1 p
        exact piecewise_eq_of_mem _ _ _ hp
      have hp' : canonicalGluedAiryIntegral S K z m (-1) p =
          (K.chart z (K.cutPair m).1 p).2 +
            (-1 : ℝ) * airyTravelPrimitive (K.chart z (K.cutPair m).1 p).1 := by
        change canonicalGluedAiryIntegral S K z m (-1) p =
          airyFirstIntegral (K.chart z (K.cutPair m).1) (-1) p
        exact piecewise_eq_of_mem _ _ _ hp
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor <;> linarith only [hm, hp']
  | true =>
      have hn : p ∉ physicalPieceOpen S K z (K.cutPair m).1 :=
        fun h => Set.disjoint_left.mp hdisjoint h hp
      have hm : canonicalGluedAiryIntegral S K z m 1 p =
          (K.chart z (K.cutPair m).2 p).2 +
            (-1 : ℝ) * airyTravelPrimitive (K.chart z (K.cutPair m).2 p).1 +
              2 * (1 : ℝ) * airyTravelPrimitive (K.cutRadius m) := by
        change canonicalGluedAiryIntegral S K z m 1 p =
          airyFirstIntegral (K.chart z (K.cutPair m).2) (-1) p +
            2 * (1 : ℝ) * airyTravelPrimitive (K.cutRadius m)
        exact piecewise_eq_of_notMem _ _ _ hn
      have hp' : canonicalGluedAiryIntegral S K z m (-1) p =
          (K.chart z (K.cutPair m).2 p).2 +
            (-(-1 : ℝ)) * airyTravelPrimitive (K.chart z (K.cutPair m).2 p).1 +
              2 * (-1 : ℝ) * airyTravelPrimitive (K.cutRadius m) := by
        change canonicalGluedAiryIntegral S K z m (-1) p =
          airyFirstIntegral (K.chart z (K.cutPair m).2) (-(-1)) p +
            2 * (-1 : ℝ) * airyTravelPrimitive (K.cutRadius m)
        exact piecewise_eq_of_notMem _ _ _ hn
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor <;> linarith only [hm, hp']

/-- The existing negative chart has the actual stored-footpoint formula
throughout its physical open half. In particular the right radial travel
is measured from the true N01 total travel, with no free boundary gauge. -/
theorem canonicalCutPair_chartValues_eq_storedFootpoints
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K z
      (if side then (K.cutPair m).2 else (K.cutPair m).1)) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let V := stateLeftChart S z.1 m (Function.invFun (L.minusFlow z m p.1) p.2)
    let U := -stateLeftChart S z.1 m (Function.invFun (L.minusFlow z m p.1) (-p.2))
    (K.chart z i p).2 = (V + U) / 2 ∧
      airyTravelPrimitive (K.chart z i p).1 =
        if side then C.travel m - (V - U) / 2 else (V - U) / 2 := by
  have hwhere : p ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
      physicalPieceOpen S K z (K.cutPair m).2 := by
    cases side
    · exact Or.inl hp
    · exact Or.inr hp
  rw [(hB.1.2 z hz hs m).2.2.2.1] at hwhere
  have hr : p.1 ∈ Ioo (C.left m) (C.right m) := hwhere.1.1
  have honto := (n03CharacteristicSlice_bijective
    hS hT hN01 hN03 hA hB hz hs hN02 m hr).2
  have hm : canonicalGluedAiryIntegral S K z m 1 p =
      stateLeftChart S z.1 m (Function.invFun (L.minusFlow z m p.1) p.2) :=
    (canonicalGluedAiryIntegral_eq_storedFootpoints
      hS hT hN01 hN03 hA hB hz hs hN02 m hr p.2).1
  let φ : ℝ := Function.invFun (L.minusFlow z m p.1) (-p.2)
  have hφ : L.minusFlow z m p.1 φ = -p.2 := Function.rightInverse_invFun honto (-p.2)
  have hodd : stateLeftChart S z.1 m (-φ) = -stateLeftChart S z.1 m φ :=
    (hN01.2.2.2.2.2.2.2.1 z hz hs m φ).2.2.2
  have hp' : canonicalGluedAiryIntegral S K z m (-1) p = -stateLeftChart S z.1 m φ := by
    simpa only [neg_neg, hφ, hodd] using
      (canonicalGluedAiryIntegral_on_n03Flows
        hS hT hN01 hN02 hN03 hA hB hz hs m hr (-φ)).2
  have hvalues := canonicalCutPair_chartValues_of_gluedIntegrals
    m side (hB.1.2 z hz hs m).2.2.1 hp
  rw [hm, hp'] at hvalues
  have hwidth := (canonicalRootGauges_eq_n01_of_n03
    hS hT hN01 hN02 hN03 hA hB hz hs m).1
  simpa only [hwidth] using hvalues

end ContinuousFlexibility.Analysis
