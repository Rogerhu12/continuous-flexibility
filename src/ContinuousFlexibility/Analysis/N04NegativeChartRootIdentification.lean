import ContinuousFlexibility.Analysis.N04NegativeChartRootFootpoints
import ContinuousFlexibility.Analysis.N04bRootHeightMatching

/-!
# The literal current chart is the supplied root projection

Both ends use the same reverse flow and the actual odd endpoint label.
The right travel complement is retained exactly. Equality holds on the
whole material band and hence on a joint state/spatial neighborhood of
each positive point of every smaller closed band.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem rootTravel_of_signed_footpoints
    (G : ℝ × ℝ × ℝ → ℝ) (u : ℝ → ℝ) (T x θ : ℝ) (side : Bool)
    (hm : ∀ η, G (x, (-n01ComponentRootOrientation side) * x ^ (3 / 2 : ℝ), η) =
      u η - if side then T else 0)
    (hr : ∀ ζ η, G (x, -ζ, -η) = -G (x, ζ, η)) :
    characteristicTravelChart (rootCharacteristicCoordinate G 1)
      (rootCharacteristicCoordinate G (-1)) (x, θ) =
      (n04bTravelOrientation T side ((u θ + u (-θ)) / 2), (u θ - u (-θ)) / 2) := by
  cases side with
  | false =>
      simp only [n01ComponentRootOrientation, Bool.false_eq_true, ↓reduceIte,
        neg_one_mul, sub_zero] at hm
      have hh : G (x, x ^ (3 / 2 : ℝ), θ) = -G (x, -(x ^ (3 / 2 : ℝ)), -θ) := by
        simpa only [neg_neg] using hr (-(x ^ (3 / 2 : ℝ))) (-θ)
      simp only [characteristicTravelChart, rootCharacteristicCoordinate, one_mul,
        neg_one_mul, hh, hm, n04bTravelOrientation, Bool.false_eq_true, ↓reduceIte]
      apply Prod.ext <;> dsimp only <;> ring
  | true =>
      simp only [n01ComponentRootOrientation, ↓reduceIte, neg_neg, one_mul] at hm
      have hh : G (x, -(x ^ (3 / 2 : ℝ)), θ) = -G (x, x ^ (3 / 2 : ℝ), -θ) := by
        simpa only [neg_neg] using hr (x ^ (3 / 2 : ℝ)) (-θ)
      simp only [characteristicTravelChart, rootCharacteristicCoordinate, one_mul,
        neg_one_mul, hh, hm, n04bTravelOrientation, ↓reduceIte]
      apply Prod.ext <;> dsimp only <;> ring

namespace N04RealizationStart

variable (W : N04RealizationStart)
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {d c : P × PolarPoint → ℝ} {δ : ℝ}

/-- The numerical inverse is re-used with the actual endpoint label.
The independent root parameter retains the exact square-root scale. -/
def negativeRootInverseCoordinate (A : NegativeChartRootFlowData d c δ)
    (z : AnnularState W.S × ℝ) (m : ℕ) (side : Bool) (y : P)
    (q : ℝ × ℝ × ℝ) : ℝ :=
  n01RootLabel W.S W.C z m side (A.inverse y (q.1, Real.sqrt δ * q.2.1) 1 q.2.2)

namespace NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

theorem fullHalfFields_root_travel
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdp : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi)
    (hcp : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi)
    (A : NegativeChartRootFlowData d c δ) (y : P)
    {z : AnnularState W.S × ℝ}
    (hz : z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (hs : stateSector W.S z.1) (m : ℕ) (side : Bool)
    {R : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hδc : δ * R ≤ W.negativeMaterialCollar m)
    (hrep : ∀ p : PolarPoint, p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
      d (y, p) = F.fullHalfDrift z m side p ∧
      c (y, p) = F.fullHalfSpeed z m side p)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) R) (θ : ℝ) :
    characteristicTravelChart
      (rootCharacteristicCoordinate (W.negativeRootInverseCoordinate A z m side y) 1)
      (rootCharacteristicCoordinate (W.negativeRootInverseCoordinate A z m side y) (-1))
      (x, θ) =
      (n04bTravelOrientation (W.C.travel m) side
        (n04bActualTravelChart W.S W.C W.L z m
          (W.negativeInwardPoint m side (δ * x, θ))).1,
       (n04bActualTravelChart W.S W.C W.L z m
          (W.negativeInwardPoint m side (δ * x, θ))).2) := by
  let G := W.negativeRootInverseCoordinate A z m side y
  let u : ℝ → ℝ := fun η => n04bMinusFirstIntegral (fun p => W.L.minusFlow z m p.1 p.2)
    (stateLeftChart W.S z.1 m) (W.negativeInwardPoint m side (δ * x, η))
  have hz' : z ∈ stateNeighborhood W.S W.C W.base W.ε :=
    stateNeighborhood_mono W.S W.C le_rfl (by linarith [W.ε_pos]) hz
  have hδx : 0 < δ * x := mul_pos hδ hx.1
  have hband : δ * x ≤ W.negativeMaterialCollar m :=
    (mul_le_mul_of_nonneg_left hx.2 hδ.le).trans hδc
  have hhalf := (W.negativeMaterialCollar_bounds m).2.2.2 side
  have hw := W.negativeOpticalWidth_pos m side
  have hwidth : δ * x < W.negativeOpticalWidth m side := by
    linarith only [hband, hhalf, hw]
  have hpar (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (δ * x)) (η : ℝ) :
      d (y, (r, -η)) = -d (y, (r, η)) ∧ c (y, (r, -η)) = c (y, (r, η)) := by
    have hp : r ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) :=
      ⟨hr.1, hr.2.trans hwidth.le⟩
    have hn := hrep (r, -η) hp
    have hh := hrep (r, η) hp
    rw [hn.1, hn.2, hh.1, hh.2]
    exact F.fullHalfFields_reflect z m side r η
  have href (ζ η : ℝ) : G (x, -ζ, -η) = -G (x, ζ, η) := by
    change n01RootLabel W.S W.C z m side
      (A.inverse y (x, Real.sqrt δ * -ζ) 1 (-η)) = _
    rw [mul_neg, A.inverse_reflect_on_fiber hd hc hdp hcp y hδx.le hpar]
    exact n01RootLabel_odd W.through03.1.1 hz' hs m side _
  have hm (η : ℝ) : G (x, (-n01ComponentRootOrientation side) * x ^ (3 / 2 : ℝ), η) =
      u η - if side then W.C.travel m else 0 := by
    change n01RootLabel W.S W.C z m side
      (A.inverse y (x, Real.sqrt δ *
        ((-n01ComponentRootOrientation side) * x ^ (3 / 2 : ℝ))) 1 η) = _
    rw [show Real.sqrt δ * ((-n01ComponentRootOrientation side) * x ^ (3 / 2 : ℝ)) =
      ((-n01ComponentRootOrientation side) * Real.sqrt δ) * x ^ (3 / 2 : ℝ) by ring]
    simpa only [u, n04bMinusFirstIntegral, parameterizedCircleInverse,
      W.negativeInwardPoint_root_add] using
      F.fullHalfFields_inverse_root_label hd hc hdp hcp A y hz hs m side hR hδ hδc hrep
        ⟨hx.1.le, hx.2⟩ η
  have ht : characteristicTravelChart (rootCharacteristicCoordinate G 1)
      (rootCharacteristicCoordinate G (-1)) (x, θ) =
      (n04bTravelOrientation (W.C.travel m) side
        (n04bActualTravelChart W.S W.C W.L z m
          (W.negativeInwardPoint m side (δ * x, θ))).1,
       (n04bActualTravelChart W.S W.C W.L z m
          (W.negativeInwardPoint m side (δ * x, θ))).2) := by
    have ha : n04bActualTravelChart W.S W.C W.L z m
        (W.negativeInwardPoint m side (δ * x, θ)) =
        ((u θ + u (-θ)) / 2, (u θ - u (-θ)) / 2) := by
      change ((1 / 2 : ℝ) * (u θ - -u (-θ)),
        (1 / 2 : ℝ) * (-u (-θ) + u θ)) = _
      apply Prod.ext <;> dsimp only <;> ring
    rw [ha]
    exact rootTravel_of_signed_footpoints G u (W.C.travel m) x θ side hm href
  exact ht

theorem fullHalfFields_root_chart
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdp : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi)
    (hcp : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi)
    (A : NegativeChartRootFlowData d c δ) (y : P)
    {z : AnnularState W.S × ℝ}
    (hz : z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (hs : stateSector W.S z.1) (m : ℕ) (side : Bool)
    {R : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hδc : δ * R ≤ W.negativeMaterialCollar m)
    (hrep : ∀ p : PolarPoint, p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
      d (y, p) = F.fullHalfDrift z m side p ∧
      c (y, p) = F.fullHalfSpeed z m side p)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) R) (θ : ℝ) :
    extendedRootEvenOddChart (W.negativeRootInverseCoordinate A z m side y) (x, θ) =
      n04bActualNegativeChart W.hT W.hS W.through03 W.field z m side
        (W.negativeInwardPoint m side (δ * x, θ)) := by
  let G := W.negativeRootInverseCoordinate A z m side y
  have ht := F.fullHalfFields_root_travel hd hc hdp hcp A y hz hs m side hR hδ hδc hrep hx θ
  have hz' : z ∈ stateNeighborhood W.S W.C W.base W.ε :=
    stateNeighborhood_mono W.S W.C le_rfl (by linarith [W.ε_pos]) hz
  have hδx : 0 < δ * x := mul_pos hδ hx.1
  have hband : δ * x ≤ W.negativeMaterialCollar m :=
    (mul_le_mul_of_nonneg_left hx.2 hδ.le).trans hδc
  have hhalf := (W.negativeMaterialCollar_bounds m).2.2.2 side
  have hw := W.negativeOpticalWidth_pos m side
  have hwidth : δ * x < W.negativeOpticalWidth m side := by
    linarith only [hband, hhalf, hw]
  have hp : W.negativeInwardPoint m side (δ * x, θ) ∈
      Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ) := by
    have hh := hwidth.trans (W.negativeOpticalWidth_lt_component m side)
    refine ⟨?_, mem_univ _⟩
    cases side <;> simp only [negativeInwardPoint, inwardComponentPoint,
      Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith only [hδx, hh]
  have htravel := (n04b_actualTravelChart_bijOn W.through03 W.hS W.hT W.field hz' hs m).mapsTo hp
  have hτ := n04b_travelOrientation_pos_of_fullStrip side htravel.1
  have hv := congrArg Prod.fst
    (characteristicTravelChart_rootCharacteristicCoordinate G (p := (x, θ)) hx.1)
  rw [ht] at hv
  dsimp only at hv
  have hχ : 0 ≤ rootOddCoefficient G (x, θ) := by
    by_contra hn
    have hm := mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hx.1 (3 / 2 : ℝ))
      (lt_of_not_ge hn)
    linarith only [hv, hτ, hm]
  have he := extendedRootEvenOddChart_eq_rootTravelPower G (p := (x, θ)) hx.1 hχ
  rw [ht] at he
  calc
    _ = n04bRootPhysicalChart (n04bActualTravelChart W.S W.C W.L z m)
        (W.C.travel m) side (W.negativeInwardPoint m side (δ * x, θ)) := by
      simpa only [n04bRootPhysicalChart, n04bRootStripChart, n04bRootHalfCoordinate,
        n04b_rootTravelPower_eq_rootCoordinate] using he
    _ = _ := ((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
      hz' hs m side).component_chart_germ hp).self_of_nhds.symm

/-- A uniform representative neighborhood gives equality of the full
finite-plot functions on an open state/spatial germ. Taking `R = 2`
covers every positive point of the closed normalized unit collar. -/
theorem fullHalfFields_root_chart_germ
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdp : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi)
    (hcp : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi)
    (A : NegativeChartRootFlowData d c δ)
    (z : P → AnnularState W.S × ℝ) (V : Set P) (hV : IsOpen V)
    (hz : ∀ y ∈ V, z y ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (hs : ∀ y ∈ V, stateSector W.S (z y).1) (m : ℕ) (side : Bool)
    {R : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hδc : δ * R ≤ W.negativeMaterialCollar m)
    (hrep : ∀ y ∈ V, ∀ p : PolarPoint,
      p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
      d (y, p) = F.fullHalfDrift (z y) m side p ∧
      c (y, p) = F.fullHalfSpeed (z y) m side p)
    {y : P} (hy : y ∈ V) {p : PolarPoint} (hp : p.1 ∈ Ioo (0 : ℝ) R) :
    (fun q : P × PolarPoint => extendedRootEvenOddChart
      (W.negativeRootInverseCoordinate A (z q.1) m side q.1) q.2) =ᶠ[𝓝 (y, p)]
    (fun q => n04bActualNegativeChart W.hT W.hS W.through03 W.field (z q.1) m side
      (W.negativeInwardPoint m side (δ * q.2.1, q.2.2))) := by
  filter_upwards [(hV.prod (isOpen_Ioo.prod isOpen_univ)).mem_nhds
    (show (y, p) ∈ V ×ˢ (Ioo (0 : ℝ) R ×ˢ univ) from ⟨hy, hp, mem_univ _⟩)] with q hq
  exact F.fullHalfFields_root_chart hd hc hdp hcp A q.1 (hz q.1 hq.1)
    (hs q.1 hq.1) m side hR hδ hδc (hrep q.1 hq.1)
    ⟨hq.2.1.1, hq.2.1.2.le⟩ q.2.2

end NegativeOpticalFactors
end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_root_chart_germ'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_root_chart_germ
