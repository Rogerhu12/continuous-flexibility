import ContinuousFlexibility.Analysis.N04NegativeChartNormalizationBounds
import ContinuousFlexibility.Analysis.N04NegativeChartCoordinatePullback
import ContinuousFlexibility.Analysis.N04NegativeChartData

/-!
# From the actual physical coordinates to their normalized atoms

Physical estimates are evaluated on the original reference half. The
fixed affine pullback costs only material powers; its state derivative
loss is unchanged. All towers below are towers of the stored chart.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

private def negativePhysicalProjectionRegularity (W : N04RealizationStart)
    (m : ℕ) (side radial : Bool) :
    MixedJetRegularity (sectorNeighborhood W.S W.base W.ε W.ε)
      (Ioo (W.C.left m) (W.C.right m) ×ˢ univ)
      (fun z q => if radial then
        (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m side q).1
        else (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m side q).2) := by
  cases radial
  · exact W.negativeChartMixedRegularity m side (ContinuousLinearMap.snd ℝ ℝ ℝ)
  · exact W.negativeChartMixedRegularity m side (ContinuousLinearMap.fst ℝ ℝ ℝ)

private theorem negativeChart_atom_coordinate_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    (K : CanonicalData S) (z : AnnularState S × ℝ) (k : ℕ)
    (g : PolarPoint → PolarPoint) (hg : K.chart z k = g) (radial : Bool) :
    atom D T S C L K z k (if radial then .chartRadial else .chartAngleDefect) =
      fun q => (if radial then K.right k - K.left k else 1)⁻¹ *
        ((if radial then (g (physicalUnitPoint K k q)).1
          else (g (physicalUnitPoint K k q)).2) -
          (if radial then K.left k else q.2)) := by
  funext q
  cases radial with
  | false =>
      change (K.chart z k (physicalUnitPoint K k q)).2 - q.2 =
        (1 : ℝ)⁻¹ * ((g (physicalUnitPoint K k q)).2 - q.2)
      rw [inv_one, one_mul]
      exact congrArg (fun f : PolarPoint → PolarPoint =>
        (f (physicalUnitPoint K k q)).2 - q.2) hg
  | true =>
      change ((K.chart z k (physicalUnitPoint K k q)).1 - K.left k) /
        (K.right k - K.left k) =
          (K.right k - K.left k)⁻¹ * ((g (physicalUnitPoint K k q)).1 - K.left k)
      calc
        _ = ((g (physicalUnitPoint K k q)).1 - K.left k) /
            (K.right k - K.left k) := congrArg (fun f : PolarPoint → PolarPoint =>
          ((f (physicalUnitPoint K k q)).1 - K.left k) / (K.right k - K.left k)) hg
        _ = _ := by rw [div_eq_mul_inv, mul_comm]

private theorem normalized_coordinate_cost
    {a c d B C D E H V : ℝ} (hE : 1 ≤ E) (hH : 0 ≤ H) (hV : 0 ≤ V)
    (hC : 0 ≤ C) (ha : a = c * d)
    (hc : |c| ≤ C * E ^ C) (hd : |d| ≤ B * E ^ B * H * V)
    (hpack : (C * B) * E ^ (C + B) ≤ D * E ^ D) :
    |a| ≤ D * E ^ D * H * V := by
  calc
    |a| = |c| * |d| := by rw [ha, abs_mul]
    _ ≤ (C * E ^ C) * (B * E ^ B * H * V) :=
      mul_le_mul hc hd (abs_nonneg _)
        (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hE) C))
    _ = ((C * B) * E ^ (C + B)) * H * V := by
      rw [Real.rpow_add (zero_lt_one.trans_le hE)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpack hH) hV

/-- Positive state jets of the two literal physical chart components.
The constants precede the component, side, projection and spatial point. -/
def N04NegativeChartPhysicalPositiveBounds
    (W : N04RealizationStart) (e : ℕ ≃ N04PieceIndex W.D) (b : ℕ) (ε : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ m (side radial : Bool) p,
      p ∈ referencePhysicalPieceOpen W.S (W.A e) (e.symm (.inl (m, side))) →
      ∀ i j : ℕ, i + j ≤ s →
      ∀ J : SmoothDirections (sectorNeighborhood W.S b ε ε)
        (fun z => mixedDerivative i j (fun q =>
          if radial then
            (n04bActualNegativeChart W.hT W.hS W.through03 W.field
              (liftSectorParameter W.S W.C z) m side q).1
          else
            (n04bActualNegativeChart W.hT W.hS W.through03 W.field
              (liftSectorParameter W.S W.C z) m side q).2) p),
      ∀ z ∈ sectorNeighborhood W.S b ε ε, ∀ v : Fin n → Parameter W.S,
        |J.D n z v| ≤
          B * W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ B *
            W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ) *
              oneHighVariationWeight (parameterGrading W.S) b (s + loss) z v

set_option diagnostics true in
/-- A stronger low seminorm and a smaller state neighborhood preserve
the physical estimate. Uniqueness compares every requested tower with
the actual chart tower on the original neighborhood. -/
theorem N04NegativeChartPhysicalPositiveBounds.mono
    {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
    {b b' : ℕ} {ε ε' : ℝ}
    (h : N04NegativeChartPhysicalPositiveBounds W e b ε)
    (hbW : W.base ≤ b) (hεW : ε ≤ W.ε) (hb : b ≤ b') (hε : ε' ≤ ε) :
    N04NegativeChartPhysicalPositiveBounds W e b' ε' := by
  intro n hn
  have hnB := h n hn
  let loss := hnB.choose
  refine ⟨loss, fun s => ?_⟩
  have hs := hnB.choose_spec s
  let B := hs.choose
  have hB : 0 < B := hs.choose_spec.1
  have hbound := hs.choose_spec.2
  refine ⟨B, hB, fun m side radial p hp i j hij J z hz v => ?_⟩
  have hp' := n04NegativeGeometry_referenceHalf_subset_component
    W.hT W.hS W.through03 W.field e (e.symm (.inl (m, side))) m side
    (e.apply_symm_apply _) hp
  let R := negativePhysicalProjectionRegularity W m side radial
  let J₀ : SmoothDirections (sectorNeighborhood W.S b ε ε)
      (fun x => mixedDerivative i j (fun q =>
        if radial then
          (n04bActualNegativeChart W.hT W.hS W.through03 W.field
            (liftSectorParameter W.S W.C x) m side q).1
        else
          (n04bActualNegativeChart W.hT W.hS W.through03 W.field
            (liftSectorParameter W.S W.C x) m side q).2) p) :=
    (R.parameter i j p hp').restrict (isOpen_sectorNeighborhood W.S b ε ε)
      (sectorNeighborhood_mono W.S hbW hεW hεW)
  have hsub := sectorNeighborhood_mono W.S hb hε hε
  have he : J.D n z v = J₀.D n z v :=
    congrArg (fun L : Parameter W.S [×n]→L[ℝ] ℝ => L v)
      (J.unique (J₀.restrict (isOpen_sectorNeighborhood W.S b' ε' ε') hsub) n z hz)
  have hr := hbound m side radial p hp i j hij J₀ z (hsub hz) v
  have hweight := oneHighVariationWeight_mono (n07aParameterGrading_monotone W.S)
    hb (le_rfl : s + loss ≤ s + loss) z v
  have hcost : 0 ≤
      B * W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ B *
        W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ) := by
    apply mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg
      (zero_le_one.trans (W.floor _)) B))
    exact Real.rpow_nonneg (W.hT.2.1 _
      (materialSample_mem_interval W.radial.1 W.hT _)).2.1.le _
  exact (congrArg abs he).trans_le (hr.trans (mul_le_mul_of_nonneg_left hweight hcost))

namespace N04RealizationStart

variable (W : N04RealizationStart)

set_option diagnostics true in
/-- The normalization retains the same state loss. In particular, no
spatial order is used to choose the neighborhood or its low seminorm. -/
theorem negativeChart_normalized_positive_bounds
    (e : ℕ ≃ N04PieceIndex W.D) {b : ℕ} {ε : ℝ}
    (hb : W.base ≤ b) (hε : ε ≤ W.ε)
    (hphysical : N04NegativeChartPhysicalPositiveBounds W e b ε) :
    ∀ n : ℕ, 0 < n → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m (side radial : Bool) q, q ∈ unitStrip →
      ∀ i j : ℕ, i + j ≤ s →
      ∀ J : SmoothDirections (sectorNeighborhood W.S b ε ε)
        (fun z => mixedDerivative i j
          (atom W.D W.U W.S W.C W.L (W.A e) (liftSectorParameter W.S W.C z)
            (e.symm (.inl (m, side))) (if radial then .chartRadial else .chartAngleDefect)) q),
      ∀ z ∈ sectorNeighborhood W.S b ε ε, ∀ v : Fin n → Parameter W.S,
        |J.D n z v| ≤
          B * W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ B *
            W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ) *
              oneHighVariationWeight (parameterGrading W.S) b (s + loss) z v := by
  intro n hn
  have hphys := hphysical n hn
  let loss := hphys.choose
  refine ⟨loss, fun s => ?_⟩
  have hbs := hphys.choose_spec s
  let B := hbs.choose
  have hbound := hbs.choose_spec.2
  have hsc := W.negativeChart_normalization_material e s
  let C := hsc.choose
  have hC : 0 < C := hsc.choose_spec.1
  have hscale := hsc.choose_spec.2
  have henv := coefficientEnvelope_pack (C * B) (C + B)
  let D := henv.choose
  have hD : 0 < D := henv.choose_spec.1
  have hpack := henv.choose_spec.2
  refine ⟨D, hD, fun m side radial q hq i j hij J z hz v => ?_⟩
  let K := W.A e
  let k := e.symm (.inl (m, side))
  let U := sectorNeighborhood W.S b ε ε
  let Ω : Set PolarPoint := Ioo (W.C.left m) (W.C.right m) ×ˢ univ
  let f : Parameter W.S → PolarPoint → ℝ := fun x p =>
    if radial then (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C x) m side p).1
    else (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C x) m side p).2
  let c : ℝ := K.physicalRight k - K.physicalLeft k
  let d : ℝ := if radial then K.right k - K.left k else 1
  let h : PolarPoint → ℝ := fun q => if radial then K.left k else q.2
  let p := physicalUnitPoint K k q
  have hU : IsOpen U := isOpen_sectorNeighborhood W.S b ε ε
  have hsub := sectorNeighborhood_mono W.S hb hε hε
  have hPart := n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field e
  have hunit := n04NegativeGeometry_affine_unitPoint
    (K.physicalLeft k) (K.physicalRight k) (hPart.referenceBounds k).1
  have hmap : MapsTo (physicalUnitPoint K k) unitStrip Ω := fun y hy =>
    n04NegativeGeometry_referenceHalf_subset_component W.hT W.hS W.through03 W.field
      e k m side (e.apply_symm_apply _) (hunit.2.1 hy)
  let RF := negativePhysicalProjectionRegularity W m side radial
  let JP : SmoothDirections U (fun x => mixedDerivative i j (f x) p) :=
    (RF.parameter i j p (hmap hq)).restrict hU hsub
  have hf (x : Parameter W.S) (hx : x ∈ U) : ContDiffOn ℝ ∞ (f x) Ω :=
    RF.spatial x (hsub hx)
  have hh : ContDiffOn ℝ ∞ h unitStrip := by
    cases radial <;> first | exact contDiffOn_const | exact contDiff_snd.contDiffOn
  have hchart (x : Parameter W.S) : K.chart (liftSectorParameter W.S W.C x) k =
      n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C x) m side :=
    (n04bTypedAtlasData_negative_fields (C := W.C) (L := W.L)
      (z := liftSectorParameter W.S W.C x) e
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field)
      (n04bActualNegativeHeight W.hT W.hS W.through03 W.field)
      (n04bActualNegativeInverse W.hT W.hS W.through03 W.field)
      (n04bActualReferenceCut W.through03) k m side (e.apply_symm_apply _)).2.2.2.1
  have hatom (x : Parameter W.S) :
      atom W.D W.U W.S W.C W.L K (liftSectorParameter W.S W.C x) k
        (if radial then .chartRadial else .chartAngleDefect) =
      (fun y : PolarPoint => d⁻¹ * (f x (K.physicalLeft k + c * y.1, y.2) - h y)) :=
    negativeChart_atom_coordinate_eq K (liftSectorParameter W.S W.C x) k
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C x) m side) (hchart x) radial
  let JK := J.congrOn (fun x _ =>
    congrArg (fun g : PolarPoint → ℝ => mixedDerivative i j g q) (hatom x))
  have hjet := n04NegativeChart_coordinatePullback_positiveJet hU
    (K.physicalLeft k) c d h hh hf hmap i j hq JP JK hn hz v
  have hraw := hbound m side radial p (hunit.2.1 hq) i j hij JP z hz v
  let E : ℝ := W.T.E0 (W.T.sample (K.cell k))
  let H : ℝ := W.T.H (W.T.sample (K.cell k)) ^ (3 / 4 : ℝ)
  let V : ℝ := oneHighVariationWeight (parameterGrading W.S) b (s + loss) z v
  have hE : 1 ≤ E := W.floor _
  have hH : 0 ≤ H := Real.rpow_nonneg
    (W.hT.2.1 _ (materialSample_mem_interval W.radial.1 W.hT (K.cell k))).2.1.le _
  have hV : 0 ≤ V := oneHighVariationWeight_nonneg _ _ _ _ _
  have hd : |d⁻¹| ≤ 1 + |(K.right k - K.left k)⁻¹| := by
    cases radial <;> simp only [d, Bool.false_eq_true, ↓reduceIte, inv_one, abs_one]
    · exact le_add_of_nonneg_right (abs_nonneg _)
    · exact le_add_of_nonneg_left zero_le_one
  have hcoef : |c ^ i / d| ≤ C * E ^ C := by
    rw [div_eq_mul_inv, abs_mul]
    exact (mul_le_mul_of_nonneg_left hd (abs_nonneg _)).trans
      (hscale m side i (by omega))
  exact normalized_coordinate_cost hE hH hV hC.le hjet hcoef hraw (hpack E hE)

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeChart_normalized_positive_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeChart_normalized_positive_bounds
