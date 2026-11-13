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
  obtain ⟨loss, hs⟩ := h n hn
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hs s
  refine ⟨B, hB, fun m side radial p hp i j hij J z hz v => ?_⟩
  let A : PolarPoint →L[ℝ] ℝ := if radial then ContinuousLinearMap.fst ℝ ℝ ℝ
    else ContinuousLinearMap.snd ℝ ℝ ℝ
  have hp' := n04NegativeGeometry_referenceHalf_subset_component
    W.hT W.hS W.through03 W.field e (e.symm (.inl (m, side))) m side
    (e.apply_symm_apply _) hp
  let R := W.negativeChartMixedRegularity m side A
  let J₀ : SmoothDirections (sectorNeighborhood W.S b ε ε)
      (fun x => mixedDerivative i j (fun q =>
        if radial then
          (n04bActualNegativeChart W.hT W.hS W.through03 W.field
            (liftSectorParameter W.S W.C x) m side q).1
        else
          (n04bActualNegativeChart W.hT W.hS W.through03 W.field
            (liftSectorParameter W.S W.C x) m side q).2) p) :=
    ((R.parameter i j p hp').restrict (isOpen_sectorNeighborhood W.S b ε ε)
      (sectorNeighborhood_mono W.S hbW hεW hεW)).congrOn (fun x _ => by
        cases radial <;> rfl)
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
  obtain ⟨loss, hphys⟩ := hphysical n hn
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hphys s
  obtain ⟨C, hC, hscale⟩ := W.negativeChart_normalization_material e s
  obtain ⟨D, hD, hpack⟩ := coefficientEnvelope_pack (C * B) (C + B)
  refine ⟨D, hD, fun m side radial q hq i j hij J z hz v => ?_⟩
  let K := W.A e
  let k := e.symm (.inl (m, side))
  let U := sectorNeighborhood W.S b ε ε
  let Ω : Set PolarPoint := Ioo (W.C.left m) (W.C.right m) ×ˢ univ
  let A : PolarPoint →L[ℝ] ℝ := if radial then ContinuousLinearMap.fst ℝ ℝ ℝ
    else ContinuousLinearMap.snd ℝ ℝ ℝ
  let f : Parameter W.S → PolarPoint → ℝ := fun x p =>
    A (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C x) m side p)
  let c : ℝ := K.physicalRight k - K.physicalLeft k
  let d : ℝ := if radial then K.right k - K.left k else 1
  let h : PolarPoint → ℝ := if radial then (fun _ => K.left k) else Prod.snd
  let p := physicalUnitPoint K k q
  have hU : IsOpen U := isOpen_sectorNeighborhood W.S b ε ε
  have hsub := sectorNeighborhood_mono W.S hb hε hε
  have hPart := n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field e
  have hunit := n04NegativeGeometry_affine_unitPoint
    (K.physicalLeft k) (K.physicalRight k) (hPart.referenceBounds k).1
  have hmap : MapsTo (physicalUnitPoint K k) unitStrip Ω := fun y hy =>
    n04NegativeGeometry_referenceHalf_subset_component W.hT W.hS W.through03 W.field
      e k m side (e.apply_symm_apply _) (hunit.2.1 hy)
  let RF := W.negativeChartMixedRegularity m side A
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
      (fun y : PolarPoint => d⁻¹ * (f x (K.physicalLeft k + c * y.1, y.2) - h y)) := by
    funext y
    cases radial <;> simp only [atom, Bool.false_eq_true, ↓reduceIte,
      d, h, f, A, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      physicalUnitPoint, hchart x, c, inv_one, one_mul, div_eq_mul_inv] <;> ring
  let JK := J.congrOn (fun x _ =>
    congrArg (fun g : PolarPoint → ℝ => mixedDerivative i j g q) (hatom x))
  have hjet := n04NegativeChart_coordinatePullback_positiveJet hU
    (K.physicalLeft k) c d h hh hf hmap i j hq JP JK hn hz v
  let JP' : SmoothDirections U (fun x => mixedDerivative i j (fun y =>
      if radial then
        (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x) m side y).1
      else
        (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x) m side y).2) p) :=
    JP.congrOn (fun x _ => by
      apply congrArg (fun g : PolarPoint → ℝ => mixedDerivative i j g p)
      funext y
      cases radial <;> rfl)
  have hraw := hbound m side radial p (hunit.2.1 hq) i j hij JP' z hz v
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
  calc
    |J.D n z v| = |c ^ i / d| * |JP.D n z v| := by rw [hjet, abs_mul]
    _ ≤ (C * E ^ C) * (B * E ^ B * H * V) :=
      mul_le_mul hcoef hraw (abs_nonneg _) (mul_nonneg hC.le
        (Real.rpow_nonneg (zero_le_one.trans hE) C))
    _ = ((C * B) * E ^ (C + B)) * H * V := by
      rw [Real.rpow_add (zero_lt_one.trans_le hE)]
      ring
    _ ≤ D * E ^ D * H * V :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hpack E hE) hH) hV

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeChart_normalized_positive_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeChart_normalized_positive_bounds
