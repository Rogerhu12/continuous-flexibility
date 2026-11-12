import ContinuousFlexibility.Analysis.N05OpticalLipschitz
import ContinuousFlexibility.Analysis.N05ReferenceNegativeDensity

/-!
# Optical control of the actual negative Jacobian and density

The two physical orientations use the same optical lower bound. Reflection
handles the right root, with the genuine interval integral unchanged.
The analytic input is a Lipschitz bound for the actual profile radicand;
neither a chart derivative bound nor an inverse root slope is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory

set_option backward.isDefEq.respectTransparency false

private theorem n05_optical_radicand_le_radius_right
    {f : ℝ → ℝ} {a b ξ : ℝ} {A : ℝ≥0} (hab : a ≤ b) (hA : 1 ≤ (A : ℝ))
    (hf : LipschitzOnWith A f (Icc a b))
    (hzero : f b = 0) (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x) (hξ : 0 ≤ ξ)
    (htime : (∫ x in a..b, Real.sqrt (f x)) = (2 / 3 : ℝ) * ξ * Real.sqrt ξ) :
    f a ≤ 4 * (A : ℝ) * ξ := by
  have hmem (x : ℝ) (hx : x ∈ Icc (-b) (-a)) : -x ∈ Icc a b := by
    constructor <;> linarith only [hx.1, hx.2]
  have hf' : LipschitzOnWith A (fun x => f (-x)) (Icc (-b) (-a)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_neg_neg] using hf.dist_le_mul (-x) (hmem x hx) (-y) (hmem y hy)
  have ht : (∫ x in -b..-a, Real.sqrt (f (-x))) =
      (2 / 3 : ℝ) * ξ * Real.sqrt ξ := by
    rw [intervalIntegral.integral_comp_neg]
    simpa only [neg_neg] using htime
  simpa only [neg_neg] using
    n05_optical_radicand_le_radius (neg_le_neg hab) hA hf'
      (by simpa only [neg_neg] using hzero)
      (fun x hx => hnonneg (-x) (hmem x hx)) hξ ht

/-- One analytic Lipschitz constant bounds the true Jacobian squared and
the source/output density on either actual negative half. The constant is
for `-w'/(r*w)` on the physical interval, independently of `K.cell`. -/
theorem n05_cut_reference_density_le_of_optical_lipschitz
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {A : ℝ≥0} (hA : 1 ≤ (A : ℝ))
    (hLip : LipschitzOnWith A (fun r => -deriv D.w r / (r * D.w r))
      (Icc (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
        (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1))))
    {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K
      (if right then (K.cutPair m).2 else (K.cutPair m).1)) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    let z := (C.referenceState, 0)
    |planeJacobian (K.chart z i) x| ^ 2 ≤ 4 * (A : ℝ) ∧
      |planeJacobian (K.chart z i) x| / K.height z i x ^ 2 ≤
        4 * (A : ℝ) * D.w x.1 := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  let F : ℝ → ℝ := fun r => -deriv D.w r / (r * D.w r)
  let ξ := (K.chart (C.referenceState, 0) i x).1
  let q := deriv (fun r => (K.chart (C.referenceState, 0) i (r, x.2)).1) x.1
  have h01 := h.1.1.1
  rcases h.2.2.2.2 with ⟨_, _, _, _, _, _, _, hcharts, _, _, _, hcuts, _⟩
  obtain ⟨hnegL, hnegR, hleft, hright, _, _, hzeroL, hzeroR, _⟩ := hcuts m
  have hi : K.positive i = false := by cases right <;> assumption
  have hi0 : K.left i = 0 := by cases right <;> assumption
  have hr : x.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i) :=
    ⟨hx.1.1.le, hx.1.2.le⟩
  have hξ : 0 < ξ := by
    have hp := (hcharts (C.referenceState, 0) (n05_referenceState_mem h01.2.1)
      (n05_referenceState_sector h01.2.2.1) i).1 x hx
    simpa only [hi0] using hp.1.1
  have hnonneg (t : ℝ) (ht : t ∈ Icc (K.physicalLeft i) (K.physicalRight i)) :
      0 ≤ F t := by
    have hd := (n05_negative_reference_density_closed hT hS h hi ht x.2).2.2.1
    change _ = F t at hd
    rw [← hd]
    exact mul_nonneg (n05_cut_reference_closed_radius_nonneg h m right ht x.2)
      (sq_nonneg _)
  have ht := (n05_cut_reference_angle_and_time hT hS h m right hr x.2).2
  have hroots := h01.2.2.2.1.2.1 m
  have hbound : F x.1 ≤ 4 * (A : ℝ) * ξ := by
    cases right with
    | false =>
      have hz : F (K.physicalLeft (K.cutPair m).1) = 0 := by
        dsimp only [F]
        rw [hleft, hroots.1, neg_zero, zero_div]
      have htime : (∫ r in K.physicalLeft (K.cutPair m).1..x.1, Real.sqrt (F r)) =
          (2 / 3 : ℝ) * ξ * Real.sqrt ξ := by
        change n05TricomiTime ξ = 1 *
          (opticalTravel D.w (K.physicalLeft (K.cutPair m).1) x.1 -
            opticalTravel D.w (K.physicalLeft (K.cutPair m).1) (C.left m)) at ht
        rw [← hleft] at ht
        simpa only [n05TricomiTime, opticalTravel, opticalSpeed,
          intervalIntegral.integral_same, sub_zero, one_mul] using ht.symm
      exact n05_optical_radicand_le_radius hx.1.1.le hA
        (hLip.mono (Icc_subset_Icc le_rfl hx.1.2.le)) hz
        (fun r hr' => hnonneg r ⟨hr'.1, hr'.2.trans hx.1.2.le⟩) hξ.le htime
    | true =>
      have hz : F (K.physicalRight (K.cutPair m).2) = 0 := by
        dsimp only [F]
        rw [hright, hroots.2.1, neg_zero, zero_div]
      have hg : ContinuousOn (opticalSpeed D.w)
          (Icc (K.physicalLeft (K.cutPair m).2) (K.physicalRight (K.cutPair m).2)) :=
        Real.continuous_sqrt.comp_continuousOn hLip.continuousOn
      have hL := (hg.mono (Icc_subset_Icc le_rfl hx.1.2.le)).intervalIntegrable_of_Icc hx.1.1.le
      have hR := (hg.mono (Icc_subset_Icc hx.1.1.le le_rfl)).intervalIntegrable_of_Icc hx.1.2.le
      have hadd := intervalIntegral.integral_add_adjacent_intervals hL hR
      have htime : (∫ r in x.1..K.physicalRight (K.cutPair m).2, Real.sqrt (F r)) =
          (2 / 3 : ℝ) * ξ * Real.sqrt ξ := by
        change n05TricomiTime ξ = (-1) *
          (opticalTravel D.w (K.physicalLeft (K.cutPair m).2) x.1 -
            opticalTravel D.w (K.physicalLeft (K.cutPair m).2) (C.right m)) at ht
        rw [← hright] at ht
        change opticalTravel D.w (K.physicalLeft (K.cutPair m).2) x.1 +
          opticalTravel D.w x.1 (K.physicalRight (K.cutPair m).2) =
          opticalTravel D.w (K.physicalLeft (K.cutPair m).2)
            (K.physicalRight (K.cutPair m).2) at hadd
        change opticalTravel D.w x.1 (K.physicalRight (K.cutPair m).2) = _
        dsimp only [n05TricomiTime] at ht
        linarith only [ht, hadd]
      exact n05_optical_radicand_le_radius_right hx.1.2.le hA
        (hLip.mono (Icc_subset_Icc hx.1.1.le le_rfl)) hz
        (fun r hr' => hnonneg r ⟨hx.1.1.le.trans hr'.1, hr'.2⟩) hξ.le htime
  have hd := n05_negative_reference_density_closed hT hS h hi hr x.2
  have hmul : ξ * |q| ^ 2 ≤ ξ * (4 * (A : ℝ)) := calc
    _ = F x.1 := hd.2.2.1
    _ ≤ 4 * (A : ℝ) * ξ := hbound
    _ = _ := mul_comm _ _
  have hq := (mul_le_mul_left hξ).mp hmul
  have hw : 0 ≤ D.w x.1 := by
    by_contra hw
    have hbad := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (sq_nonneg (K.height (C.referenceState, 0) i x)) (le_of_lt (lt_of_not_ge hw)))
      (abs_nonneg q)
    rw [hd.2.1] at hbad
    norm_num at hbad
  constructor
  · simpa only [hd.1] using hq
  · calc
      _ = D.w x.1 * |q| ^ 2 := hd.2.2.2
      _ ≤ D.w x.1 * (4 * (A : ℝ)) := mul_le_mul_of_nonneg_left hq hw
      _ = _ := mul_comm _ _

end ContinuousFlexibility.Statements
