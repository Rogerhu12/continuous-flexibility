import ContinuousFlexibility.Analysis.RootTravelOppositeCoordinates
import ContinuousFlexibility.Analysis.N04bActualAtlasGerms

/-!
# Opposite-root identities for the original stored negative fields

Both indices are the original typed atlas indices of one negative
component. The formulas use its actual shared travel chart on the whole
open component, so they also apply where a moving half crosses the fixed
reference cut. No half domain or material sample is replaced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

def n04bOppositeRootHeightFactor (T ξ : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (n04bOppositeRootRadial T ξ) / Real.sqrt ξ)

def n04bOppositeRootJacobianFactor (T ξ : ℝ) : ℝ :=
  Real.sqrt (ξ / n04bOppositeRootRadial T ξ)

theorem n04b_contDiffAt_oppositeRootFactors {T ξ : ℝ}
    (hξ : 0 < ξ) (htravel : n04bRootTravel ξ < T) :
    ContDiffAt ℝ ∞ (n04bOppositeRootHeightFactor T) ξ ∧
      ContDiffAt ℝ ∞ (n04bOppositeRootJacobianFactor T) ξ := by
  have hG := n04b_contDiffAt_oppositeRootRadial hξ htravel
  have hGpos := n04bOppositeRootRadial_pos htravel
  have hi : ContDiffAt ℝ ∞ (fun x : ℝ => x) ξ := contDiffAt_id
  have hsq := hi.sqrt hξ.ne'
  have hsqG := hG.sqrt hGpos.ne'
  exact ⟨(hsqG.div hsq (Real.sqrt_pos.mpr hξ).ne').sqrt
      (div_pos (Real.sqrt_pos.mpr hGpos) (Real.sqrt_pos.mpr hξ)).ne',
    (hi.div hG hGpos.ne').sqrt (div_pos hξ hGpos).ne'⟩

section Actual

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e : ℕ ≃ N04PieceIndex D)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1)

include hT hS hN hfield hz hs

/-- Actual values and both differential rows at the same physical point.
The opposite index is certified by the original enumeration. -/
theorem n04bActualTypedAtlas_negative_opposite_fields_at
    (k k' m : ℕ) (side : Bool)
    (hk : e k = .inl (m, side)) (hk' : e k' = .inl (m, !side))
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    0 < (K.chart z k p).1 ∧ 0 < (K.chart z k' p).1 ∧
      K.chart z k p = n04bOppositeRootMap (C.travel m) (K.chart z k' p) ∧
      K.height z k p = K.height z k' p *
        n04bOppositeRootHeightFactor (C.travel m) (K.chart z k' p).1 ∧
      |planeJacobian (K.chart z k) p| = |planeJacobian (K.chart z k') p| *
        n04bOppositeRootJacobianFactor (C.travel m) (K.chart z k' p).1 ∧
      ∀ v : PolarPoint, fderiv ℝ (K.chart z k) p v =
        (-n04bOppositeRootJacobianFactor (C.travel m) (K.chart z k' p).1 *
            (fderiv ℝ (K.chart z k') p v).1,
          (fderiv ℝ (K.chart z k') p v).2) := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let F : PolarPoint → PolarPoint := n04bActualTravelChart S C L z m
  have hg := n04bActualTypedAtlas_negative_component_germs
    hT hS hN hfield e hz hs k m side hk hp
  have hg' := n04bActualTypedAtlas_negative_component_germs
    hT hS hN hfield e hz hs k' m (!side) hk' hp
  have hFk : K.chart z k p = n04bRootPhysicalChart F (C.travel m) side p :=
    hg.1.eq_of_nhds
  have hFk' : K.chart z k' p = n04bRootPhysicalChart F (C.travel m) (!side) p :=
    hg'.1.eq_of_nhds
  have hHk := hg.2.eq_of_nhds
  have hHk' := hg'.2.eq_of_nhds
  have hJk : planeJacobian (K.chart z k) p =
      planeJacobian (n04bRootPhysicalChart F (C.travel m) side) p := by
    simp only [planeJacobian, hg.1.fderiv_eq (𝕜 := ℝ)]
  have hJk' : planeJacobian (K.chart z k') p =
      planeJacobian (n04bRootPhysicalChart F (C.travel m) (!side)) p := by
    simp only [planeJacobian, hg'.1.fderiv_eq (𝕜 := ℝ)]
  have ht : (F p).1 ∈ Ioo (0 : ℝ) (C.travel m) :=
    ((n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m).mapsTo hp).1
  have hF : DifferentiableAt ℝ F p :=
    ((n04b_actualTravelChart_smooth hN hS hT hfield hz hs m).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hx : 0 < (n04bRootPhysicalChart F (C.travel m) side p).1 :=
    n04bRootPhysicalChart_fst_pos (n04b_travelOrientation_pos_of_fullStrip side ht)
  have hx' : 0 < (n04bRootPhysicalChart F (C.travel m) (!side) p).1 :=
    n04bRootPhysicalChart_fst_pos (n04b_travelOrientation_pos_of_fullStrip (!side) ht)
  have hchange := n04b_rootPhysicalChart_opposite (F := F) side (p := p) ht
  have hrad : (n04bRootPhysicalChart F (C.travel m) side p).1 =
      n04bOppositeRootRadial (C.travel m)
        (n04bRootPhysicalChart F (C.travel m) (!side) p).1 :=
    congrArg Prod.fst hchange
  have hcontrol : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hp.1.1, hp.1.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have ha := hfield.positive_a z hz hs p hpD
  have hv := n04b_actualCharacteristic_halfGap_pos hN hfield hz hs m hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFk]
    exact hx
  · rw [hFk']
    exact hx'
  · rw [hFk, hFk']
    exact hchange
  · rw [hHk, hHk', hFk']
    unfold n04bOppositeRootHeightFactor
    rw [← hrad]
    exact n04b_rootPhysicalHeight_opposite side ha hv ht
  · rw [hJk, hJk', hFk']
    unfold n04bOppositeRootJacobianFactor
    rw [← hrad]
    exact n04b_abs_planeJacobian_rootPhysicalChart_opposite side hF ht
  · intro v
    simp only [hg.1.fderiv_eq (𝕜 := ℝ), hg'.1.fderiv_eq (𝕜 := ℝ), hFk',
      n04bOppositeRootJacobianFactor, ← hrad, Real.sqrt_div' _ hx.le]
    exact n04b_fderiv_rootPhysicalChart_opposite side hF ht v

/-- Full open-component germs, including the actual artificial cut.
Each conversion factor depends only on the opposite stored radial field. -/
theorem n04bActualTypedAtlas_negative_opposite_germs
    (k k' m : ℕ) (side : Bool)
    (hk : e k = .inl (m, side)) (hk' : e k' = .inl (m, !side))
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    (K.chart z k =ᶠ[𝓝 p]
      fun x => n04bOppositeRootMap (C.travel m) (K.chart z k' x)) ∧
    (K.height z k =ᶠ[𝓝 p]
      fun x => K.height z k' x *
        n04bOppositeRootHeightFactor (C.travel m) (K.chart z k' x).1) ∧
    ((fun x => |planeJacobian (K.chart z k) x|) =ᶠ[𝓝 p]
      fun x => |planeJacobian (K.chart z k') x| *
        n04bOppositeRootJacobianFactor (C.travel m) (K.chart z k' x).1) := by
  dsimp only
  have hnear : ∀ᶠ q in 𝓝 p,
      q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have hall := hnear.mono (fun q hq =>
    n04bActualTypedAtlas_negative_opposite_fields_at hT hS hN hfield e hz hs
      k k' m side hk hk' hq)
  exact ⟨hall.mono (fun _ h => h.2.2.1),
    hall.mono (fun _ h => h.2.2.2.1), hall.mono (fun _ h => h.2.2.2.2.1)⟩

/-- First jets of the actual height and absolute Jacobian are the first
jets of the explicit opposite-field formulas; no new field is chosen. -/
theorem n04bActualTypedAtlas_negative_opposite_firstJets
    (k k' m : ℕ) (side : Bool)
    (hk : e k = .inl (m, side)) (hk' : e k' = .inl (m, !side))
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    fderiv ℝ (K.chart z k) p =
      fderiv ℝ (fun x => n04bOppositeRootMap (C.travel m) (K.chart z k' x)) p ∧
    fderiv ℝ (K.height z k) p =
      fderiv ℝ (fun x => K.height z k' x *
        n04bOppositeRootHeightFactor (C.travel m) (K.chart z k' x).1) p ∧
    fderiv ℝ (fun x => |planeJacobian (K.chart z k) x|) p =
      fderiv ℝ (fun x => |planeJacobian (K.chart z k') x| *
        n04bOppositeRootJacobianFactor (C.travel m) (K.chart z k' x).1) p := by
  have h := n04bActualTypedAtlas_negative_opposite_germs
    hT hS hN hfield e hz hs k k' m side hk hk' hp
  exact ⟨h.1.fderiv_eq (𝕜 := ℝ), h.2.1.fderiv_eq (𝕜 := ℝ),
    h.2.2.fderiv_eq (𝕜 := ℝ)⟩

/-- The ratio formulation uses genuine nonvanishing of the stored fields. -/
theorem n04bActualTypedAtlas_negative_opposite_ratios
    (k k' m : ℕ) (side : Bool)
    (hk : e k = .inl (m, side)) (hk' : e k' = .inl (m, !side))
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    K.height z k p / K.height z k' p =
        n04bOppositeRootHeightFactor (C.travel m) (K.chart z k' p).1 ∧
      |planeJacobian (K.chart z k) p| / |planeJacobian (K.chart z k') p| =
        n04bOppositeRootJacobianFactor (C.travel m) (K.chart z k' p).1 := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have h := n04bActualTypedAtlas_negative_opposite_fields_at
    hT hS hN hfield e hz hs k k' m side hk hk' hp
  have hg := n04bActualTypedAtlas_negative_component_germs
    hT hS hN hfield e hz hs k' m (!side) hk' hp
  have hr := n04b_actualRootPhysical_regular_at hN hS hT hfield hz hs m (!side) hp
  have hH : K.height z k' p ≠ 0 := by
    rw [hg.2.eq_of_nhds]
    exact hr.2.2.2.ne'
  have hJ : |planeJacobian (K.chart z k') p| ≠ 0 := by
    have he : planeJacobian (K.chart z k') p =
        planeJacobian (n04bRootPhysicalChart (n04bActualTravelChart S C L z m)
          (C.travel m) (!side)) p := by
      simp only [planeJacobian, hg.1.fderiv_eq (𝕜 := ℝ)]
    rw [he]
    exact abs_ne_zero.mpr hr.2.2.1
  constructor
  · apply (div_eq_iff₀ hH).mpr
    exact h.2.2.2.1.trans (mul_comm _ _)
  · apply (div_eq_iff₀ hJ).mpr
    exact h.2.2.2.2.1.trans (mul_comm _ _)

/-- Dimensionless formulas at the actual stored point. The scale is the
original component's cut radius, not a newly chosen width. -/
theorem n04bActualTypedAtlas_negative_opposite_normalized
    (k k' m : ℕ) (side : Bool)
    (hk : e k = .inl (m, side)) (hk' : e k' = .inl (m, !side))
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let ρ := n04bRootCutRadius (C.travel m)
    let u := (K.chart z k' p).1 / ρ
    let v := (K.chart z k p).1 / ρ
    0 < u ∧ 0 < v ∧ v ^ (3 / 2 : ℝ) + u ^ (3 / 2 : ℝ) = 2 ∧
      v = (2 - u ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ∧
      K.height z k p / K.height z k' p = (v / u) ^ (1 / 4 : ℝ) ∧
      |planeJacobian (K.chart z k) p| / |planeJacobian (K.chart z k') p| =
        Real.sqrt (u / v) := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let ρ := n04bRootCutRadius (C.travel m)
  let u := (K.chart z k' p).1 / ρ
  let v := (K.chart z k p).1 / ρ
  have htravel := n04b_actualTravel_positive hN hS hT hfield hz hs m
  have hρ : 0 < ρ := n04bRootCutRadius_pos htravel
  have h := n04bActualTypedAtlas_negative_opposite_fields_at
    hT hS hN hfield e hz hs k k' m side hk hk' hp
  have hr := n04bActualTypedAtlas_negative_opposite_ratios
    hT hS hN hfield e hz hs k k' m side hk hk' hp
  have hg := n04bActualTypedAtlas_negative_component_germs
    hT hS hN hfield e hz hs k m side hk hp
  have hg' := n04bActualTypedAtlas_negative_component_germs
    hT hS hN hfield e hz hs k' m (!side) hk' hp
  have ht := ((n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m).mapsTo hp).1
  have hrad : (K.chart z k p).1 =
      n04bOppositeRootRadial (C.travel m) (K.chart z k' p).1 :=
    congrArg Prod.fst h.2.2.1
  have hvu : v / u = (K.chart z k p).1 / (K.chart z k' p).1 := by
    change ((K.chart z k p).1 / ρ) / ((K.chart z k' p).1 / ρ) = _
    field_simp [hρ.ne', h.2.1.ne']
  have huv : u / v = (K.chart z k' p).1 / (K.chart z k p).1 := by
    change ((K.chart z k' p).1 / ρ) / ((K.chart z k p).1 / ρ) = _
    field_simp [hρ.ne', h.1.ne']
  refine ⟨div_pos h.2.1 hρ, div_pos h.1 hρ, ?_, ?_, ?_, ?_⟩
  · rw [hg.1.eq_of_nhds, hg'.1.eq_of_nhds]
    exact n04b_rootHalfCoordinate_normalized_sum htravel side ht
  · rw [hg.1.eq_of_nhds, hg'.1.eq_of_nhds]
    exact n04b_rootHalfCoordinate_normalized_opposite htravel side ht
  · rw [hr.1, n04bOppositeRootHeightFactor, ← hrad,
      n04b_nested_sqrt_ratio_eq_rpow h.1.le h.2.1.le, hvu]
  · rw [hr.2, n04bOppositeRootJacobianFactor, ← hrad, huv]

end Actual
end ContinuousFlexibility.Analysis
