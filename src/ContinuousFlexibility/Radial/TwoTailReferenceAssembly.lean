import ContinuousFlexibility.Radial.SmoothTailCoordinate
import ContinuousFlexibility.Radial.ReferenceCoordinateBounds
import ContinuousFlexibility.Radial.ReferenceDilation

/-!
# Concrete two-tail accumulating-reference assembly

The profile and Jacobi field are supplied by the actual gluing.  This
module constructs all remaining reference data: the two endpoint scales,
pulled-back cells and localizers, positive cell labels and trace
scaffold.  The input tail identities are only required on the two open
pieces of the original annulus.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- An exact radius pullback on an open interval gives the ordinary
function germ in the rescaled radius. -/
theorem scaled_profile_germ_of_interval_identity
    {old new : ℝ → ℝ} {R F l h r : ℝ} (hR : 0 < R)
    (heq : ∀ x ∈ Ioo l h, new (R * x) = F * old x)
    (hr : r ∈ Ioo (R * l) (R * h)) :
    new =ᶠ[𝓝 r] fun x => F * old (R⁻¹ * x) := by
  filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
  have hx' : x / R ∈ Ioo l h := by
    constructor
    · apply (lt_div_iff₀ hR).mpr
      simpa only [mul_comm l R] using hx.1
    · apply (div_lt_iff₀ hR).mpr
      simpa only [mul_comm h R] using hx.2
  have hcancel : R * (x / R) = x := by field_simp [hR.ne']
  have hv := heq (x / R) hx'
  rw [hcancel] at hv
  simpa only [div_eq_mul_inv, mul_comm] using hv

private theorem scalar_bounds_of_sum_le {F c M : ℝ}
    (h : |F| + |F⁻¹| + |c| ≤ M) :
    |F| ≤ M ∧ F⁻¹ ≤ M ∧ |c| ≤ M := by
  have hF := abs_nonneg F
  have hi := abs_nonneg F⁻¹
  have hc := abs_nonneg c
  have hia := le_abs_self F⁻¹
  constructor
  · linarith
  constructor <;> linarith

/-- Construct the complete accumulating reference with the prescribed
new profile, field and independently rescaled endpoints. -/
theorem exists_accumulating_reference_of_two_tail_surgery_with_transport
    {D : ReferenceData} {W Phi : ℝ → ℝ} {A B HL HR c d : ℝ}
    (hD : IsAccumulatingProfile D)
    (hA : 0 < A) (hAB : A ≤ B) (hHL : 0 < HL) (hHR : 0 < HR)
    (hac : D.a < c) (hcd : c < d) (hdb : d < D.b)
    (hGeo : RadialProfileGeometry
      { D with a := A * D.a, b := B * D.b, w := W, phi := Phi })
    (hleft : ∀ r ∈ Ioo D.a c, W (A * r) = HL * A * D.w r)
    (hright : ∀ r ∈ Ioo d D.b, W (B * r) = HR * B * D.w r) :
    ∃ E : ReferenceData,
      E.a = A * D.a ∧ E.b = B * D.b ∧ E.w = W ∧ E.phi = Phi ∧
      IsAccumulatingProfile E ∧
      ∃ e : ℝ ≃o ℝ, E.cells = (fun m => e ⁻¹' D.cells m) ∧
        E.cellIndex = (fun m => max (D.cellIndex m) 1) ∧
        E.localizer = (fun m r => D.localizer m (e r)) ∧
        (∀ r, r ≤ c → e.symm r = A * r) ∧
        (∀ r, d ≤ r → e.symm r = B * r) := by
  rcases hD with ⟨C, hDb⟩
  have hc : 0 < c := hDb.1.1.trans hac
  have hB : 0 < B := hA.trans_le hAB
  obtain ⟨e, he, heInv, heDeriv, heLeft, heRight, heLeftInv, heRightInv,
    L, hL, hforward, hbackward⟩ := exists_smooth_tail_coordinate hA hAB hc hcd
  have ha : e.symm D.a = A * D.a := heLeft D.a hac.le
  have hb : e.symm D.b = B * D.b := heRight D.b hdb.le
  let D₁ : ReferenceData := positiveIndexReference D
  let E : ReferenceData := replaceReferenceProfile (coordinateReference D₁ e) W Phi
  have hEa : E.a = A * D.a := ha
  have hEb : E.b = B * D.b := hb
  have hNew : RadialProfileGeometry E := by
    simpa only [RadialProfileGeometry, EndpointFlat, radialCore, E,
      replaceReferenceProfile, coordinateReference, D₁, positiveIndexReference, floorReferenceIndex, ha, hb] using hGeo
  let K : Set ℝ := Icc (A * c) (B * d)
  have hK : IsCompact K := isCompact_Icc
  have hKcore : K ⊆ radialCore (coordinateReference D₁ e) := by
    intro r hr
    change e.symm D.a < r ∧ r < e.symm D.b
    rw [ha, hb]
    exact ⟨(mul_lt_mul_of_pos_left hac hA).trans_le hr.1,
      hr.2.trans_lt (mul_lt_mul_of_pos_left hdb hB)⟩
  let TL : ℝ := |HL * A| + |(HL * A)⁻¹| + |A⁻¹|
  let TR : ℝ := |HR * B| + |(HR * B)⁻¹| + |B⁻¹|
  let M : ℝ := 1 + TL + TR
  have hTL : 0 ≤ TL := by dsimp only [TL]; positivity
  have hTR : 0 ≤ TR := by dsimp only [TR]; positivity
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hTLM : TL ≤ M := by dsimp only [M]; linarith
  have hTRM : TR ≤ M := by dsimp only [M]; linarith
  have hleftBounds : |HL * A| ≤ M ∧ (HL * A)⁻¹ ≤ M ∧ |A⁻¹| ≤ M :=
    scalar_bounds_of_sum_le hTLM
  have hrightBounds : |HR * B| ≤ M ∧ (HR * B)⁻¹ ≤ M ∧ |B⁻¹| ≤ M :=
    scalar_bounds_of_sum_le hTRM
  have hTail : ∀ r ∈ radialCore (coordinateReference D₁ e), r ∉ K →
      ∃ F q : ℝ, 0 < F ∧ |F| ≤ M ∧ F⁻¹ ≤ M ∧ |q| ≤ M ∧
        e r = q * r ∧ W =ᶠ[𝓝 r] fun x => F * D₁.w (q * x) := by
    intro r hr hKr
    have hr' : A * D.a < r ∧ r < B * D.b := by
      change e.symm D.a < r ∧ r < e.symm D.b at hr
      simpa only [ha, hb] using hr
    have hout : r < A * c ∨ B * d < r := by
      by_cases hl : r < A * c
      · exact Or.inl hl
      · exact Or.inr (lt_of_not_ge fun hh => hKr ⟨le_of_not_gt hl, hh⟩)
    rcases hout with hl | hr
    · refine ⟨HL * A, A⁻¹, mul_pos hHL hA,
        hleftBounds.1, hleftBounds.2.1, hleftBounds.2.2, ?_, ?_⟩
      · simpa only [div_eq_mul_inv, mul_comm] using heLeftInv r hl.le
      · exact scaled_profile_germ_of_interval_identity hA hleft ⟨hr'.1, hl⟩
    · refine ⟨HR * B, B⁻¹, mul_pos hHR hB,
        hrightBounds.1, hrightBounds.2.1, hrightBounds.2.2, ?_, ?_⟩
      · simpa only [div_eq_mul_inv, mul_comm] using heRightInv r hr.le
      · exact scaled_profile_germ_of_interval_identity hB hright ⟨hr, hr'.2⟩
  have hAccum : IsAccumulatingProfile E :=
    isAccumulatingProfile_coordinateSurgery e
      (isAccumulatingProfile_positiveIndexReference ⟨C, hDb⟩)
      (positiveIndexReference_index_pos D) he hL hforward hbackward
      hNew hK hKcore hM hTail
  exact ⟨E, hEa, hEb, rfl, rfl, hAccum, e, rfl, rfl, rfl, heLeft, heRight⟩

/-- The existing cell interface forgets only the localizer identity. -/
theorem exists_accumulating_reference_of_two_tail_surgery_with_cells
    {D : ReferenceData} {W Phi : ℝ → ℝ} {A B HL HR c d : ℝ}
    (hD : IsAccumulatingProfile D)
    (hA : 0 < A) (hAB : A ≤ B) (hHL : 0 < HL) (hHR : 0 < HR)
    (hac : D.a < c) (hcd : c < d) (hdb : d < D.b)
    (hGeo : RadialProfileGeometry
      { D with a := A * D.a, b := B * D.b, w := W, phi := Phi })
    (hleft : ∀ r ∈ Ioo D.a c, W (A * r) = HL * A * D.w r)
    (hright : ∀ r ∈ Ioo d D.b, W (B * r) = HR * B * D.w r) :
    ∃ E : ReferenceData,
      E.a = A * D.a ∧ E.b = B * D.b ∧ E.w = W ∧ E.phi = Phi ∧
      IsAccumulatingProfile E ∧
      ∃ e : ℝ ≃o ℝ, E.cells = (fun m => e ⁻¹' D.cells m) ∧
        E.cellIndex = (fun m => max (D.cellIndex m) 1) ∧
        (∀ r, r ≤ c → e.symm r = A * r) ∧
        (∀ r, d ≤ r → e.symm r = B * r) := by
  obtain ⟨E, ha, hb, hw, hPhi, hE, e, hc, hi, _, hL, hR⟩ :=
    exists_accumulating_reference_of_two_tail_surgery_with_transport hD hA hAB hHL hHR
      hac hcd hdb hGeo hleft hright
  exact ⟨E, ha, hb, hw, hPhi, hE, e, hc, hi, hL, hR⟩

/-- The original surgery API follows by forgetting the retained coordinate. -/
theorem exists_accumulating_reference_of_two_tail_surgery
    {D : ReferenceData} {W Phi : ℝ → ℝ} {A B HL HR c d : ℝ}
    (hD : IsAccumulatingProfile D)
    (hA : 0 < A) (hAB : A ≤ B) (hHL : 0 < HL) (hHR : 0 < HR)
    (hac : D.a < c) (hcd : c < d) (hdb : d < D.b)
    (hGeo : RadialProfileGeometry
      { D with a := A * D.a, b := B * D.b, w := W, phi := Phi })
    (hleft : ∀ r ∈ Ioo D.a c, W (A * r) = HL * A * D.w r)
    (hright : ∀ r ∈ Ioo d D.b, W (B * r) = HR * B * D.w r) :
    ∃ E : ReferenceData,
      E.a = A * D.a ∧ E.b = B * D.b ∧ E.w = W ∧ E.phi = Phi ∧
      IsAccumulatingProfile E := by
  obtain ⟨E, ha, hb, hw, hPhi, hE, _⟩ :=
    exists_accumulating_reference_of_two_tail_surgery_with_cells hD hA hAB hHL hHR
      hac hcd hdb hGeo hleft hright
  exact ⟨E, ha, hb, hw, hPhi, hE⟩

/-- Open tail equality is enough for the full closed negative component:
its endpoints are interior points of the tail on which the identity
holds, so their derivative germs are transported as well. -/
theorem negativeRadialComponent_travel_of_tail_identity
    {D E : ReferenceData} {R H l h α β : ℝ}
    (hR : 0 < R) (hH : 0 < H) (hneg : NegativeRadialComponent D l h)
    (ha : E.a < R * l) (hb : R * h < E.b)
    (hD : ContDiff ℝ ∞ D.w) (hE : ContDiff ℝ ∞ E.w)
    (hInterval : Icc l h ⊆ Ioo α β)
    (heq : ∀ r ∈ Ioo α β, E.w (R * r) = H * R * D.w r) :
    NegativeRadialComponent E (R * l) (R * h) ∧
      radialTravel E (R * l) (R * h) = radialTravel D l h := by
  apply negativeRadialComponent_travel_of_scaled_germs hR hH hneg ha hb
    (hD.differentiable (by simp)) (hE.differentiable (by simp))
  intro r hr
  filter_upwards [isOpen_Ioo.mem_nhds (hInterval hr)] with x hx
  exact heq x hx

end ContinuousFlexibility.Radial
