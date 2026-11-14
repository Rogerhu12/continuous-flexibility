module

public import ContinuousFlexibility.Radial.SelectedLaterRetained
public import ContinuousFlexibility.Radial.ConnectedSelectedNaturalTransport
public import ContinuousFlexibility.Radial.SelectedBoundaryMargin

/-!
# Actual transport of the later incoming interval in one connected reference

The single radius and height dilation supplied by the same R08 witness
covers every later canonical matching interval. The cut, join and entry
are retained by proved geometry. The actual target profile has the required
germ throughout that closed interval, so the incoming equation, endpoint
jets, normalization, selected entry angle and natural tail all transport.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem preimage_div_uIcc_of_pos {κ : ℝ} (hκ : 0 < κ) (c e : ℝ) :
    (fun t : ℝ => t / κ) ⁻¹' uIcc c e = uIcc (κ * c) (κ * e) := by
  rcases le_total c e with h | h
  · rw [uIcc_of_le h, uIcc_of_le (mul_le_mul_of_nonneg_left h hκ.le)]
    ext t
    change (c ≤ t / κ ∧ t / κ ≤ e) ↔ (κ * c ≤ t ∧ t ≤ κ * e)
    rw [le_div_iff₀ hκ, div_le_iff₀ hκ]
    simp only [mul_comm]
  · rw [uIcc_of_ge h, uIcc_of_ge (mul_le_mul_of_nonneg_left h hκ.le)]
    ext t
    change (e ≤ t / κ ∧ t / κ ≤ c) ↔ (κ * e ≤ t ∧ t ≤ κ * c)
    rw [le_div_iff₀ hκ, div_le_iff₀ hκ]
    simp only [mul_comm]

/-- Closed incoming intervals may be transported using a profile identity
on a larger open set. This keeps the actual equation at both endpoints. -/
theorem radialHomogeneousOn_reference_scaled_uIcc {D E : ReferenceData}
    {κ β c e : ℝ} {I : Set ℝ} (hκ : 0 < κ) (hI : IsOpen I)
    (hsub : uIcc c e ⊆ I)
    (hprofile : ∀ r ∈ I, E.w (κ * r) = (β * κ) * D.w r)
    {j : ℕ} {u : ℝ → ℝ} (hu : RadialHomogeneousOn D j (uIcc c e) u) (α : ℝ) :
    RadialHomogeneousOn E j (uIcc (κ * c) (κ * e)) (radialRadiusScale κ α u) := by
  have H : RadialHomogeneousOn E j ((fun t : ℝ => t / κ) ⁻¹' uIcc c e)
      (radialRadiusScale κ α u) := by
    refine ⟨contDiffOn_radialRadiusScale hu.1 κ α, ?_⟩
    intro t ht
    have hcancel : κ * (t / κ) = t := by field_simp [hκ.ne']
    have h := radialJacobi_reference_radiusScale hκ.ne' hI (hsub ht) hprofile
      ((j : ℝ) ^ 2) α u
    rw [hcancel, hu.2 (t / κ) ht, mul_zero] at h
    exact h
  rwa [preimage_div_uIcc_of_pos hκ c e] at H

/-- All later bands use one dilation from the same connected geometry.
The only canonical formulas supplied by the actual constructor concern
entry and cut; the selected order itself places joinInner in the span. -/
theorem ConnectedReferenceGeometry.selected_later_transport
    (Γ : ConnectedReferenceGeometry) (hΓ : Γ.Realizes)
    (G : MorseChainGeometryWitness Γ.selected.chain)
    (hentry : Γ.selected.entry = r07CellEntry Γ.selected.chain)
    (hcut : ∀ right n, Γ.selected.chain.index < n →
      Γ.selected.cut right n = r07PreviousCellCut Γ.selected.chain right (n - 1))
    (right : Bool) :
    let S := Γ.selected
    let D := S.family S.sigma
    let E := Γ.reference
    ∃ κ β : ℝ, 0 < κ ∧ 0 < β ∧
      ∀ n j, S.chain.index < n → 2 ≤ j → Even j →
        radialFrequencyBand S.chain S.Cstar n j →
        let c := S.cut right n
        let p := S.joinInner right n
        let e := S.entry right n
        let U := radialRadiusScale κ 1 (S.incoming right j)
        let V := radialRadiusScale κ 1 (S.outgoing right j)
        (∀ r ∈ uIcc c e, κ * r ∈ radialCore E ∧
          E.w (κ * r) = (β * κ) * D.w r ∧
          deriv E.w (κ * r) = β * deriv D.w r) ∧
        κ * p ∈ radialCore E ∧
        0 < standInBoundaryScale ((j : ℝ) ^ 2) (E.w (κ * p)) (κ * p) ∧
        ContDiffAt ℝ ∞ U (κ * c) ∧ ContDiffAt ℝ ∞ U (κ * e) ∧
        RadialHomogeneousOn E j (uIcc (κ * c) (κ * e)) U ∧
        U (κ * c) = 0 ∧ U (κ * p) = 1 ∧
        (if right then 0 < deriv U (κ * c) else deriv U (κ * c) < 0) ∧
        RadialNaturalTail E right j (κ * e) V ∧
        S.c₀ * exp (-(n : ℝ) ^ 2) ≤
          radialAngleSine (radialState E j (κ * e) (E.w (κ * p)) U)
            (radialState E j (κ * e) (E.w (κ * p)) V) := by
  let S := Γ.selected
  let D := S.family S.sigma
  let E := Γ.reference
  rcases hΓ with ⟨hS, hacc, _, _, hpatch, _, htails, _, _, _⟩
  have hgeomE : RadialProfileGeometry E := hacc.choose_spec.1
  have hlh : Γ.centralLeft < Γ.centralRight :=
    hpatch.2.1.trans (central_turning_radii_pos_ordered.2.trans hpatch.2.2.1)
  have hcentral : (if right then Γ.centralRight else Γ.centralLeft) ∈ radialCore E := by
    cases right
    · exact ⟨hpatch.1, hlh.trans hpatch.2.2.2.1⟩
    · exact ⟨hpatch.1.trans hlh, hpatch.2.2.2.1⟩
  obtain ⟨κ, β, α, hκ, hβ, _, hend0, htail, _⟩ := htails right
  have hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a) := by
    cases right <;> exact hend0
  let I := radialTailInterval D right (S.entry right S.chain.index)
  have hopen : IsOpen I := by cases right <;> exact isOpen_Ioo
  have hprofile : ∀ r ∈ I, E.w (κ * r) = (β * κ) * D.w r :=
    fun r hr => (htail r hr).2.1
  have hmapcore (r : ℝ) (hr : r ∈ I) : κ * r ∈ radialCore E := by
    have hm := (htail r hr).1
    cases right
    · exact ⟨hm.1, hm.2.trans hcentral.2⟩
    · exact ⟨hcentral.1.trans hm.1, hm.2⟩
  refine ⟨κ, β, hκ, hβ, ?_⟩
  intro n j hn hj heven hband
  let c := S.cut right n
  let p := S.joinInner right n
  let e := S.entry right n
  obtain ⟨hp, hsub⟩ := selected_later_span_retained hS G hentry right
    hn hj heven hband (hcut right n hn)
  have hdata (r : ℝ) (hr : r ∈ uIcc c e) :
      κ * r ∈ radialCore E ∧ E.w (κ * r) = (β * κ) * D.w r ∧
        deriv E.w (κ * r) = β * deriv D.w r := by
    have hg := referenceProfile_radiusScale_eventuallyEq hκ.ne' hopen (hsub hr) hprofile
    have hd := hg.deriv_eq
    rw [deriv_radialRadiusScale_apply_mul hκ.ne'] at hd
    have hβκ : (β * κ) / κ = β := by field_simp [hκ.ne']
    exact ⟨hmapcore r (hsub hr), hprofile r (hsub hr), by simpa only [hβκ] using hd⟩
  have hbandData := hS.2.2.2.2.2 right n j hj heven hband
  rcases hbandData with
    ⟨_, he, _, _, _, _, hinit, _, hcs, hes, hode, hnatural, hangle⟩
  have hnormalized : S.incoming right j c = 0 ∧ S.incoming right j p = 1 ∧
      (if right then 0 < deriv (S.incoming right j) c
        else deriv (S.incoming right j) c < 0) := by
    simpa only [if_neg hn.ne'] using hinit
  have hEentry : κ * e ∈ radialCore E := (hdata e right_mem_uIcc).1
  have heRet : e ∈ I := hsub right_mem_uIcc
  have htailProfile : ∀ r ∈ radialTailInterval D right e,
      E.w (κ * r) = (β * κ) * D.w r := by
    intro r hr
    apply hprofile
    cases right
    · exact ⟨hr.1, hr.2.trans heRet.2⟩
    · exact ⟨heRet.1.trans hr.1, hr.2⟩
  refine ⟨hdata, (hdata p hp).1, ?_,
    contDiffAt_radialRadiusScale hκ.ne' hcs 1,
    contDiffAt_radialRadiusScale hκ.ne' hes 1,
    radialHomogeneousOn_reference_scaled_uIcc hκ hopen hsub hprofile hode 1,
    ?_, ?_, ?_,
    radialNaturalTail_reference_scaled hκ hβ one_ne_zero right he hEentry hend
      htailProfile hnatural, ?_⟩
  · have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    exact standInBoundaryScale_pos (sq_pos_of_pos hjpos)
      (hgeomE.2.2.2.2.1 _ (hdata p hp).1)
      (hgeomE.1.trans (hdata p hp).1.1)
  · simpa only [radialRadiusScale_apply_mul hκ.ne', one_mul] using hnormalized.1
  · simpa only [radialRadiusScale_apply_mul hκ.ne', one_mul] using hnormalized.2.1
  · rw [deriv_radialRadiusScale_apply_mul hκ.ne', one_div]
    cases right
    · exact mul_neg_of_pos_of_neg (inv_pos.mpr hκ) hnormalized.2.2
    · exact mul_pos (inv_pos.mpr hκ) hnormalized.2.2
  · have ha := radialState_radiusScale_angle (D := D) (E := E) j
      (κ := κ) (β := β) (α := 1) (γ := 1) (r := e) (scale := D.w p)
      hκ.ne' hβ.ne' one_ne_zero one_ne_zero (hdata e right_mem_uIcc).2.1
      (S.incoming right j) (S.outgoing right j)
    rw [← (hdata p hp).2.1] at ha
    exact hangle.trans_eq ha.symm

end ContinuousFlexibility.Radial
