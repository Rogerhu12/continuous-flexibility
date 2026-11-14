module

public import ContinuousFlexibility.Radial.SelectedNaturalJoin
public import ContinuousFlexibility.Radial.SelectedGrowingCone
public import ContinuousFlexibility.Radial.R07FiniteAngles
public import ContinuousFlexibility.Radial.R07LaterSelection
public import ContinuousFlexibility.Radial.RadialGreenBoundary

/-!
# A first-band margin fixed before constructing the cone heads

All choices in this file depend only on the original selected tail.
The preserved entrance angle gives a nonzero Wronskian, hence a positive
angle at the actual join. The incoming cone slope is exactly `1 / j`.
A positive minimum over the finite first band is therefore available
before choosing any retained-cone length or connected reference.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem radialWronskian_eq_on_uIcc {J p e : ℝ} {w u v : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hU : ∀ r ∈ uIcc p e, radialJacobi J w u r = 0)
    (hV : ∀ r ∈ uIcc p e, radialJacobi J w v r = 0) :
    radialWronskian w u v p = radialWronskian w u v e := by
  have hdu : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have hdv : ContDiff ℝ ∞ (deriv v) := (contDiff_infty_iff_deriv.mp hv).2
  have hd (r : ℝ) (hr : r ∈ uIcc p e) : HasDerivAt (radialWronskian w u v) 0 r := by
    have h := hasDerivAt_radialWronskian_general (J := J)
      (hw.differentiable (by simp) r) (hu.differentiable (by simp) r)
      (hdu.differentiable (by simp) r) (hv.differentiable (by simp) r)
      (hdv.differentiable (by simp) r)
    simpa only [hU r hr, hV r hr, mul_zero, sub_self] using h
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0)
    (f' := fun _ : ℝ => (0 : ℝ))
    (fun r hr => (hd r hr).hasDerivWithinAt) (fun _ _ => by simp)
    (convex_uIcc p e) left_mem_uIcc right_mem_uIcc
  have hz : radialWronskian w u v e - radialWronskian w u v p = 0 :=
    norm_eq_zero.mp (le_antisymm (by simpa only [zero_mul] using hb) (norm_nonneg _))
  exact (sub_eq_zero.mp hz).symm

theorem radialState_det_eq_wronskian (D : ReferenceData) (j : ℕ)
    (r scale : ℝ) (u v : ℝ → ℝ) :
    (radialState D j r scale u).1 * (radialState D j r scale v).2 -
      (radialState D j r scale u).2 * (radialState D j r scale v).1 =
      (r / (((j : ℝ) ^ 2) * scale)) * radialWronskian D.w u v r := by
  simp only [radialState, radialWronskian, div_eq_mul_inv, mul_inv_rev]
  ring

theorem radialState_angle_pos_at_join {D : ReferenceData} {j : ℕ} {p e scale : ℝ}
    (hw : ContDiff ℝ ∞ D.w) (hj : (j : ℝ) ≠ 0) (hp : p ≠ 0) (hs : scale ≠ 0)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hU : ∀ r ∈ uIcc p e, radialJacobi ((j : ℝ) ^ 2) D.w u r = 0)
    (hV : ∀ r ∈ uIcc p e, radialJacobi ((j : ℝ) ^ 2) D.w v r = 0)
    (hangle : 0 < radialAngleSine (radialState D j e scale u) (radialState D j e scale v)) :
    0 < radialAngleSine (radialState D j p scale u) (radialState D j p scale v) := by
  have hdet :
      (radialState D j e scale u).1 * (radialState D j e scale v).2 -
        (radialState D j e scale u).2 * (radialState D j e scale v).1 ≠ 0 := by
    intro hz
    have ha : radialAngleSine (radialState D j e scale u) (radialState D j e scale v) = 0 := by
      simp only [radialAngleSine, hz, abs_zero, zero_div]
    exact (ne_of_gt hangle) ha
  have hWe : radialWronskian D.w u v e ≠ 0 := by
    intro hz
    apply hdet
    rw [radialState_det_eq_wronskian, hz, mul_zero]
  have hWp : radialWronskian D.w u v p ≠ 0 := by
    rw [radialWronskian_eq_on_uIcc hw hu hv hU hV]
    exact hWe
  apply radialAngleSine_pos_of_det_ne
  rw [radialState_det_eq_wronskian]
  exact mul_ne_zero (div_ne_zero hp (mul_ne_zero (pow_ne_zero 2 hj) hs)) hWp

/-- Exact invariance of the complete physical state under the common
positive radius/height dilation and solution amplitude one. -/
theorem selectedBoundaryState_radiusScale_one {D E : ReferenceData}
    {κ β p ε : ℝ} {j : ℕ} (hκ : κ ≠ 0) (hβ : β ≠ 0)
    (hj : (j : ℝ) ≠ 0) (hp : p ≠ 0) (hw : D.w p ≠ 0)
    (hprofile : E.w (κ * p) = (β * κ) * D.w p) (v : ℝ → ℝ) :
    selectedBoundaryState E j ε (κ * p) (radialRadiusScale κ 1 v) =
      selectedBoundaryState D j ε p v := by
  apply Prod.ext
  · simp only [selectedBoundaryState, outerFluxState, radialRadiusScale_apply_mul hκ, one_mul]
  · change ε * E.w (κ * p) * deriv (radialRadiusScale κ 1 v) (κ * p) /
        standInBoundaryScale ((j : ℝ) ^ 2) (E.w (κ * p)) (κ * p) =
      ε * D.w p * deriv v p / standInBoundaryScale ((j : ℝ) ^ 2) (D.w p) p
    rw [hprofile, deriv_radialRadiusScale_apply_mul hκ]
    unfold standInBoundaryScale
    field_simp [hκ, hβ, hj, hp, hw] <;> ring

def SelectedFirstNaturalData (S : SelectedTailData) (right : Bool) (j : ℕ)
    (v : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ v ∧
    RadialNaturalTail (S.family S.sigma) right j (S.joinInner right S.chain.index) v ∧
    EqOn v (S.outgoing right j)
      (radialTailInterval (S.family S.sigma) right (S.entry right S.chain.index)) ∧
    v (S.entry right S.chain.index) = S.outgoing right j (S.entry right S.chain.index) ∧
    deriv v (S.entry right S.chain.index) = deriv (S.outgoing right j) (S.entry right S.chain.index)

def selectedFirstBoundaryMargin (S : SelectedTailData) (right : Bool) (j : ℕ)
    (v : ℝ → ℝ) : ℝ :=
  let AB := outerUnitState (selectedBoundaryState (S.family S.sigma) j
    (r07OutwardSign right) (S.joinInner right S.chain.index) v)
  |AB.1 / (j : ℝ) - AB.2|

theorem exists_selected_first_natural_margin {S : SelectedTailData}
    (hS : IsSelectedTail S) (right : Bool) {j : ℕ} (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index j)
    (hu : ContDiff ℝ ∞ (S.incoming right j)) (hv : ContDiff ℝ ∞ (S.outgoing right j))
    (hcone : ∃ C : ℝ, 0 < C ∧ ∀ r ∈ uIcc (S.cut right S.chain.index)
        (S.joinInner right S.chain.index),
      (S.family S.sigma).w =ᶠ[nhds r] fun t => C * t) :
    ∃ v : ℝ → ℝ, SelectedFirstNaturalData S right j v ∧
      0 < selectedFirstBoundaryMargin S right j v := by
  let D := S.family S.sigma
  let c := S.cut right S.chain.index
  let p := S.joinInner right S.chain.index
  let e := S.entry right S.chain.index
  let u := S.incoming right j
  let ν : ℝ := if right then (j : ℝ) else -(j : ℝ)
  have hD : RadialProfileGeometry D :=
    MorseChainRealization.geometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
  obtain ⟨v, hvs, hNv, hvalue, hderiv, hEq, hODEv, _, hsep⟩ :=
    selected_natural_continue_to_join hS right hj heven hband hv
  have hd := hS.2.2.2.2.2 right S.chain.index j hj heven hband
  rcases hd with ⟨hc, he, hp, hwp, horder, _, hinit, _, _, _, hODE, _, _⟩
  have hinit' : u c = 1 ∧ deriv u c = ν / c := by
    have hi := hinit
    simp only [if_pos rfl, ite_true] at hi
    exact hi.2
  have hpFull : p ∈ uIcc c e := by
    cases right
    · rw [uIcc_of_ge (horder.1.trans horder.2).le]
      exact ⟨horder.1.le, horder.2.le⟩
    · rw [uIcc_of_le (horder.1.trans horder.2).le]
      exact ⟨horder.1.le, horder.2.le⟩
  have hconeSub : uIcc c p ⊆ uIcc c e :=
    ordConnected_uIcc.uIcc_subset left_mem_uIcc hpFull
  have hjoinSub : uIcc p e ⊆ uIcc c e :=
    ordConnected_uIcc.uIcc_subset hpFull right_mem_uIcc
  have hODEu : ∀ r ∈ uIcc p e, radialJacobi ((j : ℝ) ^ 2) D.w u r = 0 :=
    fun r hr => hODE.2 r (hjoinSub hr)
  have hν : ν ^ 2 = (j : ℝ) ^ 2 := by cases right <;> simp [ν]
  obtain ⟨C, _, hcone⟩ := hcone
  have hpower := radialConeIncoming_eqOn_power hD hc hp hcone hu
    (fun r hr => hODE.2 r (hconeSub hr)) hinit'.1 hinit'.2 hν
  have hcp : c ≠ p := by
    cases right
    · exact ne_of_gt horder.2
    · exact ne_of_lt horder.1
  have hcpos : 0 < c := hD.1.trans hc.1
  have hppos : 0 < p := hD.1.trans hp.1
  have hup : 0 < u p := by
    have hvaluep : u p = p ^ ν / c ^ ν := hpower right_mem_uIcc
    rw [hvaluep]
    exact div_pos (rpow_pos_of_pos hppos ν) (rpow_pos_of_pos hcpos ν)
  have hdu := radialConePower_deriv_of_eqOn hcpos hppos hcp hu hpower right_mem_uIcc
  have hjn : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hε : r07OutwardSign right = 1 ∨ r07OutwardSign right = -1 := by
    cases right
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hslope : standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2) p u = 1 / (j : ℝ) := by
    apply standInBoundarySlope_of_cone_derivative hε hjn hppos.ne' hup.ne'
    rw [hdu]
    cases right <;> simp only [ν, r07OutwardSign, Bool.false_eq_true, ite_false, ite_true] <;> ring
  have hangle := radialState_angle_pos_at_join hD.2.2.1.1 hjn hppos.ne' hwp.ne'
    hu hvs hODEu hODEv ((mul_pos hS.2.1 (exp_pos _)).trans_le hsep)
  have hangle' : 0 < radialAngleSine (radialState D j p (D.w p) v)
      (radialState D j p (D.w p) u) := by
    rw [radialAngleSine_comm]
    exact hangle
  have hmargin := (selectedBoundaryState_matching_margin D hjn hppos.ne' hwp.ne'
    hε hup.ne' hangle' le_rfl).2
  rw [hslope] at hmargin
  refine ⟨v, ⟨hvs, hNv, hEq, hvalue, hderiv⟩, ?_⟩
  have hpos := (div_pos hangle' (by norm_num : (0 : ℝ) < 4)).trans_le hmargin
  simpa only [selectedFirstBoundaryMargin, div_eq_mul_inv, one_mul] using hpos

/-- This margin is chosen on the original `S`, before any retained pair,
cone length, head length or final connected reference is an input. -/
theorem exists_selected_first_uniform_margin {S : SelectedTailData}
    (hS : IsSelectedTail S)
    (hregular : ∀ right j, 2 ≤ j → Even j →
      radialFrequencyBand S.chain S.Cstar S.chain.index j →
      ContDiff ℝ ∞ (S.incoming right j) ∧ ContDiff ℝ ∞ (S.outgoing right j))
    (hcone : ∀ right, ∃ C : ℝ, 0 < C ∧ ∀ r ∈ uIcc (S.cut right S.chain.index)
        (S.joinInner right S.chain.index),
      (S.family S.sigma).w =ᶠ[nhds r] fun t => C * t) :
    ∃ V : Bool → R07FirstFrequency S.chain S.Cstar → ℝ → ℝ,
      ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 48 ∧
        ∀ right f, SelectedFirstNaturalData S right f.1 (V right f) ∧
          2 * η ≤ selectedFirstBoundaryMargin S right f.1 (V right f) := by
  classical
  have H (q : Bool × R07FirstFrequency S.chain S.Cstar) :
      ∃ v : ℝ → ℝ, SelectedFirstNaturalData S q.1 q.2.1 v ∧
        0 < selectedFirstBoundaryMargin S q.1 q.2.1 v := by
    have hr := hregular q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
    exact exists_selected_first_natural_margin hS q.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
      hr.1 hr.2 (hcone q.1)
  choose V hV using H
  obtain ⟨η, hη, hηsmall, hηbound⟩ := r07_exists_finite_angle_tolerance Finset.univ
    (fun q : Bool × R07FirstFrequency S.chain S.Cstar =>
      selectedFirstBoundaryMargin S q.1 q.2.1 (V q)) (fun q _ => (hV q).2)
  exact ⟨fun right f => V (right, f), η, hη, hηsmall,
    fun right f => ⟨(hV (right, f)).1, hηbound (right, f) (Finset.mem_univ _)⟩⟩

end ContinuousFlexibility.Radial
