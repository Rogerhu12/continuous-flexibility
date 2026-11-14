module

public import ContinuousFlexibility.Radial.SelectedSideTransport
public import ContinuousFlexibility.Radial.SelectedBoundaryRadiusScale
public import ContinuousFlexibility.Radial.R07DeepTailChange

/-!
# Normalized first-band incoming solutions on the final common geometry

The physical solution uses the same side radius and height as the retained
pair. Its growing cap, actual equation, unit join value, slope `1 / j`
and original selected entrance angle therefore refer to one geometry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem radialRadiusScale_power_eqOn {u : ℝ → ℝ} {κ a p ν : ℝ}
    (hκ : 0 < κ) (ha : 0 < a) (hp : 0 < p)
    (hu : EqOn u (fun r => r ^ ν / p ^ ν) (uIcc a p)) :
    EqOn (radialRadiusScale κ 1 u)
      (fun r => r ^ ν / (κ * p) ^ ν) (uIcc (κ * a) (κ * p)) := by
  intro r hr
  have hx : r / κ ∈ uIcc a p := (mem_uIcc_div_pos hκ).mpr hr
  have hxpos : 0 < r / κ := (lt_min ha hp).trans_le hx.1
  have he : κ * (r / κ) = r := by field_simp [hκ.ne'] <;> ring
  have h (x : ℝ) (hxp : 0 < x) (hxu : u x = x ^ ν / p ^ ν) :
      radialRadiusScale κ 1 u (κ * x) = (κ * x) ^ ν / (κ * p) ^ ν := by
    rw [radialRadiusScale_apply_mul hκ.ne', one_mul, hxu,
      mul_rpow hκ.le hxp.le, mul_rpow hκ.le hp.le]
    field_simp [(rpow_pos_of_pos hκ ν).ne', (rpow_pos_of_pos hp ν).ne']
    <;> ring
  simpa only [he] using h (r / κ) hxpos (hu hx)

structure SeedPhysicalFirstIncoming {S : SelectedTailData} {K : SeedCentralCutoff}
    {q length : ℝ} (P : SeedRetainedPair S K q length) (D : ReferenceData)
    (right : Bool) (j : ℕ) where
  solution : ℝ → ℝ
  oldAmplitude : ℝ
  oldAmplitude_pos : 0 < oldAmplitude
  smooth : ContDiff ℝ ∞ solution
  join_value : solution (P.sideRadius right * S.joinInner right S.chain.index) = 1
  join_deriv : deriv solution (P.sideRadius right * S.joinInner right S.chain.index) =
    r07OutwardSign right * (j : ℝ) / (P.sideRadius right * S.joinInner right S.chain.index)
  join_slope : standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2)
    (P.sideRadius right * S.joinInner right S.chain.index) solution = 1 / (j : ℝ)
  cone_power : EqOn solution
    (fun r => r ^ (if right then (j : ℝ) else -(j : ℝ)) /
      (P.sideRadius right * S.joinInner right S.chain.index) ^
        (if right then (j : ℝ) else -(j : ℝ)))
    (uIcc (P.sideRadius right * (P.side right).inner)
      (P.sideRadius right * S.joinInner right S.chain.index))
  equation : ∀ r ∈ uIcc (P.sideRadius right * (P.side right).inner)
      (P.sideRadius right * S.entry right S.chain.index),
    radialJacobi ((j : ℝ) ^ 2) D.w solution r = 0
  incoming_germ : ∀ r, (if right then S.joinInner right S.chain.index ≤ r
      else r ≤ S.joinInner right S.chain.index) →
    solution =ᶠ[𝓝 (P.sideRadius right * r)]
      radialRadiusScale (P.sideRadius right) oldAmplitude (S.incoming right j)
  entry_angle : S.c₀ * exp (-(S.chain.index : ℝ) ^ 2) ≤
    radialAngleSine
      (radialState D j (P.sideRadius right * S.entry right S.chain.index)
        (D.w (P.sideRadius right * S.joinInner right S.chain.index)) solution)
      (radialState D j (P.sideRadius right * S.entry right S.chain.index)
        (D.w (P.sideRadius right * S.joinInner right S.chain.index))
        (radialRadiusScale (P.sideRadius right) 1 (S.outgoing right j)))

theorem SeedRetainedPair.exists_physical_firstIncoming {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
    (right : Bool) {j : ℕ} (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index j)
    (hu : ContDiff ℝ ∞ (S.incoming right j))
    (hcone : ∃ C : ℝ, 0 < C ∧ ∀ r ∈ uIcc (S.cut right S.chain.index)
        (S.joinInner right S.chain.index),
      (S.family S.sigma).w =ᶠ[𝓝 r] (fun t => C * t)) :
    Nonempty (SeedPhysicalFirstIncoming P D right j) := by
  let κ := P.sideRadius right
  let β := P.sideHeight right
  let a := (P.side right).inner
  let c := S.cut right S.chain.index
  let p := S.joinInner right S.chain.index
  let e := S.entry right S.chain.index
  let ν : ℝ := if right then (j : ℝ) else -(j : ℝ)
  have hκ : 0 < κ := P.sideRadius_pos right
  have hβ : 0 < β := P.sideHeight_pos right
  have ha : 0 < a := (P.side right).inner_pos
  have hD₀ : RadialProfileGeometry (S.family S.sigma) :=
    MorseChainRealization.geometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hm := hS.2.2.2.2.2 right S.chain.index j hj heven hband
  rcases hm with ⟨hc, he, hp, _, horder, _, _, _, _, _, _, _, hangle⟩
  have hppos : 0 < p := hD₀.1.trans hp.1
  have hepos : 0 < e := hD₀.1.trans he.1
  have hap : if right then a < p else p < a := by
    cases right
    · exact horder.2.trans (P.side false).inner_order
    · exact (P.side true).inner_order.trans horder.1
  have hae : if right then a < e else e < a := by
    cases right
    · exact horder.1.trans hap
    · exact hap.trans horder.2
  have hapne : a ≠ p := by
    cases right
    · exact ne_of_gt hap
    · exact ne_of_lt hap
  obtain ⟨u, α, hα, hus, hu₀, hupower, huret, hueq⟩ :=
    (P.side right).exists_normalized_growingIncoming hS hj heven hband hu hcone
  let U := radialRadiusScale κ 1 u
  have hUs : ContDiff ℝ ∞ U := contDiff_radialRadiusScale hus κ 1
  have hU₀ : U (κ * p) = 1 := by
    change radialRadiusScale κ 1 u (κ * p) = 1
    rw [radialRadiusScale_apply_mul hκ.ne', one_mul]
    exact hu₀
  have hUpower : EqOn U (fun r => r ^ ν / (κ * p) ^ ν)
      (uIcc (κ * a) (κ * p)) := radialRadiusScale_power_eqOn hκ ha hppos hupower
  have hne : κ * a ≠ κ * p := fun h => hapne (mul_left_cancel₀ hκ.ne' h)
  have hdu : deriv U (κ * p) = ν / (κ * p) := by
    rw [radialConePower_deriv_of_eqOn (mul_pos hκ ha) (mul_pos hκ hppos)
      hne hUs hUpower right_mem_uIcc, hU₀, mul_one]
  have hν : ν = r07OutwardSign right * (j : ℝ) := by
    cases right <;> simp only [ν, r07OutwardSign, Bool.false_eq_true, ite_false, ite_true,
      one_mul, neg_one_mul]
  have hε : r07OutwardSign right = 1 ∨ r07OutwardSign right = -1 := by
    cases right
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hjpos : (0 : ℝ) < j := by
    have hh : (2 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hslope : standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2)
      (κ * p) U = 1 / (j : ℝ) := by
    apply standInBoundarySlope_of_cone_derivative hε hjpos.ne' (mul_pos hκ hppos).ne'
      (by rw [hU₀]; exact one_ne_zero)
    rw [hdu, hU₀, mul_one, hν]
  refine ⟨{
    solution := U
    oldAmplitude := α
    oldAmplitude_pos := hα
    smooth := hUs
    join_value := hU₀
    join_deriv := by simpa only [hν] using hdu
    join_slope := hslope
    cone_power := hUpower
    equation := ?_
    incoming_germ := ?_
    entry_angle := ?_ }⟩
  · intro r hr
    have hx : r / κ ∈ uIcc a e := (mem_uIcc_div_pos hκ).mpr hr
    have hxpos : 0 < r / κ := (lt_min ha hepos).trans_le hx.1
    have hi : if right then a ≤ r / κ else r / κ ≤ a := by
      cases right
      · rw [uIcc_of_ge hae.le] at hx
        exact hx.2
      · rw [uIcc_of_le hae.le] at hx
        exact hx.1
    have hwp := P.reference_side_profile_germ hw right hxpos hi
    have ht := radialJacobi_radiusScale_of_profile_germ (α := 1) hκ.ne' hwp (hueq (r / κ) hx)
    have heq : κ * (r / κ) = r := by field_simp [hκ.ne'] <;> ring
    simpa only [heq] using ht
  · intro r hr
    have ht := radialRadiusScale_germ (α := 1) hκ.ne' (huret r hr)
    have hf : radialRadiusScale κ 1 (fun t => α * S.incoming right j t) =
        radialRadiusScale κ α (S.incoming right j) := by
      funext t
      simp only [radialRadiusScale, one_mul]
    rw [hf] at ht
    exact ht
  · have hce : if right then c ≤ e else e ≤ c := by
      cases right <;> exact (horder.1.trans horder.2).le
    have hcp : if right then c ≤ p else p ≤ c := by
      cases right
      · exact horder.2.le
      · exact horder.1.le
    have hpe : if right then p ≤ e else e ≤ p := by
      cases right
      · exact horder.1.le
      · exact horder.2.le
    have hprofileE : D.w (κ * e) = (β * κ) * (S.family S.sigma).w e :=
      P.reference_side_old_value hw hS right he hce
    have hprofileP : D.w (κ * p) = (β * κ) * (S.family S.sigma).w p :=
      P.reference_side_old_value hw hS right hp hcp
    have heq := radialState_radiusScale_angle_of_scaled_germ
      (D := S.family S.sigma) (E := D) j (A := 1) (B := 1)
      (v := S.outgoing right j)
      (scale := (S.family S.sigma).w p) hκ.ne' hβ.ne' one_ne_zero one_ne_zero hα.ne'
      hprofileE (hu.differentiable (by simp) e) (huret e hpe)
    rw [← hprofileP] at heq
    exact hangle.trans_eq heq.symm

end ContinuousFlexibility.Radial
