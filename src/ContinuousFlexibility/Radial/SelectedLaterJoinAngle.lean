module

public import ContinuousFlexibility.Radial.R07IncomingJoin
public import ContinuousFlexibility.Radial.SelectedJoinAngle
public import ContinuousFlexibility.Radial.SelectedNaturalJoin

/-!
# The actual later selected angle at the matching join

A stronger geometric action threshold is fixed before the chain is
constructed. The realized profile's contrast and prescribed connector
width give the exponential transfer estimate for both actual solutions.
Continuing the natural solution inward preserves the selected entry jet;
the resulting lower angle bound is therefore at joinInner itself.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem r10a_actual_join_selected_angle {T : MorseChainData} {D : ReferenceData}
    (G : MorseChainGeometryWitness T) {σ K : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D K) (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2)
    {C c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1)
    (hsmall : R07JoinActionSmall T C (c₀ / 100))
    (right : Bool) (k : ℕ) {j : ℕ} (hj : 2 ≤ j)
    (hband : radialFrequencyBand T C (T.index + k + 1) j)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hodeU : ∀ r ∈ uIcc (r07PreviousCellJoin T right (T.index + k))
      (r07CellEntry T right (T.index + k + 1)), radialJacobi ((j : ℝ) ^ 2) D.w u r = 0)
    (hodeV : ∀ r ∈ uIcc (r07PreviousCellJoin T right (T.index + k))
      (r07CellEntry T right (T.index + k + 1)), radialJacobi ((j : ℝ) ^ 2) D.w v r = 0)
    (hsep : c₀ * exp (-((T.index + k + 1 : ℕ) : ℝ) ^ 2) ≤
      radialAngleSine
        (radialState D j (r07CellEntry T right (T.index + k + 1))
          (D.w (r07PreviousCellJoin T right (T.index + k))) u)
        (radialState D j (r07CellEntry T right (T.index + k + 1))
          (D.w (r07PreviousCellJoin T right (T.index + k))) v)) :
    let p := r07PreviousCellJoin T right (T.index + k)
    radialState D j p (D.w p) u ≠ (0, 0) ∧
      radialState D j p (D.w p) v ≠ (0, 0) ∧
      (c₀ * exp (-((T.index + k + 1 : ℕ) : ℝ) ^ 2)) / 2 ≤
        radialAngleSine (radialState D j p (D.w p) u) (radialState D j p (D.w p) v) := by
  let m := T.index + k
  let p := r07PreviousCellJoin T right m
  let e := r07CellEntry T right (m + 1)
  let contrast := max (D.w e / D.w p) (D.w p / D.w e)
  have hcontrast := r07_actual_join_contrast G hreal hσ right k
  have hI : uIcc p e = Icc (T.joinLeft right m) (T.joinRight right m) :=
    r07_preceding_join_interval G right k
  have hp : p ∈ Icc (T.joinLeft right m) (T.joinRight right m) := by
    rw [← hI]
    exact left_mem_uIcc
  have he : e ∈ Icc (T.joinLeft right m) (T.joinRight right m) := by
    rw [← hI]
    exact right_mem_uIcc
  have hm : T.index ≤ m := Nat.le_add_right _ _
  have hm1 : T.index ≤ m + 1 := hm.trans (Nat.le_succ m)
  have hpcut : (if right then T.rightX right m else T.leftX right m) ∈
      Icc (T.leftX right m) (T.rightX right m) := by
    have ho := (hreal.2.2.1 right m hm).2.1.le
    cases right
    · exact ⟨le_rfl, ho⟩
    · exact ⟨ho, le_rfl⟩
  have hecut : (if right then T.leftX right (m + 1) else T.rightX right (m + 1)) ∈
      Icc (T.leftX right (m + 1)) (T.rightX right (m + 1)) := by
    have ho := (hreal.2.2.1 right (m + 1) hm1).2.1.le
    cases right
    · exact ⟨ho, le_rfl⟩
    · exact ⟨le_rfl, ho⟩
  have hpCore : p ∈ radialCore D := hreal.radius_mem_core right m hm _ hpcut
  have heCore : e ∈ radialCore D := hreal.radius_mem_core right (m + 1) hm1 _ hecut
  have hleft : T.joinLeft right m ∈ uIcc p e := by
    rw [hI]
    exact left_mem_Icc.mpr (morseChainPhysicalJoin_order G right k).le
  have hr₀ : 0 < T.joinLeft right m :=
    hreal.geometry.1.trans ((ordConnected_Ioo.uIcc_subset hpCore heCore) hleft).1
  have hJ : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
    have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith only [hj', sq_nonneg ((j : ℝ) - 2)]
  have hcontrast₀ : 0 ≤ contrast := zero_le_one.trans hcontrast.1
  have hgeo := r07_geometry_join_action_le G right k (sq_nonneg (j : ℝ)) hcontrast₀ hr₀
  have hnum := hsmall (m + 1) j (by dsimp only [m]; omega) hband contrast
    ((1 / 100 : ℝ) * morseChainA T m ^ 12) hcontrast₀ hcontrast.2.1 (by positivity)
    (by simpa only [Nat.add_sub_cancel] using
      (le_refl ((1 / 100 : ℝ) * morseChainA T m ^ 12)))
  have haction : 2 * (j : ℝ) ^ 2 * contrast / T.joinLeft right m * |e - p| ≤
      (c₀ * exp (-((m + 1 : ℕ) : ℝ) ^ 2)) / 1200 := by
    rw [r07_preceding_join_length G right k]
    have h := (hgeo.trans_lt hnum).le
    convert h using 1 <;> ring
  have hmargin : c₀ * exp (-((m + 1 : ℕ) : ℝ) ^ 2) ≤ 1 :=
    (mul_le_of_le_one_right hc₀.le (exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))).trans hc₀1
  have hδ : 0 < c₀ * exp (-((m + 1 : ℕ) : ℝ) ^ 2) :=
    mul_pos hc₀ (exp_pos _)
  have herror : exp (2 * (j : ℝ) ^ 2 * contrast / T.joinLeft right m * |p - e|) - 1 ≤
      (c₀ * exp (-((m + 1 : ℕ) : ℝ) ^ 2)) / 16 := by
    rw [abs_sub_comm p e]
    have ha₀ : 0 ≤ 2 * (j : ℝ) ^ 2 * contrast / T.joinLeft right m * |e - p| := by
      positivity
    have ha₁ : |2 * (j : ℝ) ^ 2 * contrast / T.joinLeft right m * abs (e - p)| ≤ 1 := by
      rw [abs_of_nonneg ha₀]
      linarith only [haction, hmargin]
    have hexp := abs_exp_sub_one_le ha₁
    rw [abs_of_nonneg ha₀] at hexp
    have hb := (le_abs_self _).trans hexp
    linarith only [hb, haction, hδ]
  have hw : ContDiff ℝ ∞ D.w := hreal.geometry.2.2.1.1
  have hu' : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have hv' : ContDiff ℝ ∞ (deriv v) := (contDiff_infty_iff_deriv.mp hv).2
  exact joinState_selected_angle_lower hr₀ hJ (hcontrast.2.2 p left_mem_uIcc).1 hcontrast.1
    (fun r _ => ⟨hw.differentiable (by simp) r, hu.differentiable (by simp) r,
      hu'.differentiable (by simp) r⟩)
    (fun r _ => ⟨hw.differentiable (by simp) r, hv.differentiable (by simp) r,
      hv'.differentiable (by simp) r⟩)
    (fun r hr => hcontrast.2.2 r (by rwa [hI]))
    (fun r hr => hodeU r (by rwa [hI]))
    (fun r hr => hodeV r (by rwa [hI]))
    he hp hδ hsep herror

/-- The actual selected pair yields a natural representative at the
matching join with the later margin there. The selected outgoing tail
and its complete entrance jet are preserved. -/
theorem selected_later_natural_join_angle {S : SelectedTailData}
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1)
    (hsmall : R07JoinActionSmall S.chain S.Cstar (c₀ / 100))
    (right : Bool) {n j : ℕ} (hn : S.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hjoin : S.joinInner right n = r07PreviousCellJoin S.chain right (n - 1))
    (hu : ContDiff ℝ ∞ (S.incoming right j)) (hv : ContDiff ℝ ∞ (S.outgoing right j))
    (hsep : c₀ * exp (-(n : ℝ) ^ 2) ≤
      radialAngleSine
        (radialState (S.family S.sigma) j (S.entry right n)
          ((S.family S.sigma).w (S.joinInner right n)) (S.incoming right j))
        (radialState (S.family S.sigma) j (S.entry right n)
          ((S.family S.sigma).w (S.joinInner right n)) (S.outgoing right j))) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      RadialNaturalTail (S.family S.sigma) right j (S.joinInner right n) v ∧
      v (S.entry right n) = S.outgoing right j (S.entry right n) ∧
      deriv v (S.entry right n) = deriv (S.outgoing right j) (S.entry right n) ∧
      EqOn v (S.outgoing right j)
        (radialTailInterval (S.family S.sigma) right (S.entry right n)) ∧
      (∀ scale : ℝ, radialState (S.family S.sigma) j (S.entry right n) scale v =
        radialState (S.family S.sigma) j (S.entry right n) scale (S.outgoing right j)) ∧
      radialState (S.family S.sigma) j (S.joinInner right n)
        ((S.family S.sigma).w (S.joinInner right n)) (S.incoming right j) ≠ (0, 0) ∧
      radialState (S.family S.sigma) j (S.joinInner right n)
        ((S.family S.sigma).w (S.joinInner right n)) v ≠ (0, 0) ∧
      (c₀ * exp (-(n : ℝ) ^ 2)) / 2 ≤
        radialAngleSine
          (radialState (S.family S.sigma) j (S.joinInner right n)
            ((S.family S.sigma).w (S.joinInner right n)) (S.incoming right j))
          (radialState (S.family S.sigma) j (S.joinInner right n)
            ((S.family S.sigma).w (S.joinInner right n)) v) := by
  obtain ⟨v, hvs, hNv, hvalue, hderiv, hEq, hodeV, hstate, _⟩ :=
    selected_natural_continue_to_join hS right hj heven hband hv
  have hb := hS.2.2.2.2.2 right n j hj heven hband
  rcases hb with ⟨_, _, _, _, horder, heq, _, _, _, _, hODE, _, _⟩
  have hentry : S.entry right n = r07CellEntry S.chain right n := heq
  have hp : S.joinInner right n ∈ uIcc (S.cut right n) (S.entry right n) := by
    cases right
    · rw [uIcc_of_ge (horder.1.trans horder.2).le]
      exact ⟨horder.1.le, horder.2.le⟩
    · rw [uIcc_of_le (horder.1.trans horder.2).le]
      exact ⟨horder.1.le, horder.2.le⟩
  have hsub : uIcc (S.joinInner right n) (S.entry right n) ⊆
      uIcc (S.cut right n) (S.entry right n) := uIcc_subset_uIcc_right hp
  have hodeU : ∀ r ∈ uIcc (S.joinInner right n) (S.entry right n),
      radialJacobi ((j : ℝ) ^ 2) (S.family S.sigma).w (S.incoming right j) r = 0 :=
    fun r hr => hODE.2 r (hsub hr)
  have hsepV : c₀ * exp (-(n : ℝ) ^ 2) ≤
      radialAngleSine
        (radialState (S.family S.sigma) j (S.entry right n)
          ((S.family S.sigma).w (S.joinInner right n)) (S.incoming right j))
        (radialState (S.family S.sigma) j (S.entry right n)
          ((S.family S.sigma).w (S.joinInner right n)) v) := by
    rw [hstate]
    exact hsep
  let k := n - 1 - S.chain.index
  have hm : S.chain.index + k = n - 1 := by dsimp only [k]; omega
  have hn' : S.chain.index + k + 1 = n := by omega
  have hn'' : n - 1 + 1 = n := by omega
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hangle := r10a_actual_join_selected_angle G hreal hS.2.2.1
    hc₀ hc₀1 hsmall right k hj (by simpa only [hn'] using hband) hu hvs
    (by simpa only [hm, hn', hn'', hentry, hjoin] using hodeU)
    (by simpa only [hm, hn', hn'', hentry, hjoin] using hodeV)
    (by simpa only [hm, hn', hn'', hentry, hjoin] using hsepV)
  refine ⟨v, hvs, hNv, hvalue, hderiv, hEq, hstate, ?_⟩
  simpa only [hm, hn', hn'', hentry, hjoin] using hangle

end ContinuousFlexibility.Radial
