import ContinuousFlexibility.Radial.R07OutgoingFamily
import ContinuousFlexibility.Radial.SelectedBoundaryMargin

/-!
# Continue the selected natural solution to the actual matching join

The outgoing representative retained by the controlled construction is
globally smooth. The existing radial continuation theorem therefore gives
a natural solution at the earlier join with the same selected entrance
value and derivative. ODE uniqueness shows that the whole original open
tail, and not only its entrance state, is preserved.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

/-- Equal entrance Cauchy data identify two smooth natural solutions on
the original open tail, although one may start at an earlier entrance. -/
theorem radialNaturalTail_eqOn_of_cauchy {D : ReferenceData}
    (hD : RadialProfileGeometry D) {right : Bool} {j : ℕ} {p e : ℝ}
    (hp : p ∈ radialCore D) (he : e ∈ radialCore D)
    (hpe : if right then p < e else e < p)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hU : RadialNaturalTail D right j p u) (hV : RadialNaturalTail D right j e v)
    (hvalue : u e = v e) (hderiv : deriv u e = deriv v e) :
    EqOn u v (radialTailInterval D right e) := by
  intro r hr
  have hrCore : r ∈ radialCore D := by
    cases right
    · exact ⟨hr.1, hr.2.trans he.2⟩
    · exact ⟨he.1.trans hr.1, hr.2⟩
  have her : if right then e < r else r < e := by
    cases right
    · exact hr.2
    · exact hr.1
  have hUeq : ∀ x ∈ uIcc e r, radialJacobi ((j : ℝ) ^ 2) D.w u x = 0 := by
    intro x hx
    apply hU.2.1.2 x
    cases right
    · rw [uIcc_of_ge her.le] at hx
      exact ⟨hr.1.trans_le hx.1, hx.2.trans_lt hpe⟩
    · rw [uIcc_of_le her.le] at hx
      exact ⟨hpe.trans_le hx.1, hx.2.trans_lt hr.2⟩
  have hVeq := radialNaturalTail_zero_uIcc hD he hrCore her hv hV
  have hEq := radialHomogeneous_eqOn_Icc hD (lt_min he.1 hrCore.1)
    (min_le_max e r) (max_lt he.2 hrCore.2) (left_mem_uIcc : e ∈ uIcc e r)
    hu hv hUeq hVeq hvalue hderiv
  exact hEq right_mem_uIcc

/-- Inward continuation retains the complete old tail and its entrance
jet, and satisfies the actual homogeneous equation on the closed join. -/
theorem exists_radialNaturalTail_continuation_preserving_tail {D : ReferenceData}
    (hD : RadialProfileGeometry D) {right : Bool} {j : ℕ} {p e : ℝ}
    (hp : p ∈ radialCore D) (he : e ∈ radialCore D)
    (hpe : if right then p < e else e < p)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hV : RadialNaturalTail D right j e v) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ RadialNaturalTail D right j p u ∧
      u e = v e ∧ deriv u e = deriv v e ∧
      EqOn u v (radialTailInterval D right e) ∧
      ∀ r ∈ uIcc p e, radialJacobi ((j : ℝ) ^ 2) D.w u r = 0 := by
  obtain ⟨u, hu, hU, hvalue, hderiv⟩ :=
    exists_radialNaturalTail_continuation_with_cauchy hD hp he hpe hv hV
  exact ⟨u, hu, hU, hvalue, hderiv,
    radialNaturalTail_eqOn_of_cauchy hD hp he hpe hu hv hU hV hvalue hderiv,
    radialNaturalTail_zero_uIcc hD hp he hpe hu hU⟩

/-- The actual selected outgoing solution can be represented naturally
at joinInner. Every selected entrance state, at any normalization scale,
and the selected angle remain exactly unchanged. -/
theorem selected_natural_continue_to_join {S : SelectedTailData}
    (hS : IsSelectedTail S) (right : Bool) {n j : ℕ}
    (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hv : ContDiff ℝ ∞ (S.outgoing right j)) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      RadialNaturalTail (S.family S.sigma) right j (S.joinInner right n) v ∧
      v (S.entry right n) = S.outgoing right j (S.entry right n) ∧
      deriv v (S.entry right n) = deriv (S.outgoing right j) (S.entry right n) ∧
      EqOn v (S.outgoing right j)
        (radialTailInterval (S.family S.sigma) right (S.entry right n)) ∧
      (∀ r ∈ uIcc (S.joinInner right n) (S.entry right n),
        radialJacobi ((j : ℝ) ^ 2) (S.family S.sigma).w v r = 0) ∧
      (∀ scale : ℝ, radialState (S.family S.sigma) j (S.entry right n) scale v =
        radialState (S.family S.sigma) j (S.entry right n) scale (S.outgoing right j)) ∧
      S.c₀ * exp (-(n : ℝ) ^ 2) ≤
        radialAngleSine
          (radialState (S.family S.sigma) j (S.entry right n)
            ((S.family S.sigma).w (S.joinInner right n)) (S.incoming right j))
          (radialState (S.family S.sigma) j (S.entry right n)
            ((S.family S.sigma).w (S.joinInner right n)) v) := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have h := hS.2.2.2.2.2 right n j hj heven hband
  rcases h with ⟨_, he, hp, _, horder, _, _, _, _, _, _, hnatural, hangle⟩
  have hpe : if right then S.joinInner right n < S.entry right n
      else S.entry right n < S.joinInner right n := by
    cases right
    · exact horder.1
    · exact horder.2
  obtain ⟨v, hsmooth, hN, hvalue, hderiv, hEq, hODE⟩ :=
    exists_radialNaturalTail_continuation_preserving_tail hreal.geometry hp he hpe hv hnatural
  have hstate (scale : ℝ) :
      radialState (S.family S.sigma) j (S.entry right n) scale v =
        radialState (S.family S.sigma) j (S.entry right n) scale (S.outgoing right j) := by
    simp only [radialState, hvalue, hderiv]
  refine ⟨v, hsmooth, hN, hvalue, hderiv, hEq, hODE, hstate, ?_⟩
  rw [hstate]
  exact hangle

end ContinuousFlexibility.Radial
