import ContinuousFlexibility.Radial.R07ConeSolution
import ContinuousFlexibility.Radial.SeedOrientedGluing

/-!
# Exact continuation of the selected growing mode along the retained cone

The incoming solution is continued inward by its explicit growing power.
A splice strictly between the old cut and join lies in a region where
finite-interval uniqueness identifies both functions on a full germ.
Consequently the old join and entrance states are preserved exactly.
No propagation from the central model through a positive connector is
needed for this compactly supported terminal lift.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem radialConeIncoming_eqOn_power {D : ReferenceData}
    (hD : RadialProfileGeometry D) {c p scale ν J : ℝ}
    (hc : c ∈ radialCore D) (hp : p ∈ radialCore D)
    (hcone : ∀ r ∈ uIcc c p, D.w =ᶠ[𝓝 r] (fun t => scale * t))
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hODE : ∀ r ∈ uIcc c p, radialJacobi J D.w u r = 0)
    (hu₀ : u c = 1) (hu₁ : deriv u c = ν / c) (hν : ν ^ 2 = J) :
    EqOn u (fun r => r ^ ν / c ^ ν) (uIcc c p) := by
  have hcpos : 0 < c := hD.1.trans hc.1
  have hlpos : 0 < min c p := lt_min hcpos (hD.1.trans hp.1)
  obtain ⟨R, hR, hRp, hRg⟩ := exists_r07_smooth_radius_germ hlpos (min_le_max c p)
  let v : ℝ → ℝ := fun r => R r ^ ν / c ^ ν
  have hv : ContDiff ℝ ∞ v := (hR.rpow_const_of_ne (fun r => (hRp r).ne')).div_const _
  have hvg (r : ℝ) (hr : r ∈ uIcc c p) :
      v =ᶠ[𝓝 r] (fun t => t ^ ν / c ^ ν) :=
    (hRg r hr).fun_comp (fun t => t ^ ν / c ^ ν)
  have hv₀ : v c = 1 := by
    rw [(hvg c left_mem_uIcc).eq_of_nhds]
    exact div_self (rpow_pos_of_pos hcpos ν).ne'
  have hv₁ : deriv v c = ν / c := by
    rw [(r07_hasDerivAt_normalized_power hcpos (hvg c left_mem_uIcc)).deriv,
      hv₀, mul_one]
  have hEq : EqOn u v (uIcc c p) := radialHomogeneous_eqOn_Icc hD
    (lt_min hc.1 hp.1) (min_le_max c p) (max_lt hc.2 hp.2) left_mem_uIcc hu hv hODE
    (fun r hr => r07_radialJacobi_cone_power (hlpos.trans_le hr.1) hν
      (hcone r hr) (hvg r hr)) (hu₀.trans hv₀.symm) (hu₁.trans hv₁.symm)
  exact fun r hr => (hEq hr).trans (hvg r hr).eq_of_nhds

/-- Equality with a cone power on a nontrivial closed interval also fixes
the ordinary derivative at both finite endpoints. -/
theorem radialConePower_deriv_of_eqOn {a b c ν : ℝ} {u : ℝ → ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (hu : ContDiff ℝ ∞ u)
    (heq : EqOn u (fun r => r ^ ν / c ^ ν) (uIcc a b))
    {r : ℝ} (hr : r ∈ uIcc a b) : deriv u r = ν / r * u r := by
  have hrd : HasDerivAt (fun t : ℝ => t ^ ν / c ^ ν)
      (ν / r * (r ^ ν / c ^ ν)) r :=
    r07_hasDerivAt_normalized_power ((lt_min ha hb).trans_le hr.1) Filter.EventuallyEq.rfl
  have hdiff := uniqueDiffOn_Icc (min_lt_max.mpr hab) r hr
  have hd := derivWithin_congr heq (heq hr)
  rw [(hu.differentiable (by simp) r).derivWithin hdiff,
    hrd.differentiableAt.derivWithin hdiff] at hd
  rw [hd, hrd.deriv, heq hr]

/-- A genuine growing-cone extension on the new profile. The hypotheses
on `w` state exactly the retained old segment and the new inward cone. -/
theorem exists_radialConeIncoming_graft {D : ReferenceData}
    (hD : RadialProfileGeometry D) {right : Bool} {a c p e scale ν J : ℝ}
    (ha : 0 < a) (hc : c ∈ radialCore D) (hp : p ∈ radialCore D)
    (he : e ∈ radialCore D)
    (horder : if right then a < c ∧ c < p ∧ p < e else e < p ∧ p < c ∧ c < a)
    (hcone : ∀ r ∈ uIcc c p, D.w =ᶠ[𝓝 r] (fun t => scale * t))
    {u w : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hODE : ∀ r ∈ uIcc c e, radialJacobi J D.w u r = 0)
    (hu₀ : u c = 1) (hu₁ : deriv u c = ν / c) (hν : ν ^ 2 = J)
    (hnewCone : ∀ r ∈ uIcc a c, w =ᶠ[𝓝 r] (fun t => scale * t))
    (hnewOld : ∀ r ∈ uIcc c e, w =ᶠ[𝓝 r] D.w) :
    ∃ U : ℝ → ℝ, ContDiff ℝ ∞ U ∧
      (∀ r ∈ uIcc a c, U =ᶠ[𝓝 r] (fun t => t ^ ν / c ^ ν)) ∧
      EqOn U (fun r => r ^ ν / c ^ ν) (uIcc a p) ∧
      (∀ r, (if right then p ≤ r else r ≤ p) → U =ᶠ[𝓝 r] u) ∧
      ∀ r ∈ uIcc a e, radialJacobi J w U r = 0 := by
  have hac : if right then a < c else c < a := by
    cases right
    · exact horder.2.2
    · exact horder.1
  have hcp : if right then c < p else p < c := by
    cases right <;> exact horder.2.1
  have hpe : if right then p < e else e < p := by
    cases right
    · exact horder.1
    · exact horder.2.2
  have hce : if right then c < e else e < c := by
    cases right
    · exact hpe.trans hcp
    · exact hcp.trans hpe
  have hae : if right then a < e else e < a := by
    cases right
    · exact hce.trans hac
    · exact hac.trans hce
  have hcFull : c ∈ uIcc a e := by
    cases right
    · rw [uIcc_of_ge hae.le]
      exact ⟨hce.le, hac.le⟩
    · rw [uIcc_of_le hae.le]
      exact ⟨hac.le, hce.le⟩
  have hpOld : p ∈ uIcc c e := by
    cases right
    · rw [uIcc_of_ge hce.le]
      exact ⟨hpe.le, hcp.le⟩
    · rw [uIcc_of_le hce.le]
      exact ⟨hcp.le, hpe.le⟩
  have hOldSub : uIcc c e ⊆ uIcc a e :=
    ordConnected_uIcc.uIcc_subset hcFull right_mem_uIcc
  have hConeSub : uIcc c p ⊆ uIcc c e :=
    ordConnected_uIcc.uIcc_subset left_mem_uIcc hpOld
  have hInnerSub : uIcc a c ⊆ uIcc a e :=
    ordConnected_uIcc.uIcc_subset left_mem_uIcc hcFull
  have hEq := radialConeIncoming_eqOn_power hD hc hp hcone hu
    (fun r hr => hODE r (hConeSub hr)) hu₀ hu₁ hν
  let q := (c + p) / 2
  have hq : q ∈ Ioo (min c p) (max c p) := by
    cases right
    · rw [min_eq_right hcp.le, max_eq_left hcp.le]
      change p < (c + p) / 2 ∧ (c + p) / 2 < c
      constructor <;> linarith
    · rw [min_eq_left hcp.le, max_eq_right hcp.le]
      change c < (c + p) / 2 ∧ (c + p) / 2 < p
      constructor <;> linarith
  have hqc : if right then c < q else q < c := by
    cases right
    · simpa only [max_eq_left hcp.le] using hq.2
    · simpa only [min_eq_left hcp.le] using hq.1
  have hqp : if right then q < p else p < q := by
    cases right
    · simpa only [min_eq_right hcp.le] using hq.1
    · simpa only [max_eq_right hcp.le] using hq.2
  have hqFull : q ∈ uIcc a e := hOldSub (hConeSub ⟨hq.1.le, hq.2.le⟩)
  have hlpos : 0 < min a e := lt_min ha (hD.1.trans he.1)
  obtain ⟨R, hR, hRp, hRg⟩ := exists_r07_smooth_radius_germ hlpos (min_le_max a e)
  let v : ℝ → ℝ := fun r => R r ^ ν / c ^ ν
  have hv : ContDiff ℝ ∞ v := (hR.rpow_const_of_ne (fun r => (hRp r).ne')).div_const _
  have hvg (r : ℝ) (hr : r ∈ uIcc a e) :
      v =ᶠ[𝓝 r] (fun t => t ^ ν / c ^ ν) :=
    (hRg r hr).fun_comp (fun t => t ^ ν / c ^ ν)
  have hug : u =ᶠ[𝓝 q] (fun t => t ^ ν / c ^ ν) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hq)
      (fun r hr => hEq ⟨hr.1.le, hr.2.le⟩)
  have hmatch : v =ᶠ[𝓝 q] u := (hvg q hqFull).trans hug.symm
  let U := seedOrientedGlue right q v u
  have hUi (r : ℝ) (hr : if right then r ≤ q else q ≤ r) : U =ᶠ[𝓝 r] v :=
    seedOrientedGlue_inward_germ hmatch hr
  have hUo (r : ℝ) (hr : if right then q ≤ r else r ≤ q) : U =ᶠ[𝓝 r] u :=
    seedOrientedGlue_outward_germ hmatch hr
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · cases right
    · exact contDiff_morseGlueCut hu hv hmatch.symm
    · exact contDiff_morseGlueCut hv hu hmatch
  · intro r hr
    have hi : if right then r ≤ q else q ≤ r := by
      cases right
      · rw [uIcc_of_ge hac.le] at hr
        exact hqc.le.trans hr.1
      · rw [uIcc_of_le hac.le] at hr
        exact hr.2.trans hqc.le
    exact (hUi r hi).trans (hvg r (hInnerSub hr))
  · intro r hr
    have hrFull : r ∈ uIcc a e :=
      ordConnected_uIcc.uIcc_subset left_mem_uIcc (hOldSub hpOld) hr
    rcases seedOrientedGlue_sides right q r with hi | ho
    · exact (hUi r hi).eq_of_nhds.trans (hvg r hrFull).eq_of_nhds
    · have hrCone : r ∈ uIcc c p := by
        cases right
        · rw [uIcc_of_ge (hqp.trans (hqc.trans hac)).le] at hr
          rw [uIcc_of_ge hcp.le]
          exact ⟨hr.1, ho.trans hqc.le⟩
        · rw [uIcc_of_le (hac.trans (hqc.trans hqp)).le] at hr
          rw [uIcc_of_le hcp.le]
          exact ⟨hqc.le.trans ho, hr.2⟩
      exact (hUo r ho).eq_of_nhds.trans (hEq hrCone)
  · intro r hr
    apply hUo r
    cases right
    · exact hr.trans hqp.le
    · exact hqp.le.trans hr
  · intro r hr
    have hrpos : 0 < r := hlpos.trans_le hr.1
    rcases seedOrientedGlue_sides right q r with hi | ho
    · have hwg : w =ᶠ[𝓝 r] (fun t => scale * t) := by
        by_cases hrc : if right then r ≤ c else c ≤ r
        · apply hnewCone r
          cases right
          · rw [uIcc_of_ge hae.le] at hr
            rw [uIcc_of_ge hac.le]
            exact ⟨hrc, hr.2⟩
          · rw [uIcc_of_le hae.le] at hr
            rw [uIcc_of_le hac.le]
            exact ⟨hr.1, hrc⟩
        · have hrCone : r ∈ uIcc c p := by
            cases right
            · rw [uIcc_of_ge hcp.le]
              exact ⟨hqp.le.trans hi, (le_of_not_ge hrc)⟩
            · rw [uIcc_of_le hcp.le]
              exact ⟨le_of_not_ge hrc, hi.trans hqp.le⟩
          exact (hnewOld r (hConeSub hrCone)).trans (hcone r hrCone)
      exact r07_radialJacobi_cone_power hrpos hν hwg ((hUi r hi).trans (hvg r hr))
    · have hrOld : r ∈ uIcc c e := by
        cases right
        · rw [uIcc_of_ge hae.le] at hr
          rw [uIcc_of_ge hce.le]
          exact ⟨hr.1, ho.trans hqc.le⟩
        · rw [uIcc_of_le hae.le] at hr
          rw [uIcc_of_le hce.le]
          exact ⟨hqc.le.trans ho, hr.2⟩
      exact (radialJacobi_eq_of_germs (hnewOld r hrOld) (hUo r ho)).trans (hODE r hrOld)

end ContinuousFlexibility.Radial
