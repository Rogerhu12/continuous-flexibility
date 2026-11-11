import ContinuousFlexibility.Radial.R07IncomingScale
import ContinuousFlexibility.Radial.R07RadialUniqueness
import ContinuousFlexibility.Radial.R07Assembly

/-!
# A concrete continuous incoming family with a fixed cap slope

The unit-height member fixes the normalization on the positive cap. Each
other member has the same Cauchy data at the join and is transported by its
own physical equation across the join. Scalar invariance of the model and
finite-interval uniqueness identify the whole cap with the fixed member.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem r07_cap_interval_subset_model {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (right : Bool) (k : ℕ) :
    uIcc (r07PreviousCellCut T right (T.index + k)) (r07PreviousCellJoin T right (T.index + k)) ⊆
      Icc (morseChainCellLeftRadius T right k) (morseChainCellRightRadius T right k) := by
  let m := T.index + k
  have hd2 : (2 : ℝ) ≤ T.d m := by
    rw [G.d_exact]
    exact_mod_cast morseChainInteger_ge_two m
  have hAB := morseChainParameters_pos T m hd2
  have hA : 0 < morseChainA T m := (mul_pos (by norm_num) hAB.2).trans hAB.1
  have hcut : r07CapCut right (morseChainA T m) (morseChainB T m) ∈
      Icc (T.leftX right m) (T.rightX right m) := by
    have hx := r07CapPoint_mem_cell right hAB.2 hAB.1
      (left_mem_Icc.mpr (r07CapLength_pos right hA).le)
    rw [r07CapPoint_zero] at hx
    rw [G.leftX_eq right k, G.rightX_eq right k]
    exact hx
  have hR := G.actual_radius_equation right k
  have hmono := (morseCell_strictMonoOn hR.1 (fun x hx => (hR.2.2 x hx).1)).monotoneOn
  have hc : r07PreviousCellCut T right m ∈
      Icc (morseChainCellLeftRadius T right k) (morseChainCellRightRadius T right k) := by
    exact ⟨hmono ⟨le_rfl, hR.2.1.le⟩ hcut hcut.1,
      hmono hcut ⟨hR.2.1.le, le_rfl⟩ hcut.2⟩
  have hp : r07PreviousCellJoin T right m ∈
      Icc (morseChainCellLeftRadius T right k) (morseChainCellRightRadius T right k) := by
    have horder := hmono ⟨le_rfl, hR.2.1.le⟩ ⟨hR.2.1.le, le_rfl⟩ hR.2.1.le
    cases right
    · exact ⟨le_rfl, horder⟩
    · exact ⟨horder, le_rfl⟩
  exact uIcc_subset_Icc hc hp

theorem r07_preceding_join_interval {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (right : Bool) (k : ℕ) :
    uIcc (r07PreviousCellJoin T right (T.index + k))
      (r07CellEntry T right (T.index + k + 1)) =
        Icc (T.joinLeft right (T.index + k)) (T.joinRight right (T.index + k)) := by
  have hJ := G.joins k
  have ho := (morseChainPhysicalJoin_order G right k).le
  cases right
  · have hp : r07PreviousCellJoin T false (T.index + k) = T.joinRight false (T.index + k) :=
      hJ.2.2.2.symm
    have he : r07CellEntry T false (T.index + k + 1) = T.joinLeft false (T.index + k) := by
      simpa only [r07CellEntry, Bool.false_eq_true, if_false, Nat.add_assoc] using hJ.2.2.1.symm
    rw [hp, he, uIcc_of_ge ho]
  · have hp : r07PreviousCellJoin T true (T.index + k) = T.joinLeft true (T.index + k) :=
      hJ.1.symm
    have he : r07CellEntry T true (T.index + k + 1) = T.joinRight true (T.index + k) := by
      simpa only [r07CellEntry, if_true, Nat.add_assoc] using hJ.2.1.symm
    rw [hp, he, uIcc_of_le ho]

theorem r07_deriv_eq_of_eqOn_uIcc {u v : ℝ → ℝ} {a b r : ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hab : a ≠ b)
    (he : EqOn u v (uIcc a b)) (hr : r ∈ uIcc a b) : deriv u r = deriv v r := by
  have huniq : UniqueDiffOn ℝ (uIcc a b) := uniqueDiffOn_Icc (min_lt_max.mpr hab)
  have hd := derivWithin_congr he (he hr)
  rw [(hu.differentiable (by simp) r).derivWithin (huniq r hr),
    (hv.differentiable (by simp) r).derivWithin (huniq r hr)] at hd
  exact hd

/-- A later-band incoming solution family with constant normalized cap
slope and a constant positive height coordinate. All remaining dependence
on the height sequence is the actual continuous transport through the join. -/
theorem exists_r07_original_incoming_family {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (phi : ℝ → ℝ) (C : ℕ → ℝ)
    (hfamily : ∀ σ, (∀ i, 1 ≤ σ i ∧ σ i ≤ 2) →
      MorseChainRealization T σ (morseChainReferenceFamily G phi σ) C)
    {Cstar : ℝ} (hCstar : 1000 ≤ Cstar) (right : Bool) (k : ℕ) {j : ℕ} (hj : 2 ≤ j)
    (hband : radialFrequencyBand T Cstar (T.index + k + 1) j) :
    let m := T.index + k
    let c := r07PreviousCellCut T right m
    let p := r07PreviousCellJoin T right m
    let e := r07CellEntry T right (m + 1)
    ∃ (a Ξ : ℝ) (u : (ℕ → ℝ) → ℝ → ℝ),
      a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2) ∧ 0 < Ξ ∧
      (∀ σ, (∀ i, 1 ≤ σ i ∧ σ i ≤ 2) →
        let D := morseChainReferenceFamily G phi σ
        ContDiff ℝ ∞ (u σ) ∧
        (∀ v, RadialNaturalTail D right j e v →
          R07MatchingGeometry T D right (m + 1) j c p e (u σ) v) ∧
        radialState D j p (D.w p) (u σ) = (1, a) ∧
        D.w e = σ (m + 1) * Ξ * D.w p) ∧
      ContinuousOn (fun σ => radialState (morseChainReferenceFamily G phi σ) j e
        ((morseChainReferenceFamily G phi σ).w p) (u σ)) heightCube := by
  classical
  let m := T.index + k
  let c := r07PreviousCellCut T right m
  let p := r07PreviousCellJoin T right m
  let e := r07CellEntry T right (m + 1)
  let D₀ := morseChainReferenceFamily G phi morseUnitHeights
  have h₀ := hfamily morseUnitHeights morseUnitHeights_admissible
  obtain ⟨u₀, a, hc, hp, he, hwp, horder, hu₀c, hu₀p, hu₀sign, hw₀pos,
    hu₀smooth, hu₀hom, ha, hu₀state⟩ := exists_r07_incoming_on_preceding_cell G h₀
      morseUnitHeights_admissible hCstar right k hj hband
  let Ξ : ℝ := D₀.w e / D₀.w p
  have hΞ : 0 < Ξ := div_pos (h₀.geometry.2.2.2.2.1 e he) hwp
  have hpce : p ∈ uIcc c e := by
    cases right
    · exact mem_uIcc.mpr (Or.inr ⟨horder.1.le, horder.2.le⟩)
    · exact mem_uIcc.mpr (Or.inl ⟨horder.1.le, horder.2.le⟩)
  have hcp : c ≠ p := by
    cases right
    · exact horder.2.ne'
    · exact horder.1.ne
  have hcap : uIcc c p ⊆ uIcc c e := uIcc_subset_uIcc_left hpce
  have hjoin : uIcc p e ⊆ uIcc c e := uIcc_subset_uIcc_right hpce
  let D (σ : HeightRatios) := morseChainReferenceFamily G phi σ.val
  have hreal (σ : HeightRatios) := hfamily σ.val σ.property
  have hcσ (σ : HeightRatios) : c ∈ radialCore (D σ) := hc
  have hpσ (σ : HeightRatios) : p ∈ radialCore (D σ) := hp
  have heσ (σ : HeightRatios) : e ∈ radialCore (D σ) := he
  have hex (σ : HeightRatios) : ∃ u : ℝ → ℝ,
      ContDiff ℝ ∞ u ∧ u p = 1 ∧ deriv u p = deriv u₀ p ∧ u c = 0 ∧
      (if right then 0 < deriv u c else deriv u c < 0) ∧
      RadialHomogeneousOn (D σ) j (uIcc c e) u ∧
      (∀ r ∈ radialOpenSpan c p, 0 < deriv (D σ).w r) := by
    obtain ⟨u, hu, hup, hud, hode⟩ := exists_radialSolution_on_Icc (hreal σ).geometry
      (lt_min (hcσ σ).1 (heσ σ).1) (min_le_max : min c e ≤ max c e)
      (max_lt (hcσ σ).2 (heσ σ).2) hpce ((j : ℝ) ^ 2) 1 (deriv u₀ p)
    have heq : EqOn u u₀ (uIcc c p) := by
      apply radialHomogeneous_eqOn_Icc (hreal σ).geometry
        (lt_min (hcσ σ).1 (hpσ σ).1) (min_le_max : min c p ≤ max c p)
        (max_lt (hcσ σ).2 (hpσ σ).2) right_mem_uIcc hu hu₀smooth
        (fun r hr => hode r (hcap hr))
      · intro r hr
        have hg := r07_originalFamily_model_scale_germ G phi σ.val σ.property right k
          (r07_cap_interval_subset_model G right k hr)
        rw [radialJacobi_profile_scale_germ hg, hu₀hom.2 r (hcap hr), mul_zero]
      · exact hup.trans hu₀p.symm
      · exact hud
    have hdc := r07_deriv_eq_of_eqOn_uIcc hu hu₀smooth hcp heq left_mem_uIcc
    obtain ⟨v, b, hc', hp', he', hwp', hord', hvc, hvp, hvs, hinc,
      hvsmooth, hvhom, hb, hvstate⟩ :=
      exists_r07_incoming_on_preceding_cell G (hreal σ) σ.property hCstar right k hj hband
    refine ⟨u, hu, hup, hud, (heq left_mem_uIcc).trans hu₀c, ?_, ⟨hu.contDiffOn, hode⟩, hinc⟩
    simpa only [hdc] using hu₀sign
  choose U hUsmooth hUp hUd hUc hUsign hUhom hUinc using hex
  have hjet (order : ℕ) : ContinuousOn (fun z : HeightRatios × ℝ =>
      iteratedDeriv order (D z.1).w z.2) {z | z.2 ∈ uIcc p e} := by
    rw [r07_preceding_join_interval G right k]
    refine (continuousOn_morseChainGluedProfile_iteratedDeriv_join G right k order).congr ?_
    intro z hz
    dsimp only [D]
    rw [morseChainReferenceFamily_admissible G phi z.1.val z.1.property]
    <;> rfl
  have hzero : ContinuousOn (fun z : HeightRatios × ℝ => (D z.1).w z.2)
      {z | z.2 ∈ uIcc p e} := by simpa only [iteratedDeriv_zero] using hjet 0
  have hone : ContinuousOn (fun z : HeightRatios × ℝ => deriv (D z.1).w z.2)
      {z | z.2 ∈ uIcc p e} := by simpa only [iteratedDeriv_one] using hjet 1
  have hprofile (σ : HeightRatios) (r : ℝ) (hr : r ∈ uIcc p e) : (D σ).w r ≠ 0 :=
    ((hreal σ).geometry.2.2.2.2.1 r (ordConnected_Ioo.uIcc_subset (hpσ σ) (heσ σ) hr)).ne'
  have hradius (r : ℝ) (hr : r ∈ uIcc p e) : r ≠ 0 :=
    (h₀.geometry.1.trans (ordConnected_Ioo.uIcc_subset hp he hr).1).ne'
  have hY : Continuous (fun σ : HeightRatios => radialState (D σ) j e ((D σ).w p) (U σ)) :=
    continuous_radialState_transport j (fun σ => (hreal σ).geometry.2.2.1.1) hUsmooth
      hzero hone hprofile hradius (fun σ r hr => (hUhom σ).2 r (hjoin hr))
      (by simpa only [hUp] using (continuous_const : Continuous (fun _ : HeightRatios => (1 : ℝ))))
      (by simpa only [hUd] using (continuous_const : Continuous (fun _ : HeightRatios => deriv u₀ p)))
  let u (σ : ℕ → ℝ) : ℝ → ℝ :=
    if hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2 then U ⟨σ, hσ⟩ else 0
  have hu (σ : ℕ → ℝ) (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) : u σ = U ⟨σ, hσ⟩ := dif_pos hσ
  refine ⟨a, Ξ, u, ha, hΞ, ?_, ?_⟩
  · intro σ hσ
    let t : HeightRatios := ⟨σ, hσ⟩
    have hwpσ : 0 < (D t).w p := (hreal t).geometry.2.2.2.2.1 p (hpσ t)
    rw [hu σ hσ]
    refine ⟨hUsmooth t, ?_, ?_, r07_realized_entry_join_ratio (hreal t) h₀ right (Nat.le_add_right _ _)⟩
    · intro v hv
      refine ⟨hcσ t, heσ t, hpσ t, hwpσ, horder, rfl, ?_, hUinc t,
        (hUsmooth t).contDiffAt, (hUsmooth t).contDiffAt, hUhom t, hv⟩
      have hne : T.index + k + 1 ≠ T.index := by omega
      rw [if_neg hne]
      exact ⟨hUc t, hUp t, hUsign t⟩
    · change radialState (D t) j p ((D t).w p) (U t) = (1, a)
      have hs₀ : radialState D₀ j p (D₀.w p) u₀ = (1, a) := hu₀state
      have hup₀ : u₀ p = 1 := hu₀p
      have hwp₀ : D₀.w p ≠ 0 := hwp.ne'
      rw [radialState, hup₀, div_self hwp₀, one_mul] at hs₀
      rw [radialState, hUp t, hUd t, div_self hwpσ.ne', one_mul]
      exact hs₀
  · apply continuousOn_iff_continuous_domRestrict.mpr
    let lift : heightCube → HeightRatios := fun σ => ⟨σ.val, mem_heightCube.mp σ.property⟩
    have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
    have hcY := hY.comp hlift
    convert hcY using 1
    funext σ
    change radialState (D (lift σ)) j e ((D (lift σ)).w p) (u σ.val) =
      radialState (D (lift σ)) j e ((D (lift σ)).w p) (U (lift σ))
    rw [hu σ.val (mem_heightCube.mp σ.property)]

end ContinuousFlexibility.Radial
