import ContinuousFlexibility.Radial.MorseChainProfileGluing
import ContinuousFlexibility.Radial.MorseChainJetScales
import ContinuousFlexibility.Radial.MorseChainPartitionData

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private def morseSelectedXLo : ℝ := morseCellLeftCut - morseJoinCollarWidth

private def morseSelectedXEnd (T : Statements.MorseChainData) (k : ℕ) : ℝ :=
  morseRightCapEnd (Statements.morseChainA T (T.index + k))
    (Statements.morseChainB T (T.index + k)) (1 / 100)

private def morseSelectedXHi (T : Statements.MorseChainData) (k : ℕ) : ℝ :=
  morseSelectedXEnd T k + morseJoinCollarWidth

private theorem morseSelected_parameters {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) :
    4 * Statements.morseChainB T (T.index + k) < Statements.morseChainA T (T.index + k) ∧
      0 < Statements.morseChainB T (T.index + k) := by
  apply morseChainParameters_pos
  rw [G.d_exact]
  exact_mod_cast morseChainInteger_ge_two (T.index + k)

private theorem morseSelected_A_small {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) :
    Statements.morseChainA T (T.index + k) ≤ 25 / (2 * (9 : ℝ) ^ 9) := by
  have hlog : log (9 / (25 / (2 * (9 : ℝ) ^ 9))) ≤ 80 := calc
    _ ≤ log ((9 : ℝ) ^ 10) := log_le_log (by positivity) (by norm_num)
    _ = 10 * log (9 : ℝ) := by rw [log_pow]; norm_num
    _ ≤ _ := by
      have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
      linarith only [h]
  have hn : 10 ≤ T.index + k := by have h := G.start_large; omega
  have hn' : (10 : ℝ) ≤ ((T.index + k : ℕ) : ℝ) := by exact_mod_cast hn
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hn' 2
  exact morseChainA_le_of_sq_ge_log T (T.index + k) (G.d_exact _) (by positivity)
    (by linarith only [hlog, hs])

private theorem morseSelected_turn_le_end {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) :
    morseRightTurn (Statements.morseChainA T (T.index + k))
      (Statements.morseChainB T (T.index + k)) ≤ morseSelectedXEnd T k := by
  have hAB := morseSelected_parameters G k
  have hA := (mul_pos (by norm_num : (0 : ℝ) < 4) hAB.2).trans hAB.1
  exact le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le

private theorem morseSelected_cuts_mem {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) :
    morseCellLeftCut ∈ Ioo morseSelectedXLo (morseSelectedXHi T k) ∧
      morseSelectedXEnd T k ∈ Ioo morseSelectedXLo (morseSelectedXHi T k) := by
  have hh : 0 < morseJoinCollarWidth := by norm_num [morseJoinCollarWidth]
  have hAB := morseSelected_parameters G k
  have he := (morseCellLeftCut_lt_rightTurn hAB.2 hAB.1).trans_le (morseSelected_turn_le_end G k)
  have hlo : morseSelectedXLo < morseCellLeftCut := sub_lt_self _ hh
  have hhi : morseSelectedXEnd T k < morseSelectedXHi T k := lt_add_of_pos_right _ hh
  exact ⟨⟨hlo, he.trans hhi⟩, ⟨hlo.trans he, hhi⟩⟩

private theorem morseSelected_radiusJetData {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) :
    ∀ x ∈ Icc morseSelectedXLo (morseSelectedXHi T k), exp (-x) ≤ 3 ∧
      |G.normal k x| ≤ 2 ∧ Statements.morseChainA T (T.index + k) ^ 5 / 200 ≤
        deriv (G.normal k) x ∧ |deriv (G.normal k) x| ≤ 8 := by
  let A := Statements.morseChainA T (T.index + k)
  let B := Statements.morseChainB T (T.index + k)
  let a := morseCellLeftCut
  let b := morseRightTurn A B
  let e := morseSelectedXEnd T k
  let r := G.normal k
  have hAB := morseSelected_parameters G k
  have hA : 0 < A := (mul_pos (by norm_num : (0 : ℝ) < 4) hAB.2).trans hAB.1
  have hA₁ : A ≤ 1 := (morseSelected_A_small G k).trans (by norm_num)
  have hA₅ : A ^ 5 ≤ A := calc
    _ = A * A ^ 4 := by ring
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left
      (by simpa only [one_pow] using pow_le_pow_left₀ hA.le hA₁ 4) hA.le
    _ = _ := mul_one _
  have hA₅₀ : 0 ≤ A ^ 5 := pow_nonneg hA.le _
  intro x hx
  have hexp : exp (-x) ≤ 3 := by
    have hlog : morseJoinCollarWidth ≤ log 2 := calc
      _ ≤ 1 - (2 : ℝ)⁻¹ := by norm_num [morseJoinCollarWidth]
      _ ≤ _ := one_sub_inv_le_log_of_pos (by norm_num)
    have hxlo : a - morseJoinCollarWidth ≤ x := hx.1
    calc
      _ ≤ exp (-a + log 2) := exp_le_exp.mpr (by linarith only [hlog, hxlo])
      _ = _ := by
        rw [exp_add, exp_neg_morseCellLeftCut, exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  refine ⟨hexp, ?_⟩
  change |r x| ≤ 2 ∧ A ^ 5 / 200 ≤ deriv r x ∧ |deriv r x| ≤ 8
  rw [abs_of_pos ((G.model k).speed_pos x hx)]
  by_cases hxa : x ≤ a
  · obtain ⟨hrlo, hrhi, hvlo, hvhi, _, _⟩ := (G.model k).left_collar x ⟨hx.1, hxa⟩
    have hrp : 0 ≤ r x := by linarith only [hrlo]
    exact ⟨by rwa [abs_of_nonneg hrp], by linarith only [hvlo, hA₅, hA],
      by linarith only [hvhi, hA₁]⟩
  · have hax : a ≤ x := le_of_lt (lt_of_not_ge hxa)
    by_cases hxb : x ≤ b
    · obtain ⟨_, hrp, hrhi, hvlo, hvhi⟩ := (G.model k).left_half x ⟨hax, hxb⟩
      exact ⟨by rwa [abs_of_pos hrp], by linarith only [hvlo, hA₅₀], by linarith only [hvhi, hA₁]⟩
    · have hbx : b ≤ x := le_of_lt (lt_of_not_ge hxb)
      by_cases hxe : x ≤ e
      · obtain ⟨_, hrp, hrhi, hvlo, hvhi⟩ := (G.model k).right_half x ⟨hbx, hxe⟩
        exact ⟨by rwa [abs_of_pos hrp], by linarith only [hvlo, hA₅₀],
          by linarith only [hvhi, hA₅, hA₁]⟩
      · obtain ⟨hrlo, hrhi, hvlo, hvhi, _, _⟩ :=
          (G.model k).right_collar x ⟨le_of_lt (lt_of_not_ge hxe), hx.2⟩
        have hrp : 0 ≤ r x := by linarith only [hrlo]
        exact ⟨by rwa [abs_of_nonneg hrp], hvlo, by linarith only [hvhi, hA₅, hA₁]⟩

private def morseSelectedModel {T : Statements.MorseChainData} (G : MorseChainGeometryWitness T)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ) : MorseJoinJetModel := by
  have hAB := morseSelected_parameters G k
  have hA := (mul_pos (by norm_num : (0 : ℝ) < 4) hAB.2).trans hAB.1
  have hx := (morseSelected_cuts_mem G k).1
  exact
    { A := Statements.morseChainA T (T.index + k), B := Statements.morseChainB T (T.index + k)
      p := morseSelectedXLo, q := morseSelectedXHi T k
      amplitude := Statements.morseChainAmplitude T σ (T.index + k)
      scale := G.factor side k, radius := G.normal k
      hA := hA, hA₁ := (morseSelected_A_small G k).trans (by norm_num)
      hB := hAB.2.le, hBA := by linarith only [hAB.1, hAB.2]
      hpq := hx.1.trans hx.2
      hAmplitude := morseChainAmplitude_pos T σ hσ _
      hScale := G.factor_pos side k, hSmooth := (G.model k).smooth
      hExp := fun x hx => (morseSelected_radiusJetData G k x hx).1
      hBound := fun x hx => ⟨(morseSelected_radiusJetData G k x hx).2.1,
        (morseSelected_radiusJetData G k x hx).2.2.2⟩
      hEquation := (G.model k).equation
      hVelocity := fun x hx => (morseSelected_radiusJetData G k x (Ioo_subset_Icc_self hx)).2.2.1 }

private theorem morseSelected_model_velocity_pos (M : MorseJoinJetModel) :
    ∀ x ∈ Ioo M.p M.q, 0 < deriv M.radius x :=
  fun x hx => (div_pos (pow_pos M.hA 5) (by norm_num)).trans_le (M.hVelocity x hx)

private theorem morseSelected_scaledRadius_strictMonoOn (M : MorseJoinJetModel) :
    StrictMonoOn (fun x => M.scale * M.radius x) (Icc M.p M.q) := by
  have hcont : Continuous (fun x => M.scale * M.radius x) :=
    continuous_const.mul M.hSmooth.continuous
  apply strictMonoOn_of_deriv_pos (convex_Icc M.p M.q) hcont.continuousOn
  intro x hx
  have hx' : x ∈ Ioo M.p M.q := by simpa only [interior_Icc] using hx
  have hd : HasDerivAt (fun x => M.scale * M.radius x) (M.scale * deriv M.radius x) x :=
    ((M.hSmooth.differentiable (by simp) x).hasDerivAt).const_mul M.scale
  rw [hd.deriv]
  exact mul_pos M.hScale (morseSelected_model_velocity_pos M x hx')

private theorem morseSelected_scaled_mem (M : MorseJoinJetModel) {x : ℝ} (hx : x ∈ Ioo M.p M.q) :
    M.scale * M.radius x ∈ M.image := by
  change M.scale * M.radius x ∈ Ioo (M.scale * M.radius M.p) (M.scale * M.radius M.q)
  rw [← morseCollar_scaledRadius_image_Ioo M.hpq.le M.hScale M.hSmooth (morseSelected_model_velocity_pos M)]
  exact ⟨x, hx, rfl⟩

private theorem morseSelected_leftRadius_eq {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    morseChainCellLeftRadius T side k = G.factor side k * G.normal k morseCellLeftCut := by
  rw [morseChainCellLeftRadius, G.leftX_eq, G.radius_eq]

private theorem morseSelected_rightRadius_eq {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    morseChainCellRightRadius T side k = G.factor side k * G.normal k (morseSelectedXEnd T k) := by
  rw [morseChainCellRightRadius, G.rightX_eq, G.radius_eq, morseSelectedXEnd]

private theorem morseSelected_radialJet_eq (k : ℕ) (f : ℝ → ℝ) :
    Statements.radialJet k f = iteratedDeriv k f := by
  induction k with
  | zero => exact iteratedDeriv_zero.symm
  | succ k ih => rw [Statements.radialJet, ih, iteratedDeriv_succ]

private theorem morseSelected_jetBounds_congr {n k : ℕ} {C x : ℝ} {f g : ℝ → ℝ}
    (h : MorseChainJetBounds n k C f x) (hg : f =ᶠ[𝓝 x] g) :
    MorseChainJetBounds n k C g x := by
  have hv : f x = g x := hg.eq_of_nhds
  have hW : Statements.radialJet k f x = Statements.radialJet k g x := by
    simpa only [morseSelected_radialJet_eq] using hg.iteratedDeriv_eq k
  have hi : f⁻¹ =ᶠ[𝓝 x] g⁻¹ := hg.fun_comp Inv.inv
  have hI : Statements.radialJet k f⁻¹ x = Statements.radialJet k g⁻¹ x := by
    simpa only [morseSelected_radialJet_eq] using hi.iteratedDeriv_eq k
  simpa only [MorseChainJetBounds, hv, hW, hI] using h

/-- Pointwise physical jets of the very model chosen for the glued profile. -/
theorem exists_morseChainChosenModel_jetBounds {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (order : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ)
      (z : ℝ), z ∈ Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k) →
      MorseChainJetBounds (T.index + k) order C (morseChainChosenModel G σ hσ side k) z := by
  have hHi : 0 < G.factorHi := (G.factor_pos true 0).trans_le (G.factor_bounds true 0).2
  obtain ⟨C, hC, hbound⟩ := exists_morseChainModel_jetBounds G.factorLo_pos hHi order
  refine ⟨C, hC, ?_⟩
  intro σ hσ side k z hz
  let M := morseSelectedModel G σ hσ side k
  have hx := morseSelected_cuts_mem G k
  have ha := morseSelected_scaled_mem M hx.1
  have hb := morseSelected_scaled_mem M hx.2
  have hm : z ∈ M.image := ⟨
    ha.1.trans_le ((morseSelected_leftRadius_eq G side k).symm.trans_le hz.1),
    (hz.2.trans_eq (morseSelected_rightRadius_eq G side k)).trans_lt hb.2⟩
  have hn : 1 ≤ T.index + k := by have h := G.start_large; omega
  have h := hbound T σ hσ hn (G.d_exact _) M rfl rfl (G.factor_bounds side k).1
    (G.factor_bounds side k).2 z hm
  exact morseSelected_jetBounds_congr h ((morseChainChosenModel_spec G σ hσ side k).2.2 z hz).symm

private theorem morseSelected_scaled_increment (M : MorseJoinJetModel)
    {x y : ℝ} (hpx : M.p ≤ x) (hxy : x ≤ y) (hyq : y ≤ M.q) :
    M.scale * (y - x) * (M.A ^ 5 / 200) ≤ M.scale * M.radius y - M.scale * M.radius x := by
  have hv (t : ℝ) (ht : t ∈ interior (Icc x y)) : M.A ^ 5 / 200 ≤ deriv M.radius t := by
    rw [interior_Icc] at ht
    exact M.hVelocity t ⟨hpx.trans_lt ht.1, ht.2.trans_le hyq⟩
  have h := (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv
    M.hSmooth.continuous.continuousOn (M.hSmooth.differentiable (by simp)).differentiableOn hv
    x (left_mem_Icc.mpr hxy) y (right_mem_Icc.mpr hxy) hxy
  calc
    _ = M.scale * ((M.A ^ 5 / 200) * (y - x)) := by ring
    _ ≤ M.scale * (M.radius y - M.radius x) := mul_le_mul_of_nonneg_left h M.hScale.le
    _ = _ := mul_sub _ _ _

private theorem morseSelected_quarter_lt {a c s A U : ℝ}
    (ha : 0 ≤ a) (hc : c ≤ 1) (hs : 0 < s) (hA : 0 < A) (hA₀ : A ≤ 1 / 1000)
    (has : a ≤ 2 * s) (hU : 0 ≤ U) (hUA : U ≤ A) :
    c * a * U ^ 12 / 4 < s * morseJoinCollarWidth * (A ^ 5 / 200) := by
  have hca : c * a ≤ 2 * s :=
    (mul_le_mul_of_nonneg_right hc ha).trans (by simpa only [one_mul] using has)
  have h7 : A ^ 7 ≤ (1 / 1000 : ℝ) ^ 7 := pow_le_pow_left₀ hA.le hA₀ 7
  have h7' : A ^ 7 / 2 < morseJoinCollarWidth / 200 := by
    unfold morseJoinCollarWidth
    linarith only [h7]
  calc
    _ ≤ ((2 * s) * A ^ 12) / 4 := div_le_div_of_nonneg_right
      (mul_le_mul hca (pow_le_pow_left₀ hU hUA 12) (pow_nonneg hU 12) (by positivity)) (by norm_num)
    _ = (s * A ^ 5) * (A ^ 7 / 2) := by ring
    _ < (s * A ^ 5) * (morseJoinCollarWidth / 200) :=
      mul_lt_mul_of_pos_left h7' (mul_pos hs (pow_pos hA 5))
    _ = _ := by ring

private theorem morseSelected_floor_numeric {a s A : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hA : 0 < A) (hsa : s / 4 ≤ a) (hA₀ : A ≤ 25 / (2 * (9 : ℝ) ^ 9)) :
    2 / a ≤ (100 / (9 : ℝ) ^ 9) / (s * A) := by
  apply (div_le_div_iff₀ ha (mul_pos hs hA)).mpr
  calc
    2 * (s * A) = s * (2 * A) := by ring
    _ ≤ s * (25 / (9 : ℝ) ^ 9) := mul_le_mul_of_nonneg_left (by linarith only [hA₀]) hs.le
    _ = (100 / (9 : ℝ) ^ 9) * (s / 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsa (by positivity)

private theorem morseSelected_logFloor_of_model (M : MorseJoinJetModel)
    {z m : ℝ} {F : ℝ → ℝ} (hz : z ∈ M.image) (hg : F =ᶠ[𝓝 z] M.logProfile)
    (hSlope : ∀ t ∈ Ioo M.p M.q, M.scale * M.radius t = z →
      m ≤ -morseRho M.A M.B t * M.radius t / (M.scale * (deriv M.radius t) ^ 2)) :
    m ≤ deriv F z := by
  change z ∈ Ioo (M.scale * M.radius M.p) (M.scale * M.radius M.q) at hz
  rw [← morseCollar_scaledRadius_image_Ioo M.hpq.le M.hScale M.hSmooth (morseSelected_model_velocity_pos M)] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hd := (morseCollarLogProfile_jet M.hAmplitude M.hScale M.hSmooth
    (morseSelected_model_velocity_pos M) ht (M.hEquation t (Ioo_subset_Icc_self ht))).2.2
  rw [hg.deriv_eq]
  change m ≤ deriv (morseCollarLogProfile M.radius M.amplitude M.scale M.p M.q) (M.scale * M.radius t)
  rw [hd.deriv]
  exact hSlope t ht rfl

private theorem morseSelected_collar_logFloor {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) (k : ℕ) {a z : ℝ} {F : ℝ → ℝ} :
    let M := morseSelectedModel G σ hσ side k
    0 < a → M.scale / 4 ≤ a → z ∈ M.image → F =ᶠ[𝓝 z] M.logProfile →
      (z ≤ M.scale * M.radius morseCellLeftCut ∨
        M.scale * M.radius (morseSelectedXEnd T k) ≤ z) →
      2 / a ≤ deriv F z := by
  dsimp only
  intro ha hsa hz hg hcap
  let M := morseSelectedModel G σ hσ side k
  apply morseSelected_logFloor_of_model M hz hg
  intro t ht htEq
  have hmono := morseSelected_scaledRadius_strictMonoOn M
  have hx := morseSelected_cuts_mem G k
  have hBa := morseChainB_A_bounds T (T.index + k) (by
    rw [G.d_exact]
    exact_mod_cast (show 1 ≤ morseChainInteger (T.index + k) from
      (by decide : 1 ≤ 2).trans (morseChainInteger_ge_two (T.index + k))))
  have hslope : (100 / (9 : ℝ) ^ 9) / (M.scale * M.A) ≤
      -morseRho M.A M.B t * M.radius t / (M.scale * (deriv M.radius t) ^ 2) := by
    rcases hcap with hleft | hright
    · have htc : t ≤ morseCellLeftCut := by
        by_contra hbad
        have hlt := hmono (Ioo_subset_Icc_self hx.1) (Ioo_subset_Icc_self ht)
          (lt_of_not_ge hbad)
        change M.scale * M.radius morseCellLeftCut < M.scale * M.radius t at hlt
        rw [htEq] at hlt
        exact (not_lt_of_ge hleft) hlt
      obtain ⟨hrlo, hrhi, hvlo, hvhi, hκlo, hκhi⟩ :=
        (G.model k).left_collar t ⟨ht.1.le, htc⟩
      exact (morseCollarLogSlope_bounds M.hA (morseSelected_parameters G k).2 M.hScale
        hBa.1 hBa.2 ⟨hrlo, hrhi⟩ (Or.inl ⟨hvlo, hvhi, hκlo, hκhi⟩)).1
    · have hte : morseSelectedXEnd T k ≤ t := by
        by_contra hbad
        have hlt := hmono (Ioo_subset_Icc_self ht) (Ioo_subset_Icc_self hx.2)
          (lt_of_not_ge hbad)
        change M.scale * M.radius t < M.scale * M.radius (morseSelectedXEnd T k) at hlt
        rw [htEq] at hlt
        exact (not_lt_of_ge hright) hlt
      obtain ⟨hrlo, hrhi, hvlo, hvhi, hκlo, hκhi⟩ :=
        (G.model k).right_collar t ⟨hte, ht.2.le⟩
      exact (morseCollarLogSlope_bounds M.hA (morseSelected_parameters G k).2 M.hScale
        hBa.1 hBa.2 ⟨hrlo, hrhi⟩ (Or.inr ⟨hvlo, hvhi, hκlo, hκhi⟩)).1
  exact (morseSelected_floor_numeric ha M.hScale M.hA hsa (morseSelected_A_small G k)).trans hslope

/-- Pointwise jets of the very connector chosen for the glued profile.
The reference label is the outward block on both sides. -/
theorem exists_morseChainChosenJoin_jetBounds {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (order : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ)
      (z : ℝ), z ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k)) →
      MorseChainJetBounds (T.index + k) order C (morseChainChosenJoinProfile G σ hσ side k) z := by
  let c : ℝ := 1 / 100
  let aLo := G.factorLo / 2
  have hc : 0 < c := by norm_num [c]
  have hc₁ : c ≤ 1 := by norm_num [c]
  have haLo : 0 < aLo := div_pos G.factorLo_pos (by norm_num)
  have hHi : 0 < G.factorHi := (G.factor_pos true 0).trans_le (G.factor_bounds true 0).2
  obtain ⟨C, hC, hbound⟩ := exists_morseChainJoin_jetBounds hc hc₁ haLo G.factorLo_pos hHi order
  refine ⟨11 + 4 * C, by linarith only [hC], ?_⟩
  intro σ hσ side k z hz
  let P := morseChainChosenJoin G σ hσ side k
  let i := morseChainJoinDeparture side k
  let j := morseChainJoinArrival side k
  let n := T.index + i
  let m := T.index + j
  let L := morseSelectedModel G σ hσ side i
  let R := morseSelectedModel G σ hσ side j
  let e := morseSelectedXEnd T i
  let a := L.scale * L.radius e
  let b := R.scale * R.radius morseCellLeftCut
  let U := min L.A R.A
  let ell := c * a * U ^ 12
  let h := ell / 4
  have hEnds : T.joinLeft side (T.index + k) = a ∧ T.joinRight side (T.index + k) = b := by
    cases side
    · rw [(G.joins k).2.2.1, (G.joins k).2.2.2]
      exact ⟨morseSelected_rightRadius_eq G false (k + 1), morseSelected_leftRadius_eq G false k⟩
    · rw [(G.joins k).1, (G.joins k).2.1]
      exact ⟨morseSelected_rightRadius_eq G true k, morseSelected_leftRadius_eq G true (k + 1)⟩
  have hMin : U = min (Statements.morseChainA T (T.index + k))
      (Statements.morseChainA T (T.index + (k + 1))) := by
    cases side
    · exact min_comm _ _
    · rfl
  have hPlace : b - a = ell := by
    have hPlaced := G.join_width side k
    rw [hEnds.1, hEnds.2] at hPlaced
    change b - a = c * a * U ^ 12
    rw [hPlaced, morseChainJoinFraction, hMin]
    dsimp only [c]
    ring
  have hCut : morseChainProfileJoinCutoff T side k = h := by
    unfold morseChainProfileJoinCutoff
    rw [hEnds.1, hEnds.2, hPlace]
  have hNn : T.index ≤ n := Nat.le_add_right _ _
  have hNm : T.index ≤ m := Nat.le_add_right _ _
  have hn : 100 ≤ n := G.start_large.trans hNn
  have hadj : m = n + 1 ∨ n = m + 1 := by
    cases side
    · exact Or.inr (Nat.add_assoc _ _ _).symm
    · exact Or.inl (Nat.add_assoc _ _ _).symm
  have hxL : e ∈ Ioo L.p L.q := (morseSelected_cuts_mem G i).2
  have hxR : morseCellLeftCut ∈ Ioo R.p R.q := (morseSelected_cuts_mem G j).1
  have hLe := (G.model i).right_collar e (left_mem_Icc.mpr hxL.2.le)
  have hRe := (G.model j).left_collar morseCellLeftCut (right_mem_Icc.mpr hxR.1.le)
  have haL₀ : L.scale / 2 ≤ a := calc
    _ = L.scale * (1 / 2 : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hLe.1 L.hScale.le
  have haL : a ≤ 2 * L.scale :=
    (mul_le_mul_of_nonneg_left hLe.2.1 L.hScale.le).trans_eq (mul_comm _ _)
  have hbR₀ : R.scale / 2 ≤ b := calc
    _ = R.scale * (1 / 2 : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hRe.1 R.hScale.le
  have hbR : b ≤ 2 * R.scale :=
    (mul_le_mul_of_nonneg_left hRe.2.1 R.hScale.le).trans_eq (mul_comm _ _)
  have haLo' : aLo ≤ a :=
    (div_le_div_of_nonneg_right (G.factor_bounds side i).1 (by norm_num : (0 : ℝ) ≤ 2)).trans haL₀
  have ha : 0 < a := haLo.trans_le haLo'
  have hUp : 0 < U := lt_min L.hA R.hA
  have hell : 0 < ell := mul_pos (mul_pos hc ha) (pow_pos hUp 12)
  have hab : a < b := sub_pos.mp (by rw [hPlace]; exact hell)
  have haR : a ≤ 2 * R.scale := hab.le.trans hbR
  have hU₁ : U ≤ 1 := (min_le_left _ _).trans L.hA₁
  have hε : c * U ^ 12 ≤ 1 := calc
    _ ≤ (1 : ℝ) * 1 ^ 12 := mul_le_mul hc₁ (pow_le_pow_left₀ hUp.le hU₁ 12)
      (pow_nonneg hUp.le _) zero_le_one
    _ = _ := by norm_num
  have hmatch : b = a * (1 + c * U ^ 12) := calc
    _ = a + (b - a) := by ring
    _ = _ := by rw [hPlace]; dsimp only [ell]; ring
  have hb2 : b ≤ 2 * a := calc
    _ = a * (1 + c * U ^ 12) := hmatch
    _ ≤ a * 2 := mul_le_mul_of_nonneg_left (by linarith only [hε]) ha.le
    _ = _ := mul_comm _ _
  have haR₀ : R.scale / 4 ≤ a := by linarith only [hbR₀, hb2]
  have hAL : L.A ≤ 25 / (2 * (9 : ℝ) ^ 9) := morseSelected_A_small G i
  have hAR : R.A ≤ 25 / (2 * (9 : ℝ) ^ 9) := morseSelected_A_small G j
  have hLsmall : h < L.scale * morseJoinCollarWidth * (L.A ^ 5 / 200) :=
    morseSelected_quarter_lt ha.le hc₁ L.hScale L.hA (hAL.trans (by norm_num)) haL hUp.le (min_le_left _ _)
  have hRsmall : h < R.scale * morseJoinCollarWidth * (R.A ^ 5 / 200) :=
    morseSelected_quarter_lt ha.le hc₁ R.hScale R.hA (hAR.trans (by norm_num)) haR hUp.le (min_le_right _ _)
  have hLinc := morseSelected_scaled_increment L hxL.1.le hxL.2.le le_rfl
  have hRinc := morseSelected_scaled_increment R le_rfl hxR.1.le hxR.2.le
  have hLdiff : L.q - e = morseJoinCollarWidth := by
    change e + morseJoinCollarWidth - e = morseJoinCollarWidth
    ring
  have hRdiff : morseCellLeftCut - R.p = morseJoinCollarWidth := by
    change morseCellLeftCut - (morseCellLeftCut - morseJoinCollarWidth) = morseJoinCollarWidth
    ring
  rw [hLdiff] at hLinc
  rw [hRdiff] at hRinc
  have hLin : a + h < L.scale * L.radius L.q := by
    have he : L.scale * morseJoinCollarWidth * (L.A ^ 5 / 200) ≤ L.scale * L.radius L.q - a := hLinc
    linarith only [he, hLsmall]
  have hRin : R.scale * R.radius R.p < b - h := by
    have he : R.scale * morseJoinCollarWidth * (R.A ^ 5 / 200) ≤ b - R.scale * R.radius R.p := hRinc
    linarith only [he, hRsmall]
  have haIn : a ∈ L.image := morseSelected_scaled_mem L hxL
  have hbIn : b ∈ R.image := morseSelected_scaled_mem R hxR
  have hLsub : Icc a (a + h) ⊆ L.image := fun _ ht => ⟨haIn.1.trans_le ht.1, ht.2.trans_lt hLin⟩
  have hRsub : Icc (b - h) b ⊆ R.image := fun _ ht => ⟨hRin.trans_le ht.1, ht.2.trans_lt hbIn.2⟩
  have hLg (y : ℝ) (hy : y ∈ Icc a (a + h)) : P.leftLog =ᶠ[𝓝 y] L.logProfile :=
    P.left_germs y (by simpa only [hEnds.1, hCut] using hy)
  have hRg (y : ℝ) (hy : y ∈ Icc (b - h) b) : P.rightLog =ᶠ[𝓝 y] R.logProfile :=
    P.right_germs y (by simpa only [hEnds.2, hCut] using hy)
  have hFloorL (y : ℝ) (hy : y ∈ Icc a (a + h)) : 2 / a ≤ deriv P.leftLog y := by
    exact morseSelected_collar_logFloor G σ hσ side i ha
      (by linarith only [haL₀, L.hScale]) (hLsub hy) (hLg y hy) (Or.inr hy.1)
  have hFloorR (y : ℝ) (hy : y ∈ Icc (b - h) b) : 2 / a ≤ deriv P.rightLog y := by
    exact morseSelected_collar_logFloor G σ hσ side j ha haR₀
      (hRsub hy) (hRg y hy) (Or.inl hy.2)
  have hBudget : MorseJoinBudget a b h h (2 / a) P.leftLog P.rightLog := by
    simpa only [hEnds.1, hEnds.2, hCut] using P.budget
  have hvL := (G.model i).right_half e (right_mem_Icc.mpr (morseSelected_turn_le_end G i))
  have hAB := morseSelected_parameters G j
  have hvR := (G.model j).left_half morseCellLeftCut
    (left_mem_Icc.mpr (morseCellLeftCut_lt_rightTurn hAB.2 hAB.1).le)
  have hz' : z ∈ Icc a b := by simpa only [hEnds.1, hEnds.2] using hz
  have hJet := hbound T σ hσ hn hNn hNm hadj (G.d_exact n) (G.d_exact m) L R rfl rfl rfl rfl
    (G.factor_bounds side i).1 (G.factor_bounds side i).2 (G.factor_bounds side j).1 (G.factor_bounds side j).2
    hxL hxR ⟨hLe.1, hLe.2.1⟩ ⟨hRe.1, hRe.2.1⟩ hvL.2.2.2
    ⟨(G.model j).left_speed, hvR.2.2.2.2⟩ haLo' hPlace P.leftLog P.rightLog P.left_smooth P.right_smooth
    hLsub hRsub hLg hRg hFloorL hFloorR hBudget z hz'
  have hShape : morseChainChosenJoinProfile G σ hσ side k = morseJoinProfile a b h h P.leftLog P.rightLog := by
    unfold morseChainChosenJoinProfile morseChainProfileJoinShape
    rw [hEnds.1, hEnds.2, hCut]
  rw [← hShape] at hJet
  by_cases hside : side = true
  · have hnEq : n = T.index + k := by simp [n, i, morseChainJoinDeparture, hside]
    rw [hnEq] at hJet
    exact hJet.mono hC.le (by linarith only [hC])
  · have hfalse : side = false := by
      cases side
      · rfl
      · exact False.elim (hside rfl)
    have hnEq : n = (T.index + k) + 1 := by simp [n, i, morseChainJoinDeparture, hfalse, Nat.add_assoc]
    have hn' : 1 ≤ T.index + k := by have h := G.start_large; omega
    exact hJet.adjacent hn' (Or.inl hnEq) hC.le

private theorem morseSelected_jetBounds_of_germ {n s : ℕ} {C x : ℝ} {f g : ℝ → ℝ}
    (h : MorseChainJetBounds n s C g x) (he : f =ᶠ[𝓝 x] g) :
    MorseChainJetBounds n s C f x := by
  have hInv : f⁻¹ =ᶠ[𝓝 x] g⁻¹ := he.fun_comp (fun t : ℝ => t⁻¹)
  unfold MorseChainJetBounds at h ⊢
  simp only [morseSelected_radialJet_eq] at h ⊢
  rw [he.eq_of_nhds, he.iteratedDeriv_eq s, hInv.iteratedDeriv_eq s]
  exact h

private theorem morseSelected_abs_reflectedJet (s : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    |iteratedDeriv s (fun t => f (-t)) x| = |iteratedDeriv s f (-x)| := by
  rw [iteratedDeriv_comp_neg, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

private theorem morseSelected_jetBounds_reflect {n s : ℕ} {C x : ℝ} {f : ℝ → ℝ}
    (h : MorseChainJetBounds n s C f (-x)) :
    MorseChainJetBounds n s C (fun y => f (-y)) x := by
  have hInv : (fun y => f (-y))⁻¹ = fun y => (f⁻¹) (-y) := rfl
  unfold MorseChainJetBounds at h ⊢
  simpa only [morseSelected_radialJet_eq, hInv, morseSelected_abs_reflectedJet] using h

private theorem morseSelected_reflect_germ {x : ℝ} {f g : ℝ → ℝ} (h : f =ᶠ[𝓝 (-x)] g) :
    (fun y => f (-y)) =ᶠ[𝓝 x] fun y => g (-y) := by
  have ht : Tendsto (fun y : ℝ => -y) (𝓝 x) (𝓝 (-x)) :=
    continuous_neg.continuousAt
  exact h.comp_tendsto ht

/-- Fixed-order estimates on the exact chosen cut blocks on both tails.
The index is the outward block label, including on the reflected left tail. -/
theorem exists_morseChainSelectedBlock_jetBounds {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2),
      let D := morseChainSelectedProfileData G σ hσ
      (∀ k x, x ∈ Icc (D.left.enter k) (D.left.enter (k + 1)) →
        MorseChainJetBounds (T.index + k) s C (D.left.block k) x) ∧
      ∀ k x, x ∈ Icc (D.right.enter k) (D.right.enter (k + 1)) →
        MorseChainJetBounds (T.index + k) s C (D.right.block k) x := by
  obtain ⟨CM, hCM, hM⟩ := exists_morseChainChosenModel_jetBounds G s
  obtain ⟨CJ, hCJ, hJ⟩ := exists_morseChainChosenJoin_jetBounds G s
  let C := max CM CJ
  refine ⟨C, hCM.trans_le (le_max_left _ _), ?_⟩
  intro σ hσ
  let D := morseChainSelectedProfileData G σ hσ
  have hModel (side : Bool) (k : ℕ) (x : ℝ)
      (hx : x ∈ Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k)) :
      MorseChainJetBounds (T.index + k) s C (morseChainChosenModel G σ hσ side k) x :=
    (hM σ hσ side k x hx).mono hCM.le (le_max_left _ _)
  have hJoin (side : Bool) (k : ℕ) (x : ℝ)
      (hx : x ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))) :
      MorseChainJetBounds (T.index + k) s C (morseChainChosenJoinProfile G σ hσ side k) x :=
    (hJ σ hσ side k x hx).mono hCJ.le (le_max_right _ _)
  constructor
  · intro k x hx
    have hx₁ : -morseChainCellRightRadius T false k ≤ x := hx.1
    have hx₂ : x ≤ -morseChainCellRightRadius T false (k + 1) := hx.2
    rcases le_total x (D.left.leave k) with h | h
    · have h' : x ≤ -morseChainCellLeftRadius T false k := h
      have hxM : -x ∈ Icc (morseChainCellLeftRadius T false k) (morseChainCellRightRadius T false k) :=
        ⟨by simpa only [neg_neg] using neg_le_neg h', by simpa only [neg_neg] using neg_le_neg hx₁⟩
      have he : D.left.block k =ᶠ[𝓝 x] fun y => morseChainChosenModel G σ hσ false k (-y) :=
        morseGlueCut_eventually_left (D.left.meet k) h
      exact morseSelected_jetBounds_of_germ (morseSelected_jetBounds_reflect (hModel false k (-x) hxM)) he
    · have h' : -morseChainCellLeftRadius T false k ≤ x := h
      have hxJ : -x ∈ Icc (T.joinLeft false (T.index + k)) (T.joinRight false (T.index + k)) := by
        rw [(G.joins k).2.2.1, (G.joins k).2.2.2]
        change -x ∈ Icc (morseChainCellRightRadius T false (k + 1)) (morseChainCellLeftRadius T false k)
        exact ⟨by simpa only [neg_neg] using neg_le_neg hx₂, by simpa only [neg_neg] using neg_le_neg h'⟩
      have he : D.left.block k =ᶠ[𝓝 x] fun y => morseChainChosenJoinProfile G σ hσ false k (-y) :=
        morseGlueCut_eventually_right (D.left.meet k) h
      exact morseSelected_jetBounds_of_germ (morseSelected_jetBounds_reflect (hJoin false k (-x) hxJ)) he
  · intro k x hx
    rcases le_total x (D.right.leave k) with h | h
    · exact morseSelected_jetBounds_of_germ (hModel true k x ⟨hx.1, h⟩)
        (morseGlueCut_eventually_left (D.right.meet k) h)
    · have hxJ : x ∈ Icc (T.joinLeft true (T.index + k)) (T.joinRight true (T.index + k)) := by
        rw [(G.joins k).1, (G.joins k).2.1]
        exact ⟨h, hx.2⟩
      exact morseSelected_jetBounds_of_germ (hJoin true k x hxJ)
        (morseGlueCut_eventually_right (D.right.meet k) h)

private theorem morseSelected_cell_span {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    G.factorLo * ((9 / 10 : ℝ) * Statements.morseChainA T (T.index + k)) ≤
      morseChainCellRightRadius T side k - morseChainCellLeftRadius T side k := by
  let A := Statements.morseChainA T (T.index + k)
  have hA : 0 < A := (by positivity : 0 < exp (-((T.index + k : ℕ) : ℝ) ^ 2) / 3).trans_le
    (morseChainA_exp_bounds T (T.index + k) (G.d_exact _)).1
  rw [morseChainCellLeftRadius, morseChainCellRightRadius, G.leftX_eq, G.rightX_eq, G.radius_eq]
  dsimp only
  rw [← mul_sub]
  exact (mul_le_mul_of_nonneg_right (G.factor_bounds side k).1 (by positivity)).trans
    (mul_le_mul_of_nonneg_left (G.model k).span.1 (G.factor_pos side k).le)

private theorem morseSelected_tail_distance {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {endpoint : ℝ} (P : MorseOutwardProfileData endpoint)
    (hSpan : ∀ k, G.factorLo * ((9 / 10 : ℝ) * Statements.morseChainA T (T.index + k)) ≤
      P.leave k - P.enter k) (k : ℕ) (x : ℝ) (hx : x ∈ Icc (P.enter k) (P.enter (k + 1))) :
    (G.factorLo * (9 / 10 : ℝ) / 3) * exp (-(((T.index + k : ℕ) : ℝ) + 1) ^ 2) ≤ endpoint - x := by
  have hA := (morseChainA_exp_bounds T (T.index + (k + 1)) (G.d_exact _)).1
  have hcast : ((T.index + (k + 1) : ℕ) : ℝ) = ((T.index + k : ℕ) : ℝ) + 1 := by
    rw [← Nat.add_assoc, Nat.cast_add, Nat.cast_one]
  rw [hcast] at hA
  calc
    _ = G.factorLo * ((9 / 10 : ℝ) * (exp (-(((T.index + k : ℕ) : ℝ) + 1) ^ 2) / 3)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hA (by norm_num)) G.factorLo_pos.le).trans (hSpan (k + 1))
    _ ≤ _ := by linarith only [hx.2, (P.order (k + 1)).2, P.enter_lt_endpoint (k + 1 + 1)]

/-- The same actual glued profile is smooth on all of ℝ and has every
exterior jet zero, including the two accumulating physical endpoints. -/
theorem morseChainGluedProfile_flat {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    ContDiff ℝ ∞ (morseChainGluedProfile G σ hσ) ∧
      ∀ s x, x ≤ 1 ∨ G.rightEnd ≤ x → iteratedDeriv s (morseChainGluedProfile G σ hσ) x = 0 := by
  let D := morseChainSelectedProfileData G σ hσ
  let d := G.factorLo * (9 / 10 : ℝ) / 3
  have hd : 0 < d := div_pos (mul_pos G.factorLo_pos (by norm_num)) (by norm_num)
  have hL (k : ℕ) : G.factorLo * ((9 / 10 : ℝ) * Statements.morseChainA T (T.index + k)) ≤
      D.left.leave k - D.left.enter k := by
    change _ ≤ -morseChainCellLeftRadius T false k - -morseChainCellRightRadius T false k
    linarith only [morseSelected_cell_span G false k]
  have hR (k : ℕ) : G.factorLo * ((9 / 10 : ℝ) * Statements.morseChainA T (T.index + k)) ≤
      D.right.leave k - D.right.enter k := morseSelected_cell_span G true k
  have hLeft := D.left.flat_of_exp_bounds T.index hd (morseSelected_tail_distance G D.left hL) (by
    intro s
    obtain ⟨C, hC, hB⟩ := exists_morseChainSelectedBlock_jetBounds G s
    refine ⟨C, C, hC.le, fun k x hx => ?_⟩
    simpa only [morseSelected_radialJet_eq] using ((hB σ hσ).1 k x hx).2.2.1)
  have hRight := D.right.flat_of_exp_bounds T.index hd (morseSelected_tail_distance G D.right hR) (by
    intro s
    obtain ⟨C, hC, hB⟩ := exists_morseChainSelectedBlock_jetBounds G s
    refine ⟨C, C, hC.le, fun k x hx => ?_⟩
    simpa only [morseSelected_radialJet_eq] using ((hB σ hσ).2 k x hx).2.2.1)
  exact D.flat_of_tails hLeft.1 hRight.1 hLeft.2 hRight.2

/-- The physical profile has the estimates on the actual closed blocks
used in the statement layer. Reflection on the left changes the sign of
odd derivatives and preserves the absolute-value bounds. -/
theorem exists_morseChainGluedProfile_tail_jetBounds {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ)
      (x : ℝ), x ∈ Statements.morseChainBlock T side (T.index + k) →
        MorseChainJetBounds (T.index + k) s C (morseChainGluedProfile G σ hσ) x := by
  obtain ⟨C, hC, hB⟩ := exists_morseChainSelectedBlock_jetBounds G s
  refine ⟨C, hC, ?_⟩
  intro σ hσ side k x hx
  let D := morseChainSelectedProfileData G σ hσ
  change MorseChainJetBounds (T.index + k) s C D.profile x
  have hidx : T.index + k + 1 = T.index + (k + 1) := Nat.add_assoc _ _ _
  unfold Statements.morseChainBlock at hx
  rw [hidx] at hx
  cases side
  · change x ∈ uIcc (morseChainCellRightRadius T false k) (morseChainCellRightRadius T false (k + 1)) at hx
    have hn : -morseChainCellRightRadius T false k ≤ -morseChainCellRightRadius T false (k + 1) :=
      D.left.enter_strictMono.monotone (Nat.le_succ k)
    rw [uIcc_of_ge (le_of_neg_le_neg hn)] at hx
    have hx' : -x ∈ Icc (D.left.enter k) (D.left.enter (k + 1)) :=
      ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
    have hcut : x ≤ D.leftCut := by
      have h : D.left.enter 0 ≤ -x :=
        (D.left.enter_strictMono.monotone (Nat.zero_le k)).trans hx'.1
      simpa only [MorseTwoSidedProfileData.leftCut, neg_neg] using neg_le_neg h
    have hpiece : D.left.profile =ᶠ[𝓝 (-x)] D.left.block k :=
      morseOutwardGlue_eventually_piece D.left.enter_strictMono D.left.block_match hx'
    have hb : MorseChainJetBounds (T.index + k) s C (fun y => D.left.block k (-y)) x :=
      morseSelected_jetBounds_reflect ((hB σ hσ).1 k (-x) hx')
    exact morseSelected_jetBounds_of_germ hb ((D.eventually_left hcut).trans (morseSelected_reflect_germ hpiece))
  · change x ∈ uIcc (D.right.enter k) (D.right.enter (k + 1)) at hx
    rw [uIcc_of_le (D.right.enter_strictMono.monotone (Nat.le_succ k))] at hx
    have hcut : D.rightCut ≤ x := (D.right.enter_strictMono.monotone (Nat.zero_le k)).trans hx.1
    have hpiece : D.right.profile =ᶠ[𝓝 x] D.right.block k :=
      morseOutwardGlue_eventually_piece D.right.enter_strictMono D.right.block_match hx
    exact morseSelected_jetBounds_of_germ ((hB σ hσ).2 k x hx) ((D.eventually_right hcut).trans hpiece)

private theorem morseSelected_middle_abs_bound {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (s : ℕ) :
    ∃ K : ℝ, ∀ x ∈ Icc a b, |iteratedDeriv s f x| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    (hf.continuous_iteratedDeriv s (by simp)).continuousOn
  exact ⟨K, fun x hx => by simpa only [Real.norm_eq_abs] using hK x hx⟩

/-- Fixed-order middle jets, uniformly in all admissible height choices.
The single chosen unit bridge is multiplied by the actual head amplitude. -/
theorem exists_morseChainGluedProfile_middle_jetBounds {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (x : ℝ),
      x ∈ Icc (morseChainCellRightRadius T false 0) (morseChainCellLeftRadius T true 0) →
        MorseChainJetBounds T.index s C (morseChainGluedProfile G σ hσ) x := by
  let a := morseChainCellRightRadius T false 0
  let b := morseChainCellLeftRadius T true 0
  let u := morseChainMiddleUnit G
  have hu : ContDiff ℝ ∞ u ∧ ∀ x, 0 < u x :=
    let h := Classical.choose_spec (exists_morseChainMiddleUnit G)
    ⟨h.1, h.2.1⟩
  have hui : ContDiff ℝ ∞ (u⁻¹) := hu.1.inv (fun x => (hu.2 x).ne')
  obtain ⟨M₀, hM₀⟩ := morseSelected_middle_abs_bound (a := a) (b := b) hu.1 0
  obtain ⟨M₁, hM₁⟩ := morseSelected_middle_abs_bound (a := a) (b := b) hu.1 s
  obtain ⟨I₀, hI₀⟩ := morseSelected_middle_abs_bound (a := a) (b := b) hui 0
  obtain ⟨I₁, hI₁⟩ := morseSelected_middle_abs_bound (a := a) (b := b) hui s
  let M := max 1 (max (max M₀ M₁) (max I₀ I₁))
  have hM : 1 ≤ M := le_max_left _ _
  have hM₀' : M₀ ≤ M := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hM₁' : M₁ ≤ M := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hI₀' : I₀ ≤ M := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hI₁' : I₁ ≤ M := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  let p := (T.index : ℝ) ^ (5 / 2 : ℝ)
  let t := (T.index : ℝ) ^ 2
  let L := exp (-p)
  let U := L * (2 : ℝ) ^ (Finset.Icc T.index T.index).card
  let A := 1 + U + L⁻¹
  let K := A * M
  let C := 1 + K + K * exp p
  have hL : 0 < L := exp_pos _
  have hU : 0 ≤ U := mul_nonneg hL.le (by positivity)
  have hLi := (inv_pos.mpr hL).le
  have hA : 0 < A := by dsimp only [A]; linarith only [hU, hLi]
  have hK : 0 ≤ K := mul_nonneg hA.le (zero_le_one.trans hM)
  have hp : 0 ≤ p := Real.rpow_nonneg (Nat.cast_nonneg T.index) _
  have hCe : K * exp p ≤ C := by dsimp only [C]; linarith only [hK]
  have hCK : K ≤ C := by
    dsimp only [C]
    linarith only [mul_nonneg hK (exp_pos p).le]
  have hC : 0 < C := by
    dsimp only [C]
    linarith only [hK, mul_nonneg hK (exp_pos p).le]
  have hn : (1 : ℝ) ≤ T.index := by
    exact_mod_cast ((by norm_num : 1 ≤ 100).trans G.start_large)
  have ht : 1 ≤ t := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hn 2
  have hCt : C ≤ C * t := le_mul_of_one_le_right hC.le ht
  have hCe' : C ≤ exp (C * t) := hCt.trans ((le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _))
  have hCt₀ : 0 ≤ C * t := mul_nonneg hC.le (zero_le_one.trans ht)
  have hKexp : K ≤ C * exp (-p) := by
    have h := (le_div_iff₀ (exp_pos p)).mpr hCe
    simpa only [div_eq_mul_inv, exp_neg] using h
  refine ⟨C, hC, ?_⟩
  intro σ hσ x hx
  let lam := Statements.morseChainAmplitude T σ T.index
  let w := fun y => lam * u y
  have hlam : 0 < lam := morseChainAmplitude_pos T σ hσ T.index
  obtain ⟨hlo, hhi⟩ := morseChainAmplitude_bounds T σ hσ T.index
  have hhi' : lam ≤ U := hhi
  have hlo' : L ≤ lam := hlo
  have hLamBound : lam ≤ A := hhi'.trans (by dsimp only [A]; linarith only [hLi])
  have hLamInvBound : lam⁻¹ ≤ A := ((inv_le_inv₀ hlam hL).mpr hlo').trans
    (by dsimp only [A]; linarith only [hU])
  have hwpos : 0 < w x := mul_pos hlam (hu.2 x)
  have hMulInv : w⁻¹ = fun y => lam⁻¹ * (u⁻¹) y := by
    funext y
    change (lam * u y)⁻¹ = lam⁻¹ * (u y)⁻¹
    rw [mul_inv_rev, mul_comm]
  have hW₀ : w x ≤ K := by
    have h := (hM₀ x hx).trans hM₀'
    rw [iteratedDeriv_zero, abs_of_pos (hu.2 x)] at h
    exact mul_le_mul hLamBound h (hu.2 x).le hA.le
  have hI₀raw : (w x)⁻¹ ≤ K := by
    have h := (hI₀ x hx).trans hI₀'
    rw [iteratedDeriv_zero] at h
    change |(u x)⁻¹| ≤ M at h
    rw [abs_of_pos (inv_pos.mpr (hu.2 x))] at h
    change w⁻¹ x ≤ K
    rw [hMulInv]
    exact mul_le_mul hLamInvBound h (inv_nonneg.mpr (hu.2 x).le) hA.le
  have hW₁ : |iteratedDeriv s w x| ≤ K := by
    dsimp only [w]
    rw [iteratedDeriv_const_mul_field, abs_mul, abs_of_pos hlam]
    exact mul_le_mul hLamBound ((hM₁ x hx).trans hM₁') (abs_nonneg _) hA.le
  have hI₁raw : |iteratedDeriv s (w⁻¹) x| ≤ K := by
    rw [hMulInv, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (inv_pos.mpr hlam)]
    exact mul_le_mul hLamInvBound ((hI₁ x hx).trans hI₁') (abs_nonneg _) hA.le
  have hplus : 1 ≤ exp (p + C * t) := one_le_exp_iff.mpr (add_nonneg hp hCt₀)
  have hlow : exp (-p - C * t) ≤ w x := by
    apply (inv_le_inv₀ hwpos (exp_pos _)).mp
    rw [← exp_neg, show -(-p - C * t) = p + C * t by ring]
    exact hI₀raw.trans (hCK.trans (hCe'.trans (exp_le_exp.mpr (by linarith only [hp]))))
  have hhigh : w x ≤ exp (-p + C * t) := by
    rw [exp_add]
    exact hW₀.trans (hKexp.trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hCe' (exp_pos (-p)).le))
  have hExp : exp (-p) ≤ exp (-p + C * t) :=
    exp_le_exp.mpr (le_add_of_nonneg_right hCt₀)
  have hE : 1 ≤ Statements.radialE T.index :=
    one_le_exp_iff.mpr ((sq_nonneg (T.index : ℝ)).trans (radial_nat_sq_le_Q T.index))
  have hb : MorseChainJetBounds T.index s C w x := by
    unfold MorseChainJetBounds
    simp only [morseSelected_radialJet_eq]
    exact ⟨hlow, hhigh, hW₁.trans (hKexp.trans (mul_le_mul_of_nonneg_left hExp hC.le)),
      hI₁raw.trans (hCK.trans (le_mul_of_one_le_right hC.le hplus)),
      hI₁raw.trans (hCK.trans (le_mul_of_one_le_right hC.le (Real.one_le_rpow hE hC.le)))⟩
  exact morseSelected_jetBounds_of_germ hb (morseChainGluedProfile_middle_germ G σ hσ hx)

private theorem morseSelected_seam_widths {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    let s := morsePartitionSeam T side
    let h := morsePartitionWidth G side
    h k ≤ morseSeamPrevSpan s (morsePartitionMiddleSpan T) k / 16 ∧
      h k ≤ (s (k + 1) - s k) / 16 := by
  obtain ⟨hmR, hmL, _, _, hRc, hLc, hgap⟩ := morsePartitionSeam_data G
  have hmid : 0 < morsePartitionMiddleSpan T := hgap
  cases side
  · exact (morseSeamWidth_bounds hmid hmL hLc k).2.2.2
  · exact (morseSeamWidth_bounds hmid hmR hRc k).2.2.2

private theorem morseSelected_mem_block {T : Statements.MorseChainData} {side : Bool} {k : ℕ} {x : ℝ}
    (hs : StrictMono (morsePartitionSeam T side))
    (hx : morsePartitionOrientation side x ∈ Icc (morsePartitionSeam T side k)
      (morsePartitionSeam T side (k + 1))) :
    x ∈ Statements.morseChainBlock T side (T.index + k) := by
  let s := morsePartitionSeam T side
  have hq (j : ℕ) : Statements.morseChainSeam T side (T.index + j) =
      morsePartitionOrientation side (s j) := by
    cases side <;> simp [s, morsePartitionSeam, morsePartitionOrientation]
  unfold Statements.morseChainBlock
  rw [Nat.add_assoc, hq k, hq (k + 1)]
  cases side
  · have hle : -s (k + 1) ≤ -s k := neg_le_neg (hs (Nat.lt_succ_self k)).le
    change x ∈ uIcc (-s k) (-s (k + 1))
    change -x ∈ Icc (s k) (s (k + 1)) at hx
    rw [uIcc_of_ge hle]
    exact ⟨by linarith only [hx.2], by linarith only [hx.1]⟩
  · have hle : s k ≤ s (k + 1) := (hs (Nat.lt_succ_self k)).le
    change x ∈ uIcc (s k) (s (k + 1))
    rw [uIcc_of_le hle]
    exact hx

private theorem morseSelected_tail_window_split {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) {x : ℝ}
    (hx : x ∈ morsePartitionTailCell G side k) :
    x ∈ Statements.morseChainBlock T side (T.index + k) ∨
    x ∈ Statements.morseChainBlock T side (T.index + (k + 1)) ∨
    (∃ j, k = j + 1 ∧ x ∈ Statements.morseChainBlock T side (T.index + j)) ∨
    (k = 0 ∧ x ∈ Icc (morseChainCellRightRadius T false 0) (morseChainCellLeftRadius T true 0)) := by
  let s := morsePartitionSeam T side
  let h := morsePartitionWidth G side
  let y := morsePartitionOrientation side x
  let a := morseChainCellRightRadius T false 0
  let b := morseChainCellLeftRadius T true 0
  obtain ⟨hmR, hmL, _, _, _, _, hgap⟩ := morsePartitionSeam_data G
  have hs : StrictMono s := by
    cases side
    · exact hmL
    · exact hmR
  change y ∈ Ioo (s k - h k) (s (k + 1) + h (k + 1)) at hx
  by_cases hin : y < s k
  · cases k with
    | zero =>
        have hw : h 0 ≤ (b + -a) / 16 := (morseSelected_seam_widths G side 0).1
        have hab : 0 < b + -a := hgap
        have hLower := hx.1
        refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
        change x ∈ Icc a b
        cases side
        · change -x < -a at hin
          change -a - h 0 < -x at hLower
          exact ⟨by linarith only [hin], by linarith only [hLower, hw, hab]⟩
        · change x < b at hin
          change b - h 0 < x at hLower
          exact ⟨by linarith only [hLower, hw, hab], hin.le⟩
    | succ j =>
        have hw : h (j + 1) ≤ (s (j + 1) - s j) / 16 := (morseSelected_seam_widths G side (j + 1)).1
        have hj := (hs (Nat.lt_succ_self j)).le
        exact Or.inr (Or.inr (Or.inl ⟨j, rfl,
          morseSelected_mem_block hs ⟨by linarith only [hx.1, hw, hj], hin.le⟩⟩))
  · by_cases hout : y ≤ s (k + 1)
    · exact Or.inl (morseSelected_mem_block hs ⟨le_of_not_gt hin, hout⟩)
    · have hw := (morseSelected_seam_widths G side (k + 1)).2
      have hj := (hs (Nat.lt_succ_self (k + 1))).le
      exact Or.inr (Or.inl (morseSelected_mem_block hs
        ⟨le_of_not_ge hout, by linarith only [hx.2, hw, hj]⟩))

private theorem morseSelected_middle_window_split {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {x : ℝ} (hx : x ∈ morsePartitionMiddleCell G) :
    (x ∈ Icc (morseChainCellRightRadius T false 0) (morseChainCellLeftRadius T true 0)) ∨
      ∃ side : Bool, x ∈ Statements.morseChainBlock T side (T.index + 0) := by
  let a := morseChainCellRightRadius T false 0
  let b := morseChainCellLeftRadius T true 0
  obtain ⟨hmR, hmL, _, _, _, _, _⟩ := morsePartitionSeam_data G
  change x ∈ Ioo (-(morsePartitionSeam T false 0 + morsePartitionWidth G false 0))
    (morsePartitionSeam T true 0 + morsePartitionWidth G true 0) at hx
  by_cases hL : x < a
  · have hlo : morsePartitionSeam T false 0 ≤ -x := neg_le_neg hL.le
    have hw := (morseSelected_seam_widths G false 0).2
    have hhi : -x ≤ morsePartitionSeam T false 1 := by
      linarith only [hx.1, hw, (hmL (Nat.lt_succ_self 0)).le]
    exact Or.inr ⟨false, morseSelected_mem_block hmL ⟨hlo, hhi⟩⟩
  · by_cases hR : b < x
    · have hlo : morsePartitionSeam T true 0 ≤ x := hR.le
      have hw := (morseSelected_seam_widths G true 0).2
      have hhi : x ≤ morsePartitionSeam T true 1 := by
        linarith only [hx.2, hw, (hmR (Nat.lt_succ_self 0)).le]
      exact Or.inr ⟨true, morseSelected_mem_block hmR ⟨hlo, hhi⟩⟩
    · exact Or.inl ⟨le_of_not_gt hL, le_of_not_gt hR⟩

/-- All physical derivative bounds on the actual widened partition.
The constants depend on the geometry and derivative order and are uniform
over the admissible height sequences. The order zero result supplies the
height lower bound with the same zeroth constant. -/
theorem exists_morsePartitionReference_profile_jetBounds {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
      (phi chi chiLeft : ℝ → ℝ) (m : ℕ) (x : ℝ),
      let D := morsePartitionReference G (morseChainGluedProfile G σ hσ) phi chi chiLeft
      x ∈ D.cells m → MorseChainJetBounds (D.cellIndex m) s C D.w x := by
  obtain ⟨CT, hCT, hT⟩ := exists_morseChainGluedProfile_tail_jetBounds G s
  obtain ⟨CM, hCM, hM⟩ := exists_morseChainGluedProfile_middle_jetBounds G s
  let C := max CM (11 + 4 * CT)
  have hCM' : CM ≤ C := le_max_left _ _
  have hShift : 11 + 4 * CT ≤ C := le_max_right _ _
  have hCT' : CT ≤ C := (by linarith only [hCT] : CT ≤ 11 + 4 * CT).trans hShift
  have hShift₀ : 0 ≤ 11 + 4 * CT := by positivity
  refine ⟨C, hCM.trans_le hCM', ?_⟩
  intro σ hσ phi chi chiLeft m x
  dsimp only
  intro hx
  let w := morseChainGluedProfile G σ hσ
  have hn (k : ℕ) : 1 ≤ T.index + k :=
    ((by norm_num : 1 ≤ 100).trans G.start_large).trans (Nat.le_add_right _ _)
  cases m with
  | zero =>
      change x ∈ morsePartitionMiddleCell G at hx
      change MorseChainJetBounds T.index s C w x
      rcases morseSelected_middle_window_split G hx with h | ⟨side, h⟩
      · exact (hM σ hσ x h).mono hCM.le hCM'
      · simpa only [Nat.add_zero] using (hT σ hσ side 0 x h).mono hCT.le hCT'
  | succ m =>
      let q := Equiv.boolProdNatEquivNat.symm m
      change x ∈ morsePartitionTailCell G q.1 q.2 at hx
      change MorseChainJetBounds (T.index + q.2) s C w x
      rcases morseSelected_tail_window_split G q.1 q.2 hx with h | h | ⟨j, hj, h⟩ | ⟨hj, h⟩
      · exact (hT σ hσ q.1 q.2 x h).mono hCT.le hCT'
      · have he : T.index + (q.2 + 1) = T.index + q.2 + 1 := (Nat.add_assoc _ _ _).symm
        exact ((hT σ hσ q.1 (q.2 + 1) x h).adjacent (hn q.2) (Or.inl he) hCT.le).mono hShift₀ hShift
      · have he : T.index + q.2 = T.index + j + 1 := by rw [hj, Nat.add_assoc]
        exact ((hT σ hσ q.1 j x h).adjacent (hn q.2) (Or.inr he) hCT.le).mono hShift₀ hShift
      · rw [hj, Nat.add_zero]
        exact (hM σ hσ x h).mono hCM.le hCM'

end ContinuousFlexibility.Radial
