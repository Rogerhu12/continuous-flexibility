module

public import ContinuousFlexibility.Radial.R07MiddlePatch

/-!
# Uniform realization of a family with a replacement middle

The height sequence is still the actual sequence used on every Morse cell.
Only the finite middle is replaced. The fixed geometric partition and its
uniform jet estimates give one realization constant at every order for all
admissible height sequences. The already proved R05 mass-resistance theorem
then applies to that same family.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem r07_realization_replace_profile {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (w : ℝ → ℝ) (hAcc : AccumulatingProfileBounds {D with w := w} C)
    (hModel : ∀ side n, T.index ≤ n → ∀ X ∈ Icc (T.leftX side n) (T.rightX side n),
      w (T.radius side n X) = D.w (T.radius side n X))
    (hJoin : ∀ side n, T.index ≤ n → ∀ r ∈ Ioo (T.joinLeft side n) (T.joinRight side n),
      w =ᶠ[𝓝 r] D.w) :
    MorseChainRealization T σ {D with w := w} C := by
  rcases h with ⟨hi, hret, hrad, hj, hcore, hmid, hlim, hreg, hcover, _⟩
  refine ⟨hi, hret, ?_, ?_, hcore, hmid, hlim, hreg, hcover, hAcc⟩
  · intro side n hn
    obtain ⟨hs, ho, he⟩ := hrad side n hn
    refine ⟨hs, ho, fun X hX => ⟨(he X hX).1, (he X hX).2.1, ?_⟩⟩
    exact (hModel side n hn X hX).trans (he X hX).2.2
  · intro side n hn
    obtain ⟨ho, hl, hr, hwidth, hslope⟩ := hj side n hn
    refine ⟨ho, hl, hr, hwidth, fun r hr => ?_⟩
    have hg := hJoin side n hn r hr
    change 2 / r ≤ deriv w r / w r
    rw [hg.deriv_eq, hg.eq_of_nhds]
    exact hslope r hr

theorem r07MiddlePatchedProfile_model_germ {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {M : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k)) :
    r07MiddlePatchedProfile G M σ hσ =ᶠ[𝓝 x] morseChainGluedProfile G σ hσ := by
  apply (r07MiddlePatchedProfile_germs G hM σ hσ).1
  let P := morseChainSelectedProfileData G σ hσ
  cases side
  · have h : -morseChainCellRightRadius T false 0 ≤ -morseChainCellRightRadius T false k :=
      P.left.enter_strictMono.monotone (Nat.zero_le k)
    exact Or.inl (hx.2.trans (le_of_neg_le_neg h))
  · exact Or.inr ((P.right.enter_strictMono.monotone (Nat.zero_le k)).trans hx.1)

theorem r07MiddlePatchedProfile_join_germ {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {M : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))) :
    r07MiddlePatchedProfile G M σ hσ =ᶠ[𝓝 x] morseChainGluedProfile G σ hσ := by
  apply (r07MiddlePatchedProfile_germs G hM σ hσ).1
  let P := morseChainSelectedProfileData G σ hσ
  cases side
  · have h : -morseChainCellRightRadius T false 0 ≤ -morseChainCellRightRadius T false k :=
      P.left.enter_strictMono.monotone (Nat.zero_le k)
    rw [(G.joins k).2.2.2] at hx
    exact Or.inl (hx.2.trans ((morseChainCellLeftRadius_lt_right G false k).le.trans
      (le_of_neg_le_neg h)))
  · rw [(G.joins k).1] at hx
    exact Or.inr ((P.right.enter_strictMono.monotone (Nat.zero_le k)).trans
      ((morseChainCellLeftRadius_lt_right G true k).le.trans hx.1))

def r07MiddleReferenceFamily {T : MorseChainData} (G : MorseChainGeometryWitness T)
    (M phi : ℝ → ℝ) (σ : ℕ → ℝ) : ReferenceData := by
  classical
  exact morsePartitionReference G
    (if hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2 then r07MiddlePatchedProfile G M σ hσ else 0) phi 0 0

theorem r07MiddleReferenceFamily_admissible {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (M phi : ℝ → ℝ)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    r07MiddleReferenceFamily G M phi σ =
      morsePartitionReference G (r07MiddlePatchedProfile G M σ hσ) phi 0 0 := by
  simp only [r07MiddleReferenceFamily, dite_eq_left hσ]

theorem exists_r07MiddleReferenceFamily_constants {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {M phi : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    (hPhi : ContDiff ℝ ∞ phi ∧ (∀ x, x ≤ 1 ∨ G.rightEnd ≤ x → phi x = 0) ∧
      ∃ x ∈ Ioo 1 G.rightEnd, phi x ≠ 0) :
    ∃ C : ℕ → ℝ, ∀ σ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) →
      MorseChainRealization T σ (r07MiddleReferenceFamily G M phi σ) C ∧
      MorseMassResistanceBounds T σ (r07MiddleReferenceFamily G M phi σ) C := by
  classical
  obtain ⟨K, hK, hDist, hWidths⟩ := morsePartitionReference_geometry_bounds G 0 phi 0 0
  choose J hJ hJets using exists_morsePartitionReference_profile_jetBounds G
  choose P hP hPJets using exists_r07MiddlePatchedProfile_jetBounds G hM
  let C : ℕ → ℝ := fun s => max (J s) (max (P s) (max K G.rightEnd))
  have hJC (s : ℕ) : J s ≤ C s := le_max_left _ _
  have hPC (s : ℕ) : P s ≤ C s := (le_max_left _ _).trans (le_max_right _ _)
  have hKC : K ≤ C 0 := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hWC : G.rightEnd ≤ C 0 :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hC (s : ℕ) : 0 < C s := (hJ s).trans_le (hJC s)
  have hInv : (C 0)⁻¹ ≤ K⁻¹ := inv_anti₀ hK hKC
  apply exists_morseChainMassResistanceConstants T C (r07MiddleReferenceFamily G M phi)
  intro σ hσ
  rw [r07MiddleReferenceFamily_admissible G M phi σ hσ]
  let w₀ := morseChainGluedProfile G σ hσ
  let w := r07MiddlePatchedProfile G M σ hσ
  let D := morsePartitionReference G w₀ phi 0 0
  have hOld : MorseChainRealization T σ D C := by
    apply morseChainReference_realization G σ hσ phi 0 0 C hC hWC hPhi
      (morseChainGluedProfile_flat G σ hσ).1
    · intro m r hr
      obtain ⟨hl, hu⟩ := hDist m r hr
      exact ⟨(mul_le_mul_of_nonneg_right hInv (exp_pos _).le).trans hl,
        hu.trans (mul_le_mul_of_nonneg_right hKC (exp_pos _).le)⟩
    · intro m
      obtain ⟨l, h, hsub, hlen⟩ := hWidths m
      exact ⟨l, h, hsub, hlen.trans (mul_le_mul_of_nonneg_right hKC (exp_pos _).le)⟩
    · intro m r hr s
      exact (hJets s σ hσ phi 0 0 m r hr).mono (hJ s).le (hJC s)
  have hAcc : AccumulatingProfileBounds {D with w := w} C := by
    obtain ⟨_, hp, hc, hne, hfin, hloc, hdist, _, _, _, hwidth, hscale, htrace⟩ := hOld.accumulating
    refine ⟨r07MiddlePatchedProfile_geometry G hM σ hσ phi 0 0 hPhi,
      hp, hc, hne, hfin, hloc, hdist, ?_, ?_, ?_, hwidth, hscale, htrace⟩
    · intro m r hr
      exact ((hPJets 0 σ hσ phi 0 0 m r hr).mono (hP 0).le (hPC 0)).1
    · intro m r hr s
      exact ((hPJets s σ hσ phi 0 0 m r hr).mono (hP s).le (hPC s)).2.2.1
    · intro m r hr s
      exact ((hPJets s σ hσ phi 0 0 m r hr).mono (hP s).le (hPC s)).2.2.2.2
  apply r07_realization_replace_profile hOld w hAcc
  · intro side n hn X hX
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hEq := G.actual_radius_equation side k
    have hmono := (morseCell_strictMonoOn hEq.1 (fun t ht => (hEq.2.2 t ht).1)).monotoneOn
    have hmem : T.radius side (T.index + k) X ∈
        Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k) :=
      ⟨hmono (left_mem_Icc.mpr hEq.2.1.le) hX hX.1,
        hmono hX (right_mem_Icc.mpr hEq.2.1.le) hX.2⟩
    exact (r07MiddlePatchedProfile_model_germ G hM σ hσ side k hmem).eq_of_nhds
  · intro side n hn r hr
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact r07MiddlePatchedProfile_join_germ G hM σ hσ side k (Ioo_subset_Icc_self hr)

end ContinuousFlexibility.Radial
