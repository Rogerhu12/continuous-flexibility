import ContinuousFlexibility.Radial.MatchedOuterUniformCore
import ContinuousFlexibility.Radial.MatchedOuterLocalizerBounds
import ContinuousFlexibility.Radial.MatchedOuterModalCells
import ContinuousFlexibility.Radial.OuterStateScaleEnvelope

/-!
# The same matching-normalized natural column on the whole outer region

The actual pair is unit normalized at its actual core entrance. Its
natural component is divided by the physical square-root state scale,
exactly as in the matching traces. Core points and deep points are
estimated separately, using their true localizer labels.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology

/-- The reciprocal square-root normalization has the same fixed
coefficient envelope as the already proved reciprocal state scale. -/
theorem matchedOuter_stateScale_sqrt_inv_le
    (M : MorseChainData) (σ : ℕ → ℝ) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    {N : ℕ} (hN : 1 ≤ N) {lam L : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hscale : morseChainAmplitude M σ N / lam ≤ exp (L * (N : ℝ) ^ 2)) :
    (sqrt lam)⁻¹ ≤ exp ((L + 1) * radialQ N) := by
  have hi := outer_stateScale_inv_le M σ hσ hN hlam hL hscale
  rw [outer_radialE_rpow] at hi
  have hone : 1 ≤ exp ((L + 1) * radialQ N) :=
    one_le_exp_iff.mpr (mul_nonneg (by linarith only [hL]) (radialQ_nonneg N))
  calc
    _ = sqrt (lam⁻¹) := (sqrt_inv lam).symm
    _ ≤ sqrt (exp ((L + 1) * radialQ N)) := sqrt_le_sqrt hi
    _ ≤ _ := sqrt_le_iff.mpr ⟨(exp_pos _).le, by nlinarith only [hone]⟩

/-- The constant and exponent precede all heights, frequencies, scales,
and actual columns. The supplied vector remains unchanged, with its
matching normalization expressed by its actual representative. -/
theorem exists_matchedMorse_uniform_actual_natural_column_bound
    {M : MorseChainData} {C : ℕ → ℝ}
    {family : (ℕ → ℝ) → ReferenceData} {Cstar η K L : ℝ}
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization M σ (family σ) C ∧
        MorseMassResistanceBounds M σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧
      (family σ).b = (family τ).b)
    (hCstar : 0 < Cstar) (hη0 : 0 < η) (hη : η ≤ 1 / 16)
    (hK : 32 ≤ K) (hL : 0 ≤ L) (minimum : ℕ) :
    ∃ C₁ A : ℝ, 0 < C₁ ∧ 0 < A ∧
      ∃ N₀ : ℕ, minimum ≤ N₀ ∧ M.index + 3 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
      ∀ σ (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2),
      ∀ j : ℕ, 2 ≤ j → (j : ℝ) < radialFrequencyThreshold M Cstar N →
      ∀ entry : ℝ, entry ∈ morseInitialMiddle M →
      ∀ (right : Bool) (lam : ℝ), 0 < lam →
        lam / morseChainAmplitude M σ N ≤ exp (L * (N : ℝ) ^ 2) →
        morseChainAmplitude M σ N / lam ≤ exp (L * (N : ℝ) ^ 2) →
      ∀ (F : MorsePhysicalTailBasis M (family σ) right j (N + 1)
          (morseOuterDeepEntrance M right N) η K)
        (H : OuterFundamentalStatePair
          (fun x => lam / outerTailOutwardWeight (family σ) right x)
          (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight (family σ) right) x /
            (lam * x))
          F.P (F.ZP lam) F.Q (F.ZQ lam)
          (morseTransitionOutwardLeft M entry right N)
          (morseTransitionOutwardRight M entry right N)
          (outerOutwardRadius right (tailPhysicalEndpoint (family σ) right))),
        let D := family σ
        let hP := (hfamily σ hσ).1.accumulating.2.1
        let μ := outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right N)
        ∀ U : Lp ℝ 2 μ,
          (U : ℝ → ℝ) =ᵐ[μ] (fun x => H.V x / sqrt lam) →
        ∀ m : ℕ, ‖matchedOuterCell D hP right μ m U‖ ≤
          C₁ * exp (A * (radialQ (D.cellIndex m) + radialQ N) -
            |radialS (D.cellIndex m) - radialS N|) := by
  let σ₀ : ℕ → ℝ := fun _ => 1
  have h₀ := (hfamily σ₀ (fun _ => ⟨le_rfl, by norm_num [σ₀]⟩)).1
  have hC0 := h₀.constants_pos 0
  have ha : 0 < (family σ₀).a := h₀.geometry.1
  have hab : (family σ₀).a < (family σ₀).b := h₀.geometry.2.1
  obtain ⟨Ac, hAc, hcore⟩ := exists_matchedMorse_uniform_actual_core_pair_bound
    (fun σ hσ => (hfamily σ hσ).1) hends hCstar hL
  obtain ⟨Ad, hAd, Np, hNmin, hNidx, hN31, hprod⟩ :=
    outer_exists_uniform_actual_deepTailProduct M C family hfamily hends hCstar
      hη0 (by linarith only [hη]) (by linarith only [hK])
      (max minimum (M.index + 3))
  obtain ⟨Nl, hlabels⟩ := eventually_atTop.mp
    (morseOuter_eventually_uniform_localizer_labels M C family
      (fun σ hσ => (hfamily σ hσ).1) hends)
  obtain ⟨An, hAn, hnatural⟩ :=
    exists_matchedOuter_actual_tail_natural_cell_exponent hAd.le
  let B := Ac + (L + 1)
  have hB : 0 ≤ B := by dsimp only [B]; linarith only [hAc, hL]
  obtain ⟨As, hAs, hshift⟩ := outer_localized_envelope_shift hB
  let A := As + An + B + 1
  have hA : 0 < A := by dsimp only [A]; linarith only [hAs, hAn, hB]
  have hAsA : As ≤ A := by dsimp only [A]; linarith only [hAn, hB]
  have hAnA : An ≤ A := by dsimp only [A]; linarith only [hAs, hB]
  have hAnBA : An + B ≤ A := by dsimp only [A]; linarith only [hAs]
  let mass := 12 * C 0 * exp ((C 0) ^ 5) *
    ((family σ₀).b - (family σ₀).a) / (family σ₀).a ^ 2
  let C₁ := 1 + sqrt mass
  let N₀ := max Np Nl
  have hC₁ : 0 < C₁ := by dsimp only [C₁]; positivity
  refine ⟨C₁, A, hC₁, hA, N₀, by dsimp only [N₀]; omega,
    by dsimp only [N₀]; omega, ?_⟩
  intro N hN σ hσ j hj hupper entry he right lam hlam hhi hlo F H
  dsimp only
  intro U hU m
  let D := family σ
  let a := morseTransitionOutwardLeft M entry right N
  let c := morseTransitionOutwardRight M entry right N
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  let μ := outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right N)
  have h := (hfamily σ hσ).1
  have hPN : Np ≤ N := (le_max_left Np Nl).trans hN
  have hLN : Nl ≤ N := (le_max_right Np Nl).trans hN
  have hNlarge : M.index + 3 ≤ N := by omega
  have hNstrict : M.index < N := by omega
  have hne : N ≠ M.index := Nat.ne_of_gt hNstrict
  have hdata := hprod N hPN σ hσ j hj hupper right
  have hlabel := (hlabels N hLN).2 σ hσ
  have hi := morseTransitionOutward_interval h he right N hNstrict.le
  have hac : a ≤ c := hi.1.le
  have hcb : c < b := hi.2
  have hphys := morseTransitionPhysicalEntry_mem_core h he right N hNstrict.le
  letI : IsFiniteMeasure μ :=
    outerWholeMeasure_isFinite ⟨C, h.accumulating⟩ right
      (morseTransitionPhysicalEntry M entry right N)
  have hμmass : (measureUnivNNReal μ : ℝ) ≤ mass := by
    change μ.real univ ≤ mass
    have hh := outerWholeMeasure_mass_bound h.accumulating right
      (morseTransitionPhysicalEntry M entry right N)
    rw [(hends σ σ₀).1, (hends σ σ₀).2] at hh
    exact hh
  have hμmem : ∀ᵐ x ∂μ, x ∈ Ico a b := by
    have hh := outerWholeMeasure_ae_mem hphys
    rw [← morseTransitionOutwardLeft_eq] at hh
    exact hh.mono fun _ hx => Ioo_subset_Ico_self hx
  have hnorm := matchedOuter_stateScale_sqrt_inv_le M σ hσ (by omega : 1 ≤ N)
    hlam hL hlo
  have hHcore := hcore σ hσ entry he right N j hNstrict hupper lam hlam hhi hlo
    b F.P (F.ZP lam) F.Q (F.ZQ lam) H hcb
  have hVc : |H.V c| ≤ exp (Ac * radialQ N) :=
    (hHcore c (right_mem_Icc.mpr hac)).2.2.1
  have hPc : F.P c = 1 := by
    dsimp only [c]
    rw [morseTransitionOutwardRight_eq, outerOutwardRadius_eq_sign]
    exact F.P_entrance
  let E := exp (A * (radialQ (D.cellIndex m) + radialQ N) -
    |radialS (D.cellIndex m) - radialS N|)
  have hpoint : ∀ᵐ x ∂μ, D.localizer m (outerOutwardRadius right x) ≠ 0 →
      |H.V x / sqrt lam| ≤ E := by
    filter_upwards [hμmem] with x hx
    intro hθ
    rw [abs_div, abs_of_nonneg (sqrt_nonneg lam), div_eq_mul_inv]
    by_cases hxc : x ≤ c
    · have hxcore : x ∈ Icc a c := ⟨hx.1, hxc⟩
      have hV := (hHcore x hxcore).2.2.1
      have hrad : outerOutwardRadius right x ∈
          Icc (morseOuterCoreLeft M right N) (morseOuterFullCoreRight M right N) := by
        apply (outerOutwardRadius_mem_core_interval right _ _ x).mpr
        simpa only [a, c, morseTransitionOutwardLeft, morseTransitionOutwardRight,
          morseTransitionCoreLeft, morseTransitionCoreRight, if_neg hne] using hxcore
      have hnear := hlabel.2.2 right m _ hrad hθ
      have hraw : |H.V x| * (sqrt lam)⁻¹ ≤ radialE N ^ B := by
        refine (mul_le_mul hV hnorm (inv_nonneg.mpr (sqrt_nonneg lam))
          (exp_pos _).le).trans_eq ?_
        rw [outer_radialE_rpow, ← exp_add]
        congr 1 <;> dsimp only [B] <;> ring
      have hp := le_mul_of_one_le_right
        (rpow_nonneg (show 0 ≤ radialE N from (exp_pos _).le) B)
        (outer_envelope_one_le N hB)
      have hs := hshift N N (D.cellIndex m) N
        (by omega) (by omega) (by omega) (by omega)
        hnear.1 hnear.2 (by omega) (by omega)
      simp only [sub_self, abs_zero, neg_zero, exp_zero, mul_one] at hs
      have hs' : radialE N ^ B * radialE N ^ B ≤
          exp (As * (radialQ (D.cellIndex m) + radialQ N) -
            |radialS (D.cellIndex m) - radialS N|) := by
        convert hs using 1
        rw [outer_radialE_rpow, outer_radialE_rpow, ← exp_add, ← exp_add]
        congr 1 <;> ring
      exact (hraw.trans (hp.trans hs')).trans
        (exp_le_exp.mpr (sub_le_sub_right
          (mul_le_mul_of_nonneg_right hAsA
            (add_nonneg (radialQ_nonneg _) (radialQ_nonneg _))) _))
    · have hxtail : x ∈ Ico c b := ⟨(lt_of_not_ge hxc).le, hx.2⟩
      have hxdeep : x ∈ Ico (outerOutwardRadius right (morseOuterDeepEntrance M right N)) b := by
        simpa only [c, morseTransitionOutwardRight_eq] using hxtail
      have hPbound := hnatural M σ D C h N hNlarge hlabel right j η K F
        hdata.2.1 hη hK hj hdata.2.2.1 hdata.1 hdata.2.2.2 m x hxdeep hθ
      rw [H.V_tail_factor hcb hPc x hxtail, abs_mul]
      calc
        _ ≤ (exp (Ac * radialQ N) *
            exp (An * (radialQ (D.cellIndex m) + radialQ N) -
              |radialS (D.cellIndex m) - radialS N|)) *
              exp ((L + 1) * radialQ N) :=
          mul_le_mul (mul_le_mul hVc hPbound (abs_nonneg _) (exp_pos _).le)
            hnorm (inv_nonneg.mpr (sqrt_nonneg lam)) (by positivity)
        _ = exp (An * radialQ (D.cellIndex m) + (An + B) * radialQ N -
              |radialS (D.cellIndex m) - radialS N|) := by
          rw [← exp_add, ← exp_add]
          congr 1 <;> dsimp only [B] <;> ring
        _ ≤ E := by
          apply exp_le_exp.mpr
          have h₁ := mul_le_mul_of_nonneg_right hAnA (radialQ_nonneg (D.cellIndex m))
          have h₂ := mul_le_mul_of_nonneg_right hAnBA (radialQ_nonneg N)
          dsimp only [E]
          nlinarith only [h₁, h₂]
  have hbound := matchedOuterCell_norm_le_of_value h.accumulating.2.1 right μ U
    (fun x => H.V x / sqrt lam) hU m (exp_pos _).le hpoint
  exact hbound.trans (mul_le_mul_of_nonneg_right
    ((sqrt_le_sqrt hμmass).trans (by dsimp only [C₁]; linarith)) (exp_pos _).le)

end ContinuousFlexibility.Radial
