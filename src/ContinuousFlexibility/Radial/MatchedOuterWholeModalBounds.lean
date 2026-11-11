import ContinuousFlexibility.Radial.MatchedOuterKernelAlgebra
import ContinuousFlexibility.Radial.MatchedOuterUniformCore
import ContinuousFlexibility.Radial.MatchedOuterLocalizerBounds
import ContinuousFlexibility.Radial.MatchedOuterModalCells
import ContinuousFlexibility.Radial.OuterStateScaleEnvelope
import ContinuousFlexibility.Radial.OuterGreenAssembly

/-!
# Uniform cell bounds for the actual whole outer Green operator

The core, mixed and deep regions use the same normalized fundamental
pair.  The determinant gives the deep rank-one correction exactly.
The common constants precede the height, frequency, scale and supplied
operator, whose all-source integral identity is retained.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ENNReal

/-- Row measurability is a consequence of the actual value/flux ODE. -/
theorem matchedOuter_actual_whole_row_measurable
    {a c b lam : ℝ} {alpha beta P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    (ρ : ℝ → ℝ≥0∞) {x : ℝ} (hx : x ∈ Ico a b) :
    AEStronglyMeasurable (outerGreenKernel lam H.U H.V x)
      ((volume.restrict (Ioo a b)).withDensity ρ) := by
  have hU : ContinuousOn (fun y => H.U (min x y)) (Ioo a b) :=
    H.U_system.continuousOn.1.comp (continuous_const.min continuous_id).continuousOn
      (fun y hy => ⟨le_min hx.1 hy.1.le, (min_le_left _ _).trans_lt hx.2⟩)
  have hV : ContinuousOn (fun y => H.V (max x y)) (Ioo a b) :=
    H.V_system.continuousOn.1.comp (continuous_const.max continuous_id).continuousOn
      (fun y hy => ⟨hx.1.trans (le_max_left _ _), max_lt hx.2 hy.2⟩)
  have hκ : ContinuousOn (outerGreenKernel lam H.U H.V x) (Ioo a b) :=
    continuousOn_const.mul (hU.mul hV)
  exact (hκ.aestronglyMeasurable measurableSet_Ioo).mono_ac
    (withDensity_absolutelyContinuous _ _)

/-- The full kernel and supplied operator share one spatial cell envelope.
Only the actual all-source Green identity is required of the supplied
operator; no bound on that operator is a hypothesis. -/
theorem exists_matchedMorse_uniform_actual_whole_modal_bounds
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
        (∀ (k m : ℕ) (x y : ℝ),
          x ∈ Ico (morseTransitionOutwardLeft M entry right N)
            (outerOutwardRadius right (tailPhysicalEndpoint D right)) →
          y ∈ Ico (morseTransitionOutwardLeft M entry right N)
            (outerOutwardRadius right (tailPhysicalEndpoint D right)) →
          D.localizer k (outerOutwardRadius right x) ≠ 0 →
          D.localizer m (outerOutwardRadius right y) ≠ 0 →
          |outerGreenKernel lam H.U H.V x y| ≤
            2 * exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
              |radialS (D.cellIndex k) - radialS (D.cellIndex m)|)) ∧
        ∀ R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
          (∀ f : Lp ℝ 2 μ, (R f : ℝ → ℝ) =ᵐ[μ] fun x =>
            ∫ y, outerGreenKernel lam H.U H.V x y * f y ∂μ) →
        ∀ k m : ℕ,
          ‖(matchedOuterCell D hP right μ k).comp
            (R.comp (matchedOuterCell D hP right μ m))‖ ≤
              C₁ * exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
                |radialS (D.cellIndex k) - radialS (D.cellIndex m)|) := by
  let σ₀ : ℕ → ℝ := fun _ => 1
  have h₀ := (hfamily σ₀ (fun _ => ⟨le_rfl, by norm_num [σ₀]⟩)).1
  have hC0 := h₀.constants_pos 0
  have ha : 0 < (family σ₀).a := h₀.geometry.1
  have hab : (family σ₀).a < (family σ₀).b := h₀.geometry.2.1
  have hb := ha.trans hab
  obtain ⟨Ac, hAc, hcore⟩ := exists_matchedMorse_uniform_actual_core_pair_bound
    (fun σ hσ => (hfamily σ hσ).1) hends hCstar hL
  obtain ⟨Ad, hAd, Np, hNmin, hNidx, hN31, hprod⟩ :=
    outer_exists_uniform_actual_deepTailProduct M C family hfamily hends hCstar
      hη0 (by linarith only [hη]) (by linarith only [hK])
      (max minimum (M.index + 3))
  obtain ⟨Nl, hlabels⟩ := eventually_atTop.mp
    (morseOuter_eventually_uniform_localizer_labels M C family
      (fun σ hσ => (hfamily σ hσ).1) hends)
  obtain ⟨Ak, hAk, hkernel⟩ :=
    exists_matchedOuter_actual_tail_kernel_cell_exponent hC0 hb hAd.le
  obtain ⟨An, hAn, hnatural⟩ :=
    exists_matchedOuter_actual_tail_natural_cell_exponent hAd.le
  let B₀ := 2 * Ac + (L + 1)
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; linarith only [hAc, hL]
  obtain ⟨A, hA, halgebra⟩ :=
    exists_matchedOuter_whole_kernel_exponent hB₀ hAn.le hAk.le
  let mass := 12 * C 0 * exp ((C 0) ^ 5) *
    ((family σ₀).b - (family σ₀).a) / (family σ₀).a ^ 2
  let C₁ := 2 + 2 * mass
  let N₀ := max Np Nl
  have hmass : 0 < mass := by dsimp only [mass]; positivity
  have hC₁ : 0 < C₁ := by dsimp only [C₁]; positivity
  refine ⟨C₁, A, hC₁, hA, N₀, by dsimp only [N₀]; omega,
    by dsimp only [N₀]; omega, ?_⟩
  intro N hN σ hσ j hj hupper entry he right lam hlam hhi hlo F H
  dsimp only
  let D := family σ
  let a := morseTransitionOutwardLeft M entry right N
  let c := morseTransitionOutwardRight M entry right N
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  let μ := outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right N)
  let E := fun k m : ℕ => exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
    |radialS (D.cellIndex k) - radialS (D.cellIndex m)|)
  let En := fun m : ℕ => exp (An * (radialQ (D.cellIndex m) + radialQ N) -
    |radialS (D.cellIndex m) - radialS N|)
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
  have hdeep := morseOuterDeepEntrance_mem_core h right N hNstrict.le
  have hdeepPos : 0 < morseOuterDeepEntrance M right N := h.geometry.1.trans hdeep.1
  have hHcore := hcore σ hσ entry he right N j hNstrict hupper lam hlam hhi hlo
    b F.P (F.ZP lam) F.Q (F.ZQ lam) H hcb
  have hscale := outer_stateScale_inv_le M σ hσ (by omega : 1 ≤ N) hlam hL hlo
  rw [outer_radialE_rpow] at hscale
  have hPc : F.P c = 1 := by
    dsimp only [c]
    rw [morseTransitionOutwardRight_eq, outerOutwardRadius_eq_sign]
    exact F.P_entrance
  have hQc : F.Q c = 0 := by
    dsimp only [c]
    rw [morseTransitionOutwardRight_eq, outerOutwardRadius_eq_sign]
    exact F.Q_entrance
  have hflux : F.ZQ lam c = 1 / lam := by
    dsimp only [c]
    rw [morseTransitionOutwardRight_eq, outerOutwardRadius_eq_sign]
    exact F.ZQ_entrance lam
  have hcoreLabel (m : ℕ) (x : ℝ) (hx : x ∈ Icc a c)
      (hθ : D.localizer m (outerOutwardRadius right x) ≠ 0) :
      N ≤ D.cellIndex m + 2 ∧ D.cellIndex m ≤ N + 2 := by
    have hr : outerOutwardRadius right x ∈
        Icc (morseOuterCoreLeft M right N) (morseOuterFullCoreRight M right N) := by
      apply (outerOutwardRadius_mem_core_interval right _ _ x).mpr
      simpa only [a, c, morseTransitionOutwardLeft, morseTransitionOutwardRight,
        morseTransitionCoreLeft, morseTransitionCoreRight, if_neg hne] using hx
    exact hlabel.2.2 right m _ hr hθ
  have htailLabel (m : ℕ) (x : ℝ) (hx : x ∈ Ico c b)
      (hθ : D.localizer m (outerOutwardRadius right x) ≠ 0) :
      N ≤ D.cellIndex m + 2 := by
    have hx' : x ∈ Ico (outerOutwardRadius right (morseOuterDeepEntrance M right N)) b := by
      simpa only [c, morseTransitionOutwardRight_eq] using hx
    have hc := matchedOuter_tail_point_coordinates h.geometry right hdeepPos hx'
    obtain ⟨p, hp⟩ := exists_outerTailPoint hdata.2.1 hc.2.1
    have hh := hlabel.tail_point right j η K p m _ hp (by
      rw [tailPhysicalRadius_log right hc.1]
      exact hθ)
    change N ≤ (family σ).cellIndex m + 2
    omega
  have hlevel (m : ℕ) (x : ℝ) (hx : x ∈ Ico a b)
      (hθ : D.localizer m (outerOutwardRadius right x) ≠ 0) :
      1 ≤ D.cellIndex m := by
    by_cases hxc : x ≤ c
    · have hh := (hcoreLabel m x ⟨hx.1, hxc⟩ hθ).1
      omega
    · have hh := htailLabel m x ⟨(lt_of_not_ge hxc).le, hx.2⟩ hθ
      omega
  have hPbound (m : ℕ) (x : ℝ) (hx : x ∈ Ico c b)
      (hθ : D.localizer m (outerOutwardRadius right x) ≠ 0) : |F.P x| ≤ En m := by
    exact hnatural M σ D C h N hNlarge hlabel right j η K F
      hdata.2.1 hη hK hj hdata.2.2.1 hdata.1 hdata.2.2.2 m x
      (by simpa only [c, morseTransitionOutwardRight_eq] using hx) hθ
  have hcoreProduct (u v : ℝ) (hu : u ∈ Icc a c) (hv : v ∈ Icc a c) :
      |lam⁻¹ * (H.U u * H.V v)| ≤ exp (B₀ * radialQ N) := by
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hlam)]
    calc
      _ ≤ exp ((L + 1) * radialQ N) *
          (exp (Ac * radialQ N) * exp (Ac * radialQ N)) :=
        mul_le_mul hscale
          (mul_le_mul (hHcore u hu).1 (hHcore v hv).2.2.1
            (abs_nonneg _) (exp_pos _).le)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (exp_pos _).le
      _ = _ := by
        rw [← exp_add, ← exp_add]
        congr 1 <;> dsimp only [B₀] <;> ring
  have hdiag : |outerGreenKernel lam H.U H.V c c| ≤ exp (B₀ * radialQ N) := by
    rw [outerGreenKernel_self]
    exact hcoreProduct c c (right_mem_Icc.mpr hac) (right_mem_Icc.mpr hac)
  have hcross (k m : ℕ) (x y : ℝ) (hx : x ∈ Icc a c) (hy : y ∈ Ico c b)
      (hθk : D.localizer k (outerOutwardRadius right x) ≠ 0)
      (hθm : D.localizer m (outerOutwardRadius right y) ≠ 0) :
      |outerGreenKernel lam H.U H.V x y| ≤ E k m := by
    have hxw : x ∈ Ico a b := ⟨hx.1, hx.2.trans_lt hcb⟩
    have hyw : y ∈ Ico a b := ⟨hac.trans hy.1, hy.2⟩
    have hnear := hcoreLabel k x hx hθk
    have hnum := (halgebra N (D.cellIndex k) (D.cellIndex m) (by omega)
      (hlevel k x hxw hθk) (hlevel m y hyw hθm)).2.1 hnear.1 hnear.2
    rw [H.kernel_core_tail hcb hPc hx hy, abs_mul]
    have hc : |(H.V c / lam) * H.U x| ≤ exp (B₀ * radialQ N) := by
      have heq : (H.V c / lam) * H.U x = lam⁻¹ * (H.U x * H.V c) := by ring
      rw [heq]
      exact hcoreProduct x c hx (right_mem_Icc.mpr hac)
    exact (mul_le_mul hc (hPbound m y hy hθm) (abs_nonneg _) (exp_pos _).le).trans hnum
  have hpoint (k m : ℕ) (x y : ℝ) (hx : x ∈ Ico a b) (hy : y ∈ Ico a b)
      (hθk : D.localizer k (outerOutwardRadius right x) ≠ 0)
      (hθm : D.localizer m (outerOutwardRadius right y) ≠ 0) :
      |outerGreenKernel lam H.U H.V x y| ≤ 2 * E k m := by
    have hnum := halgebra N (D.cellIndex k) (D.cellIndex m) (by omega)
      (hlevel k x hx hθk) (hlevel m y hy hθm)
    have hE : 0 ≤ E k m := (exp_pos _).le
    by_cases hxc : x ≤ c
    · by_cases hyc : y ≤ c
      · have hxl := hcoreLabel k x ⟨hx.1, hxc⟩ hθk
        have hyl := hcoreLabel m y ⟨hy.1, hyc⟩ hθm
        have hh : |outerGreenKernel lam H.U H.V x y| ≤ exp (B₀ * radialQ N) := by
          exact hcoreProduct (min x y) (max x y)
            ⟨le_min hx.1 hy.1, (min_le_left _ _).trans hxc⟩
            ⟨hx.1.trans (le_max_left _ _), max_le hxc hyc⟩
        exact (hh.trans (hnum.1 hxl.1 hxl.2 hyl.1 hyl.2)).trans (by nlinarith only [hE])
      · exact (hcross k m x y ⟨hx.1, hxc⟩
          ⟨(lt_of_not_ge hyc).le, hy.2⟩ hθk hθm).trans (by nlinarith only [hE])
    · have hxt : x ∈ Ico c b := ⟨(lt_of_not_ge hxc).le, hx.2⟩
      by_cases hyc : y ≤ c
      · have hh := hcross m k y x ⟨hy.1, hyc⟩ hxt hθm hθk
        have heq : E m k = E k m := by
          dsimp only [E]
          rw [add_comm, abs_sub_comm]
        rw [heq, ← outerGreenKernel_symm lam H.U H.V x y] at hh
        exact hh.trans (by nlinarith only [hE])
      · have hyt : y ∈ Ico c b := ⟨(lt_of_not_ge hyc).le, hy.2⟩
        have hd := hkernel M σ D h (hends σ σ₀).2 N hNlarge hlabel right j η K F
          hdata.2.1 hη hK hj hdata.2.2.1 hdata.1 hdata.2.2.2 k m x y
          (by simpa only [c, morseTransitionOutwardRight_eq] using hxt)
          (by simpa only [c, morseTransitionOutwardRight_eq] using hyt) hθk hθm
        have hd' : |F.Q (min x y) * F.P (max x y)| ≤ E k m := hd.trans hnum.2.2.2
        have hr : |outerGreenKernel lam H.U H.V c c * (F.P x * F.P y)| ≤ E k m := by
          rw [abs_mul, abs_mul]
          calc
            _ ≤ exp (B₀ * radialQ N) * (En k * En m) :=
              mul_le_mul hdiag
                (mul_le_mul (hPbound k x hxt hθk) (hPbound m y hyt hθm)
                  (abs_nonneg _) (exp_pos _).le)
                (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (exp_pos _).le
            _ = exp (B₀ * radialQ N) * En k * En m := by ring
            _ ≤ E k m := hnum.2.2.1 (htailLabel k x hxt hθk)
        rw [H.green_tail_decomposition_unit_flux hlam.ne' hac hcb hPc hQc hflux hxt hyt]
        exact (abs_add_le _ _).trans ((add_le_add hd' hr).trans_eq (by ring))
  refine ⟨hpoint, ?_⟩
  intro R hR k m
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
    have hh := outerWholeMeasure_ae_mem (right := right) hphys
    rw [← morseTransitionOutwardLeft_eq] at hh
    exact hh.mono fun _ hx => Ioo_subset_Ico_self hx
  have hrow : ∀ᵐ x ∂μ, AEStronglyMeasurable (outerGreenKernel lam H.U H.V x) μ := by
    filter_upwards [hμmem] with x hx
    have hh := matchedOuter_actual_whole_row_measurable H
      (fun y => ENNReal.ofReal (12 * D.w (outerOutwardRadius right y) / y ^ 2)) hx
    dsimp only [μ]
    rw [outerWholeMeasure_eq_density hphys, ← morseTransitionOutwardLeft_eq]
    exact hh
  have hbnd := matchedOuterCell_comp_norm_le_of_kernel h.accumulating.2.1 right μ R
    (outerGreenKernel lam H.U H.V) hR hrow k m
    (show 0 ≤ 2 * E k m by dsimp only [E]; positivity) (by
      filter_upwards [hμmem] with x hx
      filter_upwards [hμmem] with y hy
      exact hpoint k m x y hx hy)
  apply hbnd.trans
  have hEc : 0 ≤ E k m := (exp_pos _).le
  have hmC : (measureUnivNNReal μ : ℝ) * 2 ≤ C₁ := by
    dsimp only [C₁]
    linarith only [hμmass]
  nlinarith only [mul_le_mul_of_nonneg_right hmC hEc]

end ContinuousFlexibility.Radial
