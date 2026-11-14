module

public import ContinuousFlexibility.Radial.MatchedOuterLocalizerBounds
public import ContinuousFlexibility.Radial.MatchedOuterModalCells

/-!
# Uniform actual deep modal blocks before the height and frequency choices

The original outer factory supplies the deep hypotheses, physical relation
and sharp denominator at one common cutoff. The original localizer support
geometry and actual kernel then give bounds for the supplied operator and
supplied natural vector on their genuine physical Hilbert space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology

/-- Uniform actual-cell bounds for the same deep inverse and same normalized
natural vector. Constants and cutoff precede every height and frequency
choice. The only operator hypothesis is its proved all-source kernel
identity, and the only vector hypothesis is its actual representative. -/
theorem exists_matchedMorse_uniform_actual_deep_modal_bounds
    {M : MorseChainData} {C : ℕ → ℝ}
    {family : (ℕ → ℝ) → ReferenceData} {Cstar η K : ℝ}
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization M σ (family σ) C ∧
        MorseMassResistanceBounds M σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧
      (family σ).b = (family τ).b)
    (hCstar : 0 < Cstar) (hη0 : 0 < η) (hη : η ≤ 1 / 16)
    (hK : 32 ≤ K) (minimum : ℕ) :
    ∃ C₁ A : ℝ, 0 < C₁ ∧ 0 < A ∧
      ∃ N₀ : ℕ, minimum ≤ N₀ ∧ M.index + 3 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
      ∀ σ (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2),
      ∀ j : ℕ, 2 ≤ j → (j : ℝ) < radialFrequencyThreshold M Cstar N →
      ∀ (right : Bool)
        (F : MorsePhysicalTailBasis M (family σ) right j (N + 1)
          (morseOuterDeepEntrance M right N) η K),
        let D := family σ
        let hP := (hfamily σ hσ).1.accumulating.2.1
        let μ := outerWholeMeasure D right (morseOuterDeepEntrance M right N)
        ∀ R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
          (∀ f : Lp ℝ 2 μ, (R f : ℝ → ℝ) =ᵐ[μ] fun x =>
            ∫ y, F.Q (min x y) * F.P (max x y) * f y ∂μ) →
        ∀ U : Lp ℝ 2 μ, (U : ℝ → ℝ) =ᵐ[μ] F.P →
        ∀ k m : ℕ,
          ‖(matchedOuterCell D hP right μ k).comp
            (R.comp (matchedOuterCell D hP right μ m))‖ ≤
              C₁ * exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
                |radialS (D.cellIndex k) - radialS (D.cellIndex m)|) ∧
          ‖matchedOuterCell D hP right μ m U‖ ≤
            C₁ * exp (A * (radialQ (D.cellIndex m) + radialQ N) -
              |radialS (D.cellIndex m) - radialS N|) := by
  let σ₀ : ℕ → ℝ := fun _ => 1
  have h₀ := (hfamily σ₀ (fun _ => ⟨le_rfl, by norm_num [σ₀]⟩)).1
  have hC0 := h₀.constants_pos 0
  have ha : 0 < (family σ₀).a := h₀.geometry.1
  have hab : (family σ₀).a < (family σ₀).b := h₀.geometry.2.1
  have hb : 0 < (family σ₀).b := ha.trans hab
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
  let A := Ak + An + 1
  let mass := 12 * C 0 * exp ((C 0) ^ 5) *
    ((family σ₀).b - (family σ₀).a) / (family σ₀).a ^ 2
  let C₁ := 1 + mass + sqrt mass
  let N₀ := max Np Nl
  have hmass0 : 0 < mass := by dsimp only [mass]; positivity
  have hC₁ : 0 < C₁ := by dsimp only [C₁]; positivity
  have hA : 0 < A := by dsimp only [A]; linarith only [hAk, hAn]
  have hAkA : Ak ≤ A := by dsimp only [A]; linarith only [hAn]
  have hAnA : An ≤ A := by dsimp only [A]; linarith only [hAk]
  have hmassC : mass ≤ C₁ := by dsimp only [C₁]; linarith only [sqrt_nonneg mass]
  have hsqrtC : sqrt mass ≤ C₁ := by dsimp only [C₁]; linarith only [hmass0]
  refine ⟨C₁, A, hC₁, hA, N₀, by dsimp only [N₀]; omega,
    by dsimp only [N₀]; omega, ?_⟩
  intro N hN σ hσ j hj hupper right F
  dsimp only
  intro R hR U hU k m
  let D := family σ
  let deep := morseOuterDeepEntrance M right N
  let μ := outerWholeMeasure D right deep
  have h := (hfamily σ hσ).1
  have hPN : Np ≤ N := (le_max_left Np Nl).trans hN
  have hLN : Nl ≤ N := (le_max_right Np Nl).trans hN
  have hNlarge : M.index + 3 ≤ N := by omega
  have hdata := hprod N hPN σ hσ j hj hupper right
  have hlabel := (hlabels N hLN).2 σ hσ
  have hT := hdata.2.1
  have hphysical := hdata.2.2.1
  have hclose := hdata.1
  have hden := hdata.2.2.2
  have hdeep : deep ∈ radialCore D :=
    morseOuterDeepEntrance_mem_core h right N (by omega)
  have hdeepPos : 0 < deep := h.geometry.1.trans hdeep.1
  letI : IsFiniteMeasure μ :=
    outerWholeMeasure_isFinite ⟨C, h.accumulating⟩ right deep
  have hμmass : (measureUnivNNReal μ : ℝ) ≤ mass := by
    change μ.real univ ≤ mass
    have hh := outerWholeMeasure_mass_bound h.accumulating right deep
    rw [(hends σ σ₀).1, (hends σ σ₀).2] at hh
    exact hh
  have hμmem : ∀ᵐ x ∂μ, x ∈ Ico (outerOutwardRadius right deep)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) :=
    (outerWholeMeasure_ae_mem hdeep).mono fun _ hx => Ioo_subset_Ico_self hx
  let Ek := exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
    |radialS (D.cellIndex k) - radialS (D.cellIndex m)|)
  let En := exp (A * (radialQ (D.cellIndex m) + radialQ N) -
    |radialS (D.cellIndex m) - radialS N|)
  have hEk : 0 ≤ Ek := (exp_pos _).le
  have hEn : 0 ≤ En := (exp_pos _).le
  have hpointK : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
      D.localizer k (outerOutwardRadius right x) ≠ 0 →
      D.localizer m (outerOutwardRadius right y) ≠ 0 →
      |F.Q (min x y) * F.P (max x y)| ≤ Ek := by
    filter_upwards [hμmem] with x hx
    filter_upwards [hμmem] with y hy
    intro hθk hθm
    have hh := hkernel M σ D h (hends σ σ₀).2 N hNlarge hlabel right j η K F
      hT hη hK hj hphysical hclose hden k m x y hx hy hθk hθm
    exact hh.trans (exp_le_exp.mpr (sub_le_sub_right
      (mul_le_mul_of_nonneg_right hAkA
        (add_nonneg (radialQ_nonneg _) (radialQ_nonneg _))) _))
  have hrow : ∀ᵐ x ∂μ,
      AEStronglyMeasurable (fun y => F.Q (min x y) * F.P (max x y)) μ := by
    filter_upwards [hμmem] with x hx
    exact (matchedOuter_actual_tail_row_memLp ⟨C, h.accumulating⟩ hdeepPos
      F hT hphysical hx).aestronglyMeasurable
  have hpointN : ∀ᵐ x ∂μ, D.localizer m (outerOutwardRadius right x) ≠ 0 →
      |F.P x| ≤ En := by
    filter_upwards [hμmem] with x hx
    intro hθ
    have hh := hnatural M σ D C h N hNlarge hlabel right j η K F
      hT hη hK hj hphysical hclose hden m x hx hθ
    exact hh.trans (exp_le_exp.mpr (sub_le_sub_right
      (mul_le_mul_of_nonneg_right hAnA
        (add_nonneg (radialQ_nonneg _) (radialQ_nonneg _))) _))
  constructor
  · exact (matchedOuterCell_comp_norm_le_of_kernel h.accumulating.2.1 right μ R
      (fun x y => F.Q (min x y) * F.P (max x y)) hR hrow k m hEk hpointK).trans
      (mul_le_mul_of_nonneg_right (hμmass.trans hmassC) hEk)
  · exact (matchedOuterCell_norm_le_of_value h.accumulating.2.1 right μ U F.P hU
      m hEn hpointN).trans
      (mul_le_mul_of_nonneg_right ((sqrt_le_sqrt hμmass).trans hsqrtC) hEn)

end ContinuousFlexibility.Radial
