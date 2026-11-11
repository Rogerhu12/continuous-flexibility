import ContinuousFlexibility.Radial.MatchedOuterFixedPointBounds
import ContinuousFlexibility.Radial.MatchedOuterRadiusLocalized
import ContinuousFlexibility.Radial.MatchedOuterRadiusCells
import ContinuousFlexibility.Radial.MatchedOuterWholeModalBounds

/-!
# Full L² localized estimates after the actual retained dilation

For a fixed frequency, the same actual deep basis supplies the whole
kernel at the regular cut. Its compact-core and deep-tail point bounds
control every cell of the original transported inverse and the supplied
matching-normalized natural column. No smooth-source restriction occurs.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter MeasureTheory
open ContinuousFlexibility.Statements

theorem exists_matchedMorse_fixed_whole_radius_bounds
    {M : MorseChainData} {σ C : ℕ → ℝ} {D E : ReferenceData}
    (h : MorseChainRealization M σ D C) (hE : IsAccumulatingProfile E)
    {N : ℕ} (hN : M.index + 3 ≤ N) (hlabels : MorseOuterLocalizerLabels M D N)
    (right : Bool) (j : ℕ) (η K : ℝ)
    (F : MorsePhysicalTailBasis M D right j (N + 1)
      (morseOuterDeepEntrance M right N) η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j (N + 1)
      (morseOuterDeepEntrance M right N) η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) (hj : 2 ≤ j)
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j (N + 1)
        (morseOuterDeepEntrance M right N) η K) right j (N + 1))
    (hclose :
      (morsePhysicalDeepTail M D right j (N + 1)
        (morseOuterDeepEntrance M right N) η K).endpoint -
      (morsePhysicalDeepTail M D right j (N + 1)
        (morseOuterDeepEntrance M right N) η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    {Ad : ℝ} (hAd : 0 ≤ Ad)
    (hden : ∀ k : ℕ,
      let T := morsePhysicalDeepTail M D right j (N + 1)
        (morseOuterDeepEntrance M right N) η K
      exp (2 * ((N + 1 + k : ℕ) : ℝ) ^ 2 -
        Ad * (((N + 1 + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (N + 1 + k : ℕ))) ≤
          T.Λ * tailMass T (k + 1) * tailResistance T k)
    {cut lam : ℝ} (hlam : 0 < lam)
    (hac : outerOutwardRadius right cut ≤
      outerOutwardRadius right (morseOuterDeepEntrance M right N))
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      F.P (F.ZP lam) F.Q (F.ZQ lam)
      (outerOutwardRadius right cut)
      (outerOutwardRadius right (morseOuterDeepEntrance M right N))
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hcut : cut ∈ radialCore D) {κ β : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hcutE : κ * cut ∈ radialCore E)
    (hend : tailPhysicalEndpoint E right = κ * tailPhysicalEndpoint D right)
    (hm : outerWholeMeasure E right (κ * cut) =
      ENNReal.ofReal β • (outerWholeMeasure D right cut).map (fun r => κ * r))
    (hindex : ∀ m, D.cellIndex m ≤ E.cellIndex m)
    (hlocal : ∀ m x, x ∈ Ico
      (outerOutwardRadius right (morseOuterDeepEntrance M right N))
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) →
        E.localizer m (outerOutwardRadius right (κ * x)) =
          D.localizer m (outerOutwardRadius right x))
    (transition : ℕ) :
    let μ := outerWholeMeasure D right cut
    let ν := outerWholeMeasure E right (κ * cut)
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ (hPE : RadialPartition E) (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ),
        (∀ f : Lp ℝ 2 μ, (R f : ℝ → ℝ) =ᵐ[μ]
          fun x => ∫ y, outerGreenKernel lam H.U H.V x y * f y ∂μ) →
      (∀ k m,
        ‖(matchedOuterCell E hPE right ν k).comp
          ((inverseRadiusOperator hκ.ne' hβ hm R).comp (matchedOuterCell E hPE right ν m))‖ ≤
          B * exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
            |radialS (D.cellIndex k) - radialS (D.cellIndex m)|)) ∧
      (∀ U : Lp ℝ 2 ν, (U : ℝ → ℝ) =ᵐ[ν]
          (fun r => H.V (r / κ) / sqrt (β * lam)) →
        ∀ m, ‖matchedOuterCell E hPE right ν m U‖ ≤
          B * exp (A * (radialQ (D.cellIndex m) + radialQ transition) -
            |radialS (D.cellIndex m) - radialS transition|)) := by
  let μ := outerWholeMeasure D right cut
  let ν := outerWholeMeasure E right (κ * cut)
  let radius : ℝ → ℝ := fun x => outerOutwardRadius right (κ * x)
  have hradius : Continuous radius := by
    dsimp only [radius]
    cases right <;> fun_prop
  have hscale (r : ℝ) : outerOutwardRadius right (κ * r) =
      κ * outerOutwardRadius right r := by cases right <;> simp [outerOutwardRadius]
  have hcb : outerOutwardRadius right (morseOuterDeepEntrance M right N) <
      outerOutwardRadius right (tailPhysicalEndpoint D right) :=
    outerWhole_interval (right := right)
      (morseOuterDeepEntrance_mem_core h right N (by omega))
  have hcore : ∀ x ∈ Icc (outerOutwardRadius right cut)
      (outerOutwardRadius right (morseOuterDeepEntrance M right N)),
        radius x ∈ radialCore E := by
    intro x hx
    apply outerWhole_coordinate_core (right := right) hcutE
    constructor
    · rw [hscale]
      exact mul_le_mul_of_nonneg_left hx.1 hκ.le
    · rw [hend, hscale]
      exact mul_lt_mul_of_pos_left (hx.2.trans_lt hcb) hκ
  obtain ⟨B, A, hB, hA, hkernel, hvalue⟩ :=
    exists_matchedMorse_fixed_whole_point_bounds h hE hN hlabels right j η K F
      hT hη hK hj hphysical hclose hAd hden hlam hac H radius hradius hcore
      hindex hlocal transition
  letI : IsFiniteMeasure μ := outerWholeMeasure_isFinite ⟨C, h.accumulating⟩ right cut
  let cost := 1 + (measureUnivNNReal μ : ℝ) + sqrt (measureUnivNNReal μ : ℝ)
  have hcost : 0 < cost := by dsimp only [cost]; positivity
  have hmass : (measureUnivNNReal μ : ℝ) ≤ cost := by
    dsimp only [cost]
    linarith only [sqrt_nonneg (measureUnivNNReal μ : ℝ)]
  have hmass' : sqrt (measureUnivNNReal μ : ℝ) ≤ cost := by
    dsimp only [cost]
    linarith only [show (0 : ℝ) ≤ (measureUnivNNReal μ : ℝ) from by positivity]
  refine ⟨cost * B, A, mul_pos hcost hB, hA, ?_⟩
  intro hPE R hR
  have hμmem : ∀ᵐ x ∂μ,
      x ∈ Ico (outerOutwardRadius right cut)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)) :=
    (outerWholeMeasure_ae_mem (right := right) hcut).mono fun _ hx => Ioo_subset_Ico_self hx
  have hrow : ∀ᵐ x ∂μ, AEStronglyMeasurable (outerGreenKernel lam H.U H.V x) μ := by
    filter_upwards [hμmem] with x hx
    change AEStronglyMeasurable (outerGreenKernel lam H.U H.V x)
      (outerWholeMeasure D right cut)
    rw [outerWholeMeasure_eq_density hcut]
    exact matchedOuter_actual_whole_row_measurable H _ hx
  constructor
  · intro k m
    have hp : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
        |E.localizer k (outerOutwardRadius right (κ * x)) *
          outerGreenKernel lam H.U H.V x y *
          E.localizer m (outerOutwardRadius right (κ * y))| ≤
        B * exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
          |radialS (D.cellIndex k) - radialS (D.cellIndex m)|) := by
      filter_upwards [hμmem] with x hx
      filter_upwards [hμmem] with y hy
      exact hkernel k m x y hx hy
    have hbnd := norm_inverseRadiusOperator_outerCells_le_of_kernel hPE right
      hκ.ne' hβ hm R (outerGreenKernel lam H.U H.V) hR hrow k m
      (mul_nonneg hB.le (exp_pos _).le) hp
    calc
      _ ≤ (measureUnivNNReal μ : ℝ) *
          (B * exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
            |radialS (D.cellIndex k) - radialS (D.cellIndex m)|)) := hbnd
      _ ≤ cost * (B * exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
            |radialS (D.cellIndex k) - radialS (D.cellIndex m)|)) :=
        mul_le_mul_of_nonneg_right hmass (mul_nonneg hB.le (exp_pos _).le)
      _ = _ := by ring
  · intro U hU m
    have hU' := inverseRadiusEquiv_normalized_ae hκ.ne' hβ hm hU
    have hp : ∀ᵐ x ∂μ, E.localizer m (outerOutwardRadius right (κ * x)) ≠ 0 →
        |H.V x / sqrt lam| ≤
        B * exp (A * (radialQ (D.cellIndex m) + radialQ transition) -
          |radialS (D.cellIndex m) - radialS transition|) := by
      filter_upwards [hμmem] with x hx
      exact hvalue m x hx
    have hbnd := norm_matchedOuterCell_le_of_radius_value hPE right hκ.ne' hβ hm U
      (fun x => H.V x / sqrt lam) hU' m (mul_nonneg hB.le (exp_pos _).le) hp
    calc
      _ ≤ sqrt (measureUnivNNReal μ : ℝ) *
          (B * exp (A * (radialQ (D.cellIndex m) + radialQ transition) -
            |radialS (D.cellIndex m) - radialS transition|)) := hbnd
      _ ≤ cost * (B * exp (A * (radialQ (D.cellIndex m) + radialQ transition) -
            |radialS (D.cellIndex m) - radialS transition|)) :=
        mul_le_mul_of_nonneg_right hmass' (mul_nonneg hB.le (exp_pos _).le)
      _ = _ := by ring

end ContinuousFlexibility.Radial
