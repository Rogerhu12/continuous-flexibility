import ContinuousFlexibility.Radial.MatchedOuterCompactLabels
import ContinuousFlexibility.Radial.MatchedOuterFiniteCoreEnvelope
import ContinuousFlexibility.Radial.MatchedOuterLocalizerBounds
import ContinuousFlexibility.Radial.OuterGreenAssembly
import ContinuousFlexibility.Radial.OuterWholeMeasure
import ContinuousFlexibility.Radial.MatchedModeLocalization

/-!
# Fixed-frequency envelopes for the actual whole pair

A deeper actual Morse basis can be used at any regular outer cut.
The compact core costs a constant, while the tail keeps the full action
decay. The localizers may be those of the final retained reference:
only their genuine equality on the deep tail is used.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

theorem exists_matchedMorse_fixed_whole_point_bounds
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
    (radius : ℝ → ℝ) (hradius : Continuous radius)
    (hcore : ∀ x ∈ Icc (outerOutwardRadius right cut)
      (outerOutwardRadius right (morseOuterDeepEntrance M right N)),
        radius x ∈ radialCore E)
    (hindex : ∀ m, D.cellIndex m ≤ E.cellIndex m)
    (hlocal : ∀ m x, x ∈ Ico
      (outerOutwardRadius right (morseOuterDeepEntrance M right N))
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) →
        E.localizer m (radius x) = D.localizer m (outerOutwardRadius right x))
    (transition : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      (∀ k m x y,
        x ∈ Ico (outerOutwardRadius right cut)
          (outerOutwardRadius right (tailPhysicalEndpoint D right)) →
        y ∈ Ico (outerOutwardRadius right cut)
          (outerOutwardRadius right (tailPhysicalEndpoint D right)) →
        |E.localizer k (radius x) * outerGreenKernel lam H.U H.V x y *
            E.localizer m (radius y)| ≤
          B * exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
            |radialS (D.cellIndex k) - radialS (D.cellIndex m)|)) ∧
      (∀ m x, x ∈ Ico (outerOutwardRadius right cut)
          (outerOutwardRadius right (tailPhysicalEndpoint D right)) →
        E.localizer m (radius x) ≠ 0 →
        |H.V x / sqrt lam| ≤
          B * exp (A * (radialQ (D.cellIndex m) + radialQ transition) -
            |radialS (D.cellIndex m) - radialS transition|)) := by
  let a := outerOutwardRadius right cut
  let c := outerOutwardRadius right (morseOuterDeepEntrance M right N)
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  have hcb : c < b := outerWhole_interval (right := right)
    (morseOuterDeepEntrance_mem_core h right N (by omega))
  have hPc : F.P c = 1 := by
    simpa only [c, outerOutwardRadius_eq_sign] using F.P_entrance
  have hQc : F.Q c = 0 := by
    simpa only [c, outerOutwardRadius_eq_sign] using F.Q_entrance
  have hflux : F.ZQ lam c = 1 / lam := by
    simpa only [c, outerOutwardRadius_eq_sign] using F.ZQ_entrance lam
  obtain ⟨Kc, hKc, hU, hV⟩ := H.exists_compact_pair_bound hcb
  obtain ⟨T, hT0, hlabel⟩ := exists_reference_compact_coordinate_action_bound
    hE radius hradius hcore
  obtain ⟨Ak, hAk, hkernel⟩ := exists_matchedOuter_actual_tail_kernel_cell_exponent
    (h.constants_pos 0) (h.geometry.1.trans h.geometry.2.1) hAd
  obtain ⟨An, hAn, hnatural⟩ := exists_matchedOuter_actual_tail_natural_cell_exponent hAd
  let A := Ak + An + 1
  have hA : 0 < A := by dsimp only [A]; linarith only [hAk, hAn]
  have hAkA : Ak ≤ A := by dsimp only [A]; linarith only [hAn]
  have hAnA : An ≤ A := by dsimp only [A]; linarith only [hAk]
  let Bn := exp (An * radialQ N + radialS N)
  have hBn : 0 < Bn := exp_pos _
  let L := max Bn (exp T)
  have hL : 0 < L := hBn.trans_le (le_max_left _ _)
  have hcoreLabel (m : ℕ) (x : ℝ) (hx : x ∈ Icc a c)
      (hθ : E.localizer m (radius x) ≠ 0) : radialS (D.cellIndex m) ≤ T :=
    (radialS_monotone (hindex m)).trans (hlabel m x hx hθ)
  have hP (m : ℕ) (x : ℝ) (hx : x ∈ Ico c b)
      (hθ : E.localizer m (radius x) ≠ 0) :
      |F.P x| ≤ Bn * exp (A * radialQ (D.cellIndex m) - radialS (D.cellIndex m)) := by
    have hθ' : D.localizer m (outerOutwardRadius right x) ≠ 0 := by
      rwa [hlocal m x hx] at hθ
    have hh := hnatural M σ D C h N hN hlabels right j η K F
      hT hη hK hj hphysical hclose hden m x hx hθ'
    refine hh.trans ?_
    dsimp only [Bn]
    rw [← exp_add]
    apply exp_le_exp.mpr
    have hq := mul_le_mul_of_nonneg_right hAnA (radialQ_nonneg (D.cellIndex m))
    have hd := le_abs_self (radialS (D.cellIndex m) - radialS N)
    nlinarith only [hq, hd]
  have hdeep (k m : ℕ) (x y : ℝ) (hx : x ∈ Ico c b) (hy : y ∈ Ico c b)
      (hk : E.localizer k (radius x) ≠ 0) (hm : E.localizer m (radius y) ≠ 0) :
      |F.Q (min x y) * F.P (max x y)| ≤
        1 * exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
          |radialS (D.cellIndex k) - radialS (D.cellIndex m)|) := by
    rw [hlocal k x hx] at hk
    rw [hlocal m y hy] at hm
    have hh := hkernel M σ D h rfl N hN hlabels right j η K F
      hT hη hK hj hphysical hclose hden k m x y hx hy hk hm
    rw [one_mul]
    exact hh.trans (exp_le_exp.mpr (sub_le_sub_right
      (mul_le_mul_of_nonneg_right hAkA
        (add_nonneg (radialQ_nonneg _) (radialQ_nonneg _))) _))
  have hpart : RadialPartition E := by obtain ⟨_, hh⟩ := hE; exact hh.2.1
  let Bk := 1 + lam⁻¹ * Kc ^ 2 * L ^ 2
  let Bv := (Kc / sqrt lam) * L * exp (radialS transition)
  let B := Bk + Bv + 1
  have hBk : 0 ≤ Bk := by dsimp only [Bk]; positivity
  have hBv : 0 ≤ Bv := by dsimp only [Bv]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBkB : Bk ≤ B := by dsimp only [B]; linarith only [hBv]
  have hBvB : Bv ≤ B := by dsimp only [B]; linarith only [hBk]
  refine ⟨B, A, hB, hA, ?_, ?_⟩
  · intro k m x y hx hy
    have hh := matchedOuter_fixedCore_kernel_envelope H hlam hKc.le hA.le
      hBn.le (by norm_num : (0 : ℝ) ≤ 1) hac hcb hPc hQc hflux hU hV
      D.cellIndex (fun m x => E.localizer m (radius x))
      (fun m x => matchedRadialLocalizer_abs_le_one hpart m (radius x))
      hcoreLabel hP hdeep k m hx hy
    exact hh.trans (mul_le_mul_of_nonneg_right hBkB (exp_pos _).le)
  · intro m x hx hθ
    have hpoint :
        |H.V x| ≤ Kc * L * exp (A * radialQ (D.cellIndex m) - radialS (D.cellIndex m)) := by
      by_cases hxc : x ≤ c
      · have hxc' : x ∈ Icc a c := ⟨hx.1, hxc⟩
        have hone : 1 ≤ L * exp (A * radialQ (D.cellIndex m) - radialS (D.cellIndex m)) := by
          have ht := hcoreLabel m x hxc' hθ
          calc
            1 ≤ exp (T + (A * radialQ (D.cellIndex m) - radialS (D.cellIndex m))) :=
              one_le_exp (by
                have hq := mul_nonneg hA.le (radialQ_nonneg (D.cellIndex m))
                linarith only [ht, hq])
            _ = exp T * exp (A * radialQ (D.cellIndex m) - radialS (D.cellIndex m)) :=
              exp_add _ _
            _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le
        exact (hV x hxc').trans (by nlinarith only [mul_le_mul_of_nonneg_left hone hKc.le])
      · have hxt : x ∈ Ico c b := ⟨(lt_of_not_ge hxc).le, hx.2⟩
        rw [H.V_tail_factor hcb hPc x hxt, abs_mul]
        have hVc := hV c (right_mem_Icc.mpr hac)
        have hPt := (hP m x hxt hθ).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le)
        exact (mul_le_mul hVc hPt (abs_nonneg _) hKc.le).trans_eq (by ring)
    have hdist : |radialS (D.cellIndex m) - radialS transition| ≤
        radialS (D.cellIndex m) + radialS transition := by
      exact abs_le.mpr ⟨by linarith only [radialS_nonneg (D.cellIndex m)],
        by linarith only [radialS_nonneg transition]⟩
    have he : exp (A * radialQ (D.cellIndex m) - radialS (D.cellIndex m)) ≤
        exp (radialS transition) *
          exp (A * (radialQ (D.cellIndex m) + radialQ transition) -
            |radialS (D.cellIndex m) - radialS transition|) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      have hq := mul_nonneg hA.le (radialQ_nonneg transition)
      nlinarith only [hdist, hq]
    rw [abs_div, abs_of_nonneg (sqrt_nonneg lam)]
    calc
      _ ≤ (Kc * L * exp (A * radialQ (D.cellIndex m) - radialS (D.cellIndex m))) /
          sqrt lam := div_le_div_of_nonneg_right hpoint (sqrt_nonneg lam)
      _ = (Kc / sqrt lam) * L *
          exp (A * radialQ (D.cellIndex m) - radialS (D.cellIndex m)) := by ring
      _ ≤ (Kc / sqrt lam) * L * (exp (radialS transition) *
          exp (A * (radialQ (D.cellIndex m) + radialQ transition) -
            |radialS (D.cellIndex m) - radialS transition|)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = Bv * exp (A * (radialQ (D.cellIndex m) + radialQ transition) -
          |radialS (D.cellIndex m) - radialS transition|) := by dsimp only [Bv]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hBvB (exp_pos _).le

end ContinuousFlexibility.Radial
