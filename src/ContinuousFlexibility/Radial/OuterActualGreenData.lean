import ContinuousFlexibility.Radial.OuterUniformCoreState
import ContinuousFlexibility.Radial.OuterActualCoreInputs
import ContinuousFlexibility.Radial.OuterActualCoreMeasure
import ContinuousFlexibility.Radial.OuterPhysicalRobinInverse
import ContinuousFlexibility.Radial.OuterGlobalEnvelope
import ContinuousFlexibility.Radial.R07DeepTailData

/-!
# The same actual outer basis, natural vector and Green operator

The data retain the actual logarithmic tail, its normalized physical
basis, the whole homogeneous pair, and the operator with their single
canonical kernel. The quantitative constructor inserts the proved
Morse-core estimates, rather than assuming core value or mass bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements

/-- Transparent data for one actual outer interval and one physical frequency. -/
structure MorseOuterGreenData (M : MorseChainData) (D : ReferenceData)
    (right : Bool) (n j : ℕ) (entry η K lam Cbound Co : ℝ) where
  profile : IsAccumulatingProfile D
  deep_hypotheses : DeepTailHypotheses
    (morsePhysicalDeepTail M D right j (n + 1) (morseOuterDeepEntrance M right n) η K)
  physical_relation : TailPhysicalRelation D
    (morsePhysicalDeepTail M D right j (n + 1) (morseOuterDeepEntrance M right n) η K)
      right j (n + 1)
  close : (morsePhysicalDeepTail M D right j (n + 1)
      (morseOuterDeepEntrance M right n) η K).endpoint -
    (morsePhysicalDeepTail M D right j (n + 1)
      (morseOuterDeepEntrance M right n) η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹
  basis : MorsePhysicalTailBasis M D right j (n + 1) (morseOuterDeepEntrance M right n) η K
  inputs : MorseOuterCoreInputs entry lam Cbound Co profile physical_relation basis
  pair : OuterFundamentalStatePair
    (fun x => lam / outerTailOutwardWeight D right x)
    (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
    basis.P (basis.ZP lam) basis.Q (basis.ZQ lam)
    (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
    (outerOutwardRadius right (morseOuterDeepEntrance M right n))
    (outerOutwardRadius right (tailPhysicalEndpoint D right))
  inverse : OuterPhysicalRobinInverse basis pair
  core_bound : ∀ x ∈ Icc
      (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
      (outerOutwardRadius right (morseOuterDeepEntrance M right n)),
    let B := radialE n ^ Cbound * exp (Co * ((j : ℝ) * sqrt (morseChainA M n)))
    |pair.U x| ≤ B ∧ |pair.ZU x| ≤ B ∧ |pair.V x| ≤ B ∧ |pair.ZV x| ≤ B
  core_mass_bound : (outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right n)).real
    (Icc (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
      (outerOutwardRadius right (morseOuterDeepEntrance M right n))) ≤ lam * radialE n ^ Cbound
  poisson_bound : ‖inverse.poisson_memLp.toLp basis.P‖ ≤ sqrt lam * radialE n ^ Cbound
  natural_bound : ‖inverse.natural_memLp.toLp pair.V‖ ≤
    sqrt lam * radialE n ^ Cbound * exp (Co * ((j : ℝ) * sqrt (morseChainA M n)))
  operator_bound : ‖inverse.operator‖ ≤
    radialE n ^ Cbound * exp (Co * ((j : ℝ) * sqrt (morseChainA M n))) ^ 2

/-- The actual core estimates and the same normalized Poisson vector
construct the full data. The natural Poisson estimate will be supplied
uniformly by the preceding mass construction. -/
theorem exists_morseOuterGreenData_of_deep
    {M : MorseChainData} {σ : ℕ → ℝ} {D₀ D : ReferenceData} {C : ℕ → ℝ}
    {B Cstar L lam entry η K Qp : ℝ} {n j : ℕ}
    (h₀ : MorseChainRealization M (fun _ => 1) D₀ C)
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates M B) (hlam : 0 < lam) (hL : 0 ≤ L)
    (he : entry ∈ morseInitialMiddle M) (right : Bool) (hn : M.index < n)
    (hj : 2 ≤ j) (hupper : (j : ℝ) < radialFrequencyThreshold M Cstar n)
    (hhi : lam / morseChainAmplitude M σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude M σ n / lam ≤ exp (L * (n : ℝ) ^ 2))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j (n + 1)
      (morseOuterDeepEntrance M right n) η K))
    (hphysical : TailPhysicalRelation D (morsePhysicalDeepTail M D right j (n + 1)
      (morseOuterDeepEntrance M right n) η K) right j (n + 1))
    (hclose : (morsePhysicalDeepTail M D right j (n + 1)
        (morseOuterDeepEntrance M right n) η K).endpoint -
      (morsePhysicalDeepTail M D right j (n + 1)
        (morseOuterDeepEntrance M right n) η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    (F : MorsePhysicalTailBasis M D right j (n + 1) (morseOuterDeepEntrance M right n) η K)
    (hP : MemLp F.P 2 (outerOutwardTailMeasure D
      (morsePhysicalDeepTail M D right j (n + 1) (morseOuterDeepEntrance M right n) η K) right))
    (hQp : 0 ≤ Qp)
    (hPnorm : ‖hP.toLp F.P‖ ≤ sqrt lam * exp (Qp * (n : ℝ) ^ 2)) :
    let Qe := outerFullCoreQuadraticExponent C B D.a Cstar L
    let Qm := L + 135 + 2 * outerCoreMassPrefactor D₀ D C B
    let Q := Qe + Qm + Qp + 1
    Nonempty (MorseOuterGreenData M D right n j entry η K lam
      (12 + 4 * Q) (outerFullCoreActionExponent C B D.a)) := by
  let Qe := outerFullCoreQuadraticExponent C B D.a Cstar L
  let Qm := L + 135 + 2 * outerCoreMassPrefactor D₀ D C B
  let Q := Qe + Qm + Qp + 1
  let Co := outerFullCoreActionExponent C B D.a
  let A := exp (Q * (n : ℝ) ^ 2)
  let Kn := exp (Co * ((j : ℝ) * sqrt (morseChainA M n)))
  have hB := hcell.pos
  have hC := h.constants_pos 0
  have ha := h.geometry.1
  have hQe : 0 ≤ Qe := by
    dsimp only [Qe, outerFullCoreQuadraticExponent, outerCoreInteriorQuadraticExponent,
      outerCoreQuadraticExponent, outerOutgoingQuadraticExponent, outerFrequencyExponent,
      outerJoinPrefactor]
    positivity
  have hQm : 0 ≤ Qm := by dsimp only [Qm, outerCoreMassPrefactor]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; linarith only [hQe, hQm, hQp]
  have hQeQ : Qe ≤ Q := by dsimp only [Q]; linarith only [hQm, hQp]
  have hQmQ : Qm ≤ Q := by dsimp only [Q]; linarith only [hQe, hQp]
  have hQpQ : Qp ≤ Q := by dsimp only [Q]; linarith only [hQe, hQm]
  have hCo : 0 ≤ Co := by
    dsimp only [Co, outerFullCoreActionExponent, outerCoreActionExponent, outerOutgoingActionExponent]
    positivity
  have hn1 : 1 ≤ n := by omega
  have hA : 1 ≤ A := one_le_exp_iff.mpr (mul_nonneg hQ (sq_nonneg _))
  have hKn : 1 ≤ Kn := one_le_exp_iff.mpr
    (mul_nonneg hCo (mul_nonneg (Nat.cast_nonneg _) (sqrt_nonneg _)))
  have hentry := morseTransitionPhysicalEntry_mem_core h he right n hn.le
  have hdeep := morseOuterDeepEntrance_mem_core h right n hn.le
  have hi := morseTransitionOutward_interval h he right n hn.le
  rw [morseTransitionOutwardLeft_eq, morseTransitionOutwardRight_eq] at hi
  have hD := r07_realization_accumulating h
  obtain ⟨H⟩ := exists_outerPhysicalFundamentalStatePair h.geometry F hentry hdeep hi.1.le hlam hT
  have hraw := H.morseFullCore_physical_bounds_of_upper h hσ hcell hlam hL he right
    hn hupper hhi hlo
  have hraw_le : exp (Qe * (n : ℝ) ^ 2 +
      Co * ((j : ℝ) * sqrt (morseChainA M n))) ≤ A * Kn := by
    dsimp only [A, Kn]
    rw [← exp_add]
    exact exp_le_exp.mpr (add_le_add_right
      (mul_le_mul_of_nonneg_right hQeQ (sq_nonneg _)) _)
  have hcore : ∀ x ∈ Icc
      (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
      (outerOutwardRadius right (morseOuterDeepEntrance M right n)),
      |H.U x| ≤ A * Kn ∧ |H.ZU x| ≤ A * Kn ∧
        |H.V x| ≤ A * Kn ∧ |H.ZV x| ≤ A * Kn := by
    intro x hx
    have hh := hraw x hx
    exact ⟨hh.1.trans hraw_le, hh.2.1.trans hraw_le,
      hh.2.2.1.trans hraw_le, hh.2.2.2.trans hraw_le⟩
  have hmassEq := morseTransitionCore_measure_mass h he right n hn.le
  rw [morseTransitionOutwardLeft_eq, morseTransitionOutwardRight_eq] at hmassEq
  simp only [morseTransitionCoreLeft, morseTransitionCoreRight,
    if_neg (ne_of_gt hn)] at hmassEq
  have hmass : (outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right n)).real
      (Icc (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
        (outerOutwardRadius right (morseOuterDeepEntrance M right n))) ≤ lam * A := by
    rw [hmassEq]
    exact (morseOuterFullCore_mass_le_state_scale h₀ h hσ hcell right n hn hlam hlo).trans
      (mul_le_mul_of_nonneg_left
        (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hQmQ (sq_nonneg _))) hlam.le)
  have hmassA : (outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right n)).real
      (Icc (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
        (outerOutwardRadius right (morseOuterDeepEntrance M right n))) ≤ lam * A ^ 2 :=
    hmass.trans (mul_le_mul_of_nonneg_left (by nlinarith only [hA] : A ≤ A ^ 2) hlam.le)
  have hPA : ‖hP.toLp F.P‖ ≤ sqrt lam * A := hPnorm.trans
    (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hQpQ (sq_nonneg _))) (sqrt_nonneg _))
  obtain ⟨G⟩ := F.exists_wholeRobinInverse H hD hentry hdeep hi.1
    hlam hT hphysical hj hη hK hKinv
  have hPA' : ‖G.poisson_memLp.toLp F.P‖ ≤ sqrt lam * A := hPA
  have hquadratic : A ≤ exp ((12 + 4 * Q) * (n : ℝ) ^ 2) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [hQ]) (sq_nonneg _))
  obtain ⟨I⟩ := exists_morseOuterCoreInputs_of_quantitative_data h hσ hcell hlam hL
    he right hn hj hupper hhi hlo hD hT hphysical hη hKinv F hP
    (show Qe + 2 ≤ 12 + 4 * Q by linarith only [hQeQ, hQ])
    (hmass.trans (mul_le_mul_of_nonneg_left hquadratic hlam.le))
    (hPA.trans (mul_le_mul_of_nonneg_left hquadratic (sqrt_nonneg _)))
  have hVnorm := G.natural_bound A (A * Kn) (zero_le_one.trans hA)
    (mul_nonneg (zero_le_one.trans hA) (zero_le_one.trans hKn))
    (fun x hx => (hcore x hx).2.2.1) hmassA hPA'
  have hRnorm := G.operator_bound A (A * Kn) (zero_le_one.trans hA)
    (mul_nonneg (zero_le_one.trans hA) (zero_le_one.trans hKn))
    (fun x hx => (hcore x hx).1) (fun x hx => (hcore x hx).2.2.1) hmassA hPA'
  have hAE : A ≤ radialE n ^ (12 + 4 * Q) := by
    simpa only [mul_one] using
      (outer_global_core_envelope (Q := Q) (Kn := 1) hn1 hQ (by norm_num))
  have hAKE : A * Kn ≤ radialE n ^ (12 + 4 * Q) * Kn :=
    outer_global_core_envelope hn1 hQ (zero_le_one.trans hKn)
  refine ⟨{
    profile := hD
    deep_hypotheses := hT
    physical_relation := hphysical
    close := hclose
    basis := F
    inputs := I
    pair := H
    inverse := G
    core_bound := ?_
    core_mass_bound := hmass.trans (mul_le_mul_of_nonneg_left hAE hlam.le)
    poisson_bound := hPA'.trans (mul_le_mul_of_nonneg_left hAE (sqrt_nonneg _))
    natural_bound := hVnorm.trans (outer_global_natural_envelope hn1 hQ (zero_le_one.trans hKn))
    operator_bound := hRnorm.trans
      (outer_global_inverse_envelope hn1 hQ hKn (outer_deep_inverse_le_four hj))
  }⟩
  intro x hx
  have hh := hcore x hx
  exact ⟨hh.1.trans hAKE, hh.2.1.trans hAKE, hh.2.2.1.trans hAKE, hh.2.2.2.trans hAKE⟩

end ContinuousFlexibility.Radial
