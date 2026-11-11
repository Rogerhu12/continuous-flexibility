import ContinuousFlexibility.Radial.OuterUniformCoreState
import ContinuousFlexibility.Radial.OuterActualCoreMeasure
import ContinuousFlexibility.Radial.OuterPhysicalInverse
import ContinuousFlexibility.Radial.OuterPhysicalFundamentalPair

/-!
# The four actual core and deep-tail inputs

The transfer is the genuine outward value/flux solution operator and its
inverse. The two mass estimates retain the quadratic exponential, before
the larger coefficient envelope is introduced in the whole-outer bound.
The Poisson function is the same basis vector used by the outer Green
operator, and the deep inverse has the actual transported Friedrichs graph.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

/-- Lemma 6.4 for the same physical tail basis and actual outward core. -/
structure MorseOuterCoreInputs
    {M : MorseChainData} {D : ReferenceData} {right : Bool} {n j : ℕ} {η K : ℝ}
    (entry lam Cbound Co : ℝ) (hD : IsAccumulatingProfile D)
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j (n + 1) (morseOuterDeepEntrance M right n) η K)
        right j (n + 1))
    (F : MorsePhysicalTailBasis M D right j (n + 1) (morseOuterDeepEntrance M right n) η K) where
  coreTransfer : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)
  coreTransfer_actual : ∀ u z : ℝ → ℝ,
    OuterFirstOrderSystem
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      u z (Icc (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
        (outerOutwardRadius right (morseOuterDeepEntrance M right n))) →
      coreTransfer
        (u (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n)),
          z (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))) =
        (u (outerOutwardRadius right (morseOuterDeepEntrance M right n)),
          z (outerOutwardRadius right (morseOuterDeepEntrance M right n)))
  transfer_bound : ‖coreTransfer.toContinuousLinearMap‖ +
      ‖coreTransfer.symm.toContinuousLinearMap‖ ≤
    exp (Cbound * (n : ℝ) ^ 2 + Co * ((j : ℝ) * sqrt (morseChainA M n)))
  core_mass_bound : (outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right n)).real
    (Icc (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
      (outerOutwardRadius right (morseOuterDeepEntrance M right n))) ≤
        lam * exp (Cbound * (n : ℝ) ^ 2)
  poisson_memLp : MemLp F.P 2 (outerOutwardTailMeasure D
    (morsePhysicalDeepTail M D right j (n + 1) (morseOuterDeepEntrance M right n) η K) right)
  poisson_bound : ‖poisson_memLp.toLp F.P‖ ≤ sqrt lam * exp (Cbound * (n : ℝ) ^ 2)
  deepInverse : OuterPhysicalTailL2 D
      (morsePhysicalDeepTail M D right j (n + 1) (morseOuterDeepEntrance M right n) η K) right →L[ℝ]
    OuterPhysicalTailL2 D
      (morsePhysicalDeepTail M D right j (n + 1) (morseOuterDeepEntrance M right n) η K) right
  deep_bound : ‖deepInverse‖ ≤ 64 / (j : ℝ) ^ 4
  deep_graph_iff : ∀ u f, OuterPhysicalDirichletGraph hD hphysical u f ↔ deepInverse f = u

/-- Actual core energy and the already proved same-basis quadratic mass
bounds construct all four inputs. The final uniform theorem derives the
two numerical hypotheses here from the realized Morse family. -/
theorem exists_morseOuterCoreInputs_of_quantitative_data
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {B Cstar L lam entry η K Cbound : ℝ} {n j : ℕ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates M B) (hlam : 0 < lam) (hL : 0 ≤ L)
    (he : entry ∈ morseInitialMiddle M) (right : Bool) (hn : M.index < n)
    (hj : 2 ≤ j) (hupper : (j : ℝ) < radialFrequencyThreshold M Cstar n)
    (hhi : lam / morseChainAmplitude M σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude M σ n / lam ≤ exp (L * (n : ℝ) ^ 2))
    (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j (n + 1)
      (morseOuterDeepEntrance M right n) η K))
    (hphysical : TailPhysicalRelation D (morsePhysicalDeepTail M D right j (n + 1)
      (morseOuterDeepEntrance M right n) η K) right j (n + 1))
    (hη : η ≤ 1 / 16) (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K)
    (F : MorsePhysicalTailBasis M D right j (n + 1) (morseOuterDeepEntrance M right n) η K)
    (hP : MemLp F.P 2 (outerOutwardTailMeasure D
      (morsePhysicalDeepTail M D right j (n + 1) (morseOuterDeepEntrance M right n) η K) right))
    (hQe : outerFullCoreQuadraticExponent C B D.a Cstar L + 2 ≤ Cbound)
    (hmass : (outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right n)).real
      (Icc (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n))
        (outerOutwardRadius right (morseOuterDeepEntrance M right n))) ≤
          lam * exp (Cbound * (n : ℝ) ^ 2))
    (hPnorm : ‖hP.toLp F.P‖ ≤ sqrt lam * exp (Cbound * (n : ℝ) ^ 2)) :
    Nonempty (MorseOuterCoreInputs entry lam Cbound
      (outerFullCoreActionExponent C B D.a) hD hphysical F) := by
  let a := outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n)
  let c := outerOutwardRadius right (morseOuterDeepEntrance M right n)
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  let Qe := outerFullCoreQuadraticExponent C B D.a Cstar L
  let τ := outerFullCoreActionExponent C B D.a * ((j : ℝ) * sqrt (morseChainA M n))
  have hi := morseTransitionOutward_interval h he right n hn.le
  rw [morseTransitionOutwardLeft_eq, morseTransitionOutwardRight_eq] at hi
  have hac : a ≤ c := hi.1.le
  have hcb : c < b := hi.2
  have hentry := morseTransitionPhysicalEntry_mem_core h he right n hn.le
  have hsmooth := outerWhole_coefficients_smooth (right := right) (J := (j : ℝ) ^ 2)
    h.geometry hentry hlam.ne'
  have hsub : Icc a c ⊆ Ico a b := fun _ hx => ⟨hx.1, hx.2.trans_lt hcb⟩
  have halpha := hsmooth.1.continuousOn.mono hsub
  have hbeta := hsmooth.2.continuousOn.mono hsub
  let Tcore := outerStateTransfer hac halpha hbeta
    (left_mem_Icc.mpr hac) (right_mem_Icc.mpr hac)
  have hB := hcell.pos
  have hC := h.constants_pos 0
  have ha := h.geometry.1
  have hQe0 : 0 ≤ Qe := by
    dsimp only [Qe, outerFullCoreQuadraticExponent, outerCoreInteriorQuadraticExponent,
      outerCoreQuadraticExponent, outerOutgoingQuadraticExponent, outerFrequencyExponent,
      outerJoinPrefactor]
    positivity
  have hτ : 0 ≤ τ := by
    dsimp only [τ, outerFullCoreActionExponent, outerCoreActionExponent, outerOutgoingActionExponent]
    positivity
  have henergy : ∀ u z : ℝ → ℝ, OuterFirstOrderSystem
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      u z (Icc a c) → ∀ s ∈ Icc a c, ∀ t ∈ Icc a c,
        u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) * exp (Qe * (n : ℝ) ^ 2 + τ) := by
    intro u z hstate s hs t ht
    have hstate' : OuterFirstOrderSystem
        (fun x => lam / outerTailOutwardWeight D right x)
        (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
        u z (Icc (morseTransitionOutwardLeft M entry right n)
          (morseTransitionOutwardRight M entry right n)) := by
      simpa only [morseTransitionOutwardLeft_eq, morseTransitionOutwardRight_eq] using hstate
    have hs' : s ∈ Icc (morseTransitionOutwardLeft M entry right n)
        (morseTransitionOutwardRight M entry right n) := by
      simpa only [morseTransitionOutwardLeft_eq, morseTransitionOutwardRight_eq] using hs
    have ht' : t ∈ Icc (morseTransitionOutwardLeft M entry right n)
        (morseTransitionOutwardRight M entry right n) := by
      simpa only [morseTransitionOutwardLeft_eq, morseTransitionOutwardRight_eq] using ht
    exact morseOuterFullCore_outward_energy_of_upper h hσ hcell hlam hL right
      hn hupper hhi hlo hstate' hs' ht'
  have hnorm : ‖Tcore.toContinuousLinearMap‖ + ‖Tcore.symm.toContinuousLinearMap‖ ≤
      exp ((Qe + 2) * (n : ℝ) ^ 2 + τ) := by
    apply outerStateTransfer_norms_le_exp hac (by omega : 1 ≤ n) halpha hbeta
      (left_mem_Icc.mpr hac) (right_mem_Icc.mpr hac) hQe0 hτ
    intro u z hstate
    constructor
    · simpa only [outerStateEnergy, mul_comm] using
        henergy u z hstate a (left_mem_Icc.mpr hac) c (right_mem_Icc.mpr hac)
    · simpa only [outerStateEnergy, mul_comm] using
        henergy u z hstate c (right_mem_Icc.mpr hac) a (left_mem_Icc.mpr hac)
  obtain ⟨A, hAnorm, hAsolve, hAunique⟩ :=
    exists_outerPhysicalDirichletInverse hD hT hphysical hj
      (show η ≤ 1 / 10 from hη.trans (by norm_num)) hKinv
  refine ⟨{
    coreTransfer := Tcore
    coreTransfer_actual := fun u z hstate => outerStateTransfer_actual
      hac halpha hbeta (left_mem_Icc.mpr hac) (right_mem_Icc.mpr hac) hstate
    transfer_bound := hnorm.trans (exp_le_exp.mpr
      (add_le_add_right (mul_le_mul_of_nonneg_right hQe (sq_nonneg _)) _))
    core_mass_bound := hmass
    poisson_memLp := hP
    poisson_bound := hPnorm
    deepInverse := A
    deep_bound := hAnorm
    deep_graph_iff := ?_
  }⟩
  intro u f
  constructor
  · exact hAunique u f
  · intro heq
    rw [← heq]
    exact hAsolve f

end ContinuousFlexibility.Radial

