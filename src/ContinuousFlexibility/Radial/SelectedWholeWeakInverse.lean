import ContinuousFlexibility.Radial.SelectedWholeGreenKernel
import ContinuousFlexibility.Radial.SelectedOuterNaturalUniqueness
import ContinuousFlexibility.Radial.SelectedOuterTestIntegrability
import ContinuousFlexibility.Radial.SelectedOuterWeakDuality

/-!
# The actual weighted weak inverse at the original outer cut

The deep Friedrichs inverse, its actual physical kernel, and finite-core
ODE continuation construct one bounded operator. Its regular response,
symmetry and homogeneous Robin uniqueness are consequences of that
construction, rather than inputs from the matching realization.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

namespace MorsePhysicalTailBasis

variable {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
  {entrance η K cut lam : ℝ}
  (F : MorsePhysicalTailBasis M D right j start entrance η K)

local notation "a" => outerTailSign right * cut
local notation "c" => outerTailSign right * entrance
local notation "b" => outerTailSign right * tailPhysicalEndpoint D right
local notation "T" => morsePhysicalDeepTail M D right j start entrance η K
local notation "w" => outerTailOutwardWeight D right
local notation "ρ" => selectedOutwardDensity D right
local notation "μ" => outerOutwardIntervalMeasure D right (radialTailInterval D right cut)
local notation "ν" => (volume.restrict (Ioo a b)).withDensity (fun x => ENNReal.ofReal (ρ x))
local notation "α" => (fun x => lam / w x)
local notation "β" => (fun x => (j : ℝ) ^ 2 * deriv w x / (lam * x))

theorem exists_wholeWeakInverse
    (hD : IsAccumulatingProfile D) (hcut : cut ∈ radialCore D)
    (hentry : entrance ∈ radialCore D) (hac : a < c) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K) :
    ∃ H : OuterFundamentalStatePair α β F.P (F.ZP lam) F.Q (F.ZQ lam) a c b,
      ∃ R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
        OuterWeightedGreenResponse μ w ρ a b ((j : ℝ) ^ 2) lam H.entrance R ∧
        R.toLinearMap.IsSymmetric ∧
        OuterWeightedHomogeneousUnique μ w a b ((j : ℝ) ^ 2) lam H.entrance := by
  have hex := F.exists_wholeGreenOperator hD hcut hentry hac.le hlam hT hphysical
    hη hK hKinv
  dsimp only at hex
  simp only [outerOutwardRegionMeasure_eq_density, outerOutwardRadius_eq_sign] at hex ⊢
  obtain ⟨H, R, hR, hrow⟩ := hex
  have hg := matchingProfileGeometry hD
  have hep : 0 < entrance := hg.1.trans hentry.1
  have hcb : c < b := by
    cases right
    · simpa [outerTailSign, tailPhysicalEndpoint] using neg_lt_neg hentry.1
    · simpa [outerTailSign, tailPhysicalEndpoint] using hentry.2
  letI : IsFiniteMeasure ν := by
    simpa only [outerOutwardRegionMeasure_eq_density, outerOutwardRadius_eq_sign] using
      isFiniteMeasure_outerOutwardRegion hD hcut
  have hw : ContDiff ℝ ∞ w := hg.2.2.1.1.comp (contDiff_const.mul contDiff_id)
  have hcore (x : ℝ) (hx : x ∈ Ico a b) : outerOutwardRadius right x ∈ radialCore D :=
    outerOutwardRadius_mem_core hcut (by simpa only [outerOutwardRadius_eq_sign] using hx)
  have hwn (x : ℝ) (hx : x ∈ Ico a b) : w x ≠ 0 := by
    change D.w (outerTailSign right * x) ≠ 0
    rw [← outerOutwardRadius_eq_sign]
    exact (hg.2.2.2.2.1 _ (hcore x hx)).ne'
  have hr (x : ℝ) (hx : x ∈ Ico a b) : x ≠ 0 := by
    have hp : 0 < outerOutwardRadius right x := hg.1.trans (hcore x hx).1
    intro hz
    rw [hz, outerOutwardRadius_eq_sign, mul_zero] at hp
    exact (lt_irrefl 0) hp
  have hρ₀ (x : ℝ) (hx : x ∈ Ioo a b) : 0 ≤ ρ x := by
    apply (selectedOutwardDensity_pos hD hcut _).le
    simpa only [outerOutwardRadius_eq_sign] using Ioo_subset_Ico_self hx
  have her : tailPhysicalRadius right T.entrance = entrance := tailPhysicalRadius_log right hep
  have horder : outerOutwardRadius right cut ≤
      outerOutwardRadius right (tailPhysicalRadius right T.entrance) := by
    simpa only [her, outerOutwardRadius_eq_sign] using hac.le
  have hm := outerOutwardRegion_restrict_deep hD hphysical horder
  simp only [her, outerOutwardRegionMeasure_eq_density, outerOutwardRadius_eq_sign] at hm
  have hPLp : MemLp F.P 2 (ν.restrict (Icc a c)ᶜ) := by
    rw [hm]
    exact morsePhysicalDeepTail_outward_lift_memLp hg hep hT F.P_natural
  have hfull : ∀ᵐ x ∂ν, x ∈ Ioo a b :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)
  refine ⟨H, R, ?_, ?_, ?_⟩
  · exact H.weighted_solution hac.le hcb hlam hw hwn hr
      (selectedOutwardDensity_measurable hD right) hρ₀ F.P_entrance hPLp R hR hrow
  · exact outerGreenOperator_isSymmetric ν hfull
      (H.U_system.continuousOn.1.mono Ioo_subset_Ico_self)
      (H.V_system.continuousOn.1.mono Ioo_subset_Ico_self) R hR
  · intro u z hu hz hsys hL2 hRobin
    have hL2' : MemLp u 2 μ := by
      simpa only [outerOutwardRegionMeasure_eq_density, outerOutwardRadius_eq_sign] using hL2
    exact F.whole_robin_unique hD hcut hentry hac hlam hT hphysical hη hK
      H hu hz hsys hL2' hRobin

/-- The Robin condition agrees with the full state of any fixed nonzero
actual natural representative. The natural representative is not reselected. -/
theorem whole_natural_robin_iff
    (hD : IsAccumulatingProfile D) (hcut : cut ∈ radialCore D)
    (hentry : entrance ∈ radialCore D) (hac : a < c) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (H : OuterFundamentalStatePair α β F.P (F.ZP lam) F.Q (F.ZQ lam) a c b)
    {u z : ℝ → ℝ} (hu : ContinuousOn u (Ico a b)) (hz : ContinuousOn z (Ico a b))
    (hsys : OuterFirstOrderSystem α β u z (Ioo a b))
    (hL2 : MemLp u 2 μ) (hne : (u a, z a) ≠ 0) (q : ℝ × ℝ) :
    outerStatePair (u a, z a) q = 0 ↔ outerStatePair H.entrance q = 0 := by
  obtain ⟨k, hk⟩ := F.whole_natural_line hD hcut hentry hac hlam hT hphysical
    hη hK H hu hz hsys hL2
  have hcb : c < b := by
    cases right
    · simpa [outerTailSign, tailPhysicalEndpoint] using neg_lt_neg hentry.1
    · simpa [outerTailSign, tailPhysicalEndpoint] using hentry.2
  have ha : a ∈ Ico a b := ⟨le_rfl, hac.trans hcb⟩
  have he : (u a, z a) = k • H.entrance := by
    apply Prod.ext
    · change u a = k * H.entrance.1
      rw [← congrArg Prod.fst H.V_initial]
      exact (hk a ha).1
    · change z a = k * H.entrance.2
      rw [← congrArg Prod.snd H.V_initial]
      exact (hk a ha).2
  have hkne : k ≠ 0 := by
    intro hz
    apply hne
    rw [he, hz, zero_smul]
  rw [he]
  change k * H.entrance.1 * q.1 + k * H.entrance.2 * q.2 = 0 ↔
    H.entrance.1 * q.1 + H.entrance.2 * q.2 = 0
  have heq : k * H.entrance.1 * q.1 + k * H.entrance.2 * q.2 =
      k * (H.entrance.1 * q.1 + H.entrance.2 * q.2) := by ring
  rw [heq, mul_eq_zero]
  constructor
  · intro h
    exact h.resolve_left hkne
  · exact Or.inr

end MorsePhysicalTailBasis

end ContinuousFlexibility.Radial
