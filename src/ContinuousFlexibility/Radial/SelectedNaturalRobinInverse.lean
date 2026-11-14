module

public import ContinuousFlexibility.Radial.SelectedTailCauchyUniqueness
public import ContinuousFlexibility.Radial.SelectedTailWeakPairing

/-!
# The actual inverse with the fixed natural solution's Robin state

The natural solution supplied by the selected construction is kept fixed.
Its state belongs to the same natural line as the deep factory's state,
so its normalized full state gives exactly the constructed Robin domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem outerUnitState_pair_zero_iff {v : ℝ × ℝ} (hv : v ≠ 0) (q : ℝ × ℝ) :
    outerStatePair (outerUnitState v) q = 0 ↔ outerStatePair v q = 0 := by
  have hL := (sqrt_pos.mpr (outerState_sq_pos hv)).ne'
  have he : outerStatePair (outerUnitState v) q =
      outerStatePair v q / sqrt (v.1 ^ 2 + v.2 ^ 2) := by
    simp only [outerStatePair, outerUnitState]
    ring
  rw [he, div_eq_zero_iff]
  simp only [hL, or_false]

theorem smoothJacobi_outerFirstOrder {w u : ℝ → ℝ} {I : Set ℝ} {J lam : ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (hlam : lam ≠ 0)
    (hwn : ∀ x ∈ I, w x ≠ 0)
    (hEq : ∀ x ∈ I, radialJacobi J w u x = 0) :
    OuterFirstOrderSystem (fun x => lam / w x) (fun x => J * deriv w x / (lam * x))
      u (fun x => w x * deriv u x / lam) I := by
  have hflux : ContDiff ℝ ∞ (fun x => w x * deriv u x) :=
    hw.mul (contDiff_infty_iff_deriv.mp hu).2
  intro x hx
  constructor
  · apply (hu.differentiable (by simp) x).hasDerivAt.congr_deriv
    field_simp [hlam, hwn x hx]
  · apply ((hflux.differentiable (by simp) x).hasDerivAt.div_const lam).congr_deriv
    have hd : deriv (fun t => w t * deriv u t) x = J * deriv w x / x * u x := by
      have hh := hEq x hx
      unfold radialJacobi at hh
      linarith only [hh]
    rw [hd]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

namespace MorsePhysicalTailBasis

variable {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
  {entrance η K cut lam : ℝ}
  (F : MorsePhysicalTailBasis M D right j start entrance η K)

/-- The full state of the supplied natural function determines exactly
the Robin line of the supplied homogeneous pair.  The direction of the
unit state is irrelevant; the original natural function is not reselected. -/
theorem radialNatural_robin_iff
    (hD : IsAccumulatingProfile D) (hcut : cut ∈ radialCore D)
    (hentry : entrance ∈ radialCore D)
    (hac : outerTailSign right * cut < outerTailSign right * entrance) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start entrance η K) right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      F.P (F.ZP lam) F.Q (F.ZQ lam)
      (outerTailSign right * cut) (outerTailSign right * entrance)
      (outerTailSign right * tailPhysicalEndpoint D right))
    {V : ℝ → ℝ} (hV : ContDiff ℝ ∞ V) (hN : RadialNaturalTail D right j cut V)
    (hne : (V cut, outerTailSign right * D.w cut * deriv V cut / lam) ≠ 0)
    (q : ℝ × ℝ) :
    outerStatePair (outerUnitState
      (V cut, outerTailSign right * D.w cut * deriv V cut / lam)) q = 0 ↔
        outerStatePair H.entrance q = 0 := by
  let a := outerTailSign right * cut
  let b := outerTailSign right * tailPhysicalEndpoint D right
  let w := outerTailOutwardWeight D right
  let y : ℝ → ℝ := fun x => V (outerOutwardRadius right x)
  let z : ℝ → ℝ := fun x => w x * deriv y x / lam
  have hw : ContDiff ℝ ∞ w :=
    (matchingProfileGeometry hD).2.2.1.1.comp (contDiff_const.mul contDiff_id)
  have hy : ContDiff ℝ ∞ y := hV.comp (contDiff_outerOutwardRadius right)
  have hz : ContDiff ℝ ∞ z := (hw.mul (contDiff_infty_iff_deriv.mp hy).2).div_const lam
  have hstate : OuterFirstOrderSystem (fun x => lam / w x)
      (fun x => (j : ℝ) ^ 2 * deriv w x / (lam * x)) y z (Ioo a b) := by
    apply smoothJacobi_outerFirstOrder hw hy hlam
    · intro x hx
      have hcore := outerOutwardRadius_mem_core hcut
        (by simpa only [a, b, outerOutwardRadius_eq_sign] using Ioo_subset_Ico_self hx)
      simpa only [w, outerTailOutwardWeight, outerOutwardRadius_eq_sign] using
        ((matchingProfileGeometry hD).2.2.2.2.1 _ hcore).ne'
    · intro x hx
      have hi : outerOutwardRadius right x ∈ radialTailInterval D right cut := by
        apply (radialTailInterval_outward D right cut _).mpr
        simpa only [outerOutwardRadius_twice] using hx
      have he := radialJacobi_outward D right ((j : ℝ) ^ 2) V x
      exact he.trans (hN.2.1.2 _ hi)
  have hyLp : MemLp y 2
      (outerOutwardIntervalMeasure D right (radialTailInterval D right cut)) := by
    rw [outerOutwardRegionMeasure_eq_map hcut]
    apply (measurableEmbedding_outerOutwardRadius right).memLp_map_measure_iff.mpr
    simpa only [Function.comp_def, y, outerOutwardRadius_twice] using hN.2.2.1
  have hstateCut : (y a, z a) =
      (V cut, outerTailSign right * D.w cut * deriv V cut / lam) := by
    have hyfun : y = fun x => V (outerTailSign right * x) := by
      funext x
      rw [← outerOutwardRadius_eq_sign]
    have hdy : deriv y a = outerTailSign right * deriv V cut := by
      rw [hyfun, deriv_comp_mul_left]
      simp only [smul_eq_mul, a, ← mul_assoc, outerTailSign_mul_self, one_mul]
    apply Prod.ext
    · simp only [y, a, outerOutwardRadius_eq_sign, ← mul_assoc, outerTailSign_mul_self, one_mul]
    · dsimp only [z]
      rw [hdy]
      simp only [w, outerTailOutwardWeight, a, ← mul_assoc, outerTailSign_mul_self, one_mul]
      ring
  rw [outerUnitState_pair_zero_iff hne]
  have hs := F.whole_natural_robin_iff hD hcut hentry hac hlam hT hphysical hη hK
    H hy.continuous.continuousOn hz.continuous.continuousOn hstate hyLp
    (by rwa [hstateCut]) q
  rwa [hstateCut] at hs

include F in
/-- A bounded regional inverse with the genuine selected natural full
state. The input natural function is used only to identify the Robin line;
the inverse itself is constructed from the deep kernel and finite core. -/
theorem exists_radialNaturalInverse
    (hD : IsAccumulatingProfile D) (hcut : cut ∈ radialCore D)
    (hentry : entrance ∈ radialCore D)
    (hac : outerTailSign right * cut < outerTailSign right * entrance) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start entrance η K) right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K)
    {V : ℝ → ℝ} (hV : ContDiff ℝ ∞ V) (hN : RadialNaturalTail D right j cut V)
    (hne : (V cut, outerTailSign right * D.w cut * deriv V cut / lam) ≠ 0) :
    let v := outerUnitState (V cut, outerTailSign right * D.w cut * deriv V cut / lam)
    ∃ R : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)),
      RadialTailWeakPairing D hD right cut j R ∧
        RadialTailRegularResponse D right cut lam v R ∧
        RadialTailCauchyUnique D right cut ((j : ℝ) ^ 2) lam v := by
  obtain ⟨H, R, hR, hsym, hUniq⟩ := F.exists_wholeWeakInverse hD hcut hentry hac
    hlam hT hphysical hη hK hKinv
  have hequiv (q : ℝ × ℝ) :
      outerStatePair (outerUnitState (V cut,
        outerTailSign right * D.w cut * deriv V cut / lam)) q = 0 ↔
        outerStatePair H.entrance q = 0 :=
    F.radialNatural_robin_iff hD hcut hentry hac hlam hT hphysical hη hK H hV hN hne q
  refine ⟨outerRadialRegionOperator hcut R, ?_, ?_, ?_⟩
  · intro ψ hψ hs f
    exact outerRadialRegionOperator_test_pairing hD hcut hlam hR hUniq hsym hψ hs f
  · intro f
    obtain ⟨u, he, hu, hb⟩ := hR.radial_regular hcut f
    exact ⟨u, he, hu, (hequiv _).mpr hb⟩
  · intro u p hu hp hsys hLp hRobin
    exact (hUniq.radial hD hcut hlam) u p hu hp hsys hLp ((hequiv _).mp hRobin)

end MorsePhysicalTailBasis

end ContinuousFlexibility.Radial
