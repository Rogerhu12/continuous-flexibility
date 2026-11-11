import ContinuousFlexibility.Radial.OuterPhysicalRobinSolution
import ContinuousFlexibility.Radial.OuterPhysicalTailUniqueness

/-!
# Uniqueness in the actual physical outer Robin graph

The difference of two graph solutions is a genuine homogeneous state in
the interior.  Its restriction to the actual deep weighted space lies on
the already proved natural line.  The normalized full entrance state then
forces the difference to vanish, without dividing by V at that entrance.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem MorsePhysicalTailBasis.whole_robin_graph_unique
    {M : MorseChainData} {D : ReferenceData}
    {right : Bool} {j start : ℕ} {entry deep η K lam : ℝ}
    (F : MorsePhysicalTailBasis M D right j start deep η K)
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      F.P (F.ZP lam) F.Q (F.ZQ lam)
      (outerOutwardRadius right entry) (outerOutwardRadius right deep)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hD : IsAccumulatingProfile D)
    (hentry : entry ∈ radialCore D) (hdeep : deep ∈ radialCore D)
    (horder : outerOutwardRadius right entry < outerOutwardRadius right deep)
    (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start deep η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    {U₀ U₁ f : OuterWholeL2 D right entry}
    (h₀ : OuterRobinWeakGraph (outerWholeMeasure D right entry)
      (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) ((j : ℝ) ^ 2) lam
      (outerTailOutwardWeight D right) (outerWholeDensity D right) H.entrance U₀ f)
    (h₁ : OuterRobinWeakGraph (outerWholeMeasure D right entry)
      (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) ((j : ℝ) ^ 2) lam
      (outerTailOutwardWeight D right) (outerWholeDensity D right) H.entrance U₁ f) :
    U₀ = U₁ := by
  let μ := outerWholeMeasure D right entry
  let a := outerOutwardRadius right entry
  let c := outerOutwardRadius right deep
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  let w := outerTailOutwardWeight D right
  let T := morsePhysicalDeepTail M D right j start deep η K
  have hab : a < b := outerWhole_interval hentry
  have hcb : c < b := outerWhole_interval hdeep
  have hgeom := matchingProfileGeometry hD
  have hw : ContDiff ℝ ∞ w := outerWhole_weight_smooth hgeom right
  have hwne : ∀ x ∈ Ico a b, w x ≠ 0 :=
    fun x hx => (outerWhole_weight_pos hgeom hentry hx).ne'
  have hxne : ∀ x ∈ Ico a b, x ≠ 0 :=
    fun x hx => outerWhole_coordinate_ne_zero hgeom hentry hx
  have hκ : ContinuousOn (fun x => (j : ℝ) ^ 2 * deriv w x / x) (Ioo a b) :=
    (continuousOn_const.mul
      (contDiff_infty_iff_deriv.mp hw).2.continuous.continuousOn).div continuousOn_id
        (fun x hx => hxne x (Ioo_subset_Ico_self hx))
  have hf : LocallyIntegrableOn (fun x => outerWholeDensity D right x * f x) (Ioo a b) := by
    simpa only [Pi.neg_apply, neg_neg] using
      (outerWholeSource_integrable hD hentry f).neg.locallyIntegrableOn
  obtain ⟨u, z, hae, hu, hz, hstate, hRobin⟩ :=
    OuterRobinWeakGraph.homogeneous_difference hab hlam hwne hκ hf h₀ h₁
  have hum : MemLp u 2 μ := (memLp_congr_ae hae).mp (Lp.memLp (U₀ - U₁))
  have hdeepPos : 0 < deep := hgeom.1.trans hdeep.1
  have hcoord : tailPhysicalRadius right T.entrance = deep :=
    tailPhysicalRadius_log right hdeepPos
  have hm : μ.restrict (Icc a c)ᶜ = outerOutwardTailMeasure D T right := by
    calc
      μ.restrict (Icc a c)ᶜ = outerWholeMeasure D right deep :=
        outerWholeMeasure_restrict_deep hentry hdeep horder.le
      _ = outerWholeMeasure D right (tailPhysicalRadius right T.entrance) :=
        congrArg (outerWholeMeasure D right) hcoord.symm
      _ = _ := outerWholeMeasure_tail D T right
  have humdeep : MemLp u 2 (outerOutwardTailMeasure D T right) := by
    rw [← hm]
    exact hum.restrict (Icc a c)ᶜ
  have hsys : OuterFirstOrderSystem
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      u z (Ico (outerTailSign right * deep)
        (outerTailSign right * tailPhysicalEndpoint D right)) := by
    intro x hx
    have hx' : x ∈ Ico c b := by
      simpa only [c, b, outerOutwardRadius_eq_sign] using hx
    exact hstate x ⟨horder.trans_le hx'.1, hx'.2⟩
  obtain ⟨A, hA⟩ := MorsePhysicalTailBasis.natural_line
    hgeom hdeepPos hlam hT hη hK F hsys humdeep
  have hnatural : ∃ C : ℝ, ∀ x ∈ Ioo c b, u x = C * F.P x := by
    refine ⟨A, ?_⟩
    intro x hx
    apply (hA x _).1
    simpa only [c, b, outerOutwardRadius_eq_sign] using (Ioo_subset_Ico_self hx)
  have hzero := H.robin_unique_continuous_state horder.le hcb
    (fun x hx => div_ne_zero hlam (hwne x ⟨horder.le.trans hx.1.le, hx.2⟩))
    hu hz hstate hRobin hnatural
  apply sub_eq_zero.mp
  apply Lp.ext
  filter_upwards [hae, outerWholeMeasure_ae_mem hentry, Lp.coeFn_zero ℝ 2 μ]
    with x hx hxi hzeroLp
  calc
    (U₀ - U₁ : Lp ℝ 2 μ) x = u x := hx
    _ = 0 := (hzero x (Ioo_subset_Ico_self hxi)).1
    _ = (0 : Lp ℝ 2 μ) x := by simpa only [Pi.zero_apply] using hzeroLp.symm

end ContinuousFlexibility.Radial
