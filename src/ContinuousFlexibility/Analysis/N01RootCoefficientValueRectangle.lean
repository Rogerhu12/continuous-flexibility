import ContinuousFlexibility.Analysis.N01LocalizedCoefficientBounds
import ContinuousFlexibility.Analysis.RootCoefficientDivision
import ContinuousFlexibility.Analysis.RootCoefficientValueBounds
import ContinuousFlexibility.Analysis.RootShiftMixedJets

/-!
# A positive value rectangle common to all N01 states at one root

Only the fixed reference profile and its true divided derivative are
minimized on a compact radial interval. N01's numerical Q/w and D bounds
then put the actual divided determinant and radial coefficient in one
positive rectangle, chosen before the state and angle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem positive_continuous_interval_bounds
    {f : ℝ → ℝ} {l u : ℝ} (hlu : l ≤ u)
    (hf : ContinuousOn f (Icc l u)) (hpos : ∀ x ∈ Icc l u, 0 < f x) :
    ∃ L U : ℝ, 0 < L ∧ L ≤ U ∧ ∀ x ∈ Icc l u, f x ∈ Icc L U := by
  have hne : (Icc l u).Nonempty := nonempty_Icc.mpr hlu
  obtain ⟨xmin, hxmin, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
  obtain ⟨xmax, hxmax, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf
  exact ⟨f xmin, f xmax, hpos xmin hxmin, hmin hxmax,
    fun x hx => ⟨hmin hx, hmax hx⟩⟩

theorem n01_rootCoefficient_positive_value_rectangle
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {r σ R : ℝ} {g : ℝ → ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hR : 0 < R) (hg : ContDiff ℝ ∞ g)
    (hphysical : Ioo (r - R) (r + R) ⊆ Ioo D.a D.b)
    (hstrip : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ R) :
    ∃ l₁ u₁ l₂ u₂ : ℝ, 0 < l₁ ∧ 0 < l₂ ∧ l₁ ≤ u₁ ∧ l₂ ≤ u₂ ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ p ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
        (rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
            (stateHeight D S C z) r σ p,
          polarLinearA (stateProfile D S C z.1) (stateHeight D S C z)
            (rootProfileShift r σ p)) ∈ Icc l₁ u₁ ×ˢ Icc l₂ u₂ := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hw : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  have href := hstrip (C.referenceState, 0)
    (reference_mem_stateNeighborhood S C base hN.2.1) hN.2.2.1.stateSector
  have hreference (x : ℝ) (hx : x ∈ Icc (-R) R) :
      0 < r + σ * x ∧ 0 < D.w (r + σ * x) ∧ 0 < g x := by
    have hp : (x, (0 : ℝ)) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
      refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hx.1, hx.2]
    have hh := href (x, 0) hp
    exact ⟨hh.1, hh.2.1, hh.2.2.1⟩
  have hab : -R ≤ R := neg_le_self hR.le
  have hwc : ContinuousOn (fun x => D.w (r + σ * x)) (Icc (-R) R) :=
    (hw.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
  obtain ⟨wl, wu, hwl, hwlu, hwb⟩ := positive_continuous_interval_bounds hab hwc
    (fun x hx => (hreference x hx).2.1)
  have hrc : ContinuousOn (rootProfileRadicand D.w g r σ) (Icc (-R) R) := by
    intro x hx
    exact (contDiffAt_rootProfileRadicand hw hg (hreference x hx).1.ne').continuousAt.continuousWithinAt
  obtain ⟨hl, hu, hhl, hhlu, hhb⟩ := positive_continuous_interval_bounds hab hrc
    (fun x hx => rootProfileRadicand_pos
      (hreference x hx).1 (hreference x hx).2.1 (hreference x hx).2.2)
  refine ⟨hl / 4, 4 * hu, wl / 4, 8 * wu,
    div_pos hhl (by norm_num), div_pos hwl (by norm_num), ?_, ?_, ?_⟩
  · nlinarith only [hhl, hhlu]
  · nlinarith only [hwl, hwlu]
  · intro z hz hsector p hp
    have hpc : p.1 ∈ Icc (-R) R := ⟨hp.1.1.le, hp.1.2.le⟩
    have hpouter : p ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
      refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hp.1.1, hp.1.2]
    obtain ⟨hrp, hwp, hgp, hDp, hQp, hweq, _⟩ := hstrip z hz hsector p hpouter
    have hpann : rootProfileShift r σ p ∈ annularOpen D :=
      ⟨hphysical (rootProfileShift_mem_symmetric_interval hσ hp.1), mem_univ _⟩
    have hlow := hN.2.2.2.2.2.2.2.2.2.1 z hz hsector (rootProfileShift r σ p) hpann
    have hQl : (7 / 8 : ℝ) ≤
        heightQ (profileEnergy (stateProfile D S C z.1) (rootProfileShift r σ p))
          (heightRadial (stateHeight D S C z) (rootProfileShift r σ p))
          (angularPartial (heightAngular (stateHeight D S C z)) (rootProfileShift r σ p)) /
            D.w (rootProfileShift r σ p).1 := by
      simpa only [hweq] using hlow.2.2.1
    have hQu :
        heightQ (profileEnergy (stateProfile D S C z.1) (rootProfileShift r σ p))
          (heightRadial (stateHeight D S C z) (rootProfileShift r σ p))
          (angularPartial (heightAngular (stateHeight D S C z)) (rootProfileShift r σ p)) /
            D.w (rootProfileShift r σ p).1 ≤ (9 / 8 : ℝ) := by
      simpa only [hweq] using hlow.2.2.2.1
    have ha := root_radial_coefficient_relative_bounds hwp hQl hQu
      hlow.2.2.2.2.1 hlow.2.2.2.2.2
    change D.w (rootProfileShift r σ p).1 / 4 ≤
      polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) (rootProfileShift r σ p) ∧
      polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) (rootProfileShift r σ p) ≤
        8 * D.w (rootProfileShift r σ p).1 at ha
    have hh := root_positive_square_denominator_bounds
      (rootProfileRadicand_pos hrp hwp hgp).le hlow.2.2.2.2.1 hlow.2.2.2.2.2
    rw [← rootCoefficientRadialFactor_eq hrp hwp hgp hDp hQp.ne'] at hh
    have hwbound : D.w (rootProfileShift r σ p).1 ∈ Icc wl wu := hwb p.1 hpc
    have hhbound := hhb p.1 hpc
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · linarith only [hh.1, hhbound.1]
    · linarith only [hh.2, hhbound.2]
    · linarith only [ha.1, hwbound.1]
    · linarith only [ha.2, hwbound.2]

end ContinuousFlexibility.Analysis
