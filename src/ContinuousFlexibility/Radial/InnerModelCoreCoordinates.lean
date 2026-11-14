module

public import ContinuousFlexibility.Radial.InnerDirichletDomain

/-!
# Supported representatives of the actual interval energy core

The original core only states support for the value coordinate.
Smoothness implies that the derivative also vanishes off the closed
interval; its two endpoints have zero Lebesgue measure. Both L²
coordinates therefore have the actual open-interval indicator form.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem innerModelCore_indicator_representatives {a b : ℝ} {V : ℝ → ℝ}
    (hab : a < b) {t : RadialL2 × RadialL2 × RadialL2}
    (ht : t ∈ IntervalEnergyCore V a b) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ HasCompactSupport p ∧
      EqOn p (fun _ => 0) ((Ioo a b)ᶜ) ∧
      (t.1 : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p ∧
      (t.2.1 : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p) := by
  obtain ⟨p, hp, hcp, hval, hderiv, _hpot⟩ := ht.1
  have hvalout : (t.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] p :=
    ae_restrict_of_ae hval
  have hpout : p =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0) :=
    Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hvalout) ht.2
  have hzero := innerDirichlet_representative_zero_outside hab hp.continuous hpout
  refine ⟨p, hp, hcp, hzero, ?_, ?_⟩
  · filter_upwards [hval] with x hx
    rw [hx]
    by_cases hi : x ∈ Ioo a b
    · rw [indicator_of_mem hi]
    · rw [indicator_of_notMem hi]
      exact hzero hi
  · have hna : ∀ᵐ x : ℝ ∂volume, x ≠ a := by simp [ae_iff]
    have hnb : ∀ᵐ x : ℝ ∂volume, x ≠ b := by simp [ae_iff]
    filter_upwards [hderiv, hna, hnb] with x hx hxa hxb
    rw [hx]
    by_cases hi : x ∈ Ioo a b
    · rw [indicator_of_mem hi]
    · rw [indicator_of_notMem hi]
      have hout : x ∉ Icc a b := by
        intro hcc
        exact hi ⟨lt_of_le_of_ne hcc.1 (Ne.symm hxa), lt_of_le_of_ne hcc.2 hxb⟩
      have hn : p =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hout] with y hy
        exact hzero (fun h => hy (Ioo_subset_Icc_self h))
      exact hn.deriv_eq.trans (deriv_const x 0)

end ContinuousFlexibility.Radial
