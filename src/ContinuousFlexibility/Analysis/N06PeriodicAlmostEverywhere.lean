module

public import ContinuousFlexibility.Analysis.N06ChartAlmostEverywhere

/-!
# Extending almost-everywhere identities from a half-period tile

The exceptional set in the whole strip is contained in the countable
union of angular translates of its exceptional set in the measured tile.
Translations preserve null sets. No continuity of the representatives
and no pointwise identity inferred from an L² class are used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n06_periodic_ae_eq_on_strip {l r : ℝ} {f g : PolarPoint → ℝ}
    (hf : ∀ y ∈ Ioo l r, Function.Periodic (fun θ => f (y, θ)) Real.pi)
    (hg : ∀ y ∈ Ioo l r, Function.Periodic (fun θ => g (y, θ)) Real.pi)
    (heq : f =ᵐ[volume.restrict (Ioo l r ×ˢ Ioc (0 : ℝ) Real.pi)] g) :
    f =ᵐ[volume.restrict (Ioo l r ×ˢ (univ : Set ℝ))] g := by
  classical
  let E : Set PolarPoint := {p | p ∈ Ioo l r ×ˢ Ioc (0 : ℝ) Real.pi ∧ f p ≠ g p}
  have hE : volume E = 0 := by
    have hh := ae_iff.mp ((ae_restrict_iff'
      (measurableSet_Ioo.prod measurableSet_Ioc)).mp heq)
    exact measure_mono_null (fun p hp => fun h => hp.2 (h hp.1)) hh
  let shift : ℤ → PolarPoint → PolarPoint := fun k p => (p.1, p.2 + k • Real.pi)
  have hshift (k : ℤ) : Differentiable ℝ (shift k) :=
    differentiable_fst.prodMk (differentiable_snd.add_const _)
  have hnull : volume (⋃ k : ℤ, shift k '' E) = 0 :=
    measure_iUnion_null fun k =>
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (hshift k).differentiableOn hE
  have havoid : ∀ᵐ p ∂volume, p ∉ ⋃ k : ℤ, shift k '' E := by
    apply ae_iff.mpr
    exact measure_mono_null (fun _ hp => Classical.not_not.mp hp) hnull
  apply (ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)).mpr
  filter_upwards [havoid] with p hp hpU
  by_contra hne
  let k : ℤ := toIocDiv Real.pi_pos 0 p.2
  let q : PolarPoint := (p.1, toIocMod Real.pi_pos 0 p.2)
  have hq : q ∈ Ioo l r ×ˢ Ioc (0 : ℝ) Real.pi := by
    refine ⟨hpU.1, ?_⟩
    simpa only [q, zero_add] using toIocMod_mem_Ioc Real.pi_pos 0 p.2
  have hfp : f q = f p := by
    simpa only [q, toIocMod, k] using (hf p.1 hpU.1).sub_zsmul_eq (x := p.2) k
  have hgp : g q = g p := by
    simpa only [q, toIocMod, k] using (hg p.1 hpU.1).sub_zsmul_eq (x := p.2) k
  have hqE : q ∈ E := ⟨hq, fun h => hne (hfp.symm.trans (h.trans hgp))⟩
  apply hp
  apply mem_iUnion.mpr
  refine ⟨k, q, hqE, ?_⟩
  apply Prod.ext
  · rfl
  · simp only [shift, q, toIocMod, k, sub_add_cancel]

end ContinuousFlexibility.Statements
