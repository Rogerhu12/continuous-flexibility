module

public import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveL2
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Compactly supported radial fields belong to every weighted height space

The support is transported by the prescribed material coordinate. Its
image is compact because the original radial support stays inside the
open annulus. All material derivatives keep compact support, so every
actual weighted jet is square integrable on the material cylinder.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

private theorem scalar_hasCompactSupport_iteratedDeriv {g : ℝ → ℝ}
    (hg : HasCompactSupport g) (n : ℕ) : HasCompactSupport (iteratedDeriv n g) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hg
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

/-- A globally smooth radial field with actual compact support in the
physical core lies in every prescribed weighted height space. -/
theorem heightMember_radial_of_compact_support
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {k : ℝ → ℝ}
    (hT : IsMaterialData D T) (hk : ContDiff ℝ ∞ k)
    (hsupport : HasCompactRadialSupport D (fun p => k p.1)) :
    HeightMember D T γ (fun p => k p.1) := by
  obtain ⟨K, hK, hKcore, hKzero⟩ := hsupport
  have hdata := hT
  obtain ⟨hcont, hpos, _, _, _, _, hradius, hinside, _⟩ := hdata
  let F : ℝ → ℝ := fun x => T.H (T.radius x) ^ (-γ) * k (T.radius x)
  have hH : ContDiff ℝ ∞ (fun x => T.H (T.radius x)) :=
    (hcont T.H (by simp)).comp_contDiff hradius (fun x => (hinside x).1)
  have hF : ContDiff ℝ ∞ F :=
    (hH.rpow_const_of_ne (fun x => (hpos _ (hinside x).1).2.1.ne')).mul (hk.comp hradius)
  have hM : ContDiff ℝ ∞ (fun x => T.M (T.radius x)) :=
    (hcont T.M (by simp)).comp_contDiff hradius (fun x => (hinside x).1)
  have himage : IsCompact (T.rho '' K) :=
    hK.image_of_continuousOn ((hcont T.rho (by simp)).continuousOn.mono hKcore)
  have hFsupp : Function.support F ⊆ T.rho '' K := by
    intro x hx
    by_contra hn
    have hr : T.radius x ∉ K := by
      intro hr
      exact hn ⟨T.radius x, hr, (hinside x).2⟩
    have hz : k (T.radius x) = 0 := hKzero _ hr 0
    exact hx (by simp only [F, hz, mul_zero])
  have hFc : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact himage hFsupp
  let : IsFiniteMeasure angleMeasure :=
    ⟨by rw [scalar_angleMeasure_mass]; exact ENNReal.ofReal_lt_top⟩
  refine ⟨(hk.comp contDiff_fst).contDiffOn, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro p
    simp only [Prod.fst_add, add_zero]
  · intro p hp
    exact hKzero p.1 (fun hr => hp ⟨hKcore hr, mem_univ _⟩) p.2
  · intro a b c
    cases b with
    | zero =>
      let J : ℝ → ℝ := fun x => T.M (T.radius x) ^ c * iteratedDeriv a F x
      have hderiv : ContDiff ℝ ∞ (iteratedDeriv a F) := by
        rw [iteratedDeriv_eq_iterate]
        exact hF.iterate_deriv a
      have hJ : ContDiff ℝ ∞ J := (hM.pow c).mul hderiv
      have hJc : HasCompactSupport J := (scalar_hasCompactSupport_iteratedDeriv hFc a).mul_left
      have hJmem : MemLp J 2 (volume : Measure ℝ) :=
        hJ.continuous.memLp_of_hasCompactSupport hJc
      have he : weightedPhysicalJet T γ a 0 c (fun p => k p.1) =
          fun p => J p.1 := by
        funext p
        simp only [weightedPhysicalJet, materialPullback, mixedDerivative,
          iteratedDeriv_zero, F, J]
      rw [he, materialCylinderMeasure_eq_prod]
      exact hJmem.comp_fst angleMeasure
    | succ b =>
      have he : weightedPhysicalJet T γ a (b + 1) c (fun p => k p.1) = 0 := by
        funext p
        simp only [weightedPhysicalJet, materialPullback, mixedDerivative,
          iteratedDeriv_const, Nat.succ_ne_zero, ↓reduceIte, ite_self, mul_zero, Pi.zero_apply]
      rw [he]
      exact MemLp.zero

end ContinuousFlexibility.Statements
