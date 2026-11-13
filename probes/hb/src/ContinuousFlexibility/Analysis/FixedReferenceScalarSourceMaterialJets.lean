import ContinuousFlexibility.Analysis.RadialReferencePotentialJetEnvelope
import ContinuousFlexibility.Analysis.N06ReferenceSourceJets
import Mathlib.Topology.Order.Compact

/-!
# Scalar source jets in one fixed radial reference family

A reference source is the actual radial source factor times the physical
radial profile pulled back by the same inverse, times its angular mode.
Only numerical constants are selected below. The factor, inverse and
original sample weight are inputs shared by every derivative order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

private theorem referenceScalarSource_compact_prefix
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (l r : ℝ) (N : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ k, k ≤ N → ∀ x ∈ Icc l r,
      |iteratedDeriv k f x| ≤ P := by
  classical
  have hb (k : Fin (N + 1)) : ∃ A : ℝ, ∀ x ∈ Icc l r,
      ‖iteratedDeriv k.val f x‖ ≤ A :=
    isCompact_Icc.exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedDeriv k.val hf (by simp)).continuousOn
  choose A hA using hb
  refine ⟨∑ k : Fin (N + 1), |A k|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro k hk x hx
  let j : Fin (N + 1) := ⟨k, by omega⟩
  have hj : |iteratedDeriv k f x| ≤ A j := by
    simpa only [Real.norm_eq_abs] using hA j x hx
  exact (hj.trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun k => |A k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))

/-- The given inverse and source factor determine every scalar source.
Only positive inverse derivatives are charged; its value is used through
the genuine physical range. The angular profile has its actual period. -/
theorem fixedReferenceScalarSource_material_jets
    {ι : Type*} (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i)
    (X F : ι → ℝ → ℝ) (l r : ℝ)
    (hX : ∀ i, ContDiffOn ℝ ∞ (X i) (Ioo (0 : ℝ) 1))
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (Ioo (0 : ℝ) 1))
    (hrange : ∀ i x, x ∈ Ioo (0 : ℝ) 1 → X i x ∈ Icc l r)
    (hjets : ∀ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ i x,
      x ∈ Ioo (0 : ℝ) 1 → ∀ k, k ≤ N →
        |iteratedDeriv k (F i) x| ≤ A * W i ^ A ∧
        (1 ≤ k → |iteratedDeriv k (X i) x| ≤ A * W i ^ A))
    (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hgperiod : Function.Periodic g Real.pi) :
    ∀ s : ℕ, ∃ M : ℝ, 1 ≤ M ∧ ∀ i,
      let V := fun p : PolarPoint => F i p.1 * f (X i p.1) * g p.2
      ContDiffOn ℝ ∞ V unitStrip ∧
      (∀ p ∈ unitStrip, V (p + (0, Real.pi)) = V p) ∧
      ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b V p| ≤ M * W i ^ M := by
  intro s
  obtain ⟨A, hA, hactual⟩ := hjets s
  obtain ⟨P, hP, hprofile⟩ := referenceScalarSource_compact_prefix hf l r s
  have hgplane : ContDiff ℝ ∞ (fun p : PolarPoint => g p.2) := hg.comp contDiff_snd
  have hgplanePeriod : Function.Periodic (fun p : PolarPoint => g p.2) (0, Real.pi) := by
    intro p
    exact hgperiod p.2
  obtain ⟨G, hG, hangular⟩ :=
    n06_smooth_periodic_angularJets_bounded hgplane hgplanePeriod 0 0 s
  obtain ⟨CC, hCC, hcomp⟩ := referencePotential_composition_envelope s
  obtain ⟨CP, hCP, hprod⟩ := referencePotential_product_envelope s
  let coefficient : ℝ := CP * CC * P * G * A ^ (s + 1)
  let exponent : ℝ := A * ((s + 1 : ℕ) : ℝ)
  let M : ℝ := 1 + coefficient + exponent
  have hcoefficient : 0 ≤ coefficient :=
    mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (zero_le_one.trans hCP) (zero_le_one.trans hCC)) hP) hG.le)
      (pow_nonneg (zero_le_one.trans hA) _)
  have hexponent : 0 ≤ exponent :=
    mul_nonneg (zero_le_one.trans hA) (Nat.cast_nonneg _)
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hcoefficient, hexponent]
  have hcM : coefficient ≤ M := by dsimp only [M]; linarith only [hexponent]
  have heM : exponent ≤ M := by dsimp only [M]; linarith only [hcoefficient]
  refine ⟨M, hM, ?_⟩
  intro i
  dsimp only
  have hXa (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : ContDiffAt ℝ ∞ (X i) x :=
    (hX i x hx).contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hFa (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : ContDiffAt ℝ ∞ (F i) x :=
    (hF i x hx).contDiffAt (isOpen_Ioo.mem_nhds hx)
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact ((((hFa p.1 hp.1).comp p contDiffAt_fst).mul
      ((hf.contDiffAt.comp p.1 (hXa p.1 hp.1)).comp p contDiffAt_fst)).mul
      (hg.contDiffAt.comp p contDiffAt_snd)).contDiffWithinAt
  · intro p hp
    simp only [Prod.fst_add, Prod.snd_add, add_zero, hgperiod p.2]
  · intro p hp a b hab
    have ha : a ≤ s := by omega
    have hb : b ≤ s := by omega
    let Z : ℝ := A * W i ^ A
    have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le hA
      (Real.one_le_rpow (hW i) (zero_le_one.trans hA))
    have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
    have hcomposed (k : ℕ) (hk : k ≤ s) :
        |iteratedDeriv k (f ∘ X i) p.1| ≤ CC * P * Z ^ s :=
      hcomp hP hZ f (X i) p.1 hf.contDiffAt (hXa p.1 hp.1)
        (fun j hj => hprofile j hj _ (hrange i p.1 hp.1))
        (fun j hj hjs => (hactual i p.1 hp.1 j hjs).2 hj) k hk
    have hcomp0 : 0 ≤ CC * P * Z ^ s :=
      mul_nonneg (mul_nonneg (zero_le_one.trans hCC) hP) (pow_nonneg hZ0 _)
    have hradial : |iteratedDeriv a (fun t => F i t * f (X i t)) p.1| ≤
        CP * Z * (CC * P * Z ^ s) :=
      hprod hZ0 hcomp0 (F i) (f ∘ X i) p.1 (hFa p.1 hp.1)
        (hf.contDiffAt.comp p.1 (hXa p.1 hp.1))
        (fun j hj => (hactual i p.1 hp.1 j hj).1) hcomposed a ha
    have hang : |iteratedDeriv b g p.2| ≤ G := by
      have hh := hangular b hb ((0 : ℝ), p.2) ⟨le_rfl, le_rfl⟩
      simpa only [mixedDerivative, iteratedDeriv_zero] using hh
    have hradial0 : 0 ≤ CP * Z * (CC * P * Z ^ s) :=
      mul_nonneg (mul_nonneg (zero_le_one.trans hCP) hZ0) hcomp0
    calc
      _ = |iteratedDeriv a (fun t => F i t * f (X i t)) p.1| *
          |iteratedDeriv b g p.2| := by
        simp only [mixedDerivative, iteratedDeriv_const_mul_field,
          iteratedDeriv_mul_const_field, abs_mul]
      _ ≤ (CP * Z * (CC * P * Z ^ s)) * G :=
        mul_le_mul hradial hang (abs_nonneg _) hradial0
      _ = (CP * CC * P * G) * Z ^ (s + 1) := by rw [pow_succ]; ring
      _ = coefficient * W i ^ exponent := by
        dsimp only [Z, coefficient, exponent]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans (hW i)) A (s + 1)]
        ring
      _ ≤ coefficient * W i ^ M := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hW i) heM) hcoefficient
      _ ≤ M * W i ^ M := mul_le_mul_of_nonneg_right hcM
        (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)

end ContinuousFlexibility.Analysis
