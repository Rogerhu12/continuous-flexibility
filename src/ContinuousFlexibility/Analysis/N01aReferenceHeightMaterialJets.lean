module

public import ContinuousFlexibility.Analysis.N01aReferenceHeightPhysicalJets
public import ContinuousFlexibility.Analysis.N01aReferenceHeightScalarJets
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Material jets of the actual reference eigenfield

The bounded affine-coordinate jets transfer the ordinary Jacobi estimates
to material derivatives. Differentiating the actual height weight retains
its original power, leaving only a finite envelope moment to integrate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

theorem n01aPointwiseBound_comp_of_uniform_jets {U : Set ℝ} {E W f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hmap : ∀ x, g x ∈ U)
    (hE : ∀ x ∈ U, 1 ≤ E x) (hW : ∀ x ∈ U, 0 ≤ W x)
    (hfb : ∀ i : ℕ, N01aPointwiseBound U E W (iteratedDeriv i f))
    (hgb : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv i g x| ≤ C)
    (n : ℕ) :
    N01aPointwiseBound univ (fun x => E (g x)) (fun x => W (g x))
      (iteratedDeriv n (fun x => f (g x))) := by
  classical
  obtain ⟨k, A, hA, houter⟩ := n01aPointwiseBound_finite
    (fun i : Fin (n + 1) => iteratedDeriv i.val f) hE hW (fun i => hfb i.val)
  choose B hB hb using hgb
  let D : ℝ := 1 + ∑ i : Fin (n + 1), B i.val
  have hD : 1 ≤ D := by
    have hs : 0 ≤ ∑ i : Fin (n + 1), B i.val := Finset.sum_nonneg (fun i _ => hB i.val)
    dsimp only [D]
    linarith
  have hDb (i : ℕ) (hi : i ≤ n) : B i ≤ D := by
    have hb' : B i ≤ ∑ j : Fin (n + 1), B j.val :=
      Finset.single_le_sum (fun j _ => hB j.val)
        (Finset.mem_univ (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (n + 1)))
    dsimp only [D]
    linarith
  refine ⟨k, (n.factorial : ℝ) * A * D ^ n,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hA) (pow_nonneg (zero_le_one.trans hD) _),
    fun x hx => ?_⟩
  have ho (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i f (g x)‖ ≤ A * E (g x) ^ k * W (g x) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact houter ⟨i, Nat.lt_succ_of_le hi⟩ (g x) (hmap x)
  have hi (i : ℕ) (hione : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i g x‖ ≤ D ^ i := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact ((hb i x).trans (hDb i hin)).trans (le_self_pow₀ hD (by omega))
  have hcomp := norm_iteratedFDeriv_comp_le hf hg (n := n) (by simp) x ho hi
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hcomp
  calc
    _ ≤ (n.factorial : ℝ) * (A * E (g x) ^ k * W (g x)) * D ^ n := by
      simpa only [Function.comp_def] using hcomp
    _ = _ := by ring

theorem n01a_reference_phi_material_jets {D : ReferenceData} {sample : ℕ → ℝ}
    (hD : IsRadialReference D) (k : ℕ) :
    N01aPointwiseBound univ
      (fun x => (affineMaterialData D sample).M ((affineMaterialData D sample).radius x))
      (fun x => |D.phi ((affineMaterialData D sample).radius x)| +
        |deriv D.phi ((affineMaterialData D sample).radius x)|)
      (iteratedDeriv k (fun x => D.phi ((affineMaterialData D sample).radius x))) := by
  obtain ⟨C, hprofile⟩ := hD.1
  have hgeom := hprofile.1
  exact n01aPointwiseBound_comp_of_uniform_jets hgeom.2.2.2.1.1
    (contDiff_affineMaterialData_radius (sample := sample))
    (fun x => (affineMaterialData_radius_mem_rho (sample := sample) hgeom.2.1 x).1)
    (fun r hr => (affineMaterialData_positive (sample := sample) hgeom.2.1 hr).2.2.2)
    (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
    (fun i => n01a_reference_phi_physical_jets (sample := sample) hD i)
    (fun i => n01a_affine_radius_jets (sample := sample) hgeom.2.1 i) k

theorem n01a_reference_weighted_material_jets {D : ReferenceData} {sample : ℕ → ℝ}
    (hD : IsRadialReference D) (β : ℝ) (k : ℕ) :
    N01aPointwiseBound univ
      (fun x => (affineMaterialData D sample).M ((affineMaterialData D sample).radius x))
      (fun x => (affineMaterialData D sample).H ((affineMaterialData D sample).radius x) ^ (-β) *
        (|D.phi ((affineMaterialData D sample).radius x)| +
          |deriv D.phi ((affineMaterialData D sample).radius x)|))
      (iteratedDeriv k (fun x =>
        (affineMaterialData D sample).H ((affineMaterialData D sample).radius x) ^ (-β) *
          D.phi ((affineMaterialData D sample).radius x))) := by
  obtain ⟨C, hprofile⟩ := hD.1
  have hgeom := hprofile.1
  let T := affineMaterialData D sample
  have hi (x : ℝ) := (affineMaterialData_radius_mem_rho (sample := sample) hgeom.2.1 x).1
  have hp (x : ℝ) : 0 < T.H (T.radius x) :=
    (affineMaterialData_positive (sample := sample) hgeom.2.1 (hi x)).2.1
  have hH : ContDiff ℝ ∞ (fun x => T.H (T.radius x)) :=
    (affineMaterialData_smooth_scalar (sample := sample) hgeom.2.1 T.H (by simp [T])).comp_contDiff
      (contDiff_affineMaterialData_radius (sample := sample)) hi
  have hF : ContDiff ℝ ∞ (fun x => T.H (T.radius x) ^ (-β)) :=
    hH.rpow_const_of_ne (fun x => (hp x).ne')
  apply n01aPointwiseBound_iteratedDeriv_weighted_mul k
    (fun x _ => (affineMaterialData_positive (sample := sample) hgeom.2.1 (hi x)).2.2.2)
    (fun x _ => (Real.rpow_pos_of_pos (hp x) (-β)).le)
    (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
    (fun x _ => hF.contDiffAt)
    (fun x _ => (hgeom.2.2.2.1.1.comp
      (contDiff_affineMaterialData_radius (sample := sample))).contDiffAt)
  · intro i hi'
    obtain ⟨A, hA, hb⟩ := n01a_affine_H_rpow_jets (sample := sample) hgeom.2.1 (-β) i
    exact ⟨0, A, hA, fun x _ => by simpa only [pow_zero, mul_one] using hb x⟩
  · intro i hi'
    exact n01a_reference_phi_material_jets (sample := sample) hD i

end ContinuousFlexibility.Statements
