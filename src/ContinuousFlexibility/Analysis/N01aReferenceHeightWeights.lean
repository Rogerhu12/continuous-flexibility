module

public import ContinuousFlexibility.Analysis.AffineMaterialSampling
public import ContinuousFlexibility.Analysis.MaterialRadialExpansion
public import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# The material height weight versus the reference output weight

The Jacobian of the material coordinate costs one inverse density scale.
Every fixed envelope moment, including that scale, is absorbed by a
positive fraction of the additional reference attenuation. The remaining
comparison uses the actual cell logarithms from the affine material model.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter Real
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n01a_affine_inv_ell_le_M {D : ReferenceData} {sample : ℕ → ℝ}
    (hab : D.a < D.b) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ radialCore D,
      ((affineMaterialData D sample).ell r)⁻¹ ≤
        C * (affineMaterialData D sample).M r := by
  obtain ⟨A, hA, ha⟩ := affineMaterialData_inv_ell_le_E0_sq (sample := sample) hab
  obtain ⟨B, hB, hb⟩ := affineMaterialData_E0_rpow_le_M (D := D) (sample := sample) (2 : ℝ)
  refine ⟨A * B + 1, by positivity, fun r hr => ?_⟩
  have hm : 0 ≤ (affineMaterialData D sample).M r :=
    zero_le_one.trans (affineMaterialData_positive (sample := sample) hab hr).2.2.2
  have he : (affineMaterialData D sample).E0 r ^ (2 : ℕ) ≤
      B * (affineMaterialData D sample).M r := by
    simpa only [Real.rpow_two] using hb r hr
  calc
    _ ≤ A * (B * (affineMaterialData D sample).M r) :=
      (ha r hr).trans (mul_le_mul_of_nonneg_left he hA)
    _ ≤ (A * B + 1) * (affineMaterialData D sample).M r := by nlinarith

/-- The physical density for a material-coordinate weighted square is
bounded by a slightly stronger negative power of the material H weight. -/
theorem n01a_affine_height_density_bound {D : ReferenceData} {sample : ℕ → ℝ}
    (hab : D.a < D.b) (β : ℝ) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ radialCore D,
      ((affineMaterialData D sample).ell r)⁻¹ *
          ((affineMaterialData D sample).M r ^ k *
            (affineMaterialData D sample).H r ^ (-β)) ^ 2 ≤
        C * (affineMaterialData D sample).H r ^ (-(2 * β + ε)) := by
  let T := affineMaterialData D sample
  obtain ⟨A, hA, ha⟩ := n01a_affine_inv_ell_le_M (sample := sample) hab
  obtain ⟨B, hB, hb, _, _⟩ := affineMaterialData_H_rpow_mul_M_rpow
    (sample := sample) hab (((2 * k + 1 : ℕ) : ℝ)) ε hε
  refine ⟨A * B, mul_pos hA hB, fun r hr => ?_⟩
  have hH : 0 < T.H r := (affineMaterialData_positive (sample := sample) hab hr).2.1
  have hB' : T.H r ^ ε * T.M r ^ (2 * k + 1) ≤ B := by
    simpa only [Real.rpow_natCast] using hb r hr
  have hfactor :
      T.M r * (T.M r ^ k * T.H r ^ (-β)) ^ 2 =
        (T.H r ^ ε * T.M r ^ (2 * k + 1)) * T.H r ^ (-(2 * β + ε)) := by
    have hpow : (T.H r ^ (-β)) ^ 2 = T.H r ^ ε * T.H r ^ (-(2 * β + ε)) := by
      rw [← Real.rpow_mul_natCast hH.le, ← Real.rpow_add hH]
      congr 1
      ring
    have hMpow : T.M r ^ (2 * k + 1) = T.M r * (T.M r ^ k) ^ 2 := by
      rw [pow_succ, ← pow_mul, Nat.mul_comm k 2]
      ring
    rw [mul_pow, hpow, hMpow]
    ring
  calc
    _ ≤ (A * T.M r) * (T.M r ^ k * T.H r ^ (-β)) ^ 2 :=
      mul_le_mul_of_nonneg_right (ha r hr) (sq_nonneg _)
    _ = A * ((T.H r ^ ε * T.M r ^ (2 * k + 1)) *
        T.H r ^ (-(2 * β + ε))) := by rw [mul_assoc, hfactor]
    _ ≤ A * (B * T.H r ^ (-(2 * β + ε))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hB' (Real.rpow_nonneg hH.le _)) hA.le
    _ = _ := by ring

/-- A strict gap between the reference and material attenuation exponents
absorbs every material envelope moment and the actual coordinate Jacobian. -/
theorem n01a_affine_height_cell_density_bound {D : ReferenceData} {sample : ℕ → ℝ}
    (hD : IsAccumulatingProfile D) {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε)
    (M : ℝ) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m r, r ∈ D.cells m →
      ((affineMaterialData D sample).ell r)⁻¹ *
          ((affineMaterialData D sample).M r ^ k *
            (affineMaterialData D sample).H r ^ (-β)) ^ 2 ≤
        K * Real.exp (-2 * M * radialQ (D.cellIndex m) +
          2 * (β + ε) * radialS (D.cellIndex m)) := by
  let T := affineMaterialData D sample
  have hprofile := hD
  obtain ⟨C, hgeom, hpart, hC, hnonempty, hfinite, hlocal, hdist,
    hlower, hwjets, hinvjets, hwidth, habsorb, htrace⟩ := hprofile
  obtain ⟨A, hA, ha⟩ := n01a_affine_height_density_bound
    (sample := sample) hgeom.2.1 β hε k
  obtain ⟨_, J, _, hJ, hj⟩ := affineMaterialData_cell_log_bounds (sample := sample) hD
  let s : ℝ := 2 * β + ε
  have hs : 0 < s := by dsimp [s]; positivity
  let q : ℝ := |2 * M| + 1
  let b : ℝ := s * J + 1
  have hq : 0 < q := by dsimp [q]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨B, hB, hab⟩ := habsorb q b ε hq hb hε
  refine ⟨A * Real.exp (s * J) * B, by positivity, fun m r hr => ?_⟩
  let n := D.cellIndex m
  have hcore : r ∈ radialCore D := hpart.2.2.2.1 m hr
  have hH : 0 < T.H r := (affineMaterialData_positive (sample := sample) hgeom.2.1 hcore).2.1
  have hlog := (abs_le.mp (hj m r hr).2.2).1
  have hpow : T.H r ^ (-s) ≤
      Real.exp (s * radialS n + s * J * (1 + (n : ℝ) ^ 2)) := by
    rw [Real.rpow_def_of_pos hH]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hlog hs.le
    dsimp [n] at *
    nlinarith only [hm]
  have hquad : s * J * (n : ℝ) ^ 2 ≤ b * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right (by dsimp [b]; linarith) (sq_nonneg _)
  have hcoef :
      Real.exp (2 * M * radialQ n + s * J * (n : ℝ) ^ 2) ≤
        B * Real.exp (ε * radialS n) := by
    have hQ := Radial.radialQ_nonneg n
    have hM : 2 * M ≤ q := by dsimp [q]; linarith [le_abs_self (2 * M)]
    have ha' := hab n
    rw [radialE, ← Real.exp_mul, mul_comm (radialQ n) q, ← Real.exp_add] at ha'
    exact (Real.exp_le_exp.mpr (add_le_add
      (mul_le_mul_of_nonneg_right hM hQ) hquad)).trans ha'
  have hsplit :
      Real.exp (s * radialS n + s * J * (1 + (n : ℝ) ^ 2)) =
        Real.exp (s * J) *
          (Real.exp (2 * M * radialQ n + s * J * (n : ℝ) ^ 2) *
            Real.exp (-2 * M * radialQ n + s * radialS n)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexp : Real.exp (ε * radialS n) *
      Real.exp (-2 * M * radialQ n + s * radialS n) =
        Real.exp (-2 * M * radialQ n + 2 * (β + ε) * radialS n) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [s]
    ring
  calc
    _ ≤ A * T.H r ^ (-s) := ha r hcore
    _ ≤ A * Real.exp (s * radialS n + s * J * (1 + (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hpow hA.le
    _ = A * (Real.exp (s * J) *
        (Real.exp (2 * M * radialQ n + s * J * (n : ℝ) ^ 2) *
          Real.exp (-2 * M * radialQ n + s * radialS n))) := by rw [hsplit]
    _ ≤ A * (Real.exp (s * J) *
        ((B * Real.exp (ε * radialS n)) *
          Real.exp (-2 * M * radialQ n + s * radialS n))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)
          (Real.exp_pos _).le) hA.le
    _ = _ := by rw [mul_assoc B, hexp]; ring

end ContinuousFlexibility.Statements
