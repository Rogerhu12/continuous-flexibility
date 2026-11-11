import ContinuousFlexibility.Analysis.SolveNewtonBridge
import ContinuousFlexibility.Analysis.SolveNewtonLimit

/-!
# A nonzero-parameter solution in the actual residual space

Only the residual is transported to its projective representation. The
source keeps its complete closed-subspace topology and its inherited grading.
The sum and maximum residual gradings are compared with uniform constants.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [UniformSpace X] [AddCommGroup X] [Module ℝ X]
  [IsUniformAddGroup X] [ContinuousSMul ℝ X] [T2Space X] [CompleteSpace X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  {f : ∀ n, F (n + 1) →L[ℝ] F n}

/-- The abstract fixed-parameter theorem gives a genuine nonzero parameter
for a complete source and a uniformly equivalent projective residual model. -/
theorem solve_exists_nonzero_zero
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y)
    (hp : Monotone p) (hwp : WithSeminorms p)
    (Φ : Y ≃L[ℝ] ProjectiveLimit F f)
    (hΦle : ∀ n y, gradedSeminorm F f n (Φ y) ≤ q n y)
    (hleΦ : ∀ n y, q n y ≤ 2 * gradedSeminorm F f n (Φ y))
    (base : ℕ) (ε : ℝ) (hε : 0 < ε)
    (R : X × ℝ → Y) (V : X × ℝ → Y →ₗ[ℝ] X)
    (Q : X × ℝ → Y →ₗ[ℝ] Y →ₗ[ℝ] Y)
    (hzero : R (0, 0) = 0) :
    let U : Set (X × ℝ) := {z | p base z.1 < ε ∧ |z.2| < ε}
    let a := pairGrading p realGrading
    HasSmoothing p → HasSmoothing q →
    SmoothTameOn a q U R →
    SmoothTameOn (pairGrading a q) p (U ×ˢ univ)
      (fun z : (X × ℝ) × Y => V z.1 z.2) →
    SmoothTameOn (pairGrading (pairGrading a q) q) q ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((X × ℝ) × Y) × Y => Q z.1.1 z.1.2 z.2) →
    (∀ z ∈ U, ∀ y, HasProjectiveLineDerivAt (fun x => R (x, z.2))
      (y + Q z (R z) y) z.1 (V z y)) →
    ∃ x : X, ∃ τ : ℝ, τ ≠ 0 ∧ (x, τ) ∈ U ∧ R (x, τ) = 0 := by
  dsimp only
  let U : Set (X × ℝ) := {z | p base z.1 < ε ∧ |z.2| < ε}
  let a := pairGrading p realGrading
  let qP := gradedSeminorm F f
  intro hSX hSY hR hV hQ hRight
  let RP : X × ℝ → ProjectiveLimit F f := fun z => Φ (R z)
  let VP : X × ℝ → ProjectiveLimit F f →ₗ[ℝ] X :=
    fun z => (V z).comp Φ.symm.toLinearMap
  let QP : X × ℝ → ProjectiveLimit F f →ₗ[ℝ]
      ProjectiveLimit F f →ₗ[ℝ] ProjectiveLimit F f := fun z =>
    { toFun := fun r => (Φ.toLinearMap.comp (Q z (Φ.symm r))).comp Φ.symm.toLinearMap
      map_add' := by intro r s; ext y; simp [map_add]
      map_smul' := by intro c r; ext y; simp [map_smul] }
  have hSYPull : HasSmoothing (fun n => (qP n).comp Φ.toLinearMap) :=
    solve_hasSmoothing_of_comparable (by norm_num : (0 : ℝ) ≤ 2) zero_le_one
      hleΦ (fun n y => by simpa only [one_mul, Seminorm.comp_apply] using hΦle n y) hSY
  have hSYP : HasSmoothing qP :=
    hasSmoothing_transport Φ (fun _ _ => rfl) hSYPull
  have hRP : SmoothTameOn a qP U RP := by
    simpa only [RP] using solve_smoothTameOn_postcomp hR Φ.toContinuousLinearMap
      zero_le_one (fun n y => by simpa only [one_mul] using hΦle n y)
  let Lv : ((X × ℝ) × ProjectiveLimit F f) →L[ℝ] ((X × ℝ) × Y) :=
    (ContinuousLinearMap.id ℝ (X × ℝ)).prodMap Φ.symm.toContinuousLinearMap
  have hLv : ∀ n z, pairGrading a q n (Lv z) ≤ 2 * pairGrading a qP n z := by
    intro n z
    change a n z.1 + q n (Φ.symm z.2) ≤ 2 * (a n z.1 + qP n z.2)
    have h := hleΦ n (Φ.symm z.2)
    rw [Φ.apply_symm_apply] at h
    linarith only [h, apply_nonneg (a n) z.1]
  have hVP : SmoothTameOn (pairGrading a qP) p (U ×ˢ univ)
      (fun z : (X × ℝ) × ProjectiveLimit F f => VP z.1 z.2) := by
    have h := solve_smoothTameOn_precomp hV Lv (by norm_num : (1 : ℝ) ≤ 2) hLv
    have hdom : Lv ⁻¹' (U ×ˢ univ) = U ×ˢ univ := by ext z; simp [Lv]
    rw [hdom] at h
    exact h
  let Lq : (((X × ℝ) × ProjectiveLimit F f) × ProjectiveLimit F f) →L[ℝ]
      (((X × ℝ) × Y) × Y) := Lv.prodMap Φ.symm.toContinuousLinearMap
  have hLq : ∀ n z,
      pairGrading (pairGrading a q) q n (Lq z) ≤
        2 * pairGrading (pairGrading a qP) qP n z := by
    intro n z
    change pairGrading a q n (Lv z.1) + q n (Φ.symm z.2) ≤
      2 * (pairGrading a qP n z.1 + qP n z.2)
    have h := hleΦ n (Φ.symm z.2)
    rw [Φ.apply_symm_apply] at h
    linarith only [h, hLv n z.1]
  have hQP : SmoothTameOn (pairGrading (pairGrading a qP) qP) qP
      ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((X × ℝ) × ProjectiveLimit F f) × ProjectiveLimit F f =>
        QP z.1.1 z.1.2 z.2) := by
    have h := solve_smoothTameOn_precomp hQ Lq (by norm_num : (1 : ℝ) ≤ 2) hLq
    have hdom : Lq ⁻¹' ((U ×ˢ univ) ×ˢ univ) = (U ×ˢ univ) ×ˢ univ := by
      ext z
      simp [Lq, Lv]
    rw [hdom] at h
    exact solve_smoothTameOn_postcomp h Φ.toContinuousLinearMap zero_le_one
      (fun n y => by simpa only [one_mul] using hΦle n y)
  have hzeroP : RP (0, 0) = 0 := by simp only [RP, hzero, map_zero]
  have hRightP : ∀ z ∈ U, ∀ y, HasProjectiveLineDerivAt (fun x => RP (x, z.2))
      (y + QP z (RP z) y) z.1 (VP z y) := by
    intro z hz y
    have h := (hRight z hz (Φ.symm y)).clm_comp Φ.toContinuousLinearMap
    simpa only [RP, VP, QP, LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, map_add, Φ.apply_symm_apply,
      Φ.symm_apply_apply] using h
  obtain ⟨SX, N, ρ, hρ, x, _, hx⟩ :=
    solve_exists_fixed_branch p hp hwp (0 : X) base ε hε
      (U := U) (by ext z; simp only [U, sub_zero]) RP VP QP hzeroP hRightP
      hSX hSYP hRP hVP hQP
  have hτ : |ρ / 2| < ρ := by rw [abs_of_pos (half_pos hρ)]; linarith only [hρ]
  obtain ⟨_, hmem, hz⟩ := hx (ρ / 2) hτ
  refine ⟨x (ρ / 2), ρ / 2, (half_pos hρ).ne', hmem, ?_⟩
  exact Φ.injective (hz.trans (map_zero Φ).symm)

end ContinuousFlexibility.Analysis
