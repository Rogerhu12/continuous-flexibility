module

public import ContinuousFlexibility.Analysis.SolveApplication
public import ContinuousFlexibility.Analysis.SolveNormalization
public import ContinuousFlexibility.Analysis.SolveTameSubspace

/-!
# Solving on a continuously normalized hyperplane

The kernel restriction, smoothing, tame transport, and Newton application are
proved on abstract spaces. A concrete system supplies its actual continuous
row and the fact that its correction is tangent to that row. The conclusion
returns a point in the ambient space together with its exact zero row.
-/

@[expose] public section

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

/-- The fixed-parameter solve preserves an actual continuous normalization
row when the supplied right inverse is tangent to its kernel. The residual
may be tame on the larger parameter cylinder already supplied by N08. -/
theorem solve_exists_nonzero_zero_in_ker
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y)
    (hp : Monotone p) (hwp : WithSeminorms p)
    (Φ : Y ≃L[ℝ] ProjectiveLimit F f)
    (hΦle : ∀ n y, gradedSeminorm F f n (Φ y) ≤ q n y)
    (hleΦ : ∀ n y, q n y ≤ 2 * gradedSeminorm F f n (Φ y))
    (base : ℕ) (ε q0 : ℝ) (hε : 0 < ε) (hq0 : 0 < q0) (hqε : q0 ≤ ε)
    (row : X →L[ℝ] ℝ) (ψ : X) (hψ : row ψ = 1)
    (R : X × ℝ → Y) (V : X × ℝ → Y →ₗ[ℝ] X)
    (Q : X × ℝ → Y →ₗ[ℝ] Y →ₗ[ℝ] Y)
    (hzero : R (0, 0) = 0) :
    let U : Set (X × ℝ) := {z | p base z.1 < ε ∧ |z.2| < q0}
    let Uε : Set (X × ℝ) := {z | p base z.1 < ε ∧ |z.2| < ε}
    let a := pairGrading p realGrading
    HasSmoothing p → HasSmoothing q →
    SmoothTameOn a q Uε R →
    SmoothTameOn (pairGrading a q) p (U ×ˢ univ)
      (fun z : (X × ℝ) × Y => V z.1 z.2) →
    SmoothTameOn (pairGrading (pairGrading a q) q) q ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((X × ℝ) × Y) × Y => Q z.1.1 z.1.2 z.2) →
    (∀ z ∈ U, ∀ y, row (V z y) = 0) →
    (∀ z ∈ U, ∀ y, HasProjectiveLineDerivAt (fun x => R (x, z.2))
      (y + Q z (R z) y) z.1 (V z y)) →
    ∃ x : X, ∃ τ : ℝ, τ ≠ 0 ∧ (x, τ) ∈ U ∧ row x = 0 ∧ R (x, τ) = 0 := by
  classical
  dsimp only
  intro hSX hSY hR hV hQ hrow hRight
  let U : Set (X × ℝ) := {z | p base z.1 < ε ∧ |z.2| < q0}
  let Uε : Set (X × ℝ) := {z | p base z.1 < ε ∧ |z.2| < ε}
  let a := pairGrading p realGrading
  let W : Submodule ℝ X := row.toLinearMap.ker
  let _ : IsUniformAddGroup W := W.toAddSubgroup.isUniformAddGroup
  let _ : CompleteSpace W := row.isClosed_ker.completeSpace_coe
  let pK : ℕ → Seminorm ℝ W := fun n => (p n).comp W.subtype
  have hpK : Monotone pK := by
    intro m n h x
    simpa only [pK, Seminorm.comp_apply, Submodule.subtype_apply] using hp h x.val
  have hwpK : WithSeminorms pK :=
    (Topology.IsInducing.subtypeVal).withSeminorms (f := W.subtype) hwp
  have hSXK : HasSmoothing pK :=
    hasSmoothing_ker_of_continuous p hwp hp hSX row ψ hψ
  let ρ : ℝ := min ε q0
  have hρ : 0 < ρ := lt_min hε hq0
  let UK : Set (W × ℝ) := {z | pK base z.1 < ρ ∧ |z.2| < ρ}
  let aK := pairGrading pK realGrading
  let Lz : (W × ℝ) →L[ℝ] (X × ℝ) :=
    W.subtypeL.prodMap (ContinuousLinearMap.id ℝ ℝ)
  have hLz_apply (z : W × ℝ) : Lz z = (z.1.val, z.2) := by
    simp only [Lz, ContinuousLinearMap.coe_prodMap', Prod.map_apply',
      ContinuousLinearMap.id_apply, Submodule.subtypeL_apply]
  have hUKopen : IsOpen UK :=
    (isOpen_lt ((hwpK.continuous_seminorm base).comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  have hnear (z : W × ℝ) (hz : z ∈ UK) : Lz z ∈ U := by
    refine ⟨?_, ?_⟩
    · simpa only [hLz_apply, pK, Seminorm.comp_apply, Submodule.subtype_apply] using
        hz.1.trans_le (min_le_left ε q0)
    · simpa only [hLz_apply] using hz.2.trans_le (min_le_right ε q0)
  have hnearε (z : W × ℝ) (hz : z ∈ UK) : Lz z ∈ Uε :=
    ⟨(hnear z hz).1, (hnear z hz).2.trans_le hqε⟩
  have hVmem (z : W × ℝ) (hz : z ∈ UK) (y : Y) : V (Lz z) y ∈ W :=
    LinearMap.mem_ker.mpr (hrow (Lz z) (hnear z hz) y)
  let RN : W × ℝ → Y := fun z => R (Lz z)
  let VN : W × ℝ → Y →ₗ[ℝ] W := fun z =>
    if hz : z ∈ UK then (V (Lz z)).codRestrict W (hVmem z hz) else 0
  let QN : W × ℝ → Y →ₗ[ℝ] Y →ₗ[ℝ] Y := fun z => Q (Lz z)
  have hVN (z : W × ℝ) (hz : z ∈ UK) (y : Y) :
      (VN z y).val = V (Lz z) y := by
    simp only [VN, dite_eq_left hz, LinearMap.codRestrict_apply]
  have hLz : ∀ n z, a n (Lz z) ≤ 1 * aK n z := by
    intro n z
    simpa only [a, aK, pK, pairGrading, add_apply, Seminorm.comp_apply,
      hLz_apply, LinearMap.fst_apply, LinearMap.snd_apply, Submodule.subtype_apply,
      one_mul] using (le_refl (p n z.1.val + realGrading n z.2))
  have hRN : SmoothTameOn aK q UK RN := by
    have hpre := solve_smoothTameOn_precomp hR Lz le_rfl hLz
    exact smoothTameOn_mono hpre hUKopen (fun z hz => hnearε z hz)
  let Lv : ((W × ℝ) × Y) →L[ℝ] ((X × ℝ) × Y) :=
    Lz.prodMap (ContinuousLinearMap.id ℝ Y)
  have hLv : ∀ n z, pairGrading a q n (Lv z) ≤ 1 * pairGrading aK q n z := by
    intro n z
    simpa only [Lv, a, aK, pK, pairGrading, add_apply, Seminorm.comp_apply,
      ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply,
      hLz_apply, LinearMap.fst_apply, LinearMap.snd_apply, Submodule.subtype_apply,
      one_mul] using (le_refl (p n z.1.1.val + realGrading n z.1.2 + q n z.2))
  have hVpre : SmoothTameOn (pairGrading aK q) p (UK ×ˢ univ)
      (fun z : (W × ℝ) × Y => V (Lz z.1) z.2) := by
    have hpre := solve_smoothTameOn_precomp hV Lv le_rfl hLv
    exact smoothTameOn_mono hpre (hUKopen.prod isOpen_univ)
      (fun z hz => ⟨hnear z.1 hz.1, mem_univ _⟩)
  have hVN_tame : SmoothTameOn (pairGrading aK q) pK (UK ×ˢ univ)
      (fun z : (W × ℝ) × Y => VN z.1 z.2) :=
    solve_smoothTameOn_codRestrict W row.isClosed_ker hVpre
      (fun z => VN z.1 z.2) (fun z hz => hVN z.1 hz.1 z.2)
  let Lq : (((W × ℝ) × Y) × Y) →L[ℝ] (((X × ℝ) × Y) × Y) :=
    Lv.prodMap (ContinuousLinearMap.id ℝ Y)
  have hLq : ∀ n z, pairGrading (pairGrading a q) q n (Lq z) ≤
      1 * pairGrading (pairGrading aK q) q n z := by
    intro n z
    simpa only [Lq, Lv, a, aK, pK, pairGrading, add_apply, Seminorm.comp_apply,
      ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply,
      hLz_apply, LinearMap.fst_apply, LinearMap.snd_apply, Submodule.subtype_apply,
      one_mul] using
      (le_refl (p n z.1.1.1.val + realGrading n z.1.1.2 + q n z.1.2 + q n z.2))
  have hQN : SmoothTameOn (pairGrading (pairGrading aK q) q) q
      ((UK ×ˢ univ) ×ˢ univ)
      (fun z : ((W × ℝ) × Y) × Y => QN z.1.1 z.1.2 z.2) := by
    have hpre := solve_smoothTameOn_precomp hQ Lq le_rfl hLq
    exact smoothTameOn_mono hpre ((hUKopen.prod isOpen_univ).prod isOpen_univ)
      (fun z hz => ⟨⟨hnear z.1.1 hz.1.1, mem_univ _⟩, mem_univ _⟩)
  have hzeroN : RN (0, 0) = 0 := by
    simpa only [RN, hLz_apply, ZeroMemClass.coe_zero] using hzero
  have hRightN : ∀ z ∈ UK, ∀ y, HasProjectiveLineDerivAt (fun x => RN (x, z.2))
      (y + QN z (RN z) y) z.1 (VN z y) := by
    intro z hz y
    have h := hRight (Lz z) (hnear z hz) y
    rw [← hVN z hz y] at h
    have hcomp := HasProjectiveLineDerivAt.comp_linear W.subtype
      (x := z.1) (v := VN z y) h
    simpa only [RN, QN, hLz_apply, Submodule.subtype_apply] using hcomp
  obtain ⟨x, τ, hτ, hmem, hz⟩ := solve_exists_nonzero_zero pK q hpK hwpK
    Φ hΦle hleΦ base ρ hρ RN VN QN hzeroN
    hSXK hSY hRN hVN_tame hQN hRightN
  refine ⟨x.val, τ, hτ, ?_, ?_, ?_⟩
  · simpa only [hLz_apply] using hnear (x, τ) hmem
  · exact LinearMap.mem_ker.mp x.property
  · simpa only [RN, hLz_apply] using hz

end ContinuousFlexibility.Analysis
