module

public import ContinuousFlexibility.Geometry.MarkerStabilizer
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A genuine principal frame from an immersed plane and its normal

The plane eigenbasis is sent to E3 by the actual injective surface differential.
Together with its unit normal these vectors form a basis. A commuting plane
operator forces its simple eigenlines to be preserved; the chain rule then
forces preservation of the actual E3 principal lines. Surface applications must
derive that commutation from their actual shape transformation law.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Function

set_option backward.isDefEq.respectTransparency false

abbrev MarkerPlane := Fin 2 → ℝ

theorem eigenvectors_linearIndependent_two
    (S : MarkerPlane →ₗ[ℝ] MarkerPlane) (v : Fin 2 → MarkerPlane) (μ : Fin 2 → ℝ)
    (hv : ∀ i, v i ≠ 0) (hμ : μ 0 ≠ μ 1)
    (heigen : ∀ i, S (v i) = μ i • v i) : LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have ha : c 0 • v 0 + c 1 • v 1 = 0 := by simpa only [Fin.sum_univ_two] using hc
  have hs : c 0 • (μ 0 • v 0) + c 1 • (μ 1 • v 1) = 0 := by
    simpa only [map_add, map_smul, heigen, map_zero] using congrArg S ha
  have hz : c 0 • (μ 0 • v 0) + c 1 • (μ 0 • v 1) = 0 := by
    calc
      _ = μ 0 • (c 0 • v 0 + c 1 • v 1) := by
        simp only [smul_add, smul_smul, mul_comm]
      _ = 0 := by rw [ha, smul_zero]
  have hd : c 1 • ((μ 1 - μ 0) • v 1) = 0 := by
    calc
      _ = (c 0 • (μ 0 • v 0) + c 1 • (μ 1 • v 1)) -
          (c 0 • (μ 0 • v 0) + c 1 • (μ 0 • v 1)) := by
        rw [add_sub_add_left_eq_sub, ← smul_sub, ← sub_smul]
      _ = 0 := by rw [hs, hz, sub_self]
  have hc1 : c 1 = 0 := (smul_eq_zero.mp hd).resolve_right
    (smul_ne_zero (sub_ne_zero.mpr hμ.symm) (hv 1))
  have hc0 : c 0 = 0 := by
    rw [hc1, zero_smul, add_zero] at ha
    exact (smul_eq_zero.mp ha).resolve_right (hv 0)
  intro i
  fin_cases i
  · exact hc0
  · exact hc1

def markerPlaneEigenbasis
    (S : MarkerPlane →ₗ[ℝ] MarkerPlane) (v : Fin 2 → MarkerPlane) (μ : Fin 2 → ℝ)
    (hv : ∀ i, v i ≠ 0) (hμ : μ 0 ≠ μ 1)
    (heigen : ∀ i, S (v i) = μ i • v i) : Module.Basis (Fin 2) ℝ MarkerPlane :=
  basisOfLinearIndependentOfCardEqFinrank
    (eigenvectors_linearIndependent_two S v μ hv hμ heigen) (by simp [MarkerPlane])

@[simp] theorem markerPlaneEigenbasis_apply
    (S : MarkerPlane →ₗ[ℝ] MarkerPlane) (v : Fin 2 → MarkerPlane) (μ : Fin 2 → ℝ)
    (hv hμ heigen) (i : Fin 2) : markerPlaneEigenbasis S v μ hv hμ heigen i = v i := by
  rw [markerPlaneEigenbasis, coe_basisOfLinearIndependentOfCardEqFinrank]

def principalFrameVectors (L : MarkerPlane →L[ℝ] E3)
    (b : Module.Basis (Fin 2) ℝ MarkerPlane) (N : E3) : Fin 3 → E3 :=
  ![L (b 0), L (b 1), N]

theorem principalFrameVectors_linearIndependent
    (L : MarkerPlane →L[ℝ] E3) (b : Module.Basis (Fin 2) ℝ MarkerPlane) (N : E3)
    (hi : Injective L) (hN : ‖N‖ = 1) (ho : ∀ v, inner ℝ (L v) N = 0) :
    LinearIndependent ℝ (principalFrameVectors L b N) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have ha : c 0 • L (b 0) + c 1 • L (b 1) + c 2 • N = 0 := by
    simpa [Fin.sum_univ_succ, principalFrameVectors, add_assoc] using hc
  have hc2 : c 2 = 0 := by
    have h := congrArg (fun z : E3 => inner ℝ z N) ha
    simpa only [inner_add_left, real_inner_smul_left, ho, real_inner_self_eq_norm_sq,
      hN, one_pow, mul_zero, zero_add, mul_one, inner_zero_left] using h
  have hL : L (c 0 • b 0 + c 1 • b 1) = 0 := by
    simpa only [map_add, map_smul, hc2, zero_smul, add_zero] using ha
  have hp : c 0 • b 0 + c 1 • b 1 = 0 := hi (by simpa only [map_zero] using hL)
  have hc0 : c 0 = 0 := by
    have h := congrArg (fun z => b.repr z 0) hp
    simpa using h
  have hc1 : c 1 = 0 := by
    have h := congrArg (fun z => b.repr z 1) hp
    simpa using h
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2

def principalFrame (L : MarkerPlane →L[ℝ] E3) (b : Module.Basis (Fin 2) ℝ MarkerPlane)
    (N : E3) (hi : Injective L) (hN : ‖N‖ = 1) (ho : ∀ v, inner ℝ (L v) N = 0) :
    Module.Basis (Fin 3) ℝ E3 :=
  basisOfLinearIndependentOfCardEqFinrank
    (principalFrameVectors_linearIndependent L b N hi hN ho) (by simp [E3])

@[simp] theorem principalFrame_apply
    (L : MarkerPlane →L[ℝ] E3) (b : Module.Basis (Fin 2) ℝ MarkerPlane)
    (N : E3) (hi hN ho) (i : Fin 3) :
    principalFrame L b N hi hN ho i = principalFrameVectors L b N i := by
  rw [principalFrame, coe_basisOfLinearIndependentOfCardEqFinrank]

theorem markerPlane_operator_coordinate
    (b : Module.Basis (Fin 2) ℝ MarkerPlane) (S : MarkerPlane →ₗ[ℝ] MarkerPlane)
    (μ : Fin 2 → ℝ) (hdiag : ∀ i, S (b i) = μ i • b i) (v : MarkerPlane) (j : Fin 2) :
    b.repr (S v) j = μ j * b.repr v j := by
  have heq : S v = ∑ i, b.repr v i • (μ i • b i) := by
    calc
      S v = S (∑ i, b.repr v i • b i) := congrArg S (b.sum_repr v).symm
      _ = _ := by rw [map_sum]; simp only [map_smul, hdiag]
  rw [heq, map_sum]
  fin_cases j <;> simp [map_smul, smul_smul, mul_comm]

theorem markerPlane_mem_line_of_eigenvector
    (b : Module.Basis (Fin 2) ℝ MarkerPlane) (S : MarkerPlane →ₗ[ℝ] MarkerPlane)
    (μ : Fin 2 → ℝ) (hμ : Injective μ) (hdiag : ∀ i, S (b i) = μ i • b i)
    (i : Fin 2) {v : MarkerPlane} (hv : S v = μ i • v) :
    v ∈ Submodule.span ℝ {b i} := by
  have hz (j : Fin 2) (hji : j ≠ i) : b.repr v j = 0 := by
    have he := congrArg (fun w => b.repr w j) hv
    rw [markerPlane_operator_coordinate b S μ hdiag, map_smul] at he
    change μ j * b.repr v j = μ i * b.repr v j at he
    have hp : (μ j - μ i) * b.repr v j = 0 := by rw [sub_mul, he, sub_self]
    exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (fun h => hji (hμ h)))
  apply Submodule.mem_span_singleton.mpr
  refine ⟨b.repr v i, ?_⟩
  apply b.repr.injective
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hz j hji, Ne.symm hji]

/-- The actual chain rule and a derived shape commutation force preservation
of the E3 tangent lines; neither line-preservation conclusion is an input. -/
theorem principal_line_preserved_of_shape_commute
    (L : MarkerPlane →L[ℝ] E3) (b : Module.Basis (Fin 2) ℝ MarkerPlane)
    (S J : MarkerPlane →ₗ[ℝ] MarkerPlane) (μ : Fin 2 → ℝ)
    (hμ : Injective μ) (hdiag : ∀ i, S (b i) = μ i • b i)
    (A : E3 ≃ₗᵢ[ℝ] E3)
    (hchain : ∀ v, A (L v) = L (J v)) (hcomm : ∀ v, S (J v) = J (S v))
    (i : Fin 2) : A (L (b i)) ∈ Submodule.span ℝ {L (b i)} := by
  have heigen : S (J (b i)) = μ i • J (b i) := by rw [hcomm, hdiag, map_smul]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    (markerPlane_mem_line_of_eigenvector b S μ hμ hdiag i heigen)
  apply Submodule.mem_span_singleton.mpr
  refine ⟨a, ?_⟩
  calc
    a • L (b i) = L (a • b i) := (map_smul L a (b i)).symm
    _ = L (J (b i)) := congrArg L ha
    _ = A (L (b i)) := (hchain (b i)).symm

theorem mem_markerStabilizers_of_shape_commute
    (L : MarkerPlane →L[ℝ] E3) (b : Module.Basis (Fin 2) ℝ MarkerPlane)
    (N : E3) (hi : Injective L) (hN : ‖N‖ = 1) (ho : ∀ v, inner ℝ (L v) N = 0)
    (S J : MarkerPlane →ₗ[ℝ] MarkerPlane) (μ : Fin 2 → ℝ)
    (hμ : Injective μ) (hdiag : ∀ i, S (b i) = μ i • b i)
    (p : E3) (A : E3 ≃ᵃⁱ[ℝ] E3) (hp : A p = p) (hn : A.linearIsometryEquiv N = N)
    (hchain : ∀ v, A.linearIsometryEquiv (L v) = L (J v))
    (hcomm : ∀ v, S (J v) = J (S v)) :
    A ∈ markerStabilizers p (principalFrame L b N hi hN ho) := by
  refine ⟨hp, ?_, ?_, ?_⟩
  · simp only [principalFrame_apply]
    change A.linearIsometryEquiv N = N
    exact hn
  · simpa only [principalFrame_apply, principalFrameVectors, Matrix.cons_val_zero] using
      principal_line_preserved_of_shape_commute L b S J μ hμ hdiag A.linearIsometryEquiv hchain hcomm 0
  · simpa only [principalFrame_apply, principalFrameVectors, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      principal_line_preserved_of_shape_commute L b S J μ hμ hdiag A.linearIsometryEquiv hchain hcomm 1

end ContinuousFlexibility
