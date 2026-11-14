module

public import ContinuousFlexibility.Analysis.N04NegativeChartInteriorBudget
public import ContinuousFlexibility.Analysis.N04NegativeChartPolarization

/-! Arbitrary parameter directions preserve the actual fractional interior budget. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped BigOperators
namespace N04RealizationStart

set_option backward.isDefEq.respectTransparency true
attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul n07aNonlinearSectorParameterSub
  interiorRaw_parameterTopology interiorRaw_parameterAddGroup interiorRaw_parameterSMul
set_option diagnostics true in
/-- A uniform finite prefix of genuine mixed parameter towers, with
arbitrary directions and the unchanged fractional high-order exponent. -/
theorem negativeInterior_firstIntegral_prefix
    (W : N04RealizationStart) (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ)
    (hρ : ∀ m side, 0 < ρ m side ∧ ρ m side ≤ W.negativeMaterialCollar m)
    (hρb : ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m side,
      (ρ m side)⁻¹ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ A) :
    ∃ base : ℕ, ∃ ε : ℝ, W.base ≤ base ∧ 0 < ε ∧ ε ≤ min W.ε (1 / 2 : ℝ) ∧
      ∀ K : ℕ, ∃ D : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ k a b : ℕ, k ≤ K → a + b ≤ s → ∀ m side q,
      q ∈ W.negativeInteriorPhysicalDomain ρ (m, side) →
      ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun z => mixedDerivative a b (W.negativeFirstIntegralDefect z m) q),
      ∀ z ∈ sectorNeighborhood W.S base ε ε, ∀ v : Fin k → Parameter W.S,
      (∀ i, parameterGrading W.S base (v i) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      parameterGrading W.S (s + K * D + base + 1) z ≤ R →
      (∀ i, parameterGrading W.S (s + K * D + base + 1) (v i) ≤ R) →
      |J.D k z v| ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
        W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ) *
          R ^ (((k * D + a + b : ℕ) : ℝ) / ((s + K * D : ℕ) + 1 : ℝ)) := by
  classical
  have hex := W.negativeInterior_firstIntegral_fractional e ρ hρ hρb
  let base : ℕ := hex.choose
  let ε : ℝ := hex.choose_spec.choose
  have hbase := hex.choose_spec.choose_spec.1
  have hε := hex.choose_spec.choose_spec.2.1
  have hεW := hex.choose_spec.choose_spec.2.2.1
  have hf := hex.choose_spec.choose_spec.2.2.2
  refine ⟨base, ε, hbase, hε, hεW, fun K => ?_⟩
  have hDExists := hf K
  let D : ℕ := hDExists.choose
  have hD := hDExists.choose_spec
  refine ⟨D, fun s => ?_⟩
  let I : Type := {i : Fin (K + 1) × Fin (s + 1) × Fin (s + 1) // i.2.1.val + i.2.2.val ≤ s}
  choose Cp hCp hpolar using fun n : Fin (K + 1) => n04NegativeChart_twoBall_polarization n.val
  choose C P hC hP hb using fun i : I =>
    hD s i.val.1.val i.val.2.1.val i.val.2.2.val (Nat.le_of_lt_succ i.val.1.isLt) i.property
  choose B hB hpack using fun i : I => coefficientEnvelope_pack (3 * Cp i.val.1 * C i) (P i)
  let B₀ : ℝ := 1 + ∑ i : I, B i
  have hB₀ : 0 < B₀ := by
    have hsum : 0 ≤ ∑ i : I, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
    dsimp only [B₀]
    linarith only [hsum]
  have hBB (i : I) : B i ≤ B₀ :=
    (Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hcoef (i : I) (E : ℝ) (hE : 1 ≤ E) :
      (3 * Cp i.val.1 * C i) * E ^ P i ≤ B₀ * E ^ B₀ :=
    (hpack i E hE).trans (mul_le_mul (hBB i)
      (Real.rpow_le_rpow_of_exponent_le hE (hBB i))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) hB₀.le)
  refine ⟨B₀, hB₀, fun k a b hk hab m side q hq J z hz v hv R hR hzR hvR => ?_⟩
  let i : I := ⟨(⟨k, by omega⟩, ⟨a, by omega⟩, ⟨b, by omega⟩), hab⟩
  let E : ℝ := W.T.E0 (W.negativeHalfSample e m side)
  let H : ℝ := W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)
  let β : ℝ := ((k * D + a + b : ℕ) : ℝ) / ((s + K * D : ℕ) + 1 : ℝ)
  let high : ℕ := s + K * D + base + 1
  have hE : 1 ≤ E := W.floor _
  have hH : 0 ≤ H := Real.rpow_nonneg (W.hT.2.1 _
    (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hβ1 : β ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (s + K * D : ℕ) + 1)).mpr
    have hn : k * D + a + b ≤ s + K * D + 1 := by
      have hh := Nat.mul_le_mul_right D hk
      omega
    exact_mod_cast hn
  have hzlow := n04NegativeGeometry_parameterGrading_le_one W.S base
    (hεW.trans (min_le_right _ _)) hz
  have hzold := sectorNeighborhood_mono W.S hbase (hεW.trans (min_le_left _ _))
    (hεW.trans (min_le_left _ _)) hz
  have hqold := W.negativeInteriorPhysicalDomain_subset ρ (fun m side => (hρ m side).1) (m, side) hq
  have hΩ : IsOpen (Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioo.prod isOpen_univ
  have hc : Convex ℝ (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
      (Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ))) :=
    (sectorNeighborhood_convex W.S W.base W.ε W.ε).prod
      ((convex_Ioo _ _).prod (convex_univ : Convex ℝ (univ : Set ℝ)))
  let A := (W.negativeFirstIntegralDefectJointTower m).mixedParameterMultilinearMap
    hΩ k a b z hzold q hqold
  have hsym (u : Fin k → Parameter W.S) (σ : Equiv.Perm (Fin k)) : A (u ∘ σ) = A u :=
    (W.negativeFirstIntegralDefectJointTower m).mixedParameterMultilinearMap_comp_perm
      hΩ hc k a b z hzold q hqold u σ
  have hdiag (w : Parameter W.S) (hw : parameterGrading W.S base w ≤ 1)
      (hwR : parameterGrading W.S high w ≤ R) :
      |A (fun _ => w)| ≤ 3 * C i * E ^ P i * H * R ^ β := by
    let x : NegativeInteriorEvaluation W.S := ⟨m, side, z, w, q⟩
    have hh := hb i x (show x ∈ W.negativeInteriorBudgetDomain ρ base ε from ⟨hz, hzlow, hw, hq⟩)
    have hh₀ : |A (fun _ => w)| ≤ C i * E ^ P i * H *
        (1 + parameterGrading W.S high z + parameterGrading W.S high w) ^ β := by
      simpa only [A, SmoothDirections.mixedParameterMultilinearMap_apply,
        negativeInteriorJet, jointMixedDiagonal, x, i, pow_one] using hh
    have hscale : (1 + parameterGrading W.S high z + parameterGrading W.S high w) ^ β ≤
        3 * R ^ β := by
      calc
        _ ≤ (3 * R) ^ β := Real.rpow_le_rpow (by positivity) (by linarith only [hR, hzR, hwR]) hβ
        _ = (3 : ℝ) ^ β * R ^ β := Real.mul_rpow (by norm_num) (zero_le_one.trans hR)
        _ ≤ 3 * R ^ β := mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 3) hβ1)
          (Real.rpow_nonneg (zero_le_one.trans hR) _)
    have hpos : 0 ≤ C i * E ^ P i * H :=
      mul_nonneg (mul_nonneg (hC i) (Real.rpow_nonneg (zero_le_one.trans hE) _)) hH
    have hh' := hh₀.trans (mul_le_mul_of_nonneg_left hscale hpos)
    exact hh'.trans_eq (by rw [mul_left_comm, ← mul_assoc, ← mul_assoc, ← mul_assoc])
  have hbound := hpolar i.val.1 (Parameter W.S) (parameterGrading W.S base)
    (parameterGrading W.S high) A hsym (3 * C i * E ^ P i * H * R ^ β) R
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hC i))
      (Real.rpow_nonneg (zero_le_one.trans hE) _)) hH) (Real.rpow_nonneg (zero_le_one.trans hR) _))
    (zero_lt_one.trans_le hR) hdiag v hv hvR
  have hpoint := n04NegativeChart_joint_restricted_parameter
    (W.negativeFirstIntegralDefectJointTower m) (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
    hΩ hc (sectorNeighborhood_isOpen W.S base ε ε)
    (sectorNeighborhood_mono W.S hbase (hεW.trans (min_le_left _ _)) (hεW.trans (min_le_left _ _)))
    k a b hz hqold J v
  have hbound' : |J.D k z v| ≤ (3 * Cp i.val.1 * C i) * E ^ P i * H * R ^ β := by
    rw [hpoint]
    change |A v| ≤ _
    exact hbound.trans_eq (by simp only [mul_assoc, mul_left_comm (Cp i.val.1) 3])
  exact hbound'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hcoef i E hE) hH) (Real.rpow_nonneg (zero_le_one.trans hR) _))

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeInterior_firstIntegral_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeInterior_firstIntegral_prefix
