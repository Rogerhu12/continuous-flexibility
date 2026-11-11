import ContinuousFlexibility.Analysis.N07aScalarColumnVolumes
import ContinuousFlexibility.Analysis.N07aRelativeMainIdentity
import ContinuousFlexibility.Analysis.N07aReferenceScalarMaps
import ContinuousFlexibility.Analysis.N07aAngularBlockWeights
import ContinuousFlexibility.Analysis.N07aAngularBandNorm

/-!
# The three original finite-rank columns as weighted angular blocks

The scalar input frequencies are exactly zero, one, and zero. Three extra
output jets therefore give the same summable gap kernel for the columns
and their true frequency commutators. The construction stays in the
original volume graph and retains the original column difference.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ENNReal BigOperators

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {V : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

local instance n07aScalarWeightedLiftLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aScalarWeightedLiftLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _
local instance n07aScalarWeightedLiftUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n07aScalarWeightedLiftUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n07aScalarWeightedLiftGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n07aScalarWeightedLiftGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

theorem n07aRelativeScalarPart_eq_sum
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (U : CanonicalUnknown S K) :
    n07aRelativeScalarPart href hcur z hz m hm U =
      ∑ i : Fin 3, n07aUnknownScalar U i •
        ((n07aCurrentScalarOpenCoefficient href hcur z hz m hm i).sub
          (n07aReferenceScalarOpenCoefficient href m hm i)).toLp := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, n07aUnknownScalar,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_succ, add_zero,
    n07aRelativeScalarPart]
  abel

private theorem n07a_small_input_gap_bound {j : ℕ} (hj : j ≤ 1) (l : ℕ) (commute : Bool) :
    n07aAngularGap j l ^ 2 * |if commute then ((l : ℝ) - j) else 1| ≤
      18 * angularWeight l ^ 3 := by
  have hjR : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hw := one_le_angularWeight l
  have hl := natCast_le_angularWeight l
  have ha : |(j : ℝ) - l| ≤ j + (l : ℝ) := by
    simpa only [sub_eq_add_neg, abs_neg, abs_of_nonneg hj0, abs_of_nonneg hl0]
      using abs_add_le (j : ℝ) (-(l : ℝ))
  have hg : n07aAngularGap j l ≤ 3 * angularWeight l := by
    dsimp only [n07aAngularGap]
    linarith
  have hk : |if commute then ((l : ℝ) - j) else 1| ≤ 2 * angularWeight l := by
    cases commute
    · simp only [Bool.false_eq_true, ite_false, abs_one]
      linarith
    · simp only [ite_true, abs_sub_comm]
      linarith
  calc
    _ ≤ (3 * angularWeight l) ^ 2 * (2 * angularWeight l) :=
      mul_le_mul (pow_le_pow_left₀
        (zero_le_one.trans (n07aAngularGap_one_le j l)) hg 2) hk (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem n07a_small_input_weighted_column_block
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (hI : ∀ m, K.left m < K.right m)
    (s : ℕ) {j : ℕ} (hj : j ≤ 1) (l : ℕ) (commute : Bool)
    (Z : V.level γ t (s + 3)) :
    ‖(if commute then ((l : ℝ) - j) else 1) •
      n07aAngularLevelBand hV γ t hI s l
        (n07aAngularLevelTruncate hV γ t (Nat.le_add_right s 3) Z)‖ ≤
      18 * n07aAngularTail ((j : ℤ) - l) * ‖Z‖ := by
  have hjet := n07aAngularLevelLift_norm_lower hV γ t hI s 3 l
    (n07aAngularLevelTruncate hV γ t (Nat.le_add_right s 3) Z)
  rw [n07aAngularLevelLift_of_truncate] at hjet
  have hw := hjet.trans (n07aAngularLevelBand_norm_le hV γ t hI (s + 3) l Z)
  have hg := n07a_small_input_gap_bound hj l commute
  have hgap : 0 < n07aAngularGap j l ^ 2 :=
    pow_pos (zero_lt_one.trans_le (n07aAngularGap_one_le j l)) 2
  rw [norm_smul, Real.norm_eq_abs]
  have h : n07aAngularGap j l ^ 2 *
      (|if commute then ((l : ℝ) - j) else 1| *
        ‖n07aAngularLevelBand hV γ t hI s l
          (n07aAngularLevelTruncate hV γ t (Nat.le_add_right s 3) Z)‖) ≤ 18 * ‖Z‖ := by
    have h₁ := mul_le_mul_of_nonneg_right hg (norm_nonneg
      (n07aAngularLevelBand hV γ t hI s l
        (n07aAngularLevelTruncate hV γ t (Nat.le_add_right s 3) Z)))
    have h₂ := mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 18)
    nlinarith
  have h' : |if commute then ((l : ℝ) - j) else 1| *
      ‖n07aAngularLevelBand hV γ t hI s l
        (n07aAngularLevelTruncate hV γ t (Nat.le_add_right s 3) Z)‖ ≤
        (18 * ‖Z‖) / n07aAngularGap j l ^ 2 :=
    (le_div_iff₀ hgap).mpr (by simpa only [mul_comm] using h)
  exact h'.trans_eq (by rw [n07aAngularTail, ← n07aAngularGap_eq_int]; ring)

private theorem n07aScalarFrequency_le_one (i : Fin 3) : n07aScalarFrequency i ≤ 1 := by
  fin_cases i <;> decide

private theorem n07a_inverseUnknownScalar_norm_bound
    (F : V.level (3 / 4 : ℝ) 0 b) (i : Fin 3) :
    |n07aUnknownScalar (B.inverse F).val.1 i| ≤ ‖B.inverse‖ * ‖F‖ := by
  have he : ‖n07aReferenceScalarMap B i F‖ =
      |n07aUnknownScalar (B.inverse F).val.1 i| :=
    (congrArg (fun x : ℝ => ‖x‖) (n07aReferenceScalarMap_apply B i F)).trans
      (Real.norm_eq_abs _)
  exact he.symm.le.trans (((n07aReferenceScalarMap B i).le_opNorm F).trans
    (mul_le_mul_of_nonneg_right (n07aReferenceScalarMap_norm_le B i) (norm_nonneg F)))

private theorem n07a_scalar_column_norm_bound
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (hI : ∀ m, K.left m < K.right m)
    (s : ℕ) (i : Fin 3) (j l : ℕ) (commute : Bool)
    (Z : V.level γ t (s + 3)) (α A N : ℝ) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hZ : ‖Z‖ ≤ A) (hα : |α| ≤ N) (hzero : n07aScalarFrequency i ≠ j → α = 0) :
    ‖α • ((if commute then ((l : ℝ) - j) else 1) •
      n07aAngularLevelBand hV γ t hI s l
        (n07aAngularLevelTruncate hV γ t (Nat.le_add_right s 3) Z))‖ ≤
      18 * n07aAngularTail ((j : ℤ) - l) * A * N := by
  have ht : 0 ≤ n07aAngularTail ((j : ℤ) - l) := n07aAngularTail_nonneg _
  by_cases hi : n07aScalarFrequency i = j
  · have hj : j ≤ 1 := hi.symm.le.trans (n07aScalarFrequency_le_one i)
    have hcol := n07a_small_input_weighted_column_block hV γ t hI s hj l commute Z
    have hc := hcol.trans (mul_le_mul_of_nonneg_left hZ
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) ht))
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hα hc (norm_nonneg _) hN).trans_eq (by ring)
  · rw [hzero hi, zero_smul, norm_zero]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) ht) hA) hN

private theorem n07a_scalar_columns_forget
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (hI : ∀ m, K.left m < K.right m)
    (s l : ℕ) (κ : ℝ) (α : Fin 3 → ℝ) (Z : Fin 3 → V.level γ t (s + 3))
    (f : Fin 3 → CanonicalSequence S K) (hZ : ∀ i, V.forget γ t (s + 3) (Z i) = f i) :
    V.forget γ t s (∑ i : Fin 3, α i • (κ • n07aAngularLevelBand hV γ t hI s l
      (n07aAngularLevelTruncate hV γ t (Nat.le_add_right s 3) (Z i)))) =
      (fun m => n07aAngularBand m (hI m) l (κ • ∑ i : Fin 3, α i • f i m)) := by
  classical
  rw [map_sum]
  funext m
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply]
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hband := n07aAngularLevelBand_forget hV γ t hI s l
    (n07aAngularLevelTruncate hV γ t (Nat.le_add_right s 3) (Z i))
  have htrunc := (n07aAngularLevelTruncate_forget hV γ t
    (Nat.le_add_right s 3) (Z i)).trans (hZ i)
  have he := congrFun (hband.trans (congrArg (n07aAngularSequenceBand hI l) htrunc)) m
  simp only [n07aAngularSequenceBand_apply] at he
  rw [he, map_smul, smul_comm κ]

private theorem n07a_scalar_three_norm_bound {E : Type*} [NormedAddCommGroup E]
    (v : Fin 3 → E) (tail A N f p : ℝ)
    (hv : ∀ i, ‖v i‖ ≤ 18 * tail * (A * (1 + p)) * (N * f)) :
    ‖∑ i : Fin 3, v i‖ ≤ tail * ((54 * A * N) * (1 + p) * f) := by
  classical
  calc
    ‖∑ i : Fin 3, v i‖ ≤ ∑ i : Fin 3, ‖v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, 18 * tail * (A * (1 + p)) * (N * f) :=
      Finset.sum_le_sum (fun i _ => hv i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem n07a_actualRelativeScalar_weighted_band_lift
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hV : IsVolumeModel T S K V) (hI : ∀ m, K.left m < K.right m) :
    ∃ d : ℕ, ∀ t : ℝ, ∀ s : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε),
      ∀ (j : ℕ) (F : V.level (3 / 4 : ℝ) 0 b),
      n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1 →
      ∀ (l : ℕ) (commute : Bool), ∃ W : V.level (3 / 4 : ℝ) t s,
        V.forget (3 / 4 : ℝ) t s W = (fun m => n07aAngularBand m (hI m) l
          ((if commute then ((l : ℝ) - j) else 1) •
            n07aRelativeScalarPart href hcur z hz m (hI m) (B.inverse F).val.1)) ∧
        ‖W‖ ≤ n07aAngularTail ((j : ℤ) - l) *
          (A * (1 + parameterGrading S (s + d) z) * ‖F‖) := by
  classical
  let columns := n07a_relativeScalarColumns_volume hD hS hT h01 h03 h04 href hcur hV
  let d : ℕ := columns.choose
  have hb := columns.choose_spec
  refine ⟨3 + d, fun t s => ?_⟩
  let A : ℝ := (hb (3 / 4 : ℝ) t (s + 3)).choose
  have hA : 0 < A := (hb (3 / 4 : ℝ) t (s + 3)).choose_spec.1
  have hcols := (hb (3 / 4 : ℝ) t (s + 3)).choose_spec.2
  refine ⟨54 * A * ‖B.inverse‖, by positivity, fun z hz j F hU l commute => ?_⟩
  let U : CanonicalUnknown S K := (B.inverse F).val.1
  let κ : ℝ := if commute then ((l : ℝ) - j) else 1
  let Z (i : Fin 3) : V.level (3 / 4 : ℝ) t (s + 3) := (hcols z hz i).choose
  have hZ (i : Fin 3) := (hcols z hz i).choose_spec
  let W : V.level (3 / 4 : ℝ) t s := ∑ i : Fin 3,
    n07aUnknownScalar U i • (κ • n07aAngularLevelBand hV (3 / 4 : ℝ) t hI s l
      (n07aAngularLevelTruncate hV (3 / 4 : ℝ) t (Nat.le_add_right s 3) (Z i)))
  have hscalar (i : Fin 3) (hi : n07aScalarFrequency i ≠ j) : n07aUnknownScalar U i = 0 := by
    have hband : n07aUnknownScalar (n07aAngularUnknownBand hI j U) i =
        n07aUnknownScalar U i :=
      congrArg (fun u : CanonicalUnknown S K => n07aUnknownScalar u i) hU
    exact hband.symm.trans ((n07aUnknownScalar_angularBand hI i j U).trans (ite_eq_right hi))
  have hn (i : Fin 3) : ‖n07aUnknownScalar U i •
      (κ • n07aAngularLevelBand hV (3 / 4 : ℝ) t hI s l
        (n07aAngularLevelTruncate hV (3 / 4 : ℝ) t (Nat.le_add_right s 3) (Z i)))‖ ≤
      18 * n07aAngularTail ((j : ℤ) - l) *
        (A * (1 + parameterGrading S (s + 3 + d) z)) * (‖B.inverse‖ * ‖F‖) :=
    n07a_scalar_column_norm_bound hV (3 / 4 : ℝ) t hI s i j l commute (Z i)
      (n07aUnknownScalar U i) (A * (1 + parameterGrading S (s + 3 + d) z))
      (‖B.inverse‖ * ‖F‖)
      (mul_nonneg hA.le (add_nonneg zero_le_one (apply_nonneg _ _)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hZ i).2
      (n07a_inverseUnknownScalar_norm_bound F i) (hscalar i)
  refine ⟨W, ?_, ?_⟩
  · have hw := n07a_scalar_columns_forget hV (3 / 4 : ℝ) t hI s l κ
      (n07aUnknownScalar U) Z (fun i m =>
        ((n07aCurrentScalarOpenCoefficient href hcur z hz m (hI m) i).sub
          (n07aReferenceScalarOpenCoefficient href m (hI m) i)).toLp)
      (fun i => (hZ i).1)
    refine hw.trans (funext fun m => ?_)
    exact congrArg (fun u => n07aAngularBand m (hI m) l (κ • u))
      (n07aRelativeScalarPart_eq_sum href hcur z hz m (hI m) U).symm
  · have hnW := n07a_scalar_three_norm_bound
      (fun i : Fin 3 => n07aUnknownScalar U i •
        (κ • n07aAngularLevelBand hV (3 / 4 : ℝ) t hI s l
          (n07aAngularLevelTruncate hV (3 / 4 : ℝ) t (Nat.le_add_right s 3) (Z i))))
      (n07aAngularTail ((j : ℤ) - l)) A ‖B.inverse‖ ‖F‖
      (parameterGrading S (s + 3 + d) z) hn
    exact hnW.trans_eq (congrArg (fun p : ℝ => n07aAngularTail ((j : ℤ) - l) *
      ((54 * A * ‖B.inverse‖) * (1 + p) * ‖F‖))
      (congrArg (fun k : ℕ => parameterGrading S k z) (Nat.add_assoc s 3 d)))

end ContinuousFlexibility.Analysis
