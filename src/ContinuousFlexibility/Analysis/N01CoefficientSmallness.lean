import ContinuousFlexibility.Analysis.N01NeighborhoodRestriction
import ContinuousFlexibility.Analysis.SmoothDirectionsScalarLine
import ContinuousFlexibility.Analysis.MaterialSampleRadialLoss
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Small actual coefficient differences on one common neighborhood

The first genuine N01 variation is integrated along the affine segment
from the reference state. Its one-high weight is bounded by the small
radius of a sufficiently high state neighborhood. Positive material
height powers absorb every fixed radial coefficient loss, uniformly over
the actual reference cells.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

theorem oneHighVariationWeight_one
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x v : E) :
    oneHighVariationWeight p base high x (fun _ : Fin 1 => v) =
      (1 + p high x) * p base v + p high v := by
  classical
  have hu : (Finset.univ : Finset (Fin 1)) = {0} := by
    ext i
    simp [Subsingleton.elim i (0 : Fin 1)]
  simp only [oneHighVariationWeight, hu, Finset.prod_singleton,
    Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty, mul_one]

theorem oneHighVariationWeight_one_smul_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (v : E)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    oneHighVariationWeight p base high (t • v) (fun _ : Fin 1 => v) ≤
      (1 + p high v) * p base v + p high v := by
  rw [oneHighVariationWeight_one, map_smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg ht.1]
  have ht' : t * p high v ≤ p high v := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (apply_nonneg _ _)
  exact add_le_add_right
    (mul_le_mul_of_nonneg_right (add_le_add_left ht' 1) (apply_nonneg _ _)) _

theorem SmoothDirections.sub_le_of_first_variation
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E → ℝ}
    (J : SmoothDirections U f) (p : ℕ → Seminorm ℝ E) (base high : ℕ)
    (x y : E) (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ U)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |J.D 1 (x + t • (y - x)) (fun _ => y - x)| ≤
        A * oneHighVariationWeight p base high
          ((x + t • (y - x)) - x) (fun _ : Fin 1 => y - x)) :
    |f y - f x| ≤ A * ((1 + p high (y - x)) * p base (y - x) + p high (y - x)) := by
  let v := y - x
  have hcons : Fin.cons v (Fin.elim0 : Fin 0 → E) = (fun _ : Fin 1 => v) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s : ℝ => J.D 0 (x + s • v) Fin.elim0)
        (J.D 1 (x + t • v) (fun _ => v)) (Icc (0 : ℝ) 1) t := by
    simpa only [Nat.zero_add, hcons] using
      (J.hasDerivAt_line_jet x v 0 Fin.elim0 (hsegment t ht)).hasDerivWithinAt
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖J.D 1 (x + t • v) (fun _ => v)‖ ≤
        A * ((1 + p high v) * p base v + p high v) := by
    rw [Real.norm_eq_abs]
    have h := hbound t ht
    rw [add_sub_cancel_left] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (oneHighVariationWeight_one_smul_le p base high v ht) hA)
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  have hpoint₀ : x + (0 : ℝ) • v = x := by simp only [zero_smul, add_zero]
  have hpoint₁ : x + (1 : ℝ) • v = y := by
    dsimp only [v]
    rw [one_smul]
    abel
  have hzero : x ∈ U := by simpa only [hpoint₀] using hsegment 0 (by simp)
  have hone : y ∈ U := by simpa only [hpoint₁] using hsegment 1 (by simp)
  simpa only [hpoint₀, hpoint₁,
    J.zero x hzero, J.zero y hone, sub_zero, norm_one, mul_one, Real.norm_eq_abs] using h

theorem stateNeighborhood_segment (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) {base : ℕ} {ε : ℝ}
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (C.referenceState, (0 : ℝ)) + t • (z - (C.referenceState, 0)) ∈
      stateNeighborhood S C base ε := by
  constructor
  · change stateGrading S base
      ((C.referenceState + t • (z.1 - C.referenceState)) - C.referenceState) < ε
    rw [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (show t * stateGrading S base (z.1 - C.referenceState) ≤
      stateGrading S base (z.1 - C.referenceState) by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right ht.2 (apply_nonneg _ _)).trans_lt hz.1
  · change |(0 : ℝ) + t • (z.2 - 0)| < ε
    simp only [zero_add, sub_zero, smul_eq_mul, abs_mul, abs_of_nonneg ht.1]
    exact (show t * |z.2| ≤ |z.2| by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans_lt hz.2

theorem stateNeighborhood_pairGrading_lt
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    {base n : ℕ} {η : ℝ} (hn : n ≤ base)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base η) :
    pairGrading (stateGrading S) realGrading n (z - (C.referenceState, 0)) < 2 * η := by
  change stateGrading S n (z.1 - C.referenceState) + ‖z.2 - 0‖ < 2 * η
  rw [sub_zero, Real.norm_eq_abs]
  have hs := (solve_stateGrading_monotone S hn (z.1 - C.referenceState)).trans_lt hz.1
  linarith only [hs, hz.2]

theorem coefficientFamily_reference_zero
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (i : Fin 3) (a b : ℕ) (p : PolarPoint) :
    coefficientFamily D S C i a b p (C.referenceState, 0) = 0 := by
  simp only [coefficientFamily, sub_self, mixedDerivative,
    iteratedDeriv_const_zero, Pi.zero_apply]

/-- The small radius occurs linearly, and the constant is common to all
three coefficients and all spatial jets up to the prescribed order. -/
theorem N01Properties.coefficientFamily_small_of_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ base' : ℕ, base ≤ base' → s + loss ≤ base' →
      ∀ η : ℝ, η ≤ ε → η ≤ 1 / 2 →
      ∀ z ∈ stateNeighborhood S C base' η, ∀ m i a b p,
        a + b ≤ s → p.1 ∈ D.cells m →
        |coefficientFamily D S C i a b p z| ≤
          6 * B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample m) ^ B * η := by
  have hdata := hN
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, hcoeff, _⟩
  obtain ⟨B, hB, hcoeff⟩ := hcoeff 1 s
  refine ⟨B, hB, fun base' hb hh η hηε hη₁ z hz m i a b p hab hp => ?_⟩
  have hzold := stateNeighborhood_mono S C hb hηε hz
  obtain ⟨J, hJ⟩ := hcoeff m i a b p hab hp
  obtain ⟨_, hRef⟩ := hN.1.1
  have hsample := materialSample_mem_radialCore hT hRef.2.1 m
  have hH : 0 < T.H (T.sample m) := (hT.2.1 _ hsample).2.1
  have hE : 0 < T.E0 (T.sample m) := (hT.2.1 _ hsample).2.2.1
  let A := B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg hB.le (Real.rpow_nonneg hH.le _)) (Real.rpow_nonneg hE.le _)
  have hline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (C.referenceState, (0 : ℝ)) + t • (z - (C.referenceState, 0)) ∈
        stateNeighborhood S C base ε := stateNeighborhood_segment S C hzold ht
  have h := J.sub_le_of_first_variation (pairGrading (stateGrading S) realGrading)
    base (s + loss) (C.referenceState, 0) z hline hA
    (fun t ht => hJ _ (hline t ht) (fun _ => z - (C.referenceState, 0)))
  rw [coefficientFamily_reference_zero, sub_zero] at h
  have hl := (stateNeighborhood_pairGrading_lt S C hb hz).le
  have hh' := (stateNeighborhood_pairGrading_lt S C hh hz).le
  have hh₁ : pairGrading (stateGrading S) realGrading (s + loss)
      (z - (C.referenceState, 0)) ≤ 1 := hh'.trans (by linarith only [hη₁])
  have hweight :
      (1 + pairGrading (stateGrading S) realGrading (s + loss)
        (z - (C.referenceState, 0))) *
        pairGrading (stateGrading S) realGrading base (z - (C.referenceState, 0)) +
        pairGrading (stateGrading S) realGrading (s + loss)
          (z - (C.referenceState, 0)) ≤ 6 * η := by
    calc
      _ ≤ (1 + 1) * (2 * η) + 2 * η :=
        add_le_add (mul_le_mul (add_le_add_left hh₁ 1) hl
          (apply_nonneg _ _) (by norm_num)) hh'
      _ = _ := by ring
  exact h.trans ((mul_le_mul_of_nonneg_left hweight hA).trans_eq (by dsimp only [A]; ring))

theorem materialSample_H_E0_radialE_envelope
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {γ P : ℝ} (hγ : 0 < γ) (hP : 0 ≤ P) (B : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m,
      T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ B *
        radialE (D.cellIndex m) ^ P ≤ K := by
  have hdata := hT
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, hE, _, _, _, _, _, _⟩
  obtain ⟨CE, hCE, he⟩ := hE B
  obtain ⟨CR, hCR, hr⟩ := materialSample_radialE_rpow_le_M_of_index_bound
    hT hRef (A := (1 : ℝ)) (R := P) (by norm_num) hP
  obtain ⟨CH, hCH, hh⟩ := materialSample_H_M_envelope hT hRef hγ (2 : ℝ)
  obtain ⟨_, hRef'⟩ := hRef
  refine ⟨CE * CR * CH, mul_pos (mul_pos hCE hCR) hCH, fun m => ?_⟩
  have hs := materialSample_mem_radialCore hT hRef'.2.1 m
  have hH := (Real.rpow_pos_of_pos (hT.2.1 _ hs).2.1 γ).le
  have hM := (zero_lt_one.trans_le (hT.2.1 _ hs).2.2.2).le
  have hr' : radialE (D.cellIndex m) ^ P ≤ CR * T.M (T.sample m) :=
    hr m (D.cellIndex m) (by norm_num)
  have he' := he _ hs
  have hprod := mul_le_mul
    (mul_le_mul_of_nonneg_left he' hH) hr'
    (Real.rpow_nonneg (Real.exp_pos _).le _) (mul_nonneg hH (mul_nonneg hCE.le hM))
  calc
    _ ≤ T.H (T.sample m) ^ γ * (CE * T.M (T.sample m)) *
        (CR * T.M (T.sample m)) := hprod
    _ = (CE * CR) * (T.H (T.sample m) ^ γ * T.M (T.sample m) ^ (2 : ℝ)) := by
      rw [Real.rpow_two]
      ring
    _ ≤ (CE * CR) * CH := mul_le_mul_of_nonneg_left (hh m) (mul_nonneg hCE.le hCR.le)

/-- Every prescribed fixed radial loss is absorbed while the dependence
on the actual neighborhood radius remains linear. -/
theorem N01Properties.coefficientFamily_radial_small
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    ∃ K : ℝ, 0 < K ∧ ∀ base' : ℕ, base ≤ base' → s + loss ≤ base' →
      ∀ η : ℝ, 0 ≤ η → η ≤ ε → η ≤ 1 / 2 →
      ∀ z ∈ stateNeighborhood S C base' η, ∀ m i a b p,
        a + b ≤ s → p.1 ∈ D.cells m →
        |coefficientFamily D S C i a b p z| ≤
          K * η * radialE (D.cellIndex m) ^ (-P) := by
  obtain ⟨B, hB, hb⟩ := hN.coefficientFamily_small_of_neighborhood hT s
  obtain ⟨K, hK, henv⟩ := materialSample_H_E0_radialE_envelope
    hT hN.1.1 (γ := (3 / 4 : ℝ)) (by norm_num) hP B
  refine ⟨6 * B * K, mul_pos (mul_pos (by norm_num) hB) hK,
    fun base' hbase hhigh η hη hηε hη₁ z hz m i a b p hab hp => ?_⟩
  have hE : 0 < radialE (D.cellIndex m) := Real.exp_pos _
  have hEP : 0 < radialE (D.cellIndex m) ^ P := Real.rpow_pos_of_pos hE _
  have hscaled := mul_le_mul_of_nonneg_right
    (hb base' hbase hhigh η hηε hη₁ z hz m i a b p hab hp) hEP.le
  have henv' := mul_le_mul_of_nonneg_left (henv m)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hB.le) hη)
  have hbound : |coefficientFamily D S C i a b p z| * radialE (D.cellIndex m) ^ P ≤
      (6 * B * K) * η := by
    calc
      _ ≤ (6 * B * η) * (T.H (T.sample m) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample m) ^ B * radialE (D.cellIndex m) ^ P) := by
        convert hscaled using 1 <;> ring
      _ ≤ (6 * B * η) * K := henv'
      _ = _ := by ring
  rw [Real.rpow_neg hE.le, ← div_eq_mul_inv]
  exact (le_div_iff₀ hEP).mpr hbound

end ContinuousFlexibility.Statements

