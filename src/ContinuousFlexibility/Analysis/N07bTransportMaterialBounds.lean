import ContinuousFlexibility.Analysis.N07bFiniteTransportBounds
import ContinuousFlexibility.Analysis.N07bFiniteMaterialExtension
import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
import ContinuousFlexibility.Analysis.MaterialOrdinaryJets

/-!
# Finite material decay of the actual transported remainder

The ordinary jets of a height member lose only one material-envelope
factor. Pure pointwise bounds on the transport jets and the weight at its
image therefore give decay of the actual transported field. The final
extension uses C³ interior regularity and bounds only through order two.
The geometric weight comparison is an explicit hypothesis; no source,
operator-domain, or norm conclusion is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The three actual Fréchet jets of a height member have one common
ordinary material bound. This uses only its given height membership. -/
theorem n07b_heightMember_frechetJets_le_two
    {D : ReferenceData} {T : MaterialData} {β : ℝ} {u : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hu : HeightMember D T β u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, n ≤ 2 → ∀ x ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n u x‖ ≤ K * T.H x.1 ^ β * T.M x.1 := by
  classical
  have hmixed := mixedDerivative_bound_of_materialPullback hT hu.1
    (heightMember_materialPullback_mixedDerivative_uniform_bound hT hu)
  choose K hK hbound using hmixed
  let B : ℝ := ∑ a : Fin 3, ∑ b : Fin 3, K a b
  have hB : 0 ≤ B := Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => hK a b
  refine ⟨4 * B, mul_nonneg (by norm_num) hB, ?_⟩
  intro n hn x hx
  have hpos := hT.2.1 x.1 hx.1
  have hH : 0 ≤ T.H x.1 ^ β := (Real.rpow_pos_of_pos hpos.2.1 β).le
  have hM : 0 ≤ T.M x.1 := zero_le_one.trans hpos.2.2.2
  have hjet : ‖iteratedFDeriv ℝ n u x‖ ≤
      (2 : ℝ) ^ n * (B * T.H x.1 ^ β * T.M x.1) := by
    apply norm_iteratedFDeriv_le_of_mixedDerivative
      (isOpen_Ioo.prod isOpen_univ) hu.1 n hx
      (mul_nonneg (mul_nonneg hB hH) hM)
    intro a b hab
    let ia : Fin 3 := ⟨a, by omega⟩
    let ib : Fin 3 := ⟨b, by omega⟩
    have habound : K ia ib ≤ ∑ j : Fin 3, K ia j :=
      Finset.single_le_sum (fun j _ => hK ia j) (Finset.mem_univ ib)
    have hbouter : (∑ j : Fin 3, K ia j) ≤ B :=
      Finset.single_le_sum
        (fun i _ => Finset.sum_nonneg fun j _ => hK i j) (Finset.mem_univ ia)
    have hKB : K a b ≤ B := habound.trans hbouter
    rw [Real.norm_eq_abs]
    exact (hbound a b x hx).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKB hH) hM)
  have hpower : (2 : ℝ) ^ n ≤ 4 := by interval_cases n <;> norm_num
  calc
    _ ≤ (2 : ℝ) ^ n * (B * T.H x.1 ^ β * T.M x.1) := hjet
    _ ≤ 4 * (B * T.H x.1 ^ β * T.M x.1) :=
      mul_le_mul_of_nonneg_right hpower (mul_nonneg (mul_nonneg hB hH) hM)
    _ = _ := by ring

/-- Polynomial material bounds on the actual transport jets and a pure
weight comparison imply actual jet decay of the transported remainder.
The only image weight required here is H^β M. -/
theorem n07b_transport_height_material_jet_bound
    {D : ReferenceData} {T : MaterialData} {β δ A B Q R C : ℝ}
    {u q : PolarPoint → ℝ} {τ : PolarPoint → PolarPoint}
    (hT : IsMaterialData D T) (hu : HeightMember D T β u)
    (hq : ContDiffOn ℝ 2 q (annularOpen D))
    (hτ : ContDiffOn ℝ 2 τ (annularOpen D))
    (hmap : MapsTo τ (annularOpen D) (annularOpen D))
    (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hqjet : ∀ x ∈ annularOpen D, ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n q x‖ ≤ Q * T.M x.1 ^ A)
    (hτjet : ∀ x ∈ annularOpen D, ∀ n : ℕ, 1 ≤ n → n ≤ 2 →
      ‖iteratedFDeriv ℝ n τ x‖ ≤ R * T.M x.1 ^ B)
    (hweight : ∀ x ∈ annularOpen D,
      T.H (τ x).1 ^ β * T.M (τ x).1 ≤ C * T.H x.1 ^ δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, n ≤ 2 → ∀ x ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n (fun y => q y * u (τ y)) x‖ ≤
        K * T.H x.1 ^ δ * T.M x.1 ^ (A + 2 * B) := by
  obtain ⟨Ku, hKu, hubound⟩ := n07b_heightMember_frechetJets_le_two hT hu
  refine ⟨8 * Q * Ku * C * (R + 1) ^ 2, by positivity, ?_⟩
  intro n hn x hx
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hpos := hT.2.1 x.1 hx.1
  have hMpos : 0 < T.M x.1 := zero_lt_one.trans_le hpos.2.2.2
  have hMA : 0 ≤ T.M x.1 ^ A := (Real.rpow_pos_of_pos hMpos A).le
  have hMB : 0 ≤ T.M x.1 ^ B := (Real.rpow_pos_of_pos hMpos B).le
  have hH : 0 ≤ T.H x.1 ^ δ := (Real.rpow_pos_of_pos hpos.2.1 δ).le
  have hRbound : 1 ≤ (R + 1) * T.M x.1 ^ B := by
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (R + 1) * T.M x.1 ^ B :=
        mul_le_mul (by linarith) (Real.one_le_rpow hpos.2.2.2 hB)
          (by norm_num) (by linarith)
  have hujet (i : ℕ) (hi : i ≤ 2) :
      ‖iteratedFDeriv ℝ i u (τ x)‖ ≤ Ku * C * T.H x.1 ^ δ := by
    calc
      _ ≤ Ku * T.H (τ x).1 ^ β * T.M (τ x).1 := hubound i hi (τ x) (hmap hx)
      _ = Ku * (T.H (τ x).1 ^ β * T.M (τ x).1) := mul_assoc _ _ _
      _ ≤ Ku * (C * T.H x.1 ^ δ) := mul_le_mul_of_nonneg_left (hweight x hx) hKu
      _ = _ := by ring
  have hτjet' (i : ℕ) (hi : 1 ≤ i) (hi2 : i ≤ 2) :
      ‖iteratedFDeriv ℝ i τ x‖ ≤ (R + 1) * T.M x.1 ^ B :=
    (hτjet x hx i hi hi2).trans
      (mul_le_mul_of_nonneg_right (by linarith) hMB)
  have h := n07b_norm_jet_transport_le_two hU hU hq hτ
    (hu.1.of_le (by simp)) hmap hx (mul_nonneg hQ hMA)
    (mul_nonneg (mul_nonneg hKu hC) hH) hRbound (hqjet x hx) hujet hτjet' hn
  have hweightProduct :
      T.M x.1 ^ A * (T.M x.1 ^ B) ^ 2 = T.M x.1 ^ (A + 2 * B) := by
    rw [pow_two, ← Real.rpow_add hMpos, ← Real.rpow_add hMpos]
    congr 1
    ring
  calc
    _ ≤ 8 * (Q * T.M x.1 ^ A) * (Ku * C * T.H x.1 ^ δ) *
        ((R + 1) * T.M x.1 ^ B) ^ 2 := h
    _ = (8 * Q * Ku * C * (R + 1) ^ 2) * T.H x.1 ^ δ *
        (T.M x.1 ^ A * (T.M x.1 ^ B) ^ 2) := by ring
    _ = _ := by rw [hweightProduct]

/-- Positive image-weight decay and actual C³ interior transport give
a genuine C² flat endpoint extension. No third-jet bound is required. -/
theorem n07b_transport_height_c2_flat_extension
    {D : ReferenceData} {T : MaterialData} {β δ A B Q R C : ℝ}
    {u q : PolarPoint → ℝ} {τ : PolarPoint → PolarPoint}
    (hT : IsMaterialData D T) (hu : HeightMember D T β u) (hδ : 0 < δ)
    (hq : ContDiffOn ℝ 3 q (annularOpen D))
    (hτ : ContDiffOn ℝ 3 τ (annularOpen D))
    (hmap : MapsTo τ (annularOpen D) (annularOpen D))
    (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hqjet : ∀ x ∈ annularOpen D, ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n q x‖ ≤ Q * T.M x.1 ^ A)
    (hτjet : ∀ x ∈ annularOpen D, ∀ n : ℕ, 1 ≤ n → n ≤ 2 →
      ‖iteratedFDeriv ℝ n τ x‖ ≤ R * T.M x.1 ^ B)
    (hweight : ∀ x ∈ annularOpen D,
      T.H (τ x).1 ^ β * T.M (τ x).1 ≤ C * T.H x.1 ^ δ) :
    ContDiff ℝ 2 ((annularOpen D).indicator (fun y => q y * u (τ y))) ∧
      ∀ n : ℕ, n ≤ 2 → ∀ x : PolarPoint, x.1 ∉ Ioo D.a D.b →
        iteratedFDeriv ℝ n ((annularOpen D).indicator (fun y => q y * u (τ y))) x = 0 := by
  obtain ⟨K, hK, hbound⟩ := n07b_transport_height_material_jet_bound hT hu
    (hq.of_le (by norm_num)) (hτ.of_le (by norm_num)) hmap
    hQ hR hC hB hqjet hτjet hweight
  have hf : ContDiffOn ℝ 3 (fun y => q y * u (τ y)) (annularOpen D) :=
    hq.mul ((hu.1.of_le (by simp)).comp hτ hmap)
  exact n07b_c2_flat_extension_of_material_decay hT hδ hf
    (fun n hn => ⟨K, A + 2 * B, hK, hbound n hn⟩)

end ContinuousFlexibility.Analysis
