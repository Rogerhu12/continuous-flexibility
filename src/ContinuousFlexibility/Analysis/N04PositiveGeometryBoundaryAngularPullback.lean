module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryPlaneProjection
public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryInversePrefix
public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryComposition
public import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInverseLinearBounds

/-!
# Finite angular pullback bounds from original source tensors

A triangular first inverse differential and the positive source tensors
determine every required inverse jet. The partition formula then bounds
the actual radial pullback derivative, preserving its angular reserve.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04PositiveGeometry_boundaryAngularPullback_word_bound
    (N n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ, 1 ≤ degree ∧
    ∀ {U : Set E}, IsOpen U →
    ∀ (f g : E × ℝ → PolarPoint → PolarPoint) (ξ : E × ℝ → PolarPoint → ℝ)
      (q : E × ℝ → PolarPoint) (b : E × ℝ → ℝ)
      (S : ∀ j : ℕ, E × ℝ → PolarPoint [×j]→L[ℝ] PolarPoint),
    (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f y) (g y (q y))) →
    (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g y) (q y)) →
    (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (ξ y) (g y (q y))) →
    (∀ y ∈ U ×ˢ univ, f y ∘ g y =ᶠ[𝓝 (q y)] (id : PolarPoint → PolarPoint)) →
    (∀ y ∈ U ×ˢ univ,
      (n04PositiveGeometry_rootInverseLinear 1 1 ((S 1 y (fun _ => (1, 0))).2) (b y)).comp
        (fderiv ℝ (f y) (g y (q y))) = ContinuousLinearMap.id ℝ PolarPoint) →
    (∀ j, 2 ≤ j → j ≤ 4 → ∀ y ∈ U ×ˢ univ,
      iteratedFDeriv ℝ j (f y) (g y (q y)) =
        n04PositiveGeometry_angleOutputProjection.compContinuousMultilinearMap (S j y)) →
    (∀ j, 1 ≤ j → j ≤ 4 → ∀ y ∈ U ×ˢ univ,
      iteratedFDeriv ℝ j (ξ y) (g y (q y)) =
        (ContinuousLinearMap.fst ℝ ℝ ℝ).compContinuousMultilinearMap (S j y)) →
    ∀ JS : ∀ j, 1 ≤ j → j ≤ 4 → SmoothDirections (U ×ˢ univ) (S j),
    ∀ Jb : SmoothDirections (U ×ˢ univ) b,
    ∀ Q : SmoothDirections (U ×ˢ univ)
      (fun y => iteratedFDeriv ℝ n (ξ y ∘ g y) (q y) (fun _ => (1, 0))),
    ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
    ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ L → H ≤ M → 1 ≤ t → ∀ shift,
    (∀ j hj hj4, N04BoundaryWordBounds (JS j hj hj4) K s d x θ P M H t shift) →
    N04BoundaryWordBounds Jb K s d x θ P M H t shift →
    N04BoundaryWordBounds Q K s d x θ P (C * M ^ degree) H t shift := by
  obtain ⟨CL, hCL, dL, hdL, hlinear⟩ :=
    n04PositiveGeometry_rootInverseLinear_word_bound (E := E) N L hL
  obtain ⟨CI, hCI, dI, hdI, hinverse⟩ :=
    n04PositiveGeometry_boundaryInverse_prefix_bound
      (X := E) (E := PolarPoint) (F := PolarPoint) N 4
  obtain ⟨CC, hCC, hcomposition⟩ := n04PositiveGeometry_boundaryComposition_bound
    (X := E) (E := PolarPoint) (F := ℝ) (G := PolarPoint) N n (by omega)
  let C₁ : ℝ := 16 + CL
  have hC₁ : 1 ≤ C₁ := by dsimp only [C₁]; linarith
  let C₂ : ℝ := CI * C₁ ^ dI
  have hC₂ : 1 ≤ C₂ := one_le_mul_of_one_le_of_one_le hCI (one_le_pow₀ hC₁)
  let dc := n + 1 + 2 * N
  let C := CC * C₂ ^ dc
  let degree := (dL * dI) * dc
  have hd : 1 ≤ degree := Nat.mul_le_mul
    (Nat.mul_le_mul hdL hdI) (show 1 ≤ dc by dsimp only [dc]; omega)
  refine ⟨C, one_le_mul_of_one_le_of_one_le hCC (one_le_pow₀ hC₂), degree, hd, ?_⟩
  intro U hU f g ξ q b S hf hg hξ hfg hleft hF hX JS Jb Q K s d hN x hx θ P
    M H t hM hH hHL hHM ht shift hS hb
  let Ja := smoothDirections_postcompCLM
    (n04PositiveGeometry_boundaryFixedEvaluation_directions (JS 1 le_rfl (by decide))
      (fun _ => (1, 0))) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let Jone : SmoothDirections (U ×ˢ univ) (fun _ : E × ℝ => (1 : ℝ)) :=
    smoothDirections_constant (hU.prod isOpen_univ) (1 : ℝ)
  let JL := n04PositiveGeometry_rootInverseLinear_directions 1 Jone Ja Jb
  let Λ : E × ℝ → PolarPoint →L[ℝ] PolarPoint := fun y =>
    n04PositiveGeometry_rootInverseLinear 1 1 ((S 1 y (fun _ => (1, 0))).2) (b y)
  let JF (j : ℕ) (hj : 2 ≤ j) (hj4 : j ≤ 4) : SmoothDirections (U ×ˢ univ)
      (fun y => iteratedFDeriv ℝ j (f y) (g y (q y))) :=
    (n04PositiveGeometry_planePostcomp_directions (JS j (by omega) hj4)
      n04PositiveGeometry_angleOutputProjection).congr (fun y hy => (hF j hj hj4 y hy).symm)
  let JX (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) : SmoothDirections (U ×ˢ univ)
      (fun y => iteratedFDeriv ℝ j (ξ y) (g y (q y))) :=
    (n04PositiveGeometry_planePostcomp_directions (JS j hj hj4)
      (ContinuousLinearMap.fst ℝ ℝ ℝ)).congr (fun y hy => (hX j hj hj4 y hy).symm)
  let JG (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) (v : Fin j → PolarPoint) :=
    n04Realization_inverse_finiteJet_directions (hU.prod isOpen_univ)
      hf hg hfg hleft JL 4 JF j hj hj4 v
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have ha : N04BoundaryWordBounds Ja K s d x θ P M H t shift :=
    ((hS 1 le_rfl (by decide)).fixedEvaluation (fun _ => (1, 0)) (fun _ => by simp)).postcompCLM
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  have hone : N04BoundaryWordBounds Jone K s d x θ P M H t shift :=
    n04PositiveGeometry_boundaryWord_constant 1 Jone K s d x hx θ P M H t shift
      hM0 hH ht0 (by simpa only [abs_one] using hM)
  have hJL := hlinear hU Jone Ja Jb 1 (Or.inl rfl) JL K s d hN x hx θ P M H t
    hM hH hHL ht shift hone ha hb
  have htwo (j : ℕ) (hj : j ≤ 4) : (2 : ℝ) ^ j * M ≤ 16 * M :=
    mul_le_mul_of_nonneg_right
      ((pow_le_pow_right₀ (by norm_num) hj).trans_eq (by norm_num)) hM0
  have hJF (j : ℕ) (hj : 2 ≤ j) (hj4 : j ≤ 4) :
      N04BoundaryWordBounds (JF j hj hj4) K s d x θ P (16 * M) H t shift := by
    let JP := n04PositiveGeometry_planePostcomp_directions (JS j (by omega) hj4)
      n04PositiveGeometry_angleOutputProjection
    have h := (hS j (by omega) hj4).planePostcomp hx hM0 hH ht0
      n04PositiveGeometry_angleOutputProjection n04PositiveGeometry_angleOutputProjection_norm JP
    exact (h.enlarge hH ht0 (htwo j hj4)).congr hx (fun y hy => (hF j hj hj4 y hy).symm)
  have hJX (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) :
      N04BoundaryWordBounds (JX j hj hj4) K s d x θ P (16 * M) H t shift := by
    let JP := n04PositiveGeometry_planePostcomp_directions (JS j hj hj4)
      (ContinuousLinearMap.fst ℝ ℝ ℝ)
    have h := (hS j hj hj4).planePostcomp hx hM0 hH ht0
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) JP
    exact (h.enlarge hH ht0 (htwo j hj4)).congr hx (fun y hy => (hX j hj hj4 y hy).symm)
  let B := C₁ * M ^ dL
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hC₁ (one_le_pow₀ hM)
  have hMp : M ≤ M ^ dL := by simpa only [pow_one] using pow_le_pow_right₀ hM hdL
  have h16 : 16 * M ≤ B := mul_le_mul (by dsimp only [C₁]; linarith) hMp hM0
    (zero_le_one.trans hC₁)
  have hMB : M ≤ B := hMp.trans (le_mul_of_one_le_left (pow_nonneg hM0 _) hC₁)
  have hLB : CL * M ^ dL ≤ B :=
    mul_le_mul_of_nonneg_right (by dsimp only [C₁]; linarith) (pow_nonneg hM0 _)
  have hGI (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) (v : Fin j → PolarPoint)
      (hv : ∀ i, ‖v i‖ ≤ 1) :
      N04BoundaryWordBounds (JG j hj hj4 v) K s d x θ P (CI * B ^ dI) H t shift :=
    hinverse hU f g q Λ hf hg hfg hleft JL JF K s d hN x hx θ P B H t
      hB hH (hHM.trans hMB) ht shift (hJL.enlarge hH ht0 hLB)
      (fun k hk hk4 => (hJF k hk hk4).enlarge hH ht0 h16) j hj hj4 v hv (JG j hj hj4 v)
  let I := CI * B ^ dI
  have hBp : B ≤ B ^ dI := by
    simpa only [pow_one] using pow_le_pow_right₀ hB hdI
  have hBI : B ≤ I := hBp.trans
    (le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hB) _) hCI)
  have hI : 1 ≤ I := hB.trans hBI
  have hout := hcomposition hU ξ g q hξ hg
    (fun j hj hjn => JX j hj (hjn.trans hn4))
    (fun j hj hjn v => JG j hj (hjn.trans hn4) v)
    K s d hN x hx θ P I H t hI hH ((hHM.trans hMB).trans hBI) ht shift
    (fun j hj hjn => (hJX j hj (hjn.trans hn4)).enlarge hH ht0 (h16.trans hBI))
    (fun j hj hjn v hv => hGI j hj (hjn.trans hn4) v hv)
    (fun _ => (1, 0)) (fun _ => by simp) Q
  have hcost : CC * I ^ dc = C * M ^ degree := by
    dsimp only [I, B, C, C₂, degree]
    simp only [mul_pow, ← pow_mul, Nat.mul_assoc]
    ring
  exact hout.enlarge hH ht0 hcost.le

end ContinuousFlexibility.Analysis
