import ContinuousFlexibility.Analysis.N01OrdinaryFlowClosedJets
import ContinuousFlexibility.Analysis.ScalarInverseMaterialJets
import ContinuousFlexibility.Analysis.CanonicalReturnJacobianBounds
import ContinuousFlexibility.Analysis.CanonicalStateInterpolation

/-!
# Actual N01 return inverse jets with one state loss

Closed-time angular regularity and the actual N01 variation bound control
the forward return. At the reference state it is an angular translation.
The stored inverse is smooth by its actual right-inverse identity, and
the nonlinear inverse estimate supplies all its higher derivatives.
Component constants are selected before the state and the angle; the
common low order and loss are selected before the component.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private def ScalarReturnForwardJetBound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (A : ℕ → ℝ) (z : E) (f : ℝ → ℝ) : Prop :=
  (∀ n : ℕ, 2 ≤ n → ∀ θ,
    ‖iteratedFDeriv ℝ n f θ‖ ≤ A n * (1 + p (n + loss) z)) ∧
  ∀ θ, |f θ - θ| ≤ A 0 * (1 + p loss z)

private def returnJetMajorant (M : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  1 + |M n| + |c|

private theorem returnJetMajorant_ge_one (M : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    1 ≤ returnJetMajorant M c n := by
  dsimp only [returnJetMajorant]
  linarith [abs_nonneg (M n), abs_nonneg c]

private theorem returnForwardJets_of_translation_difference
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {base loss : ℕ} {f f₀ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {c : ℝ} (href : ∀ θ, f₀ θ = c + θ) (M : ℕ → ℝ) (z : E)
    (hdiff : ∀ n θ, |iteratedDeriv n (fun η => f η - f₀ η) θ| ≤
      M n * p (max base (n + loss)) z) :
    ScalarReturnForwardJetBound p (base + loss) (returnJetMajorant M c) z f := by
  have he₀ : f₀ = fun θ => c + θ := funext href
  have hf₀ : ContDiff ℝ ∞ f₀ := by rw [he₀]; exact contDiff_const.add contDiff_id
  have hdiff' (n : ℕ) (θ : ℝ) :
      |iteratedDeriv n (fun η => f η - f₀ η) θ| ≤
        |M n| * p (n + (base + loss)) z := by
    have horder : max base (n + loss) ≤ n + (base + loss) := by omega
    exact (hdiff n θ).trans ((mul_le_mul_of_nonneg_right (le_abs_self _)
      (apply_nonneg _ _)).trans (mul_le_mul_of_nonneg_left
        ((hp horder) z) (abs_nonneg _)))
  constructor
  · intro n hn θ
    have hzero : iteratedDeriv n f₀ θ = 0 := by
      rw [he₀, iteratedDeriv_const_add (by omega : 0 < n) c]
      simp only [iteratedDeriv_id, iteratedDeriv_fun_id,
        if_neg (by omega : n ≠ 0), if_neg (by omega : n ≠ 1)]
    have he := iteratedDeriv_fun_sub (n := n) (x := θ)
      (hf.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      (hf₀.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    have he' : iteratedDeriv n (fun η => f η - f₀ η) θ = iteratedDeriv n f θ := by
      simpa only [hzero, sub_zero] using he
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, ← he']
    apply (hdiff' n θ).trans
    have hs := apply_nonneg (p (n + (base + loss))) z
    dsimp only [returnJetMajorant]
    nlinarith [abs_nonneg (M n), abs_nonneg c]
  · intro θ
    have hb : |f θ - f₀ θ| ≤ |M 0| * p (base + loss) z := by
      simpa only [iteratedDeriv_zero, Nat.zero_add] using hdiff' 0 θ
    have he : f θ - θ = (f θ - f₀ θ) + c := by rw [href θ]; ring
    rw [he]
    apply (abs_add_le _ _).trans
    apply (add_le_add hb le_rfl).trans
    have hs := apply_nonneg (p (base + loss)) z
    dsimp only [returnJetMajorant]
    nlinarith [abs_nonneg (M 0), abs_nonneg c]

private def N01ReturnForwardJetBound
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (A : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ScalarReturnForwardJetBound (pairGrading (stateGrading S) realGrading)
      loss A (z - (C.referenceState, 0)) (C.minusFlow z m (C.right m))

private theorem n01_returnForwardJets_of_closed_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (B : ℕ → ℝ)
    (hbound : ∀ n, N01ClosedFlowLinearHighBoundAtOrder T S C base loss ε n (B n))
    (m : ℕ) :
    ∃ A : ℕ → ℝ, (∀ n, 1 ≤ A n) ∧
      N01ReturnForwardJetBound S C base (base + loss) ε m A := by
  let M : ℕ → ℝ := fun n => B n * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
    T.E0 (T.sample (C.cell m)) ^ B n * (2 + 2 * ε)
  let c : ℝ := C.minusFlow (C.referenceState, 0) m (C.right m) 0
  have hclosed : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩
  have href : ∀ θ, C.minusFlow (C.referenceState, 0) m (C.right m) θ = c + θ :=
    ordinaryFlow_zeroParameter_eq_zeroAngle_add hN.2.2.2.2.2.2.1
      (reference_mem_stateNeighborhood S C base hN.2.1) m hclosed
  refine ⟨returnJetMajorant M c, returnJetMajorant_ge_one M c, ?_⟩
  intro z hz hs
  exact returnForwardJets_of_translation_difference
    (tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl))
    ((n01_ordinaryFlow_angularRegularity hS hT hN hz hs m).1 _ hclosed)
    href M (z - (C.referenceState, 0))
    (fun n θ => hbound n m n (C.right m, θ) le_rfl hclosed z hz hs)

/-- The actual stored return inverse is smooth at every real angle,
including the physical return endpoint used to define it. -/
theorem n01_minusReturnInverse_contDiff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ContDiff ℝ ∞ (C.minusReturnInverse z m) := by
  have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩
  exact contDiff_scalar_rightInverse_of_deriv_pos
    ((n01_ordinaryFlow_angularRegularity hS hT hN hz hs m).1 _ hr)
    (fun θ => ((hN.2.2.2.2.2.2.1 z hz m θ).2.2.2 _ hr).1)
    (fun θ => (hN.2.2.2.2.2.2.2.2.1 z hz hs m θ).1)

/-- All angular orders of the actual inverse displacement, measured in
the original paired state grading on the same N01 neighborhood. -/
def N01ReturnInverseJetBound
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low outLoss : ℕ) (ε : ℝ) (m : ℕ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ n θ, ‖iteratedFDeriv ℝ n (fun η => C.minusReturnInverse z m η - η) θ‖ ≤
      B n * (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
        (z - (C.referenceState, 0)))

private theorem scalar_fderiv_norm_le_two
    {g : ℝ → ℝ} {θ : ℝ}
    (h : (1 / 2 : ℝ) ≤ deriv g θ ∧ deriv g θ ≤ 2) :
    ‖fderiv ℝ g θ‖ ≤ 2 := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_one, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [h.1], h.2⟩

private theorem n01_returnInverse_bound_of_forward
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss low outLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hJ : CanonicalReturnJacobianBounds S C base ε)
    (m : ℕ) (A B : ℕ → ℝ)
    (hf : N01ReturnForwardJetBound S C base (base + loss) ε m A)
    (hbound : ScalarInverseDisplacementEstimate
      (pairGrading (stateGrading S) realGrading) low (base + loss) outLoss A B) :
    N01ReturnInverseJetBound S C base low outLoss ε m B := by
  intro z hz hs hlow
  have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩
  exact hbound (z - (C.referenceState, 0)) hlow
    (C.minusFlow z m (C.right m)) (C.minusReturnInverse z m)
    ((n01_ordinaryFlow_angularRegularity hS hT hN hz hs m).1 _ hr)
    (n01_minusReturnInverse_contDiff hS hT hN hz hs m)
    (fun θ => (hN.2.2.2.2.2.2.2.2.1 z hz hs m θ).1)
    (fun θ => (hN.2.2.2.2.2.2.2.2.1 z hz hs m θ).2.1)
    (fun θ => scalar_fderiv_norm_le_two (hJ z hz hs m θ).1)
    (hf z hz hs).1 (hf z hz hs).2

/-- One low order and one derivative loss work for every component and
every angular order. The first-Jacobian input is the genuine uniform
bound already obtained from N01 by a common neighborhood restriction. -/
theorem n01_minusReturnInverse_displacement_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ low outLoss : ℕ, ∀ m : ℕ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      N01ReturnInverseJetBound S C base low outLoss ε m B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  obtain ⟨low, outLoss, htarget⟩ := scalarInverse_displacement_fixed_loss hp hI (base + loss)
  choose A hA hforward using
    (fun n => ordinaryFlowFamily_le_linear_high_on_closed_of_n01 hS hT hN n)
  have hJ := canonicalReturnJacobianBounds_of_n01 hN hflow
  refine ⟨low, outLoss, ?_⟩
  intro m
  obtain ⟨C, hC, hraw⟩ := n01_returnForwardJets_of_closed_bound hS hT hN A hforward m
  obtain ⟨B, hB, hbound⟩ := htarget C hC
  exact ⟨B, hB, n01_returnInverse_bound_of_forward hS hT hN hJ m C B hraw hbound⟩

end ContinuousFlexibility.Analysis
