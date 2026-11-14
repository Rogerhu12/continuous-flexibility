module

public import ContinuousFlexibility.Analysis.N01ReturnInverseJets
public import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# Uniform positive angular jets of the actual return maps

The positive material height power absorbs the coefficient factor in
the genuine closed-time N01 estimate, uniformly over the actual cells.
The reference return is a translation, so its higher angular jets vanish.
Only positive inverse jets are estimated; no bound on the reference
translation or on an arbitrarily chosen component constant is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- The real bookkeeping of the forward estimate, with the state grading
evaluated at one point as an arbitrary monotone nonnegative sequence. -/
private theorem forward_higherJet_bound_aux (P : ℕ → ℝ) (hP : Monotone P)
    (hP0 : ∀ k, 0 ≤ P k) {y b H E K e : ℝ} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (hb : 0 ≤ b) (he : 0 ≤ 2 + 2 * e) (hK : 0 ≤ K) (hw : H * E ≤ K)
    (hy : y ≤ b * H * E * (2 + 2 * e) * P k₁) :
    y ≤ (1 + b * K * (2 + 2 * e)) * (1 + P k₂) := by
  have h1 : b * H * E * (2 + 2 * e) ≤ b * K * (2 + 2 * e) := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hb) he
    simpa only [mul_assoc] using h
  have hc : 0 ≤ b * K * (2 + 2 * e) := mul_nonneg (mul_nonneg hb hK) he
  have hP2 := hP0 k₂
  calc
    y ≤ b * H * E * (2 + 2 * e) * P k₁ := hy
    _ ≤ b * K * (2 + 2 * e) * P k₁ := mul_le_mul_of_nonneg_right h1 (hP0 k₁)
    _ ≤ b * K * (2 + 2 * e) * P k₂ := mul_le_mul_of_nonneg_left (hP hk) hc
    _ ≤ (1 + b * K * (2 + 2 * e)) * (1 + P k₂) := by nlinarith only [hc, hP2]

/-- The real bookkeeping of the first inverse jet. -/
private theorem inverse_first_bound_aux (P : ℕ → ℝ) (hP0 : ∀ k, 0 ≤ P k)
    {y a q : ℝ} {k : ℕ} (hq : q = 2 + a) (ha : 1 ≤ a) (hy : y ≤ 2) :
    y ≤ q * (1 : ℝ) ^ q * (1 + P k) := by
  subst hq
  rw [Real.one_rpow, mul_one]
  have h := mul_nonneg (show (0 : ℝ) ≤ 2 + a by linarith only [ha]) (hP0 k)
  nlinarith only [h, hy, ha]

/-- The real bookkeeping of the higher forward jets fed to the inverse. -/
private theorem inverse_input_bound_aux (P : ℕ → ℝ) (hP0 : ∀ k, 0 ≤ P k)
    {k k' : ℕ} (hk : k' = k) {y a q : ℝ} (hq : q = 2 + a)
    (hy : y ≤ a * (1 + P k')) :
    y ≤ q * (1 : ℝ) ^ q * (1 + P k) := by
  subst hq
  rw [hk] at hy
  rw [Real.one_rpow, mul_one]
  exact hy.trans (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)) (add_nonneg zero_le_one (hP0 k)))

private theorem le_of_le_one_rpow_mul {y b t : ℝ} (h : y ≤ b * (1 : ℝ) ^ b * t) :
    y ≤ b * t := by
  rwa [Real.one_rpow, mul_one] at h

theorem n01_returnForward_higherJets_uniform
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ flowLoss : ℕ, ∃ A : ℕ → ℝ, (∀ n, 1 ≤ A n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m n : ℕ, 2 ≤ n → ∀ θ : ℝ,
        ‖iteratedFDeriv ℝ n (C.minusFlow z m (C.right m)) θ‖ ≤
          A n * (1 + pairGrading (stateGrading S) realGrading
            (n + (base + flowLoss)) (z - (C.referenceState, 0))) := by
  refine (ordinaryFlowFamily_le_linear_high_on_closed_of_n01 hS hT hN).elim ?_
  intro parameterLoss hclosedAll
  let B : ℕ → ℝ := fun n => (hclosedAll n).choose
  have hB (n : ℕ) : 0 < B n := (hclosedAll n).choose_spec.1
  have hclosed (n : ℕ) :
      N01ClosedFlowLinearHighBoundAtOrder T S C base (loss + parameterLoss) ε n (B n) :=
    (hclosedAll n).choose_spec.2
  have hKex (n : ℕ) := material_sample_height_coefficient_power_bounded hN.1.1 hT C.cell (B n)
    (by norm_num : (0 : ℝ) < 3 / 4)
  let K : ℕ → ℝ := fun n => (hKex n).choose
  have hK (n : ℕ) : 0 < K n := (hKex n).choose_spec.1
  have hweight (n m : ℕ) :
      T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B n ≤ K n :=
    (hKex n).choose_spec.2 m
  have hε : 0 < 2 + 2 * ε := by linarith only [hN.2.1]
  let A : ℕ → ℝ := fun n => 1 + B n * K n * (2 + 2 * ε)
  have hA (n : ℕ) : 1 ≤ A n :=
    le_add_of_nonneg_right (mul_nonneg (mul_nonneg (hB n).le (hK n).le) hε.le)
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  refine ⟨loss + parameterLoss, A, hA, ?_⟩
  intro z hz hs m n hn θ
  have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩
  let f₀ : ℝ → ℝ := C.minusFlow (C.referenceState, 0) m (C.right m)
  let c : ℝ := f₀ 0
  have href : f₀ = fun η => c + η := funext
    (ordinaryFlow_zeroParameter_eq_zeroAngle_add hN.2.2.2.2.2.2.1
      (reference_mem_stateNeighborhood S C base hN.2.1) m hr)
  have hf₀ : ContDiff ℝ ∞ f₀ := by
    rw [href]
    exact contDiff_const.add contDiff_id
  have hf := (n01_ordinaryFlow_angularRegularity hS hT hN hz hs m).1 _ hr
  have hzero : iteratedDeriv n f₀ θ = 0 := by
    rw [href, iteratedDeriv_const_add (by omega : 0 < n) c]
    simp only [iteratedDeriv_fun_id, if_neg (by omega : n ≠ 0), if_neg (by omega : n ≠ 1)]
  have he : iteratedDeriv n (fun η => C.minusFlow z m (C.right m) η - f₀ η) θ =
      iteratedDeriv n (C.minusFlow z m (C.right m)) θ := by
    simpa only [hzero, sub_zero] using iteratedDeriv_fun_sub (n := n) (x := θ)
      (hf.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      (hf₀.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
  have hfam : ordinaryFlowFamily S C m 0 n (C.right m, θ) z =
      iteratedDeriv n (fun η => C.minusFlow z m (C.right m) η - f₀ η) θ := by
    simp only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero, f₀]
  have hy : ‖iteratedFDeriv ℝ n (C.minusFlow z m (C.right m)) θ‖ =
      |ordinaryFlowFamily S C m 0 n (C.right m, θ) z| := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, ← he, hfam]
  have horder : max base (n + (loss + parameterLoss)) ≤
      n + (base + (loss + parameterLoss)) := by omega
  exact forward_higherJet_bound_aux
    (fun k => pairGrading (stateGrading S) realGrading k (z - (C.referenceState, 0)))
    (fun _ _ h => hp h _) (fun _ => apply_nonneg _ _) horder (hB n).le hε.le (hK n).le
    (hweight n m) (hy.trans_le (hclosed n m n (C.right m, θ) le_rfl hr z hz hs))

theorem n01_returnInverse_positiveJets_uniform
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ low outLoss : ℕ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m n : ℕ, 1 ≤ n → ∀ θ : ℝ,
        ‖iteratedFDeriv ℝ n (C.minusReturnInverse z m) θ‖ ≤
          B n * (1 + pairGrading (stateGrading S) realGrading
            (n + outLoss) (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  refine (n01_returnForward_higherJets_uniform hS hT hN).elim ?_
  intro flowLoss hF
  refine hF.elim ?_
  intro A hAF
  have hA := hAF.1
  have hforward := hAF.2
  refine (nonlinearInverse_positiveJets_le_material.{0, 0} hp hI (base + flowLoss)).elim ?_
  intro low hlowEx
  refine hlowEx.elim ?_
  intro outLoss htarget
  let Q : ℕ → ℝ := fun j => 2 + A (j + 1)
  have hQ (j : ℕ) : 1 ≤ Q j := by
    dsimp only [Q]
    linarith only [hA (j + 1)]
  refine (htarget Q hQ).elim ?_
  intro B hBb
  have hB := hBb.1
  have hbound := hBb.2
  refine ⟨low, outLoss, B, hB, ?_⟩
  intro z hz hs hlow m n hn θ
  let f : ℝ → ℝ := C.minusFlow z m (C.right m)
  let g : ℝ → ℝ := C.minusReturnInverse z m
  have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩
  have hf : ContDiff ℝ ∞ f :=
    (n01_ordinaryFlow_angularRegularity hS hT hN hz hs m).1 _ hr
  have hg : ContDiff ℝ ∞ g := n01_minusReturnInverse_contDiff hS hT hN hz hs m
  have hright (η : ℝ) : f (g η) = η :=
    (hN.2.2.2.2.2.2.2.2.1 z hz hs m η).1
  have hleft (η : ℝ) : g (f η) = η :=
    (hN.2.2.2.2.2.2.2.2.1 z hz hs m η).2.1
  have hfg : f ∘ g =ᶠ[𝓝 θ] (id : ℝ → ℝ) := Eventually.of_forall hright
  have hL : (fderiv ℝ g θ).comp (fderiv ℝ f (g θ)) =
      ContinuousLinearMap.id ℝ ℝ := by
    have he : g ∘ f = id := funext hleft
    calc
      _ = (fderiv ℝ g (f (g θ))).comp (fderiv ℝ f (g θ)) := by rw [hright θ]
      _ = fderiv ℝ (g ∘ f) (g θ) :=
        (fderiv_comp (g θ) (hg.differentiable (by simp) _)
          (hf.differentiable (by simp) _)).symm
      _ = _ := by rw [he, fderiv_id]
  have hfirst : ‖fderiv ℝ g θ‖ ≤ 2 := by
    have hJ := (canonicalReturnJacobianBounds_of_n01 hN hflow z hz hs m θ).1
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_one, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith only [hJ.1], hJ.2⟩
  have hP0 : ∀ k, 0 ≤ pairGrading (stateGrading S) realGrading k
      (z - (C.referenceState, 0)) := fun k => apply_nonneg _ _
  have hfirst' : ‖fderiv ℝ g θ‖ ≤ Q 0 * (1 : ℝ) ^ (Q 0) *
      (1 + pairGrading (stateGrading S) realGrading (base + flowLoss + 1)
        (z - (C.referenceState, 0))) :=
    inverse_first_bound_aux _ hP0 rfl (hA 1) hfirst
  have hraw (j : ℕ) (hj : 1 ≤ j) :
      ‖iteratedFDeriv ℝ (j + 1) f (g θ)‖ ≤ Q j * (1 : ℝ) ^ (Q j) *
        (1 + pairGrading (stateGrading S) realGrading (j + (base + flowLoss) + 1)
          (z - (C.referenceState, 0))) :=
    inverse_input_bound_aux _ hP0 (by omega) rfl
      (hforward z hz hs m (j + 1) (by omega) (g θ))
  exact le_of_le_one_rpow_mul
    (hbound (z - (C.referenceState, 0)) hlow 1 le_rfl ℝ ℝ f g θ
      hf.contDiffAt hg.contDiffAt hfg (fderiv ℝ g θ) hL hfirst' hraw n hn)

end ContinuousFlexibility.Analysis
