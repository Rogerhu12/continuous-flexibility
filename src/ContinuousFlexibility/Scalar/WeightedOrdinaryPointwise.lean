import ContinuousFlexibility.Scalar.WeightedPointwise
import ContinuousFlexibility.Analysis.MaterialOrdinaryJets

/-!
# Quantitative ordinary jets of decoded weighted heights

Constants are chosen before the height.  The material-coordinate product
formula uses only finitely many jets, all controlled by the input grading at
`a + b + 2`.  The physical derivative expansion then costs one envelope factor
`M`.  These are pointwise estimates; no estimate for a high output Sobolev norm
is inferred from them.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

private theorem weighted_angular_slice_contDiffOn
    {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (b : ℕ) (θ : ℝ) :
    ContDiffOn ℝ ∞ (fun r => iteratedDeriv b (fun t => f (r, t)) θ) (Ioo D.a D.b) := by
  have hs : ContDiff ℝ ∞ (fun r : ℝ => (r, θ)) := contDiff_id.prodMk contDiff_const
  have hm : MapsTo (fun r : ℝ => (r, θ)) (Ioo D.a D.b) (annularOpen D) :=
    fun _ hr => ⟨hr, mem_univ _⟩
  simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero] using
    (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hf 0 b).comp hs.contDiffOn hm

/-- The coefficients in the weighted Leibniz formula are independent of the
input height and its angular slice. -/
theorem materialDerivative_decode_angular_slice_le_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : A.Space) (θ r : ℝ), r ∈ Ioo D.a D.b →
      |materialDerivativeIterate T a
        (fun s => iteratedDeriv b (fun t => A.decode u (s, t)) θ) r| ≤
        C * T.H r ^ γ * A.grading (a + b + 2) u := by
  classical
  have hdata := hT
  obtain ⟨hcont, hpos, _, _, _, _, hradius, hinside, hinv, _⟩ := hdata
  have hH : ContDiff ℝ ∞ (fun x => T.H (T.radius x)) :=
    (hcont T.H (by simp)).comp_contDiff hradius (fun x => (hinside x).1)
  have hpositive (x : ℝ) : 0 < T.H (T.radius x) := (hpos _ (hinside x).1).2.1
  let F : ℝ → ℝ := fun x => T.H (T.radius x) ^ γ
  have hF : ContDiff ℝ ∞ F := hH.rpow_const_of_ne (fun x => (hpositive x).ne')
  have hweight (i : Fin (a + 1)) := iteratedDeriv_materialH_rpow_bound hT γ i.val
  choose B hB hBbound using hweight
  let C₀ : ℝ := 4 * Real.sqrt Real.pi
  have hC₀ : 0 ≤ C₀ := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  let C (i : Fin (a + 1)) : ℝ := (a.choose i.val : ℝ) * B i * C₀
  have hC (i : Fin (a + 1)) : 0 ≤ C i :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i)) hC₀
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro u θ r hr
  let f : PolarPoint → ℝ := A.decode u
  have hf : HeightMember D T γ f := hA.2.2.2.1 u
  let g : ℝ → ℝ := fun s => iteratedDeriv b (fun t => f (s, t)) θ
  let G : ℝ → ℝ := fun x =>
    iteratedDeriv b (fun t => materialPullback T γ f (x, t)) θ
  have hg : ContDiffOn ℝ ∞ g (Ioo D.a D.b) :=
    weighted_angular_slice_contDiffOn hf.1 b θ
  have hG : ContDiff ℝ ∞ G := by
    simpa only [G, mixedDerivative, iteratedDeriv_zero, Function.comp_def, id_eq] using
      (contDiff_mixedDerivative (contDiff_materialPullback hT hf.1) 0 b).comp
        (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => θ)))
  have hGform : G = fun x => T.H (T.radius x) ^ (-γ) * g (T.radius x) := by
    funext x
    change iteratedDeriv b (fun t => T.H (T.radius x) ^ (-γ) * f (T.radius x, t)) θ =
      T.H (T.radius x) ^ (-γ) * iteratedDeriv b (fun t => f (T.radius x, t)) θ
    exact iteratedDeriv_const_mul_field (T.H (T.radius x) ^ (-γ))
      (fun t => f (T.radius x, t))
  have hrestore : (fun x => F x * G x) = fun x => g (T.radius x) := by
    funext x
    change T.H (T.radius x) ^ γ * G x = _
    rw [hGform]
    rw [← mul_assoc, ← Real.rpow_add (hpositive x), add_neg_cancel, Real.rpow_zero, one_mul]
  have hpmono : Monotone A.grading :=
    gradedSeminorm_monotone (fun n => A.level n) A.bond
  have hGbound (i : Fin (a + 1)) (x : ℝ) :
      |iteratedDeriv (a - i.val) G x| ≤ C₀ * A.grading (a + b + 2) u := by
    have hbnd := materialPullback_decode_mixedDerivative_le_grading hT hA
      u (a - i.val) b (x, θ)
    change |iteratedDeriv (a - i.val) G x| ≤ C₀ * A.grading ((a - i.val) + b + 2) u at hbnd
    apply hbnd.trans
    exact mul_le_mul_of_nonneg_left (hpmono (by omega) u) hC₀
  have hbound (x : ℝ) :
      |iteratedDeriv a (fun t => F t * G t) x| ≤
        (∑ i, C i) * T.H (T.radius x) ^ γ * A.grading (a + b + 2) u := by
    let term (i : ℕ) : ℝ :=
      (a.choose i : ℝ) * iteratedDeriv i F x * iteratedDeriv (a - i) G x
    have hleibniz : iteratedDeriv a (fun t => F t * G t) x =
        ∑ i : Fin (a + 1), term i.val := by
      rw [Fin.sum_univ_eq_sum_range term]
      exact iteratedDeriv_mul (hF.contDiffAt.of_le (by simp)) (hG.contDiffAt.of_le (by simp))
    rw [hleibniz, Finset.sum_mul, Finset.sum_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    unfold term
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (a.choose i.val))]
    calc
      _ ≤ (a.choose i.val : ℝ) * (B i * T.H (T.radius x) ^ γ) *
          (C₀ * A.grading (a + b + 2) u) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hBbound i x) (Nat.cast_nonneg _))
          (hGbound i x) (abs_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (hB i) (Real.rpow_pos_of_pos (hpositive x) γ).le))
      _ = C i * T.H (T.radius x) ^ γ * A.grading (a + b + 2) u := by dsimp [C]; ring
  have hfinal := hbound (T.rho r)
  rw [hrestore, iteratedDeriv_comp_materialRadius hT hg, hinv r hr] at hfinal
  exact hfinal

/-- Every ordinary mixed jet is uniformly controlled by its explicit finite
input order.  The coefficient cost is one power of the material envelope. -/
theorem mixedDerivative_decode_le_weighted_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : A.Space) (p : PolarPoint), p ∈ annularOpen D →
      |mixedDerivative a b (A.decode u) p| ≤
        C * T.H p.1 ^ γ * T.M p.1 * A.grading (a + b + 2) u := by
  classical
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, henv, _, _, hexpansion, _⟩ := hdata
  obtain ⟨c, _, ⟨C, B, hC, _, hc⟩, hformula⟩ := hexpansion a
  obtain ⟨K, hK, hKbound⟩ := henv B
  have hslice (j : Fin (a + 1)) :=
    materialDerivative_decode_angular_slice_le_grading hT hA j.val b
  choose L hL hLbound using hslice
  let bound (j : Fin (a + 1)) : ℝ := C * K * L j
  have hbound (j : Fin (a + 1)) : 0 ≤ bound j :=
    mul_nonneg (mul_nonneg hC hK.le) (hL j)
  have hpmono : Monotone A.grading :=
    gradedSeminorm_monotone (fun n => A.level n) A.bond
  refine ⟨∑ j, bound j, Finset.sum_nonneg (fun j _ => hbound j), ?_⟩
  intro u p hp
  let g : ℝ → ℝ := fun r => iteratedDeriv b (fun θ => A.decode u (r, θ)) p.2
  have hg : ContDiffOn ℝ ∞ g (Ioo D.a D.b) :=
    weighted_angular_slice_contDiffOn (hA.2.2.2.1 u).1 b p.2
  have hr : p.1 ∈ Ioo D.a D.b := hp.1
  have hM : 0 ≤ T.M p.1 := zero_le_one.trans (hpos _ hr).2.2.2
  have hH : 0 ≤ T.H p.1 ^ γ := (Real.rpow_pos_of_pos (hpos _ hr).2.1 γ).le
  change |iteratedDeriv a g p.1| ≤ _
  rw [hformula g hg p.1 hr]
  calc
    _ ≤ ∑ j : Fin (a + 1), |c j p.1 * materialDerivativeIterate T j.val g p.1| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (a + 1),
        bound j * T.H p.1 ^ γ * T.M p.1 * A.grading (a + b + 2) u := by
      apply Finset.sum_le_sum
      intro j _
      have hcoef : |c j p.1| ≤ C * (K * T.M p.1) :=
        (hc j p.1 hr).trans (mul_le_mul_of_nonneg_left (hKbound p.1 hr) hC)
      have hslice' : |materialDerivativeIterate T j.val g p.1| ≤
          L j * T.H p.1 ^ γ * A.grading (a + b + 2) u := by
        apply (hLbound j u p.2 p.1 hr).trans
        exact mul_le_mul_of_nonneg_left (hpmono (by omega) u) (mul_nonneg (hL j) hH)
      rw [abs_mul]
      calc
        _ ≤ (C * (K * T.M p.1)) * (L j * T.H p.1 ^ γ * A.grading (a + b + 2) u) :=
          mul_le_mul hcoef hslice' (abs_nonneg _) (mul_nonneg hC (mul_nonneg hK.le hM))
        _ = _ := by dsimp [bound]; ring
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]

end ContinuousFlexibility.Statements
