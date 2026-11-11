import ContinuousFlexibility.Analysis.ReturnResidualDriftSpeedMixed
import ContinuousFlexibility.Analysis.N01CoefficientMixedBounds

/-!
# Mixed weighted jets of the actual frozen coefficient error

The exact coefficient formula cancels every denominator involving the
radial coefficient. Only the already quantified characteristic
discriminant square root remains. Polynomial composition and product
estimates then preserve the independent residual's precise height
factor through the actual frozen coefficient reconstruction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

theorem returnCoefficientError_division_cancel
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a : ℝ} (ha : a ≠ 0) (b v : ℝ) (D V : E →ₗ[ℝ] ℝ) (e ρ : E) :
    returnCoefficientError a (b / a) (v / a) D V e ρ =
      (-a * D ρ, -(2 * b + a * D e) * D ρ + (2 * v + a * V e) * V ρ) := by
  rw [returnCoefficientError_apply]
  apply Prod.ext
  · rfl
  · dsimp only
    field_simp [ha]
    <;> ring

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

theorem N01Properties.returnCorrectionLocalCoefficientError_mixed_weighted_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (R : ReturnEquationData S) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (j : ℕ → ℕ) (x δ : ℕ → ℝ)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
    (χ : ℕ → ℝ → ℝ) {lam P₀ : ℝ} (hlam : 0 < lam) (hP₀ : 0 ≤ P₀)
    (hlower : ∀ m : ℕ, ∀ p : PolarPoint,
      p.1 ∈ Ioo (x m - δ m) (x m + δ m) →
      lam * radialE (D.cellIndex (j m)) ^ (-P₀) ≤
        (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (hV : ∀ ρ : CircleSpace S, ∀ m, ContDiff ℝ ∞
      (fun p => returnCorrectionVelocityLinear D S C χ z m p ρ))
    (hVbound : ∀ ρ : CircleSpace S, ∀ k : ℕ, ∃ A P : ℝ,
      0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      ‖iteratedFDeriv ℝ k (fun q => returnCorrectionVelocityLinear D S C χ z m q ρ) p‖ ≤
        A * T.H (T.sample m) ^ (3 / 4 : ℝ) * radialE (D.cellIndex (j m)) ^ P)
    (ρ : CircleSpace S) (n : ℕ) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      p.1 ∈ Ioo (x m - δ m) (x m + δ m) →
      ‖iteratedFDeriv ℝ n
        (fun q => returnCorrectionLocalCoefficientError D S C R χ z m q ρ) p‖ ≤
        A * T.H (T.sample m) ^ (3 / 4 : ℝ) * radialE (D.cellIndex (j m)) ^ P := by
  let W (m : ℕ) : ℝ := radialE (D.cellIndex (j m))
  let H (m : ℕ) : ℝ := T.H (T.sample m) ^ (3 / 4 : ℝ)
  let U (m : ℕ) : Set PolarPoint := Ioo (x m - δ m) (x m + δ m) ×ˢ univ
  let a : PolarPoint → ℝ := (originalCoefficients D S C z).a
  let b : PolarPoint → ℝ := (originalCoefficients D S C z).b
  let c : PolarPoint → ℝ := (originalCoefficients D S C z).c
  let Δ (p : PolarPoint) : ℝ := b p * b p - a p * c p
  let d (u : CircleSpace S) (m : ℕ) (p : PolarPoint) : ℝ :=
    returnCorrectionDriftLinear D S C χ z m p u
  let v (u : CircleSpace S) (m : ℕ) (p : PolarPoint) : ℝ :=
    returnCorrectionSpeedLinear D S C χ z m p u
  let e : CircleSpace S := R.residual z
  let Lneg : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hH (m : ℕ) : 0 < H m :=
    Real.rpow_pos_of_pos ((material_circle_sample_weights_pos hT hN.1.1).2 m) _
  have hU (m : ℕ) : IsOpen (U m) := isOpen_Ioo.prod isOpen_univ
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hcomponent (m : ℕ) (p : PolarPoint) (hp : p ∈ U m) :
      p.1 ∈ Ioo (C.left m) (C.right m) :=
    ⟨(hinside m).1.trans hp.1.1, hp.1.2.trans (hinside m).2⟩
  have hcore (m : ℕ) (p : PolarPoint) (hp : p ∈ U m) : p ∈ annularOpen D :=
    ⟨⟨(hC.1 m).1.trans (hcomponent m p hp).1,
      (hcomponent m p hp).2.trans (hC.1 m).2.2⟩, mem_univ _⟩
  have hsel (i : Fin 3) (m : ℕ) : ContDiffOn ℝ ∞
      (if i = 0 then a else if i = 1 then b else c) (U m) :=
    (hN.original_coefficient_contDiffOn hS hT hz hsector i).mono (hcore m)
  have ha (m : ℕ) : ContDiffOn ℝ ∞ a (U m) := by simpa using hsel 0 m
  have hb (m : ℕ) : ContDiffOn ℝ ∞ b (U m) := by simpa using hsel 1 m
  have hc (m : ℕ) : ContDiffOn ℝ ∞ c (U m) := by simpa using hsel 2 m
  have hsb (i : Fin 3) (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (if i = 0 then a else if i = 1 then b else c) p‖ ≤
        A * W m ^ P := by
    obtain ⟨A, hA, hbound⟩ := hN.original_coefficient_fderiv_jets hS hT hz hsector i k
    exact ⟨A, 0, hA, le_rfl, fun m p hp => by
      simpa only [Real.rpow_zero, mul_one] using hbound (j m) p (hcell m (hcomponent m p hp))⟩
  have hab (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k a p‖ ≤ A * W m ^ P := by simpa using hsb 0 k
  have hbb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k b p‖ ≤ A * W m ^ P := by simpa using hsb 1 k
  have hcb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k c p‖ ≤ A * W m ^ P := by simpa using hsb 2 k
  have hΔ (m : ℕ) : ContDiffOn ℝ ∞ Δ (U m) := ((hb m).mul (hb m)).sub ((ha m).mul (hc m))
  have hΔb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k Δ p‖ ≤ A * W m ^ P := by
    have hbb' := norm_iteratedFDeriv_mul_polynomial_bound W hW U hU
      (fun _ => b) (fun _ => b) hb hb k (fun l _ => hbb l) (fun l _ => hbb l)
    have hac := norm_iteratedFDeriv_mul_polynomial_bound W hW U hU
      (fun _ => a) (fun _ => c) ha hc k (fun l _ => hab l) (fun l _ => hcb l)
    have hneg := norm_iteratedFDeriv_clm_left_polynomial_bound W U hU
      (fun _ p => a p * c p) (fun m => (ha m).mul (hc m)) Lneg k hac
    have h := norm_iteratedFDeriv_add_polynomial_bound W hW U hU
      (fun _ p => b p * b p) (fun _ p => Lneg (a p * c p))
      (fun m => (hb m).mul (hb m))
      (fun m => Lneg.contDiff.contDiffOn.comp ((ha m).mul (hc m))
        (fun _ _ => mem_univ _)) k hbb' hneg
    simpa only [Lneg, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
      ← sub_eq_add_neg] using h
  have hΔlower (m : ℕ) (p : PolarPoint) (hp : p ∈ U m) :
      lam * W m ^ (-P₀) ≤ Δ p := by
    simpa only [Δ, a, b, c, pow_two] using hlower m p hp.1
  have hΔpos (m : ℕ) (p : PolarPoint) (hp : p ∈ U m) : 0 < Δ p :=
    (mul_pos hlam (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hW m)) _)).trans_le
      (hΔlower m p hp)
  have hroot (m : ℕ) : ContDiffOn ℝ ∞ (fun p => Real.sqrt (Δ p)) (U m) :=
    (hΔ m).sqrt (fun p hp => (hΔpos m p hp).ne')
  have hrootb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (fun q => Real.sqrt (Δ q)) p‖ ≤ A * W m ^ P :=
    norm_iteratedFDeriv_sqrt_polynomial_bound W hW U hU (fun _ => Δ)
      hΔ hlam hP₀ hΔlower hΔb k
  have hds (u : CircleSpace S) (m : ℕ) :
      ContDiff ℝ ∞ (d u m) ∧ ContDiff ℝ ∞ (v u m) :=
    returnCorrectionDriftSpeedLinear_contDiff_of_velocity D S C χ z u (hV u) m
  have hdb (u : CircleSpace S) (k : ℕ) :
      ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
        ‖iteratedFDeriv ℝ k (d u m) p‖ ≤ A * H m * W m ^ P :=
    (returnCorrectionDriftSpeedLinear_weighted_bound_of_velocity
      D S C χ z u W H hW hH (hV u) (hVbound u) k).1
  have hvb (u : CircleSpace S) (k : ℕ) :
      ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
        ‖iteratedFDeriv ℝ k (v u m) p‖ ≤ A * H m * W m ^ P :=
    (returnCorrectionDriftSpeedLinear_weighted_bound_of_velocity
      D S C χ z u W H hW hH (hV u) (hVbound u) k).2
  obtain ⟨M, hM, hMb⟩ :=
    materialSample_H_E0_envelope hT hN.1.1 (γ := (3 / 4 : ℝ)) (by norm_num) 0
  have hHM (m : ℕ) : H m ≤ M := by
    simpa only [Real.rpow_zero, mul_one] using hMb m
  have hde (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (d e m) p‖ ≤ A * W m ^ P := by
    obtain ⟨A, P, hA, hP, hbound⟩ := hdb e k
    refine ⟨A * M, P, mul_nonneg hA hM.le, hP, fun m p _ => ?_⟩
    exact (hbound m p).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hHM m) hA)
      (Real.rpow_nonneg (zero_le_one.trans (hW m)) _))
  have hve (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (v e m) p‖ ≤ A * W m ^ P := by
    obtain ⟨A, P, hA, hP, hbound⟩ := hvb e k
    refine ⟨A * M, P, mul_nonneg hA hM.le, hP, fun m p _ => ?_⟩
    exact (hbound m p).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hHM m) hA)
      (Real.rpow_nonneg (zero_le_one.trans (hW m)) _))
  let F (m : ℕ) (p : PolarPoint) : ℝ := -(b p + b p + a p * d e m p)
  let G (m : ℕ) (p : PolarPoint) : ℝ := Real.sqrt (Δ p) + Real.sqrt (Δ p) + a p * v e m p
  have hF (m : ℕ) : ContDiffOn ℝ ∞ (F m) (U m) :=
    (((hb m).add (hb m)).add ((ha m).mul (hds e m).1.contDiffOn)).neg
  have hG (m : ℕ) : ContDiffOn ℝ ∞ (G m) (U m) :=
    ((hroot m).add (hroot m)).add ((ha m).mul (hds e m).2.contDiffOn)
  have hFb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (F m) p‖ ≤ A * W m ^ P := by
    have htwob := norm_iteratedFDeriv_add_polynomial_bound W hW U hU
      (fun _ => b) (fun _ => b) hb hb k (hbb k) (hbb k)
    have had := norm_iteratedFDeriv_mul_polynomial_bound W hW U hU
      (fun _ => a) (d e) ha (fun m => (hds e m).1.contDiffOn) k
      (fun l _ => hab l) (fun l _ => hde l)
    have hsum := norm_iteratedFDeriv_add_polynomial_bound W hW U hU
      (fun _ p => b p + b p) (fun m p => a p * d e m p)
      (fun m => (hb m).add (hb m))
      (fun m => (ha m).mul (hds e m).1.contDiffOn) k htwob had
    have hneg := norm_iteratedFDeriv_clm_left_polynomial_bound W U hU
      (fun m p => b p + b p + a p * d e m p)
      (fun m => ((hb m).add (hb m)).add ((ha m).mul (hds e m).1.contDiffOn))
      Lneg k hsum
    simpa only [Lneg, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply] using hneg
  have hGb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (G m) p‖ ≤ A * W m ^ P := by
    have htwov := norm_iteratedFDeriv_add_polynomial_bound W hW U hU
      (fun _ p => Real.sqrt (Δ p)) (fun _ p => Real.sqrt (Δ p))
      hroot hroot k (hrootb k) (hrootb k)
    have hav := norm_iteratedFDeriv_mul_polynomial_bound W hW U hU
      (fun _ => a) (v e) ha (fun m => (hds e m).2.contDiffOn) k
      (fun l _ => hab l) (fun l _ => hve l)
    exact norm_iteratedFDeriv_add_polynomial_bound W hW U hU
      (fun _ p => Real.sqrt (Δ p) + Real.sqrt (Δ p)) (fun m p => a p * v e m p)
      (fun m => (hroot m).add (hroot m))
      (fun m => (ha m).mul (hds e m).2.contDiffOn) k htwov hav
  let f (m : ℕ) (p : PolarPoint) : ℝ := -a p * d ρ m p
  let g (m : ℕ) (p : PolarPoint) : ℝ := F m p * d ρ m p + G m p * v ρ m p
  have hf (m : ℕ) : ContDiffOn ℝ ∞ (f m) (U m) :=
    (ha m).neg.mul (hds ρ m).1.contDiffOn
  have hg (m : ℕ) : ContDiffOn ℝ ∞ (g m) (U m) :=
    ((hF m).mul (hds ρ m).1.contDiffOn).add ((hG m).mul (hds ρ m).2.contDiffOn)
  have hρd (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (d ρ m) p‖ ≤ A * H m * W m ^ P := by
    obtain ⟨A, P, hA, hP, hbound⟩ := hdb ρ k
    exact ⟨A, P, hA, hP, fun m p _ => hbound m p⟩
  have hρv (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (v ρ m) p‖ ≤ A * H m * W m ^ P := by
    obtain ⟨A, P, hA, hP, hbound⟩ := hvb ρ k
    exact ⟨A, P, hA, hP, fun m p _ => hbound m p⟩
  have hnegative (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (fun q => -a q) p‖ ≤ A * W m ^ P := by
    simpa only [Lneg, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply] using
      norm_iteratedFDeriv_clm_left_polynomial_bound W U hU (fun _ => a) ha Lneg k (hab k)
  obtain ⟨A, P, hA, hP, hfb⟩ := norm_iteratedFDeriv_mul_weighted_polynomial_bound
    W H hW hH U hU (fun _ p => -a p) (d ρ)
    (fun m => (ha m).neg) (fun m => (hds ρ m).1.contDiffOn) n
    (fun k _ => hnegative k) (fun k _ => hρd k)
  have hFd := norm_iteratedFDeriv_mul_weighted_polynomial_bound W H hW hH U hU F (d ρ)
    hF (fun m => (hds ρ m).1.contDiffOn) n (fun k _ => hFb k) (fun k _ => hρd k)
  have hGv := norm_iteratedFDeriv_mul_weighted_polynomial_bound W H hW hH U hU G (v ρ)
    hG (fun m => (hds ρ m).2.contDiffOn) n (fun k _ => hGb k) (fun k _ => hρv k)
  obtain ⟨B, Q, hB, hQ, hgb⟩ := norm_iteratedFDeriv_add_weighted_polynomial_bound
    W H hW hH U hU (fun m p => F m p * d ρ m p) (fun m p => G m p * v ρ m p)
    (fun m => (hF m).mul (hds ρ m).1.contDiffOn)
    (fun m => (hG m).mul (hds ρ m).2.contDiffOn) n hFd hGv
  refine ⟨A + B, P + Q, add_nonneg hA hB, add_nonneg hP hQ, fun m p hp => ?_⟩
  have hpU : p ∈ U m := ⟨hp, mem_univ _⟩
  have heq : (fun q => returnCorrectionLocalCoefficientError D S C R χ z m q ρ) =ᶠ[𝓝 p]
      (fun q => (f m q, g m q)) := by
    filter_upwards [(hU m).mem_nhds hpU] with q hq
    have hapos : a q ≠ 0 := (hN.originalRadialCoefficient_pos hz hsector (hcore m q hq)).ne'
    unfold returnCorrectionLocalCoefficientError
    rw [returnCoefficientError_division_cancel hapos]
    apply Prod.ext
    · rfl
    · dsimp only [f, g, F, G, Δ, a, b, c, d, v, e]
      simp only [pow_two]
      ring
  rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds,
    iteratedFDeriv_prodMk ((hf m).contDiffAt ((hU m).mem_nhds hpU))
      ((hg m).contDiffAt ((hU m).mem_nhds hpU)),
    ContinuousMultilinearMap.opNorm_prod]
  have ha' : A * H m * W m ^ P ≤ A * H m * W m ^ (P + Q) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hW m) (le_add_of_nonneg_right hQ))
      (mul_nonneg hA (hH m).le)
  have hb' : B * H m * W m ^ Q ≤ B * H m * W m ^ (P + Q) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hW m) (le_add_of_nonneg_left hP))
      (mul_nonneg hB (hH m).le)
  have hAnonneg : 0 ≤ A * H m * W m ^ (P + Q) :=
    mul_nonneg (mul_nonneg hA (hH m).le)
      (Real.rpow_nonneg (zero_le_one.trans (hW m)) _)
  have hBnonneg : 0 ≤ B * H m * W m ^ (P + Q) :=
    mul_nonneg (mul_nonneg hB (hH m).le)
      (Real.rpow_nonneg (zero_le_one.trans (hW m)) _)
  apply max_le
  · exact (hfb m p hpU).trans (ha'.trans
      ((le_add_of_nonneg_right hBnonneg).trans_eq (by ring)))
  · exact (hgb m p hpU).trans (hb'.trans
      ((le_add_of_nonneg_left hAnonneg).trans_eq (by ring)))

end ContinuousFlexibility.Statements
