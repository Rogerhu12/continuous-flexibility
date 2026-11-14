module

public import ContinuousFlexibility.Analysis.PrincipalCoefficientPullback
public import ContinuousFlexibility.Analysis.BoundaryMixedJets
public import ContinuousFlexibility.Analysis.FiniteRadialJets
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Actual principal-density jets from matched coordinates and heights

The physical expression for each principal coefficient is built from the
height, four actual first derivatives of the chart, and the common
physical coefficient fields. Matching coordinate boundary jets through
order n+1 and height jets through order n therefore matches all radial
principal-density jets through order n. The Jacobian is required to be
nonzero at the point where division is differentiated.

No coefficient matching or boundary vanishing is supplied as an input:
it is derived from the actual coordinate and height jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private structure ScalarJetMatch (n : ℕ) (x : ℝ) (f g : ℝ → ℝ) : Prop where
  left_smooth : ContDiffAt ℝ ∞ f x
  right_smooth : ContDiffAt ℝ ∞ g x
  jets : ∀ k ≤ n, iteratedDeriv k f x = iteratedDeriv k g x

private theorem scalarJetMatch_refl {n : ℕ} {x : ℝ} {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ ∞ f x) : ScalarJetMatch n x f f :=
  ⟨hf, hf, fun _ _ => rfl⟩

private theorem scalarJetMatch_add {n : ℕ} {x : ℝ} {f g u v : ℝ → ℝ}
    (h : ScalarJetMatch n x f g) (k : ScalarJetMatch n x u v) :
    ScalarJetMatch n x (fun r => f r + u r) (fun r => g r + v r) := by
  refine ⟨h.left_smooth.add k.left_smooth, h.right_smooth.add k.right_smooth, ?_⟩
  intro j hj
  rw [iteratedDeriv_fun_add (h.left_smooth.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)) (k.left_smooth.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)),
    iteratedDeriv_fun_add (h.right_smooth.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)) (k.right_smooth.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)),
    h.jets j hj, k.jets j hj]

private theorem scalarJetMatch_sub {n : ℕ} {x : ℝ} {f g u v : ℝ → ℝ}
    (h : ScalarJetMatch n x f g) (k : ScalarJetMatch n x u v) :
    ScalarJetMatch n x (fun r => f r - u r) (fun r => g r - v r) := by
  refine ⟨h.left_smooth.sub k.left_smooth, h.right_smooth.sub k.right_smooth, ?_⟩
  intro j hj
  rw [iteratedDeriv_fun_sub (h.left_smooth.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)) (k.left_smooth.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)),
    iteratedDeriv_fun_sub (h.right_smooth.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)) (k.right_smooth.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)),
    h.jets j hj, k.jets j hj]

private theorem scalarJetMatch_mul {n : ℕ} {x : ℝ} {f g u v : ℝ → ℝ}
    (h : ScalarJetMatch n x f g) (k : ScalarJetMatch n x u v) :
    ScalarJetMatch n x (fun r => f r * u r) (fun r => g r * v r) := by
  refine ⟨h.left_smooth.mul k.left_smooth, h.right_smooth.mul k.right_smooth, ?_⟩
  intro j hj
  rw [iteratedDeriv_fun_mul (h.left_smooth.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)) (k.left_smooth.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)),
    iteratedDeriv_fun_mul (h.right_smooth.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)) (k.right_smooth.of_le (show (j : ℕ∞ω) ≤ ∞ by simp))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h.jets i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj),
    k.jets (j - i) ((Nat.sub_le j i).trans hj)]

private theorem scalarJetMatch_comp {n : ℕ} {x : ℝ} {f g H : ℝ → ℝ}
    (h : ScalarJetMatch n x f g) (hH : ContDiffAt ℝ ∞ H (f x)) :
    ScalarJetMatch n x (fun r => H (f r)) (fun r => H (g r)) := by
  have h0 : f x = g x := by
    simpa only [iteratedDeriv_zero] using h.jets 0 (Nat.zero_le n)
  have hHg : ContDiffAt ℝ ∞ H (g x) := h0 ▸ hH
  refine ⟨ContDiffAt.fun_comp (f := f) (g := H) x hH h.left_smooth,
    ContDiffAt.fun_comp (f := g) (g := H) x hHg h.right_smooth, ?_⟩
  intro j hj
  simpa only [Function.comp_def] using
    iteratedDeriv_vcomp_eq_of_finiteJet_eq h.left_smooth h.right_smooth hH h.jets hj

private theorem scalarJetMatch_pow {n : ℕ} {x : ℝ} {f g : ℝ → ℝ}
    (h : ScalarJetMatch n x f g) (k : ℕ) :
    ScalarJetMatch n x (fun r => f r ^ k) (fun r => g r ^ k) :=
  scalarJetMatch_comp h (H := fun r : ℝ => r ^ k) (contDiff_id.pow k).contDiffAt

private theorem scalarJetMatch_abs {n : ℕ} {x : ℝ} {f g : ℝ → ℝ}
    (h : ScalarJetMatch n x f g) (hf : f x ≠ 0) :
    ScalarJetMatch n x (fun r => |f r|) (fun r => |g r|) :=
  scalarJetMatch_comp h (H := fun r : ℝ => |r|) (contDiffAt_abs hf)

private theorem scalarJetMatch_div {n : ℕ} {x : ℝ} {f g u v : ℝ → ℝ}
    (h : ScalarJetMatch n x f g) (k : ScalarJetMatch n x u v) (hu : u x ≠ 0) :
    ScalarJetMatch n x (fun r => f r / u r) (fun r => g r / v r) := by
  have hi := scalarJetMatch_comp k (H := fun r : ℝ => r⁻¹) (contDiffAt_inv ℝ hu)
  simpa only [div_eq_mul_inv] using scalarJetMatch_mul h hi

private def coordinateDirectionDerivative (F : PolarPoint → PolarPoint)
    (ℓ : PolarPoint →L[ℝ] ℝ) (j : Fin 2) (p : PolarPoint) : ℝ :=
  ℓ (fderiv ℝ F p (cylinderBasisVector j))

private theorem contDiffOn_coordinateDirectionDerivative
    {U : Set PolarPoint} (hU : IsOpen U) {F : PolarPoint → PolarPoint}
    (hF : ContDiffOn ℝ ∞ F U) (ℓ : PolarPoint →L[ℝ] ℝ) (j : Fin 2) :
    ContDiffOn ℝ ∞ (coordinateDirectionDerivative F ℓ j) U :=
  ℓ.contDiff.fun_comp_contDiffOn
    ((hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const)

private theorem coordinateDirectionDerivative_eq
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (ℓ : PolarPoint →L[ℝ] ℝ) (j : Fin 2) :
    coordinateDirectionDerivative F ℓ j p =
      fderiv ℝ (fun q => ℓ (F q)) p (cylinderBasisVector j) := by
  have hs : HasFDerivAt (fun q => ℓ (F q)) (ℓ.comp (fderiv ℝ F p)) p :=
    ℓ.hasFDerivAt.comp p hF.hasFDerivAt
  rw [hs.fderiv]
  simp only [coordinateDirectionDerivative, ContinuousLinearMap.comp_apply]

private theorem radialBoundaryJet_coordinateDirectionDerivative
    {U : Set PolarPoint} (hU : IsOpen U) {F : PolarPoint → PolarPoint}
    (hF : ContDiffOn ℝ ∞ F U) (c : ℝ)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) (ℓ : PolarPoint →L[ℝ] ℝ)
    (j : Fin 2) (k : ℕ) (θ : ℝ) :
    radialBoundaryJet (coordinateDirectionDerivative F ℓ j) c k θ =
      mixedDerivative (k + if j = 0 then 1 else 0) (if j = 0 then 0 else 1)
        (fun q => ℓ (F q)) (c, θ) := by
  have hφ : ContDiffOn ℝ ∞ (fun q => ℓ (F q)) U :=
    ℓ.contDiff.fun_comp_contDiffOn hF
  have hline : Continuous (fun r : ℝ => (r, θ)) := continuous_id.prodMk continuous_const
  have he : (fun r => coordinateDirectionDerivative F ℓ j (r, θ)) =ᶠ[𝓝 c]
      (fun r => fderiv ℝ (fun q => ℓ (F q)) (r, θ) (cylinderBasisVector j)) := by
    filter_upwards [(hline.tendsto c).eventually (hU.mem_nhds (hc θ))] with r hr
    exact coordinateDirectionDerivative_eq
      ((hF.contDiffAt (hU.mem_nhds hr)).differentiableAt (by simp)) ℓ j
  have hd := (he.iteratedDeriv k).eq_of_nhds
  by_cases hj : j = 0
  · have ht : radialBoundaryJet (coordinateDirectionDerivative F ℓ j) c k θ =
        mixedDerivative k 0 (radialPartial (fun q => ℓ (F q))) (c, θ) := by
      simpa only [radialBoundaryJet, mixedDerivative, iteratedDeriv_zero,
        radialPartial, cylinderBasisVector, ite_eq_left hj] using hd
    simpa only [ite_eq_left hj] using
      ht.trans (mixedDerivative_radialPartial hU hφ k 0 (hc θ))
  · have ht : radialBoundaryJet (coordinateDirectionDerivative F ℓ j) c k θ =
        mixedDerivative k 0 (angularPartial (fun q => ℓ (F q))) (c, θ) := by
      simpa only [radialBoundaryJet, mixedDerivative, iteratedDeriv_zero,
        angularPartial, cylinderBasisVector, ite_eq_right hj] using hd
    simpa only [ite_eq_right hj, Nat.add_zero, Nat.zero_add] using
      ht.trans (mixedDerivative_angularPartial hU hφ k 0 (hc θ))

private theorem scalarJetMatch_coordinateDirectionDerivative
    {U : Set PolarPoint} (hU : IsOpen U) {F G : PolarPoint → PolarPoint}
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U) (c : ℝ)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) (ℓ : PolarPoint →L[ℝ] ℝ)
    {n : ℕ}
    (hjet : ∀ k ≤ n + 1, ∀ θ : ℝ,
      radialBoundaryJet (fun q => ℓ (F q)) c k θ =
        radialBoundaryJet (fun q => ℓ (G q)) c k θ)
    (j : Fin 2) (θ : ℝ) :
    ScalarJetMatch n c (fun r => coordinateDirectionDerivative F ℓ j (r, θ))
      (fun r => coordinateDirectionDerivative G ℓ j (r, θ)) := by
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hLF := (contDiffOn_coordinateDirectionDerivative hU hF ℓ j).contDiffAt
    (hU.mem_nhds (hc θ))
  have hLG := (contDiffOn_coordinateDirectionDerivative hU hG ℓ j).contDiffAt
    (hU.mem_nhds (hc θ))
  refine ⟨ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ))
      (g := coordinateDirectionDerivative F ℓ j) c hLF hline,
    ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ))
      (g := coordinateDirectionDerivative G ℓ j) c hLG hline, ?_⟩
  intro k hk
  change radialBoundaryJet (coordinateDirectionDerivative F ℓ j) c k θ =
    radialBoundaryJet (coordinateDirectionDerivative G ℓ j) c k θ
  rw [radialBoundaryJet_coordinateDirectionDerivative hU hF c hc,
    radialBoundaryJet_coordinateDirectionDerivative hU hG c hc]
  have hk' : k + (if j = 0 then 1 else 0) ≤ n + 1 := by
    by_cases hj : j = 0
    · simpa only [ite_eq_left hj] using Nat.add_le_add_right hk 1
    · simpa only [ite_eq_right hj, Nat.add_zero] using Nat.le_succ_of_le hk
  exact mixedDerivative_boundary_eq_of_radialBoundaryJet_eq hU hU
    (ℓ.contDiff.fun_comp_contDiffOn hF) (ℓ.contDiff.fun_comp_contDiffOn hG)
    c hc hc hjet hk' _ θ

/-- Smooth charts, heights and physical coefficients give actual smooth
principal-density fields wherever the chart Jacobian is nonzero. -/
theorem contDiffAt_coordinatePrincipalDensity
    {A : SymmetricCoefficients} {F : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {x : PolarPoint}
    (hAa : ContDiffAt ℝ ∞ A.a x) (hAb : ContDiffAt ℝ ∞ A.b x)
    (hAc : ContDiffAt ℝ ∞ A.c x)
    (hF : ContDiffAt ℝ ∞ F x) (hh : ContDiffAt ℝ ∞ h x)
    (hJ : planeJacobian F x ≠ 0) :
    ContDiffAt ℝ ∞ (coordinatePrincipalDensity A F h).a x ∧
      ContDiffAt ℝ ∞ (coordinatePrincipalDensity A F h).b x ∧
      ContDiffAt ℝ ∞ (coordinatePrincipalDensity A F h).c x := by
  have hr : ContDiffAt ℝ ∞ (fun p => fderiv ℝ F p (1, 0)) x :=
    (hF.fderiv_right (by simp)).clm_apply contDiffAt_const
  have ht : ContDiffAt ℝ ∞ (fun p => fderiv ℝ F p (0, 1)) x :=
    (hF.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hdet : ContDiffAt ℝ ∞ (planeJacobian F) x :=
    (hr.fst.mul ht.snd).sub (hr.snd.mul ht.fst)
  have hScale : ContDiffAt ℝ ∞
      (fun p => h p ^ 2 / |planeJacobian F p|) x :=
    (hh.pow 2).fun_div (hdet.abs hJ) (abs_ne_zero.mpr hJ)
  have htwo : ContDiffAt ℝ ∞ (fun _ : PolarPoint => (2 : ℝ)) x :=
    contDiffAt_const
  dsimp only [coordinatePrincipalDensity, coefficientQuadratic]
  refine ⟨hScale.mul ?_, hScale.mul ?_, hScale.mul ?_⟩
  · exact ((hAa.mul (hr.fst.pow 2)).add
      (((htwo.mul hAb).mul hr.fst).mul ht.fst)).add (hAc.mul (ht.fst.pow 2))
  · exact (((hAa.mul hr.fst).mul hr.snd).add
      (hAb.mul ((hr.fst.mul ht.snd).add (ht.fst.mul hr.snd)))).add
        ((hAc.mul ht.fst).mul ht.snd)
  · exact ((hAa.mul (hr.snd.pow 2)).add
      (((htwo.mul hAb).mul hr.snd).mul ht.snd)).add (hAc.mul (ht.snd.pow 2))

/-- Matching the actual chart jets through order n+1 and height jets
through order n matches the principal-density jets through order n.
The physical operator is common to the two coordinate descriptions. -/
theorem radialBoundaryJets_coordinatePrincipalDensity_eq
    {U : Set PolarPoint} (hU : IsOpen U) {A : SymmetricCoefficients}
    {F G : PolarPoint → PolarPoint} {h g : PolarPoint → ℝ}
    (hAa : ContDiffOn ℝ ∞ A.a U) (hAb : ContDiffOn ℝ ∞ A.b U)
    (hAc : ContDiffOn ℝ ∞ A.c U)
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (hh : ContDiffOn ℝ ∞ h U) (hg : ContDiffOn ℝ ∞ g U)
    (c : ℝ) (hc : ∀ θ : ℝ, (c, θ) ∈ U) {n : ℕ}
    (hFst : ∀ k ≤ n + 1, ∀ θ : ℝ,
      radialBoundaryJet (fun q => (F q).1) c k θ =
        radialBoundaryJet (fun q => (G q).1) c k θ)
    (hSnd : ∀ k ≤ n + 1, ∀ θ : ℝ,
      radialBoundaryJet (fun q => (F q).2) c k θ =
        radialBoundaryJet (fun q => (G q).2) c k θ)
    (hHeight : ∀ k ≤ n, ∀ θ : ℝ,
      radialBoundaryJet h c k θ = radialBoundaryJet g c k θ)
    (θ : ℝ) (hJ : planeJacobian F (c, θ) ≠ 0) :
    ∀ k ≤ n,
      radialBoundaryJet (coordinatePrincipalDensity A F h).a c k θ =
          radialBoundaryJet (coordinatePrincipalDensity A G g).a c k θ ∧
        radialBoundaryJet (coordinatePrincipalDensity A F h).b c k θ =
          radialBoundaryJet (coordinatePrincipalDensity A G g).b c k θ ∧
        radialBoundaryJet (coordinatePrincipalDensity A F h).c c k θ =
          radialBoundaryJet (coordinatePrincipalDensity A G g).c c k θ := by
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hs {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
      ContDiffAt ℝ ∞ (fun r => f (r, θ)) c :=
    ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ)) (g := f) c
      (hf.contDiffAt (hU.mem_nhds (hc θ))) hline
  have hH : ScalarJetMatch n c (fun r => h (r, θ)) (fun r => g (r, θ)) :=
    ⟨hs hh, hs hg, fun k hk => hHeight k hk θ⟩
  have h11 : ScalarJetMatch n c
      (fun r => (fderiv ℝ F (r, θ) (1, 0)).1)
      (fun r => (fderiv ℝ G (r, θ) (1, 0)).1) := by
    simpa only [coordinateDirectionDerivative, cylinderBasisVector, ite_eq_left rfl, ite_true,
      ContinuousLinearMap.coe_fst'] using
      scalarJetMatch_coordinateDirectionDerivative hU hF hG c hc
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (by
          simpa only [ContinuousLinearMap.coe_fst'] using hFst) 0 θ
  have h12 : ScalarJetMatch n c
      (fun r => (fderiv ℝ F (r, θ) (0, 1)).1)
      (fun r => (fderiv ℝ G (r, θ) (0, 1)).1) := by
    simpa only [coordinateDirectionDerivative, cylinderBasisVector,
      ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), ContinuousLinearMap.coe_fst'] using
      scalarJetMatch_coordinateDirectionDerivative hU hF hG c hc
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (by
          simpa only [ContinuousLinearMap.coe_fst'] using hFst) 1 θ
  have h21 : ScalarJetMatch n c
      (fun r => (fderiv ℝ F (r, θ) (1, 0)).2)
      (fun r => (fderiv ℝ G (r, θ) (1, 0)).2) := by
    simpa only [coordinateDirectionDerivative, cylinderBasisVector, ite_eq_left rfl, ite_true,
      ContinuousLinearMap.coe_snd'] using
      scalarJetMatch_coordinateDirectionDerivative hU hF hG c hc
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (by
          simpa only [ContinuousLinearMap.coe_snd'] using hSnd) 0 θ
  have h22 : ScalarJetMatch n c
      (fun r => (fderiv ℝ F (r, θ) (0, 1)).2)
      (fun r => (fderiv ℝ G (r, θ) (0, 1)).2) := by
    simpa only [coordinateDirectionDerivative, cylinderBasisVector,
      ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), ContinuousLinearMap.coe_snd'] using
      scalarJetMatch_coordinateDirectionDerivative hU hF hG c hc
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (by
          simpa only [ContinuousLinearMap.coe_snd'] using hSnd) 1 θ
  have hDet : ScalarJetMatch n c (fun r => planeJacobian F (r, θ))
      (fun r => planeJacobian G (r, θ)) := by
    simpa only [planeJacobian] using
      scalarJetMatch_sub (scalarJetMatch_mul h11 h22) (scalarJetMatch_mul h21 h12)
  have hScale := scalarJetMatch_div (scalarJetMatch_pow hH 2)
    (scalarJetMatch_abs hDet hJ) (abs_ne_zero.mpr hJ)
  have ha : ScalarJetMatch n c (fun r => A.a (r, θ)) (fun r => A.a (r, θ)) :=
    scalarJetMatch_refl (hs hAa)
  have hb : ScalarJetMatch n c (fun r => A.b (r, θ)) (fun r => A.b (r, θ)) :=
    scalarJetMatch_refl (hs hAb)
  have hc' : ScalarJetMatch n c (fun r => A.c (r, θ)) (fun r => A.c (r, θ)) :=
    scalarJetMatch_refl (hs hAc)
  have htwo : ScalarJetMatch n c (fun _ => (2 : ℝ)) (fun _ => (2 : ℝ)) :=
    scalarJetMatch_refl contDiffAt_const
  have hqa := scalarJetMatch_add
    (scalarJetMatch_add (scalarJetMatch_mul ha (scalarJetMatch_pow h11 2))
      (scalarJetMatch_mul (scalarJetMatch_mul (scalarJetMatch_mul htwo hb) h11) h12))
    (scalarJetMatch_mul hc' (scalarJetMatch_pow h12 2))
  have hqb := scalarJetMatch_add
    (scalarJetMatch_add (scalarJetMatch_mul (scalarJetMatch_mul ha h11) h21)
      (scalarJetMatch_mul hb
        (scalarJetMatch_add (scalarJetMatch_mul h11 h22) (scalarJetMatch_mul h12 h21))))
    (scalarJetMatch_mul (scalarJetMatch_mul hc' h12) h22)
  have hqc := scalarJetMatch_add
    (scalarJetMatch_add (scalarJetMatch_mul ha (scalarJetMatch_pow h21 2))
      (scalarJetMatch_mul (scalarJetMatch_mul (scalarJetMatch_mul htwo hb) h21) h22))
    (scalarJetMatch_mul hc' (scalarJetMatch_pow h22 2))
  intro k hk
  refine ⟨?_, ?_, ?_⟩
  · simpa only [radialBoundaryJet, coordinatePrincipalDensity, coefficientQuadratic] using
      (scalarJetMatch_mul hScale hqa).jets k hk
  · simpa only [radialBoundaryJet, coordinatePrincipalDensity] using
      (scalarJetMatch_mul hScale hqb).jets k hk
  · simpa only [radialBoundaryJet, coordinatePrincipalDensity, coefficientQuadratic] using
      (scalarJetMatch_mul hScale hqc).jets k hk

end ContinuousFlexibility.Analysis
