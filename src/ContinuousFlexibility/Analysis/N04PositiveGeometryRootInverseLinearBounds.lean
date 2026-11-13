import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInverseLinear
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryMoving
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsFiniteProducts

/-!
# Word estimates for the triangular inverse differential

Three scalar coefficients determine the operator. Their finite product
and the fixed reconstruction map retain the full angular reserve.
Moving the two physical coefficients uses only positive inner jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem N04BoundaryWordBounds.postcompCLM_norm
    {U : Set E} {f : E × ℝ → F} {J : SmoothDirections (U ×ˢ univ) f}
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop} {M H t : ℝ} {shift : ℕ}
    (h : N04BoundaryWordBounds J K s d x θ P M H t shift) (A : F →L[ℝ] G) :
    N04BoundaryWordBounds (smoothDirections_postcompCLM J A)
      K s d x θ P (‖A‖ * M) H t shift := by
  intro n w hk ha v hv hp
  rw [smoothDirections_postcompCLM_D_apply]
  exact (A.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (h n w hk ha v hv hp) (norm_nonneg A)).trans_eq
      (by ring))

theorem N04BoundaryWordBounds.shift
    {U : Set E} {f : E × ℝ → F} {J : SmoothDirections (U ×ˢ univ) f}
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop} {M H t : ℝ} {c c' : ℕ}
    (h : N04BoundaryWordBounds J K s d x θ P M H t c)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t) (hc : c ≤ c') :
    N04BoundaryWordBounds J K s d x θ P M H t c' := by
  intro n w hk ha v hv hp
  exact (h n w hk ha v hv hp).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ ht (Nat.add_le_add_left (Nat.mul_le_mul_right _ hc) _))
    (mul_nonneg hM (parameterHeightWeight_nonneg hH _)))

private def rootColumnsLinear :
    (PolarPoint × PolarPoint) →L[ℝ] (PolarPoint →L[ℝ] PolarPoint) :=
  (ContinuousLinearMap.smulRightL ℝ PolarPoint PolarPoint
    (ContinuousLinearMap.fst ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.fst ℝ PolarPoint PolarPoint) +
  (ContinuousLinearMap.smulRightL ℝ PolarPoint PolarPoint
    (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.snd ℝ PolarPoint PolarPoint)

private theorem rootColumnsLinear_apply (z : PolarPoint × PolarPoint) (v : PolarPoint) :
    rootColumnsLinear z v = v.1 • z.1 + v.2 • z.2 := by
  simp only [rootColumnsLinear, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply]

theorem n04PositiveGeometry_rootInverseLinear_word_bound (N : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ, 1 ≤ degree ∧
    ∀ {U : Set E}, IsOpen U → ∀ {a e b : E × ℝ → ℝ},
    ∀ Ja : SmoothDirections (U ×ˢ univ) a,
    ∀ Je : SmoothDirections (U ×ˢ univ) e,
    ∀ Jb : SmoothDirections (U ×ˢ univ) b,
    ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
    ∀ Q : SmoothDirections (U ×ˢ univ)
      (fun y => n04PositiveGeometry_rootInverseLinear σ (a y) (e y) (b y)),
    ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
    ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ L → 1 ≤ t → ∀ shift : ℕ,
    N04BoundaryWordBounds Ja K s d x θ P M H t shift →
    N04BoundaryWordBounds Je K s d x θ P M H t shift →
    N04BoundaryWordBounds Jb K s d x θ P M H t shift →
    N04BoundaryWordBounds Q K s d x θ P (C * M ^ degree) H t shift := by
  obtain ⟨Cp, hCp, dp, hprod⟩ := n04PositiveGeometry_boundaryWord_finiteProduct (E := E) 3 N L hL
  let B : ℝ := max 1 ‖rootColumnsLinear‖
  have hB : 1 ≤ B := le_max_left _ _
  have hCp1 : 1 ≤ 1 + Cp := le_add_of_nonneg_right (zero_le_one.trans hCp)
  refine ⟨B * (1 + Cp), one_le_mul_of_one_le_of_one_le hB hCp1,
    1 + dp, by omega, ?_⟩
  intro U hU a e b Ja Je Jb σ hσ Q K s d hN x hx θ P M H t hM hH hHL ht shift ha he hb
  let f : Fin 3 → E × ℝ → ℝ := ![b, e, a]
  let J : ∀ i, SmoothDirections (U ×ˢ univ) (f i) := by
    intro i
    fin_cases i
    · exact Jb
    · exact Je
    · exact Ja
  let JP := smoothDirections_finiteProduct Ja.open_domain J
  have hp := hprod hU J JP K s d hN x hx θ P M H t hM hH hHL ht shift
    (fun i => by fin_cases i <;> assumption)
  let M' : ℝ := (1 + Cp) * M ^ (1 + dp)
  have hc := n04PositiveGeometry_power_product_cost (degree := dp) hCp hM
  have ha' := ha.enlarge hH (zero_le_one.trans ht) hc.2.1
  have hb' := hb.enlarge hH (zero_le_one.trans ht) hc.2.1
  have hp' := hp.enlarge hH (zero_le_one.trans ht) hc.2.2
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hrad := ha'.scale σ
  have hcross := hp'.scale (-1 : ℝ)
  simp only [hσabs, abs_neg, abs_one, one_mul] at hrad hcross
  have hzero := ha'.scale (0 : ℝ)
  have hz : N04BoundaryWordBounds
      (smoothDirections_postcompCLM Ja (0 • ContinuousLinearMap.id ℝ ℝ))
      K s d x θ P M' H t shift := by
    apply hzero.enlarge hH (zero_le_one.trans ht)
    simpa only [abs_zero, zero_mul] using zero_le_one.trans hc.1
  let JT := smoothDirectionsProd
    (smoothDirectionsProd
      (smoothDirections_postcompCLM Ja (σ • ContinuousLinearMap.id ℝ ℝ))
      (smoothDirections_postcompCLM JP ((-1 : ℝ) • ContinuousLinearMap.id ℝ ℝ)))
    (smoothDirectionsProd
      (smoothDirections_postcompCLM Ja (0 • ContinuousLinearMap.id ℝ ℝ)) Jb)
  have htuple := (hrad.prod hcross).prod (hz.prod hb')
  have hmap := htuple.postcompCLM_norm rootColumnsLinear
  have hout : N04BoundaryWordBounds Q K s d x θ P
      (‖rootColumnsLinear‖ * M') H t shift := by
    apply hmap.congr (Q := Q) hx
    intro y _
    apply ContinuousLinearMap.ext
    intro v
    simp only [Function.comp_apply]
    rw [rootColumnsLinear_apply, n04PositiveGeometry_rootInverseLinear_apply]
    simp only [Function.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk,
      Fin.prod_univ_succ, Fin.prod_univ_zero, f, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, zero_mul, mul_one]
    ext <;> ring
  apply hout.enlarge hH (zero_le_one.trans ht)
  calc
    _ ≤ B * M' := mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hc.1)
    _ = _ := by dsimp only [M']; ring

/-- The physical coefficients move; the inverse-label slope is already
at the output angle. Both receive the same final parameter shift. -/
theorem n04PositiveGeometry_rootInverseMoving_word_bound (K s : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ, 1 ≤ degree ∧
    ∀ {U : Set E}, IsOpen U → ∀ {a e b ψ : E × ℝ → ℝ},
    ∀ Ja : SmoothDirections (U ×ˢ univ) a,
    ∀ Je : SmoothDirections (U ×ˢ univ) e,
    ∀ Jb : SmoothDirections (U ×ˢ univ) b,
    ∀ Jψ : SmoothDirections (U ×ˢ univ) ψ,
    ∀ Jam : SmoothDirections (U ×ˢ univ) (fun y => a (y.1, ψ y)),
    ∀ Jem : SmoothDirections (U ×ˢ univ) (fun y => e (y.1, ψ y)),
    ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
    ∀ Q : SmoothDirections (U ×ˢ univ) (fun y =>
      n04PositiveGeometry_rootInverseLinear σ (a (y.1, ψ y)) (e (y.1, ψ y)) (b y)),
    ∀ x ∈ U, ∀ θ, ∀ p q : Seminorm ℝ E, ∀ R : ℝ, 0 ≤ R →
    ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → H ≤ L → 1 ≤ t → ∀ shift,
    N04BoundaryWordBounds Ja K (s + K) 1 x (ψ (x, θ))
      (fun v => p v ≤ 1 ∧ q v ≤ R) M H t shift →
    N04BoundaryWordBounds Je K (s + K) 1 x (ψ (x, θ))
      (fun v => p v ≤ 1 ∧ q v ≤ R) M H t shift →
    N04BoundaryPositiveWordBounds Jψ K (s + K) 1 x θ
      (fun v => p v ≤ 1 ∧ q v ≤ R) M H t shift →
    N04BoundaryWordBounds Jb K s 1 x θ
      (fun v => p v ≤ 1 ∧ q v ≤ R) M H t shift →
    N04BoundaryWordBounds Q K s 1 x θ (fun v => p v ≤ 1 ∧ q v ≤ R)
      (C * M ^ degree) H t (shift + 1) := by
  obtain ⟨Cm, hCm, hmove⟩ := n04PositiveGeometry_boundaryMoving_saved_word_bound (E := E) (F := ℝ) K s
  obtain ⟨Cl, hCl, dl, hdl, hlinear⟩ :=
    n04PositiveGeometry_rootInverseLinear_word_bound (E := E) (K + s + 1) L hL
  let dm := 2 * (K + s + 1) + 2
  refine ⟨Cl * (1 + Cm) ^ dl,
    one_le_mul_of_one_le_of_one_le hCl (one_le_pow₀ (by linarith)),
    (1 + dm) * dl, by nlinarith, ?_⟩
  intro U hU a e b ψ Ja Je Jb Jψ Jam Jem σ hσ Q x hx θ p q R hR M H t hM hH hHM hHL ht shift ha he hψ hb
  have ham := hmove Ja Jψ Jam x hx θ p q R hR M H t hM hH hHM ht shift ha hψ
  have hem := hmove Je Jψ Jem x hx θ p q R hR M H t hM hH hHM ht shift he hψ
  have hc := n04PositiveGeometry_power_product_cost (degree := dm) hCm hM
  have hb' := (hb.shift (zero_le_one.trans hM) hH ht (Nat.le_succ shift)).enlarge
    hH (zero_le_one.trans ht) hc.2.1
  have ha' := ham.enlarge hH (zero_le_one.trans ht) hc.2.2
  have he' := hem.enlarge hH (zero_le_one.trans ht) hc.2.2
  have hout := hlinear hU Jam Jem Jb σ hσ Q K s 1 le_rfl x hx θ
    (fun v => p v ≤ 1 ∧ q v ≤ R) ((1 + Cm) * M ^ (1 + dm)) H t
    hc.1 hH hHL ht (shift + 1) ha' he' hb'
  simpa only [mul_pow, ← pow_mul, mul_assoc] using hout

end ContinuousFlexibility.Analysis
