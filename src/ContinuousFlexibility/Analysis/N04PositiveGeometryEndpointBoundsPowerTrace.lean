import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPositivePower
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsFiniteProducts
import ContinuousFlexibility.Analysis.N06BoundaryRadialJets

/-!
# Actual finite radial traces of a positive power

Only the finite radial trace packet enters the exact scalar partition
formula. Its joint parameter and angular tower is therefore constructed
without assuming joint smoothness of an arbitrary root extension.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

def n04PositiveGeometry_rootPowerTrace (γ : ℝ) (n : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ c : OrderedFinpartition n, rpowJetCoefficient γ c.length *
    v 0 ^ (γ - c.length) * ∏ i, v (c.partSize i)

theorem n04PositiveGeometry_radialBoundaryJet_rpow
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) {θ : ℝ}
    (hpos : 0 < f (0, θ)) (γ : ℝ) (n : ℕ) :
    radialBoundaryJet (fun p => f p ^ γ) 0 n θ =
      n04PositiveGeometry_rootPowerTrace γ n (fun j => radialBoundaryJet f 0 j θ) := by
  let F : ℝ → ℝ := fun r => f (r, θ)
  have hF : ContDiff ℝ ∞ F := hf.comp (contDiff_id.prodMk contDiff_const)
  let Ω : Set ℝ := F ⁻¹' Ioi 0
  have hΩ : IsOpen Ω := isOpen_Ioi.preimage hF.continuous
  have hg : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ γ) (Ioi 0) :=
    fun _ hy => (contDiffAt_id.rpow_const_of_ne (ne_of_gt hy)).contDiffWithinAt
  have h := iteratedFDeriv_comp_ordered_apply hΩ isOpen_Ioi hF.contDiffOn hg
    (fun _ h => h) n (show (0 : ℝ) ∈ Ω from hpos) (fun _ => 1)
  have hleft : iteratedFDeriv ℝ n ((fun y : ℝ => y ^ γ) ∘ F) 0 (fun _ => 1) =
      radialBoundaryJet (fun p => f p ^ γ) 0 n θ := by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp only [Finset.prod_const_one, one_smul]
    rfl
  rw [hleft] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro c _
  have hj (i : Fin c.length) : iteratedFDeriv ℝ (c.partSize i) F 0
      ((fun _ => (1 : ℝ)) ∘ c.emb i) = radialBoundaryJet f 0 (c.partSize i) θ := by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp only [Function.comp_def, Finset.prod_const_one, one_smul]
    rfl
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_rpow_eq, smul_eq_mul]
  simp only [hj]
  change _ * (rpowJetCoefficient γ c.length * f (0, θ) ^ (γ - c.length)) =
    rpowJetCoefficient γ c.length * f (0, θ) ^ (γ - c.length) * _
  ring

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

def n04PositiveGeometry_rootPowerTraceTermFields
    (γ : ℝ) (f : ℕ → E × ℝ → ℝ) {n : ℕ} (c : OrderedFinpartition n) :
    Fin (c.length + 1) → E × ℝ → ℝ :=
  Fin.cons (fun y => f 0 y ^ (γ - c.length)) (fun i y => f (c.partSize i) y)

def n04PositiveGeometry_rootPowerTraceTerm_inputs
    {U : Set E} {f : ℕ → E × ℝ → ℝ} {n : ℕ}
    (J : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ) (f j))
    (γ : ℝ) (hpos : ∀ y ∈ U ×ˢ (univ : Set ℝ), 0 < f 0 y)
    (c : OrderedFinpartition n) :
    ∀ i, SmoothDirections (U ×ˢ univ)
      (n04PositiveGeometry_rootPowerTraceTermFields γ f c i) :=
  Fin.cases (n04PositiveGeometry_positivePower_joint (J 0 (Nat.zero_le _))
    (γ - c.length) hpos) (fun i => J (c.partSize i) (c.partSize_le i))

def n04PositiveGeometry_rootPowerTraceTerm_joint
    {U : Set E} (hU : IsOpen U) {f : ℕ → E × ℝ → ℝ} {n : ℕ}
    (J : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ) (f j))
    (γ : ℝ) (hpos : ∀ y ∈ U ×ˢ (univ : Set ℝ), 0 < f 0 y)
    (c : OrderedFinpartition n) :=
  smoothDirections_postcompCLM
    (smoothDirections_finiteProduct (hU.prod isOpen_univ)
      (n04PositiveGeometry_rootPowerTraceTerm_inputs J γ hpos c))
    (rpowJetCoefficient γ c.length • ContinuousLinearMap.id ℝ ℝ)

def n04PositiveGeometry_rootPowerTrace_joint
    {U : Set E} (hU : IsOpen U) {f : ℕ → E × ℝ → ℝ} {n : ℕ}
    (J : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ) (f j))
    (γ : ℝ) (hpos : ∀ y ∈ U ×ˢ (univ : Set ℝ), 0 < f 0 y) :
    SmoothDirections (U ×ˢ univ)
      (fun y => n04PositiveGeometry_rootPowerTrace γ n (fun j => f j y)) := by
  apply (smoothDirections_finiteSum (hU.prod isOpen_univ)
    (n04PositiveGeometry_rootPowerTraceTerm_joint hU J γ hpos)).congr
  intro y _
  apply Finset.sum_congr rfl
  intro c _
  simp only [Function.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, Fin.prod_univ_succ,
    n04PositiveGeometry_rootPowerTraceTermFields, Fin.cons_zero, Fin.cons_succ, mul_assoc]

theorem n04PositiveGeometry_rootPowerTrace_word_bound
    (γ : ℝ) (n N : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ,
      ∀ {U : Set E}, IsOpen U → ∀ {f : ℕ → E × ℝ → ℝ},
      ∀ J : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ) (f j),
      ∀ Q : SmoothDirections (U ×ˢ univ)
        (fun y => n04PositiveGeometry_rootPowerTrace γ n (fun j => f j y)),
      (∀ y ∈ U ×ˢ (univ : Set ℝ), 0 < f 0 y) →
      ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → H ≤ L → 1 ≤ t → ∀ shift,
      (∀ j (hj : j ≤ n), N04BoundaryWordBounds (J j hj) K s d x θ P M H t shift) →
      (f 0 (x, θ))⁻¹ ≤ M →
      N04BoundaryWordBounds Q K s d x θ P (C * M ^ degree) H t shift := by
  classical
  choose Cp hCp dp hpower using fun c : OrderedFinpartition n =>
    n04PositiveGeometry_boundaryWord_positivePower (E := E) (γ - c.length) N
  choose Ct hCt dt hprod using fun c : OrderedFinpartition n =>
    n04PositiveGeometry_boundaryWord_finiteProduct (E := E) (c.length + 1) N L hL
  let coeff (c : OrderedFinpartition n) : ℝ :=
    |rpowJetCoefficient γ c.length| * Ct c * (1 + Cp c) ^ dt c
  let deg (c : OrderedFinpartition n) : ℕ := (1 + dp c) * dt c
  let C₀ : ℝ := 1 + ∑ c, coeff c
  let degree : ℕ := ∑ c, deg c
  have hcoeff (c : OrderedFinpartition n) : 0 ≤ coeff c :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (zero_le_one.trans (hCt c)))
      (pow_nonneg (by linarith only [hCp c]) _)
  have hC₀ : 1 ≤ C₀ := le_add_of_nonneg_right (Finset.sum_nonneg fun c _ => hcoeff c)
  have hcc (c : OrderedFinpartition n) : coeff c ≤ C₀ :=
    (Finset.single_le_sum (fun d _ => hcoeff d) (Finset.mem_univ c)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hdd (c : OrderedFinpartition n) : deg c ≤ degree :=
    Finset.single_le_sum (fun d _ => Nat.zero_le (deg d)) (Finset.mem_univ c)
  let count : ℝ := Fintype.card (OrderedFinpartition n)
  have hc : 0 ≤ count := Nat.cast_nonneg _
  refine ⟨(1 + count) * C₀, one_le_mul_of_one_le_of_one_le
    (le_add_of_nonneg_right hc) hC₀, degree, ?_⟩
  intro U hU f J Q hpos K s d hN x hx θ P M H t hM hH hHM hHL ht shift hin hinv
  let JT := n04PositiveGeometry_rootPowerTraceTerm_joint hU J γ hpos
  have hterm (c : OrderedFinpartition n) :
      N04BoundaryWordBounds (JT c) K s d x θ P (C₀ * M ^ degree) H t shift := by
    let JJ := n04PositiveGeometry_rootPowerTraceTerm_inputs J γ hpos c
    let JP := smoothDirections_finiteProduct (hU.prod isOpen_univ) JJ
    have hp := hpower c (J 0 (Nat.zero_le _)) (JJ 0) hpos
      K s d hN x hx θ P M H t hM hH hHM ht shift (hin 0 (Nat.zero_le _)) hinv
    have hm := n04PositiveGeometry_power_product_cost (degree := dp c) (hCp c) hM
    have hj : ∀ i, N04BoundaryWordBounds (JJ i) K s d x θ P
        ((1 + Cp c) * M ^ (1 + dp c)) H t shift :=
      Fin.cases (hp.enlarge hH (zero_le_one.trans ht) hm.2.2)
        (fun i => (hin (c.partSize i) (c.partSize_le i)).enlarge
          hH (zero_le_one.trans ht) hm.2.1)
    have hproduct := hprod c hU JJ JP K s d hN x hx θ P
      ((1 + Cp c) * M ^ (1 + dp c)) H t hm.1 hH hHL ht shift hj
    have hs := hproduct.scale (rpowJetCoefficient γ c.length)
    apply hs.enlarge hH (zero_le_one.trans ht)
    calc
      _ = coeff c * M ^ deg c := by
        dsimp only [coeff, deg]
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ C₀ * M ^ degree := mul_le_mul (hcc c)
        (pow_le_pow_right₀ hM (hdd c)) (pow_nonneg (zero_le_one.trans hM) _)
        (zero_le_one.trans hC₀)
  have hsum := N04BoundaryWordBounds.finiteSum hU JT hterm
  have heq : EqOn (fun y => ∑ c, rpowJetCoefficient γ c.length *
      ∏ i, n04PositiveGeometry_rootPowerTraceTermFields γ f c i y)
      (fun y => n04PositiveGeometry_rootPowerTrace γ n (fun j => f j y)) (U ×ˢ univ) := by
    intro y _
    apply Finset.sum_congr rfl
    intro c _
    simp only [Fin.prod_univ_succ, n04PositiveGeometry_rootPowerTraceTermFields,
      Fin.cons_zero, Fin.cons_succ, mul_assoc]
  have hq := hsum.congr (Q := Q) hx heq
  apply hq.enlarge hH (zero_le_one.trans ht)
  change count * (C₀ * M ^ degree) ≤ (1 + count) * C₀ * M ^ degree
  nlinarith only [mul_nonneg (zero_le_one.trans hC₀)
    (pow_nonneg (zero_le_one.trans hM) degree)]

end ContinuousFlexibility.Analysis
