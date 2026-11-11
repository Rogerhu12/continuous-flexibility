import ContinuousFlexibility.Analysis.RootCoordinateJets
import ContinuousFlexibility.Analysis.RootTaylorBounds
import ContinuousFlexibility.Analysis.TaylorRemainderBounds
import ContinuousFlexibility.Analysis.RootCompositionZeroOrder
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Even root-substitution estimates at positive points

At each positive base point the input splits into its full Taylor
polynomial and a remainder.  The polynomial has a uniform jet bound.
For the remainder, the source box intersected with a ball about the
Taylor center supplies all hypotheses of the weighted composition
estimate.  One scalar coordinate parameter treats both root signs.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology ContDiff

/-- Every root sample of parameter norm at most one remains in the
source box. -/
theorem rootCoordinate_mem_sourceBox {σ : ℝ} (hσ : ‖σ‖ ≤ 1) {p : ℝ × ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) :
    rootCoordinate σ p ∈
      Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi := by
  have hλ := Statements.rpow_three_halves_mem_Icc hp.1
  have hσabs : |σ| ≤ 1 := by simpa only [Real.norm_eq_abs] using hσ
  have hmid : |σ * p.1 ^ (3 / 2 : ℝ)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hλ.1]
    simpa only [one_mul] using mul_le_mul hσabs hλ.2 hλ.1 zero_le_one
  exact ⟨hp.1, abs_le.mp hmid, hp.2⟩

/-- In the product max norm the sample lies within one root radius of
the Taylor center. -/
theorem norm_rootCoordinate_sub_center_le {σ : ℝ} (hσ : ‖σ‖ ≤ 1)
    {p : ℝ × ℝ} (hp : 0 ≤ p.1) :
    ‖rootCoordinate σ p - (p.1, 0, p.2)‖ ≤ p.1 ^ (3 / 2 : ℝ) := by
  have hλ : 0 ≤ p.1 ^ (3 / 2 : ℝ) := Real.rpow_nonneg hp _
  have hmid : ‖σ * p.1 ^ (3 / 2 : ℝ)‖ ≤ p.1 ^ (3 / 2 : ℝ) := by
    rw [norm_mul, Real.norm_of_nonneg hλ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hσ hλ
  simp only [rootCoordinate, Prod.mk_sub_mk, sub_self, sub_zero, Prod.norm_mk, norm_zero]
  exact max_le hλ (max_le hmid hλ)

/-- Away from the boundary the even average is an ordinary smooth
composition. -/
theorem contDiffAt_rootEven_pos {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContDiffAt ℝ ∞ (Statements.rootEven G) p := by
  have hplus : ContDiffAt ℝ ∞ (G ∘ rootCoordinate 1) p :=
    hG.contDiffAt.comp p (contDiffAt_rootCoordinate 1 hp)
  have hminus : ContDiffAt ℝ ∞ (G ∘ rootCoordinate (-1)) p :=
    hG.contDiffAt.comp p (contDiffAt_rootCoordinate (-1) hp)
  unfold Statements.rootEven
  simpa only [Function.comp_apply, rootCoordinate, one_mul, neg_one_mul]
    using (hplus.add hminus).div_const 2

/-- Averaging the two root-coordinate jets preserves a common bound. -/
theorem norm_iteratedFDeriv_rootEven_le_of_coordinate_bounds
    {R : ℝ × ℝ × ℝ → ℝ} (hR : ContDiff ℝ ∞ R)
    {p : ℝ × ℝ} (hp : 0 < p.1) (n : ℕ) {B : ℝ}
    (hbound : ∀ σ : ℝ, ‖σ‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n (R ∘ rootCoordinate σ) p‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (Statements.rootEven R) p‖ ≤ B := by
  have hplus : ContDiffAt ℝ n (R ∘ rootCoordinate 1) p :=
    (hR.contDiffAt.comp p (contDiffAt_rootCoordinate 1 hp)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hminus : ContDiffAt ℝ n (R ∘ rootCoordinate (-1)) p :=
    (hR.contDiffAt.comp p (contDiffAt_rootCoordinate (-1) hp)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have heq : Statements.rootEven R =
      (2 : ℝ)⁻¹ • ((R ∘ rootCoordinate 1) + (R ∘ rootCoordinate (-1))) := by
    funext q
    simp only [Statements.rootEven, rootCoordinate, Function.comp_apply,
      Pi.add_apply, Pi.smul_apply, one_mul, neg_one_mul, smul_eq_mul]
    ring
  rw [heq, iteratedFDeriv_const_smul_apply (hplus.add hminus),
    iteratedFDeriv_add_apply hplus hminus, norm_smul,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
  calc
    (2 : ℝ)⁻¹ * ‖iteratedFDeriv ℝ n (R ∘ rootCoordinate 1) p +
        iteratedFDeriv ℝ n (R ∘ rootCoordinate (-1)) p‖ ≤ (2 : ℝ)⁻¹ * (B + B) :=
      mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add
          (hbound 1 (by norm_num)) (hbound (-1) (by norm_num)))) (by norm_num)
    _ = B := by ring

/-- The Taylor remainder after either root sample has a uniform fixed-order
jet bound.  The same constant works for every parameter of norm at most one. -/
theorem exists_rootTaylor_remainder_coordinate_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G → ∀ M : ℝ,
      Statements.CSBound n
        (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G M →
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi, 0 < p.1 →
      ∀ σ : ℝ, ‖σ‖ ≤ 1 →
        ‖iteratedFDeriv ℝ n
          ((G - finiteTaylorPolynomial n G (p.1, 0, p.2)) ∘ rootCoordinate σ) p‖ ≤ C * M := by
  obtain ⟨D, hD, hcoord⟩ := exists_rootCoordinate_jet_bound n
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  refine ⟨(n.factorial : ℝ) * 2 * D ^ n,
    mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)) (by norm_num))
      (pow_pos hDpos n), ?_⟩
  intro G hG M hB p hp hp0 σ hσ
  let q : ℝ × ℝ × ℝ := (p.1, 0, p.2)
  let ρ : ℝ := p.1 ^ (3 / 2 : ℝ)
  let K : Set (ℝ × ℝ × ℝ) :=
    (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) ∩
      Metric.closedBall q ρ
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hp0 _
  have hqBox : q ∈
      Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi :=
    ⟨hp.1, ⟨by norm_num, by norm_num⟩, hp.2⟩
  have hM : 0 ≤ M :=
    (norm_nonneg (iteratedFDeriv ℝ 0 G q)).trans (hB 0 (Nat.zero_le n) q hqBox)
  have hK : Convex ℝ K :=
    ((convex_Icc (0 : ℝ) 1).prod
      ((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-Real.pi) Real.pi))).inter
        (convex_closedBall q ρ)
  have hq : q ∈ K := ⟨hqBox, Metric.mem_closedBall_self hρ.le⟩
  have hsample : rootCoordinate σ p ∈ K := by
    refine ⟨rootCoordinate_mem_sourceBox hσ hp, Metric.mem_closedBall.mpr ?_⟩
    simpa only [dist_eq_norm] using norm_rootCoordinate_sub_center_le hσ hp0.le
  have hradius : ∀ z ∈ K, ‖z - q‖ ≤ ρ := by
    intro z hz
    simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz.2
  have hrem := norm_iteratedFDeriv_finiteTaylor_remainder_comp_le
    (isOpen_Ioi.prod isOpen_univ) (contDiffOn_rootCoordinate σ) hG
    (show p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hp0, mem_univ _⟩)
    hK hq hsample hM hρ hradius n
    (fun z hz => hB n le_rfl z hz.1)
    (fun i hi hin => hcoord σ hσ i hi hin p hp0 hp.1.2)
  calc
    ‖iteratedFDeriv ℝ n
        ((G - finiteTaylorPolynomial n G (p.1, 0, p.2)) ∘ rootCoordinate σ) p‖ ≤
        (n.factorial : ℝ) * (2 * M) * D ^ n := hrem
    _ = ((n.factorial : ℝ) * 2 * D ^ n) * M := by ring

/-- At positive points the even root substitution preserves the exact
finite derivative order in the source bound. -/
theorem exists_rootEven_pos_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G → ∀ M : ℝ,
      Statements.CSBound n
        (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G M →
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi, 0 < p.1 →
        ‖iteratedFDeriv ℝ n (Statements.rootEven G) p‖ ≤ C * M := by
  obtain ⟨Cₚ, hCₚ, hpoly⟩ := exists_rootEven_finiteTaylor_jet_bound n
  obtain ⟨Cᵣ, hCᵣ, hrem⟩ := exists_rootTaylor_remainder_coordinate_jet_bound n
  refine ⟨Cₚ + Cᵣ, add_pos hCₚ hCᵣ, ?_⟩
  intro G hG M hB p hp hp0
  let P : ℝ × ℝ × ℝ → ℝ := finiteTaylorPolynomial n G (p.1, 0, p.2)
  let R : ℝ × ℝ × ℝ → ℝ := G - P
  have hP : ContDiff ℝ ∞ P := contDiff_finiteTaylorPolynomial n G (p.1, 0, p.2)
  have hR : ContDiff ℝ ∞ R := hG.sub hP
  have hqBox : (p.1, 0, p.2) ∈
      Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi :=
    ⟨hp.1, ⟨by norm_num, by norm_num⟩, hp.2⟩
  have hPe : ‖iteratedFDeriv ℝ n (Statements.rootEven P) p‖ ≤ Cₚ * M :=
    hpoly G p.1 p.2 M hp0 hp.1.2 (fun k hk => hB k hk _ hqBox)
  have hRe : ‖iteratedFDeriv ℝ n (Statements.rootEven R) p‖ ≤ Cᵣ * M :=
    norm_iteratedFDeriv_rootEven_le_of_coordinate_bounds hR hp0 n
      (fun σ hσ => hrem G hG M hB p hp hp0 σ hσ)
  have hPeSmooth : ContDiffAt ℝ n (Statements.rootEven P) p :=
    (contDiffAt_rootEven_pos hP hp0).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hReSmooth : ContDiffAt ℝ n (Statements.rootEven R) p :=
    (contDiffAt_rootEven_pos hR hp0).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hsplit : Statements.rootEven G = Statements.rootEven P + Statements.rootEven R := by
    funext z
    simp only [Statements.rootEven, R, Pi.sub_apply, Pi.add_apply]
    ring
  rw [hsplit, iteratedFDeriv_add_apply hPeSmooth hReSmooth]
  calc
    ‖iteratedFDeriv ℝ n (Statements.rootEven P) p +
        iteratedFDeriv ℝ n (Statements.rootEven R) p‖ ≤ Cₚ * M + Cᵣ * M :=
      (norm_add_le _ _).trans (add_le_add hPe hRe)
    _ = (Cₚ + Cᵣ) * M := by ring

end ContinuousFlexibility.Analysis
