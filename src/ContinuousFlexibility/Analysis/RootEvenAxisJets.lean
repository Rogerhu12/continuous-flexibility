import ContinuousFlexibility.Analysis.RootEvenInteriorBounds
import ContinuousFlexibility.Analysis.RootExtensionPhysicalBounds

/-!
# Genuine even root jets from input jets on the root axis

The interior Taylor estimate only uses the shrinking ball around the
actual Taylor center. Continuity bounds its finitely many input jets by
their root values plus any positive error. Passing to the actual smooth
extension at the root removes that error. No inverse neighborhood radius
appears in the constant, and no jet of the totalized raw boundary formula
is substituted for a jet of the smooth extension.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem rootEven_pos_local_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
      ∀ (x θ M : ℝ), 0 < x → x ≤ 1 →
      (∀ k ≤ n, ∀ q ∈ Metric.closedBall (x, 0, θ) (x ^ (3 / 2 : ℝ)),
        ‖iteratedFDeriv ℝ k G q‖ ≤ M) →
      ‖iteratedFDeriv ℝ n (rootEven G) (x, θ)‖ ≤ C * M := by
  obtain ⟨CP, hCP, hpoly⟩ := exists_rootEven_finiteTaylor_jet_bound n
  obtain ⟨D, hD, hcoord⟩ := exists_rootCoordinate_jet_bound n
  let CR : ℝ := (n.factorial : ℝ) * 2 * D ^ n
  have hCR : 0 < CR := mul_pos
    (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)) (by norm_num))
    (pow_pos (zero_lt_one.trans_le hD) n)
  refine ⟨CP + CR, add_pos hCP hCR, ?_⟩
  intro G hG x θ M hx hx1 hB
  let q : ℝ × ℝ × ℝ := (x, 0, θ)
  let ρ : ℝ := x ^ (3 / 2 : ℝ)
  let K : Set (ℝ × ℝ × ℝ) := Metric.closedBall q ρ
  let P : ℝ × ℝ × ℝ → ℝ := finiteTaylorPolynomial n G q
  let R : ℝ × ℝ × ℝ → ℝ := G - P
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hx _
  have hq : q ∈ K := Metric.mem_closedBall_self hρ.le
  have hM : 0 ≤ M := (norm_nonneg _).trans (hB 0 (Nat.zero_le n) q hq)
  have hP : ContDiff ℝ ∞ P := contDiff_finiteTaylorPolynomial n G q
  have hR : ContDiff ℝ ∞ R := hG.sub hP
  have hPB : ‖iteratedFDeriv ℝ n (rootEven P) (x, θ)‖ ≤ CP * M :=
    hpoly G x θ M hx hx1 (fun k hk => hB k hk q hq)
  have hRB : ‖iteratedFDeriv ℝ n (rootEven R) (x, θ)‖ ≤ CR * M := by
    apply norm_iteratedFDeriv_rootEven_le_of_coordinate_bounds hR hx n
    intro σ hσ
    have hsample : rootCoordinate σ (x, θ) ∈ K := by
      apply Metric.mem_closedBall.mpr
      simpa only [dist_eq_norm] using
        norm_rootCoordinate_sub_center_le hσ (p := (x, θ)) hx.le
    have hrem := norm_iteratedFDeriv_finiteTaylor_remainder_comp_le
      (isOpen_Ioi.prod isOpen_univ) (contDiffOn_rootCoordinate σ) hG
      (show (x, θ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hx, mem_univ _⟩)
      (convex_closedBall q ρ) hq hsample hM hρ
      (fun y hy => by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hy)
      n (fun y hy => hB n le_rfl y hy)
      (fun k hk hkn => hcoord σ hσ k hk hkn (x, θ) hx hx1)
    change ‖iteratedFDeriv ℝ n ((G - finiteTaylorPolynomial n G q) ∘
      rootCoordinate σ) (x, θ)‖ ≤ CR * M
    exact hrem.trans_eq (by dsimp only [CR]; ring)
  have hsplit : rootEven G = rootEven P + rootEven R := by
    funext p
    simp only [rootEven, R, Pi.sub_apply, Pi.add_apply]
    ring
  rw [hsplit, iteratedFDeriv_add_apply
    ((contDiffAt_rootEven_pos hP hx).of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    ((contDiffAt_rootEven_pos hR hx).of_le (by simp : (n : ℕ∞ω) ≤ ∞))]
  exact ((norm_add_le _ _).trans (add_le_add hPB hRB)).trans_eq (by ring)

/-- Every genuine smooth extension of the physical even formula has a
fixed finite-order bound at the root in terms of the actual input jets
there. The constant precedes the input, extension, angle and majorant. -/
theorem exists_rootEven_axis_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
      ∀ F : PolarPoint → ℝ, ContDiff ℝ ∞ F →
      EqOn F (rootEven G) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) →
      ∀ θ M : ℝ, (∀ k ≤ n, ‖iteratedFDeriv ℝ k G (0, 0, θ)‖ ≤ M) →
      ‖iteratedFDeriv ℝ n F (0, θ)‖ ≤ C * M := by
  obtain ⟨C, hC, hlocal⟩ := rootEven_pos_local_jet_bound n
  refine ⟨C, hC, ?_⟩
  intro G hG F hF hEq θ M hB
  apply le_of_forall_pos_le_add
  intro ε hε
  let η : ℝ := ε / C
  have hη : 0 < η := div_pos hε hC
  have hnear : ∀ᶠ q : ℝ × ℝ × ℝ in 𝓝 (0, 0, θ),
      ∀ k : Fin (n + 1), ‖iteratedFDeriv ℝ k.val G q‖ < M + η := by
    apply Filter.eventually_all.mpr
    intro k
    have hc : ContinuousAt (fun q => ‖iteratedFDeriv ℝ k.val G q‖) (0, 0, θ) :=
      (hG.continuous_iteratedFDeriv (by simp)).norm.continuousAt
    exact hc.eventually_lt_const
      ((hB k.val (Nat.le_of_lt_succ k.isLt)).trans_lt (lt_add_of_pos_right M hη))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  let a : ℝ := min 1 (δ / 4)
  have ha : 0 < a := lt_min zero_lt_one (div_pos hδ (by norm_num))
  have hclosed : IsClosed {p : PolarPoint | ‖iteratedFDeriv ℝ n F p‖ ≤ C * (M + η)} :=
    isClosed_le (hF.continuous_iteratedFDeriv (by simp)).norm continuous_const
  have hsub : Ioo (0 : ℝ) a ×ˢ ({θ} : Set ℝ) ⊆
      {p : PolarPoint | ‖iteratedFDeriv ℝ n F p‖ ≤ C * (M + η)} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hy' : y = θ := mem_singleton_iff.mp hy
    subst y
    have hx1 : x ≤ 1 := hx.2.le.trans (min_le_left _ _)
    have hxδ : x < δ / 4 := hx.2.trans_le (min_le_right _ _)
    have hball : ∀ k ≤ n, ∀ q ∈ Metric.closedBall (x, 0, θ) (x ^ (3 / 2 : ℝ)),
        ‖iteratedFDeriv ℝ k G q‖ ≤ M + η := by
      intro k hk q hq
      have hrpow : x ^ (3 / 2 : ℝ) ≤ x :=
        Real.rpow_le_self_of_le_one hx.1.le hx1 (by norm_num)
      have hcenter : dist ((x, 0, θ) : ℝ × ℝ × ℝ) (0, 0, θ) = x := by
        simp only [dist_eq_norm, Prod.mk_sub_mk, sub_zero, sub_self, Prod.norm_mk,
          norm_zero, Real.norm_eq_abs, abs_of_pos hx.1, max_self, max_eq_left hx.1.le]
      have hdist : dist q (0, 0, θ) < δ := by
        calc
          _ ≤ dist q (x, 0, θ) + dist (x, 0, θ) (0, 0, θ) := dist_triangle _ _ _
          _ ≤ x ^ (3 / 2 : ℝ) + x :=
            add_le_add (Metric.mem_closedBall.mp hq) hcenter.le
          _ ≤ x + x := add_le_add hrpow le_rfl
          _ < δ := by linarith only [hxδ, hδ]
      exact (hδsub (Metric.mem_ball.mpr hdist) ⟨k, Nat.lt_succ_of_le hk⟩).le
    rw [mem_setOf_eq, iteratedFDeriv_eqOn_of_isOpen (isOpen_Ioi.prod isOpen_univ) hEq n
      (show (x, θ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hx.1, mem_univ _⟩)]
    exact hlocal G hG x θ (M + η) hx.1 hx1 hball
  have hmem : ((0, θ) : PolarPoint) ∈ closure (Ioo (0 : ℝ) a ×ˢ ({θ} : Set ℝ)) := by
    rw [closure_prod_eq, closure_Ioo ha.ne, closure_singleton]
    exact ⟨⟨le_rfl, ha.le⟩, mem_singleton θ⟩
  have hb := closure_minimal hsub hclosed hmem
  have he : C * (M + η) = C * M + ε := by
    dsimp only [η]
    field_simp [hC.ne'] <;> ring
  exact hb.trans_eq he

end ContinuousFlexibility.Analysis
