import ContinuousFlexibility.Analysis.N08HeightRescale

/-!
# Parameter comparison from a small actual localized height

A fixed nonzero comparison parameter allows both diagonal entries to
be read from the same N02 first jet. The smallness of the localized
total height is used explicitly to keep both new states in that jet's
domain; proximity of the original state alone would not suffice.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

theorem n08CircleDiagonal_parameter_difference_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) :
    ∃ b : ℕ, ∃ δ K : ℝ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧ 0 ≤ K ∧
      ∀ x : AnnularState S, ∀ q : ℝ,
        (x, q) ∈ stateNeighborhood S C b δ → stateSector S x →
        ∀ m (h : (S.height (3 / 4 : ℝ)).Space),
          (S.height (3 / 4 : ℝ)).grading b h ≤ δ / 2 →
          (∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ,
            (S.height (3 / 4 : ℝ)).decode h =ᶠ[𝓝 (r, θ)]
              (S.height (3 / 4 : ℝ)).decode x.1.1) →
          (∀ r ∈ Ioo (C.left m) (C.right m), ∃ c : ℝ,
            S.chiLeft =ᶠ[𝓝 r] (fun _ => c)) →
          |n08CircleDiagonal hS hR (x, q) m - n08CircleDiagonal hS hR (x, 0) m| ≤
            K * T.M (T.sample m) ^ b * (S.height (3 / 4 : ℝ)).grading b h := by
  obtain ⟨b, ρ, K, hbase, hρ, hρε, hK, hcompare⟩ :=
    n08CircleDiagonal_state_difference_bound hT hS hN hR
  let δ := ρ / 4
  have hδ : 0 < δ := div_pos hρ (by norm_num)
  have hδρ : δ ≤ ρ := by dsimp only [δ]; linarith
  have htwodelta : 2 * δ < ρ := by dsimp only [δ]; linarith
  refine ⟨b, δ, K, hbase, hδ, hδρ.trans hρε, hK, ?_⟩
  intro x q hx hs m h hh hdecode hχ
  let qstar := 2 * δ
  let t := q / qstar
  let Y (v : ℝ) := n08LocalHeightState S x h (v - 1)
  have hqstar : 0 < qstar := mul_pos (by norm_num) hδ
  have ht : |t| ≤ 1 := by
    dsimp only [t]
    rw [abs_div, abs_of_pos hqstar]
    apply (div_le_one hqstar).mpr
    exact hx.2.le.trans (by dsimp only [qstar]; linarith)
  have hY (v : ℝ) (hv : |v| ≤ 1) : (Y v, qstar) ∈ stateNeighborhood S C b ρ := by
    constructor
    · have hcoeff : |v - 1| ≤ 2 := by
        have hb : |v - 1| ≤ |v| + 1 := by simpa only [abs_one] using abs_sub v 1
        linarith only [hb, hv]
      have hb := n08LocalHeightState_grading_bound S C.referenceState x h b (v - 1)
      have hterm : |v - 1| * (S.height (3 / 4 : ℝ)).grading b h ≤ δ :=
        (mul_le_mul hcoeff hh (apply_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
      exact (hb.trans (add_le_add le_rfl hterm)).trans_lt
        ((add_lt_add_of_lt_of_le hx.1 (le_refl δ)).trans
          (by simpa only [two_mul] using htwodelta))
    · rw [abs_of_pos hqstar]
      exact htwodelta
  have hsY (v : ℝ) : stateSector S (Y v) := n08LocalHeightState_sector S hs h (v - 1)
  have hmono : stateNeighborhood S C b ρ ⊆ stateNeighborhood S C base ε :=
    n08_stateNeighborhood_mono hbase hρε
  have hxρ : (x, q) ∈ stateNeighborhood S C b ρ := n08_stateNeighborhood_mono le_rfl hδρ hx
  have hxzero : (x, 0) ∈ stateNeighborhood S C b ρ :=
    ⟨hxρ.1, (abs_zero : |(0 : ℝ)| = 0).trans_lt hρ⟩
  have hscale : qstar * t = q := by
    dsimp only [t]
    field_simp [hqstar.ne']
  have heq := n08CircleDiagonal_height_rescale hT hS hN hR h hscale
    (hmono hxρ) (hmono (hY t ht)) hs hdecode hχ
  have heqzero := n08CircleDiagonal_height_rescale hT hS hN hR h
    (show qstar * (0 : ℝ) = 0 from mul_zero _)
    (hmono hxzero) (hmono (hY 0 (by norm_num))) hs hdecode hχ
  have hdiff := hcompare (Y 0) (Y t) qstar (hY 0 (by norm_num)) (hY t ht) (hsY 0) (hsY t) m
  have hd : stateGrading S b (Y t - Y 0) ≤ (S.height (3 / 4 : ℝ)).grading b h := by
    have he : (t - 1) - ((0 : ℝ) - 1) = t := by ring
    exact ((n08LocalHeightState_difference_grading S x h b
      (t - 1) ((0 : ℝ) - 1)).trans
      (congrArg (fun a : ℝ => |a| * (S.height (3 / 4 : ℝ)).grading b h) he)).trans_le
      ((mul_le_mul_of_nonneg_right ht (apply_nonneg _ _)).trans_eq (one_mul _))
  rw [heq, heqzero]
  exact hdiff.trans (mul_le_mul_of_nonneg_left hd
    (mul_nonneg hK (pow_nonneg
      (zero_le_one.trans (n08_material_sample_bounds hN.1.1 hT m).2) _)))

end ContinuousFlexibility.Statements
