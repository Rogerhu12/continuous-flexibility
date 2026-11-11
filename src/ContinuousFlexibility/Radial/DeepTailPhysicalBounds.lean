import ContinuousFlexibility.Radial.DeepTailPhysicalFlatness
import ContinuousFlexibility.Radial.DeepTailEdgeFluxBounds

/-!
# From the actual natural line to physical flatness

The natural-node recurrence, the whole-edge Poisson comparison and the
actual flux estimate supply the two initial bounds for the physical flux
system. Compactness controls the nonsingular gauge factors, and the
previous physical-jet and extension results give the frozen conclusion.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The density has one finite bound on the full natural half-open tail.
The physical expression is continuous even at the accumulation endpoint. -/
theorem tailPhysical_density_bounded {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start) :
    ∃ P : ℝ, 0 < P ∧ ∀ x ∈ Ico T.entrance T.endpoint, T.p x ≤ P := by
  let Q : ℝ → ℝ := fun x =>
    (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ (2 * (j : ℝ) ^ 2) *
      D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x
  have hR := tailPhysicalEndpoint_pos hD right
  obtain ⟨C, hC⟩ := hD
  have hQ : Continuous Q := by
    apply Continuous.div
    · exact ((continuous_tailPhysicalRadius right).div_const _ |>.rpow_const
        (fun x => Or.inl (div_pos (tailPhysicalRadius_pos right x) hR).ne')).mul
          (hC.1.2.2.1.1.continuous.comp (continuous_tailPhysicalRadius right))
    · exact continuous_tailPhysicalRadius right
    · exact fun x => (tailPhysicalRadius_pos right x).ne'
  obtain ⟨P, hP⟩ := (isCompact_Icc : IsCompact (Icc T.entrance T.endpoint)).
    exists_bound_of_continuousOn hQ.continuousOn
  refine ⟨|P| + 1, by positivity, fun x hx => ?_⟩
  have heq : T.p x = Q x := by
    rcases eq_or_lt_of_le hx.1 with hxe | hxe
    · subst x
      exact tailPhysical_density_at_entrance ⟨C, hC⟩ hT hphysical
    · exact (hphysical.2.2.1 x ⟨hxe, hx.2⟩).2
  calc
    _ ≤ |Q x| := by rw [heq]; exact le_abs_self (Q x)
    _ ≤ P := by simpa only [Real.norm_eq_abs] using hP x ⟨hx.1, hx.2.le⟩
    _ ≤ |P| + 1 := by linarith [le_abs_self P]

/-- A fixed outward shift of the node envelope also controls the sum of
the two values used by the actual whole-edge comparison. -/
theorem physical_node_sum_envelope {u : ℕ → ℝ} {start : ℕ}
    (hu : ∃ A : ℝ, 0 < A ∧ ∀ n,
      |u n| ≤ A * radialE (start + n) ^ A * exp (-radialS (start + n))) :
    ∃ C : ℝ, 0 < C ∧ ∀ n,
      |u n| + |u (n + 1)| ≤ C * radialE (start + n) ^ C * exp (-radialS (start + n)) := by
  obtain ⟨A, hA, hbound⟩ := hu
  obtain ⟨B, hB, hshift⟩ := physicalEnvelope_shift A hA.le 1
  let C : ℝ := A + A * B + B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith [mul_pos hA hB]
  have hBC : B ≤ C := by dsimp [C]; linarith [mul_pos hA hB]
  have hcoef : A + A * B ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun n => ?_⟩
  have hE : 1 ≤ radialE (start + n) := one_le_exp_iff.mpr (radialQ_nonneg _)
  have hfirst : |u n| ≤ A * radialE (start + n) ^ C * exp (-radialS (start + n)) :=
    (hbound n).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hE hAC) hA.le) (exp_pos _).le)
  have hsecond : |u (n + 1)| ≤ A * B * radialE (start + n) ^ C * exp (-radialS (start + n)) := by
    calc
      _ ≤ A * (radialE (start + n + 1) ^ A * exp (-radialS (start + n + 1))) := by
        simpa only [Nat.add_assoc, mul_assoc] using hbound (n + 1)
      _ ≤ A * (B * radialE (start + n) ^ B * exp (-radialS (start + n))) :=
        mul_le_mul_of_nonneg_left (hshift (start + n)) hA.le
      _ ≤ A * (B * radialE (start + n) ^ C * exp (-radialS (start + n))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hE hBC) hB.le)
          (exp_pos _).le) hA.le
      _ = _ := by ring
  calc
    _ ≤ A * radialE (start + n) ^ C * exp (-radialS (start + n)) +
        A * B * radialE (start + n) ^ C * exp (-radialS (start + n)) := add_le_add hfirst hsecond
    _ = (A + A * B) * radialE (start + n) ^ C * exp (-radialS (start + n)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (rpow_nonneg (exp_pos _).le _)) (exp_pos _).le

/-- Any fixed nonnegative multiple of a discrete envelope majorant is a
physical cell bound with a larger, still index-independent coefficient. -/
theorem physicalCellBound_of_majorant {cells : ℕ → Set ℝ} {E H N : ℕ → ℝ}
    {f : ℝ → ℝ} {A : ℝ} (hE : ∀ n, 1 ≤ E n) (hH : ∀ n, 0 ≤ H n) (hA : 0 ≤ A)
    (hN : ∃ B : ℝ, 0 < B ∧ ∀ n, N n ≤ B * E n ^ B * H n)
    (hf : ∀ n r, r ∈ cells n → |f r| ≤ A * N n) : PhysicalCellBound cells E H f := by
  obtain ⟨B, hB, hN⟩ := hN
  let C : ℝ := A * B + B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; linarith [mul_nonneg hA hB.le]
  have hABC : A * B ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun n r hr => ?_⟩
  calc
    _ ≤ A * N n := hf n r hr
    _ ≤ A * (B * E n ^ B * H n) := mul_le_mul_of_nonneg_left (hN n) hA
    _ = (A * B) * E n ^ B * H n := by ring
    _ ≤ C * E n ^ C * H n := mul_le_mul_of_nonneg_right
      (mul_le_mul hABC (rpow_le_rpow_of_exponent_le (hE n) hBC)
        (rpow_nonneg (zero_le_one.trans (hE n)) _) hC.le) (hH n)

/-- Compact continuity of a coefficient gives a uniform physical cell bound. -/
theorem physicalCellBound_of_compact_coefficient {cells : ℕ → Set ℝ} {E : ℕ → ℝ}
    {a b : ℝ} {f : ℝ → ℝ} (hE : ∀ n, 1 ≤ E n)
    (hs : ∀ n, cells n ⊆ Icc a b) (hf : ContinuousOn f (Icc a b)) :
    PhysicalCellBound cells E (fun _ => 1) f := by
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hf
  exact physicalCellBound_of_uniform hE
    (fun n r hr => by simpa only [Real.norm_eq_abs] using hK r (hs n hr))

/-- The physical gauge and flux have whole-edge envelopes obtained from
the actual natural solution, rather than from a chosen interpolation. -/
theorem tailNaturalLift_cell_bounds {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hη : T.η ≤ 1 / 2) (hu : TailNaturalEquation T u)
    (hnodes : ∃ A : ℝ, 0 < A ∧ ∀ n,
      |u (T.node n)| ≤ A * radialE (start + n) ^ A * exp (-radialS (start + n))) :
    PhysicalCellBound (tailPhysicalEdge T right) (fun n => radialE (start + n))
        (fun n => exp (-radialS (start + n))) (tailPhysicalLift D right j u) ∧
      PhysicalCellBound (tailPhysicalEdge T right) (fun n => radialE (start + n))
        (fun n => exp (-radialS (start + n))) (tailPhysicalFlux D right j u) := by
  have hE : ∀ n, 1 ≤ radialE (start + n) := fun n => one_le_exp_iff.mpr (radialQ_nonneg _)
  have hH : ∀ n : ℕ, 0 ≤ exp (-radialS (start + n)) := fun _ => (exp_pos _).le
  have hsum := physical_node_sum_envelope hnodes
  obtain ⟨P, hP, hPb⟩ := tailPhysical_density_bounded hD hT hphysical
  have hU : PhysicalCellBound (tailPhysicalEdge T right) (fun n => radialE (start + n))
      (fun n => exp (-radialS (start + n))) (fun r => u (tailPhysicalLog right r)) := by
    apply physicalCellBound_of_majorant hE hH (show (0 : ℝ) ≤ 2 by norm_num) hsum
    rintro n r ⟨x, hx, rfl⟩
    simpa only [tailPhysicalLog_radius] using
      tailNatural_edge_bound hT hu hη n (Ioo_subset_Icc_self hx)
  have hQ : PhysicalCellBound (tailPhysicalEdge T right) (fun n => radialE (start + n))
      (fun n => exp (-radialS (start + n)))
        (fun r => T.p (tailPhysicalLog right r) * deriv u (tailPhysicalLog right r)) := by
    apply physicalCellBound_of_majorant hE hH
      (show 0 ≤ 3 * T.Λ * P * (T.endpoint - T.entrance) from
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT.2.2.1.le) hP.le)
          (sub_pos.mpr hT.1).le) hsum
    rintro n r ⟨x, hx, rfl⟩
    simpa only [tailPhysicalLog_radius] using
      tailNatural_flux_edge_bound hT hu hη hP hPb n (Ioo_subset_Icc_self hx)
  have hR := tailPhysicalEndpoint_pos hD right
  obtain ⟨C, hC⟩ := hD
  have hs : ∀ n, tailPhysicalEdge T right n ⊆ Icc D.a D.b := by
    intro n r hr
    exact Ioo_subset_Icc_self (tailPhysicalEdge_subset_core hT hphysical n hr)
  let G : ℝ → ℝ := fun r => (r / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)
  have hG : ContinuousOn G (Icc D.a D.b) :=
    continuousOn_id.div_const _ |>.rpow_const
      (fun r hr => Or.inl (div_pos (hC.1.1.trans_le hr.1) hR).ne')
  have hGi : ContinuousOn (fun r => (G r)⁻¹) (Icc D.a D.b) :=
    hG.inv₀ (fun r hr => (rpow_pos_of_pos (div_pos (hC.1.1.trans_le hr.1) hR) _).ne')
  have hA : ContinuousOn (fun r => (j : ℝ) ^ 2 * (G r * D.w r / r)) (Icc D.a D.b) :=
    continuousOn_const.mul ((hG.mul hC.1.2.2.1.1.continuous.continuousOn).div continuousOn_id
      (fun r hr => (hC.1.1.trans_le hr.1).ne'))
  have hGB := physicalCellBound_of_compact_coefficient hE hs hG
  have hAB := physicalCellBound_of_compact_coefficient hE hs hA
  have hBi := (physicalCellBound_of_compact_coefficient hE hs hGi).const_mul
    hE (fun _ => zero_le_one) (if right then 1 else -1 : ℝ)
  constructor
  · exact hGB.coeff_mul hE hH hU
  · apply ((hAB.coeff_mul hE hH hU).add hE hH (hBi.coeff_mul hE hH hQ)).congr
    rintro n r ⟨x, hx, rfl⟩
    have hxt : x ∈ Ioo T.entrance T.endpoint :=
      ⟨(deepTail_entrance_le_node hT n).trans_lt hx.1,
        hx.2.trans (deepTail_node_lt_endpoint hT (n + 1))⟩
    simpa only [tailPhysicalLog_radius, G, mul_assoc] using
      (tailPhysicalFlux_radius ⟨C, hC⟩ hphysical hu hxt).symm

/-- The original natural line and physical relation imply all clauses of
the frozen physical-flatness conclusion at sufficiently deep smallness. -/
theorem tailPhysicalFlatConclusion_of_natural_line {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hη : T.η ≤ 1 / 2) (hline : TailNaturalLineAndKernel T) :
    TailPhysicalFlatConclusion D T right j start := by
  obtain ⟨u, hu, hune, hnodes⟩ := exists_tailNatural_nodes_decay hline hphysical
  have hb := tailNaturalLift_cell_bounds hD hT hphysical hη hu hnodes
  exact tailPhysicalFlatConclusion_of_cell_bounds hD hT hphysical hu hune hb.1 hb.2

end ContinuousFlexibility.Radial
