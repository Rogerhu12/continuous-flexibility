import ContinuousFlexibility.Analysis.SpacesPhysicalSynthesisCoordinates

/-!
# Physical shell synthesis into the actual closed weak graph

Each finite row gives the complete weighted jet of an actual even,
smooth, compactly supported cylinder packet. Continuity and closedness
extend that graph membership to every square-summable row family. The
same coordinates at successive levels give exact bonding compatibility.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal NNReal BigOperators Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

def spacesPhysicalShellHilbert (s k : ℕ) : SpacesPhysicalIntegerRows →L[ℝ] PhysicalJetHilbert s :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : JetIndex s => CylinderL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : JetIndex s =>
      spacesPhysicalSynthesisCoordinate hT (j.val 0).val (j.val 1).val (j.val 2).val k)

theorem spacesPhysicalShellHilbert_apply (s k : ℕ) (u : SpacesPhysicalIntegerRows) (j : JetIndex s) :
    spacesPhysicalShellHilbert hT s k u j =
      spacesPhysicalSynthesisCoordinate hT (j.val 0).val (j.val 1).val (j.val 2).val k u := by
  simp only [spacesPhysicalShellHilbert, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv, PiLp.toLp_apply,
    ContinuousLinearMap.pi_apply]

def spacesPhysicalShellSynthesisConstant (s : ℕ) : ℝ≥0 :=
  ((Fintype.card (JetIndex s) : ℝ≥0) + 1) *
    ∑ j : JetIndex s, spacesPhysicalSynthesisCoordinateConstant hT
      (j.val 0).val (j.val 1).val (j.val 2).val

theorem spacesPhysicalShellHilbert_norm_le (s k : ℕ) (u : SpacesPhysicalIntegerRows) :
    ‖spacesPhysicalShellHilbert hT s k u‖ ≤
      (spacesPhysicalShellSynthesisConstant hT s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) * ‖u‖ := by
  let C : ℝ≥0 := ∑ j : JetIndex s, spacesPhysicalSynthesisCoordinateConstant hT
    (j.val 0).val (j.val 1).val (j.val 2).val
  let B : ℝ := (C : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) * ‖u‖
  have hB : 0 ≤ B := by positivity
  have hpoint (j : JetIndex s) : ‖spacesPhysicalShellHilbert hT s k u j‖ ≤ B := by
    rw [spacesPhysicalShellHilbert_apply]
    have hCj : (spacesPhysicalSynthesisCoordinateConstant hT
        (j.val 0).val (j.val 1).val (j.val 2).val : ℝ) ≤ C := by
      have hj : spacesPhysicalSynthesisCoordinateConstant hT
          (j.val 0).val (j.val 1).val (j.val 2).val ≤ C := by
        change spacesPhysicalSynthesisCoordinateConstant hT
          (j.val 0).val (j.val 1).val (j.val 2).val ≤
          ∑ i : JetIndex s, spacesPhysicalSynthesisCoordinateConstant hT
            (i.val 0).val (i.val 1).val (i.val 2).val
        exact Finset.single_le_sum (f := fun i : JetIndex s =>
          spacesPhysicalSynthesisCoordinateConstant hT
            (i.val 0).val (i.val 1).val (i.val 2).val)
          (fun _ _ => by positivity) (Finset.mem_univ j)
      exact_mod_cast hj
    have hexp : Real.exp ((((j.val 0).val + (j.val 1).val + (j.val 2).val : ℕ) : ℝ) * (k : ℝ)) ≤
        Real.exp ((s : ℝ) * (k : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr j.property) (Nat.cast_nonneg _))
    exact (spacesPhysicalSynthesisCoordinate_norm_le hT
      (j.val 0).val (j.val 1).val (j.val 2).val k u).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul hCj hexp (Real.exp_pos _).le C.property) (norm_nonneg u))
  have hcard : 0 ≤ (Fintype.card (JetIndex s) : ℝ) := Nat.cast_nonneg _
  have hcard' : (Fintype.card (JetIndex s) : ℝ) ≤ ((Fintype.card (JetIndex s) : ℝ) + 1) ^ 2 := by
    nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    (∑ j : JetIndex s, ‖spacesPhysicalShellHilbert hT s k u j‖ ^ 2) ≤
        ∑ _j : JetIndex s, B ^ 2 := Finset.sum_le_sum (fun j _ =>
          (sq_le_sq₀ (norm_nonneg _) hB).mpr (hpoint j))
    _ = (Fintype.card (JetIndex s) : ℝ) * B ^ 2 := by simp
    _ ≤ ((Fintype.card (JetIndex s) : ℝ) + 1) ^ 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_right hcard' (sq_nonneg B)
    _ = _ := by
      change ((Fintype.card (JetIndex s) : ℝ) + 1) ^ 2 *
        ((C : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) * ‖u‖) ^ 2 =
        ((((Fintype.card (JetIndex s) : ℝ) + 1) * (C : ℝ)) *
          Real.exp ((s : ℝ) * (k : ℝ)) * ‖u‖) ^ 2
      ring

theorem spacesPhysicalShellHilbert_single_mem_graph (s k : ℕ) (n : ℤ) (u : CylinderL2) :
    spacesPhysicalShellHilbert hT s k (lp.single 2 n u) ∈ physicalJetGraph T s := by
  apply spaces_physicalJetGraph_of_test T s
    (spacesPhysicalPacket_isCylinderTest n (spacesPhysicalFrequencyBand (T.M (T.radius n)) k) u).spaces_even
    (spacesCylinderEvenFunction_reflection _) (spacesPhysicalShellHilbert hT s k (lp.single 2 n u))
  intro j
  rw [spacesPhysicalShellHilbert_apply]
  exact spacesPhysicalSynthesisCoordinate_single_ae hT (j.val 0).val (j.val 1).val (j.val 2).val k n u

/-- Closedness of the original weak graph gives every infinite row family. -/
theorem spacesPhysicalShellHilbert_mem_graph (s k : ℕ) (u : SpacesPhysicalIntegerRows) :
    spacesPhysicalShellHilbert hT s k u ∈ physicalJetGraph T s := by
  have hs := (spacesPhysicalShellHilbert hT s k).hasSum (lp.hasSum_single ENNReal.ofNat_ne_top u)
  apply (isClosed_physicalJetGraph hT s).mem_of_tendsto hs
  filter_upwards [] with S
  rw [← physicalJetClosedSubmodule_carrier hT s]
  apply (physicalJetClosedSubmodule hT s).sum_mem
  intro n _
  change spacesPhysicalShellHilbert hT s k (lp.single 2 n (u n)) ∈
    (physicalJetClosedSubmodule hT s : Set (PhysicalJetHilbert s))
  rw [physicalJetClosedSubmodule_carrier hT s]
  exact spacesPhysicalShellHilbert_single_mem_graph hT s k n (u n)

/-- A physical shell operator into one of the actual closed Hilbert levels. -/
def spacesPhysicalShellSynthesis (s k : ℕ) :
    SpacesPhysicalIntegerRows →L[ℝ] physicalJetClosedSubmodule hT s :=
  (spacesPhysicalShellHilbert hT s k).codRestrict (physicalJetClosedSubmodule hT s) (by
    intro u
    change spacesPhysicalShellHilbert hT s k u ∈
      (physicalJetClosedSubmodule hT s : Set (PhysicalJetHilbert s))
    rw [physicalJetClosedSubmodule_carrier hT s]
    exact spacesPhysicalShellHilbert_mem_graph hT s k u)

theorem spacesPhysicalShellSynthesis_val (s k : ℕ) (u : SpacesPhysicalIntegerRows) :
    (spacesPhysicalShellSynthesis hT s k u).val = spacesPhysicalShellHilbert hT s k u := rfl

theorem spacesPhysicalShellSynthesis_apply (s k : ℕ) (u : SpacesPhysicalIntegerRows) (j : JetIndex s) :
    (spacesPhysicalShellSynthesis hT s k u).val j =
      spacesPhysicalSynthesisCoordinate hT (j.val 0).val (j.val 1).val (j.val 2).val k u := by
  rw [spacesPhysicalShellSynthesis_val, spacesPhysicalShellHilbert_apply]

theorem spacesPhysicalShellSynthesis_norm_le (s k : ℕ) (u : SpacesPhysicalIntegerRows) :
    ‖spacesPhysicalShellSynthesis hT s k u‖ ≤
      (spacesPhysicalShellSynthesisConstant hT s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) * ‖u‖ :=
  spacesPhysicalShellHilbert_norm_le hT s k u

theorem spacesPhysicalShellSynthesis_compatible (s k : ℕ) (u : SpacesPhysicalIntegerRows) :
    physicalJetBond hT s (spacesPhysicalShellSynthesis hT (s + 1) k u) =
      spacesPhysicalShellSynthesis hT s k u := by
  apply Subtype.ext
  apply PiLp.ext
  intro j
  change (physicalJetHilbertRestrict (Nat.le_succ s)
    (spacesPhysicalShellHilbert hT (s + 1) k u)) j = spacesPhysicalShellHilbert hT s k u j
  rw [physicalJetHilbertRestrict_apply, spacesPhysicalShellHilbert_apply, spacesPhysicalShellHilbert_apply]
  simp only [physicalJetIndexOfLE_val]

theorem spacesPhysicalShellSynthesis_zero (s k : ℕ) (u : SpacesPhysicalIntegerRows) :
    (spacesPhysicalShellSynthesis hT s k u).val (zeroJetIndex s) =
      spacesCylinderParity 0 (spacesPhysicalEnvelopeSynthesis hT 0 0
        (spacesPhysicalSynthesisJetRows hT 0 0 0 0 (by omega) k u)) := by
  rw [spacesPhysicalShellSynthesis_apply, spacesPhysicalSynthesisCoordinate_apply,
    spacesPhysicalSynthesisRawCoordinate_apply]
  simp only [zeroJetIndex, Fin.val_zero, Nat.zero_add, Nat.add_zero, Nat.zero_sub,
    Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right, Nat.cast_one, one_smul]

end ContinuousFlexibility.Statements
