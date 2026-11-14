module

public import ContinuousFlexibility.Analysis.N05CanonicalRestriction
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Actual finite-cell approximations in the canonical weak graph

A finite coordinate mask multiplies all angular jets on each retained cell
by one and all other jets by zero. The approximations remain in the actual
weak graph, are contractions, and converge in its Hilbert norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal

def n05CanonicalCellMask (q : Finset ℕ) (m : ℕ) : ℝ :=
  if m ∈ q then 1 else 0

theorem n05CanonicalCellMask_bound (q : Finset ℕ) (m : ℕ) :
    ‖n05CanonicalCellMask q m‖ ≤ 1 := by
  by_cases hm : m ∈ q <;> simp [n05CanonicalCellMask, hm]

def n05CanonicalFiniteTruncateRaw (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (q : Finset ℕ) :
    CanonicalVolumeJets S K s →L[ℝ] CanonicalVolumeJets S K s :=
  n05CanonicalJetMultiplierRaw S K s (n05CanonicalCellMask q) 1 zero_le_one
    (n05CanonicalCellMask_bound q)

theorem n05CanonicalFiniteTruncateRaw_piece (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (q : Finset ℕ)
    (v : CanonicalVolumeJets S K s) (m : ℕ) :
    n05CanonicalFiniteTruncateRaw S K s q v m = if m ∈ q then v m else 0 := by
  rw [n05CanonicalFiniteTruncateRaw, n05CanonicalJetMultiplierRaw,
    n05LpMapCLM_apply, n05CanonicalJetMultiplierCoordinate_apply]
  by_cases hm : m ∈ q <;> simp [n05CanonicalCellMask, hm]

theorem n05CanonicalFiniteTruncateRaw_eq_sum (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (q : Finset ℕ) (v : CanonicalVolumeJets S K s) :
    n05CanonicalFiniteTruncateRaw S K s q v = ∑ m ∈ q, lp.single 2 m (v m) := by
  apply lp.ext
  funext m
  rw [n05CanonicalFiniteTruncateRaw_piece]
  simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply, Finset.sum_pi_single]

def n05CanonicalFiniteTruncate (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (q : Finset ℕ) :
    n05CanonicalClosedSubmodule S K s →L[ℝ] n05CanonicalClosedSubmodule S K s :=
  n05CanonicalJetMultiplier S K s (n05CanonicalCellMask q) 1 zero_le_one
    (n05CanonicalCellMask_bound q)

theorem n05CanonicalFiniteTruncate_piece (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (q : Finset ℕ)
    (v : n05CanonicalClosedSubmodule S K s) (m : ℕ) :
    (n05CanonicalFiniteTruncate S K s q v).val m =
      if m ∈ q then v.val m else 0 :=
  n05CanonicalFiniteTruncateRaw_piece S K s q v.val m

theorem n05CanonicalFiniteTruncate_apply (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (q : Finset ℕ)
    (v : n05CanonicalClosedSubmodule S K s) (m : ℕ) (j : Fin (s + 1)) :
    (n05CanonicalFiniteTruncate S K s q v).val m j =
      if m ∈ q then v.val m j else 0 := by
  rw [n05CanonicalFiniteTruncate_piece]
  by_cases hm : m ∈ q <;> simp [hm]

theorem n05CanonicalFiniteTruncate_bound (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (q : Finset ℕ)
    (v : n05CanonicalClosedSubmodule S K s) :
    ‖n05CanonicalFiniteTruncate S K s q v‖ ≤ ‖v‖ := by
  simpa only [n05CanonicalFiniteTruncate, one_mul] using n05CanonicalJetMultiplier_bound S K s
    (n05CanonicalCellMask q) 1 zero_le_one (n05CanonicalCellMask_bound q) v

theorem n05CanonicalFiniteTruncate_tendsto (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (v : n05CanonicalClosedSubmodule S K s) :
    Tendsto (fun q : Finset ℕ => n05CanonicalFiniteTruncate S K s q v) atTop (𝓝 v) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun q : Finset ℕ => n05CanonicalFiniteTruncateRaw S K s q v.val)
    atTop (𝓝 v.val)
  simp only [n05CanonicalFiniteTruncateRaw_eq_sum]
  exact lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) v.val

theorem n05CanonicalFiniteTruncate_range_tendsto (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (v : n05CanonicalClosedSubmodule S K s) :
    Tendsto (fun n : ℕ => n05CanonicalFiniteTruncate S K s (Finset.range n) v)
      atTop (𝓝 v) :=
  (n05CanonicalFiniteTruncate_tendsto S K s v).comp tendsto_finset_range

theorem n05CanonicalFiniteTruncate_forget (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (s : ℕ) (q : Finset ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γ t s) (m : ℕ) :
    (n05CanonicalVolumeModel T S K).forget γ t s
        (n05CanonicalFiniteTruncate S K s q v) m =
      if m ∈ q then (n05CanonicalVolumeModel T S K).forget γ t s v m else 0 := by
  have hleft := n05CanonicalVolumeModel_forget T S K γ t s
    (n05CanonicalFiniteTruncate S K s q v) m
  have hright := n05CanonicalVolumeModel_forget T S K γ t s v m
  have hj := n05CanonicalFiniteTruncate_apply S K s q
    (show n05CanonicalClosedSubmodule S K s from v) m 0
  have hw := congrArg (fun z : CanonicalL2 S K m =>
    (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) • z) hj
  by_cases hm : m ∈ q
  · simp only [if_pos hm] at hw
    rw [if_pos hm]
    exact hleft.trans (hw.trans hright.symm)
  · simp only [if_neg hm, smul_zero] at hw
    rw [if_neg hm]
    exact hleft.trans hw


theorem n05CanonicalFiniteTruncate_forget_eq (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) {γ₁ t₁ γ₂ t₂ : ℝ} {s₁ s₂ : ℕ}
    {u : (n05CanonicalVolumeModel T S K).level γ₁ t₁ s₁}
    {v : (n05CanonicalVolumeModel T S K).level γ₂ t₂ s₂}
    (h : (n05CanonicalVolumeModel T S K).forget γ₁ t₁ s₁ u =
      (n05CanonicalVolumeModel T S K).forget γ₂ t₂ s₂ v) (q : Finset ℕ) :
    (n05CanonicalVolumeModel T S K).forget γ₁ t₁ s₁
        (n05CanonicalFiniteTruncate S K s₁ q u) =
      (n05CanonicalVolumeModel T S K).forget γ₂ t₂ s₂
        (n05CanonicalFiniteTruncate S K s₂ q v) := by
  funext m
  rw [n05CanonicalFiniteTruncate_forget, n05CanonicalFiniteTruncate_forget, h]

def n05CanonicalFiniteCellCarrier (S : PhysicalSpacesData) (K : CanonicalData S) (s : ℕ) :
    Set (n05CanonicalClosedSubmodule S K s) :=
  {v | ∃ q : Finset ℕ, ∀ m, m ∉ q → v.val m = 0}

theorem n05CanonicalFiniteTruncate_mem (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (q : Finset ℕ) (v : n05CanonicalClosedSubmodule S K s) :
    n05CanonicalFiniteTruncate S K s q v ∈ n05CanonicalFiniteCellCarrier S K s := by
  refine ⟨q, fun m hm => ?_⟩
  rw [n05CanonicalFiniteTruncate_piece, if_neg hm]

theorem n05CanonicalFiniteCellCarrier_dense (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) : Dense (n05CanonicalFiniteCellCarrier S K s) := by
  intro v
  apply mem_closure_of_tendsto (n05CanonicalFiniteTruncate_tendsto S K s v)
  exact Eventually.of_forall fun q => n05CanonicalFiniteTruncate_mem S K s q v

end ContinuousFlexibility.Statements

