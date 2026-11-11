import ContinuousFlexibility.Analysis.N05CanonicalFiniteApproximation

/-!
# A common dense carrier for all material and endpoint weights

For a fixed angular order, every finite-cell graph element can be reweighted
to every endpoint exponent and every real material order. Finite-cell
truncation therefore gives an actual dense common carrier in each level.
No smooth-density hypothesis or relationship between physical charts is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators Topology

def n05CanonicalFiniteScalar (q : Finset ℕ) (w : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m ∈ q then w m else 0

def n05CanonicalFiniteScalarBound (q : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ q, ‖w m‖

theorem n05CanonicalFiniteScalarBound_nonneg (q : Finset ℕ) (w : ℕ → ℝ) :
    0 ≤ n05CanonicalFiniteScalarBound q w :=
  Finset.sum_nonneg fun m _ => norm_nonneg (w m)

theorem n05CanonicalFiniteScalar_bound (q : Finset ℕ) (w : ℕ → ℝ) (m : ℕ) :
    ‖n05CanonicalFiniteScalar q w m‖ ≤ n05CanonicalFiniteScalarBound q w := by
  by_cases hm : m ∈ q
  · rw [n05CanonicalFiniteScalar, if_pos hm]
    exact Finset.single_le_sum (fun i _ => norm_nonneg (w i)) hm
  · rw [n05CanonicalFiniteScalar, if_neg hm, norm_zero]
    exact n05CanonicalFiniteScalarBound_nonneg q w

theorem n05CanonicalWeightRatio_cancel {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γfrom tfrom γto tto : ℝ) (m : ℕ) :
    n05CanonicalSampleWeight T S K γto tto m *
      n05CanonicalWeightRatio T S K γto γfrom tto tfrom m =
        n05CanonicalSampleWeight T S K γfrom tfrom m := by
  have hw := (n05CanonicalSampleWeight_pos hT hPart S K γto tto m).ne'
  rw [n05CanonicalWeightRatio, div_eq_mul_inv]
  calc
    _ = n05CanonicalSampleWeight T S K γfrom tfrom m *
        (n05CanonicalSampleWeight T S K γto tto m *
          (n05CanonicalSampleWeight T S K γto tto m)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hw, mul_one]

def n05CanonicalFiniteReweight (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γfrom tfrom γto tto : ℝ) (s : ℕ) (q : Finset ℕ) :
    (n05CanonicalVolumeModel T S K).level γfrom tfrom s →L[ℝ]
      (n05CanonicalVolumeModel T S K).level γto tto s :=
  n05CanonicalJetMultiplier S K s
    (n05CanonicalFiniteScalar q (n05CanonicalWeightRatio T S K γto γfrom tto tfrom))
    (n05CanonicalFiniteScalarBound q (n05CanonicalWeightRatio T S K γto γfrom tto tfrom))
    (n05CanonicalFiniteScalarBound_nonneg q _)
    (n05CanonicalFiniteScalar_bound q _)

theorem n05CanonicalFiniteReweight_apply (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γfrom tfrom γto tto : ℝ) (s : ℕ) (q : Finset ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γfrom tfrom s)
    (m : ℕ) (j : Fin (s + 1)) :
    (n05CanonicalFiniteReweight T S K γfrom tfrom γto tto s q v).val m j =
      if m ∈ q then n05CanonicalWeightRatio T S K γto γfrom tto tfrom m • v.val m j
        else 0 := by
  unfold n05CanonicalFiniteReweight
  have he := n05CanonicalJetMultiplier_apply S K s
    (n05CanonicalFiniteScalar q (n05CanonicalWeightRatio T S K γto γfrom tto tfrom))
    (n05CanonicalFiniteScalarBound q (n05CanonicalWeightRatio T S K γto γfrom tto tfrom))
    (n05CanonicalFiniteScalarBound_nonneg q _)
    (n05CanonicalFiniteScalar_bound q _)
    (show n05CanonicalClosedSubmodule S K s from v) m j
  by_cases hm : m ∈ q
  · simpa only [n05CanonicalFiniteScalar, if_pos hm] using he
  · simpa only [n05CanonicalFiniteScalar, if_neg hm, zero_smul] using he

theorem n05CanonicalFiniteReweight_bound (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γfrom tfrom γto tto : ℝ) (s : ℕ) (q : Finset ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γfrom tfrom s) :
    ‖n05CanonicalFiniteReweight T S K γfrom tfrom γto tto s q v‖ ≤
      n05CanonicalFiniteScalarBound q
        (n05CanonicalWeightRatio T S K γto γfrom tto tfrom) * ‖v‖ :=
  n05CanonicalJetMultiplier_bound S K s
    (n05CanonicalFiniteScalar q (n05CanonicalWeightRatio T S K γto γfrom tto tfrom))
    (n05CanonicalFiniteScalarBound q (n05CanonicalWeightRatio T S K γto γfrom tto tfrom))
    (n05CanonicalFiniteScalarBound_nonneg q _)
    (n05CanonicalFiniteScalar_bound q _) v

theorem n05CanonicalFiniteReweight_forget {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γfrom tfrom γto tto : ℝ) (s : ℕ) (q : Finset ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γfrom tfrom s) :
    (n05CanonicalVolumeModel T S K).forget γto tto s
        (n05CanonicalFiniteReweight T S K γfrom tfrom γto tto s q v) =
      (n05CanonicalVolumeModel T S K).forget γfrom tfrom s
        (n05CanonicalFiniteTruncate S K s q v) := by
  funext m
  have hleft := n05CanonicalVolumeModel_forget T S K γto tto s
    (n05CanonicalFiniteReweight T S K γfrom tfrom γto tto s q v) m
  have hright := n05CanonicalVolumeModel_forget T S K γfrom tfrom s
    (n05CanonicalFiniteTruncate S K s q v) m
  refine hleft.trans (Eq.trans ?_ hright.symm)
  have hr := n05CanonicalFiniteReweight_apply T S K γfrom tfrom γto tto s q v m 0
  have ht := n05CanonicalFiniteTruncate_apply S K s q
    (show n05CanonicalClosedSubmodule S K s from v) m 0
  rw [hr, ht]
  by_cases hm : m ∈ q
  · simp only [if_pos hm, smul_smul]
    simpa only [n05CanonicalSampleWeight] using
      congrArg (fun c : ℝ => c • v.val m 0)
        (n05CanonicalWeightRatio_cancel hT hPart S K γfrom tfrom γto tto m)
  · simp only [if_neg hm, smul_zero]

def n05CanonicalCommonWeightCarrier (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (s : ℕ) :
    Set ((n05CanonicalVolumeModel T S K).level γ t s) :=
  {v | ∀ γ' t' : ℝ, VolumeMember S K (n05CanonicalVolumeModel T S K) γ' t' s
    ((n05CanonicalVolumeModel T S K).forget γ t s v)}

theorem n05CanonicalFiniteTruncate_mem_commonWeights {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (s : ℕ) (q : Finset ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γ t s) :
    n05CanonicalFiniteTruncate S K s q v ∈ n05CanonicalCommonWeightCarrier T S K γ t s := by
  intro γ' t'
  exact ⟨n05CanonicalFiniteReweight T S K γ t γ' t' s q v,
    n05CanonicalFiniteReweight_forget hT hPart S K γ t γ' t' s q v⟩

theorem n05CanonicalCommonWeightCarrier_dense {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (s : ℕ) :
    Dense (n05CanonicalCommonWeightCarrier T S K γ t s) := by
  intro v
  apply mem_closure_of_tendsto (n05CanonicalFiniteTruncate_tendsto S K s v)
  exact Eventually.of_forall fun q =>
    n05CanonicalFiniteTruncate_mem_commonWeights hT hPart S K γ t s q v

end ContinuousFlexibility.Statements

