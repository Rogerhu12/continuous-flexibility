import ContinuousFlexibility.Analysis.N05CanonicalAngularJetChoice

/-!
# Assembling the actual finite angular family

Each square-summable column is inserted into the genuine finite Hilbert
row. Their finite sum gives the literal canonical jet space, with the
expected coordinates and an explicit norm bound.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open scoped BigOperators

def n05CanonicalJetInsertion (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (j : Fin (s + 1)) (w : CanonicalL2Sequence S K) : CanonicalVolumeJets S K s :=
  ⟨fun m => PiLp.single 2 j (w m), (lp.memℓp w).mono' (fun m => by
    simp only [PiLp.norm_single, le_refl])⟩

theorem n05CanonicalJetInsertion_bound (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (j : Fin (s + 1)) (w : CanonicalL2Sequence S K) :
    ‖n05CanonicalJetInsertion S K s j w‖ ≤ ‖w‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro m
  change ‖(PiLp.single 2 j (w m) :
    PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m))‖ ≤ ‖w m‖
  simp only [PiLp.norm_single, le_refl]

def n05CanonicalJetAssembly (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : Fin (s + 1) → CanonicalL2Sequence S K) : CanonicalVolumeJets S K s :=
  ∑ j, n05CanonicalJetInsertion S K s j (w j)

theorem n05CanonicalJetAssembly_apply (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : Fin (s + 1) → CanonicalL2Sequence S K) (m : ℕ) (j : Fin (s + 1)) :
    n05CanonicalJetAssembly S K s w m j = w j m := by
  let P : CanonicalVolumeJets S K s →L[ℝ] CanonicalL2 S K m :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) j).comp
      (lp.evalCLM ℝ (fun k => PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K k)) 2 m)
  change P (∑ i, n05CanonicalJetInsertion S K s i (w i)) = w j m
  rw [map_sum]
  rw [Finset.sum_eq_single j]
  · exact PiLp.single_eq_same
      (β := fun _ : Fin (s + 1) => CanonicalL2 S K m) 2 j (w j m)
  · intro i hi hij
    exact PiLp.single_eq_of_ne'
      (β := fun _ : Fin (s + 1) => CanonicalL2 S K m) 2 hij (w i m)
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

theorem n05CanonicalJetAssembly_bound (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : Fin (s + 1) → CanonicalL2Sequence S K) :
    ‖n05CanonicalJetAssembly S K s w‖ ≤ ∑ j, ‖w j‖ := by
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum
    (fun j _ => n05CanonicalJetInsertion_bound S K s j (w j)))

theorem n05CanonicalJetAssembly_mem_graph (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : Fin (s + 1) → CanonicalL2Sequence S K)
    (hreflect : ∀ m, n05CanonicalReflection S K m (w 0 m) = w 0 m)
    (hweak : ∀ m (j : Fin (s + 1)),
      WeakCanonicalAngularDerivative S K m (w 0 m) (w j m) j.val) :
    n05CanonicalJetAssembly S K s w ∈ canonicalVolumeGraph S K s := by
  constructor
  · intro m
    simpa only [n05CanonicalJetAssembly_apply] using
      (n05CanonicalReflection_fixed_iff S K m (w 0 m)).mp (hreflect m)
  · intro m j
    simpa only [n05CanonicalJetAssembly_apply] using hweak m j

end ContinuousFlexibility.Statements
