import ContinuousFlexibility.Geometry.GraphEmbedding
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Data.Set.Card

/-!
# At most four affine isometries preserve a marked frame

This is the linear algebra step of Section 2, lines 250–253. All Euclidean
affine isometries, including reflections, are allowed. The point, normal and
two principal lines must still be identified on the actual closed surface.
No existence of a cap or a noncongruence conclusion is assumed here.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Module

set_option backward.isDefEq.respectTransparency false

/-- A real linear isometry preserving a nonzero real line acts by a sign. -/
theorem linearIsometry_eq_or_eq_neg_of_mem_span
    (L : E3 ≃ₗᵢ[ℝ] E3) {v : E3} (hv : v ≠ 0)
    (hline : L v ∈ Submodule.span ℝ {v}) : L v = v ∨ L v = -v := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hline
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnorm : |a| * ‖v‖ = ‖v‖ := by
    calc
      |a| * ‖v‖ = ‖a • v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖L v‖ := congrArg norm ha
      _ = ‖v‖ := L.norm_map v
  have habs : |a| = 1 := mul_right_cancel₀ hn (hnorm.trans (one_mul ‖v‖).symm)
  rcases abs_eq_abs.mp (show |a| = |(1 : ℝ)| by simpa using habs) with h | h
  · left
    simpa [h] using ha.symm
  · right
    simpa [h] using ha.symm

/-- The last frame vector is the fixed normal; the first two are preserved
as unoriented lines. No orientation or determinant restriction is imposed. -/
def markerStabilizers (p : E3) (b : Basis (Fin 3) ℝ E3) : Set (E3 ≃ᵃⁱ[ℝ] E3) :=
  {A | A p = p ∧ A.linearIsometryEquiv (b 2) = b 2 ∧
    A.linearIsometryEquiv (b 0) ∈ Submodule.span ℝ {b 0} ∧
    A.linearIsometryEquiv (b 1) ∈ Submodule.span ℝ {b 1}}

def markerStabilizerEncoding (b : Basis (Fin 3) ℝ E3) (A : E3 ≃ᵃⁱ[ℝ] E3) : E3 × E3 :=
  (A.linearIsometryEquiv (b 0), A.linearIsometryEquiv (b 1))

theorem markerStabilizerEncoding_injOn (p : E3) (b : Basis (Fin 3) ℝ E3) :
    Set.InjOn (markerStabilizerEncoding b) (markerStabilizers p b) := by
  intro A hA B hB hab
  have hL : A.linearIsometryEquiv.toLinearEquiv = B.linearIsometryEquiv.toLinearEquiv := by
    apply b.ext'
    intro i
    fin_cases i
    · exact congrArg Prod.fst hab
    · exact congrArg Prod.snd hab
    · exact hA.2.1.trans hB.2.1.symm
  apply AffineIsometryEquiv.ext
  intro x
  have hvec : A.linearIsometryEquiv (x - p) = B.linearIsometryEquiv (x - p) :=
    congrArg (fun L : E3 ≃ₗ[ℝ] E3 => L (x - p)) hL
  have ha := A.map_vadd p (x - p)
  have hb := B.map_vadd p (x - p)
  change A ((x - p) + p) = A.linearIsometryEquiv (x - p) + A p at ha
  change B ((x - p) + p) = B.linearIsometryEquiv (x - p) + B p at hb
  simp only [sub_add_cancel] at ha hb
  calc
    A x = A.linearIsometryEquiv (x - p) + A p := ha
    _ = B.linearIsometryEquiv (x - p) + B p := by rw [hvec, hA.1, hB.1]
    _ = B x := hb.symm

theorem markerStabilizerEncoding_mapsTo (p : E3) (b : Basis (Fin 3) ℝ E3) :
    Set.MapsTo (markerStabilizerEncoding b) (markerStabilizers p b)
      (({b 0, -b 0} : Set E3) ×ˢ ({b 1, -b 1} : Set E3)) := by
  intro A hA
  constructor
  · exact (linearIsometry_eq_or_eq_neg_of_mem_span A.linearIsometryEquiv
      (b.ne_zero 0) hA.2.2.1)
  · exact (linearIsometry_eq_or_eq_neg_of_mem_span A.linearIsometryEquiv
      (b.ne_zero 1) hA.2.2.2)

/-- Four sign pairs determine all possible linear parts; fixing `p` also
determines the translation. This bound includes ambient reflections. -/
theorem markerStabilizers_encard_le_four (p : E3) (b : Basis (Fin 3) ℝ E3) :
    (markerStabilizers p b).encard ≤ 4 := by
  have hpair (v : E3) : ({v, -v} : Set E3).encard ≤ 2 := by
    calc
      ({v, -v} : Set E3).encard ≤ ({-v} : Set E3).encard + 1 := Set.encard_insert_le _ _
      _ = 2 := by simp; norm_num
  calc
    (markerStabilizers p b).encard ≤
        (({b 0, -b 0} : Set E3) ×ˢ ({b 1, -b 1} : Set E3)).encard :=
      Set.encard_le_encard_of_injOn (markerStabilizerEncoding_mapsTo p b)
        (markerStabilizerEncoding_injOn p b)
    _ = ({b 0, -b 0} : Set E3).encard * ({b 1, -b 1} : Set E3).encard := Set.encard_prod
    _ ≤ 2 * 2 := mul_le_mul' (hpair (b 0)) (hpair (b 1))
    _ = 4 := by norm_num

theorem markerStabilizers_finite (p : E3) (b : Basis (Fin 3) ℝ E3) :
    (markerStabilizers p b).Finite :=
  Set.finite_of_encard_le_coe (markerStabilizers_encard_le_four p b)

/-- Coordinates of an actual linear operator diagonal in the supplied frame. -/
theorem marker_diagonal_operator_coordinate (b : Basis (Fin 3) ℝ E3)
    (S : E3 →ₗ[ℝ] E3) (eigenvalue : Fin 3 → ℝ)
    (hdiag : ∀ i, S (b i) = eigenvalue i • b i) (v : E3) (j : Fin 3) :
    b.repr (S v) j = eigenvalue j * b.repr v j := by
  have heq : S v = ∑ i, b.repr v i • (eigenvalue i • b i) := by
    calc
      S v = S (∑ i, b.repr v i • b i) := congrArg S (b.sum_repr v).symm
      _ = _ := by rw [map_sum]; simp only [map_smul, hdiag]
  rw [heq, map_sum]
  simp [map_smul, smul_smul, mul_comm, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- A simple eigenvalue has exactly its frame line as eigenspace. -/
theorem marker_mem_line_of_eigenvector (b : Basis (Fin 3) ℝ E3)
    (S : E3 →ₗ[ℝ] E3) (eigenvalue : Fin 3 → ℝ) (heigenvalue : Function.Injective eigenvalue)
    (hdiag : ∀ i, S (b i) = eigenvalue i • b i) (i : Fin 3) {v : E3}
    (heigen : S v = eigenvalue i • v) : v ∈ Submodule.span ℝ {b i} := by
  have hz (j : Fin 3) (hji : j ≠ i) : b.repr v j = 0 := by
    have he := congrArg (fun w : E3 => b.repr w j) heigen
    rw [marker_diagonal_operator_coordinate b S eigenvalue hdiag, map_smul] at he
    change eigenvalue j * b.repr v j = eigenvalue i * b.repr v j at he
    have hprod : (eigenvalue j - eigenvalue i) * b.repr v j = 0 := by rw [sub_mul, he, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr (fun h => hji (heigenvalue h)))
  apply Submodule.mem_span_singleton.mpr
  refine ⟨b.repr v i, ?_⟩
  apply b.repr.injective
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hz j hji, Ne.symm hji]

/-- Commutation with an operator having three distinct frame eigenvalues
forces preservation of each eigenline, rather than assuming line preservation. -/
theorem marker_line_preserved_of_commute (b : Basis (Fin 3) ℝ E3)
    (S : E3 →ₗ[ℝ] E3) (eigenvalue : Fin 3 → ℝ) (heigenvalue : Function.Injective eigenvalue)
    (hdiag : ∀ i, S (b i) = eigenvalue i • b i) (L : E3 ≃ₗᵢ[ℝ] E3)
    (hcomm : ∀ v, S (L v) = L (S v)) (i : Fin 3) :
    L (b i) ∈ Submodule.span ℝ {b i} := by
  apply marker_mem_line_of_eigenvector b S eigenvalue heigenvalue hdiag i
  rw [hcomm, hdiag, map_smul]

/-- The frame is fixed through its normal and the operator itself. -/
def markerOperatorStabilizers (p : E3) (b : Basis (Fin 3) ℝ E3)
    (S : E3 →ₗ[ℝ] E3) : Set (E3 ≃ᵃⁱ[ℝ] E3) :=
  {A | A p = p ∧ A.linearIsometryEquiv (b 2) = b 2 ∧
    ∀ v, S (A.linearIsometryEquiv v) = A.linearIsometryEquiv (S v)}

theorem markerOperatorStabilizers_subset (p : E3) (b : Basis (Fin 3) ℝ E3)
    (S : E3 →ₗ[ℝ] E3) (eigenvalue : Fin 3 → ℝ) (heigenvalue : Function.Injective eigenvalue)
    (hdiag : ∀ i, S (b i) = eigenvalue i • b i) :
    markerOperatorStabilizers p b S ⊆ markerStabilizers p b := by
  intro A hA
  exact ⟨hA.1, hA.2.1,
    marker_line_preserved_of_commute b S eigenvalue heigenvalue hdiag A.linearIsometryEquiv hA.2.2 0,
    marker_line_preserved_of_commute b S eigenvalue heigenvalue hdiag A.linearIsometryEquiv hA.2.2 1⟩

theorem markerOperatorStabilizers_encard_le_four (p : E3) (b : Basis (Fin 3) ℝ E3)
    (S : E3 →ₗ[ℝ] E3) (eigenvalue : Fin 3 → ℝ) (heigenvalue : Function.Injective eigenvalue)
    (hdiag : ∀ i, S (b i) = eigenvalue i • b i) :
    (markerOperatorStabilizers p b S).encard ≤ 4 :=
  (Set.encard_le_encard (markerOperatorStabilizers_subset p b S eigenvalue heigenvalue hdiag)).trans
    (markerStabilizers_encard_le_four p b)

/-- The two nonzero, distinct marker curvatures and the zero normal
eigenvalue satisfy the simple-spectrum hypothesis above. -/
theorem marker_center_eigenvalues_injective {A B k : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hk : k ≠ 0) (hAB : A ≠ B) :
    Function.Injective (![-k * A, -k * B, 0] : Fin 3 → ℝ) := by
  have h0 : -k * A ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hk) hA
  have h1 : -k * B ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hk) hB
  have h01 : -k * A ≠ -k * B :=
    fun h => hAB (mul_left_cancel₀ (neg_ne_zero.mpr hk) h)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

end ContinuousFlexibility
