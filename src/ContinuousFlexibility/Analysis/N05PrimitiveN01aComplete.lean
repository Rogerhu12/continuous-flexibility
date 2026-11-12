import ContinuousFlexibility.Analysis.N05RetainedReferenceAssembly
import ContinuousFlexibility.Analysis.N05RetainedOpticalLowerAdapter
import ContinuousFlexibility.Analysis.N05RetainedN01a
import Lean.Util.CollectAxioms

/-!
# Primitive geometry on one actual retained reference

The result explicitly retains the same radial reference, material data,
physical spaces, controls, Part A and primitive geometry certificate.
It does not depend on whether the public `N01aStatement` currently includes
that last conjunct. The certificate is constructed from the actual Morse
tails and finite central part, not inferred from `N01PartA`.

The retained R11a/R12 assembly completes its own `Γ.reference`; the adapter
preserves that reference and its selected raw index formula.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

/-- The new primitive conjunct is supplied explicitly on the same seed. -/
theorem n05PrimitiveN01a_of_seed {q : ℝ} (P : SeedReferenceConstruction q)
    (hq : 0 < q) (hD : IsRadialReference P.reference)
    (hraw : (P.selected.family P.selected.sigma).cellIndex =
      morseTwoTailAt P.selected.chain.index (fun _ k => P.selected.chain.index + k)) :
    ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
      ∃ C : NonlinearGeometryData S,
        IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
          N01PartA A.val T S C ∧ N01PrimitiveGeometry A.val T S C := by
  obtain ⟨T, S, C, hT, hS, hA, _, _, _, hprimitive⟩ :=
    P.exists_n05RetainedN01a hq hD hraw
  exact ⟨⟨P.reference, hD⟩, T, S, C, hT, hS, hA, hprimitive⟩

/-- The actual closed retained construction supplies the strengthened
existential, including its new primitive geometry certificate. -/
theorem n05PrimitiveN01a_complete :
    ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
      ∃ C : NonlinearGeometryData S,
        IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
          N01PartA A.val T S C ∧ N01PrimitiveGeometry A.val T S C := by
  obtain ⟨_B, _C₀, _K₀, _B₀, _T, _models,
      _hC₀, _hK₀, _hB₀, _hT, _hwindow, _hcap,
      _hfar, _hbuffers, _henergy, _hrem, _herror,
      _CM, _KM, _Cstar, _requested, S, metadata,
      _hCM, _hKM, _hCstar, _hindex, _hmodels,
      _η, _Kfirst, _ε, _H, _K, P, Γ,
      _hη, _hη48, _hKfirst, _hε, _hsmall, _hH,
      _hselected, _hhead, _hreal, hw, hphi,
      _hleft, _hright, _hTL, _hTR, _hcolumn, _hcentral, _hcentralHeight,
      hconstruction, hcoordinates, hreference, _hfamily⟩ :=
    n05_exists_retained_radial_reference
  obtain ⟨Q, hreference_eq, hselected_eq, _hretained, _hprofile, _hheight⟩ :=
    exists_n05_seedReferenceConstruction_of_retained P metadata.selected
      metadata.first_two hw hphi hreference.1 hconstruction hcoordinates
  have hQ : IsRadialReference Q.reference := by
    simpa only [hreference_eq] using hreference
  obtain ⟨_e, _N, _hN, hraw, _hrest⟩ := hcoordinates
  have hrawQ : (Q.selected.family Q.selected.sigma).cellIndex =
      morseTwoTailAt Q.selected.chain.index (fun _ k => Q.selected.chain.index + k) := by
    simpa only [hselected_eq] using hraw
  exact n05PrimitiveN01a_of_seed Q zero_lt_one hQ hrawQ

end ContinuousFlexibility.Blueprint

/-- info: 'ContinuousFlexibility.Blueprint.n05PrimitiveN01a_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ContinuousFlexibility.Blueprint.n05PrimitiveN01a_complete
