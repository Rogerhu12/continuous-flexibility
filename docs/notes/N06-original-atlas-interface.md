# N06 original-atlas proof and the shared construction interface

## Scope and provenance

The public endpoint remains exactly

```lean
theorem N06 (hN05 : N05Statement) : N06Statement
```

The shared construction interface was implemented by N07a at commit
`438e5d40c0de8d0a0f22bdccadd4feb820ba44bd` and integrated into main at
`c9b130b932d5c608befa1ae9c46bff36145880f2`. This branch uses the same
`PrimitiveGeometryProperties`, raw return-correction spatial properties and
physical-witness periods. The authoritative repair record is now on main in
`docs/STATUS.md`; its mathematical audit and manuscript locations are recorded
in `N07a-interface-repair.md`.

This changes the propositions carried by the construction stages. It is not a
claim that the former complete existential `N05Statement → N06Statement` has
been refuted. In particular, a defect in an arbitrary chosen gauge alone would
not prove that existential statement false. The added clauses are explicit
obligations for the N02N03 and N04Coordinates producers.

## Exact coordinate payload retained by this port

Before the N07a integration, main already carried N07b's state-dependent
physical domains and `CanonicalPrimitiveGeometry`. The former Through04 tail was

```lean
N04Properties D T S C L K base loss ε ∧
  CanonicalPrimitiveGeometry D T S C L K base ε
```

The integrated interface inserts the raw construction certificate while
retaining that existing certificate on the same objects:

```lean
N04Properties D T S C L K base loss ε ∧
  CanonicalGeometry.PrimitiveGeometryProperties D T S C L K base ε ∧
  CanonicalPrimitiveGeometry D T S C L K base ε
```

`Blueprint.Statements.N04cStatement` carries precisely this tail.
`Blueprint.Assembly.N04_of_nodes` retains the entire pair of certificates.
Neighborhood restriction retains both certificates, including actual current
jets and root/moving-cut first-jet matching, as well as the new N03 spatial
coefficient clause. The corresponding N08 and coupled restriction clients are
ported with the same upstream proofs.

The raw certificate states reference radiality and positivity, actual spatial
and parameter jets, the chosen auxiliary-source gauge, and actual forward
chart/height transmission jets. It supplies no inverse estimate, source-level
membership, weak-solution regularity, finite Green formula, or relative
operator bound. The N06 analysis proves those conclusions separately.

## Actual physical representatives

The former physical witness clause was

```lean
HasCanonicalRepresentation D S C K z U F η f ∧ referenceRow D η = 0 ∧
```

The repaired clause explicitly retains `Function.Periodic η (0, Real.pi)` and
`Function.Periodic f (0, Real.pi)` between representation and normalization.
N06's named reconstruction already proves both. At the reference state,
`OutputMember` gives the height period, and `SourceMember` gives the period of
`f - λψ`; the original Sobolev-model period of ψ recovers the period of f.
No new regularity premise is imposed on an inverse solution.

## Retained objects and retired alternative transport

The proof keeps the original N05 K, V, b, graph, inverse and ψ. Its positive
cubic factor is `(r - K.left m) * (K.right m - r)`, on the actual original
interval. The finite Green identity identifies the complete forcing from the
original weak graph, including all three scalar columns.

Three unused cumulative arbitrary-normalizer transport declarations are
retired: `n06Normalizer_through04`,
`n06_exists_supported_normalizer_through05`, and
`n06_exists_fixed_normalizer_through05`. An arbitrary replacement of ψ need
not retain the new auxiliary-column gauge or jets. The independent copied-data
transport and the actual N05 graph shear, weighted estimates and first-normal
transport remain. The final original-atlas proof does not import this
alternative normalizer chain.

The exact endpoint extracts the raw certificate from the original Through05
witness. It does not add a geometry hypothesis to either N06 theorem. The
endpoint, every imported proof module and the standard-axiom audit must pass
CI before this line is reported complete.
