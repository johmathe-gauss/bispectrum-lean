# Design Decisions

## No escnn dependency (2026-02-23)

**Decision**: Do not use `escnn` for Clebsch-Gordan coefficients.

**Rationale**: Keep dependencies minimal and math transparent.

**Instead**:
- C_n: no CG needed (commutative → scalar products)
- D_n: compute analytically from explicit 2D irrep formulas in paper
- SO(3): pre-computed JSON bundled with package; generation script provided

---

## nn.Module only, no functional API (2026-02-23)

**Decision**: All bispectrum computations exposed as `nn.Module` subclasses only.

**Rationale**: One way to do things. Reduces surface area and confusion.

---

## Raw signals in (2026-02-23)

**Decision**: Modules take raw real-valued spatial signals; handle Fourier transform internally.

**Rationale**: Consistency, encapsulation, correctness by default, simpler tests.

**Breaking change**: `SO3onS2` v0.1.0 accepted SH coefficients. New API accepts `(batch, nlat, nlon)`.

**Escape hatch**: `_forward_from_coeffs()` for advanced users, non-public API.

---

## float32 throughout (2026-02-23)

**Decision**: float32 (complex64 for complex outputs).

**Rationale**: GPU training pipeline compatibility.

---

## Naming: `{Group}on{Domain}` (2026-02-23)

**Decision**: Class names encode both the group and the domain it acts on, in mathematical notation.

**Examples**: `CnonZn`, `DnonR2`, `SO3onS2`, `OonR3`

**Rationale**: Precise, unambiguous, consistent with mathematical literature.

---

## Sole author on commits: Johan Mathe (2026-02-23)

**Decision**: No co-author lines in commit messages. Johan is the sole attributed author.
