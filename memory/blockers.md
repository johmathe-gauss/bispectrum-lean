# Blockers & Open Questions

## Current Blockers

*None - ready for implementation work*

### Completed
1. ✓ GitHub Access - Token stored, repo cloned
2. ✓ Colleague's Draft - Read and documented
3. ✓ Codebase Review - Analysis complete

## Open Questions

### Technical (Answered)
- ✓ Which groups: Only SO(3) currently (continuous rotations on sphere)
- ✓ Performance: O(lmax⁶) per forward pass, CG multiplication dominant
- ✓ FFT: Uses torch-harmonics for spherical case, not yet for finite groups
- ✓ CG coefficients: Pre-computed in JSON for SO(3), placeholder function otherwise

### Direction Needed from Johan

**Priority decision**:
- **Option A**: Optimize existing SO(3) implementation?
- **Option B**: Add finite groups (cyclic, dihedral)?
- **Option C**: Full refactor for unified framework?

**If Option B (finite groups)**:
- Which groups first? Cyclic (simplest)? Dihedral (2D images)?
- CG source: Runtime (escnn) or pre-compute?
- Keep SO(3) separate or integrate?

---
*Last updated: 2026-02-23 03:47 UTC*
